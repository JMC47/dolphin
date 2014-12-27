// Copyright 2013 Dolphin Emulator Project
// Licensed under GPLv2
// Refer to the license.txt file included.

#include "Common/JitRegister.h"
#include "Common/MemoryUtil.h"

#include "Core/PowerPC/Jit64/Jit.h"
#include "Core/PowerPC/Jit64/JitAsm.h"
#include "Core/PowerPC/JitInterface.h"

using namespace Gen;

// Not PowerPC state.  Can't put in 'this' because it's out of range...
static void* s_saved_rsp;

// PLAN: no more block numbers - crazy opcodes just contain offset within
// dynarec buffer
// At this offset - 4, there is an int specifying the block number.

inline bool memcmp_insts(u32* src1, u32* src2, size_t insts)
{
	int first = insts & 7;
	u32 accum = 0;
	switch (first)
	{
	case 7: if (src1[6] != src2[6]) return false;
	case 6: if (src1[5] != src2[5]) return false;
	case 5: if (src1[4] != src2[4]) return false;
	case 4: if (src1[3] != src2[3]) return false;
	case 3: if (src1[2] != src2[2]) return false;
	case 2: if (src1[1] != src2[1]) return false;
	case 1: if (src1[0] != src2[0]) return false;
	default:
		break;
	}
	src1 += first;
	src2 += first;
	for (int i = 0; i < (insts >> 3); i++)
	{
		__m128i a1 = _mm_loadu_si128((__m128i*)(src1 + i * 8 + 0));
		__m128i a2 = _mm_loadu_si128((__m128i*)(src1 + i * 8 + 4));
		__m128i b1 = _mm_loadu_si128((__m128i*)(src2 + i * 8 + 0));
		__m128i b2 = _mm_loadu_si128((__m128i*)(src2 + i * 8 + 4));
		a1 = _mm_xor_si128(a1, b1);
		a2 = _mm_xor_si128(a2, b2);
		a1 = _mm_or_si128(a1, a2);
		if (!_mm_testz_si128(a1, a1))
			return false;
	}
	return true;
}

bool check_cache(JitBlock *b)
{
	u32 address = b->originalAddress;
	u8* memaddress = Memory::base + address;
	//u8* memaddress = Memory::GetPointer(address);
	//u32* code = (u32*)&blockdata[address & 0x1fffffff];
	int size = b->originalSize;
	//if (!memcmp_insts((u32*)(Memory::base + address), code, size))
	//if (memcmp(memaddress, code, size * 4))
	u64 crc = crccode((u32*)memaddress, size);
	if (crc != b->crc)
	{
		JitInterface::InvalidateICache(address, size*4, false);
		return false;
	}
	return true;
}

void Jit64AsmRoutineManager::Generate()
{
	enterCode = AlignCode16();
	// We need to own the beginning of RSP, so we do an extra stack adjustment
	// for the shadow region before calls in this function.  This call will
	// waste a bit of space for a second shadow, but whatever.
	ABI_PushRegistersAndAdjustStack(ABI_ALL_CALLEE_SAVED, 8, /*frame*/ 16);
	if (m_stack_top)
	{
		// Pivot the stack to our custom one.
		MOV(64, R(RSCRATCH), R(RSP));
		MOV(64, R(RSP), Imm64((u64)m_stack_top - 0x20));
		MOV(64, MDisp(RSP, 0x18), R(RSCRATCH));
	}
	else
	{
		MOV(64, M(&s_saved_rsp), R(RSP));
	}
	// something that can't pass the BLR test
	MOV(64, MDisp(RSP, 8), Imm32((u32)-1));

	// Two statically allocated registers.
	MOV(64, R(RMEM), Imm64((u64)Memory::base));
	MOV(64, R(RPPCSTATE), Imm64((u64)&PowerPC::ppcState + 0x80));

	const u8* outerLoop = GetCodePtr();
		ABI_PushRegistersAndAdjustStack({}, 0);
		ABI_CallFunction(reinterpret_cast<void *>(&CoreTiming::Advance));
		ABI_PopRegistersAndAdjustStack({}, 0);
		FixupBranch skipToRealDispatch = J(SConfig::GetInstance().m_LocalCoreStartupParameter.bEnableDebugging); //skip the sync and compare first time
		dispatcherMispredictedBLR = GetCodePtr();
		AND(32, PPCSTATE(pc), Imm32(0xFFFFFFFC));

		#if 0 // debug mispredicts
		MOV(32, R(ABI_PARAM1), MDisp(RSP, 8)); // guessed_pc
		ABI_PushRegistersAndAdjustStack(1 << RSCRATCH2, 0);
		CALL(reinterpret_cast<void *>(&ReportMispredict));
		ABI_PopRegistersAndAdjustStack(1 << RSCRATCH2, 0);
		#endif

		ResetStack();

		SUB(32, PPCSTATE(downcount), R(RSCRATCH2));

		dispatcher = GetCodePtr();
			// The result of slice decrementation should be in flags if somebody jumped here
			// IMPORTANT - We jump on negative, not carry!!!
			FixupBranch bail = J_CC(CC_BE, true);

			FixupBranch dbg_exit;

			if (SConfig::GetInstance().m_LocalCoreStartupParameter.bEnableDebugging)
			{
				TEST(32, M(PowerPC::GetStatePtr()), Imm32(PowerPC::CPU_STEPPING));
				FixupBranch notStepping = J_CC(CC_Z);
				ABI_PushRegistersAndAdjustStack({}, 0);
				ABI_CallFunction(reinterpret_cast<void *>(&PowerPC::CheckBreakPoints));
				ABI_PopRegistersAndAdjustStack({}, 0);
				TEST(32, M(PowerPC::GetStatePtr()), Imm32(0xFFFFFFFF));
				dbg_exit = J_CC(CC_NZ, true);
				SetJumpTarget(notStepping);
			}

			SetJumpTarget(skipToRealDispatch);

			dispatcherNoCheck = GetCodePtr();
			MOV(32, R(RSCRATCH), PPCSTATE(pc));

			u64 icache = (u64)jit->GetBlockCache()->iCache.data();
			u64 icacheVmem = (u64)jit->GetBlockCache()->iCacheVMEM.data();
			u64 icacheEx = (u64)jit->GetBlockCache()->iCacheEx.data();
			u32 mask = 0;
			FixupBranch no_mem;
			FixupBranch exit_mem;
			FixupBranch exit_vmem;
			if (SConfig::GetInstance().m_LocalCoreStartupParameter.bWii)
				mask = JIT_ICACHE_EXRAM_BIT;
			mask |= JIT_ICACHE_VMEM_BIT;
			TEST(32, R(RSCRATCH), Imm32(mask));
			no_mem = J_CC(CC_NZ);
			AND(32, R(RSCRATCH), Imm32(JIT_ICACHE_MASK));

			if (icache <= INT_MAX)
			{
				MOV(32, R(RSCRATCH), MDisp(RSCRATCH, (s32)icache));
			}
			else
			{
				MOV(64, R(RSCRATCH2), Imm64(icache));
				MOV(32, R(RSCRATCH), MComplex(RSCRATCH2, RSCRATCH, SCALE_1, 0));
			}

			exit_mem = J();
			SetJumpTarget(no_mem);
			TEST(32, R(RSCRATCH), Imm32(JIT_ICACHE_VMEM_BIT));
			FixupBranch no_vmem = J_CC(CC_Z);
			AND(32, R(RSCRATCH), Imm32(JIT_ICACHE_MASK));
			if (icacheVmem <= INT_MAX)
			{
				MOV(32, R(RSCRATCH), MDisp(RSCRATCH, (s32)icacheVmem));
			}
			else
			{
				MOV(64, R(RSCRATCH2), Imm64(icacheVmem));
				MOV(32, R(RSCRATCH), MComplex(RSCRATCH2, RSCRATCH, SCALE_1, 0));
			}

			if (SConfig::GetInstance().m_LocalCoreStartupParameter.bWii) exit_vmem = J();
			SetJumpTarget(no_vmem);
			if (SConfig::GetInstance().m_LocalCoreStartupParameter.bWii)
			{
				TEST(32, R(RSCRATCH), Imm32(JIT_ICACHE_EXRAM_BIT));
				FixupBranch no_exram = J_CC(CC_Z);
				AND(32, R(RSCRATCH), Imm32(JIT_ICACHEEX_MASK));

				if (icacheEx <= INT_MAX)
				{
					MOV(32, R(RSCRATCH), MDisp(RSCRATCH, (s32)icacheEx));
				}
				else
				{
					MOV(64, R(RSCRATCH2), Imm64(icacheEx));
					MOV(32, R(RSCRATCH), MComplex(RSCRATCH2, RSCRATCH, SCALE_1, 0));
				}

				SetJumpTarget(no_exram);
			}
			SetJumpTarget(exit_mem);
			if (SConfig::GetInstance().m_LocalCoreStartupParameter.bWii)
				SetJumpTarget(exit_vmem);

			TEST(32, R(RSCRATCH), R(RSCRATCH));
			FixupBranch notfound = J_CC(CC_L, true);

			u64 blockPointers = (u64)jit->GetBlockCache()->GetBlocks();
			/*IMUL(32, RSCRATCH2, R(RSCRATCH), Imm32(sizeof(JitBlock)));
			MOV(64, R(R13), Imm64(blockPointers));
			MOV(32, R(ABI_PARAM1), MComplex(R13, RSCRATCH2, SCALE_1, offsetof(JitBlock, originalAddress)));
			MOV(32, R(ABI_PARAM3), MComplex(R13, RSCRATCH2, SCALE_1, offsetof(JitBlock, originalSize)));
			MOV(64, R(ABI_PARAM2), MComplex(R13, RSCRATCH2, SCALE_1, offsetof(JitBlock, originalCode)));
			SHL(32, R(ABI_PARAM3), Imm8(2));
			ADD(64, R(ABI_PARAM1), R(RMEM));*/
			MOV(32, R(R14), R(RSCRATCH));
			IMUL(32, ABI_PARAM1, R(RSCRATCH), Imm32(sizeof(JitBlock)));
			MOV(64, R(RSCRATCH), Imm64(blockPointers));
			ADD(64, R(ABI_PARAM1), R(RSCRATCH));
			ABI_PushRegistersAndAdjustStack({}, 0);
			ABI_CallFunctionR((void *)&check_cache, ABI_PARAM1);
			ABI_PopRegistersAndAdjustStack({}, 0);
			TEST(8, R(ABI_RETURN), R(ABI_RETURN));
			FixupBranch icachefail = J_CC(CC_Z);
			MOV(32, R(RSCRATCH), R(R14));


			/*MOV(32, R(R8), MComplex(RSCRATCH_EXTRA, RSCRATCH2, SCALE_1, offsetof(JitBlock, originalAddress)));
			MOV(32, R(R9), MComplex(RSCRATCH_EXTRA, RSCRATCH2, SCALE_1, offsetof(JitBlock, originalSize)));
			MOV(64, R(R10), MComplex(RSCRATCH_EXTRA, RSCRATCH2, SCALE_1, offsetof(JitBlock, originalCode)));
			SHL(32, R(R9), Imm8(2));

			XOR(32, R(R11), R(R11));
			MOV(32, R(R12), R(R9));
			AND(32, R(R12), Imm8(0x1f));

			// Check until we have a multiple of 32 left
			const u8 *memcmpLoop1 = GetCodePtr();
			MOV(32, R(R13), MComplex(RMEM, R8, SCALE_1, 0));
			CMP(32, R(R13), MatR(R10));
			FixupBranch icachefail1 = J_CC(CC_NZ, true);
			ADD(32, R(R8), Imm8(4));
			ADD(64, R(R10), Imm8(4));
			SUB(32, R(R12), Imm8(4));
			J_CC(CC_G, memcmpLoop1);

			AND(32, R(R9), Imm32(~0x1f));
			FixupBranch doneCheck = J_CC(CC_Z);

			// Do the rest
			const u8 *memcmpLoop2 = GetCodePtr();
			MOVDQU(XMM0, MComplex(RMEM, R8, SCALE_1, 0));
			MOVDQU(XMM1, MComplex(RMEM, R8, SCALE_1, 16));
			MOVDQU(XMM2, MComplex(R10, R11, SCALE_1, 0));
			MOVDQU(XMM3, MComplex(R10, R11, SCALE_1, 16));
			PXOR(XMM0, R(XMM2));
			PXOR(XMM1, R(XMM3));
			POR(XMM0, R(XMM1));
			PTEST(XMM1, R(XMM1));
			FixupBranch icachefail2 = J_CC(CC_NZ);
			ADD(32, R(R8), Imm8(32));
			ADD(32, R(R11), Imm8(32));
			CMP(32, R(R11), R(R9));
			J_CC(CC_GE, memcmpLoop2);

			SetJumpTarget(doneCheck);*/

			//grab from list and jump to it
			u64 codePointers = (u64)jit->GetBlockCache()->GetCodePointers();
			if (codePointers <= INT_MAX)
			{
				JMPptr(MScaled(RSCRATCH, 8, (s32)codePointers));
			}
			else
			{
				MOV(64, R(RSCRATCH2), Imm64(codePointers));
				JMPptr(MComplex(RSCRATCH2, RSCRATCH, 8, 0));
			}
			SetJumpTarget(notfound);
			SetJumpTarget(icachefail);
		//	SetJumpTarget(icachefail2);

			//Ok, no block, let's jit
			ABI_PushRegistersAndAdjustStack({}, 0);
			ABI_CallFunctionA(32, (void *)&Jit, PPCSTATE(pc));
			ABI_PopRegistersAndAdjustStack({}, 0);

			// Jit might have cleared the code cache
			ResetStack();

			JMP(dispatcherNoCheck, true); // no point in special casing this

		SetJumpTarget(bail);
		doTiming = GetCodePtr();

		// Test external exceptions.
		TEST(32, PPCSTATE(Exceptions), Imm32(EXCEPTION_EXTERNAL_INT | EXCEPTION_PERFORMANCE_MONITOR | EXCEPTION_DECREMENTER));
		FixupBranch noExtException = J_CC(CC_Z);
		MOV(32, R(RSCRATCH), PPCSTATE(pc));
		MOV(32, PPCSTATE(npc), R(RSCRATCH));
		ABI_PushRegistersAndAdjustStack({}, 0);
		ABI_CallFunction(reinterpret_cast<void *>(&PowerPC::CheckExternalExceptions));
		ABI_PopRegistersAndAdjustStack({}, 0);
		SetJumpTarget(noExtException);

		TEST(32, M(PowerPC::GetStatePtr()), Imm32(0xFFFFFFFF));
		J_CC(CC_Z, outerLoop);

	//Landing pad for drec space
	if (SConfig::GetInstance().m_LocalCoreStartupParameter.bEnableDebugging)
		SetJumpTarget(dbg_exit);
	ResetStack();
	if (m_stack_top)
	{
		ADD(64, R(RSP), Imm8(0x18));
		POP(RSP);
	}
	ABI_PopRegistersAndAdjustStack(ABI_ALL_CALLEE_SAVED, 8, 16);
	RET();

	JitRegister::Register(enterCode, GetCodePtr(), "JIT_Loop");

	GenerateCommon();
}

void Jit64AsmRoutineManager::ResetStack()
{
	if (m_stack_top)
		MOV(64, R(RSP), Imm64((u64)m_stack_top - 0x20));
	else
		MOV(64, R(RSP), M(&s_saved_rsp));
}


void Jit64AsmRoutineManager::GenerateCommon()
{
	fifoDirectWrite8 = AlignCode4();
	GenFifoWrite(8);
	fifoDirectWrite16 = AlignCode4();
	GenFifoWrite(16);
	fifoDirectWrite32 = AlignCode4();
	GenFifoWrite(32);
	fifoDirectWrite64 = AlignCode4();
	GenFifoWrite(64);
	frsqrte = AlignCode4();
	GenFrsqrte();
	fres = AlignCode4();
	GenFres();
	mfcr = AlignCode4();
	GenMfcr();

	GenQuantizedLoads();
	GenQuantizedStores();
	GenQuantizedSingleStores();

	//CMPSD(R(XMM0), M(&zero),
	// TODO

	// Fast write routines - special case the most common hardware write
	// TODO: use this.
	// Even in x86, the param values will be in the right registers.
	/*
	const u8 *fastMemWrite8 = AlignCode16();
	CMP(32, R(ABI_PARAM2), Imm32(0xCC008000));
	FixupBranch skip_fast_write = J_CC(CC_NE, false);
	MOV(32, RSCRATCH, M(&m_gatherPipeCount));
	MOV(8, MDisp(RSCRATCH, (u32)&m_gatherPipe), ABI_PARAM1);
	ADD(32, 1, M(&m_gatherPipeCount));
	RET();
	SetJumpTarget(skip_fast_write);
	CALL((void *)&Memory::Write_U8);*/
}
