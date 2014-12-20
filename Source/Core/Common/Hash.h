// Copyright 2013 Dolphin Emulator Project
// Licensed under GPLv2
// Refer to the license.txt file included.

#pragma once

#include <cstddef>

#include "Common/Common.h"

u32 HashFletcher(const u8* data_u8, size_t length);  // FAST. Length & 1 == 0.
u32 HashAdler32(const u8* data, size_t len);         // Fairly accurate, slightly slower
u32 HashFNV(const u8* ptr, int length);              // Another fast and decent hash
u32 HashEctor(const u8* ptr, int length);            // JUNK. DO NOT USE FOR NEW THINGS
u64 GetCRC32(const u8 *src, int len, u32 samples);   // SSE4.2 version of CRC32
u64 GetHashHiresTexture(const u8 *src, int len, u32 samples);
u64 GetMurmurHash3(const u8 *src, int len, u32 samples);
u64 GetHash64(const u8 *src, int len, u32 samples);
void SetHash64Function(bool useHiresTextures);

#if _M_SSE >= 0x402

template <size_t Sz>
inline u32 GetCRC32_SmallSize(u64 cur, u8 const * b);

template <> inline u32 GetCRC32_SmallSize<0>(u64 cur, u8 const *) { return u32(cur); }

template <> inline u32 GetCRC32_SmallSize<1>(u64 cur, u8 const *b) { 
	u32 tmp = u32(cur);
	tmp = _mm_crc32_u8(tmp, *(u8 const *)(b+0));
	return tmp; 
}

template <> inline u32 GetCRC32_SmallSize<2>(u64 cur, u8 const *b) { 
	u32 tmp = u32(cur);
	tmp = _mm_crc32_u16(tmp, *(u16 const *)(b+0));
	return tmp; 
}

template <> inline u32 GetCRC32_SmallSize<3>(u64 cur, u8 const *b) { 
	u32 tmp = u32(cur);
	tmp = _mm_crc32_u16(tmp, *(u16 const *)(b+0));
	tmp = _mm_crc32_u8(tmp, *(u8 const *)(b+2));
	return tmp; 
}

template <> inline u32 GetCRC32_SmallSize<4>(u64 cur, u8 const *b) { 
	u32 tmp = u32(cur);
	tmp = _mm_crc32_u32(tmp, *(u32 const *)(b+0));
	return tmp; 
}

template <> inline u32 GetCRC32_SmallSize<5>(u64 cur, u8 const *b) { 
	u32 tmp = u32(cur);
	tmp = _mm_crc32_u32(tmp, *(u32 const *)(b+0));
	tmp = _mm_crc32_u8(tmp, *(u8 const *)(b+4));
	return tmp; 
}

template <> inline u32 GetCRC32_SmallSize<6>(u64 cur, u8 const *b) { 
	u32 tmp = u32(cur);
	tmp = _mm_crc32_u32(tmp, *(u32 const *)(b+0));
	tmp = _mm_crc32_u16(tmp, *(u16 const *)(b+4));
	return tmp; 
}

template <> inline u32 GetCRC32_SmallSize<7>(u64 cur, u8 const *b) { 
	u32 tmp = u32(cur);
	tmp = _mm_crc32_u32(tmp, *(u32 const *)(b+0));
	tmp = _mm_crc32_u16(tmp, *(u16 const *)(b+4));
	tmp = _mm_crc32_u8(tmp, *(u8 const *)(b+6));
	return tmp; 
}

template <> inline u32 GetCRC32_SmallSize<8>(u64 cur, u8 const *b) {
	return u32(_mm_crc32_u64(cur, *(u64*)b));
}

template <size_t Sz>
inline u32 GetCRC32_SmallSize(u64 cur, u8 const * b) {
	return GetCRC32_SmallSize<Sz-8>( _mm_crc32_u64(cur, *(u64*)b),b+8);
}

template <typename T>
u32 GetCRC32_CT(T const & st) {
	return GetCRC32_SmallSize<sizeof(st)>(sizeof(st), (u8 const*)&st);
#if 0
	u32 sz { sizeof(st) };
	u8 const * ptr{(u8 const *)&st};

	u64 crc{sz};

	while( sz >= 8 ) {
		crc = _mm_crc32_u64(crc, *(u64*)ptr);
		ptr += 8;
		sz -= 8;
	}
	u32 crc32 = u32(crc);
	if( sz >= 4 ) {
		crc32 = _mm_crc32_u32(crc32, *(u32*)ptr);
		ptr += 4;
		sz -= 4;
	}
	if( sz >= 2 ) {
		crc32 = _mm_crc32_u16(crc32, *(u16*)ptr);
		ptr += 2;
		sz -= 2;
	}
	if( sz ) {
		crc32 = _mm_crc32_u8(crc32, *(u8*)ptr);
	}
	
	return crc32;
#endif
}
#else 
u64 GetCRC32_CT(const u8 *src, int len) {
	return GetHash64(src,len, 0);
}
#endif