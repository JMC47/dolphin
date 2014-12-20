// Copyright 2013 Dolphin Emulator Project
// Licensed under GPLv2
// Refer to the license.txt file included.

#include "VideoBackends/D3D/D3DBase.h"
#include "VideoBackends/D3D/PixelShaderCache.h"
#include "VideoBackends/D3D/Render.h"
#include "VideoBackends/D3D/VertexManager.h"
#include "VideoBackends/D3D/VertexShaderCache.h"

#include "VideoCommon/BPMemory.h"
#include "VideoCommon/Debugger.h"
#include "VideoCommon/IndexGenerator.h"
#include "VideoCommon/MainBase.h"
#include "VideoCommon/PixelShaderManager.h"
#include "VideoCommon/RenderBase.h"
#include "VideoCommon/Statistics.h"
#include "VideoCommon/TextureCacheBase.h"
#include "VideoCommon/VertexShaderManager.h"
#include "VideoCommon/VideoConfig.h"

// internal state for loading vertices
extern NativeVertexFormat *g_nativeVertexFmt;

namespace DX11
{

//TODO: test if it really change something
// Src may be unaligned, Dst and Size have to be aligned on 16
void Memcpy16( void* dst_raw, void const *src_raw, unsigned int size ) {
	size >>= 4;
	__m128* dst = (__m128*)dst_raw;
	__m128 const * src = (__m128*)src_raw;

	unsigned int remainder = size & 0x7;
	unsigned int loop = size >> 3;
	while (loop) {
		_mm_prefetch((char const *)(src+4),_MM_HINT_NTA);
		_mm_prefetch((char const *)(src+8),_MM_HINT_NTA);
		__m128 s0 = _mm_loadu_ps((float const*)(src+0));
		__m128 s1 = _mm_loadu_ps((float const*)(src+1));
		__m128 s2 = _mm_loadu_ps((float const*)(src+2));
		__m128 s3 = _mm_loadu_ps((float const*)(src+3));
		__m128 s4 = _mm_loadu_ps((float const*)(src+4));
		__m128 s5 = _mm_loadu_ps((float const*)(src+5));
		__m128 s6 = _mm_loadu_ps((float const*)(src+6));
		__m128 s7 = _mm_loadu_ps((float const*)(src+7));
		_mm_stream_ps((float*)(dst+0),s0);
		_mm_stream_ps((float*)(dst+1),s1);
		_mm_stream_ps((float*)(dst+2),s2);
		_mm_stream_ps((float*)(dst+3),s3);
		_mm_stream_ps((float*)(dst+4),s4);
		_mm_stream_ps((float*)(dst+5),s5);
		_mm_stream_ps((float*)(dst+6),s6);
		_mm_stream_ps((float*)(dst+7),s7);
		src+=8;
		dst+=8;
		--loop;
	}
	while (remainder) {
		__m128 a = _mm_loadu_ps((float const*)(src++));
		_mm_stream_ps((float*)(dst++),a);
		--remainder;
	}
}

// TODO: Find sensible values for these two
const UINT IBUFFER_SIZE = VertexManager::MAXIBUFFERSIZE* sizeof(u16) * 8;
const UINT VBUFFER_SIZE = 4u<<20u;//VertexManager::MAXVBUFFERSIZE;

void VertexManager::CreateDeviceObjects()
{
	CD3D11_BUFFER_DESC bufdesc(VBUFFER_SIZE, D3D11_BIND_VERTEX_BUFFER|D3D11_BIND_INDEX_BUFFER, 
	                           D3D11_USAGE_DYNAMIC, D3D11_CPU_ACCESS_WRITE);

	for ( auto &p : m_buffers)
	{
		p = nullptr;
		CHECK(SUCCEEDED(D3D::device->CreateBuffer(&bufdesc, nullptr, &p)),
		"Failed to create index buffer.");
		D3D::SetDebugObjectName((ID3D11DeviceChild*)p, "index buffer of VertexManager");
	}

	m_currentBuffer = u32(m_buffers.size())-1;
	
	m_bufferCursor = VBUFFER_SIZE;
	m_lineAndPointShader.Init();
}

void VertexManager::DestroyDeviceObjects()
{
	m_lineAndPointShader.Shutdown();
	for ( auto& p : m_buffers)
		SAFE_RELEASE(p);
}

VertexManager::VertexManager()
{
	//TODO:Fix MAXVBUFFERSIZE versus VBUFFER_SIZE and check overflow system in Common
	LocalVBuffer.resize(MAXVBUFFERSIZE+16);
	s_pCurBufferPointer = s_pBaseBufferPointer = LocalVBuffer.data()+16;
	s_pEndBufferPointer = LocalVBuffer.data() + LocalVBuffer.size();

	LocalIBuffer.resize(MAXIBUFFERSIZE);

	CreateDeviceObjects();
}

VertexManager::~VertexManager()
{
	DestroyDeviceObjects();
}

void VertexManager::PrepareDrawBuffers(u32 stride)
{
	UINT vSize = UINT(s_pCurBufferPointer - s_pBaseBufferPointer);
	UINT iSize = IndexGenerator::GetIndexLen() * sizeof(u16);

	u32 cursor = m_bufferCursor;
	if ( u32 padding = (cursor % stride) )
		cursor += stride - padding;

	cursor += vSize;

	cursor = (cursor+0xf) & ~0xf;

	cursor += iSize;

	if ( u32 padding = (cursor % 16) )
		cursor += 16 - padding;

		
	auto mapType = D3D11_MAP_WRITE_NO_OVERWRITE;
	if ( cursor > VBUFFER_SIZE ) {
		m_currentBuffer = (m_currentBuffer + 1) % m_buffers.size();
		m_bufferCursor = 0;
		mapType = D3D11_MAP_WRITE_DISCARD;
	}

	auto vbstart = m_bufferCursor;
	if ( u32 padding = (vbstart % stride) )
		vbstart += stride - padding;
	auto vbAlignedStart = vbstart & ~0xf;
	auto vbend = vbstart + vSize;
	vbend = (vbend+0xf) & ~0xf;

	D3D11_MAPPED_SUBRESOURCE map;
	auto hr = D3D::context->Map(m_buffers[m_currentBuffer], 0, mapType, 0, &map);

	if( hr != S_OK ) {
		PanicAlert("unable to lock the VB/IB buffer, prepare to see garbage on screen" );
		return;
	}

	D3D11_BOX vbSrcBox { vbAlignedStart, 0, 0, vbend, 1, 1 };
	Memcpy16((u8*)map.pData + vbSrcBox.left, s_pBaseBufferPointer-(vbstart-vbAlignedStart), vbSrcBox.right - vbSrcBox.left );
	
	D3D11_BOX ibSrcBox { vbend, 0, 0, (vbend + iSize + 0xF) & ~0xf, 1, 1 };
	Memcpy16((u8*)map.pData + ibSrcBox.left, GetIndexBuffer(), ibSrcBox.right - ibSrcBox.left );

	D3D::context->Unmap(m_buffers[m_currentBuffer], 0);
	
	m_bufferCursor = ibSrcBox.right;
	m_vertexDrawOffset = vbstart/stride;
	m_indexDrawOffset = ibSrcBox.left / 2;

	ADDSTAT(stats.thisFrame.bytesVertexStreamed, vbSrcBox.right - vbSrcBox.left);
	ADDSTAT(stats.thisFrame.bytesIndexStreamed, ibSrcBox.right - ibSrcBox.left);
}

static const float LINE_PT_TEX_OFFSETS[8] = {
	0.f, 0.0625f, 0.125f, 0.25f, 0.5f, 1.f, 1.f, 1.f
};

void VertexManager::Draw(UINT stride)
{

	u32 zero{};
	D3D::context->IASetVertexBuffers(0, 1, &m_buffers[m_currentBuffer], &stride, &zero);
	D3D::context->IASetIndexBuffer(m_buffers[m_currentBuffer], DXGI_FORMAT_R16_UINT, 0);

	if (current_primitive_type == PRIMITIVE_TRIANGLES)
	{
		auto pt = g_ActiveConfig.backend_info.bSupportsPrimitiveRestart ? 
		          D3D11_PRIMITIVE_TOPOLOGY_TRIANGLESTRIP : 
		          D3D11_PRIMITIVE_TOPOLOGY_TRIANGLELIST;
		D3D::context->IASetPrimitiveTopology(pt);
		D3D::context->GSSetShader(nullptr, nullptr, 0);
		D3D::context->DrawIndexed(IndexGenerator::GetIndexLen(), m_indexDrawOffset, m_vertexDrawOffset);
		INCSTAT(stats.thisFrame.numIndexedDrawCalls);
	}
	else if (current_primitive_type == PRIMITIVE_LINES)
	{
		float lineWidth = float(bpmem.lineptwidth.linesize) / 6.f;
		float texOffset = LINE_PT_TEX_OFFSETS[bpmem.lineptwidth.lineoff];
		float vpWidth = 2.0f * xfmem.viewport.wd;
		float vpHeight = -2.0f * xfmem.viewport.ht;

		bool texOffsetEnable[8];

		for (int i = 0; i < 8; ++i)
			texOffsetEnable[i] = bpmem.texcoords[i].s.line_offset;

		if (m_lineAndPointShader.SetLineShader(g_nativeVertexFmt->m_components, lineWidth,
			texOffset, vpWidth, vpHeight, texOffsetEnable))
		{
			((DX11::Renderer*)g_renderer)->ApplyCullDisable(); // Disable culling for lines and points
			D3D::context->IASetPrimitiveTopology(D3D11_PRIMITIVE_TOPOLOGY_LINELIST);
			D3D::context->DrawIndexed(IndexGenerator::GetIndexLen(), m_indexDrawOffset, m_vertexDrawOffset);
			INCSTAT(stats.thisFrame.numIndexedDrawCalls);

			((DX11::Renderer*)g_renderer)->RestoreCull();
		}
	}
	else //if (current_primitive_type == PRIMITIVE_POINTS)
	{
		float pointSize = float(bpmem.lineptwidth.pointsize) / 6.f;
		float texOffset = LINE_PT_TEX_OFFSETS[bpmem.lineptwidth.pointoff];
		float vpWidth = 2.0f * xfmem.viewport.wd;
		float vpHeight = -2.0f * xfmem.viewport.ht;

		bool texOffsetEnable[8];

		for (int i = 0; i < 8; ++i)
			texOffsetEnable[i] = bpmem.texcoords[i].s.point_offset;

		if (m_lineAndPointShader.SetPointShader(g_nativeVertexFmt->m_components, pointSize,
			texOffset, vpWidth, vpHeight, texOffsetEnable))
		{
			((DX11::Renderer*)g_renderer)->ApplyCullDisable(); // Disable culling for lines and points
			D3D::context->IASetPrimitiveTopology(D3D11_PRIMITIVE_TOPOLOGY_POINTLIST);
			D3D::context->DrawIndexed(IndexGenerator::GetIndexLen(), m_indexDrawOffset, m_vertexDrawOffset);
			INCSTAT(stats.thisFrame.numIndexedDrawCalls);

			((DX11::Renderer*)g_renderer)->RestoreCull();
		}
	}
}

void VertexManager::vFlush(bool useDstAlpha)
{
/*
	// TODO: Only do this if triangles are being used.
	// TODO: Is it nice that we're assuming that first 4 bytes == position? o_o
	float vtx[9], out[9];
	u8* vtx_ptr = (u8*)&GetVertexBuffer()[GetTriangleIndexBuffer()[IndexGenerator::GetNumTriangles()*3 - 1] * g_nativeVertexFmt->GetVertexStride()];
	for (unsigned int i = 0; i < 3; ++i)
	{
		vtx[0 + i * 3] = ((float*)vtx_ptr)[0];
		vtx[1 + i * 3] = ((float*)vtx_ptr)[1];
		vtx[2 + i * 3] = ((float*)vtx_ptr)[2];
		VertexLoader::TransformVertex(&vtx[i*3], &out[i*3]);
		vtx_ptr += g_nativeVertexFmt->GetVertexStride();
	}

	float fltx1 = out[0];
	float flty1 = out[1];
	float fltdx31 = out[6] - fltx1;
	float fltdx12 = fltx1 - out[3];
	float fltdy12 = flty1 - out[4];
	float fltdy31 = out[7] - flty1;

	float DF31 = vtx[8] - vtx[2];
	float DF21 = vtx[5] - vtx[2];

	float a = DF31 * -fltdy12 - DF21 * fltdy31;
	float b = fltdx31 * DF21 + fltdx12 * DF31;
	float c = -fltdx12 * fltdy31 - fltdx31 * -fltdy12;

	float slope_dfdx = -a / c;
	float slope_dfdy = -b / c;
	float slope_f0 = vtx[2];

	if (!bpmem.genMode.zfreeze)
		PixelShaderManager::SetZSlope(slope_dfdx, slope_dfdy, slope_f0);
*/
	if (IndexGenerator::GetIndexLen()== 4149) {
	//	__debugbreak();
		NOTICE_LOG(VIDEO,"");
	}

	if (!PixelShaderCache::SetShader(
		useDstAlpha ? DSTALPHA_DUAL_SOURCE_BLEND : DSTALPHA_NONE,
		g_nativeVertexFmt->m_components))
	{
		GFX_DEBUGGER_PAUSE_LOG_AT(NEXT_ERROR,true,{printf("Fail to set pixel shader\n");});
		return;
	}
	if (!VertexShaderCache::SetShader(g_nativeVertexFmt->m_components))
	{
		GFX_DEBUGGER_PAUSE_LOG_AT(NEXT_ERROR,true,{printf("Fail to set pixel shader\n");});
		return;
	}

	FlushTextures(PixelShaderCache::GetActiveMask());

	unsigned int stride = g_nativeVertexFmt->GetVertexStride();
	PrepareDrawBuffers(stride);
	g_nativeVertexFmt->SetupVertexPointers();
	g_renderer->ApplyState(useDstAlpha);
	//if (bpmem.genMode.zfreeze == 0)
		Draw(stride);

	g_renderer->RestoreState();
}

void VertexManager::ResetBuffer(u32 stride)
{
	s_pCurBufferPointer = s_pBaseBufferPointer;
	IndexGenerator::Start(GetIndexBuffer());
}

}  // namespace
