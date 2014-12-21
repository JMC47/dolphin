// Copyright 2013 Dolphin Emulator Project
// Licensed under GPLv2
// Refer to the license.txt file included.

#include "Core/HW/Memmap.h"
#include "VideoCommon/VideoConfig.h"
#include "VideoBackends/D3D/D3DPtr.h"
#include "VideoBackends/D3D/D3DBase.h"
#include "VideoBackends/D3D/D3DShader.h"
#include "VideoBackends/D3D/FramebufferManager.h"
#include "VideoBackends/D3D/GfxState.h"
#include "VideoBackends/D3D/PSTextureDecoder.h"
#include "VideoBackends/D3D/Render.h"
#include "VideoBackends/D3D/TextureCache.h"


namespace DX11
{


static const char DECODER_CS[] = R"HLSL(
//

Buffer<uint> rawData_ : register(t0);
Buffer<uint> lutData_ : register(t1);

RWTexture2D<uint4> dstTexture_ : register(u0);

static uint2 dims_;

uint ReadByte( uint addr ) {
	uint r = rawData_[addr>>2];

	return (r >> (8*(addr&0x3)))&0xff;
}

uint ReadTwoBytes( uint addr ) {
	uint r = rawData_[addr>>2];
	r = (r >> (16*((addr>>1)&0x1)))&0xffff;
	return ((r&0xff)<<8)| ((r&0xff00)>>8);
}

uint ReadFourBytes( uint addr ) {
	uint r = rawData_[addr>>2];
	
	return ((r&0xff)<<24) | ((r&0xff00)<<8) | ((r&0xff000000)>>24) | ((r&0xff0000)>>8);
}

uint ReadFourBytesNoSwap( uint addr ) {
	uint r = rawData_[addr>>2];
	
	return r;
}

#ifndef DECODER_FUNC
#error DECODER_FUNC not set
#endif

#ifndef LUT_FUNC
#error LUT_FUNC not set
#endif

uint4 Read5A3( uint v ) {
	if (v&0x8000) {
		uint r = (v&0x7C00)>>7; r |= r>>5;
		uint g = (v&0x03E0)>>2;	g |= g>>5;
		uint b = (v&0x001F)<<3;	b |= b>>5;
		return uint4(r,g,b,255);
	} else {
		uint a = (v&0x7000)>>7; a |= (a>>3) | (a>>6);
		uint r = (v&0x0F00)>>4; r |= r>>4;
		uint g = (v&0x00F0)>>0; g |= g>>4;
		uint b = (v&0x000F)<<4; b |= b>>4;
		return uint4(r,g,b,a);
	}
}

uint4 Read565( uint v ) {
	uint b = (v&0x1F)<<3; b |= b >> 5;
	uint g = (v&0x7E0)>>3; g |= g >> 6;
	uint r = (v&0xF800)>>8; r |= r >> 5;
  return uint4(r,g,b,255);
}


uint4 ReadLutIA8( uint idx ) {
	uint v = lutData_[idx];
	v = ((v&0xff)<<8)| ((v&0xff00)>>8);
	return uint4( uint(v&0xff).xxx, (v&0xff00)>>8 );
}

uint4 ReadLut565( uint idx ) {
	uint v = lutData_[idx];
	v = ((v&0xff)<<8)| ((v&0xff00)>>8);
  return Read565(v);
}

uint4 ReadLut5A3( uint idx ) {
	uint v = lutData_[idx];
	v = ((v&0xff)<<8)| ((v&0xff00)>>8);
	return Read5A3(v);
}

uint Decode2Nibbles( uint2 st ) {
	uint pitch = ((dims_.x+7)/8)*32;
	uint tile = (st.y/8) * pitch + 32 * (st.x/8);
  uint offs = (st.x&0x7) + (st.y&0x7)*4;
	return ReadByte( tile + offs );
}

uint Decode1Byte( uint2 st ) {
	uint pitch = ((dims_.x+7)/8)*32;
	uint tile = (st.y/4) * pitch + 32 * (st.x/8);
  uint offs = (st.x&0x7) + (st.y&0x3)*8;
	return ReadByte( tile + offs );
}

uint Decode2Bytes( uint2 st ) {
	uint pitch = ((dims_.x+3)/4)*32;
	uint tile = (st.y/4) * pitch + 32 * (st.x/4);
  uint offs = (st.x&0x3)*2 + (st.y&0x3)*8;
	return ReadTwoBytes( tile + offs );
}

uint4 DecodeI8( uint2 st ) {
	uint v = Decode1Byte( st);
  return v.xxxx;
}

uint4 DecodeC8( uint2 st ) {
	uint v = Decode1Byte(st);
	return LUT_FUNC(v);
}

uint4 DecodeC14( uint2 st ) {
	uint v = Decode1Byte(st);
	return LUT_FUNC(v&0x3FFF);
}

uint4 DecodeI4( uint2 st ) {
	uint sBlk = st.x >> 3;
	uint tBlk = st.y >> 3;
	uint widthBlks = ((dims_.x+7) >> 3);// + 1;
	uint base = (tBlk * widthBlks + sBlk) << 5;
	uint blkS = st.x & 7;
	uint blkT =  st.y & 7;
	uint blkOff = (blkT << 3) + blkS;

	uint rs = (blkOff & 1)?0:4;
	uint offset = base + (blkOff >> 1);

	uint v = ReadByte( offset );
	uint i = (blkOff&1) ? (v & 0x0F): ((v & 0xF0)>>4);
  i <<= 4;
	i |= (i>>4);
  return i.xxxx;
}
uint4 DecodeC4( uint2 st ) {
	uint sBlk = st.x >> 3;
	uint tBlk = st.y >> 3;
	uint widthBlks = ((dims_.x+7) >> 3);// + 1;
	uint base = (tBlk * widthBlks + sBlk) << 5;
	uint blkS = st.x & 7;
	uint blkT =  st.y & 7;
	uint blkOff = (blkT << 3) + blkS;

	uint rs = (blkOff & 1)?0:4;
	uint offset = base + (blkOff >> 1);

	uint v = ReadByte( offset );
	uint i = (blkOff&1) ? (v & 0x0F): ((v & 0xF0)>>4);

	return LUT_FUNC(i);
  //
}

uint4 Decode565( uint2 st ) {
	uint v = Decode2Bytes( st );
	return Read565(v);
}

uint4 DecodeIA8( uint2 st ) {
	uint v = Decode2Bytes( st );
	uint i = (v&0xFF);
	uint a = (v&0xFF00)>>8;
  return uint4(i.xxx,a);
}

uint4 NotImplemented( uint2 st ) {
	return uint4(uint(255).xx*st/dims_, 0,128 );
}

uint4 DecodeIA4( uint2 st ) {
  uint v = Decode1Byte( st );
	uint i = (v&0x0F)<<4; i |= (i>>4);
	uint a = (v&0xF0); a |= (a>>4);
  return uint4(i.xxx,a);
}



uint4 Decode5A3( uint2 st ) {
	uint v = Decode2Bytes( st );
	return Read5A3(v);
}

uint4 DecodeCmpr( uint2 st ) {
	uint pitch = ((dims_.x+7)/8)*32;
	uint tile = (st.y/8) * pitch + 32 * (st.x/8);

  uint2 pix = st & 0x7;
	uint offs = 8 * ( pix.x/4 ) + 16 * (pix.y/4);
  uint col0 = ReadTwoBytes( tile + offs + 0 );
  uint col1 = ReadTwoBytes( tile + offs + 2 );
  uint lut = ReadFourBytes( tile + offs + 4 );

  uint2 px = st & 0x3;
  uint idx = ( lut >> ( 32 - (px.x*2+2) - px.y*8 ) ) & 3;

	uint3 c0,c1;
	c0 = Read565(col0).rgb;
	c1 = Read565(col1).rgb;

	if ( col0<=col1 ) {
		// transparent case
		uint3 result = (idx&1) ? c1 : c0;
		if( idx == 2 ) {
			result = (c0+c1)>>1;
		}
		return uint4(result,idx==3 ? 0 : 255);
	} else {
		uint3 result = (idx&1) ? c1 : c0;
		if ( idx&2 ) {
			int3 delta = c1-c0;
			int3 tier = (delta>>1) - (delta >> 3);
			result = result + ( (idx&1) ? -tier : tier );
		}
		return uint4(result,255);
	}
}


uint4 DecodeRGBA8( uint2 st ) {
	uint pitch = ((dims_.x+3)/4)*64;
	uint tile = (st.y/4) * pitch + 64 * (st.x/4);
  uint offs = (st.x&0x3)*2 + (st.y&0x3)*8;

	uint ar = ReadTwoBytes( tile + offs );
	uint gb = ReadTwoBytes( tile + offs + 32);

	return uint4( (ar&0x00ff)>>0, (gb&0xff00)>>8, (gb&0x00ff)>>0, (ar&0xff00)>>8);
}

uint4 DecodeRGBA8FromTMEM( uint2 st ) {
	uint bgoffs = 2 * ((dims_.x+3)&~3) * ((dims_.y+3)&~3);
	uint pitch = ((dims_.x+3)/4)*32;
	uint tile = (st.y/4) * pitch + 32 * (st.x/4);
  uint offs = (st.x&0x3)*2 + (st.y&0x3)*8;

	uint ar = ReadTwoBytes( tile + offs );
	uint gb = ReadTwoBytes( tile + offs + bgoffs);

	return uint4( (ar&0x00ff)>>0, (gb&0xff00)>>8, (gb&0x00ff)>>0, (ar&0xff00)>>8);
}


#ifndef FMT
#error no fmt
#endif 
[numthreads(8,8,1)]
void main(in uint3 groupIdx : SV_GroupID, in uint3 subgroup : SV_GroupThreadID) {
	dstTexture_.GetDimensions(dims_.x,dims_.y);
	uint2 st = groupIdx.xy * 8 + subgroup.xy;
	//if( st.x <2 && st.y < 2 ){
	//	dstTexture_[st] = 128+uint(FMT);
	//} else 
	if ( all( st < dims_) ) {
		dstTexture_[st] = DECODER_FUNC( st ); 
	}
	
}
//
)HLSL";

void PSTextureDecoder::Init()
{
	m_ready = false;

		
	
	HRESULT hr;

	auto outBd = CD3D11_BUFFER_DESC(2<<20,D3D11_BIND_SHADER_RESOURCE);
	//outBd.MiscFlags |= D3D11_RESOURCE_MISC_BUFFER_ALLOW_RAW_VIEWS;
	hr = D3D::device->CreateBuffer(&outBd, nullptr, ToAddr(rawDataRsc_));
	CHECK(SUCCEEDED(hr), "create texture decoder input buffer");
	D3D::SetDebugObjectName(rawDataRsc_.get(), "texture decoder input buffer");
	auto outUavDesc = CD3D11_SHADER_RESOURCE_VIEW_DESC(rawDataRsc_.get(),DXGI_FORMAT_R32_UINT,0,(2<<20)/4,0/*D3D11_BUFFEREX_SRV_FLAG_RAW*/);
	hr = D3D::device->CreateShaderResourceView(rawDataRsc_.get(),&outUavDesc,ToAddr(rawDataSrv_));
	CHECK(SUCCEEDED(hr), "create texture decoder input buffer srv");
	D3D::SetDebugObjectName(rawDataSrv_.get(), "texture decoder input buffer srv");

	{
		u32 lutMaxEntries = (1<<15) - 1;
		auto outBd = CD3D11_BUFFER_DESC(sizeof(u16)*lutMaxEntries,D3D11_BIND_SHADER_RESOURCE);
		hr = D3D::device->CreateBuffer(&outBd, nullptr, ToAddr(lutRsc_));
		CHECK(SUCCEEDED(hr), "create texture decoder lut buffer");
		D3D::SetDebugObjectName(lutRsc_.get(), "texture decoder lut buffer");
		auto outUavDesc = CD3D11_SHADER_RESOURCE_VIEW_DESC(lutRsc_.get(),DXGI_FORMAT_R16_UINT,0,lutMaxEntries,0);
		hr = D3D::device->CreateShaderResourceView(lutRsc_.get(),&outUavDesc,ToAddr(lutSrv_));
		CHECK(SUCCEEDED(hr), "create texture decoder lut srv");
		D3D::SetDebugObjectName(lutSrv_.get(), "texture decoder lut srv");

	}

	m_ready = true;

	// Warm up with shader cache
	char cache_filename[MAX_PATH];
	sprintf(cache_filename, "%sdx11-PSDECODER-cs.cache", File::GetUserPath(D_SHADERCACHE_IDX).c_str());
	m_shaderCache.OpenAndRead(cache_filename, ShaderCacheInserter(*this));
	
}

void PSTextureDecoder::Shutdown()
{
	m_ready = false;

	
}


char const* DecFunc[] = {
"DecodeI4",//GX_TF_I4     = 0x0,
"DecodeI8",//GX_TF_I8     = 0x1,
"DecodeIA4",//GX_TF_IA4    = 0x2,
"DecodeIA8",//GX_TF_IA8    = 0x3,
"Decode565",//GX_TF_RGB565 = 0x4,
"Decode5A3",//GX_TF_RGB5A3 = 0x5,
"DecodeRGBA8",//GX_TF_RGBA8  = 0x6,
"NotImplemented",//
"DecodeC4",//GX_TF_C4     = 0x8,
"DecodeC8",//GX_TF_C8     = 0x9,
"DecodeC14",//GX_TF_C14X2  = 0xA,
"NotImplemented",//
"NotImplemented",//
"NotImplemented",//
"DecodeCmpr",//GX_TF_CMPR   = 0xE,
"DecodeRGBA8FromTMEM",//
};

char const* valType[] = {
"1",
"2",
"3",
"4",
"5",
"6",
"7",
"8",
"9",
"10",
"11",
"12",
"13",
"14",
"15",
"16",
};

char const* LutFunc[] = {
"ReadLutIA8",
"ReadLut565",
"ReadLut5A3",
};

bool PSTextureDecoder::SetStaticShader(TextureFormat srcFmt, u32 lutFmt, u32 dstFmt ) {
	//srcFmt = TextureFormat(0xd);

	u32 rawFmt = (u32(srcFmt)&0xF);
	if (rawFmt < GX_TF_C4 || rawFmt > GX_TF_C14X2 ) {
		lutFmt = 0;
	}
	auto key = MakeComboKey(srcFmt,lutFmt,dstFmt);

	auto it = m_staticShaders.find(key);

	if (it!=m_staticShaders.end()) {
		D3D::context->CSSetShader(it->second.get(),nullptr, 0);
		return bool(it->second);
	}

	// Shader permutation not found, so compile it
	
	D3D_SHADER_MACRO macros[] = {
			{ "DECODER_FUNC", DecFunc[u32(srcFmt) & 0xF] },
			{ "LUT_FUNC", LutFunc[u32(lutFmt) & 0xF] },
			{ "FMT", valType[u32(srcFmt) & 0xF] },
		{ nullptr, nullptr }
	};

	D3DBlob bytecode = nullptr;
	if (!D3D::CompileComputeShader(DECODER_CS, sizeof(DECODER_CS), bytecode, macros)) {
		WARN_LOG(VIDEO, "noooo");
	}

	m_shaderCache.Append(key, bytecode.Data(), u32(bytecode.Size()));

	auto & result = m_staticShaders[key];
	HRESULT hr = D3D::device->CreateComputeShader(bytecode.Data(), bytecode.Size(), nullptr, ToAddr(result) );
	CHECK(SUCCEEDED(hr), "create efb encoder pixel shader");
	D3D::context->CSSetShader(result.get(),nullptr, 0);

	return bool(result);
}

ID3D11ComputeShader* PSTextureDecoder::InsertShader( ComboKey const &key, u8 const *data, u32 sz) {
	auto & result = m_staticShaders[key];
	HRESULT hr = D3D::device->CreateComputeShader(data, sz, nullptr, ToAddr(result) );
	CHECK(SUCCEEDED(hr), "create efb encoder pixel shader");
	return result.get();
}

void PSTextureDecoder::LoadLut(u32 lutFmt, void* addr, u32 size ) {
	D3D11_BOX box{0,0,0,size,1,1};
	D3D::context->UpdateSubresource(lutRsc_.get(),0,&box,addr,0,0);
	lutFmt_ = lutFmt;
}
size_t PSTextureDecoder::Decode(u8* dst, u32 srcFmt, u32 w, u32 h, u32 level, D3DTexture2D& dstTexture, u32 dstFmt)
{
	if (!m_ready) // Make sure we initialized OK
		return 0;

	if (!SetStaticShader(TextureFormat(srcFmt),lutFmt_,0)) {
		return 0;
	}

	auto it = pool_.find( {0,w,h} );
	if ( it == pool_.end() ) {
		// create the pool texture here
		auto desc = CD3D11_TEXTURE2D_DESC(DXGI_FORMAT_R8G8B8A8_UINT,w,h,1,1,D3D11_BIND_UNORDERED_ACCESS);

		HRESULT hr;
		PoolValue val;
		hr = D3D::device->CreateTexture2D( &desc, nullptr, ToAddr(val.rsc_));
		CHECK(SUCCEEDED(hr), "create efb encoder pixel shader");

		hr = D3D::device->CreateUnorderedAccessView( val.rsc_.get(), nullptr, ToAddr(val.uav_));
		CHECK(SUCCEEDED(hr), "create efb encoder pixel shader");
		PoolKey key{0,w,h};
		it = pool_.emplace( key, std::move(val) ).first;
	}

	if (it != pool_.end()) {
		if(0&&srcFmt == 0) {
			std::vector<u8> dummy(TextureCache::src_temp_size);

			for(int i{};i!=dummy.size();++i) {
				dummy[i] = ((i/32)&0x1) ? 0xff : 0;
			}


			D3D11_BOX box{0,0,0,TextureCache::src_temp_size,1,1};
			D3D::context->UpdateSubresource(rawDataRsc_.get(),0,&box,dummy.data(),0,0);
		} else {
			D3D11_BOX box{0,0,0,TextureCache::src_temp_size,1,1};
			D3D::context->UpdateSubresource(rawDataRsc_.get(),0,&box,TextureCache::src_temp,0,0);
		}
		ID3D11UnorderedAccessView* uav = it->second.uav_.get();
		D3D::context->CSSetUnorderedAccessViews(0,1,&uav);

		ID3D11ShaderResourceView* srvs[] = { rawDataSrv_.get(), lutSrv_.get() };
		D3D::context->CSSetShaderResources(0,2, srvs);
		
		D3D::context->Dispatch( (w+7)/8, (h+7)/8, 1 );

		uav = nullptr;
		D3D::context->CSSetUnorderedAccessViews(0,1,&uav);
		D3D::context->CopySubresourceRegion( dstTexture.GetTex(),level,0,0,0,it->second.rsc_.get(), 0, nullptr );
	}

	return 0;
}

size_t PSTextureDecoder::DecodeRGBAFromTMEM( u8 const * ar_src, u8 const * bg_src, u32 w, u32 h, D3DTexture2D& dstTexture) {

	if (!m_ready) // Make sure we initialized OK
		return 0;

	if (!SetStaticShader(TextureFormat(0xf),0,0)) {
		return 0;
	}

	auto it = pool_.find( {0,w,h} );
	if ( it == pool_.end() ) {
		// create the pool texture here
		auto desc = CD3D11_TEXTURE2D_DESC(DXGI_FORMAT_R8G8B8A8_UINT,w,h,1,1,D3D11_BIND_UNORDERED_ACCESS);

		HRESULT hr;
		PoolValue val;
		hr = D3D::device->CreateTexture2D( &desc, nullptr, ToAddr(val.rsc_));
		CHECK(SUCCEEDED(hr), "create efb encoder pixel shader");

		hr = D3D::device->CreateUnorderedAccessView( val.rsc_.get(), nullptr, ToAddr(val.uav_));
		CHECK(SUCCEEDED(hr), "create efb encoder pixel shader");
		PoolKey key{0,w,h};
		it = pool_.emplace( key, std::move(val) ).first;
	}

	if (it != pool_.end()) {
		u32 aw = (w+4)&~4;
		u32 ah = (h+4)&~4;

		D3D11_BOX box{0,0,0,(aw*ah)<<1,1,1};
		D3D::context->UpdateSubresource(rawDataRsc_.get(),0,&box,ar_src,0,0);

		D3D11_BOX box2{(aw*ah)<<1,0,0,2*((aw*ah)<<1),1,1};
		D3D::context->UpdateSubresource(rawDataRsc_.get(),0,&box2,bg_src,0,0);

		ID3D11UnorderedAccessView* uav = it->second.uav_.get();
		D3D::context->CSSetUnorderedAccessViews(0,1,&uav);

		ID3D11ShaderResourceView* srvs[] = { rawDataSrv_.get() };
		D3D::context->CSSetShaderResources(0,1, srvs);
		
		D3D::context->Dispatch( (w+7)/8, (h+7)/8, 1 );

		uav = nullptr;
		D3D::context->CSSetUnorderedAccessViews(0,1,&uav);
		D3D::context->CopySubresourceRegion( dstTexture.GetTex(),0,0,0,0,it->second.rsc_.get(), 0, nullptr );
	}

	return 0;
}

}
