// Copyright 2013 Dolphin Emulator Project
// Licensed under GPLv2
// Refer to the license.txt file included.

#pragma once

#include <map>
#include "Common/LinearDiskCache.h"
#include "VideoBackends/D3D/D3DPtr.h"
#include "VideoBackends/D3D/TextureCache.h"


namespace DX11
{

class PSTextureDecoder : public TextureDecoder
{

public:

	PSTextureDecoder() = default;

	void Init() override;
	void Shutdown() override;
	size_t Decode(u8* dst, u32 srcFmt, u32 w, u32 h, u32 levels, D3DTexture2D& dstTexture, u32 dstFmt) override;
	size_t DecodeRGBAFromTMEM( u8 const * ar_src, u8 const * bg_src, u32 width, u32 height, D3DTexture2D& dstTexture) override;
	void LoadLut(u32 lutFmt, void* addr, u32 size ) override;
private:

	bool m_ready{};

	D3D::BufferPtr m_in; // dynamic to fill with the raw texture
	//D3D::UniquePtr<ID3D11Buffer> m_outStage;

	struct PoolKey {
		u32 dstFmt;
		u32 w_;
		u32 h_;
		bool operator<(PoolKey const & o) const {
			return dstFmt < o.dstFmt 
				|| dstFmt == o.dstFmt && w_ < o.w_
				|| dstFmt == o.dstFmt && w_ == o.w_ && h_ < o.h_;
		}
	};

	struct PoolValue {
		D3D::Texture2dPtr rsc_;
		D3D::UavPtr uav_;
		PoolValue() = default;
		PoolValue( PoolValue && o) : rsc_{std::move(o.rsc_)}, uav_{std::move(o.uav_)} {}
	};

	using TexturePool = std::map<PoolKey,PoolValue>;
	TexturePool pool_;

	

	//D3D::UniquePtr<ID3D11Buffer> m_encodeParams;

	// Stuff only used in static-linking mode (SM4.0-compatible)

	bool InitStaticMode();
	bool SetStaticShader(TextureFormat srcFmt, u32 lutFmt, u32 dstFmt);

	typedef unsigned int ComboKey; // Key for a shader combination

	ID3D11ComputeShader* InsertShader( ComboKey const &key, u8 const *data, u32 sz);

	ComboKey MakeComboKey(TextureFormat srcFmt, u32 lutFmt, u32 dstFmt)
	{
		u32 rawFmt = (u32(srcFmt)&0xF);
		return rawFmt | ((lutFmt&0xF)<<16);
	}

	typedef std::map<ComboKey, D3D::ComputeShaderPtr> ComboMap;

	D3D::BufferPtr rawDataRsc_;
	D3D::SrvPtr rawDataSrv_;

	D3D::BufferPtr lutRsc_;
	D3D::SrvPtr lutSrv_;
	u32 lutFmt_{};

	D3D::BufferPtr parms_;

	ComboMap m_staticShaders;

	class ShaderCacheInserter : public LinearDiskCacheReader<ComboKey, u8>
	{
	public:
		void Read(const ComboKey &key, const u8 *value, u32 value_size)
		{
			//encoder_.InsertShader(key, value, value_size);
		}
		ShaderCacheInserter(PSTextureDecoder &encoder) : encoder_(encoder) {}
	private:
		PSTextureDecoder& encoder_;
	};
	friend ShaderCacheInserter;

	LinearDiskCache<ComboKey, u8> m_shaderCache;

};

}
