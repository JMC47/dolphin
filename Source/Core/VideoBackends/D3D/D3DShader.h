// Copyright 2013 Dolphin Emulator Project
// Licensed under GPLv2
// Refer to the license.txt file included.

#pragma once

#include "VideoBackends/D3D/D3DBase.h"
#include "VideoBackends/D3D/D3DBlob.h"

struct ID3D11PixelShader;
struct ID3D11VertexShader;

namespace DX11
{

namespace D3D
{
	enum class ShaderType : u32 {
		Vertex,
		Pixel,
		Geometry,
		Compute,
		//Hull,
		//Domain,
	};

	VertexShaderPtr CreateVertexShaderFromByteCode(const void* bytecode, size_t len);
	GeometryShaderPtr CreateGeometryShaderFromByteCode(const void* bytecode, size_t len);
	PixelShaderPtr CreatePixelShaderFromByteCode(const void* bytecode, size_t len);
	u32 ReflectTextureMask( const void* code, size_t len );

	// The returned bytecode buffers should be Release()d.
	bool CompileVertexShader(const char* code, size_t len,
		D3DBlob& blob);
	bool CompileGeometryShader(const char* code, size_t len,
		D3DBlob& blob, const D3D_SHADER_MACRO* pDefines = nullptr);
	bool CompilePixelShader(const char* code, size_t len,
		D3DBlob& blob, const D3D_SHADER_MACRO* pDefines = nullptr);
	bool CompileComputeShader(const char* code, size_t len,
		D3DBlob& blob, const D3D_SHADER_MACRO* pDefines = nullptr);

	bool CompileShader(ShaderType type, const char* code, size_t len,
		D3DBlob& blob, const D3D_SHADER_MACRO* pDefines = nullptr);

	// Utility functions
	VertexShaderPtr CompileAndCreateVertexShader(const char* code,
		size_t len);
	GeometryShaderPtr CompileAndCreateGeometryShader(const char* code,
		size_t len, const D3D_SHADER_MACRO* pDefines = nullptr);
	PixelShaderPtr CompileAndCreatePixelShader(const char* code,
		size_t len);
	ComputeShaderPtr CompileAndCreateComputeShader(const char* code,
		size_t len);

	inline VertexShaderPtr CreateVertexShaderFromByteCode(D3DBlob& bytecode)
	{ return CreateVertexShaderFromByteCode(bytecode.Data(), bytecode.Size()); }
	inline GeometryShaderPtr CreateGeometryShaderFromByteCode(D3DBlob& bytecode)
	{ return CreateGeometryShaderFromByteCode(bytecode.Data(), bytecode.Size()); }
	inline PixelShaderPtr CreatePixelShaderFromByteCode(D3DBlob& bytecode)
	{ return CreatePixelShaderFromByteCode(bytecode.Data(), bytecode.Size()); }

	inline VertexShaderPtr CompileAndCreateVertexShader(D3DBlob& code)
	{ return CompileAndCreateVertexShader((const char*)code.Data(), code.Size()); }
	inline GeometryShaderPtr CompileAndCreateGeometryShader(D3DBlob& code, const D3D_SHADER_MACRO* pDefines = nullptr)
	{ return CompileAndCreateGeometryShader((const char*)code.Data(), code.Size(), pDefines); }
	inline PixelShaderPtr CompileAndCreatePixelShader(D3DBlob& code)
	{ return CompileAndCreatePixelShader((const char*)code.Data(), code.Size()); }
}

}  // namespace DX11