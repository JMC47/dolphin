// Copyright 2013 Dolphin Emulator Project
// Licensed under GPLv2
// Refer to the license.txt file included.

#include <string>

#include "VideoBackends/D3D/D3DPtr.h"
#include "VideoBackends/D3D/D3DBase.h"
#include "VideoBackends/D3D/D3DShader.h"
#include "VideoCommon/VideoConfig.h"

namespace DX11
{

namespace D3D
{

// bytecode->shader
UniquePtr<ID3D11VertexShader> CreateVertexShaderFromByteCode(const void* bytecode, size_t len)
{
	UniquePtr<ID3D11VertexShader> v_shader;
	HRESULT hr = D3D::device->CreateVertexShader(bytecode, len, nullptr, ToAddr(v_shader) );
	if (FAILED(hr))
		return nullptr;

	return v_shader;
}

// code->bytecode
bool CompileVertexShader(const char* code, size_t len, D3DBlob& blob)
{
	ID3DBlobPtr shaderBuffer;
	ID3DBlobPtr errorBuffer;

#if defined(_DEBUG) || defined(DEBUGFAST)
	UINT flags = D3DCOMPILE_DEBUG|D3DCOMPILE_SKIP_OPTIMIZATION;
#else
	UINT flags =  D3DCOMPILE_OPTIMIZATION_LEVEL3|D3DCOMPILE_SKIP_VALIDATION;
#endif
	HRESULT hr = PD3DCompile(code, len, nullptr, nullptr, nullptr, "main", D3D::VertexShaderVersionString(),
							flags, 0, ToAddr(shaderBuffer), ToAddr(errorBuffer) );
	if (errorBuffer)
	{
		INFO_LOG(VIDEO, "Vertex shader compiler messages:\n%s\n",
			(const char*)errorBuffer->GetBufferPointer());
	}

	if (FAILED(hr))
	{
		static int num_failures = 0;
		char szTemp[MAX_PATH];
		sprintf(szTemp, "%sbad_vs_%04i.txt", File::GetUserPath(D_DUMP_IDX).c_str(), num_failures++);
		std::ofstream file;
		OpenFStream(file, szTemp, std::ios_base::out);
		file << code;
		file.close();

		PanicAlert("Failed to compile vertex shader!\nThis usually happens when trying to use Dolphin with an outdated GPU or integrated GPU like the Intel GMA series.\n\nIf you're sure this is Dolphin's error anyway, post the contents of %s along with this error message at the forums.\n\nDebug info (%s):\n%s",
						szTemp,
						D3D::VertexShaderVersionString(),
						(char*)errorBuffer->GetBufferPointer());

		blob = nullptr;
	}
	else
	{
		blob = std::move(shaderBuffer);
	}
	return SUCCEEDED(hr);
}

// bytecode->shader
UniquePtr<ID3D11GeometryShader> CreateGeometryShaderFromByteCode(const void* bytecode, size_t len)
{
	UniquePtr<ID3D11GeometryShader> g_shader;
	HRESULT hr = D3D::device->CreateGeometryShader(bytecode, len, nullptr, ToAddr(g_shader) );
	if (FAILED(hr))
		return nullptr;

	return g_shader;
}

// code->bytecode
bool CompileGeometryShader(const char* code, size_t len, D3DBlob& blob,
	const D3D_SHADER_MACRO* pDefines)
{
	ID3DBlobPtr shaderBuffer;
	ID3DBlobPtr errorBuffer;

#if defined(_DEBUG) || defined(DEBUGFAST)
	UINT flags = D3DCOMPILE_DEBUG|D3DCOMPILE_SKIP_OPTIMIZATION;
#else
	UINT flags = D3DCOMPILE_OPTIMIZATION_LEVEL3|D3DCOMPILE_SKIP_VALIDATION;
#endif
	HRESULT hr = PD3DCompile(code, len, nullptr, pDefines, nullptr, "main", D3D::GeometryShaderVersionString(),
							flags, 0, ToAddr(shaderBuffer), ToAddr(errorBuffer) );

	if (errorBuffer)
	{
		INFO_LOG(VIDEO, "Geometry shader compiler messages:\n%s\n",
			(const char*)errorBuffer->GetBufferPointer());
	}

	if (FAILED(hr))
	{
		static int num_failures = 0;
		char szTemp[MAX_PATH];
		sprintf(szTemp, "%sbad_gs_%04i.txt", File::GetUserPath(D_DUMP_IDX).c_str(), num_failures++);
		std::ofstream file;
		OpenFStream(file, szTemp, std::ios_base::out);
		file << code;
		file.close();

		PanicAlert("Failed to compile geometry shader!\nThis usually happens when trying to use Dolphin with an outdated GPU or integrated GPU like the Intel GMA series.\n\nIf you're sure this is Dolphin's error anyway, post the contents of %s along with this error message at the forums.\n\nDebug info (%s):\n%s",
						szTemp,
						D3D::GeometryShaderVersionString(),
						(char*)errorBuffer->GetBufferPointer());

		blob = nullptr;
		
	}
	else
	{
		blob = std::move(shaderBuffer);
	}
	return SUCCEEDED(hr);
}

// bytecode->shader
UniquePtr<ID3D11PixelShader> CreatePixelShaderFromByteCode(const void* bytecode, size_t len)
{
	UniquePtr<ID3D11PixelShader> p_shader;
	HRESULT hr = D3D::device->CreatePixelShader(bytecode, len, nullptr, ToAddr(p_shader) );
	if (FAILED(hr))
	{
		PanicAlert("CreatePixelShaderFromByteCode failed at %s %d\n", __FILE__, __LINE__);
	}
	return p_shader;
}

u32 ReflectTextureMask( const void* code, size_t len ) {
	UniquePtr<ID3D11ShaderReflection> reflect;
	PD3DReflect( code, len, IID_ID3D11ShaderReflection, ToAddr(reflect) );
	if (!reflect)
		return u32(-1);

	u32 mask = 0;
	D3D11_SHADER_DESC desc;
	reflect->GetDesc( &desc );

	for( int i{}; i != desc.BoundResources; ++i ) {
		D3D11_SHADER_INPUT_BIND_DESC idesc;
		reflect->GetResourceBindingDesc(i, &idesc );
		if( idesc.Type == D3D_SIT_TEXTURE) {
			mask |= 1 << idesc.BindPoint;
		}
	}
	return mask;
};
// code->bytecode
bool CompilePixelShader(const char* code, size_t len, D3DBlob& blob,
	const D3D_SHADER_MACRO* pDefines)
{
	ID3DBlobPtr shaderBuffer;
	ID3DBlobPtr errorBuffer;

#if defined(_DEBUG) || defined(DEBUGFAST)
	UINT flags = D3DCOMPILE_DEBUG|D3DCOMPILE_SKIP_OPTIMIZATION;
#else
	UINT flags = D3DCOMPILE_OPTIMIZATION_LEVEL3;
#endif
	HRESULT hr = PD3DCompile(code, len, nullptr, pDefines, nullptr, "main", D3D::PixelShaderVersionString(),
							flags, 0, ToAddr(shaderBuffer), ToAddr(errorBuffer) );

	if (errorBuffer)
	{
		INFO_LOG(VIDEO, "Pixel shader compiler messages:\n%s",
			(const char*)errorBuffer->GetBufferPointer());
	}

	if (FAILED(hr))
	{
		static int num_failures = 0;
		char szTemp[MAX_PATH];
		sprintf(szTemp, "%sbad_ps_%04i.txt", File::GetUserPath(D_DUMP_IDX).c_str(), num_failures++);
		std::ofstream file;
		OpenFStream(file, szTemp, std::ios_base::out);
		file << code;
		file.close();

		PanicAlert("Failed to compile pixel shader!\nThis usually happens when trying to use Dolphin with an outdated GPU or integrated GPU like the Intel GMA series.\n\nIf you're sure this is Dolphin's error anyway, post the contents of %s along with this error message at the forums.\n\nDebug info (%s):\n%s",
						szTemp,
						D3D::PixelShaderVersionString(),
						(char*)errorBuffer->GetBufferPointer());

		blob = nullptr;
	}
	else
	{
		blob = std::move(shaderBuffer);
	}

	return SUCCEEDED(hr);
}

bool CompileComputeShader(const char* code, size_t len, D3DBlob& blob,
	const D3D_SHADER_MACRO* pDefines)
{
	ID3DBlobPtr shaderBuffer;
	ID3DBlobPtr errorBuffer;

#if defined(_DEBUG) || defined(DEBUGFAST)
	UINT flags = D3DCOMPILE_DEBUG|D3DCOMPILE_SKIP_OPTIMIZATION;
#else
	UINT flags = D3DCOMPILE_OPTIMIZATION_LEVEL3;
#endif
	HRESULT hr = PD3DCompile(code, len, nullptr, pDefines, nullptr, "main", D3D::ComputeShaderVersionString(),
							flags, 0, ToAddr(shaderBuffer), ToAddr(errorBuffer) );

	if (errorBuffer)
	{
		INFO_LOG(VIDEO, "Pixel shader compiler messages:\n%s",
			(const char*)errorBuffer->GetBufferPointer());
	}

	if (FAILED(hr))
	{
		static int num_failures = 0;
		char szTemp[MAX_PATH];
		sprintf(szTemp, "%sbad_cs_%04i.txt", File::GetUserPath(D_DUMP_IDX).c_str(), num_failures++);
		std::ofstream file;
		OpenFStream(file, szTemp, std::ios_base::out);
		file << code;
		file.close();

		PanicAlert("Failed to compile pixel shader!\nThis usually happens when trying to use Dolphin with an outdated GPU or integrated GPU like the Intel GMA series.\n\nIf you're sure this is Dolphin's error anyway, post the contents of %s along with this error message at the forums.\n\nDebug info (%s):\n%s",
						szTemp,
						D3D::ComputeShaderVersionString(),
						(char*)errorBuffer->GetBufferPointer());

		blob = nullptr;
	}
	else
	{
		blob =  std::move(shaderBuffer);
	}

	return SUCCEEDED(hr);
}
/*
struct ShaderException {
	D3DBlob
};

struct CallerSite {
	char const * file_;
	u32 line_;
	char const * func_;
};

#define CALLERSITE CallerSite{__FILE__, __LINE__, __FUNC__ }
D3DBlob CompileShader(ShaderType type, const char* code, size_t len, D3D_SHADER_MACRO const* pDefines)
{

	char const *profile{};
	switch (type) {
	case DX11::D3D::ShaderType::Vertex:
		profile = D3D::VertexShaderVersionString();
		break;
	case DX11::D3D::ShaderType::Pixel:
		profile = D3D::PixelShaderVersionString();
		break;
	case DX11::D3D::ShaderType::Geometry:
		profile = D3D::GeometryShaderVersionString();
		break;
	case DX11::D3D::ShaderType::Compute:
		profile = D3D::ComputeShaderVersionString();
		break;
	default:
		return false;
		break;
	}

#if defined(_DEBUG) || defined(DEBUGFAST)
	UINT flags = D3DCOMPILE_DEBUG|D3DCOMPILE_SKIP_OPTIMIZATION;
#else
	UINT flags = D3DCOMPILE_OPTIMIZATION_LEVEL3;
#endif

	ID3DBlobPtr shaderBuffer;
	ID3DBlobPtr errorBuffer;
	HRESULT hr = PD3DCompile(code, len, nullptr, pDefines, nullptr, "main", profile,
							flags, 0, ToAddr(shaderBuffer), ToAddr(errorBuffer) );

	if (errorBuffer)
	{
		INFO_LOG(VIDEO, "Pixel shader compiler messages:\n%s",
			(const char*)errorBuffer->GetBufferPointer());
	}

	if (FAILED(hr))
	{
		static int num_failures = 0;
		char szTemp[MAX_PATH];
		sprintf(szTemp, "%sbad_cs_%04i.txt", File::GetUserPath(D_DUMP_IDX).c_str(), num_failures++);
		std::ofstream file;
		OpenFStream(file, szTemp, std::ios_base::out);
		file << code;
		file.close();

		PanicAlert("Failed to compile pixel shader!\nThis usually happens when trying to use Dolphin with an outdated GPU or integrated GPU like the Intel GMA series.\n\nIf you're sure this is Dolphin's error anyway, post the contents of %s along with this error message at the forums.\n\nDebug info (%s):\n%s",
						szTemp,
						D3D::ComputeShaderVersionString(),
						(char*)errorBuffer->GetBufferPointer());

		blob = nullptr;
	}
	else
	{
		blob =  std::move(shaderBuffer);
	}

	return SUCCEEDED(hr);
}
*/


UniquePtr<ID3D11VertexShader> CompileAndCreateVertexShader(const char* code,
	size_t len)
{
	D3DBlob blob;
	if (CompileVertexShader(code, len, blob))
	{
		return CreateVertexShaderFromByteCode(blob);
	}
	return nullptr;
}

UniquePtr<ID3D11GeometryShader> CompileAndCreateGeometryShader(const char* code,
	size_t len, const D3D_SHADER_MACRO* pDefines)
{
	D3DBlob blob;
	if (CompileGeometryShader(code, len, blob, pDefines))
	{
		return CreateGeometryShaderFromByteCode(blob);
	}
	return nullptr;
}

UniquePtr<ID3D11PixelShader> CompileAndCreatePixelShader(const char* code,
	size_t len)
{
	D3DBlob blob;
	if (CompilePixelShader(code, len, blob))
	{
		return CreatePixelShaderFromByteCode(blob);
	}
	return nullptr;
}

}  // namespace

}  // namespace DX11
