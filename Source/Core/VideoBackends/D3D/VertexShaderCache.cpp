// Copyright 2013 Dolphin Emulator Project
// Licensed under GPLv2
// Refer to the license.txt file included.

#include "Common/FileUtil.h"
#include "Common/LinearDiskCache.h"

#include "Core/ConfigManager.h"

#include "VideoBackends/D3D/D3DShader.h"
#include "VideoBackends/D3D/Globals.h"
#include "VideoBackends/D3D/VertexShaderCache.h"

#include "VideoCommon/Debugger.h"
#include "VideoCommon/Statistics.h"
#include "VideoCommon/VertexShaderGen.h"
#include "VideoCommon/VertexShaderManager.h"

namespace DX11 {

VertexShaderCache::VSCache VertexShaderCache::vshaders;
const VertexShaderCache::VSCacheEntry *VertexShaderCache::last_entry;
VertexShaderUid VertexShaderCache::last_uid;
UidChecker<VertexShaderUid,VertexShaderCode> VertexShaderCache::vertex_uid_checker;

static D3D::UniquePtr<ID3D11VertexShader> SimpleVertexShader;
static D3D::UniquePtr<ID3D11VertexShader> ClearVertexShader;
static D3D::UniquePtr<ID3D11InputLayout> SimpleLayout;
static D3D::UniquePtr<ID3D11InputLayout> ClearLayout;

LinearDiskCache<VertexShaderUid, u8> g_vs_disk_cache;

ID3D11VertexShader* VertexShaderCache::GetSimpleVertexShader() { return SimpleVertexShader.get(); }
ID3D11VertexShader* VertexShaderCache::GetClearVertexShader() { return ClearVertexShader.get(); }
ID3D11InputLayout* VertexShaderCache::GetSimpleInputLayout() { return SimpleLayout.get(); }
ID3D11InputLayout* VertexShaderCache::GetClearInputLayout() { return ClearLayout.get(); }

ID3D11Buffer* vscbuf = nullptr;

ID3D11Buffer* &VertexShaderCache::GetConstantBuffer()
{
	// TODO: divide the global variables of the generated shaders into about 5 constant buffers to speed this up
	if (VertexShaderManager::dirty)
	{
		D3D::context->UpdateSubresource(vscbuf,0,nullptr, &VertexShaderManager::constants, sizeof(VertexShaderConstants),0);
		VertexShaderManager::dirty = false;

		ADDSTAT(stats.thisFrame.bytesUniformStreamed, sizeof(VertexShaderConstants));
	}
	return vscbuf;
}

// this class will load the precompiled shaders into our cache
class VertexShaderCacheInserter : public LinearDiskCacheReader<VertexShaderUid, u8>
{
public:
	void Read(const VertexShaderUid &key, const u8 *value, u32 value_size)
	{
		VertexShaderCache::InsertByteCode( key, D3DBlob(value_size, value) );
	}
};

const char simple_shader_code[] = {
	"struct VSOUTPUT\n"
	"{\n"
	"float4 vPosition : SV_Position;\n"
	"float2 vTexCoord : TEXCOORD0;\n"
	"float  vTexCoord1 : TEXCOORD1;\n"
	"};\n"
	"VSOUTPUT main(float4 inPosition : POSITION,float3 inTEX0 : TEXCOORD0)\n"
	"{\n"
	"VSOUTPUT OUT;\n"
	"OUT.vPosition = inPosition;\n"
	"OUT.vTexCoord = inTEX0.xy;\n"
	"OUT.vTexCoord1 = inTEX0.z;\n"
	"return OUT;\n"
	"}\n"
};

const char clear_shader_code[] = {
	"struct VSOUTPUT\n"
	"{\n"
	"float4 vPosition   : SV_Position;\n"
	"float4 vColor0   : COLOR0;\n"
	"};\n"
	"VSOUTPUT main(float4 inPosition : POSITION,float4 inColor0: COLOR0)\n"
	"{\n"
	"VSOUTPUT OUT;\n"
	"OUT.vPosition = inPosition;\n"
	"OUT.vColor0 = inColor0;\n"
	"return OUT;\n"
	"}\n"
};

void VertexShaderCache::Init()
{
	const D3D11_INPUT_ELEMENT_DESC simpleelems[2] =
	{
		{ "POSITION", 0, DXGI_FORMAT_R32G32B32_FLOAT, 0,  0, D3D11_INPUT_PER_VERTEX_DATA, 0 },
		{ "TEXCOORD", 0, DXGI_FORMAT_R32G32B32_FLOAT, 0, 12, D3D11_INPUT_PER_VERTEX_DATA, 0 },

	};
	const D3D11_INPUT_ELEMENT_DESC clearelems[2] =
	{
		{ "POSITION", 0, DXGI_FORMAT_R32G32B32_FLOAT, 0,  0, D3D11_INPUT_PER_VERTEX_DATA, 0 },
		{ "COLOR", 0, DXGI_FORMAT_R8G8B8A8_UNORM, 0, 12, D3D11_INPUT_PER_VERTEX_DATA, 0 },
	};

	unsigned int cbsize = ((sizeof(VertexShaderConstants))&(~0xf))+0x10; // must be a multiple of 16
	D3D11_BUFFER_DESC cbdesc = CD3D11_BUFFER_DESC(cbsize, D3D11_BIND_CONSTANT_BUFFER, D3D11_USAGE_DEFAULT, 0 );
	HRESULT hr = D3D::device->CreateBuffer(&cbdesc, nullptr, &vscbuf);
	CHECK(hr==S_OK, "Create vertex shader constant buffer (size=%u)", cbsize);
	D3D::SetDebugObjectName((ID3D11DeviceChild*)vscbuf, "vertex shader constant buffer used to emulate the GX pipeline");

	D3DBlob blob;
	D3D::CompileVertexShader(simple_shader_code, sizeof(simple_shader_code), blob);
	D3D::device->CreateInputLayout(simpleelems, 2, blob.Data(), blob.Size(), ToAddr(SimpleLayout));
	SimpleVertexShader = D3D::CreateVertexShaderFromByteCode(blob);
	if (SimpleLayout == nullptr || SimpleVertexShader == nullptr) 
		PanicAlert("Failed to create simple vertex shader or input layout at %s %d\n", __FILE__, __LINE__);

	D3D::SetDebugObjectName((ID3D11DeviceChild*)SimpleVertexShader.get(), "simple vertex shader");
	D3D::SetDebugObjectName((ID3D11DeviceChild*)SimpleLayout.get(), "simple input layout");

	D3D::CompileVertexShader(clear_shader_code, sizeof(clear_shader_code), blob);
	D3D::device->CreateInputLayout(clearelems, 2, blob.Data(), blob.Size(), ToAddr(ClearLayout));
	ClearVertexShader = D3D::CreateVertexShaderFromByteCode(blob);
	if (ClearLayout == nullptr || ClearVertexShader == nullptr) 
		PanicAlert("Failed to create clear vertex shader or input layout at %s %d\n", __FILE__, __LINE__);


	D3D::SetDebugObjectName((ID3D11DeviceChild*)ClearVertexShader.get(), "clear vertex shader");
	D3D::SetDebugObjectName((ID3D11DeviceChild*)ClearLayout.get(), "clear input layout");

	Clear();

	if (!File::Exists(File::GetUserPath(D_SHADERCACHE_IDX)))
		File::CreateDir(File::GetUserPath(D_SHADERCACHE_IDX));

	SETSTAT(stats.numVertexShadersCreated, 0);
	SETSTAT(stats.numVertexShadersAlive, 0);

	char cache_filename[MAX_PATH];
	sprintf(cache_filename, "%sdx11-%s-vs.cache", File::GetUserPath(D_SHADERCACHE_IDX).c_str(),
			SConfig::GetInstance().m_LocalCoreStartupParameter.m_strUniqueID.c_str());
	VertexShaderCacheInserter inserter;
	g_vs_disk_cache.OpenAndRead(cache_filename, inserter);

	if (g_Config.bEnableShaderDebugging)
		Clear();

	last_entry = nullptr;
}

void VertexShaderCache::Clear()
{
	for (auto& iter : vshaders)
		iter.second.Destroy();
	vshaders.clear();
	vertex_uid_checker.Invalidate();

	last_entry = nullptr;
}

void VertexShaderCache::Shutdown()
{
	SAFE_RELEASE(vscbuf);

	SimpleVertexShader.reset();
	ClearVertexShader.reset();

	SimpleLayout.reset();
	ClearLayout.reset();

	Clear();
	g_vs_disk_cache.Sync();
	g_vs_disk_cache.Close();
}

bool VertexShaderCache::SetShader(u32 components)
{
	VertexShaderUid uid;
	GetVertexShaderUid(uid, components, API_D3D);
	if (g_ActiveConfig.bEnableShaderDebugging)
	{
		VertexShaderCode code;
		GenerateVertexShaderCode(code, components, API_D3D);
		vertex_uid_checker.AddToIndexAndCheck(code, uid, "Vertex", "v");
	}

	if (last_entry)
	{
		if (uid == last_uid)
		{
			GFX_DEBUGGER_PAUSE_AT(NEXT_VERTEX_SHADER_CHANGE, true);
			return (last_entry->shader != nullptr);
		}
	}

	last_uid = uid;

	VSCache::iterator iter = vshaders.find(uid);
	if (iter != vshaders.end())
	{
		const VSCacheEntry &entry = iter->second;
		last_entry = &entry;

		GFX_DEBUGGER_PAUSE_AT(NEXT_VERTEX_SHADER_CHANGE, true);
		return (entry.shader != nullptr);
	}

	VertexShaderCode code;
	GenerateVertexShaderCode(code, components, API_D3D);

	D3DBlob bytecode;
	;

	if (!D3D::CompileVertexShader(code.GetBuffer(), (int)strlen(code.GetBuffer()), bytecode))
	{
		GFX_DEBUGGER_PAUSE_AT(NEXT_ERROR, true);
		return false;
	}
	g_vs_disk_cache.Append(uid, bytecode.Data(), u32(bytecode.Size()));

	bool success = InsertByteCode(uid, std::move(bytecode));

	if (g_ActiveConfig.bEnableShaderDebugging && success)
	{
		vshaders[uid].code = code.GetBuffer();
	}

	GFX_DEBUGGER_PAUSE_AT(NEXT_VERTEX_SHADER_CHANGE, true);
	return success;
}

bool VertexShaderCache::InsertByteCode(const VertexShaderUid &uid, D3DBlob && bcodeblob)
{
	auto shader = D3D::CreateVertexShaderFromByteCode(bcodeblob);
	if (!shader)
		return false;

	// TODO: Somehow make the debug name a bit more specific
	D3D::SetDebugObjectName((ID3D11DeviceChild*)shader.get(), "a vertex shader of VertexShaderCache");

	// Make an entry in the table
	VSCacheEntry &entry = vshaders[uid];
	entry.shader = std::move(shader);
	entry.SetByteCode(std::move(bcodeblob));

	last_entry = &vshaders[uid];

	INCSTAT(stats.numVertexShadersCreated);
	SETSTAT(stats.numVertexShadersAlive, (int)vshaders.size());

	return true;
}

}  // namespace DX11
