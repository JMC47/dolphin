// Copyright 2014 Dolphin Emulator Project
// Licensed under GPLv2
// Refer to the license.txt file included.

#pragma once

#include <d3d11_1.h>
#include <memory>

namespace DX11
{
namespace D3D
{

// This is a specialized simpler version of std::unique_ptr dedicaced to D3D objects (with AddRef/Release methods).
// The single ownership semantics of std::unique_ptr is used and we hide the AddRef/Release API to prevent invalid uses.
// When VS2014 will be here, think to add the noexcept where it is possible
template <typename T>
struct UniquePtr {
	// http://en.cppreference.com/w/cpp/memory/unique_ptr/unique_ptr
	UniquePtr() = default;

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/unique_ptr
	UniquePtr( std::nullptr_t ) {
	}

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/unique_ptr
	explicit UniquePtr( T* p ) : 
		ptr_ { p } {
	}

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/unique_ptr
	// Copy semantics is unwanted
	UniquePtr( UniquePtr const & ) = delete;

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/unique_ptr
	UniquePtr& operator=( UniquePtr const & ) = delete;

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/unique_ptr
	UniquePtr( UniquePtr && p ) : ptr_ { p.release() } {}

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/operator%3D
	UniquePtr& operator=( UniquePtr && p ) {
		// the next line is important as it is safe with self assignment
		reset( p.release() );
		return *this;
	}

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/operator%3D
	UniquePtr& operator=( std::nullptr_t ) {
		reset();
		return *this;
	}

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/~unique_ptr
	~UniquePtr() {
		if (ptr_)
			ptr_->Release();
	}

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/release
	T* release() { 
		auto p = ptr_; 
		ptr_ = nullptr;
		return p; 
	}

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/reset
	void reset( T* p = nullptr ) {
		// the std enforce the order of the operation ( first assign, then delete )
		auto old = ptr_;
		ptr_ = p;
		if (old)
			old->Release();
	}

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/reset
	void reset( std::nullptr_t ) {
		reset();
	}

	// this is the ugly part but there is no real clean way to hide the unwanted API
	struct ReleaseAndAddRefHiddenT : public T {
	private:
		virtual ULONG Release(void) override;
		virtual ULONG AddRef(void) override;
	};

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/get
	ReleaseAndAddRefHiddenT* get() const { return static_cast<ReleaseAndAddRefHiddenT*>(ptr_); }

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/operator*
	ReleaseAndAddRefHiddenT* operator->() const { return static_cast<ReleaseAndAddRefHiddenT*>(ptr_); }
	ReleaseAndAddRefHiddenT& operator*() const { return *static_cast<ReleaseAndAddRefHiddenT*>(ptr_); }

	// Because D3D ojjects are ref counted, we are able to clone if really we need it,
	// still it is better to keep owership in one place and use naked pointer in the rendering code
	// to prune unneccessary AddRef/Release cycles
	UniquePtr Share() {
		auto p = get();
		if (p)
			p->AddRef();
		return UniquePtr{p};
	}

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/operator_bool
	explicit operator bool() const { return ptr_!=nullptr; }

	// http://en.cppreference.com/w/cpp/memory/unique_ptr/operator_cmp
	friend bool operator!=( UniquePtr const& a, UniquePtr const& b ) { return a.ptr_ != b.ptr_; }
	friend bool operator!=( UniquePtr const& p, std::nullptr_t )     { return p.ptr_ != nullptr; }
	friend bool operator!=( std::nullptr_t, UniquePtr const& p )     { return p.ptr_ != nullptr; }
	friend bool operator==( UniquePtr const& a, UniquePtr const& b ) { return a.ptr_ == b.ptr_; }
	friend bool operator==( UniquePtr const& p, std::nullptr_t )     { return p.ptr_ == nullptr; }
	friend bool operator==( std::nullptr_t, UniquePtr const& p )     { return p.ptr_ == nullptr; }

private:
	T* ptr_{};
};

// Alias to UniquePtr of most of the D3D object 
using VertexShaderPtr = UniquePtr<ID3D11VertexShader>;
using PixelShaderPtr = UniquePtr<ID3D11PixelShader>;
using GeometryShaderPtr = UniquePtr<ID3D11GeometryShader>;
using ComputeShaderPtr = UniquePtr<ID3D11ComputeShader>;
using BufferPtr = UniquePtr<ID3D11Buffer>;
using SrvPtr = UniquePtr<ID3D11ShaderResourceView>;
using UavPtr = UniquePtr<ID3D11UnorderedAccessView>;
using Texture1dPtr = UniquePtr<ID3D11Texture1D>;
using Texture2dPtr = UniquePtr<ID3D11Texture2D>;
using RtvPtr = UniquePtr<ID3D11RenderTargetView>;
using DsvPtr = UniquePtr<ID3D11DepthStencilView>;

using InputLayoutPtr = UniquePtr<ID3D11InputLayout>;
using BlendStatePtr = UniquePtr<ID3D11BlendState>;

using RasterizerStatePtr = UniquePtr<ID3D11RasterizerState>;
using DepthStencilStatePtr = UniquePtr<ID3D11DepthStencilState>;
using SamplerStatePtr = UniquePtr<ID3D11SamplerState>;



// helper class to use a UniquePtr in the various CreateSomething( (T**)/(void**) result )
// use with the following function
template <typename T> 
struct ToAddrImpl {
	ToAddrImpl( UniquePtr<T> & ptr ) : ptr_{ptr} {}
	ToAddrImpl( ToAddrImpl const & ) = delete;
	ToAddrImpl& operator=( ToAddrImpl const & ) = delete;

	~ToAddrImpl() {
		if (temp_)
			ptr_.reset(temp_);
	}

	operator void**() { return (void**)&temp_; }
	operator T**() { return &temp_; }
private:
	UniquePtr<T> & ptr_;
	T* temp_{};
};

// usage example : device->CreateBuffer( bla, ToAddr( m_myBuffer ) );
template <typename T>
ToAddrImpl<T> ToAddr( UniquePtr<T>& ptr ) {
	return { ptr };
}

}  // namespace D3D
}  // namespace DX11
