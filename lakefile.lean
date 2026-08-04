import Lake
open Lake DSL

package «crypto_topos» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib CryptoTopos where

require HoTTLean from git
  "https://github.com/sinhp/HoTTLean.git" 

