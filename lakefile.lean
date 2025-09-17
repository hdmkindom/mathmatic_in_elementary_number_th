import Lake
open Lake DSL

package "mathmatic_in_elementary_number_th" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ "git#v4.24.0-rc1"

@[default_target]
lean_lib «MathmaticInElementaryNumberTh» where
  -- add any library configuration options here
