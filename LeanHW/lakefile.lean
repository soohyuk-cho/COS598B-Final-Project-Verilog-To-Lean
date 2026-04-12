import Lake
open Lake DSL

package «LeanHW» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «LeanHW» where
  srcDir := "."
