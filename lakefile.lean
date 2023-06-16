import Lake
open Lake DSL

package «groupComp» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «GroupComp» {
  -- add any library configuration options here
}
