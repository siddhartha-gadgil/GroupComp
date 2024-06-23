import Lake
open Lake DSL

package «groupComp» {
  -- add any package configuration options here
}

@[default_target]
lean_lib «GroupComp» {
  -- add any library configuration options here
}

@[default_target]
lean_lib «Lectures» {
  -- add any library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"


meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "c7f4ac8"
