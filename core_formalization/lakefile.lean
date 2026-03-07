import Lake
open Lake DSL

package «gpu» {
}

lean_lib «Gpu» {
}

lean_lib «FamousProblems» {
}

@[default_target]
lean_exe «gpu» {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
