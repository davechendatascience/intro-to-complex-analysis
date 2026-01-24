import Lake
open Lake DSL

-- Use the Lean version (e.g. v4.23.0) to pin dependencies
def leanVersion : String := s!"v{Lean.versionString}"

package «complex-analysis-game» where
  leanOptions := #[
    ⟨`linter.all, false⟩,
    ⟨`pp.showLetValues, true⟩,
    ⟨`tactic.hygienic, false⟩
  ]
  moreLeanArgs := #["-Dtrace.debug=false"]
  moreServerOptions := #[⟨`trace.debug, true⟩]

-- Require dependencies at the same version tag
require GameServer from git "https://github.com/leanprover-community/lean4game" @ leanVersion / "server"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ leanVersion

@[default_target]
lean_lib Game where
