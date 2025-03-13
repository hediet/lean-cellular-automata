import Lake
open Lake DSL

package «cellular-automatas» where
    -- add package configuration options here

@[default_target]
lean_lib «CellularAutomatas» where
  -- add library configuration options here

lean_lib «scripts» where
  -- Scripts library (includes VerifyConfig)

lean_exe «verify_proofs» where
  root := `scripts.verify_proofs

require mathlib from git "https://github.com/leanprover-community/mathlib4"
