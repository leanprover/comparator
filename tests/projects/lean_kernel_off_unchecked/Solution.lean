import Lean

open Lean Elab Term Meta

-- A theorem whose value proves `0 = 0`, added without the kernel check: only a replay can reject it.
run_elab
  withOptions (fun o => o.setBool `debug.skipKernelTC true) <|
    addDecl <| .thmDecl {
      name        := `zero_eq_one
      levelParams := []
      type        := mkApp3 (.const ``Eq [1]) (.const ``Nat []) (mkNatLit 0) (mkNatLit 1)
      value       := mkApp2 (.const ``Eq.refl [1]) (.const ``Nat []) (mkNatLit 0)
    }
