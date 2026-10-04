import Lean
import FrogModel.Solution
import FrogModel.SolutionRecurrent

/-! For the badges of ci.yml: the hypotheses of the theorems of config.json and config-recurrent.json (their binders
whose type is a proposition) and the axioms they use. Run with `lake env lean code/formal-proof/facts.lean`. -/

open Lean Meta in
#eval show MetaM Unit from do
  let mut hyps := 0
  let mut axs : Array Name := #[]
  for n in [``FrogModel.transient_four, ``FrogModel.meanVisits_four_le, ``FrogModel.recurrent_three] do
    let c ← getConstInfo n
    hyps := hyps + (← forallTelescope c.type fun xs _ =>
      xs.foldlM (fun k x => do return if ← isProp (← inferType x) then k + 1 else k) 0)
    for a in ← collectAxioms n do
      unless axs.contains a do axs := axs.push a
  IO.println s!"hypotheses {hyps}"
  IO.println s!"axioms {axs.size}"
  IO.println s!"sorryAx {axs.contains ``sorryAx}"
