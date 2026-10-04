module

public import FrogModel.D3.LaneA.Pool.Main
public import FrogModel.D3.LaneB.Lemma10

@[expose] public section

/-!
# Lemma 11.5 of the paper without hypotheses (d = 3)

`lemma10_of` takes `curveLaw_succ` as a hypothesis; `curveLaw_succ_proof` discharges it.
-/

namespace FrogModel.D3.LaneA

open FrogModel.D3.Iface

/-- **Lemma 11.5 of the paper** (deep fresh trials), with no hypothesis. -/
theorem lemma10_proof : lemma10 :=
  lemma10_of Pool.curveLaw_succ_proof

end FrogModel.D3.LaneA
