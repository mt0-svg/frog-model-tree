module

public import FrogModel.LemmaX.PlanSound
public import FrogModel.LemmaX.LData
public import FrogModel.LemmaX.PlanData

@[expose] public section

/-!
# (I4) for the certificate (condition (C7) of the paper)

The check of (I4) on the atoms `Latoms` of `L = V'(s_0)` and the plan `planData` of the version 4
certificate, by `decide +kernel`, and `PlanI4 (latMeasure Latoms)` by `planI4_of_check`.
-/

namespace FrogModel.LemmaX

/-- The check of (I4) passes on the data of the certificate. -/
theorem planCheck_cand : planCheck Latoms planDen planData = true := by decide +kernel

/-- **(I4)** for the certificate: a plan from `L = latMeasure Latoms` onto the finite part of
`H*`. -/
theorem planI4_cand : PlanI4 (latMeasure Latoms) := planI4_of_check _ _ _ planCheck_cand

end FrogModel.LemmaX
