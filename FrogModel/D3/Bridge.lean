module

public import FrogModel.D3.Defs
public import FrogModel.LemmaR.Planted.Check

@[expose] public section

/-!
# The frozen d = 3 target against the development

`FrogModel.Recurrent` (FrogModel/D3/Defs.lean, the text of the frozen statement in
FrogModel/ChallengeRecurrent.lean) is `FrogModel.LemmaR.Recurrent` (LemmaR/Statement.lean) by
definition, so `FrogModel.LemmaR.recurrent_of_plantedCount` closes the target `recurrent_three`
once a linear first moment of the planted counts is proved. Sanity: recurrence excludes
transience.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace FrogModel.D3

/-- The frozen `Recurrent` and the one of FrogModel/LemmaR (Theorem 8.2 of the paper) are the same
proposition. -/
theorem recurrent_iff_lemmaR (d : ℕ) [NeZero d] :
    FrogModel.Recurrent d ↔ FrogModel.LemmaR.Recurrent d :=
  Iff.rfl

/-- The target from a linear first moment of the planted counts at `d = 3`. -/
theorem recurrent_three_of_plantedCount
    (h : 0 < limsup (fun m : ℕ => (∫⁻ ζ, LemmaR.plantedCount m ζ ∂frogMeasure 3) / m) atTop) :
    FrogModel.Recurrent 3 :=
  (recurrent_iff_lemmaR 3).2 (LemmaR.recurrent_of_plantedCount (by norm_num) h)

/-- A recurrent frog model is not transient. -/
theorem not_transient_of_recurrent {d : ℕ} [NeZero d] (h : FrogModel.Recurrent d) :
    ¬ Transient d := by
  intro ht
  have : IsProbabilityMeasure (frogMeasure d) := by unfold frogMeasure; infer_instance
  obtain ⟨ω, h1, h2⟩ := (h.and ht).exists
  exact h1 h2

end FrogModel.D3
