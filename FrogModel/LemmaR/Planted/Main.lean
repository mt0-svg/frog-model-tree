module

public import FrogModel.LemmaR.Planted.Awake
public import FrogModel.LemmaR.Planted.Paths

@[expose] public section

/-!
# Lemma 9.2 of the paper: the proof

`plantedLemmaR_lower'`: the second moment method along a sequence
(`measure_top_pos_of_linear`) with `V = X = frozenCount`, the dominating variables `U'_m` and
`E U'_m^2 ≤ (m + 1) + (m + 1)^2 ≤ 6 m^2`. `plantedLemmaR'` takes `Z = Z_m`;
`recurrent_of_planted'` adds Theorem 9.3. The frozen statements of
`FrogModel.LemmaR.Planted.Statement` hold: the `_holds` theorems at the end of the file.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaR

/-- Lemma 9.2 of the paper for a lower model (frozen statement `PlantedLemmaRLowerStatement`). -/
theorem FrogModel.LemmaR.plantedLemmaR_lower' {d : ℕ} [NeZero d] (Z : ℕ → Sample d → ℝ≥0∞)
    (hZ : ∀ m, AEMeasurable (Z m) (frogMeasure d))
    (hZX : ∀ m, ∀ᵐ ζ ∂frogMeasure d, Z m ζ ≤ frozenCount ζ)
    (hZU : ∀ m, ∀ᵐ ζ ∂frogMeasure d, Z m ζ ≤ plantedAwake m ζ)
    {c : ℝ≥0∞} (hc : 0 < c) (hfreq : ∃ᶠ m in atTop, c * m ≤ ∫⁻ ζ, Z m ζ ∂frogMeasure d) :
    0 < frogMeasure d {ζ | frozenCount ζ = ⊤} := by
  have : IsProbabilityMeasure (frogMeasure d) := by unfold frogMeasure; infer_instance
  refine measure_top_pos_of_linear (frogMeasure d) frozenCount (measurable_frozenCount d) Z
    plantedAwake hZ (fun m => (measurable_plantedAwake m).aemeasurable) hZX hZU 6 (by simp)
    (fun m hm => ?_) hc hfreq
  refine (lintegral_plantedAwake_sq_le m).trans ?_
  have h : (((m + 1) + (m + 1) ^ 2 : ℕ) : ℝ≥0∞) ≤ ((6 * m ^ 2 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (by nlinarith : (m + 1) + (m + 1) ^ 2 ≤ 6 * m ^ 2)
  push_cast at h
  exact h

/-- Lemma 9.2 of the paper (frozen statement `PlantedLemmaRStatement`). -/
theorem FrogModel.LemmaR.plantedLemmaR' {d : ℕ} [NeZero d]
    (h : 0 < limsup (fun m : ℕ => (∫⁻ ζ, plantedCount m ζ ∂frogMeasure d) / m) atTop) :
    0 < frogMeasure d {ζ | frozenCount ζ = ⊤} := by
  obtain ⟨c, hc, -, hfreq⟩ := frequently_of_limsup_pos _ h
  exact plantedLemmaR_lower' plantedCount (fun m => (measurable_plantedCount m).aemeasurable)
    (fun m => Eventually.of_forall (plantedCount_le_frozenCount m))
    (fun m => Eventually.of_forall (plantedCount_le_plantedAwake m)) hc hfreq

/-- Lemma 9.2 and Theorem 9.3 of the paper give recurrence (`RecurrentOfPlantedStatement`). -/
theorem FrogModel.LemmaR.recurrent_of_planted' {d : ℕ} [NeZero d]
    (hB : 0 < frogMeasure d {ζ | frozenCount ζ = ⊤} →
      ∀ᵐ ω ∂frogMeasure d, (visits (paths ω)).Infinite)
    (h : 0 < limsup (fun m : ℕ => (∫⁻ ζ, plantedCount m ζ ∂frogMeasure d) / m) atTop) :
    Recurrent d :=
  hB (plantedLemmaR' h)

/-! The frozen statements (Planted/Statement.lean) hold. -/

/-- The frozen `PlantedLemmaRStatement` holds. -/
theorem FrogModel.LemmaR.plantedLemmaRStatement_holds (d : ℕ) [NeZero d] :
    PlantedLemmaRStatement d :=
  fun h => plantedLemmaR' h

/-- The frozen `PlantedLemmaRLowerStatement` holds. -/
theorem FrogModel.LemmaR.plantedLemmaRLowerStatement_holds (d : ℕ) [NeZero d] :
    PlantedLemmaRLowerStatement d :=
  fun Z hZ hZX hZU _ hc hfreq => plantedLemmaR_lower' Z hZ hZX hZU hc hfreq

/-- The frozen `RecurrentOfPlantedStatement` holds. -/
theorem FrogModel.LemmaR.recurrentOfPlantedStatement_holds (d : ℕ) [NeZero d] :
    RecurrentOfPlantedStatement d :=
  fun hB h => recurrent_of_planted' hB h
