module

public import FrogModel.LemmaR.Awake
public import FrogModel.LemmaR.Planted.Defs
public import FrogModel.Pieces.Basic

@[expose] public section

/-!
# Lemmas 9.1 and 9.2 of the paper: the all-awake planted count

`U'_m` is a sum of independent indicators over the vertices at depth at most `m`
(`plantedAwake_eq_sum`), the walk on `T*` from `some v` reaches `y` with probability at most
`d^(-(|v| + 1))` (`hitStar_le`, by the embedding of `T*` below a child of the root), so
`E U'_m^2 ≤ (m + 1) + (m + 1)^2` (`lintegral_plantedAwake_sq_le`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaR

open Classical in
/-- `U'_m` is a finite sum of indicators over the vertices at depth at most `m`. -/
theorem FrogModel.LemmaR.plantedAwake_eq_sum {d : ℕ} (m : ℕ) (ζ : Sample d) :
    plantedAwake m ζ = ∑ v ∈ words d m,
      (if ∃ n, walkStar (some v) (ζ v) n = none then (1 : ℝ≥0∞) else 0) := by
  unfold plantedAwake
  rw [tsum_eq_sum (s := words d m) fun v hv => by
    rw [mem_words] at hv
    simp [hv]]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [mem_words] at hv
  simp [hv]

/-- The event that the walk on `T*` from `some v` reaches `y` is measurable. -/
theorem FrogModel.LemmaR.measurableSet_hitStar {d : ℕ} (v : Vertex d) :
    MeasurableSet {x : ℕ → Step d | ∃ n, walkStar (some v) x n = none} := by
  rw [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun n => measurableSet_walkStar_eq d v n none

/-- From `some v` the walk on `T*` reaches `y` with probability at most `d^(-(|v| + 1))`. -/
theorem FrogModel.LemmaR.hitStar_le {d : ℕ} [NeZero d] (v : Vertex d) :
    seqLaw d {x : ℕ → Step d | ∃ n, walkStar (some v) x n = none} ≤
      ((d : ℝ≥0∞)⁻¹) ^ (v.length + 1) := by
  classical
  set c : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hsub : {x : ℕ → Step d | ∃ n, walkStar (some v) x n = none} ⊆
      {x | cut (v ++ [c]) x ≠ ⊤} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    set n := Nat.find hx with hn
    have hnone : walkStar (some v) x n = none := Nat.find_spec hx
    have hbefore : ∀ i < n, walkStar (some v) x i ≠ none := fun i hi => Nat.find_min hx hi
    have hwalk : walk (v ++ [c]) x n = root := by
      rw [walk_append c v x n hbefore, hnone]
      rfl
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0] at hnone
        simp [walkStar] at hnone
      · exact h0
    have hle : cut (v ++ [c]) x ≤ n := (cut_le_iff _ _ n).2 ⟨n, hn1, le_rfl, hwalk⟩
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top n) hle
  calc seqLaw d {x : ℕ → Step d | ∃ n, walkStar (some v) x n = none}
      ≤ seqLaw d {x | cut (v ++ [c]) x ≠ ⊤} := measure_mono hsub
    _ ≤ ((d : ℝ≥0∞)⁻¹) ^ (v ++ [c]).length := hitProb_le (v ++ [c]) (by simp [root])
    _ = ((d : ℝ≥0∞)⁻¹) ^ (v.length + 1) := by simp

/-- `U'_m` is measurable. -/
theorem FrogModel.LemmaR.measurable_plantedAwake {d : ℕ} (m : ℕ) :
    Measurable (plantedAwake (d := d) m) := by
  classical
  have : plantedAwake (d := d) m = fun ζ => ∑ v ∈ words d m,
      (if ∃ n, walkStar (some v) (ζ v) n = none then (1 : ℝ≥0∞) else 0) := by
    funext ζ
    exact plantedAwake_eq_sum m ζ
  rw [this]
  refine Finset.measurable_sum _ fun v _ => ?_
  exact Measurable.ite ((measurableSet_hitStar v).preimage (measurable_pi_apply v))
    measurable_const measurable_const

/-- `E U'_m^2 ≤ (m + 1) + (m + 1)^2`. -/
theorem FrogModel.LemmaR.lintegral_plantedAwake_sq_le {d : ℕ} [NeZero d] (m : ℕ) :
    ∫⁻ ζ, plantedAwake m ζ ^ 2 ∂frogMeasure d ≤ (m + 1) + (m + 1) ^ 2 := by
  classical
  have : IsProbabilityMeasure (frogMeasure d) := by unfold frogMeasure; infer_instance
  set H : Vertex d → Set (ℕ → Step d) := fun v => {x | ∃ n, walkStar (some v) x n = none}
    with hH
  set g : Vertex d → (ℕ → Step d) → ℝ≥0∞ := fun v => (H v).indicator 1 with hgdef
  set X : Vertex d → Sample d → ℝ≥0∞ := fun v ζ => g v (ζ v) with hX
  have hg : ∀ v : Vertex d, Measurable (g v) := fun v =>
    measurable_one.indicator (measurableSet_hitStar v)
  have hXm : ∀ v : Vertex d, Measurable (X v) := fun v => (hg v).comp (measurable_pi_apply v)
  have hind : iIndepFun X (frogMeasure d) :=
    ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : Vertex d => seqLaw d) (X := g) hg
  have hlaw : ∀ (v : Vertex d) (f : (ℕ → Step d) → ℝ≥0∞), Measurable f →
      ∫⁻ ζ, f (ζ v) ∂frogMeasure d = ∫⁻ x, f x ∂seqLaw d := by
    intro v f hf
    rw [← lintegral_map hf (measurable_pi_apply v)]
    congr 1
    exact Measure.infinitePi_map_eval _ v
  have hpow : ∀ v : Vertex d, ((d : ℝ≥0∞)⁻¹) ^ (v.length + 1) ≤ ((d : ℝ≥0∞)⁻¹) ^ v.length := by
    intro v
    rw [pow_succ]
    refine mul_le_of_le_one_right' ?_
    exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d))
  have hX1 : ∀ v : Vertex d, ∫⁻ ζ, X v ζ ∂frogMeasure d ≤ ((d : ℝ≥0∞)⁻¹) ^ v.length := by
    intro v
    rw [hlaw v (g v) (hg v), lintegral_indicator_one (measurableSet_hitStar v)]
    exact (hitStar_le v).trans (hpow v)
  have hX2 : ∀ v : Vertex d, ∫⁻ ζ, X v ζ ^ 2 ∂frogMeasure d ≤ ((d : ℝ≥0∞)⁻¹) ^ v.length := by
    intro v
    refine le_trans (le_of_eq (lintegral_congr fun ζ => ?_)) (hX1 v)
    simp only [hX, hgdef, Set.indicator_apply]
    split_ifs <;> simp
  have hsum : ∑ v ∈ words d m, ((d : ℝ≥0∞)⁻¹) ^ v.length = m + 1 := sum_words_pow m
  calc ∫⁻ ζ, plantedAwake m ζ ^ 2 ∂frogMeasure d
      = ∫⁻ ζ, (∑ v ∈ words d m, X v ζ) ^ 2 ∂frogMeasure d := by
        congr 1
        funext ζ
        rw [plantedAwake_eq_sum]
        congr 2
    _ ≤ ∑ v ∈ words d m, ∫⁻ ζ, X v ζ ^ 2 ∂frogMeasure d +
          (∑ v ∈ words d m, ∫⁻ ζ, X v ζ ∂frogMeasure d) ^ 2 :=
        lintegral_sq_sum_le _ _ X hXm hind
    _ ≤ (m + 1) + (m + 1) ^ 2 := by
        gcongr
        · rw [← hsum]
          exact Finset.sum_le_sum fun v _ => hX2 v
        · rw [← hsum]
          exact Finset.sum_le_sum fun v _ => hX1 v
