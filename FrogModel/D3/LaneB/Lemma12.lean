module

public import FrogModel.D3.LaneB.Words
public import FrogModel.Pieces.Basic

@[expose] public section

/-!
# The tail bounds of Lemma 11.1 (3) of the paper on the planted curve

Lemma 11.1 (1) with `X = G_m(k)` and `U = U_m(k)`, the number of frogs among the `k` entrants and
the frogs of depth at most `m` whose path reaches `y` (Lemma 10.2). A woken frog is one of them,
so `G_m(k) ≤ U_m(k)` pathwise; the events are independent (each reads one frog's path), and
`E U_m(k) = k/3 + ∑ over depths i ≤ m of 3^i 3^-(i+1) = mu_m(k)` (`prob_reach`). This also proves
two statements of Lemma 10.2, outright or from `prob_reach`: `plantedG_le_frogs` and
`lintegral_plantedG_le`. Each theorem takes the statements it uses as hypotheses.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace FrogModel.D3.Iface

/-- The frogs that can be woken: the entrants `i < k` and the frogs of depth at most `m`. -/
def frogsF (m k : ℕ) : Finset PFrog := (Finset.range k).disjSum (wordsLe m)

/-- The path of `φ` reaches `y`. -/
def reachSet (φ : PFrog) : Set (PFrog → ℕ → Step 3) := {π | ∃ n, pos π φ n = none}

/-- A woken frog is an entrant or a frog of depth at most `m`. -/
theorem woken_mem_frogsF {m k : ℕ} {π : PFrog → ℕ → Step 3} {φ : PFrog} (h : Woken m k π φ) :
    φ ∈ frogsF m k := by
  induction h with
  | ent i hi => simpa [frogsF] using hi
  | wake φ v n _ hv _ _ => simpa [frogsF, mem_wordsLe] using hv

/-- The reach event of one path. -/
theorem measurableSet_reach1 (v : Vertex 3) :
    MeasurableSet {x : ℕ → Step 3 | ∃ n, walkStar (some v) x n = none} := by
  have : {x : ℕ → Step 3 | ∃ n, walkStar (some v) x n = none} =
      ⋃ n, (fun x : ℕ → Step 3 => walkStar (some v) x n) ⁻¹' {none} := by
    ext x; simp
  rw [this]
  exact MeasurableSet.iUnion fun n => (measurable_walkStar_at 3 v n) (measurableSet_singleton none)

theorem measurableSet_reachSet (φ : PFrog) : MeasurableSet (reachSet φ) :=
  show MeasurableSet ((fun f : PFrog → ℕ → Step 3 => f φ) ⁻¹'
      {x : ℕ → Step 3 | ∃ n, walkStar (some (frogStart φ)) x n = none}) from
    measurableSet_preimage (measurable_pi_apply φ) (measurableSet_reach1 (frogStart φ))

/-- The reach events are independent: each reads the path of one frog. -/
theorem iIndepSet_reachSet : iIndepSet reachSet pathMeasure :=
  iIndepSet_infinitePi_preimage (Measure.infinitePi fun _ : ℕ => stepLaw 3)
    (fun φ => {x | ∃ n, walkStar (some (frogStart φ)) x n = none})
    (fun φ => measurableSet_reach1 (frogStart φ))

/-- `G_m(k) ≤ U_m(k)` pathwise. -/
theorem plantedG_le_card (m k : ℕ) (π : PFrog → ℕ → Step 3) :
    plantedG m k π ≤ (((frogsF m k).filter fun φ => π ∈ reachSet φ).card : ℕ∞) := by
  unfold plantedG
  rw [← Set.encard_coe_eq_coe_finsetCard]
  refine Set.encard_le_encard fun φ hφ => ?_
  simp only [Finset.coe_filter, Set.mem_ofPred_eq]
  exact ⟨woken_mem_frogsF hφ.1, hφ.2⟩

/-- **`plantedG_le_frogs`** (Lemma 10.2 (2) of the paper), proved: `G_m(k) ≤ k + (3^(m+1) - 1)/2`. -/
theorem plantedG_le_frogs_proof : plantedG_le_frogs := by
  intro m k π
  refine (plantedG_le_card m k π).trans ?_
  have h := Finset.card_filter_le (frogsF m k) fun φ => π ∈ reachSet φ
  rw [frogsF, Finset.card_disjSum, Finset.card_range, card_wordsLe] at h
  exact_mod_cast h

theorem plantedG_eq_nat (m k : ℕ) (π : PFrog → ℕ → Step 3) : ∃ n : ℕ, plantedG m k π = n :=
  ⟨_, (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top _) (plantedG_le_card m k π))).symm⟩

/-- `G_m(k)` as a real random variable. -/
noncomputable def Xr (m k : ℕ) (π : PFrog → ℕ → Step 3) : ℝ := ((plantedG m k π).toNat : ℝ)

theorem measurable_Xr (hmeas : measurable_plantedPair) (m k : ℕ) :
    Measurable (Xr m k) := by
  have h : Measurable fun π => plantedCurve m π k :=
    (measurable_pi_apply k).comp (hmeas m).fst
  exact (Measurable.of_discrete (f := fun x : ℕ∞ => (x.toNat : ℝ))).comp h

theorem Xr_nonneg (m k : ℕ) (π : PFrog → ℕ → Step 3) : 0 ≤ Xr m k π := Nat.cast_nonneg _

theorem Xr_le (m k : ℕ) (π : PFrog → ℕ → Step 3) :
    Xr m k π ≤ ∑ φ ∈ frogsF m k, (reachSet φ).indicator (1 : (PFrog → ℕ → Step 3) → ℝ) π := by
  have h1 : ∑ φ ∈ frogsF m k, (reachSet φ).indicator (1 : (PFrog → ℕ → Step 3) → ℝ) π =
      (((frogsF m k).filter fun φ => π ∈ reachSet φ).card : ℝ) := by
    simp only [Set.indicator_apply, Pi.one_apply, Finset.sum_boole]
  rw [h1, Xr]
  have h2 := plantedG_le_card m k π
  obtain ⟨n, hn⟩ := plantedG_eq_nat m k π
  rw [hn] at h2 ⊢
  simp only [ENat.toNat_natCast]
  exact_mod_cast h2

/-- `P(G_m(k) ≤ v)` as `P(X ≤ v)`. -/
theorem cdfG_eq_le (m k v : ℕ) : cdfG m k v = (pathMeasure {π | Xr m k π ≤ v}).toReal := by
  unfold cdfG
  congr 2
  ext π
  obtain ⟨n, hn⟩ := plantedG_eq_nat m k π
  simp only [Set.mem_ofPred_eq, Xr, hn, ENat.toNat_natCast, Nat.cast_le]

/-- `P(G_m(k) ≤ v)` as `P(X < v + 1)`. -/
theorem cdfG_eq_lt (m k v : ℕ) :
    cdfG m k v = (pathMeasure {π | Xr m k π < (v : ℝ) + 1}).toReal := by
  rw [cdfG_eq_le]
  congr 2
  ext π
  obtain ⟨n, hn⟩ := plantedG_eq_nat m k π
  simp only [Set.mem_ofPred_eq, Xr, hn, ENat.toNat_natCast]
  rw [show (v : ℝ) + 1 = ((v + 1 : ℕ) : ℝ) by push_cast; ring, Nat.cast_le, Nat.cast_lt]
  omega

theorem integral_Xr (hmeas : measurable_plantedPair) (m k : ℕ) :
    ∫ π, Xr m k π ∂pathMeasure = meanG m k := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (Xr_nonneg m k))
    (measurable_Xr hmeas m k).aestronglyMeasurable]
  unfold meanG
  congr 1
  refine lintegral_congr fun π => ?_
  obtain ⟨n, hn⟩ := plantedG_eq_nat m k π
  simp [Xr, hn]

/-- `∑ over U_m(k)'s frogs of P(reach) = mu_m(k)`. -/
theorem sum_reach (hreach : prob_reach) (m k : ℕ) :
    ∑ φ ∈ frogsF m k, (pathMeasure (reachSet φ)).toReal = mu m k := by
  have h : ∀ φ, (pathMeasure (reachSet φ)).toReal = (3⁻¹ : ℝ) ^ (frogDepth φ + 1) := by
    intro φ
    rw [reachSet, hreach φ]
    simp [ENNReal.toReal_pow, ENNReal.toReal_inv]
  simp only [h, frogsF, Finset.sum_disjSum, frogDepth]
  rw [sum_wordsLe]
  simp only [zero_add, pow_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold mu
  ring

/-- **`lintegral_plantedG_le`** (Lemma 10.2 (1) of the paper) from `prob_reach`:
`E G_m(k) ≤ E U_m(k) = mu_m(k)`. -/
theorem lintegral_plantedG_le_of (hreach : prob_reach) :
    lintegral_plantedG_le := by
  intro m k
  calc ∫⁻ π, (plantedG m k π : ℝ≥0∞) ∂pathMeasure
      ≤ ∫⁻ π, ∑ φ ∈ frogsF m k, (reachSet φ).indicator 1 π ∂pathMeasure := by
        refine lintegral_mono fun π => ?_
        have h := plantedG_le_card m k π
        have h' : (plantedG m k π : ℝ≥0∞) ≤
            ((((frogsF m k).filter fun φ => π ∈ reachSet φ).card : ℕ∞) : ℝ≥0∞) :=
          ENat.toENNReal_le.mpr h
        simpa only [Set.indicator_apply, Pi.one_apply, Finset.sum_boole, ENat.toENNReal_coe]
          using h'
    _ = ∑ φ ∈ frogsF m k, pathMeasure (reachSet φ) := by
        rw [lintegral_finsetSum _ fun φ _ => measurable_one.indicator (measurableSet_reachSet φ)]
        exact Finset.sum_congr rfl fun φ _ => lintegral_indicator_one (measurableSet_reachSet φ)
    _ = ENNReal.ofReal (mu m k) := by
        rw [← sum_reach hreach m k, ENNReal.ofReal_sum_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
        exact Finset.sum_congr rfl fun φ _ => (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

theorem cdfG_le_one (m k v : ℕ) : cdfG m k v ≤ 1 := by
  unfold cdfG
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

/-- **The second bound of Lemma 11.1 (3) of the paper** from the first bound of Lemma 11.1 (1),
measurability and `prob_reach` (Lemma 10.2 (1)). -/
theorem lemma12_G_of (h12 : lemma12_general.{0, 0}) (hmeas : measurable_plantedPair)
    (hreach : prob_reach) : lemma12_G := by
  intro m k v D hD
  unfold lemma12B
  split_ifs with hv
  · have key := h12 pathMeasure (frogsF m k) reachSet measurableSet_reachSet iIndepSet_reachSet
      (Xr m k) (measurable_Xr hmeas m k) (Xr_nonneg m k) (Xr_le m k) (mu m k)
      (sum_reach hreach m k).symm ((v : ℝ) + 1) hv
    rw [cdfG_eq_lt]
    refine key.trans (div_le_div_of_nonneg_right ?_ (by linarith))
    rw [integral_Xr hmeas]
    unfold deficit at hD
    linarith
  · exact cdfG_le_one m k v

/-- **The third bound of Lemma 11.1 (3) of the paper** from the second bound of Lemma 11.1 (1),
measurability and `prob_reach` (Lemma 10.2 (1)). -/
theorem lemma12'_G_of (h12 : lemma12'_general.{0, 0}) (hmeas : measurable_plantedPair)
    (hreach : prob_reach) : lemma12'_G := by
  intro m k v D t hD ht0 ht1
  unfold lemma12'B
  split_ifs with hv
  · have key := h12 pathMeasure (frogsF m k) reachSet measurableSet_reachSet iIndepSet_reachSet
      (Xr m k) (measurable_Xr hmeas m k) (Xr_nonneg m k) (Xr_le m k) (mu m k)
      (sum_reach hreach m k).symm t v ht0 ht1 hv
    have hpos : 0 ≤ (1 - t) * mu m k - v := by linarith
    rw [cdfG_eq_le]
    have hnum : mu m k - ∫ π, Xr m k π ∂pathMeasure ≤ D := by
      rw [integral_Xr hmeas]
      unfold deficit at hD
      linarith
    have := div_le_div_of_nonneg_right hnum hpos
    linarith
  · exact cdfG_le_one m k v

end FrogModel.D3.Iface
