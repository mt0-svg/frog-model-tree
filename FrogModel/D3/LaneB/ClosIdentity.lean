module

public import FrogModel.D3.LaneB.Good
public import FrogModel.D3.LaneB.Counts
public import FrogModel.D3.LaneB.Measurability
public import FrogModel.D3.LaneB.ClosureFacts

@[expose] public section

/-!
# The identity of the mean of the closure (proof of Lemma 10.5 of the paper)

With good children (nondecreasing, `G(k) ≤ k + B`), Wald's identity at `N ∧ n` and monotone
convergence give `E N ≤ 4 (q + 3B) < ∞`, so `N < ∞` almost surely, and the identity
`3 E X = q + ∑_c (E G_c(e_c) - E e_c / 3)` of the closure.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-! ## Wald for the closure and finiteness of `N` -/

/-- `N ∧ n` as a natural number. -/
noncomputable def tauN (q n : ℕ) (x : ClosSample) : ℕ := (min (closN q x.1 x.2) (n : ℕ∞)).toNat

theorem tauN_le (q n : ℕ) (x : ClosSample) : tauN q n x ≤ n := by
  unfold tauN
  have h : min (closN q x.1 x.2) (n : ℕ∞) ≤ n := min_le_right _ _
  have hne : min (closN q x.1 x.2) (n : ℕ∞) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) h
  rw [← ENat.natCast_le_natCast, ENat.natCast_toNat hne]
  exact h

theorem tauN_cast (q n : ℕ) (x : ClosSample) :
    (tauN q n x : ℕ∞) = min (closN q x.1 x.2) (n : ℕ∞) := by
  unfold tauN
  exact ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top n) (min_le_right _ _))

theorem lt_tauN_iff (q n i : ℕ) (x : ClosSample) :
    i < tauN q n x ↔ (i : ℕ∞) < closN q x.1 x.2 ∧ i < n := by
  rw [← ENat.natCast_lt_natCast, tauN_cast, lt_min_iff, ENat.natCast_lt_natCast]

theorem measurable_tauN (q n : ℕ) : Measurable (tauN q n) :=
  (Measurable.of_discrete (f := fun y : ℕ∞ => (min y (n : ℕ∞)).toNat)).comp (measurable_closN q)

/-- Wald at `N ∧ n`: `E k_a(N ∧ n) = E(N ∧ n)/4`. -/
theorem wald_tauN (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q n : ℕ) (a : Fin 4) :
    ∫ x, (dirCount x.2 a (tauN q n x) : ℝ) ∂closMeasure Q =
      (1 / 4) * ∫ x, (tauN q n x : ℝ) ∂closMeasure Q :=
  wald_dirCount (Measure.pi fun _ : Fin 3 => Q) (tauN q n) (measurable_tauN q n)
    (fun i G D D' hD => by
      simp only [lt_tauN_iff]
      rw [closN_stop q i G D D' hD]) n (tauN_le q n) a

/-- Fewer than `q + 3B + 1` ups up to `N ∧ n` for good children. -/
theorem dirCount_tauN_le (q B n : ℕ) (x : ClosSample) (hx : ∀ c, GoodC B (x.1 c)) :
    dirCount x.2 0 (tauN q n x) ≤ q + 3 * B := by
  match h : tauN q n x with
  | 0 => simp [dirCount]
  | t + 1 =>
    have ht : (t : ℕ∞) < closN q x.1 x.2 := by
      have : t < tauN q n x := by omega
      exact ((lt_tauN_iff q n t x).1 this).1
    have hb := closN_kup_bound q B x.1 x.2 (fun c k => (hx c).2 k) t ht
    have hs := (sum_dirCount x.2 t).2 0
    have : dirCount x.2 0 (t + 1) ≤ dirCount x.2 0 t + 1 := by
      unfold dirCount
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs <;> simp
    omega

theorem integrable_nat_bdd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : Ω → ℕ) (hf : Measurable f) (C : ℕ) (hC : ∀ ω, f ω ≤ C) :
    Integrable (fun ω => (f ω : ℝ)) P :=
  (integrable_const (C : ℝ)).mono' ((Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp
    hf).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast hC ω)

theorem measurable_dirCount_tauN (q n : ℕ) (a : Fin 4) :
    Measurable fun x : ClosSample => dirCount x.2 a (tauN q n x) :=
  measurable_comp_nat (fun x k => dirCount x.2 a k)
    (fun k => show Measurable ((fun D => dirCount D a k) ∘ Prod.snd) from
      (measurable_dirCount a k).comp measurable_snd) _ (measurable_tauN q n)

/-- `E(N ∧ n) ≤ 4 (q + 3B)` for good children. -/
theorem integral_tauN_le (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q B n : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) :
    ∫ x, (tauN q n x : ℝ) ∂closMeasure Q ≤ 4 * ((q : ℝ) + 3 * B) := by
  have hw := wald_tauN Q q n 0
  have hint := integrable_nat_bdd (closMeasure Q) _ (measurable_dirCount_tauN q n 0) n
    (fun x => (Finset.card_filter_le _ _).trans (by rw [Finset.card_range]; exact tauN_le q n x))
  have hle : ∫ x, (dirCount x.2 0 (tauN q n x) : ℝ) ∂closMeasure Q ≤ (q : ℝ) + 3 * B := by
    calc ∫ x, (dirCount x.2 0 (tauN q n x) : ℝ) ∂closMeasure Q
        ≤ ∫ _x, ((q + 3 * B : ℕ) : ℝ) ∂closMeasure Q :=
          integral_mono_ae hint (integrable_const _)
            (hgood.mono fun x hx => Nat.cast_le.mpr (dirCount_tauN_le q B n x hx))
      _ = (q : ℝ) + 3 * B := by simp
  linarith

theorem tauN_mono (q : ℕ) (x : ClosSample) : Monotone fun n => tauN q n x := by
  intro a b hab
  simp only
  rw [← ENat.natCast_le_natCast, tauN_cast, tauN_cast]
  exact min_le_min_left _ (by exact_mod_cast hab)

theorem iSup_tauN (q : ℕ) (x : ClosSample) :
    ⨆ n, ((tauN q n x : ℕ∞) : ℝ≥0∞) = (closN q x.1 x.2 : ℝ≥0∞) := by
  simp only [tauN_cast]
  generalize closN q x.1 x.2 = N
  induction N using ENat.recTopCoe with
  | top =>
    simp only [min_eq_right (le_top : ((_ : ℕ) : ℕ∞) ≤ ⊤), ENat.toENNReal_coe, ENat.toENNReal_top]
    exact ENNReal.iSup_natCast
  | coe k =>
    apply le_antisymm
    · exact iSup_le fun n => ENat.toENNReal_le.mpr (min_le_left _ _)
    · exact le_iSup_of_le k (by simp)

theorem lintegral_tauN (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q n : ℕ) :
    ∫⁻ x, ((tauN q n x : ℕ∞) : ℝ≥0∞) ∂closMeasure Q =
      ENNReal.ofReal (∫ x, (tauN q n x : ℝ) ∂closMeasure Q) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_nat_bdd _ _ (measurable_tauN q n) n (tauN_le q n))
    (Filter.Eventually.of_forall fun x => Nat.cast_nonneg _)]
  exact lintegral_congr fun x => by simp

theorem measurable_tauN_ennreal (q n : ℕ) :
    Measurable fun x : ClosSample => ((tauN q n x : ℕ∞) : ℝ≥0∞) :=
  (Measurable.of_discrete (f := fun k : ℕ => ((k : ℕ∞) : ℝ≥0∞))).comp (measurable_tauN q n)

/-- `E N ≤ 4 (q + 3B)` for good children. -/
theorem lintegral_closN_le (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q B : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) :
    ∫⁻ x, (closN q x.1 x.2 : ℝ≥0∞) ∂closMeasure Q ≤ ENNReal.ofReal (4 * ((q : ℝ) + 3 * B)) := by
  simp_rw [← iSup_tauN q]
  rw [lintegral_iSup (fun n => measurable_tauN_ennreal q n)
    (fun a b hab x => ENat.toENNReal_le.mpr (by exact_mod_cast tauN_mono q x hab))]
  exact iSup_le fun n => by
    rw [lintegral_tauN]
    exact ENNReal.ofReal_le_ofReal (integral_tauN_le Q q B n hgood)

theorem ae_closN_lt_top (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q B : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) :
    ∀ᵐ x ∂closMeasure Q, closN q x.1 x.2 < ⊤ := by
  have h := ae_lt_top' ((Measurable.of_discrete (f := fun y : ℕ∞ => (y : ℝ≥0∞))).comp
    (measurable_closN q)).aemeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_closN_le Q q B hgood))
  exact h.mono fun x hx => by simpa using hx

theorem dirCount_mono (D : ℕ → Fin 4) (a : Fin 4) : Monotone (dirCount D a) := fun _ _ h =>
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

theorem iSup_dirCount_tauN (q : ℕ) (a : Fin 4) (x : ClosSample) :
    ⨆ n, ((dirCount x.2 a (tauN q n x) : ℕ∞) : ℝ≥0∞) =
      (countAt x.2 a (closN q x.1 x.2) : ℝ≥0∞) := by
  apply le_antisymm
  · refine iSup_le fun n => ENat.toENNReal_le.mpr ?_
    exact (countAt_facts x.2 a).2.1 _ _ (by rw [tauN_cast]; exact min_le_left _ _)
  · unfold countAt
    rw [ENat.toENNReal_iSup]
    refine iSup_le fun n => ?_
    rw [ENat.toENNReal_iSup]
    refine iSup_le fun hn => le_iSup_of_le n (ENat.toENNReal_le.mpr ?_)
    have : tauN q n x = n := by
      rw [← ENat.natCast_inj, tauN_cast]
      exact min_eq_right hn
    rw [this]

/-- **Wald** for the closure: `E k_a(N) = E N / 4`. -/
theorem lintegral_countAt_closN (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q : ℕ)
    (a : Fin 4) :
    ∫⁻ x, (countAt x.2 a (closN q x.1 x.2) : ℝ≥0∞) ∂closMeasure Q =
      4⁻¹ * ∫⁻ x, (closN q x.1 x.2 : ℝ≥0∞) ∂closMeasure Q := by
  simp_rw [← iSup_dirCount_tauN q a, ← iSup_tauN q]
  have hm1 : ∀ n, Measurable fun x : ClosSample => ((dirCount x.2 a (tauN q n x) : ℕ∞) : ℝ≥0∞) :=
    fun n => (Measurable.of_discrete (f := fun k : ℕ => ((k : ℕ∞) : ℝ≥0∞))).comp
      (measurable_dirCount_tauN q n a)
  rw [lintegral_iSup hm1 (fun n m hnm x => ENat.toENNReal_le.mpr (by
      exact_mod_cast dirCount_mono x.2 a (tauN_mono q x hnm))),
    lintegral_iSup (fun n => measurable_tauN_ennreal q n)
      (fun a b hab x => ENat.toENNReal_le.mpr (by exact_mod_cast tauN_mono q x hab)),
    ENNReal.mul_iSup]
  refine iSup_congr fun n => ?_
  have h4 : (4⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 4) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  rw [lintegral_tauN, h4, ← ENNReal.ofReal_mul (by norm_num), ← wald_tauN Q q n a,
    ofReal_integral_eq_lintegral_ofReal
      (integrable_nat_bdd _ _ (measurable_dirCount_tauN q n a) n
        (fun x => (Finset.card_filter_le _ _).trans (by rw [Finset.card_range]; exact tauN_le q n x)))
      (Filter.Eventually.of_forall fun x => Nat.cast_nonneg _)]
  exact lintegral_congr fun x => by simp

/-! ## The identity `3 E X = q + ∑_c E[G_c(e_c) - e_c/3]` -/

/-- `G_c(e_c)`. -/
noncomputable def gE (q : ℕ) (c : Fin 3) (x : ClosSample) : ℕ∞ :=
  x.1 c ((closE q x.1 x.2 c).toNat)

theorem measurable_gE (q : ℕ) (c : Fin 3) : Measurable (gE q c) :=
  measurable_comp_nat (fun x k => x.1 c k) (measurable_child c) _
    ((Measurable.of_discrete (f := fun y : ℕ∞ => y.toNat)).comp (measurable_closE q c))

theorem measurable_gE_enn (q : ℕ) (c : Fin 3) :
    Measurable fun x : ClosSample => ((gE q c x : ℕ∞) : ℝ≥0∞) :=
  (Measurable.of_discrete (f := fun y : ℕ∞ => (y : ℝ≥0∞))).comp (measurable_gE q c)

theorem measurable_closE_enn (q : ℕ) (c : Fin 3) :
    Measurable fun x : ClosSample => ((closE q x.1 x.2 c : ℕ∞) : ℝ≥0∞) :=
  (Measurable.of_discrete (f := fun y : ℕ∞ => (y : ℝ≥0∞))).comp (measurable_closE q c)

theorem measurable_closX_enn (q : ℕ) :
    Measurable fun x : ClosSample => ((closX q x.1 x.2 : ℕ∞) : ℝ≥0∞) :=
  (Measurable.of_discrete (f := fun y : ℕ∞ => (y : ℝ≥0∞))).comp (measurable_closX q)

theorem toENNReal_sum3 (f : Fin 3 → ℕ∞) : ((∑ c, f c : ℕ∞) : ℝ≥0∞) = ∑ c, (f c : ℝ≥0∞) := by
  simp only [Fin.sum_univ_three, ENat.toENNReal_add]

/-- At a finite end: `N = q + ∑_c G_c(e_c)` and `N = X + ∑_c e_c`. -/
theorem ae_closN_eq (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q B : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) :
    ∀ᵐ x ∂closMeasure Q, closN q x.1 x.2 < ⊤ ∧
      closN q x.1 x.2 = q + ∑ c, gE q c x ∧
      closN q x.1 x.2 = closX q x.1 x.2 + ∑ c, closE q x.1 x.2 c := by
  filter_upwards [ae_closN_lt_top Q q B hgood, hgood] with x hN hx
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hN.ne
  have h1 := closT_closN q x.1 x.2 (fun c => (hx c).1) n hn.symm
  have h2 := sum_countAt_closN q n x.1 x.2 hn.symm
  have he : ∀ c, closE q x.1 x.2 c = dirCount x.2 c.succ n := fun c => by
    unfold closE
    rw [← hn]
    exact (countAt_facts _ _).1 n
  refine ⟨hN, ?_, by rw [← hn]; exact h2.symm⟩
  rw [← hn]
  unfold gE
  simp_rw [he, ENat.toNat_natCast]
  exact h1.2.symm

theorem lintegral_closN_eq (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q B : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) :
    ∫⁻ x, (closN q x.1 x.2 : ℝ≥0∞) ∂closMeasure Q =
      q + ∑ c, ∫⁻ x, (gE q c x : ℝ≥0∞) ∂closMeasure Q := by
  rw [lintegral_congr_ae ((ae_closN_eq Q q B hgood).mono fun x hx => by
    rw [hx.2.1, ENat.toENNReal_add, toENNReal_sum3, ENat.toENNReal_coe])]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_finsetSum _ fun c _ => (measurable_gE_enn q c)]

theorem lintegral_closN_eq' (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q B : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) :
    ∫⁻ x, (closN q x.1 x.2 : ℝ≥0∞) ∂closMeasure Q =
      ∫⁻ x, (closX q x.1 x.2 : ℝ≥0∞) ∂closMeasure Q +
        ∑ c, ∫⁻ x, (closE q x.1 x.2 c : ℝ≥0∞) ∂closMeasure Q := by
  rw [lintegral_congr_ae ((ae_closN_eq Q q B hgood).mono fun x hx => by
    rw [hx.2.2, ENat.toENNReal_add, toENNReal_sum3])]
  rw [lintegral_add_left (measurable_closX_enn q),
    lintegral_finsetSum _ fun c _ => measurable_closE_enn q c]

theorem integral_toNat {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℕ∞)
    (hf : Measurable f) (hfin : ∀ᵐ ω ∂P, f ω ≠ ⊤) :
    ∫ ω, ((f ω).toNat : ℝ) ∂P = (∫⁻ ω, (f ω : ℝ≥0∞) ∂P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg _)
    ((Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp hf).aestronglyMeasurable]
  congr 1
  refine lintegral_congr_ae (hfin.mono fun ω h => ?_)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
  show ENNReal.ofReal ((f ω).toNat : ℝ) = (f ω : ℝ≥0∞)
  rw [← hn, ENat.toNat_natCast, ENNReal.ofReal_natCast, ENat.toENNReal_coe]

/-- **The identity of the proof of Lemma 10.5 of the paper**:
`3 E X = q + ∑_c (E G_c(e_c) - E e_c / 3)`. -/
theorem closure_identity (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q B : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) :
    3 * ∫ x, ((closX q x.1 x.2).toNat : ℝ) ∂closMeasure Q =
      q + ∑ c, (∫ x, ((gE q c x).toNat : ℝ) ∂closMeasure Q -
        1 / 3 * ∫ x, ((closE q x.1 x.2 c).toNat : ℝ) ∂closMeasure Q) := by
  have hae := ae_closN_eq Q q B hgood
  have hX : ∀ᵐ x ∂closMeasure Q, closX q x.1 x.2 ≠ ⊤ := hae.mono fun x hx => by
    intro h; have := hx.2.2; rw [h, top_add] at this; exact hx.1.ne this
  have hE : ∀ c, ∀ᵐ x ∂closMeasure Q, closE q x.1 x.2 c ≠ ⊤ := fun c => hae.mono fun x hx => by
    intro h
    have h3 := hx.2.2
    have : closE q x.1 x.2 c ≤ closN q x.1 x.2 := by
      rw [h3]
      exact le_add_left (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ c))
    rw [h, top_le_iff] at this
    exact hx.1.ne this
  have hG : ∀ c, ∀ᵐ x ∂closMeasure Q, gE q c x ≠ ⊤ := fun c => hae.mono fun x hx => by
    intro h
    have h3 := hx.2.1
    have : gE q c x ≤ closN q x.1 x.2 := by
      rw [h3]
      exact le_add_left (Finset.single_le_sum (f := fun c => gE q c x)
        (fun _ _ => bot_le) (Finset.mem_univ c))
    rw [h, top_le_iff] at this
    exact hx.1.ne this
  rw [integral_toNat _ _ (measurable_closX q) hX]
  simp_rw [fun c => integral_toNat _ _ (measurable_gE q c) (hG c),
    fun c => integral_toNat _ _ (measurable_closE q c) (hE c)]
  have hL := lintegral_closN_le Q q B hgood
  have hLt : ∫⁻ x, (closN q x.1 x.2 : ℝ≥0∞) ∂closMeasure Q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL
  have hW0 := lintegral_countAt_closN Q q 0
  have hWc := fun c : Fin 3 => lintegral_countAt_closN Q q c.succ
  have h1 := lintegral_closN_eq Q q B hgood
  have h2 := lintegral_closN_eq' Q q B hgood
  set L := ∫⁻ x, (closN q x.1 x.2 : ℝ≥0∞) ∂closMeasure Q with hLdef
  have hXv : ∫⁻ x, (closX q x.1 x.2 : ℝ≥0∞) ∂closMeasure Q = 4⁻¹ * L := hW0
  have hEv : ∀ c, ∫⁻ x, (closE q x.1 x.2 c : ℝ≥0∞) ∂closMeasure Q = 4⁻¹ * L := hWc
  have hgfin : ∀ c, ∫⁻ x, (gE q c x : ℝ≥0∞) ∂closMeasure Q ≠ ⊤ := fun c =>
    ne_top_of_le_ne_top hLt (by
      rw [h1]
      exact le_add_left (Finset.single_le_sum (f := fun c => ∫⁻ x, (gE q c x : ℝ≥0∞) ∂closMeasure Q)
        (fun _ _ => bot_le) (Finset.mem_univ c)))
  have hsum : (L).toReal = q + ∑ c, (∫⁻ x, (gE q c x : ℝ≥0∞) ∂closMeasure Q).toReal := by
    rw [h1, ENNReal.toReal_add (by simp) (ENNReal.sum_ne_top.2 fun c _ => hgfin c),
      ENNReal.toReal_sum fun c _ => hgfin c]
    simp
  rw [hXv]
  simp_rw [hEv]
  have hs : ∑ c, (∫⁻ x, (gE q c x : ℝ≥0∞) ∂closMeasure Q).toReal = L.toReal - q := by linarith
  rw [Finset.sum_sub_distrib, hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num
  ring

end FrogModel.D3.Iface
