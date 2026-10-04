module

public import FrogModel.D3.LaneB.ClosMean

@[expose] public section

/-!
# Lemma 10.6 of the paper, first bound

`L_{j,J} ≤ E G_m(J) P(e_1 < J)`: for each child, on `{e_c = e}` with `e < J` (an event of the
child's prefix up to `e` and of the rest of the closure) future domination (Lemma 10.4,
`future_dom`) bounds `E[G_c(J) - G_c(e)]` by `P(e_c = e) E G_m(J - e) ≤ P(e_c = e) E G_m(J)`; the
three children have the same law of `e_c` by the symmetry of the closure (`closMeasure_perm`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-! ## The first bound of Lemma 10.6 of the paper -/

/-- `{e_c = e}` reads the child `c` up to `e` only. -/
theorem closE_eq_iff_of_prefix (q e : ℕ) (c : Fin 3) (G G' : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4)
    (hG : ∀ c', c' ≠ c → G c' = G' c') (hc : ∀ k ≤ e, G c k = G' c k) :
    closE q G D c = e ↔ closE q G' D c = e := by
  have h1 := closE_stop q e c G G' D hG hc
  cases e with
  | zero =>
    have key : ∀ y : ℕ∞, y = ((0 : ℕ) : ℕ∞) ↔ ¬ (((0 : ℕ) : ℕ∞) < y) := by
      intro y; simp [pos_iff_ne_zero]
    rw [key, key, h1]
  | succ e =>
    have h2 := closE_stop q e c G G' D hG (fun k hk => hc k (by omega))
    have key : ∀ y : ℕ∞, y = ((e + 1 : ℕ) : ℕ∞) ↔
        (e : ℕ∞) < y ∧ ¬ (((e + 1 : ℕ) : ℕ∞) < y) := by
      intro y
      constructor
      · rintro rfl
        exact ⟨ENat.natCast_lt_natCast.2 (Nat.lt_succ_self e), lt_irrefl _⟩
      · rintro ⟨h1, h2⟩
        refine le_antisymm (not_lt.1 h2) ?_
        have := Order.add_one_le_of_lt h1
        simpa using this
    rw [key, key, h1, h2]

/-- Future domination in the closure (Lemma 10.4 of the paper for the child `c`, the rest
independent). -/
theorem future_dom_closure (hfd : future_dom) (m q : ℕ) (c : Fin 3) (e J : ℕ)
    (heJ : e ≤ J) :
    ∫⁻ x in {x : ClosSample | closE q x.1 x.2 c = e}, (x.1 c J : ℝ≥0∞)
        ∂closMeasure (curveLaw m) ≤
      ∫⁻ x in {x : ClosSample | closE q x.1 x.2 c = e}, (x.1 c e : ℝ≥0∞)
          ∂closMeasure (curveLaw m) +
        closMeasure (curveLaw m) {x | closE q x.1 x.2 c = e} *
          ∫⁻ G, (G (J - e) : ℝ≥0∞) ∂curveLaw m := by
  set Q := curveLaw m
  set U : (ℕ → ℕ∞) × ClosSample → ClosSample := fun p => (Function.update p.2.1 c p.1, p.2.2)
    with hUdef
  have hU : Measurable U :=
    ((measurable_update' (a := c)).comp ((measurable_fst.comp measurable_snd).prodMk
      measurable_fst)).prodMk (measurable_snd.comp measurable_snd)
  have hmap : (Q.prod (closMeasure Q)).map U = closMeasure Q := prod_update_map Q dirMeasure c
  have hA : MeasurableSet {x : ClosSample | closE q x.1 x.2 c = e} :=
    (measurable_closE q c) (measurableSet_singleton _)
  set B : Set ((Fin (e + 1) → ℕ∞) × ClosSample) :=
    {hr | closE q (Function.update hr.2.1 c (extPrefix e hr.1)) hr.2.2 c = e}
  have hB : MeasurableSet B := by
    have hm : Measurable fun hr : (Fin (e + 1) → ℕ∞) × ClosSample =>
        (Function.update hr.2.1 c (extPrefix e hr.1), hr.2.2) :=
      ((measurable_update' (a := c)).comp ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_extPrefix e).comp measurable_fst))).prodMk
          (measurable_snd.comp measurable_snd)
    exact ((measurable_closE q c).comp hm) (measurableSet_singleton _)
  have hpre : U ⁻¹' {x : ClosSample | closE q x.1 x.2 c = e} =
      {p : (ℕ → ℕ∞) × ClosSample | ((fun l : Fin (e + 1) => p.1 l), p.2) ∈ B} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, B, hUdef]
    refine closE_eq_iff_of_prefix q e c _ _ p.2.2
      (fun c' hc' => by simp [Function.update_of_ne hc']) (fun k hk => ?_)
    simp [extPrefix, Nat.min_eq_left hk]
  have hf : ∀ k, Measurable fun x : ClosSample => (x.1 c k : ℝ≥0∞) := fun k =>
    (Measurable.of_discrete (f := fun y : ℕ∞ => (y : ℝ≥0∞))).comp (measurable_child c k)
  rw [← hmap, setLIntegral_map hA (hf J) hU, setLIntegral_map hA (hf e) hU,
    Measure.map_apply hU hA, hpre]
  simp only [hUdef, Function.update_self]
  exact future_dom_prod Q (closMeasure Q) e J (hfd m e J heJ) B hB

theorem lintegral_child_ne_top (P : Measure ClosSample) [IsFiniteMeasure P] (B : ℕ)
    (hgood : ∀ᵐ x ∂P, ∀ c, GoodC B (x.1 c)) (c : Fin 3) (k : ℕ) (A : Set ClosSample) :
    ∫⁻ x in A, (x.1 c k : ℝ≥0∞) ∂P ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _ in A, ((k + B : ℕ) : ℝ≥0∞) ∂P) ?_
    (lintegral_mono_ae ((ae_restrict_of_ae hgood).mono fun x hx => ?_))
  · rw [setLIntegral_const]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · have h := ENat.toENNReal_le.mpr ((hx c).2 k)
    simpa using h

theorem lintegral_curve_ne_top (hmeas : measurable_plantedPair) (m k : ℕ) :
    ∫⁻ G, (G k : ℝ≥0∞) ∂curveLaw m ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _, ((k + (3 ^ (m + 1) - 1) / 2 : ℕ) : ℝ≥0∞) ∂curveLaw m) ?_
    (lintegral_mono_ae ((ae_goodC hmeas m).mono fun G hG => ?_))
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · have h := ENat.toENNReal_le.mpr (hG.2 k)
    simpa using h

theorem meanG_eq_curve (hmeas : measurable_plantedPair) (m k : ℕ) :
    meanG m k = (∫⁻ G, (G k : ℝ≥0∞) ∂curveLaw m).toReal := by
  rw [meanG, lintegral_plantedG_eq hmeas]

theorem meanG_mono (hmeas : measurable_plantedPair) (m : ℕ) : Monotone (meanG m) := by
  intro a b hab
  rw [meanG_eq_curve hmeas, meanG_eq_curve hmeas]
  exact ENNReal.toReal_mono (lintegral_curve_ne_top hmeas m b)
    (lintegral_mono_ae ((ae_goodC hmeas m).mono fun G hG => ENat.toENNReal_le.mpr (hG.1 hab)))

/-- One end count: `E[1{e_c = e} (G_c(J) - G_c(e))] ≤ P(e_c = e) E G_m(J - e)`. -/
theorem lemma8a_term (hfd : future_dom) (hmeas : measurable_plantedPair)
    (m q : ℕ) (c : Fin 3) (e J : ℕ) (heJ : e ≤ J) :
    ∫ x, {x : ClosSample | closE q x.1 x.2 c = e}.indicator
        (fun x => ((x.1 c J).toNat : ℝ) - (x.1 c e).toNat) x ∂closMeasure (curveLaw m) ≤
      (closMeasure (curveLaw m) {x | closE q x.1 x.2 c = e}).toReal * meanG m (J - e) := by
  set Q := curveLaw m
  set B0 := (3 ^ (m + 1) - 1) / 2
  have hgood := ae_closGood Q B0 (ae_goodC hmeas m)
  have hA : MeasurableSet {x : ClosSample | closE q x.1 x.2 c = e} :=
    (measurable_closE q c) (measurableSet_singleton _)
  set A := {x : ClosSample | closE q x.1 x.2 c = e}
  have hfinite : ∀ k, ∀ᵐ x ∂((closMeasure Q).restrict A), x.1 c k ≠ ⊤ := fun k =>
    ae_restrict_of_ae (hgood.mono fun x hx =>
      ne_top_of_le_ne_top (ENat.natCast_ne_top _) ((hx c).2 k))
  have hint : ∀ k, Integrable (fun x : ClosSample => ((x.1 c k).toNat : ℝ))
      ((closMeasure Q).restrict A) := fun k =>
    (integrable_const ((k + B0 : ℕ) : ℝ)).mono'
      ((Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp
        (measurable_child c k)).aestronglyMeasurable
      ((ae_restrict_of_ae hgood).mono fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast toNat_le_of_le_natCast ((hx c).2 k))
  rw [integral_indicator hA, integral_sub (hint J) (hint e),
    integral_toNat _ _ (measurable_child c J) (hfinite J),
    integral_toNat _ _ (measurable_child c e) (hfinite e), meanG_eq_curve hmeas]
  have hfd' := future_dom_closure hfd m q c e J heJ
  have hfe := lintegral_child_ne_top (closMeasure Q) B0 hgood c e A
  have hfc := lintegral_curve_ne_top hmeas m (J - e)
  have hR : ∫⁻ x in A, (x.1 c e : ℝ≥0∞) ∂closMeasure Q +
      closMeasure Q A * ∫⁻ G, (G (J - e) : ℝ≥0∞) ∂Q ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hfe, ENNReal.mul_ne_top (measure_ne_top _ _) hfc⟩
  have h := ENNReal.toReal_mono hR hfd'
  rw [ENNReal.toReal_add hfe (ENNReal.mul_ne_top (measure_ne_top _ _) hfc),
    ENNReal.toReal_mul] at h
  linarith

/-- The ends `e_c < J` are the disjoint ends `e_c = e`, `e < J`. -/
theorem closE_lt_eq_iUnion (q J : ℕ) (c : Fin 3) :
    {x : ClosSample | closE q x.1 x.2 c < J} =
      ⋃ e ∈ Finset.range J, {x : ClosSample | closE q x.1 x.2 c = e} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · intro h
    refine ⟨(closE q x.1 x.2 c).toNat, ?_, (ENat.natCast_toNat (ne_top_of_lt h)).symm⟩
    rw [← ENat.natCast_lt_natCast, ENat.natCast_toNat (ne_top_of_lt h)]
    exact h
  · rintro ⟨e, he, h⟩
    rw [h]
    exact_mod_cast he

/-- `E L_c ≤ E G_m(J) P(e_c < J)` for one child (proof of Lemma 10.6 of the paper). -/
theorem lemma8a_child (hfd : future_dom) (hmeas : measurable_plantedPair)
    (m j J : ℕ) (c : Fin 3) :
    ∫ x, (((x.1 c J).toNat : ℝ) - J / 3 -
      (((x.1 c (minE (closE (j + 1) x.1 x.2 c) J)).toNat : ℝ) -
        (minE (closE (j + 1) x.1 x.2 c) J : ℝ) / 3)) ∂closMeasure (curveLaw m) ≤
      meanG m J * (closMeasure (curveLaw m) {x | closE (j + 1) x.1 x.2 c < J}).toReal := by
  set Q := curveLaw m
  set B0 := (3 ^ (m + 1) - 1) / 2
  have hgood := ae_closGood Q B0 (ae_goodC hmeas m)
  have hA : ∀ e : ℕ, MeasurableSet {x : ClosSample | closE (j + 1) x.1 x.2 c = e} := fun e =>
    (measurable_closE (j + 1) c) (measurableSet_singleton _)
  have htoNat : ∀ k, Measurable fun x : ClosSample => ((x.1 c k).toNat : ℝ) := fun k =>
    (Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp (measurable_child c k)
  have hbdk : ∀ k, ∀ᵐ x ∂closMeasure Q, ((x.1 c k).toNat : ℝ) ≤ (k + B0 : ℕ) := fun k =>
    hgood.mono fun x hx => by exact_mod_cast toNat_le_of_le_natCast ((hx c).2 k)
  -- the pathwise bound by the sum over the end counts
  have hint_ind : ∀ e ∈ Finset.range J, Integrable ({x : ClosSample | closE (j + 1) x.1 x.2 c = e}.indicator
      (fun x => ((x.1 c J).toNat : ℝ) - (x.1 c e).toNat)) (closMeasure Q) := by
    intro e he
    refine Integrable.indicator ?_ (hA e)
    refine (integrable_const ((2 * (J + B0) : ℕ) : ℝ)).mono' ((htoNat J).sub (htoNat e)).aestronglyMeasurable ?_
    filter_upwards [hbdk J, hbdk e] with x h1 h2
    have he' : e < J := Finset.mem_range.1 he
    have h0 : (0 : ℝ) ≤ (x.1 c J).toNat := Nat.cast_nonneg _
    have h0' : (0 : ℝ) ≤ (x.1 c e).toNat := Nat.cast_nonneg _
    have hle : ((e + B0 : ℕ) : ℝ) ≤ (J + B0 : ℕ) := by exact_mod_cast (by omega : e + B0 ≤ J + B0)
    rw [Real.norm_eq_abs, abs_le]
    push_cast at h1 h2 hle ⊢
    constructor <;> linarith
  have hm : Measurable fun x : ClosSample => minE (closE (j + 1) x.1 x.2 c) J :=
    (Measurable.of_discrete (f := fun y : ℕ∞ => minE y J)).comp (measurable_closE (j + 1) c)
  have hint_L : Integrable (fun x : ClosSample => (((x.1 c J).toNat : ℝ) - J / 3 -
      (((x.1 c (minE (closE (j + 1) x.1 x.2 c) J)).toNat : ℝ) -
        (minE (closE (j + 1) x.1 x.2 c) J : ℝ) / 3))) (closMeasure Q) := by
    have h1 := integrable_osVal_bdd Q B0 hgood c _ hm J (fun x => minE_le _ J)
    have h2 : Integrable (fun x : ClosSample => ((x.1 c J).toNat : ℝ) - (J : ℝ) / 3)
        (closMeasure Q) :=
      ((integrable_const ((J + B0 : ℕ) : ℝ)).mono' (htoNat J).aestronglyMeasurable
        ((hbdk J).mono fun x hx => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]; exact hx)).sub
        (integrable_const _)
    exact h2.sub h1
  have hpt : ∀ᵐ x ∂closMeasure Q, (((x.1 c J).toNat : ℝ) - J / 3 -
      (((x.1 c (minE (closE (j + 1) x.1 x.2 c) J)).toNat : ℝ) -
        (minE (closE (j + 1) x.1 x.2 c) J : ℝ) / 3)) ≤
      ∑ e ∈ Finset.range J, {x : ClosSample | closE (j + 1) x.1 x.2 c = e}.indicator
        (fun x => ((x.1 c J).toNat : ℝ) - (x.1 c e).toNat) x := by
    filter_upwards [hgood] with x hx
    refine (lemma8a_pathwise (x.1 c) (hx c).1 B0 (hx c).2 (closE (j + 1) x.1 x.2 c) J).trans_eq ?_
    split_ifs with hlt
    · obtain ⟨e0, he0⟩ : ∃ e0 : ℕ, closE (j + 1) x.1 x.2 c = e0 :=
        ⟨(closE (j + 1) x.1 x.2 c).toNat, (ENat.natCast_toNat (ne_top_of_lt hlt)).symm⟩
      have he0J : e0 < J := by rw [he0] at hlt; exact_mod_cast hlt
      rw [Finset.sum_eq_single e0]
      · rw [Set.indicator_of_mem (show x ∈ {x : ClosSample | closE (j + 1) x.1 x.2 c = e0}
          from he0), he0, ENat.toNat_natCast]
      · intro b _ hb
        refine Set.indicator_of_notMem ?_ _
        simp only [Set.mem_ofPred_eq, he0]
        exact fun h => hb (by exact_mod_cast h.symm)
      · intro h
        exact absurd (Finset.mem_range.2 he0J) h
    · symm
      refine Finset.sum_eq_zero fun e he => Set.indicator_of_notMem ?_ _
      simp only [Set.mem_ofPred_eq]
      intro h
      rw [h] at hlt
      exact hlt (by exact_mod_cast Finset.mem_range.1 he)
  refine (integral_mono_ae hint_L (integrable_finsetSum _ hint_ind) hpt).trans ?_
  rw [integral_finsetSum _ hint_ind, closE_lt_eq_iUnion, measure_biUnion_finset
    (fun e _ e' _ hee' => Set.disjoint_left.2 fun x h1 h2 => hee' (by
      have := h1.symm.trans h2; exact_mod_cast this)) (fun e _ => hA e),
    ENNReal.toReal_sum (fun e _ => measure_ne_top _ _), Finset.mul_sum]
  refine Finset.sum_le_sum fun e he => ?_
  refine (lemma8a_term hfd hmeas m (j + 1) c e J (Finset.mem_range.1 he).le).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (meanG_mono hmeas m (Nat.sub_le J e)) ENNReal.toReal_nonneg

/-- The children are exchangeable: `P(e_c < J) = P(e_1 < J)`. -/
theorem prob_closE_symm (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q J : ℕ) (c : Fin 3) :
    closMeasure Q {x | closE q x.1 x.2 c < J} = closMeasure Q {x | closE q x.1 x.2 0 < J} := by
  set σ := Equiv.swap (0 : Fin 3) c
  set T : ClosSample → ClosSample := fun x =>
    ((fun c' => x.1 (σ c')), (fun i => Fin.cases 0 (fun c' => (σ.symm c').succ) (x.2 i))) with hT
  have hTm : Measurable T :=
    (measurable_pi_iff.mpr fun c' => (measurable_pi_apply (σ c')).comp measurable_fst).prodMk
      (measurable_pi_iff.mpr fun i => (Measurable.of_discrete
        (f := fun b : Fin 4 => (Fin.cases 0 (fun c' => (σ.symm c').succ) b : Fin 4))).comp
          ((measurable_pi_apply i).comp measurable_snd))
  have hs : MeasurableSet {x : ClosSample | closE q x.1 x.2 0 < J} :=
    (measurable_closE q 0) (MeasurableSet.of_discrete (s := {y : ℕ∞ | y < J}))
  conv_rhs => rw [← closMeasure_perm Q σ]
  rw [Measure.map_apply hTm hs]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hT]
  rw [closE_perm σ q x.1 x.2 0]
  simp [σ]

/-- **Lemma 10.6 of the paper**, first bound, from measurability and future domination
(Lemma 10.4). -/
theorem lemma8a_of (hmeas : measurable_plantedPair) (hfd : future_dom) :
    lemma8a := by
  intro m j J hj
  unfold lossL closProb
  have h0 := lemma8a_child hfd hmeas m j J 0
  have h1 := lemma8a_child hfd hmeas m j J 1
  have h2 := lemma8a_child hfd hmeas m j J 2
  rw [prob_closE_symm] at h1 h2
  rw [Fin.sum_univ_three]
  linarith

end FrogModel.D3.Iface
