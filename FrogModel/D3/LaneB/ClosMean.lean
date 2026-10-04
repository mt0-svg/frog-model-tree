module

public import FrogModel.D3.LaneB.OptSampling

@[expose] public section

/-!
# The closure means, Lemmas 10.5 and 10.8 of the paper

From optional sampling in the closure: Lemma 10.5, `E G_m(J) + (1 + j - J)/3 - L_{j,J} ≤ E G_(m+1)(j)`
(`d1_of`), and Lemma 10.8, a dead child (`lemmaS2'_of`), where the stopping index `e'_c` does not read
the child `c` and the child is replaced by an independent copy carrying its own data.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-! ## Optional stopping (Lemma 10.5 of the paper) -/


/-- `E G_c(J) = E G_m(J)` for a child of the closure. -/
theorem integral_child_toNat (hmeas : measurable_plantedPair) (m : ℕ) (c : Fin 3)
    (J : ℕ) :
    ∫ x, ((x.1 c J).toNat : ℝ) ∂closMeasure (curveLaw m) = meanG m J := by
  have hmp := measurePreserving_child (curveLaw m) c
  have hg : Measurable fun G : ℕ → ℕ∞ => ((G J).toNat : ℝ) :=
    (Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp (measurable_pi_apply J)
  have hfin : ∀ᵐ G ∂curveLaw m, G J ≠ ⊤ := (ae_goodC hmeas m).mono fun G hG =>
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hG.2 J)
  calc ∫ x, ((x.1 c J).toNat : ℝ) ∂closMeasure (curveLaw m)
      = ∫ G, ((G J).toNat : ℝ) ∂(closMeasure (curveLaw m)).map (fun x => x.1 c) :=
        (integral_map hmp.measurable.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ G, ((G J).toNat : ℝ) ∂curveLaw m := by rw [hmp.map_eq]
    _ = meanG m J := by
        rw [integral_toNat _ _ (measurable_pi_apply J) hfin, meanG, lintegral_plantedG_eq hmeas]

theorem integrable_le_closN (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q B : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) (f : ClosSample → ℕ∞) (hf : Measurable f)
    (hle : ∀ᵐ x ∂closMeasure Q, f x ≤ closN q x.1 x.2) :
    Integrable (fun x => ((f x).toNat : ℝ)) (closMeasure Q) :=
  (integrable_closN Q q B hgood).mono'
    ((Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp hf).aestronglyMeasurable
    (by
      filter_upwards [hle, ae_le_closN Q q B hgood] with x h1 h2
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast ENat.toNat_le_toNat h1 h2.1.ne)

theorem integrable_osVal_bdd (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (B : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) (c : Fin 3) (s : ClosSample → ℕ)
    (hs : Measurable s) (J : ℕ) (hsJ : ∀ x, s x ≤ J) :
    Integrable (osVal c s) (closMeasure Q) :=
  (integrable_const ((2 * J + B : ℕ) : ℝ)).mono' (measurable_osVal c s hs).aestronglyMeasurable
    (hgood.mono fun x hx => by
      have h1 : ((x.1 c (s x)).toNat : ℝ) ≤ (s x + B : ℕ) := by
        exact_mod_cast toNat_le_of_le_natCast ((hx c).2 (s x))
      have h2 : ((s x : ℕ) : ℝ) ≤ J := by exact_mod_cast hsJ x
      have h0 : (0 : ℝ) ≤ (x.1 c (s x)).toNat := Nat.cast_nonneg _
      have h0' : (0 : ℝ) ≤ (s x : ℕ) := Nat.cast_nonneg _
      push_cast at h1 ⊢
      rw [Real.norm_eq_abs, abs_le]
      unfold osVal
      constructor <;> linarith)

theorem minE_le (e : ℕ∞) (J : ℕ) : minE e J ≤ J := by
  unfold minE
  exact toNat_le_of_le_natCast (min_le_right _ _)

theorem measurable_minE_closE (q : ℕ) (c : Fin 3) (J : ℕ) :
    Measurable fun x : ClosSample => minE (closE q x.1 x.2 c) J :=
  (Measurable.of_discrete (f := fun y : ℕ∞ => minE y J)).comp (measurable_closE q c)

/-- **Lemma 10.5 of the paper** from the statements of measurability, of the law of the closure
(Lemma 10.1) and of the coins (Lemma 10.3). -/
theorem d1_of (hmeas : measurable_plantedPair) (hsucc : curveLaw_succ)
    (hcoin : coin_coupling) : d1 := by
  intro m j J hj
  set Q := curveLaw m with hQ
  set B := (3 ^ (m + 1) - 1) / 2
  have hgoodQ : ∀ᵐ G ∂Q, GoodC B G := ae_goodC hmeas m
  have hgood := ae_closGood Q B hgoodQ
  obtain ⟨μ, hμ, hfst, hξ, hindep, hae⟩ := hcoin m
  have hind : ∀ i, IndepFun (fun z => z.2 i) (fun z => fun l : Fin (i + 1) => z.1 l) μ :=
    fun i => (hindep i).comp measurable_id measurable_fst
  have hinc : ∀ᵐ z ∂μ, ∀ i, z.1 i + (if z.2 i then 1 else 0) ≤ z.1 (i + 1) :=
    hae.mono fun z hz => hz.2
  have hbd : ∀ᵐ z ∂μ, ∀ i, z.1 i ≤ ((i + B : ℕ) : ℕ∞) := by
    have h : ∀ᵐ G ∂μ.map Prod.fst, GoodC B G := by rw [hfst]; exact hgoodQ
    exact (ae_of_ae_map measurable_fst.aemeasurable h).mono fun z hz => hz.2
  have hid := closure_identity Q (j + 1) B hgood
  have hos := fun c => os_closure_limit Q μ hfst hξ hind hinc B hbd hgood (j + 1) c J
  have hae' := ae_le_closN Q (j + 1) B hgood
  rw [meanG_succ_eq hmeas hsucc m j hj,
    ← integral_toNat _ _ (measurable_closX (j + 1)) (hae'.mono fun x hx =>
      ne_top_of_le_ne_top hx.1.ne hx.2.1)]
  have hlin : ∀ c, ∫ x, (((gE (j + 1) c x).toNat : ℝ) - ((closE (j + 1) x.1 x.2 c).toNat : ℝ) / 3)
      ∂closMeasure Q = ∫ x, ((gE (j + 1) c x).toNat : ℝ) ∂closMeasure Q -
        1 / 3 * ∫ x, ((closE (j + 1) x.1 x.2 c).toNat : ℝ) ∂closMeasure Q := by
    intro c
    rw [integral_sub (integrable_le_closN Q (j + 1) B hgood _ (measurable_gE (j + 1) c)
        (hae'.mono fun x hx => (hx.2.2 c).2))
      ((integrable_le_closN Q (j + 1) B hgood _ (measurable_closE (j + 1) c)
        (hae'.mono fun x hx => (hx.2.2 c).1)).div_const 3), integral_div]
    ring
  have hloss : lossL m j J = 1 / 3 * ∑ c, (meanG m J - J / 3 -
      ∫ x, osVal c (fun x => minE (closE (j + 1) x.1 x.2 c) J) x ∂closMeasure Q) := by
    unfold lossL
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    have hiJ : Integrable (fun x : ClosSample => ((x.1 c J).toNat : ℝ)) (closMeasure Q) :=
      (integrable_const ((J + B : ℕ) : ℝ)).mono'
        ((Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp
          (measurable_child c J)).aestronglyMeasurable
        (hgood.mono fun x hx => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
          exact_mod_cast toNat_le_of_le_natCast ((hx c).2 J))
    have hio := integrable_osVal_bdd Q B hgood c _ (measurable_minE_closE (j + 1) c J) J
      (fun x => minE_le _ J)
    have hiJ' : Integrable (fun x : ClosSample => ((x.1 c J).toNat : ℝ) - (J : ℝ) / 3)
        (closMeasure Q) := hiJ.sub (integrable_const _)
    have e1 := integral_sub hiJ' hio
    have e2 := integral_sub hiJ (integrable_const ((J : ℝ) / 3))
    have e3 := integral_child_toNat hmeas m c J
    simp only [integral_const, probReal_univ, one_smul] at e2
    unfold osVal at e1 ⊢
    rw [e1, e2, e3]
  rw [hloss]
  have h0 := hos 0
  have h1 := hos 1
  have h2 := hos 2
  rw [hlin] at h0 h1 h2
  simp only [Fin.sum_univ_three] at hid ⊢
  push_cast at hid ⊢
  linarith

/-! ## A dead child (Lemma 10.8 of the paper) -/

/-- Replacing the curve of the child `c` by an independent one: for `h` that reads nothing else of
the child `c`, `E h(G_c, y) = E h(G, y)` with `G` of law `Q` independent. -/
theorem integral_replace_child {Ωc R : Type*} [MeasurableSpace Ωc] [MeasurableSpace R]
    (μc : Measure ((ℕ → ℕ∞) × Ωc)) [IsProbabilityMeasure μc] (ρ : Measure R)
    [IsProbabilityMeasure ρ] (c : Fin 3)
    (h : (ℕ → ℕ∞) × ((Fin 3 → (ℕ → ℕ∞) × Ωc) × R) → ℝ) (hh : Measurable h)
    (hloc : ∀ G y y', (∀ c', c' ≠ c → y.1 c' = y'.1 c') → y.2 = y'.2 → h (G, y) = h (G, y')) :
    ∫ y, h ((y.1 c).1, y) ∂((Measure.pi fun _ : Fin 3 => μc).prod ρ) =
      ∫ p, h p ∂((μc.map Prod.fst).prod ((Measure.pi fun _ : Fin 3 => μc).prod ρ)) := by
  have hUm : Measurable fun p : ((ℕ → ℕ∞) × Ωc) × ((Fin 3 → (ℕ → ℕ∞) × Ωc) × R) =>
      (Function.update p.2.1 c p.1, p.2.2) :=
    ((measurable_update' (a := c)).comp ((measurable_fst.comp measurable_snd).prodMk
      measurable_fst)).prodMk (measurable_snd.comp measurable_snd)
  have hH : Measurable fun y : (Fin 3 → (ℕ → ℕ∞) × Ωc) × R => h ((y.1 c).1, y) :=
    hh.comp ((measurable_fst.comp ((measurable_pi_apply c).comp measurable_fst)).prodMk
      measurable_id)
  conv_lhs => rw [← prod_update_map μc ρ c]
  rw [integral_map hUm.aemeasurable hH.aestronglyMeasurable,
    ← integral_fst_prod μc _ h hh]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.update_self]
  exact hloc _ _ _ (fun c' hc' => by simp [Function.update_of_ne hc']) rfl

variable {Ωc Ωa : Type*} [MeasurableSpace Ωc] [MeasurableSpace Ωa]

/-- The child curves of an enriched closure sample. -/
def curvesOf (y : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa)) : Fin 3 → ℕ → ℕ∞ :=
  fun c => (y.1 c).1

theorem measurable_curvesOf :
    Measurable (curvesOf : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa) → _) :=
  measurable_pi_iff.mpr fun c => measurable_fst.comp ((measurable_pi_apply c).comp measurable_fst)

/-- The enriched sample with the curve of the child `c` replaced by `G`, as a closure sample. -/
def asmS (c : Fin 3) (p : (ℕ → ℕ∞) × ((Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa))) :
    ClosSample :=
  (Function.update (curvesOf p.2) c p.1, p.2.2.1)

theorem measurable_asmS (c : Fin 3) :
    Measurable (asmS (Ωc := Ωc) (Ωa := Ωa) c) :=
  ((measurable_update' (a := c)).comp ((measurable_curvesOf.comp measurable_snd).prodMk
    measurable_fst)).prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))

omit [MeasurableSpace Ωc] [MeasurableSpace Ωa] in
theorem asmS_self (c : Fin 3) (y : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa)) :
    asmS c ((y.1 c).1, y) = (curvesOf y, y.2.1) := by
  unfold asmS
  congr 1
  funext c'
  by_cases h : c' = c
  · subst h; simp [curvesOf]
  · simp [Function.update_of_ne h]

/-- Optional sampling in the enriched closure (proof of Lemma 10.8 of the paper), truncated at `n`: for `s ≤ e_c`
reading nothing of the child `c`, `E[G_c(s ∧ n) - (s ∧ n)/3] ≤ E[G_c(e_c ∧ n) - (e_c ∧ n)/3]`. -/
theorem os_S2_trunc (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (μ : Measure ((ℕ → ℕ∞) × (ℕ → Bool))) [IsProbabilityMeasure μ] (hμ : μ.map Prod.fst = Q)
    (hξ : ∀ i, μ {z | z.2 i = true} = 3⁻¹)
    (hind : ∀ i, IndepFun (fun z => z.2 i) (fun z => fun l : Fin (i + 1) => z.1 l) μ)
    (hinc : ∀ᵐ z ∂μ, ∀ i, z.1 i + (if z.2 i then 1 else 0) ≤ z.1 (i + 1))
    (B : ℕ) (hbd : ∀ᵐ z ∂μ, ∀ i, z.1 i ≤ ((i + B : ℕ) : ℕ∞))
    (μc : Measure ((ℕ → ℕ∞) × Ωc)) [IsProbabilityMeasure μc] (hμc : μc.map Prod.fst = Q)
    (ν : Measure Ωa) [IsProbabilityMeasure ν] (q : ℕ) (c : Fin 3)
    (s : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa) → ℕ) (hs : Measurable s)
    (hsR : ∀ y y', (∀ c', c' ≠ c → y.1 c' = y'.1 c') → y.2 = y'.2 → s y = s y')
    (hsle : ∀ y, (s y : ℕ∞) ≤ closE q (curvesOf y) y.2.1 c) (n : ℕ) :
    ∫ y, (((y.1 c).1 (min (s y) n)).toNat - ((min (s y) n : ℕ) : ℝ) / 3 : ℝ)
        ∂((Measure.pi fun _ : Fin 3 => μc).prod (dirMeasure.prod ν)) ≤
      ∫ x, osVal c (eN q c n) x ∂closMeasure Q := by
  subst hμc
  set P := (Measure.pi fun _ : Fin 3 => μc).prod (dirMeasure.prod ν) with hP
  set hσ : (ℕ → ℕ∞) × ((Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa)) → ℝ :=
    fun p => ((p.1 (min (s p.2) n)).toNat : ℝ) - ((min (s p.2) n : ℕ) : ℝ) / 3 with hσdef
  set hτ : (ℕ → ℕ∞) × ((Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa)) → ℝ :=
    fun p => osVal c (eN q c n) (asmS c p) with hτdef
  have hi : Measurable fun p : (ℕ → ℕ∞) × ((Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa)) =>
      min (s p.2) n :=
    (Measurable.of_discrete (f := fun k : ℕ => min k n)).comp (hs.comp measurable_snd)
  have hσm : Measurable hσ := by
    have h1 := measurable_comp_nat
      (fun p : (ℕ → ℕ∞) × ((Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa)) => p.1)
      (fun k => (measurable_pi_apply k).comp measurable_fst) _ hi
    exact ((Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp h1).sub
      (((Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp hi).div_const 3)
  have hτm : Measurable hτ :=
    (measurable_osVal c _ (measurable_eN q c n)).comp (measurable_asmS c)
  have hL : ∫ y, (((y.1 c).1 (min (s y) n)).toNat - ((min (s y) n : ℕ) : ℝ) / 3 : ℝ) ∂P =
      ∫ p, hσ (p.1.1, p.2) ∂(μ.prod P) := by
    rw [integral_fst_prod μ P hσ hσm, hμ]
    exact integral_replace_child μc (dirMeasure.prod ν) c hσ hσm
      (fun G y y' h1 h2 => by simp only [hσdef]; rw [hsR y y' h1 h2])
  have hforget : Measurable fun y : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa) =>
      ((fun c => (y.1 c).1), y.2.1) :=
    measurable_curvesOf.prodMk (measurable_fst.comp measurable_snd)
  have hR : ∫ x, osVal c (eN q c n) x ∂closMeasure (μc.map Prod.fst) = ∫ p, hτ (p.1.1, p.2) ∂(μ.prod P) := by
    rw [integral_fst_prod μ P hτ hτm, hμ, ← integral_replace_child μc (dirMeasure.prod ν) c hτ hτm ?_]
    · simp only [hτdef, asmS_self]
      rw [← forget_map μc ν, integral_map hforget.aemeasurable
        (measurable_osVal c _ (measurable_eN q c n)).aestronglyMeasurable]
      rfl
    · intro G y y' h1 h2
      simp only [hτdef]
      have : asmS c (G, y) = asmS c (G, y') := by
        unfold asmS
        congr 1
        · funext c'
          by_cases hc : c' = c
          · subst hc; simp
          · simp only [Function.update_of_ne hc, curvesOf, h1 c' hc]
        · rw [h2]
      rw [this]
  have hστ : ∀ g : (ℕ → ℕ∞) × ((Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa)),
      min (s g.2) n ≤ eN q c n (asmS c g) := by
    intro g
    set y' : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa) :=
      (Function.update g.2.1 c (g.1, (g.2.1 c).2), g.2.2)
    have hcur : curvesOf y' = Function.update (curvesOf g.2) c g.1 := by
      funext c'
      by_cases hc : c' = c
      · subst hc; simp [curvesOf, y']
      · simp [curvesOf, y', Function.update_of_ne hc]
    have hs' : s y' = s g.2 :=
      hsR _ _ (fun c' hc => by simp [y', Function.update_of_ne hc]) rfl
    have hle := hsle y'
    rw [hs', hcur] at hle
    rw [← ENat.natCast_le_natCast, eN_cast]
    exact le_min ((ENat.natCast_le_natCast.2 (min_le_left _ _)).trans hle)
      (ENat.natCast_le_natCast.2 (min_le_right _ _))
  have hos := os_core μ hξ hind hinc B hbd P
    (fun g => min (s g.2) n) (fun g => eN q c n (asmS c g))
    ((Measurable.of_discrete (f := fun k : ℕ => min k n)).comp (hs.comp measurable_snd))
    ((measurable_eN q c n).comp (measurable_asmS c)) hστ
    (fun i G G' r hGG' => by
      have key : (i : ℕ∞) < closE q (asmS c (G, r)).1 (asmS c (G, r)).2 c ↔
          (i : ℕ∞) < closE q (asmS c (G', r)).1 (asmS c (G', r)).2 c :=
        closE_stop q i c _ _ r.2.1 (fun c' hc' => by simp [asmS, Function.update_of_ne hc'])
          (fun k hk => by simp [asmS, hGG' k hk])
      simp only [lt_eN_iff, key]) n
  have e1 : ∀ p : ((ℕ → ℕ∞) × (ℕ → Bool)) × ((Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa)),
      stopVal (fun g => min (s g.2) n) n p = hσ (p.1.1, p.2) := by
    intro p
    simp only [stopVal, hσdef, min_eq_left (min_le_right (s p.2) n)]
  have e2 : ∀ p : ((ℕ → ℕ∞) × (ℕ → Bool)) × ((Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa)),
      stopVal (fun g => eN q c n (asmS c g)) n p = hτ (p.1.1, p.2) := by
    intro p
    simp only [stopVal, hτdef, osVal, min_eq_left (eN_le q c n _)]
    simp [asmS]
  simp only [e1, e2] at hos
  rw [hL, hR]
  exact hos

/-- The bounds behind dominated convergence: below `e_c`, `G_c(k)` and `k` are at most `N`. -/
theorem le_closN_of_le_closE (q B : ℕ) (c : Fin 3) (x : ClosSample)
    (hN : closN q x.1 x.2 < ⊤) (hc : closE q x.1 x.2 c ≤ closN q x.1 x.2 ∧
      gE q c x ≤ closN q x.1 x.2) (hg : GoodC B (x.1 c)) (k : ℕ)
    (hk : (k : ℕ∞) ≤ closE q x.1 x.2 c) :
    (x.1 c k).toNat ≤ (closN q x.1 x.2).toNat ∧ k ≤ (closN q x.1 x.2).toNat := by
  have hNne := hN.ne
  have hEne : closE q x.1 x.2 c ≠ ⊤ := ne_top_of_le_ne_top hNne hc.1
  have hk' : k ≤ (closE q x.1 x.2 c).toNat := by
    rw [← ENat.natCast_le_natCast, ENat.natCast_toNat hEne]; exact hk
  refine ⟨?_, hk'.trans (ENat.toNat_le_toNat hc.1 hNne)⟩
  exact ENat.toNat_le_toNat ((hg.1 hk').trans hc.2) hNne

theorem abs_sub_div_le (a b N : ℕ) (ha : a ≤ N) (hb : b ≤ N) :
    |(a : ℝ) - (b : ℝ) / 3| ≤ 2 * N := by
  have ha' : (a : ℝ) ≤ N := by exact_mod_cast ha
  have hb' : (b : ℝ) ≤ N := by exact_mod_cast hb
  have h0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

theorem measurable_forget :
    Measurable fun y : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa) =>
      ((fun c => (y.1 c).1), y.2.1) :=
  measurable_curvesOf.prodMk (measurable_fst.comp measurable_snd)

/-- The almost sure facts of the closure, on the enriched closure. -/
theorem ae_S2 (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (μc : Measure ((ℕ → ℕ∞) × Ωc))
    [IsProbabilityMeasure μc] (hμc : μc.map Prod.fst = Q) (ν : Measure Ωa)
    [IsProbabilityMeasure ν] (q B : ℕ) (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) :
    ∀ᵐ y ∂((Measure.pi fun _ : Fin 3 => μc).prod (dirMeasure.prod ν)),
      (closN q (curvesOf y) y.2.1 < ⊤ ∧
        closX q (curvesOf y) y.2.1 ≤ closN q (curvesOf y) y.2.1 ∧
        ∀ c, closE q (curvesOf y) y.2.1 c ≤ closN q (curvesOf y) y.2.1 ∧
          gE q c (curvesOf y, y.2.1) ≤ closN q (curvesOf y) y.2.1) ∧
      ∀ c, GoodC B (curvesOf y c) := by
  subst hμc
  have h := (ae_le_closN _ q B hgood).and hgood
  rw [← forget_map μc ν] at h
  exact ae_of_ae_map measurable_forget.aemeasurable h

theorem integrable_S2 (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (μc : Measure ((ℕ → ℕ∞) × Ωc)) [IsProbabilityMeasure μc] (hμc : μc.map Prod.fst = Q)
    (ν : Measure Ωa) [IsProbabilityMeasure ν] (q B : ℕ)
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c)) :
    Integrable (fun y => ((closN q (curvesOf y) y.2.1).toNat : ℝ))
      ((Measure.pi fun _ : Fin 3 => μc).prod (dirMeasure.prod ν)) := by
  subst hμc
  have h := integrable_closN _ q B hgood
  rw [← forget_map μc ν] at h
  exact h.comp_measurable measurable_forget

/-- Optional sampling in the enriched closure: `E[G_c(s) - s/3] ≤ E[G_c(e_c) - e_c/3]`. -/
theorem os_S2 (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (μ : Measure ((ℕ → ℕ∞) × (ℕ → Bool))) [IsProbabilityMeasure μ] (hμ : μ.map Prod.fst = Q)
    (hξ : ∀ i, μ {z | z.2 i = true} = 3⁻¹)
    (hind : ∀ i, IndepFun (fun z => z.2 i) (fun z => fun l : Fin (i + 1) => z.1 l) μ)
    (hinc : ∀ᵐ z ∂μ, ∀ i, z.1 i + (if z.2 i then 1 else 0) ≤ z.1 (i + 1))
    (B : ℕ) (hbd : ∀ᵐ z ∂μ, ∀ i, z.1 i ≤ ((i + B : ℕ) : ℕ∞))
    (hgood : ∀ᵐ x ∂closMeasure Q, ∀ c, GoodC B (x.1 c))
    (μc : Measure ((ℕ → ℕ∞) × Ωc)) [IsProbabilityMeasure μc] (hμc : μc.map Prod.fst = Q)
    (ν : Measure Ωa) [IsProbabilityMeasure ν] (q : ℕ) (c : Fin 3)
    (s : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa) → ℕ) (hs : Measurable s)
    (hsR : ∀ y y', (∀ c', c' ≠ c → y.1 c' = y'.1 c') → y.2 = y'.2 → s y = s y')
    (hsle : ∀ y, (s y : ℕ∞) ≤ closE q (curvesOf y) y.2.1 c) :
    ∫ y, (((y.1 c).1 (s y)).toNat - (s y : ℝ) / 3 : ℝ)
        ∂((Measure.pi fun _ : Fin 3 => μc).prod (dirMeasure.prod ν)) ≤
      ∫ x, (((gE q c x).toNat : ℝ) - ((closE q x.1 x.2 c).toNat : ℝ) / 3) ∂closMeasure Q := by
  have hGc : ∀ k, Measurable fun y : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa) =>
      (y.1 c).1 k := fun k =>
    (measurable_pi_apply k).comp (measurable_fst.comp ((measurable_pi_apply c).comp measurable_fst))
  have hlimL := tendsto_integral_of_dominated_convergence
    (μ := (Measure.pi fun _ : Fin 3 => μc).prod (dirMeasure.prod ν))
    (F := fun n y => (((y.1 c).1 (min (s y) n)).toNat - ((min (s y) n : ℕ) : ℝ) / 3 : ℝ))
    (f := fun y => (((y.1 c).1 (s y)).toNat - (s y : ℝ) / 3 : ℝ))
    (fun y => 2 * ((closN q (curvesOf y) y.2.1).toNat : ℝ))
    (fun n => by
      have hi : Measurable fun y : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa) =>
          min (s y) n := (Measurable.of_discrete (f := fun k : ℕ => min k n)).comp hs
      exact (((Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp
        (measurable_comp_nat (fun y k => (y.1 c).1 k) hGc _ hi)).sub
          (((Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp hi).div_const 3)).aestronglyMeasurable)
    ((integrable_S2 Q μc hμc ν q B hgood).const_mul 2)
    (fun n => by
      filter_upwards [ae_S2 Q μc hμc ν q B hgood] with y hy
      obtain ⟨⟨hN, -, hc⟩, hg⟩ := hy
      have hk : ((min (s y) n : ℕ) : ℕ∞) ≤ closE q (curvesOf y) y.2.1 c :=
        (ENat.natCast_le_natCast.2 (min_le_left _ _)).trans (hsle y)
      obtain ⟨h1, h2⟩ := le_closN_of_le_closE q B c (curvesOf y, y.2.1) hN (hc c) (hg c) _ hk
      rw [Real.norm_eq_abs]
      exact abs_sub_div_le _ _ _ h1 h2)
    (Filter.Eventually.of_forall fun y => tendsto_atTop_of_eventually_const (i₀ := s y)
      fun n hn => by simp only [min_eq_left hn])
  exact le_of_tendsto_of_tendsto' hlimL (tendsto_osVal_eN Q B hgood q c)
    (fun n => os_S2_trunc Q μ hμ hξ hind hinc B hbd μc hμc ν q c s hs hsR hsle n)

/-- `E G_m(k)` as a Bochner integral over the curve law. -/
theorem integral_curve_toNat (hmeas : measurable_plantedPair) (m k : ℕ) :
    ∫ G, ((G k).toNat : ℝ) ∂curveLaw m = meanG m k := by
  have hfin : ∀ᵐ G ∂curveLaw m, G k ≠ ⊤ := (ae_goodC hmeas m).mono fun G hG =>
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hG.2 k)
  rw [integral_toNat _ _ (measurable_pi_apply k) hfin, meanG, lintegral_plantedG_eq hmeas]

theorem meanG_le_mu (hfin : lintegral_plantedG_le) (m k : ℕ) : meanG m k ≤ mu m k :=
  ENNReal.toReal_le_of_le_ofReal (by unfold mu; positivity) (hfin m k)

universe u v in
/-- **Lemma 10.8 of the paper** from the statements of measurability, of the law of the closure
(Lemma 10.1), of the coins (Lemma 10.3) and of the all-awake count (Lemma 10.2). -/
theorem lemmaS2'_of (hmeas : measurable_plantedPair) (hsucc : curveLaw_succ)
    (hcoin : coin_coupling) (hfin : lintegral_plantedG_le) :
    lemmaS2'.{u, v} := by
  intro m j hj Ωc Ωa _ _ μc _ hμc ν _ e' he'meas he'R he'le
  set Q := curveLaw m with hQ
  set B := (3 ^ (m + 1) - 1) / 2
  set P := (Measure.pi fun _ : Fin 3 => μc).prod (dirMeasure.prod ν) with hP
  have hgoodQ : ∀ᵐ G ∂Q, GoodC B G := ae_goodC hmeas m
  have hgood := ae_closGood Q B hgoodQ
  obtain ⟨μ, hμ, hfst, hξ, hindep, hae⟩ := hcoin m
  have hind : ∀ i, IndepFun (fun z => z.2 i) (fun z => fun l : Fin (i + 1) => z.1 l) μ :=
    fun i => (hindep i).comp measurable_id measurable_fst
  have hinc : ∀ᵐ z ∂μ, ∀ i, z.1 i + (if z.2 i then 1 else 0) ≤ z.1 (i + 1) :=
    hae.mono fun z hz => hz.2
  have hbd : ∀ᵐ z ∂μ, ∀ i, z.1 i ≤ ((i + B : ℕ) : ℕ∞) := by
    have h : ∀ᵐ G ∂μ.map Prod.fst, GoodC B G := by rw [hfst]; exact hgoodQ
    exact (ae_of_ae_map measurable_fst.aemeasurable h).mono fun z hz => hz.2
  have haeP := ae_S2 Q μc hμc ν (j + 1) B hgood
  have hNint := integrable_S2 Q μc hμc ν (j + 1) B hgood
  -- the closure side, as in Lemma 10.5 of the paper
  have hid := closure_identity Q (j + 1) B hgood
  have hae' := ae_le_closN Q (j + 1) B hgood
  have hX : meanG (m + 1) j = ∫ x, ((closX (j + 1) x.1 x.2).toNat : ℝ) ∂closMeasure Q := by
    rw [meanG_succ_eq hmeas hsucc m j hj,
      ← integral_toNat _ _ (measurable_closX (j + 1)) (hae'.mono fun x hx =>
        ne_top_of_le_ne_top hx.1.ne hx.2.1)]
  have hlin : ∀ c, ∫ x, (((gE (j + 1) c x).toNat : ℝ) - ((closE (j + 1) x.1 x.2 c).toNat : ℝ) / 3)
      ∂closMeasure Q = ∫ x, ((gE (j + 1) c x).toNat : ℝ) ∂closMeasure Q -
        1 / 3 * ∫ x, ((closE (j + 1) x.1 x.2 c).toNat : ℝ) ∂closMeasure Q := by
    intro c
    rw [integral_sub (integrable_le_closN Q (j + 1) B hgood _ (measurable_gE (j + 1) c)
        (hae'.mono fun x hx => (hx.2.2 c).2))
      ((integrable_le_closN Q (j + 1) B hgood _ (measurable_closE (j + 1) c)
        (hae'.mono fun x hx => (hx.2.2 c).1)).div_const 3), integral_div]
    ring
  -- the enriched side
  have hGc : ∀ c k, Measurable fun y : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa) =>
      (y.1 c).1 k := fun c k =>
    (measurable_pi_apply k).comp (measurable_fst.comp ((measurable_pi_apply c).comp measurable_fst))
  have hGe : ∀ c, Measurable fun y : (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa) =>
      (((y.1 c).1 (e' c y)).toNat : ℝ) := fun c =>
    (Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp
      (measurable_comp_nat (fun y k => (y.1 c).1 k) (hGc c) _ (he'meas c))
  have hbnd : ∀ c, ∀ᵐ y ∂P, (((y.1 c).1 (e' c y)).toNat ≤ (closN (j + 1) (curvesOf y) y.2.1).toNat ∧
      e' c y ≤ (closN (j + 1) (curvesOf y) y.2.1).toNat) := fun c => by
    filter_upwards [haeP] with y hy
    obtain ⟨⟨hN, -, hc⟩, hg⟩ := hy
    exact le_closN_of_le_closE (j + 1) B c (curvesOf y, y.2.1) hN (hc c) (hg c) _ (he'le c y)
  have hint_e : ∀ c, Integrable (fun y => (e' c y : ℝ)) P := fun c =>
    hNint.mono' ((Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp
      (he'meas c)).aestronglyMeasurable ((hbnd c).mono fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast hy.2)
  have hint_G : ∀ c, Integrable (fun y => (((y.1 c).1 (e' c y)).toNat : ℝ)) P := fun c =>
    hNint.mono' (hGe c).aestronglyMeasurable ((hbnd c).mono fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast hy.1)
  have hint_mean : ∀ c, Integrable (fun y => meanG m (e' c y)) P := fun c =>
    (((integrable_const (((m : ℝ) + 1) / 3)).add ((hint_e c).div_const 3))).mono'
      ((Measurable.of_discrete (f := fun k : ℕ => meanG m k)).comp
        (he'meas c)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
          have h0 : 0 ≤ meanG m (e' c y) := ENNReal.toReal_nonneg
          rw [Real.norm_eq_abs, abs_of_nonneg h0]
          have := meanG_le_mu hfin m (e' c y)
          unfold mu at this
          simp only [Pi.add_apply]
          linarith)
  -- independence of the child `c` from `e' c`
  have hmean : ∀ c, ∫ y, (((y.1 c).1 (e' c y)).toNat : ℝ) ∂P = ∫ y, meanG m (e' c y) ∂P := by
    intro c
    set h : (ℕ → ℕ∞) × ((Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa)) → ℝ :=
      fun p => ((p.1 (e' c p.2)).toNat : ℝ) with hh
    have hhm : Measurable h :=
      (Measurable.of_discrete (f := fun y : ℕ∞ => (y.toNat : ℝ))).comp
        (measurable_comp_nat (fun p : (ℕ → ℕ∞) × _ => p.1)
          (fun k => (measurable_pi_apply k).comp measurable_fst) _ ((he'meas c).comp measurable_snd))
    have h1 := integral_replace_child μc (dirMeasure.prod ν) c h hhm
      (fun G y y' h1 h2 => by simp only [hh]; rw [he'R c y y' h1 h2])
    simp only [hh] at h1
    rw [h1, hμc]
    have hint : Integrable h (Q.prod P) := by
      refine (hNint.comp_snd Q |>.add (integrable_const (B : ℝ))).mono' hhm.aestronglyMeasurable ?_
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgoodQ,
        Measure.quasiMeasurePreserving_snd.ae (hbnd c)] with p hG hy
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      have := toNat_le_of_le_natCast (hG.2 (e' c p.2))
      have h2 : ((e' c p.2 : ℕ) : ℝ) ≤ (closN (j + 1) (curvesOf p.2) p.2.2.1).toNat := by
        exact_mod_cast hy.2
      simp only [hh, Pi.add_apply]
      have h3 : ((p.1 (e' c p.2)).toNat : ℝ) ≤ (e' c p.2 : ℝ) + B := by exact_mod_cast this
      linarith
    rw [integral_prod_symm h hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hh]
    exact integral_curve_toNat hmeas m (e' c y)
  have hos : ∀ c, ∫ y, (((y.1 c).1 (e' c y)).toNat : ℝ) ∂P - 1 / 3 * ∫ y, (e' c y : ℝ) ∂P ≤
      ∫ x, (((gE (j + 1) c x).toNat : ℝ) - ((closE (j + 1) x.1 x.2 c).toNat : ℝ) / 3)
        ∂closMeasure Q := by
    intro c
    have h := os_S2 Q μ hfst hξ hind hinc B hbd hgood μc hμc ν (j + 1) c (e' c) (he'meas c)
      (he'R c) (he'le c)
    rw [integral_sub (hint_G c) ((hint_e c).div_const 3), integral_div] at h
    linarith
  have hdef : ∀ c, ∫ y, deficit m (e' c y) ∂P =
      ((m : ℝ) + 1) / 3 + 1 / 3 * ∫ y, (e' c y : ℝ) ∂P - ∫ y, meanG m (e' c y) ∂P := by
    intro c
    have e1 : (fun y => deficit m (e' c y)) =
        fun y => (((m : ℝ) + 1) / 3 + (e' c y : ℝ) / 3) - meanG m (e' c y) := by
      funext y; unfold deficit mu; ring
    have hA : Integrable (fun y => ((m : ℝ) + 1) / 3 + (e' c y : ℝ) / 3) P :=
      (integrable_const _).add ((hint_e c).div_const 3)
    rw [e1, integral_sub hA (hint_mean c),
      integral_add (integrable_const _) ((hint_e c).div_const 3), integral_div, integral_div, integral_const]
    simp only [probReal_univ, one_smul]
    ring
  have h0 := hos 0
  have h1 := hos 1
  have h2 := hos 2
  rw [hlin, hmean] at h0 h1 h2
  rw [Fin.sum_univ_three, hdef 0, hdef 1, hdef 2]
  unfold deficit mu
  rw [hX]
  simp only [Fin.sum_univ_three] at hid
  push_cast at hid ⊢
  linarith


end FrogModel.D3.Iface
