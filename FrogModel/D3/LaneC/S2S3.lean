module

public import FrogModel.D3.LaneC.Couple
public import FrogModel.D3.LaneC.StageCmp
public import FrogModel.D3.LaneB.Coins
public import FrogModel.D3.LaneB.Succ
public import FrogModel.D3.LaneB.ClosLaw

@[expose] public section

/-!
# Lemma 12.1 of the paper (the lower closures)

In the convention of FrogModel/D3/LaneB, `lemmaS2_of` (Lemma 12.1 (1)) and `lemmaS3_of`
(Lemma 12.1 (2)) take the interface statements they use as hypotheses.

The route is an inequality of laws. Each child carries its planted curve `G` and its coins `ξ`
(`coin_coupling`); its lower curve answers the first entry by `min(G(1), GM + 1)` and each later
entry by a coin, and lies below `G` almost surely. The lower closure (`toL`) then has the explicit
law `lowMeasure`, whose capped counts have exactly the laws `lawS2` and `lawS3` at the true cdf
`P(G_m(1) ≤ .)` (`lawV_lawS2`, `lawV_lawS3`). Raising the cdf to the row `F1` moves these laws in the
direction of the claimed bounds (`lawS2_cmp`, `cdfS3_cmp`).

S2: Lemma 10.8 with `e'_c` the capped count of the entries into the child `c` in the lower closure
where `c` is dead (on the almost sure event where the other lower curves lie below their planted
curves, `0` off it), then `Delta_m(k) ≤ min_(k' ≤ k) D(k')` (Lemma 10.7 (1)).
S3: `X ≥ X''` almost surely, so `P(X ≤ v) ≤ P(X'' ≤ v)`.
-/

open MeasureTheory ProbabilityTheory FrogModel.D3.Iface FrogModel.D3.LaneC.Lower
open scoped ENNReal

namespace FrogModel.D3.LaneC

/-- The closure sample with coins and no auxiliary randomness. -/
abbrev CSample := (Fin 3 → (ℕ → ℕ∞) × (ℕ → Bool)) × ((ℕ → Fin 4) × Unit)

theorem measurableSet_enat_le {α : Type*} [MeasurableSpace α] {f g : α → ℕ∞} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet {a | f a ≤ g a} := by
  have h : MeasurableSet {p : ℕ∞ × ℕ∞ | p.1 ≤ p.2} := by
    have : {p : ℕ∞ × ℕ∞ | p.1 ≤ p.2} = ⋃ x : ℕ∞, {x} ×ˢ {y | x ≤ y} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨p.1, rfl, h⟩, fun ⟨x, hx, h⟩ => hx ▸ h⟩
    rw [this]
    exact MeasurableSet.iUnion fun x =>
      (measurableSet_singleton x).prod (MeasurableSet.of_discrete)
  exact (hf.prodMk hg) h

theorem minE_le_self (x : ℕ∞) (E : ℕ) : (minE x E : ℕ∞) ≤ x := by
  unfold minE
  have hne : min x (E : ℕ∞) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top E) (min_le_right _ _)
  rw [ENat.natCast_toNat hne]
  exact min_le_left _ _

theorem minE_le_cap (x : ℕ∞) (E : ℕ) : minE x E ≤ E := by
  unfold minE
  have h : min x (E : ℕ∞) ≤ (E : ℕ∞) := min_le_right _ _
  have hne : min x (E : ℕ∞) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top E) h
  rw [← ENat.natCast_toNat hne, Nat.cast_le] at h
  exact h

theorem le_iff_minE_le (x : ℕ∞) (GM v : ℕ) (hv : v ≤ GM) :
    x ≤ (v : ℕ∞) ↔ minE x (GM + 1) ≤ v := by
  induction x using ENat.recTopCoe with
  | top =>
    simp only [top_le_iff, ENat.natCast_ne_top, false_iff, not_le, minE]
    rw [min_eq_right le_top, ENat.toNat_natCast]
    omega
  | coe n =>
    have hmin : min (n : ℕ∞) ((GM + 1 : ℕ) : ℕ∞) = ((min n (GM + 1) : ℕ) : ℕ∞) := by
      rcases le_total n (GM + 1) with h | h
      · rw [min_eq_left (by exact_mod_cast h), min_eq_left h]
      · rw [min_eq_right (by exact_mod_cast h), min_eq_right h]
    simp only [minE, Nat.cast_le]
    rw [hmin, ENat.toNat_natCast]
    omega

/-- The cdf of `G_m(1)` as a function of the threshold, through the law of the planted curve. -/
noncomputable def F0 (m : ℕ) : ℕ → ℝ := fun g => (curveLaw m {G | G 1 ≤ (g : ℕ∞)}).toReal

theorem F0_mono (m GM : ℕ) : ∀ g < GM, F0 m g ≤ F0 m (g + 1) := by
  intro g _
  unfold F0
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun G hG => ?_)
  simp only [Set.mem_ofPred_eq] at hG ⊢
  exact hG.trans (by exact_mod_cast Nat.le_succ g)

theorem F0_01 (m GM : ℕ) : ∀ g ≤ GM, 0 ≤ F0 m g ∧ F0 m g ≤ 1 := by
  intro g _
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  unfold F0
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

theorem rho_zero (m GM : ℕ) : ∀ r, GM + 1 < r → rhoOf (curveLaw m) GM {r} = 0 :=
  fun r hr => rhoOf_zero (curveLaw m) GM r hr

theorem rho_plR (m GM : ℕ) : ∀ r, (rhoOf (curveLaw m) GM {r}).toReal = plR (F0 m) GM r :=
  fun r => rhoOf_plR (curveLaw m) GM r

/-! ## Lemma 12.1 (1) of the paper -/

/-- The children other than `c` have their lower curves below their planted curves. -/
def goodC (GM : ℕ) (c : Fin 3) (y : CSample) : Prop :=
  ∀ s k, s = c ∨ lcurve .fresh (Rof GM (y.1 s).1) (ζof (y.1 s).2) k ≤ (y.1 s).1 k

open Classical in
/-- `e'_c`: the entries into the child `c`, capped at `E`, in the lower closure where `c` is dead
(`0` off the almost sure event `goodC`). -/
noncomputable def eS2 (GM E j : ℕ) (c : Fin 3) (y : CSample) : ℕ :=
  if goodC GM c y then minE (cnt c.succ (j + 1) (tyS2 c) (toL GM y)) E else 0

theorem measurable_lcurve_fresh (GM : ℕ) (s : Fin 3) (k : ℕ) :
    Measurable fun y : CSample => lcurve .fresh (Rof GM (y.1 s).1) (ζof (y.1 s).2) k := by
  have h := (measurable_pi_apply k).comp ((measurable_pi_apply s).comp
    ((measurable_curves (fun _ => Ty.fresh)).comp (measurable_toL (Ωa := Unit) GM)))
  exact h

theorem measurableSet_goodC (GM : ℕ) (c : Fin 3) : MeasurableSet {y : CSample | goodC GM c y} := by
  have : {y : CSample | goodC GM c y} = ⋂ s, ⋂ k, ({_y : CSample | s = c} ∪
      {y : CSample | lcurve .fresh (Rof GM (y.1 s).1) (ζof (y.1 s).2) k ≤ (y.1 s).1 k}) := by
    ext y
    simp only [goodC, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union]
  rw [this]
  refine MeasurableSet.iInter fun s => MeasurableSet.iInter fun k =>
    (MeasurableSet.const _).union (measurableSet_enat_le (measurable_lcurve_fresh GM s k) ?_)
  exact (measurable_pi_apply k).comp (measurable_fst.comp ((measurable_pi_apply s).comp measurable_fst))

theorem measurable_eS2 (GM E j : ℕ) (c : Fin 3) : Measurable (eS2 GM E j c) := by
  have hX : Measurable fun y : CSample => minE (cnt c.succ (j + 1) (tyS2 c) (toL GM y)) E := by
    have h := (measurable_of_countable fun x : ℕ∞ => minE x E).comp
      ((measurable_cnt c.succ (j + 1) (tyS2 c)).comp (measurable_toL (Ωa := Unit) GM))
    exact h
  unfold eS2
  exact Measurable.ite (measurableSet_goodC GM c) hX measurable_const

theorem curves_tyS2_toL (GM : ℕ) (c : Fin 3) (y y' : CSample)
    (h : ∀ c', c' ≠ c → y.1 c' = y'.1 c') :
    curves (tyS2 c) (toL GM y) = curves (tyS2 c) (toL GM y') := by
  funext s k
  by_cases hs : s = c
  · subst hs
    simp [curves, tyS2, lcurve]
  · simp only [curves, toL, tyS2, ite_eq_right hs, h s hs]

theorem eS2_R (GM E j : ℕ) (c : Fin 3) (y y' : CSample) (h : ∀ c', c' ≠ c → y.1 c' = y'.1 c')
    (h2 : y.2 = y'.2) : eS2 GM E j c y = eS2 GM E j c y' := by
  have hg : goodC GM c y ↔ goodC GM c y' := by
    unfold goodC
    refine forall_congr' fun s => forall_congr' fun k => ?_
    by_cases hs : s = c
    · simp [hs]
    · rw [h s hs]
  have hc : cnt c.succ (j + 1) (tyS2 c) (toL GM y) = cnt c.succ (j + 1) (tyS2 c) (toL GM y') := by
    unfold cnt
    rw [curves_tyS2_toL GM c y y' h]
    simp only [toL, h2]
  unfold eS2
  rw [hc]
  by_cases hy : goodC GM c y
  · rw [ite_eq_left hy, ite_eq_left (hg.1 hy)]
  · rw [ite_eq_right hy, ite_eq_right fun h' => hy (hg.2 h')]

theorem eS2_le (GM E j : ℕ) (c : Fin 3) (y : CSample) :
    (eS2 GM E j c y : ℕ∞) ≤ closE (j + 1) (fun c' => (y.1 c').1) y.2.1 c := by
  unfold eS2
  split_ifs with hg
  · refine (minE_le_self _ E).trans ?_
    unfold cnt closE
    refine countAt_closN_mono (j + 1) _ _ _ _ fun s k => ?_
    by_cases hs : s = c
    · subst hs
      simp [curves, tyS2, lcurve]
    · simp only [curves, toL, tyS2, ite_eq_right hs]
      exact (hg s k).resolve_left hs
  · simp

theorem deficit_nonneg_of (hG : lintegral_plantedG_le) (m k : ℕ) : 0 ≤ deficit m k := by
  unfold deficit meanG
  have hmu : 0 ≤ mu m k := by unfold mu; positivity
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hG m k)
  rw [ENNReal.toReal_ofReal hmu] at h
  linarith

/-- **Lemma 12.1 (1) of the paper** from the interface statements it uses. -/
theorem lemmaS2_of (hmeas : measurable_plantedPair) (hcoin : coin_coupling)
    (hG : lintegral_plantedG_le) (h17a : lemma17a)
    (hS2' : lemmaS2'.{0, 0}) : lemmaS2 := by
  intro m j E GM hj hE F1 hF1 hmono h01 D hD
  obtain ⟨μ, hμP, hμ1, hξ, hind, hae⟩ := hcoin m
  set ρ := rhoOf (curveLaw m) GM with hρ
  set Λ : Measure CSample := (Measure.pi fun _ : Fin 3 => μ).prod
    (dirMeasure.prod (Measure.dirac ())) with hΛ
  have hstep := hS2' m j hj μ hμ1 (Measure.dirac ()) (eS2 GM E j) (measurable_eS2 GM E j)
    (fun c y y' h h2 => eS2_R GM E j c y y' h h2) (eS2_le GM E j)
  -- the law of the lower closure at the true cdf
  have hlaw : ∀ k, lawV ρ (0 : Fin 3).succ E (j + 1) (tyS2 0) k = lawS2 GM E (F0 m) (j + 1) k :=
    fun k => lawV_lawS2 ρ 0 E GM hE (F0 m) (rho_zero m GM) (rho_plR m GM) (j + 1) k
  -- each child gives the same mean
  have hint : ∀ c, ∫ y, deficit m (eS2 GM E j c y) ∂Λ =
      ∑ k ∈ Finset.range (E + 1), lawS2 GM E (F0 m) (j + 1) k * deficit m k := by
    intro c
    have hgood := ae_lcurve_le μ hae GM (Measure.dirac ())
    have hae' : (fun y => deficit m (eS2 GM E j c y)) =ᵐ[Λ]
        fun y => deficit m (minE (cnt c.succ (j + 1) (tyS2 c) (toL GM y)) E) := by
      refine hgood.mono fun y hy => ?_
      have hg : goodC GM c y := fun s k => Or.inr (hy s k)
      simp only [eS2, ite_eq_left hg]
    have hX : Measurable fun ω : LSample => minE (cnt c.succ (j + 1) (tyS2 c) ω) E := by
      have h := (measurable_of_countable fun x : ℕ∞ => minE x E).comp
        (measurable_cnt c.succ (j + 1) (tyS2 c))
      exact h
    have hf : Measurable fun ω : LSample => deficit m (minE (cnt c.succ (j + 1) (tyS2 c) ω) E) := by
      have h := (measurable_of_countable fun n : ℕ => deficit m n).comp hX
      exact h
    rw [integral_congr_ae hae', ← integral_map (measurable_toL GM).aemeasurable
      hf.aestronglyMeasurable, hΛ, map_toL μ (curveLaw m) hμ1 GM hξ hind (Measure.dirac ()),
      integral_nat_le _ _ hX E (fun ω => minE_le_cap _ E) (deficit m)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := lawV_lawS2 ρ c E GM hE (F0 m) (rho_zero m GM) (rho_plR m GM) (j + 1) k
    unfold lawV at h1
    rw [h1]
  rw [Finset.sum_congr rfl fun c _ => hint c, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hstep
  have hstep' : deficit (m + 1) j ≤
      ∑ k ∈ Finset.range (E + 1), lawS2 GM E (F0 m) (j + 1) k * deficit m k := by
    have h3 : (1 / 3 : ℝ) * ((3 : ℕ) * ∑ k ∈ Finset.range (E + 1),
        lawS2 GM E (F0 m) (j + 1) k * deficit m k) =
        ∑ k ∈ Finset.range (E + 1), lawS2 GM E (F0 m) (j + 1) k * deficit m k := by
      push_cast; ring
    linarith
  -- the deficit below the running minimum of `D`
  set φ : ℕ → ℝ := fun k => (Finset.range (min k E + 1)).inf' Finset.nonempty_range_add_one D
    with hφ
  have hanti : Antitone (deficit m) := antitone_nat_of_succ_le (h17a m)
  have hdef0 : ∀ k, 0 ≤ deficit m k := deficit_nonneg_of hG m
  have hφa : Antitone φ := by
    intro a b hab
    exact Finset.inf'_mono D (Finset.range_subset_range.2 (by omega)) _
  have hφ0 : ∀ k, 0 ≤ φ k := by
    intro k
    refine Finset.le_inf' _ _ fun k' hk' => ?_
    rw [Finset.mem_range] at hk'
    exact (hdef0 k').trans (hD k' (by omega))
  have hdefφ : ∀ k ≤ E, deficit m k ≤ φ k := by
    intro k hk
    refine Finset.le_inf' _ _ fun k' hk' => ?_
    rw [Finset.mem_range] at hk'
    exact (hanti (show k' ≤ k by omega)).trans (hD k' (by omega))
  have hlaw0 : ∀ k, 0 ≤ lawS2 GM E (F0 m) (j + 1) k := fun k => by
    rw [← hlaw k]; exact ENNReal.toReal_nonneg
  have hcmp := lawS2_cmp GM E (j + 1) hE F1 (F0 m)
    (fun g hg => by unfold F0; rw [← cdfG_eq hmeas m 1 g]; exact hF1 g hg) hmono h01 (F0_mono m GM)
    (F0_01 m GM) φ hφa hφ0
  unfold Vs at hcmp
  calc deficit (m + 1) j
      ≤ ∑ k ∈ Finset.range (E + 1), lawS2 GM E (F0 m) (j + 1) k * deficit m k := hstep'
    _ ≤ ∑ k ∈ Finset.range (E + 1), lawS2 GM E (F0 m) (j + 1) k * φ k := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_range] at hk
        exact mul_le_mul_of_nonneg_left (hdefφ k (by omega)) (hlaw0 k)
    _ ≤ ∑ k ∈ Finset.range (E + 1), lawS2 GM E F1 (j + 1) k * φ k := hcmp
    _ = _ := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        simp only [hφ, show min k E = k by omega]

/-! ## Lemma 12.1 (2) of the paper -/

/-- **Lemma 12.1 (2) of the paper** from the interface statements it uses. -/
theorem lemmaS3_of (hmeas : measurable_plantedPair) (hsucc : curveLaw_succ)
    (hcoin : coin_coupling) : lemmaS3 := by
  intro m j GM v hj hv F1 hF1 hmono h01
  obtain ⟨μ, hμP, hμ1, hξ, hind, hae⟩ := hcoin m
  set ρ := rhoOf (curveLaw m) GM with hρ
  set Λ : Measure CSample := (Measure.pi fun _ : Fin 3 => μ).prod
    (dirMeasure.prod (Measure.dirac ())) with hΛ
  have hforget : Measurable fun y : CSample => (((fun c => (y.1 c).1), y.2.1) : ClosSample) :=
    (Measurable.of_eval fun c => measurable_fst.comp ((measurable_pi_apply c).comp measurable_fst)).prodMk
      (measurable_fst.comp measurable_snd)
  have hXm : MeasurableSet {x : ClosSample | closX (j + 1) x.1 x.2 ≤ (v : ℕ∞)} :=
    (measurable_countAt_closN (j + 1) 0) (MeasurableSet.of_discrete (s := {x : ℕ∞ | x ≤ (v : ℕ∞)}))
  set T : Set LSample := {ω | cnt 0 (j + 1) (fun _ => Ty.fresh) ω ≤ (v : ℕ∞)} with hT
  have hTm : MeasurableSet T :=
    (measurable_cnt 0 (j + 1) (fun _ => Ty.fresh)) (MeasurableSet.of_discrete (s := {x : ℕ∞ | x ≤ (v : ℕ∞)}))
  rw [cdfG_succ_eq hmeas hsucc m j v hj]
  unfold closProb
  have hcl : closMeasure (curveLaw m) = Λ.map fun y : CSample => (((fun c => (y.1 c).1), y.2.1) : ClosSample) := by
    rw [hΛ, forget_map μ (Measure.dirac ())]
    simp only [hμ1]
  rw [hcl, Measure.map_apply hforget hXm]
  -- `X ≥ X''` almost surely
  have hle : Λ ((fun y : CSample => (((fun c => (y.1 c).1), y.2.1) : ClosSample)) ⁻¹'
      {x : ClosSample | closX (j + 1) x.1 x.2 ≤ (v : ℕ∞)}) ≤ Λ (toL GM ⁻¹' T) := by
    refine measure_mono_ae ((ae_lcurve_le μ hae GM (Measure.dirac ())).mono fun y hy hyX => ?_)
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hT, closX] at hyX ⊢
    refine le_trans ?_ hyX
    unfold cnt
    exact countAt_closN_mono (j + 1) _ _ _ _ fun s k => hy s k
  have hTlaw : Λ (toL GM ⁻¹' T) = lowMeasure ρ T := by
    rw [← Measure.map_apply (measurable_toL GM) hTm, hΛ,
      map_toL μ (curveLaw m) hμ1 GM hξ hind (Measure.dirac ())]
  have hTsum : lowMeasure ρ T = ∑ x ∈ Finset.range (v + 1),
      lowMeasure ρ {ω | minE (cnt 0 (j + 1) (fun _ => Ty.fresh) ω) (GM + 1) = x} := by
    have hU : T = ⋃ x ∈ Finset.range (v + 1),
        {ω | minE (cnt 0 (j + 1) (fun _ => Ty.fresh) ω) (GM + 1) = x} := by
      ext ω
      simp only [hT, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop,
        le_iff_minE_le _ GM v hv]
      constructor
      · intro h; exact ⟨_, by omega, rfl⟩
      · rintro ⟨x, hx, rfl⟩; omega
    rw [hU, measure_biUnion_finset]
    · intro a _ b _ hab
      exact Set.disjoint_left.2 fun ω ha hb => hab (ha.symm.trans hb)
    · intro x _
      exact measurableSet_cnt 0 (j + 1) (GM + 1) x _
  have hcdf : ((lowMeasure ρ) T).toReal = cdfS3 GM (F0 m) (j + 1) v := by
    rw [hTsum, ENNReal.toReal_sum (fun x _ => measure_ne_top _ _)]
    unfold cdfS3
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 := lawV_lawS3 ρ GM (F0 m) (rho_zero m GM) (rho_plR m GM) (j + 1) x
    unfold lawV at h1
    exact h1
  have hcmp := cdfS3_cmp GM (j + 1) v hv F1 (F0 m)
    (fun g hg => by unfold F0; rw [← cdfG_eq hmeas m 1 g]; exact hF1 g hg) hmono h01 (F0_mono m GM)
    (F0_01 m GM)
  calc (Λ _).toReal ≤ (Λ (toL GM ⁻¹' T)).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) hle
    _ = cdfS3 GM (F0 m) (j + 1) v := by rw [hTlaw, hcdf]
    _ ≤ cdfS3 GM F1 (j + 1) v := hcmp

end FrogModel.D3.LaneC
