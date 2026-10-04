module

public import FrogModel.D3.LaneC.LowerStep
public import FrogModel.D3.LaneB.Measurability
public import FrogModel.D3.LaneB.Sampling
public import FrogModel.Lemmas.Refresh

@[expose] public section

/-!
# The law of a lower closure after its first step (measure theory)

The first direction, the first coin of a child and the first answer of a child are independent of
what the lower closure reads afterwards, with their own laws: `map_dir_shift`, `map_coin_shift`,
`map_R_update`, and the decomposition of a probability along such a first read (`measure_decomp`,
`measure_R_decomp`). Also the capped count shifted by one (`measure_capShift`), integrals of
functions of a bounded count, the independence of the coins of `coin_coupling` from `G(1)`
(`coins_indep_map`) and the pseudo-law of `min(G(1), GM + 1)` (`plR_law`).
-/

open MeasureTheory ProbabilityTheory FrogModel.D3.Iface
open scoped ENNReal

namespace FrogModel.D3.LaneC.Lower

/-- The lower curves are measurable functions of the sample. -/
theorem measurable_curves (τ : Fin 3 → Ty) : Measurable (curves τ) := by
  refine measurable_pi_iff.mpr fun s => measurable_pi_iff.mpr fun k => ?_
  have hg : Measurable fun ω : LSample => (ω.2.1 s, fun i : Fin k => ω.2.2 s i) :=
    ((measurable_pi_apply s).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_pi_iff.mpr fun i =>
        (measurable_pi_apply (i : ℕ)).comp ((measurable_pi_apply s).comp
          (measurable_snd.comp measurable_snd)))
  have hΨ : Measurable fun p : ℕ × (Fin k → Bool) =>
      lcurve (τ s) p.1 (fun i => if h : i < k then p.2 ⟨i, h⟩ else false) k :=
    measurable_of_countable _
  have heq : (fun ω : LSample => curves τ ω s k) = (fun p : ℕ × (Fin k → Bool) =>
      lcurve (τ s) p.1 (fun i => if h : i < k then p.2 ⟨i, h⟩ else false) k) ∘
        (fun ω : LSample => (ω.2.1 s, fun i : Fin k => ω.2.2 s i)) := by
    funext ω
    exact lcurve_congr _ _ _ _ k fun i hi => by simp [hi]
  rw [heq]
  exact hΨ.comp hg

theorem measurable_cnt (b : Fin 4) (q : ℕ) (τ : Fin 3 → Ty) : Measurable (cnt b q τ) := by
  have h1 : Measurable fun ω : LSample => ((curves τ ω, ω.1) : ClosSample) :=
    (measurable_curves τ).prodMk measurable_fst
  have h2 : Measurable fun x : ClosSample => countAt x.2 b (closN q x.1 x.2) :=
    measurable_countAt_closN q b
  have h3 := h2.comp h1
  unfold cnt
  exact h3

theorem measurableSet_cnt (b : Fin 4) (q cap k : ℕ) (τ : Fin 3 → Ty) :
    MeasurableSet {ω : LSample | minE (cnt b q τ ω) cap = k} :=
  (measurable_of_countable (fun x : ℕ∞ => minE x cap)).comp (measurable_cnt b q τ)
    (measurableSet_singleton k)

theorem measure_capShift {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℕ∞)
    (hX : Measurable X) (cap : ℕ) (hcap : 1 ≤ cap) (k : ℕ) :
    (μ {ω | minE (1 + X ω) cap = k}).toReal =
      capShift cap (fun k' => (μ {ω | minE (X ω) cap = k'}).toReal) k := by
  have hcap_pos : 0 < cap := by omega
  -- Key lemma: minE (1 + x) cap is never 0 when cap ≥ 1
  have h_minE_one_add_ne_zero (x : ℕ∞) : minE (1 + x) cap ≠ 0 := by
    dsimp [minE]
    intro h
    rcases (ENat.toNat_eq_zero (n := min (1 + x) (cap : ℕ∞))).mp h with (hzero | htop)
    · -- min (1+x) cap = 0, but min ≥ 1
      have h1 : (1 : ℕ∞) ≤ 1 + x := by
        simp
      have hcap' : (1 : ℕ∞) ≤ (cap : ℕ∞) := by exact_mod_cast hcap
      have hmin_ge_one : (1 : ℕ∞) ≤ min (1 + x) (cap : ℕ∞) := le_min h1 hcap'
      rw [hzero] at hmin_ge_one
      exact (by norm_num : (0 : ℕ∞) < 1).not_ge hmin_ge_one
    · -- min (1+x) cap = ⊤, but min ≤ cap < ⊤
      have hle : min (1 + x) (cap : ℕ∞) ≤ (cap : ℕ∞) := min_le_right _ _
      rw [htop] at hle
      have hcap_lt_top : (cap : ℕ∞) < ⊤ := ENat.natCast_lt_top cap
      exact hcap_lt_top.not_ge hle
  -- Key lemma: for 0 < k < cap, minE (1 + x) cap = k ↔ minE x cap = k - 1
  have h_eq_lt_cap (x : ℕ∞) (k : ℕ) (hk_pos : 0 < k) (hk_lt_cap : k < cap) :
      (minE (1 + x) cap = k) ↔ (minE x cap = k - 1) := by
    by_cases hx_top : x = ⊤
    · -- x = ⊤
      subst hx_top
      constructor
      · intro h
        dsimp [minE] at h
        have hmin : min (1 + (⊤ : ℕ∞)) (cap : ℕ∞) = (cap : ℕ∞) := by simp
        rw [hmin] at h
        have hcap_toNat : (cap : ℕ∞).toNat = cap := by simp
        rw [hcap_toNat] at h
        omega
      · intro h
        dsimp [minE] at h
        have hmin : min (⊤ : ℕ∞) (cap : ℕ∞) = (cap : ℕ∞) := by simp
        rw [hmin] at h
        have hcap_toNat : (cap : ℕ∞).toNat = cap := by simp
        rw [hcap_toNat] at h
        omega
    · -- x ≠ ⊤, so x is a natural number
      have hx_nat : ∃ n : ℕ, (n : ℕ∞) = x :=
        ENat.ne_top_iff_exists.mp hx_top
      rcases hx_nat with ⟨n, hx_nat⟩
      subst hx_nat
      have h_min1 : min ((1 : ℕ∞) + (n : ℕ∞)) (cap : ℕ∞) = ((min (n+1) cap : ℕ) : ℕ∞) := by
        calc
          min ((1 : ℕ∞) + (n : ℕ∞)) (cap : ℕ∞) = min ((n : ℕ∞) + 1) (cap : ℕ∞) := by simp [add_comm]
          _ = min (((n+1 : ℕ) : ℕ∞)) (cap : ℕ∞) := by simp
          _ = ((min (n+1) cap : ℕ) : ℕ∞) := (WithTop.coe_min (n+1) cap).symm
      have h_min2 : min (n : ℕ∞) (cap : ℕ∞) = ((min n cap : ℕ) : ℕ∞) :=
        (WithTop.coe_min n cap).symm
      simp [minE, h_min1, h_min2, ENat.toNat_natCast]
      omega
  -- Lemma: minE (1 + x) cap ≤ cap for all x
  have h_minE_one_add_le_cap (x : ℕ∞) : minE (1 + x) cap ≤ cap := by
    dsimp [minE]
    have hmin : min (1 + x) (cap : ℕ∞) ≤ (cap : ℕ∞) := min_le_right _ _
    have hfin : (cap : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top cap
    exact ENat.toNat_le_toNat hmin hfin
  -- Lemma: for k > cap, minE (1 + x) cap = k is impossible
  have h_not_gt_cap (x : ℕ∞) (k : ℕ) (hk : cap < k) : minE (1 + x) cap ≠ k := by
    intro heq
    have hle := h_minE_one_add_le_cap x
    rw [heq] at hle
    omega
  -- Lemma: for k = cap, minE (1 + x) cap = cap ↔ (minE x cap = cap-1 ∨ minE x cap = cap)
  have h_eq_cap (x : ℕ∞) : (minE (1 + x) cap = cap) ↔ (minE x cap = cap - 1 ∨ minE x cap = cap) := by
    by_cases hx_top : x = ⊤
    · subst hx_top
      constructor
      · intro _; right; dsimp [minE]; simp
      · intro h; rcases h with (h | h)
        · -- h : minE ⊤ cap = cap - 1
          dsimp [minE] at h; simp at h
          omega
        · -- h : minE ⊤ cap = cap
          dsimp [minE]; simp
    · have hx_nat : ∃ n : ℕ, (n : ℕ∞) = x := ENat.ne_top_iff_exists.mp hx_top
      rcases hx_nat with ⟨n, hx_nat⟩
      subst hx_nat
      have h_min1 : min ((1 : ℕ∞) + (n : ℕ∞)) (cap : ℕ∞) = ((min (n+1) cap : ℕ) : ℕ∞) := by
        calc
          min ((1 : ℕ∞) + (n : ℕ∞)) (cap : ℕ∞) = min ((n : ℕ∞) + 1) (cap : ℕ∞) := by simp [add_comm]
          _ = min (((n+1 : ℕ) : ℕ∞)) (cap : ℕ∞) := by simp
          _ = ((min (n+1) cap : ℕ) : ℕ∞) := (WithTop.coe_min (n+1) cap).symm
      have h_min2 : min (n : ℕ∞) (cap : ℕ∞) = ((min n cap : ℕ) : ℕ∞) := (WithTop.coe_min n cap).symm
      simp [minE, h_min1, h_min2, ENat.toNat_natCast]
      omega
  -- Now the main case analysis on k
  by_cases hk0 : k = 0
  · subst hk0
    simp [capShift]
    have h_empty : {ω | minE (1 + X ω) cap = 0} = (∅ : Set Ω) := by
      ext ω; simp [h_minE_one_add_ne_zero (X ω)]
    simp [h_empty]
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    by_cases hk_lt_cap : k < cap
    · -- 0 < k < cap
      simp [capShift, hk0, hk_lt_cap]
      have h_set_eq : {ω | minE (1 + X ω) cap = k} = {ω | minE (X ω) cap = k - 1} := by
        ext ω; simp [h_eq_lt_cap (X ω) k hk_pos hk_lt_cap]
      simp [h_set_eq]
    · -- k ≥ cap
      have hk_ge_cap : cap ≤ k := Nat.le_of_not_lt hk_lt_cap
      by_cases hk_eq_cap : k = cap
      · -- k = cap
        rw [hk_eq_cap]
        simp [capShift, show cap ≠ 0 from by omega]
        have h_set_eq : {ω | minE (1 + X ω) cap = cap} = {ω | minE (X ω) cap = cap - 1} ∪ {ω | minE (X ω) cap = cap} := by
          ext ω; simp [h_eq_cap (X ω)]
        have h_disjoint : Disjoint {ω | minE (X ω) cap = cap - 1} {ω | minE (X ω) cap = cap} := by
          refine Set.disjoint_iff_inter_eq_empty.mpr ?_
          ext ω; simp; intro h1 h2; omega
        have h_countable1 : Set.Countable {x : ℕ∞ | minE x cap = cap - 1} :=
          Set.Countable.mono (Set.subset_univ _) Set.countable_univ
        have h_countable2 : Set.Countable {x : ℕ∞ | minE x cap = cap} :=
          Set.Countable.mono (Set.subset_univ _) Set.countable_univ
        have h_meas_set1 : MeasurableSet {x : ℕ∞ | minE x cap = cap - 1} :=
          h_countable1.measurableSet
        have h_meas_set2 : MeasurableSet {x : ℕ∞ | minE x cap = cap} :=
          h_countable2.measurableSet
        have h_meas1 : MeasurableSet {ω | minE (X ω) cap = cap - 1} :=
          hX h_meas_set1
        have h_meas2 : MeasurableSet {ω | minE (X ω) cap = cap} :=
          hX h_meas_set2
        rw [h_set_eq]
        rw [measure_union h_disjoint h_meas2]
        simp [ENNReal.toReal_add]
      · -- k > cap
        have hk_gt_cap : cap < k := by omega
        simp [capShift, hk0, hk_lt_cap, hk_eq_cap]
        have h_empty : {ω | minE (1 + X ω) cap = k} = (∅ : Set Ω) := by
          ext ω; simp [h_not_gt_cap (X ω) k hk_gt_cap]
        simp [h_empty]

theorem measure_decomp {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (Λ : Measure Ω) [SFinite Λ] (π : Measure X) (h : Ω → X) (g : Ω → Ω) (hh : Measurable h)
    (hg : Measurable g) (hmap : Λ.map (fun ω => (h ω, g ω)) = π.prod Λ) (S : Set (X × Ω))
    (hS : MeasurableSet S) :
    Λ {ω | (h ω, g ω) ∈ S} = ∑' x, π {x} * Λ {ω | (x, ω) ∈ S} := by
  calc
    Λ {ω | (h ω, g ω) ∈ S} = (Λ.map (fun ω => (h ω, g ω))) S := by
      simpa [Set.preimage] using (Measure.map_apply (hh.prodMk hg) hS).symm
    _ = (π.prod Λ) S := by rw [hmap]
    _ = ∫⁻ x, Λ (Prod.mk x ⁻¹' S) ∂π := by rw [Measure.prod_apply hS]
    _ = ∑' x, Λ (Prod.mk x ⁻¹' S) * π {x} := by rw [lintegral_countable']
    _ = ∑' x, π {x} * Λ (Prod.mk x ⁻¹' S) := by
      refine tsum_congr (fun x => ?_)
      rw [mul_comm]
    _ = ∑' x, π {x} * Λ {ω | (x, ω) ∈ S} := rfl

theorem map_dir_shift (ρ : Measure ℕ) [IsProbabilityMeasure ρ] :
    (lowMeasure ρ).map (fun ω => (ω.1 0, shiftD ω)) =
      (uniformOn Set.univ : Measure (Fin 4)).prod (lowMeasure ρ) := by
  -- helper: split a direction sequence into (first direction, rest)
  let f : (ℕ → Fin 4) → (Fin 4 × (ℕ → Fin 4)) := fun D => (D 0, fun i => D (i + 1))
  have hf_meas : Measurable f := by measurability
  -- the target map is the composition of Prod.map f id with the associator
  have h_decomp : (fun ω => (ω.1 0, shiftD ω)) =
      MeasurableEquiv.prodAssoc ∘
      (Prod.map f (id : ((Fin 3 → ℕ) × (Fin 3 → ℕ → Bool)) → ((Fin 3 → ℕ) × (Fin 3 → ℕ → Bool)))) := by
    funext ω
    rcases ω with ⟨D, r⟩
    rfl
  rw [h_decomp]
  -- (lowMeasure ρ) = dirMeasure.prod M  where M is the rest
  -- Use map_map to peel off the composition
  have h_map_meas : Measurable (Prod.map f (id : ((Fin 3 → ℕ) × (Fin 3 → ℕ → Bool)) → ((Fin 3 → ℕ) × (Fin 3 → ℕ → Bool)))) := by
    measurability
  rw [← Measure.map_map MeasurableEquiv.prodAssoc.measurable h_map_meas]
  -- Now we have ((lowMeasure ρ).map (Prod.map f id)).map MeasurableEquiv.prodAssoc
  -- Expand lowMeasure
  unfold lowMeasure
  -- (dirMeasure.prod M).map (Prod.map f id) = (dirMeasure.map f).prod (M.map id) = (dirMeasure.map f).prod M
  rw [← Measure.map_prod_map dirMeasure ((Measure.pi fun _ : Fin 3 => ρ).prod (Measure.pi fun _ : Fin 3 => coinSeq))
    hf_meas measurable_id]
  simp
  -- Now: ((dirMeasure.map f).prod M).map MeasurableEquiv.prodAssoc
  -- Use infinitePi_map_pair_injective: dirMeasure.map f = (uniformOn univ).prod dirMeasure
  have h_dir_map : (Measure.infinitePi fun _ : ℕ => (uniformOn Set.univ : Measure (Fin 4))).map f =
      (uniformOn Set.univ : Measure (Fin 4)).prod (Measure.infinitePi fun _ : ℕ => (uniformOn Set.univ : Measure (Fin 4))) := by
    -- This is exactly FrogModel.infinitePi_map_pair_injective with e = Nat.succ, i₀ = 0
    simpa [dirMeasure, f] using
      FrogModel.infinitePi_map_pair_injective (μ := uniformOn Set.univ) (e := Nat.succ)
        (he := Nat.succ_injective) (i₀ := 0) (hi₀ := fun a => Nat.succ_ne_zero a)
  unfold dirMeasure
  rw [h_dir_map]
  -- Now: (((uniformOn univ).prod dirMeasure).prod M).map MeasurableEquiv.prodAssoc
  -- = (uniformOn univ).prod (dirMeasure.prod M)  by prodAssoc_prod
  rw [Measure.prodAssoc_prod]
  -- Now: (uniformOn univ).prod (lowMeasure ρ)

/-- `(a, (b, c)) ↦ (b, (a, c))` preserves the product measure. -/
theorem mp_swap12 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa] [SFinite μb] [SFinite μc] :
    MeasurePreserving (fun p : α × (β × γ) => (p.2.1, (p.1, p.2.2)))
      (μa.prod (μb.prod μc)) (μb.prod (μa.prod μc)) := by
  have a := (measurePreserving_prodAssoc μa μb μc).symm
  have b := (Measure.measurePreserving_swap (μ := μa) (ν := μb)).prod (MeasurePreserving.id μc)
  have c := measurePreserving_prodAssoc μb μa μc
  exact c.comp (b.comp a)

/-- The coins of the child `s`: the first coin and the remaining sample are independent. -/
theorem map_coins_shift (s : Fin 3) :
    (Measure.pi fun _ : Fin 3 => coinSeq).map
        (fun ζ : Fin 3 → ℕ → Bool => (ζ s 0, Function.update ζ s fun i => ζ s (i + 1))) =
      coinLaw.prod (Measure.pi fun _ : Fin 3 => coinSeq) := by
  have hupd : Measurable fun p : (ℕ → Bool) × (Fin 3 → ℕ → Bool) => Function.update p.2 s p.1 :=
    measurable_update'.comp (measurable_snd.prodMk measurable_fst)
  have hkc : Measurable fun ζ : Fin 3 → ℕ → Bool =>
      (ζ s 0, Function.update ζ s fun i => ζ s (i + 1)) := by
    refine ((measurable_pi_apply 0).comp (measurable_pi_apply s)).prodMk ?_
    exact measurable_update'.comp (measurable_id.prodMk
      (measurable_pi_iff.mpr fun i => (measurable_pi_apply (i + 1)).comp (measurable_pi_apply s)))
  have hht : Measurable fun x : ℕ → Bool => (x 0, fun i => x (i + 1)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_iff.mpr fun i => measurable_pi_apply (i + 1))
  have hsplit : coinSeq.map (fun x : ℕ → Bool => (x 0, fun i => x (i + 1))) =
      coinLaw.prod coinSeq := by
    unfold coinSeq
    exact FrogModel.infinitePi_map_pair_injective coinLaw Nat.succ Nat.succ_injective 0
      fun a => Nat.succ_ne_zero a
  have hfin : Measurable fun q : Bool × ((ℕ → Bool) × (Fin 3 → ℕ → Bool)) =>
      (q.1, Function.update q.2.2 s q.2.1) := measurable_fst.prodMk (hupd.comp measurable_snd)
  have hcomp : (fun ζ : Fin 3 → ℕ → Bool => (ζ s 0, Function.update ζ s fun i => ζ s (i + 1))) ∘
      (fun p : (ℕ → Bool) × (Fin 3 → ℕ → Bool) => Function.update p.2 s p.1) =
      (fun q : Bool × ((ℕ → Bool) × (Fin 3 → ℕ → Bool)) => (q.1, Function.update q.2.2 s q.2.1)) ∘
        (MeasurableEquiv.prodAssoc : (Bool × (ℕ → Bool)) × (Fin 3 → ℕ → Bool) ≃ᵐ _) ∘
        Prod.map (fun x : ℕ → Bool => (x 0, fun i => x (i + 1))) id := by
    funext p
    simp [MeasurableEquiv.prodAssoc, Function.update_idem]
  conv_lhs => rw [← pi_update_map coinSeq s]
  rw [Measure.map_map hkc hupd, hcomp, ← Measure.map_map hfin
    (MeasurableEquiv.prodAssoc.measurable.comp (hht.prodMap measurable_id)),
    ← Measure.map_map MeasurableEquiv.prodAssoc.measurable (hht.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hht measurable_id, hsplit, Measure.map_id,
    (measurePreserving_prodAssoc coinLaw coinSeq (Measure.pi fun _ : Fin 3 => coinSeq)).map_eq]
  have hpm : (fun q : Bool × ((ℕ → Bool) × (Fin 3 → ℕ → Bool)) =>
      (q.1, Function.update q.2.2 s q.2.1)) =
      Prod.map id (fun p : (ℕ → Bool) × (Fin 3 → ℕ → Bool) => Function.update p.2 s p.1) := rfl
  rw [hpm, ← Measure.map_prod_map _ _ measurable_id hupd, Measure.map_id,
    pi_update_map coinSeq s]

theorem map_coin_shift (ρ : Measure ℕ) [IsProbabilityMeasure ρ] (s : Fin 3) :
    (lowMeasure ρ).map (fun ω => (ω.2.2 s 0,
        ((ω.1, ω.2.1, Function.update ω.2.2 s fun i => ω.2.2 s (i + 1)) : LSample))) =
      coinLaw.prod (lowMeasure ρ) := by
  set P := Measure.pi fun _ : Fin 3 => ρ
  set C := Measure.pi fun _ : Fin 3 => coinSeq
  have hkc : Measurable fun ζ : Fin 3 → ℕ → Bool =>
      (ζ s 0, Function.update ζ s fun i => ζ s (i + 1)) := by
    refine ((measurable_pi_apply 0).comp (measurable_pi_apply s)).prodMk ?_
    exact measurable_update'.comp (measurable_id.prodMk
      (measurable_pi_iff.mpr fun i => (measurable_pi_apply (i + 1)).comp (measurable_pi_apply s)))
  have e1 : MeasurePreserving (fun ζ : Fin 3 → ℕ → Bool =>
      (ζ s 0, Function.update ζ s fun i => ζ s (i + 1))) C (coinLaw.prod C) :=
    ⟨hkc, map_coins_shift s⟩
  have e2 := (MeasurePreserving.id dirMeasure).prod ((MeasurePreserving.id P).prod e1)
  have e3 := (MeasurePreserving.id dirMeasure).prod (mp_swap12 P coinLaw C)
  have e4 := mp_swap12 dirMeasure coinLaw (P.prod C)
  exact (e4.comp (e3.comp e2)).map_eq

theorem map_R_update (ρ : Measure ℕ) [IsProbabilityMeasure ρ] (s : Fin 3) :
    (ρ.prod (lowMeasure ρ)).map
        (fun p => ((p.2.1, Function.update p.2.2.1 s p.1, p.2.2.2) : LSample)) = lowMeasure ρ := by
  set P := Measure.pi fun _ : Fin 3 => ρ
  set C := Measure.pi fun _ : Fin 3 => coinSeq
  have hupd : MeasurePreserving (fun q : ℕ × (Fin 3 → ℕ) => Function.update q.2 s q.1)
      (ρ.prod P) P :=
    ⟨measurable_update'.comp (measurable_snd.prodMk measurable_fst), pi_update_map ρ s⟩
  have e1 := mp_swap12 ρ dirMeasure (P.prod C)
  have e2 := (MeasurePreserving.id dirMeasure).prod (measurePreserving_prodAssoc ρ P C).symm
  have e3 := (MeasurePreserving.id dirMeasure).prod (hupd.prod (MeasurePreserving.id C))
  exact (e3.comp (e2.comp e1)).map_eq

theorem measure_R_decomp (ρ : Measure ℕ) [IsProbabilityMeasure ρ] (s : Fin 3) (S : Set (ℕ × LSample))
    (hS : MeasurableSet S)
    (hinv : ∀ r r' ω, (r, ω) ∈ S ↔ (r, ((ω.1, Function.update ω.2.1 s r', ω.2.2) : LSample)) ∈ S) :
    lowMeasure ρ {ω | (ω.2.1 s, ω) ∈ S} = ∑' r, ρ {r} * lowMeasure ρ {ω | (r, ω) ∈ S} := by
  set U : ℕ × LSample → LSample := fun p => ((p.2.1, Function.update p.2.2.1 s p.1, p.2.2.2) : LSample) with hU
  have hmap := map_R_update ρ s
  have hUmeas : Measurable U := by
    unfold U
    fun_prop
  have h_target_meas : MeasurableSet {ω : LSample | (ω.2.1 s, ω) ∈ S} := by
    have h_meas : Measurable (fun (ω : LSample) => (ω.2.1 s, ω) : LSample → ℕ × LSample) := by
      fun_prop
    exact hS.preimage h_meas
  have hpreimage : U ⁻¹' {ω | (ω.2.1 s, ω) ∈ S} = S := by
    ext ⟨r, ω⟩
    constructor
    · intro h
      have hmem : (r, U (r, ω)) ∈ S := by
        simpa [U] using h
      rw [hinv r r ω]
      simpa [U] using hmem
    · intro h
      have hmem : (r, U (r, ω)) ∈ S := by
        rw [← hinv r r ω]
        simpa [U] using h
      simpa [U] using hmem
  have hLHS : lowMeasure ρ {ω | (ω.2.1 s, ω) ∈ S} = ∑' r, ρ {r} * (lowMeasure ρ) {ω | (r, ω) ∈ S} := by
    have h1 : lowMeasure ρ {ω | (ω.2.1 s, ω) ∈ S} = (ρ.prod (lowMeasure ρ)) S := by
      conv =>
        lhs
        rw [← hmap]
      rw [Measure.map_apply hUmeas h_target_meas, hpreimage]
    rw [h1, Measure.prod_apply hS, MeasureTheory.lintegral_countable']
    simp_rw [mul_comm]
    refine tsum_congr fun r => ?_
    have hpreimage2 : Prod.mk r ⁻¹' S = {ω | (r, ω) ∈ S} := by
      ext ω; simp
    rw [hpreimage2]
  exact hLHS

theorem integral_nat_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℕ)
    (hX : Measurable X) (E : ℕ) (hXE : ∀ ω, X ω ≤ E) (f : ℕ → ℝ) :
    ∫ ω, f (X ω) ∂μ = ∑ k ∈ Finset.range (E + 1), (μ {ω | X ω = k}).toReal * f k := by
  have hmeas (k : ℕ) : MeasurableSet {ω | X ω = k} := hX (measurableSet_singleton k)
  have hmem (ω : Ω) : X ω ∈ Finset.range (E + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hXE ω)
  calc
    ∫ ω, f (X ω) ∂μ
        = ∫ ω, (∑ k ∈ Finset.range (E + 1), (if X ω = k then f k else 0)) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [] with ω
      calc
        f (X ω) = (if X ω ∈ Finset.range (E + 1) then f (X ω) else 0) := by simp [hmem ω]
        _ = ∑ k ∈ Finset.range (E + 1), (if X ω = k then f k else 0) := by
          rw [← Finset.sum_ite_eq]
    _ = ∑ k ∈ Finset.range (E + 1), ∫ ω, (if X ω = k then f k else 0) ∂μ := by
      rw [integral_finsetSum]
      intro k hk
      have h_int : Integrable (fun (_ : Ω) => f k) μ := integrable_const _
      have h_indicator : (fun (ω : Ω) => if X ω = k then f k else 0) =
          ({ω | X ω = k}).indicator (fun _ => f k) := by
        ext ω; simp [Set.indicator]
      rw [h_indicator]
      exact h_int.indicator (hmeas k)
    _ = ∑ k ∈ Finset.range (E + 1), (μ.real {ω | X ω = k}) • f k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have h_indicator : (fun (ω : Ω) => if X ω = k then f k else 0) =
          ({ω | X ω = k}).indicator (fun _ => f k) := by
        ext ω; simp [Set.indicator]
      rw [h_indicator]
      rw [integral_indicator_const _ (hmeas k)]
    _ = ∑ k ∈ Finset.range (E + 1), (μ {ω | X ω = k}).toReal * f k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Measure.real_def, smul_eq_mul]

theorem coins_indep_map (μ : Measure ((ℕ → ℕ∞) × (ℕ → Bool))) [IsProbabilityMeasure μ]
    (hξ : ∀ i, μ {z | z.2 i = true} = 3⁻¹)
    (hind : ∀ i, IndepFun (fun z => z.2 i)
      (fun z => ((fun l : Fin (i + 1) => z.1 l), (fun l : Fin i => z.2 l))) μ) :
    μ.map (fun z => (z.1 1, fun i => z.2 (i + 1))) = (μ.map fun z => z.1 1).prod coinSeq := by
  classical
  have hWm : Measurable fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 1 :=
    (measurable_pi_apply 1).comp measurable_fst
  have hΞm : Measurable fun z : (ℕ → ℕ∞) × (ℕ → Bool) => fun i => z.2 (i + 1) :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply (i + 1)).comp measurable_snd
  -- the law of one coin
  have hcoin : ∀ j (T : Set Bool), μ {z | z.2 j ∈ T} = coinLaw T := by
    intro j T
    have hm : Measurable fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 j :=
      (measurable_pi_apply j).comp measurable_snd
    have hmap : μ.map (fun z => z.2 j) = coinLaw := by
      rw [Measure.ext_iff_singleton]
      intro b
      rw [Measure.map_apply hm (measurableSet_singleton b)]
      have ht : μ {z | z.2 j = true} = 3⁻¹ := hξ j
      have hf : μ {z | z.2 j = false} = 1 - 3⁻¹ := by
        have hs : {z : (ℕ → ℕ∞) × (ℕ → Bool) | z.2 j = false} = {z | z.2 j = true}ᶜ := by
          ext z; simp
        have hmt : MeasurableSet {z : (ℕ → ℕ∞) × (ℕ → Bool) | z.2 j = true} :=
          hm (measurableSet_singleton true)
        rw [hs, prob_compl_eq_one_sub hmt, ht]
      cases b
      · rw [show (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 j) ⁻¹' {false} = {z | z.2 j = false} from rfl, hf]
        simp [coinLaw]
      · rw [show (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 j) ⁻¹' {true} = {z | z.2 j = true} from rfl, ht]
        simp [coinLaw]
    rw [← hmap, Measure.map_apply hm (MeasurableSet.of_discrete)]
    rfl
  -- the boxes
  have hbox : ∀ (A : Set ℕ∞) (s : Finset ℕ) (t : ℕ → Set Bool),
      μ ({z | z.1 1 ∈ A} ∩ {z | ∀ i ∈ s, z.2 (i + 1) ∈ t i}) =
        μ {z | z.1 1 ∈ A} * ∏ i ∈ s, coinLaw (t i) := by
    intro A s t
    induction s using Finset.induction_on_max with
    | empty => simp
    | insert a s hlt ih =>
      have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
      rw [Finset.prod_insert ha]
      set E' : Set ((Fin (a + 1 + 1) → ℕ∞) × (Fin (a + 1) → Bool)) :=
        {p | p.1 ⟨1, by omega⟩ ∈ A ∧
          ∀ i (hi : i ∈ s), p.2 ⟨i + 1, by have := hlt i hi; omega⟩ ∈ t i} with hE'def
      have hE : {z : (ℕ → ℕ∞) × (ℕ → Bool) | z.1 1 ∈ A} ∩ {z | ∀ i ∈ s, z.2 (i + 1) ∈ t i} =
          (fun z : (ℕ → ℕ∞) × (ℕ → Bool) =>
            ((fun l : Fin (a + 1 + 1) => z.1 l), (fun l : Fin (a + 1) => z.2 l))) ⁻¹' E' := by
        ext z
        simp [hE'def]
      have hE2 : {z : (ℕ → ℕ∞) × (ℕ → Bool) | z.1 1 ∈ A} ∩
          {z | ∀ i ∈ insert a s, z.2 (i + 1) ∈ t i} =
          (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 (a + 1)) ⁻¹' (t a) ∩
            (fun z : (ℕ → ℕ∞) × (ℕ → Bool) =>
              ((fun l : Fin (a + 1 + 1) => z.1 l), (fun l : Fin (a + 1) => z.2 l))) ⁻¹' E' := by
        rw [← hE]
        ext z
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Finset.mem_insert,
          forall_eq_or_imp]
        tauto
      have hE'm : MeasurableSet E' := (Set.to_countable E').measurableSet
      rw [hE2, (hind (a + 1)).measure_inter_preimage_eq_mul _ _ (MeasurableSet.of_discrete) hE'm,
        ← hE, ih]
      rw [show (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 (a + 1)) ⁻¹' (t a) =
        {z | z.2 (a + 1) ∈ t a} from rfl, hcoin]
      ring
  -- the coins after the first, restricted to an event of `G(1)`
  have hrestr : ∀ A : Set ℕ∞, (μ.restrict {z | z.1 1 ∈ A}).map (fun z => fun i => z.2 (i + 1)) =
      μ {z | z.1 1 ∈ A} • coinSeq := by
    intro A
    have hAm : MeasurableSet {z : (ℕ → ℕ∞) × (ℕ → Bool) | z.1 1 ∈ A} :=
      hWm (MeasurableSet.of_discrete (s := A))
    by_cases hc : μ {z | z.1 1 ∈ A} = 0
    · rw [hc, zero_smul, Measure.restrict_eq_zero.2 hc, Measure.map_zero]
    · have hc' : μ {z | z.1 1 ∈ A} ≠ ⊤ := measure_ne_top _ _
      have h : (μ {z | z.1 1 ∈ A})⁻¹ •
          (μ.restrict {z | z.1 1 ∈ A}).map (fun z => fun i => z.2 (i + 1)) = coinSeq := by
        unfold coinSeq
        refine Measure.eq_infinitePi _ fun s t ht => ?_
        have hpi : MeasurableSet (Set.pi (↑s) t) :=
          MeasurableSet.pi s.countable_toSet fun i _ => ht i
        rw [Measure.smul_apply, Measure.map_apply hΞm hpi, Measure.restrict_apply' hAm]
        rw [show (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => fun i => z.2 (i + 1)) ⁻¹' (Set.pi (↑s) t) ∩
            {z | z.1 1 ∈ A} = {z | z.1 1 ∈ A} ∩ {z | ∀ i ∈ s, z.2 (i + 1) ∈ t i} from by
          ext z
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Finset.mem_coe,
            Set.mem_ofPred_eq]
          tauto]
        rw [hbox, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hc hc', one_mul]
      rw [← h, smul_smul, ENNReal.mul_inv_cancel hc hc', one_smul]
  -- the joint law
  refine (Measure.prod_eq fun A B hA hB => ?_).symm
  rw [Measure.map_apply (hWm.prodMk hΞm) (hA.prod hB), Measure.map_apply hWm hA]
  have h : ((μ.restrict {z | z.1 1 ∈ A}).map (fun z => fun i => z.2 (i + 1))) B =
      (μ {z | z.1 1 ∈ A} • coinSeq) B := by rw [hrestr A]
  have hAm : MeasurableSet {z : (ℕ → ℕ∞) × (ℕ → Bool) | z.1 1 ∈ A} := hWm hA
  rw [Measure.map_apply hΞm hB, Measure.restrict_apply' hAm, Measure.smul_apply,
    smul_eq_mul] at h
  rw [show (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => (z.1 1, fun i => z.2 (i + 1))) ⁻¹' (A ×ˢ B) =
      (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => fun i => z.2 (i + 1)) ⁻¹' B ∩ {z | z.1 1 ∈ A} from by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto, h]
  rfl

theorem plR_law (Q : Measure ℕ∞) [IsProbabilityMeasure Q] (GM r : ℕ) :
    plR (fun g => (Q {x | x ≤ (g : ℕ∞)}).toReal) GM r =
      (Q {x | (min x ((GM + 1 : ℕ) : ℕ∞)).toNat = r}).toReal := by
  have hmeas : ∀ (A : Set ℕ∞), MeasurableSet A := fun _ => MeasurableSet.of_discrete
  have hfin : ∀ (A : Set ℕ∞), Q A ≠ ∞ := fun A => measure_ne_top Q A
  -- Helper lemma: for r ≤ GM, (min x (GM+1)).toNat = r ↔ x = r
  have h_eq_lemma (r : ℕ) (hr : r ≤ GM) : {x : ℕ∞ | (min x ((GM + 1 : ℕ) : ℕ∞)).toNat = r} = {x | x = (r : ℕ∞)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    cases x using ENat.recTopCoe
    · -- x = ⊤
      have hmin : (min (⊤ : ℕ∞) ((GM + 1 : ℕ) : ℕ∞)) = ((GM + 1 : ℕ) : ℕ∞) := by simp
      rw [hmin]
      have hne : (GM + 1 : ℕ) ≠ r := by omega
      have htoNat : ((GM + 1 : ℕ) : ℕ∞).toNat = (GM + 1 : ℕ) := by simp
      rw [htoNat]
      simp [hne]
    · -- x = n : ℕ
      rename_i n
      by_cases hle : n ≤ GM + 1
      · have hmin : (min (n : ℕ∞) ((GM + 1 : ℕ) : ℕ∞)) = (n : ℕ∞) := min_eq_left (by exact_mod_cast hle)
        rw [hmin]
        have htoNat : (n : ℕ∞).toNat = n := by simp
        rw [htoNat]
        simp
      · have hmin : (min (n : ℕ∞) ((GM + 1 : ℕ) : ℕ∞)) = ((GM + 1 : ℕ) : ℕ∞) :=
          min_eq_right (by exact_mod_cast (show GM + 1 ≤ n from by omega))
        rw [hmin]
        have htoNat : ((GM + 1 : ℕ) : ℕ∞).toNat = (GM + 1 : ℕ) := by simp
        rw [htoNat]
        have hne : (GM + 1 : ℕ) ≠ r := by omega
        have hne' : n ≠ r := by omega
        simp [hne, hne']
  -- Helper lemma: (min x (GM+1)).toNat = GM+1 ↔ GM+1 ≤ x
  have h_ge_lemma : {x : ℕ∞ | (min x ((GM + 1 : ℕ) : ℕ∞)).toNat = (GM + 1 : ℕ)} = {x | (GM + 1 : ℕ∞) ≤ x} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    cases x using ENat.recTopCoe
    · -- x = ⊤
      simp
    · -- x = n : ℕ
      rename_i n
      by_cases hle : n ≤ GM + 1
      · have hmin : (min (n : ℕ∞) ((GM + 1 : ℕ) : ℕ∞)) = (n : ℕ∞) := min_eq_left (by exact_mod_cast hle)
        rw [hmin]
        have htoNat : (n : ℕ∞).toNat = n := by simp
        rw [htoNat]
        -- Goal: n = GM+1 ↔ (GM+1 : ℕ∞) ≤ (n : ℕ∞)
        constructor
        · intro hn; subst hn; simp
        · intro hge
          have hge_nat : GM + 1 ≤ n := by exact_mod_cast hge
          exact le_antisymm hle hge_nat
      · have hmin : (min (n : ℕ∞) ((GM + 1 : ℕ) : ℕ∞)) = ((GM + 1 : ℕ) : ℕ∞) :=
          min_eq_right (by exact_mod_cast (show GM + 1 ≤ n from by omega))
        rw [hmin]
        have htoNat : ((GM + 1 : ℕ) : ℕ∞).toNat = (GM + 1 : ℕ) := by simp
        rw [htoNat]
        -- Goal: GM+1 = GM+1 ↔ (GM+1 : ℕ∞) ≤ (n : ℕ∞)
        -- LHS is true, RHS is true since n > GM+1
        simp
        exact_mod_cast (show GM + 1 ≤ n from by omega)
  -- Helper lemma: for r > GM+1, set is empty
  have h_empty_lemma (r : ℕ) (hr : GM + 1 < r) : {x : ℕ∞ | (min x ((GM + 1 : ℕ) : ℕ∞)).toNat = r} = (∅ : Set ℕ∞) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    cases x using ENat.recTopCoe
    · -- x = ⊤
      have htoNat : (min (⊤ : ℕ∞) ((GM + 1 : ℕ) : ℕ∞)).toNat = (GM + 1 : ℕ) := by simp
      rw [htoNat]
      omega
    · -- x = n : ℕ
      rename_i n
      intro h
      have hmin : (min (n : ℕ∞) ((GM + 1 : ℕ) : ℕ∞)).toNat = r := h
      have hmin_le : (min (n : ℕ∞) ((GM + 1 : ℕ) : ℕ∞)) ≤ (GM + 1 : ℕ∞) := min_le_right _ _
      have htoNat_le : (min (n : ℕ∞) ((GM + 1 : ℕ) : ℕ∞)).toNat ≤ (GM + 1 : ℕ) := by
        have h_ne_top : (GM + 1 : ℕ∞) ≠ ⊤ := by simp
        exact ENat.toNat_le_toNat hmin_le h_ne_top
      rw [hmin] at htoNat_le
      omega
  by_cases hr0 : r = 0
  · subst hr0
    simp [plR, Ftil]
  · by_cases hr_le_GM1 : r ≤ GM + 1
    · by_cases hr_le_GM : r ≤ GM
      · -- 1 ≤ r ≤ GM
        have h_eq := h_eq_lemma r hr_le_GM
        rw [h_eq]
        simp [plR, Ftil, hr0, hr_le_GM1, hr_le_GM]
        -- Goal: (Q {x | x ≤ r}).toReal - (Q {x | x ≤ r - 1}).toReal = (Q {↑r}).toReal
        have h_disjoint : Disjoint ({x : ℕ∞ | x ≤ (r - 1 : ℕ∞)} : Set ℕ∞) {x | x = (r : ℕ∞)} := by
          rw [Set.disjoint_iff_inter_eq_empty]
          ext x; simp; intro hx1 hx2; subst hx2
          -- Goal: False from (r : ℕ∞) ≤ (r - 1 : ℕ∞)
          have h_lt_nat : (r - 1 : ℕ) < r := by
            have hr_pos : 1 ≤ r := by omega
            exact Nat.sub_lt hr_pos (by omega)
          have hx1_nat' : r ≤ r - 1 := by exact_mod_cast hx1
          omega
        have h_union : {x : ℕ∞ | x ≤ (r : ℕ∞)} = ({x : ℕ∞ | x ≤ (r - 1 : ℕ∞)} ∪ {x | x = (r : ℕ∞)}) := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_union]
          constructor
          · intro hx
            by_cases hxr : x = (r : ℕ∞)
            · right; exact hxr
            · left
              cases x using ENat.recTopCoe
              · -- x = ⊤, but ⊤ ≤ r is impossible for r : ℕ
                have hlt : (r : ℕ∞) < (⊤ : ℕ∞) := by simp
                exfalso
                exact (hlt.trans_le hx).ne rfl
              · rename_i n
                have hnle : (n : ℕ∞) ≤ (r : ℕ∞) := hx
                have hn_not_r : (n : ℕ∞) ≠ (r : ℕ∞) := hxr
                have hn_le_r : n ≤ r := by exact_mod_cast hnle
                have hn_ne_r : n ≠ r := by
                  intro heq; apply hn_not_r; exact_mod_cast heq
                have hn_le_r1 : n ≤ r - 1 := by omega
                exact_mod_cast hn_le_r1
          · intro hx
            rcases hx with (hx | hx)
            · exact le_trans hx (by simp)
            · rw [hx]
        have h_meas1 : MeasurableSet ({x : ℕ∞ | x ≤ (r - 1 : ℕ∞)} : Set ℕ∞) := hmeas _
        have h_meas2 : MeasurableSet ({x | x = (r : ℕ∞)} : Set ℕ∞) := hmeas _
        have h_fin1 : Q ({x : ℕ∞ | x ≤ (r - 1 : ℕ∞)}) ≠ ∞ := hfin _
        have h_fin2 : Q ({x | x = (r : ℕ∞)}) ≠ ∞ := hfin _
        rw [h_union, MeasureTheory.measure_union h_disjoint h_meas2]
        rw [ENNReal.toReal_add h_fin1 h_fin2]
        -- Goal: (a.toReal + b.toReal) - a.toReal = b.toReal
        ring_nf
        simp
      · -- r = GM+1
        have hr_eq_GM1 : r = GM + 1 := by omega
        subst hr_eq_GM1
        have h_eq := h_ge_lemma
        rw [h_eq]
        simp [plR, Ftil]
        -- Goal: 1 - (Q {x | x ≤ GM}).toReal = (Q {x | GM+1 ≤ x}).toReal
        have h_meas1 : MeasurableSet ({x : ℕ∞ | x ≤ (GM : ℕ∞)} : Set ℕ∞) := hmeas _
        have h_fin1 : Q ({x : ℕ∞ | x ≤ (GM : ℕ∞)}) ≠ ∞ := hfin _
        have huniv : Q (Set.univ : Set ℕ∞) = 1 := measure_univ
        have h_compl : ({x : ℕ∞ | (GM + 1 : ℕ∞) ≤ x}) = ({x : ℕ∞ | x ≤ (GM : ℕ∞)})ᶜ := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
          cases x using ENat.recTopCoe
          · simp
          · rename_i n
            constructor
            · intro hge hle
              have hle_nat : n ≤ GM := by exact_mod_cast hle
              have hge_nat : GM + 1 ≤ n := by exact_mod_cast hge
              omega
            · intro hle
              have hle_nat : GM < n := by
                by_contra! heq
                have : (n : ℕ∞) ≤ (GM : ℕ∞) := by exact_mod_cast heq
                exact hle this
              have : (GM + 1 : ℕ) ≤ n := by omega
              exact_mod_cast this
        rw [h_compl, measure_compl h_meas1 h_fin1, huniv]
        have h_one_ne_top : (1 : ENNReal) ≠ ∞ := by simp
        have h_le : Q ({x : ℕ∞ | x ≤ (GM : ℕ∞)}) ≤ (1 : ENNReal) := prob_le_one
        rw [ENNReal.toReal_sub_of_le h_le h_one_ne_top]
        simp
    · -- r > GM+1
      have hr_gt_GM1 : GM + 1 < r := by omega
      have h_empty := h_empty_lemma r hr_gt_GM1
      rw [h_empty]
      simp [plR, hr0, hr_le_GM1]

end FrogModel.D3.LaneC.Lower
