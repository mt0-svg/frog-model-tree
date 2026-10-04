module

public import FrogModel.D3.Interfaces.Closure

@[expose] public section

/-!
# Consequences of the coins (Lemma 10.7 (1) of the paper)

Lemma 10.3 and part (1) of Lemma 10.7. Each theorem takes the statements it uses as hypotheses (the
`Prop` statements of FrogModel/D3/Interfaces/Model.lean).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- `E G_m(k)` against the curve law. -/
theorem lintegral_plantedG_eq (hmeas : measurable_plantedPair) (m k : ℕ) :
    ∫⁻ π, (plantedG m k π : ℝ≥0∞) ∂pathMeasure = ∫⁻ G, (G k : ℝ≥0∞) ∂curveLaw m := by
  have hm : Measurable (plantedCurve m) := (hmeas m).fst
  have hf : Measurable fun G : ℕ → ℕ∞ => ((G k : ℕ∞) : ℝ≥0∞) :=
    (Measurable.of_discrete (α := ℕ∞)).comp (measurable_pi_apply k)
  unfold curveLaw
  rw [lintegral_map hf hm]
  rfl

/-- `P(G_m(k) ≤ g)` against the curve law. -/
theorem cdfG_eq (hmeas : measurable_plantedPair) (m k g : ℕ) :
    cdfG m k g = (curveLaw m {G | G k ≤ (g : ℕ∞)}).toReal := by
  have hm : Measurable (plantedCurve m) := (hmeas m).fst
  unfold cdfG curveLaw
  have hk : Measurable fun G : ℕ → ℕ∞ => G k := measurable_pi_apply k
  have hs : MeasurableSet {G : ℕ → ℕ∞ | G k ≤ (g : ℕ∞)} :=
    hk (MeasurableSet.of_discrete (s := {x : ℕ∞ | x ≤ (g : ℕ∞)}))
  rw [Measure.map_apply hm hs]
  rfl

/-- `E G_m(k + 1) ≥ E G_m(k) + 1/3` (Lemma 10.3 of the paper), as lintegrals. -/
theorem lintegral_succ_ge (hmeas : measurable_plantedPair)
    (hcoin : coin_coupling) (m k : ℕ) :
    ∫⁻ π, (plantedG m k π : ℝ≥0∞) ∂pathMeasure + 3⁻¹ ≤
      ∫⁻ π, (plantedG m (k + 1) π : ℝ≥0∞) ∂pathMeasure := by
  obtain ⟨μ, hμ, hfst, hξ, -, hae⟩ := hcoin m
  have hev : ∀ j, ∫⁻ G, (G j : ℝ≥0∞) ∂curveLaw m = ∫⁻ z, (z.1 j : ℝ≥0∞) ∂μ := by
    intro j
    have hf : Measurable fun G : ℕ → ℕ∞ => ((G j : ℕ∞) : ℝ≥0∞) :=
      (Measurable.of_discrete (α := ℕ∞)).comp (measurable_pi_apply j)
    rw [← hfst, lintegral_map hf measurable_fst]
  rw [lintegral_plantedG_eq hmeas, lintegral_plantedG_eq hmeas, hev, hev]
  have hcoin3 : ∫⁻ z, (if z.2 k then 1 else 0 : ℝ≥0∞) ∂μ = 3⁻¹ := by
    have hs : MeasurableSet {z : (ℕ → ℕ∞) × (ℕ → Bool) | z.2 k = true} :=
      (((measurable_pi_apply k).comp measurable_snd :
        Measurable fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 k)) (measurableSet_singleton true)
    rw [← hξ k, ← lintegral_indicator_one hs]
    congr 1
    ext z
    by_cases h : z.2 k <;> simp [h, Set.indicator]
  have hmeas1 : Measurable fun z : (ℕ → ℕ∞) × (ℕ → Bool) => (z.1 k : ℝ≥0∞) :=
    Measurable.of_discrete.comp ((measurable_pi_apply k).comp measurable_fst)
  calc ∫⁻ z, (z.1 k : ℝ≥0∞) ∂μ + 3⁻¹
      = ∫⁻ z, ((z.1 k : ℝ≥0∞) + if z.2 k then 1 else 0) ∂μ := by
        rw [lintegral_add_left hmeas1, hcoin3]
    _ ≤ ∫⁻ z, (z.1 (k + 1) : ℝ≥0∞) ∂μ := by
        refine lintegral_mono_ae (hae.mono fun z hz => ?_)
        have h := hz.2 k
        have h' : ((z.1 k + (if z.2 k then 1 else 0) : ℕ∞) : ℝ≥0∞) ≤ (z.1 (k + 1) : ℝ≥0∞) :=
          ENat.toENNReal_le.mpr h
        by_cases hb : z.2 k <;> simp_all

/-- `E G_m(k) < ∞`, from `E G_m(k) ≤ mu_m(k)`. -/
theorem lintegral_plantedG_ne_top (hfin : lintegral_plantedG_le) (m k : ℕ) :
    ∫⁻ π, (plantedG m k π : ℝ≥0∞) ∂pathMeasure ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hfin m k)

/-- `E G_m(k + 1) ≥ E G_m(k) + 1/3`. -/
theorem meanG_succ_ge (hmeas : measurable_plantedPair)
    (hcoin : coin_coupling) (hfin : lintegral_plantedG_le) (m k : ℕ) :
    meanG m k + 1 / 3 ≤ meanG m (k + 1) := by
  unfold meanG
  have h := lintegral_succ_ge hmeas hcoin m k
  have h1 := lintegral_plantedG_ne_top hfin m k
  have h2 := lintegral_plantedG_ne_top hfin m (k + 1)
  have := (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨h1, by simp⟩) h2).mpr h
  rw [ENNReal.toReal_add h1 (by simp)] at this
  simpa using this

/-- **Lemma 10.7 (1) of the paper** from the statements of measurability, of the coins (Lemma 10.3)
and of the all-awake count (Lemma 10.2). -/
theorem lemma17a_of (hmeas : measurable_plantedPair) (hcoin : coin_coupling)
    (hfin : lintegral_plantedG_le) : lemma17a := by
  intro m k
  have h := meanG_succ_ge hmeas hcoin hfin m k
  unfold deficit mu
  push_cast
  linarith

/-- Pascal's rule for the binomial cdf. -/
theorem binCdf_succ (k v : ℕ) (p : ℝ) :
    binCdf (k + 1) p (v + 1) = p * binCdf k p v + (1 - p) * binCdf k p (v + 1) ∧
      binCdf (k + 1) p 0 = (1 - p) * binCdf k p 0 := by
  have h0 : binCdf (k + 1) p 0 = (1 - p) * binCdf k p 0 := by
    dsimp [binCdf, binPmf]
    simp
    ring
  have hTerm (i : ℕ) (hi : 0 < i) : binPmf (k + 1) p i = p * binPmf k p (i - 1) + (1 - p) * binPmf k p i := by
    dsimp [binPmf]
    rw [Nat.choose_succ_left k i hi]
    push_cast
    by_cases hi_le_k : i ≤ k
    · have h_exp1 : ((k + 1 : ℕ) - i : ℕ) = (k : ℕ) - (i - 1) := by omega
      have h_exp_eq : (k : ℕ) - (i - 1) = (k : ℕ) - i + 1 := by omega
      calc
        ((k.choose (i - 1) : ℝ) + (k.choose i : ℝ)) * p ^ i * (1 - p) ^ ((k + 1 : ℕ) - i)
            = ((k.choose (i - 1) : ℝ) + (k.choose i : ℝ)) * p ^ i * (1 - p) ^ (k - (i - 1)) := by rw [h_exp1]
        _ = ((k.choose (i - 1) : ℝ) + (k.choose i : ℝ)) * p ^ i * (1 - p) ^ (k - i + 1) := by rw [h_exp_eq]
        _ = ((k.choose (i - 1) : ℝ) + (k.choose i : ℝ)) * p ^ i * ((1 - p) ^ (k - i) * (1 - p)) := by rw [pow_succ]
        _ = p * ((k.choose (i - 1) : ℝ) * p ^ (i - 1) * (1 - p) ^ (k - (i - 1))) + (1 - p) * ((k.choose i : ℝ) * p ^ i * (1 - p) ^ (k - i)) := by
          rw [h_exp_eq]
          have h_pow : p ^ i = p * p ^ (i - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ i)]
          rw [h_pow]
          ring
    · -- i > k, so i ≥ k+1
      have hi_ge : k + 1 ≤ i := Nat.succ_le_of_lt (Nat.not_le.mp hi_le_k)
      by_cases hi_eq : i = k + 1
      · subst i
        simp [Nat.choose_self, Nat.choose_succ_self]
        ring
      · -- i > k+1
        have h_gt : k + 1 < i := Nat.lt_of_le_of_ne hi_ge (Ne.symm hi_eq)
        have hz1 : (k.choose (i - 1) : ℝ) = 0 := by
          rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
        have hz2 : (k.choose i : ℝ) = 0 := by
          rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
        simp [hz1, hz2]
  have hBinCdfSucc : binCdf (k + 1) p (v + 1) = p * binCdf k p v + (1 - p) * binCdf k p (v + 1) := by
    induction' v with v ih
    · -- v = 0: binCdf (k+1) p 1 = p * binCdf k p 0 + (1-p) * binCdf k p 1
      dsimp [binCdf]
      simp [Finset.sum_range_succ]
      have h0' : binPmf (k + 1) p 0 = (1 - p) * binPmf k p 0 := by
        simpa [binCdf] using h0
      rw [h0', hTerm 1 (by omega)]
      ring
    · -- v → v+1
      have h_rec1 : binCdf (k + 1) p (v + 2) = binCdf (k + 1) p (v + 1) + binPmf (k + 1) p (v + 2) := by
        dsimp [binCdf]
        rw [Finset.sum_range_succ]
      have h_rec2 : binCdf k p (v + 2) = binCdf k p (v + 1) + binPmf k p (v + 2) := by
        dsimp [binCdf]
        rw [Finset.sum_range_succ]
      have h_rec3 : binCdf k p (v + 1) = binCdf k p v + binPmf k p (v + 1) := by
        dsimp [binCdf]
        rw [Finset.sum_range_succ]
      rw [h_rec1, h_rec2, ih]
      have h_sub : (v + 2 : ℕ) - 1 = v + 1 := by omega
      have h_term := hTerm (v + 2) (by omega)
      rw [h_sub] at h_term
      rw [h_term]
      calc
        (p * binCdf k p v + (1 - p) * binCdf k p (v + 1)) + (p * binPmf k p (v + 1) + (1 - p) * binPmf k p (v + 2))
            = (p * binCdf k p v + p * binPmf k p (v + 1)) + ((1 - p) * binCdf k p (v + 1) + (1 - p) * binPmf k p (v + 2)) := by ring
        _ = p * (binCdf k p v + binPmf k p (v + 1)) + (1 - p) * (binCdf k p (v + 1) + binPmf k p (v + 2)) := by ring
        _ = p * binCdf k p (v + 1) + (1 - p) * (binCdf k p (v + 1) + binPmf k p (v + 2)) := by rw [← h_rec3]
  exact And.intro hBinCdfSucc h0

/-- One step of the coin domination: `G(k + 1) ≥ G(k) + ξ` with `ξ` a coin of probability `1/3`
independent of `G(k)`. -/
theorem coin_cdf_step (μ : Measure ((ℕ → ℕ∞) × (ℕ → Bool)))
    [IsProbabilityMeasure μ] (k v : ℕ) (hξ : μ {z | z.2 k = true} = 3⁻¹)
    (hind : IndepFun (fun z => z.2 k) (fun z => z.1 k) μ)
    (hae : ∀ᵐ z ∂μ, z.1 k + (if z.2 k then 1 else 0) ≤ z.1 (k + 1)) :
    (μ {z | z.1 (k + 1) ≤ ((v + 1 : ℕ) : ℕ∞)}).toReal ≤
        1 / 3 * (μ {z | z.1 k ≤ (v : ℕ∞)}).toReal +
          2 / 3 * (μ {z | z.1 k ≤ ((v + 1 : ℕ) : ℕ∞)}).toReal ∧
      (μ {z | z.1 (k + 1) ≤ 0}).toReal ≤ 2 / 3 * (μ {z | z.1 k ≤ 0}).toReal := by
  -- define sets (with explicit type annotations)
  set A : Set ((ℕ → ℕ∞) × (ℕ → Bool)) := {z | z.1 (k + 1) ≤ ((v + 1 : ℕ) : ℕ∞)} with hA
  set B : Set ((ℕ → ℕ∞) × (ℕ → Bool)) := {z | z.1 k ≤ (v : ℕ∞)} with hB
  set C : Set ((ℕ → ℕ∞) × (ℕ → Bool)) := {z | z.1 k ≤ ((v + 1 : ℕ) : ℕ∞)} with hC
  set ξ_true : Set ((ℕ → ℕ∞) × (ℕ → Bool)) := {z | z.2 k = true} with hξ_true
  set ξ_false : Set ((ℕ → ℕ∞) × (ℕ → Bool)) := {z | z.2 k = false} with hξ_false
  set D : Set ((ℕ → ℕ∞) × (ℕ → Bool)) := {z | z.1 (k + 1) ≤ 0} with hD
  set E : Set ((ℕ → ℕ∞) × (ℕ → Bool)) := {z | z.1 k ≤ 0} with hE
  -- measurability helpers
  have h_meas_singleton_true : MeasurableSet ({true} : Set Bool) :=
    MeasurableSet.singleton true
  have h_meas_singleton_false : MeasurableSet ({false} : Set Bool) :=
    MeasurableSet.singleton false
  -- For ℕ∞, {x | x ≤ v} is a finite set, hence measurable
  have h_meas_set_v : MeasurableSet ({x : ℕ∞ | x ≤ (v : ℕ∞)} : Set ℕ∞) := by
    have h_fin : Set.Finite ({x : ℕ∞ | x ≤ (v : ℕ∞)} : Set ℕ∞) := by
      let S : Finset ℕ∞ := (Finset.range (v+1)).image (fun i : ℕ => (i : ℕ∞))
      have hS : Set.Finite (S : Set ℕ∞) := S.finite_toSet
      refine Set.Finite.subset hS ?_
      intro x hx
      rcases ENat.le_natCast_iff.mp hx with ⟨n, rfl, hn⟩
      apply Finset.mem_coe.mpr
      apply Finset.mem_image.mpr
      exact ⟨n, Finset.mem_range.mpr (by omega), rfl⟩
    exact h_fin.measurableSet
  have h_meas_set_v1 : MeasurableSet ({x : ℕ∞ | x ≤ ((v + 1 : ℕ) : ℕ∞)} : Set ℕ∞) := by
    have h_fin : Set.Finite ({x : ℕ∞ | x ≤ ((v + 1 : ℕ) : ℕ∞)} : Set ℕ∞) := by
      let S : Finset ℕ∞ := (Finset.range (v+2)).image (fun i : ℕ => (i : ℕ∞))
      have hS : Set.Finite (S : Set ℕ∞) := S.finite_toSet
      refine Set.Finite.subset hS ?_
      intro x hx
      rcases ENat.le_natCast_iff.mp hx with ⟨n, rfl, hn⟩
      apply Finset.mem_coe.mpr
      apply Finset.mem_image.mpr
      exact ⟨n, Finset.mem_range.mpr (by omega), rfl⟩
    exact h_fin.measurableSet
  have h_meas_set_0 : MeasurableSet ({x : ℕ∞ | x ≤ (0 : ℕ∞)} : Set ℕ∞) := by
    have h_fin : Set.Finite ({x : ℕ∞ | x ≤ (0 : ℕ∞)} : Set ℕ∞) := by
      let S : Finset ℕ∞ := {(0 : ℕ∞)}
      have hS : Set.Finite (S : Set ℕ∞) := S.finite_toSet
      refine Set.Finite.subset hS ?_
      intro x hx
      rcases ENat.le_natCast_iff.mp hx with ⟨n, rfl, hn⟩
      have : n = 0 := by omega
      subst this
      dsimp [S]
      simp
    exact h_fin.measurableSet
  -- measurability of the sets in the product space
  have h_meas_fun2 : Measurable (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 k) :=
    (measurable_pi_apply k).comp measurable_snd
  have h_meas_fun1 : Measurable (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 k) :=
    (measurable_pi_apply k).comp measurable_fst
  have h_meas_fun1' : Measurable (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 (k + 1)) :=
    (measurable_pi_apply (k + 1)).comp measurable_fst
  have h_meas_ξ_true : MeasurableSet ξ_true := by
    have : ξ_true = (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 k) ⁻¹' {true} := by
      ext z; simp [ξ_true]
    rw [this]
    exact h_meas_fun2 h_meas_singleton_true
  have h_meas_ξ_false : MeasurableSet ξ_false := by
    have : ξ_false = (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 k) ⁻¹' {false} := by
      ext z; simp [ξ_false]
    rw [this]
    exact h_meas_fun2 h_meas_singleton_false
  have h_meas_B : MeasurableSet B := by
    have : B = (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 k) ⁻¹' {x : ℕ∞ | x ≤ (v : ℕ∞)} := by
      ext z; simp [B]
    rw [this]
    exact h_meas_fun1 h_meas_set_v
  have h_meas_C : MeasurableSet C := by
    have : C = (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 k) ⁻¹' {x : ℕ∞ | x ≤ ((v + 1 : ℕ) : ℕ∞)} := by
      ext z; simp [C]
    rw [this]
    exact h_meas_fun1 h_meas_set_v1
  have h_meas_E : MeasurableSet E := by
    have : E = (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 k) ⁻¹' {x : ℕ∞ | x ≤ (0 : ℕ∞)} := by
      ext z; simp [E]
    rw [this]
    exact h_meas_fun1 h_meas_set_0
  have h_meas_A : MeasurableSet A := by
    have : A = (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 (k + 1)) ⁻¹' {x : ℕ∞ | x ≤ ((v + 1 : ℕ) : ℕ∞)} := by
      ext z; simp [A]
    rw [this]
    exact h_meas_fun1' h_meas_set_v1
  have h_meas_D : MeasurableSet D := by
    have : D = (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 (k + 1)) ⁻¹' {x : ℕ∞ | x ≤ (0 : ℕ∞)} := by
      ext z; simp [D]
    rw [this]
    exact h_meas_fun1' h_meas_set_0
  -- disjointness of ξ_true and ξ_false
  have h_disjoint : Disjoint ξ_true ξ_false := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext z; simp [ξ_true, ξ_false]
  -- μ ξ_true + μ ξ_false = 1
  have h_ξ_sum : μ ξ_true + μ ξ_false = 1 := by
    calc
      μ ξ_true + μ ξ_false = μ (ξ_true ∪ ξ_false) := by
        rw [measure_union h_disjoint h_meas_ξ_false]
      _ = μ Set.univ := by
        congr
        ext z; simp [ξ_true, ξ_false]
      _ = 1 := by simp
  -- helper: a measure ≤ 1 is ≠ ⊤
  have h_fin_of_le_one {s : Set ((ℕ → ℕ∞) × (ℕ → Bool))} (h : μ s ≤ 1) : μ s ≠ ⊤ := by
    intro htop
    have : (1 : ENNReal) < ⊤ := by simp
    have htop_le_one : (⊤ : ENNReal) ≤ 1 := htop ▸ h
    exact not_lt.mpr htop_le_one this
  -- μ ξ_true ≠ ⊤ and μ ξ_false ≠ ⊤
  have h_fin_ξ_true : μ ξ_true ≠ ⊤ := by
    apply h_fin_of_le_one
    calc
      μ ξ_true ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by simp
  have h_fin_ξ_false : μ ξ_false ≠ ⊤ := by
    apply h_fin_of_le_one
    calc
      μ ξ_false ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by simp
  -- (μ ξ_false).toReal = 2/3
  have h_ξ_false_toReal : (μ ξ_false).toReal = 2/3 := by
    have h_toReal_sum : (μ ξ_true + μ ξ_false).toReal = (μ ξ_true).toReal + (μ ξ_false).toReal :=
      ENNReal.toReal_add h_fin_ξ_true h_fin_ξ_false
    have h_one_toReal : (1 : ENNReal).toReal = (1 : ℝ) := by simp
    rw [h_ξ_sum] at h_toReal_sum
    rw [h_one_toReal] at h_toReal_sum
    have h_ξ_true_toReal : (μ ξ_true).toReal = 1/3 := by
      rw [hξ]
      norm_num [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [h_ξ_true_toReal] at h_toReal_sum
    linarith
  -- (μ ξ_true).toReal = 1/3
  have h_ξ_true_toReal : (μ ξ_true).toReal = 1/3 := by
    rw [hξ]
    norm_num [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  -- Key almost-everywhere inclusion for the first claim
  have h_inclusion_first : A ≤ᵐ[μ] (ξ_true ∩ B) ∪ (ξ_false ∩ C) := by
    filter_upwards [hae] with z hz
    intro hzA
    by_cases hξz : z.2 k = true
    · apply Set.mem_union_left
      have hz' : z.1 k + 1 ≤ z.1 (k + 1) := by simpa [hξz] using hz
      have h_total : z.1 k + 1 ≤ ((v + 1 : ℕ) : ℕ∞) := le_trans hz' hzA
      have h_fin : z.1 k ≠ ⊤ := by
        intro htop
        have htop_add : z.1 k + 1 = ⊤ := by simp [htop]
        have h_vtop : ((v + 1 : ℕ) : ℕ∞) ≠ ⊤ := by simp
        apply h_vtop
        exact top_unique (htop_add ▸ h_total)
      have h_lt : z.1 k < ((v + 1 : ℕ) : ℕ∞) :=
        (ENat.add_one_le_iff h_fin).mp h_total
      have hzB : z.1 k ≤ (v : ℕ∞) :=
        (ENat.lt_natCast_add_one_iff (n := v)).mp h_lt
      exact ⟨hξz, hzB⟩
    · apply Set.mem_union_right
      have hξz' : z.2 k = false := Bool.eq_false_iff.mpr hξz
      have hz' : z.1 k ≤ z.1 (k + 1) := by simpa [hξz'] using hz
      exact ⟨hξz', le_trans hz' hzA⟩
  -- Key almost-everywhere inclusion for the second claim
  have h_inclusion_second : D ≤ᵐ[μ] ξ_false ∩ E := by
    filter_upwards [hae] with z hz
    intro hzD
    by_cases hξz : z.2 k = true
    · -- then z.1 k + 1 ≤ z.1 (k+1) ≤ 0, impossible
      have hz' : z.1 k + 1 ≤ z.1 (k + 1) := by simpa [hξz] using hz
      have h_contra : z.1 k + 1 ≤ (0 : ℕ∞) := le_trans hz' hzD
      have h_one_pos : (0 : ℕ∞) < 1 := by decide
      have h_lt : z.1 k + 1 < 1 := lt_of_le_of_lt h_contra h_one_pos
      have h_ge : (1 : ℕ∞) ≤ z.1 k + 1 := by
        simp
      exact absurd h_lt (not_lt.mpr h_ge)
    · -- z.2 k = false
      have hξz' : z.2 k = false := Bool.eq_false_iff.mpr hξz
      refine ⟨hξz', ?_⟩
      have hz' : z.1 k ≤ z.1 (k + 1) := by simpa [hξz'] using hz
      exact le_trans hz' hzD
  -- assemble the first claim
  have h_first : (μ A).toReal ≤ 1 / 3 * (μ B).toReal + 2 / 3 * (μ C).toReal := by
    have h_measure_le : μ A ≤ μ ((ξ_true ∩ B) ∪ (ξ_false ∩ C)) :=
      measure_mono_ae h_inclusion_first
    have h_union_le : μ ((ξ_true ∩ B) ∪ (ξ_false ∩ C)) ≤ μ (ξ_true ∩ B) + μ (ξ_false ∩ C) :=
      measure_union_le _ _
    have h_total_le : μ A ≤ μ (ξ_true ∩ B) + μ (ξ_false ∩ C) :=
      le_trans h_measure_le h_union_le
    have h_fin1 : μ (ξ_true ∩ B) ≠ ⊤ := by
      apply h_fin_of_le_one
      calc
        μ (ξ_true ∩ B) ≤ μ ξ_true := measure_mono (fun x hx => hx.1)
        _ ≤ 1 := by
          calc
            μ ξ_true ≤ μ Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := by simp
    have h_fin2 : μ (ξ_false ∩ C) ≠ ⊤ := by
      apply h_fin_of_le_one
      calc
        μ (ξ_false ∩ C) ≤ μ ξ_false := measure_mono (fun x hx => hx.1)
        _ ≤ 1 := by
          calc
            μ ξ_false ≤ μ Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := by simp
    have h_fin_sum : μ (ξ_true ∩ B) + μ (ξ_false ∩ C) ≠ ⊤ := by
      intro htop
      have htop' := ENNReal.add_eq_top.mp htop
      rcases htop' with (h | h)
      · exact h_fin1 h
      · exact h_fin2 h
    have h_toReal_le : (μ A).toReal ≤ (μ (ξ_true ∩ B) + μ (ξ_false ∩ C)).toReal :=
      ENNReal.toReal_mono h_fin_sum h_total_le
    have h_toReal_add : (μ (ξ_true ∩ B) + μ (ξ_false ∩ C)).toReal =
        (μ (ξ_true ∩ B)).toReal + (μ (ξ_false ∩ C)).toReal :=
      ENNReal.toReal_add h_fin1 h_fin2
    rw [h_toReal_add] at h_toReal_le
    -- independence
    have h_indep_B : μ (ξ_true ∩ B) = μ ξ_true * μ B := by
      have h := hind.measure_inter_preimage_eq_mul ({true} : Set Bool)
        ({x : ℕ∞ | x ≤ (v : ℕ∞)} : Set ℕ∞) h_meas_singleton_true h_meas_set_v
      have h_preimage_f : (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 k) ⁻¹' ({true} : Set Bool) = ξ_true := by
        ext z; simp [ξ_true]
      have h_preimage_g : (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 k) ⁻¹' ({x : ℕ∞ | x ≤ (v : ℕ∞)} : Set ℕ∞) = B := by
        ext z; simp [B]
      rw [h_preimage_f, h_preimage_g] at h
      exact h
    have h_indep_C : μ (ξ_false ∩ C) = μ ξ_false * μ C := by
      have h := hind.measure_inter_preimage_eq_mul ({false} : Set Bool)
        ({x : ℕ∞ | x ≤ ((v + 1 : ℕ) : ℕ∞)} : Set ℕ∞) h_meas_singleton_false h_meas_set_v1
      have h_preimage_f : (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 k) ⁻¹' ({false} : Set Bool) = ξ_false := by
        ext z; simp [ξ_false]
      have h_preimage_g : (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 k) ⁻¹' ({x : ℕ∞ | x ≤ ((v + 1 : ℕ) : ℕ∞)} : Set ℕ∞) = C := by
        ext z; simp [C]
      rw [h_preimage_f, h_preimage_g] at h
      exact h
    rw [h_indep_B, h_indep_C] at h_toReal_le
    have h_toReal_mul1 : (μ ξ_true * μ B).toReal = (μ ξ_true).toReal * (μ B).toReal :=
      ENNReal.toReal_mul
    have h_toReal_mul2 : (μ ξ_false * μ C).toReal = (μ ξ_false).toReal * (μ C).toReal :=
      ENNReal.toReal_mul
    rw [h_toReal_mul1, h_toReal_mul2] at h_toReal_le
    rw [h_ξ_true_toReal, h_ξ_false_toReal] at h_toReal_le
    exact h_toReal_le
  -- assemble the second claim
  have h_second : (μ D).toReal ≤ 2 / 3 * (μ E).toReal := by
    have h_measure_le : μ D ≤ μ (ξ_false ∩ E) :=
      measure_mono_ae h_inclusion_second
    have h_fin : μ (ξ_false ∩ E) ≠ ⊤ := by
      apply h_fin_of_le_one
      calc
        μ (ξ_false ∩ E) ≤ μ ξ_false := measure_mono (fun x hx => hx.1)
        _ ≤ 1 := by
          calc
            μ ξ_false ≤ μ Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := by simp
    have h_toReal_le : (μ D).toReal ≤ (μ (ξ_false ∩ E)).toReal :=
      ENNReal.toReal_mono h_fin h_measure_le
    -- independence
    have h_indep_E : μ (ξ_false ∩ E) = μ ξ_false * μ E := by
      have h := hind.measure_inter_preimage_eq_mul ({false} : Set Bool)
        ({x : ℕ∞ | x ≤ (0 : ℕ∞)} : Set ℕ∞) h_meas_singleton_false h_meas_set_0
      have h_preimage_f : (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.2 k) ⁻¹' ({false} : Set Bool) = ξ_false := by
        ext z; simp [ξ_false]
      have h_preimage_g : (fun z : (ℕ → ℕ∞) × (ℕ → Bool) => z.1 k) ⁻¹' ({x : ℕ∞ | x ≤ (0 : ℕ∞)} : Set ℕ∞) = E := by
        ext z; simp [E]
      rw [h_preimage_f, h_preimage_g] at h
      exact h
    rw [h_indep_E] at h_toReal_le
    have h_toReal_mul : (μ ξ_false * μ E).toReal = (μ ξ_false).toReal * (μ E).toReal :=
      ENNReal.toReal_mul
    rw [h_toReal_mul] at h_toReal_le
    rw [h_ξ_false_toReal] at h_toReal_le
    exact h_toReal_le
  exact And.intro h_first h_second

/-- **Lemma 10.3 of the paper**: `G_m(k)` dominates `Bin(k, 1/3)`, from the coins. -/
theorem cdfG_le_binCdf_of (hmeas : measurable_plantedPair)
    (hcoin : coin_coupling) : cdfG_le_binCdf := by
  intro m k
  obtain ⟨μ, hμ, hfst, hξ, hindep, hae⟩ := hcoin m
  have hcdf : ∀ k g : ℕ, cdfG m k g = (μ {z | z.1 k ≤ (g : ℕ∞)}).toReal := by
    intro k g
    have hk : Measurable fun G : ℕ → ℕ∞ => G k := measurable_pi_apply k
    have hs : MeasurableSet {G : ℕ → ℕ∞ | G k ≤ (g : ℕ∞)} :=
      hk (MeasurableSet.of_discrete (s := {x : ℕ∞ | x ≤ (g : ℕ∞)}))
    rw [cdfG_eq hmeas, ← hfst, Measure.map_apply measurable_fst hs]
    rfl
  have hind : ∀ k, IndepFun (fun z => z.2 k) (fun z => z.1 k) μ := fun k =>
    (hindep k).comp measurable_id
      ((measurable_pi_apply (⟨k, by omega⟩ : Fin (k + 1))).comp measurable_fst)
  induction k with
  | zero =>
    intro v
    have h1 : binCdf 0 (1 / 3) v = 1 := by
      unfold binCdf binPmf
      rw [Finset.sum_eq_single 0 (fun i _ hi => by
        simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hi)]) (by simp)]
      simp
    rw [h1, hcdf]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  | succ k ih =>
    intro v
    cases v with
    | zero =>
      obtain ⟨-, h0⟩ := coin_cdf_step μ k 0 (hξ k) (hind k) (hae.mono fun z hz => hz.2 k)
      have h1 := ih 0
      rw [hcdf] at h1
      rw [(binCdf_succ k 0 (1 / 3)).2, hcdf]
      simp only [Nat.cast_zero] at h0 h1 ⊢
      linarith
    | succ v =>
      obtain ⟨h0, -⟩ := coin_cdf_step μ k v (hξ k) (hind k) (hae.mono fun z hz => hz.2 k)
      have h1 := ih v
      have h2 := ih (v + 1)
      rw [hcdf] at h1 h2
      rw [(binCdf_succ k v (1 / 3)).1, hcdf]
      linarith

end FrogModel.D3.Iface
