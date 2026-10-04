module

public import FrogModel.D3.LaneB.NegBin
public import FrogModel.D3.LaneB.Lemma16
public import FrogModel.D3.LaneB.Lemma8
public import FrogModel.D3.LaneB.Succ
public import FrogModel.D3.LaneB.Good

@[expose] public section

/-!
# Lemmas 11.2 and 11.3 of the paper

The probability bounds of Lemma 11.2 (A) and (B) on a closure with i.i.d. nondecreasing children: the
event is contained almost surely in a union (`lemma16A_incl`, `lemma16B_incl`) bounded part by part
(`toReal_le_union_bound`): few directions up (a binomial cdf), one child small at `E` with many
entries into it (`negbin_bound` times `P(G(E) ≤ n0 - q - 1)`), or given counts at `q + s` with
`S_e = s` (the multinomial weight times `P(S_e = s)`, `closMeasure_counts_Se`). Then Lemma 11.3 (1),
and the statements `lemma16A`, `lemma16B`, `lemma16C`, `lemma16AC`, `lemma16BC` of the interface from
`measurable_plantedPair` and `curveLaw_succ` (Lemma 10.1).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- Union bound in real numbers: an event contained almost surely in `P1`, a union of `P2 c` over
`c ∈ C` and a union of `P3 i` over `i ∈ I`. -/
theorem toReal_le_union_bound {Ω ι κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S P1 : Set Ω) (C : Finset ι) (P2 : ι → Set Ω) (I : Finset κ)
    (P3 : κ → Set Ω) (b1 b2 : ℝ) (w : κ → ℝ)
    (hS : ∀ᵐ x ∂μ, x ∈ S → x ∈ P1 ∨ (∃ c ∈ C, x ∈ P2 c) ∨ ∃ i ∈ I, x ∈ P3 i)
    (h1 : (μ P1).toReal ≤ b1) (h2 : ∀ c ∈ C, (μ (P2 c)).toReal ≤ b2)
    (h3 : ∀ i ∈ I, (μ (P3 i)).toReal ≤ w i) :
    (μ S).toReal ≤ ∑ i ∈ I, w i + C.card * b2 + b1 := by
  have hsub : S ≤ᵐ[μ] (P1 ∪ (⋃ c ∈ C, P2 c) ∪ ⋃ i ∈ I, P3 i : Set Ω) := by
    filter_upwards [hS] with x hx hxS
    rcases hx hxS with h | ⟨c, hc, h⟩ | ⟨i, hi, h⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Set.mem_biUnion hc h))
    · exact Or.inr (Set.mem_biUnion hi h)
  have hle : μ S ≤ μ P1 + ∑ c ∈ C, μ (P2 c) + ∑ i ∈ I, μ (P3 i) :=
    (measure_mono_ae hsub).trans ((measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _)))
      (measure_biUnion_finset_le _ _)))
  have hfin : ∀ U : Set Ω, μ U ≠ ∞ := fun U => measure_ne_top μ U
  have hreal := ENNReal.toReal_mono (by simp [hfin]) hle
  rw [ENNReal.toReal_add (by simp [hfin]) (by simp [hfin]), ENNReal.toReal_add (hfin _)
    (by simp [hfin]), ENNReal.toReal_sum (fun _ _ => hfin _),
    ENNReal.toReal_sum (fun _ _ => hfin _)] at hreal
  have hC : ∑ c ∈ C, (μ (P2 c)).toReal ≤ C.card * b2 := by
    simpa using Finset.sum_le_sum h2
  have hI : ∑ i ∈ I, (μ (P3 i)).toReal ≤ ∑ i ∈ I, w i := Finset.sum_le_sum h3
  linarith

/-- The closure measure of an event of one child and of the directions. -/
theorem closMeasure_child_dir (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (c : Fin 3)
    (B : Set (ℕ → ℕ∞)) (hB : MeasurableSet B) (A : Set (ℕ → Fin 4)) :
    closMeasure Q {x | x.1 c ∈ B ∧ x.2 ∈ A} = Q B * dirMeasure A := by
  unfold closMeasure
  rw [show {x : ClosSample | x.1 c ∈ B ∧ x.2 ∈ A} = ((fun G : Fin 3 → ℕ → ℕ∞ => G c) ⁻¹' B) ×ˢ A by
    ext x; simp, Measure.prod_prod, (measurePreserving_eval (fun _ : Fin 3 => Q) c).measure_preimage
      hB.nullMeasurableSet]

theorem dirMeasure_dirCount_le (n v : ℕ) (a : Fin 4) :
    (dirMeasure {D | dirCount D a n ≤ v}).toReal = binCdf n (1 / 4) v := by
  rw [show {D : ℕ → Fin 4 | dirCount D a n ≤ v} = {D | dirCount D a n < v + 1} by
    ext D; simp, dirMeasure_dirCount_lt]
  rfl

theorem measurableSet_le_at (E t : ℕ) : MeasurableSet {G : ℕ → ℕ∞ | G E ≤ (t : ℕ∞)} :=
  show MeasurableSet ((fun f : ℕ → ℕ∞ => f E) ⁻¹' {y : ℕ∞ | y ≤ t}) from
    (measurable_pi_apply E) (MeasurableSet.of_discrete)

/-- The part of the union bound of Lemma 11.2 of the paper with one child small at `E`. -/
theorem closMeasure_child_negbin (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (c : Fin 3)
    (b : Fin 4) (hb : c.succ ≠ b) (E v t : ℕ) :
    (closMeasure Q {x | x.1 c ∈ {G : ℕ → ℕ∞ | G E ≤ (t : ℕ∞)} ∧
      x.2 ∈ {D | ∃ n, E ≤ dirCount D c.succ n ∧ dirCount D b n ≤ v}}).toReal ≤
      binGe (E + v) (1 / 2) E * (Q {G | G E ≤ (t : ℕ∞)}).toReal := by
  rw [closMeasure_child_dir Q c _ (measurableSet_le_at E t), ENNReal.toReal_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (negbin_bound c.succ b hb E v) ENNReal.toReal_nonneg

/-- The part of the union bound of Lemma 11.2 of the paper with given counts at `q + s` and
`S_e = s`. -/
theorem closMeasure_counts_part (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q : ℕ)
    (e : Fin 3 → ℕ) (s : ℕ) (P : Prop) [Decidable P] (W : ℝ)
    (hW : P → W = mult4 (q + s) (q + s - (e 0 + e 1 + e 2)) (e 0) (e 1) (e 2))
    (hW0 : ¬ P → W = 0) :
    (closMeasure Q {x | P ∧ e 0 + e 1 + e 2 ≤ q + s ∧
      dirCount x.2 0 (q + s) = q + s - (e 0 + e 1 + e 2) ∧
      (∀ c : Fin 3, dirCount x.2 c.succ (q + s) = e c) ∧
      ∑ c : Fin 3, x.1 c (e c) = (s : ℕ∞)}).toReal ≤ W * probSeQ Q e s := by
  by_cases hP : P
  · by_cases hle : e 0 + e 1 + e 2 ≤ q + s
    · let k : Fin 4 → ℕ := ![q + s - (e 0 + e 1 + e 2), e 0, e 1, e 2]
      have hk : ∑ a, k a = q + s := by simp [k, Fin.sum_univ_four]; omega
      have hset : {x : ClosSample | P ∧ e 0 + e 1 + e 2 ≤ q + s ∧
          dirCount x.2 0 (q + s) = q + s - (e 0 + e 1 + e 2) ∧
          (∀ c : Fin 3, dirCount x.2 c.succ (q + s) = e c) ∧
          ∑ c : Fin 3, x.1 c (e c) = (s : ℕ∞)} =
          {x | (∀ a, dirCount x.2 a (q + s) = k a) ∧ ∑ c : Fin 3, x.1 c (e c) = (s : ℕ∞)} := by
        ext x
        simp only [Set.mem_ofPred_eq, Fin.forall_fin_succ, k]
        simp [hP, hle, and_assoc]
      rw [hset, closMeasure_counts_Se Q (q + s) k hk e s, hW hP]
      simp [k]
    · simp [hle]
      exact mul_nonneg (by rw [hW hP]; unfold mult4; positivity) ENNReal.toReal_nonneg
  · simp [hP, hW0 hP]

theorem lemma16A_prob (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (hmono : ∀ᵐ x ∂closMeasure Q, ∀ c, Monotone (x.1 c)) (q v n0 E : ℕ) :
    (closMeasure Q {x | closX q x.1 x.2 ≤ v}).toReal ≤
      (∑ e ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range E), ∑ s ∈ Finset.range n0,
          WA q v n0 e s * probSeQ Q e s) +
        3 * binGe (E + v) (1 / 2) E * (Q {G | G E ≤ ((n0 - q - 1 : ℕ) : ℕ∞)}).toReal +
          binCdf n0 (1 / 4) v := by
  have h := toReal_le_union_bound (closMeasure Q) {x | closX q x.1 x.2 ≤ v}
    {x | x.2 ∈ {D | dirCount D 0 n0 ≤ v}} (Finset.univ : Finset (Fin 3))
    (fun c => {x | x.1 c ∈ {G : ℕ → ℕ∞ | G E ≤ ((n0 - q - 1 : ℕ) : ℕ∞)} ∧
      x.2 ∈ {D | ∃ n, E ≤ dirCount D c.succ n ∧ dirCount D 0 n ≤ v}})
    (Fintype.piFinset (fun _ : Fin 3 => Finset.range E) ×ˢ Finset.range n0)
    (fun i => {x | (i.1 0 + i.1 1 + i.1 2 ≤ q + i.2 ∧ q + i.2 - (i.1 0 + i.1 1 + i.1 2) ≤ v ∧
      q + i.2 < n0) ∧ i.1 0 + i.1 1 + i.1 2 ≤ q + i.2 ∧
      dirCount x.2 0 (q + i.2) = q + i.2 - (i.1 0 + i.1 1 + i.1 2) ∧
      (∀ c : Fin 3, dirCount x.2 c.succ (q + i.2) = i.1 c) ∧
      ∑ c : Fin 3, x.1 c (i.1 c) = (i.2 : ℕ∞)})
    (binCdf n0 (1 / 4) v) (binGe (E + v) (1 / 2) E * (Q {G | G E ≤ ((n0 - q - 1 : ℕ) : ℕ∞)}).toReal)
    (fun i => WA q v n0 i.1 i.2 * probSeQ Q i.1 i.2) ?_ ?_ ?_ ?_
  · rw [Finset.sum_product] at h
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at h
    linarith
  · filter_upwards [hmono] with x hx hxS
    rcases lemma16A_incl q v n0 E x.1 x.2 hx hxS with h | ⟨c, h1, h2⟩ |
      ⟨e, he, s, hs, hle, hv, h0, hc, hsum⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨c, Finset.mem_univ _, h2, h1⟩)
    · refine Or.inr (Or.inr ⟨(e, s), Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun c =>
        Finset.mem_range.2 (he c), Finset.mem_range.2 (by omega)⟩, ⟨hle, hv, hs⟩, hle, h0, hc, hsum⟩)
  · rw [closMeasure_dir, dirMeasure_dirCount_le]
  · intro c _
    exact closMeasure_child_negbin Q c 0 (Fin.succ_ne_zero c) E v _
  · rintro ⟨e, s⟩ _
    exact closMeasure_counts_part Q q e s _ _ (fun h => by simp [WA, h])
      (fun h => by simp only [WA, ite_eq_right_iff]; exact fun h' => absurd h' h)

theorem WA_nonneg (q v n0 : ℕ) (e : Fin 3 → ℕ) (s : ℕ) : 0 ≤ WA q v n0 e s := by
  unfold WA mult4
  split_ifs <;> positivity

theorem WB_nonneg (q K : ℕ) (e : Fin 3 → ℕ) (s : ℕ) : 0 ≤ WB q K e s := by
  unfold WB mult4
  split_ifs <;> positivity

theorem lemma16B_prob (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (hmono : ∀ᵐ x ∂closMeasure Q, ∀ c, Monotone (x.1 c)) (q J K E : ℕ) (hJE : J ≤ E) :
    (closMeasure Q {x | closE q x.1 x.2 0 < J}).toReal ≤
      (∑ e ∈ Fintype.piFinset (fun c : Fin 3 => if c = 0 then Finset.range J else Finset.range E),
          ∑ s ∈ Finset.range K, WB q K e s * probSeQ Q e s) +
        2 * binGe (E + J - 1) (1 / 2) E * (Q {G | G E ≤ ((K - q - 1 : ℕ) : ℕ∞)}).toReal +
          binLt K (1 / 4) J := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · have hempty : {x : ClosSample | closE q x.1 x.2 0 < ((0 : ℕ) : ℕ∞)} = ∅ := by ext x; simp
    rw [hempty, measure_empty, ENNReal.toReal_zero]
    have h1 : 0 ≤ ∑ e ∈ Fintype.piFinset (fun c : Fin 3 => if c = 0 then Finset.range 0 else
        Finset.range E), ∑ s ∈ Finset.range K, WB q K e s * probSeQ Q e s :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg (WB_nonneg _ _ _ _) ENNReal.toReal_nonneg
    have h2 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (binGe_half_nonneg (E + 0 - 1) E))
      (ENNReal.toReal_nonneg (a := Q {G | G E ≤ ((K - q - 1 : ℕ) : ℕ∞)}))
    have h3 : binLt K (1 / 4) 0 = 0 := by simp [binLt]
    linarith
  have h := toReal_le_union_bound (closMeasure Q) {x | closE q x.1 x.2 0 < J}
    {x | x.2 ∈ {D | dirCount D 1 K < J}} (Finset.univ.filter fun c : Fin 3 => c ≠ 0)
    (fun c => {x | x.1 c ∈ {G : ℕ → ℕ∞ | G E ≤ ((K - q - 1 : ℕ) : ℕ∞)} ∧
      x.2 ∈ {D | ∃ n, E ≤ dirCount D c.succ n ∧ dirCount D 1 n ≤ J - 1}})
    (Fintype.piFinset (fun c : Fin 3 => if c = 0 then Finset.range J else Finset.range E) ×ˢ
      Finset.range K)
    (fun i => {x | (i.1 0 + i.1 1 + i.1 2 ≤ q + i.2 ∧ q + i.2 < K) ∧
      i.1 0 + i.1 1 + i.1 2 ≤ q + i.2 ∧
      dirCount x.2 0 (q + i.2) = q + i.2 - (i.1 0 + i.1 1 + i.1 2) ∧
      (∀ c : Fin 3, dirCount x.2 c.succ (q + i.2) = i.1 c) ∧
      ∑ c : Fin 3, x.1 c (i.1 c) = (i.2 : ℕ∞)})
    (binLt K (1 / 4) J) (binGe (E + (J - 1)) (1 / 2) E * (Q {G | G E ≤ ((K - q - 1 : ℕ) : ℕ∞)}).toReal)
    (fun i => WB q K i.1 i.2 * probSeQ Q i.1 i.2) ?_ ?_ ?_ ?_
  · rw [Finset.sum_product] at h
    have hcard : (Finset.univ.filter fun c : Fin 3 => c ≠ 0).card = 2 := by decide
    rw [hcard] at h
    have hEJ : E + J - 1 = E + (J - 1) := by omega
    rw [hEJ]
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at h
    linarith
  · filter_upwards [hmono] with x hx hxS
    rcases lemma16B_incl q J K E hJE x.1 x.2 hx hxS with h | ⟨c, hc0, h1, h2⟩ |
      ⟨e, he0, he1, he2, s, hs, hle, h0, hc, hsum⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨c, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc0⟩, h2, h1⟩)
    · refine Or.inr (Or.inr ⟨(e, s), Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun c => ?_,
        Finset.mem_range.2 (by omega)⟩, ⟨hle, hs⟩, hle, h0, hc, hsum⟩)
      fin_cases c
      · simpa using he0
      · simpa using he1
      · simpa using he2
  · rw [closMeasure_dir, dirMeasure_dirCount_lt]
  · intro c hc
    have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
    refine closMeasure_child_negbin Q c 1 ?_ E (J - 1) _
    intro h
    exact hc0 (Fin.succ_injective _ (h.trans Fin.succ_zero_eq_one.symm))
  · rintro ⟨e, s⟩ _
    exact closMeasure_counts_part Q q e s _ _ (fun h => by simp [WB, h])
      (fun h => by simp only [WB, ite_eq_right_iff]; exact fun h' => absurd h' h)


theorem lemma16C_of (hmeas : measurable_plantedPair) : lemma16C := by
  intro m E GM F hF hmono h01 e he W hW0 S hWS
  set Q := curveLaw m
  set S' := min S (GM + 1) with hS'
  have hS'S : S' ≤ S := min_le_left _ _
  have hp : ∀ c g, 0 ≤ plF F GM (e c) g := fun c g =>
    plF_nonneg F GM (e c) (h01 (e c) (he c) 0 (Nat.zero_le _)).1
      (fun g hg => hmono (e c) (he c) g hg) g
  have hconv0 : ∀ s, 0 ≤ convF F GM e s := by
    intro s
    rw [convF_eq]
    unfold conv3
    exact Finset.sum_nonneg fun g1 _ => Finset.sum_nonneg fun g2 _ =>
      mul_nonneg (mul_nonneg (hp 0 g1) (hp 1 g2)) (hp 2 _)
  -- the left side stops at `GM`
  have hL : ∑ s ∈ Finset.range S, W s * probSe m e s =
      ∑ s ∈ Finset.range S', W s * probSe m e s := by
    rw [← Finset.sum_range_add_sum_Ico _ hS'S]
    rw [Finset.sum_eq_zero (s := Finset.Ico S' S) fun s hs => by
      have : GM < s := by
        have h1 : min S (GM + 1) ≤ s := (Finset.mem_Ico.1 hs).1
        have h2 := (Finset.mem_Ico.1 hs).2
        omega
      rw [hWS s this, zero_mul], add_zero]
  -- cumulative domination below `GM`
  have hcum : ∀ t < S', ∑ s ∈ Finset.range (t + 1), probSe m e s ≤
      ∑ s ∈ Finset.range (t + 1), convF F GM e s := by
    intro t ht
    have htGM : t ≤ GM := by omega
    have e1 : ∀ s, probSe m e s = conv3 (fun g => (Q {G | G (e 0) = (g : ℕ∞)}).toReal)
        (fun g => (Q {G | G (e 1) = (g : ℕ∞)}).toReal)
        (fun g => (Q {G | G (e 2) = (g : ℕ∞)}).toReal) s := fun s => by
      rw [show probSe m e s = probSeQ Q e s from rfl, probSeQ_conv]
      rfl
    rw [Finset.sum_congr rfl fun s _ => e1 s, Finset.sum_congr rfl fun s _ => convF_eq F GM e s]
    refine cum_conv3_mono _ _ _ _ _ _ t (fun g => ⟨ENNReal.toReal_nonneg, ENNReal.toReal_nonneg,
      ENNReal.toReal_nonneg⟩) (fun g => ⟨hp 0 g, hp 1 g, hp 2 g⟩) ?_ ?_ ?_
    all_goals
      intro u hu
      rw [sum_measure_eq, sum_plF F GM _ u (hu.trans htGM), ← cdfG_eq hmeas]
      exact hF _ (he _) u (hu.trans htGM)
  rw [hL]
  calc ∑ s ∈ Finset.range S', W s * probSe m e s
      ≤ ∑ s ∈ Finset.range S', envelope W S' s * convF F GM e s :=
        lemma16C_real W _ _ S' hW0 (fun s => ENNReal.toReal_nonneg) hcum
    _ ≤ ∑ s ∈ Finset.range S', envelope W S s * convF F GM e s := by
        refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right ?_ (hconv0 s)
        unfold envelope
        rw [Finset.fold_max_le]
        refine ⟨(envelope_props W S s).2.2, fun x hx => ?_⟩
        rcases Finset.mem_Icc.1 hx with ⟨h1, h2⟩
        exact (envelope_props W S s).1 x h1 (h2.trans hS'S)
    _ ≤ ∑ s ∈ Finset.range S, envelope W S s * convF F GM e s := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hS'S) fun s _ _ => ?_
        exact mul_nonneg (envelope_props W S s).2.2 (hconv0 s)

theorem ae_closMono (hmeas : measurable_plantedPair) (m : ℕ) :
    ∀ᵐ x ∂closMeasure (curveLaw m), ∀ c, Monotone (x.1 c) :=
  (ae_closGood _ _ (ae_goodC hmeas m)).mono fun _ hx c => (hx c).1

/-- **Lemma 11.2 (A) of the paper** from measurability and the law of the closure (Lemma 10.1). -/
theorem lemma16A_of (hmeas : measurable_plantedPair)
    (hsucc : curveLaw_succ) : lemma16A := by
  intro m j v n0 E hj hE hn0
  rw [cdfG_succ_eq hmeas hsucc m j v hj, cdfG_eq hmeas]
  exact lemma16A_prob (curveLaw m) (ae_closMono hmeas m) (j + 1) v n0 E

/-- **Lemma 11.2 (B) of the paper** from measurability. -/
theorem lemma16B_of (hmeas : measurable_plantedPair) : lemma16B := by
  intro m j J K E hj hJ hJE hK
  rw [cdfG_eq hmeas]
  exact lemma16B_prob (curveLaw m) (ae_closMono hmeas m) (j + 1) J K E hJE

/-- **Lemma 11.3 (2) of the paper** for the bound (A), from Lemma 11.2 (A) and Lemma 11.3 (1). -/
theorem lemma16AC_of (h16A : lemma16A) (h16C : lemma16C) :
    lemma16AC := by
  intro m j v n0 E GM F hj hE hn0 hGM hF hmono h01
  refine (h16A m j v n0 E hj hE hn0).trans ?_
  unfold boundA
  refine add_le_add (add_le_add (Finset.sum_le_sum fun e he => ?_) ?_) le_rfl
  · refine h16C m E GM F hF hmono h01 e (fun c => ?_) _ (WA_nonneg _ _ _ e) n0 fun s hs => ?_
    · have := Fintype.mem_piFinset.1 he c
      exact (Finset.mem_range.1 this).le
    · unfold WA
      rw [ite_eq_right]
      omega
  · exact mul_le_mul_of_nonneg_left (hF E le_rfl _ hGM)
      (mul_nonneg (by norm_num) (binGe_half_nonneg _ _))

/-- **Lemma 11.3 (2) of the paper** for the bound (B), from Lemma 11.2 (B) and Lemma 11.3 (1). -/
theorem lemma16BC_of (h16B : lemma16B) (h16C : lemma16C) :
    lemma16BC := by
  intro m j J K E GM F hj hJ hJE hK hGM hF hmono h01
  refine (h16B m j J K E hj hJ hJE hK).trans ?_
  unfold boundB
  refine add_le_add (add_le_add (Finset.sum_le_sum fun e he => ?_) ?_) le_rfl
  · refine h16C m E GM F hF hmono h01 e (fun c => ?_) _ (WB_nonneg _ _ e) K fun s hs => ?_
    · have := Fintype.mem_piFinset.1 he c
      by_cases hc : c = 0
      · subst hc
        simp only [ite_true, Finset.mem_range] at this
        omega
      · simp only [hc, ite_false, Finset.mem_range] at this
        omega
    · unfold WB
      rw [ite_eq_right]
      omega
  · exact mul_le_mul_of_nonneg_left (hF E le_rfl _ hGM)
      (mul_nonneg (by norm_num) (binGe_half_nonneg _ _))

end FrogModel.D3.Iface
