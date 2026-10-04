module

public import FrogModel.D3.LaneB.Counts
public import FrogModel.D3.LaneB.Tails

@[expose] public section

/-!
# The negative binomial bound of Lemma 11.2 of the paper

For two directions `a ≠ b`, the probability that at some time at least `E` directions `a` and at
most `v` directions `b` have occurred is at most `P(Bin(E + v, 1/2) ≥ E)` (`negbin_bound`). Proof at
a finite horizon `M`: the event reads the first `M` directions, a cylinder of probability
`#words/4^M` (`dirMeasure_cyl`); the words are counted by their first letter (`negbinWords_succ_card`)
against Pascal's rule for the binomial tail (`binGe_pascal`); then `M → ∞` by continuity from below.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- `k_a(n)` for a finite word `w` of length `M`: the number of `i < n` with `w i = a`. -/
def wCount {M : ℕ} (w : Fin M → Fin 4) (a : Fin 4) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin M => (i : ℕ) < n ∧ w i = a).card

/-- The words of length `M` in which, at some time `n ≤ M`, at least `E` letters `a` and at most
`v` letters `b` have occurred. -/
def negbinWords (a b : Fin 4) (M E v : ℕ) : Finset (Fin M → Fin 4) :=
  Finset.univ.filter fun w => ∃ n : Fin (M + 1), E ≤ wCount w a n ∧ wCount w b n ≤ v

theorem wCount_zero {M : ℕ} (w : Fin M → Fin 4) (a : Fin 4) : wCount w a 0 = 0 := by
  simp [wCount]

theorem wCount_cons {M : ℕ} (d : Fin 4) (w : Fin M → Fin 4) (a : Fin 4) (n : ℕ) :
    wCount (Fin.cons d w : Fin (M + 1) → Fin 4) a (n + 1) = (if d = a then 1 else 0) + wCount w a n := by
  simp only [wCount, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, Nat.add_lt_add_iff_right]
  simp

theorem negbinWords_zero (a b : Fin 4) (M v : ℕ) : (negbinWords a b M 0 v).card = 4 ^ M := by
  rw [negbinWords, Finset.filter_true_of_mem fun w _ => ⟨0, by simp [wCount_zero]⟩]
  simp

/-- Membership of `Fin.cons d w`, read on the first letter. -/
theorem cons_mem_negbinWords (a b : Fin 4) (M E v : ℕ) (d : Fin 4) (w : Fin M → Fin 4) :
    (Fin.cons d w : Fin (M + 1) → Fin 4) ∈ negbinWords a b (M + 1) (E + 1) v ↔
      ∃ n : Fin (M + 1), E + 1 ≤ (if d = a then 1 else 0) + wCount w a n ∧
        (if d = b then 1 else 0) + wCount w b n ≤ v := by
  simp only [negbinWords, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.exists_fin_succ]
  simp only [Fin.val_zero, wCount_zero, Fin.val_succ, wCount_cons]
  constructor
  · rintro (h | h)
    · omega
    · exact h
  · exact Or.inr

theorem card_filter_cons (a b : Fin 4) (hab : a ≠ b) (M E v : ℕ) (d : Fin 4) :
    (Finset.univ.filter fun w : Fin M → Fin 4 =>
      (Fin.cons d w : Fin (M + 1) → Fin 4) ∈ negbinWords a b (M + 1) (E + 1) v).card =
      if d = a then (negbinWords a b M E v).card
      else if d = b then (if v = 0 then 0 else (negbinWords a b M (E + 1) (v - 1)).card)
      else (negbinWords a b M (E + 1) v).card := by
  simp only [cons_mem_negbinWords]
  by_cases hda : d = a
  · subst hda
    simp only [hab, ↓reduceIte, negbinWords]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact exists_congr fun n => by omega
  · by_cases hdb : d = b
    · subst hdb
      simp only [hda, ↓reduceIte]
      by_cases hv : v = 0
      · simp only [hv, ite_true]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro w _ ⟨n, _, h⟩
        omega
      · simp only [hv, ite_false, negbinWords]
        congr 1
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact exists_congr fun n => by omega
    · simp only [hda, hdb, ↓reduceIte, negbinWords]
      congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact exists_congr fun n => by omega

theorem negbinWords_succ_card (a b : Fin 4) (hab : a ≠ b) (M E v : ℕ) :
    (negbinWords a b (M + 1) (E + 1) v).card =
      (negbinWords a b M E v).card +
        (if v = 0 then 0 else (negbinWords a b M (E + 1) (v - 1)).card) +
          2 * (negbinWords a b M (E + 1) v).card := by
  have hsplit : (negbinWords a b (M + 1) (E + 1) v).card = ∑ d : Fin 4,
      (Finset.univ.filter fun w : Fin M → Fin 4 =>
        (Fin.cons d w : Fin (M + 1) → Fin 4) ∈ negbinWords a b (M + 1) (E + 1) v).card := by
    simp only [Finset.card_filter]
    rw [← Fintype.sum_prod_type', Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 4)
      (fun p : Fin 4 × (Fin M → Fin 4) => if (Fin.cons p.1 p.2 : Fin (M + 1) → Fin 4) ∈
        negbinWords a b (M + 1) (E + 1) v then 1 else 0)
      (fun f => if f ∈ negbinWords a b (M + 1) (E + 1) v then 1 else 0) (fun p => rfl)]
    simp
  rw [hsplit]
  simp only [card_filter_cons a b hab]
  generalize (negbinWords a b M E v).card = x
  generalize (if v = 0 then 0 else (negbinWords a b M (E + 1) (v - 1)).card) = y
  generalize (negbinWords a b M (E + 1) v).card = z
  fin_cases a <;> fin_cases b <;> simp_all [Fin.sum_univ_four] <;> omega

/-- At `p = 1/2` the binomial tail is a sum of binomial coefficients over `2^m`. -/
theorem binGe_half_eq (m k : ℕ) :
    binGe m (1 / 2) k = (∑ i ∈ Finset.Icc k m, (m.choose i : ℝ)) / 2 ^ m := by
  unfold binGe binPmf
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := (Finset.mem_Icc.1 hi).2
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, mul_assoc, ← pow_add, Nat.add_sub_cancel' him]
  rw [one_div_pow, mul_one_div]

/-- Pascal's rule on the tails of a row of binomial coefficients. -/
theorem sum_Icc_choose_succ (n E : ℕ) (hE : E ≤ n) :
    ∑ i ∈ Finset.Icc (E + 1) (n + 1), ((n + 1).choose i : ℝ) =
      ∑ i ∈ Finset.Icc E n, (n.choose i : ℝ) + ∑ i ∈ Finset.Icc (E + 1) n, (n.choose i : ℝ) := by
  have hmap : ∀ f : ℕ → ℝ, ∑ i ∈ Finset.Icc (E + 1) (n + 1), f i = ∑ j ∈ Finset.Icc E n, f (j + 1) := by
    intro f
    rw [← Finset.map_add_right_Icc E n 1, Finset.sum_map]
    rfl
  rw [hmap]
  simp only [Nat.choose_succ_succ', Nat.cast_add, Finset.sum_add_distrib]
  congr 1
  rw [← hmap (fun i => (n.choose i : ℝ)), Finset.sum_Icc_succ_top (by omega),
    Nat.choose_succ_self, Nat.cast_zero, add_zero]

theorem binGe_pascal (E v : ℕ) :
    binGe (E + 1 + (v + 1)) (1 / 2) (E + 1) =
      (binGe (E + (v + 1)) (1 / 2) E + binGe (E + 1 + v) (1 / 2) (E + 1)) / 2 := by
  rw [show E + 1 + (v + 1) = (E + v + 1) + 1 by omega, show E + (v + 1) = E + v + 1 by omega,
    show E + 1 + v = E + v + 1 by omega, binGe_half_eq, binGe_half_eq, binGe_half_eq,
    sum_Icc_choose_succ _ _ (by omega), pow_succ]
  field_simp

theorem binGe_zero_right (v : ℕ) : binGe v (1 / 2) 0 = 1 := by
  rw [binGe_half_eq, show Finset.Icc 0 v = Finset.range (v + 1) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_range]; omega]
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  field_simp

theorem binGe_diag_succ (E : ℕ) : binGe (E + 1) (1 / 2) (E + 1) = binGe E (1 / 2) E / 2 := by
  rw [binGe_half_eq, binGe_half_eq, Finset.Icc_self, Finset.Icc_self, Finset.sum_singleton,
    Finset.sum_singleton, Nat.choose_self, Nat.choose_self, pow_succ]
  field_simp

theorem binGe_half_nonneg (n E : ℕ) : 0 ≤ binGe n (1 / 2) E := by
  rw [binGe_half_eq]
  positivity

/-- The number of words of length `M` in which at some time at least `E` letters `a` and at most
`v` letters `b` occurred is at most `4^M P(Bin(E + v, 1/2) ≥ E)`. -/
theorem negbinWords_card (a b : Fin 4) (hab : a ≠ b) :
    ∀ M E v : ℕ, ((negbinWords a b M E v).card : ℝ) ≤ 4 ^ M * binGe (E + v) (1 / 2) E
  | M, 0, v => by
    rw [negbinWords_zero, zero_add, binGe_zero_right]
    simp
  | 0, E + 1, v => by
    have h : negbinWords a b 0 (E + 1) v = ∅ := by
      rw [negbinWords, Finset.filter_eq_empty_iff]
      rintro w - ⟨n, h, -⟩
      have : wCount w a n = 0 := by simp [wCount]
      omega
    rw [h, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by positivity) (binGe_half_nonneg _ _)
  | M + 1, E + 1, v => by
    have h1 := negbinWords_card a b hab M E v
    have h3 := negbinWords_card a b hab M (E + 1) v
    rw [negbinWords_succ_card a b hab, pow_succ]
    rcases v with _ | v
    · simp only [↓reduceIte, add_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h1 h3 ⊢
      rw [binGe_diag_succ] at h3 ⊢
      nlinarith
    · have h2 := negbinWords_card a b hab M (E + 1) v
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat] at h1 h2 h3 ⊢
      have key : 4 ^ M * binGe (E + (v + 1)) (1 / 2) E + 4 ^ M * binGe (E + 1 + v) (1 / 2) (E + 1) =
          2 * (4 ^ M * binGe (E + 1 + (v + 1)) (1 / 2) (E + 1)) := by
        rw [binGe_pascal]; ring
      linarith

/-- The direction counts up to time `n ≤ M` read only the first `M` directions. -/
theorem dirCount_eq_wCount (D : ℕ → Fin 4) (M n : ℕ) (hn : n ≤ M) (a : Fin 4) :
    dirCount D a n = wCount (fun i : Fin M => D i) a n := by
  unfold dirCount wCount
  rw [Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun i => if i < n ∧ D i = a then 1 else 0) M,
    ← Finset.sum_range_add_sum_Ico _ hn]
  have h0 : ∑ i ∈ Finset.Ico n M, (if i < n ∧ D i = a then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_Ico] at hi
      simp [show ¬ i < n by omega]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  simp [hi]

/-- A cylinder event of the first `M` directions: its probability is the number of words over
`4^M`. -/
theorem dirMeasure_cyl (M : ℕ) (S : Finset (Fin M → Fin 4)) :
    dirMeasure {D | (fun i : Fin M => D i) ∈ S} = S.card * (4⁻¹ : ℝ≥0∞) ^ M := by
  have hmeas : ∀ w : Fin M → Fin 4, MeasurableSet {D : ℕ → Fin 4 | (fun i : Fin M => D i) = w} :=
    fun w => by
      rw [show {D : ℕ → Fin 4 | (fun i : Fin M => D i) = w} = ⋂ i : Fin M, {D | D i = w i} by
        ext D; simp [funext_iff]]
      refine MeasurableSet.iInter fun i => ?_
      have hk : Measurable fun D : ℕ → Fin 4 => D i := measurable_pi_apply _
      exact hk (measurableSet_singleton (w i))
  have hone : ∀ w : Fin M → Fin 4,
      dirMeasure {D : ℕ → Fin 4 | (fun i : Fin M => D i) = w} = (4⁻¹ : ℝ≥0∞) ^ M := by
    intro w
    let t : ℕ → Set (Fin 4) := fun j => {if h : j < M then w ⟨j, h⟩ else 0}
    have hset : {D : ℕ → Fin 4 | (fun i : Fin M => D i) = w} =
        Set.pi (↑(Finset.range M)) t := by
      ext D
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio, t,
        Set.mem_singleton_iff, funext_iff]
      constructor
      · intro h j hj
        simp only [hj, ↓reduceDIte]
        exact h ⟨j, hj⟩
      · intro h i
        have := h i i.2
        simpa only [i.2, ↓reduceDIte] using this
    rw [hset]
    unfold dirMeasure
    rw [Measure.infinitePi_pi _ fun j _ => MeasurableSet.singleton _]
    simp only [uniformOn_univ, Measure.count_singleton, Fintype.card_fin]
    simp [Finset.prod_const]
  have hU : {D : ℕ → Fin 4 | (fun i : Fin M => D i) ∈ S} =
      ⋃ w ∈ S, {D : ℕ → Fin 4 | (fun i : Fin M => D i) = w} := by
    ext D
    simp
  rw [hU, measure_biUnion_finset (fun w _ w' _ hne => Set.disjoint_left.2 fun D h h' =>
    hne (h.symm.trans h')) fun w _ => hmeas w]
  simp only [hone, Finset.sum_const, nsmul_eq_mul]

theorem dirMeasure_cyl_toReal (M : ℕ) (S : Finset (Fin M → Fin 4)) :
    (dirMeasure {D | (fun i : Fin M => D i) ∈ S}).toReal = S.card / 4 ^ M := by
  rw [dirMeasure_cyl, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
  simp [div_eq_mul_inv]

/-- The probability that, for two distinct directions `a ≠ b`, at some time at least `E` directions
`a` and at most `v` directions `b` have occurred is at most `P(Bin(E + v, 1/2) ≥ E)`. -/
theorem negbin_bound (a b : Fin 4) (hab : a ≠ b) (E v : ℕ) :
    (dirMeasure {D | ∃ n, E ≤ dirCount D a n ∧ dirCount D b n ≤ v}).toReal ≤
      binGe (E + v) (1 / 2) E := by
  have hg : 0 ≤ binGe (E + v) (1 / 2) E := binGe_half_nonneg _ _
  set A : ℕ → Set (ℕ → Fin 4) :=
    fun M => {D | (fun i : Fin M => D i) ∈ negbinWords a b M E v} with hA_def
  have hA : ∀ M, A M = {D | ∃ n ≤ M, E ≤ dirCount D a n ∧ dirCount D b n ≤ v} := by
    intro M
    ext D
    simp only [hA_def, negbinWords, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h1, h2⟩
      have hn : (n : ℕ) ≤ M := Nat.lt_succ_iff.1 n.2
      exact ⟨n, hn, by rwa [dirCount_eq_wCount D M n hn], by rwa [dirCount_eq_wCount D M n hn]⟩
    · rintro ⟨n, hn, h1, h2⟩
      exact ⟨⟨n, Nat.lt_succ_of_le hn⟩, by rwa [← dirCount_eq_wCount D M n hn],
        by rwa [← dirCount_eq_wCount D M n hn]⟩
  have hmono : Monotone A := by
    intro M M' h
    rw [hA, hA]
    rintro D ⟨n, hn, h'⟩
    exact ⟨n, hn.trans h, h'⟩
  have hU : {D : ℕ → Fin 4 | ∃ n, E ≤ dirCount D a n ∧ dirCount D b n ≤ v} = ⋃ M, A M := by
    ext D
    simp only [Set.mem_iUnion, hA, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h⟩
      exact ⟨n, n, le_rfl, h⟩
    · rintro ⟨M, n, -, h⟩
      exact ⟨n, h⟩
  have hle : ∀ M, dirMeasure (A M) ≤ ENNReal.ofReal (binGe (E + v) (1 / 2) E) := by
    intro M
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hg, hA_def, dirMeasure_cyl_toReal,
      div_le_iff₀ (by positivity), mul_comm]
    exact negbinWords_card a b hab M E v
  rw [hU, hmono.measure_iUnion]
  exact ENNReal.toReal_le_of_le_ofReal hg (iSup_le hle)

end FrogModel.D3.Iface
