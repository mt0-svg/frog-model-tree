module

public import FrogModel.LemmaX.PlanCheck

@[expose] public section

/-!
# Soundness of the check of (I4) (condition (C7) of the paper)

`planI4_of_check`: if `planCheck A den pl = true`, then `PlanI4 (latMeasure A)`. The coupling is
the finite sum, over the entries `(i, a)` of the plan for the path `π`, of
`(a / den) • dirac (x_i, block of π)`:

- second marginal: the entries of each path fill it exactly, so it is `hstarFin`;
- first marginal: regrouped by atom, the amount drawn from atom `i` is at most `m_i / 2^40`;
- every atom of the coupling is a pair `x_i ≤ block of π`.

The Kronecker digits of the check are identified by `digit_packDigits` and `digit_kron`.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.LemmaX

open FrogModel.Cert

/-! ### Kronecker digits -/

/-- The digits of a number written in base `2^s` with digits below `2^s`. -/
theorem digit_packDigits (s k : ℕ) (L : List ℕ) (hL : ∀ d ∈ L, d < 2 ^ s) :
    digit s (packDigits (2 ^ s) L) k = L.getD k 0 := by
  induction L generalizing k with
  | nil => simp [digit, packDigits]
  | cons d L ih =>
    have hd : d < 2 ^ s := hL d (by simp)
    have ih' := fun k => ih k (fun x hx => hL x (by simp [hx]))
    cases k with
    | zero =>
      simp only [digit, packDigits, mul_zero, Nat.shiftRight_zero, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hd, List.getD_cons_zero]
    | succ k =>
      rw [List.getD_cons_succ, ← ih' k]
      simp only [digit, packDigits, Nat.shiftRight_eq_div_pow]
      have hp : 2 ^ (s * (k + 1)) = 2 ^ s * 2 ^ (s * k) := by
        rw [mul_add, mul_one, pow_add, mul_comm]
      rw [hp, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt hd, zero_add]

/-- Kronecker substitution without carry: when the values sum to less than `2^s`, digit `k` of
`kron s l` is the sum of the values of index `k`. -/
theorem digit_kron (s k : ℕ) (l : List (ℕ × ℕ)) (hl : (l.map Prod.snd).sum < 2 ^ s) :
    digit s (kron s l) k = ((l.filter fun e => e.1 == k).map Prod.snd).sum := by
  -- the three parts of the entries: index below, equal to, above `k`
  set lo : List (ℕ × ℕ) → ℕ := fun l =>
    ((l.filter fun e => decide (e.1 < k)).map fun e => e.2 * 2 ^ (s * e.1)).sum with hlo
  set C : List (ℕ × ℕ) → ℕ := fun l => ((l.filter fun e => e.1 == k).map Prod.snd).sum with hC
  set hi : List (ℕ × ℕ) → ℕ := fun l =>
    ((l.filter fun e => decide (k < e.1)).map fun e => e.2 * 2 ^ (s * (e.1 - k - 1))).sum with hhi
  have hsplit : ∀ l : List (ℕ × ℕ), kron s l = lo l + 2 ^ (s * k) * (C l + 2 ^ s * hi l) := by
    intro l
    induction l with
    | nil => simp [kron, hlo, hC, hhi]
    | cons e l ih =>
      have hk : kron s (e :: l) = e.2 * 2 ^ (s * e.1) + kron s l := by simp [kron]
      rw [hk, ih]
      rcases lt_trichotomy e.1 k with h | h | h
      · have h1 : lo (e :: l) = e.2 * 2 ^ (s * e.1) + lo l := by
          simp [hlo, h]
        have h2 : C (e :: l) = C l := by
          simp [hC, h.ne]
        have h3 : hi (e :: l) = hi l := by
          simp [hhi, not_lt.2 h.le]
        rw [h1, h2, h3]; ring
      · have h1 : lo (e :: l) = lo l := by simp [hlo, h]
        have h2 : C (e :: l) = e.2 + C l := by simp [hC, h]
        have h3 : hi (e :: l) = hi l := by simp [hhi, h]
        rw [h1, h2, h3, ← h]; ring
      · have h1 : lo (e :: l) = lo l := by simp [hlo, not_lt.2 h.le]
        have h2 : C (e :: l) = C l := by simp [hC, h.ne']
        have h3 : hi (e :: l) = e.2 * 2 ^ (s * (e.1 - k - 1)) + hi l := by
          simp [hhi, h]
        have hp : 2 ^ (s * e.1) = 2 ^ (s * k) * (2 ^ s * 2 ^ (s * (e.1 - k - 1))) := by
          rw [← pow_add, ← pow_add]
          congr 1
          have : e.1 = k + 1 + (e.1 - k - 1) := by omega
          conv_lhs => rw [this]
          ring
        rw [h1, h2, h3, hp]; ring
  -- the low part is below `2^(s k)`
  have hlo_le : ∀ l : List (ℕ × ℕ), lo l * 2 ^ s ≤
      ((l.filter fun e => decide (e.1 < k)).map Prod.snd).sum * 2 ^ (s * k) := by
    intro l
    induction l with
    | nil => simp [hlo]
    | cons e l ih =>
      by_cases h : e.1 < k
      · have h1 : lo (e :: l) = e.2 * 2 ^ (s * e.1) + lo l := by
          simp [hlo, h]
        rw [h1, List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons,
          add_mul, add_mul]
        refine add_le_add ?_ ih
        rw [mul_assoc]
        refine Nat.mul_le_mul_left _ ?_
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      · have h1 : lo (e :: l) = lo l := by simp [hlo, h]
        rw [h1, List.filter_cons_of_neg (by simpa using h)]
        exact ih
  have hsub : ∀ (p : ℕ × ℕ → Bool), ((l.filter p).map Prod.snd).sum ≤ (l.map Prod.snd).sum := by
    intro p
    exact List.Sublist.sum_le_sum ((List.filter_sublist).map _) (fun _ _ => Nat.zero_le _)
  have hlo_lt : lo l < 2 ^ (s * k) := by
    have h1 := hlo_le l
    have h2 := hsub fun e => decide (e.1 < k)
    have h3 : lo l * 2 ^ s < 2 ^ s * 2 ^ (s * k) := by
      calc lo l * 2 ^ s ≤ _ := h1
        _ < 2 ^ s * 2 ^ (s * k) := by
          exact Nat.mul_lt_mul_of_pos_right (lt_of_le_of_lt h2 hl) (by positivity)
    rw [mul_comm (2 ^ s)] at h3
    exact Nat.lt_of_mul_lt_mul_right h3
  have hC_lt : C l < 2 ^ s := lt_of_le_of_lt (hsub _) hl
  unfold digit
  rw [hsplit l, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt hlo_lt, zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hC_lt]

/-- Decoding a code. -/
theorem decode4_code4 (x : ℕ × ℕ × ℕ × ℕ) (h1 : x.1 < 16) (h2 : x.2.1 < 16) (h3 : x.2.2.1 < 16)
    (h4 : x.2.2.2 < 16) : decode4 (code4 x) = x := by
  obtain ⟨a, b, c, e⟩ := x
  simp only at h1 h2 h3 h4
  simp only [decode4, code4, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- A code is below `2^16`. -/
theorem code4_lt (x : ℕ × ℕ × ℕ × ℕ) (h1 : x.1 < 16) (h2 : x.2.1 < 16) (h3 : x.2.2.1 < 16)
    (h4 : x.2.2.2 < 16) : code4 x < 2 ^ 16 := by
  obtain ⟨a, b, c, e⟩ := x
  simp only at h1 h2 h3 h4
  simp only [code4]
  omega

/-- The digit `i` of `atomCode A` decodes to the block of atom `i`. -/
theorem decode4_digit_atomCode (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) (hA : atomsSmall A = true)
    (i : ℕ) (hi : i < A.length) :
    decode4 (digit 16 (atomCode A) i) = (A.getD i ((0, 0, 0, 0), 0)).1 := by
  simp only [atomsSmall, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hA
  have hL : ∀ d ∈ A.map (fun a => code4 a.1), d < 2 ^ 16 := by
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨a, ha, rfl⟩ := hd
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hA a ha
    exact code4_lt _ h1 h2 h3 h4
  have hai : A.getD i ((0, 0, 0, 0), 0) ∈ A := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hA _ hai
  unfold atomCode
  rw [digit_packDigits 16 i _ hL]
  have : (A.map fun a => code4 a.1).getD i 0 = code4 (A.getD i ((0, 0, 0, 0), 0)).1 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi]
    rfl
  rw [this, decode4_code4 _ h1 h2 h3 h4]

/-! ### Blocks -/

/-- `blockLE` gives the order of the blocks in `Fin 4 → ℕ∞`. -/
theorem toBlock4_le_pathBlock (x : ℕ × ℕ × ℕ × ℕ) (π : List Tr) (h : blockLE x π = true) :
    toBlock4 x ≤ pathBlock 4 π := by
  simp only [blockLE, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  intro i
  fin_cases i
  · show (x.1 : ℕ∞) ≤ (((π.take 1).map Tr.δ).sum : ℕ)
    exact_mod_cast h1
  · show (x.2.1 : ℕ∞) ≤ (((π.take 2).map Tr.δ).sum : ℕ)
    exact_mod_cast h2
  · show (x.2.2.1 : ℕ∞) ≤ (((π.take 3).map Tr.δ).sum : ℕ)
    exact_mod_cast h3
  · show (x.2.2.2 : ℕ∞) ≤ (((π.take 4).map Tr.δ).sum : ℕ)
    exact_mod_cast h4

/-! ### Finite sums of weighted Dirac masses -/

/-- The image of a finite sum of weighted Dirac masses. -/
theorem map_sum_smul_dirac {γ α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (l : List γ)
    (c : γ → ℝ≥0∞) (f : γ → α) {g : α → β} (hg : Measurable g) :
    ((l.map fun t => c t • Measure.dirac (f t)).sum).map g =
      (l.map fun t => c t • Measure.dirac (g (f t))).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.sum_cons, Measure.map_add _ _ hg, Measure.map_smul,
      Measure.map_dirac' hg, ih, List.map_cons, List.sum_cons]
    exact hg.aemeasurable

/-- A property of every atom of a finite sum of weighted Dirac masses holds almost everywhere. -/
theorem ae_sum_smul_dirac {γ α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (l : List γ) (c : γ → ℝ≥0∞) (f : γ → α) (P : α → Prop) (h : ∀ t ∈ l, P (f t)) :
    ∀ᵐ p ∂(l.map fun t => c t • Measure.dirac (f t)).sum, P p := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.sum_cons, ae_add_measure_iff]
    refine ⟨Measure.ae_smul_measure ?_ _, ih fun u hu => h u (by simp [hu])⟩
    rw [Filter.Eventually, ae_dirac_eq]
    exact Filter.eventually_pure.2 (h t (by simp))

/-- Regrouping a finite sum by an index below `n`. -/
theorem sum_smul_regroup {γ α : Type*} [MeasurableSpace α] (l : List γ) (idx : γ → ℕ)
    (w : γ → ℝ≥0∞) (F : ℕ → Measure α) (n : ℕ) (h : ∀ t ∈ l, idx t < n) :
    (l.map fun t => w t • F (idx t)).sum =
      ((List.range n).map fun i => ((l.filter fun t => idx t == i).map w).sum • F i).sum := by
  have hb : ∀ f : ℕ → Measure α, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
    intro f
    rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe,
      Multiset.sum_coe]
  rw [hb]
  induction l with
  | nil => simp
  | cons t l ih =>
    have ht := h t (by simp)
    rw [List.map_cons, List.sum_cons, ih fun u hu => h u (by simp [hu])]
    have hs : ∀ i, ((List.filter (fun u => idx u == i) (t :: l)).map w).sum • F i =
        (if idx t = i then w t • F i else 0) +
          ((List.filter (fun u => idx u == i) l).map w).sum • F i := by
      intro i
      by_cases hi : idx t = i
      · simp [hi, add_smul]
      · simp [hi]
    rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp [ht]

/-- Termwise comparison of two finite sums of measures over the same list. -/
theorem list_sum_measure_le {γ α : Type*} [MeasurableSpace α] (l : List γ)
    (μ ν : γ → Measure α) (h : ∀ t ∈ l, μ t ≤ ν t) :
    (l.map μ).sum ≤ (l.map ν).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact add_le_add (h t (by simp)) (ih fun u hu => h u (by simp [hu]))

/-- A natural number over a positive one in `ℝ≥0∞`, from an equality of rationals. -/
theorem natCast_div_eq_ofReal (n den : ℕ) (q : ℚ) (hden : 0 < den) (h : (n : ℚ) = den * q) :
    (n : ℝ≥0∞) / den = ENNReal.ofReal (q : ℝ) := by
  have hd : (den : ℚ) ≠ 0 := by exact_mod_cast hden.ne'
  have hq : q = n / den := by
    rw [eq_div_iff hd, h]
    ring
  have hq' : (q : ℝ) = (n : ℝ) / den := by
    rw [hq]
    push_cast
    rfl
  rw [hq', ENNReal.ofReal_div_of_pos (by exact_mod_cast hden), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

/-- A comparison of fractions in `ℝ≥0∞`. -/
theorem natCast_div_le_div (a m den : ℕ) (hden : 0 < den) (h : a * 2 ^ 40 ≤ m * den) :
    (a : ℝ≥0∞) / den ≤ (m : ℝ≥0∞) / 2 ^ 40 := by
  have h40 : (2 : ℝ≥0∞) ^ 40 ≠ 0 := by positivity
  have h40' : (2 : ℝ≥0∞) ^ 40 ≠ ⊤ := by simp
  have hd : (den : ℝ≥0∞) ≠ 0 := by exact_mod_cast hden.ne'
  have hd' : (den : ℝ≥0∞) ≠ ⊤ := by simp
  have hc : (a : ℝ≥0∞) * 2 ^ 40 ≤ m * den := by exact_mod_cast h
  calc (a : ℝ≥0∞) / den = (a * 2 ^ 40) / (den * 2 ^ 40) :=
        (ENNReal.mul_div_mul_right _ _ h40 h40').symm
    _ ≤ (m * den) / (den * 2 ^ 40) := by gcongr
    _ = m / 2 ^ 40 := by
        rw [mul_comm (den : ℝ≥0∞)]
        exact ENNReal.mul_div_mul_right _ _ hd hd'

/-! ### Lists of measures -/

/-- The sum over a `flatMap`, by blocks. -/
theorem sum_flatMap_map {α β M : Type*} [AddMonoid M] (Z : List α) (G : α → List β)
    (f : β → M) : ((Z.flatMap G).map f).sum = (Z.map fun q => ((G q).map f).sum).sum := by
  induction Z with
  | nil => simp
  | cons q Z ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- A finite sum of multiples of one measure. -/
theorem sum_map_smul_measure {γ α : Type*} [MeasurableSpace α] (l : List γ) (c : γ → ℝ≥0∞)
    (μ : Measure α) : (l.map fun x => c x • μ).sum = (l.map c).sum • μ := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.sum_cons, ih, add_smul]

/-- A finite sum of fractions with one denominator in `ℝ≥0∞`. -/
theorem sum_natCast_div (l : List ℕ) (den : ℕ) :
    (l.map fun a : ℕ => (a : ℝ≥0∞) / den).sum = ((l.sum : ℕ) : ℝ≥0∞) / den := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, ih, List.sum_cons, Nat.cast_add, ENNReal.add_div]

/-- A list mapped through its indices. -/
theorem map_eq_map_range {α β : Type*} (A : List α) (d : α) (f : α → β) :
    A.map f = (List.range A.length).map fun i => f (A.getD i d) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

/-- Multiples of a measure are monotone in the factor. -/
theorem smul_le_smul_measure {α : Type*} [MeasurableSpace α] {c d : ℝ≥0∞} (μ : Measure α)
    (h : c ≤ d) : c • μ ≤ d • μ := by
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr

set_option maxRecDepth 20000 in
/-- `hstarFin` with the paths and blocks at `J = 4`. -/
theorem hstarFin_eq : hstarFin = ENNReal.ofReal ((1 - cand.eps : ℚ) : ℝ) •
    ((cand.paths 4 0 0).map fun π => ENNReal.ofReal (pathProb π : ℝ) •
      Measure.dirac (pathBlock 4 π)).sum := by
  unfold hstarFin Data.tabLaw
  rfl

/-! ### The coupling -/

/-- The coupling of a plan. -/
noncomputable def planCoupling (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) (den : ℕ)
    (pl : List (List (ℕ × ℕ))) : Measure ((Fin 4 → ℕ∞) × (Fin 4 → ℕ∞)) :=
  ((((cand.paths 4 0 0).zip pl).flatMap fun q => q.2.map fun e => (e, q.1)).map fun t =>
    ((t.1.2 : ℝ≥0∞) / den) •
      Measure.dirac (toBlock4 (A.getD t.1.1 ((0, 0, 0, 0), 0)).1, pathBlock 4 t.2)).sum

/-- **Soundness of the check of (I4).** -/
theorem planI4_of_check (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) (den : ℕ) (pl : List (List (ℕ × ℕ)))
    (h : planCheck A den pl = true) : PlanI4 (latMeasure A) := by
  simp only [planCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hden, hsmall⟩, hlen⟩, hpaths⟩, htot⟩, hdrawn⟩ := h
  set P := cand.paths 4 0 0 with hP
  set Z := P.zip pl with hZ
  set d0 : (ℕ × ℕ × ℕ × ℕ) × ℕ := ((0, 0, 0, 0), 0) with hd0
  set E := Z.flatMap fun q => q.2.map fun e => (e, q.1) with hE
  set w : (ℕ × ℕ) × List Tr → ℝ≥0∞ := fun t => (t.1.2 : ℝ≥0∞) / den with hw
  set X : ℕ → Fin 4 → ℕ∞ := fun i => toBlock4 (A.getD i d0).1 with hX
  have hcpl : planCoupling A den pl =
      (E.map fun t => w t • Measure.dirac (X t.1.1, pathBlock 4 t.2)).sum := rfl
  have hmemE : ∀ t ∈ E, ∃ q ∈ Z, t.1 ∈ q.2 ∧ t.2 = q.1 := by
    intro t ht
    rw [hE, List.mem_flatMap] at ht
    obtain ⟨q, hq, ht⟩ := ht
    rw [List.mem_map] at ht
    obtain ⟨e, he, rfl⟩ := ht
    exact ⟨q, hq, he, rfl⟩
  have hent : ∀ t ∈ E, t.1.1 < A.length ∧
      blockLE (decode4 (digit 16 (atomCode A) t.1.1)) t.2 = true := by
    intro t ht
    obtain ⟨q, hq, he, h2⟩ := hmemE t ht
    have hq' := hpaths q hq
    simp only [pathOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hq'
    have := hq'.2 t.1 he
    rw [h2]
    exact this
  refine ⟨planCoupling A den pl, ?_, ?_, ?_⟩
  · -- first marginal
    have hfst : (E.map Prod.fst) = pl.flatten := by
      rw [hE, List.map_flatMap]
      have h1 : (fun q : List Tr × List (ℕ × ℕ) => (q.2.map fun e => (e, q.1)).map Prod.fst) =
          fun q => q.2 := by
        funext q
        rw [List.map_map]
        exact List.map_id' q.2
      rw [h1, List.flatMap_def]
      show (Z.map Prod.snd).flatten = _
      rw [hZ, List.map_snd_zip hlen.ge]
    have hdr : ∀ i, ((E.filter fun t => t.1.1 == i).map w).sum =
        ((((pl.flatten.filter fun e => e.1 == i).map Prod.snd).sum : ℕ) : ℝ≥0∞) / den := by
      intro i
      rw [← sum_natCast_div, ← hfst, List.filter_map, List.map_map, List.map_map]
      rfl
    rw [hcpl, map_sum_smul_dirac E w _ measurable_fst]
    have hre := sum_smul_regroup E (fun t => t.1.1) w (fun i => Measure.dirac (X i)) A.length
      (fun t ht => (hent t ht).1)
    rw [hre]
    unfold latMeasure
    rw [map_eq_map_range A d0]
    refine list_sum_measure_le _ _ _ fun i hi => ?_
    rw [List.mem_range] at hi
    refine smul_le_smul_measure _ ?_
    rw [hdr i]
    refine natCast_div_le_div _ _ _ hden ?_
    rw [← digit_kron planBits i pl.flatten htot]
    simp only [drawnOK, List.all_eq_true, decide_eq_true_eq] at hdrawn
    have hmem : (A.getD i d0, i) ∈ A.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hh := hdrawn _ hmem
    simpa using hh
  · -- second marginal
    have heps : cand.eps = 1 / 10000 := rfl
    have hc : (0 : ℝ) ≤ ((1 - cand.eps : ℚ) : ℝ) := by rw [heps]; norm_num
    set c : ℝ≥0∞ := ENNReal.ofReal ((1 - cand.eps : ℚ) : ℝ) with hcdef
    set F : List Tr → Measure (Fin 4 → ℕ∞) := fun π =>
      c • (ENNReal.ofReal (pathProb π : ℝ) • Measure.dirac (pathBlock 4 π)) with hF
    rw [hcpl, map_sum_smul_dirac E w _ measurable_snd, hE, sum_flatMap_map]
    have hq : ∀ q ∈ Z, (((q.2.map fun e => (e, q.1)).map fun t =>
        w t • Measure.dirac ((X t.1.1, pathBlock 4 t.2).2)).sum) = F q.1 := by
      intro q hqZ
      rw [List.map_map]
      have e0 : ((fun t => w t • Measure.dirac ((X t.1.1, pathBlock 4 t.2).2)) ∘
          fun e : ℕ × ℕ => (e, q.1)) =
          fun e => (fun e : ℕ × ℕ => (e.2 : ℝ≥0∞) / den) e • Measure.dirac (pathBlock 4 q.1) := rfl
      rw [e0, sum_map_smul_measure, hF]
      simp only
      rw [smul_smul]
      congr 1
      have hq' := hpaths q hqZ
      simp only [pathOK, Bool.and_eq_true, decide_eq_true_eq] at hq'
      have e1 : (q.2.map fun e : ℕ × ℕ => (e.2 : ℝ≥0∞) / den) =
          ((q.2.map Prod.snd).map fun a : ℕ => (a : ℝ≥0∞) / den) := by
        rw [List.map_map]
        rfl
      rw [e1, sum_natCast_div, natCast_div_eq_ofReal _ _ _ hden hq'.1, Rat.cast_mul,
        ENNReal.ofReal_mul hc]
    rw [List.map_congr_left hq]
    have hZP : (Z.map fun q => F q.1) = P.map F := by
      rw [show (fun q : List Tr × List (ℕ × ℕ) => F q.1) = F ∘ Prod.fst from rfl, ← List.map_map,
        hZ, List.map_fst_zip hlen.le]
    rw [hZP, hF]
    have e2 : (P.map fun π => c • (ENNReal.ofReal (pathProb π : ℝ) • Measure.dirac (pathBlock 4 π))) =
        (P.map fun π => ENNReal.ofReal (pathProb π : ℝ) • Measure.dirac (pathBlock 4 π)).map
          (c • ·) := by
      rw [List.map_map]
      rfl
    rw [e2, ← List.smul_sum, hstarFin_eq]
  · -- the order
    rw [hcpl]
    refine ae_sum_smul_dirac E w (fun t => (X t.1.1, pathBlock 4 t.2))
      (fun p => p.1 ≤ p.2) fun t ht => ?_
    obtain ⟨hi, hb⟩ := hent t ht
    have hx := decode4_digit_atomCode A hsmall t.1.1 hi
    rw [hx] at hb
    exact toBlock4_le_pathBlock _ _ hb

end FrogModel.LemmaX
