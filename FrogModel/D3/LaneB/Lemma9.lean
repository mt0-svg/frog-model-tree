module

public import FrogModel.D3.LaneB.Counts
public import FrogModel.D3.LaneB.Good

@[expose] public section

/-!
# Pieces of Lemma 11.4 of the paper (two initial frogs reach a child)

The inclusion `N < x` implies `G_c(1) < x` for the children entered, the
product law of three i.i.d. curves, and the value of the bound at `q = 2`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- The inclusion of the proof of Lemma 11.4 of the paper: if `N < x` then every child `c` entered
among the first `q` directions has `G_c(1) < x` (child curves nondecreasing). -/
theorem lemma9_incl (q x : ℕ) (G : Fin 3 → ℕ → ℕ∞) (D : ℕ → Fin 4)
    (hG : ∀ c, Monotone (G c)) (hN : closN q G D < x) (c : Fin 3)
    (hc : 1 ≤ dirCount D c.succ q) : G c 1 < x := by
  -- Step 1: The set S = {n | q ≤ n ∧ closT q G D n ≤ n} is nonempty.
  -- If it were empty, then closN would be ⊤, contradicting hN.
  have hS_nonempty : ∃ n : ℕ, q ≤ n ∧ closT q G D n ≤ n := by
    by_contra! h_empty
    -- h_empty : ∀ n, q ≤ n → (n : ℕ∞) < closT q G D n
    have h_closN_top : closN q G D = ⊤ := by
      unfold closN
      -- closN = ⨅ n, ⨅ (_ : q ≤ n ∧ closT n ≤ n), (n : ℕ∞)
      -- Since the condition is false for all n, each inner iInf is ⊤.
      -- So the whole iInf is ⊤.
      apply iInf_eq_top.mpr
      intro n
      by_cases hq : q ≤ n
      · have h_not_le : ¬ (closT q G D n ≤ n) := by
          intro hle
          have h_lt := h_empty n hq
          have : (n : ℕ∞) < (n : ℕ∞) := lt_of_lt_of_le h_lt hle
          exact lt_irrefl _ this
        simp [hq, h_not_le]
      · simp [hq]
    have h_contra : (⊤ : ℕ∞) < (x : ℕ∞) := by
      rw [← h_closN_top]
      exact hN
    -- ⊤ < (x : ℕ∞) is impossible because (x : ℕ∞) is finite
    have : ¬ ((⊤ : ℕ∞) < (x : ℕ∞)) := by
      intro hlt
      have := lt_of_lt_of_le hlt le_top
      exact lt_irrefl _ this
    exact this h_contra
  -- Step 2: Let n₀ be the minimal element of S.
  let S : Set ℕ := {n | q ≤ n ∧ closT q G D n ≤ n}
  have hS_nonempty' : S.Nonempty := hS_nonempty
  let n₀ := Nat.find hS_nonempty'
  have hn₀S : n₀ ∈ S := Nat.find_spec hS_nonempty'
  rcases hn₀S with ⟨hqn₀, hTn₀⟩
  have hn₀_min : ∀ m, m ∈ S → n₀ ≤ m := fun m hm => Nat.find_min' hS_nonempty' hm
  -- Step 3: Lemma: closT is monotone in its argument.
  have h_closT_mono : Monotone (closT q G D) := by
    intro a b h
    unfold closT
    have h_sum_le : (∑ c' : Fin 3, G c' (dirCount D c'.succ a)) ≤
                   (∑ c' : Fin 3, G c' (dirCount D c'.succ b)) := by
      refine Finset.sum_le_sum fun c' _ => ?_
      have h_dc : dirCount D c'.succ a ≤ dirCount D c'.succ b := by
        unfold dirCount
        have hrange : Finset.range a ⊆ Finset.range b := by
          intro i hi
          rw [Finset.mem_range] at hi ⊢
          omega
        have hfilter : ((Finset.range a).filter fun i => D i = c'.succ) ⊆
                      ((Finset.range b).filter fun i => D i = c'.succ) := by
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          rcases hx with ⟨hxr, hxeq⟩
          exact ⟨hrange hxr, hxeq⟩
        exact Finset.card_le_card hfilter
      exact hG c' h_dc
    -- Goal: (q : ℕ∞) + sum_a ≤ (q : ℕ∞) + sum_b
    -- `add_le_add_left h_sum_le (q : ℕ∞)` gives this.
    simpa [closT] using add_le_add_left h_sum_le (q : ℕ∞)
  -- Step 4: Chain of inequalities.
  -- G c 1 ≤ G c (dirCount D c.succ q) by monotonicity of G c
  have h_Gc1_le_Gcdq : G c 1 ≤ G c (dirCount D c.succ q) := hG c hc
  -- G c (dirCount D c.succ q) ≤ G c (dirCount D c.succ n₀) by monotonicity
  have h_Gcdq_le_Gcdn₀ : G c (dirCount D c.succ q) ≤ G c (dirCount D c.succ n₀) := by
    have h_dc : dirCount D c.succ q ≤ dirCount D c.succ n₀ := by
      unfold dirCount
      have hrange : Finset.range q ⊆ Finset.range n₀ := by
        intro i hi
        rw [Finset.mem_range] at hi ⊢
        omega
      have hfilter : ((Finset.range q).filter fun i => D i = c.succ) ⊆
                    ((Finset.range n₀).filter fun i => D i = c.succ) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        rcases hx with ⟨hxr, hxeq⟩
        exact ⟨hrange hxr, hxeq⟩
      exact Finset.card_le_card hfilter
    exact hG c h_dc
  -- G c (dirCount D c.succ n₀) ≤ closT q G D n₀
  have h_Gcdn₀_le_Tn₀ : G c (dirCount D c.succ n₀) ≤ closT q G D n₀ := by
    unfold closT
    have h_single_le_sum : G c (dirCount D c.succ n₀) ≤
        ∑ c' : Fin 3, G c' (dirCount D c'.succ n₀) :=
      Finset.single_le_sum (fun i _ => @zero_le ℕ∞ _ _ _ (G i (dirCount D i.succ n₀))) (Finset.mem_univ c)
    have h_sum_le_T : ∑ c' : Fin 3, G c' (dirCount D c'.succ n₀) ≤
        (q : ℕ∞) + ∑ c' : Fin 3, G c' (dirCount D c'.succ n₀) :=
      le_add_of_nonneg_left (@zero_le ℕ∞ _ _ _ (q : ℕ∞))
    exact le_trans h_single_le_sum h_sum_le_T
  -- closT q G D n₀ ≤ (n₀ : ℕ∞) from hTn₀
  have h_Tn₀_le_n₀ : closT q G D n₀ ≤ (n₀ : ℕ∞) := hTn₀
  -- Step 5: Relate closN to n₀: closN q G D = (n₀ : ℕ∞)
  have h_closN_eq_n₀ : closN q G D = (n₀ : ℕ∞) := by
    apply le_antisymm
    · -- closN ≤ n₀: since n₀ ∈ S, the infimum is ≤ n₀
      unfold closN
      -- We need: (⨅ n, ⨅ (_ : condition n), (n : ℕ∞)) ≤ (n₀ : ℕ∞)
      -- Using iInf_le with index n₀:
      -- (⨅ n, ...) ≤ (⨅ (_ : condition n₀), (n₀ : ℕ∞))
      -- And since condition n₀ is true, (⨅ (_ : condition n₀), (n₀ : ℕ∞)) = (n₀ : ℕ∞)
      refine le_trans (iInf_le (fun n => ⨅ (_ : q ≤ n ∧ closT q G D n ≤ n), (n : ℕ∞)) n₀) ?_
      simp [hqn₀, hTn₀]
    · -- n₀ ≤ closN: we need (n₀ : ℕ∞) ≤ ⨅ n, ⨅ (_ : condition n), (n : ℕ∞)
      -- Using le_iInf: it suffices to show for all n, (n₀ : ℕ∞) ≤ inner iInf
      refine le_iInf ?_
      intro n
      by_cases h_cond : q ≤ n ∧ closT q G D n ≤ n
      · rcases h_cond with ⟨hqn, hTn⟩
        have hnS : n ∈ S := ⟨hqn, hTn⟩
        have hn₀_le_n : n₀ ≤ n := hn₀_min n hnS
        -- Now (n₀ : ℕ∞) ≤ (n : ℕ∞) = inner iInf (since condition is true)
        have h_cast : (n₀ : ℕ∞) ≤ (n : ℕ∞) := Nat.cast_le.mpr hn₀_le_n
        -- Now we need to show (n₀ : ℕ∞) ≤ ⨅ (_ : condition), (n : ℕ∞)
        -- Since condition is true, this iInf equals (n : ℕ∞)
        simpa [hqn, hTn] using h_cast
      · -- condition false, inner iInf = ⊤, and (n₀ : ℕ∞) ≤ ⊤
        simp [h_cond]
  -- Step 6: Combine everything
  calc
    G c 1 ≤ G c (dirCount D c.succ q) := h_Gc1_le_Gcdq
    _ ≤ G c (dirCount D c.succ n₀) := h_Gcdq_le_Gcdn₀
    _ ≤ closT q G D n₀ := h_Gcdn₀_le_Tn₀
    _ ≤ (n₀ : ℕ∞) := h_Tn₀_le_n₀
    _ = closN q G D := by symm; exact h_closN_eq_n₀
    _ < (x : ℕ∞) := hN

/-- For three i.i.d. curves, `P(G_c(1) < x for every c ∈ S) = P(G(1) < x)^|S|`. -/
theorem pi_forall_lt (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q]
    (S : Finset (Fin 3)) (x : ℕ) :
    ((Measure.pi fun _ : Fin 3 => Q) {G | ∀ c ∈ S, G c 1 < (x : ℕ∞)}).toReal =
      (Q {G | G 1 < (x : ℕ∞)}).toReal ^ S.card := by
  let t : Fin 3 → Set (ℕ → ℕ∞) := fun c => if c ∈ S then {G | G 1 < (x : ℕ∞)} else Set.univ
  have h_set_eq : {G | ∀ c ∈ S, G c 1 < (x : ℕ∞)} = Set.univ.pi t := by
    ext G; simp [t, Set.mem_pi, Set.mem_univ]
  rw [h_set_eq]
  have h_meas : ∀ c : Fin 3, MeasurableSet (t c) := by
    intro c
    dsimp [t]
    split
    · have h_eval_meas : Measurable fun (G : ℕ → ℕ∞) => G 1 := measurable_pi_apply 1
      have h_set_meas : MeasurableSet {y : ℕ∞ | y < (x : ℕ∞)} := MeasurableSet.of_discrete
      exact measurableSet_preimage h_eval_meas h_set_meas
    · exact MeasurableSet.univ
  rw [MeasureTheory.Measure.pi_pi (fun _ : Fin 3 => Q) t]
  have h_prod : (∏ c : Fin 3, Q (t c)) = (Q {G | G 1 < (x : ℕ∞)}) ^ S.card := by
    calc
      (∏ c : Fin 3, Q (t c)) = (∏ c : Fin 3, (if c ∈ S then Q {G | G 1 < (x : ℕ∞)} else Q Set.univ)) := by
        refine Finset.prod_congr rfl fun c hc => ?_
        dsimp [t]
        split <;> rfl
      _ = (∏ c : Fin 3, (if c ∈ S then Q {G | G 1 < (x : ℕ∞)} else 1)) := by
        refine Finset.prod_congr rfl fun c hc => ?_
        split
        · rfl
        · rw [MeasureTheory.IsProbabilityMeasure.measure_univ (μ := Q)]
      _ = (∏ c ∈ S, Q {G | G 1 < (x : ℕ∞)}) := by
        simp [Finset.prod_ite_mem, Finset.prod_const]
      _ = (Q {G | G 1 < (x : ℕ∞)}) ^ S.card := by
        simp [Finset.prod_const]
  rw [h_prod]
  rw [ENNReal.toReal_pow]

/-- The bound of Lemma 11.4 of the paper at `q = 2` is `1 - S(p)` (`1 - χ(p)` in the paper). -/
theorem lemma9Bound_two (p : ℝ) : lemma9Bound 2 p = 1 - SPoly p := by
  unfold lemma9Bound SPoly mult4
  have h_set : (Fintype.piFinset fun _ : Fin 4 => Finset.range 3).filter (fun a => ∑ i : Fin 4, a i = 2) =
    {λ (i : Fin 4) => if i = 0 then 2 else 0,
     λ (i : Fin 4) => if i = 1 then 2 else 0,
     λ (i : Fin 4) => if i = 2 then 2 else 0,
     λ (i : Fin 4) => if i = 3 then 2 else 0,
     λ (i : Fin 4) => if i = 0 then 1 else if i = 1 then 1 else 0,
     λ (i : Fin 4) => if i = 0 then 1 else if i = 2 then 1 else 0,
     λ (i : Fin 4) => if i = 0 then 1 else if i = 3 then 1 else 0,
     λ (i : Fin 4) => if i = 1 then 1 else if i = 2 then 1 else 0,
     λ (i : Fin 4) => if i = 1 then 1 else if i = 3 then 1 else 0,
     λ (i : Fin 4) => if i = 2 then 1 else if i = 3 then 1 else 0} := by
    decide
  rw [h_set]
  -- Expand the Finset sum by repeatedly applying Finset.sum_insert
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  -- Now we have 10 explicit terms
  -- Step 1: Compute the counts (Finset.card of Finset.univ.filter)
  -- These are still Finset.card at this point (displayed as set notation)
  have h_count1 : ({c : Fin 3 | 1 ≤ (λ (i : Fin 4) => if i = 0 then 2 else 0) c.succ} : Finset (Fin 3)).card = 0 := by
    decide
  have h_count2 : ({c : Fin 3 | 1 ≤ (λ (i : Fin 4) => if i = 1 then 2 else 0) c.succ} : Finset (Fin 3)).card = 1 := by
    decide
  have h_count3 : ({c : Fin 3 | 1 ≤ (λ (i : Fin 4) => if i = 2 then 2 else 0) c.succ} : Finset (Fin 3)).card = 1 := by
    decide
  have h_count4 : ({c : Fin 3 | 1 ≤ (λ (i : Fin 4) => if i = 3 then 2 else 0) c.succ} : Finset (Fin 3)).card = 1 := by
    decide
  have h_count5 : ({c : Fin 3 | 1 ≤ (λ (i : Fin 4) => if i = 0 then 1 else if i = 1 then 1 else 0) c.succ} : Finset (Fin 3)).card = 1 := by
    decide
  have h_count6 : ({c : Fin 3 | 1 ≤ (λ (i : Fin 4) => if i = 0 then 1 else if i = 2 then 1 else 0) c.succ} : Finset (Fin 3)).card = 1 := by
    decide
  have h_count7 : ({c : Fin 3 | 1 ≤ (λ (i : Fin 4) => if i = 0 then 1 else if i = 3 then 1 else 0) c.succ} : Finset (Fin 3)).card = 1 := by
    decide
  have h_count8 : ({c : Fin 3 | 1 ≤ (λ (i : Fin 4) => if i = 1 then 1 else if i = 2 then 1 else 0) c.succ} : Finset (Fin 3)).card = 2 := by
    decide
  have h_count9 : ({c : Fin 3 | 1 ≤ (λ (i : Fin 4) => if i = 1 then 1 else if i = 3 then 1 else 0) c.succ} : Finset (Fin 3)).card = 2 := by
    decide
  have h_count10 : ({c : Fin 3 | 1 ≤ (λ (i : Fin 4) => if i = 2 then 1 else if i = 3 then 1 else 0) c.succ} : Finset (Fin 3)).card = 2 := by
    decide
  rw [h_count1, h_count2, h_count3, h_count4, h_count5, h_count6, h_count7, h_count8, h_count9, h_count10]
  -- Step 2: Simplify the if expressions in the factorials using Fin inequalities
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h10 : (1 : Fin 4) ≠ 0 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  have h32 : (3 : Fin 4) ≠ 2 := by decide
  simp [h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32]
  -- Step 3: Simplify (4^2)⁻¹ and 2/4^2
  norm_num
  -- Step 4: Expand both sides with ring
  ring

/-- The probability computed in the proof of Lemma 11.4 of the paper: every child entered among the
first `q` directions has `G_c(1) < x`. -/
theorem lemma9_prod (Q : Measure (ℕ → ℕ∞)) [IsProbabilityMeasure Q] (q x : ℕ) :
    (closMeasure Q {y | ∀ c : Fin 3, 1 ≤ dirCount y.2 c.succ q → y.1 c 1 < (x : ℕ∞)}).toReal =
      lemma9Bound q (1 - (Q {G | G 1 < (x : ℕ∞)}).toReal) := by
  set r := (Q {G | G 1 < (x : ℕ∞)}).toReal with hr
  let A := (Fintype.piFinset fun _ : Fin 4 => Finset.range (q + 1)).filter (fun a => ∑ i, a i = q)
  let D_set (a : Fin 4 → ℕ) : Set (ℕ → Fin 4) := {D | ∀ i, dirCount D i q = a i}
  let G_set (a : Fin 4 → ℕ) : Set (Fin 3 → ℕ → ℕ∞) := {G | ∀ c : Fin 3, 1 ≤ a c.succ → G c 1 < (x : ℕ∞)}
  let E : Set ((Fin 3 → ℕ → ℕ∞) × (ℕ → Fin 4)) := {y | ∀ c : Fin 3, 1 ≤ dirCount y.2 c.succ q → y.1 c 1 < (x : ℕ∞)}
  have h_clos_eq : closMeasure Q = ((Measure.pi fun _ : Fin 3 => Q).prod dirMeasure) := rfl
  -- Provide missing instances
  have : IsProbabilityMeasure dirMeasure := by
    dsimp [dirMeasure]
    infer_instance
  have : SFinite dirMeasure := by
    have : SigmaFinite dirMeasure := inferInstance
    infer_instance
  have : IsProbabilityMeasure ((Measure.pi fun _ : Fin 3 => Q).prod dirMeasure) := by
    infer_instance
  -- each a ∈ A has sum q
  have hA_sum (a : Fin 4 → ℕ) (ha : a ∈ A) : ∑ i : Fin 4, a i = q := by
    have := (Finset.mem_filter.mp ha).2
    simpa [A] using this
  -- D_set a is measurable
  have hD_measurable (a : Fin 4 → ℕ) : MeasurableSet (D_set a) := by
    have : D_set a = ⋂ i : Fin 4, {D | dirCount D i q = a i} := by
      ext D; simp [D_set]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    -- dirCount D i q is a measurable function to ℕ (discrete σ-algebra)
    have h_dirCount_meas : Measurable (fun (D : ℕ → Fin 4) => dirCount D i q) := by
      dsimp [dirCount]
      -- dirCount D i q = ((range q).filter fun j => D j = i).card
      -- = ∑ j ∈ range q, (if D j = i then 1 else 0)
      have h_eq : (fun (D : ℕ → Fin 4) => ((Finset.range q).filter fun j => D j = i).card) =
          (fun D => ∑ j ∈ Finset.range q, if D j = i then (1 : ℕ) else 0) := by
        ext D; rw [Finset.card_filter]
      rw [h_eq]
      refine Finset.measurable_sum _ (fun j hj => ?_)
      -- fun D => (if D j = i then 1 else 0) is the indicator of {D | D j = i}
      have h_set : MeasurableSet {D : ℕ → Fin 4 | D j = i} := by
        have h_proj : Measurable (fun (D : ℕ → Fin 4) => D j) := measurable_pi_apply j
        exact measurableSet_preimage h_proj (MeasurableSet.singleton i)
      -- indicator of measurable set with constant 1 is measurable
      let s : Set (ℕ → Fin 4) := {D | D j = i}
      have h_eq : (fun D => if D j = i then (1 : ℕ) else 0) = s.indicator (fun _ => (1 : ℕ)) := by
        ext D; simp [s, Set.indicator]
      rw [h_eq]
      exact Measurable.indicator measurable_const h_set
    -- {D | dirCount D i q = a i} = (dirCount · i q)⁻¹' {a i}
    have h_singleton : MeasurableSet ({a i} : Set ℕ) := MeasurableSet.singleton _
    exact measurableSet_preimage h_dirCount_meas h_singleton
  -- G_set a is measurable
  have hG_measurable (a : Fin 4 → ℕ) : MeasurableSet (G_set a) := by
    -- G_set a = ⋂ c, {G | 1 ≤ a c.succ → G c 1 < x}
    -- For each c, if 1 ≤ a c.succ, the set is {G | G c 1 < x}; otherwise it's univ
    have h_eq : G_set a = ⋂ c : Fin 3, {G : Fin 3 → ℕ → ℕ∞ | 1 ≤ a c.succ → G c 1 < (x : ℕ∞)} := by
      ext G; simp [G_set]
    rw [h_eq]
    refine MeasurableSet.iInter fun c => ?_
    by_cases hc : 1 ≤ a c.succ
    · -- set is {G | G c 1 < x}
      have h_set : {G : Fin 3 → ℕ → ℕ∞ | 1 ≤ a c.succ → G c 1 < (x : ℕ∞)} = {G | G c 1 < (x : ℕ∞)} := by
        ext G; simp [hc]
      rw [h_set]
      -- G c 1 is measurable: G ↦ G c is measurable (measurable_pi_apply c), then evaluation at 1
      have h_eval : Measurable (fun (G : Fin 3 → ℕ → ℕ∞) => G c 1) :=
        (measurable_pi_apply (1 : ℕ)).comp (measurable_pi_apply c)
      -- {G | G c 1 < x} = (fun G => G c 1)⁻¹' {y | y < x}
      -- {y : ℕ∞ | y < (x : ℕ∞)} is measurable by measurableSet_lt
      have h_lt_set : MeasurableSet {y : ℕ∞ | y < (x : ℕ∞)} := by
        simp
      exact measurableSet_preimage h_eval h_lt_set
    · -- set is univ (vacuously true)
      have h_set : {G : Fin 3 → ℕ → ℕ∞ | 1 ≤ a c.succ → G c 1 < (x : ℕ∞)} = Set.univ := by
        ext G; simp [hc]
      rw [h_set]
      exact MeasurableSet.univ
  -- the event equals the disjoint union
  have h_union : E = ⋃ a ∈ A, (G_set a ×ˢ D_set a) := by
    ext ⟨G, D⟩
    constructor
    · intro h
      let a := fun i : Fin 4 => dirCount D i q
      have ha_range : ∀ i, a i ∈ Finset.range (q + 1) := by
        intro i
        have hle : dirCount D i q ≤ q := by
          dsimp [dirCount]
          calc
            ((Finset.range q).filter fun j => D j = i).card ≤ (Finset.range q).card :=
              Finset.card_filter_le _ _
            _ = q := Finset.card_range q
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
      have ha_sum : ∑ i : Fin 4, a i = q := by
        dsimp [a, dirCount]
        simp_rw [Finset.card_filter]
        rw [Finset.sum_comm]
        simp [Finset.sum_ite_eq]
      have ha_mem : a ∈ A := by
        refine Finset.mem_filter.mpr ⟨?_, ha_sum⟩
        refine Fintype.mem_piFinset.mpr fun i => ?_
        exact ha_range i
      -- (G, D) ∈ G_set a ×ˢ D_set a
      have h_mem_prod : (G, D) ∈ G_set a ×ˢ D_set a := by
        constructor
        · intro c hc
          have hc' : 1 ≤ dirCount D c.succ q := by
            simpa [a] using hc
          exact h c hc'
        · intro i
          simp [a]
      -- Now (G, D) ∈ ⋃ a ∈ A, (G_set a ×ˢ D_set a)
      refine Set.mem_iUnion₂.mpr ⟨a, ha_mem, h_mem_prod⟩
    · intro h
      rcases Set.mem_iUnion₂.mp h with ⟨a, ha_mem, hGD⟩
      rcases hGD with ⟨hG, hD⟩
      intro c hc
      have ha_c : 1 ≤ a c.succ := by
        rw [← hD c.succ]
        exact hc
      exact hG c ha_c
  -- pairwise disjoint
  have h_disjoint : Set.PairwiseDisjoint (↑A) (fun a => G_set a ×ˢ D_set a) := by
    intro a ha a' ha' hne
    have h_diff : ∃ i, a i ≠ a' i := by
      contrapose! hne
      ext i; exact hne i
    rcases h_diff with ⟨i, hi⟩
    -- Show that the intersection is empty, which implies disjointness
    have h_empty : (G_set a ×ˢ D_set a) ∩ (G_set a' ×ˢ D_set a') = ∅ := by
      ext ⟨G, D⟩
      constructor
      · intro h
        rcases h with ⟨⟨hG, hD⟩, ⟨hG', hD'⟩⟩
        -- hD : D ∈ D_set a, so ∀ i, dirCount D i q = a i
        -- hD' : D ∈ D_set a', so ∀ i, dirCount D i q = a' i
        -- So a i = a' i, contradiction
        have h_eq_i : a i = a' i := by
          rw [← hD i, ← hD' i]
        exact absurd h_eq_i hi
      · intro h
        simp at h
    -- Now convert to Disjoint; note that Function.onFun Disjoint f a a' = Disjoint (f a) (f a')
    simpa [Set.disjoint_iff_inter_eq_empty] using h_empty
  -- apply measure_biUnion_finset
  have h_measure_ennreal : (closMeasure Q) E = ∑ a ∈ A, (closMeasure Q) (G_set a ×ˢ D_set a) := by
    rw [h_union]
    refine measure_biUnion_finset h_disjoint (fun a ha => ?_)
    exact (hG_measurable a).prod (hD_measurable a)
  -- convert to ℝ
  have h_measure_real : ((closMeasure Q) E).toReal = ∑ a ∈ A, ((closMeasure Q) (G_set a ×ˢ D_set a)).toReal := by
    rw [h_measure_ennreal]
    refine ENNReal.toReal_sum fun a ha => ?_
    -- need to show (closMeasure Q) (G_set a ×ˢ D_set a) ≠ ⊤
    -- closMeasure Q is a probability measure, so ≤ 1 < ⊤
    have h_le : (closMeasure Q) (G_set a ×ˢ D_set a) ≤ 1 := by
      have : IsProbabilityMeasure (closMeasure Q) := by
        rw [h_clos_eq]
        infer_instance
      calc
        (closMeasure Q) (G_set a ×ˢ D_set a) ≤ (closMeasure Q) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    -- Since ≤ 1 < ⊤, it's not ⊤
    exact lt_of_le_of_lt h_le (by norm_num : (1 : ENNReal) < ⊤) |>.ne
  -- compute each term
  have h_term (a : Fin 4 → ℕ) (ha : a ∈ A) :
      ((closMeasure Q) (G_set a ×ˢ D_set a)).toReal =
      mult4 q (a 0) (a 1) (a 2) (a 3) * r ^ (Finset.univ.filter fun c : Fin 3 => 1 ≤ a c.succ).card := by
    rw [h_clos_eq, MeasureTheory.Measure.prod_prod (s := G_set a) (t := D_set a)]
    rw [ENNReal.toReal_mul]
    have h_dir : (dirMeasure (D_set a)).toReal = mult4 q (a 0) (a 1) (a 2) (a 3) := by
      have ha_sum := hA_sum a ha
      have h_set : D_set a = {D | ∀ i, dirCount D i q = a i} := rfl
      simpa [h_set] using dirMeasure_counts q a ha_sum
    have h_pi : ((Measure.pi fun _ : Fin 3 => Q) (G_set a)).toReal =
        r ^ (Finset.univ.filter fun c : Fin 3 => 1 ≤ a c.succ).card := by
      let S := Finset.univ.filter fun c : Fin 3 => 1 ≤ a c.succ
      have h_set : G_set a = {G | ∀ c ∈ S, G c 1 < (x : ℕ∞)} := by
        ext G; simp [G_set, S]
      rw [h_set]
      simpa [hr] using pi_forall_lt Q S x
    rw [h_pi, h_dir]
    ring
  -- sum both sides
  rw [h_measure_real]
  -- Use h_term to rewrite each term in the sum
  rw [Finset.sum_congr rfl (fun a ha => h_term a ha)]
  -- Now relate the sum to lemma9Bound
  unfold lemma9Bound
  -- lemma9Bound q (1 - r) = ∑ a ∈ A, mult4 q (a 0) (a 1) (a 2) (a 3) * (1 - (1 - r)) ^ ...
  -- = ∑ a ∈ A, mult4 q (a 0) (a 1) (a 2) (a 3) * r ^ ...
  -- So we need to show the sum matches
  apply Finset.sum_congr rfl fun a ha => ?_
  have h_eq : (1 - (1 - r)) = r := by ring
  rw [h_eq]

/-- `P(G_m(1) ≥ x) = 1 - P(G(1) < x)` under the curve law. -/
theorem tailG_eq (hmeas : measurable_plantedPair) (m k x : ℕ) :
    tailG m k x = 1 - (curveLaw m {G | G k < (x : ℕ∞)}).toReal := by
  have hk : Measurable fun G : ℕ → ℕ∞ => G k := measurable_pi_apply k
  have hs : MeasurableSet {G : ℕ → ℕ∞ | G k < (x : ℕ∞)} :=
    hk (MeasurableSet.of_discrete (s := {y : ℕ∞ | y < (x : ℕ∞)}))
  have hc : {G : ℕ → ℕ∞ | (x : ℕ∞) ≤ G k} = {G : ℕ → ℕ∞ | G k < (x : ℕ∞)}ᶜ := by
    ext G; simp
  have h1 : tailG m k x = (curveLaw m {G : ℕ → ℕ∞ | (x : ℕ∞) ≤ G k}).toReal := by
    unfold tailG curveLaw
    rw [Measure.map_apply (hmeas m).fst (by rw [hc]; exact hs.compl)]
    rfl
  rw [h1, hc, prob_compl_eq_one_sub hs, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one]

/-- **Lemma 11.4 of the paper** from the measurability statement. -/
theorem lemma9_of (hmeas : measurable_plantedPair) : lemma9 := by
  intro m q x hq hx
  have hgood := ae_closGood (curveLaw m) _ (ae_goodC hmeas m)
  unfold closProb
  rw [tailG_eq hmeas, ← lemma9_prod (curveLaw m) q x]
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (hgood.mono fun y hy => ?_))
  intro hN c hc
  exact lemma9_incl q x y.1 y.2 (fun c => (hy c).1) hN c hc

/-- **Lemma 11.4 of the paper at `q = 2`** from the general case. -/
theorem lemma9_two_of (h9 : lemma9) : lemma9_two := fun m x hx =>
  (h9 m 2 x le_rfl hx).trans_eq (lemma9Bound_two _)

end FrogModel.D3.Iface
