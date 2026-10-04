module

public import FrogModel.D3.M1L.GenDefs

@[expose] public section

/-!
# M1_L at every height: the identities of the recursion `Gen`

The equation of a round, linearity in the additive term and the end value, nonnegativity, total
mass one, lumping of an H closure by its count of unmarked children, and the support of an H
closure (the recursion of Section 13 of the paper and the proof of Lemma 13.2).
-/

namespace FrogModel.D3

theorem rankK_update_none (k : Kid) (c : Fin 3) (f : Fin 4) (hc : k c = none) :
    rankK (Function.update k c (some f)) < rankK k :=
  rankK_update_lt k c (some f) (by rw [hc]; simp only [krank]; exact f.isLt)

theorem rankK_update_some (k : Kid) (c : Fin 3) (t f : Fin 4) (hc : k c = some t)
    (hf : f < t) : rankK (Function.update k c (some f)) < rankK k :=
  rankK_update_lt k c (some f) (by rw [hc]; simp only [krank]; exact hf)

/-- Marking an unmarked child lowers the count of unmarked children by one. -/
theorem nN_update_none (k : Kid) (c : Fin 3) (f : Fin 4) (hc : k c = none) :
    nN (Function.update k c (some f)) + 1 = nN k := by
  unfold FrogModel.D3.nN
  have hmem : c ∈ Finset.univ.filter fun c' => k c' = none := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hc⟩
  have heq : (Finset.univ.filter fun c' => Function.update k c (some f) c' = none) =
      (Finset.univ.filter fun c' => k c' = none).erase c := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hx_univ, hx_eq⟩
      apply Finset.mem_erase.mpr
      constructor
      · intro h_eq
        rw [h_eq, Function.update_apply] at hx_eq
        simp at hx_eq
      · apply Finset.mem_filter.mpr
        constructor
        · exact hx_univ
        · by_cases hx_c : x = c
          · exfalso
            rw [hx_c, Function.update_apply] at hx_eq
            simp at hx_eq
          · rw [Function.update_apply, ite_eq_right hx_c] at hx_eq
            exact hx_eq
    · intro hx
      rcases Finset.mem_erase.mp hx with ⟨hx_ne, hx_mem⟩
      rcases Finset.mem_filter.mp hx_mem with ⟨hx_univ, hx_eq⟩
      apply Finset.mem_filter.mpr
      constructor
      · exact hx_univ
      · rw [Function.update_apply]
        split
        · exfalso; exact hx_ne ‹_›
        · exact hx_eq
  rw [heq]
  rw [Finset.card_erase_of_mem hmem]
  have hpos : 0 < (Finset.univ.filter fun c' => k c' = none).card :=
    Finset.card_pos.mpr ⟨c, hmem⟩
  omega

/-- Changing the type of a marked child keeps the count of unmarked children. -/
theorem nN_update_some (k : Kid) (c : Fin 3) (x : Option (Fin 4)) (hc : k c ≠ none)
    (hx : x ≠ none) : nN (Function.update k c x) = nN k := by
  unfold FrogModel.D3.nN
  congr 1
  apply Finset.filter_congr
  intro c'
  by_cases h : c' = c
  · subst h
    simp [hc, hx]
  · simp [h]

/-- A sum over the three children, equal on the unmarked ones. -/
theorem sum_kid (k : Kid) (F : Fin 3 → ℝ) (G A : ℝ) (hF : ∀ c, k c = none → F c = A) :
    ∑ c, (match k c with | none => F c | some _ => G) = (nN k : ℝ) * A + (3 - (nN k : ℝ)) * G := by
  rcases h0 : k 0 with (none | t0)
  · rcases h1 : k 1 with (none | t1)
    · rcases h2 : k 2 with (none | t2)
      · have hnN : FrogModel.D3.nN k = 3 := by
          unfold FrogModel.D3.nN; rw [Finset.card_filter, Fin.sum_univ_three]; simp [h0, h1, h2]
        simp [Fin.sum_univ_three, h0, h1, h2, hnN, hF]
        ring
      · have hnN : FrogModel.D3.nN k = 2 := by
          unfold FrogModel.D3.nN; rw [Finset.card_filter, Fin.sum_univ_three]; simp [h0, h1, h2]
        simp [Fin.sum_univ_three, h0, h1, h2, hnN, hF]
        ring
    · rcases h2 : k 2 with (none | t2)
      · have hnN : FrogModel.D3.nN k = 2 := by
          unfold FrogModel.D3.nN; rw [Finset.card_filter, Fin.sum_univ_three]; simp [h0, h1, h2]
        simp [Fin.sum_univ_three, h0, h1, h2, hnN, hF]
        ring
      · have hnN : FrogModel.D3.nN k = 1 := by
          unfold FrogModel.D3.nN; rw [Finset.card_filter, Fin.sum_univ_three]; simp [h0, h1, h2]
        simp [Fin.sum_univ_three, h0, h1, h2, hnN, hF]
        ring
  · rcases h1 : k 1 with (none | t1)
    · rcases h2 : k 2 with (none | t2)
      · have hnN : FrogModel.D3.nN k = 2 := by
          unfold FrogModel.D3.nN; rw [Finset.card_filter, Fin.sum_univ_three]; simp [h0, h1, h2]
        simp [Fin.sum_univ_three, h0, h1, h2, hnN, hF]
        ring
      · have hnN : FrogModel.D3.nN k = 1 := by
          unfold FrogModel.D3.nN; rw [Finset.card_filter, Fin.sum_univ_three]; simp [h0, h1, h2]
        simp [Fin.sum_univ_three, h0, h1, h2, hnN, hF]
        ring
    · rcases h2 : k 2 with (none | t2)
      · have hnN : FrogModel.D3.nN k = 1 := by
          unfold FrogModel.D3.nN; rw [Finset.card_filter, Fin.sum_univ_three]; simp [h0, h1, h2]
        simp [Fin.sum_univ_three, h0, h1, h2, hnN, hF]
        ring
      · have hnN : FrogModel.D3.nN k = 0 := by
          unfold FrogModel.D3.nN; rw [Finset.card_filter, Fin.sum_univ_three]; simp [h0, h1, h2]
        simp [Fin.sum_univ_three, h0, h1, h2, hnN]
        ring

/-- The loop of an H closure: `(3 - nN) pL / 4`. -/
theorem loopK_H (pL : ℝ) (K : ℕ → ℕ → ℕ → ℝ) (k : Kid) :
    loopK false pL K k = (3 - (nN k : ℝ)) * pL / 4 := by
  unfold FrogModel.D3.loopK FrogModel.D3.nN
  simp_rw [Bool.false_eq_true, ite_false]
  calc
    (∑ x : Fin 3, match k x with
      | none => (0 : ℝ)
      | some _ => 1/4 * pL)
        = (∑ x : Fin 3, if k x = none then (0 : ℝ) else 1/4 * pL) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      cases k x <;> simp
    _ = (∑ x with k x = none, (0 : ℝ)) + (∑ x with ¬ k x = none, 1/4 * pL) := by rw [Finset.sum_ite]
    _ = 0 + ((Finset.univ.filter fun x => k x ≠ none).card : ℝ) * (1/4 * pL) := by
      simp [Finset.sum_const]
    _ = ((Finset.univ.filter fun x => k x ≠ none).card : ℝ) * (1/4 * pL) := by simp
    _ = ((Finset.univ.filter fun x => k x ≠ none).card : ℝ) * pL / 4 := by ring
    _ = ((3 : ℝ) - ((Finset.univ.filter fun x => k x = none).card : ℝ)) * pL / 4 := by
      have hcard := Finset.card_filter_add_card_filter_not (fun c : Fin 3 => k c = none) (s := Finset.univ)
      have hcard_univ_nat : (Finset.univ : Finset (Fin 3)).card = 3 := by norm_num
      have h_eq : {a ∈ (Finset.univ : Finset (Fin 3)) | ¬ k a = none} = Finset.univ.filter fun x => k x ≠ none := by
        ext x; simp
      rw [h_eq] at hcard
      rw [hcard_univ_nat] at hcard
      -- hcard : card(filter (k c = none)) + card(filter (k c ≠ none)) = 3
      have hcard_compl : ((Finset.univ.filter fun x => k x ≠ none).card : ℝ) = (3 : ℝ) - ((Finset.univ.filter fun x => k x = none).card : ℝ) := by
        have hcard' := congrArg (fun n : ℕ => (n : ℝ)) hcard
        rw [Nat.cast_add] at hcard'
        have hcard'' : ((Finset.univ.filter fun x => k x ≠ none).card : ℝ) + ((Finset.univ.filter fun x => k x = none).card : ℝ) = (3 : ℝ) := by
          rw [add_comm]
          exact hcard'
        exact eq_sub_of_add_eq hcard''
      rw [hcard_compl]

/-- The loop probability is in [0, 3/4]. -/
theorem loopK_bounds (isR : Bool) (pL : ℝ) (K : ℕ → ℕ → ℕ → ℝ) (hp0 : 0 ≤ pL) (hp1 : pL ≤ 1)
    (hK0 : ∀ t : ℕ, 0 ≤ K t 1 t) (hK1 : ∀ t : ℕ, K t 1 t ≤ 1) (k : Kid) :
    0 ≤ loopK isR pL K k ∧ loopK isR pL K k ≤ 3 / 4 := by
  unfold FrogModel.D3.loopK
  have hterm : ∀ (x : Option (Fin 4)),
    0 ≤ (match x with
      | none => 0
      | some t => 1 / 4 * (if isR then K t 1 t else pL)) ∧
    (match x with
      | none => 0
      | some t => 1 / 4 * (if isR then K t 1 t else pL)) ≤ 1 / 4 := by
    intro x
    cases x with
    | none =>
      constructor <;> norm_num
    | some t =>
      dsimp
      constructor
      · by_cases hisR : isR
        · rw [ite_eq_left hisR]
          apply mul_nonneg (by norm_num) (hK0 t)
        · rw [ite_eq_right hisR]
          apply mul_nonneg (by norm_num) hp0
      · by_cases hisR : isR
        · rw [ite_eq_left hisR]
          nlinarith [hK1 t]
        · rw [ite_eq_right hisR]
          nlinarith
  rw [Fin.sum_univ_three]
  have h0 := hterm (k 0)
  have h1 := hterm (k 1)
  have h2 := hterm (k 2)
  rcases h0 with ⟨h0l, h0u⟩
  rcases h1 with ⟨h1l, h1u⟩
  rcases h2 with ⟨h2l, h2u⟩
  constructor
  · -- 0 ≤ term0 + term1 + term2
    have h01 : 0 ≤ (match k 0 with
      | none => 0
      | some t => 1 / 4 * (if isR then K t 1 t else pL)) +
      (match k 1 with
        | none => 0
        | some t => 1 / 4 * (if isR then K t 1 t else pL)) :=
      add_nonneg h0l h1l
    exact add_nonneg h01 h2l
  · -- term0 + term1 + term2 ≤ 3/4
    have hsum := add_le_add (add_le_add h0u h1u) h2u
    calc
      (match k 0 with
        | none => 0
        | some t => 1 / 4 * (if isR then K t 1 t else pL)) +
      (match k 1 with
        | none => 0
        | some t => 1 / 4 * (if isR then K t 1 t else pL)) +
      (match k 2 with
        | none => 0
        | some t => 1 / 4 * (if isR then K t 1 t else pL))
      ≤ (1/4 : ℝ) + 1/4 + 1/4 := hsum
      _ = 3/4 := by norm_num

/-- The value of a closure with an empty pool is its end value. -/
theorem Gen_zero (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (add : Kid → ℝ) (term : Kid → ℕ → ℝ) (k : Kid) (a : ℕ) :
    Gen V P isR pL ρ K add term k 0 a = term k a := by
  unfold FrogModel.D3.Gen
  simp

/-- One round of a closure, with the loop solved out. -/
theorem Gen_step (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (add : Kid → ℝ) (term : Kid → ℕ → ℝ) (k : Kid) (n a : ℕ)
    (hn : n ≠ 0) :
    Gen V P isR pL ρ K add term k n a =
      (add k + 1 / 4 * Gen V P isR pL ρ K add term k (n - 1) (upA V a) +
        ∑ c, 1 / 4 * bodyG V P isR pL ρ K (Gen V P isR pL ρ K add term) k n a c) /
      (1 - loopK isR pL K k) := by
  rw [FrogModel.D3.Gen]
  simp only [dite_eq_right hn]
  congr 1
  -- Both numerators have the form: add k + 1/4 * Gen ... + ∑ c, 1/4 * ...
  -- We need to show the sum parts are equal
  simp only [FrogModel.D3.bodyG]
  refine congrArg (fun s => add k + 1 / 4 * FrogModel.D3.Gen V P isR pL ρ K add term k (n - 1) (FrogModel.D3.upA V a) + s) ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  match k c with
  | none => rfl
  | some t => rfl

/-- One round of a closure, the loop on the right. -/
theorem Gen_eq (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (add : Kid → ℝ) (term : Kid → ℕ → ℝ) (hp0 : 0 ≤ pL) (hp1 : pL ≤ 1)
    (hK0 : ∀ t : ℕ, 0 ≤ K t 1 t) (hK1 : ∀ t : ℕ, K t 1 t ≤ 1) (k : Kid) (n a : ℕ)
    (hn : n ≠ 0) :
    Gen V P isR pL ρ K add term k n a =
      add k + 1 / 4 * Gen V P isR pL ρ K add term k (n - 1) (upA V a) +
        ∑ c, 1 / 4 * bodyG V P isR pL ρ K (Gen V P isR pL ρ K add term) k n a c +
        loopK isR pL K k * Gen V P isR pL ρ K add term k n a := by
  have hbounds := FrogModel.D3.loopK_bounds isR pL K hp0 hp1 hK0 hK1 k
  rcases hbounds with ⟨hlo, hhi⟩
  have hne : 1 - FrogModel.D3.loopK isR pL K k ≠ 0 := by linarith
  set X := FrogModel.D3.Gen V P isR pL ρ K add term k n a
  set A := add k + 1 / 4 * FrogModel.D3.Gen V P isR pL ρ K add term k (n - 1) (FrogModel.D3.upA V a) +
        ∑ c, 1 / 4 * FrogModel.D3.bodyG V P isR pL ρ K (FrogModel.D3.Gen V P isR pL ρ K add term) k n a c
  set l := FrogModel.D3.loopK isR pL K k
  have hstep := FrogModel.D3.Gen_step V P isR pL ρ K add term k n a hn
  have hmul : X * (1 - l) = A := by
    dsimp [X, A, l]
    rw [hstep]
    exact div_mul_cancel₀ _ hne
  linarith

/-- `bodyG` reads its value function below `(k, n)` only. -/
theorem bodyG_congr (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (X Y : Kid → ℕ → ℕ → ℝ) (k : Kid) (n a : ℕ) (c : Fin 3)
    (h1 : X k (n - 1) a = Y k (n - 1) a)
    (h2 : ∀ k', rankK k' < rankK k → ∀ n', X k' n' a = Y k' n' a) :
    bodyG V P isR pL ρ K X k n a c = bodyG V P isR pL ρ K Y k n a c := by
  unfold bodyG
  cases hk : k c with
  | none =>
    simp only
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun b _ => ?_
    rw [h2 _ (rankK_update_none k c f hk)]
  | some t =>
    simp only
    rw [h1]
    congr 2
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with hf
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [h2 _ (rankK_update_some k c t f hk hf)]
    · rfl

theorem bodyG_add (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (X Y : Kid → ℕ → ℕ → ℝ) (k : Kid) (n a : ℕ) (c : Fin 3) :
    bodyG V P isR pL ρ K (fun k n a => X k n a + Y k n a) k n a c =
      bodyG V P isR pL ρ K X k n a c + bodyG V P isR pL ρ K Y k n a c := by
  unfold bodyG
  cases k c with
  | none =>
    simp only [mul_add, Finset.sum_add_distrib]
  | some t =>
    cases isR
    · simp only [Bool.false_eq_true, ite_false]; ring
    · simp only [ite_true, mul_add, Finset.sum_add_distrib]
      have : ∀ f : Fin 4, (if f < t then (∑ a' ∈ Finset.range (V + 1),
          K (↑t) a' (↑f) * X (Function.update k c (some f)) (min (n - 1 + a') P) a) + ∑ a' ∈ Finset.range (V + 1),
            K (↑t) a' (↑f) * Y (Function.update k c (some f)) (min (n - 1 + a') P) a else 0) =
          (if f < t then ∑ a' ∈ Finset.range (V + 1),
            K (↑t) a' (↑f) * X (Function.update k c (some f)) (min (n - 1 + a') P) a else 0) +
          (if f < t then ∑ a' ∈ Finset.range (V + 1),
            K (↑t) a' (↑f) * Y (Function.update k c (some f)) (min (n - 1 + a') P) a else 0) := by
        intro f; split_ifs <;> simp
      rw [Finset.sum_congr rfl fun f _ => this f, Finset.sum_add_distrib]
      ring

theorem bodyG_smul (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (X : Kid → ℕ → ℕ → ℝ) (r : ℝ) (k : Kid) (n a : ℕ) (c : Fin 3) :
    bodyG V P isR pL ρ K (fun k n a => r * X k n a) k n a c =
      r * bodyG V P isR pL ρ K X k n a c := by
  unfold bodyG
  cases k c with
  | none =>
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun b _ => by ring
  | some t =>
    cases isR
    · simp only [Bool.false_eq_true, ite_false]; ring
    · simp only [ite_true, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun f _ => ?_
        split_ifs
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
        · simp

/-- `Gen` is additive in its additive term and end value together. -/
theorem Gen_add (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (add1 add2 : Kid → ℝ) (t1 t2 : Kid → ℕ → ℝ) (k : Kid) (n a : ℕ) :
    Gen V P isR pL ρ K (fun k => add1 k + add2 k) (fun k a => t1 k a + t2 k a) k n a =
      Gen V P isR pL ρ K add1 t1 k n a + Gen V P isR pL ρ K add2 t2 k n a := by
  induction h : rankK k using Nat.strong_induction_on generalizing k n a with
  | h m IH =>
    induction n generalizing a with
    | zero => simp only [Gen_zero]
    | succ n IHn =>
      rw [Gen_step _ _ _ _ _ _ _ _ k _ _ (Nat.succ_ne_zero n),
        Gen_step _ _ _ _ _ _ _ _ k _ _ (Nat.succ_ne_zero n),
        Gen_step _ _ _ _ _ _ _ _ k _ _ (Nat.succ_ne_zero n), ← add_div]
      congr 1
      have hb : ∀ c, bodyG V P isR pL ρ K
          (Gen V P isR pL ρ K (fun k => add1 k + add2 k) (fun k a => t1 k a + t2 k a)) k (n + 1) a c =
          bodyG V P isR pL ρ K (Gen V P isR pL ρ K add1 t1) k (n + 1) a c +
            bodyG V P isR pL ρ K (Gen V P isR pL ρ K add2 t2) k (n + 1) a c := by
        intro c
        rw [← bodyG_add]
        exact bodyG_congr _ _ _ _ _ _ _ _ _ _ _ _ (IHn a)
          (fun k' hk' n' => IH _ (h ▸ hk') k' n' a rfl)
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, hb, IHn (upA V a), mul_add, Finset.sum_add_distrib]
      ring

/-- `Gen` is homogeneous in its additive term and end value together. -/
theorem Gen_smul (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (add : Kid → ℝ) (term : Kid → ℕ → ℝ) (r : ℝ) (k : Kid) (n a : ℕ) :
    Gen V P isR pL ρ K (fun k => r * add k) (fun k a => r * term k a) k n a =
      r * Gen V P isR pL ρ K add term k n a := by
  induction h : rankK k using Nat.strong_induction_on generalizing k n a with
  | h m IH =>
    induction n generalizing a with
    | zero => simp only [Gen_zero]
    | succ n IHn =>
      rw [Gen_step _ _ _ _ _ _ _ _ k _ _ (Nat.succ_ne_zero n),
        Gen_step _ _ _ _ _ _ _ _ k _ _ (Nat.succ_ne_zero n), mul_div_assoc']
      congr 1
      have hb : ∀ c, bodyG V P isR pL ρ K
          (Gen V P isR pL ρ K (fun k => r * add k) (fun k a => r * term k a)) k (n + 1) a c =
          r * bodyG V P isR pL ρ K (Gen V P isR pL ρ K add term) k (n + 1) a c := by
        intro c
        rw [← bodyG_smul]
        exact bodyG_congr _ _ _ _ _ _ _ _ _ _ _ _ (IHn a)
          (fun k' hk' n' => IH _ (h ▸ hk') k' n' a rfl)
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, hb, IHn (upA V a), mul_add, Finset.mul_sum]
      ring_nf
/-- With additive term and end value `0`, `Gen` is `0`. -/
theorem Gen_zero_zero (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (k : Kid) (n a : ℕ) :
    Gen V P isR pL ρ K (fun _ => 0) (fun _ _ => 0) k n a = 0 := by
  have h := FrogModel.D3.Gen_smul V P isR pL ρ K (fun _ => 0) (fun _ _ => 0) 0 k n a
  simpa [zero_mul] using h

/-- `Gen` of a finite sum of additive terms and end values. -/
theorem Gen_sum (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) {ι : Type} [DecidableEq ι] (s : Finset ι)
    (add : ι → Kid → ℝ) (term : ι → Kid → ℕ → ℝ) (k : Kid) (n a : ℕ) :
    Gen V P isR pL ρ K (fun k => ∑ i ∈ s, add i k) (fun k a => ∑ i ∈ s, term i k a) k n a =
      ∑ i ∈ s, Gen V P isR pL ρ K (add i) (term i) k n a := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := FrogModel.D3.Gen_smul V P isR pL ρ K (fun _ => 0) (fun _ _ => 0) 0 k n a
    simpa [zero_smul] using h
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [FrogModel.D3.Gen_add V P isR pL ρ K (add i) (fun k => ∑ i ∈ s, add i k) (term i) (fun k a => ∑ i ∈ s, term i k a) k n a]
    rw [ih]

/-- `Gen` reads its end value only at ups `≤ V`. -/
theorem Gen_congr (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (add : Kid → ℝ)
    (t1 t2 : Kid → ℕ → ℝ) (ht : ∀ k a, a ≤ V → t1 k a = t2 k a) (k : Kid) (n a : ℕ)
    (ha : a ≤ V) :
    Gen V P isR pL ρ K add t1 k n a = Gen V P isR pL ρ K add t2 k n a := by
  induction h : FrogModel.D3.rankK k using Nat.strong_induction_on generalizing k n a
  case h m ih =>
    induction n generalizing a with
    | zero =>
        rw [FrogModel.D3.Gen_zero V P isR pL ρ K add t1 k a, FrogModel.D3.Gen_zero V P isR pL ρ K add t2 k a]
        exact ht k a ha
    | succ n ih_n =>
        have hn : n.succ ≠ 0 := by omega
        rw [FrogModel.D3.Gen_step V P isR pL ρ K add t1 k n.succ a hn,
            FrogModel.D3.Gen_step V P isR pL ρ K add t2 k n.succ a hn]
        have hsub : n.succ - 1 = n := by omega
        simp [hsub]
        have ha_up : upA V a ≤ V := by
          unfold FrogModel.D3.upA
          split_ifs with hlt
          · omega
          · exact ha
        have hGen_up : FrogModel.D3.Gen V P isR pL ρ K add t1 k n (upA V a) =
                      FrogModel.D3.Gen V P isR pL ρ K add t2 k n (upA V a) :=
          ih_n (upA V a) ha_up
        rw [hGen_up]
        -- Goal: (add k + 4⁻¹ * G + S1) / D = (add k + 4⁻¹ * G + S2) / D  where G = Gen ... t2 k n (upA V a)
        -- Cancel the common prefix (add k + 4⁻¹ * G) and the denominator
        congr 1
        -- Goal: add k + 4⁻¹ * G + S1 = add k + 4⁻¹ * G + S2
        congr 1
        -- Goal: S1 = S2
        refine Finset.sum_congr rfl fun x _ => ?_
        unfold FrogModel.D3.bodyG
        rw [hsub]
        cases hk : k x with
        | none =>
            dsimp
            -- Goal: 4⁻¹ * (∑ f, ∑ b, ρ b f * Gen ... t1 ... a) = 4⁻¹ * (∑ f, ∑ b, ρ b f * Gen ... t2 ... a)
            have hS : (∑ f : Fin 4, ∑ b ∈ Finset.range (V + 1),
                ρ b f * FrogModel.D3.Gen V P isR pL ρ K add t1 (Function.update k x (some f)) (min (n + b) P) a) =
              (∑ f : Fin 4, ∑ b ∈ Finset.range (V + 1),
                ρ b f * FrogModel.D3.Gen V P isR pL ρ K add t2 (Function.update k x (some f)) (min (n + b) P) a) := by
              refine Finset.sum_congr rfl fun f _ => ?_
              refine Finset.sum_congr rfl fun b _ => ?_
              have hrank : FrogModel.D3.rankK (Function.update k x (some f)) < FrogModel.D3.rankK k :=
                FrogModel.D3.rankK_update_none k x f hk
              have hrank' : FrogModel.D3.rankK (Function.update k x (some f)) < m :=
                hrank.trans_eq h
              have h_ih := ih (FrogModel.D3.rankK (Function.update k x (some f))) hrank'
                (Function.update k x (some f)) (min (n + b) P) a ha rfl
              rw [h_ih]
            rw [hS]
        | some t =>
            cases isR with
            | false =>
                dsimp
                -- Goal: 4⁻¹ * ((1 - pL) * Gen ... t1 k n a) = 4⁻¹ * ((1 - pL) * Gen ... t2 k n a)
                have h_inner : FrogModel.D3.Gen V P false pL ρ K add t1 k n a =
                              FrogModel.D3.Gen V P false pL ρ K add t2 k n a :=
                  ih_n a ha
                rw [h_inner]
            | true =>
                dsimp
                -- Goal: 4⁻¹ * (K t 0 t * Gen ... t1 k n a + S1) = 4⁻¹ * (K t 0 t * Gen ... t2 k n a + S2)
                have h_inner : FrogModel.D3.Gen V P true pL ρ K add t1 k n a =
                              FrogModel.D3.Gen V P true pL ρ K add t2 k n a :=
                  ih_n a ha
                rw [h_inner]
                -- Goal: 4⁻¹ * (K t 0 t * G2 + S1) = 4⁻¹ * (K t 0 t * G2 + S2)
                congr 1
                -- Goal: K t 0 t * G2 + S1 = K t 0 t * G2 + S2
                congr 1
                -- Goal: S1 = S2
                refine Finset.sum_congr rfl fun f _ => ?_
                split_ifs with hft
                · refine Finset.sum_congr rfl fun a' _ => ?_
                  have hrank : FrogModel.D3.rankK (Function.update k x (some f)) < FrogModel.D3.rankK k :=
                    FrogModel.D3.rankK_update_some k x t f hk hft
                  have hrank' : FrogModel.D3.rankK (Function.update k x (some f)) < m :=
                    hrank.trans_eq h
                  have h_ih := ih (FrogModel.D3.rankK (Function.update k x (some f))) hrank'
                    (Function.update k x (some f)) (min (n + a') P) a ha rfl
                  rw [h_ih]
                · rfl

/-- `Gen` of nonnegative data is nonnegative. -/
theorem Gen_nonneg (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (add : Kid → ℝ)
    (term : Kid → ℕ → ℝ) (hρ : ∀ b f, 0 ≤ ρ b f) (hK : ∀ t a f, 0 ≤ K t a f)
    (hK1 : ∀ t : ℕ, K t 1 t ≤ 1) (hp0 : 0 ≤ pL) (hp1 : pL ≤ 1) (hadd : ∀ k, 0 ≤ add k)
    (hterm : ∀ k a, 0 ≤ term k a) (k : Kid) (n a : ℕ) :
    0 ≤ Gen V P isR pL ρ K add term k n a := by
  induction h : FrogModel.D3.rankK k using Nat.strong_induction_on generalizing k n a with
  | h k IH =>
    induction n generalizing a with
    | zero =>
      rw [FrogModel.D3.Gen_zero]
      exact hterm k a
    | succ n IHn =>
      rw [FrogModel.D3.Gen_step V P isR pL ρ K add term k n.succ a (by omega : n.succ ≠ 0)]
      have h_add : 0 ≤ add k := hadd k
      have h_gen_up : 0 ≤ FrogModel.D3.Gen V P isR pL ρ K add term k n (FrogModel.D3.upA V a) :=
        IHn (FrogModel.D3.upA V a)
      have h_denom : 0 ≤ 1 - FrogModel.D3.loopK isR pL K k := by
        have h_loop := FrogModel.D3.loopK_bounds isR pL K hp0 hp1 (by
          intro t
          exact hK t 1 t) hK1 k
        rcases h_loop with ⟨h_loop_nonneg, h_loop_le⟩
        linarith
      have h_bodyG : ∀ (c : Fin 3), 0 ≤ (1 / 4 : ℝ) * FrogModel.D3.bodyG V P isR pL ρ K (FrogModel.D3.Gen V P isR pL ρ K add term) k n.succ a c := by
        intro c
        match hkc : k c with
        | none =>
          rw [FrogModel.D3.bodyG, hkc]
          simp
          refine Finset.sum_nonneg fun f _ => ?_
          refine Finset.sum_nonneg fun b _ => ?_
          have h_rank : FrogModel.D3.rankK (Function.update k c (some f)) < FrogModel.D3.rankK k :=
            FrogModel.D3.rankK_update_none k c f hkc
          rw [h] at h_rank
          have h_ineq := IH (FrogModel.D3.rankK (Function.update k c (some f))) h_rank (Function.update k c (some f)) (min (n + b) P) a rfl
          have h_nonneg : 0 ≤ FrogModel.D3.Gen V P isR pL ρ K add term (Function.update k c (some f)) (min (n + b) P) a := h_ineq
          have h_rho : 0 ≤ ρ b f := hρ b f
          nlinarith
        | some t =>
          rw [FrogModel.D3.bodyG, hkc]
          by_cases hisR : isR
          · have h_gen_same : 0 ≤ FrogModel.D3.Gen V P true pL ρ K add term k n a := by
              simpa [hisR] using IHn a
            have h_sum : 0 ≤ ∑ f : Fin 4, (if hf : f < t then ∑ a' ∈ Finset.range (V + 1),
              K t a' f * FrogModel.D3.Gen V P true pL ρ K add term (Function.update k c (some f))
                (min (n + a') P) a else 0) := by
              refine Finset.sum_nonneg fun f _ => ?_
              split
              · rename_i hf
                refine Finset.sum_nonneg fun a' _ => ?_
                have h_Kaa' : 0 ≤ K t a' f := hK t a' f
                have h_rank : FrogModel.D3.rankK (Function.update k c (some f)) < FrogModel.D3.rankK k :=
                  FrogModel.D3.rankK_update_some k c t f hkc hf
                rw [h] at h_rank
                have h_ineq := IH (FrogModel.D3.rankK (Function.update k c (some f))) h_rank (Function.update k c (some f)) (min (n + a') P) a rfl
                have h_nonneg : 0 ≤ FrogModel.D3.Gen V P true pL ρ K add term (Function.update k c (some f)) (min (n + a') P) a := by
                  simpa [hisR] using h_ineq
                nlinarith
              · exact le_refl _
            have h_first : 0 ≤ K t 0 t * FrogModel.D3.Gen V P true pL ρ K add term k n a :=
              mul_nonneg (hK t 0 t) h_gen_same
            have h_total : 0 ≤ K t 0 t * FrogModel.D3.Gen V P true pL ρ K add term k n a +
              ∑ f : Fin 4, (if hf : f < t then ∑ a' ∈ Finset.range (V + 1),
                K t a' f * FrogModel.D3.Gen V P true pL ρ K add term (Function.update k c (some f))
                  (min (n + a') P) a else 0) :=
              add_nonneg h_first h_sum
            have h_pos : 0 ≤ (1 / 4 : ℝ) := by norm_num
            simpa [hisR, Nat.succ_sub_succ] using mul_nonneg h_pos h_total
          · simpa [hisR, Nat.succ_sub_succ] using mul_nonneg (by norm_num : 0 ≤ (1 / 4 : ℝ))
              (mul_nonneg (by linarith : 0 ≤ 1 - pL) (by simpa [hisR] using IHn a))
      have h_sum : 0 ≤ ∑ c : Fin 3, (1 / 4 : ℝ) * FrogModel.D3.bodyG V P isR pL ρ K (FrogModel.D3.Gen V P isR pL ρ K add term) k n.succ a c :=
        Finset.sum_nonneg fun c _ => h_bodyG c
      have h_num : 0 ≤ add k + (1 / 4 : ℝ) * FrogModel.D3.Gen V P isR pL ρ K add term k n (FrogModel.D3.upA V a) +
        ∑ c : Fin 3, (1 / 4 : ℝ) * FrogModel.D3.bodyG V P isR pL ρ K (FrogModel.D3.Gen V P isR pL ρ K add term) k n.succ a c := by
        nlinarith
      exact div_nonneg h_num h_denom

/-- A law: with inputs of total mass `1`, additive term `0` and end value `1`, `Gen` is `1`. -/
theorem Gen_one (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (hρ : ∑ f : Fin 4, ∑ b ∈ Finset.range (V + 1), ρ b f = 1)
    (hK : ∀ t : Fin 4, K t 0 t + K t 1 t +
      ∑ f : Fin 4, (if f < t then ∑ a' ∈ Finset.range (V + 1), K t a' f else 0) = 1)
    (hK0 : ∀ t : ℕ, 0 ≤ K t 1 t) (hK1 : ∀ t : ℕ, K t 1 t ≤ 1) (hp0 : 0 ≤ pL) (hp1 : pL ≤ 1)
    (k : Kid) (n a : ℕ) :
    Gen V P isR pL ρ K (fun _ => 0) (fun _ _ => 1) k n a = 1 := by
  induction h : rankK k using Nat.strong_induction_on generalizing k n a with
  | h m IH =>
    induction n generalizing a with
    | zero => simp only [Gen_zero]
    | succ n IHn =>
      rw [Gen_step _ _ _ _ _ _ _ _ k _ _ (Nat.succ_ne_zero n), Nat.succ_sub_one, Nat.succ_eq_add_one,
        IHn (upA V a)]
      have hb : ∀ c, 1 / 4 * bodyG V P isR pL ρ K (Gen V P isR pL ρ K (fun _ => 0) (fun _ _ => 1))
          k (n + 1) a c =
          1 / 4 - (match k c with | none => 0 | some t => 1 / 4 * (if isR then K t 1 t else pL)) := by
        intro c
        rw [bodyG_congr V P isR pL ρ K _ (fun _ _ _ => 1) k (n + 1) a c (IHn a)
          (fun k' hk' n' => IH _ (h ▸ hk') k' n' a rfl)]
        unfold bodyG
        cases k c with
        | none => simp only [mul_one, hρ]; ring
        | some t =>
          cases isR
          · simp only [Bool.false_eq_true, ite_false, mul_one]; ring
          · simp only [ite_true, mul_one]
            have := hK t
            linarith
      rw [Finset.sum_congr rfl fun c _ => hb c, Finset.sum_sub_distrib]
      have hloop : ∑ c, (match k c with
          | none => (0 : ℝ)
          | some t => 1 / 4 * (if isR then K t 1 t else pL)) = loopK isR pL K k := rfl
      rw [hloop]
      have hl := loopK_bounds isR pL K hp0 hp1 hK0 hK1 k
      have hne : 1 - loopK isR pL K k ≠ 0 := by linarith
      rw [div_eq_one_iff_eq hne]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- An H closure depends on its child types only through the count of unmarked children. -/
theorem Gen_lump (V P : ℕ) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (add : Kid → ℝ) (term : Kid → ℕ → ℝ)
    (hadd : ∀ k k', nN k = nN k' → add k = add k')
    (hterm : ∀ k k' a, nN k = nN k' → term k a = term k' a)
    (k k' : Kid) (n a : ℕ) (hk : nN k = nN k') :
    Gen V P false pL ρ K add term k n a = Gen V P false pL ρ K add term k' n a := by
  induction h : nN k using Nat.strong_induction_on generalizing k k' n a with
  | h m IH =>
    induction n generalizing a with
    | zero => rw [Gen_zero, Gen_zero]; exact hterm k k' a hk
    | succ n IHn =>
      rw [Gen_step _ _ _ _ _ _ _ _ k _ _ (Nat.succ_ne_zero n),
        Gen_step _ _ _ _ _ _ _ _ k' _ _ (Nat.succ_ne_zero n), loopK_H, loopK_H, ← hk,
        hadd k k' hk, Nat.succ_sub_one, Nat.succ_eq_add_one, IHn (upA V a)]
      congr 2
      set X := Gen V P false pL ρ K add term with hX
      have hform : ∀ k'' : Kid, ∑ c, 1 / 4 * bodyG V P false pL ρ K X k'' (n + 1) a c =
          ∑ c, (match k'' c with
            | none => 1 / 4 * ∑ f : Fin 4, ∑ b ∈ Finset.range (V + 1),
                ρ b f * X (Function.update k'' c (some f)) (min (n + b) P) a
            | some _ => 1 / 4 * ((1 - pL) * X k'' n a)) := by
        intro k''
        refine Finset.sum_congr rfl fun c _ => ?_
        unfold bodyG
        cases k'' c <;> simp
      rw [hform k, hform k', IHn a]
      have hcount : ∀ k'' : Kid, (∃ c, k'' c = none) ↔ 0 < nN k'' := by
        intro k''
        unfold nN
        rw [Finset.card_pos]
        constructor
        · rintro ⟨c, hc⟩; exact ⟨c, by simp [hc]⟩
        · rintro ⟨c, hc⟩; exact ⟨c, (Finset.mem_filter.mp hc).2⟩
      by_cases hex : ∃ c0, k c0 = none
      · obtain ⟨c0, hc0⟩ := hex
        set A := 1 / 4 * ∑ f : Fin 4, ∑ b ∈ Finset.range (V + 1),
          ρ b f * X (Function.update k c0 (some f)) (min (n + b) P) a with hA
        have hnu : ∀ (k'' : Kid) (c : Fin 3), k'' c = none → nN k'' = m →
            (1 / 4 * ∑ f : Fin 4, ∑ b ∈ Finset.range (V + 1),
              ρ b f * X (Function.update k'' c (some f)) (min (n + b) P) a) = A := by
          intro k'' c hc hm
          rw [hA]
          congr 1
          refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun b _ => ?_
          have h1 := nN_update_none k'' c f hc
          have h2 := nN_update_none k c0 f hc0
          rw [IH _ (by omega) (Function.update k'' c (some f)) (Function.update k c0 (some f))
            _ a (by omega) rfl]
        rw [sum_kid k _ _ A (fun c hc => hnu k c hc h), sum_kid k' _ _ A
          (fun c hc => hnu k' c hc (hk ▸ h)), hk]
      · have hk0 : nN k = 0 := by
          by_contra hne
          exact hex ((hcount k).2 (Nat.pos_of_ne_zero hne))
        have hk0' : nN k' = 0 := hk ▸ hk0
        rw [sum_kid k _ _ 0 (fun c hc => absurd ⟨c, hc⟩ hex), sum_kid k' _ _ 0
          (fun c hc => absurd ((hcount k').1 ⟨c, hc⟩) (by omega)), hk]

/-- An H closure never reaches more unmarked children, nor, without marking a child, more than
its ups plus its pool. -/
theorem Gen_supp (V P : ℕ) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (term : Kid → ℕ → ℝ) (f b : ℕ)
    (hterm : ∀ k a, (nN k < f ∨ (nN k = f ∧ a < b)) → term k a = 0)
    (k : Kid) (n a : ℕ)
    (hk : nN k < f ∨ (nN k = f ∧ a + n < b)) :
    Gen V P false pL ρ K (fun _ => 0) term k n a = 0 := by
  -- We prove the statement by strong induction on nN k, with inner induction on n.
  -- Let P(m) := ∀ k a n, nN k = m → (nN k < f ∨ (nN k = f ∧ a + n < b)) → Gen ... k n a = 0
  -- We use Nat.strong_induction_on on m = nN k.
  set m0 := nN k with hm0_def
  -- Prove P(m) for all m by strong induction
  have hP : ∀ m, (∀ m' < m, ∀ (k' : Kid) (a' n' : ℕ), nN k' = m' → (nN k' < f ∨ (nN k' = f ∧ a' + n' < b)) → Gen V P false pL ρ K (fun _ => 0) term k' n' a' = 0) → ∀ (k' : Kid) (a' n' : ℕ), nN k' = m → (nN k' < f ∨ (nN k' = f ∧ a' + n' < b)) → Gen V P false pL ρ K (fun _ => 0) term k' n' a' = 0 := by
    intro m ih_m k' a' n' hm hcond
    -- Now inner strong induction on n'
    have h_inner : ∀ (n'' : ℕ), (∀ n''' < n'', ∀ (a'' : ℕ), (nN k' < f ∨ (nN k' = f ∧ a'' + n''' < b)) → Gen V P false pL ρ K (fun _ => 0) term k' n''' a'' = 0) → ∀ (a'' : ℕ), (nN k' < f ∨ (nN k' = f ∧ a'' + n'' < b)) → Gen V P false pL ρ K (fun _ => 0) term k' n'' a'' = 0 := by
      intro n'' ih_n a'' hcond''
      by_cases hn'' : n'' = 0
      · subst hn''
        rw [FrogModel.D3.Gen_zero]
        exact hterm k' a'' (by simpa [add_zero] using hcond'')
      · have hn0'' : n'' ≠ 0 := hn''
        rw [FrogModel.D3.Gen_step V P false pL ρ K (fun _ => 0) term k' n'' a'' hn0'']
        have h_upA : Gen V P false pL ρ K (fun _ => 0) term k' (n'' - 1) (FrogModel.D3.upA V a'') = 0 := by
          have h_lt' : n'' - 1 < n'' := by omega
          have h_cond_upA : nN k' < f ∨ (nN k' = f ∧ FrogModel.D3.upA V a'' + (n'' - 1) < b) := by
            rcases hcond'' with (h_lt_c | ⟨h_eq_c, h_lt_a_c⟩)
            · left; exact h_lt_c
            · right; constructor
              · exact h_eq_c
              · have h_upA_le : FrogModel.D3.upA V a'' ≤ a'' + 1 := by
                  unfold FrogModel.D3.upA
                  split_ifs with h
                  · omega
                  · omega
                omega
          exact ih_n (n'' - 1) h_lt' (FrogModel.D3.upA V a'') h_cond_upA
        have h_bodyG : (∑ c : Fin 3, 1 / 4 * FrogModel.D3.bodyG V P false pL ρ K
            (Gen V P false pL ρ K (fun _ => 0) term) k' n'' a'' c) = 0 := by
          have h_term (c : Fin 3) : 1 / 4 * FrogModel.D3.bodyG V P false pL ρ K
              (Gen V P false pL ρ K (fun _ => 0) term) k' n'' a'' c = 0 := by
            unfold FrogModel.D3.bodyG
            cases hc : k' c with
            | none =>
              simp
              refine Finset.sum_eq_zero (fun f' _ => ?_)
              refine Finset.sum_eq_zero (fun b' _ => ?_)
              have h_nN_lt : nN (Function.update k' c (some f')) < nN k' := by
                have := FrogModel.D3.nN_update_none k' c f' hc
                omega
              have h_cond_upd : nN (Function.update k' c (some f')) < f ∨
                  (nN (Function.update k' c (some f')) = f ∧ a'' + min (n'' - 1 + b') P < b) := by
                rcases hcond'' with (h_lt_c | ⟨h_eq_c, h_lt_a_c⟩)
                · left; exact lt_trans h_nN_lt h_lt_c
                · left; exact h_eq_c ▸ h_nN_lt
              have h_lt_m : nN (Function.update k' c (some f')) < m := by
                rw [← hm]
                exact h_nN_lt
              have h_gen_zero := ih_m (nN (Function.update k' c (some f'))) h_lt_m
                (Function.update k' c (some f')) a'' (min (n'' - 1 + b') P) rfl h_cond_upd
              rw [h_gen_zero]
              simp
            | some t =>
              simp
              have h_lt' : n'' - 1 < n'' := by omega
              have h_cond_some : nN k' < f ∨ (nN k' = f ∧ a'' + (n'' - 1) < b) := by
                rcases hcond'' with (h_lt_c | ⟨h_eq_c, h_lt_a_c⟩)
                · left; exact h_lt_c
                · right; constructor
                  · exact h_eq_c
                  · omega
              rw [ih_n (n'' - 1) h_lt' a'' h_cond_some]
              simp
          calc
            (∑ c : Fin 3, 1 / 4 * FrogModel.D3.bodyG V P false pL ρ K
                (Gen V P false pL ρ K (fun _ => 0) term) k' n'' a'' c)
                = (∑ c : Fin 3, 0) := by
                  refine Finset.sum_congr rfl (fun c _ => ?_)
                  rw [h_term c]
            _ = 0 := by simp
        have h_num : (0 : ℝ) + 1 / 4 * Gen V P false pL ρ K (fun _ => 0) term k' (n'' - 1) (FrogModel.D3.upA V a'') +
            ∑ c : Fin 3, 1 / 4 * FrogModel.D3.bodyG V P false pL ρ K
              (Gen V P false pL ρ K (fun _ => 0) term) k' n'' a'' c = 0 := by
          rw [h_upA, h_bodyG]
          simp
        rw [h_num, zero_div]
    -- Now use Nat.strong_induction_on to get the inner induction hypothesis
    have h_ind : ∀ (n'' : ℕ), n'' < n' → ∀ (a'' : ℕ), (nN k' < f ∨ (nN k' = f ∧ a'' + n'' < b)) → Gen V P false pL ρ K (fun _ => 0) term k' n'' a'' = 0 := by
      intro n'' h_lt_n
      refine Nat.strong_induction_on n'' (fun m ih => ?_)
      intro a'' hcond''
      exact h_inner m (fun p hp => ih p hp) a'' hcond''
    exact h_inner n' h_ind a' hcond
  -- Now apply hP to get the result for all m, in particular m = nN k
  have h_all : ∀ m, ∀ (k' : Kid) (a' n' : ℕ), nN k' = m → (nN k' < f ∨ (nN k' = f ∧ a' + n' < b)) → Gen V P false pL ρ K (fun _ => 0) term k' n' a' = 0 := by
    intro m
    refine Nat.strong_induction_on m hP
  exact h_all (nN k) k a n rfl hk

end FrogModel.D3
