module

public import FrogModel.D3.M1L.Height0
public import FrogModel.D3.M1L.Height1Defs

@[expose] public section

/-!
# M1_L at height 1: the chain of the top closure at `p.m = 1`

The law of the run at `m = 1` (the case `m = 1` of Lemma 13.2 of the paper, with the recursion of
`Height1Defs`), on the stream. The candidate `W1` of `Height1Defs` is checked read by read against
the chain `h1step`: a round of the top (`W1_round`), a read inside a child closure (`W1_inner`), the
kill coin at the end of a child closure (`W1_kill`). The recursion `W1top` is the loop-solved
form; `W1top_step` puts the loop back on the right.
-/

open MeasureTheory FrogModel
open scoped ENNReal

namespace FrogModel.D3

/-- With an empty pool the top has ended. -/
theorem W1top_zero (V P b : ℕ) (ρR ρH : ℕ → ℝ) (κ : Bool → ℕ → ℕ → ℝ)
    (σ : Fin 3 → Fin 3) (a : ℕ) : W1top V P b ρR ρH κ σ 0 a = if a = b then 1 else 0 := by
  rw [W1top]
  simp

/-- The defining equation of `W1top` at a nonempty pool, with `rest1` and `loop1`. -/
theorem W1top_succ (V P b : ℕ) (ρR ρH : ℕ → ℝ) (κ : Bool → ℕ → ℕ → ℝ)
    (σ : Fin 3 → Fin 3) (n a : ℕ) :
    W1top V P b ρR ρH κ σ (n + 1) a =
      (1 / 4 * W1top V P b ρR ρH κ σ n (if a < V then a + 1 else a) +
        ∑ c, 1 / 4 * rest1 P ρR ρH κ (W1top V P b ρR ρH κ) σ (n + 1) a c) /
        (1 - loop1 ρH κ σ) := by
  rw [W1top]
  simp only [Nat.succ_ne_zero n, Nat.add_sub_cancel, dite_eq_ite]
  rfl

/-- The loop has probability at most 3/4. -/
theorem loop1_le (ρH : ℕ → ℝ) (κ : Bool → ℕ → ℕ → ℝ) (h0 : 0 ≤ ρH 1) (h1 : ρH 1 ≤ 1)
    (hκ : ∀ i f b', 0 ≤ κ i f b' ∧ κ i f b' ≤ 1) (σ : Fin 3 → Fin 3) :
    0 ≤ loop1 ρH κ σ ∧ loop1 ρH κ σ ≤ 3 / 4 := by
  have hκ_nonneg : ∀ i f b', 0 ≤ κ i f b' := fun i f b' => (hκ i f b').1
  have hκ_le_one : ∀ i f b', κ i f b' ≤ 1 := fun i f b' => (hκ i f b').2
  unfold loop1
  have hpos : 0 ≤ ∑ c : Fin 3, (if (σ c).val = 0 then (0 : ℝ) else 1 / 4 * ρH 1 * κ false (if (σ c).val = 1 then 3 else 0) 1) := by
    refine Finset.sum_nonneg (fun c _ => ?_)
    by_cases h0c : (σ c).val = 0
    · simp [h0c]
    · have hpos_term : 0 ≤ 1 / 4 * ρH 1 * κ false (if (σ c).val = 1 then 3 else 0) 1 := by
        have h_quarter : (0 : ℝ) ≤ 1/4 := by norm_num
        have h_ρH1 : 0 ≤ ρH 1 := h0
        have h_κ : 0 ≤ κ false (if (σ c).val = 1 then 3 else 0) 1 := hκ_nonneg false (if (σ c).val = 1 then 3 else 0) 1
        nlinarith
      simpa [h0c] using hpos_term
  have hle : (∑ c : Fin 3, (if (σ c).val = 0 then (0 : ℝ) else 1 / 4 * ρH 1 * κ false (if (σ c).val = 1 then 3 else 0) 1)) ≤ 3/4 := by
    calc
      (∑ c : Fin 3, (if (σ c).val = 0 then (0 : ℝ) else 1 / 4 * ρH 1 * κ false (if (σ c).val = 1 then 3 else 0) 1)) ≤
          ∑ c : Fin 3, (1/4 : ℝ) := by
        refine Finset.sum_le_sum (fun c _ => ?_)
        by_cases h0c : (σ c).val = 0
        · simp [h0c]
        · have hterm : 1 / 4 * ρH 1 * κ false (if (σ c).val = 1 then 3 else 0) 1 ≤ 1/4 := by
            have h_ρH1 : ρH 1 ≤ 1 := h1
            have h_κ : κ false (if (σ c).val = 1 then 3 else 0) 1 ≤ 1 := hκ_le_one false (if (σ c).val = 1 then 3 else 0) 1
            nlinarith
          simpa [h0c] using hterm
      _ = 3/4 := by norm_num [Fin.sum_univ_three]
  exact And.intro hpos hle

/-- **The first-step equation of the top at height 1**, the loop on the right. -/
theorem W1top_step (V P b : ℕ) (ρR ρH : ℕ → ℝ) (κ : Bool → ℕ → ℕ → ℝ) (h0 : 0 ≤ ρH 1)
    (h1 : ρH 1 ≤ 1) (hκ : ∀ i f b', 0 ≤ κ i f b' ∧ κ i f b' ≤ 1) (σ : Fin 3 → Fin 3) (n a : ℕ) :
    W1top V P b ρR ρH κ σ (n + 1) a =
      1 / 4 * W1top V P b ρR ρH κ σ n (if a < V then a + 1 else a) +
        ∑ c, 1 / 4 * (rest1 P ρR ρH κ (W1top V P b ρR ρH κ) σ (n + 1) a c +
          (if (σ c).val = 0 then 0 else ρH 1 * κ false (if (σ c).val = 1 then 3 else 0) 1) *
            W1top V P b ρR ρH κ σ (n + 1) a) := by
  set X := W1top V P b ρR ρH κ σ (n + 1) a with hX
  set U := W1top V P b ρR ρH κ σ n (if a < V then a + 1 else a) with hU
  set R := fun (c : Fin 3) => rest1 P ρR ρH κ (W1top V P b ρR ρH κ) σ (n + 1) a c with hR
  set t := fun (c : Fin 3) => if (σ c).val = 0 then 0 else ρH 1 * κ false (if (σ c).val = 1 then 3 else 0) 1 with ht
  set ℓ := loop1 ρH κ σ with hℓ
  have hW1top_succ : X = (1 / 4 * U + ∑ c, 1 / 4 * R c) / (1 - ℓ) := by
    rw [hX, hU, hR, hℓ]
    simpa using W1top_succ V P b ρR ρH κ σ n a
  have h_loop_le := loop1_le ρH κ h0 h1 hκ σ
  rcases h_loop_le with ⟨h_loop_nonneg, h_loop_le_34⟩
  have h_denom_ne_zero : 1 - ℓ ≠ 0 := by linarith
  have h_loop_sum : (∑ c : Fin 3, 1 / 4 * t c) = ℓ := by
    calc
      (∑ c : Fin 3, 1 / 4 * t c) = (∑ c : Fin 3, 1 / 4 * (if (σ c).val = 0 then 0 else ρH 1 * κ false (if (σ c).val = 1 then 3 else 0) 1)) := by simp [t]
      _ = (∑ c : Fin 3, if (σ c).val = 0 then 0 else 1 / 4 * (ρH 1 * κ false (if (σ c).val = 1 then 3 else 0) 1)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        split <;> simp
      _ = loop1 ρH κ σ := by
        simp [loop1, mul_assoc]
      _ = ℓ := rfl
  have h_eq : X * (1 - ℓ) = 1 / 4 * U + ∑ c, 1 / 4 * R c := by
    rw [hW1top_succ]
    field_simp [h_denom_ne_zero]
  calc
    X = X * (1 - ℓ) + X * ℓ := by ring
    _ = (1 / 4 * U + ∑ c, 1 / 4 * R c) + X * ℓ := by rw [h_eq]
    _ = (1 / 4 * U + ∑ c, 1 / 4 * R c) + X * (∑ c, 1 / 4 * t c) := by rw [h_loop_sum]
    _ = 1 / 4 * U + (∑ c, 1 / 4 * R c) + (∑ c, X * (1 / 4 * t c)) := by
      simp [Finset.mul_sum, add_assoc]
    _ = 1 / 4 * U + ∑ c, (1 / 4 * R c + X * (1 / 4 * t c)) := by
      simp [Finset.sum_add_distrib, add_assoc]
    _ = 1 / 4 * U + ∑ c, 1 / 4 * (R c + t c * X) := by
      refine congrArg (fun s => 1 / 4 * U + s) (Finset.sum_congr rfl fun c _ => ?_)
      ring
    _ = 1 / 4 * W1top V P b ρR ρH κ σ n (if a < V then a + 1 else a) +
        ∑ c, 1 / 4 * (rest1 P ρR ρH κ (W1top V P b ρR ρH κ) σ (n + 1) a c +
          (if (σ c).val = 0 then 0 else ρH 1 * κ false (if (σ c).val = 1 then 3 else 0) 1) *
            W1top V P b ρR ρH κ σ (n + 1) a) := by
      simp [hU, hR, ht, hX]

/-- The rank of the child states is at most 6. -/
theorem rank1_le (σ : Fin 3 → Fin 3) : rank1 σ ≤ 6 := by
  unfold rank1
  calc
    ∑ c : Fin 3, (2 - (σ c).val) ≤ ∑ c : Fin 3, 2 :=
      Finset.sum_le_sum fun c _ => Nat.sub_le 2 (σ c).val
    _ = 6 := by simp

/-- The candidate at height 1 is nonnegative. -/
theorem W1top_nonneg (V P b : ℕ) (ρR ρH : ℕ → ℝ) (κ : Bool → ℕ → ℕ → ℝ)
    (hR : ∀ j, 0 ≤ ρR j) (hH : ∀ j, 0 ≤ ρH j) (_hRs : ∑ j ∈ Finset.range 3, ρR j = 1)
    (hHs : ρH 0 + ρH 1 = 1) (hκ : ∀ i f j, 0 ≤ κ i f j ∧ κ i f j ≤ 1) (σ : Fin 3 → Fin 3) (n a : ℕ) : 0 ≤ W1top V P b ρR ρH κ σ n a := by
  have hρH1 : ρH 1 ≤ 1 := by
    have h0 := hH 0
    linarith
  have hκ_nonneg : ∀ i f j, 0 ≤ κ i f j := fun i f j => (hκ i f j).1
  have hκ_le_one : ∀ i f j, κ i f j ≤ 1 := fun i f j => (hκ i f j).2
  have hloop := loop1_le ρH κ (hH 1) hρH1 hκ σ
  rcases hloop with ⟨hloop_nonneg, hloop_le⟩
  have h_denom_nonneg : 0 ≤ 1 - loop1 ρH κ σ := by
    have : loop1 ρH κ σ ≤ 3/4 := hloop_le
    linarith
  let rel : (ℕ × ℕ) → (ℕ × ℕ) → Prop := Prod.Lex (· < ·) (· < ·)
  have hwf : WellFounded rel := WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf
  -- Define the property we prove by well-founded induction on (rank1 σ, n):
  -- for all σ' with rank1 σ' = r, and all a, the value is nonnegative
  let P_prop : ℕ × ℕ → Prop := fun p => ∀ (σ' : Fin 3 → Fin 3), rank1 σ' = p.1 → ∀ a', 0 ≤ W1top V P b ρR ρH κ σ' p.2 a'
  have hP : ∀ p, (∀ q, rel q p → P_prop q) → P_prop p := by
    intro p ih σ' hr a'
    -- hr: rank1 σ' = p.1
    -- We need to prove 0 ≤ W1top ... σ' p.2 a'
    -- Use the definition of W1top
    rw [W1top]
    split
    · -- p.2 = 0
      rename_i h
      -- h : p.2 = 0, goal is 0 ≤ if a' = b then 1 else 0
      -- p.2 doesn't appear in the goal, so just split on the remaining if
      split <;> norm_num
    · -- p.2 ≠ 0
      rename_i hn
      -- Now p.2 > 0, so p.2 - 1 < p.2
      have h_up : 0 ≤ W1top V P b ρR ρH κ σ' (p.2 - 1) (if a' < V then a' + 1 else a') := by
        -- This recursive call uses (σ', p.2 - 1)
        -- Need to show rel (rank1 σ', p.2 - 1) p
        have h_rel : rel (rank1 σ', p.2 - 1) p := by
          -- p = (p.1, p.2), and rank1 σ' = p.1
          -- So we need (rank1 σ', p.2 - 1) < (p.1, p.2)
          -- Using hr: rank1 σ' = p.1, this is (p.1, p.2 - 1) < (p.1, p.2)
          -- which is Prod.Lex.right with p.2 - 1 < p.2
          have : rank1 σ' = p.1 := hr
          rw [this]
          exact Prod.Lex.right (p.1) (by omega)
        have h_Pq := ih (rank1 σ', p.2 - 1) h_rel
        -- h_Pq : P_prop (rank1 σ', p.2 - 1)
        -- i.e., ∀ σ'', rank1 σ'' = rank1 σ' → ∀ a'', 0 ≤ W1top ... σ'' (rank1 σ', p.2 - 1).2 a''
        simpa using h_Pq σ' rfl (if a' < V then a' + 1 else a')
      have h_rest : ∀ c, 0 ≤ rest1 P ρR ρH κ (W1top V P b ρR ρH κ) σ' p.2 a' c := by
        intro c
        unfold rest1
        split
        · -- (σ' c).val = 0
          rename_i h0
          refine Finset.sum_nonneg fun b' hb' => ?_
          have h_rhoR : 0 ≤ ρR b' := hR b'
          have h_kappa : 0 ≤ κ true 3 b' := hκ_nonneg true 3 b'
          have h_kappa_le : κ true 3 b' ≤ 1 := hκ_le_one true 3 b'
          have h_one_minus_kappa : 0 ≤ 1 - κ true 3 b' := by linarith
          -- Two recursive calls in rest1:
          -- 1. W1top (Function.update σ' c 1) (min (p.2 - 1 + b') P) a'
          have h_w1 : 0 ≤ W1top V P b ρR ρH κ (Function.update σ' c 1) (min (p.2 - 1 + b') P) a' := by
            have h_rank_lt : rank1 (Function.update σ' c 1) < rank1 σ' :=
              rank1_update_lt σ' c 1 (by rw [h0]; decide)
            have h_rank_lt' : rank1 (Function.update σ' c 1) < p.1 := by
              rw [← hr]; exact h_rank_lt
            have h_rel : rel (rank1 (Function.update σ' c 1), min (p.2 - 1 + b') P) p :=
              Prod.Lex.left (min (p.2 - 1 + b') P) p.2 h_rank_lt'
            have h_Pq := ih (rank1 (Function.update σ' c 1), min (p.2 - 1 + b') P) h_rel
            simpa using h_Pq (Function.update σ' c 1) rfl a'
          -- 2. W1top (Function.update σ' c 2) (p.2 - 1) a'
          have h_w2 : 0 ≤ W1top V P b ρR ρH κ (Function.update σ' c 2) (p.2 - 1) a' := by
            have h_rank_lt : rank1 (Function.update σ' c 2) < rank1 σ' :=
              rank1_update_lt σ' c 2 (by rw [h0]; decide)
            have h_rank_lt' : rank1 (Function.update σ' c 2) < p.1 := by
              rw [← hr]; exact h_rank_lt
            have h_rel : rel (rank1 (Function.update σ' c 2), p.2 - 1) p :=
              Prod.Lex.left (p.2 - 1) p.2 h_rank_lt'
            have h_Pq := ih (rank1 (Function.update σ' c 2), p.2 - 1) h_rel
            simpa using h_Pq (Function.update σ' c 2) rfl a'
          apply mul_nonneg h_rhoR
          apply add_nonneg
          · apply mul_nonneg h_kappa h_w1
          · apply mul_nonneg h_one_minus_kappa h_w2
        · -- (σ' c).val ≠ 0
          rename_i h_not0
          have h_rhoH0 : 0 ≤ ρH 0 := hH 0
          have h_rhoH1 : 0 ≤ ρH 1 := hH 1
          split
          · -- (σ' c).val = 1
            rename_i h1
            have h_kappa0 : 0 ≤ κ false 3 0 := hκ_nonneg false 3 0
            have h_kappa0_le : κ false 3 0 ≤ 1 := hκ_le_one false 3 0
            have h_one_minus_kappa0 : 0 ≤ 1 - κ false 3 0 := by linarith
            -- Two recursive calls:
            -- 1. W1top σ' (p.2 - 1) a'
            have h_w1 : 0 ≤ W1top V P b ρR ρH κ σ' (p.2 - 1) a' := by
              have h_rel : rel (rank1 σ', p.2 - 1) p := by
                rw [hr]
                exact Prod.Lex.right (p.1) (by omega)
              have h_Pq := ih (rank1 σ', p.2 - 1) h_rel
              simpa using h_Pq σ' rfl a'
            -- 2. W1top (Function.update σ' c 2) (p.2 - 1) a'
            have h_w2 : 0 ≤ W1top V P b ρR ρH κ (Function.update σ' c 2) (p.2 - 1) a' := by
              have h_rank_lt : rank1 (Function.update σ' c 2) < rank1 σ' :=
                rank1_update_lt σ' c 2 (by rw [h1]; decide)
              have h_rank_lt' : rank1 (Function.update σ' c 2) < p.1 := by
                rw [← hr]; exact h_rank_lt
              have h_rel : rel (rank1 (Function.update σ' c 2), p.2 - 1) p :=
                Prod.Lex.left (p.2 - 1) p.2 h_rank_lt'
              have h_Pq := ih (rank1 (Function.update σ' c 2), p.2 - 1) h_rel
              simpa using h_Pq (Function.update σ' c 2) rfl a'
            have h_kappa1_le : κ false 3 1 ≤ 1 := hκ_le_one false 3 1
            have h_one_minus_kappa1 : 0 ≤ 1 - κ false 3 1 := by linarith
            -- Goal: 0 ≤ ρH 0 * (κ false 3 0 * W1top ... σ' ... + (1 - κ false 3 0) * W1top ... (Function.update σ' c 2) ...) +
            --        ρH 1 * (1 - κ false 3 1) * W1top ... (Function.update σ' c 2) ...
            -- All W1top values are nonnegative by h_w1, h_w2
            have h_term1 : 0 ≤ ρH 0 * (κ false 3 0 * W1top V P b ρR ρH κ σ' (p.2 - 1) a' +
                (1 - κ false 3 0) * W1top V P b ρR ρH κ (Function.update σ' c 2) (p.2 - 1) a') := by
              apply mul_nonneg h_rhoH0
              apply add_nonneg
              · apply mul_nonneg h_kappa0 h_w1
              · apply mul_nonneg h_one_minus_kappa0 h_w2
            have h_term2 : 0 ≤ ρH 1 * (1 - κ false 3 1) * W1top V P b ρR ρH κ (Function.update σ' c 2) (p.2 - 1) a' := by
              apply mul_nonneg (mul_nonneg h_rhoH1 h_one_minus_kappa1) h_w2
            nlinarith
          · -- (σ' c).val ≠ 0 and ≠ 1, so must be 2
            rename_i h_not1
            -- Two recursive calls, both at σ' (p.2 - 1) a'
            have h_w : 0 ≤ W1top V P b ρR ρH κ σ' (p.2 - 1) a' := by
              have h_rel : rel (rank1 σ', p.2 - 1) p := by
                rw [hr]
                exact Prod.Lex.right (p.1) (by omega)
              have h_Pq := ih (rank1 σ', p.2 - 1) h_rel
              simpa using h_Pq σ' rfl a'
            have h_kappa01_le : κ false 0 1 ≤ 1 := hκ_le_one false 0 1
            have h_one_minus_kappa01 : 0 ≤ 1 - κ false 0 1 := by linarith
            -- Goal: 0 ≤ ρH 0 * W1top ... σ' ... + ρH 1 * (1 - κ false 0 1) * W1top ... σ' ...
            apply add_nonneg
            · apply mul_nonneg h_rhoH0 h_w
            · apply mul_nonneg (mul_nonneg h_rhoH1 h_one_minus_kappa01) h_w
      -- Need denominator bound for the current σ'
      have hloop' := loop1_le ρH κ (hH 1) hρH1 hκ σ'
      rcases hloop' with ⟨hloop_nonneg', hloop_le'⟩
      have h_denom_nonneg' : 0 ≤ 1 - loop1 ρH κ σ' := by
        have : loop1 ρH κ σ' ≤ 3/4 := hloop_le'
        linarith
      have h_num : 0 ≤ 1/4 * W1top V P b ρR ρH κ σ' (p.2 - 1) (if a' < V then a' + 1 else a') +
        ∑ c, 1/4 * rest1 P ρR ρH κ (W1top V P b ρR ρH κ) σ' p.2 a' c := by
        have h_sum : 0 ≤ ∑ c, 1/4 * rest1 P ρR ρH κ (W1top V P b ρR ρH κ) σ' p.2 a' c := by
          refine Finset.sum_nonneg fun c _ => ?_
          nlinarith [h_rest c]
        nlinarith
      simpa [rest1, loop1] using div_nonneg h_num h_denom_nonneg'
  have hP_total : P_prop (rank1 σ, n) := hwf.induction (rank1 σ, n) hP
  exact hP_total σ rfl a

/-- No end above the cap. -/
theorem W1top_zero_of_lt (V P b : ℕ) (ρR ρH : ℕ → ℝ) (κ : Bool → ℕ → ℕ → ℝ)
    (hb : V < b) (σ : Fin 3 → Fin 3) (n a : ℕ) (ha : a ≤ V) : W1top V P b ρR ρH κ σ n a = 0 := by
  -- Well-founded induction on (rank1 σ, n) with lexicographic order
  let r : (Fin 3 → Fin 3) × ℕ → (Fin 3 → Fin 3) × ℕ → Prop :=
    InvImage (Prod.Lex (· < ·) (· < ·)) (λ x => (rank1 x.1, x.2))
  have h_wf : WellFounded r := by
    unfold r
    apply InvImage.wf
    exact WellFounded.prod_lex (by infer_instance) (by infer_instance)
  let C : (Fin 3 → Fin 3) × ℕ → Prop := λ ⟨σ', n'⟩ => ∀ a', a' ≤ V → W1top V P b ρR ρH κ σ' n' a' = 0
  have hC : C (σ, n) := by
    refine WellFounded.induction h_wf (σ, n) (λ x IH => ?_)
    rcases x with ⟨σ', n'⟩
    intro a' ha'
    by_cases hn' : n' = 0
    · subst hn'
      simp [W1top]
      by_cases h_eq : a' = b
      · exfalso
        have ha'_lt_b : a' < b := lt_of_le_of_lt ha' hb
        exact ne_of_lt ha'_lt_b h_eq
      · exact h_eq
    · have hn_pos : 0 < n' := Nat.pos_of_ne_zero hn'
      have hn_eq : n' = (n' - 1) + 1 := by omega
      rw [hn_eq, W1top_succ V P b ρR ρH κ σ' (n' - 1) a']
      have h_simpl : (n' - 1) + 1 = n' := Nat.sub_add_cancel hn_pos
      rw [h_simpl]
      have ha'_le : (if a' < V then a' + 1 else a') ≤ V := by
        split_ifs with h
        · omega
        · exact ha'
      have h_up : W1top V P b ρR ρH κ σ' (n' - 1) (if a' < V then a' + 1 else a') = 0 := by
        have h_r : r (σ', n' - 1) (σ', n') := by
          unfold r InvImage
          refine Prod.Lex.right (rank1 σ') ?_
          omega
        exact IH (σ', n' - 1) h_r (if a' < V then a' + 1 else a') ha'_le
      have h_rest : ∀ c, rest1 P ρR ρH κ (W1top V P b ρR ρH κ) σ' n' a' c = 0 := by
        intro c
        unfold rest1
        split_ifs with h0 h1
        · -- (σ' c).val = 0
          apply Finset.sum_eq_zero
          intro b' hb'
          have h_term1 : W1top V P b ρR ρH κ (Function.update σ' c 1) (min ((n' - 1) + b') P) a' = 0 := by
            have h_r : r (Function.update σ' c 1, min ((n' - 1) + b') P) (σ', n') := by
              unfold r InvImage
              refine Prod.Lex.left (min ((n' - 1) + b') P) n' ?_
              have h_lt : (σ' c).val < (1 : Fin 3).val := by
                simp [h0]
              exact rank1_update_lt σ' c 1 h_lt
            exact IH (Function.update σ' c 1, min ((n' - 1) + b') P) h_r a' ha'
          have h_term2 : W1top V P b ρR ρH κ (Function.update σ' c 2) (n' - 1) a' = 0 := by
            have h_r : r (Function.update σ' c 2, n' - 1) (σ', n') := by
              unfold r InvImage
              refine Prod.Lex.left (n' - 1) n' ?_
              have h_lt : (σ' c).val < (2 : Fin 3).val := by
                simp [h0]
              exact rank1_update_lt σ' c 2 h_lt
            exact IH (Function.update σ' c 2, n' - 1) h_r a' ha'
          simp [h_term1, h_term2]
        · -- (σ' c).val = 1
          have h_term1 : W1top V P b ρR ρH κ σ' (n' - 1) a' = 0 := by
            have h_r : r (σ', n' - 1) (σ', n') := by
              unfold r InvImage
              refine Prod.Lex.right (rank1 σ') ?_
              omega
            exact IH (σ', n' - 1) h_r a' ha'
          have h_term2 : W1top V P b ρR ρH κ (Function.update σ' c 2) (n' - 1) a' = 0 := by
            have h_r : r (Function.update σ' c 2, n' - 1) (σ', n') := by
              unfold r InvImage
              refine Prod.Lex.left (n' - 1) n' ?_
              have h_lt : (σ' c).val < (2 : Fin 3).val := by
                simp [h1]
              exact rank1_update_lt σ' c 2 h_lt
            exact IH (Function.update σ' c 2, n' - 1) h_r a' ha'
          simp [h_term1, h_term2]
        · -- (σ' c).val = 2
          have h_term : W1top V P b ρR ρH κ σ' (n' - 1) a' = 0 := by
            have h_r : r (σ', n' - 1) (σ', n') := by
              unfold r InvImage
              refine Prod.Lex.right (rank1 σ') ?_
              omega
            exact IH (σ', n' - 1) h_r a' ha'
          simp [h_term]
      simp [h_up, h_rest]
  exact hC a ha

/-- The ups of an R closure at height 0 (two frogs) take values in `{0, 1, 2}`. -/
theorem rhoR_sum (V L : ℕ) (hV : 2 ≤ V) :
    ∑ j ∈ Finset.range 3, U0 V L j (2, 0, 0) = 1 := by
  simp only [U0, capBin]
  have hmin : ∀ i ∈ Finset.range 3, min (0 + i) V = i := by
    intro i hi
    have hi2 : i ≤ 2 := by
      have := Finset.mem_range.1 hi
      omega
    have hiV : i ≤ V := Nat.le_trans hi2 hV
    simp [hiV]
  -- Simplify min (0+i) V = i in the inner sum
  have hsum_eq : (∑ j ∈ Finset.range 3,
      ∑ i ∈ Finset.range 3,
        if min (0 + i) V = j then ((2 : ℕ).choose i : ℝ) * (qL L) ^ i * (1 - qL L) ^ (2 - i) else 0) =
      (∑ j ∈ Finset.range 3,
      ∑ i ∈ Finset.range 3,
        if i = j then ((2 : ℕ).choose i : ℝ) * (qL L) ^ i * (1 - qL L) ^ (2 - i) else 0) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hmin i hi]
  rw [hsum_eq]
  -- Swap sums
  rw [Finset.sum_comm]
  -- Simplify the inner sum using sum_ite_eq
  have hsum_ite : ∀ i ∈ Finset.range 3, (∑ j ∈ Finset.range 3,
    if i = j then ((2 : ℕ).choose i : ℝ) * (qL L) ^ i * (1 - qL L) ^ (2 - i) else 0) =
    ((2 : ℕ).choose i : ℝ) * (qL L) ^ i * (1 - qL L) ^ (2 - i) := by
    intro i hi
    rw [Finset.sum_ite_eq, ite_eq_left hi]
  rw [Finset.sum_congr rfl (fun i hi => hsum_ite i hi)]
  -- Now: ∑ i ∈ range 3, ((2 : ℕ).choose i : ℝ) * (qL L) ^ i * (1 - qL L) ^ (2 - i) = 1
  simp [Finset.sum_range_succ]
  ring

/-- The ups of an H closure at height 0 (one frog) take values in `{0, 1}`. -/
theorem rhoH_sum (V L : ℕ) (hV : 1 ≤ V) :
    U0 V L 0 (1, 0, 0) + U0 V L 1 (1, 0, 0) = 1 := by
  unfold U0
  simp [capBin, Finset.sum_range_succ]
  have hV0 : V ≠ 0 := by omega
  simp [hV, hV0]

theorem sum_U0_ended (p : Params) (hL : 2 ≤ p.L) (u : ℕ) (hu : u ≤ p.V) (F : ℕ → ℝ) :
    ∑ b' ∈ Finset.range (p.V + 1), U0 p.V p.L b' (0, u, 0) * F b' = F u := by
  have hc := fun b' => (capBin_basic p.V (qL p.L) (qL_mem p.L hL).1 (qL_mem p.L hL).2).2.2 u b' hu
  simp only [U0, hc, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_of_le hu]

/-- **An inner read at height 1** keeps the candidate on average. -/
theorem W1_inner (p : Params) (hL : 2 ≤ p.L) (b : ℕ) (n a : ℕ) (σ : Fin 3 → Fin 3) (r : Bool)
    (c : Fin 3) (y : ℕ × ℕ × ℕ) (hd : y.2.2 < p.L) (hu : y.2.1 ≤ p.V)
    (hne : ¬(y.1 = 0 ∧ y.2.2 = 0)) (j : ℕ) :
    ∑ d : Fin 4, 1 / 4 * W1 p b (h1step p (n, a, σ, some (r, c, y, false)) (d, j)) =
      W1 p b (n, a, σ, some (r, c, y, false)) := by
  have hnext : ∀ d : Fin 4, W1 p b (h1step p (n, a, σ, some (r, c, y, false)) (d, j)) =
      ∑ b' ∈ Finset.range (p.V + 1), U0 p.V p.L b' (hstep p.V p.L y d) * K1 p b r c b' n a σ := by
    intro d
    simp only [h1step]
    by_cases he : (hstep p.V p.L y d).1 = 0 ∧ (hstep p.V p.L y d).2.2 = 0
    · rw [decide_eq_true he]
      simp only [W1]
      have hu' := hstep_ups_le p.V p.L y hu d
      rcases hy : hstep p.V p.L y d with ⟨y1, y2, y3⟩
      rw [hy] at he hu'
      simp only at he hu'
      obtain ⟨rfl, rfl⟩ := he
      rw [sum_U0_ended p hL y2 hu']
    · rw [decide_eq_false he]
      rfl
  rw [Finset.sum_congr rfl fun d _ => by rw [hnext d]]
  simp only [W1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [U0_step p.V p.L b' hL y hd hu hne, Fin.sum_univ_four, hstep_dir p.V p.L y 2 (by decide),
    hstep_dir p.V p.L y 3 (by decide)]
  ring

theorem capBin_zero_of_gt (V : ℕ) (x : ℝ) (p a b : ℕ) (h : a + p < b) : capBin V x p a b = 0 := by
  unfold capBin
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have : min (a + j) V ≠ b := by have := min_le_left (a + j) V; omega
  simp [this]

theorem sum_range_U0 (p : Params) (y : ℕ × ℕ × ℕ) (k : ℕ) (hk : k ≤ p.V + 1)
    (hy : ∀ b', k ≤ b' → U0 p.V p.L b' y = 0) (F : ℕ → ℝ) :
    ∑ b' ∈ Finset.range (p.V + 1), U0 p.V p.L b' y * F b' =
      ∑ b' ∈ Finset.range k, U0 p.V p.L b' y * F b' := by
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 hk) fun b' _ hb' => ?_
  rw [hy b' (by simpa using hb'), zero_mul]

theorem rhoR_zero (p : Params) (b' : ℕ) (h : 3 ≤ b') : U0 p.V p.L b' (2, 0, 0) = 0 :=
  capBin_zero_of_gt _ _ _ _ _ (by omega)

theorem rhoH_zero (p : Params) (b' : ℕ) (h : 2 ≤ b') : U0 p.V p.L b' (1, 0, 0) = 0 :=
  capBin_zero_of_gt _ _ _ _ _ (by omega)

theorem κ1_mem (p : Params) (r : Bool) (f b' : ℕ) : 0 ≤ κ1 p r f b' ∧ κ1 p r f b' ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  unfold κ1
  have : coinLaw {j | p.keep r 0 f b' f j = true} ≤ 1 := prob_le_one
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)

theorem ρH1_mem (p : Params) (hL : 2 ≤ p.L) (hV : 1 ≤ p.V) : 0 ≤ ρH1 p 1 ∧ ρH1 p 1 ≤ 1 := by
  have h := U0_nonneg_sum p.V p.L hL (1, 0, 0)
  have hs := rhoH_sum p.V p.L hV
  have h0 := h.1 0
  exact ⟨h.1 1, by simp only [ρH1]; linarith⟩

/-- A round of the top at height 1 into child `c`. -/
theorem W1_child (p : Params) (hV : 2 ≤ p.V) (b m a : ℕ) (σ : Fin 3 → Fin 3) (c : Fin 3)
    (hmP : m + 1 ≤ p.P) (j : ℕ) :
    W1 p b (h1step p (m + 1, a, σ, none) (c.succ, j)) =
      rest1 p.P (ρR1 p) (ρH1 p) (κ1 p) (Wt p b) σ (m + 1) a c +
        (if (σ c).val = 0 then 0 else ρH1 p 1 * κ1 p false (if (σ c).val = 1 then 3 else 0) 1) *
          Wt p b σ (m + 1) a := by
  have hsucc : (c.succ : Fin 4) ≠ 0 := Fin.succ_ne_zero c
  simp only [h1step, Nat.add_one_ne_zero, ↓reduceIte, hsucc, ↓reduceDIte, Fin.pred_succ,
    Nat.add_sub_cancel]
  by_cases h0 : (σ c).val = 0
  · simp only [h0, ↓reduceIte, W1, rest1, zero_mul, add_zero]
    rw [sum_range_U0 p _ 3 (by omega) (fun b' hb' => rhoR_zero p b' hb')]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp [K1, f0of, ρR1, Function.update_idem]
  · simp only [h0, ↓reduceIte, W1]
    rw [sum_range_U0 p _ 2 (by omega) (fun b' hb' => rhoH_zero p b' hb')]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, K1, rest1, h0,
      ↓reduceIte, add_zero, Nat.add_sub_cancel, min_eq_left (show m ≤ p.P by omega), min_eq_left hmP]
    have hc := (σ c).isLt
    by_cases h1 : (σ c).val = 1
    · simp only [h1, ↓reduceIte, f0of, ρH1]
      ring
    · have h2 : σ c = 2 := Fin.ext (by simp; omega)
      have hu : Function.update σ c 2 = σ := by rw [← h2]; exact Function.update_eq_self c σ
      simp only [h1, ↓reduceIte, f0of, ρH1, hu]
      ring

/-- **A round of the top at height 1** keeps the candidate on average. -/
theorem W1_round (p : Params) (hL : 2 ≤ p.L) (hV : 2 ≤ p.V) (b m a : ℕ) (σ : Fin 3 → Fin 3)
    (hmP : m + 1 ≤ p.P) (j : ℕ) :
    ∑ d : Fin 4, 1 / 4 * W1 p b (h1step p (m + 1, a, σ, none) (d, j)) =
      W1 p b (m + 1, a, σ, none) := by
  have hH1 := ρH1_mem p hL (by omega)
  conv_rhs => simp only [W1, Wt]
  rw [W1top_step p.V p.P b _ _ _ hH1.1 hH1.2 (fun i f b' => κ1_mem p i f b') σ m a,
    Fin.sum_univ_succ, Fin.sum_univ_three]
  rw [W1_child p hV b m a σ 0 hmP j, W1_child p hV b m a σ 1 hmP j,
    W1_child p hV b m a σ 2 hmP j, Fin.sum_univ_three]
  simp only [h1step, Nat.add_one_ne_zero, ↓reduceIte, ↓reduceDIte, Nat.add_sub_cancel, W1, Wt]


theorem rest1_sum (P : ℕ) (ρR ρH : ℕ → ℝ) (κ : Bool → ℕ → ℕ → ℝ) (s : Finset ℕ)
    (W : ℕ → (Fin 3 → Fin 3) → ℕ → ℕ → ℝ) (σ : Fin 3 → Fin 3) (n a : ℕ) (c : Fin 3) :
    ∑ b ∈ s, rest1 P ρR ρH κ (W b) σ n a c =
      rest1 P ρR ρH κ (fun σ' n' a' => ∑ b ∈ s, W b σ' n' a') σ n a c := by
  unfold rest1
  split_ifs
  · rw [Finset.sum_comm]
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  · simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  · simp only [Finset.mul_sum, Finset.sum_add_distrib]

/-- The candidate at height 1 is a probability law on `{0, ..., V}`. -/
theorem W1top_sum (V P : ℕ) (ρR ρH : ℕ → ℝ) (κ : Bool → ℕ → ℕ → ℝ)
    (hH : ∀ j, 0 ≤ ρH j) (hRs : ∑ j ∈ Finset.range 3, ρR j = 1)
    (hHs : ρH 0 + ρH 1 = 1) (hκ : ∀ i f j, 0 ≤ κ i f j ∧ κ i f j ≤ 1) (σ : Fin 3 → Fin 3)
    (n a : ℕ) (ha : a ≤ V) :
    ∑ b ∈ Finset.range (V + 1), W1top V P b ρR ρH κ σ n a = 1 := by
  have hH1 : ρH 1 ≤ 1 := by linarith [hH 0]
  let r : (Fin 3 → Fin 3) × ℕ → (Fin 3 → Fin 3) × ℕ → Prop :=
    InvImage (Prod.Lex (· < ·) (· < ·)) (fun x => (rank1 x.1, x.2))
  have hwf : WellFounded r := InvImage.wf _ (WellFounded.prod_lex wellFounded_lt wellFounded_lt)
  let C : (Fin 3 → Fin 3) × ℕ → Prop := fun x =>
    ∀ a', a' ≤ V → ∑ b ∈ Finset.range (V + 1), W1top V P b ρR ρH κ x.1 x.2 a' = 1
  suffices h : C (σ, n) from h a ha
  refine hwf.induction (σ, n) fun x IH => ?_
  obtain ⟨σ', n'⟩ := x
  intro a' ha'
  rcases n' with _ | m
  · simp only [W1top_zero]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range, Nat.lt_succ_of_le ha']
  · have hl := loop1_le ρH κ (hH 1) hH1 hκ σ'
    have hd : 1 - loop1 ρH κ σ' ≠ 0 := by linarith [hl.2]
    have hup : (if a' < V then a' + 1 else a') ≤ V := by split_ifs <;> omega
    have IHn : ∀ a'', a'' ≤ V → ∑ b ∈ Finset.range (V + 1), W1top V P b ρR ρH κ σ' m a'' = 1 :=
      IH (σ', m) (Prod.Lex.right _ (Nat.lt_succ_self m))
    have IHr : ∀ t : Fin 3, ∀ c, (σ' c).val < t.val → ∀ k a'', a'' ≤ V →
        ∑ b ∈ Finset.range (V + 1), W1top V P b ρR ρH κ (Function.update σ' c t) k a'' = 1 :=
      fun t c h k => IH (Function.update σ' c t, k) (Prod.Lex.left _ _ (rank1_update_lt σ' c t h))
    simp only [W1top_succ]
    rw [← Finset.sum_div, div_eq_one_iff_eq hd, Finset.sum_add_distrib, ← Finset.mul_sum,
      IHn _ hup, Finset.sum_comm]
    have hc : ∀ c, ∑ b ∈ Finset.range (V + 1), 1 / 4 * rest1 P ρR ρH κ (W1top V P b ρR ρH κ) σ'
        (m + 1) a' c = 1 / 4 - (if (σ' c).val = 0 then 0 else
          1 / 4 * ρH 1 * κ false (if (σ' c).val = 1 then 3 else 0) 1) := by
      intro c
      rw [← Finset.mul_sum, rest1_sum]
      unfold rest1
      simp only [Nat.add_sub_cancel]
      have hc3 := (σ' c).isLt
      by_cases h0 : (σ' c).val = 0
      · simp only [h0, ↓reduceIte, sub_zero]
        rw [Finset.sum_congr rfl fun b' _ => by
          rw [IHr 1 c (by simp [h0]) _ _ ha', IHr 2 c (by simp [h0]) _ _ ha']]
        simp only [mul_one, add_sub_cancel, hRs]
      · by_cases h1 : (σ' c).val = 1
        · simp only [h1, one_ne_zero, ↓reduceIte, IHn a' ha', IHr 2 c (by simp [h1]) _ _ ha']
          linear_combination (1 / 4 : ℝ) * hHs
        · simp only [h0, h1, ↓reduceIte, IHn a' ha']
          linear_combination (1 / 4 : ℝ) * hHs
    rw [Finset.sum_congr rfl fun c _ => hc c]
    simp only [loop1, Fin.sum_univ_three]
    ring

theorem rank1_update_eq (σ : Fin 3 → Fin 3) (c t : Fin 3) :
    rank1 (Function.update σ c t) + t.val = rank1 σ + (σ c).val := by
  unfold rank1
  simp only [Fin.sum_univ_three]
  have h0 := (σ 0).isLt
  have h1 := (σ 1).isLt
  have h2 := (σ 2).isLt
  have ht := t.isLt
  fin_cases c <;> simp <;> omega

theorem rhoH_vals (p : Params) (hV : 1 ≤ p.V) :
    ρH1 p 0 = 1 - qL p.L ∧ ρH1 p 1 = qL p.L ∧ ∀ b', 2 ≤ b' → ρH1 p b' = 0 := by
  refine ⟨?_, ?_, fun b' hb' => rhoH_zero p b' hb'⟩ <;>
  · simp only [ρH1, U0, capBin, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [hV]

theorem Wt_nonneg (p : Params) (hL : 2 ≤ p.L) (hV : 2 ≤ p.V) (b : ℕ) (σ : Fin 3 → Fin 3)
    (n a : ℕ) : 0 ≤ Wt p b σ n a := by
  have hH := fun j => (U0_nonneg_sum p.V p.L hL (1, 0, 0)).1 j
  have hR := fun j => (U0_nonneg_sum p.V p.L hL (2, 0, 0)).1 j
  exact W1top_nonneg p.V p.P b _ _ _ hR hH (rhoR_sum p.V p.L hV) (rhoH_sum p.V p.L (by omega))
    (fun i f j => κ1_mem p i f j) σ n a

theorem Wt_sum (p : Params) (hL : 2 ≤ p.L) (hV : 2 ≤ p.V) (σ : Fin 3 → Fin 3) (n a : ℕ)
    (ha : a ≤ p.V) : ∑ b ∈ Finset.range (p.V + 1), Wt p b σ n a = 1 := by
  have hH := fun j => (U0_nonneg_sum p.V p.L hL (1, 0, 0)).1 j
  exact W1top_sum p.V p.P _ _ _ hH (rhoR_sum p.V p.L hV) (rhoH_sum p.V p.L (by omega))
    (fun i f j => κ1_mem p i f j) σ n a ha

end FrogModel.D3
