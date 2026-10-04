module

public import FrogModel.Lanes.Basic
public import FrogModel.D3.M1K.Check

@[expose] public section

/-!
# Packed rows and tables: the arithmetic of the checker

The loops and packings of `FrogModel/D3/M1K/Check.lean` in terms of `FrogModel.Lanes.pack`:
`packTree` is a `pack`, `blocks` lists the blocks of a number, a product of two packs is the pack
of the convolution (Kronecker substitution), a pack divided by or reduced modulo a power of the
base is the pack of the shifted or truncated lanes.
-/

open FrogModel.Lanes

namespace FrogModel.D3.M1K

theorem natFold_zero {α : Type} (init : α) (f : ℕ → α → α) : natFold 0 init f = init := rfl

theorem natFold_succ {α : Type} (n : ℕ) (init : α) (f : ℕ → α → α) :
    natFold (n + 1) init f = f n (natFold n init f) := rfl

theorem natFold_sum (n : ℕ) (g : ℕ → ℕ) :
    natFold n 0 (fun l acc => Nat.add acc (g l)) = ∑ l ∈ Finset.range n, g l := by
  induction n with
  | zero => rfl
  | succ n ih => rw [natFold_succ, ih, Finset.sum_range_succ]; rfl

theorem pack_sum {ι : Type} (s : Finset ι) (B n : ℕ) (f : ι → ℕ → ℕ) :
    ∑ i ∈ s, pack B n (f i) = pack B n (fun l => ∑ i ∈ s, f i l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pack]
  | insert a s ha ih => rw [Finset.sum_insert ha, ih, pack_add]; simp [Finset.sum_insert ha]

theorem pack_add_len (B n m : ℕ) (g : ℕ → ℕ) :
    pack B (n + m) g = pack B n g + pack B m (fun j => g (n + j)) * 2 ^ (B * n) := by
  unfold pack
  rw [Finset.sum_range_add, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_add, pow_add]; ring

theorem packTree_succ (B : ℕ) (f : ℕ → ℕ) (i lo : ℕ) :
    packTree B f (i + 1) lo = packTree B f i lo +
      packTree B f i (lo + 2 ^ i) * 2 ^ (B * 2 ^ i) := by
  have h : packTree B f (i + 1) lo = Nat.add (packTree B f i lo)
      (Nat.shiftLeft (packTree B f i (Nat.add lo (Nat.pow 2 i))) (Nat.mul B (Nat.pow 2 i))) := rfl
  rw [h, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [show ∀ a b : ℕ, Nat.shiftLeft a b = a <<< b from fun _ _ => rfl, Nat.shiftLeft_eq]

theorem ofFn_eq_map_range {α : Type} (n : ℕ) (g : ℕ → α) :
    List.ofFn (fun j : Fin n => g j) = (List.range n).map g := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp

theorem blocks_succ (B i x : ℕ) (acc : List ℕ) :
    blocks B (i + 1) x acc =
      blocks B i (x % 2 ^ (B * 2 ^ i)) (blocks B i (x / 2 ^ (B * 2 ^ i)) acc) := by
  have h : blocks B (i + 1) x acc = blocks B i (Nat.mod x (Nat.pow 2 (Nat.mul B (Nat.pow 2 i))))
      (blocks B i (Nat.shiftRight x (Nat.mul B (Nat.pow 2 i))) acc) := rfl
  rw [h, Nat.mul_eq, Nat.pow_eq, Nat.pow_eq,
    show ∀ a b : ℕ, Nat.shiftRight a b = a >>> b from fun _ _ => rfl, Nat.shiftRight_eq_div_pow]
  rfl

theorem packTree_eq (B : ℕ) (f : ℕ → ℕ) (d lo : ℕ) :
    packTree B f d lo = pack B (2 ^ d) (fun j => f (lo + j)) := by
  induction d generalizing lo with
  | zero => simp [packTree, pack]
  | succ i ih =>
    rw [packTree_succ, ih, ih, pow_succ, mul_two, pack_add_len]
    simp only [Nat.add_assoc]

theorem blocks_eq (B d x : ℕ) (acc : List ℕ) :
    blocks B d x acc = List.ofFn (fun j : Fin (2 ^ d) => x / 2 ^ (B * j) % 2 ^ B) ++ acc := by
  rw [ofFn_eq_map_range (2 ^ d) (fun j => x / 2 ^ (B * j) % 2 ^ B)]
  induction d generalizing x acc with
  | zero => simp; rfl
  | succ i ih =>
    rw [blocks_succ, ih, ih, pow_succ, mul_two, List.range_add, List.map_append, List.map_map,
      List.append_assoc]
    congr 1
    · refine List.map_congr_left fun j hj => ?_
      rw [List.mem_range] at hj
      have hb : B * (j + 1) ≤ B * 2 ^ i := Nat.mul_le_mul_left B hj
      rw [mul_add, mul_one] at hb
      apply Nat.eq_of_testBit_eq
      intro n
      simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
      by_cases hn : n < B
      · have : n + B * j < B * 2 ^ i := by omega
        simp [hn, this]
      · simp [hn]
    · congr 1
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp, Nat.div_div_eq_div_mul, ← pow_add, ← mul_add]

theorem pack_mul_pack (B n m : ℕ) (f g : ℕ → ℕ) :
    pack B n f * pack B m g =
      pack B (n + m) (fun k => ∑ i ∈ Finset.range n, if i ≤ k ∧ k - i < m then f i * g (k - i) else 0) := by
  unfold pack
  rw [Finset.sum_mul_sum, eq_comm]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun k => k - i) (fun j => i + j) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega
  · intro j hj
    simp
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, h1, _⟩ := hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h1
    simp only [Nat.add_sub_cancel_left]
    rw [mul_add, pow_add]; ring

theorem pack_div_pow (B n k : ℕ) (f : ℕ → ℕ) (hf : ∀ l < n, f l < 2 ^ B) :
    pack B n f / 2 ^ (B * k) = pack B (n - k) (fun j => f (j + k)) := by
  rcases le_or_gt k n with hk | hk
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pack_add_len, Nat.add_sub_cancel_left]
    have hlt : pack B k f < 2 ^ (B * k) := pack_lt B k f (fun l hl => hf l (by omega))
    rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
    congr 1; funext j; rw [Nat.add_comm]
  · rw [Nat.sub_eq_zero_of_le hk.le]
    have hlt : pack B n f < 2 ^ (B * k) :=
      lt_of_lt_of_le (pack_lt B n f hf) (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left B hk.le))
    rw [Nat.div_eq_of_lt hlt]; simp [pack]

end FrogModel.D3.M1K
