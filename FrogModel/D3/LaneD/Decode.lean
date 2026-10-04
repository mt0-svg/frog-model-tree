module

public import FrogModel.D3.Interfaces.Step
public import FrogModel.D3.LaneD.Pack

@[expose] public section

/-!
# The stored states

A stored state is a list of cdf rows (row `k`, 64-bit slot `g`) and a natural of deficits (64-bit
slot `k`), every value at `2^-52`. `decState F D` is the state they denote, `decState_WF` its shape
from bounds on the slots, and `shapeRow_spec`, `shapeVec_spec` those bounds from the shape checks of
the kernel code.
-/

namespace FrogModel.D3.LaneD

open FrogModel.D3.Iface FrogModel.D3.LaneD.K

/-- The state stored in the rows `F` and the deficits `D`, at `2^-52`. -/
noncomputable def decState (F : List ℕ) (D : ℕ) : State :=
  ⟨fun k g => (slot 64 (getN F k) g : ℝ) / 2 ^ 52, fun k => (slot 64 D k : ℝ) / 2 ^ 52⟩

theorem decState_WF (P : StParams) (F : List ℕ) (D : ℕ)
    (hF : ∀ k ≤ P.E, ∀ g ≤ P.GM, slot 64 (getN F k) g ≤ 2 ^ 52)
    (hmono : ∀ k ≤ P.E, ∀ g < P.GM, slot 64 (getN F k) g ≤ slot 64 (getN F k) (g + 1))
    (hD : ∀ k ≤ P.E, slot 64 D k ≤ 2 ^ 52) (h0F : ∀ g ≤ P.GM, slot 64 (getN F 0) g = 2 ^ 52)
    (h0D : slot 64 D 0 = 2 ^ 52) : (decState F D).WF P := by
  have h52 : (0 : ℝ) < 2 ^ 52 := by positivity
  refine ⟨fun k hk g hg => ⟨by simp only [decState]; positivity, ?_⟩, fun k hk g hg => ?_,
    fun k hk => ⟨by simp only [decState]; positivity, ?_⟩, fun g hg => ?_, ?_⟩
  · simp only [decState]
    rw [div_le_one h52]
    exact_mod_cast hF k hk g hg
  · simp only [decState]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmono k hk g hg) h52.le
  · simp only [decState]
    rw [div_le_one h52]
    exact_mod_cast hD k hk
  · simp only [decState]
    rw [h0F g hg, Nat.cast_pow, Nat.cast_ofNat]
    exact div_self h52.ne'
  · simp only [decState]
    rw [h0D, Nat.cast_pow, Nat.cast_ofNat]
    exact div_self h52.ne'

theorem dec_natFold_succ {α : Type} (n : ℕ) (init : α) (f : ℕ → α → α) :
    natFold (n + 1) init f = f n (natFold n init f) := rfl

/-- The loop of `shapeRow`: the failure count is the sum of the tests of each slot. -/
theorem shapeRow_fold (n row : ℕ) :
    natFold n ((0 : ℕ), (0 : ℕ)) (fun g (st : ℕ × ℕ) =>
      (Nat.add st.1 (Nat.add (bad (slot 64 row g) one52) (bad st.2 (slot 64 row g))), slot 64 row g)) =
    (∑ g ∈ Finset.range n, (bad (slot 64 row g) one52 +
      bad (if g = 0 then 0 else slot 64 row (g - 1)) (slot 64 row g)),
      if n = 0 then 0 else slot 64 row (n - 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dec_natFold_succ, ih, Finset.sum_range_succ]
    simp only [Nat.add_eq, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]

theorem shapeRow_spec (n row : ℕ) (h : shapeRow n row = 0) :
    (∀ g < n, slot 64 row g ≤ 2 ^ 52) ∧ ∀ g, g + 1 < n → slot 64 row g ≤ slot 64 row (g + 1) := by
  have h' : ∑ g ∈ Finset.range n, (bad (slot 64 row g) one52 +
      bad (if g = 0 then 0 else slot 64 row (g - 1)) (slot 64 row g)) = 0 :=
    (congrArg Prod.fst (shapeRow_fold n row)).symm.trans h
  rw [Finset.sum_eq_zero_iff] at h'
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · have := (Nat.add_eq_zero_iff.1 (h' g (Finset.mem_range.2 hg))).1
    rw [bad_eq_zero] at this
    exact this
  · have := (Nat.add_eq_zero_iff.1 (h' (g + 1) (Finset.mem_range.2 hg))).2
    rw [bad_eq_zero] at this
    simpa using this

theorem shapeVec_spec (n row : ℕ) (h : shapeVec n row = 0) : ∀ g < n, slot 64 row g ≤ 2 ^ 52 := by
  have h' : ∑ g ∈ Finset.range n, bad (slot 64 row g) one52 = 0 := (natFold_add n _).symm.trans h
  intro g hg
  have := (Finset.sum_eq_zero_iff.1 h') g (Finset.mem_range.2 hg)
  rw [bad_eq_zero] at this
  exact this

end FrogModel.D3.LaneD
