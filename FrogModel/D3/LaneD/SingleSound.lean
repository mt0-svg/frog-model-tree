module

public import FrogModel.D3.Interfaces.Seed
public import FrogModel.D3.LaneD.Decode
public import FrogModel.D3.LaneD.Terms
public import FrogModel.D3.LaneD.K.Single

@[expose] public section

/-!
# The terms checked at a single height, sound

The loops `allN`, `anyN`; the cdf terms `L` (`lterm_sound`, through `lemma12B_check`) and `C`
(`cOK_sound`); the shape of a stored state (`shapeOK_sound`); and `rows_le`, the induction over the
rows (`k` up) and the entries (`g` down) shared by the seed and the extension: a row `k` of the form
`min over g' ≥ g of pre k g' (row k - 1 at g')` is below a stored row whose every entry passes the
term `G` (the stored entry `g + 1`), `J` (the stored entry of row `k - 1`) or a term bounding `pre`.
-/

namespace FrogModel.D3.LaneD

open FrogModel.D3.Iface FrogModel.D3.LaneD.K

theorem shl_eq (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem allN_eq_true (n : ℕ) (f : ℕ → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    have e : allN (n + 1) f = (allN n f && f n) := rfl
    rw [e, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem anyN_eq_true (n : ℕ) (f : ℕ → Bool) : anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun h => (by cases h), fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    have e : anyN (n + 1) f = (anyN n f || f n) := rfl
    rw [e, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl
      · exact Or.inl ⟨i, h', h⟩
      · exact Or.inr h

theorem mu_eq (m k : ℕ) : mu m k = ((m + 1 + k : ℕ) : ℝ) / 3 := by
  unfold mu
  push_cast
  ring

theorem one_le_of (o : ℕ) (h : one52 ≤ o) (x : ℝ) (hx : x ≤ 1) : x ≤ (o : ℝ) / 2 ^ 52 := by
  have h' : (2 : ℝ) ^ 52 ≤ o := by
    have e : one52 = 2 ^ 52 := (shl_eq 1 52).trans (one_mul _)
    rw [e] at h
    exact_mod_cast h
  exact hx.trans ((one_le_div (by positivity)).2 h')

theorem lterm_sound (N od rho v o : ℕ) (D : ℝ) (hD : D ≤ (od : ℝ) / 2 ^ 52 * ((N : ℝ) / 3))
    (h : lOK N (Nat.shiftLeft od 76) rho v o = true) : L12 D ((N : ℝ) / 3) v ≤ (o : ℝ) / 2 ^ 52 := by
  unfold lOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.mul_eq, Nat.add_eq, Nat.sub_eq, shl_eq] at h
  obtain ⟨⟨hv, hrho⟩, hc⟩ := h
  unfold L12
  refine (min_le_left _ _).trans (lemma12B_check N v (od * 2 ^ 76) rho o D ?_ ?_ hv hc)
  · calc D ≤ (od : ℝ) / 2 ^ 52 * ((N : ℝ) / 3) := hD
      _ = ((od * 2 ^ 76 : ℕ) : ℝ) / 2 ^ 128 * ((N : ℝ) / 3) := by push_cast; ring
  · rw [sq]
    exact hrho

theorem cOK_sound (k v o : ℕ) (h : cOK k v o = true) : binCdf k (1 / 3) v ≤ (o : ℝ) / 2 ^ 52 := by
  unfold cOK at h
  simp only [Nat.ble_eq, shl_eq, Nat.mul_eq, Nat.pow_eq] at h
  rw [binCdf_third, div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast h

theorem shapeOK_sound (P : StParams) (F : List ℕ) (D : ℕ) (h : shapeOK P.E P.GM F D = true) :
    (decState F D).WF P := by
  have e52 : one52 = 2 ^ 52 := (shl_eq 1 52).trans (one_mul _)
  unfold shapeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, allN_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.add_eq,
    e52] at h
  obtain ⟨⟨⟨hrow, hD⟩, h0F⟩, h0D⟩ := h
  refine decState_WF P F D (fun k hk g hg => (hrow k (by omega) g (by omega)).1)
    (fun k hk g hg => ?_) (fun k hk => hD k (by omega)) (fun g hg => h0F g (by omega)) h0D
  rcases (hrow k (by omega) g (by omega)).2 with h | h
  · omega
  · exact h

theorem rows_le (E GM : ℕ) (pre : ℕ → ℕ → ℝ → ℝ) (Fr : ℕ → ℕ → ℝ) (h0 : ∀ g, Fr 0 g = 1)
    (hs : ∀ k g, Fr (k + 1) g =
      (Finset.Icc g GM).fold min (pre (k + 1) g (Fr k g)) fun g' => pre (k + 1) g' (Fr k g'))
    (hpre : ∀ k g x, pre k g x ≤ x) (out : ℕ → ℕ → ℝ) (hout0 : ∀ g ≤ GM, 1 ≤ out 0 g)
    (hent : ∀ k, 1 ≤ k → k ≤ E → ∀ g ≤ GM,
      (g < GM ∧ out k (g + 1) ≤ out k g) ∨ out (k - 1) g ≤ out k g ∨ ∀ x, pre k g x ≤ out k g) :
    ∀ k ≤ E, ∀ g ≤ GM, Fr k g ≤ out k g := by
  -- (a) a row is at most its terms at `g`
  have ha : ∀ k g, Fr (k + 1) g ≤ pre (k + 1) g (Fr k g) := fun k g => by
    rw [hs]; exact (Finset.fold_min_le _).2 (Or.inl le_rfl)
  -- (b) a row is nondecreasing in `g`
  have hb : ∀ k g, g < GM → Fr (k + 1) g ≤ Fr (k + 1) (g + 1) := fun k g hg => by
    rw [hs k (g + 1), Finset.le_fold_min]
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hs]
      exact (Finset.fold_min_le _).2 (Or.inr ⟨g + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, le_rfl⟩)
    · obtain ⟨_, h2⟩ := Finset.mem_Icc.1 hx
      rw [hs]
      exact (Finset.fold_min_le _).2 (Or.inr ⟨x, Finset.mem_Icc.2 ⟨by omega, h2⟩, le_rfl⟩)
  intro k
  induction k with
  | zero => intro _ g hg; rw [h0]; exact hout0 g hg
  | succ k ih =>
    intro hk
    have hJ' : ∀ g ≤ GM, out (k + 1 - 1) g ≤ out (k + 1) g → Fr (k + 1) g ≤ out (k + 1) g :=
      fun g hg hJ => (ha k g).trans ((hpre _ _ _).trans ((ih (by omega) g hg).trans (by simpa using hJ)))
    have key : ∀ i g, g ≤ GM → GM - g = i → Fr (k + 1) g ≤ out (k + 1) g := by
      intro i
      induction i with
      | zero =>
        intro g hg hi
        rcases hent (k + 1) (by omega) hk g hg with ⟨hlt, _⟩ | hJ | hT
        · omega
        · exact hJ' g hg hJ
        · exact (ha k g).trans (hT _)
      | succ i ihi =>
        intro g hg hi
        rcases hent (k + 1) (by omega) hk g hg with ⟨hlt, hG⟩ | hJ | hT
        · exact (hb k g hlt).trans ((ihi (g + 1) hlt (by omega)).trans hG)
        · exact hJ' g hg hJ
        · exact (ha k g).trans (hT _)
    intro g hg
    exact key _ g hg rfl

end FrogModel.D3.LaneD
