module

public import FrogModel.D3.LaneD.SingleSound
public import FrogModel.D3.LaneD.K.Ext

@[expose] public section

/-!
# The extension check is sound

`extCheck_sound`: if `K.extCheck` accepts the input state `(Fi, Di)` at `(E0, G0) = (P0.E, P0.GM)` and the
stored output `(Fo, Do)` at `(E, GM) = (P.E, P.GM)`, at height `h`, then `(E0, G0) ≤ (E, GM)`, the stored
output is at least `ext P0 P h` of the input (Definition 12.4 of the paper, Step.lean) and it is well
formed at `P`.

The deficit terms as exact integer comparisons: `T` (`ext_T_le`) and `X` (`ext_X_le`); the induction
over the deficits through the order of `deltaExt` (`deltaExt_le`).
-/

namespace FrogModel.D3.LaneD

open FrogModel.D3.Iface FrogModel.D3.LaneD.K

theorem ext_T_le (h k o : ℕ) (hc : 2 ^ 52 * (h + 1) ≤ o * (h + 1 + k)) :
    mu h 0 / mu h k ≤ (o : ℝ) / 2 ^ 52 := by
  have h' : (2 : ℝ) ^ 52 * ((h : ℝ) + 1) ≤ (o : ℝ) * ((h : ℝ) + 1 + k) := by exact_mod_cast hc
  unfold mu
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem ext_X_le (h E0 k a o : ℕ) (hc : a * (h + 1 + E0) ≤ o * (h + 1 + k)) :
    (a : ℝ) / 2 ^ 52 * mu h E0 / mu h k ≤ (o : ℝ) / 2 ^ 52 := by
  have h' : (a : ℝ) * ((h : ℝ) + 1 + E0) ≤ (o : ℝ) * ((h : ℝ) + 1 + k) := by exact_mod_cast hc
  unfold mu
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  field_simp
  linarith

theorem deltaExt_le (P0 : StParams) (h : ℕ) (S : State) (out : ℕ → ℝ) (E : ℕ) (h0 : 1 ≤ out 0)
    (hk : ∀ k, 1 ≤ k → k ≤ E → 1 ≤ out k ∨ mu h 0 / mu h k ≤ out k ∨ out (k - 1) ≤ out k ∨
      (k ≤ P0.E ∧ S.delta k ≤ out k) ∨ (P0.E < k ∧ S.delta P0.E * mu h P0.E / mu h k ≤ out k)) :
    ∀ k ≤ E, deltaExt P0 h S k ≤ out k := by
  intro k
  induction k with
  | zero => intro _; exact h0
  | succ k ih =>
    intro hk'
    have e : deltaExt P0 h S (k + 1) = min (min 1 (mu h 0 / mu h (k + 1)))
        (min (deltaExt P0 h S k) (if k + 1 ≤ P0.E then S.delta (k + 1)
          else S.delta P0.E * mu h P0.E / mu h (k + 1))) := rfl
    rw [e]
    rcases hk (k + 1) (by omega) hk' with h1 | hT | hP | ⟨hle, hc⟩ | ⟨hlt, hX⟩
    · exact min_le_of_left_le (min_le_of_left_le h1)
    · exact min_le_of_left_le (min_le_of_right_le hT)
    · exact min_le_of_right_le (min_le_of_left_le ((ih (by omega)).trans (by simpa using hP)))
    · exact min_le_of_right_le (min_le_of_right_le (by rw [ite_eq_left hle]; exact hc))
    · exact min_le_of_right_le (min_le_of_right_le (by rw [ite_eq_right (by omega)]; exact hX))

theorem preExt_le_copy (P0 : StParams) (h : ℕ) (S : State) (k g : ℕ) (prev : ℝ) :
    preExt P0 h S k g prev ≤ if k ≤ P0.E ∧ g ≤ P0.GM then S.F k g else 1 :=
  min_le_of_left_le (min_le_left _ _)

theorem preExt_le_C (P0 : StParams) (h : ℕ) (S : State) (k g : ℕ) (prev : ℝ) :
    preExt P0 h S k g prev ≤ binCdf k (1 / 3) g :=
  min_le_of_left_le (min_le_right _ _)

theorem preExt_le_L (P0 : StParams) (h : ℕ) (S : State) (k g : ℕ) (prev : ℝ) :
    preExt P0 h S k g prev ≤ L12 (deltaExt P0 h S k * mu h k) (mu h k) g :=
  min_le_of_right_le (min_le_left _ _)

theorem preExt_le_prev (P0 : StParams) (h : ℕ) (S : State) (k g : ℕ) (prev : ℝ) :
    preExt P0 h S k g prev ≤ prev :=
  min_le_of_right_le (min_le_right _ _)

/-- **The extension check is sound.** -/
theorem extCheck_sound (P0 P : StParams) (h : ℕ) (Fi : List ℕ) (Di : ℕ) (Fo : List ℕ) (Do : ℕ) (hint : ℕ)
    (hc : K.extCheck P0.E P0.GM P.E P.GM h Fi Di Fo Do hint = true) :
    P0.E ≤ P.E ∧ P0.GM ≤ P.GM ∧ (ext P0 P h (decState Fi Di)).Le P (decState Fo Do) ∧
      (decState Fo Do).WF P := by
  simp only [K.extCheck, Bool.and_eq_true, Nat.ble_eq, allN_eq_true] at hc
  obtain ⟨⟨⟨⟨hE, hG⟩, hshape⟩, hdef⟩, hrow⟩ := hc
  have hWF : (decState Fo Do).WF P := shapeOK_sound P Fo Do hshape
  have hmu : ∀ k, 0 < mu h k := fun k => by unfold mu; positivity
  have h52 : (0 : ℝ) < 2 ^ 52 := by positivity
  have hone : ∀ o : ℕ, one52 ≤ o → 1 ≤ (o : ℝ) / 2 ^ 52 := fun o ho => one_le_of o ho 1 le_rfl
  -- the deficits
  have hdelta : ∀ k ≤ P.E, deltaExt P0 h (decState Fi Di) k ≤ (slot 64 Do k : ℝ) / 2 ^ 52 := by
    refine deltaExt_le P0 h _ _ P.E (le_of_eq hWF.2.2.2.2.symm) fun k hk1 hk => ?_
    have hd := hdef (k - 1) (by omega)
    rw [show Nat.add (k - 1) 1 = k by simp only [Nat.add_eq]; omega] at hd
    simp only [K.extDef, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.add_eq,
      Nat.sub_eq, Nat.mul_eq] at hd
    rcases hd with (((h1 | hT) | hP) | ⟨hk0, hcp⟩) | ⟨hk0, hX⟩
    · exact Or.inl (hone _ h1)
    · rw [show one52 = 2 ^ 52 from (shl_eq 1 52).trans (one_mul _)] at hT
      exact Or.inr (Or.inl (ext_T_le h k _ hT))
    · exact Or.inr (Or.inr (Or.inl (div_le_div_of_nonneg_right (by exact_mod_cast hP) h52.le)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hk0, div_le_div_of_nonneg_right (by exact_mod_cast hcp)
        h52.le⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hk0, ext_X_le h P0.E k _ _ hX⟩)))
  refine ⟨hE, hG, ⟨fun k hk g hg => ?_, hdelta⟩, hWF⟩
  -- the cdf rows, by `rows_le`
  have hout0 : ∀ g ≤ P.GM, 1 ≤ (slot 64 (getN Fo 0) g : ℝ) / 2 ^ 52 :=
    fun g hg => le_of_eq (hWF.2.2.2.1 g hg).symm
  refine rows_le P.E P.GM (preExt P0 h (decState Fi Di)) (FExt P0 P h (decState Fi Di)) (fun _ => rfl)
    (fun _ _ => rfl) (fun k g x => preExt_le_prev P0 h _ k g x)
    (fun k g => (slot 64 (getN Fo k) g : ℝ) / 2 ^ 52) hout0 ?_ k hk g hg
  intro k hk1 hk g hg
  have hr := hrow (k - 1) (by omega)
  rw [show Nat.add (k - 1) 1 = k by simp only [Nat.add_eq]; omega] at hr
  simp only [K.extRow, allN_eq_true] at hr
  have he := hr g (by simp only [Nat.add_eq]; omega)
  simp only [K.extEntry, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.add_eq,
    Nat.sub_eq] at he
  rcases he with ((((⟨hg', hn⟩ | hJ) | ⟨⟨hkE, hgG⟩, hcp⟩) | h1) | hL) | hC
  · exact Or.inl ⟨hg', div_le_div_of_nonneg_right (by exact_mod_cast hn) h52.le⟩
  · exact Or.inr (Or.inl (div_le_div_of_nonneg_right (by exact_mod_cast hJ) h52.le))
  · refine Or.inr (Or.inr fun x => (preExt_le_copy P0 h _ k g x).trans ?_)
    rw [ite_eq_left ⟨hkE, hgG⟩]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcp) h52.le
  · exact Or.inr (Or.inr fun x => (preExt_le_C P0 h _ k g x).trans
      ((binCdf_le_one _ _ _ (by norm_num) (by norm_num)).trans (hone _ h1)))
  · refine Or.inr (Or.inr fun x => (preExt_le_L P0 h _ k g x).trans ?_)
    have hm : mu h k = ((h + 1 + k : ℕ) : ℝ) / 3 := mu_eq h k
    rw [hm]
    refine lterm_sound (h + 1 + k) (slot 64 Do k) _ g _ _ ?_ hL
    rw [← hm]
    exact mul_le_mul_of_nonneg_right (hdelta k hk) (hmu k).le
  · exact Or.inr (Or.inr fun x => (preExt_le_C P0 h _ k g x).trans (cOK_sound _ _ _ hC))

end FrogModel.D3.LaneD
