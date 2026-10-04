module

public import FrogModel.D3.Interfaces.Seed

@[expose] public section

/-!
# Sub-solutions of the recursions of Section 13 of the paper

The remark after Proposition 13.3: with the stored inputs fixed, every operation of the R recursion
`Wrec` and of the H recursion `Yrec` is nondecreasing in the values it reads. So a table `T` whose
first row is below the first row of the recursion and whose every later row is below the step of the
recursion applied to `T` itself lies below the recursion (`wrec_lower`, `yrec_lower`).
-/

open FrogModel.D3.Iface

namespace FrogModel.D3.M1K

/-- The event term of the child `c` in the step of the R recursion, read on a table `T`. -/
noncomputable def evC (V P : ℕ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (T : (Fin 3 → CType) → ℕ → ℕ → ℕ → ℝ) (σ : Fin 3 → CType) (c : Fin 3) (p x g : ℕ) : ℝ :=
  match σ c with
  | none => ∑ b ∈ Finset.range (V + 1), ∑ f' : Fin 4,
      ρ b f' * T (Function.update σ c (some f')) (min (p + b) P) x g
  | some t => ∑ a ∈ Finset.range (V + 1), ∑ f' : Fin 4,
      if f' < t then K t a f' * T (Function.update σ c (some f')) (min (p + a) P) x g else 0

/-- The step of the R recursion (Section 13 of the paper, the loop solved out) read on a table `T`. -/
noncomputable def wBody (V P : ℕ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (T : (Fin 3 → CType) → ℕ → ℕ → ℕ → ℝ) (σ : Fin 3 → CType) (p x g : ℕ) : ℝ :=
  (1 / 4 * upV V (fun x' g' => T σ p x' g') x g + lostS K σ * T σ p x g +
      1 / 4 * ∑ c : Fin 3, evC V P ρ K T σ c p x g) / (1 - loopS K σ)

/-- The step of the H recursion read on a table `T` (`f` the count of the kid). -/
noncomputable def yBody (V P L : ℕ) (rb : ℕ → ℝ) (T : ℕ → ℕ → ℕ → ℕ → ℝ) (f s a f' : ℕ) : ℝ :=
  (1 / 4 * upV V (fun a' f'' => T f s a' f'') a f' +
      (3 - (f : ℝ)) / 4 * (1 - pL L) * T f s a f' +
      (if f = 0 then 0 else
        (f : ℝ) / 4 * ∑ b ∈ Finset.range (V + 1), rb b * T (f - 1) (min (s + b) P) a f')) /
    (1 - (3 - (f : ℝ)) * pL L / 4)

theorem wrec_succ (V P : ℕ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (σ : Fin 3 → CType)
    (p x g : ℕ) : Wrec V P ρ K σ (p + 1) x g = wBody V P ρ K (Wrec V P ρ K) σ p x g := by
  rw [Wrec.eq_2]
  unfold wBody
  congr 3
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold evC
  rcases hc : σ c with _ | t
  · simp only
  · simp only [dite_eq_ite]

theorem yrec_succ (V P L : ℕ) (rb : ℕ → ℝ) (f s a f' : ℕ) :
    Yrec V P L rb f (s + 1) a f' = yBody V P L rb (Yrec V P L rb) f s a f' := by
  rw [Yrec.eq_2]
  unfold yBody
  congr 2

theorem upV_mono (V : ℕ) (W W' : ℕ → ℕ → ℝ) (h : ∀ a f, W a f ≤ W' a f) (a f : ℕ) :
    upV V W a f ≤ upV V W' a f := by
  unfold upV
  split_ifs
  · exact le_rfl
  · exact h _ _
  · exact add_le_add (h _ _) (h _ _)
  · exact le_rfl

theorem upV_nonneg (V : ℕ) (W : ℕ → ℕ → ℝ) (h : ∀ a f, 0 ≤ W a f) (a f : ℕ) : 0 ≤ upV V W a f := by
  unfold upV
  split_ifs
  · exact le_rfl
  · exact h _ _
  · exact add_nonneg (h _ _) (h _ _)
  · exact le_rfl

theorem lostS_nonneg (K : ℕ → ℕ → ℕ → ℝ) (hK : ∀ t a f, 0 ≤ K t a f) (σ : Fin 3 → CType) :
    0 ≤ lostS K σ := by
  unfold lostS
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun c _ => ?_)
  rcases σ c with _ | t
  · exact le_rfl
  · exact hK _ _ _

theorem evC_mono (V P : ℕ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (hρ : ∀ b f, 0 ≤ ρ b f)
    (hK : ∀ t a f, 0 ≤ K t a f) (T T' : (Fin 3 → CType) → ℕ → ℕ → ℕ → ℝ) (σ : Fin 3 → CType)
    (c : Fin 3) (p x g : ℕ)
    (h : ∀ (f' : Fin 4) q, (∀ t, σ c = some t → f' < t) →
      T (Function.update σ c (some f')) q x g ≤ T' (Function.update σ c (some f')) q x g) :
    evC V P ρ K T σ c p x g ≤ evC V P ρ K T' σ c p x g := by
  unfold evC
  rcases hc : σ c with _ | t
  · exact Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun f' _ =>
      mul_le_mul_of_nonneg_left (h f' _ (by simp [hc])) (hρ _ _)
  · refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun f' _ => ?_
    split_ifs with hf
    · exact mul_le_mul_of_nonneg_left (h f' _ (by simp [hc]; exact hf)) (hK _ _ _)
    · exact le_rfl

theorem evC_nonneg (V P : ℕ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (hρ : ∀ b f, 0 ≤ ρ b f)
    (hK : ∀ t a f, 0 ≤ K t a f) (T : (Fin 3 → CType) → ℕ → ℕ → ℕ → ℝ)
    (hT : ∀ σ q x g, 0 ≤ T σ q x g) (σ : Fin 3 → CType) (c : Fin 3) (p x g : ℕ) :
    0 ≤ evC V P ρ K T σ c p x g := by
  unfold evC
  rcases σ c with _ | t
  · exact Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun f' _ => mul_nonneg (hρ _ _) (hT _ _ _ _)
  · refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun f' _ => ?_
    split_ifs
    · exact mul_nonneg (hK _ _ _) (hT _ _ _ _)
    · exact le_rfl

theorem wBody_mono (V P : ℕ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (hρ : ∀ b f, 0 ≤ ρ b f)
    (hK : ∀ t a f, 0 ≤ K t a f) (σ : Fin 3 → CType) (hloop : loopS K σ < 1)
    (T T' : (Fin 3 → CType) → ℕ → ℕ → ℕ → ℝ) (p x g : ℕ)
    (h0 : ∀ x' g', T σ p x' g' ≤ T' σ p x' g')
    (h1 : ∀ (c : Fin 3) (f' : Fin 4) q, (∀ t, σ c = some t → f' < t) →
      T (Function.update σ c (some f')) q x g ≤ T' (Function.update σ c (some f')) q x g) :
    wBody V P ρ K T σ p x g ≤ wBody V P ρ K T' σ p x g := by
  unfold wBody
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact mul_le_mul_of_nonneg_left (upV_mono V _ _ h0 x g) (by norm_num)
  · exact mul_le_mul_of_nonneg_left (h0 x g) (lostS_nonneg K hK σ)
  · exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun c _ => evC_mono V P ρ K hρ hK T T' σ c p x g (h1 c)) (by norm_num)

theorem wBody_nonneg (V P : ℕ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (hρ : ∀ b f, 0 ≤ ρ b f)
    (hK : ∀ t a f, 0 ≤ K t a f) (σ : Fin 3 → CType) (hloop : loopS K σ < 1)
    (T : (Fin 3 → CType) → ℕ → ℕ → ℕ → ℝ) (hT : ∀ σ q x g, 0 ≤ T σ q x g) (p x g : ℕ) :
    0 ≤ wBody V P ρ K T σ p x g := by
  unfold wBody
  refine div_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) (by linarith)
  · exact mul_nonneg (by norm_num) (upV_nonneg V _ (fun _ _ => hT _ _ _ _) x g)
  · exact mul_nonneg (lostS_nonneg K hK σ) (hT _ _ _ _)
  · exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun c _ => evC_nonneg V P ρ K hρ hK T hT σ c p x g)

/-- **Sub-solutions of the R recursion.** -/
theorem wrec_lower (V P : ℕ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (hρ : ∀ b f, 0 ≤ ρ b f)
    (hK : ∀ t a f, 0 ≤ K t a f) (hloop : ∀ σ, loopS K σ < 1)
    (T : (Fin 3 → CType) → ℕ → ℕ → ℕ → ℝ)
    (h0 : ∀ σ x g, T σ 0 x g ≤ Wrec V P ρ K σ 0 x g)
    (hs : ∀ σ p x g, T σ (p + 1) x g ≤ wBody V P ρ K T σ p x g) :
    ∀ σ p x g, T σ p x g ≤ Wrec V P ρ K σ p x g := by
  have key : ∀ r (σ : Fin 3 → CType), rankS σ = r → ∀ p x g, T σ p x g ≤ Wrec V P ρ K σ p x g := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r IH =>
      intro σ hr p
      induction p with
      | zero => exact h0 σ
      | succ p IHp =>
        intro x g
        refine (hs σ p x g).trans ?_
        rw [wrec_succ]
        refine wBody_mono V P ρ K hρ hK σ (hloop σ) _ _ p x g IHp fun c f' q hf => ?_
        refine IH _ ?_ _ rfl q x g
        rw [← hr]
        exact rankS_update_lt σ c _ (by
          rcases hc : σ c with _ | t
          · simp only [tval]; omega
          · simp only [tval]; exact hf t hc)
  exact fun σ => key _ σ rfl

theorem pL_nonneg (L : ℕ) (hL : 1 ≤ L) : 0 ≤ pL L := by
  unfold pL
  have h1 : (1 : ℝ) ≤ 3 ^ (L - 1) := one_le_pow₀ (by norm_num)
  have h2 : (3 : ℝ) ≤ 3 ^ L := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hL
  exact div_nonneg (by linarith) (by linarith)

theorem pL_le_third (L : ℕ) (hL : 1 ≤ L) : pL L ≤ 1 / 3 := by
  unfold pL
  have h2 : (3 : ℝ) ≤ 3 ^ L := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hL
  have h3 : (3 : ℝ) ^ L = 3 * 3 ^ (L - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem yBody_mono (V P L : ℕ) (hL : 1 ≤ L) (rb : ℕ → ℝ) (hrb : ∀ b, 0 ≤ rb b)
    (T T' : ℕ → ℕ → ℕ → ℕ → ℝ) (f s a f' : ℕ) (hf : f ≤ 3)
    (h0 : ∀ a' f'', T f s a' f'' ≤ T' f s a' f'')
    (h1 : 1 ≤ f → ∀ q, T (f - 1) q a f' ≤ T' (f - 1) q a f') :
    yBody V P L rb T f s a f' ≤ yBody V P L rb T' f s a f' := by
  have hp0 := pL_nonneg L hL
  have hp1 := pL_le_third L hL
  have hf' : (f : ℝ) ≤ 3 := by exact_mod_cast hf
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  unfold yBody
  refine div_le_div_of_nonneg_right ?_ (by nlinarith)
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact mul_le_mul_of_nonneg_left (upV_mono V _ _ h0 a f') (by norm_num)
  · exact mul_le_mul_of_nonneg_left (h0 a f') (mul_nonneg (by linarith) (by linarith))
  · split_ifs with hz
    · exact le_rfl
    · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (by positivity)
      exact mul_le_mul_of_nonneg_left (h1 (by omega) _) (hrb b)

/-- **Sub-solutions of the H recursion** (counts `f ≤ 3`). -/
theorem yrec_lower (V P L : ℕ) (hL : 1 ≤ L) (rb : ℕ → ℝ) (hrb : ∀ b, 0 ≤ rb b)
    (T : ℕ → ℕ → ℕ → ℕ → ℝ)
    (h0 : ∀ f ≤ 3, ∀ a f', T f 0 a f' ≤ Yrec V P L rb f 0 a f')
    (hs : ∀ f ≤ 3, ∀ s a f', T f (s + 1) a f' ≤ yBody V P L rb T f s a f') :
    ∀ f ≤ 3, ∀ s a f', T f s a f' ≤ Yrec V P L rb f s a f' := by
  intro f
  induction f using Nat.strong_induction_on with
  | h f IH =>
    intro hf s
    induction s with
    | zero => exact h0 f hf
    | succ s IHs =>
      intro a f'
      refine (hs f hf s a f').trans ?_
      rw [yrec_succ]
      exact yBody_mono V P L hL rb hrb _ _ f s a f' hf IHs
        fun h1 q => IH (f - 1) (by omega) (by omega) q a f'

end FrogModel.D3.M1K
