module

public import FrogModel.D3.M1L.GenAux
public import FrogModel.D3.M1L.Height0

@[expose] public section

/-!
# M1_L at every height: the laws by height are laws, the costs are nonnegative

`InpOK V q`: `q = (ρ, K)` are laws of the kind the run produces (`K(t → (a, f))` vanishes for
`f > t`, as in the recursion of Section 13 of the paper, and for `f = t`, `a ≥ 2`). By induction
on the height, `inp p h` satisfies it for every `h` (`inp_ok`), and the costs are nonnegative
(`costs_nonneg`).
-/

open MeasureTheory ProbabilityTheory

namespace FrogModel.D3

/-- Inputs that are laws of the kind the run produces. -/
def InpOK (V : ℕ) (q : LawIn) : Prop :=
  (∀ b f, 0 ≤ q.1 b f) ∧ (∑ f : Fin 4, ∑ b ∈ Finset.range (V + 1), q.1 b f = 1) ∧
    (∀ t a f, 0 ≤ q.2 t a f) ∧ (∀ t : ℕ, q.2 t 1 t ≤ 1) ∧
    (∀ t : Fin 4, q.2 t 0 t + q.2 t 1 t +
      ∑ f : Fin 4, (if f < t then ∑ a' ∈ Finset.range (V + 1), q.2 t a' f else 0) = 1) ∧
    (∀ t a f : ℕ, t < f → q.2 t a f = 0) ∧ (∀ t a : ℕ, 2 ≤ a → q.2 t a t = 0)

theorem laws_eq (p : Params) (h : ℕ) : laws p h = lawsAt p h (inp p h) := by
  cases h <;> rfl

theorem costs_eq (p : Params) (c : ℝ) (h : ℕ) : costs p c h = costsAt p c h (cinp p c h) := by
  cases h <;> rfl

theorem κm_mem (p : Params) (r : Bool) (h f0 a g : ℕ) : 0 ≤ κm p r h f0 a g ∧ κm p r h f0 a g ≤ 1 := by
  unfold κm
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have : coinLaw {j | p.keep r h f0 a g j = true} ≤ 1 := prob_le_one
  have h1 : (coinLaw {j | p.keep r h f0 a g j = true}).toReal ≤ (1 : ENNReal).toReal :=
    ENNReal.toReal_mono ENNReal.one_ne_top this
  simpa using h1

/-- `Gen` with additive term `0` and an end value that is a finite combination. -/
theorem Gen_sum0 (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (Y : ι → ℝ) (T : ι → Kid → ℕ → ℝ) (k : Kid)
    (n a : ℕ) :
    Gen V P isR pL ρ K (fun _ => 0) (fun k a => ∑ i ∈ s, Y i * T i k a) k n a =
      ∑ i ∈ s, Y i * Gen V P isR pL ρ K (fun _ => 0) (T i) k n a := by
  have h := Gen_sum V P isR pL ρ K s (fun i k => Y i * 0) (fun i k a => Y i * T i k a) k n a
  simp only [mul_zero, Finset.sum_const_zero] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 := Gen_smul V P isR pL ρ K (fun _ => 0) (T i) (Y i) k n a
  simp only [mul_zero] at h2
  exact h2

/-- The linear decomposition of a closure value: its cost, plus the mean of a function of its
outcome after the kill. -/
theorem Gen_lin (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (A : Kid → ℝ) (c : ℝ) (Y : ℕ → Fin 4 → ℝ) (κ : ℕ → ℕ → ℝ) (k : Kid) (n a : ℕ) :
    Gen V P isR pL ρ K A (fun k a => c + ∑ b ∈ Finset.range (V + 1), ∑ f : Fin 4,
        killP (κ a (nN k)) a (nN k) b f * Y b f) k n a =
      Gen V P isR pL ρ K A (fun _ _ => c) k n a +
        ∑ b ∈ Finset.range (V + 1), ∑ f : Fin 4, Y b f *
          Gen V P isR pL ρ K (fun _ => 0) (fun k a => killP (κ a (nN k)) a (nN k) b f) k n a := by
  have h1 := Gen_add V P isR pL ρ K A (fun _ => 0) (fun _ _ => c)
    (fun k a => ∑ b ∈ Finset.range (V + 1), ∑ f : Fin 4, killP (κ a (nN k)) a (nN k) b f * Y b f)
    k n a
  simp only [add_zero] at h1
  rw [h1]
  congr 1
  have h2 := Gen_sum0 V P isR pL ρ K (Finset.range (V + 1) ×ˢ (Finset.univ : Finset (Fin 4)))
    (fun i => Y i.1 i.2) (fun i k a => killP (κ a (nN k)) a (nN k) i.1 i.2) k n a
  rw [Finset.sum_product] at h2
  have h3 : (fun k a => ∑ b ∈ Finset.range (V + 1), ∑ f : Fin 4,
      killP (κ a (nN k)) a (nN k) b f * Y b f) =
      (fun k a => ∑ x ∈ Finset.range (V + 1) ×ˢ (Finset.univ : Finset (Fin 4)),
        Y x.1 x.2 * killP (κ a (nN k)) a (nN k) x.1 x.2) := by
    funext k a
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun f _ => mul_comm _ _
  rw [h3, h2]

theorem dummy_ok (V : ℕ) : InpOK V dummyIn := by
  unfold InpOK dummyIn
  refine ⟨fun b f => by positivity, ?_, fun t a f => by positivity, fun t => by simp, ?_,
    fun t a f h => by simp; omega, fun t a h => by simp; omega⟩
  · rw [Fin.sum_univ_four]
    simp [Finset.sum_ite_eq', Finset.mem_range]
  · intro t
    fin_cases t <;> simp [Fin.sum_univ_four, Finset.sum_ite_eq']

/-- The end value of `K_h(t → (b, f))` vanishes off its support. -/
theorem killP_supp (κ : ℝ) (a g b f : ℕ) (h : g < f ∨ (g = f ∧ a < b)) : killP κ a g b f = 0 := by
  unfold killP
  rcases h with h | ⟨h1, h2⟩ <;> (rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp)

/-- The laws at height `h` from inputs that are laws are laws. -/
theorem lawsAt_ok (p : Params) (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (h : ℕ) (q : LawIn)
    (hq : InpOK p.V q) : InpOK p.V (lawsAt p h q) := by
  obtain ⟨hρ0, hρ1, hK0, hK1, hKs, hKf, hKa⟩ := hq
  have hp := pL_mem p.L hL
  have hK0' : ∀ t : ℕ, 0 ≤ q.2 t 1 t := fun t => hK0 t 1 t
  have hkill : ∀ (r : Bool) (f0 : ℕ) (b f : ℕ) (k : Kid) (a : ℕ),
      0 ≤ killP (κm p r h f0 a (nN k)) a (nN k) b f := fun r f0 b f k a =>
    killP_nonneg _ (κm_mem p r h f0 a (nN k)).1 (κm_mem p r h f0 a (nN k)).2 _ _ _ _
  -- the total mass of a closure from any start, after the kill
  have htot : ∀ (r : Bool) (f0 : ℕ) (k : Kid) (n : ℕ),
      ∑ f : Fin 4, ∑ b ∈ Finset.range (p.V + 1),
        GenH p h r q (fun _ => 0) (fun k a => killP (κm p r h f0 a (nN k)) a (nN k) b f) k n 0 = 1 := by
    intro r f0 k n
    unfold GenH
    have h1 := Gen_sum0 p.V p.P (isRe h r) (pL p.L) q.1 q.2
      ((Finset.univ : Finset (Fin 4)) ×ˢ Finset.range (p.V + 1)) (fun _ => 1)
      (fun i k a => killP (κm p r h f0 a (nN k)) a (nN k) i.2 i.1) k n 0
    simp only [one_mul] at h1
    rw [Finset.sum_product] at h1
    rw [← h1]
    rw [Gen_congr p.V p.P (isRe h r) (pL p.L) q.1 q.2 (fun _ => 0) _ (fun _ _ => 1) ?_ k n 0
      (Nat.zero_le _)]
    · exact Gen_one p.V p.P (isRe h r) (pL p.L) q.1 q.2 hρ1 hKs hK0' hK1 hp.1 hp.2 k n 0
    · intro k a ha
      rw [Finset.sum_product, Finset.sum_comm]
      exact killP_sum p.V _ a (nN k) ha (nN_lt k)
  -- the support of an H closure from the representative child types
  have hsupp : ∀ t a f : ℕ, (nN (kidOf h t) < f ∨ (nN (kidOf h t) = f ∧ 1 < a)) →
      (lawsAt p h q).2 t a f = 0 := by
    intro t a f hh
    unfold lawsAt GenH
    have hR : isRe h false = false := by simp [isRe]
    simp only [hR]
    refine Gen_supp p.V p.P (pL p.L) q.1 q.2 _ f a ?_ (kidOf h t) 1 0 (by omega)
    intro k a' ha'
    exact killP_supp _ a' (nN k) a f ha'
  have hsf : ∀ t a f : ℕ, t < f → (lawsAt p h q).2 t a f = 0 := fun t a f htf =>
    hsupp t a f (Or.inl (lt_of_le_of_lt (nN_kidOf_le h t) htf))
  have hsa : ∀ t a : ℕ, 2 ≤ a → (lawsAt p h q).2 t a t = 0 := by
    intro t a ha
    rcases lt_or_eq_of_le (nN_kidOf_le h t) with h1 | h1
    · exact hsupp t a t (Or.inl h1)
    · exact hsupp t a t (Or.inr ⟨h1, by omega⟩)
  have hKsum : ∀ t : Fin 4, (lawsAt p h q).2 t 0 t + (lawsAt p h q).2 t 1 t +
      ∑ f : Fin 4, (if f < t then ∑ a' ∈ Finset.range (p.V + 1), (lawsAt p h q).2 t a' f else 0)
        = 1 := by
    intro t
    have hs := K_split p.V hV (lawsAt p h q).2 t (fun a f htf => hsf t a f htf)
      (fun a ha => hsa t a ha) (fun _ _ => 1)
    simp only [mul_one] at hs
    rw [← hs, Finset.sum_comm]
    exact htot false t (kidOf h t) 1
  have hKnn : ∀ t a f, 0 ≤ (lawsAt p h q).2 t a f := by
    intro t a f
    unfold lawsAt GenH
    dsimp only
    exact Gen_nonneg _ _ _ _ _ _ _ _ hρ0 hK0 hK1 hp.1 hp.2 (fun _ => le_refl 0)
      (fun k a' => hkill false t a f k a') _ _ _
  refine ⟨?_, ?_, hKnn, ?_, hKsum, hsf, hsa⟩
  · intro b f
    unfold lawsAt GenH
    dsimp only
    exact Gen_nonneg _ _ _ _ _ _ _ _ hρ0 hK0 hK1 hp.1 hp.2 (fun _ => le_refl 0)
      (fun k a => hkill true 3 b f k a) _ _ _
  · exact htot true 3 (initK h) 2
  · intro t
    rcases Nat.lt_or_ge t 4 with ht | ht
    · have hs := hKsum ⟨t, ht⟩
      have h0 := hKnn t 0 t
      have hr : 0 ≤ ∑ f : Fin 4, (if f < (⟨t, ht⟩ : Fin 4) then
          ∑ a' ∈ Finset.range (p.V + 1), (lawsAt p h q).2 t a' f else 0) := by
        refine Finset.sum_nonneg fun f _ => ?_
        split_ifs
        · exact Finset.sum_nonneg fun a' _ => hKnn t a' f
        · exact le_refl 0
      simp only at hs
      linarith
    · rw [hsupp t 1 t (Or.inl (lt_of_lt_of_le (nN_lt _) ht))]
      norm_num

/-- `ρ_h` and `K_h` are laws of the kind the run produces, at every height. -/
theorem inp_ok (p : Params) (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (h : ℕ) : InpOK p.V (inp p h) := by
  induction h with
  | zero => exact dummy_ok p.V
  | succ h ih =>
    show InpOK p.V (laws p h)
    rw [laws_eq]
    exact lawsAt_ok p hL hV h _ ih

/-- The costs are nonnegative for a nonnegative cost per read. -/
theorem costs_nonneg (p : Params) (hL : 1 ≤ p.L) (hV : 1 ≤ p.V) (c : ℝ) (hc : 0 ≤ c) (h : ℕ) :
    0 ≤ (cinp p c h).1 ∧ ∀ t, 0 ≤ (cinp p c h).2 t := by
  have hp := pL_mem p.L hL
  have hg : 0 ≤ gcost p.L 1 := by
    unfold gcost
    positivity
  induction h with
  | zero => exact ⟨le_refl 0, fun _ => le_refl 0⟩
  | succ h ih =>
    obtain ⟨hρ0, -, hK0, hK1, -⟩ := inp_ok p hL hV h
    have hadd : ∀ r k, 0 ≤ addC p c h r (cinp p c h) k := by
      intro r k
      unfold addC
      refine add_nonneg hc (Finset.sum_nonneg fun c' _ => mul_nonneg (by norm_num) ?_)
      rcases k c' with _ | t
      · exact ih.1
      · simp only
        split_ifs
        · exact ih.2 t
        · exact mul_nonneg hc hg
    show 0 ≤ (costs p c h).1 ∧ ∀ t, 0 ≤ (costs p c h).2 t
    rw [costs_eq]
    exact ⟨Gen_nonneg _ _ _ _ _ _ _ _ hρ0 hK0 hK1 hp.1 hp.2 (hadd true) (fun _ _ => hc) _ _ _,
      fun t => Gen_nonneg _ _ _ _ _ _ _ _ hρ0 hK0 hK1 hp.1 hp.2 (hadd false) (fun _ _ => hc) _ _ _⟩

end FrogModel.D3
