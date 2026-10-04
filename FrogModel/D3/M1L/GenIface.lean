module

public import FrogModel.D3.M1L.GenMain
public import FrogModel.D3.Interfaces.Seed

@[expose] public section

/-!
# M1_L at every height: `Gen` against the recursions of the interface (Section 13 of the paper)

The recursions of the interface (FrogModel/D3/Interfaces/Seed.lean) follow the ups still to come
from a state, with the cap `V` absorbing (`upV`); `Gen` follows the ups so far (`upA`). A shift
(`Gen_shift`) moves the ups so far into the end value; then `Gen` with the end value the indicator
of an outcome is `Wrec` for an R closure (`Gen_Wrec`) and `Yrec` for an H closure, lumped by its
count of unmarked children (`Gen_Yrec`).
-/

open MeasureTheory ProbabilityTheory

namespace FrogModel.D3

theorem iface_pL (L : ℕ) : Iface.pL L = pL L := rfl

theorem iface_qL (L : ℕ) : Iface.qL L = qL L := rfl

/-- The indicator of an outcome `(x, g)`: `x` ups, `g` unmarked children. -/
noncomputable def ind (x g : ℕ) : Kid → ℕ → ℝ := fun k a => if a = x ∧ nN k = g then 1 else 0

theorem bodyG_a (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (X : Kid → ℕ → ℕ → ℝ) (k : Kid) (n a : ℕ) (c : Fin 3) :
    bodyG V P isR pL ρ K X k n a c = bodyG V P isR pL ρ K (fun k n _ => X k n a) k n 0 c := by
  unfold bodyG
  rfl

/-- **The shift**: the ups so far go into the end value. -/
theorem Gen_shift (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (add : Kid → ℝ) (hV : 1 ≤ V) (T : Kid → ℕ → ℝ) (k : Kid) (n a : ℕ) (ha : a ≤ V) :
    Gen V P isR pL ρ K add T k n a =
      Gen V P isR pL ρ K add (fun k' a' => T k' (min (a + a') V)) k n 0 := by
  induction h : rankK k using Nat.strong_induction_on generalizing k n a T with
  | h m IH =>
    induction n generalizing a T with
    | zero => simp only [Gen_zero, add_zero, min_eq_left ha]
    | succ n IHn =>
      rw [Gen_step _ _ _ _ _ _ _ _ k _ _ (Nat.succ_ne_zero n),
        Gen_step _ _ _ _ _ _ _ _ k _ _ (Nat.succ_ne_zero n), Nat.succ_sub_one]
      have hup : upA V 0 = 1 := by simp only [upA]; split_ifs <;> omega
      have hua : upA V a ≤ V := by unfold upA; split_ifs <;> omega
      rw [hup, IHn T (upA V a) hua, IHn _ 1 hV]
      have hT : (fun k' a' => T k' (min (upA V a + a') V)) =
          (fun k' a' => (fun k'' a'' => T k'' (min (a + a'') V)) k' (min (1 + a') V)) := by
        funext k' a'
        simp only [upA]
        split_ifs <;> congr 1 <;> omega
      rw [hT]
      congr 2
      refine Finset.sum_congr rfl fun c _ => ?_
      congr 1
      rw [bodyG_a _ _ _ _ _ _ (Gen V P isR pL ρ K add T) k (n + 1) a c]
      exact bodyG_congr _ _ _ _ _ _ _ _ _ _ _ _ (IHn T a ha)
        (fun k' hk' n' => IH _ (h ▸ hk') T k' n' a ha rfl)

/-- The up of the interface as a sum over the ups before it. -/
theorem upV_eq_sum (V : ℕ) (hV : 1 ≤ V) (W : ℕ → ℕ → ℝ) (x g : ℕ) (hx : x ≤ V) :
    Iface.upV V W x g = ∑ y ∈ Finset.range (V + 1), (if min (1 + y) V = x then W y g else 0) := by
  unfold Iface.upV
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · simp only [↓reduceIte]
    refine (Finset.sum_eq_zero fun y _ => ?_).symm
    rw [ite_eq_right (by omega)]
  · rw [ite_eq_right (by omega)]
    by_cases hxV : x < V
    · rw [ite_eq_left hxV, Finset.sum_eq_single (x - 1)]
      · rw [ite_eq_left (by omega)]
      · intro y _ hy
        rw [ite_eq_right (by omega)]
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    · have hxe : x = V := by omega
      subst hxe
      rw [ite_eq_right hxV, ite_eq_left rfl, Finset.sum_range_succ, Finset.sum_eq_single (x - 1)]
      · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      · intro y hy hy'
        rw [Finset.mem_range] at hy
        rw [ite_eq_right (by omega)]
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h

/-- The up step of an outcome indicator, as a sum of outcome indicators. -/
theorem Gen_up_ind (V P : ℕ) (isR : Bool) (pL : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (hV : 1 ≤ V) (x g : ℕ) (k : Kid) (n : ℕ) :
    Gen V P isR pL ρ K (fun _ => 0) (ind x g) k n (upA V 0) =
      ∑ y ∈ Finset.range (V + 1),
        (if min (1 + y) V = x then 1 else 0) * Gen V P isR pL ρ K (fun _ => 0) (ind y g) k n 0 := by
  have hup : upA V 0 = 1 := by simp only [upA]; split_ifs <;> omega
  rw [hup, Gen_shift V P isR pL ρ K _ hV _ k n 1 hV, ← Gen_sum0]
  refine Gen_congr _ _ _ _ _ _ _ _ _ (fun k' a' ha' => ?_) k n 0 (Nat.zero_le _)
  simp only [ind]
  rw [Finset.sum_eq_single a']
  · by_cases h1 : min (1 + a') V = x <;> by_cases h2 : nN k' = g <;> simp [h1, h2]
  · intro y _ hy
    simp [Ne.symm hy]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

end FrogModel.D3

namespace FrogModel.D3

/-- A sum over the three children, by their kind. -/
theorem sum_kid_ite (k : Kid) (A G : ℝ) :
    ∑ c, (if k c = none then A else G) = (nN k : ℝ) * A + (3 - (nN k : ℝ)) * G := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 3)))
    (fun c => k c = none)
  simp only [Finset.card_univ, Fintype.card_fin] at h3
  have h4 : ((Finset.univ.filter fun c => ¬k c = none).card : ℝ) = 3 - (nN k : ℝ) := by
    rw [eq_sub_iff_add_eq, ← Nat.cast_add, add_comm]
    unfold nN
    rw [h3]
    norm_num
  rw [h4]
  rfl

/-- **An H closure is `Yrec`**, lumped by its count of unmarked children. -/
theorem Gen_Yrec (V P L : ℕ) (hV : 1 ≤ V) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (g : ℕ) (k : Kid)
    (n x : ℕ) (hx : x ≤ V) :
    Gen V P false (pL L) ρ K (fun _ => 0) (ind x g) k n 0 =
      Iface.Yrec V P L (fun b => ∑ f ∈ Finset.range 4, ρ b f) (nN k) n x g := by
  induction h : nN k using Nat.strong_induction_on generalizing k n x with
  | h m IH =>
    induction n generalizing x with
    | zero =>
      rw [Gen_zero, Iface.Yrec]
      simp only [ind, h]
      by_cases h1 : x = 0 <;> by_cases h2 : m = g <;> simp [h1, h2, eq_comm]
      omega
    | succ n IHn =>
      rw [Gen_step _ _ _ _ _ _ _ _ k _ _ (Nat.succ_ne_zero n), Nat.succ_sub_one, Iface.Yrec, loopK_H,
        iface_pL, h]
      congr 1
      rw [Gen_up_ind V P false (pL L) ρ K hV x g k n, upV_eq_sum V hV _ x g hx]
      have hup : ∑ y ∈ Finset.range (V + 1), (if min (1 + y) V = x then (1 : ℝ) else 0) *
          Gen V P false (pL L) ρ K (fun _ => 0) (ind y g) k n 0 =
          ∑ y ∈ Finset.range (V + 1), (if min (1 + y) V = x then
            Iface.Yrec V P L (fun b => ∑ f ∈ Finset.range 4, ρ b f) m n y g else 0) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [IHn y (by simpa [Nat.lt_succ_iff] using hy)]
        split_ifs <;> simp
      rw [hup]
      have hbody : ∀ c, 1 / 4 * bodyG V P false (pL L) ρ K
          (Gen V P false (pL L) ρ K (fun _ => 0) (ind x g)) k (n + 1) 0 c =
          (if k c = none then 1 / 4 * ∑ b ∈ Finset.range (V + 1), (∑ f ∈ Finset.range 4, ρ b f) *
                Iface.Yrec V P L (fun b => ∑ f ∈ Finset.range 4, ρ b f) (m - 1) (min (n + b) P) x g
            else 1 / 4 * ((1 - pL L) *
                Iface.Yrec V P L (fun b => ∑ f ∈ Finset.range 4, ρ b f) m n x g)) := by
        intro c
        unfold bodyG
        cases hc : k c with
        | none =>
          simp only [Nat.add_sub_cancel, ↓reduceIte]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← Fin.sum_univ_eq_sum_range (fun f => ρ b f) 4, Finset.sum_mul]
          refine Finset.sum_congr rfl fun f _ => ?_
          have hu := nN_update_none k c f hc
          rw [IH _ (by omega) (Function.update k c (some f)) _ x hx rfl]
          congr 2
          omega
        | some t =>
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel, reduceCtorEq]
          rw [IHn x hx]
      rw [Finset.sum_congr rfl fun c _ => hbody c,
        sum_kid_ite k, h]
      by_cases hm : m = 0
      · subst hm
        simp only [Nat.cast_zero, zero_mul, ↓reduceDIte]
        ring
      · rw [dite_eq_right hm, Finset.mul_sum]
        simp only [Finset.mul_sum]
        ring_nf

end FrogModel.D3

namespace FrogModel.D3

/-- **An R closure is `Wrec`.** -/
theorem Gen_Wrec (V P : ℕ) (hV : 1 ≤ V) (pL' : ℝ) (ρ : ℕ → ℕ → ℝ) (K : ℕ → ℕ → ℕ → ℝ) (g : ℕ)
    (k : Kid) (n x : ℕ) (hx : x ≤ V) :
    Gen V P true pL' ρ K (fun _ => 0) (ind x g) k n 0 = Iface.Wrec V P ρ K k n x g := by
  induction h : rankK k using Nat.strong_induction_on generalizing k n x with
  | h m IH =>
    induction n generalizing x with
    | zero =>
      rw [Gen_zero, Iface.Wrec]
      simp only [ind, Iface.numN, nN]
      by_cases h1 : x = 0 <;> simp [h1, eq_comm]
    | succ n IHn =>
      have hloop : loopK true pL' K k = Iface.loopS K k := by
        unfold loopK Iface.loopS
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        cases k c <;> simp
      rw [Gen_step _ _ _ _ _ _ _ _ k _ _ (Nat.succ_ne_zero n), Nat.succ_sub_one, Iface.Wrec, hloop]
      congr 1
      rw [Gen_up_ind V P true pL' ρ K hV x g k n, upV_eq_sum V hV _ x g hx]
      have hup : ∑ y ∈ Finset.range (V + 1), (if min (1 + y) V = x then (1 : ℝ) else 0) *
          Gen V P true pL' ρ K (fun _ => 0) (ind y g) k n 0 =
          ∑ y ∈ Finset.range (V + 1), (if min (1 + y) V = x then Iface.Wrec V P ρ K k n y g else 0) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [IHn y (by simpa [Nat.lt_succ_iff] using hy)]
        split_ifs <;> simp
      rw [hup]
      have hlost : Iface.lostS K k * Iface.Wrec V P ρ K k n x g =
          ∑ c, 1 / 4 * (if k c = none then 0 else
            (match k c with | none => 0 | some t => K t 0 t)) * Iface.Wrec V P ρ K k n x g := by
        unfold Iface.lostS
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        cases k c <;> simp
      rw [hlost, Finset.mul_sum (Finset.univ : Finset (Fin 3)), zero_add, add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      unfold bodyG
      rcases hc : k c with _ | t
      · simp only [↓reduceIte, mul_zero, zero_mul, zero_add, Nat.succ_sub_one]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun f _ => ?_
        rw [IH _ (h ▸ rankK_update_none k c f hc) (Function.update k c (some f)) _ x hx rfl]
      · simp only [↓reduceIte, reduceCtorEq, Nat.succ_sub_one, IHn x hx]
        rw [mul_add]
        congr 1
        · ring
        · congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun f _ => ?_
          split_ifs with hf
          · refine Finset.sum_congr rfl fun a _ => ?_
            rw [IH _ (h ▸ rankK_update_some k c t f hc hf) (Function.update k c (some f)) _ x hx rfl]
          · simp

end FrogModel.D3
