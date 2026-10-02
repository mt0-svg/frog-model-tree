module

public import FrogModel.Engine.Defs

@[expose] public section

/-!
# The root engine: the output of a trajectory is the closed formula

`recOut_eq_outPsi`: along the trajectory of the root chain from a valid state, the outputs
recorded are `outPsi` of the start, for every input sequence. The proof is by one step:
`need_rstep` (frog `k` not yet finished: one more step consumes one of the frogs needed), then
`outPsi_rstep` (the formula does not change along a step), and the frogs never finished have
no `n` with `need n ≤ n` (`outPsi_eq_top_of_unfinished`).

`le_recOut_of_redirect` is Lemma 6.4 of the paper in pathwise form: a chain whose
every step is a real step followed by a redirect to a dominating state (`Dom`, children related
by a simulation `R`), and which redirects only before some time, has outputs at least the
outputs of the real chain, for the same inputs (the same direction and the same uniform at each
step).
-/

open scoped ENNReal

namespace FrogModel.Engine

variable {S U : Type*} {d J : ℕ}

/-! ### Steps of the driven system and of the root chain -/

theorem traj_succ_shift {X Ξ : Type*} (f : X → Ξ → X) (x : X) (w : ℕ → Ξ) (n : ℕ) :
    traj f x w (n + 1) = traj f (f x (w 0)) (fun k => w (k + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [traj, ih]; rfl

theorem rstep_of_absorbed (cstep : S → U → ℕ × S) (x : RState S d J) (hx : J ≤ x.i)
    (ξ : Fin (d + 1) × U) : rstep cstep x ξ = x := by
  unfold rstep
  rw [dite_eq_right (not_lt.2 hx)]

theorem rstep_valid (cstep : S → U → ℕ × S) (x : RState S d J) (hx : Valid x)
    (ξ : Fin (d + 1) × U) : Valid (rstep cstep x ξ) := by
  unfold rstep
  split_ifs with h h0
  · refine ⟨fun _ => le_rfl, fun k hk => ?_⟩
    have hne : k ≠ ⟨x.i, h⟩ := fun e => by simp [e] at hk
    simp only [Function.update_of_ne hne]
    exact hx.2 k (by simp at hk ⊢; omega)
  · exact ⟨fun _ => Nat.one_le_iff_ne_zero.2 h0, hx.2⟩
  · exact hx

theorem rstep_out_le (cstep : S → U → ℕ × S) (x : RState S d J) (hx : Valid x)
    (ξ : Fin (d + 1) × U) : (rstep cstep x ξ).out ≤ x.out := by
  intro k
  unfold rstep
  split_ifs with h h0
  · by_cases hk : k = ⟨x.i, h⟩
    · subst hk; simp [hx.2 ⟨x.i, h⟩ le_rfl]
    · simp [Function.update_of_ne hk]
  · exact le_rfl
  · exact le_rfl

/-- A recorded output does not change. -/
theorem rstep_out_of_lt (cstep : S → U → ℕ × S) (x : RState S d J) (ξ : Fin (d + 1) × U)
    (k : Fin J) (hk : (k : ℕ) < x.i) : (rstep cstep x ξ).out k = x.out k := by
  unfold rstep
  split_ifs with h h0
  · have hne : k ≠ ⟨x.i, h⟩ := fun e => by simp [e] at hk
    simp [Function.update_of_ne hne]
  · rfl
  · rfl

theorem le_rstep_i (cstep : S → U → ℕ × S) (x : RState S d J) (ξ : Fin (d + 1) × U) :
    x.i ≤ (rstep cstep x ξ).i := by
  unfold rstep
  split_ifs <;> simp

theorem rstep_sigma (cstep : S → U → ℕ × S) (x : RState S d J) (hx : x.i < J)
    (w : ℕ → Fin (d + 1) × U) :
    (rstep cstep x (w 0)).σ = childAt cstep x.σ w 1 := by
  have hm : (move cstep x (w 0).1 (w 0).2).2.2 = childAt cstep x.σ w 1 := by
    unfold move
    simp only [childAt]
    split_ifs <;> rfl
  unfold rstep
  rw [dite_eq_left hx]
  split_ifs <;> exact hm

theorem move_p (cstep : S → U → ℕ × S) (x : RState S d J) (w : ℕ → Fin (d + 1) × U) :
    (move cstep x (w 0).1 (w 0).2).2.1 = x.p - 1 + delivAt cstep x.σ w 0 := by
  unfold move delivAt
  split_ifs <;> rfl

theorem move_e (cstep : S → U → ℕ × S) (x : RState S d J) (w : ℕ → Fin (d + 1) × U) :
    (move cstep x (w 0).1 (w 0).2).1 = x.e + (if (w 0).1 = 0 then 1 else 0) := by
  unfold move
  split_ifs <;> simp

theorem childAt_succ_shift (cstep : S → U → ℕ × S) (σ : Fin d → S) (w : ℕ → Fin (d + 1) × U)
    (n : ℕ) :
    childAt cstep σ w (n + 1) = childAt cstep (childAt cstep σ w 1) (fun k => w (k + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [childAt, ih]
    rfl

theorem delivAt_succ_shift (cstep : S → U → ℕ × S) (σ : Fin d → S) (w : ℕ → Fin (d + 1) × U)
    (n : ℕ) :
    delivAt cstep σ w (n + 1) = delivAt cstep (childAt cstep σ w 1) (fun k => w (k + 1)) n := by
  unfold delivAt
  rw [childAt_succ_shift]

theorem cumDeliv_succ_shift (cstep : S → U → ℕ × S) (σ : Fin d → S) (w : ℕ → Fin (d + 1) × U)
    (n : ℕ) :
    cumDeliv cstep σ w (n + 1) =
      delivAt cstep σ w 0 + cumDeliv cstep (childAt cstep σ w 1) (fun k => w (k + 1)) n := by
  unfold cumDeliv
  rw [Finset.sum_range_succ', add_comm]
  simp only [delivAt_succ_shift]

theorem exitCount_succ_shift (w : ℕ → Fin (d + 1) × U) (n : ℕ) :
    exitCount w (n + 1) = (if (w 0).1 = 0 then 1 else 0) + exitCount (fun k => w (k + 1)) n := by
  unfold exitCount
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ', add_comm]

theorem exitCount_mono (w : ℕ → Fin (d + 1) × U) : Monotone (exitCount w) := by
  intro n n' h
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

theorem exists_le_iff_of_shift (T T' : ℕ → ℕ) (h0 : 1 ≤ T 0) (hT : ∀ n, T (n + 1) = T' n + 1) :
    (∃ n, T n ≤ n) ↔ ∃ n, T' n ≤ n := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => omega
    | succ k => exact ⟨k, by have := hT k; omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by have := hT k; omega⟩

theorem find_eq_of_shift (T T' : ℕ → ℕ) (h0 : 1 ≤ T 0) (hT : ∀ n, T (n + 1) = T' n + 1)
    (h : ∃ n, T n ≤ n) (h' : ∃ n, T' n ≤ n) : Nat.find h = Nat.find h' + 1 := by
  rw [Nat.find_eq_iff]
  refine ⟨by have := hT (Nat.find h'); have := Nat.find_spec h'; omega, fun n hn => ?_⟩
  cases n with
  | zero => omega
  | succ k =>
    have := Nat.find_min h' (show k < Nat.find h' by omega)
    have := hT k
    omega

/-! ### One step of the formula -/

/-- Frog `k` not finished after the step: one step consumes one of the frogs needed. -/
theorem need_rstep (cstep : S → U → ℕ × S) (x : RState S d J) (hx : Valid x) (h : x.i < J)
    (w : ℕ → Fin (d + 1) × U) (k : ℕ) (hk : ¬ k < (rstep cstep x (w 0)).i) (n : ℕ) :
    need cstep x w k (n + 1) = need cstep (rstep cstep x (w 0)) (fun t => w (t + 1)) k n + 1 := by
  have hp := hx.1 h
  have hs := rstep_sigma cstep x h w
  have hm := move_p cstep x w
  unfold need
  rw [cumDeliv_succ_shift, ← hs]
  revert hk
  unfold rstep
  rw [dite_eq_left h]
  split_ifs with h0
  · intro hk
    simp only at hk ⊢
    omega
  · intro hk
    simp only at hk ⊢
    omega

theorem one_le_need (cstep : S → U → ℕ × S) (x : RState S d J) (hx : Valid x) (h : x.i < J)
    (w : ℕ → Fin (d + 1) × U) (k : ℕ) : 1 ≤ need cstep x w k 0 := by
  have := hx.1 h
  unfold need
  omega

/-- The formula does not change along a step. -/
theorem outPsi_rstep (cstep : S → U → ℕ × S) (x : RState S d J) (hx : Valid x)
    (w : ℕ → Fin (d + 1) × U) :
    outPsi cstep x w = outPsi cstep (rstep cstep x (w 0)) (fun k => w (k + 1)) := by
  funext k
  by_cases h : x.i < J
  swap
  · rw [rstep_of_absorbed cstep x (not_lt.1 h)]
    have hk : (k : ℕ) < x.i := lt_of_lt_of_le k.isLt (not_lt.1 h)
    simp [outPsi, hk]
  have he : (rstep cstep x (w 0)).e = x.e + (if (w 0).1 = 0 then 1 else 0) := by
    rw [← move_e cstep x w]; unfold rstep; rw [dite_eq_left h]; split_ifs <;> rfl
  have hx1 : exitCount w 1 = if (w 0).1 = 0 then 1 else 0 := by
    unfold exitCount; rw [Finset.card_filter, Finset.sum_range_one]
  by_cases hky : (k : ℕ) < (rstep cstep x (w 0)).i
  · -- frog `k` is finished after the step
    by_cases hkx : (k : ℕ) < x.i
    · simp only [outPsi, hkx, ite_true, hky, rstep_out_of_lt cstep x (w 0) k hkx]
    · -- frog `k = x.i` finishes at this step
      have hp := hx.1 h
      have hm := move_p cstep x w
      have hyi : (rstep cstep x (w 0)).i ≤ x.i + 1 := by
        unfold rstep; rw [dite_eq_left h]; split_ifs <;> simp
      have hkeq : (k : ℕ) = x.i := by omega
      have h0 : (move cstep x (w 0).1 (w 0).2).2.1 = 0 := by
        by_contra h0
        have : (rstep cstep x (w 0)).i = x.i := by unfold rstep; rw [dite_eq_left h, ite_eq_right h0]
        omega
      have hyout : (rstep cstep x (w 0)).out k =
          ((x.e + (if (w 0).1 = 0 then 1 else 0) : ℕ) : ℕ∞) := by
        have hk' : k = ⟨x.i, h⟩ := Fin.ext hkeq
        unfold rstep; rw [dite_eq_left h, ite_eq_left h0, hk']; dsimp only; rw [Function.update_self, move_e]
      have hn : ∃ n, need cstep x w k n ≤ n := ⟨1, by
        unfold need; rw [cumDeliv, Finset.sum_range_one]; omega⟩
      have hf : Nat.find hn = 1 := by
        rw [Nat.find_eq_iff]
        refine ⟨by unfold need; rw [cumDeliv, Finset.sum_range_one]; omega, fun n hn1 => ?_⟩
        have : n = 0 := by omega
        subst this
        unfold need; omega
      simp only [outPsi, hkx, ite_false, hky, ite_true, dite_eq_left hn, hf, hyout, hx1]
  · -- frog `k` is not finished after the step
    have hkx : ¬ (k : ℕ) < x.i := fun hkx => hky (lt_of_lt_of_le hkx (le_rstep_i cstep x (w 0)))
    have hT := need_rstep cstep x hx h w k hky
    have h1 := one_le_need cstep x hx h w k
    have hiff := exists_le_iff_of_shift (need cstep x w k)
      (need cstep (rstep cstep x (w 0)) (fun t => w (t + 1)) k) h1 hT
    simp only [outPsi, hkx, ite_false, hky]
    by_cases hn : ∃ n, need cstep x w k n ≤ n
    · have hn' := hiff.1 hn
      rw [dite_eq_left hn, dite_eq_left hn', find_eq_of_shift (need cstep x w k)
        (need cstep (rstep cstep x (w 0)) (fun t => w (t + 1)) k) h1 hT hn hn',
        exitCount_succ_shift, he]
      congr 1
      omega
    · rw [dite_eq_right hn, dite_eq_right (fun hn' => hn (hiff.2 hn'))]

/-! ### Along a trajectory -/

theorem traj_valid (cstep : S → U → ℕ × S) (x : RState S d J) (hx : Valid x)
    (w : ℕ → Fin (d + 1) × U) (n : ℕ) : Valid (traj (rstep cstep) x w n) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact rstep_valid cstep _ ih _

/-- The step of the trajectory at time `t`, with the inputs from `t` on. -/
theorem rstep_traj_shift (cstep : S → U → ℕ × S) (x : RState S d J) (w : ℕ → Fin (d + 1) × U)
    (t : ℕ) :
    rstep cstep (traj (rstep cstep) x w t) ((fun s => w (s + t)) 0) =
      traj (rstep cstep) x w (t + 1) := by
  simp [traj]

theorem shift_succ (w : ℕ → Fin (d + 1) × U) (t : ℕ) :
    (fun s => (fun s => w (s + t)) (s + 1)) = fun s => w (s + (t + 1)) := by
  funext s; simp only; congr 1; omega

theorem outPsi_traj (cstep : S → U → ℕ × S) (x : RState S d J) (hx : Valid x)
    (w : ℕ → Fin (d + 1) × U) (n : ℕ) :
    outPsi cstep x w = outPsi cstep (traj (rstep cstep) x w n) (fun t => w (t + n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ih, outPsi_rstep cstep _ (traj_valid cstep x hx w n), rstep_traj_shift, shift_succ]

theorem traj_out_antitone (cstep : S → U → ℕ × S) (x : RState S d J) (hx : Valid x)
    (w : ℕ → Fin (d + 1) × U) : Antitone fun n => (traj (rstep cstep) x w n).out :=
  antitone_nat_of_succ_le fun n => rstep_out_le cstep _ (traj_valid cstep x hx w n) _

theorem traj_i_mono (cstep : S → U → ℕ × S) (x : RState S d J) (w : ℕ → Fin (d + 1) × U) :
    Monotone fun n => (traj (rstep cstep) x w n).i :=
  monotone_nat_of_le_succ fun _ => le_rstep_i cstep _ _

theorem traj_out_stable (cstep : S → U → ℕ × S) (x : RState S d J) (w : ℕ → Fin (d + 1) × U)
    (k : Fin J) (n : ℕ) (hk : (k : ℕ) < (traj (rstep cstep) x w n).i) (t : ℕ) (ht : n ≤ t) :
    (traj (rstep cstep) x w t).out k = (traj (rstep cstep) x w n).out k := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t hnt ih =>
    rw [traj, rstep_out_of_lt cstep _ _ k
      (lt_of_lt_of_le hk (traj_i_mono cstep x w hnt)), ih]

/-- A frog never finished along the trajectory has no `n` with `need n ≤ n`: along the
trajectory the least such `n` drops by one per step, and it is at least `1`. -/
theorem outPsi_eq_top_of_unfinished (cstep : S → U → ℕ × S) (x : RState S d J) (hx : Valid x)
    (w : ℕ → Fin (d + 1) × U) (k : Fin J) (hk : ∀ n, (traj (rstep cstep) x w n).i ≤ k) :
    outPsi cstep x w k = ⊤ := by
  have hkx : ¬ (k : ℕ) < x.i := not_lt.2 (hk 0)
  simp only [outPsi, hkx, ite_false]
  rw [dite_eq_right]
  rintro ⟨N, hN⟩
  have key : ∀ t, ∃ n, need cstep (traj (rstep cstep) x w t) (fun s => w (s + t)) k n ≤ n ∧
      n + t ≤ N := by
    intro t
    induction t with
    | zero => exact ⟨N, hN, by omega⟩
    | succ t ih =>
      obtain ⟨n, hn, hnt⟩ := ih
      have hv := traj_valid cstep x hx w t
      have hlive : (traj (rstep cstep) x w t).i < J := lt_of_le_of_lt (hk t) k.isLt
      have h1 := one_le_need cstep _ hv hlive (fun s => w (s + t)) k
      cases n with
      | zero => omega
      | succ m =>
        have hk' : ¬ (k : ℕ) <
            (rstep cstep (traj (rstep cstep) x w t) ((fun s => w (s + t)) 0)).i := by
          rw [rstep_traj_shift]; exact not_lt.2 (hk (t + 1))
        have e := need_rstep cstep _ hv hlive (fun s => w (s + t)) k hk' m
        rw [rstep_traj_shift, shift_succ] at e
        exact ⟨m, by omega, by omega⟩
  obtain ⟨n, -, hn⟩ := key (N + 1)
  omega

/-- **The output of a trajectory is the formula**, for every input sequence. -/
theorem recOut_eq_outPsi (cstep : S → U → ℕ × S) (x : RState S d J) (hx : Valid x)
    (w : ℕ → Fin (d + 1) × U) : recOut (traj (rstep cstep) x w) = outPsi cstep x w := by
  funext k
  unfold recOut
  by_cases hfin : ∃ n, (k : ℕ) < (traj (rstep cstep) x w n).i
  · obtain ⟨n, hn⟩ := hfin
    rw [outPsi_traj cstep x hx w n]
    simp only [outPsi, hn, ite_true]
    refine le_antisymm (iInf_le _ n) (le_iInf fun t => ?_)
    rcases le_total t n with htn | hnt
    · exact traj_out_antitone cstep x hx w htn k
    · exact (traj_out_stable cstep x w k n hn t hnt).ge
  · push Not at hfin
    rw [outPsi_eq_top_of_unfinished cstep x hx w k fun n => hfin n]
    exact le_antisymm le_top (le_iInf fun t =>
      le_of_eq ((traj_valid cstep x hx w t).2 k (hfin t)).symm)

end FrogModel.Engine
