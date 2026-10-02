module

public import FrogModel.Engine.Redirect
public import FrogModel.Engine.Absorb
public import FrogModel.Engine.Law
public import FrogModel.LemmaX.Coupling

@[expose] public section

/-!
# The root engine: the redirected chain dominates (Lemma 6.4 of the paper)

A chain `g` on states with a memory `Z` that moves, at every step, to a state dominating the step
of the root chain (`Dom R`, `R` a simulation of the child chain), and that follows the root chain
from the first state with more than `T` exits or absorbed on (`free`), has outputs at least those
of the root chain, almost surely under i.i.d. inputs whose directions exit with positive
probability (`ae_le_recOut_redirect`); hence its output law dominates the output law of the root
chain in the coupling order (`couplingLE_redirect`).

The exits are unbounded almost surely (`ae_exitCount_unbounded`), and a chain whose counts move as
in the root chain makes more than `T` exits or is absorbed once there are enough exits
(`exists_stop_of_exits`); from there on it follows the root chain, and `le_recOut_of_redirect`
applies.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Engine

variable {S U Z : Type*} {d J : ℕ}

/-! ### Measurability and exits -/

theorem rstep_e (cstep : S → U → ℕ × S) (x : RState S d J) (ξ : Fin (d + 1) × U) :
    (rstep cstep x ξ).e = if x.i < J ∧ ξ.1 = 0 then x.e + 1 else x.e := by
  simp only [FrogModel.Engine.rstep]
  by_cases hJ : x.i < J
  · simp [hJ]
    by_cases hξ : ξ.1 = 0
    · rw [hξ]
      unfold FrogModel.Engine.move
      simp
      split_ifs <;> rfl
    · unfold FrogModel.Engine.move
      simp [hξ]
      split_ifs <;> rfl
  · simp [hJ]

theorem measurableSet_traj_eq {X Ξ : Type*} [MeasurableSpace Ξ] [Countable X]
    (f : X → Ξ → X) (hf : ∀ x y, MeasurableSet {ξ | f x ξ = y}) (x : X) (n : ℕ) (y : X) :
    MeasurableSet {w : ℕ → Ξ | traj f x w n = y} := by
  induction n generalizing y with
  | zero =>
    dsimp [traj]
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy]
  | succ n ih =>
    dsimp [traj]
    have h_eq : {w : ℕ → Ξ | f (traj f x w n) (w n) = y} =
        ⋃ z : X, {w : ℕ → Ξ | traj f x w n = z} ∩ (fun (w : ℕ → Ξ) => w n) ⁻¹' {ξ : Ξ | f z ξ = y} := by
      ext w
      simp
    rw [h_eq]
    refine MeasurableSet.iUnion fun z => ?_
    refine ((ih z).inter ?_)
    have hmeas : Measurable fun (w : ℕ → Ξ) => w n := measurable_pi_apply n
    refine hmeas ?_
    exact hf z y

theorem measurable_recOut_traj [MeasurableSpace U] [Countable S] [Countable Z]
    (g : RState S d J × Z → Fin (d + 1) × U → RState S d J × Z)
    (hg : ∀ x y, MeasurableSet {ξ | g x ξ = y}) (x : RState S d J × Z) :
    Measurable fun w : ℕ → Fin (d + 1) × U => recOut fun t => (traj g x w t).1 := by
  have hn : ∀ n (k : Fin J), Measurable fun w : ℕ → Fin (d + 1) × U => (traj g x w n).1.out k := by
    intro n k
    refine measurable_to_countable' fun v => ?_
    have : (fun w : ℕ → Fin (d + 1) × U => (traj g x w n).1.out k) ⁻¹' {v} =
        ⋃ y ∈ {y : RState S d J × Z | y.1.out k = v}, {w | traj g x w n = y} := by
      ext w; simp
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) fun y _ =>
      measurableSet_traj_eq g hg x n y
  refine measurable_pi_iff.2 fun k => measurable_to_countable' fun v => ?_
  have hge : ∀ v' : ℕ∞, MeasurableSet {w : ℕ → Fin (d + 1) × U | v' ≤ ⨅ n, (traj g x w n).1.out k} := by
    intro v'
    simp only [le_iInf_iff, Set.ofPred_forall]
    exact MeasurableSet.iInter fun n => hn n k (MeasurableSet.of_discrete (s := Set.Ici v'))
  have : (fun w : ℕ → Fin (d + 1) × U => recOut (fun t => (traj g x w t).1) k) ⁻¹' {v} =
      {w | v ≤ ⨅ n, (traj g x w n).1.out k} \
        ⋃ v' ∈ {v' : ℕ∞ | v < v'}, {w | v' ≤ ⨅ n, (traj g x w n).1.out k} := by
    ext w
    simp only [recOut, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq,
      Set.mem_iUnion, exists_prop, not_exists, not_and, not_le]
    constructor
    · rintro rfl
      exact ⟨le_rfl, fun v' hv' => hv'⟩
    · rintro ⟨h1, h2⟩
      exact le_antisymm (not_lt.1 fun hlt => (h2 _ hlt).false) h1
  rw [this]
  exact (hge v).diff (MeasurableSet.biUnion (Set.to_countable _) fun v' _ => hge v')

/-! ### The domination -/

/-- One more step adds one exit exactly when its direction is `0`. -/
theorem exitCount_succ (w : ℕ → Fin (d + 1) × U) (n : ℕ) :
    exitCount w (n + 1) = exitCount w n + if (w n).1 = 0 then 1 else 0 := by
  unfold exitCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => by simp at hm)]
  · rfl

/-- Along states whose exit count `e` moves as in the root chain, unbounded exits force a state
with more than `T` exits or an absorbed one. -/
theorem exists_stop_of_exits (cstep : S → U → ℕ × S) (st : ℕ → RState S d J)
    (w : ℕ → Fin (d + 1) × U) (hst : ∀ n, (st (n + 1)).e = (rstep cstep (st n) (w n)).e)
    (T : ℕ) (hw : ∀ m, ∃ n, m ≤ exitCount w n) :
    ∃ n, T < (st n).e ∨ J ≤ (st n).i := by
  by_contra h
  push Not at h
  have hcount : ∀ n, (st 0).e + exitCount w n = (st n).e := by
    intro n
    induction n with
    | zero => simp [exitCount]
    | succ n ih =>
      rw [hst n, rstep_e, exitCount_succ, ← ih]
      by_cases hw0 : (w n).1 = 0
      · simp [hw0, (h n).2]; omega
      · simp [hw0]
  obtain ⟨n, hn⟩ := hw (T + 1)
  have := hcount n
  have := (h n).1
  omega

/-- **Lemma 6.4, almost surely.** A chain that steps to states dominating the steps of the root
chain, and follows the root chain from its first state with more than `T` exits or absorbed on,
has outputs at least the outputs of the root chain, almost surely. -/
theorem ae_le_recOut_redirect [MeasurableSpace U] (cstep : S → U → ℕ × S) (R : S → S → Prop)
    (hR : IsSim cstep R) (g : RState S d J × Z → Fin (d + 1) × U → RState S d J × Z)
    (hg : ∀ x z ξ, Dom R (rstep cstep x ξ) (g (x, z) ξ).1) (free : RState S d J × Z → Prop)
    (hfree : ∀ y ξ, free y → (g y ξ).1 = rstep cstep y.1 ξ ∧ free (g y ξ)) (T : ℕ)
    (hstop : ∀ y : RState S d J × Z, T < y.1.e ∨ J ≤ y.1.i → free y)
    (ν : Measure (Fin (d + 1) × U)) [IsProbabilityMeasure ν] (hν : ν {ξ | ξ.1 = 0} ≠ 0)
    (x : RState S d J) (hx : Valid x) (z : Z) :
    ∀ᵐ w ∂(iidMeasure ν), outPsi cstep x w ≤ recOut fun t => (traj g (x, z) w t).1 := by
  filter_upwards [ae_exitCount_unbounded ν hν] with w hw
  have hst : ∀ n, (traj g (x, z) w (n + 1)).1.e =
      (rstep cstep (traj g (x, z) w n).1 (w n)).e := fun n =>
    ((hg (traj g (x, z) w n).1 (traj g (x, z) w n).2 (w n)).2.1).symm
  obtain ⟨n, hn⟩ := exists_stop_of_exits cstep (fun n => (traj g (x, z) w n).1) w hst T hw
  have hfr : ∀ k, n ≤ k → free (traj g (x, z) w k) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hstop _ hn
    | succ k _ ih => exact (hfree _ (w k) ih).2
  exact le_recOut_of_redirect cstep R hR g hg n x z w hx fun k hk => (hfree _ (w k) (hfr k hk)).1

/-- **Lemma 6.4 for laws.** The output law of the redirected chain dominates the output law of the
root chain in the coupling order. -/
theorem couplingLE_redirect [MeasurableSpace U] [Countable S] [Countable Z]
    (cstep : S → U → ℕ × S) (hc : ∀ s r, MeasurableSet {u | cstep s u = r}) (R : S → S → Prop)
    (hR : IsSim cstep R) (g : RState S d J × Z → Fin (d + 1) × U → RState S d J × Z)
    (hgm : ∀ y y', MeasurableSet {ξ | g y ξ = y'})
    (hg : ∀ x z ξ, Dom R (rstep cstep x ξ) (g (x, z) ξ).1) (free : RState S d J × Z → Prop)
    (hfree : ∀ y ξ, free y → (g y ξ).1 = rstep cstep y.1 ξ ∧ free (g y ξ)) (T : ℕ)
    (hstop : ∀ y : RState S d J × Z, T < y.1.e ∨ J ≤ y.1.i → free y)
    (ν : Measure (Fin (d + 1) × U)) [IsProbabilityMeasure ν] (hν : ν {ξ | ξ.1 = 0} ≠ 0)
    (x : RState S d J) (hx : Valid x) (z : Z) :
    FrogModel.LemmaX.CouplingLE ((iidMeasure ν).map (outPsi cstep x))
      ((iidMeasure ν).map fun w => recOut fun t => (traj g (x, z) w t).1) := by
  have : IsProbabilityMeasure (iidMeasure ν) := by unfold iidMeasure; infer_instance
  exact FrogModel.LemmaX.couplingLE_of_map _ _ _ (measurable_outPsi cstep hc x)
    (measurable_recOut_traj g hgm (x, z))
    (FrogModel.LemmaX.measurableSet_le_pi fun _ => FrogModel.LemmaX.measurableSet_le_of_countable)
    (ae_le_recOut_redirect cstep R hR g hg free hfree T hstop ν hν x hx z)


/-! ### The root chain stops or is absorbed -/

/-- While the root chain is live, its exit count is the start's plus the exits read. -/
theorem exitCount_le_traj_e (cstep : S → U → ℕ × S) (x : RState S d J)
    (w : ℕ → Fin (d + 1) × U) (n : ℕ) (hlive : (traj (rstep cstep) x w n).i < J) :
    x.e + exitCount w n = (traj (rstep cstep) x w n).e := by
  induction n with
  | zero => simp [traj, exitCount]
  | succ n ih =>
    have hlive_n : (traj (rstep cstep) x w n).i < J :=
      lt_of_le_of_lt (traj_i_mono cstep x w (Nat.le_succ n)) hlive
    have h := ih hlive_n
    rw [exitCount_succ, show traj (rstep cstep) x w (n + 1) =
      rstep cstep (traj (rstep cstep) x w n) (w n) from rfl, rstep_e]
    by_cases hdir : (w n).1 = 0
    · simp only [hdir, hlive_n, and_self, ite_true]
      omega
    · simp only [hdir, and_false, ite_false]
      omega

/-- Under i.i.d. inputs whose directions exit with positive probability, the root chain almost
surely makes more than `T` exits or is absorbed. -/
theorem ae_stop_or_absorbed [MeasurableSpace U] (cstep : S → U → ℕ × S)
    (ν : Measure (Fin (d + 1) × U)) [IsProbabilityMeasure ν] (hν : ν {ξ | ξ.1 = 0} ≠ 0)
    (x : RState S d J) (T : ℕ) :
    ∀ᵐ w ∂(iidMeasure ν), ∃ n, T < (traj (rstep cstep) x w n).e ∨ J ≤ (traj (rstep cstep) x w n).i := by
  filter_upwards [ae_exitCount_unbounded ν hν] with w hw
  by_contra h
  push Not at h
  obtain ⟨n, hn⟩ := hw (T + 1)
  have h_eq := exitCount_le_traj_e cstep x w n (h n).2
  have := (h n).1
  omega

end FrogModel.Engine
