module

public import FrogModel.Engine.Defs

@[expose] public section

/-!
# The dominating chain: definitions

The redirected chain of the proof of Theorem 6.5 of the paper. The dominating chain
runs on root states with a flag, set once a stop has occurred. From a flagged state, a state with
more than `T` exits, or an absorbed state, it is the root chain with the flag kept (`domFree`).
Otherwise it takes the step `x'` of the root chain; it sets the flag if `x'` has more than `T`
exits or more than `T'` pending frogs, keeps `x'` if `x'` is absorbed or `keep x'` (a state of
the data with flag 1), and moves to `lump x'` (the state of max labels) otherwise.

The output law of the dominating chain splits into the part absorbed unflagged with outputs `o`
(the events `absUnflagged`, a least solution of the system with kernel `fkKernel (domStep ..)`)
and the flagged part, whose weight `E theta^B(J)` is bounded through the reward `flagReward` at
the step that sets the flag. `contrW` is the contraction weight `2^(T + 1 - e)` on the live
unflagged states with at most `T` exits.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Engine

variable {S U : Type*} {d J : ℕ}

/-- **The dominating chain**: one step from `y = (state, flag)`. -/
def domStep (cstep : S → U → ℕ × S) (T T' : ℕ) (keep : RState S d J → Bool)
    (lump : RState S d J → RState S d J) (y : RState S d J × Bool) (ξ : Fin (d + 1) × U) :
    RState S d J × Bool :=
  if y.2 = true ∨ T < y.1.e ∨ J ≤ y.1.i then (rstep cstep y.1 ξ, y.2)
  else if T < (rstep cstep y.1 ξ).e ∨ T' < (rstep cstep y.1 ξ).p then (rstep cstep y.1 ξ, true)
  else if J ≤ (rstep cstep y.1 ξ).i ∨ keep (rstep cstep y.1 ξ) = true then
    (rstep cstep y.1 ξ, false)
  else (lump (rstep cstep y.1 ξ), false)

/-- The states from which the dominating chain is the root chain. -/
def domFree (T : ℕ) (y : RState S d J × Bool) : Prop :=
  y.2 = true ∨ T < y.1.e ∨ J ≤ y.1.i

/-- The outputs recorded along the trajectory of a chain on states with a memory. -/
noncomputable def domOut {Z : Type*} (g : RState S d J × Z → Fin (d + 1) × U → RState S d J × Z)
    (y : RState S d J × Z) (w : ℕ → Fin (d + 1) × U) : Fin J → ℕ∞ :=
  recOut fun t => (traj g y w t).1

/-- The inputs whose step absorbs the chain unflagged with the outputs `o`. -/
def absUnflagged (g : RState S d J × Bool → Fin (d + 1) × U → RState S d J × Bool)
    (o : Fin J → ℕ) (y : RState S d J × Bool) : Set (Fin (d + 1) × U) :=
  {ξ | y.2 = false ∧ y.1.i < J ∧ (g y ξ).2 = false ∧ J ≤ (g y ξ).1.i ∧
    (g y ξ).1.out = fun k => (o k : ℕ∞)}

/-- The inputs whose step sets the flag. -/
def flagSet (g : RState S d J × Bool → Fin (d + 1) × U → RState S d J × Bool)
    (y : RState S d J × Bool) : Set (Fin (d + 1) × U) :=
  {ξ | y.2 = false ∧ (g y ξ).2 = true}

open Classical in
/-- The reward `Phi` of the state reached at the step that sets the flag. -/
noncomputable def flagReward (g : RState S d J × Bool → Fin (d + 1) × U → RState S d J × Bool)
    (Φ : RState S d J → ℝ≥0∞) (y : RState S d J × Bool) (ξ : Fin (d + 1) × U) : ℝ≥0∞ :=
  if y.2 = false ∧ (g y ξ).2 = true then Φ (g y ξ).1 else 0

open Classical in
/-- The contraction weight: `2^(T + 1 - e)` on the live unflagged states with `e ≤ T`. -/
noncomputable def contrW (T : ℕ) (y : RState S d J × Bool) : ℝ≥0∞ :=
  if y.2 = false ∧ y.1.i < J ∧ y.1.e ≤ T then 2 ^ (T + 1 - y.1.e) else 0

end FrogModel.Engine
