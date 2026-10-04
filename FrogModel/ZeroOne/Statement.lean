module

public import FrogModel.Defs
public import FrogModel.Pieces.Defs

@[expose] public section

/-!
# Frozen statement: Theorem 9.3 of the paper

`RecurrentOfFrozenCount d` (Theorem 9.3): if the planted tree `T*` (Pieces/Defs.lean) has
infinitely many frozen frogs with positive probability, the root is visited infinitely often
almost surely. Proved in ZeroOne/Main.lean as `FrogModel.ZeroOne.recurrent_of_frozenCount` and
`FrogModel.ZeroOne.recurrentOfFrozenCount_holds`.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.ZeroOne

/-- **Theorem 9.3 of the paper.** Infinitely many frozen frogs in `T*` with positive probability give
recurrence: almost surely the root is visited infinitely often. -/
def RecurrentOfFrozenCount (d : ℕ) [NeZero d] : Prop :=
  2 ≤ d → 0 < frogMeasure d {ζ | frozenCount ζ = ⊤} →
    ∀ᵐ ω ∂frogMeasure d, (visits (paths ω)).Infinite

end FrogModel.ZeroOne
