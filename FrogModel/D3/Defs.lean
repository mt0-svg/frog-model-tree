module

public import FrogModel.Defs

@[expose] public section

/-!
# The definition of the frozen d = 3 statement

The definition of FrogModel/ChallengeRecurrent.lean that the d = 4 statement lacks, line for line:
`Recurrent d` over the definitions of FrogModel/Defs.lean. The development imports this module; the
challenge imports nothing of the development, and a Comparator run checks that the final theorem has
the type of its target with these definitions.
-/

open MeasureTheory

namespace FrogModel

/-- The frog model on the rooted `d`-ary tree is recurrent: almost surely the root is visited
infinitely often. -/
def Recurrent (d : ℕ) [NeZero d] : Prop :=
  ∀ᵐ ω ∂frogMeasure d, (visits (paths ω)).Infinite

end FrogModel
