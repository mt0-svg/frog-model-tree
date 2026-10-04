module

public import FrogModel.LemmaR.Planted.Statement

@[expose] public section

/-!
# The planted counts: the woken set written as a least set, as in Definition 8.1 of the paper

`ReachStar ζ m`: the least set of frogs of `T*` containing the frog at `r` and closed under the
visits of the paths of its members to vertices at depth at most `m`. The cross-check
`plantedCount_eq_reachStar` (Planted/Paths.lean) proves that `plantedCount m ζ` counts the members
of this set whose path reaches `y`.
-/

namespace FrogModel.LemmaR

variable {d : ℕ}

/-- The frogs of `T*` woken when the sleeping frogs sit at depth at most `m` only. -/
inductive ReachStar (ζ : Sample d) (m : ℕ) : Vertex d → Prop
  | root : ReachStar ζ m []
  | path {a b : Vertex d} (n : ℕ) : ReachStar ζ m a → walkStar (some a) (ζ a) n = some b →
      b.length ≤ m → ReachStar ζ m b

end FrogModel.LemmaR
