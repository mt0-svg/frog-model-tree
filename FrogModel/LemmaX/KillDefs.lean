module

public import FrogModel.Pieces.Defs

@[expose] public section

/-!
# Lemma X: the kill depth

Section 4.1 of the paper. At kill depth `K` a frog of `T*` is killed at its first step to depth
`K + 1` below `r`: that vertex is not visited, so no frog at depth `K + 1` or deeper is ever
woken. `visitsK K v x b`: the walk on `T*` from `v` driven by `x` is at `b` at some time `n`
having stayed at depth at most `K` up to `n` (the leaf `y = none` has depth `0`); a frog is frozen
when it visits `y`. `frozenCountK K` is `X^(K)`. `curveK K ζ ξ m` is the response curve `G_K(m)`:
the active frogs at `r` follow `ξ 0, ..., ξ (m - 1)`, there is no other frog at `r` (`ζ []` is
never read), and the sleeping frog at `some v`, `v ≠ []`, follows `ζ v`.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.LemmaX

variable {d : ℕ}

/-- The depth below `r` of a vertex of `T*`, `0` at the leaf `y`. -/
def depthStar : Option (Vertex d) → ℕ
  | none => 0
  | some v => v.length

/-- At kill depth `K`, the walk on `T*` from `v` driven by `x` visits `b` before it is killed. -/
def visitsK (K : ℕ) (v : Option (Vertex d)) (x : ℕ → Step d) (b : Option (Vertex d)) : Prop :=
  ∃ n, walkStar v x n = b ∧ ∀ i ≤ n, depthStar (walkStar v x i) ≤ K

/-- The arcs of the reachability digraph of `T*` at kill depth `K`: frog `a` reaches the frog of
`b ≠ r` when its path visits `some b` before it is killed. -/
def starArcK (K : ℕ) (ζ : Sample d) (a b : Vertex d) : Prop :=
  b ≠ [] ∧ visitsK K (some a) (ζ a) (some b)

open Classical in
/-- `X^(K)`: the number of frogs of `T*` reached from the frog at `r` and frozen, at kill depth
`K`. -/
noncomputable def frozenCountK (K : ℕ) (ζ : Sample d) : ℝ≥0∞ :=
  ∑' v : Vertex d,
    if Relation.ReflTransGen (starArcK K ζ) [] v ∧ visitsK K (some v) (ζ v) none then 1 else 0

/-- At kill depth `K`, with active frogs `ξ 0, ..., ξ (m - 1)` at `r`, the frog of `b` is
reached: an active frog visits some `v ≠ r` before it is killed, and `v` reaches `b`. -/
def reachedK (K : ℕ) (ζ : Sample d) (ξ : ℕ → ℕ → Step d) (m : ℕ) (b : Vertex d) : Prop :=
  ∃ a < m, ∃ v : Vertex d, v ≠ [] ∧ visitsK K (some []) (ξ a) (some v) ∧
    Relation.ReflTransGen (starArcK K ζ) v b

/-- The response curve `G_K(m)` at kill depth `K`: the frozen frogs among the active frogs
`ξ 0, ..., ξ (m - 1)` at `r` and the reached sleeping frogs. -/
noncomputable def curveK (K : ℕ) (ζ : Sample d) (ξ : ℕ → ℕ → Step d) (m : ℕ) : ℕ∞ :=
  {a : ℕ | a < m ∧ visitsK K (some []) (ξ a) none}.encard +
    {b : Vertex d | reachedK K ζ ξ m b ∧ visitsK K (some b) (ζ b) none}.encard

end FrogModel.LemmaX
