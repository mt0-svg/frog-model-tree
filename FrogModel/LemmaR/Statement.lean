module

public import FrogModel.Defs

@[expose] public section

/-!
# The counts of visits to the root on `T_d`, and the definition `Recurrent`

Definitions on the frog model of FrogModel/Defs.lean (frogs named by their start vertex; once woken,
frog `u` follows the path `paths ω u`; `visits` are the pairs (frog, time `t ≥ 1`) with an active
frog at the root), used by FrogModel/LemmaR and FrogModel/D3:

- `truncPaths n S`: the frogs at depth `≤ n` follow their paths `S u`, the deeper ones never move.
  A frog that never moves sits at a vertex other than the root: it never visits the root and wakes
  no other frog. So `visits (truncPaths n S)` are the visits of the frog model with sleeping frogs
  at depths `1, ..., n` only and infinite walks, run by the frozen `wake`.
- `truncCount n ω`: their number `V^(n)`.
- `awakeCount n ω`: the count `U_n` of the frogs at depth `≤ n` as if all were awake at time `0`:
  the pairs (frog `u` at depth `≤ n`, time `t ≥ 1`) with the path of `u` at the root at time `t`.
- `Recurrent d`: almost surely the root is visited infinitely often. It is the `Recurrent` of the
  frozen statement by `Iff.rfl` (`FrogModel.D3.recurrent_iff_lemmaR`).

The module also states three forms of the criterion of recurrence on the tree itself:
`LemmaRStatement d` (on the rooted `d`-ary tree, `d ≥ 2`, if `limsup_n E V^(n) / n > 0`, the root
is visited infinitely often with positive probability), `LemmaRLowerStatement d` (the same
conclusion for any lower model: counts `Z n ≤ V` and `Z n ≤ U_n` almost surely with
`E Z n ≥ c n`, `c > 0`, for infinitely many `n`) and `RecurrentOfZeroOneStatement d` (with a 0-1
law for the event of infinitely many visits, `LemmaRStatement` gives recurrence). This repository
does not prove them and the proof does not use them: it proves the planted form instead
(FrogModel/LemmaR/Planted, Theorem 8.2 of the paper), with Theorem 9.3 in place of the 0-1 law.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace FrogModel.LemmaR

variable {d : ℕ}

/-- The paths of the model truncated at depth `n`: frog `u` follows `S u` if `u` is at depth
`≤ n`, and stays at `u` forever otherwise. -/
def truncPaths (n : ℕ) (S : Vertex d → ℕ → Vertex d) : Vertex d → ℕ → Vertex d :=
  fun u => if u.length ≤ n then S u else fun _ => u

/-- `V^(n)`: the number of visits to the root of the frog model with sleeping frogs at depths
`1, ..., n` only (the deeper frogs never move), on the paths of `ω`. -/
noncomputable def truncCount (n : ℕ) (ω : Sample d) : ℝ≥0∞ :=
  (((visits (truncPaths n (paths ω))).encard : ℕ∞) : ℝ≥0∞)

/-- `U_n`: the visits to the root of the frogs at depth `≤ n` as if all were awake from time `0`,
the pairs `(u, t)` with `|u| ≤ n`, `t ≥ 1` and the path of `u` at the root at time `t`. -/
noncomputable def awakeCount (n : ℕ) (ω : Sample d) : ℝ≥0∞ :=
  (({p : Vertex d × ℕ | p.1.length ≤ n ∧ 1 ≤ p.2 ∧ paths ω p.1 p.2 = root}.encard : ℕ∞) : ℝ≥0∞)

/-- The frog model is recurrent: almost surely the root is visited infinitely often. It is the
`FrogModel.Recurrent` of the frozen statement (FrogModel/D3/Defs.lean, the definition of
FrogModel/ChallengeRecurrent.lean line for line) by `Iff.rfl`, as
`FrogModel.D3.recurrent_iff_lemmaR` states. -/
def Recurrent (d : ℕ) [NeZero d] : Prop :=
  ∀ᵐ ω ∂frogMeasure d, (visits (paths ω)).Infinite


/-- **Recurrence from a linear first moment.** On the rooted `d`-ary tree, `d ≥ 2`: if
`limsup_n E V^(n) / n > 0`, the root is visited infinitely often with positive probability. Not
proved in this repository, and not used by the proof. -/
def LemmaRStatement (d : ℕ) [NeZero d] : Prop :=
  2 ≤ d → 0 < limsup (fun n : ℕ => (∫⁻ ω, truncCount n ω ∂frogMeasure d) / n) atTop →
    0 < frogMeasure d {ω | (visits (paths ω)).Infinite}

/-- **Recurrence from a linear first moment, for a lower model.** Counts `Z n` with `Z n ≤ V` and
`Z n ≤ U_n` almost surely and `E Z n ≥ c n` for infinitely many `n`, `c > 0`: the root is visited
infinitely often with positive probability. Not proved in this repository, and not used by the
proof. -/
def LemmaRLowerStatement (d : ℕ) [NeZero d] : Prop :=
  2 ≤ d → ∀ Z : ℕ → Sample d → ℝ≥0∞, (∀ n, AEMeasurable (Z n) (frogMeasure d)) →
    (∀ n, ∀ᵐ ω ∂frogMeasure d, Z n ω ≤ (((visits (paths ω)).encard : ℕ∞) : ℝ≥0∞)) →
    (∀ n, ∀ᵐ ω ∂frogMeasure d, Z n ω ≤ awakeCount n ω) →
    ∀ c : ℝ≥0∞, 0 < c → (∃ᶠ n in atTop, c * n ≤ ∫⁻ ω, Z n ω ∂frogMeasure d) →
    0 < frogMeasure d {ω | (visits (paths ω)).Infinite}

/-- `LemmaRStatement` and a 0-1 law for the event of infinitely many visits give recurrence. Not
proved in this repository, and not used by the proof. -/
def RecurrentOfZeroOneStatement (d : ℕ) [NeZero d] : Prop :=
  2 ≤ d → (frogMeasure d {ω | (visits (paths ω)).Infinite} = 0 ∨
      frogMeasure d {ω | (visits (paths ω)).Infinite} = 1) →
    0 < limsup (fun n : ℕ => (∫⁻ ω, truncCount n ω ∂frogMeasure d) / n) atTop → Recurrent d

end FrogModel.LemmaR
