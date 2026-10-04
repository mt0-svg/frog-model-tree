module

public import FrogModel.LemmaR.Statement
public import FrogModel.Pieces.Defs

@[expose] public section

/-!
# Frozen statement: the recurrence criterion on the planted tree (Theorem 8.2 and Lemma 9.2 of the paper)

The planted tree `T*` of `FrogModel.Pieces.Defs`: frog `v` sits at `some v`, follows the steps
`ζ v`, and `frozenCount ζ` is the number `X` of frogs reached from the frog at `r = some []` whose
path reaches the leaf `y = none`.

- `starArcTrunc m ζ`: the arcs of `starArc ζ` towards frogs at depth at most `m`.
- `plantedCount m ζ`: `Z_m`, the frozen count of `T*` with sleeping frogs at depth at most `m`
  only (the deeper ones are absent, so they are never woken).
- `plantedAwake m ζ`: `U'_m`, the number of frogs of `T*` at depth at most `m` whose path reaches
  `y`, all of them awake.
- `PlantedLemmaRStatement d`: if `limsup_m E Z_m / m > 0` then `P(X = ∞) > 0`, which is the
  hypothesis `hX` of `FrogModel.ZeroOne.recurrent_of_frozenCount` (ZeroOne/Main.lean).
- `PlantedLemmaRLowerStatement d`: the same conclusion for any a.e.-measurable `Z m` with
  `Z m ≤ X` and `Z m ≤ U'_m` almost surely and `c m ≤ E Z m` for infinitely many `m`, `c > 0`.
- `RecurrentOfPlantedStatement d`: with the implication of `recurrent_of_frozenCount` as a
  hypothesis, the hypothesis of `PlantedLemmaRStatement` gives `Recurrent d`.

Proved in Planted/Main.lean: `plantedLemmaR'`, `plantedLemmaR_lower'`, `recurrent_of_planted'`,
and the three statements as `plantedLemmaRStatement_holds`, `plantedLemmaRLowerStatement_holds`,
`recurrentOfPlantedStatement_holds`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace FrogModel.LemmaR

variable {d : ℕ}

/-- The arcs of the reachability digraph of `T*` towards frogs at depth at most `m`: frog `a`
reaches the frog of `b ≠ r` when its path visits `some b` and `|b| ≤ m`. -/
def starArcTrunc (m : ℕ) (ζ : Sample d) (a b : Vertex d) : Prop :=
  starArc ζ a b ∧ b.length ≤ m

open Classical in
/-- `Z_m`: the number of frogs of `T*` reached from the frog at `r` through frogs at depth at
most `m` whose path reaches `y`. -/
noncomputable def plantedCount (m : ℕ) (ζ : Sample d) : ℝ≥0∞ :=
  ∑' v : Vertex d,
    if Relation.ReflTransGen (starArcTrunc m ζ) [] v ∧ ∃ n, walkStar (some v) (ζ v) n = none then 1
    else 0

open Classical in
/-- `U'_m`: the number of frogs of `T*` at depth at most `m` whose path reaches `y`. -/
noncomputable def plantedAwake (m : ℕ) (ζ : Sample d) : ℝ≥0∞ :=
  ∑' v : Vertex d, if v.length ≤ m ∧ ∃ n, walkStar (some v) (ζ v) n = none then 1 else 0

/-- **Lemma 9.2 of the paper.** A linear first moment of the truncated planted counts gives
infinitely many frozen frogs with positive probability. -/
def PlantedLemmaRStatement (d : ℕ) [NeZero d] : Prop :=
  0 < limsup (fun m : ℕ => (∫⁻ ζ, plantedCount m ζ ∂frogMeasure d) / m) atTop →
    0 < frogMeasure d {ζ | frozenCount ζ = ⊤}

/-- **Lemma 9.2 of the paper for a lower model.** -/
def PlantedLemmaRLowerStatement (d : ℕ) [NeZero d] : Prop :=
  ∀ Z : ℕ → Sample d → ℝ≥0∞, (∀ m, AEMeasurable (Z m) (frogMeasure d)) →
    (∀ m, ∀ᵐ ζ ∂frogMeasure d, Z m ζ ≤ frozenCount ζ) →
    (∀ m, ∀ᵐ ζ ∂frogMeasure d, Z m ζ ≤ plantedAwake m ζ) →
    ∀ c : ℝ≥0∞, 0 < c → (∃ᶠ m in atTop, c * m ≤ ∫⁻ ζ, Z m ζ ∂frogMeasure d) →
    0 < frogMeasure d {ζ | frozenCount ζ = ⊤}

/-- Lemma 9.2 and Theorem 9.3 of the paper give recurrence: Theorem 8.2. -/
def RecurrentOfPlantedStatement (d : ℕ) [NeZero d] : Prop :=
  (0 < frogMeasure d {ζ | frozenCount ζ = ⊤} →
      ∀ᵐ ω ∂frogMeasure d, (visits (paths ω)).Infinite) →
    0 < limsup (fun m : ℕ => (∫⁻ ζ, plantedCount m ζ ∂frogMeasure d) / m) atTop → Recurrent d

end FrogModel.LemmaR
