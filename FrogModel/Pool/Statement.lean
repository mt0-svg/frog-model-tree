module

public import Mathlib

@[expose] public section

/-!
# Frozen statement: pieces drawn from i.i.d. pools in an adapted order

The pools of the proof of Lemma 4.3 of the paper.

Pools `i : I` (countable), each an i.i.d. sequence of pieces in a measurable space `E` with law
`μ i`. A rule `sel k y` gives the pool of the `k`-th piece from the pieces `y` already read. On the
pool space `I × ℕ → E` (coordinate `(i, m)`: the `m`-th element of pool `i`) the `k`-th piece is the
first unused element of its pool (`poolRead`). On the fresh space `ℕ × I → E` the `k`-th piece is
coordinate `(k, i)` of a fresh vector (`freshRead`). Both spaces carry the product of the pool laws.

- `MapPoolRead`, `MapPoolSeq`: the pieces read, listed in order of use, have the same law in both
  spaces, for every number `n` of pieces and for the whole sequence (`poolSeq`, `freshSeq`).
- `MeasurablePoolRead`, `MeasurableFreshRead`, `MeasurablePoolSeq`: the maps whose laws these are
  measurable. `Measure.map` of a map that is not a.e.-measurable is a junk value, so these make
  the laws above the laws of the pieces.
- `MapFreshReadSucc`: on the fresh space the law of `n + 1` pieces is the law of `n` pieces bound
  with the kernel `y ↦ (μ (sel n y)).map (Fin.snoc y)`.

Each statement is a `Prop`; Pool/Main.lean proves it (`mapPoolRead_holds` and so on), from the
theorems `map_poolRead`, `map_poolSeq`, `map_freshRead_succ`, `measurable_poolRead`,
`measurable_freshRead`, `measurable_poolSeq` with the same hypotheses and conclusions.
-/

open MeasureTheory

namespace FrogModel.Pool

variable {I E : Type*} [MeasurableSpace E]

open Classical in
/-- The first `n` pieces read on the pool space: the `k`-th is the first element of pool
`sel k y` not read before, `y` the pieces read before it. -/
noncomputable def poolRead (sel : ∀ k : ℕ, (Fin k → E) → I) (ω : I × ℕ → E) :
    (n : ℕ) → Fin n → E
  | 0 => Fin.elim0
  | n + 1 =>
    Fin.snoc (poolRead sel ω n)
      (ω (sel n (poolRead sel ω n),
        ((Finset.univ : Finset (Fin n)).filter fun j : Fin n =>
          sel j.val (Fin.take j.val j.isLt.le (poolRead sel ω n)) =
            sel n (poolRead sel ω n)).card))

/-- The first `n` pieces read on the fresh space: the `k`-th is coordinate `(k, sel k y)`. -/
def freshRead (sel : ∀ k : ℕ, (Fin k → E) → I) (ω : ℕ × I → E) : (n : ℕ) → Fin n → E
  | 0 => Fin.elim0
  | n + 1 => Fin.snoc (freshRead sel ω n) (ω (n, sel n (freshRead sel ω n)))

/-- All the pieces read on the pool space, in order of use. -/
noncomputable def poolSeq (sel : ∀ k : ℕ, (Fin k → E) → I) (ω : I × ℕ → E) : ℕ → E :=
  fun k => poolRead sel ω (k + 1) (Fin.last k)

/-- All the pieces read on the fresh space. -/
def freshSeq (sel : ∀ k : ℕ, (Fin k → E) → I) (ω : ℕ × I → E) : ℕ → E :=
  fun k => freshRead sel ω (k + 1) (Fin.last k)

/-- The pool space: element `m` of pool `i` has law `μ i`, all independent. -/
noncomputable def poolMeasure (μ : I → Measure E) : Measure (I × ℕ → E) :=
  Measure.infinitePi fun p : I × ℕ => μ p.1

/-- The fresh space: coordinate `(k, i)` has law `μ i`, all independent. -/
noncomputable def freshMeasure (μ : I → Measure E) : Measure (ℕ × I → E) :=
  Measure.infinitePi fun p : ℕ × I => μ p.2

universe u v

/-- The pieces read on the pool space are measurable. -/
def MeasurablePoolRead : Prop :=
  ∀ (I : Type u) (E : Type v) [MeasurableSpace E] (sel : ∀ k : ℕ, (Fin k → E) → I) [Countable I],
    (∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) → ∀ n : ℕ,
    Measurable fun ω : I × ℕ → E => poolRead sel ω n

/-- All the pieces read are measurable, on both spaces. -/
def MeasurablePoolSeq : Prop :=
  ∀ (I : Type u) (E : Type v) [MeasurableSpace E] (sel : ∀ k : ℕ, (Fin k → E) → I) [Countable I],
    (∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) →
    Measurable (poolSeq sel) ∧ Measurable (freshSeq sel)

/-- The pieces read on the fresh space are measurable. -/
def MeasurableFreshRead : Prop :=
  ∀ (I : Type u) (E : Type v) [MeasurableSpace E] (sel : ∀ k : ℕ, (Fin k → E) → I) [Countable I],
    (∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) → ∀ n : ℕ,
    Measurable fun ω : ℕ × I → E => freshRead sel ω n

/-- **Pools.** Pieces drawn from i.i.d. pools in an order that depends only on the pieces already
read have the law of pieces drawn fresh at every step. -/
def MapPoolRead : Prop :=
  ∀ (I : Type u) (E : Type v) [MeasurableSpace E] [Countable I] (μ : I → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (sel : ∀ k : ℕ, (Fin k → E) → I),
    (∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) → ∀ n : ℕ,
    (poolMeasure μ).map (fun ω => poolRead sel ω n) =
      (freshMeasure μ).map (fun ω => freshRead sel ω n)

/-- **Pools, whole sequence.** -/
def MapPoolSeq : Prop :=
  ∀ (I : Type u) (E : Type v) [MeasurableSpace E] [Countable I] (μ : I → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (sel : ∀ k : ℕ, (Fin k → E) → I),
    (∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) →
    (poolMeasure μ).map (poolSeq sel) = (freshMeasure μ).map (freshSeq sel)

/-- **One step on the fresh space.** The law of `n + 1` pieces is the law of `n` pieces bound with
the kernel `y ↦ (μ (sel n y)).map (Fin.snoc y)`. -/
def MapFreshReadSucc : Prop :=
  ∀ (I : Type u) (E : Type v) [MeasurableSpace E] [Countable I] (μ : I → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (sel : ∀ k : ℕ, (Fin k → E) → I),
    (∀ (k : ℕ) (i : I), MeasurableSet {y : Fin k → E | sel k y = i}) → ∀ n : ℕ,
    (freshMeasure μ).map (fun ω => freshRead sel ω (n + 1)) =
      ((freshMeasure μ).map (fun ω => freshRead sel ω n)).bind
        (fun y => (μ (sel n y)).map (Fin.snoc (α := fun _ => E) y))

end FrogModel.Pool
