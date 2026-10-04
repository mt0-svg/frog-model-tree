module

public import FrogModel.LemmaR.Planted.Main
public import FrogModel.ZeroOne.Main

@[expose] public section

/-!
# Lemma 9.2 against Theorem 9.3 of the paper: Theorem 8.2

The conclusion of `plantedLemmaR` is the hypothesis `hX` of
`FrogModel.ZeroOne.recurrent_of_frozenCount` (Theorem 9.3, proved in ZeroOne/Main.lean; frozen
statement `FrogModel.ZeroOne.RecurrentOfFrozenCount` in ZeroOne/Statement.lean), and the
hypothesis `hB` of `recurrent_of_planted` is `recurrent_of_frozenCount d hd` itself.
`recurrent_of_plantedCount` composes the proved theorems.
-/

open MeasureTheory Filter
open scoped ENNReal
open FrogModel FrogModel.LemmaR

example {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    type_of% (FrogModel.ZeroOne.recurrent_of_frozenCount d hd) =
      (0 < frogMeasure d {ζ | frozenCount ζ = ⊤} →
        ∀ᵐ ω ∂frogMeasure d, (visits (paths ω)).Infinite) := rfl

example {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (h : 0 < limsup (fun m : ℕ => (∫⁻ ζ, plantedCount m ζ ∂frogMeasure d) / m) atTop) :
    ∀ᵐ ω ∂frogMeasure d, (visits (paths ω)).Infinite :=
  FrogModel.ZeroOne.recurrent_of_frozenCount d hd (plantedLemmaR' h)

/-- **Theorem 8.2 of the paper**, from Lemma 9.2 and Theorem 9.3: a linear first moment of the
truncated planted counts gives recurrence. -/
theorem FrogModel.LemmaR.recurrent_of_plantedCount {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (h : 0 < limsup (fun m : ℕ => (∫⁻ ζ, plantedCount m ζ ∂frogMeasure d) / m) atTop) :
    Recurrent d :=
  recurrent_of_planted' (FrogModel.ZeroOne.recurrent_of_frozenCount d hd) h
