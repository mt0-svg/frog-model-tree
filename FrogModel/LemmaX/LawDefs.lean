module

public import FrogModel.Recursion.Statement
public import FrogModel.Lemmas.Defs

@[expose] public section

/-!
# Lemma X: the coupling order and the laws of the induction

Sections 4.2, 4.4 and 5 of the paper. The curve law `N_K` is
`FrogModel.Recursion.curveLaw d K` and `Psi` on laws is `FrogModel.Recursion.psiLaw d`
(Recursion/Statement.lean); they are not redefined here.

- `CouplingLE P Q`: the coupling order, a probability law on pairs with marginals `P` and `Q`,
  carried by `{p | p.1 ≤ p.2}`. On `ℕ → ℕ∞` (curves) and on `Fin J → ℕ∞` (blocks) the order is
  Mathlib's pointwise order.
- `firstValues J G = (G(1), ..., G(J))`, coordinate `s` holding `G (s + 1)`; the restriction
  `P|_J` of a curve law `P` is `P.map (firstValues J)`.
- `blockLaw d K J`: `E_K`, the law of the first `J` values of the curve at kill depth `K`.
- `blockCurve B`: a block as a curve on `0, ..., J`.
- `brLaw J H`: `BR(H)`, the law of the curve of i.i.d. blocks of law `H` (`Order.brCurve`).
- `phiLaw d J H`: `Phi_J(H) = Psi(BR(H))|_J`.

`Measure.infinitePi` of a family that is not of probability measures is `0`, so `brLaw J H` is
`0` unless `H` is a probability measure; every law it is applied to below is one (an image of a
probability measure, or a marginal of a coupling).
-/

open MeasureTheory

namespace FrogModel.LemmaX

open FrogModel.Recursion

/-- The coupling order: a probability law on pairs with marginals `P` and `Q`, carried by
`{p | p.1 ≤ p.2}`. -/
def CouplingLE {α : Type*} [MeasurableSpace α] [LE α] (P Q : Measure α) : Prop :=
  ∃ π : Measure (α × α), IsProbabilityMeasure π ∧ π.map Prod.fst = P ∧ π.map Prod.snd = Q ∧
    ∀ᵐ p ∂π, p.1 ≤ p.2

/-- The first `J` values `(G(1), ..., G(J))` of a curve, coordinate `s` holding `G (s + 1)`. -/
def firstValues (J : ℕ) (G : ℕ → ℕ∞) : Fin J → ℕ∞ := fun s => G ((s : ℕ) + 1)

/-- `E_K`: the law of the first `J` values `(G_K(1), ..., G_K(J))` of the curve at kill
depth `K`. -/
noncomputable def blockLaw (d : ℕ) [NeZero d] (K J : ℕ) : Measure (Fin J → ℕ∞) :=
  (curveLaw d K).map (firstValues J)

/-- A block as a curve on `0, ..., J`: `0` at `0` and `B ⟨s - 1⟩` at `1 ≤ s ≤ J` (and `0`
beyond `J`, never read by `Order.brCurve`). -/
def blockCurve {J : ℕ} (B : Fin J → ℕ∞) (s : ℕ) : ℕ∞ :=
  if h : 0 < s ∧ s ≤ J then B ⟨s - 1, by omega⟩ else 0

/-- `BR(H)`: the law of `Order.brCurve J` of i.i.d. blocks of law `H`. -/
noncomputable def brLaw (J : ℕ) (H : Measure (Fin J → ℕ∞)) : Measure (ℕ → ℕ∞) :=
  (Measure.infinitePi fun _ : ℕ => H).map fun B =>
    FrogModel.Order.brCurve J fun b => blockCurve (B b)

/-- `Phi_J(H) = Psi(BR(H))|_J`, a map of laws on `Fin J → ℕ∞`. -/
noncomputable def phiLaw (d J : ℕ) (H : Measure (Fin J → ℕ∞)) : Measure (Fin J → ℕ∞) :=
  (psiLaw d (brLaw J H)).map (firstValues J)

end FrogModel.LemmaX
