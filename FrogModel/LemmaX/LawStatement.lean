module

public import FrogModel.LemmaX.LawDefs
public import FrogModel.LemmaX.ClaimADefs

@[expose] public section

/-!
# Frozen statements: Claim A, the coupling order, the induction

Sections 4 and 5 of the paper. Each statement is a `Prop`; the proofs are elsewhere.

- Claim A (Proposition 5.1 of the paper): `ClaimA` (`N_K ≤ BR(E_K)`), and its three parts
  `ClaimAPathwise`, `ClaimAIid`, `ClaimAOrig` (Lemma 5.2 (1), (2), (3) of the paper).
- The coupling order: reflexive where `≤` is a measurable relation, transitive on countable
  types, products, finite and countable products of couplings, monotone images, the restriction
  to the first `J` values, `BR` monotone (Lemma 4.5 of the paper), `Psi` monotone (Lemma 4.4),
  `Phi_J` monotone.
- The induction (Theorem 5.3 of the paper): from Lemma 4.3 in domination form, Claim A and a
  supersolution `Phi_J(H) ≤ H`, every `E_K ≤ H`; then `E X ≤ E B(1)` for `B` of law `H`.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.LemmaX

open FrogModel.Recursion

/-! ## Claim A -/

/-- **Claim A** (Proposition 5.1 of the paper): for every `d ≥ 1`, every kill depth `K` and every
block length `J ≥ 1`, the curve law is below the block renewal of its own first `J` values,
`N_K ≤ BR(E_K)`. -/
def ClaimA : Prop :=
  ∀ (d : ℕ) [NeZero d] (K J : ℕ), 0 < J →
    CouplingLE (curveLaw d K) (brLaw J (blockLaw d K J))

/-- **Claim A (a), pathwise**: for every sequence of block configurations and every `m`, the
curve of the original configuration is below the block renewal curve of the outputs of the
root-refreshed configurations. -/
def ClaimAPathwise : Prop :=
  ∀ (d K J : ℕ) (hJ : 0 < J) (ω : ℕ → BlockSample d J) (m : ℕ),
    curveK K (blockSleep (ω 0)) (origActive J hJ ω) m ≤
      FrogModel.Order.brCurve J (fun b => blockCurve (blockOut K (refreshSeq K J ω b))) m

/-- **Claim A (b), i.i.d. blocks**: the block output has law `E_K`, and the outputs of the
root-refreshed configurations are i.i.d. with law `E_K`. -/
def ClaimAIid : Prop :=
  ∀ (d : ℕ) [NeZero d] (K J : ℕ), 0 < J →
    (blockMeasure d J).map (blockOut K) = blockLaw d K J ∧
    (Measure.infinitePi fun _ : ℕ => blockMeasure d J).map
        (fun ω b => blockOut K (refreshSeq K J ω b)) =
      Measure.infinitePi fun _ : ℕ => blockLaw d K J

/-- **Claim A (c), the original configuration** has the law of the sample of `N_K`. -/
def ClaimAOrig : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : ℕ) (hJ : 0 < J),
    (Measure.infinitePi fun _ : ℕ => blockMeasure d J).map
        (fun ω => (blockSleep (ω 0), origActive J hJ ω)) =
      (frogMeasure d).prod (initMeasure d)

/-! ## The coupling order -/

/-- The coupling order is reflexive on probability laws where `≤` is a measurable relation. -/
def CouplingRefl : Prop :=
  ∀ (α : Type) [MeasurableSpace α] [Preorder α] (P : Measure α) [IsProbabilityMeasure P],
    MeasurableSet {p : α × α | p.1 ≤ p.2} → CouplingLE P P

/-- The coupling order is transitive on a countable type with measurable points (Section 4.2
of the paper: glue the two couplings along the middle marginal). -/
def CouplingTrans : Prop :=
  ∀ (α : Type) [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] [Preorder α]
    (P Q R : Measure α), CouplingLE P Q → CouplingLE Q R → CouplingLE P R

/-- Two couplings give a coupling of the product laws, for the product order. -/
def CouplingProd : Prop :=
  ∀ (α β : Type) [MeasurableSpace α] [MeasurableSpace β] [Preorder α] [Preorder β]
    (P P' : Measure α) (Q Q' : Measure β), CouplingLE P P' → CouplingLE Q Q' →
      CouplingLE (P.prod Q) (P'.prod Q')

/-- Finitely many couplings give a coupling of the product laws, for the pointwise order. -/
def CouplingPi : Prop :=
  ∀ (ι : Type) [Fintype ι] (α : ι → Type) [∀ i, MeasurableSpace (α i)] [∀ i, Preorder (α i)]
    (P Q : ∀ i, Measure (α i)), (∀ i, CouplingLE (P i) (Q i)) →
      CouplingLE (Measure.pi P) (Measure.pi Q)

/-- Countably many couplings give a coupling of the infinite product laws, for the pointwise
order. -/
def CouplingInfinitePi : Prop :=
  ∀ (ι : Type) [Countable ι] (α : ι → Type) [∀ i, MeasurableSpace (α i)] [∀ i, Preorder (α i)]
    (P Q : ∀ i, Measure (α i)), (∀ i, CouplingLE (P i) (Q i)) →
      CouplingLE (Measure.infinitePi P) (Measure.infinitePi Q)

/-- A measurable monotone map preserves the coupling order, where `≤` is a measurable relation on
its target. -/
def CouplingMap : Prop :=
  ∀ (α β : Type) [MeasurableSpace α] [MeasurableSpace β] [Preorder α] [Preorder β] (f : α → β),
    Measurable f → Monotone f → MeasurableSet {p : β × β | p.1 ≤ p.2} →
      ∀ P Q : Measure α, CouplingLE P Q → CouplingLE (P.map f) (Q.map f)

/-- The restriction to the first `J` values preserves the coupling order: `P ≤ Q` on curves
gives `P|_J ≤ Q|_J` on `Fin J → ℕ∞`. -/
def RestrictMono : Prop :=
  ∀ (J : ℕ) (P Q : Measure (ℕ → ℕ∞)), CouplingLE P Q →
    CouplingLE (P.map (firstValues J)) (Q.map (firstValues J))

/-- **Lemma 4.5 of the paper for laws**: `H ≤ H'` on `Fin J → ℕ∞` gives `BR(H) ≤ BR(H')` on
curves. -/
def BrLawMono : Prop :=
  ∀ (J : ℕ) (H H' : Measure (Fin J → ℕ∞)), CouplingLE H H' → CouplingLE (brLaw J H) (brLaw J H')

/-- **Lemma 4.4 of the paper**: `P ≤ Q` on curves gives `Psi(P) ≤ Psi(Q)`. -/
def PsiLawMono : Prop :=
  ∀ (d : ℕ) (P Q : Measure (ℕ → ℕ∞)), CouplingLE P Q → CouplingLE (psiLaw d P) (psiLaw d Q)

/-- `Phi_J` is monotone: `H ≤ H'` gives `Phi_J(H) ≤ Phi_J(H')`. -/
def PhiLawMono : Prop :=
  ∀ (d J : ℕ) (H H' : Measure (Fin J → ℕ∞)), CouplingLE H H' →
    CouplingLE (phiLaw d J H) (phiLaw d J H')

/-! ## The induction -/

/-- **The block laws are below a supersolution** (Theorem 5.3 of the paper). Lemma 4.3 in
domination form (`N_0 ≤ Psi(δ_0)`, `N_(K+1) ≤ Psi(N_K)`), Claim A at `d` and `J`, and
`Phi_J(H) ≤ H` give `E_K ≤ H` for every `K`. -/
def BlockInduction : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : ℕ) (H : Measure (Fin J → ℕ∞)),
    CouplingLE (curveLaw d 0) (psiLaw d (Measure.dirac 0)) →
    (∀ K, CouplingLE (curveLaw d (K + 1)) (psiLaw d (curveLaw d K))) →
    (∀ K, CouplingLE (curveLaw d K) (brLaw J (blockLaw d K J))) →
    CouplingLE (phiLaw d J H) H → ∀ K, CouplingLE (blockLaw d K J) H

/-- **The mean from the block bound** (proof of Theorem 5.3 of the paper, with
Lemma 4.1): if `E_K ≤ H` for every `K`, then `E X ≤ E B(1)` for `B` of law `H` (coordinate `0`
holds `B(1)`). -/
def MeanOfBlockBound : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : ℕ) (hJ : 0 < J) (H : Measure (Fin J → ℕ∞)),
    (∀ K, CouplingLE (blockLaw d K J) H) →
      meanX d ≤ ∫⁻ B, ((B ⟨0, hJ⟩ : ℕ∞) : ℝ≥0∞) ∂H

/-- **Lemma X from a supersolution** (Theorem 5.3 of the paper): the hypotheses of
`BlockInduction` give `E X ≤ E B(1)` for `B` of law `H`. -/
def LemmaXOfSuper : Prop :=
  ∀ (d : ℕ) [NeZero d] (J : ℕ) (hJ : 0 < J) (H : Measure (Fin J → ℕ∞)),
    CouplingLE (curveLaw d 0) (psiLaw d (Measure.dirac 0)) →
    (∀ K, CouplingLE (curveLaw d (K + 1)) (psiLaw d (curveLaw d K))) →
    (∀ K, CouplingLE (curveLaw d K) (brLaw J (blockLaw d K J))) →
    CouplingLE (phiLaw d J H) H → meanX d ≤ ∫⁻ B, ((B ⟨0, hJ⟩ : ℕ∞) : ℝ≥0∞) ∂H

end FrogModel.LemmaX
