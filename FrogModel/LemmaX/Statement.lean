module

public import FrogModel.LemmaX.Defs
public import FrogModel.LemmaX.KillDefs

@[expose] public section

/-!
# Lemma X: frozen statements on the kill depth and on `Psi`

Each statement is a `Prop`, proved in LemmaX/Main.lean as `<name>_holds`. The kill depth and
Lemma 4.1 of the paper (definitions in LemmaX/KillDefs.lean). The map `Psi` of Section 4.3 of the
paper as a deterministic map, Lemma 4.2 (definitions in LemmaX/Defs.lean).
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.LemmaX

/-- **`Psi`, least fixed point.** `N(j)` is a fixed point of `T_j` and lies below every fixed
point of `T_j` (Lemma 4.2 (1) of the paper). -/
def PsiLeastFixed : Prop :=
  ∀ (d : ℕ) (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ),
    psiT G D j (psiN G D j) = psiN G D j ∧ ∀ n : ℕ∞, psiT G D j n = n → psiN G D j ≤ n

/-- **`Psi`, iterates.** `N(j)` is the limit of the iterates of `T_j` from `0` (Lemma 4.2 (1) of
the paper). -/
def PsiIterate : Prop :=
  ∀ (d : ℕ) (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ),
    psiN G D j = ⨆ t : ℕ, (psiT G D j)^[t] 0

/-- **`Psi`, a step needs a frog.** For `k < N(j)`, `k < T_j(k)`: when `k` steps are taken at
the root, a frog is there for the next one (Lemma 4.2 (2) of the paper). -/
def PsiStep : Prop :=
  ∀ (d : ℕ) (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j k : ℕ),
    (k : ℕ∞) < psiN G D j → (k : ℕ∞) < psiT G D j k

/-- **`Psi`, curves and nesting.** `G(0) = 0` and `G` is non-decreasing in `j` (Lemma 4.2 (3) of
the paper). -/
def PsiCurve : Prop :=
  ∀ (d : ℕ) (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)), psiG G D 0 = 0 ∧ Monotone (psiG G D)

/-- **`Psi`, monotonicity.** Larger child curves, with the same directions, give larger `N(j)`
and `G(j)`, for every `j` (Lemma 4.2 (4) of the paper). -/
def PsiMono : Prop :=
  ∀ (d : ℕ) (G G' : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)), (∀ c i, G c i ≤ G' c i) →
    ∀ j : ℕ, psiN G D j ≤ psiN G' D j ∧ psiG G D j ≤ psiG G' D j

/-- **`Psi`, kill depth `0`.** With zero child curves, `N(j) = j` (Lemma 4.2 (5) of the paper). -/
def PsiZero : Prop :=
  ∀ (d : ℕ) (D : ℕ → Fin (d + 1)) (j : ℕ), psiN (fun _ _ => 0 : Fin d → ℕ → ℕ∞) D j = j

/-- **`Psi`, measurability.** `Psi` is a measurable map of the child curves and the directions
(product σ-algebras, `ℕ∞` with all its subsets). -/
def MeasurablePsiG : Prop :=
  ∀ d : ℕ, Measurable fun x : (Fin d → ℕ → ℕ∞) × (ℕ → Fin (d + 1)) => psiG x.1 x.2

/-- **Kill depth, measurability.** `X^(K)` is measurable in the sample, and the curve in the sample
and the paths of the active frogs. -/
def MeasurableKill : Prop :=
  ∀ d K : ℕ, Measurable (frozenCountK (d := d) K) ∧
    Measurable fun p : Sample d × (ℕ → ℕ → Step d) => curveK K p.1 p.2

/-- **Kill depth, nesting.** `G_K(0) = 0` and `G_K` is non-decreasing in `m`. -/
def CurveNested : Prop :=
  ∀ (d K : ℕ) (ζ : Sample d) (ξ : ℕ → ℕ → Step d), curveK K ζ ξ 0 = 0 ∧ Monotone (curveK K ζ ξ)

/-- **Kill depth, the first value.** `X^(K)` is the first value of the curve whose active frog
follows the path of the frog at `r`. -/
def CurveFirst : Prop :=
  ∀ (d K : ℕ) (ζ : Sample d), frozenCountK K ζ = (curveK K ζ (fun _ => ζ []) 1 : ℝ≥0∞)

/-- **Lemma 4.1 (truncation), pathwise.** `X^(K)` is non-decreasing in `K` with supremum `X`. -/
def Truncation : Prop :=
  ∀ (d : ℕ) (ζ : Sample d), Monotone (fun K => frozenCountK K ζ) ∧
    ⨆ K, frozenCountK K ζ = frozenCount ζ

/-- **Lemma 4.1 (truncation), in mean.** `E X = sup_K E X^(K)`. -/
def MeanTruncation : Prop :=
  ∀ (d : ℕ) [NeZero d], meanX d = ⨆ K, ∫⁻ ζ, frozenCountK K ζ ∂frogMeasure d

/-- **Kill depth, what the curve reads.** `G_K(m)` reads neither the sleeping frog at `r` nor the
active frogs `ξ a`, `a ≥ m`. -/
def CurveCongr : Prop :=
  ∀ (d K m : ℕ) (ζ ζ' : Sample d) (ξ ξ' : ℕ → ℕ → Step d), (∀ v, v ≠ [] → ζ v = ζ' v) →
    (∀ a < m, ξ a = ξ' a) → curveK K ζ ξ m = curveK K ζ' ξ' m

end FrogModel.LemmaX
