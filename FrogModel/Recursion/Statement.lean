module

public import FrogModel.LemmaX.Statement

@[expose] public section

/-!
# Frozen statement: the exact recursion of Lemma 4.3 of the paper

The response curve at kill depth `K` is `curveK K ζ ξ` (LemmaX/KillDefs.lean): initial frogs
`ξ 0, ξ 1, ...` at the root `r` of `T*`, sleeping frogs `ζ v` at the other vertices, every frog
killed at its first step to depth `K + 1`. The map `Psi` is `psiG` (LemmaX/Defs.lean).

- `initMeasure d`: the initial frogs, i.i.d. step sequences of law `stepLaw d`.
- `curveLaw d K`: `N_K`, the law of the curve `curveK K` under `frogMeasure d ⊗ initMeasure d`.
- `dirMeasure d`: the directions at `r`, i.i.d. uniform on `Fin (d + 1)`.
- `psiLaw d P`: `Psi(P)`, the law of `psiG G D` for `G_1, ..., G_d` i.i.d. with law `P` and
  independent directions `D` of law `dirMeasure d`.
- `CurveLawZero d`: `N_0 = Psi(δ_0)`, `δ_0` the law of the zero curve.
- `CurveLawSucc d`: `N_(K+1) = Psi(N_K)` for every `K`.

`Measure.map` of a map that is not a.e.-measurable is a junk value (a Dirac mass at an arbitrary
point, the same for both sides here), so these equalities carry content together with the
measurability of `curveK` and `psiG`: `FrogModel.LemmaX.MeasurableKill` and
`FrogModel.LemmaX.MeasurablePsiG` (LemmaX/Statement.lean).
-/

open MeasureTheory ProbabilityTheory FrogModel.LemmaX

namespace FrogModel.Recursion

/-- The law of the initial frogs at `r`: i.i.d. step sequences. -/
noncomputable def initMeasure (d : ℕ) [NeZero d] : Measure (ℕ → ℕ → Step d) :=
  Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stepLaw d

/-- `N_K`: the law of the response curve of `T*` at kill depth `K`. -/
noncomputable def curveLaw (d : ℕ) [NeZero d] (K : ℕ) : Measure (ℕ → ℕ∞) :=
  ((frogMeasure d).prod (initMeasure d)).map fun p => curveK K p.1 p.2

/-- The law of the directions at `r`: i.i.d. uniform on `Fin (d + 1)` (`0` to the parent,
`c.succ` to the child `c`). -/
noncomputable def dirMeasure (d : ℕ) : Measure (ℕ → Fin (d + 1)) :=
  Measure.infinitePi fun _ : ℕ => (uniformOn Set.univ : Measure (Fin (d + 1)))

/-- `Psi(P)`: the law of `psiG G D`, `G_1, ..., G_d` i.i.d. with law `P`, `D` independent with
law `dirMeasure d`. -/
noncomputable def psiLaw (d : ℕ) (P : Measure (ℕ → ℕ∞)) : Measure (ℕ → ℕ∞) :=
  ((Measure.pi fun _ : Fin d => P).prod (dirMeasure d)).map fun x => psiG x.1 x.2

/-- **Lemma 4.3 of the paper at kill depth 0.** `N_0 = Psi(δ_0)`. -/
def CurveLawZero (d : ℕ) [NeZero d] : Prop :=
  curveLaw d 0 = psiLaw d (Measure.dirac 0)

/-- **Lemma 4.3 of the paper (exact recursion).** `N_(K+1) = Psi(N_K)` for every `K`. -/
def CurveLawSucc (d : ℕ) [NeZero d] : Prop :=
  ∀ K : ℕ, curveLaw d (K + 1) = psiLaw d (curveLaw d K)

end FrogModel.Recursion
