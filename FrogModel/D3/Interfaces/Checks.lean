module

public import FrogModel.D3.Interfaces.Seed
public import FrogModel.D3.Interfaces.DPrime

@[expose] public section

/-!
# The interface of the computations: Propositions 15.1 and 15.2 (d = 3)

Section 15 of the paper. The statements of the computations, proved from stored data checked in the
kernel, with the definitions of Step.lean (Section 12), Seed.lean (Section 13) and DPrime.lean
(Section 14):

- Proposition 15.1, `m1run_certS`: a run at `(V, P, L) = (48, 96, 60)` and height `100` that
  satisfies (i) and (ii) of Proposition 13.3 with its tops `q = 2..33`, and a certificate in the
  sense of Lemma 12.5 (5) from the seed made from its top masses (rounding of the stored seed: any
  state above the exact seed), ending in a state `T` with `Phi^S_[hn, m1 - 1](T) ≤ T`,
  `hn ≤ m1 - 30`, `delta_T(1) ≤ 2/5` and `delta_T(62) ≤ 7045771/88917100`;
- Proposition 15.2, `dcheck1`: the parameters of the 95 intervals from `m1` to `10^30` and the
  conditions of Theorem 14.1 on `[m1, 10^30]`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- The stored run satisfies the hypotheses of Proposition 13.3 at `(V, P, L, m) = (48, 96, 60, 100)`,
with top arrays `Wtil_q ≤ Wtop_q[rho*_99, K*_99]` for `q = 2..33` (Proposition 15.1 (1)). -/
def M1Run.Holds (R : M1Run) : Prop :=
  F3Hyp 48 96 60 100 R ∧ ∀ q, 2 ≤ q → q ≤ 33 → ∀ x ≤ 48, ∀ f ≤ 3,
    R.Wt q x f ≤ Wtop 48 96 (R.rho 99) (R.K 99) q x f

/-- `W_k(x) = sum over the second index of Wtil_(k+1)(x, .)`. -/
noncomputable def topMass (R : M1Run) (k x : ℕ) : ℝ := ∑ f ∈ Finset.range 4, R.Wt (k + 1) x f

/-- The parameters of the seed and of the plain steps from it: `(E, GM, VM, JM) = (32, 96, 16, 12)`. -/
def P0 : StParams := ⟨32, 96, 16, 12⟩

/-- The certificate of Proposition 15.1 (2) from the seed state `S0` at `100`. -/
def CertS1 (S0 : State) : Prop :=
  ∃ (S0' : State) (P : StParams) (hn : ℕ) (Sn T : State),
    S0.Le P0 S0' ∧ S0'.WF P0 ∧ Relation.ReflTransGen CertStep (P0, 100, S0') (P, hn, Sn) ∧
      Sn.Le P T ∧ T.WF P ∧ P.OK ∧ (phiS P hn (m1 - 1) T).Le P T ∧ hn ≤ m1 - 30 ∧ 62 ≤ P.E ∧
      T.delta 1 ≤ 2 / 5 ∧ T.delta 62 ≤ 7045771 / 88917100

/-- **Proposition 15.1 of the paper**. -/
def m1run_certS : Prop :=
  ∃ R : M1Run, R.Holds ∧ CertS1 (seedState 48 100 96 (topMass R))

/-- **Proposition 15.2 of the paper**: the conditions on `[m1, 10^30]`. -/
def dcheck1 : Prop :=
  ∃ J D k y k1 : ℕ → ℕ, J m1 = 62 ∧ MonotoneOn J (Set.Icc m1 (10 ^ 30)) ∧
    J (10 ^ 30) ≤ 140 ∧ ∀ m, m1 ≤ m → m ≤ 10 ^ 30 → DCond J D k y k1 m

end FrogModel.D3.Iface
