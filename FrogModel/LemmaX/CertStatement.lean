module

public import FrogModel.LemmaX.LawDefs
public import FrogModel.Cert.Cheap

@[expose] public section

/-!
# Lemma X at `d = 4`: the certificate law and the interface of Theorem 6.5 of the paper

Sections 6 and 7 of the paper. The certificate law of a table `D` (FrogModel.Cert.Defs) is

`H* = (1 - eps) P_tab + eps sum_(n ≥ 0) (1 - rho) rho^n delta_(Z_(T + 1 + n))`, `Z_t = (t, ..., t)`,

with `P_tab` the law of the block of a path of the table from `root`. A block is stored as in
`firstValues`: coordinate `i` holds `B(i + 1)`. `Hstar` is the law of the certificate `cand`
(FrogModel.Cert.Cheap, `J = 4`).

Lemma X reduces to `PhiSuper`, `Phi_4(H*) ≤ H*` in the coupling order (with `CurveLawZero 4` and
`CurveLawSucc 4`), and `MeanHstar`, `E B*(1) = c`. The last step of the proof of Theorem 6.5 of
the paper (`Lemma62`) derives `PhiSuper` from three facts on a dominating output `Out_dom = L + D`:

- `DomSplit` (Lemmas 6.1, 6.2 and 6.4 and the proof of Theorem 6.5 of the paper):
  `Phi_4(H*) ≤ Out_dom`, `Out_dom` a probability law carried by the non-decreasing blocks, `L`
  carried by `F_T = {B | B(4) ≤ T}`, and `D(B(4) ≥ t) ≤ theta^-t S_ov` for every `t ≥ T + 1`;
- `StopWeight` ((I3b), condition (C6) of the paper): `S_ov ≤ eps theta^(T + 1)`;
- `PlanI4` ((I4), condition (C7) of the paper): a measure on pairs `x ≤ y` with first marginal at
  most `L` and second marginal the finite part `(1 - eps) P_tab` of `H*`.

The measure `L` delivered by the checker is `latMeasure Latoms` for a list `Latoms` of atoms
`(x, m)`: `x = (B(1), ..., B(4))` a cumulative block and `m` its mass in units of `2^-40`.

The rational data enter `ℝ≥0∞` through `ENNReal.ofReal` of their real casts; every one of them is
nonnegative for `cand` ((I0), (I1)).
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Cert

/-- The block of a path of the table: coordinate `i` holds `B(i + 1) = δ_1 + ... + δ_(i+1)`. -/
def pathBlock (J : ℕ) (π : List Tr) : Fin J → ℕ∞ :=
  fun i => (((π.take ((i : ℕ) + 1)).map Tr.δ).sum : ℕ)

namespace Data

variable (D : Data)

/-- `P_tab`: the law of the block of a path of the table from `root`, a path `π` with probability
`pathProb π`. -/
noncomputable def tabLaw : Measure (Fin D.J → ℕ∞) :=
  ((D.paths D.J 0 0).map fun π =>
    ENNReal.ofReal (pathProb π : ℝ) • Measure.dirac (pathBlock D.J π)).sum

/-- The tail law `sum_(n ≥ 0) (1 - rho) rho^n delta_(Z_(T + 1 + n))`. -/
noncomputable def tailLaw : Measure (Fin D.J → ℕ∞) :=
  Measure.sum fun n : ℕ => ENNReal.ofReal (((1 - D.rho) * D.rho ^ n : ℚ) : ℝ) •
    Measure.dirac fun _ => ((D.T + 1 + n : ℕ) : ℕ∞)

/-- The certificate law `H* = (1 - eps) P_tab + eps (tail law)`. -/
noncomputable def hstar : Measure (Fin D.J → ℕ∞) :=
  ENNReal.ofReal ((1 - D.eps : ℚ) : ℝ) • D.tabLaw + ENNReal.ofReal ((D.eps : ℚ) : ℝ) • D.tailLaw

end Data

end FrogModel.Cert

namespace FrogModel.LemmaX

open FrogModel.Cert

/-- The certificate law `H*` of `cand` (`J = 4`). -/
noncomputable def Hstar : Measure (Fin 4 → ℕ∞) := cand.hstar

/-- The finite part `(1 - eps) P_tab` of `H*`. -/
noncomputable def hstarFin : Measure (Fin 4 → ℕ∞) :=
  ENNReal.ofReal ((1 - cand.eps : ℚ) : ℝ) • cand.tabLaw

/-- `theta = 5 phi - 4 kappa` of `cand`, in `ℝ≥0∞`. -/
noncomputable def thetaC : ℝ≥0∞ := ENNReal.ofReal ((cand.theta : ℚ) : ℝ)

/-- `eps` of `cand`, in `ℝ≥0∞`. -/
noncomputable def epsC : ℝ≥0∞ := ENNReal.ofReal ((cand.eps : ℚ) : ℝ)

/-- **`Phi_J(H*) ≤ H*`** (Theorem 6.5 of the paper) at `d = J = 4`, in the coupling order. -/
def PhiSuper : Prop := CouplingLE (phiLaw 4 4 Hstar) Hstar

/-- **`E B*(1) = c`** (Section 6.1 and Proposition 7.1 of the paper), with
`c = 9337230319347/17448304640000` (`cand_c`). -/
def MeanHstar : Prop :=
  ∫⁻ B, ((B 0 : ℕ∞) : ℝ≥0∞) ∂Hstar = ENNReal.ofReal (9337230319347 / 17448304640000)

/-- **Lemma X at `d = 4`**: `E X ≤ c`. -/
def LemmaXFour : Prop := meanX 4 ≤ ENNReal.ofReal (9337230319347 / 17448304640000)

/-- **The output of the dominating chain** (proof of Theorem 6.5 of the paper, with
Lemmas 6.1, 6.2 and 6.4): `Phi_4(H*) ≤ Out_dom`, `Out_dom = L + D` a probability law, `L` carried
by `F_T`, and the tail of `D` beyond any `t ≥ T + 1` at most `theta^-t S_ov` (the Markov
inequality after Lemma 6.3 of the paper). -/
structure DomSplit (Odom L Dres : Measure (Fin 4 → ℕ∞)) (Sov : ℝ≥0∞) : Prop where
  le_dom : CouplingLE (phiLaw 4 4 Hstar) Odom
  split : Odom = L + Dres
  prob : IsProbabilityMeasure Odom
  mono : ∀ᵐ B ∂Odom, Monotone B
  supp : L {B | ((cand.T : ℕ) : ℕ∞) < B 3} = 0
  tail : ∀ t : ℕ, cand.T + 1 ≤ t → Dres {B | (t : ℕ∞) ≤ B 3} ≤ thetaC⁻¹ ^ t * Sov

/-- A block `(B(1), B(2), B(3), B(4))` of naturals as a point of `Fin 4 → ℕ∞`. -/
def toBlock4 (x : ℕ × ℕ × ℕ × ℕ) : Fin 4 → ℕ∞ :=
  ![(x.1 : ℕ∞), (x.2.1 : ℕ∞), (x.2.2.1 : ℕ∞), (x.2.2.2 : ℕ∞)]

/-- The measure of a list of atoms `(x, m)`, the atom `x` with mass `m 2^-40`. -/
noncomputable def latMeasure (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) : Measure (Fin 4 → ℕ∞) :=
  (A.map fun a => ((a.2 : ℝ≥0∞) / 2 ^ 40) • Measure.dirac (toBlock4 a.1)).sum

/-- **(I3b)**: `S_ov ≤ eps theta^(T + 1)`. -/
def StopWeight (Sov : ℝ≥0∞) : Prop := Sov ≤ epsC * thetaC ^ (cand.T + 1)

/-- **(I4)**, transport form: a measure on pairs `x ≤ y`, first marginal at most `L`, second
marginal the finite part of `H*`. -/
def PlanI4 (L : Measure (Fin 4 → ℕ∞)) : Prop :=
  ∃ π : Measure ((Fin 4 → ℕ∞) × (Fin 4 → ℕ∞)), π.map Prod.fst ≤ L ∧
    π.map Prod.snd = hstarFin ∧ ∀ᵐ p ∂π, p.1 ≤ p.2

/-- **The last step of Theorem 6.5 of the paper**: a dominating output split as in `DomSplit`,
with (I3b) and (I4), gives `Phi_4(H*) ≤ H*`. -/
def Lemma62 : Prop :=
  ∀ (Odom L Dres : Measure (Fin 4 → ℕ∞)) (Sov : ℝ≥0∞), DomSplit Odom L Dres Sov →
    StopWeight Sov → PlanI4 L → PhiSuper

end FrogModel.LemmaX
