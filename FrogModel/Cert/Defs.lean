module

public import Mathlib

@[expose] public section

/-!
# The data of a certificate and its cheap conditions

The rational data of a certificate (Section 6.1 of the paper, code/certificate/FORMAT.md version 3),
their ranges and the conditions (I1), (I2) and (I5), stated exactly as Theorem 6.5 of the paper
consumes them, and the paths of the table, through which FrogModel.Cert.Sound relates them to the
laws of Section 6.1.
Labels are numbered per level; `root` and `end` are label `0` of levels `0` and `J`.
FrogModel.Cert.Cheap proves the conditions for the certificate of Section 7 of the paper.
-/

namespace FrogModel.Cert

/-- A transition `tr q s δ s' p` of a table: from label `s` of level `q`, with probability `p`,
the increment `B(q + 1) - B(q)` is `δ` and the next label is `s'` of level `q + 1`. -/
structure Tr where
  q : ℕ
  s : ℕ
  δ : ℕ
  s' : ℕ
  p : ℚ

/-- The data of a certificate: `J`, `T`, `eps`, `rho`, `phi`, `kappa`, the number of labels of each
level `0, ..., J`, and the table. (`T'`, the round cap and the threshold enter only (I3), (I4).) -/
structure Data where
  J : ℕ
  T : ℕ
  eps : ℚ
  rho : ℚ
  phi : ℚ
  kappa : ℚ
  labels : List ℕ
  table : List Tr

namespace Data

variable (D : Data)

/-- The number of labels of level `q`. -/
def nLabels (q : ℕ) : ℕ := D.labels.getD q 0

/-- The transitions of label `s` of level `q`. -/
def row (q s : ℕ) : List Tr := D.table.filter fun t => t.q = q ∧ t.s = s

/-- The ranges of the data in Section 6.1: `J ≥ 2`, `T ≥ 1`, `eps` and `rho` in `(0, 1)`,
`phi > 1` (`kappa ≥ 1` is part of (I2)). -/
def I0 : Prop :=
  2 ≤ D.J ∧ 1 ≤ D.T ∧ 0 < D.eps ∧ D.eps < 1 ∧ 0 < D.rho ∧ D.rho < 1 ∧ 1 < D.phi

/-- (I1): the table is well formed (one label at levels `0` and `J`, every transition from a label
of a level `q < J` to a label of level `q + 1`), every `p > 0`, and the `p` of every row sum to 1. -/
def I1 : Prop :=
  D.labels.length = D.J + 1 ∧ D.nLabels 0 = 1 ∧ D.nLabels D.J = 1 ∧
    (∀ t ∈ D.table, t.q < D.J ∧ t.s < D.nLabels t.q ∧ t.s' < D.nLabels (t.q + 1) ∧ 0 < t.p) ∧
    ∀ q < D.J, ∀ s < D.nLabels q, ((D.row q s).map Tr.p).sum = 1

/-- The values `r_q(s)` over the labels `s` of level `q = J - n`: `r_J(end) = 1` and
`r_q(s) = sum over the transitions (p, δ, s') of s of p phi^δ r_(q+1)(s')`. -/
def rLevel : ℕ → List ℚ
  | 0 => [1]
  | n + 1 =>
    (List.range (D.nLabels (D.J - (n + 1)))).map fun s =>
      ((D.row (D.J - (n + 1)) s).map fun t => t.p * D.phi ^ t.δ * (rLevel n).getD t.s' 0).sum

/-- `r_q(s)`, for `q ≤ J`. -/
def r (q s : ℕ) : ℚ := (D.rLevel (D.J - q)).getD s 0

/-- `M = (1 - eps) r_0(root) + eps (1 - rho) phi^(T+1) / (1 - phi rho)`. -/
def M : ℚ := (1 - D.eps) * D.r 0 0 + D.eps * (1 - D.rho) * D.phi ^ (D.T + 1) / (1 - D.phi * D.rho)

/-- `theta = 5 phi - 4 kappa`. -/
def theta : ℚ := 5 * D.phi - 4 * D.kappa

/-- (I2): `phi rho < 1`, `kappa ≥ 1`, `kappa^J ≥ M`, `theta > 1`, `theta rho ≥ 1`. -/
def I2 : Prop :=
  D.phi * D.rho < 1 ∧ 1 ≤ D.kappa ∧ D.M ≤ D.kappa ^ D.J ∧ 1 < D.theta ∧ 1 ≤ D.theta * D.rho

/-- `E_tab B(1)`: the sum over the transitions `root → s_1` of `p_1 δ_1`. -/
def EB1 : ℚ := ((D.row 0 0).map fun t => t.p * (t.δ : ℚ)).sum

/-- `c = (1 - eps) E_tab B(1) + eps (T + 1 + rho / (1 - rho))`. -/
def c : ℚ := (1 - D.eps) * D.EB1 + D.eps * (D.T + 1 + D.rho / (1 - D.rho))

/-- (I5): `c < 1`. -/
def I5 : Prop := D.c < 1

instance : Decidable D.I0 := by unfold I0; infer_instance
instance : Decidable D.I1 := by unfold I1; infer_instance
instance : Decidable D.I2 := by unfold I2; infer_instance
instance : Decidable D.I5 := by unfold I5; infer_instance

end Data

/-- The probability of a path of the table: the product of its `p`. -/
def pathProb (π : List Tr) : ℚ := (π.map Tr.p).prod

/-- The total increment of a path, `B(J) - B(q)` for a path from level `q` to `end`. -/
def pathInc (π : List Tr) : ℕ := (π.map Tr.δ).sum

/-- The first increment of a path, `B(1)` for a path from `root`. -/
def firstInc (π : List Tr) : ℕ := (π.head?.map Tr.δ).getD 0

namespace Data

variable (D : Data)

/-- The paths of the table of `n` transitions from label `s` of level `q`. For `q + n = J`, the
paths to `end`; from `root` (`n = J`, `q = s = 0`) they carry the law `P_tab` of Section 6.1. -/
def paths : ℕ → ℕ → ℕ → List (List Tr)
  | 0, _, _ => [[]]
  | n + 1, q, s => (D.row q s).flatMap fun t => (paths n (q + 1) t.s').map (t :: ·)

end Data

end FrogModel.Cert
