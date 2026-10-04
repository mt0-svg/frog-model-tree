module

public import FrogModel.D3.Interfaces.Closure

@[expose] public section

/-!
# The interface of Section 14: Theorem 14.1 and the tail past 10^30 (d = 3)

Section 14 of the paper. The comparison index `J`, the depth `D`, the thresholds `k`, `y` and `k1`
(`J`, `w`, `k`, `k_2` and `k_1` in the paper) are functions of the height `m`; `DCond` collects, at
one height, the ranges the proof reads and the inequalities (K1) and (K2). On `[m1, 10^30]` they are
the finite check of Proposition 15.2; past `10^30` they are Lemma 14.3, stated here as `dprime_tail`.

Clamps. `jackLower` is the lower bound `pi(h, x)` of Section 14 on `P(G_h(1) ≥ x)` given
`E G_h(1) ≥ c0 mu_h(1)`, clamped below at `0` (and `0` for `x ≥ mu_h(1)`); `LJ` clamps the
coefficient `2/3 - J 3^-D` below at `0`, as `Theta_J` does. Both clamps only lower `LJ` and `L1`
where the unclamped values are negative or meaningless, and each clamped value still bounds the
probability it stands for (Lemma 11.5 with a negative coefficient is a bound at least `1`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-- The hand-over height `m1 = round(10^6.25)`. -/
def m1 : ℕ := 1778279

/-- `c0 = 3/5`. -/
noncomputable def c0 : ℝ := 3 / 5

/-- `eps = 1/50`. -/
noncomputable def eps : ℝ := 1 / 50

/-- `b1 = 27290443/50`. -/
noncomputable def b1 : ℝ := 27290443 / 50

/-- The lower bound `pi(h, x)` on `P(G_h(1) ≥ x)` given `E G_h(1) ≥ c0 mu_h(1)` (Lemma 11.1 (1)):
`1 - ((1 - c0) mu_h(1) + mu_h(1)^(1/2)/2)/(mu_h(1) - x)` for `x < mu_h(1)`, clamped at `0`. -/
noncomputable def jackLower (h x : ℕ) : ℝ :=
  if (x : ℝ) < mu h 1 then
    max 0 (1 - ((1 - c0) * mu h 1 + Real.sqrt (mu h 1) / 2) / (mu h 1 - x))
  else 0

/-- `LJ(m) = (1 - (2/3 - J 3^-D) p_D)^(J+1) + P(Bin(y, 3^(1-D)) < k) + P(Bin(k, 1/4) < J)`,
`p_D = jackLower (m + 1 - D) y`: `Theta_J(m)` of Section 14. -/
noncomputable def LJ (m J D k y : ℕ) : ℝ :=
  (1 - max 0 (2 / 3 - (J : ℝ) * (3 : ℝ)⁻¹ ^ D) * jackLower (m + 1 - D) y) ^ (J + 1) +
    binLt y ((3 : ℝ)⁻¹ ^ (D - 1)) k + binLt k (1 / 4) J

/-- `L1(m) = 1 - S(p_1) + P(Bin(k1, 1/4) < J)`, `p_1 = jackLower m k1`: `Theta_1(m)` of Section 14,
with `S` the `chi` of Lemma 11.4. -/
noncomputable def L1 (m J k1 : ℕ) : ℝ :=
  1 - SPoly (jackLower m k1) + binLt k1 (1 / 4) J

/-- The conditions at the height `m`: `J ≥ 1`, `1 ≤ D ≤ m + 1`, `m + 1 - D > m1 - 30`,
`k, y, k1 ≥ 1`, (K1) `((m + J + 1)/3) LJ(m) ≤ eps` and
(K2) `(b1 + (1/3 - eps)(m - m1))(1 - L1(m)) - (J - 2)/3 ≥ c0 (m + 3)/3`. -/
def DCond (J D k y k1 : ℕ → ℕ) (m : ℕ) : Prop :=
  1 ≤ J m ∧ 1 ≤ D m ∧ D m ≤ m + 1 ∧ m1 - 30 < m + 1 - D m ∧ 1 ≤ k m ∧ 1 ≤ y m ∧ 1 ≤ k1 m ∧
    ((m : ℝ) + J m + 1) / 3 * LJ m (J m) (D m) (k m) (y m) ≤ eps ∧
    c0 * ((m : ℝ) + 3) / 3 ≤
      (b1 + (1 / 3 - eps) * ((m : ℝ) - m1)) * (1 - L1 m (J m) (k1 m)) - ((J m : ℝ) - 2) / 3

/-- **Theorem 14.1 of the paper**. With `J(m1) = 62`, `J` nondecreasing from `m1`, the conditions at
every `m ≥ m1`, and the assumptions `E G_h(1) ≥ (3/5) mu_h(1)` for `m1 - 30 < h ≤ m1` and
`E G_m1(62) ≥ b1`; then `E G_m(1) ≥ (3/5) mu_m(1)` for every `m > m1 - 30`. -/
def thmDprime1 : Prop :=
  ∀ (J D k y k1 : ℕ → ℕ) (_hJ62 : J m1 = 62) (_hJmono : MonotoneOn J (Set.Ici m1))
    (_hcond : ∀ m, m1 ≤ m → DCond J D k y k1 m)
    (_hB1 : ∀ h, m1 - 30 < h → h ≤ m1 → c0 * mu h 1 ≤ meanG h 1) (_hB62 : b1 ≤ meanG m1 62),
    ∀ m, m1 - 30 < m → c0 * mu m 1 ≤ meanG m 1

/-- `J(m) = max(140, ceil((11/5) ln m))` past `10^30`. -/
noncomputable def Jtail (m : ℕ) : ℕ := max 140 ⌈(11 / 5 : ℝ) * Real.log m⌉₊

/-- `D(m) = ceil(log_3(100 J(m)))`. -/
noncomputable def Dtail (m : ℕ) : ℕ := Nat.clog 3 (100 * Jtail m)

/-- `y(m) = 18 J(m) 3^(D(m) - 1)`. -/
noncomputable def ytail (m : ℕ) : ℕ := 18 * Jtail m * 3 ^ (Dtail m - 1)

/-- `k(m) = k1(m) = 12 J(m)`. -/
noncomputable def ktail (m : ℕ) : ℕ := 12 * Jtail m

/-- **Lemma 14.3 of the paper**: the conditions at every `m ≥ 10^30`. -/
def dprime_tail : Prop :=
  ∀ m, 10 ^ 30 ≤ m → DCond Jtail Dtail ktail ytail ktail m

end FrogModel.D3.Iface
