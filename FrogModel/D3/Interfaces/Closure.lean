module

public import FrogModel.D3.Interfaces.Model

@[expose] public section

/-!
# The interface of Sections 10 and 11: tails, the closure bounds and the deficit recursion (d = 3)

Lemmas 10.5 to 10.8 and Section 11 of the paper, with consequences of Lemma 10.3. The statements
below are proved, in FrogModel/D3/LaneA and FrogModel/D3/LaneB, from the ones of
FrogModel/D3/Interfaces/Model.lean. The closure at height `m + 1` is the closure of `Model.lean`
whose children are i.i.d. planted curves at height `m` (`closMeasure (curveLaw m)`); with `j ≥ 1`
entrants it has `q = j + 1` initial frogs, so `closE (j + 1) G D 0` is `e_1` of the `j`-closure and
`closN (j + 1) G D` is `N(j)`.

Self-contained (no model): `chernoff_binLt`, `lemma12_general`, `lemma12'_general`.
Applied to the planted curve: `lemma12_G`, `lemma12'_G`, `cdfG_le_binCdf`, `lemma17a`.
Closure: `d1` (Lemma 10.5), `lemma8a`, `lemma8b`, `lemma17b`, `lemmaS2'`, `lemma16A`, `lemma16B`,
`lemma16C` and the composed `lemma16AC`, `lemma16BC`, `lemma9`, `lemma9_two`, `lemma10`.

Probabilities and expectations are real numbers; a Bochner integral of a function that is not
integrable is `0`, which would make Lemmas 10.5, 10.6 and 10.8 harder, never easier, so no junk value
can prove them.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-! ## Binomial tails -/

/-- `P(Bin(n, p) = i)`. -/
noncomputable def binPmf (n : ℕ) (p : ℝ) (i : ℕ) : ℝ :=
  (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)

/-- `P(Bin(n, p) ≤ v)`. -/
noncomputable def binCdf (n : ℕ) (p : ℝ) (v : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (v + 1), binPmf n p i

/-- `P(Bin(n, p) < J)`. -/
noncomputable def binLt (n : ℕ) (p : ℝ) (J : ℕ) : ℝ :=
  ∑ i ∈ Finset.range J, binPmf n p i

/-- `P(Bin(n, p) ≥ E)`. -/
noncomputable def binGe (n : ℕ) (p : ℝ) (E : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc E n, binPmf n p i

/-- The Bernoulli relative entropy `KL(a, p)`. -/
noncomputable def klBern (a p : ℝ) : ℝ :=
  a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p))

/-- Chernoff (Lemma 11.1 (2) of the paper): `P(Bin(n, p) < k) ≤ exp(-n KL(k/n, p))` for
`k/n < p`. -/
def chernoff_binLt : Prop :=
  ∀ (n k : ℕ) (p : ℝ) (_hp0 : 0 < p) (_hp1 : p < 1) (_hk : (k : ℝ) < n * p),
    binLt n p k ≤ Real.exp (-(n * klBern (k / n) p))

/-! ## The two bounds of Lemma 11.1 (1) -/

/-- **Lemma 11.1 (1) of the paper, first bound**. `0 ≤ X ≤ U` pathwise, `U` a sum of independent indicators with mean
`mu`, `Delta = mu - E X`: for `x < mu`, `P(X < x) ≤ (Delta + mu^(1/2)/2)/(mu - x)`. -/
def lemma12_general : Prop :=
  ∀ {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (A : ι → Set Ω) (_hA : ∀ i, MeasurableSet (A i)) (_hind : iIndepSet A μ)
    (X : Ω → ℝ) (_hX : Measurable X) (_hX0 : ∀ ω, 0 ≤ X ω)
    (_hXU : ∀ ω, X ω ≤ ∑ i ∈ s, (A i).indicator 1 ω)
    (mu : ℝ) (_hmu : mu = ∑ i ∈ s, (μ (A i)).toReal) (x : ℝ) (_hx : x < mu),
    (μ {ω | X ω < x}).toReal ≤ (mu - ∫ ω, X ω ∂μ + Real.sqrt mu / 2) / (mu - x)

/-- **Lemma 11.1 (1), second bound**. Same hypotheses, `t ∈ (0, 1)` and `(1 - t) mu > g`:
`P(X ≤ g) ≤ Delta/((1 - t) mu - g) + exp(-t^2 mu/2)`. -/
def lemma12'_general : Prop :=
  ∀ {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (A : ι → Set Ω) (_hA : ∀ i, MeasurableSet (A i)) (_hind : iIndepSet A μ)
    (X : Ω → ℝ) (_hX : Measurable X) (_hX0 : ∀ ω, 0 ≤ X ω)
    (_hXU : ∀ ω, X ω ≤ ∑ i ∈ s, (A i).indicator 1 ω)
    (mu : ℝ) (_hmu : mu = ∑ i ∈ s, (μ (A i)).toReal) (t g : ℝ) (_ht0 : 0 < t) (_ht1 : t < 1)
    (_hg : g < (1 - t) * mu),
    (μ {ω | X ω ≤ g}).toReal ≤
      (mu - ∫ ω, X ω ∂μ) / ((1 - t) * mu - g) + Real.exp (-(t ^ 2 * mu / 2))

/-- The first bound of Lemma 11.1 (1) on `P(X ≤ v) = P(X < v + 1)` from a deficit bound `D`, at mean `mu`;
`1` (no information) when `v + 1 ≥ mu`. -/
noncomputable def lemma12B (D mu : ℝ) (v : ℕ) : ℝ :=
  if (v : ℝ) + 1 < mu then (D + Real.sqrt mu / 2) / (mu - ((v : ℝ) + 1)) else 1

/-- The second bound of Lemma 11.1 (1) on `P(X ≤ v)` at `t`; `1` when `(1 - t) mu ≤ v`. -/
noncomputable def lemma12'B (D mu t : ℝ) (v : ℕ) : ℝ :=
  if (v : ℝ) < (1 - t) * mu then D / ((1 - t) * mu - v) + Real.exp (-(t ^ 2 * mu / 2)) else 1

/-- The first bound for the planted curve, Lemma 11.1 (3) (`X = G_m(k)`, `U = U_m(k)`, `mu = mu_m(k)`), with any
`D ≥ Delta_m(k)`. -/
def lemma12_G : Prop :=
  ∀ (m k v : ℕ) (D : ℝ) (_hD : deficit m k ≤ D),
    cdfG m k v ≤ lemma12B D (mu m k) v

/-- The second bound for the planted curve, Lemma 11.1 (3), with any `D ≥ Delta_m(k)` and `t ∈ (0, 1)`. -/
def lemma12'_G : Prop :=
  ∀ (m k v : ℕ) (D t : ℝ) (_hD : deficit m k ≤ D) (_ht0 : 0 < t) (_ht1 : t < 1),
    cdfG m k v ≤ lemma12'B D (mu m k) t v

/-! ## Consequences of the coins: the binomial bound and Lemma 10.7 (1) -/

/-- Lemma 10.3 of the paper: `G_m(k)` stochastically dominates `Bin(k, 1/3)`. -/
def cdfG_le_binCdf : Prop :=
  ∀ (m k v : ℕ),
    cdfG m k v ≤ binCdf k (1 / 3) v

/-- **Lemma 10.7 (1) of the paper**: `Delta_m(k + 1) ≤ Delta_m(k)`. -/
def lemma17a : Prop :=
  ∀ (m k : ℕ),
    deficit m (k + 1) ≤ deficit m k

/-! ## The closure: Lemmas 10.5, 10.6, 10.7 (2) and 10.8 -/

/-- A probability in the closure at height `m + 1` (children at height `m`). -/
noncomputable def closProb (m : ℕ) (A : Set ClosSample) : ℝ :=
  ((closMeasure (curveLaw m)) A).toReal

/-- `min(e, J)` for `e ∈ ℕ∞`, as a natural number. -/
noncomputable def minE (e : ℕ∞) (J : ℕ) : ℕ := (min e (J : ℕ∞)).toNat

/-- `L_{j,J} = (1/3) ∑_c E[(G_c(J) - J/3) - (G_c(e_c ∧ J) - (e_c ∧ J)/3)]` in the `j`-closure. -/
noncomputable def lossL (m j J : ℕ) : ℝ :=
  (1 / 3) * ∑ c : Fin 3, ∫ x, (((x.1 c J).toNat : ℝ) - J / 3 -
    (((x.1 c (minE (closE (j + 1) x.1 x.2 c) J)).toNat : ℝ) - (minE (closE (j + 1) x.1 x.2 c) J : ℝ) / 3))
      ∂closMeasure (curveLaw m)

/-- **Lemma 10.5 of the paper**: `E G_(m+1)(j) ≥ E G_m(J) + (1 + j - J)/3 - L_{j,J}` for `j ≥ 1`, `J ≥ 0`. -/
def d1 : Prop :=
  ∀ (m j J : ℕ) (_hj : 1 ≤ j),
    meanG m J + (1 + (j : ℝ) - J) / 3 - lossL m j J ≤ meanG (m + 1) j

/-- **Lemma 10.6 of the paper**, first bound: `L_{j,J} ≤ E G_m(J) P(e_1 < J)`. -/
def lemma8a : Prop :=
  ∀ (m j J : ℕ) (_hj : 1 ≤ j),
    lossL m j J ≤ meanG m J * closProb m {x | closE (j + 1) x.1 x.2 0 < J}

/-- **Lemma 10.6**, second bound: `P(e_1 < J) ≤ P(N(j) < k) + P(Bin(k, 1/4) < J)` for every `k ≥ 1`. -/
def lemma8b : Prop :=
  ∀ (m j J k : ℕ) (_hj : 1 ≤ j) (_hk : 1 ≤ k),
    closProb m {x | closE (j + 1) x.1 x.2 0 < J} ≤
      closProb m {x | closN (j + 1) x.1 x.2 < k} + binLt k (1 / 4) J

/-- **Lemma 10.7 (2) of the paper**: for `j ≥ 1`, `J ≥ 0` and `P ≥ P(e_1 < J)` in the `j`-closure at
height `m + 1`, `Delta_(m+1)(j) ≤ Delta_m(J) (1 - P) + mu_m(J) P`. -/
def lemma17b : Prop :=
  ∀ (m j J : ℕ) (_hj : 1 ≤ j) (P : ℝ)
    (_hP : closProb m {x | closE (j + 1) x.1 x.2 0 < J} ≤ P),
    deficit (m + 1) j ≤ deficit m J * (1 - P) + mu m J * P

/-- **Lemma 10.8 of the paper**, in the form used by Lemma 12.1 (1). The children carry extra data
(`Ωc`, for instance their coins; the curve marginal is the planted law at height `m`) and the closure
auxiliary randomness (`Ωa`). For each child `c`, `e' c` reads nothing of the child `c` (it is a
function of `R_c`: the directions, the two other children and the auxiliary randomness) and
`e' c ≤ e_c` pathwise. Then `Delta_(m+1)(j) ≤ (1/3) ∑_c E Delta_m(e'_c)`. -/
def lemmaS2' : Prop :=
  ∀ (m j : ℕ) (_hj : 1 ≤ j) {Ωc Ωa : Type*} [MeasurableSpace Ωc] [MeasurableSpace Ωa]
    (μc : Measure ((ℕ → ℕ∞) × Ωc)) [IsProbabilityMeasure μc] (_hμc : μc.map Prod.fst = curveLaw m)
    (ν : Measure Ωa) [IsProbabilityMeasure ν]
    (e' : Fin 3 → (Fin 3 → (ℕ → ℕ∞) × Ωc) × ((ℕ → Fin 4) × Ωa) → ℕ)
    (_he'meas : ∀ c, Measurable (e' c))
    (_he'R : ∀ c y y', (∀ c', c' ≠ c → y.1 c' = y'.1 c') → y.2 = y'.2 → e' c y = e' c y')
    (_he'le : ∀ c y, (e' c y : ℕ∞) ≤ closE (j + 1) (fun c' => (y.1 c').1) y.2.1 c),
    deficit (m + 1) j ≤
      (1 / 3) * ∑ c : Fin 3, ∫ y, deficit m (e' c y)
        ∂((Measure.pi fun _ : Fin 3 => μc).prod (dirMeasure.prod ν))

/-! ## Lemmas 11.2 and 11.3 (end configurations) -/

/-- `Mult(n; k_up, k_1, k_2, k_3) = n!/(k_up! k_1! k_2! k_3!) 4^-n`. -/
noncomputable def mult4 (n k0 k1 k2 k3 : ℕ) : ℝ :=
  (n.factorial : ℝ) / ((k0.factorial : ℝ) * k1.factorial * k2.factorial * k3.factorial) / 4 ^ n

/-- `W^A_e(s) = Mult(q + s; (q + s - |e|, e)) 1{0 ≤ q + s - |e| ≤ v, q + s < n0}`. -/
noncomputable def WA (q v n0 : ℕ) (e : Fin 3 → ℕ) (s : ℕ) : ℝ :=
  if e 0 + e 1 + e 2 ≤ q + s ∧ q + s - (e 0 + e 1 + e 2) ≤ v ∧ q + s < n0 then
    mult4 (q + s) (q + s - (e 0 + e 1 + e 2)) (e 0) (e 1) (e 2)
  else 0

/-- `W^B_e(s) = Mult(q + s; (q + s - |e|, e)) 1{q + s ≥ |e|, q + s < K}`. -/
noncomputable def WB (q K : ℕ) (e : Fin 3 → ℕ) (s : ℕ) : ℝ :=
  if e 0 + e 1 + e 2 ≤ q + s ∧ q + s < K then
    mult4 (q + s) (q + s - (e 0 + e 1 + e 2)) (e 0) (e 1) (e 2)
  else 0

/-- `P(S_e = s)` for `S_e = ∑_c G_c(e_c)`, the three child curves i.i.d. at height `m`. -/
noncomputable def probSe (m : ℕ) (e : Fin 3 → ℕ) (s : ℕ) : ℝ :=
  ((Measure.pi fun _ : Fin 3 => curveLaw m) {G | ∑ c : Fin 3, G c (e c) = (s : ℕ∞)}).toReal

/-- The nonincreasing envelope `w(s) = max over s ≤ s' ≤ S of W(s')` (`W ≥ 0`). -/
noncomputable def envelope (W : ℕ → ℝ) (S s : ℕ) : ℝ :=
  (Finset.Icc s S).fold max 0 W

/-- The pseudo-law of a cdf bound `F e .` on `0..GM`: the mass at `g ≤ GM` (the rest at `+∞`). -/
noncomputable def plF (F : ℕ → ℕ → ℝ) (GM e g : ℕ) : ℝ :=
  if g ≤ GM then F e g - (if g = 0 then 0 else F e (g - 1)) else 0

/-- `P(Y_1 + Y_2 + Y_3 = s)` for independent `Y_c` of pseudo-laws `F (e c) .` (finite values). -/
noncomputable def convF (F : ℕ → ℕ → ℝ) (GM : ℕ) (e : Fin 3 → ℕ) (s : ℕ) : ℝ :=
  ∑ g1 ∈ Finset.range (GM + 1), ∑ g2 ∈ Finset.range (GM + 1),
    if g1 + g2 ≤ s then plF F GM (e 0) g1 * plF F GM (e 1) g2 * plF F GM (e 2) (s - g1 - g2)
    else 0

/-- **Lemma 11.2 (A) of the paper**, the `j`-closure at height `m + 1`, `q = j + 1`, `E ≥ 1`, `n0 > q`.
The sum over `s` runs over `s < n0`, which holds every `s` with `W^A_e(s) ≠ 0`. -/
def lemma16A : Prop :=
  ∀ (m j v n0 E : ℕ) (_hj : 1 ≤ j) (_hE : 1 ≤ E) (_hn0 : j + 1 < n0),
    cdfG (m + 1) j v ≤
      (∑ e ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range E), ∑ s ∈ Finset.range n0,
          WA (j + 1) v n0 e s * probSe m e s) +
        3 * binGe (E + v) (1 / 2) E * cdfG m E (n0 - (j + 1) - 1) + binCdf n0 (1 / 4) v

/-- **Lemma 11.2 (B)**, `1 ≤ J ≤ E`, `K > q`. -/
def lemma16B : Prop :=
  ∀ (m j J K E : ℕ) (_hj : 1 ≤ j) (_hJ : 1 ≤ J) (_hJE : J ≤ E) (_hK : j + 1 < K),
    closProb m {x | closE (j + 1) x.1 x.2 0 < J} ≤
      (∑ e ∈ Fintype.piFinset (fun c : Fin 3 => if c = 0 then Finset.range J else Finset.range E),
          ∑ s ∈ Finset.range K, WB (j + 1) K e s * probSe m e s) +
        2 * binGe (E + J - 1) (1 / 2) E * cdfG m E (K - (j + 1) - 1) + binLt K (1 / 4) J

/-- **Lemma 11.3 (1) of the paper**, for one `e` with every `e_c ≤ E`: cdf bounds `F e' g ≥ P(G_m(e') ≤ g)` on
`0..GM`, in `[0, 1]` and nondecreasing in `g`, and a weight `W ≥ 0` vanishing beyond `GM`. -/
def lemma16C : Prop :=
  ∀ (m E GM : ℕ) (F : ℕ → ℕ → ℝ) (_hF : ∀ e ≤ E, ∀ g ≤ GM, cdfG m e g ≤ F e g)
    (_hmono : ∀ e ≤ E, ∀ g < GM, F e g ≤ F e (g + 1))
    (_h01 : ∀ e ≤ E, ∀ g ≤ GM, 0 ≤ F e g ∧ F e g ≤ 1)
    (e : Fin 3 → ℕ) (_he : ∀ c, e c ≤ E) (W : ℕ → ℝ) (_hW0 : ∀ s, 0 ≤ W s) (S : ℕ)
    (_hWS : ∀ s, GM < s → W s = 0),
    ∑ s ∈ Finset.range S, W s * probSe m e s ≤
      ∑ s ∈ Finset.range S, envelope W S s * convF F GM e s

/-- The bound (A) of Lemma 11.3 (2) computed from cdf bounds `F` (rows `0..E`, `g ≤ GM`), `q` initial frogs. -/
noncomputable def boundA (F : ℕ → ℕ → ℝ) (E GM q v n0 : ℕ) : ℝ :=
  (∑ e ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range E), ∑ s ∈ Finset.range n0,
      envelope (WA q v n0 e) n0 s * convF F GM e s) +
    3 * binGe (E + v) (1 / 2) E * F E (n0 - q - 1) + binCdf n0 (1 / 4) v

/-- The bound (B) of Lemma 11.3 (2) computed from `F`. -/
noncomputable def boundB (F : ℕ → ℕ → ℝ) (E GM q J K : ℕ) : ℝ :=
  (∑ e ∈ Fintype.piFinset (fun c : Fin 3 => if c = 0 then Finset.range J else Finset.range E),
      ∑ s ∈ Finset.range K, envelope (WB q K e) K s * convF F GM e s) +
    2 * binGe (E + J - 1) (1 / 2) E * F E (K - q - 1) + binLt K (1 / 4) J

/-- Lemma 11.3 (2) for (A): the cdf bound used by the step map. -/
def lemma16AC : Prop :=
  ∀ (m j v n0 E GM : ℕ) (F : ℕ → ℕ → ℝ) (_hj : 1 ≤ j) (_hE : 1 ≤ E)
    (_hn0 : j + 1 < n0) (_hGM : n0 - (j + 1) - 1 ≤ GM)
    (_hF : ∀ e ≤ E, ∀ g ≤ GM, cdfG m e g ≤ F e g) (_hmono : ∀ e ≤ E, ∀ g < GM, F e g ≤ F e (g + 1))
    (_h01 : ∀ e ≤ E, ∀ g ≤ GM, 0 ≤ F e g ∧ F e g ≤ 1),
    cdfG (m + 1) j v ≤ boundA F E GM (j + 1) v n0

/-- Lemma 11.3 (2) for (B): the bound on `P(e_1 < J)` used by the step map. -/
def lemma16BC : Prop :=
  ∀ (m j J K E GM : ℕ) (F : ℕ → ℕ → ℝ) (_hj : 1 ≤ j) (_hJ : 1 ≤ J) (_hJE : J ≤ E)
    (_hK : j + 1 < K) (_hGM : K - (j + 1) - 1 ≤ GM)
    (_hF : ∀ e ≤ E, ∀ g ≤ GM, cdfG m e g ≤ F e g) (_hmono : ∀ e ≤ E, ∀ g < GM, F e g ≤ F e (g + 1))
    (_h01 : ∀ e ≤ E, ∀ g ≤ GM, 0 ≤ F e g ∧ F e g ≤ 1),
    closProb m {x | closE (j + 1) x.1 x.2 0 < J} ≤ boundB F E GM (j + 1) J K

/-! ## Lemmas 11.4 and 11.5 (fresh trials) -/

/-- `E[∏ over the children c with a_c ≥ 1 of (1 - p)]`, `(a_up, a_1, a_2, a_3)` multinomial
`(q; 1/4)`: the bound of Lemma 11.4. -/
noncomputable def lemma9Bound (q : ℕ) (p : ℝ) : ℝ :=
  ∑ a ∈ (Fintype.piFinset fun _ : Fin 4 => Finset.range (q + 1)).filter (fun a => ∑ i, a i = q),
    mult4 q (a 0) (a 1) (a 2) (a 3) *
      (1 - p) ^ (Finset.univ.filter fun c : Fin 3 => 1 ≤ a c.succ).card

/-- `S(p) = 15/16 - (9/16)(1 - p) - (3/8)(1 - p)^2`. -/
noncomputable def SPoly (p : ℝ) : ℝ := 15 / 16 - 9 / 16 * (1 - p) - 3 / 8 * (1 - p) ^ 2

/-- **Lemma 11.4 of the paper**: `w` at height `m + 1` with `q ≥ 2` initial frogs, `x ≥ 1`,
`p = P(G_m(1) ≥ x)`: `P(N(q - 1) < x) ≤ E[∏_{c : a_c ≥ 1} (1 - p)]`. -/
def lemma9 : Prop :=
  ∀ (m q x : ℕ) (_hq : 2 ≤ q) (_hx : 1 ≤ x),
    closProb m {y | closN q y.1 y.2 < x} ≤ lemma9Bound q (tailG m 1 x)

/-- **Lemma 11.4** at `q = 2`: `P(N(1) < x) ≤ 1 - S(p)`. -/
def lemma9_two : Prop :=
  ∀ (m x : ℕ) (_hx : 1 ≤ x),
    closProb m {y | closN 2 y.1 y.2 < x} ≤ 1 - SPoly (tailG m 1 x)

/-- **Lemma 11.5 of the paper** (deep fresh trials): `w` at height `m + 1` with `q ≥ 2` initial frogs,
`1 ≤ D ≤ m + 1`, `x, y ≥ 1`, `p_D = P(G_(m+1-D)(1) ≥ y)`:
`P(N(q - 1) < x) ≤ (1 - (2/3 - (q - 1) 3^-D) p_D)^q + P(Bin(y, 3^(1-D)) < x)`. -/
def lemma10 : Prop :=
  ∀ (m q D x y : ℕ) (_hq : 2 ≤ q) (_hD1 : 1 ≤ D) (_hDm : D ≤ m + 1) (_hx : 1 ≤ x)
    (_hy : 1 ≤ y),
    closProb m {z | closN q z.1 z.2 < x} ≤
      (1 - (2 / 3 - ((q : ℝ) - 1) * (3 : ℝ)⁻¹ ^ D) * tailG (m + 1 - D) 1 y) ^ q +
        binLt y ((3 : ℝ)⁻¹ ^ (D - 1)) x

end FrogModel.D3.Iface
