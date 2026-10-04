module

public import FrogModel.D3.Interfaces.Closure
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# The interface of Section 12: states, the step map `Phi^S`, the lower closures and Lemma 12.5 (d = 3)

Section 12 of the paper. A state is a pair of real tables; `phiS P a b S` is `Phi^S_[a, b](S)`, the
map `Phi_[a, b]` of Definition 12.3 (children heights in `[a, b]`, parents at `m + 1`), computed in
the order of that definition: the deficits `j = 1..E`, then the cdf rows `j = 1..E`, each row the
minimum over `v' ≥ v` of its terms (the term `G`). `ext` is the extension of Definition 12.4, with
its terms: deficits `1`, `T = mu_h(0)/mu_h(k)` and `P = delta^(k - 1)`, cdf entries `C`, `L`,
`t<i>` and `J` on every row. Each is a valid bound at the extension's height, and a smaller `ext`
only makes `CertStep` easier to meet.

FrogModel/D3/LaneC proves `lemmaS2`, `lemmaS3` (Lemma 12.1, the laws of the lower closures),
`lemma18_1`, `lemma18_3` and `ext_valid` (Lemma 12.5 (1) to (3)). `valid_mono`, Lemma 12.5 (4) and
Lemma 12.5 (5) are proved here from them (`lemma18_4_of`, `lemma18_6_of` take them as hypotheses).
Each of these statements is a `Prop` definition, proved under a name of its own.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FrogModel.D3.Iface

/-! ## States and validity (Definition 12.2) -/

/-- The parameters of a state: `E` entries tracked, `GM` the cdf range, `VM` the cut of (A),
`JM` the largest comparison index. -/
structure StParams where
  E : ℕ
  GM : ℕ
  VM : ℕ
  JM : ℕ

/-- `E ≥ 1`, `JM ≤ E`, `VM ≤ GM`. -/
def StParams.OK (P : StParams) : Prop := 1 ≤ P.E ∧ P.JM ≤ P.E ∧ P.VM ≤ P.GM

/-- A state: cdf bounds `F k g` and normalized deficit bounds `delta k`. Only `k ≤ E` and
`g ≤ GM` are read. -/
structure State where
  F : ℕ → ℕ → ℝ
  delta : ℕ → ℝ

/-- The shape of a state (Definition 12.2): `F` in `[0, 1]` and nondecreasing in `g`, `delta` in `[0, 1]`,
`F(0, .) = 1` and `delta(0) = 1`. -/
def State.WF (P : StParams) (S : State) : Prop :=
  (∀ k ≤ P.E, ∀ g ≤ P.GM, 0 ≤ S.F k g ∧ S.F k g ≤ 1) ∧
    (∀ k ≤ P.E, ∀ g < P.GM, S.F k g ≤ S.F k (g + 1)) ∧
    (∀ k ≤ P.E, 0 ≤ S.delta k ∧ S.delta k ≤ 1) ∧ (∀ g ≤ P.GM, S.F 0 g = 1) ∧ S.delta 0 = 1

/-- Componentwise order on the tables read at `P`. -/
def State.Le (P : StParams) (S S' : State) : Prop :=
  (∀ k ≤ P.E, ∀ g ≤ P.GM, S.F k g ≤ S'.F k g) ∧ ∀ k ≤ P.E, S.delta k ≤ S'.delta k

/-- `S` is valid at height `m`: `P(G_m(k) ≤ g) ≤ F(k, g)` and `Delta_m(k) ≤ delta(k) mu_m(k)`. -/
def Valid (P : StParams) (m : ℕ) (S : State) : Prop :=
  (∀ k ≤ P.E, ∀ g ≤ P.GM, cdfG m k g ≤ S.F k g) ∧ ∀ k ≤ P.E, deficit m k ≤ S.delta k * mu m k

/-- Validity is preserved by raising the state. -/
theorem valid_mono {P : StParams} {m : ℕ} {S S' : State} (h : Valid P m S) (hle : S.Le P S') :
    Valid P m S' := by
  refine ⟨fun k hk g hg => (h.1 k hk g hg).trans (hle.1 k hk g hg), fun k hk => ?_⟩
  have hmu : 0 ≤ mu m k := by unfold mu; positivity
  exact (h.2 k hk).trans (mul_le_mul_of_nonneg_right (hle.2 k hk) hmu)

/-! ## The lower closures (Lemma 12.1) -/

/-- `F~(g)`: the row `F(1, .)` on `0..GM`, `1` beyond. -/
noncomputable def Ftil (F1 : ℕ → ℝ) (GM g : ℕ) : ℝ := if g ≤ GM then F1 g else 1

/-- The pseudo-law of `R`: `P(R = r) = F~(r) - F~(r - 1)` for `r ≤ GM + 1`. -/
noncomputable def plR (F1 : ℕ → ℝ) (GM r : ℕ) : ℝ :=
  if r = 0 then Ftil F1 GM 0 else if r ≤ GM + 1 then Ftil F1 GM r - Ftil F1 GM (r - 1) else 0

/-- The law `A` on `0..cap` shifted by one, `cap` absorbing. -/
noncomputable def capShift (cap : ℕ) (A : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else if k < cap then A (k - 1) else if k = cap then A (cap - 1) + A cap else 0

/-- One stage of the lower closure (Section 12): `A_f(y)` from `A_(f+1)` (`next`), with the count
probability `pc`, the gone probability `pg` and the new-child probability `pn` of the jump chain,
`R` the pseudo-law of the frogs a new child returns (on `0..Rmax`), the count capped at `cap`.
`A_f(0) = delta_0`, `A_f(y + 1) = pc shift(A_f(y)) + pg A_f(y) + pn sum_r P(R = r) A_(f+1)(y + r)`. -/
noncomputable def stageLaw (cap : ℕ) (pc pg pn : ℝ) (R : ℕ → ℝ) (Rmax : ℕ) (next : ℕ → ℕ → ℝ) :
    ℕ → ℕ → ℝ
  | 0 => fun k => if k = 0 then 1 else 0
  | y + 1 => fun k =>
    pc * capShift cap (stageLaw cap pc pg pn R Rmax next y) k +
      pg * stageLaw cap pc pg pn R Rmax next y k +
      pn * ∑ r ∈ Finset.range (Rmax + 1), R r * next (y + r) k

/-- The law of `min(e''_c, E)` in the lower closure of Lemma 12.1 (1) with `q` initial frogs
(`a^(2)_q` of the paper): stages `f = 0, 1, 2` with (count, gone, new) = `(1/4, 1/4, 1/2)`,
`(3/11, 5/11, 3/11)`, `(3/10, 7/10, 0)`. -/
noncomputable def lawS2 (GM E : ℕ) (F1 : ℕ → ℝ) (q : ℕ) : ℕ → ℝ :=
  let R := plR F1 GM
  let s2 := stageLaw E (3 / 10) (7 / 10) 0 R (GM + 1) fun _ _ => 0
  let s1 := stageLaw E (3 / 11) (5 / 11) (3 / 11) R (GM + 1) s2
  stageLaw E (1 / 4) (1 / 4) (1 / 2) R (GM + 1) s1 q

/-- The law of `min(X'', GM + 1)` in the lower closure of Lemma 12.1 (2) with `q` initial frogs
(`a^(3)_q` of the paper): stages `f = 0..3` with (count, gone, new) = `(1/4, 0, 3/4)`,
`(3/11, 2/11, 6/11)`, `(3/10, 4/10, 3/10)`, `(1/3, 2/3, 0)`. -/
noncomputable def lawS3 (GM : ℕ) (F1 : ℕ → ℝ) (q : ℕ) : ℕ → ℝ :=
  let R := plR F1 GM
  let t3 := stageLaw (GM + 1) (1 / 3) (2 / 3) 0 R (GM + 1) fun _ _ => 0
  let t2 := stageLaw (GM + 1) (3 / 10) (4 / 10) (3 / 10) R (GM + 1) t3
  let t1 := stageLaw (GM + 1) (3 / 11) (2 / 11) (6 / 11) R (GM + 1) t2
  stageLaw (GM + 1) (1 / 4) 0 (3 / 4) R (GM + 1) t1 q

/-- `P(X'' ≤ v)` in the lower closure of Lemma 12.1 (2). -/
noncomputable def cdfS3 (GM : ℕ) (F1 : ℕ → ℝ) (q v : ℕ) : ℝ :=
  ∑ x ∈ Finset.range (v + 1), lawS3 GM F1 q x

/-- **Lemma 12.1 (1) of the paper**, with Lemmas 10.8 and 10.7 (1): for `j ≥ 1`, a row `F1 ≥ P(G_m(1) ≤ .)` on
`0..GM` in `[0, 1]` and nondecreasing, and `D k ≥ Delta_m(k)` for `k ≤ E`:
`Delta_(m+1)(j) ≤ sum_k P(min(e''_c, E) = k) min_(k' ≤ k) D(k')`. -/
def lemmaS2 : Prop :=
  ∀ (m j E GM : ℕ) (_hj : 1 ≤ j) (_hE : 1 ≤ E) (F1 : ℕ → ℝ)
    (_hF1 : ∀ g ≤ GM, cdfG m 1 g ≤ F1 g) (_hmono : ∀ g < GM, F1 g ≤ F1 (g + 1))
    (_h01 : ∀ g ≤ GM, 0 ≤ F1 g ∧ F1 g ≤ 1) (D : ℕ → ℝ) (_hD : ∀ k ≤ E, deficit m k ≤ D k),
    deficit (m + 1) j ≤
      ∑ k ∈ Finset.range (E + 1),
        lawS2 GM E F1 (j + 1) k * (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one D

/-- **Lemma 12.1 (2) of the paper**: `P(G_(m+1)(j) ≤ v) ≤ P(X''_j ≤ v)` for `v ≤ GM`, same row `F1`. -/
def lemmaS3 : Prop :=
  ∀ (m j GM v : ℕ) (_hj : 1 ≤ j) (_hv : v ≤ GM) (F1 : ℕ → ℝ)
    (_hF1 : ∀ g ≤ GM, cdfG m 1 g ≤ F1 g) (_hmono : ∀ g < GM, F1 g ≤ F1 (g + 1))
    (_h01 : ∀ g ≤ GM, 0 ≤ F1 g ∧ F1 g ≤ 1),
    cdfG (m + 1) j v ≤ cdfS3 GM F1 (j + 1) v

/-! ## The step map (Definition 12.3) -/

/-- The offsets of the grids of `n0` and `K`. -/
def gridOffsets : Finset ℕ := {8, 16, 24, 32, 48, 64, 96, 128, 192, 256}

/-- The grid `q + offsets`, capped at `q + GM + 1`, which is added. -/
def grid (GM q : ℕ) : Finset ℕ :=
  insert (q + GM + 1) (gridOffsets.image fun o => min (q + o) (q + GM + 1))

theorem grid_nonempty (GM q : ℕ) : (grid GM q).Nonempty := Finset.insert_nonempty _ _

/-- `P_B(j, J)`: the minimum over the `K` grid of the bound `B_F(j, J, K)` of Lemma 11.3 (2),
`q = j + 1` (`gamma_B(j, J)` of the paper). -/
noncomputable def PB (P : StParams) (S : State) (j J : ℕ) : ℝ :=
  (grid P.GM (j + 1)).inf' (grid_nonempty _ _) fun K => boundB S.F P.E P.GM (j + 1) J K

/-- The minimum over the `n0` grid of the bound `A_F(j, v, n0)` of Lemma 11.3 (2), `q = j + 1`. -/
noncomputable def PA (P : StParams) (S : State) (j v : ℕ) : ℝ :=
  (grid P.GM (j + 1)).inf' (grid_nonempty _ _) fun n0 => boundA S.F P.E P.GM (j + 1) v n0

/-- `r(k', j) = max over h in {a, b} of mu_h(k')/mu_(h+1)(j)`. -/
noncomputable def ratio (a b k' j : ℕ) : ℝ :=
  max (mu a k' / mu (a + 1) j) (mu b k' / mu (b + 1) j)

/-- `Dt_j(k) = min over k' ≤ k of delta(k') r(k', j)`. -/
noncomputable def Dt (S : State) (a b j k : ℕ) : ℝ :=
  (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one fun k' => S.delta k' * ratio a b k' j

/-- The terms `T`, `L` (for `1 ≤ J ≤ JM`) and `S2` of `delta'(j)`. -/
noncomputable def dTerms (P : StParams) (S : State) (a b j : ℕ) : ℝ :=
  min ((Finset.Icc 1 P.JM).fold min (ratio a b 0 j) fun J =>
      (S.delta J * (1 - PB P S j J) + PB P S j J) * ratio a b J j)
    (∑ k ∈ Finset.range (P.E + 1), lawS2 P.GM P.E (S.F 1) (j + 1) k * Dt S a b j k)

/-- `delta'(j)`: `T`, `L`, `S2`, and `P` (`delta'(j - 1)`) for `j ≥ 2`. -/
noncomputable def deltaNew (P : StParams) (S : State) (a b : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => dTerms P S a b 1
  | j + 2 => min (dTerms P S a b (j + 2)) (deltaNew P S a b (j + 1))

/-- The term `L` (the second bound of Lemma 11.1 (3)) and the terms `t<i>` (its third bound,
`t = i/200`, `i = 1..199`). -/
noncomputable def L12 (D mu : ℝ) (v : ℕ) : ℝ :=
  min (lemma12B D mu v) ((Finset.Icc (1 : ℕ) 199).fold min 1 fun i : ℕ => lemma12'B D mu ((i : ℝ) / 200) v)

/-- The terms `C`, `L`, `t<i>`, `A<n0>` (for `v ≤ VM`), `S3` and `J` (`prev = F'(j - 1, v)`) of
`F'(j, v)`; the terms of Lemma 11.1 (3) with `D = delta'(j) mu_(a+1)(j)` at `mu = mu_(a+1)(j)`. -/
noncomputable def preF (P : StParams) (S : State) (a b j v : ℕ) (prev : ℝ) : ℝ :=
  min (min (binCdf j (1 / 3) v) (L12 (deltaNew P S a b j * mu (a + 1) j) (mu (a + 1) j) v))
    (min (if v ≤ P.VM then PA P S j v else 1) (min (cdfS3 P.GM (S.F 1) (j + 1) v) prev))

/-- `F'(j, .)`: row `0` is `1`; row `j` is the minimum over `v' ≥ v` (`v' ≤ GM`) of its terms
(the term `G`). -/
noncomputable def Fnew (P : StParams) (S : State) (a b : ℕ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 1
  | j + 1 => fun v => (Finset.Icc v P.GM).fold min (preF P S a b (j + 1) v (Fnew P S a b j v))
      fun v' => preF P S a b (j + 1) v' (Fnew P S a b j v')

/-- `Phi^S_[a, b](S)`, the map `Phi_[a, b]` of Definition 12.3. `Phi^S_m = phiS P m m`. -/
noncomputable def phiS (P : StParams) (a b : ℕ) (S : State) : State :=
  ⟨Fnew P S a b, deltaNew P S a b⟩

/-! ## The extension (Definition 12.4) -/

/-- The deficits of the extension at height `h` from `P0` to `P`: copied for `k ≤ E0`,
`delta(E0) mu_h(E0)/mu_h(k)` beyond (`X`), with the terms `1`, `T` and `P`. -/
noncomputable def deltaExt (P0 : StParams) (h : ℕ) (S : State) : ℕ → ℝ
  | 0 => 1
  | k + 1 => min (min 1 (mu h 0 / mu h (k + 1)))
      (min (deltaExt P0 h S k)
        (if k + 1 ≤ P0.E then S.delta (k + 1) else S.delta P0.E * mu h P0.E / mu h (k + 1)))

/-- The terms of the extension's cdf entry `(k, g)`: copied (`k ≤ E0`, `g ≤ G0`), `C`, `L`, `t<i>`
at height `h` with `delta^(k)`, and `J` (`prev = F^(k - 1, g)`). -/
noncomputable def preExt (P0 : StParams) (h : ℕ) (S : State) (k g : ℕ) (prev : ℝ) : ℝ :=
  min (min (if k ≤ P0.E ∧ g ≤ P0.GM then S.F k g else 1) (binCdf k (1 / 3) g))
    (min (L12 (deltaExt P0 h S k * mu h k) (mu h k) g) prev)

/-- The extension's cdf rows, each the minimum over `g' ≥ g` (`g' ≤ GM`) of its terms. -/
noncomputable def FExt (P0 P : StParams) (h : ℕ) (S : State) : ℕ → ℕ → ℝ
  | 0 => fun _ => 1
  | k + 1 => fun g => (Finset.Icc g P.GM).fold min (preExt P0 h S (k + 1) g (FExt P0 P h S k g))
      fun g' => preExt P0 h S (k + 1) g' (FExt P0 P h S k g')

/-- `ext_h(S)` of Definition 12.4 from `(E0, G0) = (P0.E, P0.GM)` to `(E, GM) = (P.E, P.GM)`. -/
noncomputable def ext (P0 P : StParams) (h : ℕ) (S : State) : State :=
  ⟨FExt P0 P h S, deltaExt P0 h S⟩

/-! ## Lemma 12.5 -/

/-- **Lemma 12.5 (1) of the paper** (one step): a valid state at `m` gives a valid `Phi^S_m(S)` at `m + 1`. -/
def lemma18_1 : Prop :=
  ∀ (P : StParams) (m : ℕ) (S : State) (_hP : P.OK) (_hW : S.WF P)
    (_hS : Valid P m S),
    Valid P (m + 1) (phiS P m m S)

/-- **Lemma 12.5 (2)** (worst case): `Phi^S_m(S) ≤ Phi^S_[a, b](S)` for `m ∈ [a, b]`. -/
def lemma18_3 : Prop :=
  ∀ (P : StParams) (a b m : ℕ) (S : State) (_hP : P.OK) (_hW : S.WF P)
    (_ham : a ≤ m) (_hmb : m ≤ b),
    (phiS P m m S).Le P (phiS P a b S)

/-- **Lemma 12.5 (3)** (extension): `ext_h(S)` is valid at `h` if `S` is. -/
def ext_valid : Prop :=
  ∀ (P0 P : StParams) (h : ℕ) (S : State) (_hE : P0.E ≤ P.E) (_hG : P0.GM ≤ P.GM)
    (_hS : Valid P0 h S),
    Valid P h (ext P0 P h S)

/-- **Lemma 12.5 (4)** (interval), from (1) and (2): if `S` is valid at `a` and
`Phi^S_[a, b - 1](S) ≤ S`, then `S` is valid at every height of `[a, b]`. -/
theorem lemma18_4_of (h1 : lemma18_1) (h3 : lemma18_3)
    (P : StParams) (a b : ℕ) (S : State) (hP : P.OK) (hW : S.WF P) (hS : Valid P a S)
    (hfix : (phiS P a (b - 1) S).Le P S) : ∀ m, a ≤ m → m ≤ b → Valid P m S := by
  intro m ham hmb
  induction m, ham using Nat.le_induction with
  | base => exact hS
  | succ m ham ih =>
    have hv := h1 P m S hP hW (ih (by omega))
    have hle := h3 P a (b - 1) m S hP hW ham (by omega)
    refine valid_mono hv ⟨fun k hk g hg => (hle.1 k hk g hg).trans (hfix.1 k hk g hg),
      fun k hk => (hle.2 k hk).trans (hfix.2 k hk)⟩

/-- One link of a certificate (Lemma 12.5 (5)): a plain step `S' ≥ Phi^S_h(S)` to `h + 1`, or an
extension `S' ≥ ext_h(S)` at `h`, each with a well-formed `S'` at its own parameters. -/
inductive CertStep : StParams × ℕ × State → StParams × ℕ × State → Prop
  | plain (P : StParams) (h : ℕ) (S S' : State) (hP : P.OK) (hW : S'.WF P)
      (hle : (phiS P h h S).Le P S') : CertStep (P, h, S) (P, h + 1, S')
  | ext (P0 P : StParams) (h : ℕ) (S S' : State) (hE : P0.E ≤ P.E) (hG : P0.GM ≤ P.GM)
      (hW : S'.WF P) (hle : (ext P0 P h S).Le P S') : CertStep (P0, h, S) (P, h, S')

/-- **Lemma 12.5 (5)** (certificate), from (1), (2) and (3). -/
theorem lemma18_6_of (h1 : lemma18_1) (h3 : lemma18_3)
    (hx : ext_valid)
    (P0 : StParams) (h0 : ℕ) (S0 : State) (hS0 : Valid P0 h0 S0) (hW0 : S0.WF P0)
    (P : StParams) (hn : ℕ) (Sn : State)
    (hc : Relation.ReflTransGen CertStep (P0, h0, S0) (P, hn, Sn))
    (T : State) (hT : Sn.Le P T) (hWT : T.WF P) (hP : P.OK) (b : ℕ)
    (hfix : (phiS P hn (b - 1) T).Le P T) : ∀ m, hn ≤ m → m ≤ b → Valid P m T := by
  have key : ∀ x y, Relation.ReflTransGen CertStep x y →
      Valid x.1 x.2.1 x.2.2 → x.2.2.WF x.1 → Valid y.1 y.2.1 y.2.2 ∧ y.2.2.WF y.1 := by
    intro x y hxy
    induction hxy with
    | refl => exact fun hv hw => ⟨hv, hw⟩
    | tail _ hst ih =>
      intro hv hw
      obtain ⟨hv', hw'⟩ := ih hv hw
      cases hst with
      | plain P h S S' hP hW hle => exact ⟨valid_mono (h1 P h S hP hw' hv') hle, hW⟩
      | ext P0 P h S S' hE hG hW hle => exact ⟨valid_mono (hx P0 P h S hE hG hv') hle, hW⟩
  obtain ⟨hvn, _⟩ := key _ _ hc hS0 hW0
  exact lemma18_4_of h1 h3 P hn b T hP hWT (valid_mono hvn hT) hfix

end FrogModel.D3.Iface
