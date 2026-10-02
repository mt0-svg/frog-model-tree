module

public import Mathlib

@[expose] public section

/-!
# Lemma X: definitions of the kill depth and of the map `Psi`

Section 4 of the paper.

The map `Psi` as a deterministic map (Section 4.3). A curve is a map `ℕ → ℕ∞`; `G c` is the curve
of the child `c` (`G c i`: the frogs returned to the root by the subtree of `c` when `i` frogs are
active at `c`, its own frog first). `D k : Fin (d + 1)` is the direction of the `k`-th step taken
at the root (`0`: to the parent, `c.succ`: to the child `c`, as `Step d` codes it), counted from
`k = 0`. Then `T_j(n) = j + ∑_c F_c(n_c(n))` with `n_c(n)` the steps to `c` among the first `n`,
`F_c(0) = 0`, `F_c(m) = G_c(m + 1)` for `m ≥ 1`; `N(j)` is the least fixed point of `T_j` in `ℕ∞`
and `G(j)` the number of steps to the parent among the first `N(j)`. Everything is on `ℕ∞`, so
`T_j` is defined at `⊤` and the least fixed point exists for every input; the curves are extended
to `ℕ∞` by `extCurve`, monotone whatever `G`.
-/

open scoped ENNReal

namespace FrogModel.LemmaX

/-- A curve extended to `ℕ∞`: at `m`, the supremum of `G i` over the `i ≤ m` (so `G m` for a
non-decreasing `G` and finite `m`, the supremum of `G` at `⊤`). -/
noncomputable def extCurve (G : ℕ → ℕ∞) (m : ℕ∞) : ℕ∞ :=
  ⨆ (i : ℕ) (_ : (i : ℕ∞) ≤ m), G i

/-- `n_a(n)`: the number of `k < n` with `D k = a`. -/
noncomputable def dirCount {d : ℕ} (D : ℕ → Fin (d + 1)) (a : Fin (d + 1)) (n : ℕ∞) : ℕ∞ :=
  {k : ℕ | (k : ℕ∞) < n ∧ D k = a}.encard

/-- `F_c(m)`: the frogs returned by a child after `m` entries, `0` for `m = 0` and `G_c(m + 1)`
for `m ≥ 1` (the first entry also wakes the child's own frog). -/
noncomputable def childRet (G : ℕ → ℕ∞) (m : ℕ∞) : ℕ∞ :=
  if m = 0 then 0 else extCurve G (m + 1)

/-- `T_j(n)`: the frogs available for the first `n` steps at the root, the `j` initial ones and
the returns from the children. -/
noncomputable def psiT {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ) (n : ℕ∞) :
    ℕ∞ :=
  j + ∑ c : Fin d, childRet (G c) (dirCount D c.succ n)

/-- `N(j)`: the least fixed point of `T_j` (the infimum of its prefixed points). -/
noncomputable def psiN {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ) : ℕ∞ :=
  sInf {n : ℕ∞ | psiT G D j n ≤ n}

/-- `G(j)`: the steps to the parent among the first `N(j)` steps; `Psi` maps the child curves
and the directions to the curve `psiG G D`. -/
noncomputable def psiG {d : ℕ} (G : Fin d → ℕ → ℕ∞) (D : ℕ → Fin (d + 1)) (j : ℕ) : ℕ∞ :=
  dirCount D 0 (psiN G D j)

end FrogModel.LemmaX
