module

public import FrogModel.D3.M1L.Bridge

@[expose] public section

/-!
# M1_L at height 0: the chain on the directions and its law

A closure at height 0 (Section 13 of the paper), on the stream. At `p.m = 0` the top closure is a
closure at height 0: every entry into a child is a ghost entry, so the run only reads directions
and its state projects to `(n, u, d)`, the pool size, the number of ups and the depth of the ghost
walk below the root (`0`: no ghost). `hstep` is that projected chain; `capBin` and `U0` are the law
of its outcome (`min (u + Bin(n, q_L), V)`, mixed over the return of the ghost; the laws `Rhat_0`
and `Khat_0` of Section 13 are the cases `n = 2` and `n = 1` with `u = 0`).
-/

open MeasureTheory ProbabilityTheory

namespace FrogModel.D3

/-- The law of a direction: uniform on `Fin 4`. -/
noncomputable def dirLaw : Measure (Fin 4) := uniformOn Set.univ

/-- The return probability of a ghost walk at depth `L`: `p_L = (3^(L-1) - 1)/(3^L - 1)`. -/
noncomputable def pL (L : ℕ) : ℝ := ((3 : ℝ) ^ (L - 1) - 1) / ((3 : ℝ) ^ L - 1)

/-- A frog at height `0` goes up before it is lost with probability `q_L = 1/(4 - 3 p_L)`. -/
noncomputable def qL (L : ℕ) : ℝ := 1 / (4 - 3 * pL L)

/-- The return probability of a ghost walk from depth `d`: `(3^(L-d) - 1)/(3^L - 1)`. -/
noncomputable def rL (L d : ℕ) : ℝ := ((3 : ℝ) ^ (L - d) - 1) / ((3 : ℝ) ^ L - 1)

/-- The law of `min (a + Bin(p, x), V)` at `b`. -/
noncomputable def capBin (V : ℕ) (x : ℝ) (p a b : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (p + 1),
    if min (a + j) V = b then (p.choose j : ℝ) * x ^ j * (1 - x) ^ (p - j) else 0

/-- The closure at height 0 on the directions read: `(n, u, d)` is the pool size, the number of
ups and the depth of the ghost walk (`0`: none). A round reads one direction: `0` sends the frog
up (an up, capped at `V`), the others start a ghost walk at depth `1`. A ghost step moves the depth
by `-1` on `0` and `+1` otherwise; at depth `0` the frog is back in the pool, at depth `L` it is
lost. The states `(0, u, 0)` are the end, with `u` ups. -/
def hstep (V L : ℕ) : ℕ × ℕ × ℕ → Fin 4 → ℕ × ℕ × ℕ
  | (n, u, 0), a =>
    if n = 0 then (0, u, 0)
    else if a = 0 then (n - 1, if u < V then u + 1 else u, 0) else (n - 1, u, 1)
  | (n, u, d + 1), a =>
    if (if a = 0 then d else d + 2) = 0 then (n + 1, u, 0)
    else if (if a = 0 then d else d + 2) = L then (n, u, 0)
    else (n, u, if a = 0 then d else d + 2)

/-- The probability that the closure at height 0 ends with `b` ups, from a state, as a real: the
capped binomial, mixed over the return of the ghost frog. -/
noncomputable def U0 (V L : ℕ) (b : ℕ) : ℕ × ℕ × ℕ → ℝ
  | (n, u, 0) => capBin V (qL L) n u b
  | (n, u, d + 1) =>
    rL L (d + 1) * capBin V (qL L) (n + 1) u b + (1 - rL L (d + 1)) * capBin V (qL L) n u b

/-- A bound on the expected number of reads before the end, from a state with `d < L`. -/
def T0 (L : ℕ) : ℕ × ℕ × ℕ → ℕ
  | (n, _, 0) => 2 * L * n
  | (n, _, d + 1) => 2 * L * n + 2 * (L - (d + 1))

/-- The state of the run of M1_L at `p.m = 0`, projected: pool size, ups, ghost depth. -/
def proj0 (s : St) : ℕ × ℕ × ℕ :=
  match s.stack with
  | [] => (0, s.out.length, 0)
  | f :: _ => (f.pool.length, f.ups.length, match f.ghost with | none => 0 | some (_, u) => u.length)

/-- The shape of the states of the run at `p.m = 0`: ended, or one frame at the root, not waiting
for a kill coin, with its ghost strictly below the root. -/
def Shape0 (s : St) : Prop :=
  s.stack = [] ∨ ∃ f, s.stack = [f] ∧ f.v = [] ∧ f.killing = false ∧
    ∀ φ u, f.ghost = some (φ, u) → u ≠ []

end FrogModel.D3
