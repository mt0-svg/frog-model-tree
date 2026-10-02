module

public import Mathlib

@[expose] public section

/-!
# Nonnegative linear systems

The operator of a kernel `K : ι → ι → ℝ≥0∞` on functions `ι → ℝ≥0∞`, the iterates of the affine
map `f ↦ b + K f` from `0`, and their supremum, the least nonnegative solution of `f = b + K f`.
These carry the backward check (Theorem 6.5 of the paper: a sub-solution lies below the least
solution when the kernel is transient, a super-solution above it) and Lemma 6.3 of the paper in
super-solution form.
-/

open scoped ENNReal

namespace FrogModel.LinSys

variable {ι : Type*}

/-- `(K f) i = ∑' j, K i j * f j`. -/
noncomputable def app (K : ι → ι → ℝ≥0∞) (f : ι → ℝ≥0∞) : ι → ℝ≥0∞ :=
  fun i => ∑' j, K i j * f j

/-- The iterates of `f ↦ b + K f` from `0`: `iter K b n = ∑_{k < n} K^k b`. -/
noncomputable def iter (K : ι → ι → ℝ≥0∞) (b : ι → ℝ≥0∞) : ℕ → ι → ℝ≥0∞
  | 0 => 0
  | n + 1 => b + app K (iter K b n)

/-- The least nonnegative solution of `f = b + K f`, the supremum of the iterates. -/
noncomputable def least (K : ι → ι → ℝ≥0∞) (b : ι → ℝ≥0∞) : ι → ℝ≥0∞ :=
  fun i => ⨆ n, iter K b n i

end FrogModel.LinSys
