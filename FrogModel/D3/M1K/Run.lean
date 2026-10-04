module

public import FrogModel.D3.M1K.Sound
public import FrogModel.D3.M1Data.All
public import FrogModel.D3.M1Data.CTop

@[expose] public section

/-!
# The stored M1 run satisfies `M1Run.Holds`

The stored run (code/m1run, `(V, P, L, m) = (48, 96, 60, 100)`, tops `q = 2..33`) as an `M1Run`,
`storedRun`, and its two results: `storedRun_holds`, the hypotheses of Proposition 13.3 of the paper
and the top bound, and `topMass_eq_massPk`, its top masses read in `massPk`. The data modules
`FrogModel.D3.M1Data.*` and their kernel checks are written by code/m1gen/gen.sh and checked against
its modules.sha256.
-/

open FrogModel.D3.Iface FrogModel.D3.M1Data

namespace FrogModel.D3.M1K

/-- The stored run: `rho*_h`, `K*_h` of the stored heights `h < 100` and the rows `Wtil_q`, `q = 2..33`,
lanes over `2^62`. -/
noncomputable def storedRun : M1Run := runOf stAt wtil

/-- **Proposition 15.1 (1) of the paper**: the stored run satisfies the hypotheses of Proposition 13.3
at `(48, 96, 60, 100)` and `Wtil_q ≤ Wtop_q[rho*_99, K*_99]` for `q = 2..33`. -/
theorem storedRun_holds : storedRun.Holds :=
  runOf_holds stAt wtil valid_all check0_0 step_all top

/-- The top masses of the stored run: `topMass storedRun k x = 2^-62` times slot `49 (k - 1) + x` (64 bits)
of `FrogModel.D3.M1Data.massPk`. -/
theorem topMass_eq_massPk : ∀ k, 1 ≤ k → k ≤ 32 → ∀ x ≤ 48, topMass storedRun k x =
    ((massPk >>> (64 * (49 * (k - 1) + x))) % 2 ^ 64 : ℕ) / 2 ^ 62 :=
  topMass_runOf stAt wtil massPk mass mass_ok

end FrogModel.D3.M1K
