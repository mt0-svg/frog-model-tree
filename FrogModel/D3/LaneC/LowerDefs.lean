module

public import FrogModel.D3.Interfaces.Step

@[expose] public section

/-!
# The lower closures as explicit processes (definitions)

Lower closures for the proof of Lemma 12.1 of the paper. A child of a lower closure answers its
entries by a lower curve: `dead` (it returns nothing), `fresh` (its first entry returns `R`, each
later entry a coin), or `coin` (each entry returns a coin). A fresh child becomes a coin child once
entered. The lower closure is the closure of FrogModel/D3/Interfaces/Model.lean (`closN`, `countAt`)
with these curves.

The randomness of a lower closure: the directions at `w`, a first answer `R s` for each child, and
a coin sequence `ζ s` for each child (the coin `ζ s i` answers the entry `i + 2` of a fresh child,
the entry `i + 1` of a coin child). Under `lowMeasure ρ` the directions are uniform, the `R s` of
law `ρ`, the coins true with probability `1/3`, all independent. `lawV ρ b cap q τ k` is the
probability that the count of the direction `b` at the end, capped at `cap`, is `k`, from `q`
frogs at `w` and children of types `τ`.
-/

open MeasureTheory ProbabilityTheory FrogModel.D3.Iface
open scoped ENNReal

namespace FrogModel.D3.LaneC.Lower

/-- The type of a child of a lower closure. -/
inductive Ty
  | dead
  | fresh
  | coin
  deriving DecidableEq

instance : Fintype Ty :=
  ⟨{.dead, .fresh, .coin}, fun t => by cases t <;> simp⟩

/-- The lower curve of a child of type `t` with first answer `R` and coins `ζ`. -/
def lcurve : Ty → ℕ → (ℕ → Bool) → ℕ → ℕ∞
  | .dead, _, _ => fun _ => 0
  | .fresh, R, ζ => fun k =>
      if k = 0 then 0 else ((R + ∑ i ∈ Finset.range (k - 1), (ζ i).toNat : ℕ) : ℕ∞)
  | .coin, _, ζ => fun k => ((∑ i ∈ Finset.range k, (ζ i).toNat : ℕ) : ℕ∞)

/-- A sample of a lower closure: the directions, the first answers and the coins of the children. -/
abbrev LSample := (ℕ → Fin 4) × ((Fin 3 → ℕ) × (Fin 3 → ℕ → Bool))

/-- The three child curves of a lower closure with types `τ`. -/
def curves (τ : Fin 3 → Ty) (ω : LSample) : Fin 3 → ℕ → ℕ∞ :=
  fun s => lcurve (τ s) (ω.2.1 s) (ω.2.2 s)

/-- The count of the direction `b` at the end of the lower closure with `q` frogs at `w`. -/
noncomputable def cnt (b : Fin 4) (q : ℕ) (τ : Fin 3 → Ty) (ω : LSample) : ℕ∞ :=
  countAt ω.1 b (closN q (curves τ ω) ω.1)

/-- The directions after the first one. -/
def shiftD (ω : LSample) : LSample := (fun i => ω.1 (i + 1), ω.2)

/-- The state after a first step in the direction `a` (the directions of `ω` already shifted):
the number of frogs at `w`, the types and the randomness still to be read. -/
def stepA (a : Fin 4) (q : ℕ) (τ : Fin 3 → Ty) (ω : LSample) :
    ℕ × (Fin 3 → Ty) × LSample :=
  Fin.cases (motive := fun _ => ℕ × (Fin 3 → Ty) × LSample) (q - 1, τ, ω)
    (fun s => match τ s with
      | .dead => (q - 1, τ, ω)
      | .fresh => (q - 1 + ω.2.1 s, Function.update τ s .coin, ω)
      | .coin => (q - 1 + (ω.2.2 s 0).toNat, τ,
          (ω.1, ω.2.1, Function.update ω.2.2 s fun i => ω.2.2 s (i + 1))))
    a

/-- The coin law: `true` with probability `1/3`. -/
noncomputable def coinLaw : Measure Bool :=
  (3⁻¹ : ℝ≥0∞) • Measure.dirac true + (1 - 3⁻¹ : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure coinLaw := by
  constructor
  have h3 : (3⁻¹ : ℝ≥0∞) ≤ 1 := ENNReal.inv_le_one.2 (by norm_num)
  simp [coinLaw, add_tsub_cancel_of_le h3]

/-- An i.i.d. sequence of coins. -/
noncomputable def coinSeq : Measure (ℕ → Bool) := Measure.infinitePi fun _ : ℕ => coinLaw

instance : IsProbabilityMeasure coinSeq := by unfold coinSeq; infer_instance

/-- The law of a lower closure's randomness, the first answers of law `ρ`. -/
noncomputable def lowMeasure (ρ : Measure ℕ) [IsProbabilityMeasure ρ] : Measure LSample :=
  dirMeasure.prod ((Measure.pi fun _ : Fin 3 => ρ).prod (Measure.pi fun _ : Fin 3 => coinSeq))

instance (ρ : Measure ℕ) [IsProbabilityMeasure ρ] : IsProbabilityMeasure (lowMeasure ρ) := by
  unfold lowMeasure; infer_instance

/-- `P(min(count of b, cap) = k)` in the lower closure with `q` frogs at `w` and types `τ`. -/
noncomputable def lawV (ρ : Measure ℕ) [IsProbabilityMeasure ρ] (b : Fin 4) (cap q : ℕ)
    (τ : Fin 3 → Ty) (k : ℕ) : ℝ :=
  (lowMeasure ρ {ω | minE (cnt b q τ ω) cap = k}).toReal

/-- `∑_(k ≤ cap) A k φ k`: the mean of `φ` under a law on `0..cap`. -/
noncomputable def Vs (cap : ℕ) (A : ℕ → ℝ) (φ : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (cap + 1), A k * φ k

end FrogModel.D3.LaneC.Lower
