module

public import FrogModel.LemmaX.KillDefs
public import FrogModel.Lemmas.Defs

@[expose] public section

/-!
# Claim A: the root-refreshed process (Section 5 of the paper)

A block configuration gives a step sequence to every vertex label and to every initial label
`0, ..., J - 1`. The root-refreshed configurations `ζ_1, ζ_2, ...` (numbered from `0` here)
refresh, before each block, the labels woken during the previous block (`Stage.refresh`). The
original configuration keeps the vertex paths of block `0` and the initial paths of every block.
-/

open MeasureTheory

namespace FrogModel.LemmaX

variable {d : ℕ}

/-- A block configuration: a step sequence for every vertex label and every initial label. -/
abbrev BlockSample (d J : ℕ) := Vertex d ⊕ Fin J → ℕ → Step d

/-- The law of a block configuration: all steps independent with law `stepLaw d`. -/
noncomputable def blockMeasure (d : ℕ) [NeZero d] (J : ℕ) : Measure (BlockSample d J) :=
  Measure.infinitePi fun _ => Measure.infinitePi fun _ : ℕ => stepLaw d

/-- The sleeping frogs of a block configuration. -/
def blockSleep {J : ℕ} (ω : BlockSample d J) : Sample d := fun v => ω (.inl v)

/-- The initial frogs of a block configuration. The labels `a ≥ J` are never read by the curve
up to `J` (`curveK_congr`); they get the label of `r`, which is never read either. -/
def blockActive {J : ℕ} (ω : BlockSample d J) : ℕ → ℕ → Step d :=
  fun a => if h : a < J then ω (.inr ⟨a, h⟩) else ω (.inl [])

/-- The block output `B(ω) = (G(1), ..., G(J))` at kill depth `K`. -/
noncomputable def blockOut (K : ℕ) {J : ℕ} (ω : BlockSample d J) : Fin J → ℕ∞ :=
  fun s => curveK K (blockSleep ω) (blockActive ω) ((s : ℕ) + 1)

/-- The block woken set `Kset(ω)`: every initial label and the vertex labels reached by the
`J` initial frogs. -/
def blockWoken (K : ℕ) {J : ℕ} (ω : BlockSample d J) : Set (Vertex d ⊕ Fin J) :=
  Set.range Sum.inr ∪ Sum.inl '' {v | reachedK K (blockSleep ω) (blockActive ω) J v}

/-- The root-refreshed configurations: `ζ_0 = ω 0`, and `ζ_(b+1)` is `ζ_b` with the labels of
`Kset(ζ_b)` replaced by those of `ω (b + 1)`. -/
noncomputable def refreshSeq (K J : ℕ) (ω : ℕ → BlockSample d J) : ℕ → BlockSample d J
  | 0 => ω 0
  | b + 1 => FrogModel.Stage.refresh (blockWoken K) (refreshSeq K J ω b) (ω (b + 1))

/-- The initial frogs of the original configuration: the initial frogs of every block in order,
frog `i` being the initial label `i % J` of block `i / J`. -/
def origActive (J : ℕ) (hJ : 0 < J) (ω : ℕ → BlockSample d J) : ℕ → ℕ → Step d :=
  fun i => ω (i / J) (.inr ⟨i % J, Nat.mod_lt i hJ⟩)

end FrogModel.LemmaX
