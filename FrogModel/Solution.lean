module

public import FrogModel.Final
public import FrogModel.G3K.Equiv
public import FrogModel.G3Q.Cand.All

@[expose] public section

/-!
# The targets of the frozen statements

`transient_four` and `meanVisits_four_le`, the two targets of FrogModel/Challenge.lean, under their
names and with their types there, from the data tree `G3Q.theTree`
of the certificate (the release asset of ASSETS.md). The data and theorem modules `FrogModel.G3Q.Cand.*`
are written by `g3k` (code/g3k/gen.sh), not committed; the kernel checks every chunk of the tree
in them, assembled in `G3Q.checkAll_theTree : checkAllF theTree = true`.
-/

open MeasureTheory

namespace FrogModel

/-- The start checks of the certificate on the data tree, by the kernel. -/
theorem startOK_theTree : Engine.G3.startOK LemmaX.Latoms G3Q.theTree = true := by
  decide +kernel

/-- The data tree passes the reference checker `G3K.Spec.checkAll`. -/
theorem checkAll_theTree : G3K.Spec.checkAll G3Q.theTree = true := by
  rw [← G3K.Equiv.checkAllF_eq]
  exact G3Q.checkAll_theTree

/-- **Target.** The Hoffman-Johnson-Junge conjecture at `d = 4`: the frog model on the rooted
4-ary tree is transient. -/
theorem transient_four : Transient 4 :=
  transient_four_of_data ⟨G3Q.theTree, checkAll_theTree, startOK_theTree⟩

/-- **Target.** The expected number of visits to the root of the frog model on the rooted 4-ary
tree is at most `5.756`. -/
theorem meanVisits_four_le :
    ∫⁻ ω, (visits (paths ω)).encard ∂frogMeasure 4 ≤ ENNReal.ofReal (5756 / 1000) :=
  meanVisits_four_le_of_data ⟨G3Q.theTree, checkAll_theTree, startOK_theTree⟩

end FrogModel
