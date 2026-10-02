module

public import FrogModel.Engine.G3StepW
public import FrogModel.LemmaX.Lemma61
public import FrogModel.LemmaX.Lemma62
public import FrogModel.LemmaX.ChildLaw
public import FrogModel.LemmaX.PlanSound
public import FrogModel.LemmaX.PlanData

@[expose] public section

/-!
# What a certificate that passes the G3 checker proves

`domCert_of_check`: a tree of entries that passes `checkAll`, with the start checks of `startOK`,
gives `DomCert` for the dominating chain that keeps the states of the data with flag 1: the
sub-solution `Vs` of the absorption (`Vs_sub_of_check`, `Vs_le_of_check`, `latMeasure_le_Vs`) and
the super-solution `Ws` of the flagged weight (`Ws_super_of_check`, `Ws_start`).

`phiSuper_of_check`: with a plan that passes `planCheck` for the atoms `A`, the last step of
Theorem 6.5 of the paper (`lemma62_holds`) gives `PhiSuper`, through the split of the dominating
output (`domSplit_of_domCert`, with the child laws `childPsiLaw_holds`, Lemma 6.3 of the paper
`lemma61_holds` and the simulation `isSim_childStep`), the stop weight (`stopWeight_of_check`)
and (I4) (`planI4_of_check`).
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Engine.G3

open FrogModel.Cert FrogModel.LemmaX

/-- **What the checker delivers**. -/
theorem domCert_of_check (t : G3K.Tree) (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ))
    (h : G3K.Spec.checkAll t = true) (hs : startOK A t = true) :
    DomCert 16 (keepOf t) A (Sov t) := by
  have hs' := hs
  simp only [startOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs'
  obtain ⟨⟨⟨hkey, -⟩, hat⟩, -⟩ := hs'
  refine ⟨fun a ha => ?_, ⟨Vs t, 128, by norm_num, Vs_sub_of_check t h, Vs_supp t,
    Vs_le_of_check t h, latMeasure_le_Vs t A hs⟩, ⟨Ws t, Ws_super_of_check t h,
    (Ws_start t hkey).le⟩⟩
  have := hat a ha
  simp only [atomOK, decide_eq_true_eq] at this
  rw [show cand.T = 8 from rfl]
  exact this.2.2.2.1

/-- **`PhiSuper` from a certificate**: a tree of entries that passes the checker and the start
checks for the atoms `A`, and a plan for `A` that passes `planCheck`. -/
theorem phiSuper_of_check (t : G3K.Tree) (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ))
    (pl : List (List (ℕ × ℕ))) (h : G3K.Spec.checkAll t = true) (hs : startOK A t = true)
    (hplan : planCheck A planDen pl = true) : PhiSuper :=
  lemma62_holds (odomC 16 (keepOf t)) (latMeasure A) (odomC 16 (keepOf t) - latMeasure A) (Sov t)
    (domSplit_of_domCert 16 (keepOf t) A (Sov t) childPsiLaw_holds lemma61_holds
      (isSim_childStep cand cand_I0 cand_I1) (domCert_of_check t A h hs))
    (stopWeight_of_check A t hs) (planI4_of_check A planDen pl hplan)

/-- **The composed statement**. -/
theorem phiSuper_of_cert
    (hc : ∃ (t : G3K.Tree) (A : List ((ℕ × ℕ × ℕ × ℕ) × ℕ)) (pl : List (List (ℕ × ℕ))),
      G3K.Spec.checkAll t = true ∧ startOK A t = true ∧ planCheck A planDen pl = true) :
    PhiSuper := by
  obtain ⟨t, A, pl, h, hs, hplan⟩ := hc
  exact phiSuper_of_check t A pl h hs hplan

end FrogModel.Engine.G3
