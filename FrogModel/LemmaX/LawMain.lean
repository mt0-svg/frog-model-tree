module

public import FrogModel.LemmaX.LawStatement
public import FrogModel.LemmaX.Mean
public import FrogModel.LemmaX.ClaimALaw

@[expose] public section

/-!
# Lemma X: the frozen statements of Claim A, the coupling order and the induction hold

The `Prop`s of LemmaX/LawStatement.lean. Claim A: `claimAPathwise_holds` in LemmaX/ClaimA.lean,
`claimAOrig_holds`, `claimAIid_holds` and `claimA_holds` in LemmaX/ClaimALaw.lean. The coupling
order and the induction below, from LemmaX/Coupling.lean and LemmaX/Mean.lean.
-/

open MeasureTheory

namespace FrogModel.LemmaX

theorem couplingRefl_holds : CouplingRefl := by
  intro α _ _ P _ hle
  exact couplingLE_refl P hle

theorem couplingTrans_holds : CouplingTrans := by
  intro α _ _ _ _ P Q R hPQ hQR
  exact couplingLE_trans P Q R hPQ hQR

theorem couplingProd_holds : CouplingProd := by
  intro α β _ _ _ _ P P' Q Q' hP hQ
  exact couplingLE_prod P P' Q Q' hP hQ

theorem couplingPi_holds : CouplingPi := by
  intro ι _ α _ _ P Q h
  exact couplingLE_pi P Q h

theorem couplingInfinitePi_holds : CouplingInfinitePi := by
  intro ι _ α _ _ P Q h
  exact couplingLE_infinitePi P Q h

theorem couplingMap_holds : CouplingMap := by
  intro α β _ _ _ _ f hf hmono hle P Q h
  exact couplingLE_map f hf hmono hle P Q h

theorem restrictMono_holds : RestrictMono := fun J P Q h => restrict_mono J P Q h

theorem brLawMono_holds : BrLawMono := fun J H H' h => brLaw_mono J H H' h

theorem psiLawMono_holds : PsiLawMono := fun d P Q h => psiLaw_mono d P Q h

theorem phiLawMono_holds : PhiLawMono := fun d J H H' h => phiLaw_mono d J H H' h

theorem blockInduction_holds : BlockInduction := by
  intro d _ J H h0 hs hA hH K
  exact blockInduction d J H h0 hs hA hH K

theorem meanOfBlockBound_holds : MeanOfBlockBound := by
  intro d _ J hJ H h
  exact meanOfBlockBound d J hJ H h

theorem lemmaXOfSuper_holds : LemmaXOfSuper := by
  intro d _ J hJ H h0 hs hA hH
  exact lemmaXOfSuper d J hJ H h0 hs hA hH

end FrogModel.LemmaX
