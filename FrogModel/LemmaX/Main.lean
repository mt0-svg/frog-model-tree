module

public import FrogModel.LemmaX.Statement
public import FrogModel.LemmaX.Psi
public import FrogModel.LemmaX.Kill

@[expose] public section

/-!
# Lemma X: the frozen statements of Lemmas 4.1 and 4.2 of the paper hold

Each `<name>_holds` proves the `Prop` `<name>` of LemmaX/Statement.lean.
-/

open scoped ENNReal

namespace FrogModel.LemmaX

theorem psiLeastFixed_holds : PsiLeastFixed := fun _ G D j =>
  ⟨psiN_fixed G D j, fun n hn => psiN_le G D j n hn.le⟩

theorem psiIterate_holds : PsiIterate := fun _ G D j => psiN_eq_iSup_iterate G D j

theorem psiStep_holds : PsiStep := fun _ G D j k hk => lt_psiT_of_lt_psiN G D j k hk

theorem psiCurve_holds : PsiCurve := fun _ G D => ⟨psiG_zero G D, psiG_mono G D⟩

theorem psiMono_holds : PsiMono := fun _ G G' D h j =>
  ⟨psiN_le_of_le G G' D h j, psiG_le_of_le G G' D h j⟩

theorem psiZero_holds : PsiZero := fun _ D j => psiN_of_zero D j

theorem measurableKill_holds : MeasurableKill := fun _ K =>
  ⟨measurable_frozenCountK K, measurable_curveK K⟩

theorem curveNested_holds : CurveNested := fun _ K ζ ξ => ⟨curveK_zero K ζ ξ, curveK_mono K ζ ξ⟩

theorem curveFirst_holds : CurveFirst := fun _ K ζ => frozenCountK_eq_curveK K ζ

theorem truncation_holds : Truncation := fun _ ζ => ⟨frozenCountK_mono ζ, iSup_frozenCountK ζ⟩

theorem meanTruncation_holds : MeanTruncation := fun d _ => meanX_eq_iSup d

theorem curveCongr_holds : CurveCongr := fun _ K m ζ ζ' ξ ξ' hζ hξ =>
  curveK_congr K m ζ ζ' ξ ξ' hζ hξ

theorem measurablePsiG_holds : MeasurablePsiG := fun _ => measurable_psiG

end FrogModel.LemmaX
