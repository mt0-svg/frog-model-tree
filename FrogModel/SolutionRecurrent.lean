module

public import FrogModel.D3.Assembly
public import FrogModel.D3.Chain.Final

@[expose] public section

/-!
# The target of the frozen d = 3 statement

`recurrent_three`, the target of FrogModel/ChallengeRecurrent.lean (config-recurrent.json), that is
Theorem 1.3 of the paper: `D3.Assembly.recurrent_three_of_m1` (Theorem 8.4 and Lemma 8.3) applied to
`D3.Chain.m1run_certS_proof` (the stored run and its certificate, Proposition 15.1).
-/

namespace FrogModel

theorem recurrent_three : Recurrent 3 :=
  D3.Assembly.recurrent_three_of_m1 D3.Chain.m1run_certS_proof

end FrogModel
