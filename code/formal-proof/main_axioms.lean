import FrogModel.Solution
import FrogModel.SolutionRecurrent

-- The axioms of the delivered theorems (those of config.json and config-recurrent.json at least). Run from the
-- package root: lake env lean code/formal-proof/main_axioms.lean

#print axioms FrogModel.transient_four
#print axioms FrogModel.meanVisits_four_le
#print axioms FrogModel.checkAll_theTree
#print axioms FrogModel.startOK_theTree
#print axioms FrogModel.recurrent_three
#print axioms FrogModel.D3.Chain.m1run_certS_proof
#print axioms FrogModel.D3.M1K.storedRun_holds
