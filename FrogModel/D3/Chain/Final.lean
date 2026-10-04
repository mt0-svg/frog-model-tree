module

public import FrogModel.D3.CertData.Main
public import FrogModel.D3.M1K.Run

@[expose] public section

/-!
# Proposition 15.1 of the paper: `Iface.m1run_certS`

The stored run (`M1K.storedRun`) satisfies `M1Run.Holds`, part (1), and the stored certificate (the
modules `FrogModel.D3.CertData` that the generator code/d3chain writes from it) is a certificate as
in part (2) from the seed of the run's top masses: `m1run_certS_of` from the soundness of the step
check, `m1run_certS_proof` with `LaneD.step_sound`.
-/

namespace FrogModel.D3.Chain

open FrogModel.D3.Iface

/-- **Proposition 15.1 of the paper**, given the soundness of the step check. -/
theorem m1run_certS_of (hs : StepSoundT) : m1run_certS :=
  ⟨M1K.storedRun, M1K.storedRun_holds,
    CertData.certS1_stored hs LaneD.seedCheck_sound LaneD.extCheck_sound (topMass M1K.storedRun)
      M1K.topMass_eq_massPk⟩

/-- **Proposition 15.1 of the paper**. -/
theorem m1run_certS_proof : m1run_certS := m1run_certS_of LaneD.step_sound

end FrogModel.D3.Chain
