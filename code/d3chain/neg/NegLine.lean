import FrogModel.D3.CertData.L.L350

/-! Negative control: the line L350 with the stored output deficit 5 lowered by `2^30` units
(`2^-22`); the kernel check of its part must fail. -/

open FrogModel.D3.LaneD.K FrogModel.D3.CertData

set_option Elab.async false

theorem neg_line : check ({ L350.line with outD := L350.line.outD - 2 ^ (64 * 5 + 30) }.withPart L350.p0) = true := by
  decide +kernel
