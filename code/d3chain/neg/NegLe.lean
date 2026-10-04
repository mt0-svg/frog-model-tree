import FrogModel.D3.CertData.LeT

/-! Negative control: `T` with its cdf row 1 replaced by the row 1 of `S605` lowered by one unit in
slot 0 (`2` to `1`): the kernel check `leCheck` of `S605 ≤ T` must fail. -/

open FrogModel.D3.LaneD.K FrogModel.D3.CertData FrogModel.D3.Chain

set_option Elab.async false

theorem neg_le : leCheck 64 224 S605.F S605.D (T.F.set 1 (getN S605.F 1 - 1)) T.D = true := by
  decide +kernel
