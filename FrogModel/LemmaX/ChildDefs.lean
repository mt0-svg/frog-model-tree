module

public import FrogModel.Engine.Defs
public import FrogModel.LemmaX.CertStatement

@[expose] public section

/-!
# The child chain of a certificate and the statements of Lemmas 6.1 and 6.3 of the paper

Sections 6.2, 6.4 and 6.5 of the paper. The root engine (FrogModel.Engine) consumes these
definitions.

**States** (`CState`). `fresh` (never entered), `bdry` (a block complete), `lab q s` (label `s` of
level `q`), `tail q` (level `q` of a tail block `Z_t`), `maxLab q` (the max label of level `q`,
the redirect target of Lemma 6.4). The well-formed states (`ChildWF`) have `1 ≤ q ≤ J - 1`
and `s` a label of level `q`; every move keeps them well formed.

**Rows.** The row of a state is a finite list of entries `(p, δ, next)` (`finRow`), followed for
`fresh` and `bdry` by the geometric tail: entry `n` has weight `eps (1 - rho) rho^n`, delivers
`T + 1 + n` and moves to `tail 2` (from `fresh`) or `tail 1` (from `bdry`). From `fresh` the
own frog and the entering frog use the first two transitions of a block at once. A level `J`
reads as `bdry`. The rows of `lab q s` are the table rows sorted by `δ`; the row of `maxLab q`
has `P(δ ≥ k) = max_s P_s(δ ≥ k)` over the labels `s` of level `q`, in the order of `δ`.

**One uniform per entry** (`childStep`). The entry reads a uniform `u`, moved to `0` off
`[0, 1)`, and takes the first entry of the row sequence (`rowSeq`) whose cumulative weight
exceeds it (the inverse distribution function), or stays at `(0, s)` if there is none.

**Weights of Lemma 6.3** (`wQ`, `PhiQ`), computable over `ℚ` from the same rows.
-/

open MeasureTheory
open scoped ENNReal

namespace FrogModel.Cert

/-- The states of the child chain. -/
inductive CState
  | fresh
  | bdry
  | lab (q s : ℕ)
  | tail (q : ℕ)
  | maxLab (q : ℕ)
  deriving DecidableEq, Repr

/-- The code of a state: its constructor and its arguments. -/
def CState.code : CState → ℕ × ℕ × ℕ
  | .fresh => (0, 0, 0)
  | .bdry => (1, 0, 0)
  | .lab q s => (2, q, s)
  | .tail q => (3, q, 0)
  | .maxLab q => (4, q, 0)

/-- The state of a code, the inverse of `CState.code` on its image. -/
def CState.ofCode : ℕ × ℕ × ℕ → Option CState
  | (0, _, _) => some .fresh
  | (1, _, _) => some .bdry
  | (2, q, s) => some (.lab q s)
  | (3, q, _) => some (.tail q)
  | (4, q, _) => some (.maxLab q)
  | _ => none

instance : Encodable CState :=
  Encodable.ofLeftInjection CState.code CState.ofCode fun x => by cases x <;> rfl

instance : MeasurableSpace CState := ⊤

instance : DiscreteMeasurableSpace CState := ⟨fun _ => trivial⟩

/-- An entry of a row: weight `p`, delivered returns `δ`, next state. -/
structure Entry where
  p : ℚ
  δ : ℕ
  next : CState
  deriving DecidableEq, Repr

namespace Data

variable (D : Data)

/-- Label `s` of level `q`, read as `bdry` at level `J`. -/
def nxt (q s : ℕ) : CState := if q = D.J then .bdry else .lab q s

/-- The tail state of level `q`, read as `bdry` at level `J`. -/
def nxtTail (q : ℕ) : CState := if q = D.J then .bdry else .tail q

/-- The max label of level `q`, read as `bdry` at level `J`. -/
def nxtMax (q : ℕ) : CState := if q = D.J then .bdry else .maxLab q

/-- The row of label `s` of level `q`, sorted by `δ`. -/
def labRow (q s : ℕ) : List Entry :=
  ((D.row q s).map fun t => (⟨t.p, t.δ, D.nxt (q + 1) t.s'⟩ : Entry)).mergeSort
    fun a b => decide (a.δ ≤ b.δ)

/-- The finite part of the row of `fresh`: the first two transitions of a block. -/
def freshRow : List Entry :=
  (D.row 0 0).flatMap fun t₁ => (D.row 1 t₁.s').map fun t₂ =>
    (⟨(1 - D.eps) * t₁.p * t₂.p, t₁.δ + t₂.δ, D.nxt 2 t₂.s'⟩ : Entry)

/-- The finite part of the row of `bdry`: the first transition of a block. -/
def bdryRow : List Entry :=
  (D.row 0 0).map fun t₁ => (⟨(1 - D.eps) * t₁.p, t₁.δ, D.nxt 1 t₁.s'⟩ : Entry)

/-- The row of `tail q`. -/
def tailRow (q : ℕ) : List Entry := [⟨1, 0, D.nxtTail (q + 1)⟩]

/-- `P_s(δ ≥ k)` for label `s` of level `q`. -/
def tailMass (q s k : ℕ) : ℚ := (((D.row q s).filter fun t => k ≤ t.δ).map Tr.p).sum

/-- `max_s P_s(δ ≥ k)` over the labels `s` of level `q`. -/
def tailMax (q k : ℕ) : ℚ := ((List.range (D.nLabels q)).map fun s => D.tailMass q s k).foldr max 0

/-- The largest increment of the table. -/
def maxDelta : ℕ := (D.table.map Tr.δ).foldr max 0

/-- The row of `maxLab q`: `δ = k` with weight `tailMax q k - tailMax q (k + 1)`. -/
def maxRow (q : ℕ) : List Entry :=
  (List.range (D.maxDelta + 1)).map fun k =>
    (⟨D.tailMax q k - D.tailMax q (k + 1), k, D.nxtMax (q + 1)⟩ : Entry)

/-- The finite part of the row of a state. -/
def finRow : CState → List Entry
  | .fresh => D.freshRow
  | .bdry => D.bdryRow
  | .lab q s => D.labRow q s
  | .tail q => D.tailRow q
  | .maxLab q => D.maxRow q

/-- The state reached by the geometric tail of the row, for `fresh` and `bdry`. -/
def tailNext : CState → Option CState
  | .fresh => some (D.nxtTail 2)
  | .bdry => some (D.nxtTail 1)
  | _ => none

/-- The weight of entry `n` of the geometric tail. -/
def tailW (n : ℕ) : ℚ := D.eps * (1 - D.rho) * D.rho ^ n

/-- The row of `s` as a sequence: the finite part, then the geometric tail (for `fresh` and
`bdry`), then entries of weight `0`. -/
def rowSeq (s : CState) (n : ℕ) : Entry :=
  if h : n < (D.finRow s).length then (D.finRow s)[n]
  else match D.tailNext s with
    | some s' => ⟨D.tailW (n - (D.finRow s).length), D.T + 1 + (n - (D.finRow s).length), s'⟩
    | none => ⟨0, 0, s⟩

/-- The weight of the first `n` entries of the row sequence. -/
def rowCum (s : CState) (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, (D.rowSeq s k).p

/-- The weight of the row of `s` on the move `r = (δ, next)`: the finite entries plus the tail
entry. -/
def rowLawQ (s : CState) (r : ℕ × CState) : ℚ :=
  (((D.finRow s).filter fun e => e.δ = r.1 ∧ e.next = r.2).map Entry.p).sum +
    if D.tailNext s = some r.2 ∧ D.T + 1 ≤ r.1 then D.tailW (r.1 - (D.T + 1)) else 0

/-- The well-formed states. -/
def ChildWF : CState → Prop
  | .fresh => True
  | .bdry => True
  | .lab q s => 1 ≤ q ∧ q < D.J ∧ s < D.nLabels q
  | .tail q => 1 ≤ q ∧ q < D.J
  | .maxLab q => 1 ≤ q ∧ q < D.J

instance : DecidablePred D.ChildWF := fun s => by
  cases s <;> unfold ChildWF <;> infer_instance

open Classical in
/-- **One entry of the child chain**: the uniform `u` (moved to `0` off `[0, 1)`) selects the
first entry of the row sequence whose cumulative weight exceeds it. -/
noncomputable def childStep (s : CState) (u : ℝ) : ℕ × CState :=
  if h : ∃ n, (if 0 ≤ u ∧ u < 1 then u else 0) < (D.rowCum s (n + 1) : ℝ) then
    ((D.rowSeq s (Nat.find h)).δ, (D.rowSeq s (Nat.find h)).next)
  else (0, s)

/-- `sum_k p_k phi^(δ_k)` over a list of entries. -/
def rowMgf (l : List Entry) : ℚ := (l.map fun e => e.p * D.phi ^ e.δ).sum

/-- `r_q(M_q)` at level `q = J - n`: `1` at level `J`, and `rowMgf (maxRow q) r_(q+1)(M_(q+1))`. -/
def rMaxLevel : ℕ → ℚ
  | 0 => 1
  | n + 1 => D.rowMgf (D.maxRow (D.J - (n + 1))) * rMaxLevel n

/-- `r_q(M_q)`, for `q ≤ J`. -/
def rMax (q : ℕ) : ℚ := D.rMaxLevel (D.J - q)

/-- The weight `w` of a child state (Sections 6.4 and 6.5 of the paper, with
`w(maxLab q) = kappa^(q-1) r_q(M_q)`). -/
def wQ : CState → ℚ
  | .fresh => D.kappa ^ D.J
  | .bdry => D.kappa ^ (D.J - 1)
  | .lab q s => D.kappa ^ (q - 1) * D.r q s
  | .tail q => D.kappa ^ (q - 1)
  | .maxLab q => D.kappa ^ (q - 1) * D.rMax q

/-- `Phi(state) = theta^e phi^(p + J - i) prod_c w(σ_c)` of Lemma 6.3, at `d = J = 4`. The
engine counts the finished frogs from `0`, so the exponent is `p + 4 - i - 1`: `4` at the start,
`0` once absorbed. -/
def PhiQ (x : FrogModel.Engine.RState CState 4 4) : ℚ :=
  D.theta ^ x.e * D.phi ^ (x.p + 4 - x.i - 1) * ∏ c, D.wQ (x.σ c)

end Data

end FrogModel.Cert

namespace FrogModel.LemmaX

open FrogModel.Cert

/-- The law of the uniforms: Lebesgue measure on `[0, 1]`. -/
noncomputable def lam : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure lam := ⟨by simp [lam]⟩

/-- `theta^n` for `n : ℕ∞`, `⊤` at `⊤`. -/
noncomputable def epow (θ : ℝ≥0∞) (n : ℕ∞) : ℝ≥0∞ := if n = ⊤ then ⊤ else θ ^ n.toNat

/-- `G` with its values at `0` and `1` set to `0`: `psiG` reads a child curve only at the
indices `m + 1 ≥ 2`, and the child chain delivers `G(2)` at its first entry. -/
def trimCurve (G : ℕ → ℕ∞) (i : ℕ) : ℕ∞ := if i ≤ 1 then 0 else G i

/-- **The row law** (Lemma 6.1, consumed by the checker): for a well-formed state of `cand`,
the uniform selects the move `r` with probability the weight of the row on `r`. -/
def RowLaw : Prop :=
  ∀ s r, cand.ChildWF s →
    lam {u | cand.childStep s u = r} = ENNReal.ofReal (cand.rowLawQ s r : ℝ)

/-- **The child chain** (Lemma 6.1): from `fresh`, the delivery curve of the chain driven by
i.i.d. uniforms has the law `BR(H*)` at the indices `≥ 2`. -/
def ChildLaw : Prop :=
  (FrogModel.Engine.iidMeasure lam).map (FrogModel.Engine.chainCurve cand.childStep .fresh) =
    (brLaw 4 Hstar).map trimCurve

/-- **The child chain under `Psi`** (Lemma 6.1, consumed by `law_outPsi_start`). -/
def ChildPsiLaw : Prop :=
  FrogModel.Recursion.psiLaw 4
      ((FrogModel.Engine.iidMeasure lam).map (FrogModel.Engine.chainCurve cand.childStep .fresh)) =
    FrogModel.Recursion.psiLaw 4 (brLaw 4 Hstar)

/-- **Lemma 6.3**: from a live (or correctly absorbed) state with well-formed children,
the root chain of the child chains of `cand` ends almost surely and
`E theta^(G(J)) ≤ Phi(state)` (`θ^⊤ = ⊤`). -/
def Lemma61 : Prop :=
  ∀ x : FrogModel.Engine.RState CState 4 4, FrogModel.Engine.Valid x →
    (x.i < 4 ∨ (x.i = 4 ∧ x.out 3 = (x.e : ℕ∞))) → (∀ c, cand.ChildWF (x.σ c)) →
    ∫⁻ w, epow thetaC (FrogModel.Engine.recOut
        (FrogModel.Engine.traj (FrogModel.Engine.rstep cand.childStep) x w) 3)
      ∂(FrogModel.Engine.iidMeasure ((FrogModel.Engine.unifDir 4).prod lam)) ≤
      ENNReal.ofReal (cand.PhiQ x : ℝ)

end FrogModel.LemmaX
