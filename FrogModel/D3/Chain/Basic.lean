module

public import FrogModel.D3.LaneD.K.Cover

@[expose] public section

/-!
# The chain of the certificate (Proposition 15.1 (2) of the paper): kernel helpers (Lean core)

The generated modules of `FrogModel.D3.CertData` (code/d3chain) check every part of a line in its own
declaration and collect the parts in `AllP`. Two more checks of stored states: `leCheck`, every
stored value of one state at most the one of another (the step chain ends in `m605`, the CHECK line
reads `T ≥ m605`), and `wfCheck`, the shape of a stored state (`State.WF` of the CHECK state `T`, which
`step_sound` takes as a hypothesis on its input).
-/

namespace FrogModel.D3.Chain

open FrogModel.D3.LaneD.K

/-- `f p` for every part `p` of the list, as nested conjunctions. -/
def AllP (f : Part → Prop) : List Part → Prop
  | [] => True
  | p :: l => f p ∧ AllP f l

theorem forall_mem_of_allP {f : Part → Prop} : ∀ {l : List Part}, AllP f l → ∀ p ∈ l, f p
  | [], _, _, hp => nomatch hp
  | _ :: _, ⟨ha, hl⟩, p, hp => by
    cases hp with
    | head => exact ha
    | tail _ h => exact forall_mem_of_allP hl p h

/-- Every stored value of `(F, D)` is at most the one of `(F', D')`: rows `0..E`, slots `0..GM`,
deficits `0..E`, 64-bit slots. -/
def leCheck (E GM : Nat) (F : List Nat) (D : Nat) (F' : List Nat) (D' : Nat) : Bool :=
  allN (Nat.add E 1) (fun k => allN (Nat.add GM 1) (fun g =>
      Nat.ble (slot 64 (getN F k) g) (slot 64 (getN F' k) g))) &&
    allN (Nat.add E 1) (fun k => Nat.ble (slot 64 D k) (slot 64 D' k))

/-- The shape of a stored state with rows `0..E` of slots `0..GM` and deficits `0..E`: values at most
`2^52`, rows nondecreasing in `g`, row `0` and deficit `0` equal to `2^52`. -/
def wfCheck (E GM : Nat) (F : List Nat) (D : Nat) : Bool :=
  allN (Nat.add E 1) (fun k => allN (Nat.add GM 1) (fun g =>
      Nat.ble (slot 64 (getN F k) g) one52 &&
        (Nat.beq g GM || Nat.ble (slot 64 (getN F k) g) (slot 64 (getN F k) (Nat.add g 1))))) &&
    allN (Nat.add E 1) (fun k => Nat.ble (slot 64 D k) one52) &&
    allN (Nat.add GM 1) (fun g => Nat.beq (slot 64 (getN F 0) g) one52) &&
    Nat.beq (slot 64 D 0) one52

end FrogModel.D3.Chain
