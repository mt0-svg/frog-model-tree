module

public import FrogModel.D3.LaneD.K.Basic

@[expose] public section

/-!
# The end-configuration sums of Lemmas 11.2 and 11.3 of the paper, exact

`convF` of FrogModel/D3/Interfaces/Closure.lean summed over the triples `e` with the multinomial
weights, by exponential generating functions packed in two dimensions: with `x_e(g)` the pseudo-law
of the row `F(e, .)` at `2^-52` (an integer) times `(E - 1)!/e!`, in slots of `SW` bits, the rows `e`
at a stride of `B2 = (2 GM + 1) SW` bits, `X = sum_e x_e Y^e`; `Q = X^2` and `R = X_J Q` (rows `e < J`
of `X`) truncated at `s ≤ GM`. Row `M` of `R` at `s`, times `M!`, is
`sum over |e| = M (e_0 < J) of M!/(e_0! e_1! e_2!) convF(F, GM, e, s) (E - 1)!^3 2^156`, exactly.

The sums of (A) and (B) are evaluated by query families, every `q = 2..Q0` (`Q0 = E + 1`) at once, as
a vector over `t = Q0 - q` (`E` slots of `SW` bits): a family is a cut `sh` on `s` (`n0 - q - 1` or
`K - q - 1`) and an upper cut `nh` on `n = q + s` (`M + v` for (A), none for (B)). No rounding
anywhere; the slot width `SW` holds every value (checked in `Check.lean`).
-/

namespace FrogModel.D3.LaneD.K

structure ConvCfg where
  E : Nat
  GM : Nat
  SW : Nat

def ConvCfg.B2 (c : ConvCfg) : Nat := Nat.mul (Nat.add (Nat.mul 2 c.GM) 1) c.SW
def ConvCfg.rowW (c : ConvCfg) : Nat := Nat.mul (Nat.add c.GM 1) c.SW
def ConvCfg.Q0 (c : ConvCfg) : Nat := Nat.add c.E 1
def ConvCfg.NN (c : ConvCfg) : Nat := Nat.add (Nat.add c.E c.GM) 1

/-- The slots `s ≤ GM` in each of the rows `0..k-1`. -/
def tmask (c : ConvCfg) (k : Nat) : Nat := Nat.mul (mask c.rowW) (ones c.B2 k)

/-- The pseudo-law of a row (64-bit slots, `g = 0..GM`), times `m`, in `SW`-bit slots. -/
def plRow (c : ConvCfg) (m row : Nat) : Nat :=
  packTree c.SW (fun g => cond (Nat.ble g c.GM)
    (Nat.mul m (Nat.sub (slot 64 row g) (cond (Nat.beq g 0) 0 (slot 64 row (Nat.sub g 1))))) 0)
    (clog (Nat.add c.GM 1)) 0

/-- `X` from the rows `F(0..E-1, .)`. -/
def buildX (c : ConvCfg) (rows : List Nat) : Nat :=
  let fE1 := fact (Nat.sub c.E 1)
  packTree c.B2 (fun e => cond (Nat.blt e c.E) (plRow c (Nat.div fE1 (fact e)) (getN rows e)) 0)
    (clog c.E) 0

def sqQ (c : ConvCfg) (X : Nat) : Nat := Nat.land (Nat.mul X X) (tmask c (Nat.sub (Nat.mul 2 c.E) 1))

/-- `R = X_J Q` truncated, rows `0..J + 2E - 3`. -/
def prodR (c : ConvCfg) (X Q J : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.land X (mask (Nat.mul J c.B2))) Q)
    (tmask c (Nat.add J (Nat.sub (Nat.mul 2 c.E) 2)))

/-- The prefix sums along `s` of every row. -/
def prefixR (c : ConvCfg) (R J : Nat) : Nat :=
  Nat.land (Nat.mul R (ones c.SW (Nat.add c.GM 1)))
    (tmask c (Nat.add J (Nat.sub (Nat.mul 2 c.E) 2)))

/-- Every row `M` of the list times `M!`. -/
def scaleFact (l : List Nat) : List Nat :=
  (natFold l.length ([], l, 1) (fun M (st : List Nat × List Nat × Nat) =>
    (Nat.mul st.2.2 (hd st.2.1) :: st.1, tl st.2.1, Nat.mul st.2.2 (Nat.add M 1)))).1.reverse

/-- The tables of one `J`: the rows `M` of `R` and of its prefix sums, times `M!`, each packed
(slots `s ≤ GM`). -/
structure Tab where
  J : Nat
  R : List Nat
  PR : List Nat

def mkTab (c : ConvCfg) (X Q J : Nat) : Tab :=
  let R := prodR c X Q J
  let n := Nat.add J (Nat.sub (Nat.mul 2 c.E) 2)
  ⟨J, scaleFact (split c.B2 n R), scaleFact (split c.B2 n (prefixR c R J))⟩

/-- The rows `M = 0..m-1` of `omega'(n, M) = C(n, M) 4^(NN - n)`, `n = 0..NN`, at the slot `NN - n`
(reversed, slots of `SW` bits), by the exact division
`r_(M+1) (2^(SW+2) - 1) = r_M - C(NN, M) - C(NN, M+1)` (Pascal's rule along the slots), from
`r_0 = sum over k ≤ NN of 2^((SW+2) k)`. -/
def omRows (SW NN m : Nat) : List Nat :=
  let d := Nat.sub (Nat.shiftLeft 1 (Nat.add SW 2)) 1
  let r0 := Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul (Nat.add SW 2) (Nat.add NN 1))) 1) d
  (natFold m ([], r0, 1) (fun M (st : List Nat × Nat × Nat) =>
    let c1 := Nat.div (Nat.mul st.2.2 (Nat.sub NN M)) (Nat.add M 1)
    (st.2.1 :: st.1, Nat.div (Nat.sub (Nat.sub st.2.1 st.2.2) c1) d, c1))).1.reverse

/-! ## The envelope sums by query families

For one `M`, `q`, a cut `sh` on `s` and a cut `nh` on `n = q + s`, with `ns = floor(4M/3)` the mode of
`omega'(., M)`, the envelope sum is `omega'(q + c, M) PR(c) + sum over c < s ≤ hi of omega'(q + s, M) R(s)`,
`hi = min(sh, nh - q)`, `c = clamp(ns - q, max(0, M - q), hi)` (zero when `hi < M - q`). Case by case it is
* the window `sum over n in [ns + 1, nh], 0 ≤ n - q ≤ sh of omega'(n) R(n - q)`: one product of the
  weights on `[ns + 1, nh]` (a slice of the reversed row) with `R` cut at `sh`, read at slot `nh - q`;
* plus, for `q ≤ ns`, with `a = min(ns, nh)`: `omega'(a) PR(a - q)` when `q ≥ a - sh`, else
  `omega'(q + sh) PR(sh)`. -/

/-- The vector over `t = Q0 - q` (`q = 2..Q0`) of the envelope sum of one `M`: rows `O` (weights,
reversed), `R`, `PR`, and `Ow` the weights on the window `n ∈ [ns + 1, nw]`, `nw = min(nh, NN)`, at the
slots `i = nw - n`. Every operand is cut to the slots that reach some `q ≤ Q0` first. -/
def envUnit (c : ConvCfg) (sh M nh Ow O R PR : Nat) : Nat :=
  let SW := c.SW
  let Q0 := c.Q0
  let ns := Nat.div (Nat.mul 4 M) 3
  let a := minN ns nh
  let nw := minN nh c.NN
  -- the window: `s = n - q ∈ [s0, s1]`, product slot `nw - q - s0`, read at `t = Q0 - q`
  let s0 := Nat.sub (Nat.add ns 1) Q0
  let s1 := minN sh (Nat.sub nw 2)
  let Zc := Nat.land (Nat.shiftRight R (Nat.mul s0 SW)) (mask (Nat.mul (Nat.sub (Nat.add s1 1) s0) SW))
  let P := Nat.mul Ow Zc
  let up := Nat.add s0 Q0
  let vW := Nat.land
    (cond (Nat.ble up nw) (Nat.shiftRight P (Nat.mul (Nat.sub nw up) SW))
      (Nat.shiftLeft P (Nat.mul (Nat.sub up nw) SW)))
    (mask (Nat.mul c.E SW))
  -- `omega'(a) PR(a - q)` for `q ∈ [max(2, a - sh), min(Q0, ns, a)]`
  let qlo := maxN 2 (Nat.sub a sh)
  let qhi := minN (minN Q0 ns) a
  let PRx := Nat.land (Nat.shiftRight PR (Nat.mul (Nat.sub a qhi) SW))
    (mask (Nat.mul (Nat.sub (Nat.add qhi 1) qlo) SW))
  let vA := Nat.mul (slot SW O (Nat.sub c.NN a)) (Nat.shiftLeft PRx (Nat.mul (Nat.sub Q0 qhi) SW))
  -- `omega'(q + sh) PR(sh)` for `q ∈ [2, min(Q0, ns, a - sh - 1)]`
  let qs := minN (minN Q0 ns) (Nat.sub (Nat.sub a sh) 1)
  let Ox := Nat.land (Nat.shiftRight O (Nat.mul (Nat.sub (Nat.sub c.NN sh) qs) SW))
    (mask (Nat.mul (Nat.sub qs 1) SW))
  let vS := Nat.mul (slot SW PR sh) (Nat.shiftLeft Ox (Nat.mul (Nat.sub Q0 qs) SW))
  Nat.add vW (Nat.add vA vS)

/-- (A), one cut `sh` and every `v ≤ VM` whose bit is set in `used`: the vectors over `t` of
`sum over M of envUnit(sh, M, M + v)` (zero for the other `v`), from the table `J = E`. -/
def famA (c : ConvCfg) (VM sh used : Nat) (oms : List Nat) (t : Tab) : List Nat :=
  let Mn := Nat.sub (Nat.mul 3 c.E) 2
  (natFold Mn ((List.range (Nat.add VM 1)).map (fun _ => 0), oms, t.R, t.PR)
    (fun M (st : List Nat × List Nat × List Nat × List Nat) =>
      let O := hd st.2.1
      let R := hd st.2.2.1
      let PR := hd st.2.2.2
      let ns := Nat.div (Nat.mul 4 M) 3
      let nwF := minN (Nat.add M VM) c.NN
      let OwF := Nat.land (Nat.shiftRight O (Nat.mul (Nat.sub c.NN nwF) c.SW))
        (mask (Nat.mul (Nat.sub nwF ns) c.SW))
      let vs := (natFold (Nat.add VM 1) ([], st.1) (fun v (u : List Nat × List Nat) =>
        let x := hd u.2
        let nh := Nat.add M v
        let Ow := Nat.shiftRight OwF (Nat.mul (Nat.sub nwF (minN nh c.NN)) c.SW)
        (cond (Nat.beq (Nat.land (Nat.shiftRight used v) 1) 1)
            (Nat.add x (envUnit c sh M nh Ow O R PR)) x :: u.1, tl u.2))).1.reverse
      (vs, tl st.2.1, tl st.2.2.1, tl st.2.2.2))).1

/-- (B), one family `(J, sh)` from the table of `J`: the vector over `t` of
`sum over M of envUnit(sh, M, NN)` on the rows `M = 0..J + 2E - 3` of `R = X_J Q` (no cut on `n`). -/
def famB (c : ConvCfg) (sh : Nat) (oms : List Nat) (t : Tab) : Nat :=
  (natFold t.R.length (0, oms, t.R, t.PR) (fun M (st : Nat × List Nat × List Nat × List Nat) =>
    let O := hd st.2.1
    let Ow := Nat.land O (mask (Nat.mul (Nat.sub c.NN (Nat.div (Nat.mul 4 M) 3)) c.SW))
    (Nat.add st.1 (envUnit c sh M c.NN Ow O (hd st.2.2.1) (hd st.2.2.2)),
      tl st.2.1, tl st.2.2.1, tl st.2.2.2))).1

end FrogModel.D3.LaneD.K
