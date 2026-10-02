/-!
# The table of a version 3 certificate and its child chain (code/certificate/FORMAT.md, version 4)

Exact rationals on `Nat`, the parser of the table, the child states with their rows, potentials and
lumps ("Objects derived from the table"), and the compositions in the lane order of the Lean checker.
Untrusted: a wrong table module makes the checker reject
the certificate or check another chain, which the soundness proof would expose.
-/

namespace G3Tool

structure Q where
  n : Nat
  d : Nat
deriving Inhabited, BEq

namespace Q
def mk' (n d : Nat) : Q := let g := Nat.gcd n d; if g == 0 then ⟨0, 1⟩ else ⟨n / g, d / g⟩
def zero : Q := ⟨0, 1⟩
def one : Q := ⟨1, 1⟩
def ofNat (k : Nat) : Q := ⟨k, 1⟩
def add (a b : Q) : Q := mk' (a.n * b.d + b.n * a.d) (a.d * b.d)
/-- `a - b`, assuming `a ≥ b`. -/
def sub (a b : Q) : Q := mk' (a.n * b.d - b.n * a.d) (a.d * b.d)
def mul (a b : Q) : Q := mk' (a.n * b.n) (a.d * b.d)
def div (a b : Q) : Q := mk' (a.n * b.d) (a.d * b.n)
def pow (a : Q) (k : Nat) : Q := ⟨a.n ^ k, a.d ^ k⟩
def lt (a b : Q) : Bool := a.n * b.d < b.n * a.d
def parse (s : String) : Option Q :=
  match s.splitOn "/" with
  | [a] => a.toNat?.map fun x => ⟨x, 1⟩
  | [a, b] => do
    let x ← a.toNat?
    let y ← b.toNat?
    if y == 0 then none else pure (mk' x y)
  | _ => none
def floor48 (a : Q) : Nat := a.n * 2 ^ 48 / a.d
def ceil48 (a : Q) : Nat := (a.n * 2 ^ 48 + a.d - 1) / a.d
end Q

structure TrLine where
  q : Nat
  src : String
  delta : Nat
  dst : String
  p : Q

structure Table where
  j : Nat := 0
  t : Nat := 0
  tp : Nat := 0
  eps : Q := Q.zero
  rho : Q := Q.zero
  phi : Q := Q.zero
  kappa : Q := Q.zero
  labs : Array (Nat × String) := #[]
  trs : Array TrLine := #[]

def Table.labels (tb : Table) (q : Nat) : Array String :=
  if q == 0 then #["root"] else if q == tb.j then #["end"]
  else (tb.labs.filter (·.1 == q)).map (·.2)

def Table.trAt (tb : Table) (q : Nat) : Array TrLine := tb.trs.filter (·.q == q)

def words (l : String) : List String := (l.splitOn " ").filter (· != "")

def parseTable (text : String) : Except String Table := do
  let mut tb : Table := {}
  let mut tpSet := false
  for l in text.splitOn "\n" do
    let w := words l
    match w with
    | [] => pure ()
    | t :: rest =>
      if t.startsWith "#" then continue
      let nat (s : String) : Except String Nat :=
        match s.toNat? with | some x => pure x | none => throw s!"integer expected: {l}"
      let rat (s : String) : Except String Q :=
        match Q.parse s with | some x => pure x | none => throw s!"rational expected: {l}"
      match t, rest with
      | "d", [x] => if (← nat x) != 4 then throw "d must be 4"
      | "J", [x] => tb := { tb with j := ← nat x }
      | "T", [x] => tb := { tb with t := ← nat x }
      | "Tpend", [x] => tb := { tb with tp := ← nat x }; tpSet := true
      | "eps", [x] => tb := { tb with eps := ← rat x }
      | "rho", [x] => tb := { tb with rho := ← rat x }
      | "phi", [x] => tb := { tb with phi := ← rat x }
      | "kappa", [x] => tb := { tb with kappa := ← rat x }
      | "label", [q, n] => tb := { tb with labs := tb.labs.push (← nat q, n) }
      | "tr", [q, a, dl, b, p] =>
        tb := { tb with trs := tb.trs.push ⟨← nat q, a, ← nat dl, b, ← rat p⟩ }
      | "rounds", _ => pure ()
      | "prune", _ => pure ()
      | "h", _ => throw "h lines: not a table"
      | "plan", _ => pure ()
      | _, _ => throw s!"unknown line: {l}"
  if !tpSet then tb := { tb with tp := tb.t }
  return tb

structure Row where
  p : Q
  delta : Nat
  next : Nat

structure Chain where
  names : Array String
  rows : Array (Array Row)
  w : Array Q
  lump : Array Nat
  tailF : Nat
  tailB : Nat
  theta : Q

def buildChain (tb : Table) : Chain := Id.run do
  let j := tb.j
  let mut names : Array String := #["F", "B"]
  for q in [1:j] do
    for l in tb.labels q do names := names.push s!"{q}:{l}"
  for q in [1:j] do names := names.push s!"{q}:tail"
  for q in [1:j] do names := names.push s!"{q}:M"
  let idx (s : String) : Nat := (names.findIdx? (· == s)).getD 1000
  let lab (q : Nat) (l : String) : Nat := if q == j then 1 else idx s!"{q}:{l}"
  let tl (q : Nat) : Nat := if q == j then 1 else idx s!"{q}:tail"
  let mm (q : Nat) : Nat := if q == j then 1 else idx s!"{q}:M"
  let n := names.size
  let mut rows : Array (Array Row) := Array.replicate n #[]
  let ome := Q.sub Q.one tb.eps
  for r in tb.trAt 0 do
    rows := rows.modify 1 (·.push ⟨Q.mul ome r.p, r.delta, lab 1 r.dst⟩)
    for r2 in (tb.trAt 1).filter (·.src == r.dst) do
      rows := rows.modify 0 (·.push ⟨Q.mul (Q.mul ome r.p) r2.p, r.delta + r2.delta, lab 2 r2.dst⟩)
  for q in [1:j] do
    for r in tb.trAt q do
      rows := rows.modify (lab q r.src) (·.push ⟨r.p, r.delta, lab (q + 1) r.dst⟩)
    rows := rows.modify (tl q) (·.push ⟨Q.one, 0, tl (q + 1)⟩)
    let dmax := (tb.trAt q).foldl (fun a x => max a x.delta) 0
    let mut tau : Array Q := Array.replicate (dmax + 2) Q.zero
    for l in tb.labels q do
      for k in [0:dmax + 1] do
        let s := ((tb.trAt q).filter fun x => x.src == l && x.delta ≥ k).foldl (fun a x => Q.add a x.p) Q.zero
        if Q.lt tau[k]! s then tau := tau.set! k s
    for k in [0:dmax + 1] do
      let pk := Q.sub tau[k]! tau[k + 1]!
      if pk.n > 0 then rows := rows.modify (mm q) (·.push ⟨pk, k, mm (q + 1)⟩)
  -- potentials r_q(S) = sum P phi^delta r_(q+1)(S2), r_J(end) = 1
  let mut r : Array (Array (String × Q)) := Array.replicate (j + 1) #[]
  r := r.set! j #[("end", Q.one)]
  for q' in [0:j] do
    let q := j - 1 - q'
    let mut acc : Array (String × Q) := #[]
    for l in tb.labels q do
      let mut s := Q.zero
      for x in (tb.trAt q).filter (·.src == l) do
        let rn := ((r[q + 1]!).find? (·.1 == x.dst)).map (·.2) |>.getD Q.zero
        s := Q.add s (Q.mul (Q.mul x.p (Q.pow tb.phi x.delta)) rn)
      acc := acc.push (l, s)
    r := r.set! q acc
  let mut rm : Array Q := Array.replicate (j + 1) Q.one
  for q' in [1:j] do
    let q := j - q'
    let mut s := Q.zero
    for x in rows[mm q]! do
      s := Q.add s (Q.mul (Q.mul x.p (Q.pow tb.phi x.delta)) rm[q + 1]!)
    rm := rm.set! q s
  let mut w : Array Q := Array.replicate n Q.zero
  w := w.set! 0 (Q.pow tb.kappa j)
  w := w.set! 1 (Q.pow tb.kappa (j - 1))
  let mut lump : Array Nat := (Array.range n)
  for q in [1:j] do
    for l in tb.labels q do
      let rv := ((r[q]!).find? (·.1 == l)).map (·.2) |>.getD Q.zero
      w := w.set! (lab q l) (Q.mul (Q.pow tb.kappa (q - 1)) rv)
      lump := lump.set! (lab q l) (mm q)
    w := w.set! (tl q) (Q.pow tb.kappa (q - 1))
    w := w.set! (mm q) (Q.mul (Q.pow tb.kappa (q - 1)) rm[q]!)
  let theta := Q.sub (Q.mul (Q.ofNat 5) tb.phi) (Q.mul (Q.ofNat 4) tb.kappa)
  return { names, rows, w, lump, tailF := tl 2, tailB := tl 1, theta }

/-! Compositions. `C_L(n)` is the set of vectors of length `L` with sum at most `n`; the Lean lane
order sorts a vector `x` by `|x|`, then by its tail: `idx(x) = |C_L(|x| - 1)| + idx(tail x)`. -/

def binom (n k : Nat) : Nat := Id.run do
  let mut r := 1
  for i in [0:k] do r := r * (n - i) / (i + 1)
  return r

/-- `|C_L(n - 1)|`, so `0` at `n = 0`. -/
def cntm (len n : Nat) : Nat := if n == 0 then 0 else binom (n - 1 + len) len

/-- The vectors of length `len` with sum at most `t`, in lexicographic order (FORMAT.md). -/
def lexComps (len t : Nat) : Array (Array Nat) := Id.run do
  let mut res : Array (Array Nat) := #[#[]]
  for _ in [0:len] do
    let mut nx : Array (Array Nat) := #[]
    for v in res do
      let s := v.foldl (· + ·) 0
      for dd in [0:t - s + 1] do nx := nx.push (v.push dd)
    res := nx
  return res

/-- The Lean lane index of a vector. -/
partial def laneIdx (x : List Nat) : Nat :=
  match x with
  | [] => 0
  | _ :: tl => cntm x.length (x.foldl (· + ·) 0) + laneIdx tl

/-- `perm[i]`: the lane of the `i`-th vector of `C_q` in lexicographic order. -/
def lanePerm (j t q : Nat) : Array Nat := (lexComps (j - q + 1) t).map fun v => laneIdx v.toList

/-- The gathers of phase `q`, as lists of `(a, b, s)`: lanes `[a, b)` moved up by `s` lanes. -/
def gxList (j t q : Nat) : List (Nat × Nat × Nat) :=
  let L := j - q + 1
  (List.range t).map fun n => (cntm L n, cntm L (n + 1), cntm (L - 1) (n + 1))

def cpList (j t q f : Nat) : List (Nat × Nat × Nat) :=
  if q ≥ j then [] else
  let L := j - q + 1
  ((List.range (t + 1)).filter (· ≥ f)).map fun n => (cntm (L - 1) (n - f), cntm (L - 1) (n - f + 1), cntm L n)

end G3Tool
