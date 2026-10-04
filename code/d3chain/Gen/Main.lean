import FrogModel.D3.LaneD.K.Cover
import FrogModel.D3.LaneD.K.Seed
import FrogModel.D3.LaneD.K.Ext

/-!
# d3chain: the Lean data modules of the certificate of Proposition 15.1 (2) of the paper

`d3chain CERTDIR OUTROOT [-c] [-j N]` reads `CERTDIR/manifest.txt` (lines `SEED MASSES CERT`,
`STEP IN OUT`, `EXT IN OUT`, `CHECK IN OUT mode1`, in the order of the chain) and the `D3CERT 1` files it
names, and writes under `OUTROOT/FrogModel/D3/CertData/` the modules `FrogModel.D3.CertData.*` of the
Lean module system:

- `S/<name>.lean`, one per stored state (`S<h>` the seed and the output of a step at height `h`, `X<h>`
  the output of an extension at `h`, `T` the state of the CHECK line): `F`, the rows `0..E` (row `0`
  equal to `2^52` everywhere), slots `0..GM` of 64 bits, and `D`, the deficits `0..E` (deficit `0`
  equal to `2^52`), values at `2^-52`;
- `L/<name>.lean`, one per STEP line (`L<h>`, `h` the height of its input) and the CHECK line (`LT`):
  the names `dn`, `fn`, the hints `uD` (the deficit bounds, `K.deficitBounds`, compiled here) and `sq`
  (the square root witnesses), the line `line`, its parts `p0, p1, ...` and `ps`, the theorems
  `chk<i> : check (line.withPart p<i>) = true` and `cov : covers line ps = true` by `decide +kernel`, and
  `chks`, the parts collected in `AllP`. A cdf entry stored as `1` is named `1` (the term `1`), whatever
  its name in the certificate: the law of the term `S3` (Lemma 12.1 (2) of the paper), rounded up at
  `2^-64` per entry, can pass `1` in its last entries. A line with `E ≤ 32` is one part (every term);
  a line with `E = 64` is cut into parts of 16 rows (mask 5), one part per (A) family and chunk of 8
  values of `v` (mask 8), one part per (B) family (mask 2);
- `Seed.lean`: `seed_ok : K.seedCheck M1Data.massPk F D hint = true` on the seed state, `hint` the
  witnesses for `N = 101 + k`; `Ext.lean`, one theorem `ext_ok` per extension (`Ext<h>` in it):
  `K.extCheck E0 G0 E GM h Fi Di Fo Do hint = true`;
- `LeT.lean`: `le_ok` (the last state of the chain is at most `T`), `wf_ok` (the shape of `T`),
  `d1_ok`, `d62_ok` (`delta_T(1) ≤ 2/5`, `delta_T(62) ≤ 7045771/88917100` on the stored slots);
- `B/B<i>.lean`: the segments of at most 50 consecutive steps of one parameter set, `seg`;
- `Main.lean`: `certS1_stored`, the chain of Proposition 15.1 (2) from the seed of the masses of
  `M1Data.massPk`, given the soundness statements of the step, seed and extension checks.

`-c` also runs the compiled checkers on every part, the seed and the extension, and prints the failure
counts (each must be `0`); `-j N` computes `N` lines at once. Every number the kernel reads is written as
a `nat_lit` in hexadecimal. The program checks the structure of the manifest and nothing else: a wrong
module makes a kernel check fail.
-/

open FrogModel.D3.LaneD.K

def words (s : String) : List String := (s.splitOn " ").filter (· ≠ "")

/-- `sum over i of xs[i] 2^(w i)`. -/
def pack (w : Nat) (xs : List Nat) : Nat :=
  (xs.foldl (fun (acc : Nat × Nat) x => (acc.1 + x * 2 ^ (w * acc.2), acc.2 + 1)) (0, 0)).1

def hexDigits (w : Nat) (x : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 x)
  String.ofList (List.replicate (w / 4 - s.length) '0') ++ s

/-- The raw literal of `pack w xs` (`w` a multiple of 4), slot by slot, high slot first. -/
def litSlots (w : Nat) (xs : List Nat) : String := Id.run do
  let ys := (xs.reverse.dropWhile (· == 0))
  if ys.isEmpty then return "(nat_lit 0)"
  let mut s := "(nat_lit 0x" ++ String.ofList (Nat.toDigits 16 ys.head!)
  for y in ys.tail do
    s := s ++ hexDigits w y
  return s ++ ")"

def litNat (x : Nat) : String := "(nat_lit 0x" ++ String.ofList (Nat.toDigits 16 x) ++ ")"

def lst (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

structure St where
  kind : String := ""
  h : Nat := 0
  E : Nat := 0
  GM : Nat := 0
  VM : Nat := 0
  JM : Nat := 0
  lo : Nat := 0
  hi : Nat := 0
  D : Array Nat := #[]
  Dn : Array String := #[]
  F : Array (List Nat) := #[]
  Fn : Array (List String) := #[]
  deriving Inhabited

def parse (path : String) : IO St := do
  let ls ← IO.FS.lines path
  if ls[0]? != some "D3CERT 1" then throw (IO.userError s!"{path}: not a D3CERT 1 file")
  let mut s : St := {}
  for l in ls do
    match words l with
    | ["kind", k] => s := { s with kind := k }
    | ["height", h] => s := { s with h := h.toNat! }
    | "params" :: e :: gm :: vm :: jm :: _ =>
      s := { s with E := e.toNat!, GM := gm.toNat!, VM := vm.toNat!, JM := jm.toNat! }
      s := { s with D := Array.replicate (s.E + 1) 0, Dn := Array.replicate (s.E + 1) "",
                    F := Array.replicate (s.E + 1) [], Fn := Array.replicate (s.E + 1) [] }
    | ["children", a, b] => s := { s with lo := a.toNat!, hi := b.toNat! }
    | "D" :: k :: n :: rest => s := { s with D := s.D.set! k.toNat! n.toNat!, Dn := s.Dn.set! k.toNat! (rest.headD "") }
    | "F" :: k :: ns => s := { s with F := s.F.set! k.toNat! (ns.map String.toNat!) }
    | "N" :: k :: ns => s := { s with Fn := s.Fn.set! k.toNat! ns }
    | _ => pure ()
  for k in [1:s.E + 1] do
    if s.F[k]!.length != s.GM + 1 then throw (IO.userError s!"{path}: row {k} has {s.F[k]!.length} entries")
  -- a cdf entry stored as `1` is named `1`: the term `1` holds there, while the law of the term `S3`
  -- (Lemma 12.1 (2) of the paper) rounded up (`2^-64` per entry) can pass `1` in its last entries
  let Fn := (s.F.zip s.Fn).map fun (r, n) =>
    if n.isEmpty then n else (r.zip n).map fun (x, nm) => if x ≥ 2 ^ 52 then "1" else nm
  return { s with Fn }

def one : Nat := 2 ^ 52

def rowSlots (s : St) : List (List Nat) :=
  List.replicate (s.GM + 1) one :: (List.range s.E).map (fun i => s.F[i + 1]!)

def rows (s : St) : List Nat := (rowSlots s).map (pack 64)

def dSlots (s : St) : List Nat := one :: (List.range s.E).map (fun i => s.D[i + 1]!)

def dvec (s : St) : Nat := pack 64 (dSlots s)

def dcode (nm : String) : Nat :=
  if nm = "T" then 1 else if nm = "P" then 2 else if nm = "S2" then 4
  else if nm.startsWith "L" then
    match (nm.drop 1).toString.splitOn "." with
    | [j, k] => 3 + 256 * j.toNat! + 2 ^ 24 * k.toNat!
    | _ => 255
  else 255

def fcode (nm : String) : Nat :=
  if nm = "1" then 0 else if nm = "C" then 1 else if nm = "L" then 2 else if nm = "S3" then 5
  else if nm = "J" then 6 else if nm = "G" then 7
  else if nm.startsWith "A" then 4 + 256 * (nm.drop 1).toString.toNat!
  else 255

def isqrtUp (n : Nat) : Nat := Id.run do
  let mut r := n.sqrt
  while r * r < n do r := r + 1
  return r

/-- The witnesses `rho_k`, `3 rho_k^2 ≥ (base + k) 2^256`, `k = 1..E`, slot `0` zero. -/
def sqSlots (base E : Nat) : List Nat :=
  (List.range (E + 1)).map (fun k => if k = 0 then 0 else isqrtUp (((base + k) * 2 ^ 256 + 2) / 3))

def header (imports : List String) (doc : String) (ns : String) (opens : String) : String :=
  "module\n\n" ++ String.join (imports.map fun m => s!"public import {m}\n") ++
    "\n@[expose] public section\n\n/-! " ++ doc ++ " (written by d3chain) -/\n\nnamespace " ++ ns ++
    "\n\n" ++ (if opens.isEmpty then "" else "open " ++ opens ++ "\n\n")

def root : String := "FrogModel.D3.CertData"

/-- A state module. -/
def stateModule (name : String) (s : St) (src : String) : String :=
  header [] s!"The stored state `{name}` ({src}, height {s.h}, `(E, GM) = ({s.E}, {s.GM})`)" s!"{root}.{name}" "" ++
    "noncomputable def F : List Nat := " ++ lst ((rowSlots s).map (litSlots 64)) ++ "\n\n" ++
    "noncomputable def D : Nat := " ++ litSlots 64 (dSlots s) ++ "\n\n" ++
    s!"end {root}.{name}\n"

/-- A part: `(d0, d1, f0, f1, mask, famsA, famsB, shsB)`. -/
abbrev PartD := Nat × Nat × Nat × Nat × Nat × List (Nat × Nat) × List Nat × List Nat

def toPart (p : PartD) : Part :=
  let (d0, d1, f0, f1, m, fa, fb, sb) := p
  ⟨d0, d1, f0, f1, m, fa, fb, sb⟩

def partLit (p : PartD) : String :=
  let (d0, d1, f0, f1, m, fa, fb, sb) := p
  s!"⟨{d0}, {d1}, {f0}, {f1}, {m}, " ++ lst (fa.map fun (a, b) => s!"({a}, {b})") ++ ", " ++
    lst (fb.map toString) ++ ", " ++ lst (sb.map toString) ++ "⟩"

/-- The data of one line: the line (with the full part) and its parts. -/
structure LineD where
  name : String
  inName : String
  outName : String
  so : St
  line : Line
  dnS : List Nat
  fnS : List (List Nat)
  uDS : List Nat
  sqS : List Nat
  parts : List PartD

def mkLine (name inName outName : String) (si so : St) : LineD :=
  let E := so.E
  let dnS := 0 :: (List.range E).map (fun i => dcode so.Dn[i + 1]!)
  let fnS := [] :: (List.range E).map (fun i => so.Fn[i + 1]!.map fcode)
  let dn := pack 64 dnS
  let fn := fnS.map (pack 32)
  -- (A) families of the rows `f0..f1`: (sh, bitmask of v), sh = n0 - q - 1
  let famsAOf (f0 f1 : Nat) : List (Nat × Nat) :=
    let aEntries : List (Nat × Nat) := ((List.range E).filter (fun i => f0 ≤ i + 1 && i + 1 ≤ f1)).flatMap (fun i =>
      ((so.Fn[i + 1]!).zipIdx.filter (·.1.startsWith "A")).map (fun (s, v) =>
        ((s.drop 1).toString.toNat! - (i + 2) - 1, v)))
    let shs := (aEntries.map (·.1)).eraseDups
    shs.map (fun sh => (sh, (aEntries.filter (·.1 = sh)).foldl (fun m (_, v) => m ||| (1 <<< v)) 0))
  -- (B) families of the deficits `d0..d1`: J + 2^16 (K - q - 1)
  let famsBOf (d0 d1 : Nat) : List Nat := ((List.range E).filterMap (fun i =>
    let c := dcode so.Dn[i + 1]!
    if d0 ≤ i + 1 && i + 1 ≤ d1 && c % 256 = 3 then some ((c / 256) % 65536 + 65536 * (c / 2 ^ 24 - (i + 2) - 1))
    else none)).eraseDups
  let shsOf (fb : List Nat) : List Nat := (fb.map (· / 65536)).eraseDups
  let sqS := sqSlots (so.lo + 2) E
  let fA := famsAOf 1 E
  let fB := famsBOf 1 E
  let L0 : Line := ⟨E, so.GM, so.VM, so.JM, so.lo, so.hi, 1, E, 1, E, 15, rows si, dvec si, rows so, dvec so,
    dn, fn, fA, fB, shsOf fB, 0, pack 256 sqS⟩
  let uD := deficitBounds L0
  let uDS := (List.range (E + 1)).map (fun j => slot 128 uD j)
  let chunks (used : Nat) : List Nat :=
    let bits := (List.range 64).filter (fun v => (used >>> v) % 2 = 1)
    (List.range ((bits.length + 7) / 8)).map (fun i =>
      ((bits.drop (i * 8)).take 8).foldl (fun m v => m ||| (1 <<< v)) 0)
  let parts : List PartD :=
    if E ≤ 32 then [(1, E, 1, E, 15, fA, fB, shsOf fB)]
    else
      ((List.range ((E + 15) / 16)).map (fun k =>
        let lo := 1 + k * 16; let hi := min E ((k + 1) * 16)
        (lo, hi, lo, hi, 5, [], [], []))) ++
      (fA.flatMap (fun f => (chunks f.2).map (fun u => (1, 0, 1, E, 8, [(f.1, u)], [], [])))) ++
      (fB.map (fun f => (1, E, 1, 0, 2, [], [f], [f / 65536])))
  { name, inName, outName, so, line := { L0 with uD }, dnS, fnS, uDS, sqS, parts }

def lineModule (d : LineD) : String :=
  let so := d.so
  let L := d.line
  let nps := d.parts.length
  let chkNames := (List.range nps).map (s!"chk{·}")
  header ["FrogModel.D3.Chain.Basic", s!"{root}.S.{d.inName}", s!"{root}.S.{d.outName}"]
      s!"The line `{d.inName}` to `{d.outName}` (children heights `{so.lo}..{so.hi}`, `(E, GM, VM, JM) = ({so.E}, {so.GM}, {so.VM}, {so.JM})`), parts: {nps}"
      s!"{root}.{d.name}" "FrogModel.D3.LaneD.K FrogModel.D3.Chain" ++
    "def dn : Nat := " ++ litSlots 64 d.dnS ++ "\n\n" ++
    "def fn : List Nat := " ++ lst (d.fnS.map (litSlots 32)) ++ "\n\n" ++
    "def uD : Nat := " ++ litSlots 128 d.uDS ++ "\n\n" ++
    "def sq : Nat := " ++ litSlots 256 d.sqS ++ "\n\n" ++
    s!"noncomputable def line : Line :=\n  ⟨{L.E}, {L.GM}, {L.VM}, {L.JM}, {L.a}, {L.b}, 0, 0, 0, 0, 0, {d.inName}.F, {d.inName}.D, {d.outName}.F, {d.outName}.D, dn, fn,\n    [], [], [], uD, sq⟩\n\n" ++
    String.join (d.parts.zipIdx.map fun (p, i) => s!"def p{i} : Part := {partLit p}\n") ++ "\n" ++
    "def ps : List Part := " ++ lst ((List.range nps).map (s!"p{·}")) ++ "\n\n" ++
    "set_option Elab.async false\n\n" ++
    String.join ((List.range nps).map fun i =>
      s!"theorem chk{i} : check (line.withPart p{i}) = true := by decide +kernel\n\n") ++
    "theorem chks : AllP (fun p => check (line.withPart p) = true) ps :=\n  ⟨" ++
      ", ".intercalate (chkNames ++ ["trivial"]) ++ "⟩\n\n" ++
    "theorem cov : covers line ps = true := by decide +kernel\n\n" ++
    s!"end {root}.{d.name}\n"

inductive Item where
  | seed (masses cert : String)
  | step (inp out : String)
  | ext (inp out : String)
  | check (inp out : String)

def parseManifest (path : String) : IO (List Item) := do
  let ls ← IO.FS.lines path
  let mut items : Array Item := #[]
  for l in ls do
    match words l with
    | ["SEED", m, c] => items := items.push (.seed m c)
    | ["STEP", i, o] => items := items.push (.step i o)
    | ["EXT", i, o] => items := items.push (.ext i o)
    | ["CHECK", i, o, "mode1"] => items := items.push (.check i o)
    | [] => pure ()
    | w => if (w.headD "").startsWith "#" then pure () else throw (IO.userError s!"manifest: unexpected line {l}")
  return items.toList

def writeFile (outRoot rel body : String) : IO Unit := do
  let p : System.FilePath := outRoot ++ "/FrogModel/D3/CertData/" ++ rel
  if let some d := p.parent then IO.FS.createDirAll d
  IO.FS.writeFile p body

/-- The compiled check of every part of a line: the failure counts. -/
def checkLine (d : LineD) : List Nat := d.parts.map fun p => failures (d.line.withPart (toPart p))

/-- `d3chain --debug IN OUT`: the failure counts of the line `IN` to `OUT`, deficit by deficit (mask 3)
and row by row (mask 4, then the entries `A` with mask 8), every nonzero count printed. -/
def debugLine (inp outp : String) : IO UInt32 := do
  let si ← parse inp
  let so ← parse outp
  let d := mkLine "dbg" "I" "O" si so
  let (_, _, _, _, _, fA, fB, sB) := d.parts.headD (0, 0, 0, 0, 0, [], [], [])
  let fA := if d.parts.length == 1 then fA else d.parts.flatMap (fun p => p.2.2.2.2.2.1)
  let fB := if d.parts.length == 1 then fB else d.parts.flatMap (fun p => p.2.2.2.2.2.2.1)
  let sB := if d.parts.length == 1 then sB else (fB.map (· / 65536)).eraseDups
  let E := so.E
  for j in [1:E + 1] do
    let n := failures (d.line.withPart ⟨j, j, 1, 0, 3, [], fB, sB⟩)
    if n != 0 then IO.println s!"deficit {j} ({so.Dn[j]!}): {n}"
  for j in [1:E + 1] do
    let n := failures (d.line.withPart ⟨1, 0, j, j, 4, [], [], []⟩)
    if n != 0 then
      IO.println s!"row {j} (mask 4): {n}"
      -- the entry `v` renamed `1` (code 0): the count drops when `v` fails and its value is `2^52`
      for v in [0:so.GM + 1] do
        let row := getN d.line.fn j
        let fn2 := d.line.fn.set j (row - (slot 32 row v) * 2 ^ (32 * v))
        let n2 := failures ({ d.line with fn := fn2 }.withPart ⟨1, 0, j, j, 4, [], [], []⟩)
        if n2 < n then IO.println s!"  v {v}: {so.Fn[j]!.getD v ""} value {so.F[j]!.getD v 0}, renamed 1: {n2}"
    for (sh, used) in fA do
      for v in [0:64] do
        if (used >>> v) % 2 = 1 then
          let n := failures (d.line.withPart ⟨1, 0, j, j, 8, [(sh, 1 <<< v)], [], []⟩)
          if n != 0 then IO.println s!"row {j} A sh {sh} v {v}: {n}"
  return 0

def main (args : List String) : IO UInt32 := do
  if let ["--debug", i, o] := args then return ← debugLine i o
  let certDir :: outRoot :: opts := args | do
    IO.eprintln "usage: d3chain CERTDIR OUTROOT [-c] [-j N]"; return 2
  let doCheck := opts.contains "-c"
  let jobs := match opts.dropWhile (· != "-j") with
    | _ :: n :: _ => n.toNat!
    | _ => 1
  let items ← parseManifest (certDir ++ "/manifest.txt")
  -- the states, in the order of the chain, with their names
  let mut states : Array (String × String × St) := #[]   -- (name, file, state)
  let mut cur : Option (String × St) := none            -- the last state of the chain
  let mut lines : Array (String × String × String × St × St) := #[]  -- (name, in, out, si, so)
  let mut exts : Array (String × String × St × St) := #[] -- (in, out, si, so)
  let mut seed : Option (String × St) := none
  let mut checkL : Option (String × String × St × St) := none
  let mut chain : Array String := #[]                  -- the items of Main, in order
  for it in items do
    match it with
    | .seed _ c =>
      let s ← parse (certDir ++ "/" ++ c)
      let nm := s!"S{s.h}"
      states := states.push (nm, c, s); cur := some (nm, s); seed := some (nm, s)
    | .step i o =>
      let some (inN, si) := cur | throw (IO.userError "STEP before the seed")
      let s ← parse (certDir ++ "/" ++ o)
      if s.kind != "STEP" || s.h != si.h + 1 || s.lo != si.h || s.hi != si.h then
        throw (IO.userError s!"STEP {i} -> {o}: heights {si.h} -> {s.h}, children {s.lo} {s.hi}")
      let nm := s!"S{s.h}"
      let ln := s!"L{si.h}"
      if (lines.any (·.1 == ln)) then throw (IO.userError s!"two lines named {ln}")
      states := states.push (nm, o, s); lines := lines.push (ln, inN, nm, si, s)
      chain := chain.push ln; cur := some (nm, s)
    | .ext i o =>
      let some (inN, si) := cur | throw (IO.userError "EXT before the seed")
      let s ← parse (certDir ++ "/" ++ o)
      if s.kind != "EXT" || s.h != si.h then throw (IO.userError s!"EXT {i} -> {o}: heights {si.h} -> {s.h}")
      let nm := s!"X{s.h}"
      states := states.push (nm, o, s); exts := exts.push (inN, nm, si, s)
      chain := chain.push ("E:" ++ nm); cur := some (nm, s)
    | .check _ o =>
      let some (inN, si) := cur | throw (IO.userError "CHECK before the seed")
      let s ← parse (certDir ++ "/" ++ o)
      if s.kind != "CHECK" || s.lo != si.h then throw (IO.userError s!"CHECK {o}: children {s.lo}, last height {si.h}")
      states := states.push ("T", o, s); checkL := some (inN, "T", si, s)
  let some (seedN, seedS) := seed | throw (IO.userError "no SEED")
  let some (lastN, _, lastS, tS) := checkL | throw (IO.userError "no CHECK")
  -- state modules
  for (nm, file, s) in states do
    writeFile outRoot s!"S/{nm}.lean" (stateModule nm s file)
  IO.println s!"{states.size} state modules"
  -- line modules, `jobs` at a time
  let allLines : Array (String × String × String × St × St) := lines.push ("LT", "T", "T", tS, tS)
  let mut failed := 0
  let mut i := 0
  while i < allLines.size do
    let batch := allLines.extract i (i + jobs)
    let tasks ← batch.mapM fun (ln, inN, outN, si, so) => IO.asTask (prio := .dedicated) do
      let d := mkLine ln inN outN si so
      writeFile outRoot s!"L/{ln}.lean" (lineModule d)
      let fails := if doCheck then checkLine d else []
      return (ln, d.parts.length, fails)
    for t in tasks do
      match ← IO.wait t with
      | .ok (ln, np, fails) =>
        if doCheck then
          IO.println s!"{ln}: {np} parts, failures {fails}"
          if fails.any (· != 0) then failed := failed + 1
        else IO.println s!"{ln}: {np} parts"
      | .error e => throw e
    i := i + jobs
  -- the seed
  let seedHint := pack 256 (sqSlots 101 seedS.E)
  writeFile outRoot "Seed.lean" (header ["FrogModel.D3.LaneD.K.Seed", "FrogModel.D3.M1Data.Top", s!"{root}.S.{seedN}"]
      s!"The seed state `{seedN}` against the masses `M1Data.massPk`" s!"{root}.Seed" "FrogModel.D3.LaneD.K" ++
    "def hint : Nat := " ++ litSlots 256 (sqSlots 101 seedS.E) ++ "\n\n" ++
    "set_option Elab.async false\n\n" ++
    s!"theorem seed_ok : seedCheck FrogModel.D3.M1Data.massPk {seedN}.F {seedN}.D hint = true := by decide +kernel\n\n" ++
    s!"end {root}.Seed\n")
  if doCheck then
    let masses ← IO.FS.lines (certDir ++ "/masses100.txt")
    let mut n : Array Nat := Array.replicate (32 * 49) 0
    for l in masses do
      match words l with
      | ["MASS", "100", k, x, v] =>
        let k := k.toNat!; let x := x.toNat!
        if 1 ≤ k ∧ k ≤ 32 ∧ x ≤ 48 then n := n.set! (49 * (k - 1) + x) v.toNat!
      | _ => pure ()
    let ok := seedCheck (pack 64 n.toList) (rows seedS) (dvec seedS) seedHint
    IO.println s!"seed (masses100.txt): {ok}"
    if !ok then failed := failed + 1
  -- the extensions
  let extBody := String.join (exts.toList.map fun (inN, outN, si, so) =>
    let hint := sqSlots (so.h + 1) so.E
    s!"def hint{outN} : Nat := " ++ litSlots 256 hint ++ "\n\n" ++
    s!"theorem ext_ok{outN} : extCheck {si.E} {si.GM} {so.E} {so.GM} {so.h} {inN}.F {inN}.D {outN}.F {outN}.D hint{outN} = true :=\n  by decide +kernel\n\n")
  writeFile outRoot "Ext.lean" (header (["FrogModel.D3.LaneD.K.Ext"] ++ exts.toList.flatMap (fun (i, o, _, _) => [s!"{root}.S.{i}", s!"{root}.S.{o}"]))
      "The extensions" s!"{root}.Ext" "FrogModel.D3.LaneD.K" ++ "set_option Elab.async false\n\n" ++ extBody ++ s!"end {root}.Ext\n")
  if doCheck then
    for (_, outN, si, so) in exts do
      let ok := extCheck si.E si.GM so.E so.GM so.h (rows si) (dvec si) (rows so) (dvec so) (pack 256 (sqSlots (so.h + 1) so.E))
      IO.println s!"ext {outN}: {ok}"
      if !ok then failed := failed + 1
  -- the comparisons of T
  writeFile outRoot "LeT.lean" (header ["FrogModel.D3.Chain.Basic", s!"{root}.S.{lastN}", s!"{root}.S.T"]
      s!"The CHECK state `T`: at least `{lastN}`, its shape, and its deficits 1 and 62" s!"{root}.LeT" "FrogModel.D3.LaneD.K FrogModel.D3.Chain" ++
    "set_option Elab.async false\n\n" ++
    s!"theorem le_ok : leCheck {tS.E} {tS.GM} {lastN}.F {lastN}.D T.F T.D = true := by decide +kernel\n\n" ++
    s!"theorem wf_ok : wfCheck {tS.E} {tS.GM} T.F T.D = true := by decide +kernel\n\n" ++
    "theorem d1_ok : slot 64 T.D 1 * 5 ≤ 2 * 2 ^ 52 := by decide +kernel\n\n" ++
    "theorem d62_ok : slot 64 T.D 62 * 88917100 ≤ 7045771 * 2 ^ 52 := by decide +kernel\n\n" ++
    s!"end {root}.LeT\n")
  if doCheck then
    let le := FrogModel.D3.LaneD.K.allN (tS.E + 1) (fun k => allN (tS.GM + 1) (fun g =>
      Nat.ble (slot 64 (getN (rows lastS) k) g) (slot 64 (getN (rows tS) k) g)))
    IO.println s!"T at least {lastN} (rows): {le}"
  -- the segments: runs of consecutive steps of one parameter set, at most 50 each
  let mut blocks : Array (List String) := #[]
  let mut curB : List String := []
  let mut curP : Option (Nat × Nat × Nat × Nat) := none
  let mut mainItems : Array String := #[]
  for c in chain do
    if c.startsWith "E:" then
      if !curB.isEmpty then blocks := blocks.push curB.reverse; mainItems := mainItems.push s!"B{blocks.size - 1}"
      curB := []; curP := none
      mainItems := mainItems.push c
    else
      let some (_, _, _, _, so) := lines.find? (·.1 == c) | throw (IO.userError s!"no line {c}")
      let p := (so.E, so.GM, so.VM, so.JM)
      if curP != some p || curB.length == 50 then
        if !curB.isEmpty then blocks := blocks.push curB.reverse; mainItems := mainItems.push s!"B{blocks.size - 1}"
        curB := []
      curB := c :: curB; curP := some p
  if !curB.isEmpty then blocks := blocks.push curB.reverse; mainItems := mainItems.push s!"B{blocks.size - 1}"
  let pName (so : St) : IO String :=
    if (so.E, so.GM, so.VM, so.JM) == (32, 96, 16, 12) then pure "P0"
    else if (so.E, so.GM, so.VM, so.JM) == (64, 224, 32, 24) then pure "P1"
    else throw (IO.userError s!"parameters ({so.E}, {so.GM}, {so.VM}, {so.JM}) not P0 or P1")
  let mut bi := 0
  for b in blocks do
    let ls := b.map fun ln => (lines.find? (·.1 == ln)).get!
    let (_, firstIn, _, si0, so0) := ls.head!
    let (_, _, lastOut, _, soL) := ls.getLast!
    let P ← pName so0
    let links := String.join (ls.map fun (ln, _, _, si, _) =>
      s!"  have r := plain_link hs {P} {si.h} {ln}.line {ln}.ps ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ {P}_OK {P}_E64 {P}_G256\n    {ln}.chks {ln}.cov X r\n")
    writeFile outRoot s!"B/B{bi}.lean" (header (["FrogModel.D3.Chain.Link"] ++ ls.map (fun l => s!"{root}.L.{l.1}"))
        s!"The steps `{firstIn}` to `{lastOut}`" s!"{root}.B{bi}" "FrogModel.D3.Iface FrogModel.D3.Chain" ++
      s!"theorem seg (hs : StepSoundT) (X : StParams × ℕ × State) (r : CertReach X {P} {si0.h} {firstIn}.F {firstIn}.D) :\n    CertReach X {P} {soL.h} {lastOut}.F {lastOut}.D :=\n" ++
      links ++ "  r\n\n" ++ s!"end {root}.B{bi}\n")
    bi := bi + 1
  -- Main
  let mut steps : String := ""
  for c in mainItems do
    if c.startsWith "E:" then
      let nm := (c.drop 2).toString
      let some (inN, _, si, so) := exts.find? (·.2.1 == nm) | throw (IO.userError s!"no extension {nm}")
      let Pi ← pName si
      let some (_, _, _, _, so1) := lines.find? (·.2.1 == nm) | throw (IO.userError s!"no step after {nm}")
      let Po ← pName so1
      steps := steps ++ s!"  have r := ext_link hx {Pi} {Po} {so.h} {inN}.F {inN}.D {nm}.F {nm}.D Ext.hint{nm} Ext.ext_ok{nm} _ r\n"
    else
      steps := steps ++ s!"  have r := {c}.seg hs _ r\n"
  let PT ← pName tS
  writeFile outRoot "Main.lean" (header (["FrogModel.D3.CertData.Seed", "FrogModel.D3.CertData.Ext", "FrogModel.D3.CertData.LeT",
        s!"{root}.L.LT"] ++ (List.range blocks.size).map (s!"{root}.B.B{·}"))
      "(CertS_1) from the stored certificate" root "FrogModel.D3.Iface FrogModel.D3.LaneD FrogModel.D3.Chain" ++
    "/-- (CertS_1) from the seed of the masses `M1Data.massPk`, given the soundness of the checks. -/\n" ++
    "theorem certS1_stored (hs : StepSoundT) (hsd : SeedSoundT) (hx : ExtSoundT) (W : ℕ → ℕ → ℝ)\n" ++
    "    (hW : ∀ k, 1 ≤ k → k ≤ 32 → ∀ x ≤ 48,\n" ++
    "      W k x = (((M1Data.massPk >>> (64 * (49 * (k - 1) + x))) % 2 ^ 64 : ℕ) : ℝ) / 2 ^ 62) :\n" ++
    "    CertS1 (seedState 48 100 96 W) := by\n" ++
    s!"  obtain ⟨hle, r⟩ := seed_start hsd M1Data.massPk {seedN}.F {seedN}.D Seed.hint Seed.seed_ok W hW\n" ++
    steps ++
    s!"  exact certS1_of hs W {seedN}.F {seedN}.D hle {PT} {lastS.h} {lastN}.F {lastN}.D r T.F T.D LeT.le_ok LeT.wf_ok\n" ++
    s!"    LT.line LT.ps ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ {PT}_OK {PT}_E64 {PT}_G256 LT.chks LT.cov\n" ++
    "    (by decide) (by decide) LeT.d1_ok LeT.d62_ok\n\n" ++
    s!"end {root}\n")
  IO.println s!"{allLines.size} line modules, {blocks.size} segments, {exts.size} extensions"
  if failed != 0 then IO.println s!"FAILED: {failed}"; return 1
  return 0
