import FrogModel.G3K.Spec
import G3Tool.Parse

/-!
# g3k: the Lean modules of the data of a certificate

`g3k TABLE DATA OUTDIR NAME` reads the table and the version 4 data file (uncompressed), packs V'
and W' in the lanes of the checker, builds the tree of entries (`FrogModel.G3K.Tree`), and writes
it under `OUTDIR/FrogModel/G3Q/NAME/` as modules `FrogModel.G3Q.NAME.*` of the Lean module system
(`module`, `public import`, `@[expose] public section`), declarations in the namespace
`FrogModel.G3Q`: data modules `D0.lean`, `D1.lean`, ... (whole chunks each, at most 5000000 bytes
of source per module), `Data.lean` (the nodes above the chunks and `theTree`), theorem modules
`Thm0.lean`, `Thm1.lean`, ... (five theorems each, one theorem `allF (stateOKF theTree) u = true`
by `decide +kernel` per chunk `u`), and `All.lean` (`checkAllF theTree = true`, chained from the
chunk theorems by `allF_node`). The chunks cut the states, in the order of their keys, into runs
of at most 20000 raw moves. On the way it runs the compiled reference checker
`FrogModel.G3K.Spec.stateOK` on every chunk and prints the result, which the proof does not use.
-/

open G3Tool

namespace G3KTool

structure St where
  key : Nat
  flag : Nat
  q : Nat
  file : Nat
deriving Inhabited

def natOf (s : String) : Nat := s.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

/-- `Σ_l a[l] 2^(W l)` for `l ∈ [lo, hi)`, by halves. -/
partial def packRange (a : Array Nat) (W lo hi : Nat) : Nat :=
  if hi ≤ lo then 0 else if hi == lo + 1 then a[lo]! else
  let mid := (lo + hi) / 2
  packRange a W lo mid + packRange a W mid hi * 2 ^ (W * (mid - lo))

def hexLane (v W : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (W / 4 - s.length) '0') ++ s

/-- The raw literal of the lanes `a` of `W` bits. -/
def hexLit (a : Array Nat) (W : Nat) : String := Id.run do
  if a.all (· == 0) then return "(nat_lit 0)"
  let mut s := "(nat_lit 0x"
  let mut started := false
  for l in [0:a.size] do
    let h := hexLane a[a.size - 1 - l]! W
    if started then s := s ++ h
    else if a[a.size - 1 - l]! != 0 then
      s := s ++ String.ofList (Nat.toDigits 16 a[a.size - 1 - l]!); started := true
  return s ++ ")"

/-- The value term of V': one literal, or four (`cat4`, 124 lanes each) for 495 lanes. -/
def vTerm (lanes : Array Nat) : String :=
  if lanes.size ≤ 124 then hexLit lanes 96 else
  let part (i : Nat) := hexLit (lanes.extract (124 * i) (124 * i + 124)) 96
  s!"(cat4 {part 0} {part 1} {part 2} {part 3})"

/-- The moves of the state of key `k` as FORMAT.md lists them (the exit, one per row transition
of each distinct child state, one per tail atom), stops p' > T' included: the raw count. -/
def rawMoves (ch : Chain) (tb : Table) (k : Nat) : Nat := Id.run do
  let p := k % 128
  let cs := #[k / 268435456 % 128, k / 2097152 % 128, k / 16384 % 128, k / 128 % 128]
  let mut n := 1
  for a in [0:4] do
    if a > 0 && cs[a]! == cs[a - 1]! then continue
    let c := cs[a]!
    n := n + ch.rows[c]!.size
    if c ≤ 1 then n := n + (tb.tp + 1 - (p + tb.t))
  return n

/-- The balanced tree over the sorted entries `[lo, hi)`. -/
partial def build (ents : Array FrogModel.G3K.E) (lo hi : Nat) : FrogModel.G3K.Tree :=
  if hi ≤ lo + 1 then .leaf ents[lo]! else
  let mid := (lo + hi) / 2
  .node ents[mid]!.key (build ents lo mid) (build ents mid hi)

/-- The tree over the chunks `[i, j)` of start indices `st` (with the end `st[j]`). -/
partial def buildTop (ents : Array FrogModel.G3K.E) (st : Array Nat) (i j : Nat) : FrogModel.G3K.Tree :=
  if j ≤ i + 1 then build ents st[i]! st[i + 1]! else
  let mid := (i + j) / 2
  .node ents[st[mid]!]!.key (buildTop ents st i mid) (buildTop ents st mid j)

end G3KTool

open G3KTool

def main (args : List String) : IO UInt32 := do
  let (tabPath, dataPath, outDir, name) ← match args with
    | [t, d, o, nm] => pure (t, d, o, nm)
    | _ => do IO.eprintln "usage: g3k TABLE DATA OUTDIR NAME"; return 2
  let tb ← match parseTable (← IO.FS.readFile tabPath) with
    | .ok tb => pure tb
    | .error e => do IO.eprintln e; return 1
  let ch := buildChain tb
  let j := tb.j
  let t := tb.t
  let perms : Array (Array Nat) := (Array.range (j + 1)).map fun q => if q == 0 then #[] else lanePerm j t q
  let lines ← IO.FS.lines dataPath
  let mut sts : Array St := #[]
  let mut vRaw : Array (Array Nat) := #[]
  let mut wRaw : Array (Array Nat) := #[]
  for l in lines do
    match words l with
    | "state" :: k :: q :: p :: h :: names =>
      let cs := (names.map fun s => (ch.names.findIdx? (· == s)).getD 127).toArray.qsort (· < ·)
      let key := FrogModel.G3K.Spec.enc (natOf q) cs[0]! cs[1]! cs[2]! cs[3]! (natOf p)
      sts := sts.push ⟨key, natOf h, natOf q, natOf k⟩
    | "V" :: _ :: ns => vRaw := vRaw.push (ns.toArray.map natOf)
    | "W" :: _ :: ns => wRaw := wRaw.push (ns.toArray.map natOf)
    | _ => pure ()
  IO.println s!"read {sts.size} states, {vRaw.size} V lines, {wRaw.size} W lines"
  if vRaw.size != sts.size || wRaw.size != sts.size then
    IO.eprintln "V or W lines missing"; return 1
  let sorted := sts.qsort (fun a b => a.key < b.key)
  let n := sorted.size
  let mut ents : Array FrogModel.G3K.E := #[]
  let mut vLanes : Array (Array Nat) := #[]
  let mut maxV := 0
  let mut maxW := 0
  for s in sorted do
    let raw := vRaw[s.file]!
    let pm := perms[s.q]!
    let mut lanes := Array.replicate raw.size 0
    for i in [0:raw.size] do lanes := lanes.set! pm[i]! raw[i]!
    let wl := wRaw[s.file]!
    maxV := max maxV (raw.foldl max 0)
    maxW := max maxW (wl.foldl max 0)
    let v := packRange lanes 96 0 lanes.size
    let w := packRange wl 128 0 wl.size
    ents := ents.push ⟨s.key, s.flag, v, w⟩
    vLanes := vLanes.push lanes
  let keys := sorted.map (·.key)
  let raws := keys.map (rawMoves ch tb)
  IO.println s!"max V' {maxV} (below 2^{Nat.log2 maxV + 1}), max W' {maxW} (below 2^{Nat.log2 maxW + 1})"
  -- the chunk cut: runs of at most 20000 raw moves
  let maxMoves := 20000
  let starts : Array Nat := Id.run do
    let mut st : Array Nat := #[]
    let mut i := 0
    while i < n do
      st := st.push i
      let mut m := 0
      while i < n && (m == 0 || m + raws[i]! ≤ maxMoves) do
        m := m + raws[i]!; i := i + 1
    return st
  let stE := starts.push n
  let tree := buildTop ents stE 0 starts.size
  IO.println s!"{starts.size} chunks of at most {maxMoves} raw moves"
  let leaf (i : Nat) : String :=
    s!"(Tree.leaf (E.mk (nat_lit {keys[i]!}) (nat_lit {ents[i]!.flag}) {vTerm vLanes[i]!} {hexLit wRaw[sorted[i]!.file]! 128}))"
  -- definitions of one chunk: blocks of at most 64 leaves, nodes above them
  let rec inl (lo hi : Nat) : String :=
    if hi ≤ lo + 1 then leaf lo else
    let mid := (lo + hi) / 2
    s!"(Tree.node (nat_lit {keys[mid]!}) {inl lo mid} {inl mid hi})"
  let rec defs (lo hi : Nat) (acc : Array String) : String × Array String :=
    if hi - lo ≤ 64 then
      (s!"t{lo}_{hi}", acc.push s!"noncomputable def t{lo}_{hi} : Tree :=\n  {inl lo hi}\n")
    else
      let mid := (lo + hi) / 2
      let (l, acc) := defs lo mid acc
      let (r, acc) := defs mid hi acc
      (s!"t{lo}_{hi}", acc.push s!"noncomputable def t{lo}_{hi} : Tree := Tree.node (nat_lit {keys[mid]!}) {l} {r}\n")
  let dir := s!"{outDir}/FrogModel/G3Q/{name}"
  IO.FS.createDirAll dir
  let partBytes := 5000000
  let mut mods : Array String := #[]
  let mut roots : Array String := #[]
  let mut cur : Option IO.FS.Handle := none
  let mut bytes := 0
  for c in [0:starts.size] do
    let (root, ds) := defs stE[c]! stE[c + 1]! #[]
    roots := roots.push root
    let sz := ds.foldl (· + ·.utf8ByteSize) 0
    if cur.isNone || bytes + sz > partBytes then
      if let some h := cur then h.putStrLn "end FrogModel.G3Q"; h.flush
      let h ← IO.FS.Handle.mk s!"{dir}/D{mods.size}.lean" .write
      h.putStrLn ("module\n\npublic import FrogModel.G3K.Fast\n\n@[expose] public section\n\n" ++
        "namespace FrogModel.G3Q\nopen FrogModel.G3K\n")
      mods := mods.push s!"FrogModel.G3Q.{name}.D{mods.size}"
      cur := some h
      bytes := 0
    if let some h := cur then
      for d in ds do h.putStrLn d
    bytes := bytes + sz
  if let some h := cur then h.putStrLn "end FrogModel.G3Q"; h.flush
  -- the nodes above the chunks and the assembly
  let rec top (i j : Nat) (acc : Array String) : String × Array String :=
    if j ≤ i + 1 then (roots[i]!, acc) else
    let mid := (i + j) / 2
    let (l, acc) := top i mid acc
    let (r, acc) := top mid j acc
    (s!"t{stE[i]!}_{stE[j]!}",
      acc.push s!"noncomputable def t{stE[i]!}_{stE[j]!} : Tree := Tree.node (nat_lit {keys[stE[mid]!]!}) {l} {r}\n")
  let (rootName, topDefs) := top 0 starts.size #[]
  let h ← IO.FS.Handle.mk s!"{dir}/Data.lean" .write
  h.putStrLn "module\n"
  for m in mods do h.putStrLn s!"public import {m}"
  h.putStrLn "\n@[expose] public section\n\nnamespace FrogModel.G3Q\nopen FrogModel.G3K\n"
  for d in topDefs do h.putStrLn d
  h.putStrLn s!"noncomputable def theTree : Tree := {rootName}\n\nend FrogModel.G3Q"
  h.flush
  -- the theorems, five per module
  let per := 5
  let hdr := s!"module\n\npublic import FrogModel.G3Q.{name}.Data\n\n@[expose] public section\n\n" ++
    "set_option Elab.async false\n" ++ "\nnamespace FrogModel.G3Q\nopen FrogModel.G3K FrogModel.G3K.Fast\n\n"
  let thms := (Array.range starts.size).map fun c =>
    s!"theorem c{c} : allF (stateOKF theTree) {roots[c]!} = true := by decide +kernel\n"
  let groups : Array (String × Array String) :=
    (Array.range ((thms.size + per - 1) / per)).map fun g => (s!"Thm{g}", thms.extract (g * per) (g * per + per))
  for (fn, ts) in groups do
    IO.FS.writeFile s!"{dir}/{fn}.lean" (ts.foldl (· ++ ·) hdr ++ "\nend FrogModel.G3Q\n")
  for c in [0:starts.size] do
    let a := stE[c]!
    let b := stE[c + 1]!
    IO.println s!"chunk {c}: states [{a}, {b}), phases {sorted[a]!.q} to {sorted[b - 1]!.q}, raw moves {(List.range (b - a)).foldl (fun s i => s + raws[a + i]!) 0}, compiled check {(List.range (b - a)).all fun i => FrogModel.G3K.Spec.stateOK tree ents[a + i]!}"
  -- the assembly `checkAllF theTree = true`
  let rec asm (i j : Nat) (acc : Array String) : String × Array String :=
    if j ≤ i + 1 then (s!"c{i}", acc) else
    let mid := (i + j) / 2
    let (l, acc) := asm i mid acc
    let (r, acc) := asm mid j acc
    (s!"h{stE[i]!}_{stE[j]!}", acc.push
      s!"theorem h{stE[i]!}_{stE[j]!} : allF (stateOKF theTree) t{stE[i]!}_{stE[j]!} = true := allF_node {l} {r}\n")
  let (last, hs) := asm 0 starts.size #[]
  let h ← IO.FS.Handle.mk s!"{dir}/All.lean" .write
  h.putStrLn "module\n"
  for (fn, _) in groups do h.putStrLn s!"public import FrogModel.G3Q.{name}.{fn}"
  h.putStrLn "\n@[expose] public section\n\nnamespace FrogModel.G3Q\nopen FrogModel.G3K FrogModel.G3K.Fast\n"
  for d in hs do h.putStrLn d
  h.putStrLn s!"theorem checkAll_theTree : checkAllF theTree = true := {last}\n\nend FrogModel.G3Q"
  h.flush
  IO.println s!"wrote {mods.size} data modules, Data.lean, {groups.size} theorem modules and All.lean under {dir}"
  return 0
