/-!
# m1gen: the Lean data modules of the stored M1 run

`m1gen RUNFILE MASSFILE OUTDIR` reads the stored run (code/m1run/src/bin/m1run.rs, format `M1RUN 1`,
`PARAMS 48 96 62 100 33 sat`) and its mass file, and writes under
`OUTDIR/FrogModel/D3/M1Data/` the modules `FrogModel.D3.M1Data.*` of the Lean module system:

- `H0.lean` .. `H9.lean`: the stored laws of the heights `10 i .. 10 i + 9`, one
  `FrogModel.D3.M1K.St` each (`h0` .. `h99`), every row packed in lanes of 144 bits as
  `FrogModel/D3/M1K/Check.lean` reads it (lane `4 a + g`);
- `Top.lean`: `wtil`, the rows `Wtil_q`, `q = 2..33`, `mass`, the mass lines (row `k - 1`, entry
  `x - 1`, `k = 1..32`, `x = 1..48`), and `massPk`, the masses `2^62 W_k(x)` (`x = 0..48`) in slots of 64
  bits, slot `49 (k - 1) + x`, computed from `wtil`;
- `Data.lean`: `stored`, the list `h0 .. h99`;
- `C0.lean` .. `C9.lean`: the kernel checks of the heights `10 i .. 10 i + 9`, `valid_h :
  validSt h = true` and, for `h ≥ 1`, `step_h : checkStep h(h-1) h = true`, by `decide +kernel`;
  `C0.lean` also `check0_0 : check0 h0 = true`;
- `CTop.lean`: `top : checkTop h99 wtil = true` and `mass_ok : checkMass wtil massPk mass = true`;
- `All.lean`: `stAt h`, the height `h` of `stored`, and `valid_all`, `step_all`, the checks of the C modules
  indexed by the height.

The program checks the header and the counts of the lines and nothing else: a wrong module makes a
kernel check fail.
-/

def natOf (s : String) : Nat := s.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

def laneHex (v : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (36 - s.length) '0') ++ s

/-- The raw literal of a row of 196 lanes of 144 bits, lane 0 lowest. -/
def rowLit (a : Array Nat) : String := Id.run do
  if a.all (· == 0) then return "(nat_lit 0)"
  let mut s := "(nat_lit 0x"
  for i in [0:a.size] do
    s := s ++ laneHex a[a.size - 1 - i]!
  return s ++ ")"

def header (imports : List String) (doc : String) : String :=
  "module\n\n" ++ String.join (imports.map fun m => s!"public import {m}\n") ++
    "\n@[expose] public section\n\n/-! " ++ doc ++ " -/\n\nnamespace FrogModel.D3.M1Data\n\nopen FrogModel.D3.M1K\n\n"

def footer : String := "end FrogModel.D3.M1Data\n"

def main (args : List String) : IO UInt32 := do
  let [runF, massF, outD] := args | do
    IO.eprintln "usage: m1gen RUNFILE MASSFILE OUTDIR"; return 2
  let lines := (← IO.FS.readFile runF).splitOn "\n" |>.filter (· ≠ "")
  if lines.take 2 != ["M1RUN 1", "PARAMS 48 96 62 100 33 sat"] then
    IO.eprintln "unexpected header"; return 1
  let mut rho : Array (Array Nat) := Array.replicate 100 #[]
  let mut k : Array (Array (Array Nat)) := Array.replicate 100 (Array.replicate 4 #[])
  let mut wt : Array (Array Nat) := Array.replicate 34 #[]
  for ln in lines.drop 2 do
    let w := (ln.splitOn " ").toArray
    match w[0]! with
    | "RHO" => rho := rho.set! (natOf w[1]!) ((w.extract 2 w.size).map natOf)
    | "K" => k := k.modify (natOf w[1]!) (·.set! (natOf w[2]!) ((w.extract 3 w.size).map natOf))
    | "WTIL" => wt := wt.set! (natOf w[1]!) ((w.extract 2 w.size).map natOf)
    | "END" => pure ()
    | _ => IO.eprintln s!"unexpected line {w[0]!}"; return 1
  let ok := (rho.all (·.size == 196)) && (k.all (·.all (·.size == 196))) &&
    ((wt.extract 2 34).all (·.size == 196))
  if !ok then IO.eprintln "a row is missing or has the wrong length"; return 1
  let mlines := (← IO.FS.readFile massF).splitOn "\n" |>.filter (· ≠ "")
  if mlines.head? != some "MASSV 100 48" || mlines.length != 1 + 32 * 48 then
    IO.eprintln "unexpected mass file"; return 1
  let mass := (mlines.drop 1).toArray.map fun ln => natOf ((ln.splitOn " ").getLast!)
  let dir := outD ++ "/FrogModel/D3/M1Data"
  IO.FS.createDirAll dir
  for i in [0:10] do
    let mut s := header ["FrogModel.D3.M1K.Check"] s!"The stored laws of the heights {10 * i} to {10 * i + 9} (written by m1gen)."
    for h in [10 * i:10 * i + 10] do
      s := s ++ s!"def h{h} : St :=\n  ⟨{rowLit rho[h]!},\n   {rowLit k[h]![0]!},\n   {rowLit k[h]![1]!},\n   {rowLit k[h]![2]!},\n   {rowLit k[h]![3]!}⟩\n\n"
    IO.FS.writeFile s!"{dir}/H{i}.lean" (s ++ footer)
  let mut t := header ["FrogModel.D3.M1K.Check"] "The top arrays `Wtil_q`, `q = 2..33`, at height 100 and the mass lines (written by m1gen)."
  t := t ++ "/-- `Wtil_q` at entry `q - 2`. -/\ndef wtil : List Nat := [\n"
  for q in [2:34] do
    t := t ++ "  " ++ rowLit wt[q]! ++ (if q < 33 then ",\n" else "]\n\n")
  t := t ++ "/-- The mass lines: row `k - 1`, entry `x - 1`, `n = 2^62 W_k(x)`. -/\ndef mass : List (List Nat) := [\n"
  for kk in [0:32] do
    let row := (mass.extract (48 * kk) (48 * kk + 48)).toList.map toString
    t := t ++ "  [" ++ ", ".intercalate (row.map fun x => s!"(nat_lit {x})") ++ (if kk < 31 then "],\n" else "]]\n\n")
  let mut mpk : Array Nat := Array.replicate (32 * 49) 0
  for kk in [0:32] do
    for x in [0:49] do
      mpk := mpk.set! (49 * kk + x) ((List.range 4).foldl (fun s g => s + wt[kk + 2]![4 * x + g]!) 0)
  let mut hx := "(nat_lit 0x"
  for i in [0:mpk.size] do
    let s := String.ofList (Nat.toDigits 16 mpk[mpk.size - 1 - i]!)
    hx := hx ++ String.ofList (List.replicate (16 - s.length) '0') ++ s
  t := t ++ "/-- The masses `2^62 W_k(x)`, `k = 1..32`, `x = 0..48`, in slots of 64 bits, slot `49 (k - 1) + x`. -/\ndef massPk : Nat :=\n  " ++ hx ++ ")\n\n"
  IO.FS.writeFile s!"{dir}/Top.lean" (t ++ footer)
  let mut d := header ((List.range 10).map fun i => s!"FrogModel.D3.M1Data.H{i}") "The stored laws `h0 .. h99` in a list (written by m1gen)."
  d := d ++ "def stored : List St :=\n  [" ++ ", ".intercalate ((List.range 100).map fun h => s!"h{h}") ++ "]\n\n"
  IO.FS.writeFile s!"{dir}/Data.lean" (d ++ footer)
  for i in [0:10] do
    let imps := if i == 0 then ["FrogModel.D3.M1Data.H0"] else [s!"FrogModel.D3.M1Data.H{i - 1}", s!"FrogModel.D3.M1Data.H{i}"]
    let mut s := header imps s!"The kernel checks of the heights {10 * i} to {10 * i + 9} (written by m1gen)."
    s := s ++ "set_option Elab.async false\n\n"
    for h in [10 * i:10 * i + 10] do
      s := s ++ s!"theorem valid_{h} : validSt h{h} = true := by decide +kernel\n\n"
      if h == 0 then
        s := s ++ "theorem check0_0 : check0 h0 = true := by decide +kernel\n\n"
      if h ≥ 1 then
        s := s ++ s!"theorem step_{h} : checkStep h{h - 1} h{h} = true := by decide +kernel\n\n"
    IO.FS.writeFile s!"{dir}/C{i}.lean" (s ++ footer)
  let c := header ["FrogModel.D3.M1Data.H9", "FrogModel.D3.M1Data.Top"] "The kernel check of the top (written by m1gen)."
  IO.FS.writeFile s!"{dir}/CTop.lean" (c ++ "set_option Elab.async false\n\ntheorem top : checkTop h99 wtil = true := by decide +kernel\n\ntheorem mass_ok : checkMass wtil massPk mass = true := by decide +kernel\n\n" ++ footer)
  let mut a := header (((List.range 10).map fun i => s!"FrogModel.D3.M1Data.C{i}") ++ ["FrogModel.D3.M1Data.Data"]) "The checks of all the heights, indexed by the height (written by m1gen)."
  a := a ++ "/-- Height `h` of the stored run. -/\ndef stAt (h : Nat) : St := stored.getD h ⟨0, 0, 0, 0, 0⟩\n\n"
  a := a ++ "theorem valid_all : ∀ h, h < 100 → validSt (stAt h) = true\n"
  for h in [0:100] do
    a := a ++ s!"  | {h}, _ => valid_{h}\n"
  a := a ++ "  | _ + 100, hh => absurd hh (by omega)\n\n"
  a := a ++ "theorem step_all : ∀ h, 1 ≤ h → h < 100 → checkStep (stAt (h - 1)) (stAt h) = true\n  | 0, h1, _ => absurd h1 (by omega)\n"
  for h in [1:100] do
    a := a ++ s!"  | {h}, _, _ => step_{h}\n"
  a := a ++ "  | _ + 100, _, hh => absurd hh (by omega)\n\n"
  IO.FS.writeFile s!"{dir}/All.lean" (a ++ footer)
  IO.println s!"m1gen: 100 heights, 32 top rows, {mass.size} mass lines, 24 modules in {dir}"
  return 0
