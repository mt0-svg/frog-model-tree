import G3Tool.TableK

/-! `g3ktable TABLE SHA256 OUT`: write the table module `FrogModel/G3K/Table.lean` of the kernel checker. -/

open G3Tool

def main (args : List String) : IO UInt32 := do
  match args with
  | [path, sha, out] =>
    let text ← IO.FS.readFile path
    match parseTable text with
    | .error e => IO.eprintln e; return 1
    | .ok tb =>
      let ch := buildChain tb
      IO.FS.writeFile out (tableModuleK tb ch sha)
      IO.println s!"J {tb.j} T {tb.t} T' {tb.tp}; {ch.names.size} child states; {(ch.rows.foldl (· + ·.size) 0)} row transitions"
      return 0
  | _ => IO.eprintln "usage: g3ktable TABLE SHA256 OUT"; return 2
