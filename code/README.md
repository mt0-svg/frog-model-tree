# The programs

The proof trusts none of these programs: the Lean kernel checks the modules that `g3k`, `m1gen` and `d3chain` write, and the PARI/GP scripts print values that the kernel decides as inequalities. Section 16 of the paper describes them.

## `g3k`: the data modules

`code/g3k` is a Lake package of its own, on Lean core alone; `FrogModel/G3K` there is a link to the checker of the main package, so that the program and the proof read the same table and the same key coding.

- `g3k TABLE DATA OUTDIR NAME` reads the table and the certificate, builds the binary search tree of the 159786 entries (key, flag, the values of the two linear systems packed into one integer per state and per system), and writes under `OUTDIR/FrogModel/G3Q/NAME/` the data modules `D0.lean` to `D144.lean`, `Data.lean` (the tree `FrogModel.G3Q.theTree`), the theorem modules `Thm0.lean` to `Thm60.lean` (303 theorems, one per subtree of at most 20000 moves, each proved by `decide +kernel`) and `All.lean` (`FrogModel.G3Q.checkAll_theTree`). On the way it runs the compiled checker on every subtree and prints the result, which the proof does not use.
- `g3ktable TABLE SHA256 OUT` writes `FrogModel/G3K/Table.lean`, the table as the checker reads it.
- `gen.sh CERTIFICATE [OUT]` checks the sha256 of the certificate (unpacked) and of the table against `modules.sha256`, builds `g3k`, writes `FrogModel/G3Q/Cand/` in the package, and compares the sha256 of the 208 modules with `modules.sha256`.

## `m1gen`: the data modules of the stored run of the lower model (d = 3)

`code/m1gen` is a Lake package of its own, on Lean core alone.

- `m1gen RUNFILE MASSFILE OUTDIR` reads the stored run of the lower model M1 (its laws at the heights 0 to 99 and its top rows at height 100) and the mass file, and writes under `OUTDIR/FrogModel/D3/M1Data/` the data modules `H0.lean` to `H9.lean`, `Top.lean` and `Data.lean`, the theorem modules `C0.lean` to `C9.lean` and `CTop.lean` (the checks of every height, of the top rows and of the masses, each proved by `decide +kernel`) and `All.lean`. It checks the header and the counts of lines of its input and nothing else: a wrong module makes a kernel check fail.
- `gen.sh RUN MASS [OUT]` checks the sha256 of the run (the release asset `frog-model-tree-d3-m1run.txt.xz`, compressed or not) and of the mass file (`masses100.txt` of the d = 3 certificate, unpacked) against `modules.sha256`, builds `m1gen`, writes `FrogModel/D3/M1Data/` in the package, and compares the sha256 of the 24 modules with `modules.sha256`.

## `d3chain`: the data modules of the certificate (d = 3)

`code/d3chain` is a Lake package of its own, on Lean core alone; `FrogModel/D3/LaneD/K` there is a link to the kernel checker of the main package, so that the program and the proof read the same encoding.

- `d3chain CERTDIR OUTROOT [-c] [-j N]` reads the certificate (`manifest.txt` and the files it names: the seed at height 100, the steps of the chain, the extension and the final check) and writes under `OUTROOT/FrogModel/D3/CertData/` one module per stored state (`S/`), one module per line of the manifest with its kernel checks (`L/`), the modules of the seed, of the extension and of the comparisons of the final check (`Seed.lean`, `Ext.lean`, `LeT.lean`), the segments of the chain (`B/`) and `Main.lean`. With `-c` it also runs the compiled checkers on every line, which the proof does not use.
- `gen.sh CERTDIR [OUT]` checks the sha256 of the certificate files (the release asset `frog-model-tree-d3-certificate.tar.zst`, unpacked) against `modules.sha256`, builds `d3chain`, writes `FrogModel/D3/CertData/` in the package, and compares the sha256 of the modules with `modules.sha256`.
- `neg/NegLine.lean` and `neg/NegLe.lean`: negative controls, two kernel checks of the chain on a falsified datum (the line L350 with its stored output deficit lowered by $`2^{-22}`$, and the final comparison with a row of T lowered by one unit); the lean job of CI checks that the kernel rejects each.

## `m1run`, `d3cert`, `dcheck`: the writers of the data (d = 3)

These programs wrote the two d = 3 assets and the table of Proposition 15.2; they reproduce them, and the proof does not trust them. Each `run.sh` writes its data again and compares it with the files that the Lean jobs read; the job writers3 of CI runs the three and compares what each prints with its recorded output `out/run.out` (the times left out), byte for byte.

- `m1run` (Rust, integer arithmetic): `m1run V P W M QMAX RUNFILE MASSFILE` writes the stored run of the lower model M1 (the laws of the heights 0 to M-1, rounded down to multiples of $`2^{-W}`$, and the top rows at height M) and the masses at height M (formats: `src/bin/m1run.rs`). `run.sh` runs it with $`(V, P) = (48, 96)`$, $`W = 62`$, $`M = 100`$, QMAX $`= 33`$, and compares the two files with the inputs listed in `m1gen/modules.sha256` (recorded output `out/run.out`).
- `d3cert` (Rust): `d3-cert` writes and checks the certificate of Proposition 15.1 (2), in floating point with outward rounding: `seed`, `chain` (the steps), `ext` (the extension), `tcheck` (the check of the function T on $`[605, 1778279]`$, raised to the state at 605 and to nondecreasing rows) and `verify MANIFEST` (every line of the manifest). `d3-fhat` searches T in floating point, with the exponential and the logarithm of the C library; its own test of T prints FAIL at the margins it is given, and only `tcheck` and the kernel judge T. `run.sh [MASSES]` writes the certificate from the masses that `m1run/run.sh` writes into `out/d3-certificate/`, verifies it, and compares the 510 files with the inputs listed in `d3chain/modules.sha256`, and `T605.txt` with the sha256 in the script (recorded output `out/run.out`).
- `dcheck` (PARI/GP): `dbranch_m1.gp`, which reads `scale4.gp` and `dp15.gp`, proposes in floating point the branches of the 95 intervals of the table, written as `dcheck_m1_cert.gp`; `dcheck_m1.gp`, with `dcheck_lib.gp`, checks them in exact rationals with outward rounding (recorded output `dcheck_m1.out`); `gen_table.gp` writes `FrogModel/D3/LaneE/Table.lean` from `dcheck_m1_cert.gp`, and the kernel checks each entry there; `gen_probe.gp` checks the inequalities of the 95 entries in exact rationals and prints their smallest margins, which Section 15 of the paper prints (it also writes them as Lean theorems under `out/probe/`, which the proof does not use). `run.sh` runs the four and compares their outputs with `dcheck_m1_cert.gp`, with `dcheck_m1.out` (times aside) and with the `Table.lean` of the checkout, and records the margins (recorded output `out/run.out`).

In the outputs of these programs and in the modules that `d3chain` writes, `(CertS)` and `(CertS_1)` name the certificate of Proposition 15.1 (2) (the Lean predicate `FrogModel.D3.Iface.CertS1`), and `(D'check) in MODE 1` the check of the table of Proposition 15.2.

## `certificate`: the table and the certificate

- `table.cert`: the table of Section 7 and Appendix A of the paper (format: `FORMAT.md`, version 3).
- `gen` (Rust): the certificate of Section 7 from the table and the occupations (format: `FORMAT.md`, version 4). It builds the states reached from the start, with the flag 1 on the pairs of occupation at least $`10^{-7}`$, every move and stop with its weight rounded to $`2^{-48}`$, the values of the two linear systems by Gauss-Seidel iteration in floating point, rounded to the grid $`2^{-40}`$ and shifted by a multiple of the expected number of remaining steps, checks the inequalities of items 4 and 5 of `FORMAT.md` exactly before writing, and builds the plan from a maximum flow. `run_gen.sh` writes `out/certificate.v4.zst` and its output `out/gen.out`.
- `occupations` (Rust): the expected numbers of visits of the pairs (multiset of child states, number of waiting frogs) in the root chain of Lemma 6.2 without lumping, at threshold $`10^{-11}`$, in floating point; they only choose the flags, and any choice of flags gives a certificate that the checker accepts or rejects on its own. Its output prints counts of the run. `run_occupations.sh` writes `out/occupations.txt` (not committed) and `out/occupations.out`.

`run_occupations.sh` then `run_gen.sh` write the certificate of the release asset, byte for byte.

## `table`: the table

- `table` (Rust, floating point): the program that wrote `certificate/table.cert`, with the constants of the table in its source ($`J=4`$, $`T=8`$, $`\varepsilon=10^{-4}`$, $`\phi=23/20`$, $`\rho=27/40`$, $`T'=16`$). `table iterate H N OUT` makes N steps from the law of the file H: one step sends a law of the class of the table (rows on its labels) to the law of the class, built level by level by quantile couplings, that dominates the normalized part on the vectors with $`B(J)\le T`$ of the output of the root chain of Lemma 6.2 for $`H^*=(1-\varepsilon)H`$ plus the tail. `table write H H' S OUT` writes the law $`H+S(H-H')`$, its rows rounded to multiples of $`2^{-28}`$, as a table (format: `certificate/FORMAT.md`, version 3).
- `H13.txt`, `H14.txt`, `H15.txt`: three successive iterates, as written by the program: the line `J T kind`, then one line per label, `q B(q) flag 0 :` followed by the probabilities of the increments 0, 1, 2, ... in its row.
- `run_iterates.sh` runs two steps from `H13.txt` and compares them with `H14.txt` and `H15.txt` (recorded output `out/iterates.out`).
- `run_table.sh` writes the table, the law $`H_{15}+30(H_{15}-H_{14})`$ for the laws $`H_{14}`$ and $`H_{15}`$ of `H14.txt` and `H15.txt`, its probabilities rounded to multiples of $`2^{-28}`$, and compares it with `certificate/table.cert` byte for byte (recorded output `out/table.out`).

## `gp`: constants and table

- `small_checks.gp` reads `certificate/table.cert` and prints the constants of the paper ($`\gamma`$, $`\phi\rho`$, $`M`$, $`\kappa^4-M`$, $`\theta`$, $`\theta\rho`$, $`\varepsilon\theta^9`$, the sum over the root row) and the bound $`5\gamma/(1-\gamma)<5.756`$ of Theorem 1.2; recorded output `small_checks.out`.
- `start_values.gp` reads the certificate, unpacked, at the path in the environment variable `CERT`, and prints the values at the start state that Proposition 7.1 (6) and (7) print: $`u(s_0)[8]`$ against $`\varepsilon\theta^9`$, and the mass of $`L`$ against $`1-\varepsilon`$; recorded output `start_values.out`, which the job data of CI compares.
- `table_tex.gp` writes `paper/table.tex`, the table of Appendix A, and stops with an error if a next label breaks the label rule of Section 7, a probability is not a multiple of $`2^{-28}`$ or a row does not sum to 1.

## `formal-proof`

- `clean_build.sh` compiles the modules of `FrogModel/`, the data modules included, in dependency order, a few at a time under a memory guard (its header lists its settings); CI runs it.
- `main_axioms.lean` prints the axioms of `FrogModel.transient_four`, of `FrogModel.meanVisits_four_le` and of the two theorems on their data, and of `FrogModel.recurrent_three` and of the two theorems on its data (`FrogModel.D3.Chain.m1run_certS_proof`, `FrogModel.D3.M1K.storedRun_holds`); `facts.lean` prints the number of hypotheses and of axioms of the three theorems of `config.json` and `config-recurrent.json`, for the badges.
