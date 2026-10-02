# The programs

The proof trusts none of these programs: the Lean kernel checks the modules that `g3k` writes, and the PARI/GP scripts print values that the kernel decides as inequalities. Section 8 of the paper describes them.

## `g3k`: the data modules

`code/g3k` is a Lake package of its own, on Lean core alone; `FrogModel/G3K` there is a link to the checker of the main package, so that the program and the proof read the same table and the same key coding.

- `g3k TABLE DATA OUTDIR NAME` reads the table and the certificate, builds the binary search tree of the 159786 entries (key, flag, the values of the two linear systems packed into one integer per state and per system), and writes under `OUTDIR/FrogModel/G3Q/NAME/` the data modules `D0.lean` to `D144.lean`, `Data.lean` (the tree `FrogModel.G3Q.theTree`), the theorem modules `Thm0.lean` to `Thm60.lean` (303 theorems, one per subtree of at most 20000 moves, each proved by `decide +kernel`) and `All.lean` (`FrogModel.G3Q.checkAll_theTree`). On the way it runs the compiled checker on every subtree and prints the result, which the proof does not use.
- `g3ktable TABLE SHA256 OUT` writes `FrogModel/G3K/Table.lean`, the table as the checker reads it.
- `gen.sh CERTIFICATE [OUT]` checks the sha256 of the certificate (unpacked) and of the table against `modules.sha256`, builds `g3k`, writes `FrogModel/G3Q/Cand/` in the package, and compares the sha256 of the 208 modules with `modules.sha256`.

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
- `main_axioms.lean` prints the axioms of `FrogModel.transient_four`, of `FrogModel.meanVisits_four_le` and of the two theorems on the data; `facts.lean` prints their number of hypotheses and of axioms, for the badges.
