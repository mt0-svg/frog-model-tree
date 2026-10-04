<h1 align="center">The frog model on regular trees</h1>

<p align="center">The cases d = 3 and d = 4 of a conjecture of Hoffman, Johnson and Junge: the frog model on the rooted 3-ary tree is recurrent, and on the rooted 4-ary tree it is transient.</p>

<p align="center">
  <a href="https://github.com/mt0-svg/frog-model-tree/releases/latest/download/frog-model-tree.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.23121586"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.23121586.svg"></a>
  <a href="https://mt0-svg.github.io/frog-model-tree/run.html"><img alt="Lean Proved" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Ffrog-model-tree%2Fbadges%2Flean.json"></a>
  <a href="https://mt0-svg.github.io/frog-model-tree/run.html"><img alt="Lean Comparator" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Ffrog-model-tree%2Fbadges%2Fcomparator.json"></a>
  <a href="https://mt0-svg.github.io/frog-model-tree/run.html"><img alt="Computation Certificates" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Ffrog-model-tree%2Fbadges%2Fcertificates.json"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

We prove that the frog model on the rooted $`d`$-ary tree is recurrent for $`d=3`$ and transient for $`d=4`$, as conjectured by Hoffman, Johnson and Junge. One frog starts awake at the root and one sleeps at every other vertex; awake frogs perform independent simple random walks, waking the frogs they visit. For $`d=4`$ the mean number of visits to the root is at most $`5.756`$. The proof runs an exact recursion on the laws of the responses of subtrees, with a law given by a finite table that dominates its image, certified by two linear systems on $`159786`$ states. For $`d=3`$ a subtree of height $`m\ge1778250`$ entered by one frog sends back at least $`(m+2)/5`$ frogs on average; the proof combines a lower model, a certified chain of steps on finite tables of bounds, and an induction on the height. Both proofs are formalized in Lean 4.

These are the cases $`d=3`$ and $`d=4`$ of Conjecture 2 of Hoffman, Johnson and Junge ([Ann. Probab. 2017](https://doi.org/10.1214/16-AOP1125); [arXiv:1404.6238](https://arxiv.org/abs/1404.6238)).

```lean
namespace FrogModel

theorem recurrent_three : Recurrent 3

theorem transient_four : Transient 4

theorem meanVisits_four_le :
    ∫⁻ ω, (visits (paths ω)).encard ∂frogMeasure 4 ≤ ENNReal.ofReal (5756 / 1000)
```

## What is checked

- **Lean 4.** `FrogModel.recurrent_three` states that on the rooted 3-ary tree the root is visited infinitely many times almost surely, `FrogModel.transient_four` that on the rooted 4-ary tree it is visited finitely many times almost surely, and `FrogModel.meanVisits_four_le` that the mean number of visits there is at most $`5.756`$, for the model defined in `FrogModel/Defs.lean` (`Recurrent` in `FrogModel/D3/Defs.lean`). The three theorems have no hypothesis and use only the axioms `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, no `native_decide`. The Lean kernel checks by evaluation, with no compiled code, the certificate for d = 4 and the run, the certificate and the table for d = 3 (below). Comparator checks `transient_four` and `meanVisits_four_le` against `FrogModel/Challenge.lean` (`config.json`) and `recurrent_three` against `FrogModel/ChallengeRecurrent.lean` (`config-recurrent.json`); each challenge imports only Mathlib and holds the definitions of the model and its statements with `sorry`. nanoda, a second implementation of the Lean kernel, checks every declaration the theorems depend on. [`STATEMENTS.md`](STATEMENTS.md) gives, for each numbered statement of the paper, its Lean declarations.
- **The data modules, d = 4.** A checker written in Lean, proved sound for every data tree, runs on the data modules of the certificate of Section 7 of the paper (145 modules of data and 61 of theorems, 303 theorems by evaluation). They are not committed: `code/g3k/gen.sh` writes them from the certificate, a release asset (`ASSETS.md`), and compares their sha256 with `code/g3k/modules.sha256`. The certificate was written by the Rust programs of `code/certificate` and the table by the Rust program of `code/table`, which the proof does not trust.
- **The data modules, d = 3.** The kernel evaluates checkers written in Lean, proved sound, on three sets of data: the stored run of the lower model of Section 13 (24 modules, written by `code/m1gen/gen.sh` from the release asset `frog-model-tree-d3-m1run.txt.xz`), the certificate of steps of Proposition 15.1 (1029 modules, written by `code/d3chain/gen.sh` from the asset `frog-model-tree-d3-certificate.tar.zst`), and the 95 entries of the table of Proposition 15.2 (`FrogModel/D3/LaneE/Table.lean`, written by `code/dcheck/gen_table.gp` from the branches that `code/dcheck/dbranch_m1.gp` chooses). The generated modules are not committed; each generator compares their sha256 with its `modules.sha256`, and CI checks that the kernel rejects two falsified entries of the certificate (`code/d3chain/neg`). The programs that wrote the data (`code/m1run` and `code/d3cert` in Rust, `code/dcheck` in PARI/GP) are not trusted; each `run.sh` writes its data again and compares it with the files the generators read, and its recorded output `out/run.out` holds the comparison.
- **PARI/GP.** `code/gp/small_checks.gp` prints the constants of the paper from the table and the bound $`5\gamma/(1-\gamma)<5.756`$; `code/gp/start_values.gp` prints the values of the certificate at the start state; `code/gp/table_tex.gp` prints the table of Appendix A and checks its label rule and its row sums.

CI (`.github/workflows/ci.yml`) reruns all of it before every release: the data modules of both proofs, the Lean build as a chain of jobs of at most 300 minutes, the axioms, the negative controls of the d = 3 data, a scan of the sources, Comparator with nanoda on 4 threads on each configuration, the PARI/GP scripts against their recorded outputs, the table from its two iterates, and the writers of the d = 3 data against the data. [`code/README.md`](code/README.md) describes the programs.

## Layout

| Path                                                                                             | Content                                                                                                                                                                                                                                                                                 |
| ------------------------------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `FrogModel/`                                                                                     | the Lean proof (Lean and Mathlib `v4.34.1`)                                                                                                                                                                                                                                             |
| `FrogModel/Defs.lean`                                                                            | the definitions of the statement: the tree, the walks, the wake times, `Transient`, `frogMeasure`                                                                                                                                                                                       |
| `FrogModel/Challenge.lean`, `FrogModel/Solution.lean`, `config.json`                             | the definitions and the two statements for d = 4 with `sorry`, their proofs, and the Comparator configuration                                                                                                                                                                           |
| `FrogModel/ChallengeRecurrent.lean`, `FrogModel/SolutionRecurrent.lean`, `config-recurrent.json` | the definitions and the statement for d = 3 with `sorry`, its proof, and the Comparator configuration                                                                                                                                                                                   |
| `FrogModel/G3K/`                                                                                 | the checker of the certificate for d = 4 that the kernel evaluates, and its soundness                                                                                                                                                                                                   |
| `FrogModel/G3Q/`                                                                                 | the data modules for d = 4, written by `code/g3k/gen.sh` (not committed)                                                                                                                                                                                                                |
| `FrogModel/LemmaR/`, `FrogModel/ZeroOne/`, `FrogModel/D3/`                                       | the proof for d = 3: the recurrence criterion and the zero-one law (Theorem 8.2, proved in Section 9, and Theorem 9.3), the closure and its bounds, the step map and its checker, the lower model and the checker of its run, the induction on the height, the chain of the certificate |
| `FrogModel/D3/M1Data/`, `FrogModel/D3/CertData/`                                                 | the data modules for d = 3, written by `code/m1gen/gen.sh` and `code/d3chain/gen.sh` (not committed)                                                                                                                                                                                    |
| `code/`                                                                                          | the programs that write the data modules, the programs that wrote the data of both proofs, the PARI/GP scripts                                                                                                                                                                          |
| `paper/`                                                                                         | the TeX source and `statement_map.sh` (which writes `STATEMENTS.md`)                                                                                                                                                                                                                    |
| `.github/`                                                                                       | the CI workflow, its scripts and the Comparator patch, the issue forms                                                                                                                                                                                                                  |
| `records/`                                                                                       | the outputs and scripts behind the figures for d = 3 of Section 16 of the paper: the full build, the writers of the data, nanoda and Comparator, run on this repository ([`records/README.md`](records/README.md))                                                                      |
| `release-notes/`                                                                                 | the notes of each release                                                                                                                                                                                                                                                               |

## Check and reuse

Times measured on a workstation with an AMD Ryzen 9 5900X (12 cores) and 64 GB of memory, under load.

The data modules for d = 4, from the certificate (about 1 minute):

```sh
gh release download --repo mt0-svg/frog-model-tree --dir code/certificate/out --pattern 'frog-model-tree-certificate.v4.zst'
zstd -d code/certificate/out/frog-model-tree-certificate.v4.zst -o code/certificate/out/certificate.v4
code/g3k/gen.sh code/certificate/out/certificate.v4
```

The data modules for d = 3, from the two assets (554 s for the 1029 certificate modules with `JOBS=4`, under a second for the 24 run modules):

```sh
gh release download --repo mt0-svg/frog-model-tree --dir code/d3data --pattern 'frog-model-tree-d3-*'
tar --zstd -C code/d3data -xf code/d3data/frog-model-tree-d3-certificate.tar.zst
code/m1gen/gen.sh code/d3data/frog-model-tree-d3-m1run.txt.xz code/d3data/d3-certificate/masses100.txt
JOBS=4 code/d3chain/gen.sh code/d3data/d3-certificate
```

Fast check, with the build of the release:

```sh
lake exe cache get          # Mathlib, from its cache
lake build :release         # this package, from the release archive
lake build --no-build       # nothing left to build
rm -f .lake/build/lib/lean/FrogModel/Challenge.* .lake/build/ir/FrogModel/Challenge.*
rm -f .lake/build/lib/lean/FrogModel/ChallengeRecurrent.* .lake/build/ir/FrogModel/ChallengeRecurrent.*
# then Comparator on config.json and on config-recurrent.json, as the job comparator of .github/workflows/ci.yml runs it
```

Comparator with nanoda takes about 50 minutes on 4 threads and 9 GB of memory for `config.json`, and 1581 s on four cores for `config-recurrent.json`, with a peak of 7.9 GiB for the memory of its control group, page cache included ([`records/comparator`](records/comparator)).

Full check, from source, once the data modules of both proofs are written (5991 s on four cores for the 1490 modules with the settings below, those of the recorded build, and at most 3.7 GiB per Lean process; [`records/build`](records/build)), then Comparator:

```sh
lake exe cache get && HB=1 LB=2 PEAK_HEAVY=9G MEM_MARGIN=1G LEAN_NUM_THREADS=2 code/formal-proof/clean_build.sh
```

The certificate for d = 4, again (`code/certificate`, Rust 1.98.1 as `rust-toolchain.toml` pins it; 3 to 8 minutes on 2 cores):

```sh
code/certificate/run_occupations.sh && code/certificate/run_gen.sh
```

The table for d = 4, again (`code/table`, Rust; 25 to 40 minutes on 1 core for the two steps, seconds for the table):

```sh
code/table/run_iterates.sh && code/table/run_table.sh
```

The data for d = 3, again (Rust 1.98.1 and PARI/GP 2.15.4; 154 s on two cores, builds included; [`records/writers`](records/writers)):

```sh
code/m1run/run.sh && code/d3cert/run.sh && code/dcheck/run.sh
```

The PARI/GP scripts (PARI/GP 2.15.4; under a second):

```sh
cd code/gp && gp -q small_checks.gp < /dev/null | diff - small_checks.out
gp -q table_tex.gp < /dev/null | diff - ../../paper/table.tex
CERT=../certificate/out/certificate.v4 gp -q start_values.gp < /dev/null | diff - start_values.out
```

As a dependency (Lean and Mathlib `v4.34.1`):

```toml
[[require]]
name = "frog-model-tree"
git = "https://github.com/mt0-svg/frog-model-tree"
rev = "v2.0.0"
```

then `lake update frog-model-tree`, `lake exe cache get` and `lake build`, which downloads the build archive of the release. A module that imports `FrogModel.Solution` also needs the data modules for d = 4, written by `code/g3k/gen.sh` in the directory of the package, and one that imports `FrogModel.SolutionRecurrent` the data modules for d = 3, written by `code/m1gen/gen.sh` and `code/d3chain/gen.sh`.

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export) and [landrun](https://github.com/zouuup/landrun): the check of the statements in CI.
- [nanoda](https://github.com/ammkrn/nanoda_lib) of Chris Bailey (Apache 2.0), commit `3a2407216ee84a75f9e1aead6803d0578be06ae7`: the second implementation of the Lean kernel, which Comparator runs to check again every declaration the theorems depend on.
- [Rust](https://www.rust-lang.org/) with [num-bigint, num-rational, num-integer and num-traits](https://github.com/rust-num) (MIT or Apache 2.0): the programs that wrote the table and the certificate for d = 4; with [rayon](https://github.com/rayon-rs/rayon) (MIT or Apache 2.0): the program that wrote the run for d = 3 (`code/m1run`); with no dependency: the program that wrote the certificate for d = 3 (`code/d3cert`).
- [PARI/GP](https://pari.math.u-bordeaux.fr/): the constants of the paper, the table of Appendix A and the table of Proposition 15.2.

## Citation

```bibtex
@misc{frog-model-tree,
  title     = {The frog model is recurrent on the 3-ary tree and transient on the 4-ary tree},
  author    = {{mt0-svg}},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23121586},
  url       = {https://doi.org/10.5281/zenodo.23121586}
}
```

## Contact

Questions and corrections: [open an issue](https://github.com/mt0-svg/frog-model-tree/issues/new/choose).

## License

Apache 2.0 (`LICENSE`, `NOTICE`).
