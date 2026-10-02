<h1 align="center">The frog model on regular trees</h1>

<p align="center">The case d = 4 of the Hoffman-Johnson-Junge conjecture: the frog model on the rooted 4-ary tree is transient.</p>

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

We prove that the frog model on the rooted $`4`$-ary tree is transient. One frog starts awake at the root and one sleeps at every other vertex; awake frogs perform independent simple random walks, waking the frogs they visit. Almost surely the root is visited finitely often; the mean number of visits is at most $`5.756`$. This is the case $`d=4`$ of a conjecture of Hoffman, Johnson and Junge on the $`d`$-ary tree, who proved recurrence for $`d=2`$ and transience for $`d\ge5`$. The proof bounds by $`0.536`$ the mean number of frogs that a subtree sends back to the parent of its root. It combines an exact recursion on the laws of the response curves of subtrees with a law, given by a finite table, that dominates its image; two linear systems on $`159786`$ states certify the domination. The proof is formalized in Lean 4, whose kernel checks the certificate.

This is the case $`d=4`$ of Conjecture 2 of Hoffman, Johnson and Junge ([Ann. Probab. 2017](https://doi.org/10.1214/16-AOP1125); [arXiv:1404.6238](https://arxiv.org/abs/1404.6238)).

```lean
namespace FrogModel

theorem transient_four : Transient 4

theorem meanVisits_four_le :
    ∫⁻ ω, (visits (paths ω)).encard ∂frogMeasure 4 ≤ ENNReal.ofReal (5756 / 1000)
```

## What is checked

- **Lean 4.** `FrogModel.transient_four` states that almost surely the root is visited finitely many times, and `FrogModel.meanVisits_four_le` that the mean number of visits is at most $`5.756`$, for the model defined in `FrogModel/Defs.lean`. They have no hypothesis and use only the axioms `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, no `native_decide`. The Lean kernel checks the certificate of Section 7 of the paper by evaluation, with no compiled code: a checker written in Lean, proved sound for every data tree, runs on the data modules. Comparator checks the two theorems against `FrogModel/Challenge.lean`, which imports only Mathlib and holds the definitions and the two statements with `sorry`, and nanoda, a second implementation of the Lean kernel, checks every declaration they depend on. [`STATEMENTS.md`](STATEMENTS.md) gives, for each numbered statement of the paper, its Lean declarations.
- **The data modules.** The Lean modules of the data (145 modules of data and 61 of theorems, 303 theorems by evaluation) are not committed: `code/g3k/gen.sh` writes them from the certificate, a release asset (`ASSETS.md`), and compares their sha256 with `code/g3k/modules.sha256`. The certificate was written by the Rust programs of `code/certificate` and the table by the Rust program of `code/table`, which the proof does not trust.
- **PARI/GP.** `code/gp/small_checks.gp` prints the constants of the paper from the table and the bound $`5\gamma/(1-\gamma)<5.756`$; `code/gp/start_values.gp` prints the values of the certificate at the start state; `code/gp/table_tex.gp` prints the table of Appendix A and checks its label rule and its row sums.

CI (`.github/workflows/ci.yml`) reruns all of it before every release: the data modules, the Lean build as a chain of jobs of at most 300 minutes, the axioms, a scan of the sources, Comparator with nanoda on 4 threads, the three PARI/GP scripts against their recorded outputs, and the table from its two iterates. [`code/README.md`](code/README.md) describes the programs.

## Layout

| Path                                                                 | Content                                                                                                              |
| -------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------- |
| `FrogModel/`                                                         | the Lean proof (Lean and Mathlib `v4.34.1`)                                                                          |
| `FrogModel/Defs.lean`                                                | the definitions of the statement: the tree, the walks, the wake times, `Transient`, `frogMeasure`                    |
| `FrogModel/Challenge.lean`, `FrogModel/Solution.lean`, `config.json` | the definitions and the two statements with `sorry`, their proofs, and the Comparator configuration                  |
| `FrogModel/G3K/`                                                     | the checker of the certificate that the kernel evaluates, and its soundness                                          |
| `FrogModel/G3Q/`                                                     | the data modules, written by `code/g3k/gen.sh` (not committed)                                                       |
| `code/`                                                              | the program that writes the data modules, the programs that wrote the table and the certificate, the PARI/GP scripts |
| `paper/`                                                             | the TeX source and `statement_map.sh` (which writes `STATEMENTS.md`)                                                 |
| `.github/`                                                           | the CI workflow, its scripts and the Comparator patch, the issue forms                                               |
| `release-notes/`                                                     | the notes of each release                                                                                            |

## Check and reuse

Times measured on a workstation with an AMD Ryzen 9 5900X (12 cores) and 64 GB of memory, under load.

The data modules, from the certificate (about 1 minute):

```sh
gh release download --repo mt0-svg/frog-model-tree --dir code/certificate/out --pattern 'frog-model-tree-certificate.v4.zst'
zstd -d code/certificate/out/frog-model-tree-certificate.v4.zst -o code/certificate/out/certificate.v4
code/g3k/gen.sh code/certificate/out/certificate.v4
```

Fast check, with the build of the release:

```sh
lake exe cache get          # Mathlib, from its cache
lake build :release         # this package, from the release archive
lake build --no-build       # nothing left to build
rm -f .lake/build/lib/lean/FrogModel/Challenge.* .lake/build/ir/FrogModel/Challenge.*
# then Comparator, as the job comparator of .github/workflows/ci.yml runs it (about 50 minutes with nanoda on 4 threads, 9 GB of memory)
```

Full check, from source (about 1 hour on 4 cores), then Comparator:

```sh
lake exe cache get && code/formal-proof/clean_build.sh
```

The certificate, again (`code/certificate`, Rust 1.98.1 as `rust-toolchain.toml` pins it; 3 to 8 minutes on 2 cores):

```sh
code/certificate/run_occupations.sh && code/certificate/run_gen.sh
```

The table, again (`code/table`, Rust; 25 to 40 minutes on 1 core for the two steps, seconds for the table):

```sh
code/table/run_iterates.sh && code/table/run_table.sh
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
rev = "v1.0.0"
```

then `lake update frog-model-tree`, `lake exe cache get` and `lake build`, which downloads the build archive of the release. A module that imports `FrogModel.Solution` also needs the data modules, written by `code/g3k/gen.sh` in the directory of the package.

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export) and [landrun](https://github.com/zouuup/landrun): the check of the statement in CI.
- [nanoda](https://github.com/ammkrn/nanoda_lib) of Chris Bailey (Apache 2.0), commit `3a2407216ee84a75f9e1aead6803d0578be06ae7`: the second implementation of the Lean kernel, which Comparator runs to check again every declaration the theorem depends on.
- [Rust](https://www.rust-lang.org/) with [num-bigint, num-rational, num-integer and num-traits](https://github.com/rust-num) (MIT or Apache 2.0): the programs that wrote the table and the certificate.
- [PARI/GP](https://pari.math.u-bordeaux.fr/): the constants of the paper and the table of Appendix A.

## Citation

```bibtex
@misc{frog-model-tree,
  title     = {The frog model on the 4-ary tree is transient},
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
