# Records

The outputs of the runs behind the figures for d = 3 in Section 16 of the paper, on the workstation of Section 16.5 (AMD Ryzen 9 5900X, 12 cores, 24 threads, 64 GB of memory). The records name commits of the development branch, which the release commit squashes, so the link to this repository is by content: the sha256 of the files that the Comparator record lists, and the hashes of the Lean sources (with the data modules written from the assets), of `lakefile.toml` and of `lake-manifest.json` at the head of the last part of `build/out/release-build-clean_build.out`, are those of the files of this repository. Each run had a memory cap with no swap and a CPU quota, given below; other work shared the machine. In the outputs, `TREE` is this repository, `ASSETS` the directory of the release assets (unpacked as in `README.md`), `SCRATCH` a temporary directory and `~` the home directory.

## build

`build/release-build.sh TREE ASSETS` writes the data modules from the assets and compiles the package as the jobs `data`, `data3`, `build-N` and `lean` of `.github/workflows/ci.yml` do, then runs the checks of the job `lean`: every target up to date, the messages of every module, `code/formal-proof/main_axioms.lean`, the negative controls of `code/d3chain/neg` and `code/formal-proof/facts.lean`. It ran with `LEAN_NUM_THREADS=2`, a memory cap of 10 GiB and a quota of 4 CPUs; the output records the 4 CPUs it sees, and the memory cap is not in it.

`build/out/release-build.out` has three parts, each headed by its commit, and keeps the last 40 lines of the output of each step:

1. the full build, from an empty build directory, and the checks;
2. `POST=1`: the checks again, after a fix of the filter of the messages (Lean prints the `sorry` of the two challenges in backquotes);
3. `RESUME=1`: after the comment changes of the final review, `code/formal-proof/clean_build.sh` on the build directory of the first part (it compiles again the modules whose comments changed), then the checks.

With comments removed, the Lean files are the same at the three commits. The other files hold the complete outputs, except that of `lake build --no-build` on the targets, kept in its last 40 lines only: `build/out/release-build-clean_build.out` is the log of `clean_build.sh` (one line per call of `lake`, with its time and memory peak), `build/out/release-build-modules.txt` the time of every module, `build/out/release-build-replay.txt` the messages of every module at the end of the third part, `build/out/release-build-messages.txt` their warnings and infos, and `build/out/release-build/` the outputs of the three data steps. `build/release-build-times.sh` writes `build/out/release-build-times.out`: the parts with their times, and the module times of the full build summed by group.

## writers

`writers/writers-local.sh TREE GPDIR` runs the job `writers3` of `ci.yml`: `code/m1run/run.sh`, `code/d3cert/run.sh` and `code/dcheck/run.sh`, with PARI/GP 2.15.4 built from source in `GPDIR` and Rust 1.98.1, under a memory cap of 4 GiB and a quota of 2 CPUs; the output records the 2 CPUs it sees, and the memory cap is not in it. Output: `writers/out/writers-local.out`.

## nanoda

`LEAN4EXPORT=... NANODA=... NANODA_REV=... nanoda/run_nanoda.sh TREE SCRATCH` exports from the built package the closures of Proposition 15.2, Lemma 14.3 and the theorem behind Theorem 14.1, and checks each with nanoda on one thread (`nanoda/nanoda.json`). lean4export and nanoda are at the commits of the job `comparator` of `ci.yml`. It ran under a memory cap of 10 GiB and a quota of 4 CPUs. Output: `nanoda/out/nanoda.txt`.

## comparator

`MEM=10G CPUS=4 comparator/run_comparator.sh TREE config-recurrent.json`, with `COMPARATOR`, `COMPARATOR_LANDRUN`, `COMPARATOR_LEAN4EXPORT`, `COMPARATOR_NANODA` and `NANODA_REV` set to the programs and commits of the job `comparator` of `ci.yml` (Comparator with `.github/comparator-lean-kernel.patch`), checks `FrogModel.recurrent_three` against `FrogModel/ChallengeRecurrent.lean` with nanoda as the job does, on the built tree, in a systemd service with a memory cap of 10 GiB, no swap and a quota of 4 CPUs. The memory peak is that of the service's control group, page cache included; a peak at the cap bounds the memory of the run and does not measure it. Output: `comparator/out/comparator.txt`.
