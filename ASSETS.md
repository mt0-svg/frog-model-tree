# Release assets

Data too large for git are assets of the GitHub release, with these sha256 sums. They are uploaded to a draft release before the tag is pushed, or taken from the previous release when this file has not changed.

```
51e5638ac02f22001cebf9437539bbb7d3c8c35c20afa4fbad256e88a2fc6247  frog-model-tree-certificate.v4.zst
ec73fa480ae41372b6da481b221f42c1ae49ddc576d2cdf7b2dee8616a07e68e  frog-model-tree-d3-certificate.tar.zst
b1b8cd68214687b85ba670419c5c260987160db9cad9009a93e79440540a5169  frog-model-tree-d3-m1run.txt.xz
```

| File                                     | Size (compressed / unpacked) | Content                                                                                                                                                                                                                                  |
| ---------------------------------------- | ---------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `frog-model-tree-certificate.v4.zst`     | 113 MB / 250 MB              | the certificate of Section 7 of the paper: the 159786 states with their flags, the values of the two linear systems and the plan (format: `code/certificate/FORMAT.md`); `code/g3k/gen.sh` writes the Lean data modules from it, unpacked |
| `frog-model-tree-d3-certificate.tar.zst` | 9.9 MB / 31 MB, 510 files    | the certificate of the recurrence on the 3-ary tree: `d3-certificate/manifest.txt` and the files it names (the seed, the states of the chain of steps, the extension, the check); `code/d3chain/gen.sh` writes the Lean data modules from `d3-certificate/`, unpacked |
| `frog-model-tree-d3-m1run.txt.xz`        | 194 KB / 555 KB              | the stored run of the lower model at heights 0 to 99 and its top rows; `code/m1gen/gen.sh` writes the Lean data modules from it and from `d3-certificate/masses100.txt`                                                                  |
