# Release assets

Data too large for git are assets of the GitHub release (tag `v1.0.0`), with these sha256 sums. They are uploaded to a draft release before the tag is pushed, or taken from the previous release when this file has not changed.

```
51e5638ac02f22001cebf9437539bbb7d3c8c35c20afa4fbad256e88a2fc6247  frog-model-tree-certificate.v4.zst
```

| File                                 | Size (compressed / unpacked) | Content                                                                                                                                                                                                                                  |
| ------------------------------------ | ---------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `frog-model-tree-certificate.v4.zst` | 113 MB / 250 MB              | the certificate of Section 7 of the paper: the 159786 states with their flags, the values of the two linear systems and the plan (format: `code/certificate/FORMAT.md`); `code/g3k/gen.sh` writes the Lean data modules from it, unpacked |
