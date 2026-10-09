# Pinned dependencies

Compiler: **Lean 4.32.0**, selected by [`lean/lean-toolchain`](lean/lean-toolchain).

Direct dependency: Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`, selected in [`lean/lakefile.toml`](lean/lakefile.toml).

The complete resolved dependency graph is committed in [`lean/lake-manifest.json`](lean/lake-manifest.json). Each `rev` below is an exact commit; an upstream `inputRev` such as `main` is descriptive and does not replace the resolved revision during reproduction.

| Package | Commit |
| --- | --- |
| [mathlib](https://github.com/leanprover-community/mathlib4/tree/81a5d257c8e410db227a6665ed08f64fea08e997) | `81a5d257c8e410db227a6665ed08f64fea08e997` |
| [plausible](https://github.com/leanprover-community/plausible/tree/e12c1910fe855cbfc38803cd4e55543906d5fa62) | `e12c1910fe855cbfc38803cd4e55543906d5fa62` |
| [LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient/tree/c5d5b8fe6e5158def25cd28eb94e4141ad97c843) | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| [importGraph](https://github.com/leanprover-community/import-graph/tree/7e9612bf0b9ee66db3cb5b9988a35afc706f5a12) | `7e9612bf0b9ee66db3cb5b9988a35afc706f5a12` |
| [proofwidgets](https://github.com/leanprover-community/ProofWidgets4/tree/6e311e2a844da9b2cc3971187df2fe0066947b93) | `6e311e2a844da9b2cc3971187df2fe0066947b93` |
| [aesop](https://github.com/leanprover-community/aesop/tree/a7dbf0c63b694e47f425f3dcddbc0e178bb432d3) | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` |
| [Qq](https://github.com/leanprover-community/quote4/tree/38d591e778f100aec9762bb582f9c7f55f50e9dc) | `38d591e778f100aec9762bb582f9c7f55f50e9dc` |
| [batteries](https://github.com/leanprover-community/batteries/tree/023ce7d62a0531e22a5331e20b587817a80d49ff) | `023ce7d62a0531e22a5331e20b587817a80d49ff` |
| [Cli](https://github.com/leanprover/lean4-cli/tree/88679d088c9720c27ebdf2ba4dafe17341747f94) | `88679d088c9720c27ebdf2ba4dafe17341747f94` |

Dependencies are fetched from their upstream repositories; their sources, compiled binaries, and caches are not bundled. Each dependency retains its own upstream license. See [build instructions](BUILD.md).
