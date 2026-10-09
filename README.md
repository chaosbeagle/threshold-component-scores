# Exact robustness and complexity of threshold component scores

Exact robustness guarantees and computational limits for graph-based threshold component scoring, with a companion Lean formalization of its semantic core.

The model is motivated by coronary artery calcium scoring. It combines threshold activation, connected components, a minimum component size, and weights determined by maximum intensity. The results concern the stated mathematical model; they do not establish clinical validity.

## Read and reproduce

1. **Article:** [Read the PDF](paper/threshold-component-scores.pdf).
2. **Lean project:** [Browse the source](lean/) and [formal verification coverage](docs/formal-coverage.md).
3. **Pinned dependencies:** [Lean, Mathlib, and all transitive revisions](DEPENDENCIES.md).
4. **Build instructions:** [Compile and audit the Lean project](BUILD.md).
5. **Project background:** [English](docs/project.en.md) · [繁體中文](docs/project.zh-TW.md).

## Results and formal scope

The article studies finite-state score-image equivalence, attained extrema, lossless stable-component summaries, category-invariance radii with separate boundary tests, monotonicity, and computational complexity.

The Lean sources cover the exact rational graph model and its semantic results: finite reduction, score extrema, summary construction and rational lifting, category radius and boundary conditions, and corner semantics for nonnegative nondecreasing weights.

Complexity classifications, hardness reductions, binary encodings, bit/runtime bounds, and common-offset equivalence remain paper proofs. The typed corner procedures are noncomputable mathematical specifications. The complete article is not claimed to be Lean-verified. See the [clause-by-clause coverage map](docs/formal-coverage.md).

## Quick start

Install [elan](https://github.com/leanprover/elan), Git, and Bash, then run:

```bash
git clone https://github.com/chaosbeagle/threshold-component-scores.git
cd threshold-component-scores/lean
bash build.sh
```

The build uses Lean **4.32.0** and the committed dependency lockfile. It compiles the proof modules and checks theorem types and transitive kernel axioms. See [BUILD.md](BUILD.md) for Windows commands and separate audit instructions.
