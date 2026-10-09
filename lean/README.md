# Lean formalization of threshold component scores

The library root is [ThresholdComponentScores.lean](ThresholdComponentScores.lean). Its 17 proof modules formalize a finite nonempty rational graph model with nonnegative areas, a positive cardinality gate, strictly increasing thresholds, and arbitrary signed weights. Activation is inclusive at its threshold; breakpoint equality belongs to the upper bin. Component weight is selected by the maximum bin.

Nonnegative nondecreasing weights are required only by the monotonicity and corner theorems. The general model allows zero areas, disconnected graphs, empty active and summary sets, and gates larger than the vertex count.

- [Build and audit](../BUILD.md)
- [Pinned dependency versions](../DEPENDENCIES.md)
- [Formal scope and paper correspondence](../docs/formal-coverage.md)
- [Explicit theorem type and axiom checks](AxiomAudit.lean)
- [Complete namespace axiom allowlist](KernelAudit.lean)

The audits permit only `propext`, `Classical.choice`, and `Quot.sound`. Noncomputable specifications do not supply executable algorithms or runtime proofs.
