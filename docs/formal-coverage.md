# Formal verification coverage

This document describes the companion Lean sources for *Exact robustness and complexity of threshold component scores*. The correspondence uses the article's stable theorem labels. The article contains its own mathematical proofs; Lean verification covers the semantic results identified below, not the full paper or its complexity classifications.

## Reproducible dependency pins

- Lean toolchain: `leanprover/lean4:v4.32.0`
- Mathlib revision: `81a5d257c8e410db227a6665ed08f64fea08e997`
- Root library: `ThresholdComponentScores.lean`

Use the companion project's build instructions and dependency manifest to check the Lean sources. See [build instructions](../BUILD.md).

## Formalized source model

`ThresholdComponentScores.Instance` represents an arbitrary finite nonempty vertex type with a simple undirected graph, rational baseline intensities, nonnegative rational areas, strictly increasing rational density thresholds, a positive cardinality gate, and arbitrary rational weights. Its score sums over genuine connected components of the active graph, uses original vertex counts for the gate, and weights each component by its maximum bin. Activation and bin equality are inclusive at their thresholds; inactivity and upper bin boundaries are strict as in the article.

The general statements allow signed and nonmonotone weights, zero areas, disconnected graphs, empty active sets, zero density breakpoints, zero category cutpoints, and gates larger than the graph. A contracted summary can have no nodes. Nonnegativity and monotonicity of weights are required only by the monotonicity and corner results. No bounded graph size, fixed number of bins, or fixed gate is assumed by the general semantics.

## Theorem-to-declaration correspondence

Module paths below are relative to `lean/`. Unless otherwise specified, declaration names have namespace `ThresholdComponentScores.Instance`.

| Article result | Module and representative declarations | Verified statement |
| --- | --- | --- |
| Model in §2 | `ThresholdComponentScores/Components.lean`: `ThresholdComponentScores.mem_components_iff_maximal`, `ThresholdComponentScores.reachable_induce_iff`; `ThresholdComponentScores/Score.lean`: `ThresholdComponentScores.Instance`, `score`, `stateScore` | Actual active connected components; original areas, cardinality gate, and maximum-bin score |
| `lem:local` | `ThresholdComponentScores/Local.lean`, namespace `ThresholdComponentScores.Thresholds`: `allowed_none_iff`, `allowed_some_below_iff`, `allowed_some_top_iff`, `representative_spec` | Exact rational interval-state predicates and coordinate representatives, including endpoint conventions |
| `thm:finite` | `ThresholdComponentScores/Score.lean`: `liftState_spec`, `stateOf_surjOn`, `score_eq_stateScore`, `scoreImage_eq_stateImage`, `scoreImage_finite`, `scoreImage_nonempty` | Surjective rational state realization, equality of the actual source and finite-state score images, and finite nonempty range |
| `cor:range` | `ThresholdComponentScores/Range.lean`: `attained_extrema`, `scoreImage_has_endpoints`, `largest_absolute_error` | Attained rational extrema and exact largest absolute error |
| `lem:summarydomains` | `ThresholdComponentScores/SummaryDomains.lean`, namespace `ThresholdComponentScores.Thresholds`: `uncertain_allowed_iff`, `stable_max_bins_iff`, `stable_max_witness` | Exact uncertain-vertex domains and stable-component maximum-bin interval, with rational witnesses |
| `lem:contraction` | `ThresholdComponentScores/SummaryGraph.lean`, namespace `ThresholdComponentScores.StableSummary`: `reachable_iff`, `components_bijOn_expand`, `card_expand`, `sum_expand`, `sup_expand`; `ThresholdComponentScores/SummaryScore.lean`: `stateScore_eq_summaryScore`; `ThresholdComponentScores/SummaryPartition.lean`: `stateScore_eq_contractedScore` | Concrete summary-graph projection and lifting, expanded-component bijection, and preservation of original mass, area, maximum bin, and score |
| `thm:summary`, legality and surjectivity | `ThresholdComponentScores/SummaryPartition.lean`: `projectSummary_mem_summaryAllowed`; `ThresholdComponentScores/SummaryRealization.lean`: `exists_summary_realization`, `projectSummary_stateOf_surjOn`, `projectSummary_surjOn` | The actual radius-derived summary's independently specified local domains are exactly realizable by legal rational source vectors and source states |
| `thm:summary`, image and extrema | `ThresholdComponentScores/SummaryRealization.lean`: `scoreImage_eq_contractedImage`, `stateImage_eq_contractedImage`, `contractedScore_rational_lift`, `summary_attained_extrema`, `contracted_category_rational_lift` | Exact score images; rational score/category witnesses; attained summary extrema lifting to source extrema |
| `thm:summary`, independent evaluator | `ThresholdComponentScores/SummaryPayload.lean`: `ThresholdComponentScores.SummaryPayload`, `toSummaryPayload`, `payload_assignments_eq`, `payload_score_eq`, `scoreImage_eq_payloadImage`, `payload_rational_lift` | A summary evaluator using only the summary graph, aggregate masses and areas, gate, weights, and finite local domains, with exact image equality and rational lifting |
| `lem:cells` | `ThresholdComponentScores/RadiusCells.lean`: `allowed_cell_constant`, `allowedStates_cell_constant`, `scoreImage_cell_constant` | Allowed-state and score-image constancy on genuine singleton, consecutive-open, and tail cells of the threshold-distance set |
| `lem:endpointcategory` | `ThresholdComponentScores/Radius.lean`: `categoryInvariant_iff_states`, `categoryInvariant_iff_endpoints` | Category invariance equals the finite-state test and the attained-extrema test |
| `thm:radius` | `ThresholdComponentScores/RadiusFormula.lean`: `exists_radiusCell`, `badRadii_eq_union_bad_cells`, `categoryRadius_eq_top_iff_no_bad_cells`, `categoryRadius_eq_min_badCriticalEndpoints`, `finite_categoryRadius_mem_criticalDistances`, `finite_radius_and_boundary`; `ThresholdComponentScores/Radius.lean`: `categoryInvariant_zero` | The ENNReal infimum of the actual bad rational radii equals infinity or the minimum bad-cell left endpoint; finite critical-distance membership, separate boundary test, and invariance at zero |
| Critical-set bound in §5 | `ThresholdComponentScores/RadiusFormula.lean`: `criticalDistances_card_le` | At most `1 + n(q + 1)` distinct critical distances; this is not a runtime theorem |
| `prop:monotone`, score and corners | `ThresholdComponentScores/Monotone.lean`: `score_mono`; `ThresholdComponentScores/MonotoneCorners.lean`: `lowerCorner_mem`, `upperCorner_mem`, `lowerCorner_isLeast`, `upperCorner_isGreatest`, `corner_extrema` | Genuine original-graph coordinatewise score monotonicity under nonnegative nondecreasing weights and attained rational corner extrema |
| `prop:monotone`, typed short-task semantics | `ThresholdComponentScores/MonotoneCorners.lean`: `computeCornerReach_correct`, `computeCornerMin_correct`, `computeCornerMax_correct`, `computeCornerEndpoints_correct`; `ThresholdComponentScores/MonotoneRadius.lean`: `computeBoundaryInvariant_correct`, `computeCornerRadius_correct`, `computeCornerRadius_boundary_correct` | Typed semantic specifications for REACH ≥ K, MIN, MAX, ENDPOINTS, CATEGORYRADIUS, and the separate finite-boundary Boolean |

The summary bridge derives its partition from the source instance and the radius. Its image and lifting results do not assume the surjectivity or score-image equality that they prove. The payload evaluator contains no field for source intensities, original vertex supports, or the source graph; source data is used to construct its aggregates. Its finite domain representation is mathematical data, not the binary payload encoding of Appendix A.

`categoryRadius` is an infimum in `ENNReal` of the image of the set of bad nonnegative rational radii, rather than a radius supplied as an assumption. The finite formula does not assert that the infimal radius is itself bad. `computeCornerRadius` uses `Option ℚ`, with `none` interpreted as infinity by `radiusAnswerValue`; the boundary Boolean is checked separately at a finite returned radius.

## Paper-only results and limits

The following remain mathematical proofs in the article and are not formalized by this release:

| Article result | Scope outside the Lean development |
| --- | --- |
| `prop:summarysize`, `app:summarycodec` | Assignment-count and exact binary payload-size formulas; encoded aggregate-area bounds |
| `lem:bits`, Appendix A | Canonical encoders, exact raw-encoder-domain bit-length envelopes, short-output bounds, parser behavior, and arbitrary-bitstring validation |
| `thm:preprocess`, `cor:np` | Complete validation, preprocessing, graph-evaluation runtime, and NP membership |
| `thm:dp`, `lem:dpbound` | The complete dynamic program and its costed state/bit bounds |
| `lem:decomp`, `thm:fpt` | Decomposition algorithm and FPT/XP classifications |
| `thm:npcomplete`, `thm:widthhard`, `thm:multiway` | Fixed-weight NP-hardness, joint width–breakpoint lower bound, and two-breakpoint hardness |
| `thm:image` | Explicit-image output-size obstruction, including raw and supplied fixed-parameter families |
| `prop:monotone`, runtime assertions | Polynomial bit runtime and validation in raw and supplied-decomposition modes |
| `thm:offset` | Common-offset equivalence and joint threshold translation |
| `thm:classification`, `prop:closure`, `prop:signed`, `prop:category` | All-gate fixed-pair classification, closure algorithm, signed-weight hardness, and category-radius classification |
| Summary-width filtration | Width relationships between the summaries used in the article |

The typed corner procedures and graph evaluators are **noncomputable semantic specifications**. The proofs do not provide an extracted executable, a complete parser/validator, a polynomial runtime theorem, or an implementation verified against arbitrary binary task inputs. In particular, no encoding-length or explicit-image-obstruction result is included merely because the article proves it. General complexity classifications should not be described as Lean-verified.
