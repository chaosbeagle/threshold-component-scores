import ThresholdComponentScores.SummaryRealization
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace ThresholdComponentScores

/-- Source-free mathematical summary payload. The node type may be empty.
No source graph, original intensities, original areas, or vertex supports are fields. -/
structure SummaryPayload (W : Type*) [Fintype W] (q : ℕ) where
  graph : SimpleGraph W
  mass : W → ℕ
  area : W → ℚ
  gate : ℕ
  weight : Fin (q+1) → ℚ
  domain : W → Finset (State q)

namespace SummaryPayload
variable {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ} (P : SummaryPayload W q)

def assignments : Set (W → State q) := {r | ∀ w, r w ∈ P.domain w}

noncomputable def active (P : SummaryPayload W q) (r : W → State q) : Finset W := by
  classical
  exact Finset.univ.filter (fun w => (r w).isSome)

/-- This evaluator accesses only the summary graph and aggregate node data. -/
noncomputable def score (r : W → State q) : ℚ := by
  classical
  exact ∑ D ∈ components P.graph (P.active r),
    if P.gate ≤ ∑ w ∈ D, P.mass w then
      (∑ w ∈ D, P.area w) * P.weight (D.sup (fun w => (r w).getD 0)) else 0

/-- A summary with no nodes has its unique empty assignment and score zero. -/
theorem score_of_isEmpty [IsEmpty W] (r : W → State q) : P.score r = 0 := by
  classical
  simp [score, active, components]

end SummaryPayload

namespace Instance
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (I : Instance V q)

noncomputable def summaryLocalDomain (e : ℚ) : I.SummaryNode e → Finset (State q) := by
  classical
  exact fun n => match n with
    | .inl u => insert none ((Finset.Icc (I.thresholds.bin I.thresholds.tau)
        (I.thresholds.bin (I.baseline u.val + e))).image some)
    | .inr C => (Finset.Icc (I.summaryAlpha e C.val) (I.summaryBeta e C.val)).image some

/-- Source data is used to construct aggregates, then discarded by the evaluator. -/
noncomputable def toSummaryPayload (e : ℚ) : SummaryPayload (I.SummaryNode e) q where
  graph := StableSummary.graph I.graph (I.stableVertices e) (I.uncertainVertices e)
  mass := fun n => (StableSummary.support n).card
  area := fun n => I.areaSum (StableSummary.support n)
  gate := I.gate
  weight := I.weight
  domain := I.summaryLocalDomain e


theorem payload_mass_pos (e : ℚ) (n : I.SummaryNode e) :
    0 < (I.toSummaryPayload e).mass n :=
  Finset.card_pos.mpr (StableSummary.support_nonempty n)

theorem payload_area_nonneg (e : ℚ) (n : I.SummaryNode e) :
    0 ≤ (I.toSummaryPayload e).area n := by
  exact Finset.sum_nonneg (fun v _ => I.area_nonneg v)

theorem payload_assignments_eq (e : ℚ) :
    (I.toSummaryPayload e).assignments = I.summaryAllowed e := by
  classical
  ext r
  change (∀ n, r n ∈ I.summaryLocalDomain e n) ↔ _
  constructor
  · intro h
    constructor
    · intro u
      have hu := h (.inl u)
      simp only [summaryLocalDomain, Finset.mem_insert, Finset.mem_image, Finset.mem_Icc] at hu
      rcases hu with hn | ⟨j, hj, heq⟩
      · exact Or.inl hn
      · exact Or.inr ⟨j, heq.symm, hj.1, hj.2⟩
    · intro C
      have hC := h (.inr C)
      simp only [summaryLocalDomain, Finset.mem_image, Finset.mem_Icc] at hC
      obtain ⟨j, hj, heq⟩ := hC
      exact ⟨j, heq.symm, hj.1, hj.2⟩
  · intro h n
    cases n with
    | inl u =>
      simp only [summaryLocalDomain, Finset.mem_insert, Finset.mem_image, Finset.mem_Icc]
      rcases h.1 u with hn | ⟨j, heq, hlo, hhi⟩
      · exact Or.inl hn
      · exact Or.inr ⟨j, ⟨hlo,hhi⟩, heq.symm⟩
    | inr C =>
      simp only [summaryLocalDomain, Finset.mem_image, Finset.mem_Icc]
      obtain ⟨j, heq, hlo, hhi⟩ := h.2 C
      exact ⟨j, ⟨hlo,hhi⟩, heq.symm⟩

theorem payload_score_eq (e : ℚ) (r : I.SummaryNode e → State q) :
    (I.toSummaryPayload e).score r = I.contractedScore e r := rfl

/-- The source-free payload has exactly the attainable source score image. -/
theorem scoreImage_eq_payloadImage {e : ℚ} (he : 0 ≤ e) :
    I.scoreImage e = (I.toSummaryPayload e).score '' (I.toSummaryPayload e).assignments := by
  rw [I.payload_assignments_eq]
  exact I.scoreImage_eq_contractedImage he

/-- Every source-free payload assignment lifts to an exact legal rational witness. -/
theorem payload_rational_lift {e : ℚ} (he : 0 ≤ e)
    {r : I.SummaryNode e → State q} (hr : r ∈ (I.toSummaryPayload e).assignments) :
    ∃ y ∈ I.box e, I.projectSummary e (I.stateOf y) = r ∧
      I.score y = (I.toSummaryPayload e).score r := by
  rw [I.payload_assignments_eq] at hr
  exact I.contractedScore_rational_lift he hr

end Instance
end ThresholdComponentScores
