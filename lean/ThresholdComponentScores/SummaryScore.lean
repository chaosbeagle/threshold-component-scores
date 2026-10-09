import ThresholdComponentScores.Score
import ThresholdComponentScores.SummaryGraph

namespace ThresholdComponentScores.Instance
open StableSummary
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (I : Instance V q)

/-- Concrete projection: a singleton keeps its state; stable fibres take their maximum bin. -/
noncomputable def summaryProjection (S U : Finset V) (s : V → State q) :
    Node I.graph S U → State q := by
  classical
  exact fun n => if support n ⊆ I.stateActive s then
    some (I.stateMaximum (support n) s) else none

noncomputable def summaryActive {S U : Finset V} (r : Node I.graph S U → State q) :
    Finset (Node I.graph S U) := by
  classical
  exact Finset.univ.filter (fun n => (r n).isSome)

noncomputable def summaryMass {S U : Finset V} (D : Finset (Node I.graph S U)) : ℕ :=
  ∑ n ∈ D, (support n).card

noncomputable def summaryArea {S U : Finset V} (D : Finset (Node I.graph S U)) : ℚ :=
  ∑ n ∈ D, I.areaSum (support n)

noncomputable def summaryMaximum {S U : Finset V} (D : Finset (Node I.graph S U))
    (r : Node I.graph S U → State q) : Fin (q+1) :=
  D.sup (fun n => (r n).getD 0)

/-- Standalone contracted graph score, gated by original vertex mass. -/
noncomputable def summaryScore (S U : Finset V) (r : Node I.graph S U → State q) : ℚ := by
  classical
  exact ∑ D ∈ components (StableSummary.graph I.graph S U) (I.summaryActive r),
    if I.gate ≤ I.summaryMass D then I.summaryArea D * I.weight (I.summaryMaximum D r) else 0

@[simp] theorem summaryActive_projection (S U : Finset V) (s : V → State q) :
    I.summaryActive (I.summaryProjection S U s) = activeNodes (I.stateActive s) := by
  classical
  ext n
  simp [summaryActive, summaryProjection, activeNodes]

theorem summaryProjection_active {S U : Finset V} {s : V → State q} {n : Node I.graph S U}
    (hn : n ∈ activeNodes (I.stateActive s)) :
    I.summaryProjection S U s n = some (I.stateMaximum (support n) s) := by
  classical
  simp [summaryProjection, mem_activeNodes.mp hn]

theorem stateMaximum_expand {S U : Finset V} (D : Finset (Node I.graph S U))
    (s : V → State q) (hD : D ⊆ activeNodes (I.stateActive s)) :
    I.stateMaximum (expand D) s = I.summaryMaximum D (I.summaryProjection S U s) := by
  classical
  unfold stateMaximum summaryMaximum
  rw [sup_expand]
  apply Finset.sup_congr rfl
  intro n hn
  rw [I.summaryProjection_active (hD hn)]
  rfl

/-- Concrete source score factors through the actual stable-component contraction. -/
theorem stateScore_eq_summaryScore {S U : Finset V} {s : V → State q}
    (hSU : Disjoint S U) (hSA : S ⊆ I.stateActive s)
    (hAU : I.stateActive s ⊆ S ∪ U) :
    I.stateScore s = I.summaryScore S U (I.summaryProjection S U s) := by
  classical
  unfold stateScore summaryScore
  rw [I.summaryActive_projection, ← components_image_expand hSU hSA hAU]
  rw [Finset.sum_image (fun _ _ _ _ h => expand_injective hSU h)]
  apply Finset.sum_congr rfl
  intro D hD
  have hcard : (expand D).card = I.summaryMass D := card_expand hSU D
  have harea : I.areaSum (expand D) = I.summaryArea D := sum_expand hSU D I.area
  have hmax := I.stateMaximum_expand D s (components_subset_active hD)
  rw [hcard, harea, hmax]

/-- Uncertain nodes retain exactly their source state, including inactivity. -/
@[simp] theorem summaryProjection_uncertain (S U : Finset V) (s : V → State q)
    (u : {v // v ∈ U}) : I.summaryProjection S U s (.inl u) = s u.val := by
  classical
  cases hs : s u.val with
  | none => simp [summaryProjection, support, stateActive, stateMaximum, hs]
  | some j => simp [summaryProjection, support, stateActive, stateMaximum, hs]

/-- Stable component nodes retain their maximum bin rather than a numerical weight. -/
theorem summaryProjection_stable {S U : Finset V} (s : V → State q)
    (hSA : S ⊆ I.stateActive s) (C : {C // C ∈ components I.graph S}) :
    I.summaryProjection S U s (.inr C) = some (I.stateMaximum C.val s) := by
  apply I.summaryProjection_active
  exact mem_activeNodes.mpr ((components_subset_active C.property).trans hSA)

end ThresholdComponentScores.Instance
