import ThresholdComponentScores.Score
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace ThresholdComponentScores.Instance
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (I : Instance V q)

noncomputable def componentMultiplier (C : Finset V) (y : V → ℚ) : ℚ :=
  if I.gate ≤ C.card then I.weight (I.thresholds.bin (I.componentMaximum C y)) else 0

noncomputable def vertexContribution (y : V → ℚ) (v : V) : ℚ :=
  I.area v * I.componentMultiplier (component I.graph (I.active y) v) y

theorem active_mono {y z : V → ℚ} (h : ∀ v, y v ≤ z v) : I.active y ⊆ I.active z := by
  intro v hv
  exact (I.mem_active z v).2 ((I.mem_active y v).1 hv |>.trans (h v))

theorem componentMaximum_mono {C D : Finset V} (hC : C.Nonempty) (hCD : C ⊆ D)
    {y z : V → ℚ} (hyz : ∀ v, y v ≤ z v) :
    I.componentMaximum C y ≤ I.componentMaximum D z := by
  classical
  simp only [componentMaximum, dif_pos hC, dif_pos (hC.mono hCD)]
  exact Finset.sup'_le hC y (fun v hv => (hyz v).trans (Finset.le_sup' z (hCD hv)))

theorem componentMultiplier_nonneg (hw : ∀ j, 0 ≤ I.weight j) (C : Finset V)
    (y : V → ℚ) : 0 ≤ I.componentMultiplier C y := by
  unfold componentMultiplier
  split_ifs
  · exact hw _
  · exact le_rfl

theorem componentMultiplier_mono (hw : ∀ j, 0 ≤ I.weight j) (hm : Monotone I.weight)
    {C D : Finset V} (hC : C.Nonempty) (hCD : C ⊆ D)
    {y z : V → ℚ} (hyz : ∀ v, y v ≤ z v) :
    I.componentMultiplier C y ≤ I.componentMultiplier D z := by
  classical
  by_cases hg : I.gate ≤ C.card
  · have hgD : I.gate ≤ D.card := hg.trans (Finset.card_le_card hCD)
    simp only [componentMultiplier, if_pos hg, if_pos hgD]
    exact hm (I.thresholds.bin_monotone (I.componentMaximum_mono hC hCD hyz))
  · rw [componentMultiplier, if_neg hg]
    exact I.componentMultiplier_nonneg hw D z

/-- The component sum is exactly a sum of the original vertices' contributions. -/
theorem score_eq_sum_vertices (y : V → ℚ) :
    I.score y = ∑ v ∈ I.active y, I.vertexContribution y v := by
  classical
  have hcover : (components I.graph (I.active y)).biUnion id = I.active y := by
    ext v
    simp only [Finset.mem_biUnion, id_eq]
    exact components_cover
  have hdis : (↑(components I.graph (I.active y)) : Set (Finset V)).PairwiseDisjoint id := by
    intro C hC D hD hne
    exact (components_disjoint_or_eq hC hD).resolve_right hne
  rw [← hcover, Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro C hC
  have heq : ∀ v ∈ C, component I.graph (I.active y) v = C := by
    intro v hv
    exact components_eq_of_mem (component_mem_components (components_subset_active hC hv))
      hC (mem_component_self (components_subset_active hC hv)) hv
  change (if I.gate ≤ C.card then I.areaSum C *
    I.weight (I.thresholds.bin (I.componentMaximum C y)) else 0) = _
  simp only [vertexContribution, id_eq]
  rw [Finset.sum_congr rfl (fun v hv => by rw [heq v hv])]
  rw [← Finset.sum_mul]
  unfold componentMultiplier areaSum
  split_ifs <;> simp

/-- Genuine graph-component growth implies score monotonicity, including mergers and zero areas. -/
theorem score_mono (hw : ∀ j, 0 ≤ I.weight j) (hm : Monotone I.weight)
    {y z : V → ℚ} (hyz : ∀ v, y v ≤ z v) : I.score y ≤ I.score z := by
  classical
  rw [I.score_eq_sum_vertices, I.score_eq_sum_vertices]
  calc
    _ ≤ ∑ v ∈ I.active y, I.vertexContribution z v := by
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_left
        (I.componentMultiplier_mono hw hm (component_nonempty hv)
          (component_mono (I.active_mono hyz)) hyz) (I.area_nonneg v)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (I.active_mono hyz)
      intro v hv hnot
      exact mul_nonneg (I.area_nonneg v) (I.componentMultiplier_nonneg hw _ _)

end ThresholdComponentScores.Instance
