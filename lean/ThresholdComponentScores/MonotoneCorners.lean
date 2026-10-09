import ThresholdComponentScores.Monotone

namespace ThresholdComponentScores.Instance
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (I : Instance V q)

def lowerCorner (e : ℚ) : V → ℚ := fun v => I.baseline v - e
def upperCorner (e : ℚ) : V → ℚ := fun v => I.baseline v + e

theorem lowerCorner_mem {e : ℚ} (he : 0 ≤ e) : I.lowerCorner e ∈ I.box e := by
  apply (I.mem_box_iff e _).2
  intro v
  dsimp [lowerCorner]
  constructor <;> linarith

theorem upperCorner_mem {e : ℚ} (he : 0 ≤ e) : I.upperCorner e ∈ I.box e := by
  apply (I.mem_box_iff e _).2
  intro v
  dsimp [upperCorner]
  constructor <;> linarith

theorem corner_bounds (hw : ∀ j, 0 ≤ I.weight j) (hm : Monotone I.weight)
    {e : ℚ} {y : V → ℚ} (hy : y ∈ I.box e) :
    I.score (I.lowerCorner e) ≤ I.score y ∧ I.score y ≤ I.score (I.upperCorner e) := by
  exact ⟨I.score_mono hw hm (fun v => ((I.mem_box_iff e y).1 hy v).1),
    I.score_mono hw hm (fun v => ((I.mem_box_iff e y).1 hy v).2)⟩

theorem lowerCorner_isLeast (hw : ∀ j, 0 ≤ I.weight j) (hm : Monotone I.weight)
    {e : ℚ} (he : 0 ≤ e) : IsLeast (I.scoreImage e) (I.score (I.lowerCorner e)) := by
  refine ⟨⟨I.lowerCorner e, I.lowerCorner_mem he, rfl⟩, ?_⟩
  rintro t ⟨y, hy, rfl⟩
  exact (I.corner_bounds hw hm hy).1

theorem upperCorner_isGreatest (hw : ∀ j, 0 ≤ I.weight j) (hm : Monotone I.weight)
    {e : ℚ} (he : 0 ≤ e) : IsGreatest (I.scoreImage e) (I.score (I.upperCorner e)) := by
  refine ⟨⟨I.upperCorner e, I.upperCorner_mem he, rfl⟩, ?_⟩
  rintro t ⟨y, hy, rfl⟩
  exact (I.corner_bounds hw hm hy).2

theorem corner_extrema (hw : ∀ j, 0 ≤ I.weight j) (hm : Monotone I.weight)
    {e : ℚ} (he : 0 ≤ e) :
    IsLeast (I.scoreImage e) (I.score (I.lowerCorner e)) ∧
    IsGreatest (I.scoreImage e) (I.score (I.upperCorner e)) :=
  ⟨I.lowerCorner_isLeast hw hm he, I.upperCorner_isGreatest hw hm he⟩

/-- REACH asks for at least K, not exact equality with K. -/
def ReachAtLeast (e K : ℚ) : Prop := ∃ y ∈ I.box e, K ≤ I.score y

noncomputable def computeCornerReach (e K : ℚ) : Bool :=
  decide (K ≤ I.score (I.upperCorner e))

noncomputable def computeCornerMin (e : ℚ) : ℚ := I.score (I.lowerCorner e)
noncomputable def computeCornerMax (e : ℚ) : ℚ := I.score (I.upperCorner e)
noncomputable def computeCornerEndpoints (e : ℚ) : ℚ × ℚ :=
  (I.computeCornerMin e, I.computeCornerMax e)

theorem computeCornerReach_correct (hw : ∀ j, 0 ≤ I.weight j) (hm : Monotone I.weight)
    {e K : ℚ} (he : 0 ≤ e) : I.computeCornerReach e K = true ↔ I.ReachAtLeast e K := by
  simp only [computeCornerReach, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨I.upperCorner e, I.upperCorner_mem he, h⟩
  · rintro ⟨y, hy, h⟩
    exact h.trans (I.corner_bounds hw hm hy).2

theorem computeCornerMin_correct (hw : ∀ j, 0 ≤ I.weight j) (hm : Monotone I.weight)
    {e : ℚ} (he : 0 ≤ e) : IsLeast (I.scoreImage e) (I.computeCornerMin e) :=
  I.lowerCorner_isLeast hw hm he

theorem computeCornerMax_correct (hw : ∀ j, 0 ≤ I.weight j) (hm : Monotone I.weight)
    {e : ℚ} (he : 0 ≤ e) : IsGreatest (I.scoreImage e) (I.computeCornerMax e) :=
  I.upperCorner_isGreatest hw hm he

theorem computeCornerEndpoints_correct (hw : ∀ j, 0 ≤ I.weight j) (hm : Monotone I.weight)
    {e : ℚ} (he : 0 ≤ e) :
    IsLeast (I.scoreImage e) (I.computeCornerEndpoints e).1 ∧
    IsGreatest (I.scoreImage e) (I.computeCornerEndpoints e).2 :=
  I.corner_extrema hw hm he

end ThresholdComponentScores.Instance
