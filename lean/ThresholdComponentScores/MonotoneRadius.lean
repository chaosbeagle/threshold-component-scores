import ThresholdComponentScores.MonotoneCorners
import ThresholdComponentScores.RadiusFormula

namespace ThresholdComponentScores.Instance
variable {V : Type*} [Fintype V] [DecidableEq V] {q m : ℕ}
    (I : Instance V q) (K : ThresholdComponentScores.Categories m)

noncomputable def computeBoundaryInvariant (e : ℚ) : Bool :=
  decide (K.category (I.computeCornerMin e) = K.category (I.score I.baseline) ∧
    K.category (I.computeCornerMax e) = K.category (I.score I.baseline))

theorem categoryInvariant_iff_corners (hw : ∀ j, 0 ≤ I.weight j) (hm : Monotone I.weight)
    {e : ℚ} (he : 0 ≤ e) : I.categoryInvariant K e ↔
      K.category (I.score (I.lowerCorner e)) = K.category (I.score I.baseline) ∧
      K.category (I.score (I.upperCorner e)) = K.category (I.score I.baseline) :=
  I.categoryInvariant_iff_endpoints K (I.lowerCorner_mem he) (I.upperCorner_mem he)
    (fun _ hy => I.corner_bounds hw hm hy)

/-- Separate exact singleton test, including a finite radius's boundary point. -/
theorem computeBoundaryInvariant_correct (hw : ∀ j, 0 ≤ I.weight j) (hm : Monotone I.weight)
    {e : ℚ} (he : 0 ≤ e) :
    I.computeBoundaryInvariant K e = true ↔ I.boundaryInvariant K e := by
  simp only [computeBoundaryInvariant, decide_eq_true_eq, computeCornerMin, computeCornerMax,
    boundaryInvariant]
  exact (I.categoryInvariant_iff_corners K hw hm he).symm

/-- Finite critical endpoints whose cell representative fails the two-corner test. -/
noncomputable def cornerBadCriticalEndpoints : Finset ℚ := by
  classical
  exact I.criticalDistances.filter (fun d => ∃ C : I.RadiusCell,
    C.left = d ∧ I.computeBoundaryInvariant K C.representative = false)

theorem cornerBadCriticalEndpoints_eq (hw : ∀ j, 0 ≤ I.weight j)
    (hm : Monotone I.weight) : I.cornerBadCriticalEndpoints K = I.badCriticalEndpoints K := by
  classical
  apply Finset.filter_congr
  intro d hd
  apply exists_congr
  intro C
  apply and_congr_right
  intro hleft
  rw [Bool.eq_false_iff]
  exact not_congr (I.computeBoundaryInvariant_correct K hw hm
    (C.nonneg C.representative_mem))

/-- Typed radius answer: `none` denotes infinity; `some d` is the exact rational radius.
This classical finite specification makes no executable-runtime claim. -/
noncomputable def computeCornerRadius : Option ℚ := by
  classical
  exact if h : (I.cornerBadCriticalEndpoints K).Nonempty then
    some ((I.cornerBadCriticalEndpoints K).min' h) else none

noncomputable def radiusAnswerValue : Option ℚ → ENNReal
  | none => ⊤
  | some d => ENNReal.ofReal (d : ℝ)

theorem computeCornerRadius_correct (hw : ∀ j, 0 ≤ I.weight j)
    (hm : Monotone I.weight) :
    radiusAnswerValue (I.computeCornerRadius K) = I.categoryRadius K := by
  classical
  unfold computeCornerRadius
  rw [I.cornerBadCriticalEndpoints_eq K hw hm]
  split_ifs with h
  · exact (I.categoryRadius_eq_min_badCriticalEndpoints K h).symm
  · exact ((I.categoryRadius_eq_top_iff_no_bad_cells K).mpr
      (Finset.not_nonempty_iff_eq_empty.mp h)).symm

theorem computeCornerRadius_some_nonneg (hw : ∀ j, 0 ≤ I.weight j)
    (hm : Monotone I.weight) {d : ℚ} (hd : I.computeCornerRadius K = some d) : 0 ≤ d := by
  classical
  unfold computeCornerRadius at hd
  rw [I.cornerBadCriticalEndpoints_eq K hw hm] at hd
  split_ifs at hd with h
  · have heq := Option.some.inj hd
    rw [← heq]
    exact I.criticalDistances_nonneg
      (Finset.mem_filter.mp (Finset.min'_mem (I.badCriticalEndpoints K) h)).1

/-- The finite answer carries an independently correct boundary-invariance bit. -/
theorem computeCornerRadius_boundary_correct (hw : ∀ j, 0 ≤ I.weight j)
    (hm : Monotone I.weight) {d : ℚ} (hd : I.computeCornerRadius K = some d) :
    I.computeBoundaryInvariant K d = true ↔ I.boundaryInvariant K d :=
  I.computeBoundaryInvariant_correct K hw hm (I.computeCornerRadius_some_nonneg K hw hm hd)

end ThresholdComponentScores.Instance
