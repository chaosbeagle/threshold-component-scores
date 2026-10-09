import ThresholdComponentScores.Score

namespace ThresholdComponentScores.Instance
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (I : Instance V q)

/-- Both extrema have legal rational witnesses, including radius zero. -/
theorem attained_extrema {e : ℚ} (he : 0 ≤ e) :
    ∃ lo ∈ I.box e, ∃ hi ∈ I.box e,
      ∀ y ∈ I.box e, I.score lo ≤ I.score y ∧ I.score y ≤ I.score hi := by
  classical
  let S := {s : V → State q // s ∈ I.allowedStates e}
  letI : Nonempty S := ⟨⟨I.stateOf I.baseline,
    I.stateOf_mem_allowedStates (I.baseline_mem_box he)⟩⟩
  obtain ⟨slo, hlo⟩ := Finite.exists_min (fun s : S => I.stateScore s.val)
  obtain ⟨shi, hhi⟩ := Finite.exists_max (fun s : S => I.stateScore s.val)
  obtain ⟨hlo_mem, hlo_state⟩ := I.liftState_spec he slo.property
  obtain ⟨hhi_mem, hhi_state⟩ := I.liftState_spec he shi.property
  refine ⟨I.liftState e slo.val, hlo_mem, I.liftState e shi.val, hhi_mem, ?_⟩
  intro y hy
  rw [I.score_eq_stateScore, I.score_eq_stateScore, I.score_eq_stateScore,
    hlo_state, hhi_state]
  exact ⟨hlo ⟨I.stateOf y, I.stateOf_mem_allowedStates hy⟩,
    hhi ⟨I.stateOf y, I.stateOf_mem_allowedStates hy⟩⟩

theorem scoreImage_has_endpoints {e : ℚ} (he : 0 ≤ e) :
    ∃ l u : ℚ, IsLeast (I.scoreImage e) l ∧ IsGreatest (I.scoreImage e) u := by
  obtain ⟨lo, hlo, hi, hhi, h⟩ := I.attained_extrema he
  refine ⟨I.score lo, I.score hi, ⟨⟨lo, hlo, rfl⟩, ?_⟩,
    ⟨⟨hi, hhi, rfl⟩, ?_⟩⟩
  · rintro t ⟨y, hy, rfl⟩
    exact (h y hy).1
  · rintro t ⟨y, hy, rfl⟩
    exact (h y hy).2

/-- Exact largest absolute error: one endpoint attains the larger deviation. -/
theorem largest_absolute_error {e : ℚ} (he : 0 ≤ e) :
    ∃ lo ∈ I.box e, ∃ hi ∈ I.box e,
      (∀ y ∈ I.box e, I.score lo ≤ I.score y ∧ I.score y ≤ I.score hi) ∧
      IsGreatest ((fun y => |I.score y - I.score I.baseline|) '' I.box e)
        (max (I.score I.baseline - I.score lo) (I.score hi - I.score I.baseline)) := by
  obtain ⟨lo, hlo, hi, hhi, h⟩ := I.attained_extrema he
  have hb := h I.baseline (I.baseline_mem_box he)
  refine ⟨lo, hlo, hi, hhi, h, ?_, ?_⟩
  · by_cases hh : I.score I.baseline - I.score lo ≤ I.score hi - I.score I.baseline
    · refine ⟨hi, hhi, ?_⟩
      change |I.score hi - I.score I.baseline| = _
      rw [max_eq_right hh, abs_of_nonneg (sub_nonneg.mpr hb.2)]
    · refine ⟨lo, hlo, ?_⟩
      change |I.score lo - I.score I.baseline| = _
      rw [max_eq_left (le_of_not_ge hh), abs_of_nonpos (sub_nonpos.mpr hb.1)]
      ring
  · rintro t ⟨y, hy, rfl⟩
    apply abs_le.mpr
    have hyb := h y hy
    have h₁ := le_max_left (I.score I.baseline - I.score lo) (I.score hi - I.score I.baseline)
    have h₂ := le_max_right (I.score I.baseline - I.score lo) (I.score hi - I.score I.baseline)
    constructor <;> linarith

end ThresholdComponentScores.Instance
