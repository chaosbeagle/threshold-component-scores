import ThresholdComponentScores.SummaryPartition

/-! Exact summary legality, rational realization, and attainable score images. -/
namespace ThresholdComponentScores.Instance
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (I : Instance V q)

/-- Every independent summary assignment has a rational source realization.
Stable fibres use the explicit one-coordinate witness from `stable_max_witness`. -/
theorem exists_summary_realization {e : ℚ} (he : 0 ≤ e)
    {r : I.SummaryNode e → State q} (hr : r ∈ I.summaryAllowed e) :
    ∃ y ∈ I.box e, I.projectSummary e (I.stateOf y) = r := by
  classical
  let SC := {C // C ∈ components I.graph (I.stableVertices e)}
  have hw (C : SC) : ∃ y : V → ℚ,
      (∀ v ∈ C.val, I.baseline v - e ≤ y v ∧ y v ≤ I.baseline v + e) ∧
      some (C.val.sup (fun v => I.thresholds.bin (y v))) = r (.inr C) := by
    obtain ⟨j, hj, hlo, hhi⟩ := hr.2 C
    obtain ⟨p, hp, hlegal, hmax⟩ := I.thresholds.stable_max_witness C.val
      (components_nonempty C.property) (fun v => I.baseline v - e)
      (fun v => I.baseline v + e) (by intro v hv; linarith)
      (by intro v hv; exact (I.mem_stableVertices e v).mp (components_subset_active C.property hv))
      j hlo hhi
    exact ⟨_, hlegal, by rw [hmax, hj]⟩
  choose ys hys using hw
  let cv (v : V) (hv : v ∈ I.stableVertices e) : SC :=
    ⟨component I.graph (I.stableVertices e) v, component_mem_components hv⟩
  let y : V → ℚ := fun v =>
    if hv : v ∈ I.stableVertices e then ys (cv v hv) v
    else if hu : v ∈ I.uncertainVertices e then
      I.thresholds.representative (I.baseline v - e) (r (.inl ⟨v, hu⟩))
    else I.baseline v
  have hunc (v : V) (hu : v ∈ I.uncertainVertices e) :
      I.thresholds.allowed (I.baseline v - e) (I.baseline v + e) (r (.inl ⟨v, hu⟩)) :=
    (I.thresholds.uncertain_allowed_iff ((I.mem_uncertainVertices e v).mp hu).1
      ((I.mem_uncertainVertices e v).mp hu).2 _).mpr (hr.1 ⟨v, hu⟩)
  have hyeq (C : SC) (v : V) (hv : v ∈ C.val) : y v = ys C v := by
    have hs := components_subset_active C.property hv
    have hc : cv v hs = C := Subtype.ext (components_eq_of_mem
      (component_mem_components hs) C.property (mem_component_self hs) hv)
    simp only [y, dif_pos hs, hc]
  have hy : y ∈ I.box e := by
    apply (I.mem_box_iff e y).mpr
    intro v
    by_cases hs : v ∈ I.stableVertices e
    · simpa only [y, dif_pos hs] using (hys (cv v hs)).1 v (mem_component_self hs)
    · by_cases hu : v ∈ I.uncertainVertices e
      · have h := I.thresholds.representative_spec (by linarith : I.baseline v - e ≤ I.baseline v + e) (hunc v hu)
        simpa only [y, dif_neg hs, dif_pos hu] using And.intro h.1 h.2.1
      · simp only [y, dif_neg hs, dif_neg hu]
        constructor <;> linarith
  refine ⟨y, hy, ?_⟩
  funext n
  cases n with
  | inl u =>
    rw [projectSummary, I.summaryProjection_uncertain]
    have hs : u.val ∉ I.stableVertices e := fun h =>
      Finset.disjoint_left.mp (I.stable_uncertain_disjoint e) h u.property
    have h := I.thresholds.representative_spec
      (by linarith : I.baseline u.val - e ≤ I.baseline u.val + e) (hunc u.val u.property)
    simpa only [stateOf, y, dif_neg hs, dif_pos u.property] using h.2.2
  | inr C =>
    rw [projectSummary, I.summaryProjection_stable _
      (I.stable_subset_stateActive (I.stateOf_mem_allowedStates hy))]
    have hmax : I.stateMaximum C.val (I.stateOf y) =
        C.val.sup (fun v => I.thresholds.bin (ys C v)) := by
      apply Finset.sup_congr rfl
      intro v hv
      have ha := (I.mem_stableVertices e v).mp (components_subset_active C.property hv)
      have hL := ((I.mem_box_iff e y).mp hy v).1
      change (I.thresholds.state (y v)).getD 0 = _
      rw [Thresholds.state, if_neg (not_lt.mpr (ha.trans hL))]
      simp only [Option.getD_some, hyeq C v hv]
    rw [hmax]
    exact (hys C).2

/-- Surjectivity is proved from the independent local domains, not assumed. -/
theorem projectSummary_stateOf_surjOn {e : ℚ} (he : 0 ≤ e) :
    Set.SurjOn (fun y => I.projectSummary e (I.stateOf y)) (I.box e) (I.summaryAllowed e) := by
  intro r hr
  exact I.exists_summary_realization he hr

/-- The standalone contracted score has exactly the source's attainable image. -/
theorem scoreImage_eq_contractedImage {e : ℚ} (he : 0 ≤ e) :
    I.scoreImage e = I.contractedScore e '' I.summaryAllowed e := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hs := I.stateOf_mem_allowedStates hy
    refine ⟨I.projectSummary e (I.stateOf y), I.projectSummary_mem_summaryAllowed hs, ?_⟩
    rw [I.score_eq_stateScore, I.stateScore_eq_contractedScore hs]
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨y, hy, hproj⟩ := I.exists_summary_realization he hr
    refine ⟨y, hy, ?_⟩
    rw [I.score_eq_stateScore, I.stateScore_eq_contractedScore (I.stateOf_mem_allowedStates hy), hproj]

/-- A summary assignment's score is attained by a legal rational source vector. -/
theorem contractedScore_rational_lift {e : ℚ} (he : 0 ≤ e)
    {r : I.SummaryNode e → State q} (hr : r ∈ I.summaryAllowed e) :
    ∃ y ∈ I.box e, I.projectSummary e (I.stateOf y) = r ∧ I.score y = I.contractedScore e r := by
  obtain ⟨y, hy, hp⟩ := I.exists_summary_realization he hr
  refine ⟨y, hy, hp, ?_⟩
  rw [I.score_eq_stateScore, I.stateScore_eq_contractedScore (I.stateOf_mem_allowedStates hy), hp]

/-- The finite-state projection is also onto the independently specified summary domain. -/
theorem projectSummary_surjOn {e : ℚ} (he : 0 ≤ e) :
    Set.SurjOn (I.projectSummary e) (I.allowedStates e) (I.summaryAllowed e) := by
  intro r hr
  obtain ⟨y, hy, hp⟩ := I.exists_summary_realization he hr
  exact ⟨I.stateOf y, I.stateOf_mem_allowedStates hy, hp⟩

theorem stateImage_eq_contractedImage {e : ℚ} (he : 0 ≤ e) :
    I.stateScore '' I.allowedStates e = I.contractedScore e '' I.summaryAllowed e := by
  rw [← I.scoreImage_eq_stateImage he, I.scoreImage_eq_contractedImage he]

/-- Summary extrema exist and their rational lifts attain the source extrema. -/
theorem summary_attained_extrema {e : ℚ} (he : 0 ≤ e) :
    ∃ rlo ∈ I.summaryAllowed e, ∃ rhi ∈ I.summaryAllowed e,
    ∃ lo ∈ I.box e, ∃ hi ∈ I.box e,
      I.projectSummary e (I.stateOf lo) = rlo ∧
      I.projectSummary e (I.stateOf hi) = rhi ∧
      I.score lo = I.contractedScore e rlo ∧
      I.score hi = I.contractedScore e rhi ∧
      (∀ r ∈ I.summaryAllowed e,
        I.contractedScore e rlo ≤ I.contractedScore e r ∧
        I.contractedScore e r ≤ I.contractedScore e rhi) ∧
      (∀ y ∈ I.box e, I.score lo ≤ I.score y ∧ I.score y ≤ I.score hi) := by
  classical
  let R := {r : I.SummaryNode e → State q // r ∈ I.summaryAllowed e}
  letI : Nonempty R := ⟨⟨I.projectSummary e (I.stateOf I.baseline),
    I.projectSummary_mem_summaryAllowed (I.stateOf_mem_allowedStates (I.baseline_mem_box he))⟩⟩
  obtain ⟨rlo, hlo⟩ := Finite.exists_min (fun r : R => I.contractedScore e r.val)
  obtain ⟨rhi, hhi⟩ := Finite.exists_max (fun r : R => I.contractedScore e r.val)
  obtain ⟨lo, hlobox, hlop, hlos⟩ := I.contractedScore_rational_lift he rlo.property
  obtain ⟨hi, hhibox, hhip, hhis⟩ := I.contractedScore_rational_lift he rhi.property
  refine ⟨rlo.val, rlo.property, rhi.val, rhi.property,
    lo, hlobox, hi, hhibox, hlop, hhip, hlos, hhis, ?_, ?_⟩
  · intro r hr
    exact ⟨hlo ⟨r, hr⟩, hhi ⟨r, hr⟩⟩
  · intro y hy
    have hs := I.stateOf_mem_allowedStates hy
    have hr := I.projectSummary_mem_summaryAllowed hs
    rw [hlos, hhis, I.score_eq_stateScore y, I.stateScore_eq_contractedScore hs]
    exact ⟨hlo ⟨_, hr⟩, hhi ⟨_, hr⟩⟩

/-- Any category function transfers exactly through the rational summary lift. -/
theorem contracted_category_rational_lift {K : Type*} (category : ℚ → K)
    {e : ℚ} (he : 0 ≤ e) {r : I.SummaryNode e → State q}
    (hr : r ∈ I.summaryAllowed e) :
    ∃ y ∈ I.box e, I.projectSummary e (I.stateOf y) = r ∧
      category (I.score y) = category (I.contractedScore e r) := by
  obtain ⟨y, hy, hp, hs⟩ := I.contractedScore_rational_lift he hr
  exact ⟨y, hy, hp, congrArg category hs⟩

end ThresholdComponentScores.Instance
