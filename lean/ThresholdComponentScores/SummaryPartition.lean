import ThresholdComponentScores.SummaryScore
import ThresholdComponentScores.SummaryDomains

namespace ThresholdComponentScores.Instance
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (I : Instance V q)

noncomputable def stableVertices (e : ℚ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => I.thresholds.tau ≤ I.baseline v - e)

noncomputable def inactiveVertices (e : ℚ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => I.baseline v + e < I.thresholds.tau)

noncomputable def uncertainVertices (e : ℚ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => I.baseline v - e < I.thresholds.tau ∧
    I.thresholds.tau ≤ I.baseline v + e)

@[simp] theorem mem_stableVertices (e : ℚ) (v : V) :
    v ∈ I.stableVertices e ↔ I.thresholds.tau ≤ I.baseline v - e := by
  classical
  simp [stableVertices]

@[simp] theorem mem_inactiveVertices (e : ℚ) (v : V) :
    v ∈ I.inactiveVertices e ↔ I.baseline v + e < I.thresholds.tau := by
  classical
  simp [inactiveVertices]

@[simp] theorem mem_uncertainVertices (e : ℚ) (v : V) :
    v ∈ I.uncertainVertices e ↔ I.baseline v - e < I.thresholds.tau ∧
      I.thresholds.tau ≤ I.baseline v + e := by
  classical
  simp [uncertainVertices]

theorem stable_uncertain_disjoint (e : ℚ) :
    Disjoint (I.stableVertices e) (I.uncertainVertices e) := by
  apply Finset.disjoint_left.mpr
  intro v hs hu
  exact (not_lt_of_ge ((I.mem_stableVertices e v).mp hs))
    ((I.mem_uncertainVertices e v).mp hu).1

/-- Stable and uncertain vertices are exactly those that can possibly be active. -/
theorem mem_stable_union_uncertain {e : ℚ} (he : 0 ≤ e) (v : V) :
    v ∈ I.stableVertices e ∪ I.uncertainVertices e ↔ I.thresholds.tau ≤ I.baseline v + e := by
  classical
  simp only [Finset.mem_union, mem_stableVertices, mem_uncertainVertices]
  constructor
  · rintro (h | h)
    · linarith
    · exact h.2
  · intro h
    by_cases hs : I.thresholds.tau ≤ I.baseline v - e
    · exact Or.inl hs
    · exact Or.inr ⟨lt_of_not_ge hs, h⟩

/-- The three radius classes cover every original vertex, including threshold equalities. -/
theorem vertex_partition {e : ℚ} (he : 0 ≤ e) :
    I.stableVertices e ∪ I.uncertainVertices e ∪ I.inactiveVertices e = Finset.univ := by
  classical
  ext v
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  by_cases hi : I.baseline v + e < I.thresholds.tau
  · exact Or.inr ((I.mem_inactiveVertices e v).mpr hi)
  · exact Or.inl (Finset.mem_union.mp ((I.mem_stable_union_uncertain he v).mpr (le_of_not_gt hi)))

theorem inactive_state_eq_none {e : ℚ} {s : V → State q}
    (hs : s ∈ I.allowedStates e) {v : V} (hv : v ∈ I.inactiveVertices e) : s v = none := by
  obtain ⟨t, htL, htU, ht⟩ := hs v
  rw [← ht]
  exact (I.thresholds.state_eq_none_iff t).mpr
    (htU.trans_lt ((I.mem_inactiveVertices e v).mp hv))

theorem stable_subset_stateActive {e : ℚ} {s : V → State q}
    (hs : s ∈ I.allowedStates e) : I.stableVertices e ⊆ I.stateActive s := by
  classical
  intro v hv
  obtain ⟨y, hL, hU, hstate⟩ := hs v
  have hactive : I.thresholds.tau ≤ y := ((I.mem_stableVertices e v).mp hv).trans hL
  simp [stateActive, ← hstate, Thresholds.state, not_lt.mpr hactive]

theorem stateActive_subset_stable_uncertain {e : ℚ} {s : V → State q}
    (hs : s ∈ I.allowedStates e) :
    I.stateActive s ⊆ I.stableVertices e ∪ I.uncertainVertices e := by
  classical
  intro v hv
  obtain ⟨y, hL, hU, hstate⟩ := hs v
  have hactive : I.thresholds.tau ≤ y := by
    by_contra hn
    have hy : y < I.thresholds.tau := lt_of_not_ge hn
    simp [stateActive, ← hstate, Thresholds.state, hy] at hv
  by_cases hstable : I.thresholds.tau ≤ I.baseline v - e
  · exact Finset.mem_union_left _ ((I.mem_stableVertices e v).mpr hstable)
  · exact Finset.mem_union_right _ ((I.mem_uncertainVertices e v).mpr
      ⟨lt_of_not_ge hstable, hactive.trans hU⟩)

abbrev SummaryNode (e : ℚ) := StableSummary.Node I.graph (I.stableVertices e) (I.uncertainVertices e)

noncomputable def summaryAlpha (e : ℚ) (C : Finset V) : Fin (q+1) :=
  C.sup (fun v => I.thresholds.bin (I.baseline v - e))

noncomputable def summaryBeta (e : ℚ) (C : Finset V) : Fin (q+1) :=
  C.sup (fun v => I.thresholds.bin (I.baseline v + e))

/-- Explicit independent local intervals, precisely manuscript (4.2). -/
noncomputable def summaryAllowed (e : ℚ) : Set (I.SummaryNode e → State q) :=
  {r | (∀ u : {v // v ∈ I.uncertainVertices e},
        r (.inl u) = none ∨ ∃ j, r (.inl u) = some j ∧
          I.thresholds.bin I.thresholds.tau ≤ j ∧ j ≤ I.thresholds.bin (I.baseline u.val + e)) ∧
    (∀ C : {C // C ∈ components I.graph (I.stableVertices e)},
        ∃ j, r (.inr C) = some j ∧ I.summaryAlpha e C.val ≤ j ∧ j ≤ I.summaryBeta e C.val)}

noncomputable def projectSummary (e : ℚ) (s : V → State q) : I.SummaryNode e → State q :=
  I.summaryProjection (I.stableVertices e) (I.uncertainVertices e) s

noncomputable def contractedScore (e : ℚ) (r : I.SummaryNode e → State q) : ℚ :=
  I.summaryScore (I.stableVertices e) (I.uncertainVertices e) r

/-- The concrete radius-dependent contraction preserves the original gated source score. -/
theorem stateScore_eq_contractedScore {e : ℚ} {s : V → State q}
    (hs : s ∈ I.allowedStates e) :
    I.stateScore s = I.contractedScore e (I.projectSummary e s) :=
  I.stateScore_eq_summaryScore (I.stable_uncertain_disjoint e)
    (I.stable_subset_stateActive hs) (I.stateActive_subset_stable_uncertain hs)

theorem stateMaximum_bounds_of_stable {e : ℚ} {s : V → State q}
    (hs : s ∈ I.allowedStates e) (C : Finset V) (hC : C ⊆ I.stableVertices e) :
    I.summaryAlpha e C ≤ I.stateMaximum C s ∧ I.stateMaximum C s ≤ I.summaryBeta e C := by
  classical
  have bounds (v : V) (hv : v ∈ C) :
      I.thresholds.bin (I.baseline v - e) ≤ (s v).getD 0 ∧
      (s v).getD 0 ≤ I.thresholds.bin (I.baseline v + e) := by
    obtain ⟨t, htL, htU, ht⟩ := hs v
    have hat : I.thresholds.tau ≤ t := ((I.mem_stableVertices e v).mp (hC hv)).trans htL
    have hst : s v = some (I.thresholds.bin t) := by
      rw [← ht]
      simp [Thresholds.state, not_lt.mpr hat]
    rw [hst]
    exact ⟨I.thresholds.bin_monotone htL, I.thresholds.bin_monotone htU⟩
  constructor
  · apply Finset.sup_le
    intro v hv
    exact (bounds v hv).1.trans (Finset.le_sup (f := fun v => (s v).getD 0) hv)
  · apply Finset.sup_le
    intro v hv
    exact (bounds v hv).2.trans
      (Finset.le_sup (f := fun v => I.thresholds.bin (I.baseline v + e)) hv)

/-- Every legal source state projects into the explicit local summary intervals. -/
theorem projectSummary_mem_summaryAllowed {e : ℚ} {s : V → State q}
    (hs : s ∈ I.allowedStates e) : I.projectSummary e s ∈ I.summaryAllowed e := by
  constructor
  · intro u
    simp only [projectSummary, I.summaryProjection_uncertain]
    have hu := (I.mem_uncertainVertices e u.val).mp u.property
    exact (I.thresholds.uncertain_allowed_iff hu.1 hu.2 (s u.val)).mp (hs u.val)
  · intro C
    refine ⟨I.stateMaximum C.val s, ?_, ?_⟩
    · exact I.summaryProjection_stable s (I.stable_subset_stateActive hs) C
    · exact I.stateMaximum_bounds_of_stable hs C.val (components_subset_active C.property)

end ThresholdComponentScores.Instance
