import ThresholdComponentScores.SummaryPartition

namespace ThresholdComponentScores.Instance
open StableSummary
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (I : Instance V q)

/-- Assemble local rational fibre realizations; uncovered inactive coordinates keep baseline. -/
noncomputable def glueSummary {S U : Finset V} (localY : Node I.graph S U → V → ℚ) : V → ℚ := by
  classical
  exact fun v => if h : ∃ n : Node I.graph S U, v ∈ support n then localY h.choose v else I.baseline v

theorem glueSummary_on_support {S U : Finset V} (hSU : Disjoint S U)
    (localY : Node I.graph S U → V → ℚ) (n : Node I.graph S U)
    {v : V} (hv : v ∈ support n) : I.glueSummary localY v = localY n v := by
  classical
  have h : ∃ m : Node I.graph S U, v ∈ support m := ⟨n, hv⟩
  have heq : h.choose = n := node_eq_of_mem hSU h.choose_spec hv
  simp [glueSummary, h, heq]

theorem glueSummary_mem_box {S U : Finset V} {e : ℚ} (he : 0 ≤ e)
    (localY : Node I.graph S U → V → ℚ)
    (hlocal : ∀ n v, v ∈ support n →
      I.baseline v - e ≤ localY n v ∧ localY n v ≤ I.baseline v + e) :
    I.glueSummary localY ∈ I.box e := by
  classical
  apply (I.mem_box_iff e _).mpr
  intro v
  by_cases h : ∃ n : Node I.graph S U, v ∈ support n
  · simpa only [glueSummary, dif_pos h] using hlocal h.choose v h.choose_spec
  · simp only [glueSummary, dif_neg h]
    constructor <;> linarith

/-- Existence is over rational source vectors, with exact agreement on every genuine fibre. -/
theorem glueSummary_exists {S U : Finset V} (hSU : Disjoint S U) {e : ℚ} (he : 0 ≤ e)
    (localY : Node I.graph S U → V → ℚ)
    (hlocal : ∀ n v, v ∈ support n →
      I.baseline v - e ≤ localY n v ∧ localY n v ≤ I.baseline v + e) :
    ∃ y ∈ I.box e, ∀ n v, v ∈ support n → y v = localY n v :=
  ⟨I.glueSummary localY, I.glueSummary_mem_box he localY hlocal,
    fun n _ hv => I.glueSummary_on_support hSU localY n hv⟩

/-- Projection depends only on the states inside the actual fibre. -/
theorem summaryProjection_congr_on_support {S U : Finset V} {s t : V → State q}
    (n : Node I.graph S U) (hst : ∀ v ∈ support n, s v = t v) :
    I.summaryProjection S U s n = I.summaryProjection S U t n := by
  classical
  have ha : support n ⊆ I.stateActive s ↔ support n ⊆ I.stateActive t := by
    constructor <;> intro h v hv
    · have := h hv
      simpa only [stateActive, Finset.mem_filter, Finset.mem_univ, true_and, hst v hv] using this
    · have := h hv
      simpa only [stateActive, Finset.mem_filter, Finset.mem_univ, true_and, hst v hv] using this
  have hm : I.stateMaximum (support n) s = I.stateMaximum (support n) t := by
    apply Finset.sup_congr rfl
    intro v hv
    rw [hst v hv]
  simp only [summaryProjection, ha, hm]

end ThresholdComponentScores.Instance
