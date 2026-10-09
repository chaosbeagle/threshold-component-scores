import ThresholdComponentScores.Local
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import ThresholdComponentScores.Components

namespace ThresholdComponentScores

/-- Exact data of manuscript §2. Areas may vanish; weights may have either sign. -/
structure Instance (V : Type*) [Fintype V] (q : ℕ) where
  vertex_nonempty : Nonempty V
  graph : SimpleGraph V
  thresholds : Thresholds q
  baseline : V → ℚ
  area : V → ℚ
  area_nonneg : ∀ v, 0 ≤ area v
  gate : ℕ
  gate_pos : 1 ≤ gate
  weight : Fin (q+1) → ℚ

namespace Instance
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (I : Instance V q)

noncomputable def active (y : V → ℚ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => I.thresholds.tau ≤ y v)

noncomputable def stateActive (I : Instance V q) (s : V → State q) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => (s v).isSome)

def stateOf (y : V → ℚ) : V → State q := fun v => I.thresholds.state (y v)

def box (e : ℚ) : Set (V → ℚ) := {y | ∀ v, |y v - I.baseline v| ≤ e}

noncomputable def areaSum (C : Finset V) : ℚ := ∑ v ∈ C, I.area v

/-- Maximum intensity, with an irrelevant default on empty supports. -/
noncomputable def componentMaximum (I : Instance V q) (C : Finset V) (y : V → ℚ) : ℚ := by
  classical
  exact if h : C.Nonempty then C.sup' h y else 0

/-- Sum over genuine active connected components, gated by original vertex count. -/
noncomputable def score (y : V → ℚ) : ℚ := by
  classical
  exact ∑ C ∈ components I.graph (I.active y),
    if I.gate ≤ C.card then
      I.areaSum C * I.weight (I.thresholds.bin (I.componentMaximum C y))
    else 0

/-- Maximum bin index, never maximum numerical weight. -/
noncomputable def stateMaximum (I : Instance V q) (C : Finset V) (s : V → State q) : Fin (q+1) := by
  classical
  exact C.sup (fun v => (s v).getD 0)

noncomputable def stateScore (s : V → State q) : ℚ := by
  classical
  exact ∑ C ∈ components I.graph (I.stateActive s),
    if I.gate ≤ C.card then I.areaSum C * I.weight (I.stateMaximum C s) else 0

noncomputable def allowedStates (e : ℚ) : Set (V → State q) :=
  {s | ∀ v, I.thresholds.allowed (I.baseline v - e) (I.baseline v + e) (s v)}

@[simp] theorem mem_active (y : V → ℚ) (v : V) :
    v ∈ I.active y ↔ I.thresholds.tau ≤ y v := by
  classical
  simp [active]

@[simp] theorem stateActive_stateOf (y : V → ℚ) : I.stateActive (I.stateOf y) = I.active y := by
  classical
  ext v
  simp [stateActive, stateOf, Thresholds.state, active]


/-- Activation, graph connectivity, area, gate, and maximum-bin weighting all agree. -/
theorem score_eq_stateScore (y : V → ℚ) : I.score y = I.stateScore (I.stateOf y) := by
  classical
  unfold score stateScore
  rw [I.stateActive_stateOf]
  apply Finset.sum_congr rfl
  intro C hC
  split_ifs with hgate
  · congr 2
    rw [componentMaximum, dif_pos (components_nonempty hC), I.thresholds.bin_sup]
    apply Finset.sup_congr rfl
    intro v hv
    have ha := (I.mem_active y v).1 (components_subset_active hC hv)
    simp [stateOf, Thresholds.state, not_lt.mpr ha]
  · rfl

@[simp] theorem mem_box_iff (e : ℚ) (y : V → ℚ) : y ∈ I.box e ↔
    ∀ v, I.baseline v - e ≤ y v ∧ y v ≤ I.baseline v + e := by
  simp only [box, Set.mem_setOf_eq, abs_le]
  constructor <;> intro h v <;> obtain ⟨h₁, h₂⟩ := h v <;> constructor <;> linarith

theorem baseline_mem_box {e : ℚ} (he : 0 ≤ e) : I.baseline ∈ I.box e := by
  simp [box, he]

theorem stateOf_mem_allowedStates {e : ℚ} {y : V → ℚ} (hy : y ∈ I.box e) :
    I.stateOf y ∈ I.allowedStates e := by
  intro v
  exact ⟨y v, ((I.mem_box_iff e y).1 hy v).1, ((I.mem_box_iff e y).1 hy v).2, rfl⟩

/-- The explicit coordinatewise rational witness in manuscript (3.2). -/
noncomputable def liftState (e : ℚ) (s : V → State q) : V → ℚ :=
  fun v => I.thresholds.representative (I.baseline v - e) (s v)

theorem liftState_spec {e : ℚ} (he : 0 ≤ e) {s : V → State q}
    (hs : s ∈ I.allowedStates e) :
    I.liftState e s ∈ I.box e ∧ I.stateOf (I.liftState e s) = s := by
  have H (v : V) := I.thresholds.representative_spec (L := I.baseline v - e)
    (U := I.baseline v + e) (by linarith) (hs v)
  constructor
  · apply (I.mem_box_iff e _).2
    intro v
    exact ⟨(H v).1, (H v).2.1⟩
  · funext v
    exact (H v).2.2

theorem stateOf_surjOn {e : ℚ} (he : 0 ≤ e) :
    Set.SurjOn I.stateOf (I.box e) (I.allowedStates e) := by
  intro s hs
  exact ⟨I.liftState e s, (I.liftState_spec he hs).1, (I.liftState_spec he hs).2⟩

/-- Exact attainable rational score set. -/
def scoreImage (e : ℚ) : Set ℚ := I.score '' I.box e

theorem scoreImage_eq_stateImage {e : ℚ} (he : 0 ≤ e) :
    I.scoreImage e = I.stateScore '' I.allowedStates e := by
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨I.stateOf y, I.stateOf_mem_allowedStates hy, (I.score_eq_stateScore y).symm⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hy, hst⟩ := I.liftState_spec he hs
    refine ⟨I.liftState e s, hy, ?_⟩
    rw [I.score_eq_stateScore, hst]

theorem scoreImage_finite {e : ℚ} (he : 0 ≤ e) : (I.scoreImage e).Finite := by
  rw [I.scoreImage_eq_stateImage he]
  exact (Set.toFinite (I.allowedStates e)).image I.stateScore

theorem scoreImage_nonempty {e : ℚ} (he : 0 ≤ e) : (I.scoreImage e).Nonempty :=
  ⟨I.score I.baseline, I.baseline, I.baseline_mem_box he, rfl⟩

end Instance
end ThresholdComponentScores
