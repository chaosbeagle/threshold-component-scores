import ThresholdComponentScores.Score

namespace ThresholdComponentScores.Instance
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (I : Instance V q)

noncomputable def thresholdValues : Finset ℚ :=
  insert I.thresholds.tau (Finset.univ.image I.thresholds.breaks)

noncomputable def criticalDistances : Finset ℚ :=
  insert 0 ((Finset.univ.product I.thresholdValues).image
    (fun p => |I.baseline p.1 - p.2|))

theorem tau_mem_thresholdValues : I.thresholds.tau ∈ I.thresholdValues := by
  classical
  simp [thresholdValues]

theorem break_mem_thresholdValues (j : Fin q) : I.thresholds.breaks j ∈ I.thresholdValues := by
  classical
  simp [thresholdValues]

theorem distance_mem_criticalDistances (v : V) {t : ℚ} (ht : t ∈ I.thresholdValues) :
    |I.baseline v - t| ∈ I.criticalDistances := by
  classical
  simp only [criticalDistances, Finset.mem_insert, Finset.mem_image]
  right
  exact ⟨(v,t), by simp [ht], rfl⟩

theorem criticalDistances_nonneg {d : ℚ} (hd : d ∈ I.criticalDistances) : 0 ≤ d := by
  classical
  simp only [criticalDistances, Finset.mem_insert, Finset.mem_image] at hd
  rcases hd with rfl | ⟨p, _, rfl⟩
  · exact le_rfl
  · exact abs_nonneg _

/-- Genuine singleton, consecutive open interval, and final unbounded cells. -/
inductive RadiusCell where
  | point (d : ℚ) (hd : d ∈ I.criticalDistances)
  | between (a b : ℚ) (ha : a ∈ I.criticalDistances) (hb : b ∈ I.criticalDistances)
      (hab : a < b) (gap : ∀ d ∈ I.criticalDistances, ¬ (a < d ∧ d < b))
  | tail (a : ℚ) (ha : a ∈ I.criticalDistances)
      (last : ∀ d ∈ I.criticalDistances, d ≤ a)

namespace RadiusCell
variable {I}
def carrier : I.RadiusCell → Set ℚ
  | .point d _ => {d}
  | .between a b _ _ _ _ => Set.Ioo a b
  | .tail a _ _ => Set.Ioi a

theorem nonneg (C : I.RadiusCell) {e : ℚ} (he : e ∈ C.carrier) : 0 ≤ e := by
  cases C with
  | point d hd =>
    change e = d at he
    subst e
    exact I.criticalDistances_nonneg hd
  | between a b ha hb hab gap => exact (I.criticalDistances_nonneg ha).trans he.1.le
  | tail a ha last => exact (I.criticalDistances_nonneg ha).trans he.le

/-- Strict and weak comparisons to every actual critical value are cell-constant. -/
theorem comparisons (C : I.RadiusCell) {e f d : ℚ}
    (he : e ∈ C.carrier) (hf : f ∈ C.carrier) (hd : d ∈ I.criticalDistances) :
    (d < e ↔ d < f) ∧ (d ≤ e ↔ d ≤ f) := by
  cases C with
  | point c hc =>
    change e = c at he
    change f = c at hf
    subst e; subst f
    exact ⟨Iff.rfl, Iff.rfl⟩
  | between a b ha hb hab gap =>
    change a < e ∧ e < b at he
    change a < f ∧ f < b at hf
    have hg := gap d hd
    by_cases hda : d ≤ a
    · have hde : d < e := hda.trans_lt he.1
      have hdf : d < f := hda.trans_lt hf.1
      simp [hde, hdf, hde.le, hdf.le]
    · have hbd : b ≤ d := le_of_not_gt (fun hdb => hg ⟨lt_of_not_ge hda, hdb⟩)
      have hed : e < d := he.2.trans_le hbd
      have hfd : f < d := hf.2.trans_le hbd
      simp [not_lt.mpr hed.le, not_lt.mpr hfd.le, not_le.mpr hed, not_le.mpr hfd]
  | tail a ha last =>
    have hde : d < e := (last d hd).trans_lt he
    have hdf : d < f := (last d hd).trans_lt hf
    simp [hde, hdf, hde.le, hdf.le]
end RadiusCell

/-- Signed endpoint comparisons reduce to a critical absolute distance or are automatic. -/
theorem endpoint_comparisons (C : I.RadiusCell) {e f : ℚ}
    (he : e ∈ C.carrier) (hf : f ∈ C.carrier) (v : V)
    {t : ℚ} (ht : t ∈ I.thresholdValues) :
    (I.baseline v - e < t ↔ I.baseline v - f < t) ∧
    (t ≤ I.baseline v + e ↔ t ≤ I.baseline v + f) := by
  have he0 := C.nonneg he
  have hf0 := C.nonneg hf
  have hd := I.distance_mem_criticalDistances v ht
  have hh := C.comparisons he hf hd
  by_cases h : t ≤ I.baseline v
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hh
    constructor
    · constructor <;> intro hx
      · have : I.baseline v - t < e := by linarith
        have := hh.1.mp this
        linarith
      · have : I.baseline v - t < f := by linarith
        have := hh.1.mpr this
        linarith
    · constructor <;> intro hx <;> linarith
  · have h' : I.baseline v < t := lt_of_not_ge h
    rw [abs_of_neg (sub_neg.mpr h')] at hh
    constructor
    · constructor <;> intro hx <;> linarith
    · constructor <;> intro hx
      · have : -(I.baseline v - t) ≤ e := by linarith
        have := hh.2.mp this
        linarith
      · have : -(I.baseline v - t) ≤ f := by linarith
        have := hh.2.mpr this
        linarith

theorem allowed_cell_constant (C : I.RadiusCell) {e f : ℚ}
    (he : e ∈ C.carrier) (hf : f ∈ C.carrier) (v : V) (s : State q) :
    I.thresholds.allowed (I.baseline v - e) (I.baseline v + e) s ↔
    I.thresholds.allowed (I.baseline v - f) (I.baseline v + f) s := by
  have he0 := C.nonneg he
  have hf0 := C.nonneg hf
  have heLU : I.baseline v - e ≤ I.baseline v + e := by linarith
  have hfLU : I.baseline v - f ≤ I.baseline v + f := by linarith
  have ht := I.endpoint_comparisons C he hf v I.tau_mem_thresholdValues
  cases s with
  | none => simpa only [I.thresholds.allowed_none_iff heLU,
      I.thresholds.allowed_none_iff hfLU] using ht.1
  | some j =>
    rw [I.thresholds.allowed_some_iff heLU, I.thresholds.allowed_some_iff hfLU]
    have hl : I.thresholds.lower j ≤ I.baseline v + e ↔
        I.thresholds.lower j ≤ I.baseline v + f := by
      unfold Thresholds.lower
      split_ifs with hj
      · exact ht.2
      · simp only [max_le_iff]
        exact and_congr ht.2
          (I.endpoint_comparisons C he hf v (I.break_mem_thresholdValues _)).2
    apply and_congr hl
    apply forall_congr'
    intro hj
    exact and_congr
      (I.endpoint_comparisons C he hf v (I.break_mem_thresholdValues _)).1 Iff.rfl

theorem allowedStates_cell_constant (C : I.RadiusCell) {e f : ℚ}
    (he : e ∈ C.carrier) (hf : f ∈ C.carrier) :
    I.allowedStates e = I.allowedStates f := by
  ext s
  exact forall_congr' (fun v => I.allowed_cell_constant C he hf v (s v))

theorem scoreImage_cell_constant (C : I.RadiusCell) {e f : ℚ}
    (he : e ∈ C.carrier) (hf : f ∈ C.carrier) : I.scoreImage e = I.scoreImage f := by
  rw [I.scoreImage_eq_stateImage (C.nonneg he), I.scoreImage_eq_stateImage (C.nonneg hf),
    I.allowedStates_cell_constant C he hf]

end ThresholdComponentScores.Instance
