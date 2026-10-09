import ThresholdComponentScores.Radius

namespace ThresholdComponentScores.Instance
variable {V : Type*} [Fintype V] [DecidableEq V] {q m : ℕ}
    (I : Instance V q)

namespace RadiusCell
variable {I}
def left : I.RadiusCell → ℚ
  | .point d _ => d
  | .between a _ _ _ _ _ => a
  | .tail a _ _ => a

def representative : I.RadiusCell → ℚ
  | .point d _ => d
  | .between a b _ _ _ _ => (a+b)/2
  | .tail a _ _ => a+1

theorem left_mem (C : I.RadiusCell) : C.left ∈ I.criticalDistances := by
  cases C <;> assumption

theorem representative_mem (C : I.RadiusCell) : C.representative ∈ C.carrier := by
  cases C with
  | point d hd => rfl
  | between a b ha hb hab gap => change a < (a+b)/2 ∧ (a+b)/2 < b; constructor <;> linarith
  | tail a ha last => change a < a+1; linarith

theorem left_le (C : I.RadiusCell) {e : ℚ} (he : e ∈ C.carrier) : C.left ≤ e := by
  cases C with
  | point d hd => change e = d at he; exact he.symm.le
  | between a b ha hb hab gap => exact he.1.le
  | tail a ha last => exact he.le
end RadiusCell

/-- Every nonnegative rational is in a genuine critical-radius cell. -/
theorem exists_radiusCell {e : ℚ} (he : 0 ≤ e) : ∃ C : I.RadiusCell, e ∈ C.carrier := by
  classical
  by_cases hc : e ∈ I.criticalDistances
  · exact ⟨.point e hc, rfl⟩
  let L := I.criticalDistances.filter (fun d => d ≤ e)
  have hL : L.Nonempty := ⟨0, by simp [L, criticalDistances, he]⟩
  let a := L.max' hL
  have haL : a ∈ L := Finset.max'_mem L hL
  have ha : a ∈ I.criticalDistances := (Finset.mem_filter.mp haL).1
  have hae : a < e := lt_of_le_of_ne (Finset.mem_filter.mp haL).2
    (fun h => hc (h ▸ ha))
  let U := I.criticalDistances.filter (fun d => e < d)
  by_cases hU : U.Nonempty
  · let b := U.min' hU
    have hbU : b ∈ U := Finset.min'_mem U hU
    have hb : b ∈ I.criticalDistances := (Finset.mem_filter.mp hbU).1
    have heb : e < b := (Finset.mem_filter.mp hbU).2
    refine ⟨.between a b ha hb (hae.trans heb) ?_, hae, heb⟩
    intro d hd hbad
    by_cases hde : d ≤ e
    · have hda : d ≤ a := Finset.le_max' L d (Finset.mem_filter.mpr ⟨hd,hde⟩)
      exact (not_lt_of_ge hda) hbad.1
    · have hbd : b ≤ d := Finset.min'_le U d (Finset.mem_filter.mpr ⟨hd,lt_of_not_ge hde⟩)
      exact (not_lt_of_ge hbd) hbad.2
  · refine ⟨.tail a ha ?_, hae⟩
    intro d hd
    have hde : d ≤ e := by
      by_contra hn
      exact hU ⟨d, Finset.mem_filter.mpr ⟨hd, lt_of_not_ge hn⟩⟩
    exact Finset.le_max' L d (Finset.mem_filter.mpr ⟨hd,hde⟩)

variable (K : ThresholdComponentScores.Categories m)
noncomputable def badCriticalEndpoints : Finset ℚ := by
  classical
  exact I.criticalDistances.filter (fun d => ∃ C : I.RadiusCell,
    C.left = d ∧ ¬ I.categoryInvariant K C.representative)

theorem badRadii_eq_union_bad_cells : I.badRadii K =
    {e | ∃ C : I.RadiusCell, ¬ I.categoryInvariant K C.representative ∧ e ∈ C.carrier} := by
  ext e
  constructor
  · rintro ⟨he, hb⟩
    obtain ⟨C, hC⟩ := I.exists_radiusCell he
    exact ⟨C, fun h => hb ((I.categoryInvariant_cell_constant K C hC C.representative_mem).mpr h), hC⟩
  · rintro ⟨C, hb, hC⟩
    exact ⟨C.nonneg hC, fun h => hb ((I.categoryInvariant_cell_constant K C hC C.representative_mem).mp h)⟩

theorem badCriticalEndpoints_empty_iff : I.badCriticalEndpoints K = ∅ ↔
    ∀ e : ℚ, 0 ≤ e → I.categoryInvariant K e := by
  classical
  constructor
  · intro h e he
    obtain ⟨C, hC⟩ := I.exists_radiusCell he
    by_contra hb
    have hmem : C.left ∈ I.badCriticalEndpoints K := by
      apply Finset.mem_filter.mpr
      refine ⟨C.left_mem, C, rfl, ?_⟩
      exact fun hr => hb ((I.categoryInvariant_cell_constant K C hC C.representative_mem).mpr hr)
    simpa [h] using hmem
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    obtain ⟨_, C, _, hb⟩ := Finset.mem_filter.mp hd
    exact hb (h C.representative (C.nonneg C.representative_mem))

theorem categoryRadius_eq_top_iff_no_bad_cells : I.categoryRadius K = ⊤ ↔
    I.badCriticalEndpoints K = ∅ := by
  rw [I.categoryRadius_eq_top_iff K, I.badCriticalEndpoints_empty_iff K]

namespace RadiusCell
variable {I}
/-- Rational points approach the left endpoint from within every open cell. -/
theorem exists_below_real (C : I.RadiusCell) {r : ℝ} (hr : (C.left : ℝ) < r) :
    ∃ e : ℚ, e ∈ C.carrier ∧ (e : ℝ) < r := by
  cases C with
  | point d hd => exact ⟨d, rfl, hr⟩
  | between a b ha hb hab gap =>
    change (a : ℝ) < r at hr
    have hab' : (a : ℝ) < (b : ℝ) := Rat.cast_lt.mpr hab
    obtain ⟨e, hae, heb⟩ := exists_rat_btwn (lt_min hab' hr)
    exact ⟨e, ⟨Rat.cast_lt.mp hae, Rat.cast_lt.mp (lt_of_lt_of_le heb (min_le_left _ _))⟩,
      lt_of_lt_of_le heb (min_le_right _ _)⟩
  | tail a ha last =>
    obtain ⟨e, hae, her⟩ := exists_rat_btwn hr
    exact ⟨e, Rat.cast_lt.mp hae, her⟩
end RadiusCell

theorem categoryRadius_le_bad_cell_left (C : I.RadiusCell)
    (hbad : ¬ I.categoryInvariant K C.representative) :
    I.categoryRadius K ≤ ENNReal.ofReal (C.left : ℝ) := by
  have hrep : C.representative ∈ I.badRadii K :=
    ⟨C.nonneg C.representative_mem, hbad⟩
  have hfinite : I.categoryRadius K ≠ ⊤ := by
    intro htop
    have hh := I.categoryRadius_le_bad K hrep
    rw [htop] at hh
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hh)
  by_contra hn
  have hlt : ENNReal.ofReal (C.left : ℝ) < I.categoryRadius K := lt_of_not_ge hn
  have hr : (C.left : ℝ) < (I.categoryRadius K).toReal := by
    have hh := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfinite).mpr hlt
    rwa [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (I.criticalDistances_nonneg C.left_mem))] at hh
  obtain ⟨e, he, her⟩ := C.exists_below_real hr
  have heBad : e ∈ I.badRadii K := by
    refine ⟨C.nonneg he, ?_⟩
    intro hi
    exact hbad ((I.categoryInvariant_cell_constant K C he C.representative_mem).mp hi)
  have hh := I.categoryRadius_le_bad K heBad
  have hh' := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mpr hh
  rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (C.nonneg he))] at hh'
  exact (not_lt_of_ge hh') her

/-- Formula (5.2): the finite answer is exactly the least bad-cell left endpoint. -/
theorem categoryRadius_eq_min_badCriticalEndpoints
    (hne : (I.badCriticalEndpoints K).Nonempty) :
    I.categoryRadius K = ENNReal.ofReal (((I.badCriticalEndpoints K).min' hne : ℚ) : ℝ) := by
  classical
  apply le_antisymm
  · have hm := Finset.min'_mem (I.badCriticalEndpoints K) hne
    obtain ⟨_, C, hleft, hbad⟩ := Finset.mem_filter.mp hm
    simpa only [hleft] using I.categoryRadius_le_bad_cell_left K C hbad
  · apply le_sInf
    rintro z ⟨e, he, rfl⟩
    obtain ⟨C, hC⟩ := I.exists_radiusCell he.1
    have hbad : ¬ I.categoryInvariant K C.representative :=
      fun hi => he.2 ((I.categoryInvariant_cell_constant K C hC C.representative_mem).mpr hi)
    have hmem : C.left ∈ I.badCriticalEndpoints K :=
      Finset.mem_filter.mpr ⟨C.left_mem, C, rfl, hbad⟩
    have hle : (I.badCriticalEndpoints K).min' hne ≤ e :=
      (Finset.min'_le _ _ hmem).trans (C.left_le hC)
    exact ENNReal.ofReal_le_ofReal (Rat.cast_le.mpr hle)

/-- Every finite category radius is an actual critical distance. -/
theorem finite_categoryRadius_mem_criticalDistances (hfinite : I.categoryRadius K ≠ ⊤) :
    ∃ d ∈ I.criticalDistances, I.categoryRadius K = ENNReal.ofReal (d : ℝ) := by
  classical
  have hne : (I.badCriticalEndpoints K).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    exact hfinite ((I.categoryRadius_eq_top_iff_no_bad_cells K).mpr hempty)
  refine ⟨(I.badCriticalEndpoints K).min' hne, ?_,
    I.categoryRadius_eq_min_badCriticalEndpoints K hne⟩
  exact (Finset.mem_filter.mp (Finset.min'_mem (I.badCriticalEndpoints K) hne)).1

/-- The critical list has the manuscript's linear-in-threshold-count bound. -/
theorem criticalDistances_card_le : I.criticalDistances.card ≤ 1 + Fintype.card V * (q+1) := by
  classical
  have hthreshold : I.thresholdValues.card ≤ q+1 := by
    have h₁ := Finset.card_insert_le I.thresholds.tau (Finset.univ.image I.thresholds.breaks)
    have h₂ : (Finset.univ.image I.thresholds.breaks).card ≤ q := by
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin q)))
        (f := I.thresholds.breaks))
    change (insert I.thresholds.tau (Finset.univ.image I.thresholds.breaks)).card ≤ q+1
    omega
  have h₁ := Finset.card_insert_le 0 ((Finset.univ.product I.thresholdValues).image
    (fun p => |I.baseline p.1 - p.2|))
  have h₂ := Finset.card_image_le (s := Finset.univ.product I.thresholdValues)
    (f := fun p => |I.baseline p.1 - p.2|)
  have hp : ((Finset.univ : Finset V).product I.thresholdValues).card =
      Fintype.card V * I.thresholdValues.card := by
    exact (Finset.card_product (Finset.univ : Finset V) I.thresholdValues).trans
      (by rw [Finset.card_univ])
  rw [hp] at h₂
  have h₃ := Nat.mul_le_mul_left (Fintype.card V) hthreshold
  unfold criticalDistances
  omega

/-- Finite radius and its separate attained-extrema boundary test, in one contract. -/
theorem finite_radius_and_boundary (hfinite : I.categoryRadius K ≠ ⊤) :
    ∃ d ∈ I.criticalDistances,
      I.categoryRadius K = ENNReal.ofReal (d : ℝ) ∧
      ∃ lo ∈ I.box d, ∃ hi ∈ I.box d,
        (∀ y ∈ I.box d, I.score lo ≤ I.score y ∧ I.score y ≤ I.score hi) ∧
        (I.boundaryInvariant K d ↔
          K.category (I.score lo) = K.category (I.score I.baseline) ∧
          K.category (I.score hi) = K.category (I.score I.baseline)) := by
  obtain ⟨d, hd, hr⟩ := I.finite_categoryRadius_mem_criticalDistances K hfinite
  exact ⟨d, hd, hr, I.boundary_test K (I.criticalDistances_nonneg hd)⟩

end ThresholdComponentScores.Instance
