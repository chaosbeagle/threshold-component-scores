import ThresholdComponentScores.RadiusCells
import ThresholdComponentScores.Range
import Mathlib.Data.ENNReal.Real

namespace ThresholdComponentScores

/-- Ordered rational cutpoints; equality belongs to the upper category. -/
structure Categories (m : ℕ) where
  cuts : Fin m → ℚ
  strict : StrictMono cuts

namespace Categories
variable {m : ℕ} (K : Categories m)
def asThresholds : Thresholds m := ⟨0, K.cuts, K.strict⟩
def category (t : ℚ) : Fin (m+1) := K.asThresholds.bin t

theorem category_monotone : Monotone K.category := K.asThresholds.bin_monotone

theorem category_cutpoint (i : Fin m) : (K.category (K.cuts i)).val = i.val + 1 :=
  K.asThresholds.bin_breakpoint i
end Categories

namespace Instance
variable {V : Type*} [Fintype V] [DecidableEq V] {q m : ℕ}
    (I : Instance V q) (K : Categories m)

def categoryInvariant (e : ℚ) : Prop :=
  ∀ y ∈ I.box e, K.category (I.score y) = K.category (I.score I.baseline)

def badRadii : Set ℚ := {e | 0 ≤ e ∧ ¬ I.categoryInvariant K e}

/-- The actual infimum of rational bad radii in the extended nonnegative reals. -/
noncomputable def categoryRadius : ENNReal :=
  sInf ((fun e : ℚ => ENNReal.ofReal (e : ℝ)) '' I.badRadii K)

/-- Boundary invariance is a separate predicate, not membership in the infimum set. -/
def boundaryInvariant (d : ℚ) : Prop := I.categoryInvariant K d

theorem categoryInvariant_iff_states {e : ℚ} (he : 0 ≤ e) :
    I.categoryInvariant K e ↔ ∀ s ∈ I.allowedStates e,
      K.category (I.stateScore s) = K.category (I.score I.baseline) := by
  constructor
  · intro h s hs
    obtain ⟨hy, hstate⟩ := I.liftState_spec he hs
    have hh := h (I.liftState e s) hy
    rwa [I.score_eq_stateScore, hstate] at hh
  · intro h y hy
    rw [I.score_eq_stateScore]
    exact h (I.stateOf y) (I.stateOf_mem_allowedStates hy)

theorem categoryInvariant_iff_endpoints {e : ℚ} {lo hi : V → ℚ}
    (hlo : lo ∈ I.box e) (hhi : hi ∈ I.box e)
    (hb : ∀ y ∈ I.box e, I.score lo ≤ I.score y ∧ I.score y ≤ I.score hi) :
    I.categoryInvariant K e ↔
      K.category (I.score lo) = K.category (I.score I.baseline) ∧
      K.category (I.score hi) = K.category (I.score I.baseline) := by
  constructor
  · intro h
    exact ⟨h lo hlo, h hi hhi⟩
  · rintro ⟨hl, hu⟩ y hy
    have hh := hb y hy
    apply le_antisymm
    · simpa only [hu] using K.category_monotone hh.2
    · simpa only [hl] using K.category_monotone hh.1

/-- Attained extrema supply an exact, separate singleton boundary test. -/
theorem boundary_test {d : ℚ} (hd : 0 ≤ d) :
    ∃ lo ∈ I.box d, ∃ hi ∈ I.box d,
      (∀ y ∈ I.box d, I.score lo ≤ I.score y ∧ I.score y ≤ I.score hi) ∧
      (I.boundaryInvariant K d ↔
        K.category (I.score lo) = K.category (I.score I.baseline) ∧
        K.category (I.score hi) = K.category (I.score I.baseline)) := by
  obtain ⟨lo, hlo, hi, hhi, hb⟩ := I.attained_extrema hd
  exact ⟨lo, hlo, hi, hhi, hb, I.categoryInvariant_iff_endpoints K hlo hhi hb⟩

theorem categoryInvariant_zero : I.categoryInvariant K 0 := by
  intro y hy
  have hxy : y = I.baseline := by
    funext v
    have hh := (I.mem_box_iff 0 y).mp hy v
    simp only [sub_zero, add_zero] at hh
    exact le_antisymm hh.2 hh.1
  rw [hxy]

theorem box_mono {e f : ℚ} (hef : e ≤ f) : I.box e ⊆ I.box f := by
  intro y hy v
  exact (hy v).trans hef

theorem categoryInvariant_antitone {e f : ℚ} (hef : e ≤ f)
    (hf : I.categoryInvariant K f) : I.categoryInvariant K e :=
  fun y hy => hf y (I.box_mono hef hy)

theorem badRadii_upward {e f : ℚ} (he : e ∈ I.badRadii K) (hef : e ≤ f) :
    f ∈ I.badRadii K :=
  ⟨he.1.trans hef, fun hf => he.2 (I.categoryInvariant_antitone K hef hf)⟩

theorem categoryInvariant_cell_constant (C : I.RadiusCell) {e f : ℚ}
    (he : e ∈ C.carrier) (hf : f ∈ C.carrier) :
    I.categoryInvariant K e ↔ I.categoryInvariant K f := by
  rw [I.categoryInvariant_iff_states K (C.nonneg he),
    I.categoryInvariant_iff_states K (C.nonneg hf), I.allowedStates_cell_constant C he hf]

theorem categoryRadius_le_bad {e : ℚ} (he : e ∈ I.badRadii K) :
    I.categoryRadius K ≤ ENNReal.ofReal (e : ℝ) :=
  sInf_le ⟨e, he, rfl⟩

theorem categoryRadius_eq_top_iff : I.categoryRadius K = ⊤ ↔
    ∀ e : ℚ, 0 ≤ e → I.categoryInvariant K e := by
  constructor
  · intro hr e he
    by_contra hb
    have hh := I.categoryRadius_le_bad K ⟨he, hb⟩
    rw [hr] at hh
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hh)
  · intro h
    have hempty : I.badRadii K = ∅ := by
      ext e
      simp only [badRadii, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun he => not_not.mpr (h e he)
    simp [categoryRadius, hempty]

end Instance
end ThresholdComponentScores
