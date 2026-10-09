import ThresholdComponentScores.Local

/-! Exact local domains and explicit rational witnesses for manuscript §4. -/
namespace ThresholdComponentScores
namespace Thresholds
variable {q : ℕ} (T : Thresholds q)

/-- On a stably active interval, precisely the bins between its endpoints occur. -/
theorem allowed_some_iff_bin_bounds {L U : ℚ} (hLU : L ≤ U) (hactive : T.tau ≤ L)
    (j : Fin (q+1)) :
    T.allowed L U (some j) ↔ T.bin L ≤ j ∧ j ≤ T.bin U := by
  constructor
  · rintro ⟨t, hLt, htU, ht⟩
    have hb := ((T.state_eq_some_iff t j).1 ht).2
    exact ⟨hb ▸ T.bin_monotone hLt, hb ▸ T.bin_monotone htU⟩
  · rintro ⟨hLj, hjU⟩
    apply (T.allowed_some_iff hLU j).2
    constructor
    · apply (T.lower_le_iff j U).2
      refine ⟨hactive.trans hLU, fun i hi => (T.break_le_iff U i).2 ?_⟩
      exact lt_of_lt_of_le hi hjU
    · intro hj
      have hL : L < T.breaks ⟨j.val,hj⟩ := by
        apply lt_of_not_ge
        intro h
        have := (T.break_le_iff L ⟨j.val,hj⟩).1 h
        exact (not_lt_of_ge hLj) this
      refine ⟨hL, ?_⟩
      unfold lower
      split_ifs with hz
      · exact hactive.trans_lt hL
      · apply max_lt (hactive.trans_lt hL)
        apply T.strict
        change j.val - 1 < j.val
        omega

/-- Closed rational intervals attain every intermediate bin, including both endpoints. -/
theorem exists_bin_iff {L U : ℚ} (hLU : L ≤ U) (j : Fin (q+1)) :
    (∃ t : ℚ, L ≤ t ∧ t ≤ U ∧ T.bin t = j) ↔ T.bin L ≤ j ∧ j ≤ T.bin U := by
  let S : Thresholds q := { T with tau := L }
  have h := S.allowed_some_iff_bin_bounds hLU (le_refl L) j
  constructor
  · rintro ⟨t, hLt, htU, ht⟩
    exact ⟨ht ▸ T.bin_monotone hLt, ht ▸ T.bin_monotone htU⟩
  · intro hb
    obtain ⟨t, hLt, htU, ht⟩ := h.mpr hb
    exact ⟨t, hLt, htU, ((S.state_eq_some_iff t j).1 ht).2⟩

/-- An uncertain vertex has inactivity and exactly bins gamma through beta. -/
theorem uncertain_allowed_iff {L U : ℚ} (hL : L < T.tau) (hU : T.tau ≤ U)
    (s : State q) :
    T.allowed L U s ↔ s = none ∨ ∃ j, s = some j ∧ T.bin T.tau ≤ j ∧ j ≤ T.bin U := by
  cases s with
  | none => simp [T.allowed_none_iff (hL.le.trans hU), hL]
  | some j =>
    simp only [Option.some_ne_none, Option.some.injEq, exists_eq_left', false_or]
    constructor
    · rintro ⟨t, hLt, htU, ht⟩
      obtain ⟨ha, hb⟩ := (T.state_eq_some_iff t j).1 ht
      exact ⟨hb ▸ T.bin_monotone ha, hb ▸ T.bin_monotone htU⟩
    · intro hb
      obtain ⟨t, htL, htU, ht⟩ := (T.allowed_some_iff_bin_bounds hU le_rfl j).2 hb
      exact ⟨t, hL.le.trans htL, htU, ht⟩

/-- The manuscript's one-coordinate rational lift of a stable component label. -/
def stableMaxWitness {V : Type*} [DecidableEq V] (L : V → ℚ)
    (p : V) (j : Fin (q+1)) : V → ℚ :=
  fun v => if v = p then T.representative (L p) (some j) else L v

/-- Every requested intermediate maximum has a representative supported at one vertex. -/
theorem stable_max_witness {V : Type*} [DecidableEq V] (C : Finset V) (hC : C.Nonempty)
    (L U : V → ℚ) (hLU : ∀ v ∈ C, L v ≤ U v) (ha : ∀ v ∈ C, T.tau ≤ L v)
    (j : Fin (q+1)) (hLj : C.sup (fun v => T.bin (L v)) ≤ j)
    (hjU : j ≤ C.sup (fun v => T.bin (U v))) :
    ∃ p ∈ C, (∀ v ∈ C, L v ≤ T.stableMaxWitness L p j v ∧
      T.stableMaxWitness L p j v ≤ U v) ∧
      C.sup (fun v => T.bin (T.stableMaxWitness L p j v)) = j := by
  obtain ⟨p, hp, hpmax⟩ := Finset.exists_mem_eq_sup C hC (fun v => T.bin (U v))
  have hpL : T.bin (L p) ≤ j := (Finset.le_sup hp).trans hLj
  have hpU : j ≤ T.bin (U p) := hpmax ▸ hjU
  have hr := T.representative_spec (hLU p hp)
    ((T.allowed_some_iff_bin_bounds (hLU p hp) (ha p hp) j).2 ⟨hpL, hpU⟩)
  have hrbin := ((T.state_eq_some_iff _ j).1 hr.2.2).2
  refine ⟨p, hp, ?_, ?_⟩
  · intro v hv
    by_cases hvp : v = p
    · subst v
      simpa [stableMaxWitness] using ⟨hr.1, hr.2.1⟩
    · simp [stableMaxWitness, hvp, hLU v hv]
  · apply le_antisymm
    · apply Finset.sup_le
      intro v hv
      by_cases hvp : v = p
      · subst v
        simp [stableMaxWitness, hrbin]
      · simpa [stableMaxWitness, hvp] using (Finset.le_sup hv).trans hLj
    · have h := Finset.le_sup (f := fun v => T.bin (T.stableMaxWitness L p j v)) hp
      simpa [stableMaxWitness, hrbin] using h

/-- Exact stable-component maximum-bin domain, without storing its internal graph. -/
theorem stable_max_bins_iff {V : Type*} [DecidableEq V] (C : Finset V) (hC : C.Nonempty)
    (L U : V → ℚ) (hLU : ∀ v ∈ C, L v ≤ U v) (ha : ∀ v ∈ C, T.tau ≤ L v)
    (j : Fin (q+1)) :
    (∃ y : V → ℚ, (∀ v ∈ C, L v ≤ y v ∧ y v ≤ U v) ∧
      C.sup (fun v => T.bin (y v)) = j) ↔
    C.sup (fun v => T.bin (L v)) ≤ j ∧ j ≤ C.sup (fun v => T.bin (U v)) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    constructor <;> apply Finset.sup_le <;> intro v hv
    · exact (T.bin_monotone (hy v hv).1).trans (Finset.le_sup (f := fun v => T.bin (y v)) hv)
    · exact (T.bin_monotone (hy v hv).2).trans (Finset.le_sup (f := fun v => T.bin (U v)) hv)
  · rintro ⟨hL, hU⟩
    obtain ⟨p, _, hy, hj⟩ := T.stable_max_witness C hC L U hLU ha j hL hU
    exact ⟨T.stableMaxWitness L p j, hy, hj⟩

end Thresholds
end ThresholdComponentScores
