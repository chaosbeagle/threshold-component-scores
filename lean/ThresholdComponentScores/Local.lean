import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fintype.Card

namespace ThresholdComponentScores

/-- Rational activation and strictly ordered density breakpoints (zero-based). -/
structure Thresholds (q : ℕ) where
  tau : ℚ
  breaks : Fin q → ℚ
  strict : StrictMono breaks

abbrev State (q : ℕ) := Option (Fin (q + 1))

namespace Thresholds
variable {q : ℕ} (T : Thresholds q)

def bin (t : ℚ) : Fin (q + 1) :=
  ⟨(Finset.univ.filter (fun i : Fin q => T.breaks i ≤ t)).card, by
    have := Finset.card_le_card (Finset.filter_subset (fun i : Fin q => T.breaks i ≤ t) Finset.univ)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega⟩

def state (t : ℚ) : State q := if t < T.tau then none else some (T.bin t)

theorem bin_monotone : Monotone T.bin := by
  intro a b hab
  change (Finset.univ.filter (fun i : Fin q => T.breaks i ≤ a)).card ≤
    (Finset.univ.filter (fun i : Fin q => T.breaks i ≤ b)).card
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans hab

theorem bin_max (a b : ℚ) : T.bin (max a b) = max (T.bin a) (T.bin b) :=
  T.bin_monotone.map_max

/-- Binning commutes with the attained maximum on any nonempty finite family. -/
theorem bin_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℚ) :
    T.bin (s.sup' hs f) = s.sup' hs (fun i => T.bin (f i)) := by
  exact Finset.apply_sup'_eq_sup'_comp hs T.bin (fun a b => T.bin_monotone.map_sup a b)

theorem bin_sup {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℚ) :
    T.bin (s.sup' hs f) = s.sup (fun i => T.bin (f i)) := by
  rw [T.bin_sup' s hs f, Finset.sup'_eq_sup]

/-- Every crossed breakpoint has index strictly below the resulting bin. -/
theorem break_le_iff (t : ℚ) (i : Fin q) : T.breaks i ≤ t ↔ i.val < (T.bin t).val := by
  constructor
  · intro h
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun k : Fin q => T.breaks k ≤ t) := by
      intro k hk
      simp only [Finset.mem_Iic] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (T.strict.monotone hk).trans h
    have hc := Finset.card_le_card hsub
    simp only [Fin.card_Iic] at hc
    change i.val < (Finset.univ.filter (fun k : Fin q => T.breaks k ≤ t)).card
    omega
  · intro h
    by_contra hn
    have hsub : Finset.univ.filter (fun k : Fin q => T.breaks k ≤ t) ⊆ Finset.Iio i := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp only [Finset.mem_Iio]
      by_contra hki
      have hik : i ≤ k := le_of_not_gt hki
      exact hn ((T.strict.monotone hik).trans hk)
    have hc := Finset.card_le_card hsub
    simp only [Fin.card_Iio] at hc
    change i.val < (Finset.univ.filter (fun k : Fin q => T.breaks k ≤ t)).card at h
    omega

@[simp] theorem state_eq_none_iff (t : ℚ) : T.state t = none ↔ t < T.tau := by
  simp [state]

@[simp] theorem state_eq_some_iff (t : ℚ) (j : Fin (q+1)) :
    T.state t = some j ↔ T.tau ≤ t ∧ T.bin t = j := by
  simp [state, not_lt]

theorem state_eq_state_iff (a b : ℚ) : T.state a = T.state b ↔
    (a < T.tau ∧ b < T.tau) ∨
    (T.tau ≤ a ∧ T.tau ≤ b ∧ T.bin a = T.bin b) := by
  by_cases ha : a < T.tau <;> by_cases hb : b < T.tau <;>
    simp [state, ha, hb, ← not_lt]

/-- The lower endpoint of an active cell; no ordering of tau relative to breaks is assumed. -/
def lower (j : Fin (q+1)) : ℚ :=
  if h : j.val = 0 then T.tau else max T.tau (T.breaks ⟨j.val-1, by omega⟩)

/-- Cell intersection definition, before elimination of the rational witness. -/
def allowed (L U : ℚ) (s : State q) : Prop :=
  ∃ t : ℚ, L ≤ t ∧ t ≤ U ∧ T.state t = s

/-- Explicit rational representative from manuscript (3.2). -/
def representative (L : ℚ) (s : State q) : ℚ :=
  match s with
  | none => L
  | some j => max L (T.lower j)

theorem bin_eq_iff (t : ℚ) (j : Fin (q+1)) :
    T.bin t = j ↔ ∀ i : Fin q, (T.breaks i ≤ t ↔ i.val < j.val) := by
  constructor
  · intro h i
    rw [T.break_le_iff, h]
  · intro h
    apply Fin.ext
    by_contra hn
    have hb := (T.bin t).isLt
    have hj := j.isLt
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · let i : Fin q := ⟨(T.bin t).val, by omega⟩
      have hc := (h i).2 (by dsimp [i]; omega)
      have hd := (T.break_le_iff t i).1 hc
      dsimp [i] at hd
      omega
    · let i : Fin q := ⟨j.val, by omega⟩
      have hc := (T.break_le_iff t i).2 (by dsimp [i]; omega)
      have hd := (h i).1 hc
      dsimp [i] at hd
      omega

/-- Equality at a breakpoint belongs to the upper-index bin. -/
theorem bin_breakpoint (i : Fin q) : (T.bin (T.breaks i)).val = i.val + 1 := by
  have h : T.bin (T.breaks i) = (⟨i.val+1, by omega⟩ : Fin (q+1)) := by
    apply (T.bin_eq_iff _ _).2
    intro k
    rw [T.strict.le_iff_le]
    change k.val ≤ i.val ↔ k.val < i.val+1
    omega
  exact congrArg Fin.val h

@[simp] theorem bin_zero (T : Thresholds 0) (t : ℚ) : T.bin t = 0 := by
  apply Fin.ext
  have := (T.bin t).isLt
  simp only [Fin.val_zero]
  omega

theorem lower_le_iff (j : Fin (q+1)) (t : ℚ) :
    T.lower j ≤ t ↔ T.tau ≤ t ∧ ∀ i : Fin q, i.val < j.val → T.breaks i ≤ t := by
  unfold lower
  split_ifs with h
  · simp [h]
  · rw [max_le_iff]
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨ha, fun i hi => ?_⟩
      apply le_trans (T.strict.monotone ?_) hb
      change i.val ≤ j.val - 1
      omega
    · rintro ⟨ha, hb⟩
      exact ⟨ha, hb _ (by simp; omega)⟩

/-- The active cell is closed below and strictly open at its next breakpoint. -/
theorem state_eq_some_cell (t : ℚ) (j : Fin (q+1)) :
    T.state t = some j ↔ T.lower j ≤ t ∧
      ∀ h : j.val < q, t < T.breaks ⟨j.val, h⟩ := by
  rw [state_eq_some_iff, T.bin_eq_iff, T.lower_le_iff]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨⟨ha, fun i hi => (hb i).2 hi⟩, ?_⟩
    intro h
    exact lt_of_not_ge (fun hc => (Nat.lt_irrefl j.val) ((hb ⟨j.val,h⟩).1 hc))
  · rintro ⟨⟨ha, hb⟩, hc⟩
    refine ⟨ha, fun i => ⟨?_, hb i⟩⟩
    intro hi
    by_contra hn
    have hji : j.val ≤ i.val := Nat.le_of_not_gt hn
    have hj : j.val < q := lt_of_le_of_lt hji i.isLt
    have ht := hc hj
    have hm : T.breaks ⟨j.val,hj⟩ ≤ T.breaks i := T.strict.monotone hji
    exact (not_lt_of_ge (hm.trans hi)) ht

theorem allowed_none_iff {L U : ℚ} (hLU : L ≤ U) :
    T.allowed L U none ↔ L < T.tau := by
  constructor
  · rintro ⟨t, htL, _, ht⟩
    exact htL.trans_lt ((T.state_eq_none_iff t).1 ht)
  · intro h
    exact ⟨L, le_rfl, hLU, (T.state_eq_none_iff L).2 h⟩

/-- Explicit predicates valid also for the top bin and q = 0. -/
theorem allowed_some_iff {L U : ℚ} (hLU : L ≤ U) (j : Fin (q+1)) :
    T.allowed L U (some j) ↔ T.lower j ≤ U ∧
      ∀ h : j.val < q, L < T.breaks ⟨j.val,h⟩ ∧ T.lower j < T.breaks ⟨j.val,h⟩ := by
  constructor
  · rintro ⟨t, htL, htU, ht⟩
    obtain ⟨hlo, hhi⟩ := (T.state_eq_some_cell t j).1 ht
    exact ⟨hlo.trans htU, fun h => ⟨htL.trans_lt (hhi h), hlo.trans_lt (hhi h)⟩⟩
  · rintro ⟨hlo, hhi⟩
    refine ⟨max L (T.lower j), le_max_left _ _, max_le hLU hlo, ?_⟩
    apply (T.state_eq_some_cell _ j).2
    exact ⟨le_max_right _ _, fun h => max_lt (hhi h).1 (hhi h).2⟩

theorem allowed_some_below_iff {L U : ℚ} (hLU : L ≤ U)
    (j : Fin (q+1)) (hj : j.val < q) :
    T.allowed L U (some j) ↔ T.lower j ≤ U ∧
      L < T.breaks ⟨j.val,hj⟩ ∧ T.lower j < T.breaks ⟨j.val,hj⟩ := by
  rw [T.allowed_some_iff hLU]
  simp [hj]

theorem allowed_some_top_iff {L U : ℚ} (hLU : L ≤ U) :
    T.allowed L U (some (Fin.last q)) ↔ T.lower (Fin.last q) ≤ U := by
  rw [T.allowed_some_iff hLU]
  simp

/-- Exact rational witness lifting for every allowed state. -/
theorem representative_spec {L U : ℚ} (hLU : L ≤ U) {s : State q}
    (hs : T.allowed L U s) :
    L ≤ T.representative L s ∧ T.representative L s ≤ U ∧
      T.state (T.representative L s) = s := by
  cases s with
  | none =>
    exact ⟨le_rfl, hLU, (T.state_eq_none_iff L).2 ((T.allowed_none_iff hLU).1 hs)⟩
  | some j =>
    obtain ⟨hlo, hhi⟩ := (T.allowed_some_iff hLU j).1 hs
    refine ⟨le_max_left _ _, max_le hLU hlo, ?_⟩
    apply (T.state_eq_some_cell _ j).2
    exact ⟨le_max_right _ _, fun h => max_lt (hhi h).1 (hhi h).2⟩

end Thresholds
end ThresholdComponentScores
