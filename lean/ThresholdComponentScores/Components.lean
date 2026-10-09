import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Finite connected components of the graph on the active vertices.
Inactive vertices are removed from every component, including their reflexive paths. -/
namespace ThresholdComponentScores

variable {V : Type*} [Fintype V] [DecidableEq V]

def activeGraph (G : SimpleGraph V) (active : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ active ∧ v ∈ active
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro v h; exact G.irrefl h.1⟩

noncomputable def component (G : SimpleGraph V) (active : Finset V) (v : V) : Finset V := by
  classical
  exact active.filter (fun w => (activeGraph G active).Reachable v w)

noncomputable def components (G : SimpleGraph V) (active : Finset V) : Finset (Finset V) := by
  classical
  exact active.image (component G active)

variable {G : SimpleGraph V} {active larger : Finset V} {u v w : V} {C D : Finset V}

@[simp] theorem mem_component : w ∈ component G active v ↔
    w ∈ active ∧ (activeGraph G active).Reachable v w := by
  classical
  simp [component]

@[simp] theorem mem_components : C ∈ components G active ↔
    ∃ v ∈ active, component G active v = C := by
  classical
  simp [components]

theorem component_subset_active : component G active v ⊆ active := by
  intro w hw
  exact (mem_component.mp hw).1

theorem mem_component_self (hv : v ∈ active) : v ∈ component G active v :=
  mem_component.mpr ⟨hv, .rfl⟩

theorem component_nonempty (hv : v ∈ active) : (component G active v).Nonempty :=
  ⟨v, mem_component_self hv⟩

theorem component_mem_components (hv : v ∈ active) : component G active v ∈ components G active :=
  mem_components.mpr ⟨v, hv, rfl⟩

theorem components_nonempty (hC : C ∈ components G active) : C.Nonempty := by
  obtain ⟨v, hv, rfl⟩ := mem_components.mp hC
  exact component_nonempty hv

theorem components_subset_active (hC : C ∈ components G active) : C ⊆ active := by
  obtain ⟨v, _, rfl⟩ := mem_components.mp hC
  exact component_subset_active

theorem mem_component_iff_reachable (hw : w ∈ active) :
    w ∈ component G active v ↔ (activeGraph G active).Reachable v w := by
  simp [hw]

theorem component_eq_of_reachable (h : (activeGraph G active).Reachable u v) :
    component G active u = component G active v := by
  ext w
  simp only [mem_component]
  exact ⟨fun ⟨hw, huw⟩ => ⟨hw, h.symm.trans huw⟩,
    fun ⟨hw, hvw⟩ => ⟨hw, h.trans hvw⟩⟩

theorem component_eq_iff_reachable (hu : u ∈ active) :
    component G active u = component G active v ↔ (activeGraph G active).Reachable u v := by
  constructor
  · intro h
    have hm : u ∈ component G active v := h ▸ mem_component_self hu
    exact (mem_component.mp hm).2.symm
  · exact component_eq_of_reachable

theorem components_cover : (∃ C ∈ components G active, v ∈ C) ↔ v ∈ active := by
  constructor
  · rintro ⟨C, hC, hv⟩
    exact components_subset_active hC hv
  · intro hv
    exact ⟨component G active v, component_mem_components hv, mem_component_self hv⟩

theorem components_eq_of_mem (hC : C ∈ components G active) (hD : D ∈ components G active)
    (hvC : v ∈ C) (hvD : v ∈ D) : C = D := by
  obtain ⟨u, _, rfl⟩ := mem_components.mp hC
  obtain ⟨w, _, rfl⟩ := mem_components.mp hD
  exact component_eq_of_reachable ((mem_component.mp hvC).2.trans (mem_component.mp hvD).2.symm)

theorem components_disjoint_or_eq (hC : C ∈ components G active)
    (hD : D ∈ components G active) : Disjoint C D ∨ C = D := by
  classical
  by_cases h : C = D
  · exact Or.inr h
  · left
    apply Finset.disjoint_left.mpr
    intro v hvC hvD
    exact h (components_eq_of_mem hC hD hvC hvD)

theorem activeGraph_mono (h : active ⊆ larger) : activeGraph G active ≤ activeGraph G larger := by
  intro u v huv
  exact ⟨huv.1, h huv.2.1, h huv.2.2⟩

theorem component_mono (h : active ⊆ larger) : component G active v ⊆ component G larger v := by
  intro w hw
  obtain ⟨hwa, hr⟩ := mem_component.mp hw
  exact mem_component.mpr ⟨h hwa, hr.mono (activeGraph_mono h)⟩

theorem component_subset_unique (h : active ⊆ larger) (hC : C ∈ components G active) :
    ∃! D, D ∈ components G larger ∧ C ⊆ D := by
  obtain ⟨v, hv, rfl⟩ := mem_components.mp hC
  refine ⟨component G larger v, ⟨component_mem_components (h hv), component_mono h⟩, ?_⟩
  intro D hD
  exact components_eq_of_mem hD.1 (component_mem_components (h hv))
    (hD.2 (mem_component_self hv)) (mem_component_self (h hv))

/-- Maximality: every active set reachable from the root lies in its component. -/
theorem subset_component_iff {S : Finset V} : S ⊆ component G active v ↔
    S ⊆ active ∧ ∀ w ∈ S, (activeGraph G active).Reachable v w := by
  constructor
  · intro h
    exact ⟨fun w hw => (mem_component.mp (h hw)).1,
      fun w hw => (mem_component.mp (h hw)).2⟩
  · rintro ⟨ha, hr⟩ w hw
    exact mem_component.mpr ⟨ha hw, hr w hw⟩

/-- The finite API uses precisely Mathlib's quotient by graph reachability. -/
theorem mem_component_iff_connectedComponent : w ∈ component G active v ↔
    w ∈ active ∧ (activeGraph G active).connectedComponentMk v =
      (activeGraph G active).connectedComponentMk w := by
  rw [mem_component, SimpleGraph.ConnectedComponent.eq]

/-- Reachability agrees with the actual induced graph on the active subtype. -/
theorem reachable_induce_iff (u v : {x // x ∈ active}) :
    (G.induce (↑active : Set V)).Reachable u v ↔
      (activeGraph G active).Reachable u.val v.val := by
  constructor
  · intro h
    let f : G.induce (↑active : Set V) →g activeGraph G active :=
      { toFun := Subtype.val
        map_rel' := by intro a b hab; exact ⟨hab, a.property, b.property⟩ }
    exact h.map f
  · intro h
    have lift : ∀ {a b : V}, (activeGraph G active).Walk a b →
        ∀ (ha : a ∈ active) (hb : b ∈ active),
        (G.induce (↑active : Set V)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a b p
      induction p with
      | nil => intro ha hb; exact .rfl
      | @cons a c b hac tail ih =>
        intro ha hb
        exact (show (G.induce (↑active : Set V)).Adj ⟨a, ha⟩ ⟨c, hac.2.2⟩ from hac.1).reachable.trans
          (ih hac.2.2 hb)
    exact h.elim (fun p => lift p u.property v.property)

/-- Vertices in a component are connected through active vertices. -/
theorem components_pairwise_reachable (hC : C ∈ components G active)
    (hu : u ∈ C) (hv : v ∈ C) : (activeGraph G active).Reachable u v := by
  obtain ⟨w, _, rfl⟩ := mem_components.mp hC
  exact (mem_component.mp hu).2.symm.trans (mem_component.mp hv).2

/-- No larger active connected set can strictly contain a component. -/
theorem components_maximal (hC : C ∈ components G active) (hCD : C ⊆ D)
    (hDa : D ⊆ active)
    (hconn : ∀ u ∈ D, ∀ v ∈ D, (activeGraph G active).Reachable u v) : D = C := by
  obtain ⟨u, hu, rfl⟩ := mem_components.mp hC
  apply Finset.Subset.antisymm
  · intro v hv
    exact mem_component.mpr ⟨hDa hv, hconn u (hCD (mem_component_self hu)) v hv⟩
  · exact hCD

/-- Exact nonempty maximal connected-set characterization of the finite components. -/
theorem mem_components_iff_maximal : C ∈ components G active ↔
    C.Nonempty ∧ C ⊆ active ∧
    (∀ u ∈ C, ∀ v ∈ C, (activeGraph G active).Reachable u v) ∧
    (∀ D : Finset V, C ⊆ D → D ⊆ active →
      (∀ u ∈ D, ∀ v ∈ D, (activeGraph G active).Reachable u v) → D = C) := by
  constructor
  · intro hC
    exact ⟨components_nonempty hC, components_subset_active hC,
      fun _ hu _ hv => components_pairwise_reachable hC hu hv,
      fun _ hCD hDa hc => components_maximal hC hCD hDa hc⟩
  · rintro ⟨⟨u, hu⟩, hCa, hconn, hmax⟩
    have hua : u ∈ active := hCa hu
    have hsub : C ⊆ component G active u := by
      intro v hv
      exact mem_component.mpr ⟨hCa hv, hconn u hu v hv⟩
    have heq : component G active u = C := hmax _ hsub component_subset_active
      (fun _ hv _ hw => components_pairwise_reachable (component_mem_components hua) hv hw)
    exact heq ▸ component_mem_components hua

@[simp] theorem components_empty : components G ∅ = ∅ := by
  classical
  simp [components]

end ThresholdComponentScores
