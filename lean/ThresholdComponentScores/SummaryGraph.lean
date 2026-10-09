import ThresholdComponentScores.Components
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold

namespace ThresholdComponentScores.StableSummary

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Tagged uncertain vertices and the genuine stable induced components. -/
abbrev Node (G : SimpleGraph V) (S U : Finset V) :=
  {v // v ∈ U} ⊕ {C // C ∈ components G S}

noncomputable instance (G : SimpleGraph V) (S U : Finset V) : Fintype (Node G S U) := by
  classical
  unfold Node
  infer_instance

noncomputable def support {G : SimpleGraph V} {S U : Finset V} : Node G S U → Finset V
  | .inl u => {u.val}
  | .inr C => C.val

variable {G : SimpleGraph V} {S U : Finset V}

@[simp] theorem support_inl (u : {v // v ∈ U}) : support (Sum.inl u : Node G S U) = {u.val} := rfl
@[simp] theorem support_inr (C : {C // C ∈ components G S}) :
    support (Sum.inr C : Node G S U) = C.val := rfl

theorem support_nonempty (n : Node G S U) : (support n).Nonempty := by
  cases n with
  | inl u => exact Finset.singleton_nonempty _
  | inr C => exact components_nonempty C.property

theorem support_subset (n : Node G S U) : support n ⊆ S ∪ U := by
  cases n with
  | inl u => intro v hv; simp only [support_inl, Finset.mem_singleton] at hv; subst v
             exact Finset.mem_union_right _ u.property
  | inr C => intro v hv; exact Finset.mem_union_left _ (components_subset_active C.property hv)

theorem supports_cover {v : V} : (∃ n : Node G S U, v ∈ support n) ↔ v ∈ S ∪ U := by
  constructor
  · rintro ⟨n, hn⟩; exact support_subset n hn
  · intro hv
    rcases Finset.mem_union.mp hv with hs | hu
    · exact ⟨.inr ⟨component G S v, component_mem_components hs⟩, mem_component_self hs⟩
    · exact ⟨.inl ⟨v, hu⟩, Finset.mem_singleton_self v⟩

theorem node_eq_of_mem (hSU : Disjoint S U) {m n : Node G S U} {v : V}
    (hm : v ∈ support m) (hn : v ∈ support n) : m = n := by
  cases m with
  | inl u =>
    simp only [support_inl, Finset.mem_singleton] at hm
    subst v
    cases n with
    | inl w => simp only [support_inl, Finset.mem_singleton] at hn
               exact congrArg Sum.inl (Subtype.ext hn)
    | inr C => exact False.elim (Finset.disjoint_left.mp hSU
        (components_subset_active C.property hn) u.property)
  | inr C =>
    cases n with
    | inl u => simp only [support_inl, Finset.mem_singleton] at hn; subst v
               exact False.elim (Finset.disjoint_left.mp hSU
                 (components_subset_active C.property hm) u.property)
    | inr D => exact congrArg Sum.inr (Subtype.ext
        (components_eq_of_mem C.property D.property hm hn))

/-- Edges are witnessed by original source edges between different tagged fibres. -/
noncomputable def graph (G : SimpleGraph V) (S U : Finset V) : SimpleGraph (Node G S U) where
  Adj m n := m ≠ n ∧ ∃ u ∈ support m, ∃ v ∈ support n, G.Adj u v
  symm := ⟨by
    rintro m n ⟨hne, u, hu, v, hv, huv⟩
    exact ⟨hne.symm, v, hv, u, hu, huv.symm⟩⟩
  loopless := ⟨by intro n h; exact h.1 rfl⟩

/-- A stable component is connected by source paths entirely inside the stable set. -/
theorem support_connected (n : Node G S U) {u v : V}
    (hu : u ∈ support n) (hv : v ∈ support n) : (activeGraph G (S ∪ U)).Reachable u v := by
  cases n with
  | inl w => simp only [support_inl, Finset.mem_singleton] at hu hv
             subst u; subst v; exact .rfl
  | inr C =>
      exact (components_pairwise_reachable C.property hu hv).mono
        (activeGraph_mono Finset.subset_union_left)

/-- There are no edges between distinct stable-component nodes. -/
theorem no_component_edges (C D : {C // C ∈ components G S}) :
    ¬ (graph G S U).Adj (.inr C) (.inr D) := by
  rintro ⟨hne, u, hu, v, hv, huv⟩
  have heq : C.val = D.val := by
    have hr : (activeGraph G S).Reachable u v :=
      (show (activeGraph G S).Adj u v from
        ⟨huv, components_subset_active C.property hu, components_subset_active D.property hv⟩).reachable
    have hcu : component G S u = C.val := components_eq_of_mem
      (component_mem_components (components_subset_active C.property hu)) C.property
      (mem_component_self (components_subset_active C.property hu)) hu
    have hdv : component G S v = D.val := components_eq_of_mem
      (component_mem_components (components_subset_active D.property hv)) D.property
      (mem_component_self (components_subset_active D.property hv)) hv
    rw [← hcu, ← hdv]
    exact component_eq_of_reachable hr
  exact hne (congrArg Sum.inr (Subtype.ext heq))

/-- On uncertain nodes the summary has exactly the original source edges. -/
@[simp] theorem graph_adj_uncertain (u v : {v // v ∈ U}) :
    (graph G S U).Adj (.inl u) (.inl v) ↔ G.Adj u.val v.val := by
  constructor
  · rintro ⟨_, a, ha, b, hb, hab⟩
    simpa only [support_inl, Finset.mem_singleton] using
      (show G.Adj u.val v.val from by
        have hau := Finset.mem_singleton.mp ha
        have hbv := Finset.mem_singleton.mp hb
        simpa only [hau, hbv] using hab)
  · intro h
    refine ⟨?_, u.val, Finset.mem_singleton_self _, v.val, Finset.mem_singleton_self _, h⟩
    intro heq
    have huv : u = v := Sum.inl.inj heq
    exact G.irrefl (huv ▸ h)

/-- Boundary edges are precisely incidences with a source neighbor in the stable component. -/
@[simp] theorem graph_adj_boundary (u : {v // v ∈ U})
    (C : {C // C ∈ components G S}) :
    (graph G S U).Adj (.inl u) (.inr C) ↔ ∃ v ∈ C.val, G.Adj u.val v := by
  constructor
  · rintro ⟨_, a, ha, b, hb, hab⟩
    have hau := Finset.mem_singleton.mp ha
    exact ⟨b, hb, hau ▸ hab⟩
  · rintro ⟨v, hv, huv⟩
    exact ⟨Sum.inl_ne_inr, u.val, Finset.mem_singleton_self _, v, hv, huv⟩

/-- Expanding a collection of summary nodes retains their original vertex supports. -/
noncomputable def expand (D : Finset (Node G S U)) : Finset V := by
  classical
  exact D.biUnion support

@[simp] theorem mem_expand {D : Finset (Node G S U)} {v : V} :
    v ∈ expand D ↔ ∃ n ∈ D, v ∈ support n := by
  classical
  simp [expand]

/-- Internal stable paths remain active whenever the stable set is retained. -/
theorem support_connected_active {A : Finset V} (hSA : S ⊆ A)
    (n : Node G S U) {u v : V} (hu : u ∈ support n) (hv : v ∈ support n) :
    (activeGraph G A).Reachable u v := by
  cases n with
  | inl w => simp only [support_inl, Finset.mem_singleton] at hu hv
             subst u; subst v; exact .rfl
  | inr C => exact (components_pairwise_reachable C.property hu hv).mono (activeGraph_mono hSA)

/-- Active nodes are exactly those whose entire source fibre is active. -/
noncomputable def activeNodes (A : Finset V) : Finset (Node G S U) := by
  classical
  exact Finset.univ.filter (fun n => support n ⊆ A)

@[simp] theorem mem_activeNodes {A : Finset V} {n : Node G S U} :
    n ∈ activeNodes A ↔ support n ⊆ A := by
  classical
  simp [activeNodes]

theorem node_active_of_mem {A : Finset V} (hSA : S ⊆ A)
    {n : Node G S U} {v : V} (hv : v ∈ support n) (hva : v ∈ A) :
    n ∈ activeNodes A := by
  apply mem_activeNodes.mpr
  cases n with
  | inl u =>
      intro w hw
      have hvu : v = u.val := Finset.mem_singleton.mp hv
      have hwu : w = u.val := Finset.mem_singleton.mp hw
      simpa only [hwu, ← hvu] using hva
  | inr C => exact (components_subset_active C.property).trans hSA

/-- Every summary path lifts through actual source edges and internal stable paths. -/
theorem reachable_lift {A : Finset V} (hSA : S ⊆ A)
    {m n : Node G S U} (hm : m ∈ activeNodes A) (hn : n ∈ activeNodes A)
    (h : (activeGraph (graph G S U) (activeNodes A)).Reachable m n)
    {u v : V} (hu : u ∈ support m) (hv : v ∈ support n) :
    (activeGraph G A).Reachable u v := by
  have lift : ∀ {m n : Node G S U},
      (activeGraph (graph G S U) (activeNodes A)).Walk m n →
      ∀ {u v : V}, u ∈ support m → v ∈ support n →
      (activeGraph G A).Reachable u v := by
    intro m n p
    induction p with
    | nil => intro u v hu hv; exact support_connected_active hSA _ hu hv
    | @cons m k n hmk tail ih =>
      intro u v hu hv
      obtain ⟨hne, a, ha, b, hb, hab⟩ := hmk.1
      exact (support_connected_active hSA m hu ha).trans
        ((show (activeGraph G A).Adj a b from
          ⟨hab, mem_activeNodes.mp hmk.2.1 ha, mem_activeNodes.mp hmk.2.2 hb⟩).reachable.trans
          (ih hb hv))
  exact h.elim (fun p => lift p hu hv)

/-- Every source path projects to a summary path, contracting internal stable steps. -/
theorem reachable_project {A : Finset V} (hSA : S ⊆ A) (hAU : A ⊆ S ∪ U)
    {u v : V} (h : (activeGraph G A).Reachable u v)
    {m n : Node G S U} (hu : u ∈ support m) (hv : v ∈ support n)
    (hSU : Disjoint S U) :
    (activeGraph (graph G S U) (activeNodes A)).Reachable m n := by
  classical
  have proj : ∀ {u v : V}, (activeGraph G A).Walk u v →
      ∀ {m n : Node G S U}, u ∈ support m → v ∈ support n →
      (activeGraph (graph G S U) (activeNodes A)).Reachable m n := by
    intro u v p
    induction p with
    | nil => intro m n hm hn; have := node_eq_of_mem hSU hm hn; subst n; exact .rfl
    | @cons u w v huw tail ih =>
      intro m n hm hn
      obtain ⟨k, hk⟩ := supports_cover.mpr (hAU huw.2.2)
      have hkn := ih hk hn
      by_cases hmk : m = k
      · simpa [hmk] using hkn
      · exact (show (activeGraph (graph G S U) (activeNodes A)).Adj m k from
          ⟨⟨hmk, u, hm, w, hk, huw.1⟩,
            node_active_of_mem hSA hm huw.2.1, node_active_of_mem hSA hk huw.2.2⟩).reachable.trans hkn
  exact h.elim (fun p => proj p hu hv)

/-- Exact source/summary connectivity, proved from paths rather than assumed. -/
theorem reachable_iff {A : Finset V} (hSU : Disjoint S U) (hSA : S ⊆ A)
    (hAU : A ⊆ S ∪ U) {m n : Node G S U}
    (hm : m ∈ activeNodes A) (hn : n ∈ activeNodes A)
    {u v : V} (hu : u ∈ support m) (hv : v ∈ support n) :
    (activeGraph G A).Reachable u v ↔
      (activeGraph (graph G S U) (activeNodes A)).Reachable m n :=
  ⟨fun h => reachable_project hSA hAU h hu hv hSU,
    fun h => reachable_lift hSA hm hn h hu hv⟩

/-- Expansion takes every genuine summary component to its genuine source component. -/
theorem expand_component {A : Finset V} (hSU : Disjoint S U) (hSA : S ⊆ A)
    (hAU : A ⊆ S ∪ U) {m : Node G S U} (hm : m ∈ activeNodes A)
    {u : V} (hu : u ∈ support m) :
    expand (component (graph G S U) (activeNodes A) m) = component G A u := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨n, hn, hvn⟩ := mem_expand.mp hv
    obtain ⟨hna, hr⟩ := mem_component.mp hn
    exact mem_component.mpr ⟨mem_activeNodes.mp hna hvn,
      reachable_lift hSA hm hna hr hu hvn⟩
  · intro hv
    obtain ⟨hva, hr⟩ := mem_component.mp hv
    obtain ⟨n, hvn⟩ := supports_cover.mpr (hAU hva)
    exact mem_expand.mpr ⟨n, mem_component.mpr
      ⟨node_active_of_mem hSA hvn hva, reachable_project hSA hAU hr hu hvn hSU⟩, hvn⟩

theorem expand_injective (hSU : Disjoint S U) :
    Function.Injective (expand (G := G) (S := S) (U := U)) := by
  classical
  intro D E h
  ext n
  constructor
  · intro hn
    obtain ⟨v, hv⟩ := support_nonempty n
    have hve : v ∈ expand E := h ▸ mem_expand.mpr ⟨n, hn, hv⟩
    obtain ⟨m, hm, hvm⟩ := mem_expand.mp hve
    exact node_eq_of_mem hSU hvm hv ▸ hm
  · intro hn
    obtain ⟨v, hv⟩ := support_nonempty n
    have hvd : v ∈ expand D := h.symm ▸ mem_expand.mpr ⟨n, hn, hv⟩
    obtain ⟨m, hm, hvm⟩ := mem_expand.mp hvd
    exact node_eq_of_mem hSU hvm hv ▸ hm

/-- Exact image equality of concrete finite component sets, hence a bijection by injectivity. -/
theorem components_image_expand {A : Finset V} (hSU : Disjoint S U) (hSA : S ⊆ A)
    (hAU : A ⊆ S ∪ U) :
    (components (graph G S U) (activeNodes A)).image expand = components G A := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨m, hm, rfl⟩ := mem_components.mp hD
    obtain ⟨u, hu⟩ := support_nonempty m
    rw [expand_component hSU hSA hAU hm hu]
    exact component_mem_components (mem_activeNodes.mp hm hu)
  · intro hC
    obtain ⟨u, hu, rfl⟩ := mem_components.mp hC
    obtain ⟨m, hm⟩ := supports_cover.mpr (hAU hu)
    have hma := node_active_of_mem hSA hm hu
    exact Finset.mem_image.mpr ⟨component (graph G S U) (activeNodes A) m,
      component_mem_components hma, expand_component hSU hSA hAU hma hm⟩

/-- Expansion characterizes the genuine components in both directions. -/
theorem expand_mem_components_iff {A : Finset V} (hSU : Disjoint S U) (hSA : S ⊆ A)
    (hAU : A ⊆ S ∪ U) (D : Finset (Node G S U)) :
    expand D ∈ components G A ↔ D ∈ components (graph G S U) (activeNodes A) := by
  classical
  rw [← components_image_expand hSU hSA hAU]
  constructor
  · intro h
    obtain ⟨E, hE, hED⟩ := Finset.mem_image.mp h
    exact expand_injective hSU hED ▸ hE
  · intro h
    exact Finset.mem_image.mpr ⟨D, h, rfl⟩

/-- A literal bijection between the genuine finite source and summary component sets. -/
theorem components_bijOn_expand {A : Finset V} (hSU : Disjoint S U) (hSA : S ⊆ A)
    (hAU : A ⊆ S ∪ U) :
    Set.BijOn (expand (G := G) (S := S) (U := U))
      (↑(components (graph G S U) (activeNodes A)) : Set (Finset (Node G S U)))
      (↑(components G A) : Set (Finset V)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro D hD
    exact (expand_mem_components_iff hSU hSA hAU D).mpr hD
  · intro D hD E hE h
    exact expand_injective hSU h
  · intro C hC
    rw [← components_image_expand hSU hSA hAU] at hC
    obtain ⟨D, hD, hDC⟩ := Finset.mem_image.mp hC
    exact ⟨D, hD, hDC⟩

theorem support_pairwise_disjoint (hSU : Disjoint S U) (D : Finset (Node G S U)) :
    (↑D : Set (Node G S U)).PairwiseDisjoint support := by
  intro m hm n hn hmn
  apply Finset.disjoint_left.mpr
  intro v hvm hvn
  exact hmn (node_eq_of_mem hSU hvm hvn)

/-- Original-vertex mass, not the number of contracted nodes, is preserved. -/
theorem card_expand (hSU : Disjoint S U) (D : Finset (Node G S U)) :
    (expand D).card = ∑ n ∈ D, (support n).card := by
  classical
  exact Finset.card_biUnion (support_pairwise_disjoint hSU D)

/-- In particular, arbitrary signed rational source area sums are preserved. -/
theorem sum_expand {M : Type*} [AddCommMonoid M] (hSU : Disjoint S U)
    (D : Finset (Node G S U)) (a : V → M) :
    ∑ v ∈ expand D, a v = ∑ n ∈ D, ∑ v ∈ support n, a v := by
  classical
  exact Finset.sum_biUnion (support_pairwise_disjoint hSU D)

/-- Maximum labels commute with expansion of the actual source fibres. -/
theorem sup_expand {B : Type*} [SemilatticeSup B] [OrderBot B]
    (D : Finset (Node G S U)) (f : V → B) :
    (expand D).sup f = D.sup (fun n => (support n).sup f) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro v hv
    obtain ⟨n, hn, hvn⟩ := mem_expand.mp hv
    exact (Finset.le_sup (f := f) hvn).trans (Finset.le_sup (f := fun n => (support n).sup f) hn)
  · apply Finset.sup_le
    intro n hn
    apply Finset.sup_le
    intro v hv
    exact Finset.le_sup (mem_expand.mpr ⟨n, hn, hv⟩)

end ThresholdComponentScores.StableSummary
