import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.LocallyFiniteConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.LocallyFinitePasting

/-!
Source bridges and indexed-layer interfaces for Chapter 15. `LocallyFinite`
and `ParacompactSpace` are reused with their actual Mathlib meanings.
In particular no Hausdorff hypothesis is needed in any declaration here.
-/

open Set
open scoped Topology
universe u v w

namespace D10Topology.Ch15

/-- The canonical indexed local-finiteness predicate, with repetitions counted. -/
abbrev LocallyFiniteFamily {X : Type u} {I : Type v} [TopologicalSpace X]
    (A : I → Set X) : Prop :=
  Specs.D10Topology.Ch15.LocallyFiniteConventions.LocallyFiniteFamily A

/-- The refining family covers the space, and each member lies in an original member. -/
abbrev CoverRefinement {X : Type u} {I : Type v} {J : Type w}
    (U : I → Set X) (V : J → Set X) : Prop :=
  Specs.D10Topology.Ch15.LocallyFiniteConventions.CoverRefinement U V

/-- Every point has a neighborhood meeting at most one index. -/
abbrev LocallyDiscrete {X : Type u} {I : Type v} [TopologicalSpace X]
    (A : I → Set X) : Prop :=
  Specs.D10Topology.Ch15.LocallyFiniteConventions.LocallyDiscrete A

/-- Countably many locally finite layers of the original index type cover all indices. -/
abbrev SigmaLocallyFinite {X : Type u} {I : Type v} [TopologicalSpace X]
    (A : I → Set X) : Prop :=
  Specs.D10Topology.Ch15.LocallyFiniteConventions.SigmaLocallyFinite A

/-- Countably many locally discrete layers retain the original index multiplicities. -/
abbrev SigmaLocallyDiscrete {X : Type u} {I : Type v} [TopologicalSpace X]
    (A : I → Set X) : Prop :=
  Specs.D10Topology.Ch15.LocallyFiniteConventions.SigmaLocallyDiscrete A

/-- Paracompactness, with no implicit Hausdorff condition. -/
abbrev Paracompact (X : Type u) [TopologicalSpace X] : Prop :=
  Specs.D10Topology.Ch15.LocallyFiniteConventions.Paracompact X

variable {X : Type u} {I : Type v} {J : Type w} [TopologicalSpace X]

theorem locallyFinite_iff_neighborhood (A : I → Set X) :
    LocallyFiniteFamily A ↔ ∀ x, ∃ N ∈ 𝓝 x, {i | (A i ∩ N).Nonempty}.Finite :=
  Iff.rfl

theorem locallyFinite_iff_open_neighborhood (A : I → Set X) :
    LocallyFiniteFamily A ↔ ∀ x, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ {i | (A i ∩ U).Nonempty}.Finite :=
  Ch02.locallyFinite_iff_open_neighborhood A

omit [TopologicalSpace X] in
theorem coverRefinement_iff (U : I → Set X) (V : J → Set X) :
    CoverRefinement U V ↔ (∀ x : X, ∃ j, x ∈ V j) ∧ ∀ j, ∃ i, V j ⊆ U i := by
  simp only [CoverRefinement,
    Specs.D10Topology.Ch15.LocallyFiniteConventions.CoverRefinement, iUnion_eq_univ_iff]

omit [TopologicalSpace X] in
theorem coverRefinement_original_covers (U : I → Set X) (V : J → Set X)
    (h : CoverRefinement U V) : (⋃ i, U i) = univ := by
  apply iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp h.1 x
  obtain ⟨i, hi⟩ := h.2 j
  exact ⟨i, hi hj⟩

theorem locallyDiscrete_iff_open_neighborhood (A : I → Set X) :
    LocallyDiscrete A ↔ ∀ x, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ {i | (A i ∩ U).Nonempty}.Subsingleton := by
  constructor
  · intro h x
    obtain ⟨N, hN, hsub⟩ := h x
    obtain ⟨U, hUN, hU, hx⟩ := mem_nhds_iff.mp hN
    refine ⟨U, hU, hx, ?_⟩
    intro i hi j hj
    apply hsub
    · obtain ⟨y, hyA, hyU⟩ := hi
      exact ⟨y, hyA, hUN hyU⟩
    · obtain ⟨y, hyA, hyU⟩ := hj
      exact ⟨y, hyA, hUN hyU⟩
  · intro h x
    obtain ⟨U, hU, hx, hsub⟩ := h x
    exact ⟨U, hU.mem_nhds hx, hsub⟩

theorem locallyDiscrete_locallyFinite (A : I → Set X)
    (h : LocallyDiscrete A) : LocallyFiniteFamily A := by
  intro x
  obtain ⟨N, hN, hsub⟩ := h x
  exact ⟨N, hN, hsub.finite⟩

/-- Restriction preserves local discreteness provided indices are not merged. -/
theorem LocallyDiscrete.comp_injective {A : I → Set X} (h : LocallyDiscrete A)
    {e : J → I} (he : Function.Injective e) : LocallyDiscrete (A ∘ e) := by
  intro x
  obtain ⟨N, hN, hsub⟩ := h x
  refine ⟨N, hN, ?_⟩
  intro i hi j hj
  exact he (hsub hi hj)

theorem sigmaLocallyFinite_iff_layers (A : I → Set X) :
    SigmaLocallyFinite A ↔ ∃ c : I → ℕ,
      ∀ n, LocallyFinite (fun i : {i // c i = n} => A i) := by
  classical
  constructor
  · rintro ⟨L, hL, hfin⟩
    have hex : ∀ i : I, ∃ n, i ∈ L n := iUnion_eq_univ_iff.mp hL
    choose c hc using hex
    refine ⟨c, fun n => ?_⟩
    let e : {i // c i = n} → L n := fun i =>
      ⟨i.val, by simpa only [i.property] using hc i.val⟩
    have he : Function.Injective e := fun i j hij =>
      Subtype.ext (congrArg (fun k : L n => k.val) hij)
    exact (hfin n).comp_injective he
  · rintro ⟨c, hc⟩
    exact ⟨fun n => {i | c i = n},
      iUnion_eq_univ_iff.mpr (fun i => ⟨c i, rfl⟩), hc⟩

theorem sigmaLocallyDiscrete_iff_layers (A : I → Set X) :
    SigmaLocallyDiscrete A ↔ ∃ c : I → ℕ,
      ∀ n, LocallyDiscrete (fun i : {i // c i = n} => A i) := by
  classical
  constructor
  · rintro ⟨L, hL, hdisc⟩
    have hex : ∀ i : I, ∃ n, i ∈ L n := iUnion_eq_univ_iff.mp hL
    choose c hc using hex
    refine ⟨c, fun n => ?_⟩
    let e : {i // c i = n} → L n := fun i =>
      ⟨i.val, by simpa only [i.property] using hc i.val⟩
    have he : Function.Injective e := fun i j hij =>
      Subtype.ext (congrArg (fun k : L n => k.val) hij)
    exact LocallyDiscrete.comp_injective (hdisc n) he
  · rintro ⟨c, hc⟩
    exact ⟨fun n => {i | c i = n},
      iUnion_eq_univ_iff.mpr (fun i => ⟨c i, rfl⟩), hc⟩

theorem sigmaLocallyDiscrete_sigmaLocallyFinite (A : I → Set X)
    (h : SigmaLocallyDiscrete A) : SigmaLocallyFinite A := by
  obtain ⟨L, hL, hd⟩ := h
  exact ⟨L, hL, fun n => locallyDiscrete_locallyFinite _ (hd n)⟩

theorem paracompact_iff_open_cover_refinement (X : Type u) [TopologicalSpace X] :
    Paracompact X ↔
      ∀ (I : Type u) (U : I → Set X), (∀ i, IsOpen (U i)) →
        (⋃ i, U i) = univ → ∃ (J : Type u) (V : J → Set X),
          (∀ j, IsOpen (V j)) ∧ LocallyFiniteFamily V ∧ CoverRefinement U V := by
  constructor
  · intro h I U ho hU
    obtain ⟨J, V, hVo, hV, hf, hsub⟩ := h.locallyFinite_refinement I U ho hU
    exact ⟨J, V, hVo, hf, hV, hsub⟩
  · intro h
    refine ⟨fun I U ho hU => ?_⟩
    obtain ⟨J, V, hVo, hf, hV, hsub⟩ := h I U ho hU
    exact ⟨J, V, hVo, hV, hf, hsub⟩

theorem paracompact_precise_refinement (h : Paracompact X) (U : I → Set X)
    (ho : ∀ i, IsOpen (U i)) (hU : (⋃ i, U i) = univ) :
    ∃ V : I → Set X, (∀ i, IsOpen (V i)) ∧ LocallyFiniteFamily V ∧
      CoverRefinement U V ∧ ∀ i, V i ⊆ U i := by
  let : ParacompactSpace X := h
  obtain ⟨V, hVo, hV, hf, hsub⟩ := precise_refinement U ho hU
  exact ⟨V, hVo, hf, ⟨hV, fun i => ⟨i, hsub i⟩⟩, hsub⟩

/-- Local finiteness implies finiteness of the indices containing any point. -/
theorem locallyFinite_point_finite (A : I → Set X) (h : LocallyFiniteFamily A) :
    ∀ x, {i | x ∈ A i}.Finite :=
  h.point_finite

/-- The indexed singleton family on the indiscrete natural numbers is point finite
but not locally finite, witnessing the strict distinction in the source. -/
theorem pointFinite_not_locallyFinite :
    ∃ (t : TopologicalSpace ℕ) (A : ℕ → Set ℕ),
      (∀ x, {i | x ∈ A i}.Finite) ∧ ¬ @LocallyFinite ℕ ℕ t A := by
  let : TopologicalSpace ℕ := ⊤
  refine ⟨⊤, fun i => {i}, ?_, ?_⟩
  · intro x
    apply (finite_singleton x).subset
    intro i hi
    exact (show x = i from hi).symm
  · intro h
    obtain ⟨N, hN, hfin⟩ := h 0
    have hNu : N = univ := by
      simpa only [nhds_top, Filter.mem_top] using hN
    have hf : (univ : Set ℕ).Finite := by
      simpa only [hNu, inter_univ, singleton_nonempty, ofPred_true] using hfin
    exact infinite_univ hf

theorem locallyFinite_const_iff (A : Set X) (hA : A.Nonempty) :
    LocallyFiniteFamily (fun _ : I => A) ↔ Finite I := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := hA
    have hf : (univ : Set I).Finite := by
      simpa only [hx, ofPred_true] using h.point_finite x
    exact finite_univ_iff.mp hf
  · intro h
    let := h
    exact locallyFinite_of_finite _

theorem locallyDiscrete_const_iff (A : Set X) (hA : A.Nonempty) :
    LocallyDiscrete (fun _ : I => A) ↔ Subsingleton I := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := hA
    obtain ⟨N, hN, hsub⟩ := h x
    refine ⟨fun i j => ?_⟩
    exact hsub ⟨x, hx, mem_of_mem_nhds hN⟩ ⟨x, hx, mem_of_mem_nhds hN⟩
  · intro h x
    exact ⟨univ, Filter.univ_mem, fun _ _ _ _ => h.elim _ _⟩

theorem empty_members (X : Type u) (I : Type v) [TopologicalSpace X] :
    LocallyFiniteFamily (fun _ : I => (∅ : Set X)) ∧
      LocallyDiscrete (fun _ : I => (∅ : Set X)) := by
  have hd : LocallyDiscrete (fun _ : I => (∅ : Set X)) := by
    intro x
    refine ⟨univ, Filter.univ_mem, ?_⟩
    simp
  exact ⟨locallyDiscrete_locallyFinite _ hd, hd⟩

end D10Topology.Ch15
