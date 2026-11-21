import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.Surfaces
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section
open Set
open scoped Topology Manifold

namespace D12Complex.Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]

/-- Weakly complex differentiable coordinate maps form a pregroupoid. -/
private def holomorphicPregroupoid : Pregroupoid ℂ where
  property f s := ∀ x ∈ s, DifferentiableAt ℂ f x
  comp hf hg _ _ _ x hx := (hg _ hx.2).comp x (hf x hx.1)
  id_mem x _ := differentiableAt_id
  locality _ h x hx := by
    obtain ⟨v, _, hv, hf⟩ := h x hx
    exact hf x ⟨hx, hv⟩
  congr hu h hf x hx :=
    (hf x hx).congr_of_eventuallyEq ((hu.eventually_mem hx).mono fun y hy => h y hy)

private def holomorphicGroupoid : StructureGroupoid ℂ := holomorphicPregroupoid.groupoid

private theorem mem_holomorphicGroupoid (t : OpenPartialHomeomorph ℂ ℂ) :
    t ∈ holomorphicGroupoid ↔ BiholomorphicPair t.source t.target t t.symm := by
  constructor
  · intro ht
    exact ⟨⟨t.open_source, ht.1⟩, ⟨t.open_target, ht.2⟩,
      t.mapsTo, t.symm.mapsTo, t.leftInvOn, t.rightInvOn⟩
  · intro ht
    exact ⟨ht.1.2, ht.2.1.2⟩

theorem compatibleCharts_symm {e f : ComplexChart X} (h : CompatibleCharts e f) :
    CompatibleCharts f e := by
  apply (mem_holomorphicGroupoid _).mp
  have ht := holomorphicGroupoid.symm ((mem_holomorphicGroupoid _).mpr h)
  exact ht

/-- A covering atlas provides the auxiliary charted-space structure used in the
locality proof for the maximal atlas. It adds no regularity assumptions. -/
@[instance_reducible] private def chartedSpaceOfAtlas (A : Set (ComplexChart X)) (hA : IsAtlas A) :
    ChartedSpace ℂ X where
  atlas := Subtype.val '' A
  chartAt x := (hA.1 x).choose.val
  mem_chart_source x := (hA.1 x).choose_spec.2
  chart_mem_atlas x := ⟨(hA.1 x).choose, (hA.1 x).choose_spec.1, rfl⟩

private theorem maximalAtlas_pairwise (A : Set (ComplexChart X)) (hA : IsAtlas A)
    {e f : ComplexChart X} (he : e ∈ maximalAtlas A) (hf : f ∈ maximalAtlas A) :
    CompatibleCharts e f := by
  let := chartedSpaceOfAtlas A hA
  have he' : e.val ∈ holomorphicGroupoid.maximalAtlas X := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨(mem_holomorphicGroupoid _).mpr (he g hg),
      (mem_holomorphicGroupoid _).mpr (compatibleCharts_symm (he g hg))⟩
  have hf' : f.val ∈ holomorphicGroupoid.maximalAtlas X := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨(mem_holomorphicGroupoid _).mpr (hf g hg),
      (mem_holomorphicGroupoid _).mpr (compatibleCharts_symm (hf g hg))⟩
  exact (mem_holomorphicGroupoid _).mp
    (holomorphicGroupoid.compatible_of_mem_maximalAtlas he' hf')

theorem atlas_union {A B : Set (ComplexChart X)} (hA : IsAtlas A) (hB : IsAtlas B)
    (h : CompatibleAtlases A B) : IsAtlas (A ∪ B) := by
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨e, he, hx⟩ := hA.1 x
    exact ⟨e, Or.inl he, hx⟩
  · intro e he f hf
    rcases he with he | he <;> rcases hf with hf | hf
    · exact hA.2 e he f hf
    · exact h e he f hf
    · exact compatibleCharts_symm (h f hf e he)
    · exact hB.2 e he f hf

theorem subset_maximalAtlas {A : Set (ComplexChart X)} (hA : IsAtlas A) :
    A ⊆ maximalAtlas A := fun e he f hf => hA.2 e he f hf

theorem maximalAtlas_isAtlas {A : Set (ComplexChart X)} (hA : IsAtlas A) :
    IsAtlas (maximalAtlas A) := by
  refine ⟨fun x => ?_, fun _ he _ hf => maximalAtlas_pairwise A hA he hf⟩
  obtain ⟨e, he, hx⟩ := hA.1 x
  exact ⟨e, subset_maximalAtlas hA he, hx⟩

theorem maximalAtlas_isMaximal {A : Set (ComplexChart X)} (hA : IsAtlas A) :
    IsMaximalAtlas (maximalAtlas A) := by
  refine ⟨maximalAtlas_isAtlas hA, fun B hB hsub => ?_⟩
  apply Set.Subset.antisymm _ hsub
  intro e he f hf
  exact hB.2 e he f (hsub (subset_maximalAtlas hA hf))

theorem maximalAtlas_unique {A : Set (ComplexChart X)} (hA : IsAtlas A) :
    ∃! B, IsMaximalAtlas B ∧ A ⊆ B := by
  refine ⟨maximalAtlas A, ⟨maximalAtlas_isMaximal hA, subset_maximalAtlas hA⟩, ?_⟩
  rintro B ⟨hB, hAB⟩
  have hBM : B ⊆ maximalAtlas A := fun e he f hf => hB.1.2 e he f (hAB hf)
  exact (hB.2 _ (maximalAtlas_isAtlas hA) hBM).symm

/-- The coordinate disks make a surface locally path connected. Connectedness
then gives paths between every pair of points. -/
theorem surface_pathConnected (S : RiemannSurface X) : PathConnectedSpace X := by
  let := S.connected
  let := chartedSpaceOfAtlas S.atlas S.isAtlas
  let := ChartedSpace.locallyPathConnectedSpace ℂ X
  exact pathConnectedSpace_iff_connectedSpace.mpr inferInstance

theorem compatibleCharts_refl (e : ComplexChart X) : CompatibleCharts e e := by
  apply (mem_holomorphicGroupoid _).mp
  apply holomorphicGroupoid.mem_of_eqOnSource
    (show OpenPartialHomeomorph.ofSet e.val.target e.val.open_target ∈
      holomorphicGroupoid from
      ⟨fun _ _ => differentiableAt_id, fun _ _ => differentiableAt_id⟩)
  exact e.val.symm_trans_self

theorem atlas_iUnion {ι : Type*} [Nonempty ι] (A : ι → Set (ComplexChart X))
    (hA : ∀ i, IsAtlas (A i)) (h : ∀ i j, CompatibleAtlases (A i) (A j)) :
    IsAtlas (⋃ i, A i) := by
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨e, he, hx⟩ := (hA i).1 x
    exact ⟨e, mem_iUnion.mpr ⟨i, he⟩, hx⟩
  · intro e he f hf
    obtain ⟨i, hi⟩ := mem_iUnion.mp he
    obtain ⟨j, hj⟩ := mem_iUnion.mp hf
    exact h i j e hi f hj

/-- Compatible atlases describe exactly the same maximal complex structure. -/
theorem compatibleAtlases_iff_maximalAtlas_eq {A B : Set (ComplexChart X)}
    (hA : IsAtlas A) (hB : IsAtlas B) :
    CompatibleAtlases A B ↔ maximalAtlas A = maximalAtlas B := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro e he f hf
      exact maximalAtlas_pairwise A hA he
        (fun g hg => compatibleCharts_symm (h g hg f hf))
    · intro e he f hf
      exact maximalAtlas_pairwise B hB he (h f hf)
  · intro h e he f hf
    exact maximalAtlas_pairwise A hA (subset_maximalAtlas hA he)
      (h ▸ subset_maximalAtlas hB hf)

theorem planeChart_apply (Ω : Set ℂ) (hΩ : IsDomain Ω) (z : Ω) :
    (planeChart Ω hΩ).val z = (z : ℂ) := by
  simp [planeChart]

theorem planeChart_source (Ω : Set ℂ) (hΩ : IsDomain Ω) :
    (planeChart Ω hΩ).val.source = Set.univ := by
  simp [planeChart]

theorem planeChart_target (Ω : Set ℂ) (hΩ : IsDomain Ω) :
    (planeChart Ω hΩ).val.target = Ω := by
  simp [planeChart]

theorem plane_domain_surface (Ω : Set ℂ) (hΩ : IsDomain Ω) :
    ∃ S : RiemannSurface Ω, S.atlas = {planeChart Ω hΩ} := by
  have hc : ConnectedSpace Ω := isConnected_iff_connectedSpace.mp ⟨hΩ.1, hΩ.2.2⟩
  refine ⟨⟨hc, inferInstance, inferInstance, {planeChart Ω hΩ}, ?_⟩, rfl⟩
  refine ⟨fun x => ⟨planeChart Ω hΩ, rfl, ?_⟩, ?_⟩
  · rw [planeChart_source]
    trivial
  · rintro e (rfl : e = planeChart Ω hΩ) f (rfl : f = planeChart Ω hΩ)
    exact compatibleCharts_refl _

/-- Under the connected convention an open plane set is a surface exactly when
it is a domain. This also excludes the empty open set. -/
theorem plane_surface_iff (Ω : Set ℂ) (hΩ : IsOpen Ω) :
    Nonempty (RiemannSurface Ω) ↔ IsDomain Ω := by
  constructor
  · rintro ⟨S⟩
    have hc := isConnected_iff_connectedSpace.mpr S.connected
    exact ⟨hc.nonempty, hΩ, hc.isPreconnected⟩
  · intro h
    obtain ⟨S, _⟩ := plane_domain_surface Ω h
    exact ⟨S⟩

/-- The components of an arbitrary plane open set are domain surfaces. -/
theorem open_components_surfaces (Ω : Set ℂ) (hΩ : IsOpen Ω) :
    (Ω = ⋃ z ∈ Ω, connectedComponentIn Ω z) ∧
    ∀ z ∈ Ω, IsDomain (connectedComponentIn Ω z) ∧
      Nonempty (RiemannSurface (connectedComponentIn Ω z)) := by
  constructor
  · apply Set.Subset.antisymm
    · intro z hz
      exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, mem_connectedComponentIn hz⟩⟩
    · intro z hz
      obtain ⟨x, hx⟩ := mem_iUnion.mp hz
      obtain ⟨_, hz⟩ := mem_iUnion.mp hx
      exact connectedComponentIn_subset Ω x hz
  · intro z hz
    have hc : IsDomain (connectedComponentIn Ω z) :=
      ⟨⟨z, mem_connectedComponentIn hz⟩, hΩ.connectedComponentIn,
        isPreconnected_connectedComponentIn⟩
    exact ⟨hc, (plane_surface_iff _ hΩ.connectedComponentIn).mpr hc⟩

end D12Complex.Surfaces

/- Definition exports preserve the independent canonical objects verbatim. -/
namespace D12Complex.Surfaces.Definitions

abbrev ComplexChart : Specs.D12Complex.Ch20.Surfaces.ComplexChart_type :=
  D12Complex.Surfaces.ComplexChart
abbrev CompatibleCharts : Specs.D12Complex.Ch20.Surfaces.CompatibleCharts_type :=
  @D12Complex.Surfaces.CompatibleCharts
abbrev IsAtlas : Specs.D12Complex.Ch20.Surfaces.IsAtlas_type :=
  @D12Complex.Surfaces.IsAtlas
abbrev CompatibleAtlases : Specs.D12Complex.Ch20.Surfaces.CompatibleAtlases_type :=
  @D12Complex.Surfaces.CompatibleAtlases
abbrev maximalAtlas : Specs.D12Complex.Ch20.Surfaces.maximalAtlas_type :=
  @D12Complex.Surfaces.maximalAtlas
abbrev IsMaximalAtlas : Specs.D12Complex.Ch20.Surfaces.IsMaximalAtlas_type :=
  @D12Complex.Surfaces.IsMaximalAtlas
abbrev RiemannSurface : Specs.D12Complex.Ch20.Surfaces.RiemannSurface_type :=
  D12Complex.Surfaces.RiemannSurface
abbrev planeChart : Specs.D12Complex.Ch20.Surfaces.planeChart_type :=
  D12Complex.Surfaces.planeChart

end D12Complex.Surfaces.Definitions
