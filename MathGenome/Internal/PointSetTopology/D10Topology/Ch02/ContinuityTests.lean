import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.ContinuityTests
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.ClosureCalculus

/-!
Continuity and the equivalent tests in paper.tex, d10:02:maps,
d10:02:continuity-tests, and d10:02:restriction. We use the canonical
Continuous, ContinuousAt, IsOpenMap and IsClosedMap predicates and prove
their defining descriptions before applying the library APIs.
-/

open Set
universe u v w

namespace D10Topology.Ch02
open D10Topology.Ch01

variable {X : Type u} {Y : Type v} {Z : Type w}
  [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [TopologicalSpace Z]

theorem continuous_iff_open_preimages (f : X → Y) :
    Continuous f ↔ ∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' V) := continuous_def

theorem continuousAt_iff_neighborhood_preimages (f : X → Y) (x : X) :
    ContinuousAt f x ↔ ∀ N : Set Y, Neighborhood tY (f x) N →
      Neighborhood tX x (f ⁻¹' N) := by
  simp only [neighborhood_iff_mem_nhds]
  exact continuousAt_def

theorem openMap_iff_open_images (f : X → Y) :
    IsOpenMap f ↔ ∀ U : Set X, IsOpen U → IsOpen (f '' U) := Iff.rfl

theorem closedMap_iff_closed_images (f : X → Y) :
    IsClosedMap f ↔ ∀ F : Set X, IsClosed F → IsClosed (f '' F) := Iff.rfl

theorem continuous_iff_pointwise (f : X → Y) :
    Continuous f ↔ ∀ x : X, ContinuousAt f x := continuous_iff_continuousAt

theorem continuous_iff_neighborhood_preimages (f : X → Y) :
    Continuous f ↔ ∀ x : X, ∀ N : Set Y, Neighborhood tY (f x) N →
      Neighborhood tX x (f ⁻¹' N) := by
  simp only [← continuousAt_iff_neighborhood_preimages]
  exact continuous_iff_pointwise f

theorem continuous_iff_closed_preimages (f : X → Y) :
    Continuous f ↔ ∀ F : Set Y, IsClosed F → IsClosed (f ⁻¹' F) :=
  continuous_iff_isClosed

theorem continuous_iff_closure_images (f : X → Y) :
    Continuous f ↔ ∀ A : Set X, f '' closure A ⊆ closure (f '' A) :=
  continuous_iff_image_closure_subset_closure_image

theorem continuous_iff_subbasis (f : X → Y) (S : Set (Set Y))
    (hS : tY = TopologicalSpace.generateFrom S) :
    Continuous f ↔ ∀ V ∈ S, IsOpen (f ⁻¹' V) := by
  rw [hS, continuous_generateFrom_iff]

theorem continuous_iff_basis (f : X → Y) (B : Set (Set Y)) (hB : BasisFor tY B) :
    Continuous f ↔ ∀ V ∈ B, IsOpen (f ⁻¹' V) :=
  ((basis_iff_mathlib tY B).mp hB).continuous_iff

theorem identity_continuous : Continuous (id : X → X) := continuous_id

theorem constant_continuous (y : Y) : Continuous (fun _ : X => y) := continuous_const

theorem compose_continuous (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := hg.comp hf

theorem restriction_continuous (f : X → Y) (A : Set X) (hf : Continuous f) :
    Continuous (fun a : A => f a.val) := hf.comp continuous_subtype_val

theorem corestriction_continuous_iff (f : X → Y) (B : Set Y) (h : range f ⊆ B) :
    Continuous (fun x => (⟨f x, h ⟨x, rfl⟩⟩ : B)) ↔ Continuous f :=
  continuous_codRestrict_iff (fun x => h ⟨x, rfl⟩)

theorem subspace_topology_trans (A B : Set X) (hAB : A ⊆ B) :
    TopologicalSpace.induced (fun a : A => (⟨a.val, hAB a.property⟩ : B))
      (inferInstance : TopologicalSpace B) = (inferInstance : TopologicalSpace A) := by
  change TopologicalSpace.induced _ (TopologicalSpace.induced Subtype.val tX) = _
  rw [induced_compose]
  rfl

end D10Topology.Ch02
