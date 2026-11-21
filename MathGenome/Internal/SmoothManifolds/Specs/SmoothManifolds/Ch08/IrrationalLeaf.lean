import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.IrrationalLine
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.GlobalLeaves
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-! The irrational-slope example following M08.03 (paper.tex:1665).
The curve, range, torus, and real atlas are the Chapter 3 objects.
The geometric target includes an actual smooth distribution and the actual
plaque-chain leaf, rather than just an independently transported range.
-/
set_option autoImplicit false
noncomputable section
namespace Specs.SmoothManifolds.Ch08.IrrationalLeaf
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.SphereTorusData _root_.SmoothManifolds.IrrationalLineData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.DistributionData _root_.SmoothManifolds.LeafData
  _root_.SmoothManifolds.GlobalLeafData Set Filter
open scoped Topology

/-- Integer rotations supply density in the second quotient coordinate. -/
def circle_densityType : Prop :=
  ∀ α : ℝ, Irrational α → DenseRange (fun j : ℤ => j • (α : AddCircle (1 : ℝ)))

/-- Density in the actual quotient torus, with its original topology. -/
def densityType : Prop :=
  ∀ α : ℝ, Irrational α → Dense (lineRange α)

/-- Positive integer parameters escaping to infinity while their images return
to the origin. This also gives the explicit topology-separating sequence. -/
def recurrenceType : Prop :=
  ∀ α : ℝ, ∃ q : ℕ → ℕ, (∀ j, 0 < q j) ∧ Tendsto q atTop atTop ∧
    Tendsto (fun j => irrationalLine α (q j : ℝ)) atTop (𝓝 (0 : FlatTorus 2))

/-- Reuse of the Chapter 3 immersion, with the same standard structures. -/
def injective_immersionType : Prop :=
  ∀ α : ℝ, Irrational α →
  ∀ (S : SmoothManifold 1 .euclidean ℝ)
    (Q : SmoothManifold 2 .euclidean (FlatTorus 2)),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) realAtlas →
    Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2) →
    Function.Injective (irrationalLine α) ∧
    IsSmoothMap S Q (irrationalLine α) ∧ IsImmersion S Q (irrationalLine α)

/-- This alone does not identify the transported topology with a leaf topology. -/
def transported_topologyType : Prop :=
  ∀ α : ℝ, Irrational α →
    immersedTopology α < (inferInstance : TopologicalSpace (lineRange α))

/-- Transfers separation from the original curve to a genuine intrinsic
parametrization, with the ambient topology written explicitly. -/
def topology_from_parametrizationType : Prop :=
  ∀ (α : ℝ) (s : Set (FlatTorus 2)) (t : TopologicalSpace s)
    (h : @Homeomorph ℝ s inferInstance t),
    (∀ x, (h x).val = irrationalLine α x) →
      t < TopologicalSpace.induced (Subtype.val : s → FlatTorus 2) inferInstance

/-- Complete target. The span condition is imposed in every small-box quotient
chart, and therefore specifies the descended constant distribution (1,α).
The diffeomorphism and strict topology comparison concern exactly leafTopology.
No construction, involutivity, leaf identification, or topology equality is
assumed as input. -/
def irrational_leafType : Prop :=
  ∀ α : ℝ, Irrational α →
  ∀ (S : SmoothManifold 1 .euclidean ℝ)
    (Q : SmoothManifold 2 .euclidean (FlatTorus 2)),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) realAtlas →
    Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2) →
    Function.Injective (irrationalLine α) ∧
    IsSmoothMap S Q (irrationalLine α) ∧ IsImmersion S Q (irrationalLine α) ∧
    Dense (lineRange α) ∧
    ∃ (C : CotangentBundle Q) (D : SmoothDistribution C 1),
      (∀ (a : Euclidean 2) (ε : ℝ) (e : ModelChart 2 .euclidean (FlatTorus 2))
        (he : e ∈ Q.smoothStructure.val), IsAngleChart a ε e →
        ∀ (p : FlatTorus 2) (hp : p ∈ e.source) (v : TangentSpace Q p),
          v ∈ D.fiber p ↔ C.tangent.fiberCoordinates.equiv e he p hp v ∈
            Submodule.span ℝ {(![1, α] : Euclidean 2)}) ∧
      IsInvolutive D ∧
      ∃ A : Set (ModelChart 2 .euclidean (FlatTorus 2)),
        IsCountableAdaptedAtlas D A ∧
        leafSet A 1 (0 : FlatTorus 2) = lineRange α ∧
        ∃ T : @SmoothManifold 1 .euclidean (leafSet A 1 (0 : FlatTorus 2))
            (leafTopology A 1 (0 : FlatTorus 2)),
          @ConnectedSpace _ (leafTopology A 1 (0 : FlatTorus 2)) ∧
          HasPlaqueCharts A 0 T ∧ IsIntegralLeaf D A 0 T ∧ UniversalIntegralLeaf D A 0 T ∧
          (letI := leafTopology A 1 (0 : FlatTorus 2)
           ∃ h : Diffeomorph S.smoothStructure.val T.smoothStructure.val,
             (∀ t : ℝ, (h.toEquiv t).val = irrationalLine α t)) ∧
          leafTopology A 1 (0 : FlatTorus 2) <
            (inferInstance : TopologicalSpace (leafSet A 1 (0 : FlatTorus 2)))

end Specs.SmoothManifolds.Ch08.IrrationalLeaf
