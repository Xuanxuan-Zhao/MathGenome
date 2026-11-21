import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.Frobenius
import Mathlib.Topology.LocallyConstant.Basic

/-! Local plaque rigidity, paper.tex 1657--1659. All subtypes below have the
original ambient subspace topology. No leaf topology or connectedness is input. -/
set_option autoImplicit false
noncomputable section
namespace Specs.SmoothManifolds.Ch08.PlaqueOverlap
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.DistributionData
  _root_.SmoothManifolds.FrobeniusData _root_.SmoothManifolds.MapData Set
universe u

/-- Transverse coordinates are locally constant on the part of a complete
slice lying in a second adapted chart, even when this part is disconnected. -/
def local_constancyType : Prop :=
  ∀ {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (e d : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val),
    IsAdaptedChart D e he → IsAdaptedChart D d hd →
    ∀ z : Euclidean (n-k),
      IsLocallyConstant (fun q : ↥(coordinateSlice e k z ∩ d.source) =>
        transverseCoordinates k (d q.val).val)

/-- Every complete-slice overlap is open in both original slice topologies. -/
def open_overlapsType : Prop :=
  ∀ {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (e d : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val),
    IsAdaptedChart D e he → IsAdaptedChart D d hd →
    ∀ z w : Euclidean (n-k),
      IsOpen ((Subtype.val : coordinateSlice e k z → M) ⁻¹' coordinateSlice d k w) ∧
      IsOpen ((Subtype.val : coordinateSlice d k w → M) ⁻¹' coordinateSlice e k z)

/-- Around an intersection point the two complete slices agree as ambient
subsets. This is local agreement, not an assertion about a whole chart. -/
def local_agreementType : Prop :=
  ∀ {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (e d : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val),
    IsAdaptedChart D e he → IsAdaptedChart D d hd →
    ∀ (z w : Euclidean (n-k)) (p : M),
      p ∈ coordinateSlice e k z → p ∈ coordinateSlice d k w →
      ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
        coordinateSlice e k z ∩ U = coordinateSlice d k w ∩ U

/-- Longitudinal coordinate changes and inverse changes have actual local
smooth Euclidean extensions on their open overlap. The inequality only indexes
the first k coordinates; at any point it already follows from D's rank. -/
def smooth_transitionsType : Prop :=
  ∀ {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (e d : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val),
    IsAdaptedChart D e he → IsAdaptedChart D d hd →
    ∀ (hk : k ≤ n) (z w : Euclidean (n-k))
      (p : ↥(coordinateSlice e k z ∩ coordinateSlice d k w)),
      LocalCoordinateExtension (⊤ : ℕ∞)
        (fun q : ↥(coordinateSlice e k z ∩ coordinateSlice d k w) =>
          fun i : Fin k => (e q.val).val (Fin.castLE hk i))
        (fun q : ↥(coordinateSlice e k z ∩ coordinateSlice d k w) =>
          fun i : Fin k => (d q.val).val (Fin.castLE hk i)) p ∧
      LocalCoordinateExtension (⊤ : ℕ∞)
        (fun q : ↥(coordinateSlice e k z ∩ coordinateSlice d k w) =>
          fun i : Fin k => (d q.val).val (Fin.castLE hk i))
        (fun q : ↥(coordinateSlice e k z ∩ coordinateSlice d k w) =>
          fun i : Fin k => (e q.val).val (Fin.castLE hk i)) p
end Specs.SmoothManifolds.Ch08.PlaqueOverlap
