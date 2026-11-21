import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.DistributionTests

/-! Independent statements of M08.02, paper.tex 1637--1648.
An adapted chart belongs to the given maximal smooth atlas. Its fiber equation
uses the actual intrinsic tangent coordinates. The transverse coordinates have
exactly n-k components. Integral slices carry the ambient subspace topology.
Neither commuting frames nor integral manifolds are input certificates.
-/
set_option autoImplicit false
noncomputable section

namespace SmoothManifolds.FrobeniusData
open ModelData AtlasData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData DistributionData Set
universe u

/-- The span of the first k standard coordinate vectors, including k=0 and k=n. -/
def CoordinatePlane {n : ℕ} (k : ℕ) : Submodule ℝ (Euclidean n) where
  carrier := {v | ∀ j : Fin n, k ≤ j.val → v j = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy j hj; simp [hx j hj, hy j hj]
  smul_mem' := by intro r x hx j hj; simp [hx j hj]

/-- Precisely the last n-k chart coordinates. -/
def transverseCoordinates {n : ℕ} (k : ℕ) (x : Euclidean n) : Euclidean (n-k) :=
  fun j => x ⟨k+j.val, by omega⟩

/-- The complete slice of a chart with the specified transverse value. -/
def coordinateSlice {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n .euclidean M) (k : ℕ) (z : Euclidean (n-k)) : Set M :=
  {q | q ∈ e.source ∧ transverseCoordinates k (e q).val = z}

/-- Equality with the longitudinal coordinate span at every point of the chart. -/
def IsAdaptedChart {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) : Prop :=
  ∀ (q : M) (hq : q ∈ e.source) (v : TangentSpace S q),
    v ∈ D.fiber q ↔ C.tangent.fiberCoordinates.equiv e he q hq v ∈ CoordinatePlane k

/-- Local coordinates are required at every point, with no global frame assumption. -/
def HasAdaptedCoordinates {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) : Prop :=
  ∀ p : M, ∃ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val),
    p ∈ e.source ∧ IsAdaptedChart D e he

/-- A k-dimensional integral submanifold with the actual subspace topology.
Thus the slice inclusion is an embedded integral submanifold, not just an
immersion with some unrelated topology on its domain. -/
def IsIntegralSlice {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (A : Set M) : Prop :=
  ∃ T : SmoothManifold k .euclidean A,
    MapData.IsSmoothMap T S Subtype.val ∧
    MapClassData.IsImmersion T S Subtype.val ∧
    ∃ L : (p : A) → TangentSpace T p →ₗ[ℝ] TangentSpace S p.val,
      (∀ p, IsDifferential T S Subtype.val p (L p)) ∧
      ∀ p, LinearMap.range (L p) = D.fiber p.val

end SmoothManifolds.FrobeniusData

namespace Specs.SmoothManifolds.Ch08.Frobenius
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.DistributionData _root_.SmoothManifolds.FrobeniusData
universe u

/-- Full local Frobenius equivalence, including the two extreme ranks. -/
def adapted_coordinatesType : Prop :=
  ∀ {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k), IsInvolutive D ↔ HasAdaptedCoordinates D

/-- Every slice of any adapted chart is an integral submanifold.
An empty slice is allowed. No connectedness or product-shaped chart image
is needed for this local embedded-submanifold assertion. -/
def integral_slicesType : Prop :=
  ∀ {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val), IsAdaptedChart D e he →
    ∀ z : Euclidean (n-k), IsIntegralSlice D (coordinateSlice e k z)

end Specs.SmoothManifolds.Ch08.Frobenius
