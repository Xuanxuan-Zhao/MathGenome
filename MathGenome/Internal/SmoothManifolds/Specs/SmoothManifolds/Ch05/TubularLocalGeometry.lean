import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleOperations

/-! Local geometric part of M05.08 (paper.tex:1338–1343).
The fibers and the smooth structure below are exactly those of the supplied
normal quotient bundle. No complement or retraction is an input hypothesis. -/
set_option autoImplicit false

namespace Specs.SmoothManifolds.Ch05.TubularLocalGeometry
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.QuotientData Bundle Set
universe u

/-- Local tubular-map data for a prescribed bundle, written generically so
that the coordinate tests do not elaborate the tangent quotient repeatedly. -/
def LocalTubularMap
    {m n r : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    {T : SmoothManifold m .euclidean P} (S : SmoothManifold n .euclidean M)
    (i : P → M) {ι : Type u} {V : P → Type u}
    [∀ p, AddCommGroup (V p)] [∀ p, Module ℝ (V p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) V)]
    (B : _root_.SmoothManifolds.BundleData.SmoothVectorBundle T r ι V) : Prop :=
  ∃ (O : Set (Bundle.TotalSpace (Euclidean r) V))
    (F : Bundle.TotalSpace (Euclidean r) V → M),
    IsOpen O ∧ (∀ p, (⟨p, 0⟩ : Bundle.TotalSpace (Euclidean r) V) ∈ O) ∧
    (∀ p, F ⟨p, 0⟩ = i p) ∧
    ManifoldSmoothOn B.totalManifold.smoothStructure.val S.smoothStructure.val F O ∧
    ∀ x ∈ O, ∃ e : OpenPartialHomeomorph (Bundle.TotalSpace (Euclidean r) V) M,
      x ∈ e.source ∧ e.source ⊆ O ∧ EqOn e F e.source ∧
      ManifoldSmoothOn S.smoothStructure.val B.totalManifold.smoothStructure.val
        e.symm e.target

/-- A smooth local tubular map near the entire zero section, before any global
injective or radial shrinking. The total map may have arbitrary values outside
its open domain. Every point of the domain has a smooth local inverse.
Here the bundle supplied to `LocalTubularMap` has exactly the quotient fibers
`TangentSpace S (i p) / range (N.differential p)` and its prescribed topology. -/
def tubular_local_geometryType : Prop :=
  ∀ {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    (T : SmoothManifold m .euclidean P) (S : SmoothManifold n .euclidean M)
    (i : P → M), IsSmoothEmbedding T S i →
    ∀ N : NormalBundle T S i,
    letI := N.ambientRealization.space.topology
    letI := N.pullback.space.topology
    letI := N.quotient.topology
    LocalTubularMap S i N.quotient.bundle

end Specs.SmoothManifolds.Ch05.TubularLocalGeometry
