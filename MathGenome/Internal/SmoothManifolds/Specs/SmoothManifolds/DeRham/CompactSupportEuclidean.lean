import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.CompactSupport
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.LocalSigned

/-! Independent statements for M11.06, paper.tex:2459–2501.

A Euclidean presentation is a single GLOBAL smooth coordinate chart onto the
whole Euclidean model. Thus it supplies coordinates, not a cohomology or
primitive certificate. The separate existence statement ensures that this
representation applies to the standard Euclidean space. Any cotangent bundle,
exterior bundles, intrinsic calculus, and FULL compact-support realization may
be used. The integral is the actual Lebesgue integral of the ordered top
coefficient; this fixes the standard coordinate orientation, including n=0.

The degree-n exact submodule is zero for n=0 and the image of the compact
differential for n>0. In particular, membership means a COMPACTLY SUPPORTED
primitive, not membership in the exact submodule of the ordinary complex.
-/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section

namespace SmoothManifolds.EuclideanCompactData
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData
  CovectorData ExteriorData DeRhamData MayerVietorisData CompactSupportData
  LocalIntegrationData MeasureTheory
universe u

/-- Coordinates on the whole standard Euclidean manifold. -/
structure Presentation (n : ℕ) (M : Type u) [TopologicalSpace M] where
  manifold : SmoothManifold n .euclidean M
  chart : ModelChart n .euclidean M
  chart_mem : chart ∈ manifold.smoothStructure.val
  source_eq : chart.source = Set.univ
  target_eq : chart.target = Set.univ

/-- Integration of the genuine ambient smooth field represented by a compact
form, in the orientation of the ordered global coordinates. -/
def totalIntegral {n : ℕ} {M : Type u} [TopologicalSpace M]
    (P : Presentation n M) {C : CotangentBundle P.manifold}
    {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (D : CompactCalculus K ⊤) (ω : D.complex.Obj n) : ℝ :=
  ∫ z : Euclidean n, coordinateCoefficient C.tangent.fiberCoordinates
    P.chart P.chart_mem (D.inclusion.map n ω).val z

/-- The zero extension to negative degrees, with the same convention as M11.01. -/
def cohomologyZ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B} {U : TopologicalSpace.Opens M} (D : CompactCalculus K U) :
    ℤ → Type u
  | .ofNat k => D.Cohomology k
  | .negSucc _ => ULift.{u} (Fin 0) → ℝ

end SmoothManifolds.EuclideanCompactData

namespace Specs.SmoothManifolds.DeRham.CompactSupportEuclidean
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.DeRhamData
  _root_.SmoothManifolds.MayerVietorisData _root_.SmoothManifolds.CompactSupportData
  _root_.SmoothManifolds.EuclideanCompactData _root_.SmoothManifolds.LocalIntegrationData
universe u

/-- Applicability to the standard Euclidean model, in every dimension. -/
def presentation_existsType : Prop :=
  ∀ n : ℕ, Nonempty (Presentation n (ModelSpace n .euclidean))

/-- The full cohomology assertion for a particular Euclidean presentation. -/
def Calculation {n : ℕ} {M : Type u} [TopologicalSpace M] (P : Presentation n M)
    (C : CotangentBundle P.manifold) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (D : CompactCalculus K ⊤) : Prop :=
    (∀ k : ℕ, k ≠ n → Subsingleton (D.Cohomology k)) ∧
    (∀ j : ℕ, Subsingleton (cohomologyZ D (.negSucc j))) ∧
    (∃ e : D.Cohomology n ≃ₗ[ℝ] ℝ,
      ∀ ω : D.complex.closed n,
        e (D.complex.classOf n ω) = totalIntegral P D ω.val) ∧
    (∀ ω : D.complex.Obj n,
      ω ∈ D.complex.exact n ↔ totalIntegral P D ω = 0)

/-- The full calculation, including all negative degrees and the explicit
compact-primitive criterion in every nonnegative dimension. No I,J,B identity
or support-preservation conclusion has been added as a hypothesis. -/
def calculationType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] (P : Presentation n M)
    (C : CotangentBundle P.manifold) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (D : CompactCalculus K ⊤), Calculation P C B K D

/-- The complete n=0 specialization, including its cohomology isomorphism. -/
def zero_dimensionType : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] (P : Presentation 0 M)
    (C : CotangentBundle P.manifold) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (D : CompactCalculus K ⊤), Calculation P C B K D

/-- The degree-zero part when the Euclidean manifold has positive dimension. -/
def degree_zeroType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] (P : Presentation n M), 0 < n →
    ∀ (C : CotangentBundle P.manifold) (B : ∀ k, FormBundle C k)
      (K : Calculus C B) (D : CompactCalculus K ⊤), Subsingleton (D.Cohomology 0)

/-- The zero-dimensional endpoint explicitly identifies the integral with the
scalar value at the unique point and exactness with zero of the actual field. -/
def pointType : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] (P : Presentation 0 M)
    (C : CotangentBundle P.manifold) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (D : CompactCalculus K ⊤)
    (ω : D.complex.Obj 0) (p : M),
    (ω ∈ D.complex.exact 0 ↔ (D.inclusion.map 0 ω).val = 0) ∧
    totalIntegral P D ω = zeroCoefficient (D.inclusion.map 0 ω).val p

/-- A reusable part of the calculation, valid on every manifold. -/
def above_dimensionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B} {U : TopologicalSpace.Opens M} (D : CompactCalculus K U)
    (k : ℕ), n < k → Subsingleton (D.Cohomology k)

end Specs.SmoothManifolds.DeRham.CompactSupportEuclidean
