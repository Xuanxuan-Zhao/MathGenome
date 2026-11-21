import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.Differential
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Quotient.Defs

/-! The boundary is the intrinsic last-coordinate face. Tangent vectors remain
unrestricted derivations; signs classify only velocities with a specified side.
All coordinates below are the evaluations on actual coordinate germs. -/
namespace SmoothManifolds.BoundaryConeData
open ModelData AtlasData MapData BoundaryData TangentData
universe u

/-- The usual subtype additive group, made explicit for quotient elaboration. -/
scoped instance tangentSpaceAddCommGroup {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (p : M) :
    AddCommGroup (TangentSpace S p) := Submodule.addCommGroup _

def VelocitySign (side : CurveSide) (r : ℝ) : Prop :=
  match side with
  | .twoSided => r = 0
  | .forward => 0 ≤ r
  | .backward => r ≤ 0

/-- The natural boundary atlas interface, already constructed upstream. -/
def IsBoundaryStructure {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) : Prop :=
  IsSmoothMap B S Subtype.val ∧
  ∀ c ∈ S.smoothStructure.val,
    Nonempty {p : intrinsicBoundary S // p.val ∈ c.source} →
    ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S c b
end SmoothManifolds.BoundaryConeData

namespace Specs.SmoothManifolds.Tangent.BoundaryCones
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.BoundaryConeData
open Set
open scoped _root_.SmoothManifolds.BoundaryConeData
universe u

def VelocitySignType := CurveSide → ℝ → Prop
def VelocitySignValue : VelocitySignType := BoundaryConeData.VelocitySign

def IsBoundaryStructureType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  (S : SmoothManifold (n + 1) .halfSpace M) →
  SmoothManifold n .euclidean (intrinsicBoundary S) → Prop
def IsBoundaryStructureValue : IsBoundaryStructureType := @BoundaryConeData.IsBoundaryStructure

/-- Exact classification, for each of the three parameter directions. -/
def boundary_curve_conesType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (p : intrinsicBoundary S)
    (e : ModelChart (n + 1) .halfSpace M), e ∈ S.smoothStructure.val →
    p.val ∈ e.source → ∀ E : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n + 1),
    IsChartCoordinates S p.val e E → ∀ (side : CurveSide) (v : TangentSpace S p.val),
    (∃ c : ℝ → M, CurveRepresentsDerivation S p.val side c v) ↔
      VelocitySign side (E v (Fin.last n))

/-- The differential is injective and its image is exactly the face hyperplane
in every boundary chart. Existence of the natural boundary structure is included. -/
def boundary_tangent_identificationType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M),
    ∃ B : SmoothManifold n .euclidean (intrinsicBoundary S),
      IsBoundaryStructure S B ∧
      ∀ (p : intrinsicBoundary S) (e : ModelChart (n + 1) .halfSpace M),
        e ∈ S.smoothStructure.val → p.val ∈ e.source →
      ∀ E : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n + 1),
        IsChartCoordinates S p.val e E →
      ∃ L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val,
        IsDifferential B S Subtype.val p L ∧ Function.Injective L ∧
        ∀ v, v ∈ LinearMap.range L ↔ E v (Fin.last n) = 0

/-- Chart changes multiply the normal coordinate by a strictly positive scalar.
This applies to every tangent vector, not only to realizable forward velocities. -/
def boundary_transition_positiveType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (p : intrinsicBoundary S)
    (e d : ModelChart (n + 1) .halfSpace M),
    e ∈ S.smoothStructure.val → d ∈ S.smoothStructure.val →
    p.val ∈ e.source → p.val ∈ d.source →
    ∀ (E F : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n + 1)),
    IsChartCoordinates S p.val e E → IsChartCoordinates S p.val d F →
    ∃ r : ℝ, 0 < r ∧ ∀ v, F v (Fin.last n) = r * E v (Fin.last n)

/-- The same rescaling for the actual derivative of every local ambient
extension of a chart transition. -/
def boundary_transition_jacobianType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (p : intrinsicBoundary S)
    (e d : ModelChart (n + 1) .halfSpace M),
    e ∈ S.smoothStructure.val → d ∈ S.smoothStructure.val →
    p.val ∈ e.source → p.val ∈ d.source →
    ∀ (U : Set (Euclidean (n + 1))) (H : Euclidean (n + 1) → Euclidean (n + 1)),
    IsOpen U → (e p.val).val ∈ U → ContDiffOn ℝ (⊤ : ℕ∞) H U →
    (fun y => H (e y).val) =ᶠ[nhds p.val] (fun y => (d y).val) →
    ∃ r : ℝ, 0 < r ∧ ∀ v, (fderiv ℝ H (e p.val).val v) (Fin.last n) = r * v (Fin.last n)

/-- The quotient by the actual inclusion differential is a real line. Its
positive and negative rays are the images of strictly inward and outward vectors,
and every other boundary chart gives the same rays by positive rescaling. -/
def boundary_normal_quotientType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)),
    IsBoundaryStructure S B → ∀ (p : intrinsicBoundary S)
    (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
    IsDifferential B S Subtype.val p L →
    ∀ e ∈ S.smoothStructure.val, p.val ∈ e.source →
    ∀ E : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n + 1),
    IsChartCoordinates S p.val e E →
    ∃ Q : (TangentSpace S p.val ⧸ LinearMap.range L) ≃ₗ[ℝ] ℝ,
      (∀ v, Q (Submodule.Quotient.mk v) = E v (Fin.last n)) ∧
      Module.finrank ℝ (TangentSpace S p.val ⧸ LinearMap.range L) = 1 ∧
      (Submodule.Quotient.mk '' {v | 0 < E v (Fin.last n)} = {q | 0 < Q q}) ∧
      (Submodule.Quotient.mk '' {v | E v (Fin.last n) < 0} = {q | Q q < 0}) ∧
      ∀ d ∈ S.smoothStructure.val, p.val ∈ d.source →
      ∀ F : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n + 1),
      IsChartCoordinates S p.val d F →
      ∃ r : ℝ, 0 < r ∧ ∀ v, F v (Fin.last n) = r * Q (Submodule.Quotient.mk v)

/-- The full tangent space retains the ambient dimension even on the face. -/
def boundary_full_tangent_dimensionType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (p : intrinsicBoundary S),
    FiniteDimensional ℝ (TangentSpace S p.val) ∧
      Module.finrank ℝ (TangentSpace S p.val) = n + 1
end Specs.SmoothManifolds.Tangent.BoundaryCones
