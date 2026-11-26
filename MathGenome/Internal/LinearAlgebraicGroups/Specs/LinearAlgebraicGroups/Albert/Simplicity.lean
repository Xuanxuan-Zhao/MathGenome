import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitModel
import Mathlib.RingTheory.Ideal.Operations

/-! Ideals and simplicity of Albert algebras (NA13-C04.05). -/

namespace LinearAlgebraicGroups.Albert.SimplicitySpecification

open SplitSpecification
open _root_.Specs.LinearAlgebraicGroups.Albert

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The outer inputs of the triple product polarize the quadratic input of U. -/
def groundTriple (J : ParaQuadratic R M) (x y z : M) : M :=
  J.groundOp (x + z) y - J.groundOp x y - J.groundOp z y

/-- Closure under U_J I and under the triple product with its last input in I. -/
def IsOuterIdeal (J : ParaQuadratic R M) (I : Submodule R M) : Prop :=
  (∀ x y, y ∈ I → J.groundOp x y ∈ I) ∧
    ∀ x y z, z ∈ I → groundTriple J x y z ∈ I

/-- A quadratic ideal also has closure under U_I J. -/
def IsQuadraticIdeal (J : ParaQuadratic R M) (I : Submodule R M) : Prop :=
  IsOuterIdeal J I ∧ ∀ x y, x ∈ I → J.groundOp x y ∈ I

/-- The ideal of scalars whose multiples of the unit lie in I. -/
def scalarIdeal (e : M) (I : Submodule R M) : Ideal R :=
  I.comap (LinearMap.toSpanSingleton R M e)

/-- The ideal correspondence over the ground ring, including closure under U_I J. -/
def AlbertOuterIdealsType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M), IsAlbert J → ∀ I : Submodule R M,
      (IsOuterIdeal J I ↔ I = scalarIdeal J.unit I • (⊤ : Submodule R M)) ∧
      (IsOuterIdeal J I → IsQuadraticIdeal J I)

/-- Every Albert algebra over a field is a nonzero simple quadratic Jordan algebra. -/
def AlbertQuadraticSimpleType : Prop :=
  ∀ {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
    (J : ParaQuadratic k M), IsAlbert J →
      J.IsJordan ∧ J.unit ≠ 0 ∧
        ∀ I : Submodule k M, IsQuadraticIdeal J I → I = ⊥ ∨ I = ⊤

/-- The associated bilinear Jordan product is simple when two is invertible. -/
def AlbertLinearSimpleType : Prop :=
  ∀ {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
    (J : QuadraticJordan k M), IsAlbert (ParaQuadratic.ofJordan J) →
      ∀ (d : kˣ), (d : k) = 2 →
        J.unit ≠ 0 ∧
          ∀ I : Submodule k M, (∀ x y, y ∈ I → J.groundProduct d x y ∈ I) →
            I = ⊥ ∨ I = ⊤

end LinearAlgebraicGroups.Albert.SimplicitySpecification
