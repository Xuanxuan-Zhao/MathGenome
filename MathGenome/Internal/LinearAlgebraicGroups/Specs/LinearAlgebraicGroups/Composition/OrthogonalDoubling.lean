import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.Adjoints
import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

namespace LinearAlgebraicGroups.Composition

universe u v

/-- A linear subspace containing the unit and closed under the ambient, possibly
nonassociative, product. -/
structure UnitalSubalgebra (k : Type u) (C : Type v)
    [Field k] [NonAssocRing C] [Module k C] extends Submodule k C where
  one_mem' : (1 : C) ∈ toSubmodule
  mul_mem' : ∀ {x y : C}, x ∈ toSubmodule → y ∈ toSubmodule → x * y ∈ toSubmodule

namespace UnitalSubalgebra

variable {k : Type u} {C : Type v} [Field k] [NonAssocRing C] [Module k C]

instance : SetLike (UnitalSubalgebra k C) C where
  coe D := D.toSubmodule
  coe_injective := by
    intro D E h
    have hsub : D.toSubmodule = E.toSubmodule := SetLike.coe_injective h
    cases D
    cases E
    cases hsub
    rfl

instance : SubringClass (UnitalSubalgebra k C) C where
  zero_mem D := D.toSubmodule.zero_mem
  add_mem {D} := D.toSubmodule.add_mem
  neg_mem {D} := D.toSubmodule.neg_mem
  one_mem D := D.one_mem'
  mul_mem {D} := D.mul_mem'

instance : SMulMemClass (UnitalSubalgebra k C) k C where
  smul_mem {D} r _ hx := D.toSubmodule.smul_mem r hx

instance (D : UnitalSubalgebra k C) [IsScalarTower k C C] : IsScalarTower k D D where
  smul_assoc r x y := Subtype.ext (smul_assoc r (x : C) (y : C))

instance (D : UnitalSubalgebra k C) [SMulCommClass k C C] : SMulCommClass k D D where
  smul_comm r x y := Subtype.ext (smul_comm r (x : C) (y : C))

/-- The ambient quadratic form restricted to the subalgebra. -/
def restrictNorm (D : UnitalSubalgebra k C) (n : QuadraticForm k C) :
    QuadraticForm k D :=
  n.comp (SMulMemClass.subtype D)

/-- The subspace of right multiples of `a` by elements of `D`. -/
def rightMultiple [IsScalarTower k C C] [SMulCommClass k C C]
    (D : UnitalSubalgebra k C) (a : C) : Submodule k C :=
  D.toSubmodule.map ((LinearMap.mul k C).flip a)

end UnitalSubalgebra

namespace DoublingSpecification

open Specification AdjointSpecification

/-- Internal Cayley–Dickson doubling for a regular composition subalgebra. -/
def internalDoubling : Prop :=
  ∀ {k : Type u} {C : Type v} [Field k] [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {n : QuadraticForm k C}
    {D : UnitalSubalgebra k C} {a : C},
    FieldNormConditions n → FieldNormConditions (D.restrictNorm n) →
    a ∈ D.toSubmodule.orthogonalBilin n.polarBilin → n a ≠ 0 →
    let lam := -n a
    a * a = lam • (1 : C) ∧
    D.rightMultiple a ≤ D.toSubmodule.orthogonalBilin n.polarBilin ∧
    Disjoint D.toSubmodule (D.rightMultiple a) ∧
    Function.Injective (fun y : D => (y : C) * a) ∧
    (∃ E : UnitalSubalgebra k C, E.toSubmodule = D.toSubmodule ⊔ D.rightMultiple a ∧
      FieldNormConditions (E.restrictNorm n)) ∧
    (∀ x y u v : D,
      ((x : C) + (y : C) * a) * ((u : C) + (v : C) * a) =
        ((x : C) * (u : C) + lam • (conjugate n (v : C) * (y : C))) +
        ((v : C) * (x : C) + (y : C) * conjugate n (u : C)) * a) ∧
    (∀ x y : D, n ((x : C) + (y : C) * a) = n (x : C) - lam * n (y : C)) ∧
    (∀ x y : D, conjugate n ((x : C) + (y : C) * a) =
      conjugate n (x : C) - (y : C) * a)

end DoublingSpecification

end LinearAlgebraicGroups.Composition
