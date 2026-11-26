import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs
open Coalgebra HopfAlgebra
open scoped TensorProduct

namespace LinearAlgebraicGroups.Descent

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Restriction of scalars for the Hopf algebra underlying a descent datum. -/
scoped instance (priority := 50) hopfRestrictScalars (A : HopfAlgebraCategory K) : Algebra k A :=
  ((algebraMap K A).comp (algebraMap k K)).toAlgebra

scoped instance (priority := 50) hopfScalarTower (A : HopfAlgebraCategory K) : IsScalarTower k K A :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A Galois action on a commutative Hopf algebra that respects all five structure maps. -/
structure HopfDescentDatum (k : Type u) {K : Type u} [Field k] [Field K] [Algebra k K]
    (A : HopfAlgebraCategory K) where
  action : SemilinearAction k K A
  map_one : ∀ g, action.act g 1 = 1
  map_mul : ∀ g x y, action.act g (x * y) = action.act g x * action.act g y
  comul_equivariant : action.Equivariant (action.tensor action) (comul (R := K) (A := A))
  counit_equivariant : action.Equivariant SemilinearAction.unit (counit (R := K) (A := A))
  antipode_equivariant : action.Equivariant action (antipode K (A := A))

namespace HopfDescentDatum

variable {A B : HopfAlgebraCategory K} (D : HopfDescentDatum k A)

/-- The elements fixed by the entire action, with their inherited algebra structure. -/
def fixed : Subalgebra k A where
  carrier := { x | ∀ g, D.action.act g x = x }
  zero_mem' g := map_zero _
  one_mem' := D.map_one
  add_mem' hx hy g := by rw [map_add, hx g, hy g]
  mul_mem' hx hy g := by rw [D.map_mul, hx g, hy g]
  algebraMap_mem' r g := by
    rw [IsScalarTower.algebraMap_apply k K A, Algebra.algebraMap_eq_smul_one, D.action.map_smul,
      AlgEquiv.commutes, D.map_one]

/-- A morphism that respects the descent data. -/
def Equivariant (E : HopfDescentDatum k B) (f : A ⟶ B) : Prop :=
  D.action.Equivariant E.action f.hom.toLinearMap

/-- A stable ideal is preserved by every action operator. -/
def Stable (J : Ideal A) : Prop :=
  ∀ g x, x ∈ J → D.action.act g x ∈ J

/-- The pullback of an ideal to the algebra of fixed elements. -/
def contract (J : Ideal A) : Ideal D.fixed :=
  J.comap D.fixed.val

end HopfDescentDatum

/-- Hopf operations on an algebra with a specified underlying scalar structure. -/
structure HopfOperations (k R : Type u) [Field k] [CommRing R] [Algebra k R] where
  coalgebra : Coalgebra k R
  counit_one : coalgebra.counit 1 = 1
  counit_mul : ∀ x y, coalgebra.counit (x * y) = coalgebra.counit x * coalgebra.counit y
  comul_one : coalgebra.comul 1 = 1
  comul_mul : ∀ x y, coalgebra.comul (x * y) = coalgebra.comul x * coalgebra.comul y
  antipode : R →ₗ[k] R
  right_inverse : ∀ x, LinearMap.mul' k R (antipode.rTensor R (coalgebra.comul x)) =
    algebraMap k R (coalgebra.counit x)
  left_inverse : ∀ x, LinearMap.mul' k R (antipode.lTensor R (coalgebra.comul x)) =
    algebraMap k R (coalgebra.counit x)

abbrev HopfOperations.toHopfAlgebra {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    (O : HopfOperations k R) : HopfAlgebra k R :=
  letI := O.coalgebra
  { Bialgebra.mk' k R O.counit_one (O.counit_mul _ _) O.comul_one (O.comul_mul _ _) with
    antipode := O.antipode
    mul_antipode_rTensor_comul := LinearMap.ext O.right_inverse
    mul_antipode_lTensor_comul := LinearMap.ext O.left_inverse }

/-- Scalar extension preserves the comparison of each fixed element with its original value. -/
structure HopfDescent {A : HopfAlgebraCategory K} (D : HopfDescentDatum k A) where
  operations : HopfOperations k D.fixed
  comparison : letI := operations.toHopfAlgebra; (K ⊗[k] D.fixed) ≃ₐc[K] A
  comparison_tmul : ∀ (r : K) (x : D.fixed), comparison (r ⊗ₜ[k] x) = r • (x : A)

namespace HopfDescent

variable {A B : HopfAlgebraCategory K} {D : HopfDescentDatum k A} {E : HopfDescentDatum k B}

/-- The descended coordinate Hopf algebra. -/
abbrev algebra (H : HopfDescent D) : HopfAlgebraCategory k :=
  letI := H.operations.toHopfAlgebra
  CommHopfAlgCat.of k D.fixed

/-- The Hopf algebra comparison as an isomorphism in the affine duality. -/
noncomputable abbrev iso (H : HopfDescent D) : extendedHopf K H.algebra ≅ A :=
  CommHopfAlgCat.isoMk H.comparison

/-- Hopf ideals of the fixed algebra use the operations carried by the descent. -/
abbrev IsHopfIdeal (H : HopfDescent D) (I : Ideal H.algebra) : Prop :=
  letI := H.operations.toHopfAlgebra
  I.IsHopfIdeal k

noncomputable abbrev quotient (H : HopfDescent D) (I : Ideal H.algebra) [H.IsHopfIdeal I] :
    HopfAlgebraCategory k :=
  letI := H.operations.toHopfAlgebra
  hopfQuotient H.algebra I

noncomputable abbrev quotientMap (H : HopfDescent D) (I : Ideal H.algebra) [H.IsHopfIdeal I] :
    H.algebra ⟶ H.quotient I :=
  letI := H.operations.toHopfAlgebra
  hopfQuotientMap H.algebra I

end HopfDescent

namespace AffineGroupSpecs

def Effective : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {A : HopfAlgebraCategory K} (D : HopfDescentDatum k A),
    ∃ H : HopfDescent D,
      (SemilinearAction.scalarExtension (K := K) D.fixed).Equivariant D.action
        H.iso.hom.hom.toLinearMap

/-- Each descended coalgebra operation and the antipode agree with the original
operation under the canonical comparisons for fixed vectors. -/
def StructureMaps : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {A : HopfAlgebraCategory K} {D : HopfDescentDatum k A} (H : HopfDescent D)
    (x : D.fixed),
    (↑(D.action.tensorComparison D.action (H.operations.coalgebra.comul x)) : A ⊗[K] A) =
      comul (R := K) (x : A) ∧
    algebraMap k K (H.operations.coalgebra.counit x) = counit (R := K) (x : A) ∧
    (H.operations.antipode x : A) = antipode K (x : A)

def Morphisms : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {A B : HopfAlgebraCategory K} {D : HopfDescentDatum k A} {E : HopfDescentDatum k B}
    (H : HopfDescent D) (L : HopfDescent E),
    (∀ (f : A ⟶ B), D.Equivariant E f →
      ∃! g : H.algebra ⟶ L.algebra,
        H.iso.hom ≫ f = extendedHopfMap K g ≫ L.iso.hom) ∧
    (∀ (g : H.algebra ⟶ L.algebra),
      D.Equivariant E (H.iso.inv ≫ extendedHopfMap K g ≫ L.iso.hom))

def Properties : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {A : HopfAlgebraCategory K} {D : HopfDescentDatum k A} (H : HopfDescent D),
    (Algebra.FiniteType K A → Algebra.FiniteType k H.algebra) ∧
    (Algebra.Smooth K A → Algebra.Smooth k H.algebra)

/-- The affine spectra recover the group schemes and reverse each descended map. -/
def Groups : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K],
    ∃ compare : ∀ {A : HopfAlgebraCategory K} {D : HopfDescentDatum k A} (H : HopfDescent D),
      specGroup A ≅ (groupBaseChange k K).obj (specGroup H.algebra),
    ∀ {A B : HopfAlgebraCategory K} {D : HopfDescentDatum k A} {E : HopfDescentDatum k B}
      (H : HopfDescent D) (L : HopfDescent E) (f : A ⟶ B) (g : H.algebra ⟶ L.algebra),
      H.iso.hom ≫ f = extendedHopfMap K g ≫ L.iso.hom →
      specGroupMap f ≫ (compare H).hom =
        (compare L).hom ≫ (groupBaseChange k K).map (specGroupMap g)

/-- Finite type and smoothness for the structure morphisms of the affine groups. -/
def GroupProperties : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {A : HopfAlgebraCategory K} {D : HopfDescentDatum k A} (H : HopfDescent D),
    (LocallyOfFiniteType (specGroup A).X.hom →
      LocallyOfFiniteType (specGroup H.algebra).X.hom ∧ QuasiCompact (specGroup H.algebra).X.hom) ∧
    (AlgebraicGeometry.Smooth (specGroup A).X.hom →
      AlgebraicGeometry.Smooth (specGroup H.algebra).X.hom)

def Ideals : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {A : HopfAlgebraCategory K} {D : HopfDescentDatum k A} (H : HopfDescent D),
    ∃ e : {J : Ideal A // J.IsHopfIdeal K ∧ D.Stable J} ≃o
        {I : Ideal H.algebra // H.IsHopfIdeal I},
      (∀ J, (e J).1 = D.contract J.1) ∧
      (∀ I, (e.symm I).1 = (extendedIdeal K I.1).map H.iso.hom.hom.toAlgHom) ∧
      ∀ J, let I := e J
           letI : J.1.IsHopfIdeal K := J.2.1
           letI : H.IsHopfIdeal I.1 := I.2
           ∃ q : extendedHopf K (H.quotient I.1) ≅ hopfQuotient A J.1,
             extendedHopfMap K (H.quotientMap I.1) ≫ q.hom =
               H.iso.hom ≫ hopfQuotientMap A J.1

/-- A closed subgroup inclusion into the descended group is defined by a unique
stable Hopf ideal of the original coordinate algebra. -/
def Subgroups : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {A : HopfAlgebraCategory K} {D : HopfDescentDatum k A} (H : HopfDescent D)
    (S : GroupScheme k) (i : S ⟶ specGroup H.algebra),
    IsClosedImmersion i.hom.hom.left ↔
      ∃! J : {J : Ideal A // J.IsHopfIdeal K ∧ D.Stable J},
        ∃ (_ : H.IsHopfIdeal (D.contract J.1)),
          ∃ e : S ≅ specGroup (H.quotient (D.contract J.1)),
            e.hom ≫ specGroupMap (H.quotientMap (D.contract J.1)) = i

end AffineGroupSpecs
end LinearAlgebraicGroups.Descent
