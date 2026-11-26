import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.InnerTypeA

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct BigOperators

universe u

namespace LinearAlgebraicGroups.Arithmetic.InnerTypeAClosedDiagonal.Specification

open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.Specs.StandardGroups
open LinearAlgebraicGroups.Descent.InnerTypeA.Specification
open _root_.Specs.RM03.CSA (isCentralSimple isCentralDivision degree)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

/-- The central scalar diagonal in the scalar extension of the matrix algebra. -/
noncomputable def scalarDiagonal {F B R : Type*} [Field F] [Ring B] [Algebra F B]
    [CommRing R] [Algebra F R] {m : ℕ} (t : Fin m → R) :
    R ⊗[F] Matrix (Fin m) (Fin m) B :=
  ∑ i, t i ⊗ₜ[F] Matrix.single i i (1 : B)

/-- The first entry is the inverse product of the free entries. -/
noncomputable def determinantOneTuple {R : Type*} [CommRing R] {n : ℕ}
    (t : Fin n → Rˣ) : Fin (n + 1) → Rˣ :=
  Fin.cons (∏ i, t i)⁻¹ t

def CentralSimpleMatrix : Prop :=
  ∀ {F B : Type u} [Field F] [DivisionRing B] [Algebra F B] (m : ℕ),
    0 < m → isCentralDivision F B → isCentralSimple F (Matrix (Fin m) (Fin m) B)

/-- Reduced norm on central scalar diagonals over every commutative test algebra. -/
def DiagonalNorm : Prop :=
  ∀ {F B R : Type u} [Field F] [DivisionRing B] [Algebra F B]
    [CommRing R] [Algebra F R] (_hB : isCentralDivision F B) {m : ℕ} (_hm : 0 < m)
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (t : Fin m → R),
    normAt hA b (scalarDiagonal (F := F) (B := B) t) = (∏ i, t i) ^ degree F B

/-- For matrix size n + 1, the product-one scalar diagonal is a closed copy of
the n-fold multiplicative group in the F05 norm-one scheme. The comparison
uses the F05 coordinates of the chosen basis and is natural on test algebras. -/
def ClosedDiagonal : Prop :=
  ∀ {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    (_hB : isCentralDivision F B) (n : ℕ)
    (hA : isCentralSimple F (Matrix (Fin (n + 1)) (Fin (n + 1)) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin (n + 1)) (Fin (n + 1)) B)),
    let T := multiplicativePowerGroup F (ULift.{u} (Fin n))
    let A := Matrix (Fin (n + 1)) (Fin (n + 1)) B
    ∃ H : HopfOperations F (NormOneCoordinates hA b),
      letI := H.hopf
      let G := spectrum F (NormOneCoordinates hA b)
      ∃ (P : TestAlgebra F ⥤ GrpCat.{u})
        (p : ∀ R : TestAlgebra F, P.obj R ≃ {x : R ⊗[F] A // normAt hA b x = 1})
        (e : (groupPointsFunctor F).obj G.val ≅ P)
        (a : (groupPointsFunctor F).obj T.val ≅
          multiplicativePowerPoints F (ULift.{u} (Fin n)))
        (i : T.val ⟶ G.val),
        IsClosedImmersion i.hom.hom.left ∧
        (∀ R, (p R 1).1 = 1) ∧
        (∀ R (x y : P.obj R), (p R (x * y)).1 = (p R x).1 * (p R y).1) ∧
        (∀ {R S : TestAlgebra F} (f : R ⟶ S) (x : P.obj R),
          (p S (P.map f x)).1 = Algebra.TensorProduct.map f.hom (.id F A) (p R x).1) ∧
        (∀ (R : TestAlgebra F) (f : NormOneCoordinates hA b →ₐ[F] R)
          (x : Points G.val.X R), x.left = Spec.map (CommRingCat.ofHom f.toRingHom) →
          ∀ j, (b.baseChange R).repr (p R (e.hom.app R x)).1 j =
            f (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X j))) ∧
        (∀ (R : TestAlgebra F) (f : LaurentPowerCoordinates F (ULift.{u} (Fin n)) →ₐ[F] R)
          (x : Points T.val.X R), x.left = Spec.map (CommRingCat.ofHom f.toRingHom) →
          ∀ j, ((show ULift.{u} (Fin n) → Rˣ from a.hom.app R x) j).val =
            f (laurentVariable F (ULift.{u} (Fin n)) j)) ∧
        (∀ (R : TestAlgebra F) (x : Points T.val.X R),
          (p R (e.hom.app R (((groupPointsFunctor F).map i).app R x))).1 =
            scalarDiagonal (fun j => ↑(determinantOneTuple
              (fun q => (show ULift.{u} (Fin n) → Rˣ from a.hom.app R x) ⟨q⟩) j))) ∧
        (∀ (R : TestAlgebra F) (t : Fin (n + 1) → Rˣ),
          (∏ j, t j) = 1 ↔ ∃ v, determinantOneTuple v = t)

/-- A closed immersion of split tori of the same finite rank is an isomorphism. -/
def SameRankClosedImmersion : Prop :=
  ∀ {F ι κ : Type u} [Field F] [Fintype ι] [Fintype κ]
    {S T : GroupScheme F},
    Nonempty (S ≅ (multiplicativePowerGroup F ι).val) →
    Nonempty (T ≅ (multiplicativePowerGroup F κ).val) →
    Fintype.card ι = Fintype.card κ →
    ∀ i : S ⟶ T, IsClosedImmersion i.hom.hom.left → IsIso i

end LinearAlgebraicGroups.Arithmetic.InnerTypeAClosedDiagonal.Specification
