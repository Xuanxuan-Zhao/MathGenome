import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

namespace LinearAlgebraicGroups.Specs.ExceptionalResidueCentralizerAction

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open AdjointRepresentation (GroupPoints)
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel
open ExceptionalIwahoriCongruence (integralRing integralRingMap changeRingHom)

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- The same ring, with its scalar embedding precomposed with the inverse automorphism. -/
abbrev twist (galois : K ≃+* K) (R : TestAlgebra K) : TestAlgebra K :=
  letI : Algebra K R := ((algebraMap K R).comp galois.symm.toRingHom).toAlgebra
  CommAlgCat.of K R

/-- The original ring homomorphism between the two twisted test algebras. -/
def twistHom (galois : K ≃+* K) {R S : TestAlgebra K} (f : R ⟶ S) :
    twist galois R ⟶ twist galois S :=
  (CommAlgCat.homEquivCommRingCat (twist galois R) (twist galois S)).symm
    ⟨CommRingCat.ofHom f.hom.toRingHom, RingHom.ext fun r => f.hom.commutes (galois.symm r)⟩

abbrev baseAlgebra (K : Type u) [Field K] : TestAlgebra K := CommAlgCat.of K K

def scalarHom (R : TestAlgebra K) : baseAlgebra K ⟶ R :=
  CommAlgCat.ofHom (Algebra.ofId K R)

variable {D : BasedRootDatum.{u}} (M : IntegralMarking D)

abbrev fibreGroup (K : Type u) [Field K] : GroupScheme K := (fibre K).obj M.group

/-- The represented centralizer of the marked roots of unity and its open identity component. -/
structure MarkedCentralizer (K : Type u) [Field K] (d : ℕ) (y : D.Y) where
  mu : GroupScheme K
  unitPoints : (groupPointsFunctor K).obj mu ≅ DiagonalizableGroups.rootsOfUnityPoints K d
  image : mu ⟶ fibreGroup M K
  image_cocharacter (R : TestAlgebra K) (r : GroupPoints mu R) :
    let s : rootsOfUnity d R := unitPoints.hom.app R r
    forgetFibrePoint M.group R (r ≫ image.hom.hom) =
      torusPoint D (integralRing R) (cocharacter D y (integralRing R) s.val) ≫ M.torus.hom.hom
  centralizer : ClosedSubgroup (fibreGroup M K)
  represents : RepresentsSubgroup centralizer (fun _ g => Centralizes image g)
  component : ClosedSubgroup centralizer.group
  component_affine : IsAffine component.group.X.left
  component_open : IsOpenImmersion component.inclusion.hom.hom.left
  component_range : Set.range component.inclusion.hom.hom.left =
    connectedComponent (η[centralizer.group.X].left (IsLocalRing.closedPoint K))

variable {M} {d : ℕ} {y : D.Y} (C : MarkedCentralizer M K d y)

/-- The inclusion of the designated identity component in the marked fibre. -/
abbrev inclusion : C.component.group ⟶ fibreGroup M K :=
  C.component.inclusion ≫ C.centralizer.inclusion

/-- Extend a rational point of the ambient fibre to an integral point on the test ring. -/
def extend (R : TestAlgebra K) (b : GroupPoints (fibreGroup M K) (baseAlgebra K)) :
    IntegralPoints M.group (integralRing R) :=
  changeRingHom M.group (integralRingMap (algebraMap K R))
    (forgetFibrePoint M.group (baseAlgebra K) b)

/-- The integral automorphism acts on the points over the underlying ring. -/
abbrev deltaPoint (δ : Aut M.group) {R : IntegralAlgebra.{u}}
    (z : IntegralPoints M.group R) : IntegralPoints M.group R :=
  z ≫ δ.asIso.hom.hom.hom

/-- The fixing equation on the full marked roots-of-unity scheme. -/
def FixesMarkedImage (δ : Aut M.group) (n : GroupPoints (fibreGroup M K) (baseAlgebra K)) :
    Prop :=
  ∀ (R : TestAlgebra K) (r : GroupPoints C.mu R),
    let q := extend R n
    let z := forgetFibrePoint M.group R (r ≫ C.image.hom.hom)
    q * deltaPoint δ z * q⁻¹ = z

/-- The point equation for the twisted operator on the actual identity component. -/
def PointFormula (galois : K ≃+* K) (δ : Aut M.group)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K))
    (b : GroupPoints C.component.group (baseAlgebra K)) (R : TestAlgebra K)
    (p : GroupPoints C.component.group R) (p' : GroupPoints C.component.group (twist galois R)) :
    Prop :=
  let bu : GroupPoints (fibreGroup M K) (baseAlgebra K) := b ≫ (inclusion C).hom.hom
  let q := extend (twist galois R) (bu * n)
  let z : IntegralPoints M.group (integralRing (twist galois R)) :=
    forgetFibrePoint M.group R (p ≫ (inclusion C).hom.hom)
  forgetFibrePoint M.group (twist galois R) (p' ≫ (inclusion C).hom.hom) =
    q * deltaPoint δ z * q⁻¹

/-- All-algebra restriction, uniqueness, multiplicativity and naturality. -/
def ConnectedCentralizerAction : Prop :=
  ∀ (K : Type u) [Field K] (D : BasedRootDatum.{u}) (M : IntegralMarking D)
    (d : ℕ) (y : D.Y) (C : MarkedCentralizer M K d y)
    (galois : K ≃+* K) (δ : Aut M.group)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K))
    (b : GroupPoints C.component.group (baseAlgebra K)),
    FixesMarkedImage C δ n →
    ∃ action : ∀ R : TestAlgebra K,
        GroupPoints C.component.group R →* GroupPoints C.component.group (twist galois R),
      (∀ R p p', PointFormula C galois δ n b R p p' ↔ p' = action R p) ∧
      (∀ {R S : TestAlgebra K} (f : R ⟶ S) (p : GroupPoints C.component.group R),
        mapPoints (twistHom galois f) (action R p) = action S (mapPoints f p))

end

end LinearAlgebraicGroups.Specs.ExceptionalResidueCentralizerAction
