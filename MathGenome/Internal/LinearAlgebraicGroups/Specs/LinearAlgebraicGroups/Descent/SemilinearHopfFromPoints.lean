import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AffineGroups

open CategoryTheory WithConv

universe u

namespace LinearAlgebraicGroups.Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The same test ring, with its scalar embedding precomposed by the inverse
coefficient automorphism. -/
def inverseTwistAlgebra (σ : Gal(K/k)) (R : TestAlgebra K) : TestAlgebra K :=
  @CommAlgCat.of K _ R R.commRing (((algebraMap K R).comp σ⁻¹.toRingHom).toAlgebra)

/-- A map of test algebras also respects the two twisted scalar embeddings. -/
def inverseTwistHom (σ : Gal(K/k)) {R S : TestAlgebra K} (f : R ⟶ S) :
    inverseTwistAlgebra σ R ⟶ inverseTwistAlgebra σ S :=
  ConcreteCategory.ofHom (C := CommAlgCat K)
    { f.hom.toRingHom with
      commutes' := fun r => f.hom.commutes (σ⁻¹ r) }

/-- Natural group homomorphisms on all test algebras with the Galois action laws
expressed on the underlying ring maps. -/
structure TwistedPointAction (k : Type u) {K : Type u} [Field k] [Field K] [Algebra k K]
    (A : HopfAlgebraCategory K) where
  operator (σ : Gal(K/k)) (R : TestAlgebra K) :
    (convolutionPoints A).obj R ⟶ (convolutionPoints A).obj (inverseTwistAlgebra σ R)
  natural (σ : Gal(K/k)) {R S : TestAlgebra K} (m : R ⟶ S) :
    (convolutionPoints A).map m ≫ operator σ S =
      operator σ R ≫ (convolutionPoints A).map (inverseTwistHom σ m)
  identity (R : TestAlgebra K) (f : (convolutionPoints A).obj R) (x : A) :
    (operator 1 R f).ofConv x = f.ofConv x
  composition (σ τ : Gal(K/k)) (R : TestAlgebra K)
      (f : (convolutionPoints A).obj R) (x : A) :
    (operator (σ * τ) R f).ofConv x =
      (operator σ (inverseTwistAlgebra τ R) (operator τ R f)).ofConv x

end LinearAlgebraicGroups.Descent

namespace LinearAlgebraicGroups.Specs

open Descent

/-- Inverse pullbacks of the point action give a semilinear action with all
the Hopf compatibilities on the given coordinate algebra. -/
def SemilinearHopfFromPoints : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (A : HopfAlgebraCategory K) (E : TwistedPointAction k A),
    ∃ D : HopfDescentDatum k A, ∀ (σ : Gal(K/k)) (R : TestAlgebra K)
      (f : (convolutionPoints A).obj R) (x : A),
      (E.operator σ R f).ofConv x = f.ofConv (D.action.act σ⁻¹ x)

end LinearAlgebraicGroups.Specs
