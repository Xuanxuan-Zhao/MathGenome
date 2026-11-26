import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.PowerMapExamples
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SmoothnessCriteria

open AlgebraicGeometry CategoryTheory Coalgebra
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.SmoothnessAndIsogenies

open CharacterDescent DiagonalizableGroups LinearAlgebraicGroups.Descent

noncomputable section

variable {k : Type u} [Field k]

/-- Smoothness in positive characteristic is detected by the geometric characters. -/
def MultiplicativeTypeSmoothness : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (p : ℕ) [Fact p.Prime] [CharP k p] (A : HopfAlgebraCategory k),
    IsMultiplicativeType A →
    (Smooth (specGroup A).X.hom ↔
      ∀ χ : GeometricCharacters K A, χ ^ p = 1 → χ = 1)

def MultiplicativeTypeSmoothnessCharZero : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : HopfAlgebraCategory k),
    IsMultiplicativeType A → Smooth (specGroup A).X.hom

def SmoothConnectedMultiplicativeType : Prop :=
  ∀ {k : Type u} [Field k] (A : HopfAlgebraCategory k),
    IsTorus A ↔ IsMultiplicativeType A ∧
      Smooth (specGroup A).X.hom ∧ ConnectedSpace (specGroup A).X.left

/-- The coordinate Hopf algebra of the group of nth roots of unity. -/
abbrev rootsOfUnityCoordinates (k : Type u) [Field k] (n : ℕ) :=
  groupAlgebra k (ULift.{u} (Multiplicative (ZMod n)))

/-- The map on exponents for the inclusion of the group of nth roots of unity. -/
def reduceExponents (n : ℕ) : IntegerCharacters.{u} →* ULift.{u} (Multiplicative (ZMod n)) :=
  MulEquiv.ulift.symm.toMonoidHom.comp
    ((Int.castAddHom (ZMod n)).toMultiplicative.comp MulEquiv.ulift.toMonoidHom)

def RootsOfUnityPowerSequence : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (_hn : 0 < n),
    let A := PowerMapExamples.torusCoordinates k
    let B := groupAlgebra k IntegerCharacters
    let C := rootsOfUnityCoordinates k n
    let f := PowerMapExamples.powerMorphism k n
    ∃ j : A ≅ B,
      j.hom.hom (LaurentPolynomial.T 1) = MonoidAlgebra.single integerGenerator 1 ∧
      let i := specGroupMap (j.hom ≫ groupAlgebraMap k (reduceExponents n))
      ∃ hi : IsClosedImmersion i.hom.hom.left,
        let N : ClosedSubgroup (specGroup A) := ⟨specGroup C, i, hi⟩
        Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
          LocallyOfFinitePresentation f.hom.hom.left ∧ IsSchemeKernel f N ∧
          ∃ e : rightQuotientSheaf N ≅ schemeFppfSheaf (specGroup A).X,
            rightQuotientProjection N ≫ e.hom = (fppfOver k).uliftYoneda.map f.hom.hom

def RootsOfUnityNonreduced : Prop :=
  ∀ (k : Type u) [Field k] (p n : ℕ) [Fact p.Prime] [CharP k p],
    0 < n → p ∣ n → ¬ AlgebraicGeometry.IsReduced (specGroup (rootsOfUnityCoordinates k n)).X.left

/-- Pullback of geometric characters by the homomorphism of group schemes. -/
def pullbackCharacter (K : Type u) [Field K] [Algebra k K]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    GeometricCharacters K A →* GeometricCharacters K B where
  toFun x := ⟨(extendedHopfMap K f).hom x.val, x.2.map (extendedHopfMap K f).hom⟩
  map_one' := GroupLike.val_injective (map_one (extendedHopfMap K f).hom)
  map_mul' x y := GroupLike.val_injective (map_mul (extendedHopfMap K f).hom x.val y.val)

/-- A torus isogeny is a surjective homomorphism with finite scheme kernel. -/
def IsTorusIsogeny {A B : HopfAlgebraCategory k} (f : A ⟶ B) : Prop :=
  let g := specGroupMap f
  Surjective g.hom.hom.left ∧
    ∃ N : ClosedSubgroup (specGroup B), IsSchemeKernel g N ∧ IsFinite N.group.X.hom

def TorusIsogenyCriterion : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B), IsTorus A → IsTorus B →
    (IsTorusIsogeny f ↔ Function.Injective (pullbackCharacter K f) ∧
      Finite (GeometricCharacters K B ⧸ (pullbackCharacter K f).range))

/-- Equivariance for the semilinear actions inducing the geometric character actions. -/
def GaloisEquivariant (K : Type u) [Field K] [Algebra k K]
    {A B : HopfAlgebraCategory k} (g : GeometricCharacters K A →* GeometricCharacters K B) : Prop :=
  ∀ (σ : Gal(K/k)) (x y : GeometricCharacters K A),
    (SemilinearAction.scalarExtension (K := K) A).act σ x.val = y.val →
    (SemilinearAction.scalarExtension (K := K) B).act σ (g x).val = (g y).val

def CharacterPullbackEquivariant : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B),
    IsMultiplicativeType A → IsMultiplicativeType B → GaloisEquivariant K (pullbackCharacter K f)

/-- Character pullback realizes the correspondence using the continuous Galois actions,
including existence and uniqueness of the isogeny for a finite-index injection. -/
def TorusIsogenyCorrespondence : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {A B : HopfAlgebraCategory k}, IsTorus A → IsTorus B →
    ∀ g : GeometricCharacters K A →* GeometricCharacters K B,
      GaloisEquivariant K g →
      Function.Injective g → Finite (GeometricCharacters K B ⧸ g.range) →
      ∃! f : A ⟶ B, IsTorusIsogeny f ∧ pullbackCharacter K f = g

/-- Restriction to the kernel is the cokernel of character pullback. The comparison
uses restriction itself, so it is compatible with the descended Galois actions. -/
def TorusIsogenyKernel : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B),
    IsTorus A → IsTorus B → IsTorusIsogeny f →
    ∃ (C : HopfAlgebraCategory k) (q : B ⟶ C)
      (hq : IsClosedImmersion (specGroupMap q).hom.hom.left),
      IsMultiplicativeType C ∧ IsFinite (specGroup C).X.hom ∧
      IsSchemeKernel (specGroupMap f) ⟨specGroup C, specGroupMap q, hq⟩ ∧
      ∃ e : (GeometricCharacters K B ⧸ (pullbackCharacter K f).range) ≃*
          GeometricCharacters K C,
        let π := QuotientGroup.mk' (pullbackCharacter K f).range
        (∀ x, e (π x) = pullbackCharacter K q x) ∧
        ∀ (σ : Gal(K/k)) (x y : GeometricCharacters K B),
          (SemilinearAction.scalarExtension (K := K) B).act σ x.val = y.val →
          (SemilinearAction.scalarExtension (K := K) C).act σ (e (π x)).val = (e (π y)).val

end

end LinearAlgebraicGroups.Specs.SmoothnessAndIsogenies
