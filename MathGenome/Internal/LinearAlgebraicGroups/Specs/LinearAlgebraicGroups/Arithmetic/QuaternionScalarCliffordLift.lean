import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuaternionSpinScaleCover
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SymplecticDatumRankOneAndPinning

open AlgebraicGeometry CategoryTheory
open scoped Matrix TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.QuaternionScalarCliffordLift

open _root_.Specs.RM03.CSA (isCentralSimple degree)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)
open CharacterDescent (Cocharacter)
open NontrialitarianSpinModels (DescendedQuadraticPair SpinModel)
open QuaternionSpinScaleCover (QuaternionHyperbolicPresentation QuaternionPairIndex spinVectorProjection)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint oppositeCocharacter HasLimit)
open LinearAlgebraicGroups.Albert.SpinSpecification (vectors)
open OppositeRadicals (IsNoncentral)

noncomputable section

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ}

/-- The scalar matrix acts on the two quaternion coordinates (in order
`e,f`) and fixes every coordinate in the complement. -/
def scalarPairMatrix (R : TestAlgebra F) (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B) :=
  Matrix.fromBlocks (g.val.map (algebraMap R (R ⊗[F] B))) 0 0 1

def scalarDiagonal {R : Type u} [CommRing R] (r : Rˣ) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![(r : R), 0; 0, (↑r⁻¹ : R)], by simp [Matrix.det_fin_two]⟩

/-- A scheme homomorphism lifts the specified scalar action on every test algebra. -/
def LiftsScalarPair (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    {A : AffineAlgebraicGroup F}
    (e : (groupPointsFunctor F).obj A.val ≅ SymplecticDatumRankOneAndPinning.determinantOnePoints F)
    (f : A.val ⟶ G.val) : Prop :=
  ∀ (R : TestAlgebra F) (p : Points A.val.X R),
    Q.matrixAt R (spinVectorProjection M R (p ≫ f.hom.hom)).val =
      scalarPairMatrix R (e.hom.app R p)

/-- The cocharacter projects to the diagonal of the scalar split
`SL₂`, with the pair scaled by `r,r⁻¹` and the complement fixed. -/
def IsPairDiagonal (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    (c : Cocharacter G.val) : Prop :=
  ∀ (R : TestAlgebra F) (r : Rˣ),
    Q.matrixAt R (spinVectorProjection M R (cocharacterPoint c R r)).val =
      scalarPairMatrix R (scalarDiagonal r)

/-- The change from the given split comparison is induced by an isometry of
the split quadratic space, acting on every scalar extension of its Clifford
algebra. -/
def IsAdaptedSplitComparison (M : SpinModel G D)
    (a : (groupBaseChange F K).obj G.val ≅ M.splitCover.spin.val) : Prop :=
  let q := OddSpinModels.hyperbolicForm I K
  ∃ (s : q →qᵢ q), Function.Bijective s ∧
    ∀ (R : TestAlgebra K) (p : Points ((groupBaseChange F K).obj G.val).X R),
      (M.splitCover.spinPoints R (p ≫ a.hom.hom.hom)).val =
        Algebra.TensorProduct.map (AlgHom.id K R) (CliffordAlgebra.map s)
          (M.splitCover.spinPoints R (p ≫ M.splitSource.hom.hom.hom)).val

/-- The scalar plane action lifts uniquely as a group scheme homomorphism
from split `SL₂`. In adapted split Clifford coordinates its upper and lower
lines are the root groups for `±(eᵢ + eⱼ)`, expressed by the two isotropic
Clifford products. The same rank-one diagonal defines the opposite radicals. -/
def ScalarCliffordLift : Prop :=
  ∀ {F K I B : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
    (M : SpinModel G D), 4 ≤ Fintype.card I →
    ∀ (hB : isCentralSimple F B), degree F B = 2 →
    ∀ {d : ℕ} (Q : QuaternionHyperbolicPresentation D hB d),
      ∃ (A : AffineAlgebraicGroup F)
        (e : (groupPointsFunctor F).obj A.val ≅ SymplecticDatumRankOneAndPinning.determinantOnePoints F)
        (f : A.val ⟶ G.val),
        Smooth A.val.X.hom ∧ GeometricallyConnected A.val.X.hom ∧
        IsClosedImmersion f.hom.hom.left ∧ LiftsScalarPair M Q e f ∧
        (∀ f' : A.val ⟶ G.val, LiftsScalarPair M Q e f' → f' = f) ∧
        (∃ (c₀ : Cocharacter A.val),
          (∀ (R : TestAlgebra F) (r : Rˣ), e.hom.app R (cocharacterPoint c₀ R r) = scalarDiagonal r) ∧
          IsPairDiagonal M Q (c₀ ≫ f) ∧ IsNoncentral (c₀ ≫ f) ∧
          ∀ (R : TestAlgebra F) (p : Points A.val.X R) (r : R),
            (e.hom.app R p = Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 2) ≠ 1 by decide) r → HasLimit (c₀ ≫ f) (p ≫ f.hom.hom) 1) ∧
            (e.hom.app R p = Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 2) ≠ 0 by decide) r →
                HasLimit (oppositeCocharacter (c₀ ≫ f)) (p ≫ f.hom.hom) 1)) ∧
        ∃ (j₁ j₂ : I), j₁ ≠ j₂ ∧
          ∃ a : (groupBaseChange F K).obj G.val ≅ M.splitCover.spin.val,
            IsAdaptedSplitComparison M a ∧
            ∀ (R : TestAlgebra K) (p : Points ((groupBaseChange F K).obj A.val).X R),
              let z := (M.splitCover.spinPoints R
                (p ≫ ((groupBaseChange F K).map f ≫ a.hom).hom.hom)).val
              let q := OddSpinModels.hyperbolicForm I K
              let v := fun j : I ⊕ I => vectors q R ((1 : R) ⊗ₜ[K] Pi.single j (1 : K))
              let E := v (Sum.inl j₁) * v (Sum.inl j₂)
              let L := v (Sum.inr j₂) * v (Sum.inr j₁)
              let g := e.hom.app ((restrictTestAlgebra F K).obj R) (baseChangePoint F K A.val.X R p)
              (∀ r : R, g = Matrix.SpecialLinearGroup.transvection
                (show (0 : Fin 2) ≠ 1 by decide) r → z = 1 + r • E) ∧
              (∀ r : R, g = Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 2) ≠ 0 by decide) r → z = 1 + r • L) ∧
              (∀ r : Rˣ, g = scalarDiagonal r →
                z = 1 + ((r : R) - 1) • (E * L) + ((↑r⁻¹ : R) - 1) • (L * E))

end

end LinearAlgebraicGroups.Specs.Arithmetic.QuaternionScalarCliffordLift
