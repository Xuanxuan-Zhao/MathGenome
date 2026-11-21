import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.SplittingCriterion

/-! SM-02 (paper.tex, 952–983). The polynomial algebra structure on B is
arbitrary, subject only to compatibility with A and surjectivity. Thus all
finite polynomial presentations are quantified over, including n = 0.
The shared conormal object is ker(P → B)/ker(P → B)² and the shared arrow
sends the class of f to 1 ⊗ df, as specified in KD-11. -/
namespace Specs.AdvCommAlg.Smooth.Conormal

universe u v
noncomputable section
open Specs.AdvCommAlg.Differentials
open Specs.AdvCommAlg.FormalLifting.SplittingCriterion
open TensorProduct

def criterion : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.FinitePresentation A B] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) A) B]
  [IsScalarTower A (MvPolynomial (Fin n) A) B]
  (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B)),
  smoothValue A B ↔
    ∃ ρ : (B ⊗[MvPolynomial (Fin n) A]
        KaehlerDifferential A (MvPolynomial (Fin n) A)) →ₗ[B]
        Differentials.Conormal A (MvPolynomial (Fin n) A) B h,
      ρ.comp (conormalMapValue A (MvPolynomial (Fin n) A) B h) = LinearMap.id

def splitFiniteProjective : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.FinitePresentation A B] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) A) B]
  [IsScalarTower A (MvPolynomial (Fin n) A) B]
  (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B)),
  smoothValue A B →
    SplitConormal A (MvPolynomial (Fin n) A) B h ∧
    Module.Finite B (Differentials.Conormal A (MvPolynomial (Fin n) A) B h) ∧
    Module.Projective B (Differentials.Conormal A (MvPolynomial (Fin n) A) B h) ∧
    Module.Finite B (KaehlerDifferential A B) ∧
    Module.Projective B (KaehlerDifferential A B)

def twoTermCriterion : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.FinitePresentation A B] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) A) B]
  [IsScalarTower A (MvPolynomial (Fin n) A) B]
  (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B)),
  smoothValue A B ↔
    Function.Injective (conormalMapValue A (MvPolynomial (Fin n) A) B h) ∧
      Module.Projective B (KaehlerDifferential A B)

end
end Specs.AdvCommAlg.Smooth.Conormal
