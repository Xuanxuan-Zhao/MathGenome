import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.RelativeRank
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.BaseChange

/-! SM-09, paper.tex:1241–1242 and 1249–1251. The new cotangent fiber
is scalar extension of the old cotangent fiber along the canonical embedding
of residue fields. Base change is arbitrary; all commutative rings, including
the zero ring, are allowed. A pushout formulation includes every realization
of the base change, and the tensor formulation specifies B' = A' ⊗[A] B. -/
namespace Specs.AdvCommAlg.Smooth.RelativeRankBaseChange

universe u v w z
noncomputable section
open scoped TensorProduct

/-- The residue-field scalar structure is induced by B → C, at a prime of C
and its contraction to B. It is not an arbitrary field extension. -/
def cotangentFiberComparison : Prop :=
  ∀ (A : Type u) (A' : Type v) (B : Type w) (C : Type z)
    [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [Algebra A A'] [Algebra A B] [Algebra A C] [Algebra A' C] [Algebra B C]
    [IsScalarTower A A' C] [IsScalarTower A B C] [Algebra.IsPushout A A' B C]
    (q' : PrimeSpectrum C),
    let q := q'.comap (algebraMap B C)
    letI : Algebra q.asIdeal.ResidueField q'.asIdeal.ResidueField :=
      (Ideal.ResidueField.map q.asIdeal q'.asIdeal (algebraMap B C) rfl).toAlgebra
    Nonempty
      (q'.asIdeal.ResidueField ⊗[q.asIdeal.ResidueField]
          (q.asIdeal.ResidueField ⊗[B] KaehlerDifferential A B) ≃ₗ[q'.asIdeal.ResidueField]
        (q'.asIdeal.ResidueField ⊗[C] KaehlerDifferential A' C))

/-- Dimensions of the specified residue fibers at corresponding primes in
any pushout. Smoothness is the original SM-09 hypothesis. -/
def baseChangeRank : Prop :=
  ∀ (A : Type u) (A' : Type v) (B : Type w) (C : Type z)
    [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [Algebra A A'] [Algebra A B] [Algebra A C] [Algebra A' C] [Algebra B C]
    [IsScalarTower A A' C] [IsScalarTower A B C] [Algebra.IsPushout A A' B C],
    smoothValue A B → ∀ q' : PrimeSpectrum C,
      RelativeRank.relativeRankValue A' C q' =
        RelativeRank.relativeRankValue A B (q'.comap (algebraMap B C))

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- In the tensor model the contraction uses b ↦ 1 ⊗ b. -/
def tensorBaseChangeRank : Prop :=
  ∀ (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'],
    smoothValue A B → ∀ q' : PrimeSpectrum (A' ⊗[A] B),
      RelativeRank.relativeRankValue A' (A' ⊗[A] B) q' =
        RelativeRank.relativeRankValue A B
          (q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom)

end
end Specs.AdvCommAlg.Smooth.RelativeRankBaseChange
