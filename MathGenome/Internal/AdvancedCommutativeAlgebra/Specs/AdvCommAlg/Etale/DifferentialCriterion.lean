import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Conormal

/-! ET-02, paper.tex:1534–1554. The conormal object and map are the
canonical I/I² and [f] ↦ 1 ⊗ df from KD-11. An isomorphism of modules is
expressed as bijectivity of this linear map. Polynomial variables in the
presentation criterion and the universal criterion have arbitrary size.
No finiteness or nontriviality condition on the rings is implicit. -/
namespace Specs.AdvCommAlg.Etale

universe u v w
noncomputable section

/-- Invertibility of the actual conormal map of a specified polynomial
presentation, using its induced structural map to B. -/
def PolynomialConormalIso (A : Type u) (B : Type v) (ι : Type w)
    [CommRing A] [CommRing B] [Algebra A B]
    (π : MvPolynomial ι A →ₐ[A] B) (hπ : Function.Surjective π) : Prop :=
  letI : Algebra (MvPolynomial ι A) B := π.toRingHom.toAlgebra
  letI : IsScalarTower A (MvPolynomial ι A) B := IsScalarTower.of_algHom π
  Function.Bijective (Differentials.conormalMapValue A (MvPolynomial ι A) B hπ)

def etaleIffSmoothOmega : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  etaleValue A B ↔ Smooth.smoothValue A B ∧ Subsingleton (KaehlerDifferential A B)

/-- The equivalence holds for each polynomial presentation, including
presentations with an infinite indexing type. -/
def polynomialPresentationCriterion : Prop := ∀ (A : Type u) (B : Type v)
  (ι : Type w) [CommRing A] [CommRing B] [Algebra A B]
  (π : MvPolynomial ι A →ₐ[A] B) (hπ : Function.Surjective π),
  etaleValue A B ↔ Algebra.FinitePresentation A B ∧ PolynomialConormalIso A B ι π hπ

/-- A finite polynomial presentation suffices as an existential witness. -/
def etaleIffExistsConormalIso : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  etaleValue A B ↔ Algebra.FinitePresentation A B ∧
    ∃ (n : ℕ) (π : MvPolynomial (Fin n) A →ₐ[A] B)
      (hπ : Function.Surjective π), PolynomialConormalIso A B (Fin n) π hπ

/-- Every presentation is allowed; w is independent of the ring universes. -/
def etaleIffEveryConormalIso : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  etaleValue A B ↔ Algebra.FinitePresentation A B ∧
    ∀ (ι : Type w) (π : MvPolynomial ι A →ₐ[A] B)
      (hπ : Function.Surjective π), PolynomialConormalIso A B ι π hπ

end
end Specs.AdvCommAlg.Etale
