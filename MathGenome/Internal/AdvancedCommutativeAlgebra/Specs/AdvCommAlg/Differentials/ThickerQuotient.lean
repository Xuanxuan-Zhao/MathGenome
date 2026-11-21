import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! KD-15. All quotient actions are induced by the quotient factor map. -/
namespace Specs.AdvCommAlg.Differentials

universe u v w z
noncomputable section
open TensorProduct

/-- The natural map after extending coefficients to a further algebra. -/
def restrictionMap (A : Type u) (B : Type v) (C : Type w) (T : Type z)
    [CommRing A] [CommRing B] [CommRing C] [CommRing T]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra B T] [Algebra C T] [IsScalarTower B C T] :
    T ⊗[B] KaehlerDifferential A B →ₗ[T] T ⊗[C] KaehlerDifferential A C :=
  LinearMap.liftBaseChange T
    (((TensorProduct.mk C T (KaehlerDifferential A C) 1).restrictScalars B).comp
      (KaehlerDifferential.map A A B C))

/-- B/I^(n+1) acts on B/I^n via the canonical factor map. -/
abbrev powerQuotientAlgebra (B : Type v) [CommRing B] (I : Ideal B) (n : ℕ) :
    Algebra (B ⧸ I ^ (n + 1)) (B ⧸ I ^ n) :=
  (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right (Nat.le_succ n))).toAlgebra

instance powerQuotientTower (B : Type v) [CommRing B] (I : Ideal B) (n : ℕ) :
    letI := powerQuotientAlgebra B I n
    IsScalarTower B (B ⧸ I ^ (n + 1)) (B ⧸ I ^ n) := by
  letI := powerQuotientAlgebra B I n
  apply IsScalarTower.of_algebraMap_eq'
  rfl

instance powerQuotientTowerBase (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (n : ℕ) :
    letI := powerQuotientAlgebra B I n
    IsScalarTower A (B ⧸ I ^ (n + 1)) (B ⧸ I ^ n) := by
  letI := powerQuotientAlgebra B I n
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rfl

/-- The actual canonical map is an isomorphism, not merely an abstract
isomorphism between the two modules. -/
def thickerQuotient : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (n : ℕ), 1 ≤ n →
    letI := powerQuotientAlgebra B I n
    ∃ e : (B ⧸ I ^ n) ⊗[B] KaehlerDifferential A B ≃ₗ[B ⧸ I ^ n]
      (B ⧸ I ^ n) ⊗[B ⧸ I ^ (n + 1)] KaehlerDifferential A (B ⧸ I ^ (n + 1)),
      e.toLinearMap = restrictionMap A B (B ⧸ I ^ (n + 1)) (B ⧸ I ^ n)

/-- For k[t] at (t), both restricted modules are k·dt, and the
ordinary differentials of k[t]/(t) over k vanish. The displayed generators
map to 1 and the identifications respect the canonical restriction map.
This formulation also works for a general commutative coefficient ring. -/
def thickerPolynomialExample : Prop := ∀ (k : Type u) [CommRing k],
  let P := Polynomial k
  let I : Ideal P := Ideal.span {Polynomial.X}
  let T := P ⧸ I ^ 1
  let C := P ⧸ I ^ (1 + 1)
  letI := powerQuotientAlgebra P I 1
  ∃ e₁ : T ⊗[P] KaehlerDifferential k P ≃ₗ[k] k,
  ∃ e₂ : T ⊗[C] KaehlerDifferential k C ≃ₗ[k] k,
    e₁ (1 ⊗ₜ[P] KaehlerDifferential.D k P Polynomial.X) = 1 ∧
    e₂ (1 ⊗ₜ[C] KaehlerDifferential.D k C (algebraMap P C Polynomial.X)) = 1 ∧
    (∀ x, e₂ (restrictionMap k P C T x) = e₁ x) ∧
    Subsingleton (KaehlerDifferential k T)

end
end Specs.AdvCommAlg.Differentials
