import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import Mathlib.Algebra.MvPolynomial.Eval

/-! Independent statements for polynomial lifts (paper.tex, FL-05).
Variables and test algebras may lie in arbitrary universes. All rings are
commutative with identity, and zero rings and empty variable types are allowed.
-/
namespace Specs.AdvCommAlg.FormalLifting

universe u v w z

/-- Polynomial algebras lift along every surjective A-algebra map, with no
condition on its kernel. -/
def polynomialSurjectionLifts : Prop :=
  ∀ (A : Type u) (Λ : Type v) (C : Type w) (D : Type z)
    [CommRing A] [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    (q : C →ₐ[A] D), Function.Surjective q →
    ∀ f : MvPolynomial Λ A →ₐ[A] D,
      ∃ g : MvPolynomial Λ A →ₐ[A] C, q.comp g = f

/-- Polynomial algebras on any set of variables satisfy the square-zero
lifting definition of formal smoothness from FL-01. -/
def polynomialFormallySmooth : Prop :=
  ∀ (A : Type u) (Λ : Type v) [CommRing A],
    formallySmoothValue A (MvPolynomial Λ A)

end Specs.AdvCommAlg.FormalLifting
