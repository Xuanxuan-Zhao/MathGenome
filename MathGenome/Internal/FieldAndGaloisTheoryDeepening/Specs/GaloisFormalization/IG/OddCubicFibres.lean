import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.CubicGaloisCriterion
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Ring.Int.Parity

open Polynomial
open scoped Polynomial

namespace GaloisFormalization.IG.OddCubicFibresSpec

abbrev PolynomialType := ℤ → ℚ[X]

noncomputable def polynomial : PolynomialType := fun a => X ^ 3 - X - C (a : ℚ)

def MonicCubic : Prop :=
  ∀ a : ℤ, IsMonicOfDegree (polynomial a) 3

def IrreducibleFibre : Prop :=
  ∀ a : ℤ, Odd a → Irreducible (polynomial a)

def SeparableFibre : Prop :=
  ∀ a : ℤ, Odd a → (polynomial a).Separable

def Discriminant : Prop :=
  ∀ a : ℤ, cubicDiscriminant (polynomial a) = 4 - 27 * (a : ℚ) ^ 2

def NegativeDiscriminant : Prop :=
  ∀ a : ℤ, Odd a → cubicDiscriminant (polynomial a) < 0

def NonsquareDiscriminant : Prop :=
  ∀ a : ℤ, Odd a → ¬ IsSquare (cubicDiscriminant (polynomial a))

universe u

def RootActionGroup : Prop :=
  ∀ (a : ℤ) {L : Type u} [Field L] [Algebra ℚ L] [(polynomial a).IsSplittingField ℚ L],
    Odd a →
      ∃ (e : CubicRootOrdering (polynomial a) L) (φ : (L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3)),
        φ.toMonoidHom = cubicRootAction e

end GaloisFormalization.IG.OddCubicFibresSpec
