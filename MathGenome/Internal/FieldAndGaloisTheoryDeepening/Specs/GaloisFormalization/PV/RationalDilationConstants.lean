import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorRing
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.GroupTheory.OrderOfElement

open scoped Polynomial

namespace GaloisFormalization.PV.Specs

universe u

/-- Substitution of `q * X` in the polynomial ring, with inverse substitution
of `q⁻¹ * X`. -/
noncomputable def polynomialDilation {K : Type u} [Field K] (q : Kˣ) :
    K[X] ≃ₐ[K] K[X] :=
  Polynomial.algEquivOfCompEqX
    (Polynomial.C (q : K) * Polynomial.X)
    (Polynomial.C (↑(q⁻¹) : K) * Polynomial.X)
    (by simp [← Polynomial.C_mul, ← mul_assoc])
    (by simp [← Polynomial.C_mul, ← mul_assoc])

def rationalDilationType :=
  {K : Type u} → [Field K] → Kˣ → RatFunc K ≃ₐ[K] RatFunc K

/-- The substitution automorphism on the field of rational functions. -/
noncomputable def rationalDilation : rationalDilationType.{u} :=
  fun q => IsFractionRing.algEquivOfAlgEquiv (polynomialDilation q)

def rationalDilationOperatorType :=
  {K : Type u} → [Field K] → Kˣ → operator .difference (RatFunc K)

noncomputable def rationalDilationOperator : rationalDilationOperatorType.{u} :=
  fun q => difference (rationalDilation q).toRingEquiv

def rationalDilationAlgebraMap : Prop :=
  ∀ {K : Type u} [Field K] (q : Kˣ) (p : K[X]),
    rationalDilation q (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (p.comp (Polynomial.C (q : K) * Polynomial.X))

def rationalDilationMk : Prop :=
  ∀ {K : Type u} [Field K] (q : Kˣ) (p d : K[X]),
    rationalDilation q (RatFunc.mk p d) =
      RatFunc.mk (p.comp (Polynomial.C (q : K) * Polynomial.X))
        (d.comp (Polynomial.C (q : K) * Polynomial.X))

def rationalDilationSymm : Prop :=
  ∀ {K : Type u} [Field K] (q : Kˣ),
    (rationalDilation q).symm = rationalDilation q⁻¹

def rationalDilationConstantSubfield : Prop :=
  ∀ {K : Type u} [Field K] (q : Kˣ), orderOf q = 0 →
    constantSubfield (rationalDilationOperator q) = (algebraMap K (RatFunc K)).fieldRange

def rationalDilationIsBaseField : Prop :=
  ∀ {K : Type u} [Field K] [CharZero K] [IsAlgClosed K] (q : Kˣ), orderOf q = 0 →
    isBaseField (rationalDilationOperator q)

end GaloisFormalization.PV.Specs
