import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.HilbertSamuelDimension
import Mathlib.Data.Nat.Factorial.Basic

/-! Multiplicity in a specified degree (I04). The cumulative lengths use
the quotient by (J^{t+1}E). -/

namespace Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity

open _root_.P103.HilbertSamuelPolynomial
open _root_.P103.Specs.Ch06.DimensionConventions

universe u v

section Definitions

variable {A : Type u} [CommRing A] (J : Ideal A)
variable (E : Type v) [AddCommGroup E] [Module A E]

/-- Select the polynomial characterized by the eventual cumulative lengths. -/
noncomputable def hilbertSamuelPolynomial : Polynomial ℚ :=
  Classical.epsilon (EventuallyPolynomial (quotientLength J E))

/-- The factorial times the specified coefficient, also defined on the zero module. -/
noncomputable def degreeMultiplicity (r : ℕ) : ℚ :=
  (r.factorial : ℚ) * (hilbertSamuelPolynomial J E).coeff r

/-- The specified-degree multiplicity taken at the dimension of the module.
The dimension conversion is exact for nonzero finite modules over Noetherian
local rings. -/
noncomputable def hilbertSamuelMultiplicity : ℚ :=
  degreeMultiplicity J E ((moduleDimensionValue A E).unbotD 0).toNat

end Definitions

section DefinitionTypes

set_option linter.checkUnivs false

def hilbertSamuelPolynomialType :=
  ∀ {A : Type u} [CommRing A] (_ : Ideal A) (E : Type v) [AddCommGroup E] [Module A E],
    Polynomial ℚ

def degreeMultiplicityType :=
  ∀ {A : Type u} [CommRing A] (_ : Ideal A) (E : Type v) [AddCommGroup E] [Module A E],
    ℕ → ℚ

def hilbertSamuelMultiplicityType :=
  ∀ {A : Type u} [CommRing A] (_ : Ideal A) (E : Type v) [AddCommGroup E] [Module A E],
    ℚ

end DefinitionTypes

def quotientLengthsFiniteType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E]
    (J : Ideal A), J ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (J • (⊤ : Submodule A E))) →
    ∀ n : ℕ, IsFiniteLength A (Quotient J E n)

def hilbertSamuelPolynomialEventuallyType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E]
    (J : Ideal A), J ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (J • (⊤ : Submodule A E))) →
    EventuallyPolynomial (quotientLength J E) (hilbertSamuelPolynomial J E)

def hilbertSamuelPolynomialUniqueType : Prop :=
  ∀ (A : Type u) [CommRing A] (E : Type v) [AddCommGroup E] [Module A E]
    (J : Ideal A),
    ∀ p : Polynomial ℚ, EventuallyPolynomial (quotientLength J E) p →
      p = hilbertSamuelPolynomial J E

def hilbertSamuelPolynomialDegreeType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E] [Nontrivial E]
    (J : Ideal A), J ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (J • (⊤ : Submodule A E))) →
    0 < (hilbertSamuelPolynomial J E).leadingCoeff ∧
      moduleDimensionValue A E = ((hilbertSamuelPolynomial J E).natDegree : WithBot ℕ∞)

def hilbertSamuelPolynomialDimensionZeroType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E] [Nontrivial E]
    (J : Ideal A), J ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (J • (⊤ : Submodule A E))) →
    moduleDimensionValue A E = 0 →
      hilbertSamuelPolynomial J E = Polynomial.C ((Module.length A E).toNat : ℚ)

def hilbertSamuelPolynomialZeroType : Prop :=
  ∀ (A : Type u) [CommRing A] (E : Type v) [AddCommGroup E] [Module A E] [Subsingleton E]
    (J : Ideal A),
    hilbertSamuelPolynomial J E = 0

def degreeMultiplicityZeroType : Prop :=
  ∀ (A : Type u) [CommRing A] (E : Type v) [AddCommGroup E] [Module A E] [Subsingleton E]
    (J : Ideal A),
    ∀ r : ℕ, degreeMultiplicity J E r = 0

def degreeMultiplicityZeroOfDimensionLTType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E]
    (J : Ideal A), J ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (J • (⊤ : Submodule A E))) →
    ∀ r : ℕ, moduleDimensionValue A E < (r : WithBot ℕ∞) → degreeMultiplicity J E r = 0

def degreeMultiplicityIntegralType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E]
    (J : Ideal A), J ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (J • (⊤ : Submodule A E))) →
    ∀ r : ℕ, moduleDimensionValue A E ≤ (r : WithBot ℕ∞) →
      ∃ z : ℤ, degreeMultiplicity J E r = (z : ℚ)

def hilbertSamuelMultiplicityAtDimensionType : Prop :=
  ∀ (A : Type u) [CommRing A] (E : Type v) [AddCommGroup E] [Module A E]
    (J : Ideal A),
    ∀ d : ℕ, moduleDimensionValue A E = (d : WithBot ℕ∞) →
      hilbertSamuelMultiplicity J E = degreeMultiplicity J E d

def hilbertSamuelMultiplicityPositiveType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E] [Nontrivial E]
    (J : Ideal A), J ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (J • (⊤ : Submodule A E))) →
    0 < hilbertSamuelMultiplicity J E

end Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity
