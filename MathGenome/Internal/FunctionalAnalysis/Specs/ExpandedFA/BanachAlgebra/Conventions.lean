import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.UnitizationL1
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
Independent specification for the Banach-algebra conventions in paper.tex,
9907–9914, 10041–10050, 10196–10206 and 10718–10726.

All algebra structures and norms are native. `NonUnitalNormedRing` and
`NormedRing` include submultiplicativity; scalar compatibility is supplied by
`NormedSpace` with the two scalar multiplication laws, or by `NormedAlgebra`.
The chapter's normalized nonzero unital Banach assumption is a separate
predicate, never a prerequisite for spectrum, resolvent, or operator definitions.

The scalar-parametric algebraic definitions include both real and complex
operators. In particular they do not assert nonempty spectrum over the reals.
The real supremum is used for the radius; its usual supremum properties require
a nonempty bounded spectrum, supplied by the subsequent Banach-algebra theory.
The resolvent is extended by zero off its resolvent set, as in Mathlib.

`UnitizationValue` uses the sum norm, rather than the regular-representation
norm (which would require additional hypotheses on the nonunital algebra).
Characters carry no continuity or boundedness condition. Automatic boundedness
belongs to the later character theorems, not to this interface.
-/

namespace Specs.ExpandedFA.BanachAlgebra.Conventions

universe u v

/-- Nonunital Banach algebras may be zero. -/
def IsBanachAlgebraType :=
  ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A], Prop

def IsBanachAlgebraValue : IsBanachAlgebraType.{u} :=
  fun A _ _ _ _ => CompleteSpace A

/-- Precisely the chapter's nonzero, normalized unital Banach convention. -/
def IsUnitalBanachAlgebraType :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], Prop

def IsUnitalBanachAlgebraValue : IsUnitalBanachAlgebraType.{u} :=
  fun A _ _ => CompleteSpace A ∧ Nontrivial A ∧ NormOneClass A

def AlgebraInvertibleType := ∀ (A : Type u) [Monoid A], A → Prop

def AlgebraInvertibleValue : AlgebraInvertibleType.{u} :=
  fun _ _ a => IsUnit a

/-- These definitions require only an algebra, not even a norm. -/
def AlgebraScalarSetType :=
  ∀ (𝕜 : Type u) (A : Type v) [CommSemiring 𝕜] [Ring A] [Algebra 𝕜 A], A → Set 𝕜

def AlgebraResolventSetValue : AlgebraScalarSetType.{u, v} :=
  fun 𝕜 A _ _ _ a => {z : 𝕜 | IsUnit (algebraMap 𝕜 A z - a)}

def AlgebraSpectrumValue : AlgebraScalarSetType.{u, v} :=
  fun 𝕜 A _ _ _ a => {z : 𝕜 | ¬ IsUnit (algebraMap 𝕜 A z - a)}

def AlgebraResolventType :=
  ∀ (𝕜 : Type u) (A : Type v) [CommSemiring 𝕜] [Ring A] [Algebra 𝕜 A], A → 𝕜 → A

noncomputable def AlgebraResolventValue : AlgebraResolventType.{u, v} :=
  fun 𝕜 A _ _ _ a z => Ring.inverse (algebraMap 𝕜 A z - a)

def AlgebraSpectralRadiusType :=
  ∀ (𝕜 : Type u) (A : Type v) [NormedField 𝕜] [Ring A] [Algebra 𝕜 A], A → ℝ

noncomputable def AlgebraSpectralRadiusValue : AlgebraSpectralRadiusType.{u, v} :=
  fun 𝕜 A _ _ _ a => sSup ((fun z : 𝕜 => ‖z‖) '' AlgebraSpectrumValue 𝕜 A a)

/-- The native unitization with its ℓ¹ norm; no completeness is imposed here. -/
def UnitizationType :=
  ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A], Type u

abbrev UnitizationValue : UnitizationType.{u} :=
  fun A _ _ _ _ => WithLp 1 (Unitization ℂ A)

def UnitizationInclusionType :=
  ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A], A → UnitizationValue A

def UnitizationInclusionValue : UnitizationInclusionType.{u} :=
  fun _ _ _ _ _ a => WithLp.toLp 1 (Unitization.inr a)

def NonunitalSpectrumType :=
  ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A], A → Set ℂ

def NonunitalSpectrumValue : NonunitalSpectrumType.{u} :=
  fun A _ _ _ _ a => AlgebraSpectrumValue ℂ (UnitizationValue A) (UnitizationInclusionValue A a)

def NonunitalResolventType :=
  ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A], A → ℂ → UnitizationValue A

noncomputable def NonunitalResolventValue : NonunitalResolventType.{u} :=
  fun A _ _ _ _ a z =>
    AlgebraResolventValue ℂ (UnitizationValue A) (UnitizationInclusionValue A a) z

def NonunitalSpectralRadiusType :=
  ∀ (A : Type u) [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A], A → ℝ

noncomputable def NonunitalSpectralRadiusValue : NonunitalSpectralRadiusType.{u} :=
  fun A _ _ _ _ a => sSup ((fun z : ℂ => ‖z‖) '' NonunitalSpectrumValue A a)

/-- The point and approximate point spectra retain the operator's scalar field. -/
def OperatorScalarSetType :=
  ∀ (𝕜 : Type u) (X : Type v) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X], (X →L[𝕜] X) → Set 𝕜

def PointSpectrumValue : OperatorScalarSetType.{u, v} :=
  fun 𝕜 X _ _ _ T => {z : 𝕜 | ∃ x : X, x ≠ 0 ∧ T x = z • x}

/-- Arbitrarily small residuals on the unit sphere, including the zero-space case. -/
def ApproximatePointSpectrumValue : OperatorScalarSetType.{u, v} :=
  fun 𝕜 X _ _ _ T => {z : 𝕜 | ∀ ε : ℝ, 0 < ε →
    ∃ x : X, ‖x‖ = 1 ∧ ‖T x - z • x‖ < ε}

/-- Algebraic characters are nonzero linear multiplicative maps, even without a unit. -/
def CharacterSpaceType :=
  ∀ (𝕜 : Type u) (A : Type v) [Field 𝕜] [NonUnitalRing A] [Module 𝕜 A],
    Set (A →ₗ[𝕜] 𝕜)

def CharacterSpaceValue : CharacterSpaceType.{u, v} :=
  fun _ A _ _ _ => {χ | χ ≠ 0 ∧ ∀ a b : A, χ (a * b) = χ a * χ b}

def CharacterType :=
  ∀ (𝕜 : Type u) (A : Type v) [Field 𝕜] [NonUnitalRing A] [Module 𝕜 A], Type (max u v)

abbrev CharacterValue : CharacterType.{u, v} :=
  fun 𝕜 A _ _ _ => ↥(CharacterSpaceValue 𝕜 A)

/-! Observable inverse laws and applicability of the algebraic definitions. -/

def InvertibleTwoSidedInverse : Prop :=
  ∀ (A : Type u) [Monoid A] (a : A),
    AlgebraInvertibleValue A a ↔ ∃ b : A, a * b = 1 ∧ b * a = 1

def SpectrumMembership : Prop :=
  ∀ (𝕜 : Type u) (A : Type v) [CommSemiring 𝕜] [Ring A] [Algebra 𝕜 A]
    (a : A) (z : 𝕜), z ∈ AlgebraSpectrumValue 𝕜 A a ↔ ¬ IsUnit (z • (1 : A) - a)

def ResolventInverse : Prop :=
  ∀ (𝕜 : Type u) (A : Type v) [CommSemiring 𝕜] [Ring A] [Algebra 𝕜 A]
    (a : A) (z : 𝕜), z ∈ AlgebraResolventSetValue 𝕜 A a →
    (z • (1 : A) - a) * AlgebraResolventValue 𝕜 A a z = 1 ∧
      AlgebraResolventValue 𝕜 A a z * (z • (1 : A) - a) = 1

def OperatorResolventBoundedInverse : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (T : X →L[𝕜] X) (z : 𝕜),
    z ∈ AlgebraResolventSetValue 𝕜 (X →L[𝕜] X) T ↔
    ∃ S : X →L[𝕜] X,
      (∀ x : X, S (z • x - T x) = x) ∧ (∀ x : X, z • S x - T (S x) = x)

def OperatorSpectrumNoBoundedInverse : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (T : X →L[𝕜] X) (z : 𝕜),
    z ∈ AlgebraSpectrumValue 𝕜 (X →L[𝕜] X) T ↔
    ¬ ∃ S : X →L[𝕜] X,
      (∀ x : X, S (z • x - T x) = x) ∧ (∀ x : X, z • S x - T (S x) = x)

def ZeroSpaceSpectra : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [Subsingleton X] (T : X →L[𝕜] X),
    AlgebraSpectrumValue 𝕜 (X →L[𝕜] X) T = ∅ ∧
      PointSpectrumValue 𝕜 X T = ∅ ∧ ApproximatePointSpectrumValue 𝕜 X T = ∅

end Specs.ExpandedFA.BanachAlgebra.Conventions
