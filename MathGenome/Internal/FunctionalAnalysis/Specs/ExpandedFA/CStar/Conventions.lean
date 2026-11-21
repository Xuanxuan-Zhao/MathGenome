import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
Independent conventions for the C*-chapter of paper.tex (12041–12400).
The native classes `NonUnitalCStarAlgebra` and `CStarAlgebra` carry all the
algebra, involution, original norm and completeness data. No representation,
order, separability or nonzeroness is assumed.

The unitization here is the native C*-normed `Unitization ℂ A`, not the
`WithLp 1` Banach unitization. Its norm is the maximum of the scalar norm
and the left-action norm. For genuinely nonunital nonzero algebras the later
unitization theorem identifies this with the left-action norm alone. The
zero and already-unital alternatives are specified explicitly below.

Positivity is self-adjointness with spectrum in the nonnegative real axis.
For a nonunital algebra the spectrum is taken in this C*-unitization; for
an already-unital algebra its extra zero does not affect positivity.
Functionals and states are algebraic complex-linear maps. Continuity and
norm estimates are conclusions of the separately allocated positive-functional
theorem, and are not fields or hypotheses of these definitions.
-/

noncomputable section
namespace ExpandedFA.CStar.Conventions.Spec
universe u

/-- The closed nonnegative real axis, as a subset of the complex plane. -/
def NonnegativeScalarsType := Set ℂ
def NonnegativeScalarsValue : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}

def CStarUnitizationType := ∀ (A : Type u) [NonUnitalCStarAlgebra A], Type u
abbrev CStarUnitizationValue : CStarUnitizationType.{u} := fun A _ => Unitization ℂ A

def UnitizationInclusionType := ∀ (A : Type u) [NonUnitalCStarAlgebra A],
  A →⋆ₙₐ[ℂ] CStarUnitizationValue A
def UnitizationInclusionValue : UnitizationInclusionType.{u} :=
  fun A _ => Unitization.inrNonUnitalStarAlgHom ℂ A

def NonunitalSpectrumType := ∀ (A : Type u) [NonUnitalCStarAlgebra A], A → Set ℂ
def NonunitalSpectrumValue : NonunitalSpectrumType.{u} :=
  fun A _ a => spectrum ℂ (UnitizationInclusionValue A a)

def UnitalSpectrumType := ∀ (A : Type u) [CStarAlgebra A], A → Set ℂ
def UnitalSpectrumValue : UnitalSpectrumType.{u} := fun _ _ a => spectrum ℂ a

def SelfAdjointType := ∀ (A : Type u) [Star A], A → Prop
def SelfAdjointValue : SelfAdjointType.{u} := fun _ _ a => IsSelfAdjoint a

def NormalType := ∀ (A : Type u) [Mul A] [Star A], A → Prop
def NormalValue : NormalType.{u} := fun _ _ _ a => IsStarNormal a

def UnitaryType := ∀ (A : Type u) [Monoid A] [StarMul A], A → Prop
def UnitaryValue : UnitaryType.{u} := fun A _ _ a => a ∈ unitary A

def PositiveType := ∀ (A : Type u) [NonUnitalCStarAlgebra A], A → Prop
def PositiveValue : PositiveType.{u} := fun A _ a =>
  SelfAdjointValue A a ∧ NonunitalSpectrumValue A a ⊆ NonnegativeScalarsValue

def OrderRelationType := ∀ (A : Type u) [NonUnitalCStarAlgebra A], A → A → Prop
def OrderRelationValue : OrderRelationType.{u} := fun A _ a b => PositiveValue A (b - a)

def PositiveFunctionalType := ∀ (A : Type u) [NonUnitalCStarAlgebra A], (A →ₗ[ℂ] ℂ) → Prop
def PositiveFunctionalValue : PositiveFunctionalType.{u} :=
  fun A _ φ => ∀ a, PositiveValue A a → φ a ∈ NonnegativeScalarsValue

def StateType := ∀ (A : Type u) [CStarAlgebra A], Type u
abbrev StateValue : StateType.{u} :=
  fun A _ => {φ : A →ₗ[ℂ] ℂ // PositiveFunctionalValue A φ ∧ φ 1 = 1}

def OperatorType := ∀ (H : Type u) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H], Type u
abbrev OperatorValue : OperatorType.{u} := fun H _ _ _ => H →L[ℂ] H

def OperatorStructureType := ∀ (H : Type u) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H], CStarAlgebra (OperatorValue H)
/-- The canonical structure, with precisely the original operator norm and adjoint. -/
abbrev OperatorStructureValue : OperatorStructureType.{u} := fun _ _ _ _ => inferInstance

/-! Observable axioms and identifications of the chosen native structures. -/

def NativeAxioms : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A],
  CompleteSpace A ∧ (∀ a : A, ‖star a * a‖ = ‖a‖ ^ 2) ∧
    (∀ a : A, ‖star a‖ = ‖a‖) ∧
    (∀ a b : A, star (a * b) = star b * star a) ∧
    (∀ (z : ℂ) (a : A), star (z • a) = star z • star a) ∧
    (∀ a : A, star (star a) = a)

def SelfAdjointIdentification : Prop := ∀ (A : Type u) [Star A] (a : A),
  SelfAdjointValue A a ↔ star a = a

def NormalIdentification : Prop := ∀ (A : Type u) [Mul A] [Star A] (a : A),
  NormalValue A a ↔ star a * a = a * star a

def UnitaryIdentification : Prop := ∀ (A : Type u) [Monoid A] [StarMul A] (a : A),
  UnitaryValue A a ↔ star a * a = 1 ∧ a * star a = 1

def OperatorStarAdjoint : Prop := ∀ (H : Type u) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] (T : OperatorValue H),
  star T = ExpandedFA.Hilbert.Adjoint.Spec.AdjointValue ℂ H H T

def OperatorAlgebra : Prop := ∀ (H : Type u) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] (S T : OperatorValue H) (x : H),
  (S * T) x = S (T x) ∧ (1 : OperatorValue H) x = x ∧
    ‖star T * T‖ = ‖T‖ ^ 2

def UnitizationNative : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A],
  CompleteSpace (CStarUnitizationValue A) ∧
    (∀ x : CStarUnitizationValue A, ‖star x * x‖ = ‖x‖ ^ 2) ∧
    Isometry (UnitizationInclusionValue A)

def UnitizationNorm : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
  (x : CStarUnitizationValue A),
  ‖x‖ = max ‖x.fst‖ ‖x.fst • (1 : A →L[ℂ] A) + ContinuousLinearMap.mul ℂ A x.snd‖

/-- The unitization of the zero algebra is canonically the scalar C*-algebra. -/
def ZeroUnitizationAlternative : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
  [Subsingleton A], ∃ e : CStarUnitizationValue A ≃⋆ₐ[ℂ] ℂ,
    (∀ x, e x = x.fst) ∧ ∀ x, ‖e x‖ = ‖x‖

/-- If A already has a unit, its larger unitization has the direct-sum max norm. -/
def UnitalUnitizationAlternative : Prop := ∀ (A : Type u) [CStarAlgebra A],
  ∃ e : CStarUnitizationValue A ≃⋆ₐ[ℂ] (A × ℂ),
    (∀ x, e x = (x.snd + x.fst • (1 : A), x.fst)) ∧ ∀ x, ‖e x‖ = ‖x‖

def NonunitalSpectrumMembership : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
  (a : A) (z : ℂ), z ∈ NonunitalSpectrumValue A a ↔
    ¬ IsUnit (z • (1 : CStarUnitizationValue A) - UnitizationInclusionValue A a)

/-- The change of unitization norm preserves the earlier algebraic spectrum. -/
def BanachSpectrumCompatibility : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A] (a : A),
  NonunitalSpectrumValue A a =
    Specs.ExpandedFA.BanachAlgebra.Conventions.NonunitalSpectrumValue A a

def UnitalSpectrumAlternative : Prop := ∀ (A : Type u) [CStarAlgebra A] (a : A),
  NonunitalSpectrumValue A a = UnitalSpectrumValue A a ∪ {0}

def ZeroSpectrumAlternative : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
  [Subsingleton A] (a : A), NonunitalSpectrumValue A a = {0}

def PositiveUnitalIdentification : Prop := ∀ (A : Type u) [CStarAlgebra A] (a : A),
  PositiveValue A a ↔ IsSelfAdjoint a ∧ UnitalSpectrumValue A a ⊆ NonnegativeScalarsValue

def StateIdentification : Prop := ∀ (A : Type u) [CStarAlgebra A] (φ : A →ₗ[ℂ] ℂ),
  (∃ s : StateValue A, s.val = φ) ↔
    (∀ a, PositiveValue A a → (φ a).im = 0 ∧ 0 ≤ (φ a).re) ∧ φ 1 = 1

def ZeroAlgebraNoStates : Prop := ∀ (A : Type u) [CStarAlgebra A] [Subsingleton A],
  IsEmpty (StateValue A)

end ExpandedFA.CStar.Conventions.Spec
