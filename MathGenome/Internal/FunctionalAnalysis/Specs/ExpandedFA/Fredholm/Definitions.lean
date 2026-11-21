import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.WithBot

/-!
Independent definitions for paper.tex:10428–10444, 10586–10599 and 10625–10634.
The cokernel is the quotient by the actual range. The finite index is an
integer subtraction; the semi-Fredholm index also admits both infinities.
No complement, parametrix, or boundedness of an algebraic splitting is assumed.
The Calkin quotient uses all compact operators, not a finite-rank closure.
-/

noncomputable section
namespace ExpandedFA.Fredholm.DefinitionsSpec
universe u v w

section Algebraic
variable {𝕜 : Type u} [Field 𝕜] {E : Type v} {F : Type w}
  [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

def IsAlgebraicFiniteIndexValue (T : E →ₗ[𝕜] F) : Prop :=
  FiniteDimensional 𝕜 T.ker ∧ FiniteDimensional 𝕜 (F ⧸ T.range)

def algebraicIndexValue (T : E →ₗ[𝕜] F) (_h : IsAlgebraicFiniteIndexValue T) : ℤ :=
  (Module.finrank 𝕜 T.ker : ℤ) - (Module.finrank 𝕜 (F ⧸ T.range) : ℤ)
end Algebraic

def IsAlgebraicFiniteIndexType :=
  ∀ {𝕜 : Type u} [Field 𝕜] {E : Type v} {F : Type w}
    [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F],
    (E →ₗ[𝕜] F) → Prop

def algebraicIndexType :=
  ∀ {𝕜 : Type u} [Field 𝕜] {E : Type v} {F : Type w}
    [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]
    (T : E →ₗ[𝕜] F), IsAlgebraicFiniteIndexValue T → ℤ

section Banach
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- The formula also makes sense in normed spaces; Banach spaces are included. -/
def IsFredholmValue (T : E →L[𝕜] F) : Prop :=
  IsClosed (T.range : Set F) ∧
    FiniteDimensional 𝕜 T.ker ∧ FiniteDimensional 𝕜 (F ⧸ T.range)

def fredholmIndexValue (T : E →L[𝕜] F) (_h : IsFredholmValue T) : ℤ :=
  (Module.finrank 𝕜 T.ker : ℤ) - (Module.finrank 𝕜 (F ⧸ T.range) : ℤ)
end Banach

def IsFredholmType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], (E →L[𝕜] F) → Prop

def fredholmIndexType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F), IsFredholmValue T → ℤ

/-- Integers with separately represented negative and positive infinity. -/
abbrev ExtendedIndexValue := WithBot (WithTop ℤ)
def ExtendedIndexType := Type

section Hilbert
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]

def IsLeftSemiFredholmValue (T : H →L[𝕜] K) : Prop :=
  IsClosed (T.range : Set K) ∧ FiniteDimensional 𝕜 T.ker

def IsRightSemiFredholmValue (T : H →L[𝕜] K) : Prop :=
  IsClosed (T.range : Set K) ∧ FiniteDimensional 𝕜 (K ⧸ T.range)

def IsSemiFredholmValue (T : H →L[𝕜] K) : Prop :=
  IsLeftSemiFredholmValue T ∨ IsRightSemiFredholmValue T

/-- The domain excludes the undefined infinity-minus-infinity case. -/
def semiFredholmIndexValue (T : H →L[𝕜] K) (_h : IsSemiFredholmValue T) :
    ExtendedIndexValue := by
  classical
  exact if FiniteDimensional 𝕜 T.ker then
    if FiniteDimensional 𝕜 (K ⧸ T.range) then
      let n : ℤ := (Module.finrank 𝕜 T.ker : ℤ) - (Module.finrank 𝕜 (K ⧸ T.range) : ℤ)
      ((n : WithTop ℤ) : WithBot (WithTop ℤ))
    else ⊥
  else ⊤
end Hilbert

def HilbertPredicateType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K], (H →L[𝕜] K) → Prop

def semiFredholmIndexType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    (T : H →L[𝕜] K), IsSemiFredholmValue T → ExtendedIndexValue

section Calkin
variable (𝕜 : Type u) [RCLike 𝕜] (E : Type v)
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The canonical ideal in the endomorphism ring. Scalar closure also follows
from compactness. This native representation has the exact unit-ball-image
meaning by the upstream compactness specification. -/
def compactIdealValue : Ideal (E →L[𝕜] E) where
  carrier := {T | IsCompactOperator T}
  zero_mem' := isCompactOperator_zero
  add_mem' := fun hS hT => hS.add hT
  smul_mem' A _T hT := hT.clm_comp A

instance compactIdeal_twoSided : (compactIdealValue 𝕜 E).IsTwoSided where
  mul_mem_of_left B hA := hA.comp_clm B

/-- The genuine quotient ring, with its native quotient topology and norm.
The definition works for Banach spaces, and hence for Hilbert spaces. -/
abbrev CalkinValue := (E →L[𝕜] E) ⧸ compactIdealValue 𝕜 E

def calkinProjectionValue : (E →L[𝕜] E) →ₐ[𝕜] CalkinValue 𝕜 E :=
  Ideal.Quotient.mkₐ 𝕜 (compactIdealValue 𝕜 E)
end Calkin

def compactIdealType :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (E : Type v)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], Ideal (E →L[𝕜] E)

def CalkinType :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (E : Type v)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], Type v

def calkinProjectionType :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (E : Type v)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (E →L[𝕜] E) →ₐ[𝕜] CalkinValue 𝕜 E


def AlgebraicIndexFormula : Prop :=
  ∀ {𝕜 : Type u} [Field 𝕜] {E : Type v} {F : Type w}
    [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F],
  ∀ (T : E →ₗ[𝕜] F) (h : IsAlgebraicFiniteIndexValue T),
    algebraicIndexValue T h =
      (Module.finrank 𝕜 T.ker : ℤ) - (Module.finrank 𝕜 (F ⧸ T.range) : ℤ)

def FredholmIffLeftAndRight : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K],
  ∀ T : H →L[𝕜] K,
    IsFredholmValue T ↔ IsLeftSemiFredholmValue T ∧ IsRightSemiFredholmValue T

def SemiFredholmCharacterization : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K],
  ∀ T : H →L[𝕜] K,
    IsSemiFredholmValue T ↔ IsClosed (T.range : Set K) ∧
      (FiniteDimensional 𝕜 T.ker ∨ FiniteDimensional 𝕜 (K ⧸ T.range))

def SemiFredholmIndexFinite : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K],
  ∀ (T : H →L[𝕜] K) (h : IsFredholmValue T) (hs : IsSemiFredholmValue T),
    semiFredholmIndexValue T hs =
      ((fredholmIndexValue T h : WithTop ℤ) : ExtendedIndexValue)

def SemiFredholmIndexBot : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K],
  ∀ (T : H →L[𝕜] K) (h : IsSemiFredholmValue T),
    (¬ FiniteDimensional 𝕜 (K ⧸ T.range)) → semiFredholmIndexValue T h = ⊥

def SemiFredholmIndexTop : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K],
  ∀ (T : H →L[𝕜] K) (h : IsSemiFredholmValue T),
    (¬ FiniteDimensional 𝕜 T.ker) → semiFredholmIndexValue T h = ⊤

def CompactIdealMembership : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
  ∀ T : E →L[𝕜] E,
    T ∈ compactIdealValue 𝕜 E ↔
      Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap

def CompactIdealClosed : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
  ∀ [CompleteSpace E], IsClosed (compactIdealValue 𝕜 E : Set (E →L[𝕜] E))

def CalkinComplete : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
  ∀ [CompleteSpace E], CompleteSpace (CalkinValue 𝕜 E)

def CalkinProjectionSurjective : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
  Function.Surjective (calkinProjectionValue 𝕜 E)

def CalkinProjectionZero : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
  ∀ T : E →L[𝕜] E,
    calkinProjectionValue 𝕜 E T = 0 ↔
      Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap

def CalkinProjectionEquality : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
  ∀ S T : E →L[𝕜] E,
    calkinProjectionValue 𝕜 E S = calkinProjectionValue 𝕜 E T ↔
      Compactness.DefinitionsSpec.IsCompactLinearMapValue (S - T).toLinearMap

def CalkinProjectionMul : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
  ∀ S T : E →L[𝕜] E,
    calkinProjectionValue 𝕜 E (S * T) =
      calkinProjectionValue 𝕜 E S * calkinProjectionValue 𝕜 E T

def CalkinProjectionNorm : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
  ∀ T : E →L[𝕜] E,
    ‖calkinProjectionValue 𝕜 E T‖ =
      Metric.infDist T (compactIdealValue 𝕜 E : Set (E →L[𝕜] E))

def CalkinNormMulLe : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
  ∀ x y : CalkinValue 𝕜 E, ‖x * y‖ ≤ ‖x‖ * ‖y‖

end ExpandedFA.Fredholm.DefinitionsSpec
