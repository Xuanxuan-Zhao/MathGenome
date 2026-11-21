import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.ZeroDerivative

/-!
Independent specification of K03.09.primitive and K03.09.uniqueness,
paper.tex:2341–2364. Functions on a real set are represented by ambient
extensions, as in the upstream derivative interface. The primitive condition
tests only interior points. It neither requires continuity of the integrand
nor an endpoint derivative. Endpoint continuity is a separate condition for
uniqueness on intervals with included endpoints. On open sets it follows from
the primitive condition itself.

`primitiveFamilyValue` is a set of functions, the indefinite integral. It
does not assign a scalar definite-integral value or assert integrability.
The open-interval family characterizations use equality on the domain, so
arbitrary ambient extensions outside that domain are retained.
-/

namespace Specs.SingleVariableAnalysis.Ch09.Primitive

open Set
universe u

def isPrimitiveOnType : Type (u + 1) :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] →
    (ℝ → E) → (ℝ → E) → Set ℝ → Prop

def isPrimitiveOnValue : isPrimitiveOnType.{u} :=
  fun F f I => ∀ x ∈ interior I, HasDerivAt F (f x) x

def continuousPrimitiveOnType : Type (u + 1) := isPrimitiveOnType.{u}

def continuousPrimitiveOnValue : continuousPrimitiveOnType.{u} :=
  fun F f I => ContinuousOn F I ∧ isPrimitiveOnValue F f I

def primitiveFamilyType : Type (u + 1) :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] →
    (ℝ → E) → Set ℝ → Set (ℝ → E)

def primitiveFamilyValue : primitiveFamilyType.{u} :=
  fun f I => {F | isPrimitiveOnValue F f I}

def primitiveOnOpenIff : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F f : ℝ → E) (I : Set ℝ), IsOpen I →
    (isPrimitiveOnValue F f I ↔ ∀ x ∈ I, HasDerivAt F (f x) x)

def primitiveIffDifferentiableDeriv : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F f : ℝ → E) (I : Set ℝ),
    isPrimitiveOnValue F f I ↔
      (∀ x ∈ interior I, DifferentiableAt ℝ F x) ∧
      (∀ x ∈ interior I, deriv F x = f x)

def primitiveIffIncrement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F f : ℝ → E) (I : Set ℝ),
    isPrimitiveOnValue F f I ↔ ∀ x ∈ interior I,
      Ch04.Derivative.hasRealIncrementDerivativeValue F (f x) x

def continuousPrimitiveOnOpenIff : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F f : ℝ → E) (I : Set ℝ), IsOpen I →
    (continuousPrimitiveOnValue F f I ↔ isPrimitiveOnValue F f I)

def continuousPrimitiveIffEndpoints : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F f : ℝ → E) (I : Set ℝ),
    continuousPrimitiveOnValue F f I ↔
      isPrimitiveOnValue F f I ∧
        ∀ x ∈ I, x ∉ interior I → ContinuousWithinAt F I x

def primitiveAddConstant : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F f : ℝ → E) (I : Set ℝ) (c : E),
    isPrimitiveOnValue F f I → isPrimitiveOnValue (fun x => F x + c) f I

def realPrimitivesDifferByConstant : Prop :=
  ∀ (F G f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected →
    continuousPrimitiveOnValue F f I → continuousPrimitiveOnValue G f I →
    ∃ c : ℝ, ∀ x ∈ I, F x - G x = c

def complexPrimitivesDifferByConstant : Prop :=
  ∀ (F G f : ℝ → ℂ) (I : Set ℝ), I.OrdConnected →
    continuousPrimitiveOnValue F f I → continuousPrimitiveOnValue G f I →
    ∃ c : ℂ, ∀ x ∈ I, F x - G x = c

def realOpenPrimitivesDifferByConstant : Prop :=
  ∀ (F G f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → IsOpen I →
    isPrimitiveOnValue F f I → isPrimitiveOnValue G f I →
    ∃ c : ℝ, ∀ x ∈ I, F x - G x = c

def complexOpenPrimitivesDifferByConstant : Prop :=
  ∀ (F G f : ℝ → ℂ) (I : Set ℝ), I.OrdConnected → IsOpen I →
    isPrimitiveOnValue F f I → isPrimitiveOnValue G f I →
    ∃ c : ℂ, ∀ x ∈ I, F x - G x = c

def realPrimitiveFamilyIffAddConstant : Prop :=
  ∀ (F G f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → IsOpen I →
    isPrimitiveOnValue F f I →
    (G ∈ primitiveFamilyValue f I ↔ ∃ c : ℝ, ∀ x ∈ I, G x = F x + c)

def complexPrimitiveFamilyIffAddConstant : Prop :=
  ∀ (F G f : ℝ → ℂ) (I : Set ℝ), I.OrdConnected → IsOpen I →
    isPrimitiveOnValue F f I →
    (G ∈ primitiveFamilyValue f I ↔ ∃ c : ℂ, ∀ x ∈ I, G x = F x + c)

def disconnectedPrimitiveExample : Prop :=
  let I : Set ℝ := Iio 0 ∪ Ioi 0
  let F : ℝ → ℝ := fun x => if x < 0 then 0 else 1
  let G : ℝ → ℝ := fun _ => 0
  continuousPrimitiveOnValue F G I ∧ continuousPrimitiveOnValue G G I ∧
    (∀ x : ℝ, x < 0 → F x = 0) ∧ (∀ x : ℝ, 0 < x → F x = 1) ∧
    ¬ (∃ c : ℝ, ∀ x ∈ I, F x - G x = c)

end Specs.SingleVariableAnalysis.Ch09.Primitive
