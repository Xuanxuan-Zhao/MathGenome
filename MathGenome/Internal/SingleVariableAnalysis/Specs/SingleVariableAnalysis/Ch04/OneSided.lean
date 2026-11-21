import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided

/-!
Independent specification of K03.04.one_sided (paper.tex:649–660).
Functions on I use the upstream ambient-extension representation. Availability
requires a ∈ I and an actual open interval on the chosen side, not merely an
accumulation point. All increments are real; all derivative values are finite.
The normed real target includes both ℝ and ℂ. Endpoint conventions are stated
only as one-sided/within statements, never as ordinary derivatives.
-/
namespace Specs.SingleVariableAnalysis.Ch04.OneSided
open scoped Topology
universe u

def sideIntervalAvailableType : Type := Set ℝ → ℝ → Prop

def rightIntervalAvailableValue : sideIntervalAvailableType :=
  fun I a => a ∈ I ∧ ∃ r : ℝ, 0 < r ∧ Set.Ioo a (a + r) ⊆ I

def leftIntervalAvailableValue : sideIntervalAvailableType :=
  fun I a => a ∈ I ∧ ∃ r : ℝ, 0 < r ∧ Set.Ioo (a - r) a ⊆ I

def oneSidedDerivativeWithinType : Type (u + 1) :=
  {F : Type u} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
    (ℝ → F) → F → Set ℝ → ℝ → Prop

def hasRightRealIncrementDerivativeWithinValue : oneSidedDerivativeWithinType.{u} :=
  fun f L I a => rightIntervalAvailableValue I a ∧
    Ch02.OneSided.rightRelativeLimitValue
      (Derivative.realIncrementQuotientValue f a) {h : ℝ | a + h ∈ I} 0 L

def hasLeftRealIncrementDerivativeWithinValue : oneSidedDerivativeWithinType.{u} :=
  fun f L I a => leftIntervalAvailableValue I a ∧
    Ch02.OneSided.leftRelativeLimitValue
      (Derivative.realIncrementQuotientValue f a) {h : ℝ | a + h ∈ I} 0 L

def interiorSideIntervals : Prop :=
  ∀ (I : Set ℝ) (a : ℝ), a ∈ interior I →
    rightIntervalAvailableValue I a ∧ leftIntervalAvailableValue I a

def rightDerivativeEpsilonIff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ),
    hasRightRealIncrementDerivativeWithinValue f L I a ↔
      rightIntervalAvailableValue I a ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, a + h ∈ I → 0 < h → h < δ →
          ‖Derivative.realIncrementQuotientValue f a h - L‖ < ε

def leftDerivativeEpsilonIff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ),
    hasLeftRealIncrementDerivativeWithinValue f L I a ↔
      leftIntervalAvailableValue I a ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, a + h ∈ I → -δ < h → h < 0 →
          ‖Derivative.realIncrementQuotientValue f a h - L‖ < ε

def withinDerivativeIffOneSided : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ),
    rightIntervalAvailableValue I a → leftIntervalAvailableValue I a →
    (Derivative.hasRealIncrementDerivativeWithinValue f L I a ↔
      hasRightRealIncrementDerivativeWithinValue f L I a ∧
      hasLeftRealIncrementDerivativeWithinValue f L I a)

def interiorDerivativeIffOneSided : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    (HasDerivAt f L a ↔ hasRightRealIncrementDerivativeWithinValue f L I a ∧
      hasLeftRealIncrementDerivativeWithinValue f L I a)

def finiteDerivativeExistsIffOneSidedAgree : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    ((∃ L : F, Derivative.hasRealIncrementDerivativeWithinValue f L I a) ↔
      ∃ L R : F, hasLeftRealIncrementDerivativeWithinValue f L I a ∧
        hasRightRealIncrementDerivativeWithinValue f R I a ∧ L = R)

def differentiableAtIffOneSidedAgree : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    (DifferentiableAt ℝ f a ↔
      ∃ L R : F, hasLeftRealIncrementDerivativeWithinValue f L I a ∧
        hasRightRealIncrementDerivativeWithinValue f R I a ∧ L = R)

def rightDerivativeUnique : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L M : F) (I : Set ℝ) (a : ℝ),
    hasRightRealIncrementDerivativeWithinValue f L I a →
    hasRightRealIncrementDerivativeWithinValue f M I a → L = M

def leftDerivativeUnique : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L M : F) (I : Set ℝ) (a : ℝ),
    hasLeftRealIncrementDerivativeWithinValue f L I a →
    hasLeftRealIncrementDerivativeWithinValue f M I a → L = M

def rightDerivativeCongr : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ), Set.EqOn f g I →
    (hasRightRealIncrementDerivativeWithinValue f L I a ↔
      hasRightRealIncrementDerivativeWithinValue g L I a)

def leftDerivativeCongr : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ), Set.EqOn f g I →
    (hasLeftRealIncrementDerivativeWithinValue f L I a ↔
      hasLeftRealIncrementDerivativeWithinValue g L I a)

/-- On any domain lying to the right of a, only the right convention applies. -/
def leftEndpointDerivativeIff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ),
    rightIntervalAvailableValue I a → I ⊆ Set.Ici a →
    (Derivative.hasRealIncrementDerivativeWithinValue f L I a ↔
      hasRightRealIncrementDerivativeWithinValue f L I a)

def rightEndpointDerivativeIff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ),
    leftIntervalAvailableValue I a → I ⊆ Set.Iic a →
    (Derivative.hasRealIncrementDerivativeWithinValue f L I a ↔
      hasLeftRealIncrementDerivativeWithinValue f L I a)

def closedIntervalLeftEndpointIff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (a b : ℝ), a < b →
    (Derivative.hasRealIncrementDerivativeWithinValue f L (Set.Icc a b) a ↔
      hasRightRealIncrementDerivativeWithinValue f L (Set.Icc a b) a)

def closedIntervalRightEndpointIff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (a b : ℝ), a < b →
    (Derivative.hasRealIncrementDerivativeWithinValue f L (Set.Icc a b) b ↔
      hasLeftRealIncrementDerivativeWithinValue f L (Set.Icc a b) b)

def closedIntervalUnavailableSides : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (a b : ℝ),
    ¬ hasLeftRealIncrementDerivativeWithinValue f L (Set.Icc a b) a ∧
    ¬ hasRightRealIncrementDerivativeWithinValue f L (Set.Icc a b) b

end Specs.SingleVariableAnalysis.Ch04.OneSided
