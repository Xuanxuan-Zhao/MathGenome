import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.RelativeLimit

/-!
Independent specification for K03.02.one_sided (paper.tex:378–385).
Input approaches are real. Finite outputs may be any metric space, in particular
exactly the source scalars ℝ and ℂ with their usual metrics. An ambient function
represents a function on E by testing only points of E. One-sided limits
require side accumulation, and infinite-input limits require directional
unboundedness. Ordinary punctured infinite-output limits permit vacuity.
`finiteApproachLimitValue` is a separate nontrivial finite-limit wrapper;
ordinary punctured finite limits are specified in RelativeLimit. Infinite output
limits use all real thresholds; no order is imposed on complex values.
-/

namespace SingleVariableAnalysis

/-- The five approaches used in the manuscript. -/
inductive RealApproach where
  | punctured (a : ℝ)
  | right (a : ℝ)
  | left (a : ℝ)
  | posInfinity
  | negInfinity

end SingleVariableAnalysis

namespace Specs.SingleVariableAnalysis.Ch02.OneSided

open _root_.SingleVariableAnalysis
universe u

def approachRegionType : Type :=
  RealApproach → ℝ → Set ℝ

def approachRegionValue : approachRegionType :=
  fun q r => match q with
  | .punctured a => {x | 0 < |x - a| ∧ |x - a| < r}
  | .right a => Set.Ioo a (a + r)
  | .left a => Set.Ioo (a - r) a
  | .posInfinity => Set.Ioi r
  | .negInfinity => Set.Iio (-r)

def approachNontrivialType : Type :=
  Set ℝ → RealApproach → Prop

def approachNontrivialValue : approachNontrivialType :=
  fun E q => ∀ r : ℝ, 0 < r → ∃ x ∈ E, x ∈ approachRegionValue q r

def approachEventuallyType : Type :=
  Set ℝ → RealApproach → (ℝ → Prop) → Prop

def approachEventuallyValue : approachEventuallyType :=
  fun E q P => ∃ r : ℝ, 0 < r ∧ ∀ x ∈ E, x ∈ approachRegionValue q r → P x

def rightAccumulationType : Type :=
  Set ℝ → ℝ → Prop

def rightAccumulationValue : rightAccumulationType :=
  fun E a => approachNontrivialValue E (.right a)

def leftAccumulationType : Type :=
  Set ℝ → ℝ → Prop

def leftAccumulationValue : leftAccumulationType :=
  fun E a => approachNontrivialValue E (.left a)

def domainUnboundedAboveType : Type :=
  Set ℝ → Prop

def domainUnboundedAboveValue : domainUnboundedAboveType :=
  fun E => approachNontrivialValue E .posInfinity

def domainUnboundedBelowType : Type :=
  Set ℝ → Prop

def domainUnboundedBelowValue : domainUnboundedBelowType :=
  fun E => approachNontrivialValue E .negInfinity

def approachAdmissibleType : Type :=
  Set ℝ → RealApproach → Prop

def approachAdmissibleValue : approachAdmissibleType :=
  fun E q => match q with
  | .punctured _ => True
  | .right a => rightAccumulationValue E a
  | .left a => leftAccumulationValue E a
  | .posInfinity => domainUnboundedAboveValue E
  | .negInfinity => domainUnboundedBelowValue E

def finiteApproachLimitType : Type (u + 1) :=
  {Y : Type u} → [MetricSpace Y] → (ℝ → Y) → Set ℝ → RealApproach → Y → Prop

def finiteApproachLimitValue : finiteApproachLimitType.{u} :=
  fun f E q L => approachNontrivialValue E q ∧
    ∀ ε : ℝ, 0 < ε → approachEventuallyValue E q (fun x => dist (f x) L < ε)

def rightRelativeLimitType : Type (u + 1) :=
  {Y : Type u} → [MetricSpace Y] → (ℝ → Y) → Set ℝ → ℝ → Y → Prop

def rightRelativeLimitValue : rightRelativeLimitType.{u} :=
  fun f E a L => finiteApproachLimitValue f E (.right a) L

def leftRelativeLimitType : Type (u + 1) :=
  {Y : Type u} → [MetricSpace Y] → (ℝ → Y) → Set ℝ → ℝ → Y → Prop

def leftRelativeLimitValue : leftRelativeLimitType.{u} :=
  fun f E a L => finiteApproachLimitValue f E (.left a) L

def limitAtPosInfinityType : Type (u + 1) :=
  {Y : Type u} → [MetricSpace Y] → (ℝ → Y) → Set ℝ → Y → Prop

def limitAtPosInfinityValue : limitAtPosInfinityType.{u} :=
  fun f E L => finiteApproachLimitValue f E .posInfinity L

def limitAtNegInfinityType : Type (u + 1) :=
  {Y : Type u} → [MetricSpace Y] → (ℝ → Y) → Set ℝ → Y → Prop

def limitAtNegInfinityValue : limitAtNegInfinityType.{u} :=
  fun f E L => finiteApproachLimitValue f E .negInfinity L

def realLimitToPosInfinityType : Type :=
  (ℝ → ℝ) → Set ℝ → RealApproach → Prop

def realLimitToPosInfinityValue : realLimitToPosInfinityType :=
  fun f E q => approachAdmissibleValue E q ∧ ∀ B : ℝ, approachEventuallyValue E q (fun x => B < f x)

def realLimitToNegInfinityType : Type :=
  (ℝ → ℝ) → Set ℝ → RealApproach → Prop

def realLimitToNegInfinityValue : realLimitToNegInfinityType :=
  fun f E q => approachAdmissibleValue E q ∧ ∀ B : ℝ, approachEventuallyValue E q (fun x => f x < B)

def complexModulusLimitToInfinityType : Type :=
  (ℝ → ℂ) → Set ℝ → RealApproach → Prop

def complexModulusLimitToInfinityValue : complexModulusLimitToInfinityType :=
  fun f E q => approachAdmissibleValue E q ∧ ∀ B : ℝ, approachEventuallyValue E q (fun x => B < ‖f x‖)

def realLimitToPosInfinityPuncturedIff : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (a : ℝ),
    realLimitToPosInfinityValue f E (.punctured a) ↔
      ∀ B : ℝ, ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, 0 < |x - a| ∧ |x - a| < δ → B < f x

def realLimitToNegInfinityPuncturedIff : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (a : ℝ),
    realLimitToNegInfinityValue f E (.punctured a) ↔
      ∀ B : ℝ, ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, 0 < |x - a| ∧ |x - a| < δ → f x < B

def complexModulusLimitToInfinityPuncturedIff : Prop :=
  ∀ (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ),
    complexModulusLimitToInfinityValue f E (.punctured a) ↔
      ∀ B : ℝ, ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, 0 < |x - a| ∧ |x - a| < δ → B < ‖f x‖

def infiniteOutputLimitsSingleton : Prop :=
  ∀ (f : ℝ → ℝ) (g : ℝ → ℂ) (a : ℝ),
    realLimitToPosInfinityValue f {a} (.punctured a) ∧
      realLimitToNegInfinityValue f {a} (.punctured a) ∧
      complexModulusLimitToInfinityValue g {a} (.punctured a)

def rightAccumulationIff : Prop :=
  ∀ (E : Set ℝ) (a : ℝ), rightAccumulationValue E a ↔
    ∀ δ : ℝ, 0 < δ → ∃ x ∈ E, a < x ∧ x < a + δ

def leftAccumulationIff : Prop :=
  ∀ (E : Set ℝ) (a : ℝ), leftAccumulationValue E a ↔
    ∀ δ : ℝ, 0 < δ → ∃ x ∈ E, a - δ < x ∧ x < a

def domainUnboundedAboveIff : Prop :=
  ∀ E : Set ℝ, domainUnboundedAboveValue E ↔
    ∀ B : ℝ, ∃ x ∈ E, B < x

def domainUnboundedBelowIff : Prop :=
  ∀ E : Set ℝ, domainUnboundedBelowValue E ↔
    ∀ B : ℝ, ∃ x ∈ E, x < B

def domainUnboundedAboveNotBddAbove : Prop :=
  ∀ E : Set ℝ,
    domainUnboundedAboveValue E ↔ ¬ BddAbove E

def domainUnboundedBelowNotBddBelow : Prop :=
  ∀ E : Set ℝ,
    domainUnboundedBelowValue E ↔ ¬ BddBelow E

def rightAccumulationDomainIff : Prop :=
  ∀ (E : Set ℝ) (a : ℝ),
    rightAccumulationValue E a ↔ Specs.SingleVariableAnalysis.Ch02.RelativeLimit.domainAccumulationValue (E ∩ Set.Ioi a) a

def leftAccumulationDomainIff : Prop :=
  ∀ (E : Set ℝ) (a : ℝ),
    leftAccumulationValue E a ↔ Specs.SingleVariableAnalysis.Ch02.RelativeLimit.domainAccumulationValue (E ∩ Set.Iio a) a

def rightRelativeLimitIff : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y),
    rightRelativeLimitValue f E a L ↔ rightAccumulationValue E a ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, a < x → x < a + δ → dist (f x) L < ε

def leftRelativeLimitIff : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y),
    leftRelativeLimitValue f E a L ↔ leftAccumulationValue E a ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, a - δ < x → x < a → dist (f x) L < ε

def rightRelativeLimitRelativeIff : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y),
    rightRelativeLimitValue f E a L ↔ rightAccumulationValue E a ∧
      Specs.SingleVariableAnalysis.Ch02.RelativeLimit.relativePuncturedLimitValue f (E ∩ Set.Ioi a) a L

def leftRelativeLimitRelativeIff : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y),
    leftRelativeLimitValue f E a L ↔ leftAccumulationValue E a ∧
      Specs.SingleVariableAnalysis.Ch02.RelativeLimit.relativePuncturedLimitValue f (E ∩ Set.Iio a) a L

def limitAtPosInfinityIff : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (L : Y),
    limitAtPosInfinityValue f E L ↔ domainUnboundedAboveValue E ∧
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ x ∈ E, A < x → dist (f x) L < ε

def limitAtNegInfinityIff : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (L : Y),
    limitAtNegInfinityValue f E L ↔ domainUnboundedBelowValue E ∧
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ x ∈ E, x < -A → dist (f x) L < ε

def realFiniteApproachLimitIff : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (q : RealApproach) (L : ℝ),
    finiteApproachLimitValue f E q L ↔ approachNontrivialValue E q ∧
      ∀ ε : ℝ, 0 < ε → approachEventuallyValue E q (fun x => |f x - L| < ε)

def complexFiniteApproachLimitIff : Prop :=
  ∀ (f : ℝ → ℂ) (E : Set ℝ) (q : RealApproach) (L : ℂ),
    finiteApproachLimitValue f E q L ↔ approachNontrivialValue E q ∧
      ∀ ε : ℝ, 0 < ε → approachEventuallyValue E q (fun x => ‖f x - L‖ < ε)

def relativePuncturedLimitIffOneSided : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ) (L : Y),
    rightAccumulationValue E a → leftAccumulationValue E a →
      (Specs.SingleVariableAnalysis.Ch02.RelativeLimit.relativePuncturedLimitValue f E a L ↔
        rightRelativeLimitValue f E a L ∧ leftRelativeLimitValue f E a L)

def finiteLimitExistsIffOneSidedAgree : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ) (a : ℝ),
    rightAccumulationValue E a → leftAccumulationValue E a →
      ((∃ L : Y, Specs.SingleVariableAnalysis.Ch02.RelativeLimit.relativePuncturedLimitValue f E a L) ↔
        ∃ L : Y, rightRelativeLimitValue f E a L ∧ leftRelativeLimitValue f E a L)

def positiveDomainZeroRightAccumulation : Prop :=
  rightAccumulationValue (Set.Ioi (0 : ℝ)) 0

def positiveDomainZeroNotLeftAccumulation : Prop :=
  ¬ leftAccumulationValue (Set.Ioi (0 : ℝ)) 0

def positiveDomainZeroRelativeIffRight : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (L : Y),
    Specs.SingleVariableAnalysis.Ch02.RelativeLimit.relativePuncturedLimitValue f (Set.Ioi 0) 0 L ↔
      rightRelativeLimitValue f (Set.Ioi 0) 0 L

def positiveDomainZeroNoLeftLimit : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (L : Y),
    ¬ leftRelativeLimitValue f (Set.Ioi 0) 0 L

end Specs.SingleVariableAnalysis.Ch02.OneSided
