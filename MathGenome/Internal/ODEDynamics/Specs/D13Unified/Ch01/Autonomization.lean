import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.AutonomousParameters

/-! Independent specification of paper.tex, Proposition d13:01:autonomization.
The original joint open domain is also the enlarged state domain. Actual
curves, rather than their arbitrary values outside an interval, are in bijection.
No existence, uniqueness or global solution selector is assumed. -/
noncomputable section
open Set

namespace D13Unified

/-- The original interval translated by `-s`, with every endpoint retained. -/
def TimeInterval.elapsed (I : TimeInterval) (s : ℝ) : TimeInterval where
  carrier := (fun h => s + h) ⁻¹' I.carrier
  nonempty := by
    obtain ⟨t, ht⟩ := I.nonempty
    exact ⟨t - s, by simpa using ht⟩
  ordConnected := I.ordConnected.preimage_mono (monotone_id.const_add s)

/-- The same translation retains openness for classical solutions. -/
def OpenTimeInterval.elapsed (I : OpenTimeInterval) (s : ℝ) : OpenTimeInterval where
  toTimeInterval := I.toTimeInterval.elapsed s
  isOpen := I.isOpen.preimage (continuous_const.add continuous_id)

/-- The clock and parameter are state coordinates; the domain is exactly the
original domain, including any dependence between its three coordinates. -/
def ParameterODE.autonomize {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : ParameterODE E P) : AutonomousODE ((ℝ × E) × P) where
  domain := F.domain
  isOpen_domain := F.isOpen_domain
  field := fun q => ((1, F.field q), 0)
  continuous_field := (continuous_const.prodMk F.continuous_field).prodMk continuous_const

/-- Lift an ambient representative by changing from absolute to elapsed time. -/
def autonomizationLift {E P : Type*} (s : ℝ) (p : P) (x : ℝ → E)
    (h : ℝ) : (ℝ × E) × P := ((s + h, x (s + h)), p)

/-- Recover the state curve in absolute time. -/
def autonomizationRecover {E P : Type*} (s : ℝ)
    (y : ℝ → (ℝ × E) × P) (t : ℝ) : E := (y (t - s)).1.2

/-- Curves on their actual domain with the shared IVP property. The existential
representative merely bridges Mathlib's ambient calculus to domain maps. -/
def ParameterIVPCurves {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : ParameterODE E P) (p : P) (I : TimeInterval) (s : ℝ) (ξ : E) :=
  {x : I.carrier → E // ∃ X : ℝ → E,
    Specs.D13Unified.Ch01.AutonomousParameters.parameterIVPOnValue F p I X s ξ ∧
    ∀ t : I.carrier, X t = x t}

/-- Every enlarged IVP curve is included, without prescribing the clock or
parameter in advance beyond their initial values. -/
def EnlargedIVPCurves {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : ParameterODE E P) (J : TimeInterval) (s : ℝ) (ξ : E) (p : P) :=
  {y : J.carrier → (ℝ × E) × P // ∃ Y : ℝ → (ℝ × E) × P,
    Specs.D13Unified.Ch01.AutonomousParameters.autonomousIVPOnValue
      F.autonomize J Y 0 ((s, ξ), p) ∧ ∀ h : J.carrier, Y h = y h}

end D13Unified

namespace Specs.D13Unified.Ch01.Autonomization
open _root_.D13Unified
open AutonomousParameters
universe u v

/-- Both directions of the differential correspondence, including initial data
and within derivatives at included endpoints. -/
def liftIffExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : ParameterODE E P) (p : P) (I : TimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E),
    parameterIVPOnValue F p I x s ξ ↔
      autonomousIVPOnValue F.autonomize (I.elapsed s)
        (autonomizationLift s p x) 0 ((s, ξ), p)

/-- Arbitrary enlarged solutions have the asserted clock and constant parameter;
the middle component recovers an original solution on exactly `I`. -/
def recoverExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P) (p : P) (I : TimeInterval)
    (y : ℝ → (ℝ × E) × P) (s : ℝ) (ξ : E),
    autonomousIVPOnValue F.autonomize (I.elapsed s) y 0 ((s, ξ), p) →
    parameterIVPOnValue F p I (autonomizationRecover s y) s ξ ∧
      ∀ h ∈ (I.elapsed s).carrier, (y h).1.1 = s + h ∧ (y h).2 = p

/-- A genuine bijection of curves on their domains, with explicit formulas in
both directions. This applies to every nonempty interval, including singletons,
compact intervals and unbounded intervals, without a uniqueness assumption. -/
def bijectionExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P) (p : P) (I : TimeInterval) (s : ℝ) (ξ : E),
    ∃ e : ParameterIVPCurves F p I s ξ ≃ EnlargedIVPCurves F (I.elapsed s) s ξ p,
      (∀ x h, (e x).val h = ((s + h.val, x.val ⟨s + h.val, h.property⟩), p)) ∧
      (∀ y (t : I.carrier), (e.symm y).val t =
        (y.val ⟨t.val - s, by simpa [TimeInterval.elapsed] using t.property⟩).1.2)

/-- C¹ classical solutions on nonempty open intervals correspond as well. -/
def classicalLiftIffExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : ParameterODE E P) (p : P) (I : OpenTimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E),
    classicalParameterIVPOnValue F p I x s ξ ↔
      classicalAutonomousIVPOnValue F.autonomize (I.elapsed s)
        (autonomizationLift s p x) 0 ((s, ξ), p)

/-- Once an original IVP curve is uniquely specified (in particular by a later
solution map Φ), the enlarged middle component has exactly those values at
absolute time `s+h`, throughout precisely the translated interval. -/
def uniqueValuesExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P) (p : P) (I : TimeInterval) (s : ℝ) (ξ : E) (x : ℝ → E),
    (∀ z : ℝ → E, parameterIVPOnValue F p I z s ξ → EqOn z x I.carrier) →
    ∀ y : ℝ → (ℝ × E) × P,
      autonomousIVPOnValue F.autonomize (I.elapsed s) y 0 ((s, ξ), p) →
      EqOn y (autonomizationLift s p x) (I.elapsed s).carrier

end Specs.D13Unified.Ch01.Autonomization
