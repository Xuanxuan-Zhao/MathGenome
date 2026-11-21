import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.MaximalSolution

/-! Canonical choices and actual domains for paper.tex, d13:04:maximal and
 d13:05:openness. Only upstream Specs are imported. The conditional choice below
 uses an existential proposition, not an assumed existence certificate. Its
 successful branch is established by the previously proved existence theorem in
 the implementation. No continuity or openness in the initial data is asserted
 here; those are the separate Chapter 5 obligations. -/
noncomputable section
open Set
open D13Unified

namespace D13Unified

/-- Raw data for a chosen curve and its actual interval. Correctness is proved
 separately; the ambient curve has no meaning off its recorded interval. -/
structure MaximalSolutionData (E : Type*) where
  interval : OpenTimeInterval
  curve : ℝ → E
  lower : EReal
  upper : EReal

end D13Unified

namespace Specs.D13Unified.Ch04.MaximalSolutionMap
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch03.LocalLipschitz
open Specs.D13Unified.Ch04.MaximalSolution
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- One choice, made from the full maximal-through proposition. In the unused
 branch the interval and curve are defaults; no solution is asserted there. -/
def maximalDataValue (F : ODE E) (s : ℝ) (ξ : E) : MaximalSolutionData E := by
  classical
  exact if h : MaximalThrough F s ξ then
    let x := Classical.choose h
    let he := (Classical.choose_spec h).2.2.2.1
    { interval := x.interval
      curve := x.representative
      lower := Classical.choose he
      upper := Classical.choose (Classical.choose_spec he) }
  else
    { interval := ⟨⟨univ, univ_nonempty, ordConnected_univ⟩, isOpen_univ⟩
      curve := fun _ => 0
      lower := ⊥
      upper := ⊤ }

def maximalIntervalValue (F : ODE E) (s : ℝ) (ξ : E) : OpenTimeInterval :=
  (maximalDataValue F s ξ).interval

def solutionCurveValue (F : ODE E) (s : ℝ) (ξ : E) : ℝ → E :=
  (maximalDataValue F s ξ).curve

def lowerEndpointValue (F : ODE E) (s : ℝ) (ξ : E) : EReal :=
  (maximalDataValue F s ξ).lower

def upperEndpointValue (F : ODE E) (s : ℝ) (ξ : E) : EReal :=
  (maximalDataValue F s ξ).upper

/-- Coordinates are `(t,(s,ξ))`; admissibility is part of the domain. -/
def solutionDomainValue (F : ODE E) : Set (ℝ × (ℝ × E)) :=
  {q | q.2 ∈ F.domain ∧ q.1 ∈ (maximalIntervalValue F q.2.1 q.2.2).carrier}

/-- Zero outside the actual solution domain is purely a totalization convention. -/
def solutionValueValue (F : ODE E) (t s : ℝ) (ξ : E) : E := by
  classical
  exact if (t, (s, ξ)) ∈ solutionDomainValue F then solutionCurveValue F s ξ t else 0

/-- The solution map on its actual domain. -/
def solutionMapValue (F : ODE E) : solutionDomainValue F → E :=
  fun q => solutionValueValue F q.val.1 q.val.2.1 q.val.2.2

/-- Parameterized objects use precisely the fixed-parameter slice, so they
 share the same choices with the unparameterized construction. -/
def parameterMaximalDataValue (F : ParameterODE E P) (s : ℝ) (ξ : E) (p : P) :
    MaximalSolutionData E := maximalDataValue (atParameterValue F p) s ξ

def parameterMaximalIntervalValue (F : ParameterODE E P) (s : ℝ) (ξ : E) (p : P) :
    OpenTimeInterval := maximalIntervalValue (atParameterValue F p) s ξ

def parameterSolutionCurveValue (F : ParameterODE E P) (s : ℝ) (ξ : E) (p : P) :
    ℝ → E := solutionCurveValue (atParameterValue F p) s ξ

def parameterLowerEndpointValue (F : ParameterODE E P) (s : ℝ) (ξ : E) (p : P) :
    EReal := lowerEndpointValue (atParameterValue F p) s ξ

def parameterUpperEndpointValue (F : ParameterODE E P) (s : ℝ) (ξ : E) (p : P) :
    EReal := upperEndpointValue (atParameterValue F p) s ξ

/-- Coordinates are `(t,((s,ξ),p))`, with the original triple domain retained. -/
def parameterSolutionDomainValue (F : ParameterODE E P) : Set (ℝ × ((ℝ × E) × P)) :=
  {q | q.2 ∈ F.domain ∧
    q.1 ∈ (parameterMaximalIntervalValue F q.2.1.1 q.2.1.2 q.2.2).carrier}

def parameterSolutionValueValue (F : ParameterODE E P) (t s : ℝ) (ξ : E) (p : P) : E :=
  solutionValueValue (atParameterValue F p) t s ξ

def parameterSolutionMapValue (F : ParameterODE E P) : parameterSolutionDomainValue F → E :=
  fun q => parameterSolutionValueValue F q.val.1 q.val.2.1.1 q.val.2.1.2 q.val.2.2

/-- Correctness of a specific record, retaining C¹ regularity, the actual
 domain, initial data, maximality, endpoint representation, restriction to
 every competitor, and uniqueness among maximal solutions. -/
def DataCorrect (F : ODE E) (s : ℝ) (ξ : E) (d : MaximalSolutionData E) : Prop :=
  ∃ hx : classicalSolutionOnValue F d.interval d.curve,
    s ∈ d.interval.carrier ∧ d.curve s = ξ ∧
    maximalValue (⟨d.interval, d.curve, hx⟩ : Solution F) ∧
    (d.lower < (s : EReal) ∧ (s : EReal) < d.upper ∧
      d.interval.carrier = {t : ℝ | d.lower < (t : EReal) ∧ (t : EReal) < d.upper}) ∧
    (∀ (J : OpenTimeInterval) (y : ℝ → E), classicalIVPOnValue F J y s ξ →
      J.carrier ⊆ d.interval.carrier ∧ EqOn d.curve y J.carrier) ∧
    (∀ y : Solution F, s ∈ y.interval.carrier → y.representative s = ξ →
      maximalValue y → y.interval.carrier = d.interval.carrier ∧
        EqOn y.representative d.curve y.interval.carrier)

def canonicalSolutionExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), locallyLipschitzInStateValue F →
    ∀ s ξ, (s, ξ) ∈ F.domain → DataCorrect F s ξ (maximalDataValue F s ξ)

def parameterCanonicalSolutionExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), parameterLocallyLipschitzInStateValue F →
    ∀ s ξ p, ((s, ξ), p) ∈ F.domain →
      DataCorrect (atParameterValue F p) s ξ (parameterMaximalDataValue F s ξ p)

/-- The totalized value agrees with the chosen curve on D and its graph stays
 in the original domain there. This is asserted only for admissible data. -/
def solutionValueExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), locallyLipschitzInStateValue F →
    ∀ t s ξ, (t, (s, ξ)) ∈ solutionDomainValue F →
      solutionValueValue F t s ξ = solutionCurveValue F s ξ t ∧
      (t, solutionValueValue F t s ξ) ∈ F.domain

def parameterSolutionValueExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), parameterLocallyLipschitzInStateValue F →
    ∀ t s ξ p, (t, ((s, ξ), p)) ∈ parameterSolutionDomainValue F →
      parameterSolutionValueValue F t s ξ p = parameterSolutionCurveValue F s ξ p t ∧
      ((t, parameterSolutionValueValue F t s ξ p), p) ∈ F.domain


def maximalDataExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    ODE E → ℝ → E → MaximalSolutionData E

def maximalIntervalExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    ODE E → ℝ → E → OpenTimeInterval

def solutionCurveExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    ODE E → ℝ → E → ℝ → E

def lowerEndpointExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    ODE E → ℝ → E → EReal

def upperEndpointExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    ODE E → ℝ → E → EReal

def solutionValueExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    ODE E → ℝ → ℝ → E → E

def solutionDomainExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    (F : ODE E) → Set (ℝ × (ℝ × E))

def solutionMapExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    (F : ODE E) → solutionDomainValue F → E

def parameterMaximalDataExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
    ParameterODE E P → ℝ → E → P → MaximalSolutionData E

def parameterMaximalIntervalExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
    ParameterODE E P → ℝ → E → P → OpenTimeInterval

def parameterSolutionCurveExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
    ParameterODE E P → ℝ → E → P → ℝ → E

def parameterLowerEndpointExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
    ParameterODE E P → ℝ → E → P → EReal

def parameterUpperEndpointExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
    ParameterODE E P → ℝ → E → P → EReal

def parameterSolutionValueExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
    ParameterODE E P → ℝ → ℝ → E → P → E

def parameterSolutionDomainExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
    (F : ParameterODE E P) → Set (ℝ × ((ℝ × E) × P))

def parameterSolutionMapExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
    (F : ParameterODE E P) → parameterSolutionDomainValue F → E

/-- The totalized Φ itself represents the classical IVP on its actual interval. -/
def solutionValueIVPExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), locallyLipschitzInStateValue F →
    ∀ s ξ, (s, ξ) ∈ F.domain →
      classicalIVPOnValue F (maximalIntervalValue F s ξ)
        (fun t => solutionValueValue F t s ξ) s ξ

def parameterSolutionValueIVPExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), parameterLocallyLipschitzInStateValue F →
    ∀ s ξ p, ((s, ξ), p) ∈ F.domain →
      classicalParameterIVPOnValue F p (parameterMaximalIntervalValue F s ξ p)
        (fun t => parameterSolutionValueValue F t s ξ p) s ξ

end Specs.D13Unified.Ch04.MaximalSolutionMap
