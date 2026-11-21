import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts

/-!
Independent specification for paper.tex, Chapter 1, d13:01:autonomous.
The constructions work on real normed spaces, and in particular on arbitrary
finite-dimensional state and parameter spaces with any fixed norm.
An ambient representative of a curve still has the actual interval recorded
separately. No existence, uniqueness, maximality, or solution value Φ is assumed.
-/

noncomputable section
open Set

namespace D13Unified

/-- A continuous autonomous equation on an actual open state domain Ω. -/
structure AutonomousODE (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  domain : Set E
  isOpen_domain : IsOpen domain
  field : domain → E
  continuous_field : Continuous field

/-- A continuous parameter-dependent equation on an actual open set of triples.
Triples are associated as `((t,x),p)`. The allowed time-state pairs may depend
on the parameter; the domain need not be a product. -/
structure ParameterODE (E P : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] where
  domain : Set ((ℝ × E) × P)
  isOpen_domain : IsOpen domain
  field : domain → E
  continuous_field : Continuous field

end D13Unified

namespace Specs.D13Unified.Ch01.AutonomousParameters
open _root_.D13Unified
open Specs.D13Unified.Ch01.SolutionConcepts

universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Evaluation outside Ω is only a convention; solutions must stay in Ω. -/
def autonomousEvalValue (F : AutonomousODE E) (x : E) : E := by
  classical
  exact if h : x ∈ F.domain then F.field ⟨x, h⟩ else 0

/-- Evaluation outside the given triple domain is only a convention. -/
def parameterEvalValue (F : ParameterODE E P) (t : ℝ) (x : E) (p : P) : E := by
  classical
  exact if h : ((t, x), p) ∈ F.domain then F.field ⟨((t, x), p), h⟩ else 0

/-- The autonomous equation as a shared ODE, on exactly ℝ × Ω. -/
def autonomousToODEValue (F : AutonomousODE E) : ODE E where
  domain := Prod.snd ⁻¹' F.domain
  isOpen_domain := F.isOpen_domain.preimage continuous_snd
  field := fun q => F.field ⟨q.val.2, q.property⟩
  continuous_field := F.continuous_field.comp
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

/-- Fix a single parameter value for the entire solution. This is the actual
slice of the joint open domain, possibly empty for an inadmissible parameter.
It does not replace that slice by all of time-state space. -/
def atParameterValue (F : ParameterODE E P) (p : P) : ODE E where
  domain := (fun q : ℝ × E => (q, p)) ⁻¹' F.domain
  isOpen_domain := F.isOpen_domain.preimage (continuous_id.prodMk continuous_const)
  field := fun q => F.field ⟨(q.val, p), q.property⟩
  continuous_field := F.continuous_field.comp
    (((continuous_id.prodMk continuous_const).comp continuous_subtype_val).subtype_mk _)

/-- Endpoint-aware autonomous solution on a specified nonempty interval. -/
def autonomousSolutionOnValue (F : AutonomousODE E) (I : TimeInterval)
    (x : ℝ → E) : Prop :=
  ContinuousOn x I.carrier ∧
  (∀ t ∈ I.carrier, x t ∈ F.domain) ∧
  ∀ t ∈ I.carrier, HasDerivWithinAt x (autonomousEvalValue F (x t)) I.carrier t

/-- Classical autonomous solution, retaining C¹ regularity and the open interval. -/
def classicalAutonomousSolutionOnValue (F : AutonomousODE E) (I : OpenTimeInterval)
    (x : ℝ → E) : Prop :=
  ContDiffOn ℝ 1 x I.carrier ∧
  (∀ t ∈ I.carrier, x t ∈ F.domain) ∧
  ∀ t ∈ I.carrier, HasDerivAt x (autonomousEvalValue F (x t)) t

def autonomousIVPOnValue (F : AutonomousODE E) (I : TimeInterval)
    (x : ℝ → E) (s : ℝ) (ξ : E) : Prop :=
  autonomousSolutionOnValue F I x ∧ s ∈ I.carrier ∧ x s = ξ

def classicalAutonomousIVPOnValue (F : AutonomousODE E) (I : OpenTimeInterval)
    (x : ℝ → E) (s : ℝ) (ξ : E) : Prop :=
  classicalAutonomousSolutionOnValue F I x ∧ s ∈ I.carrier ∧ x s = ξ

/-- A single value `p`, independent of time, is used at every graph point. -/
def parameterSolutionOnValue (F : ParameterODE E P) (p : P) (I : TimeInterval)
    (x : ℝ → E) : Prop :=
  ContinuousOn x I.carrier ∧
  (∀ t ∈ I.carrier, ((t, x t), p) ∈ F.domain) ∧
  ∀ t ∈ I.carrier, HasDerivWithinAt x (parameterEvalValue F t (x t) p) I.carrier t

def classicalParameterSolutionOnValue (F : ParameterODE E P) (p : P)
    (I : OpenTimeInterval) (x : ℝ → E) : Prop :=
  ContDiffOn ℝ 1 x I.carrier ∧
  (∀ t ∈ I.carrier, ((t, x t), p) ∈ F.domain) ∧
  ∀ t ∈ I.carrier, HasDerivAt x (parameterEvalValue F t (x t) p) t

def parameterIVPOnValue (F : ParameterODE E P) (p : P) (I : TimeInterval)
    (x : ℝ → E) (s : ℝ) (ξ : E) : Prop :=
  parameterSolutionOnValue F p I x ∧ s ∈ I.carrier ∧ x s = ξ

def classicalParameterIVPOnValue (F : ParameterODE E P) (p : P)
    (I : OpenTimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E) : Prop :=
  classicalParameterSolutionOnValue F p I x ∧ s ∈ I.carrier ∧ x s = ξ

/- Closed expected types quantify every space and instance. -/

def autonomousEvalExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  AutonomousODE E → E → E

def parameterEvalExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
  ParameterODE E P → ℝ → E → P → E

def autonomousToODEExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  AutonomousODE E → ODE E

def atParameterExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
  ParameterODE E P → P → ODE E

def autonomousSolutionOnExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  AutonomousODE E → TimeInterval → (ℝ → E) → Prop

def classicalAutonomousSolutionOnExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  AutonomousODE E → OpenTimeInterval → (ℝ → E) → Prop

def autonomousIVPOnExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  AutonomousODE E → TimeInterval → (ℝ → E) → ℝ → E → Prop

def classicalAutonomousIVPOnExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  AutonomousODE E → OpenTimeInterval → (ℝ → E) → ℝ → E → Prop

def parameterSolutionOnExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
  ParameterODE E P → P → TimeInterval → (ℝ → E) → Prop

def classicalParameterSolutionOnExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
  ParameterODE E P → P → OpenTimeInterval → (ℝ → E) → Prop

def parameterIVPOnExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
  ParameterODE E P → P → TimeInterval → (ℝ → E) → ℝ → E → Prop

def classicalParameterIVPOnExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
  ParameterODE E P → P → OpenTimeInterval → (ℝ → E) → ℝ → E → Prop

def autonomousSolutionOnIffExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  ∀ (F : AutonomousODE E) (I : TimeInterval) (x : ℝ → E),
    autonomousSolutionOnValue F I x ↔
      solutionOnValue (autonomousToODEValue F) I x

def autonomousIVPOnIffExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  ∀ (F : AutonomousODE E) (I : TimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E),
    autonomousIVPOnValue F I x s ξ ↔
      ivpOnValue (autonomousToODEValue F) I x s ξ

def classicalAutonomousSolutionOnIffExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  ∀ (F : AutonomousODE E) (I : OpenTimeInterval) (x : ℝ → E),
    classicalAutonomousSolutionOnValue F I x ↔
      classicalSolutionOnValue (autonomousToODEValue F) I x

def classicalAutonomousIVPOnIffExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
  ∀ (F : AutonomousODE E) (I : OpenTimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E),
    classicalAutonomousIVPOnValue F I x s ξ ↔
      classicalIVPOnValue (autonomousToODEValue F) I x s ξ

def parameterSolutionOnIffExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
  ∀ (F : ParameterODE E P) (p : P) (I : TimeInterval) (x : ℝ → E),
    parameterSolutionOnValue F p I x ↔
      solutionOnValue (atParameterValue F p) I x

def parameterIVPOnIffExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
  ∀ (F : ParameterODE E P) (p : P) (I : TimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E),
    parameterIVPOnValue F p I x s ξ ↔
      ivpOnValue (atParameterValue F p) I x s ξ

def classicalParameterSolutionOnIffExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
  ∀ (F : ParameterODE E P) (p : P) (I : OpenTimeInterval) (x : ℝ → E),
    classicalParameterSolutionOnValue F p I x ↔
      classicalSolutionOnValue (atParameterValue F p) I x

def classicalParameterIVPOnIffExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
  ∀ (F : ParameterODE E P) (p : P) (I : OpenTimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E),
    classicalParameterIVPOnValue F p I x s ξ ↔
      classicalIVPOnValue (atParameterValue F p) I x s ξ

end Specs.D13Unified.Ch01.AutonomousParameters
