import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.C1Dependence

/-! Independent statements of paper.tex, d13:06:initial-time.
The ambient derivatives are taken only at points of the actual open maximal
domain. The parameter is fixed when differentiating either time coordinate. -/
noncomputable section
open Set

namespace D13Unified.Ch06.InitialTimeDerivative

/-- The nonautonomous scalar field x′ = t, with a constant dummy parameter. -/
def timeField : ParameterODE ℝ ℝ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun q => q.val.1.1
  continuous_field := continuous_fst.comp (continuous_fst.comp continuous_subtype_val)

/-- The explicit global IVP solution for x′ = t. -/
def explicitSolution (t s ξ : ℝ) : ℝ := ξ + (t^2 - s^2) / 2

end D13Unified.Ch06.InitialTimeDerivative

namespace Specs.D13Unified.Ch06.InitialTimeDerivative
open _root_.D13Unified _root_.D13Unified.Ch06.C1Dependence
open _root_.D13Unified.Ch06.InitialTimeDerivative
open Ch01.AutonomousParameters Ch04.MaximalSolutionMap
universe u v

/-- The starting-time derivative, with all original C¹ hypotheses and all
allowed terminal times, starting times, states and parameters. -/
def StartingTimeDerivative : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), ContDiffOn ℝ 1 (field F) F.domain →
    ∀ t s ξ p, (t,((s,ξ),p)) ∈ parameterSolutionDomainValue F →
      HasDerivAt (fun r => solution F (t,((r,ξ),p)))
        (-(stateVariation F s ξ p t) (parameterEvalValue F s ξ p)) s

/-- The example uses the same canonical maximal solution map as the theorem.
It exists for every real datum and time, has the printed formula and both time
derivatives, and distinguishes the starting derivative from minus the terminal
velocity whenever the two time coordinates differ. -/
def NonautonomousExample : Prop :=
  ContDiffOn ℝ 1 (field timeField) timeField.domain ∧
  ∀ t s ξ p : ℝ,
    (t,((s,ξ),p)) ∈ parameterSolutionDomainValue timeField ∧
    solution timeField (t,((s,ξ),p)) = explicitSolution t s ξ ∧
    HasDerivAt (fun r => solution timeField (t,((r,ξ),p))) (-s) s ∧
    HasDerivAt (fun r => solution timeField (r,((s,ξ),p))) t t ∧
    (s ≠ t → deriv (fun r => solution timeField (t,((r,ξ),p))) s ≠
      -parameterEvalValue timeField t (solution timeField (t,((s,ξ),p))) p)

end Specs.D13Unified.Ch06.InitialTimeDerivative
