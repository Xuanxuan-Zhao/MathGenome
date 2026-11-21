import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.C1Dependence

/-! Independent statement of paper.tex, Theorem d13:06:ck-dependence.
The shared canonical solution and its actual maximal domain are retained.
Finite-dimensional normed spaces allow any fixed norm, including dimension zero.
No regularity or existence outside the recorded open domains is required. -/
noncomputable section
open Set
open scoped ContDiff

namespace Specs.D13Unified.Ch06.CkDependence
open _root_.D13Unified _root_.D13Unified.Ch06.C1Dependence
open Ch04.MaximalSolutionMap
universe u v

def JointCk : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (k : ℕ), 1 ≤ k → ∀ (F : ParameterODE E P),
    ContDiffOn ℝ k (field F) F.domain →
      IsOpen (parameterSolutionDomainValue F) ∧
      ContDiffOn ℝ k (solution F) (parameterSolutionDomainValue F)

/-- The actual terminal derivative, not merely a formal right-hand side, has
the additional joint regularity in all four groups of variables. -/
def TerminalCk : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (k : ℕ), 1 ≤ k → ∀ (F : ParameterODE E P),
    ContDiffOn ℝ k (field F) F.domain →
      (∀ q ∈ parameterSolutionDomainValue F,
        HasDerivAt (fun t => solution F (t,q.2))
          (field F ((q.1,solution F q),q.2.2)) q.1) ∧
      ContDiffOn ℝ k
        (fun q : ℝ × ((ℝ × E) × P) => deriv (fun t => solution F (t,q.2)) q.1)
        (parameterSolutionDomainValue F)

def JointSmooth : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), ContDiffOn ℝ ∞ (field F) F.domain →
      IsOpen (parameterSolutionDomainValue F) ∧
      ContDiffOn ℝ ∞ (solution F) (parameterSolutionDomainValue F)

end Specs.D13Unified.Ch06.CkDependence
