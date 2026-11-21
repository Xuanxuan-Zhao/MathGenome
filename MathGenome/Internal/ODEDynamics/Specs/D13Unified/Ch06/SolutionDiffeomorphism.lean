import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.CkDependence
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! Independent specification of paper.tex, Corollary d13:06:local-diffeomorphism.
The domains are sections of the shared actual maximal solution domain. They
may be empty or proper subsets of the state space. The partial homeomorphism
has exactly these source and target sets, and both directions have the stated
Cᵏ regularity. No complete flow or autonomous field is assumed. -/
noncomputable section
open Set
open scoped ContDiff

namespace Specs.D13Unified.Ch06.SolutionDiffeomorphism
open _root_.D13Unified _root_.D13Unified.Ch06.C1Dependence
open Ch04.MaximalSolutionMap
universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Ω_(s,t,p) records exactly those states whose maximal solution reaches t. -/
def survivalDomainValue (F : ParameterODE E P) (s t : ℝ) (p : P) : Set E :=
  {ξ | (t,((s,ξ),p)) ∈ parameterSolutionDomainValue F}

def survivalDomainType : Type (max (u+1) (v+1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
    ParameterODE E P → ℝ → ℝ → P → Set E

/-- A Cᵏ diffeomorphism of the full open survival domains, with the reverse
solution as its inverse, and with its image stated explicitly. -/
def Diffeomorphism : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (k : ℕ), 1 ≤ k → ∀ (F : ParameterODE E P),
    ContDiffOn ℝ k (field F) F.domain → ∀ (s t : ℝ) (p : P),
      IsOpen (survivalDomainValue F s t p) ∧
      IsOpen (survivalDomainValue F t s p) ∧
      (fun ξ => solution F (t,((s,ξ),p))) '' survivalDomainValue F s t p =
        survivalDomainValue F t s p ∧
      ∃ e : OpenPartialHomeomorph E E,
        e.source = survivalDomainValue F s t p ∧
        e.target = survivalDomainValue F t s p ∧
        (e : E → E) = (fun ξ => solution F (t,((s,ξ),p))) ∧
        (e.symm : E → E) = (fun η => solution F (s,((t,η),p))) ∧
        ContDiffOn ℝ k e e.source ∧ ContDiffOn ℝ k e.symm e.target

/-- The ambient state derivative is invertible at each allowed datum; the
reverse solution derivative is its two-sided inverse. -/
def DerivativeInverse : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (k : ℕ), 1 ≤ k → ∀ (F : ParameterODE E P),
    ContDiffOn ℝ k (field F) F.domain → ∀ (s t : ℝ) (ξ : E) (p : P),
      (t,((s,ξ),p)) ∈ parameterSolutionDomainValue F →
      let A := stateVariation F s ξ p t
      let B := stateVariation F t (solution F (t,((s,ξ),p))) p s
      A.IsInvertible ∧
        B.comp A = ContinuousLinearMap.id ℝ E ∧
        A.comp B = ContinuousLinearMap.id ℝ E

end Specs.D13Unified.Ch06.SolutionDiffeomorphism
