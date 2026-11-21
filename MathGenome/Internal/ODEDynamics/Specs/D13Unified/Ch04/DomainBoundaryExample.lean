import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.MaximalSolutionMap
import Mathlib.Topology.Order.Filter
import Mathlib.Tactic.NormNum

/-! Independent specification of paper.tex, Example d13:04:domain-boundary.
All curves use the shared ODE and actual-interval solution predicates. Equality
of maximal solutions means equality of their domains and of values there;
ambient representatives away from the domain need not agree. -/
noncomputable section
open Set Filter
open scoped Topology
open D13Unified
open Specs.D13Unified.Ch01.SolutionConcepts

namespace Specs.D13Unified.Ch04.DomainBoundaryExample

/-- The prescribed domain is exactly ℝ × (-1,1); the field there is 1. -/
def boundaryODE : ODE ℝ where
  domain := {p | p.2 ∈ Ioo (-1 : ℝ) 1}
  isOpen_domain := isOpen_Ioo.preimage continuous_snd
  field := fun _ => 1
  continuous_field := continuous_const

/-- The proposed maximal time interval. -/
def boundaryInterval : OpenTimeInterval :=
  ⟨⟨Ioo (-1) 1, ⟨0, by norm_num, by norm_num⟩, ordConnected_Ioo⟩, isOpen_Ioo⟩

def wholeInterval : OpenTimeInterval :=
  ⟨⟨univ, univ_nonempty, ordConnected_univ⟩, isOpen_univ⟩

/-- The different ODE for which the global formula is a solution. -/
def fullODE : ODE ℝ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun _ => 1
  continuous_field := continuous_const

def solutionExpected : Prop :=
  classicalIVPOnValue boundaryODE boundaryInterval id 0 0

/-- Every solution of the specified IVP is a restriction of t ↦ t. -/
def restrictionExpected : Prop :=
  ∀ (J : OpenTimeInterval) (x : ℝ → ℝ),
    classicalIVPOnValue boundaryODE J x 0 0 →
      J.carrier ⊆ boundaryInterval.carrier ∧ EqOn x id J.carrier

/-- Maximality is characterized exactly, without equating representatives off
 their actual domains. Combined with solutionExpected this gives existence and
 uniqueness of the maximal solution. -/
def maximalExpected : Prop :=
  ∀ (x : Solution boundaryODE), 0 ∈ x.interval.carrier → x.representative 0 = 0 →
    (maximalValue x ↔ x.interval.carrier = boundaryInterval.carrier ∧
      EqOn x.representative id x.interval.carrier)

def maximalSolutionExpected : Prop :=
  ∃ x : Solution boundaryODE,
    x.interval.carrier = boundaryInterval.carrier ∧
    EqOn x.representative id x.interval.carrier ∧
    x.representative 0 = 0 ∧ 0 ∈ x.interval.carrier ∧ maximalValue x

def boundedNotGlobalExpected : Prop :=
  ∀ (J : OpenTimeInterval) (x : ℝ → ℝ),
    classicalIVPOnValue boundaryODE J x 0 0 →
      (∀ t ∈ J.carrier, ‖x t‖ < 1) ∧ J.carrier ≠ univ

/-- Both endpoint limits exist and reach excluded state-boundary points. -/
def boundaryLimitsExpected : Prop :=
  Tendsto (id : ℝ → ℝ) (𝓝[<] 1) (𝓝 1) ∧
  Tendsto (id : ℝ → ℝ) (𝓝[>] (-1)) (𝓝 (-1)) ∧
  (1, 1) ∉ boundaryODE.domain ∧ (-1, -1) ∉ boundaryODE.domain

/-- Full eventual escape at each endpoint, with thresholds inside the actual
 solution interval. This quantifies over every compact subset of the domain. -/
def compactEscapeExpected : Prop :=
  ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ boundaryODE.domain →
    (∃ τ ∈ Ioo (-1 : ℝ) 1, ∀ t ∈ Ioo τ 1, (t, t) ∉ K) ∧
    (∃ τ ∈ Ioo (-1 : ℝ) 1, ∀ t ∈ Ioo (-1) τ, (t, t) ∉ K)

/-- The same formula is global for the full-state ODE, but violates the original
 graph condition, already at time 1. -/
def globalFormulaExpected : Prop :=
  classicalIVPOnValue fullODE wholeInterval id 0 0 ∧
  (1, (id : ℝ → ℝ) 1) ∉ boundaryODE.domain ∧
  ¬ classicalIVPOnValue boundaryODE wholeInterval id 0 0

/-- Identification with the existing canonical maximal solution map. -/
def canonicalExpected : Prop :=
  (Ch04.MaximalSolutionMap.maximalIntervalValue boundaryODE 0 0).carrier =
      boundaryInterval.carrier ∧
    ∀ t ∈ boundaryInterval.carrier,
      Ch04.MaximalSolutionMap.solutionValueValue boundaryODE t 0 0 = t

end Specs.D13Unified.Ch04.DomainBoundaryExample
