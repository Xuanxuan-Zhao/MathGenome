import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14WeakSubsequence
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.ClusterPt

/-! Independent statements for paper.tex, Proposition `prop:pde-weak-galerkin`.
The dual and bilinear form use the norm topology. The weak topology is the
initial topology of that continuous dual. Reflexivity means surjectivity of
canonical evaluation into the continuous bidual. -/
namespace P201.WeakLimit

open Filter
open scoped Topology
universe u

variable (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable abbrev weakTopology : TopologicalSpace V :=
  ExpandedFA.P1.C12DualPairSpec.DualPairTopologyValue ℝ V (V →L[ℝ] ℝ)
    (topDualPairing ℝ V)

/-- Norm density, with all continuous linear maps formed in the norm topology. -/
def DenseTests (Vm : ℕ → Submodule ℝ V) : Prop :=
  Dense (⋃ m, (Vm m : Set V))

def Solves (a : V →L[ℝ] V →L[ℝ] ℝ) (ell : V →L[ℝ] ℝ) (x : V) : Prop :=
  ∀ v : V, a x v = ell v

namespace Expected

/-- Existence retains boundedness and reflexivity, without coercivity or
any assumption that the approximants belong to their test spaces. -/
def WeakLimitExistence : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V],
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ V →
    ∀ (Vm : ℕ → Submodule ℝ V), Monotone Vm →
    (∀ m, FiniteDimensional ℝ (Vm m)) → DenseTests V Vm →
    ∀ (a : V →L[ℝ] V →L[ℝ] ℝ) (ell : V →L[ℝ] ℝ) (s : ℕ → V),
    Bornology.IsBounded (Set.range s) →
    (∀ m, ∀ v ∈ Vm m, a (s m) v = ell v) →
    ∃ (k : ℕ → ℕ), StrictMono k ∧ ∃ x : V,
      Tendsto (s ∘ k) atTop (@nhds V (weakTopology V) x) ∧ Solves V a ell x

/-- Every weak cluster point of tails solves the equation. This statement
needs neither coercivity, reflexivity, boundedness nor finite dimension. -/
def ClusterPointSolves : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Vm : ℕ → Submodule ℝ V), Monotone Vm → DenseTests V Vm →
    ∀ (a : V →L[ℝ] V →L[ℝ] ℝ) (ell : V →L[ℝ] ℝ) (s : ℕ → V),
    (∀ m, ∀ v ∈ Vm m, a (s m) v = ell v) →
    ∀ x : V, @MapClusterPt V (weakTopology V) ℕ x atTop s → Solves V a ell x

/-- Under coercivity, the extracted solution is the unique solution and
all weak cluster points (not just subsequential limits) equal it. -/
def CoerciveWeakLimit : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V],
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ V →
    ∀ (Vm : ℕ → Submodule ℝ V), Monotone Vm →
    (∀ m, FiniteDimensional ℝ (Vm m)) → DenseTests V Vm →
    ∀ (a : V →L[ℝ] V →L[ℝ] ℝ) (ell : V →L[ℝ] ℝ) (s : ℕ → V),
    Bornology.IsBounded (Set.range s) →
    (∀ m, ∀ v ∈ Vm m, a (s m) v = ell v) →
    ∀ alpha : ℝ, 0 < alpha → (∀ v : V, alpha * ‖v‖ ^ 2 ≤ a v v) →
    ∃ (k : ℕ → ℕ), StrictMono k ∧ ∃ x : V,
      Tendsto (s ∘ k) atTop (@nhds V (weakTopology V) x) ∧ Solves V a ell x ∧
      (∀ y : V, Solves V a ell y → y = x) ∧
      (∀ y : V, @MapClusterPt V (weakTopology V) ℕ y atTop s ↔ y = x)

end Expected
end P201.WeakLimit
