import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Defs.Sequences

/-!
The definitions and theorem of paper.tex §v03-01 (1337–1394).
All duals are continuous linear duals for the original norm topology, with
operator norm. `WeakSpace ℝ X` uses precisely that dual; `WeakDual ℝ X`
uses evaluation at points of the original space. Topologies are transported
back to their original carriers by the canonical identity equivalences.
Reflexivity means that canonical evaluation, not an arbitrary bidual map,
is onto. No separability or nonzero-space assumption is made.
-/

noncomputable section
open Filter
open scoped Topology
universe u
namespace VariationalNotes.Existence.Specs

def canonicalEvaluationType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    X →L[ℝ] ((X →L[ℝ] ℝ) →L[ℝ] ℝ)

def canonicalEvaluation : canonicalEvaluationType :=
  fun _ _ _ => ContinuousLinearMap.apply ℝ ℝ

def IsReflexiveType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], Prop

def IsReflexive : IsReflexiveType :=
  fun X _ _ => Function.Surjective (canonicalEvaluation X)

def weakTopologyType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X], TopologicalSpace X

def weakTopology : weakTopologyType :=
  fun X _ _ => TopologicalSpace.induced (toWeakSpace ℝ X)
    (instTopologicalSpaceWeakSpace ℝ X)

def weakStarTopologyType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    TopologicalSpace (X →L[ℝ] ℝ)

def weakStarTopology : weakStarTopologyType :=
  fun X _ _ => TopologicalSpace.induced
    (StrongDual.toWeakDual : (X →L[ℝ] ℝ) ≃ₗ[ℝ] WeakDual ℝ X)
    (instTopologicalSpaceWeakDual ℝ X)

def canonicalEvaluation_apply : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x : X) (f : X →L[ℝ] ℝ), canonicalEvaluation X x f = f x

def canonicalEvaluation_isometry : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    Isometry (canonicalEvaluation X)

/-- The weak and weak-star topologies agree on the original normed dual. -/
def dual_weakTopology_eq_weakStarTopology : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    IsReflexive X → weakTopology (X →L[ℝ] ℝ) = weakStarTopology X

/-- A strictly increasing extraction converges in the full weak topology. -/
def reflexive_weak_subsequence : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    IsReflexive X → ∀ a : ℕ → X, Bornology.IsBounded (Set.range a) →
      ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ x : X,
        Tendsto (fun n => toWeakSpace ℝ X (a (k n))) atTop (𝓝 (toWeakSpace ℝ X x))

/-- Every center and every real radius, including empty negative-radius balls. -/
def reflexive_closedBall_isWeaklyCompact : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    IsReflexive X → ∀ (c : X) (r : ℝ),
      IsCompact ((toWeakSpace ℝ X) '' Metric.closedBall c r)

end VariationalNotes.Existence.Specs
