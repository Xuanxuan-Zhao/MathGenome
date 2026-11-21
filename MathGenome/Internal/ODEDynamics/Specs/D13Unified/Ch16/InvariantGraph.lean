import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Independent formulation of paper.tex, Proposition d13:16:invariant-graph.
The product components of `field` are the original f and g. Total functions
are representatives only: all regularity, solutions and comparisons retain
their actual open domains. No completeness of a trajectory is required. -/
noncomputable section
open Set

namespace D13Unified.Ch16.InvariantGraph
universe u v
variable (E : Type u) (G : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure GraphSystem where
  domain : Set (E × G)
  isOpen_domain : IsOpen domain
  field : E × G → E × G
  field_c1 : ContDiffOn ℝ 1 field domain
  base : Set E
  isOpen_base : IsOpen base
  graph : E → G
  graph_c1 : ContDiffOn ℝ 1 graph base
  graph_mem : ∀ x ∈ base, (x, graph x) ∈ domain

variable {E G}

/-- The autonomous field on exactly its prescribed state domain. -/
def odeOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : Set X) (hU : IsOpen U) (V : X → X) (hV : ContinuousOn V U) : ODE X where
  domain := Prod.snd ⁻¹' U
  isOpen_domain := hU.preimage continuous_snd
  field := fun p => V p.val.2
  continuous_field := (continuousOn_iff_continuous_domRestrict.mp hV).comp
    ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.property))

namespace GraphSystem
variable (S : GraphSystem E G)

def lift (x : E) : E × G := (x, S.graph x)

def reducedField (x : E) : E := (S.field (S.lift x)).1

lemma lift_c1 : ContDiffOn ℝ 1 S.lift S.base :=
  contDiffOn_id.prodMk S.graph_c1

lemma reduced_c1 : ContDiffOn ℝ 1 S.reducedField S.base :=
  (S.field_c1.comp S.lift_c1 S.graph_mem).fst

def fullODE : ODE (E × G) :=
  odeOn S.domain S.isOpen_domain S.field S.field_c1.continuousOn

def reducedODE : ODE E :=
  odeOn S.base S.isOpen_base S.reducedField S.reduced_c1.continuousOn

/-- Dh(x) f(x,h(x)) = g(x,h(x)), at every point of the graph domain. -/
def Tangent : Prop :=
  ∀ x ∈ S.base, fderiv ℝ S.graph x (S.reducedField x) = (S.field (S.lift x)).2

/-- Every full trajectory through a graph point stays in the graph on an
actual smaller open interval about its initial time zero. Quantification over
all solutions does not make their existence an assumption; existence follows
from the C¹ field and is also proved in the implementation. -/
def LocallyInvariant : Prop :=
  ∀ x ∈ S.base, ∀ (I : OpenTimeInterval) (z : ℝ → E × G),
    Specs.D13Unified.Ch01.SolutionConcepts.classicalIVPOnValue
      S.fullODE I z 0 (S.lift x) →
    ∃ J : OpenTimeInterval, 0 ∈ J.carrier ∧ J.carrier ⊆ I.carrier ∧
      ∀ t ∈ J.carrier, (z t).1 ∈ S.base ∧ (z t).2 = S.graph (z t).1

end GraphSystem
end D13Unified.Ch16.InvariantGraph

namespace Specs.D13Unified.Ch16.InvariantGraph
open _root_.D13Unified _root_.D13Unified.Ch16.InvariantGraph
open Specs.D13Unified.Ch01.SolutionConcepts
universe u v

/-- Lifting works on every actual interval, including included endpoints. -/
def liftSolutionsExpected : Prop :=
  ∀ {E : Type u} {G : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (S : GraphSystem E G),
    S.Tangent → ∀ (I : TimeInterval) (x : ℝ → E),
    solutionOnValue S.reducedODE I x →
    solutionOnValue S.fullODE I (fun t => S.lift (x t))

/-- The lift agrees with any full solution from the same datum throughout
the common open interval, in both time directions. -/
def identifySolutionsExpected : Prop :=
  ∀ {E : Type u} {G : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] (S : GraphSystem E G),
    S.Tangent → ∀ (I J : OpenTimeInterval) (x : ℝ → E) (z : ℝ → E × G)
      (s : ℝ) (ξ : E),
    classicalIVPOnValue S.reducedODE I x s ξ →
    classicalIVPOnValue S.fullODE J z s (S.lift ξ) →
    EqOn (fun t => S.lift (x t)) z (I.carrier ∩ J.carrier)

def invariantGraphExpected : Prop :=
  ∀ {E : Type u} {G : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] (S : GraphSystem E G),
    S.Tangent ↔ S.LocallyInvariant

end Specs.D13Unified.Ch16.InvariantGraph
