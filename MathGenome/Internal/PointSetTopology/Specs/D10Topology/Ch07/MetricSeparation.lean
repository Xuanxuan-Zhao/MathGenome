import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent statements for paper.tex, d10:07:metric-normal.
Every topology and distance below comes from the explicitly supplied metric.
Nonemptiness is required for the distance zero-set test and the displayed
quotient, but not for normality, T4, or the G_delta conclusion. -/

open Set
universe u

namespace Specs.D10Topology.Ch07.MetricSeparation

/-- Identify the library distance with the infimum in the manuscript. -/
def metric_infDist_eq_infimum : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A : Set X) (x : X),
    letI := d
    Metric.infDist x A = sInf ((fun a => dist x a) '' A)

def metric_infDist_lipschitz : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A : Set X), A.Nonempty →
    letI := d
    LipschitzWith 1 (fun x => Metric.infDist x A)

def metric_infDist_estimate : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A : Set X), A.Nonempty →
    letI := d
    ∀ x y : X, |Metric.infDist x A - Metric.infDist y A| ≤ dist x y

def metric_infDist_zero_set : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A : Set X), A.Nonempty →
    letI := d
    {x : X | Metric.infDist x A = 0} = closure A

def metric_distance_denominator_pos : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A B : Set X),
    letI := d
    IsClosed A → IsClosed B → A.Nonempty → B.Nonempty → Disjoint A B →
    ∀ x : X, 0 < Metric.infDist x A + Metric.infDist x B

def metric_distance_quotient : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A B : Set X),
    letI := d
    IsClosed A → IsClosed B → A.Nonempty → B.Nonempty → Disjoint A B →
    let f : X → ℝ := fun x =>
      Metric.infDist x A / (Metric.infDist x A + Metric.infDist x B)
    Continuous f ∧ (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ A, f x = 0) ∧ (∀ x ∈ B, f x = 1)

/-- Empty prescribed closed sets are allowed, as is an empty ambient space. -/
def metric_closed_separation : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A B : Set X),
    letI := d
    IsClosed A → IsClosed B → Disjoint A B →
    ∃ f : X → ℝ, Continuous f ∧ (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ A, f x = 0) ∧ (∀ x ∈ B, f x = 1)

def metric_t4 : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    letI := d
    SeparationConventions.t4Value X

def metric_closed_gdelta : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    letI := d
    ∀ A : Set X, IsClosed A → SeparationConventions.gdeltaValue A

end Specs.D10Topology.Ch07.MetricSeparation
