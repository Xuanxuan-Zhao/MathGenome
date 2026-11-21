import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SphereTopology
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.Mobius
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.Cauchy

/-! The metric and stereographic part of paper.tex:2437–2450.
All points are on the canonical OnePoint ℂ, with its already fixed topology.
Euclidean three-space carries its L² norm, not the product maximum norm.
The normalization is half the unit sphere's Euclidean chord distance. -/
noncomputable section
namespace D12Complex.Chordal

abbrev Euclidean3 := EuclideanSpace ℝ (Fin 3)

def weight (z : ℂ) : ℝ := Real.sqrt (1 + ‖z‖ ^ 2)

/-- The chordal distance, including both orders of a finite/infinite pair. -/
def chordal (p q : RiemannSphere) : ℝ :=
  OnePoint.elim p (OnePoint.elim q 0 (fun w => 1 / weight w))
    (fun z => OnePoint.elim q (1 / weight z) (fun w => ‖z - w‖ / (weight z * weight w)))

def northPole : Euclidean3 := WithLp.toLp 2 ![0, 0, 1]

def finiteStereographic (z : ℂ) : Euclidean3 :=
  WithLp.toLp 2 ![2 * z.re / (1 + ‖z‖ ^ 2),
    2 * z.im / (1 + ‖z‖ ^ 2), (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2)]

/-- The exact stereographic parametrization stated in the source. -/
def stereographic (p : RiemannSphere) : Euclidean3 :=
  OnePoint.elim p northPole finiteStereographic

/-- The sphere extension of (w-a)/(1+conj(a)w), with its actual pole value. -/
def chartRotation (a : ℂ) : RiemannSphere → RiemannSphere :=
  Mobius.mobiusMap !![1, -a; star a, 1]

/-- Reciprocal sphere chart: exchanges zero and infinity. -/
def reciprocal : RiemannSphere → RiemannSphere :=
  Mobius.mobiusMap !![0, 1; 1, 0]

end D12Complex.Chordal
namespace Specs.D12Complex.Ch11.ChordalMetric
open _root_.D12Complex _root_.D12Complex.Chordal

def chordal_type := RiemannSphere → RiemannSphere → ℝ
def chordal_value : chordal_type := fun p q =>
  OnePoint.elim p (OnePoint.elim q 0 (fun w => 1 / Real.sqrt (1 + ‖w‖ ^ 2)))
    (fun z => OnePoint.elim q (1 / Real.sqrt (1 + ‖z‖ ^ 2))
      (fun w => ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2))))

def stereographic_type := RiemannSphere → Euclidean3
def stereographic_value : stereographic_type := fun p =>
  OnePoint.elim p (WithLp.toLp 2 ![0, 0, 1]) (fun z =>
    WithLp.toLp 2 ![2 * z.re / (1 + ‖z‖ ^ 2),
      2 * z.im / (1 + ‖z‖ ^ 2), (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2)])

def chartRotation_type := ℂ → RiemannSphere → RiemannSphere
def chartRotation_value : chartRotation_type := fun a =>
  Mobius.mobiusMap !![1, -a; star a, 1]

def reciprocal_type := RiemannSphere → RiemannSphere
def reciprocal_value : reciprocal_type := Mobius.mobiusMap !![0, 1; 1, 0]

def chordal_finite_type : Prop := ∀ z w : ℂ,
  chordal (sphereFinite z) (sphereFinite w) =
    ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2))

def chordal_infty_type : Prop :=
  chordal sphereInfty sphereInfty = 0 ∧ ∀ z : ℂ,
    chordal (sphereFinite z) sphereInfty = 1 / Real.sqrt (1 + ‖z‖ ^ 2) ∧
    chordal sphereInfty (sphereFinite z) = 1 / Real.sqrt (1 + ‖z‖ ^ 2)

def chordal_metric_type : Prop := ∃ m : MetricSpace RiemannSphere,
  m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace RiemannSphere) ∧
  (∀ p q, @dist RiemannSphere m.toDist p q = chordal p q) ∧
  @CompactSpace RiemannSphere m.toUniformSpace.toTopologicalSpace ∧
  @CompleteSpace RiemannSphere m.toUniformSpace

def chordal_half_chord_type : Prop := ∀ p q : RiemannSphere,
  chordal p q = dist (stereographic p) (stereographic q) / 2

def stereographic_homeomorph_type : Prop :=
  ∃ e : RiemannSphere ≃ₜ Metric.sphere (0 : Euclidean3) 1,
    ∀ p, (e p).val = stereographic p

def chartRotation_chordal_type : Prop := ∀ (a : ℂ) (p q : RiemannSphere),
  chordal (chartRotation a p) (chartRotation a q) = chordal p q

def reciprocal_chordal_type : Prop := ∀ p q : RiemannSphere,
  chordal (reciprocal p) (reciprocal q) = chordal p q

def chartRotation_bijective_type : Prop :=
  ∀ a : ℂ, Function.Bijective (chartRotation a)

def reciprocal_bijective_type : Prop := Function.Bijective reciprocal

end Specs.D12Complex.Ch11.ChordalMetric
