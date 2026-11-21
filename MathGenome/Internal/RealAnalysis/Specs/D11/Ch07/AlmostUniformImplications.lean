import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions

/-!
Independent statements for paper.tex:2270–2284.

Almost-uniform convergence implies convergence outside a measurable null
exceptional set and global convergence in measure on every positive measure
space. The predicates are the canonical upstream ones. The normed-group
formulation includes finite real and complex measurable functions; the
implications themselves require no measurability of the functions. There is
no finiteness, sigma-finiteness, or completeness assumption on the measure.
-/

open Set Filter MeasureTheory
open scoped Topology

universe u v

namespace Specs.D11.Ch07.AlmostUniformImplications

open Specs.D11.Ch07.ConvergenceDefinitions

def almost_uniform_implies_ae : Prop :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → E) (g : X → E),
    almostUniformConverges_value μ f g → aeConverges_value μ f g

def almost_uniform_implies_inMeasure : Prop :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → E) (g : X → E),
    almostUniformConverges_value μ f g → inMeasureConverges_value μ f g

end Specs.D11.Ch07.AlmostUniformImplications
