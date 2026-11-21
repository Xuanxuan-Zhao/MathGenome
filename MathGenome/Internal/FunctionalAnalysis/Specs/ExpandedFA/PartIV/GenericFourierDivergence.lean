import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.DirichletKernel
import Mathlib.Topology.Baire.Lemmas

/-! Independent statements for `fa2:p4:generic-fourier-divergence`,
paper.tex:20758–20792. The circle, normalized Haar measure, Fourier
coefficients, and symmetric sums are exactly those of the Dirichlet-kernel
interface. Unboundedness is expressed by arbitrarily large real thresholds,
which avoids a conditionally complete real supremum. Membership in `residual`
means that the complement is meagre. Both manuscript scalar fields are covered.
-/
noncomputable section
open Set TopologicalSpace

namespace ExpandedFA.PartIV.GenericFourierDivergenceSpec
open DirichletKernelSpec
abbrev Circle := DirichletKernelSpec.Circle

/-- A dense residual Gδ of complex continuous functions, each of which has
unbounded symmetric Fourier sums on a residual set of circle points. -/
def ComplexDivergence : Prop :=
  ∃ G : Set C(Circle, ℂ), G ∈ residual C(Circle, ℂ) ∧ Dense G ∧ IsGδ G ∧
    ∀ f ∈ G, {x : Circle | ∀ B : ℝ, ∃ N : ℕ, B < ‖partialSum N f x‖} ∈ residual Circle

/-- The same assertion for real continuous inputs. Fourier sums are still the
original complex exponential symmetric sums of the complexified real function. -/
def RealDivergence : Prop :=
  ∃ G : Set C(Circle, ℝ), G ∈ residual C(Circle, ℝ) ∧ Dense G ∧ IsGδ G ∧
    ∀ f ∈ G, {x : Circle | ∀ B : ℝ, ∃ N : ℕ,
      B < ‖partialSum N (fun t => (f t : ℂ)) x‖} ∈ residual Circle

end ExpandedFA.PartIV.GenericFourierDivergenceSpec
