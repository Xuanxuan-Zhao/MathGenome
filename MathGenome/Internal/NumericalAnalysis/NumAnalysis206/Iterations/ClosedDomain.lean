import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.ClosedDomain
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Iterations.Banach
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! A closed invariant domain (paper.tex, Corollary p206:W67). -/

open Filter
open scoped Topology

universe u

namespace NumAnalysis206.Iterations

/-- Banach's theorem restricted to a nonempty closed invariant subset. -/
theorem closedDomain : Specs.NumAnalysis206.Iterations.ClosedDomainStatement.{u} := by
  intro X _ _ D T q hD hclosed hmaps hq₀ hq₁ hT
  let : Nonempty D := hD.to_subtype
  let : CompleteSpace D := hclosed.isComplete.completeSpace_coe
  let S : D → D := fun x => ⟨T x, hmaps x.property⟩
  have hS : ∀ x y : D, dist (S x) (S y) ≤ q * dist x y := by
    intro x y
    exact hT x x.property y y.property
  obtain ⟨p, hp, hunique, hconv⟩ := banach D S q hq₀ hq₁ hS
  -- The coercion intertwines the restricted and ambient iterates at every step.
  have hiter : ∀ (n : ℕ) (x : D), ((S^[n] x : D) : X) = T^[n] (x : X) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact congrArg T (ih x)
  refine ⟨p, p.property, congrArg Subtype.val hp, ?_, ?_⟩
  · intro p' hp'D hp'
    have hfix : S ⟨p', hp'D⟩ = ⟨p', hp'D⟩ := Subtype.ext hp'
    exact congrArg Subtype.val (hunique ⟨p', hp'D⟩ hfix)
  · intro x₀ hx₀
    refine ⟨?_, ?_⟩
    · intro n
      rw [← hiter n ⟨x₀, hx₀⟩]
      exact (S^[n] ⟨x₀, hx₀⟩).property
    · have h := continuous_subtype_val.continuousAt.tendsto.comp (hconv ⟨x₀, hx₀⟩)
      simpa only [Function.comp_def, hiter] using h

end NumAnalysis206.Iterations
