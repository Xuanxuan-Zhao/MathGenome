import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
Independent specification for the weak Liouville clause of
`fa2:p1:frechet-holomorphy`, paper.tex:2183–2220.

Only scalar holomorphy is required: every continuous complex-linear
functional composed with the map is differentiable on all of ℂ. Weak
boundedness means that each such scalar function has bounded range, with
a bound that may depend on the functional. The target has its given TVS
structure and separating continuous dual, without any norm, local convexity,
metrizability, or completeness assumption. Separation itself implies
Hausdorffness. Zero vector spaces are included.
-/

namespace ExpandedFA.P1.WeakEntireLiouvilleSpec

universe u

/-- Scalar Liouville plus separation, for an arbitrary complex TVS. -/
def WeakEntireConstant : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E],
    TVS ℂ E → ∀ [SeparatingDual ℂ E] (f : ℂ → E),
      (∀ ℓ : E →L[ℂ] ℂ, Differentiable ℂ (fun z => ℓ (f z))) →
      (∀ ℓ : E →L[ℂ] ℂ,
        Bornology.IsBounded (Set.range (fun z : ℂ => ℓ (f z)))) →
      ∃ c : E, ∀ z : ℂ, f z = c

end ExpandedFA.P1.WeakEntireLiouvilleSpec
