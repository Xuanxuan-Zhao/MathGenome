import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06DoubleAnnihilator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Annihilators
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.DoubleAnnihilatorDual

/-!
The two double-annihilator identities in `fa2:p1:c06:double-annihilator`.
For the primal identity, continuity gives one inclusion and a distance-norming
functional excludes every point outside the norm closure. The dual identity
uses the accepted weak-star double-annihilator theorem in exactly the same
continuous scalar-linear evaluation pairing.
-/

namespace ExpandedFA.P1.C06DoubleAnnihilator

universe u v

theorem double_annihilator_primal : Spec.PrimalClosure.{u, v} := by
  intro 𝕜 E _ _ _ M
  ext x
  change (∀ f : E →L[𝕜] 𝕜, (∀ m ∈ M, f m = 0) → f x = 0) ↔
    x ∈ closure (M : Set E)
  constructor
  · intro hx
    by_contra hxM
    obtain ⟨f, hfM, _, hfx, hd⟩ :=
      C05Norming.distance_norming_functional 𝕜 E M x hxM
    have hzero : f x = 0 := hx f hfM
    have hd0 : Metric.infDist x (M : Set E) = 0 :=
      RCLike.ofReal_eq_zero.mp (hfx.symm.trans hzero)
    exact (ne_of_gt hd) hd0
  · intro hx f hf
    exact M.topologicalClosure_minimal hf f.isClosed_ker hx

theorem double_annihilator_dual : Spec.DualClosure.{u, v} :=
  DoubleAnnihilatorDual.double_annihilator_dual

end ExpandedFA.P1.C06DoubleAnnihilator
