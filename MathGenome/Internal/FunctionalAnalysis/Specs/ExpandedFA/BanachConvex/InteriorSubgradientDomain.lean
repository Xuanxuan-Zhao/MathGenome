import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.Definitions

/-! The interior-domain assertion of paper.tex:8087–8088. The space is a
real Banach space and lower semicontinuity means closed real sublevels.
The statement retains the extended-valued function and both original domains. -/
namespace ExpandedFA.BanachConvex.InteriorSpec

open P1.ExtendedConvexFunctions
universe u

/-- For a proper lower semicontinuous convex function on a real Banach space,
the subgradient domain and the finite domain have the same interior. -/
def InteriorSubgradientDomain : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (φ : ExtendedFunction X),
    P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue X φ →
    interior (Spec.SubgradientDomainValue X φ) =
      interior (P1.ExtendedConvexFunctions.Spec.finiteDomainValue X φ)

end ExpandedFA.BanachConvex.InteriorSpec
