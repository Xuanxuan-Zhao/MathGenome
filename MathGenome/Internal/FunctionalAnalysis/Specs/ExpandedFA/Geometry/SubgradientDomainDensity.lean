import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.BrondstedRockafellarApproximation
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06FenchelMoreau

/-! The remaining assertions of `fa2:p2:brondsted-rockafellar`,
paper.tex:12952–12959. Closures use the given norm topologies of X and its
continuous real-linear dual, respectively. The conjugate has values in EReal;
its finite domain is expressed by existence of a real value. No reflexivity
assumption is made. -/
namespace ExpandedFA.Geometry.SubgradientDomainDensity.Spec

open ExpandedFA.P1.ExtendedConvexFunctions

universe u

/-- Every finite-domain point has an epsilon-subgradient for every positive epsilon. -/
def EpsilonNonempty : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (φ : ExtendedFunction X),
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue X φ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    ∀ x ∈ ExpandedFA.P1.ExtendedConvexFunctions.Spec.finiteDomainValue X φ,
      ∀ ε : ℝ, 0 < ε →
        (ExpandedFA.Geometry.EpsilonSubgradient.Spec.EpsilonSubdifferentialValue X φ ε x).Nonempty

/-- The subgradient domain and the finite domain have the same norm closure. -/
def DomainClosure : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (φ : ExtendedFunction X),
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue X φ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    closure (ExpandedFA.BanachConvex.Spec.SubgradientDomainValue X φ) =
      closure (ExpandedFA.P1.ExtendedConvexFunctions.Spec.finiteDomainValue X φ)

/-- The range of the subdifferential is norm dense in the conjugate's domain,
up to taking the closure of that domain. This is the strong dual norm topology. -/
def RangeClosure : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (φ : ExtendedFunction X),
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue X φ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    closure {f : X →L[ℝ] ℝ | ∃ x : X,
      f ∈ ExpandedFA.BanachConvex.Spec.SubdifferentialValue X φ x} =
    closure {f : X →L[ℝ] ℝ | ∃ r : ℝ,
      ExpandedFA.P1.C06Conjugates.Spec.ConvexConjugateValue X φ f = (r : EReal)}

end ExpandedFA.Geometry.SubgradientDomainDensity.Spec
