import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.CompatibleConvexClosedSets
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Algebra.BigOperators.Fin

/-!
The dual-pair bipolar theorem, paper.tex 2094–2116.
The bilinear pairing is `B y x`, over the original field ℝ or ℂ.
No norm or pre-existing topology on either vector space is assumed.
All closures use the accepted pairing topology on the indicated carrier.
The hull is the finite-sum absolutely convex hull, including the empty sum,
as stipulated in paper.tex 1194–1201. Thus the empty set has hull {0}.
Annihilators use zero values, not modulus inequalities; both orders of
the dual pair are covered for arbitrary subsets, with algebraic spans.
-/
namespace ExpandedFA.P1.GeneralBipolar

universe u v w
noncomputable section

/-- Zero-inclusive absolutely convex hull, without a topology or norm on X. -/
def aconv (𝕜 : Type u) {X : Type v} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] (A : Set X) : Set X :=
  {z | ∃ (n : ℕ) (c : Fin n → 𝕜) (x : Fin n → X),
    (∀ i, x i ∈ A) ∧ (∑ i, ‖c i‖) ≤ 1 ∧ (∑ i, c i • x i) = z}

/-- Annihilator in the other member of the bilinear dual pair. -/
def annihilator {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (A : Set X) : Set Y :=
  {y | ∀ x ∈ A, B y x = 0}

namespace Spec

def Bipolar : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜), B.SeparatingLeft → B.SeparatingRight →
    ∀ A : Set X,
      B.polar (B.flip.polar A) =
        @closure X (C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B) (aconv 𝕜 A)

def DoubleAnnihilator : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜), B.SeparatingLeft → B.SeparatingRight →
    ∀ A : Set X,
      annihilator B.flip (annihilator B A) =
        @closure X (C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B)
          (Submodule.span 𝕜 A : Set X)

def DoubleAnnihilatorFlip : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜), B.SeparatingLeft → B.SeparatingRight →
    ∀ D : Set Y,
      annihilator B (annihilator B.flip D) =
        @closure Y (C12DualPairSpec.DualPairTopologyValue 𝕜 Y X B.flip)
          (Submodule.span 𝕜 D : Set Y)

/-- The compatible-topology clause, with the same full generality as upstream. -/
def CompatibleClosedConvex : Prop :=
  Specs.ExpandedFA.P1.CompatibleConvexClosedSets.compatibleConvexClosedSetsType.{u, v}

end Spec
end
end ExpandedFA.P1.GeneralBipolar
