import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.SturmLiouvilleDirichlet

/-! The periodic clause of `fa2:p3:sturm-liouville`. Endpoint values are
values of continuous representatives of the actual distributional Sobolev
classes. No regularity, boundary compatibility, or operator existence is
assumed. The spectral and heat conclusions are allocated separately. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal ComplexConjugate
namespace ExpandedFA.Models.SturmLiouvillePeriodic
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.OneDimensional
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces ExpandedFA.Unbounded
open SturmLiouvilleDirichlet

/-- The actual continuous endpoint representative, with arbitrary outside values. -/
def EndpointRepresentative {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}
    (w : H1 𝕜 a b) (f : ℝ → 𝕜) : Prop :=
  ContinuousOn f (Icc a b) ∧ Represents (baseLp w) f

def PeriodicH1 {𝕜 : Type} [RCLike 𝕜] {a b : ℝ} (w : H1 𝕜 a b) : Prop :=
  ∃ f : ℝ → 𝕜, EndpointRepresentative w f ∧ f a = f b

/-- The literal H² domain, with periodic value and weighted derivative traces.
The weight at the two endpoints is allowed to differ. -/
def StrongDomain {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}
    (c : Coefficients a b) (u : L2 𝕜 a b) : Prop :=
  (∃ w₂ : H2 𝕜 a b, w₂.val (zeroIndex 1 2) = u) ∧
  ∃ w d : H1 𝕜 a b, baseLp w = u ∧ baseLp d = derivativeLp w ∧
    ∃ f g : ℝ → 𝕜, EndpointRepresentative w f ∧ EndpointRepresentative d g ∧
      f a = f b ∧ (c.p a : 𝕜) * g a = (c.p b : 𝕜) * g b

/-- The full maximal weak graph of the periodic form. -/
def FormRealization {𝕜 : Type} [RCLike 𝕜] {a b : ℝ} (c : Coefficients a b)
    (A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b)) : Prop :=
  ∀ u f, (u, f) ∈ A.graph ↔
    ∃ w : H1 𝕜 a b, baseLp w = u ∧ PeriodicH1 w ∧
      ∀ v : H1 𝕜 a b, PeriodicH1 v → form c v w = inner 𝕜 (baseLp v) f

namespace Spec

def WeakRealization : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ)
    (c : Coefficients a b),
  ∃! A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b), FormRealization c A

/-- No H² or flux hypothesis is an input to this assertion. -/
def FluxRegularity : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ)
    (c : Coefficients a b) (A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b)),
    FormRealization c A → ∀ u : A.domain,
    ∃ w flux : H1 𝕜 a b, baseLp w = (u : L2 𝕜 a b) ∧ PeriodicH1 w ∧
      baseLp flux = multiplier c.p c.p_C1.continuousOn (derivativeLp w) ∧
      derivativeLp flux = multiplier c.q c.q_continuous (baseLp w) - A u

/-- Complete assigned result over both scalar fields, including the exact
maximal form-operator domain and compactness at every resolvent point. -/
def Realization : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ)
    (c : Coefficients a b),
  ∃! A : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b),
    FormRealization c A ∧
    (∀ u : L2 𝕜 a b, u ∈ A.domain ↔ StrongDomain c u) ∧
    DifferentialAction c A ∧ Dense (A.domain : Set (L2 𝕜 a b)) ∧
    A = HilbertAdjointSpec.adjointValue A ∧
    (∃ γ : ℝ, ∀ u : A.domain,
      γ * ‖(u : L2 𝕜 a b)‖ ^ 2 ≤ RCLike.re (inner 𝕜 (u : L2 𝕜 a b) (A u))) ∧
    HasCompactResolvent A

end Spec
end ExpandedFA.Models.SturmLiouvillePeriodic
