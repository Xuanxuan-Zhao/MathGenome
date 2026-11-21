import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SetwiseUniformIntegrability
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.WeakL1UniformIntegrability

/-! Independent statements for `fa2:p4:hahn-vitali-saks`, paper.tex:19793–19865.
The scalar field is real or complex and the original measure is σ-finite.
Setwise convergence tests all measurable sets, including those of infinite measure.
The a.e. limit in the Vitali assertion is initially an arbitrary raw function.
-/
open MeasureTheory Filter
open scoped ENNReal Topology
universe u

namespace ExpandedFA.PartIV.HahnVitaliSaks.Spec

open ExpandedFA.FunctionSpaces.WeakL1UniformIntegrabilitySpec

/-- Full setwise convergence conclusion, reusing the upstream uniform controls. -/
def MainStatement : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (f : ℕ → Lp 𝕜 1 μ),
    SetwiseUniformIntegrability.Spec.SetwiseConvergent μ (fun n => (f n : X → 𝕜)) →
    SetwiseUniformIntegrability.Spec.UniformL1Control μ (fun n => (f n : X → 𝕜)) ∧
    ∃ g : Lp 𝕜 1 μ, WeaklyConverges μ f g ∧
      ∀ h : Lp 𝕜 ∞ μ, Tendsto (fun n => ∫ x, f n x * h x ∂μ) atTop
        (𝓝 (∫ x, g x * h x ∂μ))

/-- Every weak Cauchy sequence has a weak limit in the original L¹ space. -/
def WeakSequentialCompleteness : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (f : ℕ → Lp 𝕜 1 μ),
    (∀ L : Lp 𝕜 1 μ →L[𝕜] 𝕜, CauchySeq (fun n => L (f n))) →
    ∃ g : Lp 𝕜 1 μ, WeaklyConverges μ f g

/-- No finite total mass or integrability hypothesis on the a.e. limit is added. -/
def VitaliConsequence : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (f : ℕ → Lp 𝕜 1 μ) (g : Lp 𝕜 1 μ)
    (a : X → 𝕜), WeaklyConverges μ f g →
    (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (a x))) →
    a =ᵐ[μ] (g : X → 𝕜) ∧ Tendsto f atTop (𝓝 g)

end ExpandedFA.PartIV.HahnVitaliSaks.Spec
