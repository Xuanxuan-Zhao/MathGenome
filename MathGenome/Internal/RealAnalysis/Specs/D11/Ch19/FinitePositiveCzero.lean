import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CzeroBanachDensity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Independent statements for paper.tex:5566–5573. The scalar parameter includes
both ℝ and ℂ, with the ordinary scalar-linear integral pairing. Positivity in
either field means preservation of the nonnegative real cone. The measure has
exactly the Borel domain and the three shared Radon predicates; no countability
or nonemptiness assumption is added. The integral identification explicitly
includes measurability and absolute integrability, so it does not rely on the
totalized integral of a nonintegrable function.
-/

open MeasureTheory

namespace Specs.D11.Ch19.FinitePositiveCzero
universe u

/-- Positivity for a scalar-linear C0 functional, valid over ℝ and ℂ. -/
def Positive {X : Type u} [TopologicalSpace X] {𝕜 : Type} [RCLike 𝕜]
    (L : ZeroAtInftyContinuousMap X 𝕜 →L[𝕜] 𝕜) : Prop :=
  ∀ f, (∀ x, 0 ≤ RCLike.re (f x) ∧ RCLike.im (f x) = 0) →
    0 ≤ RCLike.re (L f) ∧ RCLike.im (L f) = 0

/-- Agreement on the canonical Cc inclusion with integration against μ.
For Radon μ every Cc test is integrable, including when μ(X) is infinite. -/
def ExtendsIntegral {X : Type u} [TopologicalSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ : @Measure X (borel X)) (L : ZeroAtInftyContinuousMap X 𝕜 →L[𝕜] 𝕜) : Prop :=
  letI : MeasurableSpace X := borel X
  ∀ f : CompactlySupportedContinuousMap X 𝕜,
    L (CzeroBanachDensity.ccInclusionValue X 𝕜 f) = ∫ x, f x ∂μ

/-- The exact finite-mass criterion for bounded positive extension. -/
def bounded_extension_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure X (borel X)), Specs.D11.Ch18.RadonPredicates.isRadonValue μ →
    ((∃ L : ZeroAtInftyContinuousMap X 𝕜 →L[𝕜] 𝕜,
      ExtendsIntegral μ L ∧ Positive L) ↔ μ Set.univ < ⊤)

/-- Uniqueness among all bounded scalar-linear extensions, without presupposing
positivity of either extension or finite total mass. -/
def extension_unique : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (𝕜 : Type) [RCLike 𝕜] (μ : @Measure X (borel X))
    (L M : ZeroAtInftyContinuousMap X 𝕜 →L[𝕜] 𝕜),
    ExtendsIntegral μ L → ExtendsIntegral μ M → L = M

/-- Every bounded extension is positive, is ordinary integration on all of C0,
and has exactly the total mass as norm. In particular its existence forces
finite total mass. Both real and extended nonnegative norm formulas are given. -/
def extension_identification : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure X (borel X)), Specs.D11.Ch18.RadonPredicates.isRadonValue μ →
    ∀ L : ZeroAtInftyContinuousMap X 𝕜 →L[𝕜] 𝕜, ExtendsIntegral μ L →
      μ Set.univ < ⊤ ∧ Positive L ∧
      (letI : MeasurableSpace X := borel X
       ∀ f : ZeroAtInftyContinuousMap X 𝕜,
         Measurable f ∧ Integrable f μ ∧ L f = ∫ x, f x ∂μ) ∧
      ‖L‖ = (μ Set.univ).toReal ∧ ENNReal.ofReal ‖L‖ = μ Set.univ

end Specs.D11.Ch19.FinitePositiveCzero
