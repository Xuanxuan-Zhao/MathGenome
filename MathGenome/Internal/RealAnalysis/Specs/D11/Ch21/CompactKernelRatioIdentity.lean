import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.CompactTranslateIntegralContinuity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.CcTensorApproximation
import Mathlib.MeasureTheory.Integral.Prod

/-! Independent statements of paper.tex:5898–5923. All measures are on exactly
`borel G`; the product measurable space below is the factor Borel product.
There are no countability or global sigma-finiteness assumptions. -/
namespace Specs.D11.Ch21.CompactKernelRatioIdentity
open Set MeasureTheory
open scoped Pointwise
universe u
local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G

noncomputable def mass {G : Type u} [TopologicalSpace G] [Group G]
    (ν : @Measure G (borel G)) (g : CompactlySupportedContinuousMap G ℝ) (x : G) : ℝ :=
  ∫ t, g (t * x) ∂ν

/-- The three kernels occurring in the finite-rectangle argument. -/
noncomputable def kernels {G : Type u} [TopologicalSpace G] [Group G]
    (ν : @Measure G (borel G)) (f g : CompactlySupportedContinuousMap G ℝ) :
    Fin 3 → G × G → ℝ
  | 0 => fun p => f p.1 * g (p.2 * p.1) / mass ν g p.1
  | 1 => fun p => f (p.2⁻¹ * p.1) * g p.1 / mass ν g (p.2⁻¹ * p.1)
  | 2 => fun p => f p.2⁻¹ * g p.1 / mass ν g p.2⁻¹

/-- Real-valued B records finiteness; every defining section is absolutely integrable. -/
def denominator_properties : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (ν : @Measure G (borel G)),
    Specs.D11.Ch21.HaarDefinition.leftHaarValue ν →
    ∀ (g : CompactlySupportedContinuousMap G ℝ), (∀ x, 0 ≤ g x) → g ≠ 0 →
    Continuous (mass ν g) ∧ ∀ x,
      Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value ν (fun t => g (t * x)) ∧ 0 < mass ν g x

/-- All three kernels are measurable for B(G) tensor B(G), and absolutely
integrable on the same finite compact rectangle. -/
def kernel_control : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ ν : @Measure G (borel G)),
    Specs.D11.Ch21.HaarDefinition.leftHaarValue μ →
    Specs.D11.Ch21.HaarDefinition.leftHaarValue ν →
    ∀ (g : CompactlySupportedContinuousMap G ℝ), (∀ x, 0 ≤ g x) → g ≠ 0 →
    ∀ (f : CompactlySupportedContinuousMap G ℝ),
    let K := tsupport f
    let L := tsupport g
    let S := K ∪ L
    let T := L * K⁻¹ ∪ K⁻¹
    IsCompact S ∧ IsCompact T ∧ μ S < ⊤ ∧ ν T < ⊤ ∧
    ∀ i : Fin 3,
      @Measurable (G × G) ℝ ((borel G).prod (borel G)) (borel ℝ) (kernels ν f g i) ∧
      tsupport (kernels ν f g i) ⊆ S ×ˢ T ∧
      Integrable (kernels ν f g i) ((μ.restrict S).prod (ν.restrict T))

/-- Full signed-real identity, with all scalar integral inputs integrable. -/
def ratio_identity : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ ν : @Measure G (borel G)),
    Specs.D11.Ch21.HaarDefinition.leftHaarValue μ →
    Specs.D11.Ch21.HaarDefinition.leftHaarValue ν →
    ∀ (g : CompactlySupportedContinuousMap G ℝ), (∀ x, 0 ≤ g x) → g ≠ 0 →
    ∀ (f : CompactlySupportedContinuousMap G ℝ),
    Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value μ f ∧
    Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value μ g ∧
    Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value ν (fun y => f y⁻¹ / mass ν g y⁻¹) ∧
    (∫ x, f x ∂μ) = (∫ x, g x ∂μ) * (∫ y, f y⁻¹ / mass ν g y⁻¹ ∂ν)

end Specs.D11.Ch21.CompactKernelRatioIdentity
