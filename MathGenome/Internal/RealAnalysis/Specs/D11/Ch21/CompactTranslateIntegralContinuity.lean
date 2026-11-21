import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarPositiveOpen
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CcCzero

/-!
Independent statements for paper.tex:5890–5897,
`d11:21:compact-translate-integral-continuity`.

The group is an arbitrary Hausdorff locally compact topological group. The
measure is on exactly its Borel sigma-algebra, and Radon has the three shared
Chapter 18 conditions. Scalar integrability includes Borel measurability and
finite absolute integral; thus the integral below is never merely a totalized
value assigned to a nonintegrable function. The scalar statement covers ℝ and ℂ.
-/
namespace Specs.D11.Ch21.CompactTranslateIntegralContinuity

open MeasureTheory
universe u

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G

/-- Every right-translated Cc section has a finite, defined scalar integral. -/
def translate_integrable : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (ν : @Measure G (borel G)),
    Specs.D11.Ch18.RadonPredicates.isRadonValue ν →
    ∀ (g : CompactlySupportedContinuousMap G 𝕜) (x : G),
      Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value ν (fun t => g (t * x))

/-- Continuity in the full topology, with no sequential or countability restriction. -/
def continuous_translate_integral : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (ν : @Measure G (borel G)),
    Specs.D11.Ch18.RadonPredicates.isRadonValue ν →
    ∀ g : CompactlySupportedContinuousMap G 𝕜,
      Continuous (fun x : G => ∫ t, g (t * x) ∂ν)

/-- For either left or right Haar measure, nonzero nonnegative Cc functions
give finite strictly positive translate integrals at every point. -/
def haar_translate_integral_pos : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (ν : @Measure G (borel G)),
    (HaarDefinition.leftHaarValue ν ∨ HaarDefinition.rightHaarValue ν) →
    ∀ g : CompactlySupportedContinuousMap G ℝ, (∀ t, 0 ≤ g t) → g ≠ 0 →
    ∀ x : G,
      Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value ν (fun t => g (t * x)) ∧
        0 < ∫ t, g (t * x) ∂ν

end Specs.D11.Ch21.CompactTranslateIntegralContinuity
