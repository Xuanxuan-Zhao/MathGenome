import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.TransportNonnegative
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.TransportIntegrable
import Mathlib.MeasureTheory.Group.Measure

/-!
Independent statements for paper.tex:5927–5934, `d11:21:haar-inversion`.
The measure domain is exactly the Borel sigma-algebra of an arbitrary Hausdorff
locally compact topological group. No countability or sigma-finiteness is assumed.
The Radon and integral predicates are the canonical earlier interfaces. Scalar
integral evaluation requires actual Borel measurability and absolute integrability.
-/
namespace Specs.D11.Ch21.HaarInversion

open MeasureTheory
open scoped ENNReal
universe u

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G

/-- Pushforward by the inversion homeomorphism. -/
def inversionMeasureType : Type (u + 1) :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G],
    @Measure G (borel G) → @Measure G (borel G)

noncomputable def inversionMeasureValue : inversionMeasureType.{u} := fun μ => μ.inv

/-- The defining set formula is asserted on the original Borel domain. -/
def inversionMeasureApplyStatement : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (μ : @Measure G (borel G)) (E : Set G), MeasurableSet E →
    inversionMeasureValue μ E = μ ((fun x : G => x⁻¹) '' E)

def inversionMeasureInvolutiveStatement : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (μ : @Measure G (borel G)),
    inversionMeasureValue (inversionMeasureValue μ) = μ

def inversionMeasureNonzeroStatement : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (μ : @Measure G (borel G)), inversionMeasureValue μ ≠ 0 ↔ μ ≠ 0

def inversionMeasureRadonStatement : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (μ : @Measure G (borel G)),
    Specs.D11.Ch18.RadonPredicates.isRadonValue μ →
      Specs.D11.Ch18.RadonPredicates.isRadonValue (inversionMeasureValue μ)

/-- Nonnegative extended integrals include infinite values. -/
def inversionLIntegralStatement : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (μ : @Measure G (borel G)) (f : G → ℝ≥0∞), Measurable f →
    Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value
        (inversionMeasureValue μ) f =
      Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value μ (fun x => f x⁻¹)

/-- Both directions of scalar integrability transport, for real or complex scalars. -/
def inversionIntegrableIffStatement : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure G (borel G)) (f : G → 𝕜), Measurable f →
    (Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value (inversionMeasureValue μ) f ↔
      Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value μ (fun x => f x⁻¹))

def inversionIntegralStatement : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure G (borel G)) (f : G → 𝕜)
    (hf : Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value (inversionMeasureValue μ) f),
    ∃ hc : Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value μ (fun x => f x⁻¹),
      Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value (inversionMeasureValue μ) f hf =
        Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value μ (fun x => f x⁻¹) hc

/-- Inversion gives the full correspondence, including nonzero mass and regularity. -/
def inversionRightHaarIffStatement : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (μ : @Measure G (borel G)),
    Specs.D11.Ch21.HaarDefinition.rightHaarValue (inversionMeasureValue μ) ↔
      Specs.D11.Ch21.HaarDefinition.leftHaarValue μ

def inversionLeftHaarIffStatement : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (μ : @Measure G (borel G)),
    Specs.D11.Ch21.HaarDefinition.leftHaarValue (inversionMeasureValue μ) ↔
      Specs.D11.Ch21.HaarDefinition.rightHaarValue μ

end Specs.D11.Ch21.HaarInversion
