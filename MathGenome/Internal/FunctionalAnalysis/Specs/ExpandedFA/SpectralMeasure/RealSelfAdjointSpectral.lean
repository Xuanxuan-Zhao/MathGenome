import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.RealComplexification
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.NormalSpectralTests
import Mathlib.MeasureTheory.Measure.Regular

/-! Real bounded self-adjoint spectral resolution and the real normal tests.
The underlying real H and the existing complexification are retained exactly.
No globally unbounded symbol is passed to a bounded spectral integral. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace Topology
namespace ExpandedFA.SpectralMeasure.RealSelfAdjointSpectral
universe u v
open TraceIdeals.RealComplexification

/-- Globally bounded coordinate, including R = 0. -/
def clippedCoordinate (R : ℝ) (hR : 0 ≤ R) : RealBoundedFunction ℝ where
  toFun t := max (-R) (min R t)
  measurable := measurable_const.max (measurable_const.min measurable_id)
  bounded := ⟨R, hR, fun t => abs_le.mpr ⟨le_max_left _ _,
    max_le (by linarith) (min_le_left _ _)⟩⟩

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Resolving data only: support and the bounded clipped-coordinate identity.
Full support, regularity and uniqueness are conclusions of the theorem. -/
def Resolves (A : H →L[ℝ] H) (E : RealProjectionValuedMeasure ℝ H)
    (C : RealBoundedRealization E) (R : ℝ) (hR : 0 ≤ R) : Prop :=
  E (spectrum ℝ A)ᶜ = 0 ∧ C.integral (clippedCoordinate R hR) = A

namespace Spec
open TraceIdeals.RealComplexification.Spec

def ClippedCoordinateType := ∀ R : ℝ, 0 ≤ R → RealBoundedFunction ℝ

def ClippedCoordinateValue : ClippedCoordinateType := clippedCoordinate

/-- Intrinsic real spectrum, characterized by actual two-sided bounded inverses. -/
def RealSpectrumIdentification : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (r : ℝ),
    (r ∉ spectrum ℝ A ↔ ∃ B : H →L[ℝ] H,
      (r • (1 : H →L[ℝ] H) - A).comp B = 1 ∧
      B.comp (r • (1 : H →L[ℝ] H) - A) = 1) ∧
    (r ∈ spectrum ℝ A ↔ (r : ℂ) ∈ spectrum ℂ (operator A))

def SpectrumGeometry : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H),
    IsClosed (spectrum ℝ A) ∧ spectrum ℝ A ⊆ Icc (-‖A‖) ‖A‖

/-- Complete real existence conclusion, on all Borel sets of the real line.
The realization already includes the coefficient and norm-square integral laws
for every bounded real Borel function. -/
def SpectralResolution : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H), IsSelfAdjoint A →
    ∃ (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E),
      Resolves A E C ‖A‖ (norm_nonneg A) ∧
      IsClosed (spectrum ℝ A) ∧ spectrum ℝ A ⊆ Icc (-‖A‖) ‖A‖ ∧
      (∀ U : Set ℝ, IsOpen U → (U ∩ spectrum ℝ A).Nonempty → E U ≠ 0) ∧
      (∀ x, (C.scalar x).Regular) ∧
      (∀ x y, (C.coefficient x y).variation.Regular) ∧
      (∀ r : ℝ, LinearMap.range (E {r}).toLinearMap =
        LinearMap.ker (A - r • (1 : H →L[ℝ] H)).toLinearMap) ∧
      (∀ (F : RealProjectionValuedMeasure ℝ H) (D : RealBoundedRealization F)
        (R : ℝ) (hR : 0 ≤ R), Resolves A F D R hR →
          ∀ B : Set ℝ, MeasurableSet B → F B = E B)

/-- Singleton range for any real resolving pair, before choosing its witness. -/
def SingletonRange : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E),
    Resolves A E C ‖A‖ (norm_nonneg A) → ∀ r : ℝ,
      LinearMap.range (E {r}).toLinearMap =
        LinearMap.ker (A - r • (1 : H →L[ℝ] H)).toLinearMap

/-- Independence of the auxiliary realization, for an arbitrary measurable base. -/
def RealizationIndependence : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (E : RealProjectionValuedMeasure S H) (C D : RealBoundedRealization E),
    ∀ f : RealBoundedFunction S, C.integral f = D.integral f

/-- Every bounded real realization on the Borel real line has regular scalar
measures and regular coefficient variations; no common measure is needed. -/
def RealizationRegularity : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E),
      (∀ x, (C.scalar x).Regular) ∧ (∀ x y, (C.coefficient x y).variation.Regular)

/-- Generic descent from projections that preserve the fixed-real vectors.
This hypothesis is to be proved for the complex spectral resolution; it is not
an assumption in SpectralResolution. -/
def PVMDescent : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    letI : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace
    ∀ E : ProjectionValuedMeasure S (Space H),
      (∀ B : Set S, MeasurableSet B → ∀ x : H,
        conjugation (E B (inclusion x)) = E B (inclusion x)) →
      ∃ F : RealProjectionValuedMeasure S H,
        ∀ B : Set S, MeasurableSet B → ∀ x : H, inclusion (F B x) = E B (inclusion x)

local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace

def SelfAdjointSpectrum : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H), IsStarNormal N →
    (IsSelfAdjoint N ↔ ∀ z ∈ spectrum ℂ (operator N), z.im = 0)

def OrthogonalSpectrum : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H), IsStarNormal N →
    (star N * N = 1 ∧ N * star N = 1 ↔
      ∀ z ∈ spectrum ℂ (operator N), ‖z‖ = 1)

/-- Equality with the fixed-real part of the complex singleton range, expressed
as an exact image of the real eigenspace under the canonical inclusion. -/
def RealEigenprojection : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H), IsStarNormal N →
    ∀ E : ProjectionValuedMeasure (spectrum ℂ (operator N)) (Space H),
      NormalPVM.Spec.Resolves (operator N) E → ∀ r : ℝ,
      inclusion '' {x : H | N x = r • x} =
        {p : Space H | p ∈ LinearMap.range (E {z | (z : ℂ) = (r : ℂ)}).toLinearMap ∧
          conjugation p = p}

end Spec
end ExpandedFA.SpectralMeasure.RealSelfAdjointSpectral
