import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Interpolation.RieszThorin
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.Analysis.Fourier.AddCircle

/-!
The manuscript's Fourier normalization is exp(-2πi x·ξ). The circle is R/Z
with Haar probability measure; ℓ^q(Z) is represented as L^q of counting measure.
This retains all integer coordinates since counting measure has no nonempty
null sets. A family includes agreement on every L¹ intersection and compatibility
on all intersections of its domains, not only on Schwartz functions.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v

namespace ExpandedFA.PartIV.HausdorffYoung

/-- All pairs 1 ≤ p ≤ 2, 1/p + 1/q = 1, including (1, ∞). -/
structure ExponentPair where
  p : ℝ≥0∞
  q : ℝ≥0∞
  lower : 1 ≤ p
  upper : p ≤ 2
  conjugate : ENNReal.HolderConjugate p q

instance (a : ExponentPair) : Fact (1 ≤ a.p) := ⟨a.lower⟩
instance (a : ExponentPair) : ENNReal.HolderConjugate a.p a.q := a.conjugate
instance (a : ExponentPair) : Fact (1 ≤ a.q) := ⟨ENNReal.HolderConjugate.one_le a.q a.p⟩

/-- Contractive extensions, their L¹ formula, and compatibility on arbitrary
Lp intersections. Equality of inputs and outputs means a.e. equality. -/
structure FourierFamily {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (formula : (X → ℂ) → Y → ℂ) where
  operator : ∀ a : ExponentPair, Lp ℂ a.p μ →L[ℂ] Lp ℂ a.q ν
  norm_le : ∀ a, ‖operator a‖ ≤ 1
  agreement : ∀ a (f : Lp ℂ a.p μ), MemLp f 1 μ → operator a f =ᵐ[ν] formula f
  compatible : ∀ a b (f : Lp ℂ a.p μ) (g : Lp ℂ b.p μ),
    f =ᵐ[μ] g → operator a f =ᵐ[ν] operator b g

/-- A single linear Fourier operator on the algebraic sum, with the two
contractive endpoint bounds and agreement on the full L¹ part. This is an
auxiliary obligation, not an assumed certificate in either principal result. -/
def EndpointSystem {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (formula : (X → ℂ) → Y → ℂ) : Prop :=
  ∃ T : Interpolation.RieszThorinSpec.SumSpace μ 1 2 →ₗ[ℂ] (Y →ₘ[ν] ℂ),
    Interpolation.RieszThorinSpec.EndpointBound T 1 ∞ 1 ∧
    Interpolation.RieszThorinSpec.EndpointBound T 2 2 1 ∧
    ∀ f : Interpolation.RieszThorinSpec.SumSpace μ 1 2, MemLp (f : X →ₘ[μ] ℂ) 1 μ → T f =ᵐ[ν] formula (f : X →ₘ[μ] ℂ)

end ExpandedFA.PartIV.HausdorffYoung

namespace Specs.ExpandedFA.PartIV.HausdorffYoung
open _root_.ExpandedFA.PartIV.HausdorffYoung
open _root_.ExpandedFA.Fourier

/-- The entire Euclidean conclusion, in every dimension including zero. -/
def EuclideanHausdorffYoung : Prop := ∀ d : ℕ,
  Nonempty (FourierFamily (volume : Measure (Euclidean d)) volume integralFourier)

/-- The entire circle conclusion with normalized Haar measure. -/
def CircleHausdorffYoung : Prop :=
  Nonempty (FourierFamily (AddCircle.haarAddCircle (T := (1 : ℝ)))
    (Measure.count : Measure ℤ) fourierCoeff)

/-- The proof assembly from actual, compatible endpoint operators. -/
def InterpolationAssembly : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (formula : (X → ℂ) → Y → ℂ),
    EndpointSystem μ ν formula → Nonempty (FourierFamily μ ν formula)

end Specs.ExpandedFA.PartIV.HausdorffYoung
