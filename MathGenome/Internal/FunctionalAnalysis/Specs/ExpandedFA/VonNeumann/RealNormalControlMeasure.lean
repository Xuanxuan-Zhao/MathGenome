import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealAbelianComplexification
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.NormalAlgebraControlMeasure
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealFugledePutnam
import Mathlib.MeasureTheory.Measure.Regular

/-! The corrected real-normal control measure theorem, on the original real
Hilbert space. The spectrum and every spectral projection are complex. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace ExpandedFA.VonNeumann.RealNormalControlMeasure.Spec
universe u
open TraceIdeals.RealComplexification.Spec
open TraceIdeals.RealComplexification
open RealAbelianComplexification.Spec.NativeLp
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := completeSpace

/-- The actual real double commutant, with its inherited real operator norm. -/
def normalAlgebra (N : H →L[ℝ] H) : StarSubalgebra ℝ (H →L[ℝ] H) :=
  StarSubalgebra.centralizer ℝ (StarSubalgebra.centralizer ℝ
    (StarAlgebra.adjoin ℝ {N} : Set (H →L[ℝ] H)) : Set (H →L[ℝ] H))

abbrev Spectrum (N : H →L[ℝ] H) := spectrum ℂ (operator N)

/-- Real coordinate extraction is defined on every operator. Its restriction
property for compatible symbols is a conclusion of the theorem. -/
def realCalculus {N : H →L[ℝ] H}
    (Φ : (Spectrum N → ℂ) → Space H →L[ℂ] Space H) (f : Spectrum N → ℂ) :
    H →L[ℝ] H := RealAbelianComplexification.Spec.operatorRealPart (Φ f)

def Compatible {X : Type*} (τ : X → X) (f : X → ℂ) : Prop :=
  ∀ z, f (τ z) = star (f z)

/-- The finite vector control and its real origin. No PVM is asserted to act
on H for general Borel sets. The witnesses are retained for the algebra and
for the separately assigned predual/topology theorem. -/
structure SpectralControl (N : H →L[ℝ] H) where
  E : SpectralMeasure.ProjectionValuedMeasure (Spectrum N) (Space H)
  Φ : (Spectrum N → ℂ) → Space H →L[ℂ] Space H
  e : H
  μ : Measure (Spectrum N)
  finite : IsFiniteMeasure μ
  regular : μ.Regular
  resolves : SpectralMeasure.NormalPVM.Spec.Resolves (operator N) E
  unique : ∀ F : SpectralMeasure.ProjectionValuedMeasure (Spectrum N) (Space H),
    SpectralMeasure.NormalPVM.Spec.Resolves (operator N) F →
    ∀ B, MeasurableSet B → F B = E B
  calculus : SpectralMeasure.BorelNormSpectrum.Spec.BorelCalculus E Φ
  coordinate : Φ (fun z => (z : ℂ)) = operator N
  separating : SeparableMASA.Spec.RealIsSeparating (normalAlgebra N) e
  complexSeparating : SeparableMASA.Spec.IsSeparating
    (NormalAlgebraControlMeasure.Spec.normalAlgebra (operator N)) (inclusion e)
  vectorMeasure : ∀ B, MeasurableSet B → μ B = ENNReal.ofReal (‖E B (inclusion e)‖ ^ 2)
  control : NormalAlgebraControlMeasure.Spec.IsControlMeasure E μ
  τ : Spectrum N ≃ₜ Spectrum N
  tau_apply : ∀ z, (τ z : ℂ) = star (z : ℂ)
  involutive : Function.Involutive τ
  measurePreserving : MeasurePreserving τ μ μ
  covariance : ∀ B, MeasurableSet B → ∀ p : Space H,
    conjugation (E B (conjugation p)) = E (τ ⁻¹' B) p

/-- Use precisely the native fixed spaces, product and star from the shared
complexification interface. -/
def SpectralControl.involutionData {N : H →L[ℝ] H} (C : SpectralControl N) :
    InvolutionData C.μ := ⟨C.τ, C.measurePreserving, C.involutive⟩

structure AlgebraModel (N : H →L[ℝ] H) extends SpectralControl N where
  descent : ∀ f : Spectrum N → ℂ,
    SpectralMeasure.Spec.IsBoundedMeasurable f → Compatible τ f →
    (∀ p : Space H, conjugation p = p → conjugation (Φ f p) = Φ f p) ∧
    SpectralMeasure.RealFugledePutnam.Spec.UniqueRealRestriction (Φ f) (realCalculus Φ f) ∧
    operator (realCalculus Φ f) = Φ f
  image : ∀ T : H →L[ℝ] H, T ∈ normalAlgebra N ↔
    ∃ f : Spectrum N → ℂ, SpectralMeasure.Spec.IsBoundedMeasurable f ∧
      Compatible τ f ∧ realCalculus Φ f = T
  Ψ : Fixed toSpectralControl.involutionData ∞ ≃ₗ[ℝ] normalAlgebra N
  multiplicative : ∀ f g, Ψ (f * g) = Ψ f * Ψ g
  star_preserving : ∀ f, Ψ (star f) = star (Ψ f)
  isometric : ∀ f, ‖Ψ f‖ = ‖f‖
  representatives : ∀ h : Fixed toSpectralControl.involutionData ∞,
    ∃ f : Spectrum N → ℂ, SpectralMeasure.Spec.IsBoundedMeasurable f ∧
      Compatible τ f ∧ f =ᵐ[μ] h.val
  on_representatives : ∀ (h : Fixed toSpectralControl.involutionData ∞) (f : Spectrum N → ℂ),
    SpectralMeasure.Spec.IsBoundedMeasurable f → Compatible τ f → f =ᵐ[μ] h.val →
      (Ψ h : H →L[ℝ] H) = realCalculus Φ f ∧ operator (Ψ h : H →L[ℝ] H) = Φ f
  real_coordinate : realCalculus Φ (fun z => (z : ℂ)) = N

/-- Full finite-control/algebra statement, including the zero Hilbert space. -/
def RealNormalControlMeasure : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (N : H →L[ℝ] H),
    IsStarNormal N → Nonempty (AlgebraModel N)

/-- The self-adjoint specialization identifies the actual intrinsic real
spectrum, rather than referring to a real section of an unrelated operator. -/
def SelfAdjointSpecialization : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (N : H →L[ℝ] H), IsSelfAdjoint N →
    ∃ C : AlgebraModel N,
      (∀ z : Spectrum N, (z : ℂ).im = 0 ∧ C.τ z = z) ∧
      (∀ t : ℝ, t ∈ spectrum ℝ N ↔ (t : ℂ) ∈ Spectrum N)

/-- The usual real scalar model, on the actual intrinsic real spectrum.
The measure and representative action are anchored to the same normal model. -/
structure RealScalarModel (N : H →L[ℝ] H) (C : AlgebraModel N) where
  κ : Spectrum N ≃ₜ spectrum ℝ N
  realCoordinate : ∀ z, (κ z : ℝ) = (z : ℂ).re
  ν : Measure (spectrum ℝ N)
  measure_eq : ν = Measure.map κ C.μ
  finite : IsFiniteMeasure ν
  regular : ν.Regular
  U : Lp ℝ ∞ ν ≃ₗ[ℝ] normalAlgebra N
  isometric : ∀ h, ‖U h‖ = ‖h‖
  multiplicative : ∀ h k,
    U ((ContinuousLinearMap.mul ℝ ℝ).holder ∞ h k) = U h * U k
  selfAdjoint : ∀ h, IsSelfAdjoint (U h : H →L[ℝ] H)
  on_representatives : ∀ (h : Lp ℝ ∞ ν) (f : spectrum ℝ N → ℝ),
    Measurable f → (∃ M : ℝ, ∀ z, ‖f z‖ ≤ M) → f =ᵐ[ν] h →
    (U h : H →L[ℝ] H) = realCalculus C.Φ (fun z => (f (κ z) : ℂ))

def RealScalarSpecialization : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (N : H →L[ℝ] H), IsSelfAdjoint N →
    ∃ C : AlgebraModel N, Nonempty (RealScalarModel N C)
end ExpandedFA.VonNeumann.RealNormalControlMeasure.Spec
