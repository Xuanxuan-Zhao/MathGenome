import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.CompletedProduct
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! Independent statements for paper.tex:3170–3205. The Euclidean space,
completed Lebesgue measure, scalar integrability, and completed section maps
are the shared objects. The radial factor lives on the strictly positive ray.
The angular normalization is specified also using closed truncated cones. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Pointwise

namespace D11.Ch09.PolarMeasure
open D11.Ch03
abbrev Sphere (n : ℕ) := sphere (0 : Point n) 1
abbrev Radius := Ioi (0 : ℝ)
abbrev Punctured (n : ℕ) := ({0}ᶜ : Set (Point n))
/-- The source's cone with radial endpoint included. -/
def closedCone {n : ℕ} (A : Set (Sphere n)) : Set (Point n) :=
  Ioc (0 : ℝ) 1 • (Subtype.val '' A)
end D11.Ch09.PolarMeasure

namespace Specs.D11.Ch09.PolarMeasure
open _root_.D11.Ch03 _root_.D11.Ch09.PolarMeasure
open Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch05.NonnegativeIntegral
open Specs.D11.Ch06.ScalarIntegral
open Specs.D11.Ch08.CompletedProduct

abbrev angularMeasure_type := (n : ℕ) → Measure (Sphere n)
def angularMeasure_value : angularMeasure_type := fun n => (volume : Measure (Point n)).toSphere
abbrev radialMeasure_type := ℕ → Measure Radius
def radialMeasure_value : radialMeasure_type := fun n => Measure.volumeIoiPow (n - 1)
abbrev polarEquiv_type := (n : ℕ) → Punctured n ≃ₜ (Radius × Sphere n)
def polarEquiv_value : polarEquiv_type := fun n =>
  (homeomorphUnitSphereProd (Point n)).trans (Homeomorph.prodComm _ _)
abbrev fromPolar_type := (n : ℕ) → Radius × Sphere n → Point n
def fromPolar_value : fromPolar_type := fun _ p => (p.1 : ℝ) • (p.2 : Point _)

def polar_coordinates : Prop := ∀ n (x : Punctured n),
  ((polarEquiv_value n x).1 : ℝ) = ‖(x : Point n)‖ ∧
  ((polarEquiv_value n x).2 : Point n) = ‖(x : Point n)‖⁻¹ • (x : Point n)

def inverse_coordinates : Prop := ∀ n (p : Radius × Sphere n),
  ((polarEquiv_value n).symm p : Point n) = fromPolar_value n p

def angular_finite : Prop := ∀ n [NeZero n], IsFiniteMeasure (angularMeasure_value n)

def closedCone_borel : Prop := ∀ n (A : Set (Sphere n)), MeasurableSet A →
  MeasurableSet (closedCone A)

def angular_cone : Prop := ∀ n [NeZero n] (A : Set (Sphere n)), MeasurableSet A →
  angularMeasure_value n A = (n : ℝ≥0∞) * lebesgue_value n (closedCone A)

def total_mass : Prop := ∀ n [NeZero n],
  angularMeasure_value n univ = (n : ℝ≥0∞) * lebesgue_value n (ball 0 1)

def origin_null : Prop := ∀ n [NeZero n], lebesgue_value n {0} = 0

/-- The subtype of the full shared Lebesgue measurable space. -/
abbrev offZeroSpace (n : ℕ) [NeZero n] : MeasurableSpace (Punctured n) :=
  .comap Subtype.val (lebesgueSpace_value n)
noncomputable def offZeroMeasure (n : ℕ) [NeZero n] : @Measure (Punctured n) (offZeroSpace n) :=
  @Measure.comap _ _ (offZeroSpace n) (lebesgueSpace_value n) Subtype.val (lebesgue_value n)

/-- Transport from the full Lebesgue space off zero to the Borel product. -/
def completed_source_transport : Prop := ∀ n [NeZero n],
  @MeasurePreserving _ _ (offZeroSpace n) inferInstance (polarEquiv_value n)
    (offZeroMeasure n) ((radialMeasure_value n).prod (angularMeasure_value n))

/-- The same map also transports the completed spaces. -/
def completed_transport : Prop := ∀ n [NeZero n],
  @MeasurePreserving _ _ (offZeroSpace n)
    (Specs.D11.Ch02.Completion.completedSpace_value
      ((radialMeasure_value n).prod (angularMeasure_value n))) (polarEquiv_value n)
    (offZeroMeasure n) ((radialMeasure_value n).prod (angularMeasure_value n)).completion

/-- The existence and uniqueness assertion on the full source space.
The positive-dimension result includes the stipulated n ≥ 2. -/
def polar_measure : Prop := ∀ n [NeZero n],
  ∃! σ : Measure (Sphere n), IsFiniteMeasure σ ∧
    @Measure.map _ _ (offZeroSpace n) inferInstance (polarEquiv_value n)
      (offZeroMeasure n) = (radialMeasure_value n).prod σ

/-- Borel transport off the origin, with the factors in the source's order. -/
def radial_direction_transport : Prop := ∀ n [NeZero n],
  MeasurePreserving (polarEquiv_value n)
    ((volume : Measure (Point n)).comap Subtype.val)
    ((radialMeasure_value n).prod (angularMeasure_value n))

/-- Uniqueness concerns this exact radial-direction transport. -/
def angular_unique : Prop := ∀ n [NeZero n] (σ : Measure (Sphere n)),
  IsFiniteMeasure σ →
  Measure.map (polarEquiv_value n) ((volume : Measure (Point n)).comap Subtype.val) =
    (radialMeasure_value n).prod σ → σ = angularMeasure_value n

/-- Borel nonnegative formula; no finiteness assumption on the integral. -/
def nonnegative_formula : Prop := ∀ n [NeZero n] (h : Point n → ℝ≥0∞), Measurable h →
  @nonnegativeIntegral_value _ (lebesgueSpace_value n) (lebesgue_value n) h =
    ∫⁻ (r : Radius), ∫⁻ (θ : Sphere n), h ((r : ℝ) • (θ : Point n)) ∂angularMeasure_value n ∂radialMeasure_value n

/-- Scalar formula requires absolute integrability on the completed Euclidean
space. Borel measurability is not required in this stronger formulation. -/
def scalar_formula : Prop := ∀ n [NeZero n] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (h : Point n → 𝕜)
    (hh : @scalarIntegrable_value _ _ (lebesgueSpace_value n) _ _ _ (lebesgue_value n) h),
  Integrable (h ∘ fromPolar_value n)
      ((radialMeasure_value n).prod (angularMeasure_value n)) ∧
  (∀ᵐ (r : Radius) ∂radialMeasure_value n, Integrable (fun θ : Sphere n => h ((r : ℝ) • θ))
      (angularMeasure_value n)) ∧
  Integrable (fun r : Radius => ∫ θ : Sphere n, h ((r : ℝ) • θ) ∂angularMeasure_value n)
      (radialMeasure_value n) ∧
  @scalarIntegral_value _ _ (lebesgueSpace_value n) _ _ _ (lebesgue_value n) h hh =
    ∫ (r : Radius), ∫ (θ : Sphere n), h ((r : ℝ) • (θ : Point n)) ∂angularMeasure_value n ∂radialMeasure_value n

/-- Completion is taken after the product. The inner functions use the shared
section convention (zero on exceptional sections), and the actual sections
are measurable on the completed angular factor almost everywhere. -/
def completed_nonnegative_formula : Prop := ∀ n [NeZero n] (h : Point n → ℝ≥0∞),
  @Measurable _ _ (lebesgueSpace_value n) _ h →
  completedMeasurable ((radialMeasure_value n).prod (angularMeasure_value n))
      (h ∘ fromPolar_value n) ∧
  (∀ᵐ (r : Radius) ∂(radialMeasure_value n).completion,
    completedMeasurable (angularMeasure_value n) (fun θ : Sphere n => h ((r : ℝ) • θ))) ∧
  completedMeasurable (radialMeasure_value n)
      (nonnegativeSectionLeft_value (angularMeasure_value n) (h ∘ fromPolar_value n)) ∧
  @nonnegativeIntegral_value _ (lebesgueSpace_value n) (lebesgue_value n) h =
    completedNNIntegral (radialMeasure_value n)
      (nonnegativeSectionLeft_value (angularMeasure_value n) (h ∘ fromPolar_value n))

def completed_scalar_formula : Prop := ∀ n [NeZero n] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (h : Point n → 𝕜)
    (hh : @scalarIntegrable_value _ _ (lebesgueSpace_value n) _ _ _ (lebesgue_value n) h),
  completedIntegrable ((radialMeasure_value n).prod (angularMeasure_value n))
      (h ∘ fromPolar_value n) ∧
  (∀ᵐ (r : Radius) ∂(radialMeasure_value n).completion,
    completedIntegrable (angularMeasure_value n) (fun θ : Sphere n => h ((r : ℝ) • θ))) ∧
  ∃ hs : completedIntegrable (radialMeasure_value n)
      (scalarSectionLeft_value (angularMeasure_value n) (h ∘ fromPolar_value n)),
    @scalarIntegral_value _ _ (lebesgueSpace_value n) _ _ _ (lebesgue_value n) h hh =
      completedIntegral (radialMeasure_value n)
        (scalarSectionLeft_value (angularMeasure_value n) (h ∘ fromPolar_value n)) hs

end Specs.D11.Ch09.PolarMeasure
