import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.Set.Card

/-!
Actual signed fibers for the analytic child of the Green boundary dictionary.
The measure is Mathlib's metric Hausdorff measure, not an occupation measure.
The sums use the original parameter and the original integer coefficients.
No regularity, comparison formula, or multiplicity certificate is a field.

The area and pushforward statements below are independent full Prop types.
Their implementations must establish the identities, measurability and
integrability, rather than assume them as certificates.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal NNReal
local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace D12Complex.SignedCurveMultiplicity

/-- Nonstationary occurrences in the actual supplied parameter subset. -/
def regularFiber (γ : ℝ → ℂ) (s : Set ℝ) (z : ℂ) : Set ℝ :=
  {t | t ∈ s ∧ γ t = z ∧ deriv γ t ≠ 0}

/-- The actual unit complex tangent; totalized to zero at stationary points. -/
def unitVelocity (γ : ℝ → ℂ) (t : ℝ) : ℂ :=
  deriv γ t / (‖deriv γ t‖ : ℂ)

/-- Extended nonnegative number of actual nonstationary occurrences. -/
def multiplicity (γ : ℝ → ℂ) (s : Set ℝ) (z : ℂ) : ℝ≥0∞ :=
  (regularFiber γ s z).encard

/-- Actual oriented occurrence sum. Summability is a separate obligation. -/
def signedDensity (γ : ℝ → ℂ) (s : Set ℝ) (z : ℂ) : ℂ :=
  ∑' t : regularFiber γ s z, unitVelocity γ t

/-- Only the two original endpoints are excluded; no new parameter is chosen. -/
def pathDensity (γ : PiecewiseC1Path) : ℂ → ℂ :=
  signedDensity γ (Ioo γ.path.a γ.path.b)

/-- Every original active integer coefficient is retained, with its sign. -/
def chainDensity (Γ : IntegralChain) (z : ℂ) : ℂ :=
  ∑ γ ∈ Γ.support, (Γ γ : ℂ) * pathDensity γ z

/-- Unsigned bound with the absolute values of all original coefficients. -/
def chainMultiplicity (Γ : IntegralChain) (z : ℂ) : ℝ≥0∞ :=
  ∑ γ ∈ Γ.support, (Γ γ).natAbs * multiplicity γ (Ioo γ.path.a γ.path.b) z

end D12Complex.SignedCurveMultiplicity

namespace Specs.D12Complex.Ch04.SignedCurveMultiplicity
open _root_.D12Complex _root_.D12Complex.SignedCurveMultiplicity

-- Expected values for the new shared analytic objects.
def regularFiber_type := (ℝ → ℂ) → Set ℝ → ℂ → Set ℝ
def regularFiber_value : regularFiber_type :=
  fun γ s z => {t | t ∈ s ∧ γ t = z ∧ deriv γ t ≠ 0}
def unitVelocity_type := (ℝ → ℂ) → ℝ → ℂ
def unitVelocity_value : unitVelocity_type :=
  fun γ t => deriv γ t / (‖deriv γ t‖ : ℂ)
def multiplicity_type := (ℝ → ℂ) → Set ℝ → ℂ → ℝ≥0∞
def multiplicity_value : multiplicity_type := fun γ s z => (regularFiber γ s z).encard
def signedDensity_type := (ℝ → ℂ) → Set ℝ → ℂ → ℂ
def signedDensity_value : signedDensity_type :=
  fun γ s z => ∑' t : regularFiber γ s z, unitVelocity γ t
def pathDensity_type := PiecewiseC1Path → ℂ → ℂ
def pathDensity_value : pathDensity_type :=
  fun γ => signedDensity γ (Ioo γ.path.a γ.path.b)
def chainDensity_type := IntegralChain → ℂ → ℂ
def chainDensity_value : chainDensity_type :=
  fun Γ z => ∑ γ ∈ Γ.support, (Γ γ : ℂ) * pathDensity γ z
def chainMultiplicity_type := IntegralChain → ℂ → ℝ≥0∞
def chainMultiplicity_value : chainMultiplicity_type :=
  fun Γ z => ∑ γ ∈ Γ.support, (Γ γ).natAbs * multiplicity γ (Ioo γ.path.a γ.path.b) z

def regularFiber_countable_type : Prop :=
  ∀ (γ : ℝ → ℂ) (s : Set ℝ) (z : ℂ), (regularFiber γ s z).Countable

def ae_velocity_zero_on_countable_image_type : Prop :=
  ∀ (γ : ℝ → ℂ) (S : Set ℂ), S.Countable →
    ∀ᵐ t ∂volume, γ t ∈ S → deriv γ t = 0

def norm_unitVelocity_type : Prop :=
  ∀ (γ : ℝ → ℂ) (t : ℝ), deriv γ t ≠ 0 → ‖unitVelocity γ t‖ = 1

def unitVelocity_mul_speed_type : Prop :=
  ∀ (γ : ℝ → ℂ) (t : ℝ),
    unitVelocity γ t * (‖deriv γ t‖ : ℂ) = deriv γ t

def norm_summable_iff_finite_type : Prop :=
  ∀ (γ : ℝ → ℂ) (s : Set ℝ) (z : ℂ),
    (Summable fun t : regularFiber γ s z => ‖unitVelocity γ t‖) ↔
      (regularFiber γ s z).Finite

def density_off_image_type : Prop :=
  ∀ (γ : ℝ → ℂ) (s : Set ℝ) (z : ℂ), z ∉ γ '' s → signedDensity γ s z = 0

def density_off_trace_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (z : ℂ), z ∉ γ.trace → pathDensity γ z = 0

def hausdorff_real_normalization_type : Prop :=
  (μH[1] : Measure ℝ) = volume

def hausdorff_complex_segment_type : Prop :=
  ∀ z w : ℂ, (μH[1] : Measure ℂ) (segment ℝ z w) = edist z w

/-- Covers in particular the canonical orthonormal scalar/E1 identification. -/
def hausdorff_scalar_isometry_type : Prop :=
  ∀ {E : Type} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (e : ℝ → E), Isometry e → ∀ s : Set ℝ,
      (μH[1] : Measure E) (e '' s) = volume s

def contour_integral_off_countable_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (q : ℂ → ℂ), ContinuousOn q γ.trace →
    ∀ S : Set ℂ, S.Countable → γ.integral q =
      ∫ t in γ.path.a..γ.path.b,
        if γ t ∈ S then 0 else q (γ t) * deriv γ t

def summable_iff_finite_type : Prop :=
  ∀ (γ : ℝ → ℂ) (s : Set ℝ) (z : ℂ),
    (Summable fun t : regularFiber γ s z => unitVelocity γ t) ↔
      (regularFiber γ s z).Finite

def hausdorff_e1_coordinates_type : Prop :=
  ∀ s : Set ℝ,
    (μH[1] : Measure (EuclideanSpace ℝ (Fin 1)))
      ((fun t : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => t)) '' s) = volume s

def local_injective_at_nonstationary_type : Prop :=
  ∀ (γ : ℝ → ℂ) (U : Set ℝ), IsOpen U → ContDiffOn ℝ 1 γ U →
    ∀ t ∈ U, deriv γ t ≠ 0 →
      ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧ V ⊆ U ∧ Set.InjOn γ V

def countable_injective_cover_type : Prop :=
  ∀ (γ : ℝ → ℂ) (U : Set ℝ), IsOpen U → ContDiffOn ℝ 1 γ U →
    ∃ C : Set (Set ℝ), C.Countable ∧
      (∀ V ∈ C, IsOpen V ∧ V ⊆ U ∧ Set.InjOn γ V) ∧
      {t | t ∈ U ∧ deriv γ t ≠ 0} ⊆ ⋃₀ C

def hausdorff_c1_image_finite_type : Prop :=
  ∀ (γ : ℝ → ℂ) (a b : ℝ), ContDiffOn ℝ 1 γ (Icc a b) →
    (μH[1] : Measure ℂ) (γ '' Icc a b) < ∞

def hausdorff_path_trace_finite_type : Prop :=
  ∀ γ : PiecewiseC1Path, (μH[1] : Measure ℂ) γ.trace < ∞

def path_speed_integrable_type : Prop :=
  ∀ γ : PiecewiseC1Path,
    IntegrableOn (fun t => ‖deriv γ t‖) (Ioo γ.path.a γ.path.b) volume

def hausdorff_chain_trace_finite_type : Prop :=
  ∀ Γ : IntegralChain, (μH[1] : Measure ℂ) Γ.trace < ∞

def chainDensity_off_trace_type : Prop :=
  ∀ (Γ : IntegralChain) (z : ℂ), z ∉ Γ.trace → chainDensity Γ z = 0

def density_remove_countable_type : Prop :=
  ∀ (γ : ℝ → ℂ) (s : Set ℝ) (S : Set ℂ), S.Countable →
    signedDensity γ (s \ γ ⁻¹' S) =ᵐ[μH[1]] signedDensity γ s

def hausdorff_c1_image_null_type : Prop :=
  ∀ (γ : ℝ → ℂ) (a b : ℝ), ContDiffOn ℝ 1 γ (Icc a b) →
    ∀ s : Set ℝ, volume s = 0 →
      (μH[1] : Measure ℂ) (γ '' (s ∩ Icc a b)) = 0

def multiplicity_lt_top_iff_type : Prop :=
  ∀ (γ : ℝ → ℂ) (s : Set ℝ) (z : ℂ),
    multiplicity γ s z < ∞ ↔ (regularFiber γ s z).Finite

def density_norm_le_multiplicity_type : Prop :=
  ∀ (γ : ℝ → ℂ) (s : Set ℝ) (z : ℂ), (regularFiber γ s z).Finite →
    ‖signedDensity γ s z‖ ≤ (multiplicity γ s z).toReal

def regularFiber_congr_type : Prop :=
  ∀ (γ η : ℝ → ℂ) (s : Set ℝ), IsOpen s → EqOn γ η s →
    ∀ z : ℂ, regularFiber γ s z = regularFiber η s z

def density_congr_type : Prop :=
  ∀ (γ η : ℝ → ℂ) (s : Set ℝ), IsOpen s → EqOn γ η s →
    signedDensity γ s = signedDensity η s

def stationary_density_zero_type : Prop :=
  ∀ (γ : ℝ → ℂ) (s : Set ℝ), (∀ t ∈ s, deriv γ t = 0) →
    signedDensity γ s = 0

def degenerate_path_pushforward_type : Prop :=
  ∀ γ : PiecewiseC1Path, γ.path.a = γ.path.b → ∀ q : ℂ → ℂ,
    Integrable (fun z => q z * pathDensity γ z) μH[1] ∧
    γ.integral q = ∫ z, q z * pathDensity γ z ∂μH[1]

def constant_path_pushforward_type : Prop :=
  ∀ (a b : ℝ) (hab : a ≤ b) (z : ℂ) (q : ℂ → ℂ),
    Integrable (fun w => q w * pathDensity (PiecewiseC1Path.const a b hab z) w) μH[1] ∧
    (PiecewiseC1Path.const a b hab z).integral q =
      ∫ w, q w * pathDensity (PiecewiseC1Path.const a b hab z) w ∂μH[1]

/-- Uniform two-point distortion from the actual strict derivative. -/
def strict_deriv_distortion_type : Prop :=
  ∀ (γ : ℝ → ℂ) (v : ℂ) (t : ℝ), HasStrictDerivAt γ v t →
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
        ∀ x ∈ V, ∀ y ∈ V,
          (‖v‖ - ε) * ‖x - y‖ ≤ ‖γ x - γ y‖ ∧
          ‖γ x - γ y‖ ≤ (‖v‖ + ε) * ‖x - y‖

/-- Upper and inverse lower Hausdorff bounds on arbitrary small subsets. -/
def local_hausdorff_bounds_type : Prop :=
  ∀ (γ : ℝ → ℂ) (v : ℂ) (t : ℝ), HasStrictDerivAt γ v t →
    ∀ ε : ℝ≥0, 0 < ε → (ε : ℝ) < ‖v‖ →
      ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧ Set.InjOn γ V ∧
        ∀ A ⊆ V,
          (μH[1] : Measure ℂ) (γ '' A) ≤ (‖v‖₊ + ε : ℝ≥0) * volume A ∧
          volume A ≤ (((Real.toNNReal (‖v‖ - ε))⁻¹ : ℝ≥0) : ℝ≥0∞) *
            (μH[1] : Measure ℂ) (γ '' A)

def countable_injective_partition_type : Prop :=
  ∀ (γ : ℝ → ℂ) (U : Set ℝ), IsOpen U → ContDiffOn ℝ 1 γ U →
    ∃ P : ℕ → Set ℝ,
      (∀ n, MeasurableSet (P n) ∧ P n ⊆ U ∧ Set.InjOn γ (P n) ∧
        MeasurableSet (γ '' P n)) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (⋃ n, P n) = {t | t ∈ U ∧ deriv γ t ≠ 0}

def hausdorff_c1_null_image_type : Prop :=
  ∀ (γ : ℝ → ℂ) (U : Set ℝ), IsOpen U → ContDiffOn ℝ 1 γ U →
    ∀ s : Set ℝ, s ⊆ U → volume s = 0 →
      (μH[1] : Measure ℂ) (γ '' s) = 0

def multiplicity_partition_type : Prop :=
  ∀ (γ : ℝ → ℂ) (s : Set ℝ) (P : ℕ → Set ℝ),
    (∀ n, Set.InjOn γ (P n)) →
    Pairwise (fun i j => Disjoint (P i) (P j)) →
    (⋃ n, P n) = {t | t ∈ s ∧ deriv γ t ≠ 0} →
    ∀ z : ℂ, multiplicity γ s z =
      ∑' n, (γ '' P n).indicator (fun _ => (1 : ℝ≥0∞)) z

def measurable_multiplicity_type : Prop :=
  ∀ (γ : ℝ → ℂ) (U s : Set ℝ), IsOpen U → ContDiffOn ℝ 1 γ U →
    MeasurableSet s → s ⊆ U → Measurable (multiplicity γ s)

def aemeasurable_multiplicity_type : Prop :=
  ∀ (γ : ℝ → ℂ) (U s : Set ℝ), IsOpen U → ContDiffOn ℝ 1 γ U →
    NullMeasurableSet s volume → s ⊆ U →
    AEMeasurable (multiplicity γ s) (μH[1] : Measure ℂ)

/-! Full analytic area and pushforward obligations. -/

/-- The unsigned analytic area identity also supplies the required integrability. -/
def path_area_type : Prop :=
  ∀ γ : PiecewiseC1Path,
    AEMeasurable (multiplicity γ (Ioo γ.path.a γ.path.b)) μH[1] ∧
    (∀ᵐ z ∂(μH[1] : Measure ℂ),
      (regularFiber γ (Ioo γ.path.a γ.path.b) z).Finite) ∧
    (∫⁻ z, multiplicity γ (Ioo γ.path.a γ.path.b) z ∂μH[1]) =
      ∫⁻ t in Ioo γ.path.a γ.path.b, ENNReal.ofReal ‖deriv γ t‖

def path_pushforward_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (q : ℂ → ℂ), ContinuousOn q γ.trace →
    Integrable (fun z => q z * pathDensity γ z) μH[1] ∧
    γ.integral q = ∫ z, q z * pathDensity γ z ∂μH[1]

/-- Includes closed cycles by applying it to their unchanged underlying chain. -/
def chain_pushforward_type : Prop :=
  ∀ (Γ : IntegralChain) (q : ℂ → ℂ), ContinuousOn q Γ.trace →
    (∀ᵐ z ∂(μH[1] : Measure ℂ), chainMultiplicity Γ z < ∞) ∧
    Integrable (fun z => q z * chainDensity Γ z) μH[1] ∧
    Γ.integral q = ∫ z, q z * chainDensity Γ z ∂μH[1]

/-- General unsigned area formula on bounded Lebesgue measurable restrictions.
Without a compact neighborhood, the speed integral can be infinite. -/
def measurable_restriction_area_type : Prop :=
  ∀ (γ : ℝ → ℂ) (U s : Set ℝ), IsOpen U → ContDiffOn ℝ 1 γ U →
    s ⊆ U → Bornology.IsBounded s → NullMeasurableSet s volume →
    AEMeasurable (multiplicity γ s) μH[1] ∧
    (∫⁻ z, multiplicity γ s z ∂μH[1]) =
      ∫⁻ t in s, ENNReal.ofReal ‖deriv γ t‖

/-- Completed Lebesgue measurability, arbitrary bounded subsets, and actual C1 maps.
`K` is a supplied compact parameter neighborhood controlling the weight and speed;
no injectivity or nonzero-velocity assumption appears. -/
def measurable_restriction_pushforward_type : Prop :=
  ∀ (γ : ℝ → ℂ) (U K s : Set ℝ), IsOpen U → ContDiffOn ℝ 1 γ U →
    IsCompact K → K ⊆ U → s ⊆ K → NullMeasurableSet s volume →
    ∀ q : ℂ → ℂ, ContinuousOn q (γ '' K) →
    AEMeasurable (multiplicity γ s) μH[1] ∧
    (∀ᵐ z ∂(μH[1] : Measure ℂ), (regularFiber γ s z).Finite) ∧
    (∫⁻ z, multiplicity γ s z ∂μH[1]) =
      (∫⁻ t in s, ENNReal.ofReal ‖deriv γ t‖) ∧
    IntegrableOn (fun t => q (γ t) * deriv γ t) s volume ∧
    Integrable (fun z => q z * signedDensity γ s z) μH[1] ∧
    (∫ t in s, q (γ t) * deriv γ t) =
      ∫ z, q z * signedDensity γ s z ∂μH[1]

/-- A stronger, unbounded version of the extended area identity. -/
def area_of_nullMeasurableSet_type : Prop :=
  ∀ (γ : ℝ → ℂ) (U s : Set ℝ), IsOpen U → ContDiffOn ℝ 1 γ U →
    NullMeasurableSet s volume → s ⊆ U →
    AEMeasurable (multiplicity γ s) μH[1] ∧
      (∫⁻ z, multiplicity γ s z ∂μH[1]) =
        ∫⁻ t in s, ENNReal.ofReal ‖deriv γ t‖

/-- With integrable original weighted velocity, compact containment and
continuity of the weight are unnecessary. -/
def pushforward_of_nullMeasurableSet_type : Prop :=
  ∀ (γ : ℝ → ℂ) (U s : Set ℝ), IsOpen U → ContDiffOn ℝ 1 γ U →
    NullMeasurableSet s volume → s ⊆ U →
    ∀ q : ℂ → ℂ, IntegrableOn (fun t => q (γ t) * deriv γ t) s volume →
    Integrable (fun z => q z * signedDensity γ s z) μH[1] ∧
      (∫ t in s, q (γ t) * deriv γ t) = ∫ z, q z * signedDensity γ s z ∂μH[1]

/-- Exact absolute chain area and its finiteness. -/
def chain_absolute_area_type : Prop :=
  ∀ Γ : IntegralChain,
    AEMeasurable (chainMultiplicity Γ) μH[1] ∧
    (∫⁻ z, chainMultiplicity Γ z ∂μH[1]) =
      ∑ γ ∈ Γ.support, (Γ γ).natAbs *
        ∫⁻ t in Ioo γ.path.a γ.path.b, ENNReal.ofReal ‖deriv γ t‖ ∧
    (∫⁻ z, chainMultiplicity Γ z ∂μH[1]) < ∞

def path_summable_type : Prop :=
  ∀ γ : PiecewiseC1Path, ∀ᵐ z ∂(μH[1] : Measure ℂ),
    Summable (fun t : regularFiber γ (Ioo γ.path.a γ.path.b) z => unitVelocity γ t)

def cycle_pushforward_type : Prop :=
  ∀ (Γ : IntegralCycle) (q : ℂ → ℂ), ContinuousOn q Γ.trace →
    (∀ᵐ z ∂(μH[1] : Measure ℂ), chainMultiplicity Γ.chain z < ∞) ∧
    Integrable (fun z => q z * chainDensity Γ.chain z) μH[1] ∧
    Γ.integral q = ∫ z, q z * chainDensity Γ.chain z ∂μH[1]

end Specs.D12Complex.Ch04.SignedCurveMultiplicity
