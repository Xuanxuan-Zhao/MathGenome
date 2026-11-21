import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.Plancherel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.CalderonZygmundLp

/-! The actual line multiplier of paper.tex:18342–18385.  In particular the value
at frequency zero is zero; the singleton is discarded only in L² proofs. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace ExpandedFA.SingularIntegrals.HilbertTransform

/-- The canonical coordinate identification x ↦ (x) of the line with ℝ¹. -/
def lineIsometry : ℝ ≃ₗᵢ[ℝ] ExpandedFA.Fourier.Euclidean 1 :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr


abbrev LineLp (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) :=
  Lp 𝕜 p (volume : Measure ℝ)
abbrev ComplexL2 := LineLp ℂ 2
abbrev RealL2 := LineLp ℝ 2

def multiplier (ξ : ℝ) : ℂ :=
  if ξ = 0 then 0 else if 0 < ξ then -Complex.I else Complex.I

lemma multiplier_measurable : Measurable multiplier := by
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

lemma multiplier_norm_le (ξ : ℝ) : ‖multiplier ξ‖ ≤ 1 := by
  unfold multiplier
  split_ifs <;> simp

lemma multiplier_mul_memLp (f : ComplexL2) :
    MemLp (fun ξ => multiplier ξ * f ξ) 2 (volume : Measure ℝ) := by
  apply (Lp.memLp f).of_le
    (multiplier_measurable.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact .of_forall fun ξ => by
    change ‖multiplier ξ * f ξ‖ ≤ ‖f ξ‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (multiplier_norm_le ξ)

/-- Pointwise multiplication, as an actual equivalence class. -/
def frequencyAction (f : ComplexL2) : ComplexL2 :=
  (multiplier_mul_memLp f).toLp (fun ξ => multiplier ξ * f ξ)

/-- Native Fourier transform on the ordinary real line, with exp(-2πixξ). -/
def lineFourier : ComplexL2 ≃ₗᵢ[ℂ] ComplexL2 := Lp.fourierTransformₗᵢ ℝ ℂ

/-- The fixed multiplier definition, independent of all future CZ realizations. -/
def complexHilbert (f : ComplexL2) : ComplexL2 :=
  lineFourier.symm (frequencyAction (lineFourier f))

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace Specs.ExpandedFA.SingularIntegrals.HilbertTransform
open _root_.ExpandedFA.SingularIntegrals.HilbertTransform
open _root_.ExpandedFA.SingularIntegrals

abbrev complexHilbertType := ComplexL2 → ComplexL2
def complexHilbertValue : complexHilbertType := complexHilbert

def MultiplierFormula : Prop := ∀ f : ComplexL2,
  (lineFourier (complexHilbert f) : ℝ → ℂ) =ᵐ[volume]
    fun ξ => multiplier ξ * (lineFourier f) ξ

def Isometry : Prop := ∀ f : ComplexL2, ‖complexHilbert f‖ = ‖f‖
def Square : Prop := ∀ f : ComplexL2, complexHilbert (complexHilbert f) = -f

def BoundedLinear : Prop := ∃ T : ComplexL2 →L[ℂ] ComplexL2,
  ∀ f, T f = complexHilbert f

/-- The scalar-real embedding, also used for every interior exponent. -/
noncomputable def complexify (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    LineLp ℝ p →L[ℝ] LineLp ℂ p :=
  Complex.ofRealCLM.compLpL p volume


/-- Pullback along ℝ¹ → ℝ; no coordinate norm or measure is changed. -/
def toEuclidean {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) (f : LineLp 𝕜 p) :
    Lp 𝕜 p (volume : Measure (StandardConvolution.Space 1)) :=
  Lp.compMeasurePreserving lineIsometry.symm lineIsometry.symm.measurePreserving f

def fromEuclidean {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞)
    (f : Lp 𝕜 p (volume : Measure (StandardConvolution.Space 1))) : LineLp 𝕜 p :=
  Lp.compMeasurePreserving lineIsometry lineIsometry.measurePreserving f

def CoordinateTransport : Prop :=
  MeasurePreserving lineIsometry (volume : Measure ℝ) volume ∧
  (∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) (f : LineLp 𝕜 p),
    fromEuclidean p (toEuclidean p f) = f) ∧
  (∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞)
      (f : Lp 𝕜 p (volume : Measure (StandardConvolution.Space 1))),
    toEuclidean p (fromEuclidean p f) = f)

/-- The standard CZ structure supplies translation invariance, the C¹ bounds,
the off-zero distribution identity and its action on all smooth compact tests.
The last two clauses fix which kernel distribution and which L² operator it is. -/
def HasStandardRealization (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) : Prop :=
  ∃ T : StandardConvolution.StandardConvolutionOperator 𝕜 1,
    (∀ t : ℝ, t ≠ 0 →
      T.kernel.function (lineIsometry t) = ((Real.pi * t : ℝ) : 𝕜)⁻¹) ∧
    (∀ φ : StandardConvolution.Tests 𝕜 1,
      Tendsto (fun ε : ℝ => ∫ t in {t : ℝ | ε < |t|},
          ((Real.pi * t : ℝ) : 𝕜)⁻¹ * φ (lineIsometry t))
        (𝓝[>] 0) (𝓝 (T.distribution φ))) ∧
    (∀ f : LineLp 𝕜 2, fromEuclidean 2 (T.operator (toEuclidean 2 f)) = A f)

/-- The real operator is required to be the actual restriction. -/
def IsRealRestriction (A : RealL2 →L[ℝ] RealL2) : Prop :=
  ∀ f : RealL2, complexHilbert (complexify 2 f) = complexify 2 (A f)

def RealValuedPreservation : Prop := ∀ f : ComplexL2,
  (∀ᵐ x : ℝ ∂volume, (f x).im = 0) →
    ∀ᵐ x : ℝ ∂volume, (complexHilbert f x).im = 0

/-- The concrete symmetric truncated integral. Absolute integrability and L²
membership are conclusions in `TruncationConvergence`, not conventions for a
totalized integral. -/
def truncated {𝕜 : Type} [RCLike 𝕜] (ε : ℝ) (f : ℝ → 𝕜) (x : ℝ) : 𝕜 :=
  ∫ t in {t : ℝ | ε < |t|}, ((Real.pi * t : ℝ) : 𝕜)⁻¹ * f (x - t)

def TruncationConvergence (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) : Prop :=
  (∀ (ε : ℝ), 0 < ε → ∀ f : LineLp 𝕜 2,
    (∀ x : ℝ, IntegrableOn
      (fun t => ((Real.pi * t : ℝ) : 𝕜)⁻¹ * f (x - t)) {t : ℝ | ε < |t|}) ∧
    MemLp (truncated ε f) 2 volume) ∧
  ∀ f : LineLp 𝕜 2,
    Tendsto (fun ε : ℝ => eLpNorm (fun x => truncated ε f x - A f x) 2 volume)
      (𝓝[>] 0) (𝓝 0)

/-- A compatible family on the line, including the weak extension on all L¹. -/
structure Extensions (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) where
  strong : ∀ p : CZLp.InteriorExponent,
    LineLp 𝕜 p.val →L[𝕜] LineLp 𝕜 p.val
  weak : LineLp 𝕜 1 →ₗ[𝕜] (ℝ →ₘ[(volume : Measure ℝ)] 𝕜)
  strong_agrees : ∀ (p : CZLp.InteriorExponent) (f : ℝ → 𝕜)
    (hp : MemLp f p.val volume) (h2 : MemLp f 2 volume),
    (strong p (hp.toLp f) : ℝ → 𝕜) =ᵐ[volume] (A (h2.toLp f) : ℝ → 𝕜)
  pairwise_agrees : ∀ (p q : CZLp.InteriorExponent) (f : ℝ → 𝕜)
    (hp : MemLp f p.val volume) (hq : MemLp f q.val volume),
    (strong p (hp.toLp f) : ℝ → 𝕜) =ᵐ[volume] (strong q (hq.toLp f) : ℝ → 𝕜)
  weak_agrees : ∀ (f : ℝ → 𝕜) (h1 : MemLp f 1 volume) (h2 : MemLp f 2 volume),
    (weak (h1.toLp f) : ℝ → 𝕜) =ᵐ[volume] (A (h2.toLp f) : ℝ → 𝕜)
  weak_strong_agrees : ∀ (p : CZLp.InteriorExponent) (f : ℝ → 𝕜)
    (h1 : MemLp f 1 volume) (hp : MemLp f p.val volume),
    (weak (h1.toLp f) : ℝ → 𝕜) =ᵐ[volume] (strong p (hp.toLp f) : ℝ → 𝕜)
  weak_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : LineLp 𝕜 1) (t : ℝ), 0 < t →
    volume {x : ℝ | t < ‖weak f x‖} ≤ ENNReal.ofReal (C / t) * ENNReal.ofReal ‖f‖

/-- Natural scalar embedding on all strong and weak realizations. -/
def ExtensionsCompatible (A : RealL2 →L[ℝ] RealL2)
    (R : Extensions ℝ A) (C : Extensions ℂ complexHilbert) : Prop :=
  (∀ (p : CZLp.InteriorExponent) (f : LineLp ℝ p.val),
    C.strong p (complexify p.val f) = complexify p.val (R.strong p f)) ∧
  (∀ f : LineLp ℝ 1, (C.weak (complexify 1 f) : ℝ → ℂ) =ᵐ[volume]
    fun x => (R.weak f x : ℂ))

def indicatorL2 (𝕜 : Type) [RCLike 𝕜] : LineLp 𝕜 2 :=
  indicatorConstLp 2 (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc (by simp) 1

def indicatorImage (x : ℝ) : ℝ := Real.pi⁻¹ * Real.log |x / (x - 1)|

/-- Equality of L² representatives is necessarily an a.e. statement. The
pointwise principal value below fixes the formula at every nonendpoint. -/
def IndicatorFormula (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) : Prop :=
  ((A (indicatorL2 𝕜) : ℝ → 𝕜) =ᵐ[volume] fun x => (indicatorImage x : 𝕜)) ∧
  ∀ x : ℝ, x ≠ 0 → x ≠ 1 →
    Tendsto (fun ε : ℝ => truncated ε ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜))) x)
      (𝓝[>] 0) (𝓝 (indicatorImage x : 𝕜))

/-- One fixed bounded integrable input witnesses both endpoint failures. -/
def EndpointFailure (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) : Prop :=
  ¬MemLp (A (indicatorL2 𝕜) : ℝ → 𝕜) 1 volume ∧
  ¬MemLp (A (indicatorL2 𝕜) : ℝ → 𝕜) ∞ volume

/-- The normalized tempered principal value has exactly the Hilbert multiplier
as its Fourier transform, with scalar-linear transposition on Schwartz tests. -/
def NormalizedPrincipalValue : Prop := ∃ K : LineTempered,
  (∀ φ : LineSchwartz, K φ = (Real.pi : ℂ)⁻¹ *
    Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues.principalValuePairingValue φ) ∧
  ∀ φ : LineSchwartz, K (FourierTransform.fourierCLM ℂ LineSchwartz φ) =
    ∫ ξ : ℝ, multiplier ξ * φ ξ

/-- The analytic integrability assertion for each genuine truncated tail. -/
def TruncatedIntegrability : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (ε : ℝ), 0 < ε → ∀ (f : LineLp 𝕜 2) (x : ℝ),
  IntegrableOn (fun t => ((Real.pi * t : ℝ) : 𝕜)⁻¹ * f (x - t))
    {t : ℝ | ε < |t|}

/-- The real restriction is an isometry and squares to minus the identity. -/
def RealL2Properties : Prop := ∃ A : RealL2 →L[ℝ] RealL2,
  IsRealRestriction A ∧
  (∀ f : RealL2, ‖A f‖ = ‖f‖) ∧ (∀ f : RealL2, A (A f) = -f)

/-- The explicitly transported off-zero Hilbert kernel. -/
def kernelFunction (𝕜 : Type) [RCLike 𝕜] (x : StandardConvolution.Space 1) : 𝕜 :=
  ((Real.pi * lineIsometry.symm x : ℝ) : 𝕜)⁻¹

/-- Both scalar fields have the specified C¹ size and gradient bounds. -/
def StandardKernelBounds : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  ∃ k : StandardConvolution.StandardKernel 𝕜 1,
    k.function = kernelFunction 𝕜

/-- Translation invariance on equivalence classes on the ordinary line. -/
def LineTranslationInvariant (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) : Prop :=
  ∀ (a : ℝ) (f g : LineLp 𝕜 2),
    (g : ℝ → 𝕜) =ᵐ[volume] (fun x => f (x - a)) →
    (A g : ℝ → 𝕜) =ᵐ[volume] (fun x => A f (x - a))

def TranslationProperties : Prop :=
  LineTranslationInvariant ℂ complexHilbert ∧
  ∃ A : RealL2 →L[ℝ] RealL2, IsRealRestriction A ∧ LineTranslationInvariant ℝ A

/-- Both scalar realizations are tied to the original Fourier operator. -/
def StandardRealizations : Prop :=
  HasStandardRealization ℂ complexHilbert ∧
  ∃ A : RealL2 →L[ℝ] RealL2, IsRealRestriction A ∧ HasStandardRealization ℝ A

/-- The real and complex extensions agree under the natural scalar embedding. -/
def CompatibleExtensions : Prop :=
  ∃ A : RealL2 →L[ℝ] RealL2, IsRealRestriction A ∧
    ∃ (R : Extensions ℝ A) (C : Extensions ℂ complexHilbert), ExtensionsCompatible A R C

/-- The pointwise principal value is fixed at every nonendpoint. -/
def IndicatorPrincipalValue : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (x : ℝ),
  x ≠ 0 → x ≠ 1 →
  Tendsto (fun ε : ℝ => truncated ε
    ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜))) x)
    (𝓝[>] 0) (𝓝 (indicatorImage x : 𝕜))

/-- Full remaining source scope, on the same actual operator and its restriction.
These are obligations, not certificates supplied as hypotheses to the core. -/
def FullTheorem : Prop :=
  MultiplierFormula ∧ Isometry ∧ Square ∧ BoundedLinear ∧ NormalizedPrincipalValue ∧
  RealValuedPreservation ∧
  HasStandardRealization ℂ complexHilbert ∧ TruncationConvergence ℂ complexHilbert ∧
  IndicatorFormula ℂ complexHilbert ∧ EndpointFailure ℂ complexHilbert ∧
  ∃ A : RealL2 →L[ℝ] RealL2,
    IsRealRestriction A ∧
    (∀ f : RealL2, ‖A f‖ = ‖f‖) ∧ (∀ f : RealL2, A (A f) = -f) ∧
    HasStandardRealization ℝ A ∧ TruncationConvergence ℝ A ∧
    IndicatorFormula ℝ A ∧ EndpointFailure ℝ A ∧
    ∃ (R : Extensions ℝ A) (C : Extensions ℂ complexHilbert), ExtensionsCompatible A R C

end Specs.ExpandedFA.SingularIntegrals.HilbertTransform
