import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Independent expected objects and proposition types for the periodic foundation.
The implementation declares the public interface in `P102.Periodic`. -/
noncomputable section
open MeasureTheory Set
open scoped Real ENNReal ComplexConjugate

namespace P102.Periodic.Expected

abbrev Circle (T : ℝ) := AddCircle T

variable (T : ℝ) [Fact (0 < T)]

abbrev haar : Measure (Circle T) := AddCircle.haarAddCircle
abbrev mode (k : ℤ) : C(Circle T, ℂ) := fourier k
abbrev L1 : Type := Lp ℂ 1 (haar T)

/-- Defined on representatives; the a.e. invariance theorem gives the L¹ interface. -/
def coefficient (f : Circle T → ℂ) (k : ℤ) : ℂ :=
  ∫ x, f x * conj (mode T k x) ∂haar T

def coefficientL1 (f : L1 T) (k : ℤ) : ℂ := coefficient T f k

/-- The totalized Bochner integral; pointwise existence is specified separately. -/
def convolution (f g : Circle T → ℂ) (x : Circle T) : ℂ :=
  ∫ y, f (x - y) * g y ∂haar T

def ConvolutionExistsAt (f g : Circle T → ℂ) (x : Circle T) : Prop :=
  Integrable (fun y => f (x - y) * g y) (haar T)

def frequencies (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

def partialSum (N : ℕ) (f : Circle T → ℂ) (x : Circle T) : ℂ :=
  ∑ k ∈ frequencies N, coefficient T f k * mode T k x

def dirichletKernel (N : ℕ) (x : Circle T) : ℂ :=
  ∑ k ∈ frequencies N, mode T k x

def fejerKernel (N : ℕ) (x : Circle T) : ℂ :=
  ((N + 1 : ℝ)⁻¹ * ‖∑ j ∈ Finset.range (N + 1), mode T (j : ℤ) x‖ ^ 2 : ℝ)

def fejerMean (N : ℕ) (f : Circle T → ℂ) (x : Circle T) : ℂ :=
  (N + 1 : ℂ)⁻¹ * ∑ j ∈ Finset.range (N + 1), partialSum T j f x

/-- The source's rational Poisson formula, written using the real part of mode one. -/
def poissonKernel (r : ℝ) (x : Circle T) : ℝ :=
  (1 - r ^ 2) / (1 - 2 * r * (mode T 1 x).re + r ^ 2)

/-- The source's Abel series. Convergence for 0 ≤ r < 1 is a later theorem. -/
def abelMean (r : ℝ) (f : Circle T → ℂ) (x : Circle T) : ℂ :=
  ∑' k : ℤ, (r ^ k.natAbs : ℂ) * coefficient T f k * mode T k x

/-- Synthesis of finite integer-frequency coefficients as a continuous function. -/
def synthesis : (ℤ →₀ ℂ) →ₗ[ℂ] C(Circle T, ℂ) :=
  Finsupp.linearCombination ℂ (mode T)

def complexTrigPolynomials : Submodule ℂ C(Circle T, ℂ) := (synthesis T).range

def complexTrigDegree (n : ℕ) : Submodule ℂ C(Circle T, ℂ) :=
  (Finsupp.supported ℂ ℂ (Set.Icc (-(n : ℤ)) (n : ℤ))).map (synthesis T)

/-- Conjugate symmetry includes the zero frequency. -/
def symmetricCoefficients : Submodule ℝ (ℤ →₀ ℂ) where
  carrier := {c | ∀ k, c (-k) = conj (c k)}
  zero_mem' := by simp
  add_mem' := by
    intro c d hc hd k
    simpa using congrArg₂ (· + ·) (hc k) (hd k)
  smul_mem' := by
    intro a c hc k
    simp only [Finsupp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    rw [hc k]

def realSynthesis : (ℤ →₀ ℂ) →ₗ[ℝ] C(Circle T, ℝ) where
  toFun c := ⟨fun x => (synthesis T c x).re,
    Complex.continuous_re.comp (synthesis T c).continuous⟩
  map_add' c d := by ext x; simp
  map_smul' a c := by ext x; simp

def realTrigPolynomials : Submodule ℝ C(Circle T, ℝ) :=
  (symmetricCoefficients).map (realSynthesis T)

def realTrigDegree (n : ℕ) : Submodule ℝ C(Circle T, ℝ) :=
  ((Finsupp.supported ℂ ℂ (Set.Icc (-(n : ℤ)) (n : ℤ))).restrictScalars ℝ ⊓
    symmetricCoefficients).map (realSynthesis T)

/-- Rescaling between arbitrary positive periods; angular coordinates use U = 2π. -/
def rescale (U : ℝ) [hU : Fact (0 < U)] : Circle T ≃+ Circle U :=
  AddCircle.equivAddCircle T U ((Fact.out : 0 < T).ne') (hU.out.ne')

instance angularPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev toAngle := rescale T (2 * Real.pi)


-- Full proposition types, independent of the implementation module.
def probability : Prop := (haar T) Set.univ = 1

def translation : Prop := ∀ a : Circle T,
  MeasurePreserving (fun x => a + x) (haar T) (haar T)

def integralInterval : Prop := ∀ (f : Circle T → ℂ) (a : ℝ),
  (∫ x, f x ∂haar T) = T⁻¹ • ∫ t in a..a + T, f (t : Circle T)

def modeFormula : Prop := ∀ (k : ℤ) (t : ℝ),
  mode T k (t : Circle T) = Complex.exp (2 * Real.pi * Complex.I * k * t / T)

def coefficientCongr : Prop := ∀ (f g : Circle T → ℂ),
  f =ᵐ[haar T] g → ∀ k, coefficient T f k = coefficient T g k

def coefficientInterval : Prop := ∀ (f : Circle T → ℂ) (k : ℤ) (a : ℝ),
  coefficient T f k = (1 / T : ℝ) • ∫ t in a..a + T,
    f (t : Circle T) * Complex.exp (-(2 * Real.pi * Complex.I * k * t / T))

def coefficientL1Representative : Prop := ∀ (f : L1 T) (g : Circle T → ℂ),
  (f : Circle T → ℂ) =ᵐ[haar T] g → ∀ k, coefficientL1 T f k = coefficient T g k

def continuousDensity (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    DenseRange (ContinuousMap.toLp p (haar T) 𝕜 : C(Circle T, 𝕜) →L[𝕜] Lp 𝕜 p (haar T))

def rescaleFormula : Prop := ∀ (U : ℝ) [Fact (0 < U)] (t : ℝ),
  rescale T U (t : Circle T) = ((U * t / T : ℝ) : Circle U)

def rescaleMeasure : Prop := ∀ (U : ℝ) [Fact (0 < U)],
  MeasurePreserving (rescale T U) (haar T) (haar U)

def rescaleMode : Prop := ∀ (U : ℝ) [Fact (0 < U)] (k : ℤ) (x : Circle T),
  mode U k (rescale T U x) = mode T k x

def rescaleCoefficient : Prop := ∀ (U : ℝ) [Fact (0 < U)]
  (f : Circle U → ℂ) (k : ℤ),
  coefficient T (fun x => f (rescale T U x)) k = coefficient U f k

def rescaleConvolution : Prop := ∀ (U : ℝ) [Fact (0 < U)]
  (f g : Circle U → ℂ) (x : Circle T),
  convolution T (fun y => f (rescale T U y)) (fun y => g (rescale T U y)) x =
    convolution U f g (rescale T U x)

def rescalePartialSum : Prop := ∀ (U : ℝ) [Fact (0 < U)]
  (N : ℕ) (f : Circle U → ℂ) (x : Circle T),
  partialSum T N (fun y => f (rescale T U y)) x = partialSum U N f (rescale T U x)

def rescaleKernels : Prop := ∀ (U : ℝ) [Fact (0 < U)] (N : ℕ) (r : ℝ)
  (f : Circle U → ℂ) (x : Circle T),
  dirichletKernel T N x = dirichletKernel U N (rescale T U x) ∧
  fejerKernel T N x = fejerKernel U N (rescale T U x) ∧
  fejerMean T N (fun y => f (rescale T U y)) x = fejerMean U N f (rescale T U x) ∧
  poissonKernel T r x = poissonKernel U r (rescale T U x) ∧
  abelMean T r (fun y => f (rescale T U y)) x = abelMean U r f (rescale T U x)

/-- Quantitative density for every completed-Haar Lp representative. -/
def completedDensity (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
  ∀ (f : NullMeasurableSpace (Circle T) (haar T) → 𝕜),
    MemLp f p (haar T).completion →
    ∀ (ε : ℝ≥0∞), ε ≠ 0 → ∃ g : C(Circle T, 𝕜),
      eLpNorm (fun x : NullMeasurableSpace (Circle T) (haar T) => f x - g x)
        p (haar T).completion ≤ ε

def angularMode : Prop := ∀ (k : ℤ) (v : ℝ),
  mode (2 * Real.pi) k (v : Circle (2 * Real.pi)) = Complex.exp (Complex.I * k * v)

def angularIntegral : Prop := ∀ (f : Circle (2 * Real.pi) → ℂ) (a : ℝ),
  (∫ x, f (toAngle T x) ∂haar T) =
    (2 * Real.pi)⁻¹ • ∫ v in a..a + 2 * Real.pi, f (v : Circle (2 * Real.pi))

def poissonFormula : Prop := ∀ (r t : ℝ),
  poissonKernel T r (t : Circle T) =
    (1 - r ^ 2) / (1 - 2 * r * Real.cos (2 * Real.pi * t / T) + r ^ 2)

def symmetricSynthesis : Prop := ∀ c ∈ symmetricCoefficients, ∀ x : Circle T,
  (realSynthesis T c x : ℂ) = synthesis T c x

def synthesisTransport : Prop := ∀ (U : ℝ) [Fact (0 < U)] (c : ℤ →₀ ℂ) (x : Circle T),
  synthesis U c (rescale T U x) = synthesis T c x ∧
  realSynthesis U c (rescale T U x) = realSynthesis T c x

def intervalMeasure : Prop := ∀ a : ℝ,
  MeasurePreserving (fun t : ℝ => (t : Circle T))
    (ENNReal.ofReal (T⁻¹) • volume.restrict (Ioc a (a + T))) (haar T)

def coefficientSynthesis : Prop := ∀ (c : ℤ →₀ ℂ) (k : ℤ),
  coefficient T (synthesis T c) k = c k

def realSynthesisIff : Prop := ∀ c : ℤ →₀ ℂ,
  (∀ x : Circle T, (synthesis T c x).im = 0) ↔ c ∈ symmetricCoefficients

def complexTrigTransport : Prop := ∀ (U : ℝ) [Fact (0 < U)]
  (f : C(Circle U, ℂ)) (g : C(Circle T, ℂ)),
  (∀ x, g x = f (rescale T U x)) → ∀ n : ℕ,
    (g ∈ complexTrigPolynomials T ↔ f ∈ complexTrigPolynomials U) ∧
    (g ∈ complexTrigDegree T n ↔ f ∈ complexTrigDegree U n)

def realTrigTransport : Prop := ∀ (U : ℝ) [Fact (0 < U)]
  (f : C(Circle U, ℝ)) (g : C(Circle T, ℝ)),
  (∀ x, g x = f (rescale T U x)) → ∀ n : ℕ,
    (g ∈ realTrigPolynomials T ↔ f ∈ realTrigPolynomials U) ∧
    (g ∈ realTrigDegree T n ↔ f ∈ realTrigDegree U n)

-- Expected definition types and values.
def CircleType : Type 1 := ℝ → Type

def CircleValue (T : ℝ) := AddCircle T

def haarType : Type := ∀ (T : ℝ) [Fact (0 < T)], Measure (Circle T)

def haarValue : Measure (Circle T) := AddCircle.haarAddCircle

def modeType : Type := ∀ (T : ℝ), ℤ → C(Circle T, ℂ)

def modeValue (k : ℤ) : C(Circle T, ℂ) := fourier k

def L1Type : Type 1 := ∀ (T : ℝ) [Fact (0 < T)], Type

def L1Value : Type := Lp ℂ 1 (haar T)

def coefficientType : Type := ∀ (T : ℝ) [Fact (0 < T)], (Circle T → ℂ) → ℤ → ℂ

def coefficientValue (f : Circle T → ℂ) (k : ℤ) : ℂ :=
  ∫ x, f x * conj (mode T k x) ∂haar T

def coefficientL1Type : Type := ∀ (T : ℝ) [Fact (0 < T)], L1 T → ℤ → ℂ

def coefficientL1Value (f : L1 T) (k : ℤ) : ℂ := coefficient T f k

def convolutionType : Type := ∀ (T : ℝ) [Fact (0 < T)], (Circle T → ℂ) → (Circle T → ℂ) → Circle T → ℂ

def convolutionValue (f g : Circle T → ℂ) (x : Circle T) : ℂ :=
  ∫ y, f (x - y) * g y ∂haar T

def ConvolutionExistsAtType : Type := ∀ (T : ℝ) [Fact (0 < T)], (Circle T → ℂ) → (Circle T → ℂ) → Circle T → Prop

def ConvolutionExistsAtValue (f g : Circle T → ℂ) (x : Circle T) : Prop :=
  Integrable (fun y => f (x - y) * g y) (haar T)

def frequenciesType : Type := ℕ → Finset ℤ

def frequenciesValue (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

def partialSumType : Type := ∀ (T : ℝ) [Fact (0 < T)], ℕ → (Circle T → ℂ) → Circle T → ℂ

def partialSumValue (N : ℕ) (f : Circle T → ℂ) (x : Circle T) : ℂ :=
  ∑ k ∈ frequencies N, coefficient T f k * mode T k x

def dirichletKernelType : Type := ∀ (T : ℝ), ℕ → Circle T → ℂ

def dirichletKernelValue (N : ℕ) (x : Circle T) : ℂ :=
  ∑ k ∈ frequencies N, mode T k x

def fejerKernelType : Type := ∀ (T : ℝ), ℕ → Circle T → ℂ

def fejerKernelValue (N : ℕ) (x : Circle T) : ℂ :=
  ((N + 1 : ℝ)⁻¹ * ‖∑ j ∈ Finset.range (N + 1), mode T (j : ℤ) x‖ ^ 2 : ℝ)

def fejerMeanType : Type := ∀ (T : ℝ) [Fact (0 < T)], ℕ → (Circle T → ℂ) → Circle T → ℂ

def fejerMeanValue (N : ℕ) (f : Circle T → ℂ) (x : Circle T) : ℂ :=
  (N + 1 : ℂ)⁻¹ * ∑ j ∈ Finset.range (N + 1), partialSum T j f x

def poissonKernelType : Type := ∀ (T : ℝ), ℝ → Circle T → ℝ

def poissonKernelValue (r : ℝ) (x : Circle T) : ℝ :=
  (1 - r ^ 2) / (1 - 2 * r * (mode T 1 x).re + r ^ 2)

def abelMeanType : Type := ∀ (T : ℝ) [Fact (0 < T)], ℝ → (Circle T → ℂ) → Circle T → ℂ

def abelMeanValue (r : ℝ) (f : Circle T → ℂ) (x : Circle T) : ℂ :=
  ∑' k : ℤ, (r ^ k.natAbs : ℂ) * coefficient T f k * mode T k x

def synthesisType : Type := ∀ (T : ℝ), (ℤ →₀ ℂ) →ₗ[ℂ] C(Circle T, ℂ)

def synthesisValue : (ℤ →₀ ℂ) →ₗ[ℂ] C(Circle T, ℂ) :=
  Finsupp.linearCombination ℂ (mode T)

def complexTrigPolynomialsType : Type := ∀ (T : ℝ), Submodule ℂ C(Circle T, ℂ)

def complexTrigPolynomialsValue : Submodule ℂ C(Circle T, ℂ) := (synthesis T).range

def complexTrigDegreeType : Type := ∀ (T : ℝ), ℕ → Submodule ℂ C(Circle T, ℂ)

def complexTrigDegreeValue (n : ℕ) : Submodule ℂ C(Circle T, ℂ) :=
  (Finsupp.supported ℂ ℂ (Set.Icc (-(n : ℤ)) (n : ℤ))).map (synthesis T)

def symmetricCoefficientsType : Type := Submodule ℝ (ℤ →₀ ℂ)

def symmetricCoefficientsValue : Submodule ℝ (ℤ →₀ ℂ) where
  carrier := {c | ∀ k, c (-k) = conj (c k)}
  zero_mem' := by simp
  add_mem' := by
    intro c d hc hd k
    simpa using congrArg₂ (· + ·) (hc k) (hd k)
  smul_mem' := by
    intro a c hc k
    simp only [Finsupp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    rw [hc k]

def realSynthesisType : Type := ∀ (T : ℝ) [Fact (0 < T)], (ℤ →₀ ℂ) →ₗ[ℝ] C(Circle T, ℝ)

def realSynthesisValue : (ℤ →₀ ℂ) →ₗ[ℝ] C(Circle T, ℝ) where
  toFun c := ⟨fun x => (synthesis T c x).re,
    Complex.continuous_re.comp (synthesis T c).continuous⟩
  map_add' c d := by ext x; simp
  map_smul' a c := by ext x; simp

def realTrigPolynomialsType : Type := ∀ (T : ℝ) [Fact (0 < T)], Submodule ℝ C(Circle T, ℝ)

def realTrigPolynomialsValue : Submodule ℝ C(Circle T, ℝ) :=
  (symmetricCoefficients).map (realSynthesis T)

def realTrigDegreeType : Type := ∀ (T : ℝ) [Fact (0 < T)], ℕ → Submodule ℝ C(Circle T, ℝ)

def realTrigDegreeValue (n : ℕ) : Submodule ℝ C(Circle T, ℝ) :=
  ((Finsupp.supported ℂ ℂ (Set.Icc (-(n : ℤ)) (n : ℤ))).restrictScalars ℝ ⊓
    symmetricCoefficients).map (realSynthesis T)

def rescaleType : Type := ∀ (T : ℝ) [Fact (0 < T)], ∀ (U : ℝ) [Fact (0 < U)], Circle T ≃+ Circle U

def rescaleValue (U : ℝ) [hU : Fact (0 < U)] : Circle T ≃+ Circle U :=
  AddCircle.equivAddCircle T U ((Fact.out : 0 < T).ne') (hU.out.ne')

def toAngleType : Type := ∀ (T : ℝ) [Fact (0 < T)], Circle T ≃+ Circle (2 * Real.pi)

def toAngleValue := rescale T (2 * Real.pi)

def probabilityStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.probability T

def translationStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.translation T

def integralIntervalStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.integralInterval T

def modeFormulaStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.modeFormula T

def coefficientCongrStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.coefficientCongr T

def coefficientIntervalStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.coefficientInterval T

def coefficientL1RepresentativeStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.coefficientL1Representative T

def continuousDensityStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (𝕜 : Type) [RCLike 𝕜], P102.Periodic.Expected.continuousDensity T 𝕜

def rescaleFormulaStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.rescaleFormula T

def rescaleMeasureStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.rescaleMeasure T

def rescaleModeStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.rescaleMode T

def rescaleCoefficientStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.rescaleCoefficient T

def rescaleConvolutionStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.rescaleConvolution T

def rescalePartialSumStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.rescalePartialSum T

def rescaleKernelsStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.rescaleKernels T

def completedDensityStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (𝕜 : Type) [RCLike 𝕜], P102.Periodic.Expected.completedDensity T 𝕜

def angularModeStatement : Prop := P102.Periodic.Expected.angularMode

def angularIntegralStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.angularIntegral T

def poissonFormulaStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.poissonFormula T

def symmetricSynthesisStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.symmetricSynthesis T

def synthesisTransportStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.synthesisTransport T

def intervalMeasureStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.intervalMeasure T

def coefficientSynthesisStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.coefficientSynthesis T

def realSynthesisIffStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], P102.Periodic.Expected.realSynthesisIff T

def complexTrigTransportStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], complexTrigTransport T

def realTrigTransportStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)], realTrigTransport T

end P102.Periodic.Expected
