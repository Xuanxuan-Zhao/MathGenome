import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped Real ENNReal ComplexConjugate

namespace P102.Periodic

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

variable (T : ℝ) [hT : Fact (0 < T)]

theorem haar_probability : (haar T) Set.univ = 1 := measure_univ

theorem haar_translation : ∀ a : Circle T,
  MeasurePreserving (fun x => a + x) (haar T) (haar T) := by
  intro a
  exact measurePreserving_add_left (haar T) a

theorem haar_integral_interval : ∀ (f : Circle T → ℂ) (a : ℝ),
  (∫ x, f x ∂haar T) = T⁻¹ • ∫ t in a..a + T, f (t : Circle T) := by
  intro f a
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage T a f]

theorem mode_formula : ∀ (k : ℤ) (t : ℝ),
  mode T k (t : Circle T) = Complex.exp (2 * Real.pi * Complex.I * k * t / T) := by
  intro k t
  exact fourier_coe_apply

/-- The standard library's vector-valued coefficient specializes to the manuscript convention. -/
theorem coefficient_eq_fourierCoeff (f : Circle T → ℂ) (k : ℤ) :
    coefficient T f k = fourierCoeff f k := by
  simp only [coefficient, fourierCoeff, mode, fourier_neg, smul_eq_mul, mul_comm]

theorem coefficient_congr : ∀ (f g : Circle T → ℂ),
  f =ᵐ[haar T] g → ∀ k, coefficient T f k = coefficient T g k := by
  intro f g h k
  exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

theorem coefficient_interval : ∀ (f : Circle T → ℂ) (k : ℤ) (a : ℝ),
  coefficient T f k = (1 / T : ℝ) • ∫ t in a..a + T,
    f (t : Circle T) * Complex.exp (-(2 * Real.pi * Complex.I * k * t / T)) := by
  intro f k a
  rw [coefficient_eq_fourierCoeff, fourierCoeff_eq_intervalIntegral f k a]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [smul_eq_mul, fourier_coe_apply]
  simp only [Int.cast_neg]
  rw [mul_comm (Complex.exp _) (f _)]
  congr 2
  ring

theorem coefficientL1_representative : ∀ (f : L1 T) (g : Circle T → ℂ),
  (f : Circle T → ℂ) =ᵐ[haar T] g → ∀ k, coefficientL1 T f k = coefficient T g k := by
  intro f g h k
  exact coefficient_congr T f g h k

theorem continuous_density (𝕜 : Type) [RCLike 𝕜] :
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    DenseRange (ContinuousMap.toLp p (haar T) 𝕜 : C(Circle T, 𝕜) →L[𝕜] Lp 𝕜 p (haar T)) := by
  intro p hp hfin
  exact ContinuousMap.toLp_denseRange 𝕜 (haar T) 𝕜 hfin

theorem rescale_formula (U : ℝ) [hU : Fact (0 < U)] (t : ℝ) :
    rescale T U (t : Circle T) = ((U * t / T : ℝ) : Circle U) := by
  rw [rescale, AddCircle.equivAddCircle_apply_mk]
  congr 1
  ring

theorem rescale_measure (U : ℝ) [hU : Fact (0 < U)] :
    MeasurePreserving (rescale T U) (haar T) (haar U) := by
  have hc : Continuous (rescale T U) :=
    AddCircle.continuous_equivAddCircle T U hT.out.ne' hU.out.ne'
  have hcs : Continuous (rescale T U).symm :=
    (AddCircle.homeomorphAddCircle T U hT.out.ne' hU.out.ne').symm.continuous
  have : IsAddHaarMeasure ((haar T).map (rescale T U)) :=
    (rescale T U).isAddHaarMeasure_map (haar T) hc hcs
  exact ⟨hc.measurable, isAddHaarMeasure_eq_of_isProbabilityMeasure _ _⟩

theorem rescale_mode (U : ℝ) [hU : Fact (0 < U)] (k : ℤ) (x : Circle T) :
    mode U k (rescale T U x) = mode T k x := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    rw [rescale_formula, mode, fourier_coe_apply, fourier_coe_apply]
    congr 1
    push_cast
    field_simp [show (U : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hU.out.ne']

/-- Integral transport for all representatives; measurability is not a new hypothesis. -/
theorem integral_rescale (U : ℝ) [hU : Fact (0 < U)] (f : Circle U → ℂ) :
    (∫ x, f (rescale T U x) ∂haar T) = ∫ x, f x ∂haar U := by
  exact (rescale_measure T U).integral_comp
    (AddCircle.homeomorphAddCircle T U hT.out.ne' hU.out.ne').isClosedEmbedding.measurableEmbedding f

theorem rescale_coefficient (U : ℝ) [hU : Fact (0 < U)]
    (f : Circle U → ℂ) (k : ℤ) :
    coefficient T (fun x => f (rescale T U x)) k = coefficient U f k := by
  simp only [coefficient]
  rw [← integral_rescale T U (fun y => f y * conj (mode U k y))]
  simp only [rescale_mode]

theorem rescale_convolution : ∀ (U : ℝ) [Fact (0 < U)]
  (f g : Circle U → ℂ) (x : Circle T),
  convolution T (fun y => f (rescale T U y)) (fun y => g (rescale T U y)) x =
    convolution U f g (rescale T U x) := by
  intro U hU f g x
  simp only [convolution]
  rw [← integral_rescale T U (fun y => f (rescale T U x - y) * g y)]
  simp only [map_sub]

theorem rescale_partialSum (U : ℝ) [hU : Fact (0 < U)]
    (N : ℕ) (f : Circle U → ℂ) (x : Circle T) :
    partialSum T N (fun y => f (rescale T U y)) x = partialSum U N f (rescale T U x) := by
  simp only [partialSum, rescale_coefficient, rescale_mode]

theorem rescale_kernels : ∀ (U : ℝ) [Fact (0 < U)] (N : ℕ) (r : ℝ)
  (f : Circle U → ℂ) (x : Circle T),
  dirichletKernel T N x = dirichletKernel U N (rescale T U x) ∧
  fejerKernel T N x = fejerKernel U N (rescale T U x) ∧
  fejerMean T N (fun y => f (rescale T U y)) x = fejerMean U N f (rescale T U x) ∧
  poissonKernel T r x = poissonKernel U r (rescale T U x) ∧
  abelMean T r (fun y => f (rescale T U y)) x = abelMean U r f (rescale T U x) := by
  intro U hU N r f x
  simp only [dirichletKernel, fejerKernel, fejerMean, poissonKernel, abelMean,
    rescale_coefficient, rescale_mode, rescale_partialSum]
  simp

/-! Completing a measure changes neither Lp membership nor its seminorm. The
identity from the completion to the original Borel space is measure preserving. -/
section Completion
variable {α : Type*} [m : MeasurableSpace α] (μ : Measure α)
variable {𝕜 : Type*} [RCLike 𝕜]

theorem aeStrong_completion (f : α → 𝕜)
    (hf : AEStronglyMeasurable (α := NullMeasurableSpace α μ) f μ.completion) :
    AEStronglyMeasurable f μ := by
  dsimp only [NullMeasurableSpace] at *
  have hm : NullMeasurable (hf.aemeasurable.mk f) μ := hf.aemeasurable.measurable_mk
  exact (hm.aemeasurable.congr hf.aemeasurable.ae_eq_mk.symm).aestronglyMeasurable

theorem norm_completion (f : α → 𝕜) (p : ℝ≥0∞) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (α := NullMeasurableSpace α μ) f p μ.completion = eLpNorm f p μ := by
  have hmp : @MeasurePreserving (NullMeasurableSpace α μ) α _ m (fun x => x) μ.completion μ := by
    have hmeas : @Measurable (NullMeasurableSpace α μ) α _ m (fun x => x) :=
      fun s hs => hs.nullMeasurableSet
    refine ⟨hmeas, ?_⟩
    apply Measure.ext
    intro s hs
    exact (Measure.map_apply hmeas hs).trans rfl
  exact eLpNorm_comp_measurePreserving hf hmp

theorem mem_completion (f : α → 𝕜) (p : ℝ≥0∞) :
    MemLp (α := NullMeasurableSpace α μ) f p μ.completion ↔ MemLp f p μ := by
  dsimp only [NullMeasurableSpace] at *
  constructor
  · intro hf
    have hm := aeStrong_completion μ f hf.aestronglyMeasurable
    change eLpNorm f p μ < ∞
    exact (norm_completion μ f p hm) ▸ hf
  · intro hf
    have hm : AEStronglyMeasurable (α := NullMeasurableSpace α μ) f μ.completion :=
      ⟨hf.aestronglyMeasurable.mk f,
        hf.aestronglyMeasurable.stronglyMeasurable_mk.mono (fun s hs => hs.nullMeasurableSet),
        hf.aestronglyMeasurable.ae_eq_mk⟩
    change eLpNorm _ p μ.completion < ∞
    exact (norm_completion μ f p hf.aestronglyMeasurable).symm ▸ hf

end Completion

theorem completed_density (𝕜 : Type) [RCLike 𝕜] :
  ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
  ∀ (f : NullMeasurableSpace (Circle T) (haar T) → 𝕜),
    MemLp f p (haar T).completion →
    ∀ (ε : ℝ≥0∞), ε ≠ 0 → ∃ g : C(Circle T, 𝕜),
      eLpNorm (fun x : NullMeasurableSpace (Circle T) (haar T) => f x - g x)
        p (haar T).completion ≤ ε := by
  intro p hp hfin f hf ε hε
  have hf' : MemLp (fun x : Circle T => f x) p (haar T) :=
    (mem_completion (haar T) _ p).mp hf
  obtain ⟨g, hg, hgm⟩ := hf'.exists_boundedContinuous_eLpNorm_sub_le hfin hε
  refine ⟨g.toContinuousMap, ?_⟩
  have heq := norm_completion (haar T) (fun x : Circle T => f x - g x) p
    (hf'.aestronglyMeasurable.sub hgm.aestronglyMeasurable)
  exact heq.trans_le hg

theorem angular_mode : ∀ (k : ℤ) (v : ℝ),
  mode (2 * Real.pi) k (v : Circle (2 * Real.pi)) = Complex.exp (Complex.I * k * v) := by
  intro k v
  rw [mode, fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem angular_integral : ∀ (f : Circle (2 * Real.pi) → ℂ) (a : ℝ),
  (∫ x, f (toAngle T x) ∂haar T) =
    (2 * Real.pi)⁻¹ • ∫ v in a..a + 2 * Real.pi, f (v : Circle (2 * Real.pi)) := by
  intro f a
  rw [integral_rescale]
  exact haar_integral_interval (2 * Real.pi) f a

theorem poisson_formula : ∀ (r t : ℝ),
  poissonKernel T r (t : Circle T) =
    (1 - r ^ 2) / (1 - 2 * r * Real.cos (2 * Real.pi * t / T) + r ^ 2) := by
  intro r t
  simp only [poissonKernel, mode, fourier_coe_apply]
  have heq : 2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * t / T =
      ((2 * Real.pi * t / T : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [heq]
  simp [Complex.exp_re]

theorem synthesis_transport : ∀ (U : ℝ) [Fact (0 < U)] (c : ℤ →₀ ℂ) (x : Circle T),
  synthesis U c (rescale T U x) = synthesis T c x ∧
  realSynthesis U c (rescale T U x) = realSynthesis T c x := by
  intro U hU c x
  have h : synthesis U c (rescale T U x) = synthesis T c x := by
    simp only [synthesis, Finsupp.linearCombination_apply, Finsupp.sum,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, rescale_mode]
  exact ⟨h, congrArg Complex.re h⟩

theorem synth_sum (c : ℤ →₀ ℂ) (x : Circle T) :
    synthesis T c x = ∑ k ∈ c.support, c k * mode T k x := by
  simp only [synthesis, Finsupp.linearCombination_apply, Finsupp.sum,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]

theorem symmetric_synthesis (c : ℤ →₀ ℂ) (hc : c ∈ symmetricCoefficients) (x : Circle T) :
    (realSynthesis T c x : ℂ) = synthesis T c x := by
  have hc' : ∀ k, c (-k) = conj (c k) := hc
  have hs : ∀ k, k ∈ c.support ↔ -k ∈ c.support := by
    intro k
    simp only [Finsupp.mem_support_iff, hc', map_ne_zero]
  have hstar : conj (synthesis T c x) = synthesis T c x := by
    rw [synth_sum, _root_.map_sum]
    apply Finset.sum_equiv (Equiv.neg ℤ) hs
    intro k hk
    simp only [Equiv.neg_apply, map_mul, hc', mode, fourier_neg]
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.im hstar
    simp only [Complex.conj_im] at h
    simp only [Complex.ofReal_im]
    linarith

theorem interval_measure : ∀ a : ℝ,
  MeasurePreserving (fun t : ℝ => (t : Circle T))
    (ENNReal.ofReal (T⁻¹) • volume.restrict (Ioc a (a + T))) (haar T) := by
  intro a
  have h := (AddCircle.measurePreserving_mk T a).smul_measure (ENNReal.ofReal T⁻¹)
  convert h using 1
  rw [AddCircle.volume_eq_smul_haarAddCircle, smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.mpr hT.out.le),
    inv_mul_cancel₀ hT.out.ne', ENNReal.ofReal_one, one_smul]

theorem coeff_synth (c : ℤ →₀ ℂ) (k : ℤ) : fourierCoeff (synthesis T c) k = c k := by
  have heq : (synthesis T c : Circle T → ℂ) =
      ∑ j ∈ c.support, (fun x => c j * mode T j x) := by
    ext x
    simp [synthesis, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [heq, fourierCoeff.sum]
  · simp only [Finset.sum_apply, fourierCoeff.const_mul, mode, fourierCoeff_fourier]
    simp [Pi.single_apply, eq_comm]
  · intro j hj
    exact ((mode T j).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _

theorem coefficient_synthesis : ∀ (c : ℤ →₀ ℂ) (k : ℤ),
  coefficient T (synthesis T c) k = c k := by
  intro c k
  rw [coefficient_eq_fourierCoeff]
  exact coeff_synth T c k

/-- Conjugate symmetry for any representative with real values. -/
theorem coefficient_conj_of_real (f : Circle T → ℂ) (hf : ∀ x, (f x).im = 0) (k : ℤ) :
    coefficient T f (-k) = conj (coefficient T f k) := by
  have hi := Complex.conjCLE.integral_comp_comm (μ := haar T)
    (fun x => f x * conj (mode T k x))
  change (∫ x, conj (f x * conj (mode T k x)) ∂haar T) =
    conj (∫ x, f x * conj (mode T k x) ∂haar T) at hi
  simp only [coefficient]
  rw [← hi]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hx : conj (f x) = f x := by
    apply Complex.ext
    · rfl
    · simp [hf x]
  simp only [mode, fourier_neg, map_mul, Complex.conj_conj, hx]

theorem real_synthesis_iff : ∀ c : ℤ →₀ ℂ,
  (∀ x : Circle T, (synthesis T c x).im = 0) ↔ c ∈ symmetricCoefficients := by
  intro c
  constructor
  · intro h
    change ∀ k, c (-k) = conj (c k)
    intro k
    rw [← coeff_synth T c (-k), ← coeff_synth T c k,
      ← coefficient_eq_fourierCoeff, ← coefficient_eq_fourierCoeff]
    exact coefficient_conj_of_real T (synthesis T c) h k
  · intro hc x
    have h := congrArg Complex.im (symmetric_synthesis T c hc x)
    simpa only [Complex.ofReal_im] using h.symm

/-- Rescaling preserves each chosen set of finite coefficient vectors. -/
theorem complex_synthesis_range_transport (U : ℝ) [Fact (0 < U)]
    (S : Submodule ℂ (ℤ →₀ ℂ)) (f : C(Circle U, ℂ)) (g : C(Circle T, ℂ))
    (hfg : ∀ x, g x = f (rescale T U x)) :
    g ∈ S.map (synthesis T) ↔ f ∈ S.map (synthesis U) := by
  constructor
  · rintro ⟨c, hc, hcg⟩
    refine ⟨c, hc, ?_⟩
    ext y
    obtain ⟨x, rfl⟩ := (rescale T U).surjective y
    rw [(synthesis_transport T U c x).1, hcg, hfg]
  · rintro ⟨c, hc, hcf⟩
    refine ⟨c, hc, ?_⟩
    ext x
    rw [← (synthesis_transport T U c x).1, hcf, hfg]

theorem real_synthesis_range_transport (U : ℝ) [Fact (0 < U)]
    (S : Submodule ℝ (ℤ →₀ ℂ)) (f : C(Circle U, ℝ)) (g : C(Circle T, ℝ))
    (hfg : ∀ x, g x = f (rescale T U x)) :
    g ∈ S.map (realSynthesis T) ↔ f ∈ S.map (realSynthesis U) := by
  constructor
  · rintro ⟨c, hc, hcg⟩
    refine ⟨c, hc, ?_⟩
    ext y
    obtain ⟨x, rfl⟩ := (rescale T U).surjective y
    rw [(synthesis_transport T U c x).2, hcg, hfg]
  · rintro ⟨c, hc, hcf⟩
    refine ⟨c, hc, ?_⟩
    ext x
    rw [← (synthesis_transport T U c x).2, hcf, hfg]

theorem complex_trig_transport : ∀ (U : ℝ) [Fact (0 < U)]
  (f : C(Circle U, ℂ)) (g : C(Circle T, ℂ)),
  (∀ x, g x = f (rescale T U x)) → ∀ n : ℕ,
    (g ∈ complexTrigPolynomials T ↔ f ∈ complexTrigPolynomials U) ∧
    (g ∈ complexTrigDegree T n ↔ f ∈ complexTrigDegree U n) := by
  intro U hU f g hfg n
  constructor
  · simpa only [complexTrigPolynomials, Submodule.map_top] using
      complex_synthesis_range_transport T U ⊤ f g hfg
  · exact complex_synthesis_range_transport T U _ f g hfg

theorem real_trig_transport : ∀ (U : ℝ) [Fact (0 < U)]
  (f : C(Circle U, ℝ)) (g : C(Circle T, ℝ)),
  (∀ x, g x = f (rescale T U x)) → ∀ n : ℕ,
    (g ∈ realTrigPolynomials T ↔ f ∈ realTrigPolynomials U) ∧
    (g ∈ realTrigDegree T n ↔ f ∈ realTrigDegree U n) := by
  intro U hU f g hfg n
  exact ⟨real_synthesis_range_transport T U _ f g hfg,
    real_synthesis_range_transport T U _ f g hfg⟩

end P102.Periodic
