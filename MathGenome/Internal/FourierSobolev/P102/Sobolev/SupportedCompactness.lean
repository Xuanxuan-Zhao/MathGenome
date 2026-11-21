import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.SupportedCompactness
import MathGenome.Internal.FourierSobolev.P102.U2.ApproximateIdentities
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ConvolutionEndpointBounds
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.KolmogorovRiesz

import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions ENNReal Topology
namespace P102.Sobolev
open U4

/-- A concrete positive smooth kernel, at each strictly positive radius. -/
def probabilityKernel (d : ℕ) (ε : ℝ) : WholeTests d ℝ := by
  by_cases hε : 0 < ε
  · let b : ContDiffBump (0 : Space d) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
    exact ⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed, subset_univ _⟩
  · exact 0

theorem probabilityKernel_properties (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    IsProbabilityKernel (probabilityKernel d ε) ∧
      tsupport (probabilityKernel d ε) ⊆ Metric.closedBall 0 ε := by
  let b : ContDiffBump (0 : Space d) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have heq : (probabilityKernel d ε : Space d → ℝ) = b.normed volume := by
    simp only [probabilityKernel, dite_eq_left hε, b]
    rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x
    rw [heq]
    exact b.nonneg_normed x
  · change (∫ x, (probabilityKernel d ε : Space d → ℝ) x) = 1
    rw [heq]
    exact b.integral_normed
  · rw [heq, b.tsupport_normed_eq]

/-- This helper uses exactly the six frozen premise types, in contract order. -/
theorem supported_probabilityKernels_conditional
    (_cutoff : WholeSpaceDensityExpected.Cutoff)
    (_density : WholeSpaceDensityExpected.Density)
    (_mollification : WholeSpaceDensityExpected.Mollification)
    (_mollifierExistence : WholeSpaceDensityExpected.MollifierExistence)
    (_smoothTests : WholeSpaceDensityExpected.SmoothTests)
    (_weakMollification : WholeSpaceDensityExpected.WeakMollification) :
    SupportedCompactnessExpected.ProbabilityKernels := by
  intro d _hd
  exact ⟨probabilityKernel d, fun _ hε => probabilityKernel_properties d hε⟩

/-- The finite-net step used after smoothing. No compactness of the original
family is required. The approximating sets may vary with the tolerance. -/
theorem totallyBounded_of_uniform_approximation {E : Type*} [PseudoMetricSpace E]
    {A : Set E}
    (h : ∀ δ > 0, ∃ S : Set E, TotallyBounded S ∧
      ∀ x ∈ A, ∃ y ∈ S, dist x y < δ) : TotallyBounded A := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨S, hS, happrox⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨T, hT, hnet⟩ := Metric.totallyBounded_iff.mp hS (ε / 2) (half_pos hε)
  refine ⟨T, hT, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := happrox x hx
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hnet hy)
  apply Set.mem_iUnion₂.mpr
  refine ⟨z, hz, ?_⟩
  change dist x z < ε
  have hyz' : dist y z < ε / 2 := hyz
  exact (dist_triangle x y z).trans_lt (by linarith)

/-- Completeness converts the same finite-net construction to relative compactness. -/
theorem isCompact_closure_of_uniform_approximation {E : Type*} [MetricSpace E]
    [CompleteSpace E] {A : Set E}
    (h : ∀ δ > 0, ∃ S : Set E, TotallyBounded S ∧
      ∀ x ∈ A, ∃ y ∈ S, dist x y < δ) : IsCompact (closure A) :=
  (totallyBounded_of_uniform_approximation h).closure.isCompact_of_isClosed isClosed_closure

section GradientMap
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
theorem wholeLp_ae (f : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    wholeLp f =ᵐ[volume] f := MemLp.coeFn_toLp _

omit [Fact (1 ≤ p)] in
@[simp] theorem norm_wholeLp (f : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    ‖wholeLp f‖ = ‖f‖ := by
  rw [wholeLp, Lp.norm_toLp, Lp.norm_def]
  simp only [Opens.coe_top, Measure.restrict_univ]

/-- The harmless change from restricted whole-space measure to volume is linear
and isometric. All later continuity arguments act on classes. -/
def wholeLpCLM : DomainLp 𝕜 (⊤ : Opens (Space d)) p →L[𝕜]
    Lp 𝕜 p (volume : Measure (Space d)) :=
  LinearMap.mkContinuous
    { toFun := wholeLp
      map_add' := by
        intro f g
        apply Lp.ext
        have hadd := Lp.coeFn_add f g
        simp only [Opens.coe_top, Measure.restrict_univ] at hadd
        filter_upwards [wholeLp_ae (f + g), wholeLp_ae f, wholeLp_ae g,
          Lp.coeFn_add (wholeLp f) (wholeLp g), hadd] with x hfg hf hg hsum hsource
        simp only [hfg, hsum, hsource, Pi.add_apply, hf, hg]
      map_smul' := by
        intro c f
        apply Lp.ext
        have hsmul := Lp.coeFn_smul c f
        simp only [Opens.coe_top, Measure.restrict_univ] at hsmul
        filter_upwards [wholeLp_ae (c • f), wholeLp_ae f,
          Lp.coeFn_smul c (wholeLp f), hsmul] with x hcf hf hsm hsource
        simp only [hcf, hsm, hsource, Pi.smul_apply, hf, RingHom.id_apply] }
    1 (fun f => by simp)

/-- A single Euclidean coordinate as a continuous linear map. -/
def coordinateInjection (i : Fin d) : 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin d) :=
  LinearMap.mkContinuous
    { toFun := fun z : 𝕜 => (PiLp.single 2 i z : EuclideanSpace 𝕜 (Fin d))
      map_add' := fun _ _ => PiLp.single_add 2 i
      map_smul' := fun c z => by
        apply PiLp.ext
        intro j
        simp [PiLp.single_apply] }
    1 (fun z => by simp)

@[simp] theorem coordinateInjection_apply (i : Fin d) (z : 𝕜) :
    coordinateInjection i z = PiLp.single 2 i z := rfl

/-- The vector of first derivatives, in its genuine Euclidean Lp space. -/
def gradientCLM : WholeSobolev d 𝕜 p →L[𝕜]
    Lp (EuclideanSpace 𝕜 (Fin d)) p (volume : Measure (Space d)) :=
  ∑ i : Fin d, ((coordinateInjection (𝕜 := 𝕜) i).compLpL p volume).comp
    (wholeLpCLM.comp ((PiLp.proj 1 _ (supportedFirstIndex i)).comp
      (sobolevSubmodule 𝕜 (⊤ : Opens (Space d)) 1 p).subtypeL))

theorem gradientCLM_eq (u : WholeSobolev d 𝕜 p) : gradientCLM u = gradientLp u := by
  have hval : gradientCLM u = ∑ i : Fin d,
      (coordinateInjection (𝕜 := 𝕜) i).compLpL p volume
        (wholeLp (sobolevDerivative u (supportedFirstIndex i))) := by
    simp only [gradientCLM, sum_apply, ContinuousLinearMap.comp_apply]
    rfl
  rw [hval]
  apply Lp.ext
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun i : Fin d =>
    (coordinateInjection (𝕜 := 𝕜) i).compLpL p volume (wholeLp (sobolevDerivative u (supportedFirstIndex i))))
  have hcoords : ∀ᵐ x ∂volume, ∀ i : Fin d,
      (coordinateInjection (𝕜 := 𝕜) i).compLpL p volume
        (wholeLp (sobolevDerivative u (supportedFirstIndex i))) x =
      PiLp.single 2 i (wholeLp (sobolevDerivative u (supportedFirstIndex i)) x) := by
    apply ae_all_iff.mpr
    intro i
    exact (coordinateInjection (𝕜 := 𝕜) i).coeFn_compLpL _
  filter_upwards [hsum, hcoords, (gradientFunction_memLp u).coeFn_toLp] with x hx hc hg
  change gradientLp u x = gradientFunction u x at hg
  rw [hx, hg]
  apply PiLp.ext
  intro j
  simp [hc, gradientFunction, Pi.single_apply]

theorem continuous_gradientNorm : Continuous (@gradientNorm d 𝕜 _ p _) := by
  have heq : gradientNorm (d := d) (𝕜 := 𝕜) (p := p) = fun u => ‖gradientCLM u‖ := by
    funext u
    rw [gradientCLM_eq]
    rfl
  rw [heq]
  exact gradientCLM.continuous.norm

/-- Each coordinate weak derivative is bounded by the Euclidean gradient norm. -/
theorem derivative_norm_le_gradientNorm (u : WholeSobolev d 𝕜 p) (i : Fin d) :
    ‖sobolevDerivative u (supportedFirstIndex i)‖ ≤ gradientNorm u := by
  rw [← norm_wholeLp]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(gradientFunction_memLp u).coeFn_toLp] with x hx
  change gradientLp u x = gradientFunction u x at hx
  rw [hx]
  exact PiLp.norm_apply_le (gradientFunction u x) i

/-- The coordinate-sum norm is controlled by the source's order-one norm.
Only equivalence, rather than the best dimension constant, is needed here. -/
theorem sobolev_norm_le_euclidean_norm (u : WholeSobolev d 𝕜 p) :
    ‖u‖ ≤ (Fintype.card (SobolevIndex d 1) : ℝ) *
      (‖wholeLp (sobolevUnderlying u)‖ + gradientNorm u) := by
  rw [sobolev_norm]
  calc
    _ ≤ ∑ _α : SobolevIndex d 1, (‖wholeLp (sobolevUnderlying u)‖ + gradientNorm u) := by
      apply Finset.sum_le_sum
      intro α _hα
      by_cases hzero : α.val = 0
      · have hidx : α = zeroSobolevIndex d 1 := Subtype.ext hzero
        rw [hidx, sobolev_derivative_zero, norm_wholeLp]
        exact le_add_of_nonneg_right (norm_nonneg (gradientLp u))
      · have hc : α.val.card = 1 := by
          have hpos := Multiset.card_pos.mpr hzero
          have hle := α.property
          omega
        obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp hc
        have hidx : α = supportedFirstIndex i := Subtype.ext hi
        rw [hidx]
        exact (derivative_norm_le_gradientNorm u i).trans
          (le_add_of_nonneg_left (norm_nonneg _))
    _ = _ := by simp [mul_add]

/-- The inherited graph norm and the source's Euclidean-gradient norm have
exactly the same bounded families. This bridges the section convention explicitly. -/
theorem isBounded_iff_euclidean_gradient_bound (A : Set (WholeSobolev d 𝕜 p)) :
    Bornology.IsBounded A ↔ ∃ M : ℝ, ∀ u ∈ A,
      ‖wholeLp (sobolevUnderlying u)‖ + gradientNorm u ≤ M := by
  constructor
  · intro hA
    obtain ⟨M, hM, hb⟩ := hA.exists_pos_norm_le
    refine ⟨(1 + ‖gradientCLM (d := d) (𝕜 := 𝕜) (p := p)‖) * M, ?_⟩
    intro u hu
    have hzero : ‖wholeLp (sobolevUnderlying u)‖ ≤ ‖u‖ := by
      rw [norm_wholeLp]
      exact PiLp.norm_apply_le u.val (zeroSobolevIndex d 1)
    have hg : gradientNorm u ≤ ‖gradientCLM (d := d) (𝕜 := 𝕜) (p := p)‖ * ‖u‖ := by
      simpa only [gradientCLM_eq, gradientNorm] using (gradientCLM (d := d) (𝕜 := 𝕜) (p := p)).le_opNorm u
    calc
      _ ≤ (1 + ‖gradientCLM (d := d) (𝕜 := 𝕜) (p := p)‖) * ‖u‖ := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb u hu) (by positivity)
  · rintro ⟨M, hb⟩
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨(Fintype.card (SobolevIndex d 1) : ℝ) * M, ?_⟩
    intro u hu
    exact (sobolev_norm_le_euclidean_norm u).trans
      (mul_le_mul_of_nonneg_left (hb u hu) (Nat.cast_nonneg _))

end GradientMap

section SmoothingEstimate
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
@[simp] theorem norm_translateLp (h : Space d) (f : Lp 𝕜 p (volume : Measure (Space d))) :
    ‖translateLp h f‖ = ‖f‖ := Lp.norm_compMeasurePreserving _ _

theorem translateLp_neg_eq (y : Space d) (f : Lp 𝕜 p (volume : Measure (Space d))) :
    translateLp (-y) f = U2.ApproximateIdentities.translate volume y f := by
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving _ _).trans
    ((U2.ApproximateIdentities.translate_ae volume y f).trans
      (Eventually.of_forall (fun x => by simp [sub_eq_add_neg]))).symm

theorem continuous_translateLp_neg (hp : p ≠ ⊤)
    (f : Lp 𝕜 p (volume : Measure (Space d))) :
    Continuous (fun y => translateLp (-y) f) := by
  simp_rw [translateLp_neg_eq]
  exact U2.ApproximateIdentities.continuous_translate volume hp f

theorem integrable_kernel_translate (hp : p ≠ ⊤) (η : WholeTests d ℝ)
    (f : Lp 𝕜 p (volume : Measure (Space d))) :
    Integrable (fun y => η y • translateLp (-y) f) volume := by
  have hη : Integrable η volume := η.continuous.integrable_of_hasCompactSupport η.hasCompactSupport
  refine (hη.norm.mul_const ‖f‖).mono' ?_ ?_
  · exact hη.aestronglyMeasurable.smul (continuous_translateLp_neg hp f).aestronglyMeasurable
  · exact Eventually.of_forall (fun y => by simp [norm_smul])

/-- The quantitative smoothing step, reduced to the sharp translation bound.
Its proof uses a Bochner integral in Lp and works at p = 1. -/
theorem norm_smoothLp_sub_le_of_translation_bound (hp : p ≠ ⊤)
    {ε : ℝ} (_hε : 0 < ε) (η : WholeTests d ℝ) (hη : IsProbabilityKernel η)
    (hsupp : tsupport η ⊆ Metric.closedBall 0 ε) (u : WholeSobolev d 𝕜 p)
    (htrans : ∀ h : Space d,
      ‖translateLp h (wholeLp (sobolevUnderlying u)) - wholeLp (sobolevUnderlying u)‖ ≤
        ‖h‖ * gradientNorm u) :
    ‖smoothLp η u - wholeLp (sobolevUnderlying u)‖ ≤ ε * gradientNorm u := by
  let f := wholeLp (sobolevUnderlying u)
  have hi := integrable_kernel_translate hp η f
  have hk : Integrable η volume := η.continuous.integrable_of_hasCompactSupport η.hasCompactSupport
  have hconst : Integrable (fun y => η y • f) volume := hk.smul_const f
  have heq : smoothLp η u - f = ∫ y, η y • (translateLp (-y) f - f) := by
    simp_rw [smul_sub]
    rw [integral_sub hi hconst, integral_smul_const, hη.2, one_smul]
    rfl
  rw [heq]
  calc
    _ ≤ ∫ y, η y * (ε * gradientNorm u) := by
      apply norm_integral_le_of_norm_le (hk.mul_const _) (Eventually.of_forall ?_)
      intro y
      by_cases hy : y ∈ tsupport η
      · have hb : ‖y‖ ≤ ε := by simpa using hsupp hy
        rw [norm_smul, Real.norm_of_nonneg (hη.1 y)]
        apply mul_le_mul_of_nonneg_left _ (hη.1 y)
        exact (htrans (-y)).trans (by
          rw [norm_neg]
          exact mul_le_mul_of_nonneg_right hb (norm_nonneg (gradientLp u)))
      · simp [image_eq_zero_of_notMem_tsupport hy]
    _ = ε * gradientNorm u := by rw [integral_mul_const, hη.2, one_mul]

end SmoothingEstimate

section SmoothTranslation
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- Cauchy–Schwarz keeps the Euclidean gradient length in the sharp estimate. -/
theorem norm_apply_le_euclidean_gradient (A : Space d →L[ℝ] 𝕜) (h : Space d) :
    ‖A h‖ ≤ ‖h‖ * ‖WithLp.toLp 2 (fun i => A (coordinateVector d i))‖ := by
  have hh : h = ∑ i, h i • coordinateVector d i := by
    simpa only [coordinateVector, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr h).symm
  calc
    ‖A h‖ = ‖∑ i, h i • A (coordinateVector d i)‖ := by
      conv_lhs => rw [hh, map_sum]
      simp
    _ ≤ ∑ i, ‖h i‖ * ‖A (coordinateVector d i)‖ := by
      simpa only [norm_smul] using norm_sum_le (s := Finset.univ)
        (fun i => h i • A (coordinateVector d i))
    _ ≤ Real.sqrt (∑ i, ‖h i‖ ^ 2) *
        Real.sqrt (∑ i, ‖A (coordinateVector d i)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by simp only [PiLp.norm_eq_of_L2, Real.norm_eq_abs, sq_abs]

/-- The segment formula and Minkowski on the probability interval [0,1]. -/
theorem smooth_translation_eLpNorm_le (f : Space d → 𝕜) (hf : ContDiff ℝ 1 f)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hg : MemLp (fun y => WithLp.toLp 2
      (fun i => fderiv ℝ f y (coordinateVector d i))) p volume) (h : Space d) :
    eLpNorm (fun x => f (x + h) - f x) p volume ≤
      ENNReal.ofReal ‖h‖ * eLpNorm
        (fun y => WithLp.toLp 2 (fun i => fderiv ℝ f y (coordinateVector d i))) p volume := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  let G := fun y => WithLp.toLp 2 (fun i => fderiv ℝ f y (coordinateVector d i))
  let F : Space d × ℝ → 𝕜 := fun z => fderiv ℝ f (z.1 + z.2 • h) h
  have hc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hF : Continuous F :=
    (hc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hs (t : ℝ) : eLpNorm (fun x => F (x,t)) p volume ≤
      ENNReal.ofReal ‖h‖ * eLpNorm G p volume := by
    calc
      _ ≤ ENNReal.ofReal ‖h‖ * eLpNorm (fun x => G (x + t • h)) p volume :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (hF.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
          (Eventually.of_forall fun x => norm_apply_le_euclidean_gradient _ _) p
      _ = _ := congrArg (ENNReal.ofReal ‖h‖ * ·)
        (eLpNorm_comp_measurePreserving (g := G) hg.aestronglyMeasurable
          (measurePreserving_add_right volume (t • h)))
  have hR : (∫⁻ t in Ioc (0 : ℝ) 1, eLpNorm (fun x => F (x,t)) p volume) ≤
      ENNReal.ofReal ‖h‖ * eLpNorm G p volume := by
    calc
      _ ≤ ∫⁻ _t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal ‖h‖ * eLpNorm G p volume := lintegral_mono hs
      _ = _ := by simp
  have hfin : (∫⁻ t in Ioc (0 : ℝ) 1, eLpNorm (fun x => F (x,t)) p volume) < ⊤ :=
    hR.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top)
  obtain ⟨_, hb⟩ := ExpandedFA.Distributions.minkowski_integral_eLpNorm
    volume (volume.restrict (Ioc (0 : ℝ) 1)) p hp hpt F hF.measurable hfin
  have hid (x : Space d) : (∫ t in Ioc (0 : ℝ) 1, F (x,t)) = f (x+h) - f x := by
    have hd (t : ℝ) : HasDerivAt (fun t : ℝ => f (x + t • h)) (F (x,t)) t := by
      convert (hf.differentiable (by simp) (x + t • h)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const h)) using 1
      · rfl
      · simp [F]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
  simpa only [hid] using hb.trans hR

theorem gradientFunction_ae_of_represents {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (φ : WholeTests d 𝕜) (u : WholeSobolev d 𝕜 p) (hrep : RepresentsSobolev φ u) :
    gradientFunction u =ᵐ[volume]
      fun x => WithLp.toLp 2 (fun i => fderiv ℝ φ x (coordinateVector d i)) := by
  have hc (i : Fin d) :
      wholeLp (sobolevDerivative u (supportedFirstIndex i)) =ᵐ[volume]
        fun x => fderiv ℝ φ x (coordinateVector d i) := by
    apply (wholeLp_ae _).trans
    have hi := hrep (supportedFirstIndex i)
    simpa [supportedFirstIndex, multiPartial, partialWord, Opens.coe_top, Measure.restrict_univ] using hi
  filter_upwards [ae_all_iff.mpr hc] with x hx
  apply PiLp.ext
  intro i
  exact hx i

theorem underlying_ae_of_represents {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (φ : WholeTests d 𝕜) (u : WholeSobolev d 𝕜 p) (hrep : RepresentsSobolev φ u) :
    wholeLp (sobolevUnderlying u) =ᵐ[volume] φ := by
  apply (wholeLp_ae _).trans
  have hi := hrep (zeroSobolevIndex d 1)
  simpa [sobolevUnderlying, zeroSobolevIndex, multiPartial, partialWord, Opens.coe_top, Measure.restrict_univ] using hi

/-- The smooth estimate expressed in the project's Sobolev tuple model. -/
theorem translation_bound_of_represents {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (φ : WholeTests d 𝕜) (u : WholeSobolev d 𝕜 p) (hrep : RepresentsSobolev φ u)
    (h : Space d) :
    ‖translateLp h (wholeLp (sobolevUnderlying u)) - wholeLp (sobolevUnderlying u)‖ ≤
      ‖h‖ * gradientNorm u := by
  have hg := gradientFunction_ae_of_represents φ u hrep
  have hgm := (gradientFunction_memLp u).ae_eq hg
  have hu := underlying_ae_of_represents φ u hrep
  have he : (translateLp h (wholeLp (sobolevUnderlying u)) - wholeLp (sobolevUnderlying u) :
      Lp 𝕜 p (volume : Measure (Space d))) =ᵐ[volume] fun x => φ (x+h) - φ x := by
    filter_upwards [Lp.coeFn_sub (translateLp h (wholeLp (sobolevUnderlying u)))
      (wholeLp (sobolevUnderlying u)), Lp.coeFn_compMeasurePreserving
        (wholeLp (sobolevUnderlying u)) (measurePreserving_add_right volume h),
      (measurePreserving_add_right (volume : Measure (Space d)) h).quasiMeasurePreserving.ae_eq_comp hu,
      hu] with x hsub ht hshift hzero
    exact hsub.trans (congrArg₂ (· - ·) (ht.trans hshift) hzero)
  have hb := smooth_translation_eLpNorm_le φ (φ.contDiff.of_le (by simp))
    p Fact.out hp hgm h
  rw [Lp.norm_def, eLpNorm_congr_ae he]
  calc
    _ ≤ (ENNReal.ofReal ‖h‖ * eLpNorm
        (fun y => WithLp.toLp 2 (fun i => fderiv ℝ φ y (coordinateVector d i))) p volume).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgm.eLpNorm_ne_top) hb
    _ = ‖h‖ * gradientNorm u := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
      congr 1
      rw [gradientNorm, gradientLp, Lp.norm_toLp, eLpNorm_congr_ae hg]

/-- Density is used only here, after the smooth segment estimate has been proved. -/
theorem supported_translation_conditional
    (_cutoff : WholeSpaceDensityExpected.Cutoff)
    (density : WholeSpaceDensityExpected.Density)
    (_mollification : WholeSpaceDensityExpected.Mollification)
    (_mollifierExistence : WholeSpaceDensityExpected.MollifierExistence)
    (_smoothTests : WholeSpaceDensityExpected.SmoothTests)
    (_weakMollification : WholeSpaceDensityExpected.WeakMollification) :
    SupportedCompactnessExpected.Translation := by
  intro d _hd 𝕜 _ p _ hp u h
  obtain ⟨φ, v, hv, hconv, _hsum⟩ := density 1 p hp u
  let J : WholeSobolev d 𝕜 p →L[𝕜] Lp 𝕜 p (volume : Measure (Space d)) :=
    wholeLpCLM.comp (sobolevUnderlyingCLM ⊤ 1 p)
  let T : Lp 𝕜 p (volume : Measure (Space d)) →L[𝕜]
      Lp 𝕜 p (volume : Measure (Space d)) :=
    (Lp.compMeasurePreservingₗᵢ 𝕜 (fun x : Space d => x + h)
      (measurePreserving_add_right volume h)).toContinuousLinearMap
  have hl : Tendsto (fun n => ‖T (J (v n)) - J (v n)‖) atTop (𝓝 ‖T (J u) - J u‖) :=
    (((T.continuous.comp J.continuous).tendsto u).comp hconv).sub
      ((J.continuous.tendsto u).comp hconv) |>.norm
  have hr : Tendsto (fun n => ‖h‖ * gradientNorm (v n)) atTop (𝓝 (‖h‖ * gradientNorm u)) :=
    ((continuous_gradientNorm.tendsto u).comp hconv).const_mul ‖h‖
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun n =>
    translation_bound_of_represents hp (φ n) (v n) (hv n) h)

end SmoothTranslation

section SmoothingProperties
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Identification of the two integration-variable conventions for convolution. -/
theorem smoothFunction_eq_convolution (η : WholeTests d ℝ) (u : WholeSobolev d 𝕜 p) :
    smoothFunction η u = convolution η (wholeLp (sobolevUnderlying u))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  change (∫ y, η (x - y) • wholeLp (sobolevUnderlying u) y) =
    ∫ y, η y • wholeLp (sobolevUnderlying u) (x - y)
  rw [← integral_sub_left_eq_self
    (fun y => η (x - y) • wholeLp (sobolevUnderlying u) y) volume x]
  simp only [sub_sub_cancel]

theorem smoothFunction_contDiff (η : WholeTests d ℝ) (u : WholeSobolev d 𝕜 p) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothFunction η u) := by
  rw [smoothFunction_eq_convolution]
  exact η.hasCompactSupport.contDiff_convolution_left _ η.contDiff
    ((Lp.memLp _).locallyIntegrable Fact.out)

/-- Fubini identifies the Bochner Lp integral with the pointwise convolution. -/
theorem smoothLp_ae (hp : p ≠ ⊤) (η : WholeTests d ℝ) (u : WholeSobolev d 𝕜 p) :
    (smoothLp η u : Space d → 𝕜) =ᵐ[volume] smoothFunction η u := by
  let k : Space d → 𝕜 := fun y => (η y : 𝕜)
  let f := wholeLp (sobolevUnderlying u)
  have hk : Integrable k volume :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).integrable_comp
      (η.continuous.integrable_of_hasCompactSupport η.hasCompactSupport)
  have hval : smoothLp η u = ∫ y, k y • U2.ApproximateIdentities.translate volume y f := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    dsimp only
    rw [translateLp_neg_eq]
    exact RCLike.real_smul_eq_coe_smul (K := 𝕜) (η y) _
  rw [hval, U2.ApproximateIdentities.integral_translate_eq_convolution volume hp f hk]
  apply (MemLp.coeFn_toLp _).trans
  exact Eventually.of_forall fun x => by
    simp only [U2.Young.integralConvolution, smoothFunction, k, f, RCLike.real_smul_eq_coe_mul]

theorem smoothFunction_memLp (hp : p ≠ ⊤) (η : WholeTests d ℝ) (u : WholeSobolev d 𝕜 p) :
    MemLp (smoothFunction η u) p volume :=
  (Lp.memLp (smoothLp η u)).ae_eq (smoothLp_ae hp η u)

/-- An a.e. support restriction suffices for genuine compact support of the
smooth output; a representative may be cut off on the compact closure of B. -/
theorem smoothFunction_hasCompactSupport (η : WholeTests d ℝ) (u : WholeSobolev d 𝕜 p)
    (B : Set (Space d)) (hB : Bornology.IsBounded B)
    (hsupp : ∀ᵐ x ∂volume, x ∉ B → wholeLp (sobolevUnderlying u) x = 0) :
    HasCompactSupport (smoothFunction η u) := by
  let f := wholeLp (sobolevUnderlying u)
  let g := (closure B).indicator (f : Space d → 𝕜)
  have hgf : g =ᵐ[volume] f := by
    filter_upwards [hsupp] with x hx
    by_cases hxb : x ∈ closure B
    · simp [g, hxb]
    · have hxn : x ∉ B := fun h => hxb (subset_closure h)
      simp [g, hxb, f, hx hxn]
  have hgc : HasCompactSupport g := by
    apply hB.isCompact_closure.of_isClosed_subset (isClosed_tsupport g)
    exact closure_minimal Set.support_indicator_subset isClosed_closure
  rw [smoothFunction_eq_convolution,
    convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (ae_eq_refl η) hgf.symm]
  exact η.hasCompactSupport.convolution _ hgc

/-- Complete smoothing statement, derived using the closed sharp translation bound. -/
theorem supported_smoothing_conditional
    (cutoff : WholeSpaceDensityExpected.Cutoff)
    (density : WholeSpaceDensityExpected.Density)
    (mollification : WholeSpaceDensityExpected.Mollification)
    (mollifierExistence : WholeSpaceDensityExpected.MollifierExistence)
    (smoothTests : WholeSpaceDensityExpected.SmoothTests)
    (weakMollification : WholeSpaceDensityExpected.WeakMollification) :
    SupportedCompactnessExpected.Smoothing := by
  intro d hd 𝕜 _ p _ hp ε hε η hη hsupp u
  refine ⟨smoothLp_ae hp η u, smoothFunction_memLp hp η u,
    smoothFunction_contDiff η u, ?_, smoothFunction_hasCompactSupport η u⟩
  apply norm_smoothLp_sub_le_of_translation_bound hp hε η hη hsupp u
  exact supported_translation_conditional cutoff density mollification mollifierExistence
    smoothTests weakMollification hd p hp u

/-- Uniform approximation holds on every bounded family, without assuming it
is relatively compact. The rate is already contained in the smoothing estimate. -/
theorem supported_uniformApproximation_conditional
    (cutoff : WholeSpaceDensityExpected.Cutoff)
    (density : WholeSpaceDensityExpected.Density)
    (mollification : WholeSpaceDensityExpected.Mollification)
    (mollifierExistence : WholeSpaceDensityExpected.MollifierExistence)
    (smoothTests : WholeSpaceDensityExpected.SmoothTests)
    (weakMollification : WholeSpaceDensityExpected.WeakMollification) :
    SupportedCompactnessExpected.UniformApproximation := by
  intro d hd 𝕜 _ p _ hp A hA η hη
  obtain ⟨M, hM, hbound⟩ :=
    ((gradientCLM (d := d) (𝕜 := 𝕜) (p := p)).lipschitzWith.isBounded_image hA).exists_pos_norm_le
  have hlimit : Tendsto (fun ε : ℝ => ε * M) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul, id_eq] using
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0)).mul_const M
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hsmall := (tendsto_order.mp hlimit).2 δ hδ
  filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε hpos
  intro u hu
  have hg : gradientNorm u ≤ M := by
    simpa only [gradientCLM_eq, gradientNorm] using hbound (gradientCLM u) ⟨u, hu, rfl⟩
  rw [dist_comm, dist_eq_norm]
  have hb := (supported_smoothing_conditional cutoff density mollification mollifierExistence
    smoothTests weakMollification hd p hp ε hpos (η ε) (hη ε hpos).1 (hη ε hpos).2 u).2.2.2.1
  exact hb.trans_lt ((mul_le_mul_of_nonneg_left hg (le_of_lt hpos)).trans_lt hε)

end SmoothingProperties

section Compactness
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The coordinate change preserves volume and hence every scalar Lp norm. -/
def coordinateLp : Lp 𝕜 p (volume : Measure (Space d)) →ₗᵢ[𝕜]
    Lp 𝕜 p (volume : Measure (Fin d → ℝ)) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (WithLp.toLp 2) (PiLp.volume_preserving_toLp (Fin d))

theorem coordinateLp_ae (f : Lp 𝕜 p (volume : Measure (Space d))) :
    coordinateLp f =ᵐ[volume] fun x => f (WithLp.toLp 2 x) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- In the library coordinate convention, τ_h corresponds to our translation by -h. -/
theorem coordinateLp_translate (f : Lp 𝕜 p (volume : Measure (Space d))) (h : Fin d → ℝ) :
    ExpandedFA.Distributions.LpTranslationContinuitySpec.LpTranslationValue p h (coordinateLp f) =
      coordinateLp (translateLp (-WithLp.toLp 2 h) f) := by
  apply Lp.ext
  have h1 := ExpandedFA.Distributions.lpTranslation_representative p h (coordinateLp f)
  have h2 := (measurePreserving_sub_right (volume : Measure (Fin d → ℝ)) h).quasiMeasurePreserving.ae_eq_comp (coordinateLp_ae f)
  have h3 := coordinateLp_ae (translateLp (-WithLp.toLp 2 h) f)
  have h4 := (PiLp.volume_preserving_toLp (Fin d)).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving f
      (measurePreserving_add_right (volume : Measure (Space d)) (-WithLp.toLp 2 h)))
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  dsimp only [Function.comp_apply] at hx2 hx4
  change translateLp (-WithLp.toLp 2 h) f (WithLp.toLp 2 x) =
    f (WithLp.toLp 2 x + -WithLp.toLp 2 h) at hx4
  rw [hx1, hx2, hx3, hx4]
  congr 1

/-- Uniform translation control follows from boundedness of the gradient map.
The library uses the supremum norm on coordinates only to express a modulus. -/
theorem bounded_uniform_translation (htrans : SupportedCompactnessExpected.Translation)
    (hd : 0 < d) (hp : p ≠ ⊤) (A : Set (WholeSobolev d 𝕜 p))
    (hA : Bornology.IsBounded A) :
    ExpandedFA.Sobolev.KolmogorovRieszSpec.UniformTranslationContinuous p
      ((fun u => coordinateLp (wholeLp (sobolevUnderlying u))) '' A) := by
  obtain ⟨M, hM, hbound⟩ :=
    ((gradientCLM (d := d) (𝕜 := 𝕜) (p := p)).lipschitzWith.isBounded_image hA).exists_pos_norm_le
  let Q : (Fin d → ℝ) →L[ℝ] Space d :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap
  let C : ℝ := ‖Q‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  intro ε hε
  refine ⟨ε / (C * M + 1), div_pos hε (by positivity), ?_⟩
  intro h hh f hf
  obtain ⟨u, hu, rfl⟩ := hf
  rw [coordinateLp_translate, ← map_sub, LinearIsometry.norm_map]
  have hg : gradientNorm u ≤ M := by
    simpa only [gradientCLM_eq, gradientNorm] using hbound (gradientCLM u) ⟨u, hu, rfl⟩
  have hQ : ‖WithLp.toLp 2 h‖ ≤ C * ‖h‖ := by
    exact (Q.le_opNorm h).trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [norm_nonneg Q])
      (norm_nonneg h))
  calc
    _ ≤ ‖-WithLp.toLp 2 h‖ * gradientNorm u := htrans hd p hp u _
    _ ≤ C * ‖h‖ * M := by rw [norm_neg]; exact mul_le_mul hQ hg (norm_nonneg _) (by positivity)
    _ ≤ (C * M + 1) * ‖h‖ := by nlinarith [norm_nonneg h]
    _ < (C * M + 1) * (ε / (C * M + 1)) := mul_lt_mul_of_pos_left hh (by positivity)
    _ = ε := mul_div_cancel₀ ε (by positivity)

/-- A fixed bounded essential support makes all sufficiently remote tails zero.
No measurability of the stated support set is needed. -/
theorem bounded_support_uniform_tails (A : Set (WholeSobolev d 𝕜 p))
    (B : Set (Space d)) (hB : Bornology.IsBounded B)
    (hsupp : ∀ u ∈ A, ∀ᵐ x ∂volume, x ∉ B → wholeLp (sobolevUnderlying u) x = 0) :
    ExpandedFA.Sobolev.KolmogorovRieszSpec.UniformLpTails p
      ((fun u => coordinateLp (wholeLp (sobolevUnderlying u))) '' A) := by
  let Q : Space d →L[ℝ] (Fin d → ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  obtain ⟨R, hR, hbound⟩ := (Q.lipschitzWith.isBounded_image hB).exists_pos_norm_le
  intro ε hε
  refine ⟨R, hR, ?_⟩
  intro f hf
  obtain ⟨u, hu, rfl⟩ := hf
  have hz : ExpandedFA.Sobolev.lpRestrict p volume
      (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ
        (coordinateLp (wholeLp (sobolevUnderlying u))) = 0 := by
    apply Lp.ext
    have hsource := (PiLp.volume_preserving_toLp (Fin d)).quasiMeasurePreserving.ae (hsupp u hu)
    filter_upwards [ExpandedFA.Sobolev.lpRestrict_representative
      (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ
      (coordinateLp (wholeLp (sobolevUnderlying u))),
      ae_restrict_of_ae (coordinateLp_ae (wholeLp (sobolevUnderlying u))),
      ae_restrict_of_ae hsource, ae_restrict_mem Metric.isClosed_closedBall.measurableSet.compl,
      Lp.coeFn_zero 𝕜 p (volume.restrict (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ)]
      with x hx hx' hs houtside hzero
    rw [hx, hx', hzero]
    apply hs
    intro hin
    have hb := hbound (Q (WithLp.toLp 2 x)) ⟨WithLp.toLp 2 x, hin, rfl⟩
    change ‖x‖ ≤ R at hb
    apply houtside
    simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  change ‖ExpandedFA.Sobolev.lpRestrict p volume (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ
    (coordinateLp (wholeLp (sobolevUnderlying u)))‖ < ε
  rw [hz, norm_zero]
  exact hε

/-- Kolmogorov–Riesz yields relative compactness of every bounded-support family,
including at p=1. Only the six specified whole-space premises are parameters. -/
theorem supported_compactness_conditional
    (cutoff : WholeSpaceDensityExpected.Cutoff)
    (density : WholeSpaceDensityExpected.Density)
    (mollification : WholeSpaceDensityExpected.Mollification)
    (mollifierExistence : WholeSpaceDensityExpected.MollifierExistence)
    (smoothTests : WholeSpaceDensityExpected.SmoothTests)
    (weakMollification : WholeSpaceDensityExpected.WeakMollification) :
    SupportedCompactnessExpected.Compactness := by
  intro d hd 𝕜 _ p _ hp A hA B hB hsupp
  let J : WholeSobolev d 𝕜 p →L[𝕜] Lp 𝕜 p (volume : Measure (Space d)) :=
    wholeLpCLM.comp (sobolevUnderlyingCLM ⊤ 1 p)
  let S := (fun u => coordinateLp (J u)) '' A
  have hbounded : Bornology.IsBounded S := by
    simpa only [S, Set.image_image] using
      (coordinateLp (𝕜 := 𝕜) (p := p)).lipschitzWith.isBounded_image
        (J.lipschitzWith.isBounded_image hA)
  have ht : ExpandedFA.Sobolev.KolmogorovRieszSpec.UniformTranslationContinuous p S :=
    bounded_uniform_translation (supported_translation_conditional cutoff density mollification
      mollifierExistence smoothTests weakMollification) hd hp A hA
  have htails : ExpandedFA.Sobolev.KolmogorovRieszSpec.UniformLpTails p S :=
    bounded_support_uniform_tails A B hB hsupp
  have hc : IsCompact (closure S) :=
    (ExpandedFA.Sobolev.kolmogorovRiesz d p hp S hbounded).mpr ⟨htails, ht⟩
  have htb : TotallyBounded (J '' A) := by
    apply (totallyBounded_image_iff coordinateLp.isometry.isUniformInducing).mp
    simpa only [Set.image_image] using hc.totallyBounded.subset subset_closure
  exact htb.closure.isCompact_of_isClosed isClosed_closure

end Compactness

end P102.Sobolev

theorem _root_.«P102».«Sobolev».«supported_compactness» : _root_.«P102».«Sobolev».«SupportedCompactnessExpected».«Compactness» :=
  @_root_.«P102».«Sobolev».«supported_compactness_conditional» (@_root_.«P102».«U4».«wholeSpace_cutoff») (@_root_.«P102».«U4».«wholeSpace_density») (@_root_.«P102».«U4».«wholeSpace_mollification») (@_root_.«P102».«U4».«wholeSpace_mollifierExistence») (@_root_.«P102».«U4».«wholeSpace_smoothTests») (@_root_.«P102».«U4».«wholeSpace_weakMollification»)
theorem _root_.«P102».«Sobolev».«supported_probabilityKernels» : _root_.«P102».«Sobolev».«SupportedCompactnessExpected».«ProbabilityKernels» :=
  @_root_.«P102».«Sobolev».«supported_probabilityKernels_conditional» (@_root_.«P102».«U4».«wholeSpace_cutoff») (@_root_.«P102».«U4».«wholeSpace_density») (@_root_.«P102».«U4».«wholeSpace_mollification») (@_root_.«P102».«U4».«wholeSpace_mollifierExistence») (@_root_.«P102».«U4».«wholeSpace_smoothTests») (@_root_.«P102».«U4».«wholeSpace_weakMollification»)
theorem _root_.«P102».«Sobolev».«supported_smoothing» : _root_.«P102».«Sobolev».«SupportedCompactnessExpected».«Smoothing» :=
  @_root_.«P102».«Sobolev».«supported_smoothing_conditional» (@_root_.«P102».«U4».«wholeSpace_cutoff») (@_root_.«P102».«U4».«wholeSpace_density») (@_root_.«P102».«U4».«wholeSpace_mollification») (@_root_.«P102».«U4».«wholeSpace_mollifierExistence») (@_root_.«P102».«U4».«wholeSpace_smoothTests») (@_root_.«P102».«U4».«wholeSpace_weakMollification»)
theorem _root_.«P102».«Sobolev».«supported_translation» : _root_.«P102».«Sobolev».«SupportedCompactnessExpected».«Translation» :=
  @_root_.«P102».«Sobolev».«supported_translation_conditional» (@_root_.«P102».«U4».«wholeSpace_cutoff») (@_root_.«P102».«U4».«wholeSpace_density») (@_root_.«P102».«U4».«wholeSpace_mollification») (@_root_.«P102».«U4».«wholeSpace_mollifierExistence») (@_root_.«P102».«U4».«wholeSpace_smoothTests») (@_root_.«P102».«U4».«wholeSpace_weakMollification»)
theorem _root_.«P102».«Sobolev».«supported_uniformApproximation» : _root_.«P102».«Sobolev».«SupportedCompactnessExpected».«UniformApproximation» :=
  @_root_.«P102».«Sobolev».«supported_uniformApproximation_conditional» (@_root_.«P102».«U4».«wholeSpace_cutoff») (@_root_.«P102».«U4».«wholeSpace_density») (@_root_.«P102».«U4».«wholeSpace_mollification») (@_root_.«P102».«U4».«wholeSpace_mollifierExistence») (@_root_.«P102».«U4».«wholeSpace_smoothTests») (@_root_.«P102».«U4».«wholeSpace_weakMollification»)
