import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyCayley
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyDisk
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyHalfPlaneRepresentation
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! The Cayley unitary is constructed from its action on evaluation kernels.
Their Gram matrices agree after the factor `2 * sqrt π`. Totality on the disk
uses uniqueness of coefficients; totality on the half-plane uses uniqueness
of the accepted Laplace representation. Extension from finite kernel sums
therefore gives an onto isometry, and the representation theorem transfers it
to the actual analytic functions and their slice and boundary norms. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Real ENNReal NNReal Topology FourierTransform ComplexConjugate
namespace ExpandedFA.PartIV.HardyCayley
open HardyCayleySpec HardyHalfPlaneRepresentationSpec

abbrev cayley := HardyCayleySpec.cayley
abbrev uncayley := HardyCayleySpec.uncayley
abbrev transform := HardyCayleySpec.transform
abbrev inverseTransform := HardyCayleySpec.inverseTransform

lemma disk_norm {w : ℂ} (hw : w ∈ HardyDiskSpec.disk) : ‖w‖ < 1 := by
  simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right] using hw

lemma one_sub_ne_zero {w : ℂ} (hw : w ∈ HardyDiskSpec.disk) : 1 - w ≠ 0 := by
  intro h
  have := disk_norm hw
  rw [← sub_eq_zero.mp h] at this
  simp at this

lemma add_I_ne_zero {z : ℂ} (hz : z ∈ upperHalfPlane) : z + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at this
  change 0 < z.im at hz
  linarith

lemma cayley_im (w : ℂ) :
    (cayley w).im = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
  simp [HardyCayleySpec.cayley, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply]
  ring

lemma cayley_mem {w : ℂ} (hw : w ∈ HardyDiskSpec.disk) : cayley w ∈ upperHalfPlane := by
  change 0 < (cayley w).im
  rw [cayley_im]
  apply div_pos
  · rw [Complex.normSq_eq_norm_sq]
    have := disk_norm hw
    nlinarith [norm_nonneg w]
  · exact Complex.normSq_pos.mpr (one_sub_ne_zero hw)

lemma uncayley_mem {z : ℂ} (hz : z ∈ upperHalfPlane) :
    uncayley z ∈ HardyDiskSpec.disk := by
  change dist (uncayley z) 0 < 1
  rw [dist_zero_right]
  change ‖(z - Complex.I) / (z + Complex.I)‖ < 1
  rw [norm_div]
  apply (div_lt_one (norm_pos_iff.mpr (add_I_ne_zero hz))).mpr
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im, Complex.add_re,
    add_zero, Complex.add_im]
  change 0 < z.im at hz
  nlinarith

lemma uncayley_cayley {w : ℂ} (hw : w ∈ HardyDiskSpec.disk) : uncayley (cayley w) = w := by
  change (Complex.I * (1 + w) / (1 - w) - Complex.I) /
    (Complex.I * (1 + w) / (1 - w) + Complex.I) = w
  have h := one_sub_ne_zero hw
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  ring

lemma cayley_uncayley {z : ℂ} (hz : z ∈ upperHalfPlane) : cayley (uncayley z) = z := by
  change Complex.I * (1 + (z - Complex.I) / (z + Complex.I)) /
    (1 - (z - Complex.I) / (z + Complex.I)) = z
  have h := add_I_ne_zero hz
  field_simp
  ring

lemma normalization_ne_zero : normalization ≠ 0 := by
  unfold normalization
  exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos))

lemma transform_inverse (g : HardyDiskSpec.H2) {w : ℂ} (hw : w ∈ HardyDiskSpec.disk) :
    transform (inverseTransform g) w = HardyDiskSpec.eval g w := by
  simp only [HardyCayleySpec.transform, HardyCayleySpec.inverseTransform, uncayley_cayley hw]
  field_simp [normalization_ne_zero, one_sub_ne_zero hw]

lemma inverse_transform {F : ℂ → ℂ} {g : HardyDiskSpec.H2}
    (h : EqOn (HardyDiskSpec.eval g) (transform F) HardyDiskSpec.disk)
    {z : ℂ} (hz : z ∈ upperHalfPlane) : inverseTransform g z = F z := by
  change (1 - uncayley z) * HardyDiskSpec.eval g (uncayley z) / normalization = F z
  rw [h (uncayley_mem hz)]
  simp only [HardyCayleySpec.transform, cayley_uncayley hz]
  field_simp [normalization_ne_zero, one_sub_ne_zero (uncayley_mem hz)]

lemma cayley_differentiable : DifferentiableOn ℂ cayley HardyDiskSpec.disk := by
  apply DifferentiableOn.div
  · fun_prop
  · fun_prop
  · intro w hw; exact one_sub_ne_zero hw

lemma uncayley_differentiable : DifferentiableOn ℂ uncayley upperHalfPlane := by
  apply DifferentiableOn.div
  · fun_prop
  · fun_prop
  · intro z hz; exact add_I_ne_zero hz

lemma transform_differentiable {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalfPlane) :
    DifferentiableOn ℂ (transform F) HardyDiskSpec.disk := by
  exact ((differentiableOn_const _).mul
    (hF.comp cayley_differentiable (fun _ hw => cayley_mem hw))).div
      (by fun_prop) (fun _ hw => one_sub_ne_zero hw)

lemma inverse_differentiable (g : HardyDiskSpec.H2) :
    DifferentiableOn ℂ (inverseTransform g) upperHalfPlane := by
  exact (((differentiableOn_const _).sub uncayley_differentiable).mul
    ((HardyDisk.analytic_evaluation g).differentiableOn.comp
      uncayley_differentiable (fun _ hz => uncayley_mem hz))).div_const _

/-- The spectral Hilbert space furnished by the accepted half-plane representation. -/
abbrev SpectralL2 := Lp ℂ 2 positiveMeasure
abbrev Upper := {z : ℂ // z ∈ upperHalfPlane}

/-- Riesz vector for point evaluation in the causal spectral model. -/
def halfKernel (z : Upper) : SpectralL2 :=
  ((HardyHalfPlaneRepresentation.kernel_memLp z z.property).star).toLp
    (conj (kernel z))

lemma halfKernel_coe (z : Upper) :
    (halfKernel z : ℝ → ℂ) =ᵐ[positiveMeasure] (fun t => conj (kernel z t)) :=
  ((HardyHalfPlaneRepresentation.kernel_memLp z z.property).star).coeFn_toLp

lemma halfKernel_reproduces (z : Upper) (f : SpectralL2) :
    inner ℂ (halfKernel z) f = laplace f z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [halfKernel_coe z] with t ht
  simp [ht, RCLike.inner_apply, mul_comm]

lemma halfKernel_inner (z q : Upper) :
    inner ℂ (halfKernel z) (halfKernel q) =
      -1 / (2 * (Real.pi : ℂ) * Complex.I * (z.val - conj q.val)) := by
  rw [L2.inner_def]
  have heq : (fun t : ℝ => inner ℂ (halfKernel z t) (halfKernel q t)) =ᵐ[positiveMeasure]
      (fun t : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I *
        (z.val - conj q.val)) * (t : ℂ))) := by
    filter_upwards [halfKernel_coe z, halfKernel_coe q] with t hz hq
    simp only [hz, hq, RCLike.inner_apply, Complex.conj_conj]
    change conj (kernel q.val t) * kernel z.val t = _
    rw [kernel, kernel, ← Complex.exp_conj]
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [integral_congr_ae heq]
  have hneg : (2 * (Real.pi : ℂ) * Complex.I * (z.val - conj q.val)).re < 0 := by
    have hz := z.property
    have hq := q.property
    change 0 < z.val.im at hz
    change 0 < q.val.im at hq
    simp [Complex.mul_re, Complex.mul_im]
    nlinarith [Real.pi_pos]
  simpa only [mul_zero, Complex.ofReal_zero, Complex.exp_zero, neg_div] using
    integral_exp_mul_complex_Ioi hneg 0

/-- Riesz vector for evaluation in the canonical disk coefficient model. -/
def diskKernel (w : HardyDiskSpec.Disk) : HardyDiskSpec.H2 :=
  HardyDisk.geometricSequence ⟨conj w.val, by
    simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right, Complex.norm_conj] using
      disk_norm w.property⟩

lemma diskKernel_reproduces (w : HardyDiskSpec.Disk) (f : HardyDiskSpec.H2) :
    inner ℂ (diskKernel w) f = HardyDiskSpec.eval f w := by
  rw [lp.inner_eq_tsum]
  simp only [diskKernel, HardyDisk.geometricSequence, RCLike.inner_apply,
    map_pow, Complex.conj_conj, HardyDiskSpec.eval]

lemma diskKernel_inner (v w : HardyDiskSpec.Disk) :
    inner ℂ (diskKernel v) (diskKernel w) = (1 - v.val * conj w.val)⁻¹ := by
  rw [diskKernel_reproduces]
  change (∑' n : ℕ, (conj w.val) ^ n * v.val ^ n) = _
  simp only [← mul_pow]
  rw [mul_comm (conj w.val)]
  apply tsum_geometric_of_norm_lt_one
  rw [norm_mul, Complex.norm_conj]
  nlinarith [disk_norm v.property, disk_norm w.property, norm_nonneg v.val, norm_nonneg w.val]

def transportedKernel (w : HardyDiskSpec.Disk) : SpectralL2 :=
  conj (normalization / (1 - w.val)) • halfKernel ⟨cayley w, cayley_mem w.property⟩

lemma transportedKernel_reproduces (w : HardyDiskSpec.Disk) (f : SpectralL2) :
    inner ℂ (transportedKernel w) f = transform (laplace f) w := by
  rw [transportedKernel, inner_smul_left, Complex.conj_conj, halfKernel_reproduces]
  change normalization / (1 - w.val) * laplace f (cayley w) =
    normalization * laplace f (cayley w) / (1 - w.val)
  ring

lemma normalization_sq : normalization * conj normalization = 4 * (Real.pi : ℂ) := by
  simp only [normalization, map_mul, map_ofNat, Complex.conj_ofReal]
  have hs : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  calc
    _ = 4 * (Real.sqrt Real.pi : ℂ) ^ 2 := by ring
    _ = _ := by rw [hs]

lemma cayley_cross (v w : HardyDiskSpec.Disk) :
    (cayley v - conj (cayley w)) * (1 - v.val) * (1 - conj w.val) =
      2 * Complex.I * (1 - v.val * conj w.val) := by
  change (Complex.I * (1 + v.val) / (1 - v.val) -
    conj (Complex.I * (1 + w.val) / (1 - w.val))) * _ * _ = _
  simp only [map_div₀, map_mul, map_add, map_sub, map_one, Complex.conj_I]
  have hv := one_sub_ne_zero v.property
  have hw : 1 - conj w.val ≠ 0 := by
    simpa only [map_sub, map_one] using (map_ne_zero (starRingEnd ℂ)).mpr (one_sub_ne_zero w.property)
  field_simp
  ring

lemma transportedKernel_inner (v w : HardyDiskSpec.Disk) :
    inner ℂ (transportedKernel v) (transportedKernel w) =
      inner ℂ (diskKernel v) (diskKernel w) := by
  rw [transportedKernel, transportedKernel, inner_smul_left, inner_smul_right,
    Complex.conj_conj, halfKernel_inner, diskKernel_inner]
  have hv := one_sub_ne_zero v.property
  have hw : 1 - conj w.val ≠ 0 := by
    simpa only [map_sub, map_one] using (map_ne_zero (starRingEnd ℂ)).mpr (one_sub_ne_zero w.property)
  have hc := cayley_cross v w
  have hdiff : cayley v - conj (cayley w) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    have hv' := cayley_mem v.property
    have hw' := cayley_mem w.property
    change 0 < (cayley v).im at hv'
    change 0 < (cayley w).im at hw'
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hprod : 1 - v.val * conj w.val ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact (mul_ne_zero (mul_ne_zero hdiff hv) hw) hc
  simp only [map_div₀, map_sub, map_one]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  have hn := normalization_sq
  calc
    _ = -(normalization * conj normalization) * (1 - v.val * conj w.val) := by ring
    _ = -(4 * (Real.pi : ℂ)) * (1 - v.val * conj w.val) := by rw [hn]
    _ = (2 * (Real.pi : ℂ) * Complex.I) *
        (2 * Complex.I * (1 - v.val * conj w.val)) := by
      ring_nf
      simp [Complex.I_sq]
      ring
    _ = _ := by rw [← hc]; ring

lemma diskKernel_total (f : HardyDiskSpec.H2)
    (hf : ∀ w : HardyDiskSpec.Disk, inner ℂ (diskKernel w) f = 0) : f = 0 := by
  apply HardyDisk.evaluation_injective
  intro w hw
  rw [← diskKernel_reproduces ⟨w, hw⟩, hf]
  simp [HardyDiskSpec.eval]

lemma transportedKernel_total (f : SpectralL2)
    (hf : ∀ w : HardyDiskSpec.Disk, inner ℂ (transportedKernel w) f = 0) : f = 0 := by
  have hlap : ∀ z ∈ upperHalfPlane, laplace f z = 0 := by
    intro z hz
    have h := hf ⟨uncayley z, uncayley_mem hz⟩
    rw [transportedKernel_reproduces] at h
    change normalization * laplace f (cayley (uncayley z)) / (1 - uncayley z) = 0 at h
    rw [cayley_uncayley hz] at h
    simpa only [div_eq_zero_iff, mul_eq_zero, normalization_ne_zero, false_or,
      one_sub_ne_zero (uncayley_mem hz), or_false] using h
  have hrep : Represents (fun _ => 0) f :=
    ⟨Lp.memLp f, fun z hz => (hlap z hz).symm⟩
  have hzero : Represents (fun _ => 0) (fun _ => 0) := by
    refine ⟨MemLp.zero', ?_⟩
    intro z hz
    simp [laplace]
  have hae := HardyHalfPlaneRepresentation.representation_unique _ _ _ hrep hzero
  apply Lp.ext
  exact hae.trans (Lp.coeFn_zero ℂ 2 positiveMeasure).symm

/-- A total family has dense finite linear combinations. -/
lemma dense_linearCombination {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} (k : ι → E)
    (ht : ∀ f : E, (∀ i, inner ℂ (k i) f = 0) → f = 0) :
    DenseRange (Finsupp.linearCombination ℂ k) := by
  change Dense (Set.range (Finsupp.linearCombination ℂ k))
  rw [← LinearMap.coe_range, Finsupp.range_linearCombination,
    Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  apply eq_bot_iff.mpr
  intro f hf
  change f = 0
  apply ht
  intro i
  exact Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self i)) hf

lemma kernelCombination_norm (a : HardyDiskSpec.Disk →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ transportedKernel a‖ =
      ‖Finsupp.linearCombination ℂ diskKernel a‖ := by
  have hi : inner ℂ (Finsupp.linearCombination ℂ transportedKernel a)
      (Finsupp.linearCombination ℂ transportedKernel a) =
      inner ℂ (Finsupp.linearCombination ℂ diskKernel a)
        (Finsupp.linearCombination ℂ diskKernel a) := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
      inner_smul_left, inner_smul_right, transportedKernel_inner]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hi]

/-- Extension of the Gram-preserving map on finite kernel sums. -/
def spectralIsometry : HardyDiskSpec.H2 →ₗᵢ[ℂ] SpectralL2 :=
  (Finsupp.linearCombination ℂ transportedKernel).extendOfIsometry
    (dense_linearCombination diskKernel diskKernel_total) kernelCombination_norm

lemma spectralIsometry_kernel (w : HardyDiskSpec.Disk) :
    spectralIsometry (diskKernel w) = transportedKernel w := by
  have h := LinearMap.extendOfIsometry_eq
    (Finsupp.linearCombination ℂ transportedKernel)
    (dense_linearCombination diskKernel diskKernel_total) kernelCombination_norm
    (Finsupp.single w (1 : ℂ))
  simpa [spectralIsometry] using h

lemma spectralIsometry_surjective : Function.Surjective spectralIsometry := by
  have hspan : Submodule.span ℂ (Set.range transportedKernel) ≤
      LinearMap.range spectralIsometry.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact ⟨diskKernel w, spectralIsometry_kernel w⟩
  have hd := dense_linearCombination transportedKernel transportedKernel_total
  have hclosed : IsClosed (LinearMap.range spectralIsometry.toLinearMap : Set SpectralL2) :=
    spectralIsometry.isometry.isClosedEmbedding.isClosed_range
  have hle := Submodule.topologicalClosure_mono hspan
  have ht : (Submodule.span ℂ (Set.range transportedKernel)).topologicalClosure = ⊤ := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mp
    rwa [← Finsupp.range_linearCombination, LinearMap.coe_range]
  rw [ht, hclosed.submodule_topologicalClosure_eq] at hle
  exact LinearMap.range_eq_top.mp (top_unique hle)

/-- The disk coefficient model and the causal spectral L² model are unitary. -/
def spectralUnitary : HardyDiskSpec.H2 ≃ₗᵢ[ℂ] SpectralL2 :=
  LinearIsometryEquiv.ofSurjective spectralIsometry spectralIsometry_surjective

lemma spectralUnitary_evaluation (g : HardyDiskSpec.H2) (w : HardyDiskSpec.Disk) :
    HardyDiskSpec.eval g w = transform (laplace (spectralUnitary g)) w := by
  rw [← diskKernel_reproduces, ← spectralUnitary.inner_map_map]
  change inner ℂ (spectralIsometry (diskKernel w)) (spectralUnitary g) = _
  rw [spectralIsometry_kernel, transportedKernel_reproduces]

lemma laplace_congr {f h : ℝ → ℂ} (heq : f =ᵐ[positiveMeasure] h) (z : ℂ) :
    laplace f z = laplace h z := by
  apply integral_congr_ae
  filter_upwards [heq] with t ht
  rw [ht]

lemma inverse_represents (g : HardyDiskSpec.H2) :
    Represents (inverseTransform g) (spectralUnitary g) := by
  refine ⟨Lp.memLp _, ?_⟩
  intro z hz
  exact inverse_transform (fun w hw => spectralUnitary_evaluation g ⟨w, hw⟩) hz

lemma represents_of_match {F : ℂ → ℂ} {g : HardyDiskSpec.H2}
    (h : EqOn (HardyDiskSpec.eval g) (transform F) HardyDiskSpec.disk) :
    Represents F (spectralUnitary g) := by
  refine ⟨Lp.memLp _, ?_⟩
  intro z hz
  exact (inverse_transform h hz).symm.trans ((inverse_represents g).2 z hz)

theorem correspondence : Correspondence := by
  intro F
  constructor
  · intro hF
    obtain ⟨f, hf⟩ := (HardyHalfPlaneRepresentation.representation F).mp hF
    let u : SpectralL2 := hf.1.toLp f
    let g := spectralUnitary.symm u
    have heq : EqOn (HardyDiskSpec.eval g) (transform F) HardyDiskSpec.disk := by
      intro w hw
      rw [spectralUnitary_evaluation g ⟨w, hw⟩]
      change normalization * laplace (spectralUnitary g) (cayley w) / (1 - w) =
        normalization * F (cayley w) / (1 - w)
      dsimp only [g]
      rw [spectralUnitary.apply_symm_apply, laplace_congr hf.1.coeFn_toLp,
        hf.2 _ (cayley_mem hw)]
    refine ⟨g, heq, ?_⟩
    intro h hh
    apply HardyDisk.evaluation_injective
    exact hh.trans heq.symm
  · rintro ⟨g, hg, _⟩
    exact HardyHalfPlaneRepresentation.represents_isH2 (represents_of_match hg)

theorem onto : Onto := by
  intro g
  exact ⟨HardyHalfPlaneRepresentation.represents_isH2 (inverse_represents g),
    fun w hw => transform_inverse g hw⟩

lemma frequencyDensity_norm (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) :
    ‖HardyHalfPlaneRepresentation.frequencyDensity f hf‖ = (eLpNorm f 2 positiveMeasure).toReal := by
  rw [HardyHalfPlaneRepresentation.frequencyDensity, Lp.norm_toLp,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi.nullMeasurableSet]

lemma boundary_of_represents {F : ℂ → ℂ} {f : ℝ → ℂ} (h : Represents F f) :
    HasBoundary F (𝓕⁻ (HardyHalfPlaneRepresentation.frequencyDensity f h.1)) := by
  obtain ⟨s, hs, hlim⟩ := HardyHalfPlaneRepresentation.laplace_hasBoundary f h.1
  refine ⟨s, ?_, hlim⟩
  intro y hy
  rw [HardyHalfPlaneRepresentation.slice_of_represents h hy]
  exact hs y hy

theorem boundary_norm : BoundaryNorm := by
  intro F g hF hg b hb
  let u := spectralUnitary g
  have hrep := represents_of_match hg
  have hbc := HardyHalfPlaneRepresentation.boundary_unique hb (boundary_of_represents hrep)
  rw [hbc, HardyHalfPlaneRepresentation.norm_inverse_fourier, frequencyDensity_norm]
  change ‖g‖ = (eLpNorm u 2 positiveMeasure).toReal
  rw [← Lp.norm_def, spectralUnitary.norm_map]

lemma slice_integral_eq_density {F : ℂ → ℂ} {f : ℝ → ℂ} (h : Represents F f)
    {y : ℝ} (hy : 0 < y) :
    (∫ x : ℝ, ‖slice F y x‖ ^ 2) =
      ‖HardyHalfPlaneRepresentation.density f h.1 y‖ ^ 2 := by
  rw [HardyHalfPlaneRepresentation.slice_of_represents h hy,
    HardyHalfPlaneRepresentation.integral_norm_sq_eq _
      (HardyHalfPlaneRepresentation.slice_memLp f h.1 hy),
    HardyHalfPlaneRepresentation.slice_laplace_norm f h.1 hy,
    HardyHalfPlaneRepresentation.density_norm f h.1 hy.le]

theorem slice_norm : SliceNorm := by
  intro F g hF hg
  let u := spectralUnitary g
  have hrep : Represents F u := represents_of_match hg
  have hn : (eLpNorm u 2 positiveMeasure).toReal = ‖g‖ := by
    rw [← Lp.norm_def, spectralUnitary.norm_map]
  have hlim : Tendsto (fun y => ‖HardyHalfPlaneRepresentation.density u hrep.1 y‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (‖g‖ ^ 2)) := by
    simpa only [frequencyDensity_norm, hn] using
      (HardyHalfPlaneRepresentation.density_tendsto u hrep.1).norm.pow 2
  refine ⟨?_, ?_⟩
  · rintro r ⟨y, hy, rfl⟩
    rw [slice_integral_eq_density hrep hy,
      HardyHalfPlaneRepresentation.density_norm u hrep.1 hy.le, ← hn]
    apply pow_le_pow_left₀ ENNReal.toReal_nonneg
    exact ENNReal.toReal_mono hrep.1.eLpNorm_ne_top
      (HardyHalfPlaneRepresentation.damping_bound u hrep.1 y hy.le).2
  · intro C hC
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [← slice_integral_eq_density hrep hy]
    exact hC ⟨y, hy, rfl⟩

theorem linear_correspondence : LinearCorrespondence := by
  intro F G g h hF hG hg hh a b
  have heq : EqOn (HardyDiskSpec.eval (a • g + b • h))
      (transform (a • F + b • G)) HardyDiskSpec.disk := by
    intro w hw
    change HardyDisk.eval (a • g + b • h) w = _
    rw [HardyDisk.evaluation_add _ _ _ hw, HardyDisk.evaluation_smul,
      HardyDisk.evaluation_smul]
    change a * HardyDiskSpec.eval g w + b * HardyDiskSpec.eval h w = _
    rw [hg hw, hh hw]
    simp only [HardyCayleySpec.transform, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact ⟨HardyHalfPlaneRepresentation.represents_isH2 (represents_of_match heq), heq⟩

theorem unitary : Unitary :=
  ⟨spectralUnitary, fun g w hw => spectralUnitary_evaluation g ⟨w, hw⟩⟩

end ExpandedFA.PartIV.HardyCayley
