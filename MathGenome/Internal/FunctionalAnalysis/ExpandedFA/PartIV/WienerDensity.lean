import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.WienerDensity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.WienerLocalIdeal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section
open MeasureTheory Filter Set
open scoped Topology FourierTransform ContDiff Manifold

namespace ExpandedFA.PartIV.WienerDensity
open ExpandedFA.Fourier ExpandedFA.PartIV.WienerLocalIdeal
open ExpandedFA.PartIV.WienerLocal (evaluation evaluation_apply evaluation_translate
  phase phase_smul continuous_translate)
variable {d : ℕ}

lemma evaluation_schwartz (ψ : Schwartz ℂ d) (ξ : Euclidean d) :
    evaluation ξ (ψ.toLp 1 volume) = schwartzFourier ψ ξ := by
  rw [evaluation_apply, Real.fourier_congr_ae (ψ.coeFn_toLp 1), ← SchwartzMap.fourier_coe]
  rfl

/-- A finite smooth frequency partition patches the local ideal theorem. -/
lemma compact_spectrum_mem (Y : Submodule ℂ (L1 d))
    (hY : IsClosed (Y : Set (L1 d))) (htrans : TranslationInvariant Y)
    (hno : ∀ ξ : Euclidean d, ∃ f : L1 d, f ∈ Y ∧ integralFourier f ξ ≠ 0)
    (ψ : Schwartz ℂ d) (hc : HasCompactSupport (schwartzFourier ψ)) :
    ψ.toLp 1 volume ∈ Y := by
  classical
  have hlocal : ∀ ξ : Euclidean d, ∃ U : Set (Euclidean d), IsOpen U ∧ ξ ∈ U ∧
      ∀ φ : Schwartz ℂ d, tsupport (schwartzFourier φ) ⊆ U → φ.toLp 1 volume ∈ Y := by
    intro ξ
    obtain ⟨f, hf, hξ⟩ := hno ξ
    exact local_ideal d Y hY htrans f hf ξ hξ
  choose U hopen hpoint hmem using hlocal
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover U hopen (fun ξ _ => mem_iUnion.mpr ⟨ξ, hpoint ξ⟩)
  have hcover : tsupport (schwartzFourier ψ) ⊆ ⋃ i : s, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, Euclidean d)) (isClosed_tsupport _) (fun i : s => U i)
    (fun i => hopen i) hcover
  let P : s → Schwartz ℂ d := fun i =>
    (hc.smul_left (f := fun x => ρ i x)).toSchwartzMap
      (((ρ i).contMDiff.contDiff).smul ((schwartzFourier ψ).smooth ⊤))
  let Q : s → Schwartz ℂ d := fun i => 𝓕⁻ (P i)
  have hQ : ∀ i : s, (Q i).toLp 1 volume ∈ Y := by
    intro i
    apply hmem i (Q i)
    have hF : schwartzFourier (Q i) = P i := by
      change 𝓕 (𝓕⁻ (P i)) = P i
      exact FourierTransform.fourier_fourierInv_eq (P i)
    rw [hF]
    exact (tsupport_smul_subset_left (fun x => ρ i x) (schwartzFourier ψ)).trans (hρ i)
  have hsum : ∑ i : s, P i = schwartzFourier ψ := by
    ext x
    simp only [sum_apply]
    change ∑ i : s, ρ i x • schwartzFourier ψ x = schwartzFourier ψ x
    by_cases hx : x ∈ tsupport (schwartzFourier ψ)
    · rw [← Finset.sum_smul]
      have hh := ρ.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at hh
      rw [hh, one_smul]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hsumQ : ∑ i : s, Q i = ψ := by
    apply (FourierTransform.fourierCLE ℂ (Schwartz ℂ d)).injective
    change schwartzFourier (∑ i : s, Q i) = schwartzFourier ψ
    rw [map_sum]
    simpa only [Q, schwartzFourier, FourierTransform.fourierCLM_apply,
      FourierTransform.fourier_fourierInv_eq] using hsum
  have hlp : (∑ i : s, Q i).toLp 1 volume = ∑ i : s, (Q i).toLp 1 volume :=
    map_sum (SchwartzMap.toLpCLM ℂ ℂ 1 volume) _ _
  rw [← hsumQ, hlp]
  exact Y.sum_mem fun i _ => hQ i

@[simp] lemma translate_norm (y : Euclidean d) (f : L1 d) : ‖translate y f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

/-- A Schwartz approximate identity need not be nonnegative: integrability and
mass one suffice for convergence in L¹. -/
def scaledAverage (g : Schwartz ℂ d) (f : L1 d) (t : ℝ) : L1 d :=
  ∫ y, g y • translate (t • y) f

lemma scaledAverage_integrable (g : Schwartz ℂ d) (f : L1 d) (t : ℝ) :
    Integrable (fun y => g y • translate (t • y) f) := by
  have hc : Continuous (fun y : Euclidean d => translate (t • y) f) :=
    (continuous_translate f).comp (continuous_const_smul t)
  apply (g.integrable.norm.mul_const ‖f‖).mono'
    (g.continuous.aestronglyMeasurable.smul hc.aestronglyMeasurable)
  exact .of_forall fun y => by simp [norm_smul]

lemma scaledAverage_tendsto (g : Schwartz ℂ d) (hg : ∫ y, g y = 1) (f : L1 d) :
    Tendsto (scaledAverage g f) (𝓝 (0 : ℝ)) (𝓝 f) := by
  have hc (t : ℝ) : Continuous (fun y : Euclidean d => translate (t • y) f) :=
    (continuous_translate f).comp (continuous_const_smul t)
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Euclidean d)))
    (l := 𝓝 (0 : ℝ)) (F := fun t y => g y • translate (t • y) f)
    (f := fun y : Euclidean d => g y • f)
    (fun y => ‖g y‖ * ‖f‖)
    (.of_forall fun t => g.continuous.aestronglyMeasurable.smul (hc t).aestronglyMeasurable)
    (.of_forall fun t => .of_forall fun y => by simp [norm_smul])
    (g.integrable.norm.mul_const ‖f‖) ?_
  · change Tendsto (fun t : ℝ => ∫ y, g y • translate (t • y) f) (𝓝 0) (𝓝 f)
    rw [integral_smul_const, hg, one_smul] at h
    exact h
  · exact .of_forall fun y => by
      have hy : Tendsto (fun t : ℝ => t • y) (𝓝 0) (𝓝 0) := by
        have hh : Continuous (fun t : ℝ => t • y) := by fun_prop
        simpa only [zero_smul] using hh.tendsto (0 : ℝ)
      have ht : Tendsto (fun t : ℝ => translate (t • y) f) (𝓝 0) (𝓝 f) := by
        change Tendsto (fun t : ℝ => ExpandedFA.PartIV.WienerLocal.translate (t • y) f)
          (𝓝 0) (𝓝 f)
        simpa only [Function.comp_def, ExpandedFA.PartIV.WienerLocal.translate_zero] using
          ((continuous_translate f).tendsto 0).comp hy
      exact ht.const_smul (g y)

lemma evaluation_scaledAverage (g : Schwartz ℂ d) (f : L1 d) (t : ℝ) (ξ : Euclidean d) :
    evaluation ξ (scaledAverage g f t) = schwartzFourier g (t • ξ) * evaluation ξ f := by
  rw [scaledAverage, ← (evaluation ξ).integral_comp_comm (scaledAverage_integrable g f t)]
  calc
    (∫ y, evaluation ξ (g y • translate (t • y) f)) =
        ∫ y, (phase (t • ξ) y * g y) * evaluation ξ f := by
      apply integral_congr_ae
      filter_upwards [] with y
      change evaluation ξ (g y • ExpandedFA.PartIV.WienerLocal.translate (t • y) f) = _
      rw [map_smul, evaluation_translate, phase_smul, smul_eq_mul]
      ring
    _ = _ := by
      rw [integral_mul_const, ← ExpandedFA.PartIV.WienerLocal.fourier_eq,
        ← SchwartzMap.fourier_coe]
      rfl

/-- For nonzero dilation, the averages belong to the ideal: the dilated
compact frequency cutoff is the transform of a Schwartz member of the ideal. -/
lemma scaledAverage_mem (Y : Submodule ℂ (L1 d))
    (hY : IsClosed (Y : Set (L1 d))) (htrans : TranslationInvariant Y)
    (hno : ∀ ξ : Euclidean d, ∃ f : L1 d, f ∈ Y ∧ integralFourier f ξ ≠ 0)
    (g : Schwartz ℂ d) (hg : HasCompactSupport (schwartzFourier g))
    (f : L1 d) (t : ℝ) (ht : t ≠ 0) : scaledAverage g f t ∈ Y := by
  let B : Schwartz ℂ d :=
    (hg.comp_isClosedEmbedding (Homeomorph.smulOfNeZero t ht).isClosedEmbedding).toSchwartzMap
      (((schwartzFourier g).smooth ⊤).comp (contDiff_id.const_smul t))
  let k : Schwartz ℂ d := 𝓕⁻ B
  have hkF : schwartzFourier k = B := by
    change 𝓕 (𝓕⁻ B) = B
    exact FourierTransform.fourier_fourierInv_eq B
  have hk : k.toLp 1 volume ∈ Y := by
    apply compact_spectrum_mem Y hY htrans hno
    rw [hkF]
    exact hg.comp_isClosedEmbedding (Homeomorph.smulOfNeZero t ht).isClosedEmbedding
  have heq : scaledAverage g f t = WienerLocalIdeal.convolution (k.toLp 1 volume) f := by
    apply evaluation_injective
    intro ξ
    rw [evaluation_scaledAverage, evaluation_convolution, evaluation_schwartz, hkF]
    rfl
  rw [heq]
  exact convolution_ideal d Y hY htrans _ f hk

lemma exists_compact_spectrum_mass_one (d : ℕ) :
    ∃ g : Schwartz ℂ d, HasCompactSupport (schwartzFourier g) ∧ ∫ y, g y = 1 := by
  let b : ContDiffBump (0 : Euclidean d) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  have hc : HasCompactSupport (fun x => (b x : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) rfl
  let B : Schwartz ℂ d := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let g : Schwartz ℂ d := 𝓕⁻ B
  have hg : schwartzFourier g = B := by
    change 𝓕 (𝓕⁻ B) = B
    exact FourierTransform.fourier_fourierInv_eq B
  refine ⟨g, ?_, ?_⟩
  · rw [hg]
    exact hc
  · have hval : schwartzFourier g 0 = 1 := by
      rw [hg]
      change (b 0 : ℂ) = 1
      rw [b.one_of_mem_closedBall (by simpa using b.rIn_pos.le)]
      rfl
    rw [ExpandedFA.Fourier.schwartz_integral, integralFourier] at hval
    simpa using hval

/-- The global density step. This proof applies to every Euclidean dimension. -/
lemma eq_top_of_no_common_zero (Y : Submodule ℂ (L1 d))
    (hY : IsClosed (Y : Set (L1 d))) (htrans : TranslationInvariant Y)
    (hno : ∀ ξ : Euclidean d, ∃ f : L1 d, f ∈ Y ∧ integralFourier f ξ ≠ 0) : Y = ⊤ := by
  obtain ⟨g, hc, hg⟩ := exists_compact_spectrum_mass_one d
  apply top_unique
  intro f _
  apply hY.mem_of_tendsto ((scaledAverage_tendsto g hg f).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact scaledAverage_mem Y hY htrans hno g hc f t (ne_of_gt ht)

/-- Fourier evaluation at each frequency is a nonzero continuous functional. -/
lemma exists_evaluation_one (ξ : Euclidean d) : ∃ f : L1 d, evaluation ξ f = 1 := by
  let b : ContDiffBump ξ :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  have hc : HasCompactSupport (fun x => (b x : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) rfl
  let B : Schwartz ℂ d := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let g : Schwartz ℂ d := 𝓕⁻ B
  refine ⟨g.toLp 1 volume, ?_⟩
  rw [evaluation_schwartz]
  change (𝓕 (𝓕⁻ B) : Schwartz ℂ d) ξ = 1
  rw [FourierTransform.fourier_fourierInv_eq]
  change (b ξ : ℂ) = 1
  rw [b.one_of_mem_closedBall (by simpa using b.rIn_pos.le)]
  rfl

/-- A common Fourier zero prevents a subspace from being all of L¹. -/
lemma ne_top_of_common_zero (Y : Submodule ℂ (L1 d)) (ξ : Euclidean d)
    (hzero : ∀ f ∈ Y, integralFourier f ξ = 0) : Y ≠ ⊤ := by
  intro htop
  obtain ⟨f, hf⟩ := exists_evaluation_one ξ
  have hz := hzero f (htop ▸ Submodule.mem_top)
  rw [integralFourier_eq_native] at hz
  change evaluation ξ f = 0 at hz
  rw [hf] at hz
  exact one_ne_zero hz

theorem subspace_criterion : Specs.ExpandedFA.PartIV.WienerDensity.SubspaceCriterion := by
  intro d Y hY htrans
  constructor
  · intro htop ξ
    obtain ⟨f, hf⟩ := exists_evaluation_one ξ
    refine ⟨f, htop ▸ Submodule.mem_top, ?_⟩
    rw [integralFourier_eq_native]
    change evaluation ξ f ≠ 0
    rw [hf]
    exact one_ne_zero
  · exact eq_top_of_no_common_zero Y hY htrans

/-- Translation as a continuous complex-linear map on the same L¹ classes. -/
def translationCLM (y : Euclidean d) : L1 d →L[ℂ] L1 d :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x => x - y)
    (measurePreserving_sub_right volume y)).toContinuousLinearMap

@[simp] lemma translationCLM_apply (y : Euclidean d) (f : L1 d) :
    translationCLM y f = translate y f := rfl

lemma translate_translate (y z : Euclidean d) (f : L1 d) :
    translate y (translate z f) = translate (y + z) f := by
  apply evaluation_injective
  intro ξ
  change evaluation ξ (ExpandedFA.PartIV.WienerLocal.translate y
    (ExpandedFA.PartIV.WienerLocal.translate z f)) =
    evaluation ξ (ExpandedFA.PartIV.WienerLocal.translate (y + z) f)
  simp only [evaluation_translate]
  simp [phase, inner_add_left, AddChar.map_add_eq_mul, mul_assoc, mul_left_comm]

lemma kernel_mem_closedTranslateSpan (K : L1 d) : K ∈ closedTranslateSpan K := by
  have hz : translate (0 : Euclidean d) K = K :=
    ExpandedFA.PartIV.WienerLocal.translate_zero K
  have hh : translate (0 : Euclidean d) K ∈ closedTranslateSpan K :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self 0))
  simpa only [hz] using hh

lemma closedTranslateSpan_invariant (K : L1 d) : TranslationInvariant (closedTranslateSpan K) := by
  intro y f hf
  let S := Submodule.span ℂ (range (fun z => translate z K))
  have hS : ∀ g ∈ S, translationCLM y g ∈ S := by
    have hle : S ≤ S.comap (translationCLM y).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z, rfl⟩
      change translate y (translate z K) ∈ S
      rw [translate_translate]
      exact Submodule.subset_span (mem_range_self (y + z))
    exact fun g hg => hle hg
  have hm : MapsTo (translationCLM y) (S : Set (L1 d)) (S : Set (L1 d)) := hS
  exact hm.closure (translationCLM y).continuous hf

lemma closedTranslateSpan_le_evaluation_ker (K : L1 d) (ξ : Euclidean d)
    (hzero : integralFourier K ξ = 0) :
    closedTranslateSpan K ≤ (evaluation ξ).ker := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨y, rfl⟩
    change evaluation ξ (ExpandedFA.PartIV.WienerLocal.translate y K) = 0
    rw [evaluation_translate]
    have hz : evaluation ξ K = 0 := by
      simpa only [evaluation_apply, integralFourier_eq_native] using hzero
    rw [hz, mul_zero]
  · exact (evaluation ξ).isClosed_ker

theorem translate_criterion : Specs.ExpandedFA.PartIV.WienerDensity.TranslateCriterion := by
  intro d K
  constructor
  · intro htop ξ hzero
    have hker := closedTranslateSpan_le_evaluation_ker K ξ hzero
    obtain ⟨f, hf⟩ := exists_evaluation_one ξ
    have hz : evaluation ξ f = 0 := hker (htop ▸ Submodule.mem_top)
    rw [hf] at hz
    exact one_ne_zero hz
  · intro hK
    apply (subspace_criterion d (closedTranslateSpan K)
      (Submodule.isClosed_topologicalClosure _) (closedTranslateSpan_invariant K)).mpr
    intro ξ
    exact ⟨K, kernel_mem_closedTranslateSpan K, hK ξ⟩

/- The manuscript also allows real scalars. We pass through the closed complex
subspace whose real and imaginary parts lie in the given real subspace. -/
def ofRealLp : RealL1 d →L[ℝ] L1 d := Complex.ofRealCLM.compLpL 1 volume

def reLp : L1 d →L[ℝ] RealL1 d := Complex.reCLM.compLpL 1 volume

def imLp : L1 d →L[ℝ] RealL1 d := Complex.imCLM.compLpL 1 volume

lemma ofRealLp_ae (f : RealL1 d) :
    (ofRealLp f : Euclidean d → ℂ) =ᵐ[volume] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLp f

lemma reLp_ae (f : L1 d) :
    (reLp f : Euclidean d → ℝ) =ᵐ[volume] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLp f

lemma imLp_ae (f : L1 d) :
    (imLp f : Euclidean d → ℝ) =ᵐ[volume] fun x => (f x).im :=
  Complex.imCLM.coeFn_compLp f

lemma reLp_smul (c : ℂ) (f : L1 d) :
    reLp (c • f) = c.re • reLp f - c.im • imLp f := by
  apply Lp.ext
  filter_upwards [reLp_ae (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_sub (c.re • reLp f) (c.im • imLp f),
    Lp.coeFn_smul c.re (reLp f), Lp.coeFn_smul c.im (imLp f),
    reLp_ae f, imLp_ae f] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  change (reLp (c • f)) x = _ at h₁
  simp only [Pi.smul_apply, Pi.sub_apply] at h₂ h₃ h₄ h₅
  rw [h₁, h₂, h₃, h₄, h₅]
  change (c * f x).re = c.re * (reLp f) x - c.im * (imLp f) x
  rw [h₆, h₇, Complex.mul_re]

lemma imLp_smul (c : ℂ) (f : L1 d) :
    imLp (c • f) = c.re • imLp f + c.im • reLp f := by
  apply Lp.ext
  filter_upwards [imLp_ae (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_add (c.re • imLp f) (c.im • reLp f),
    Lp.coeFn_smul c.re (imLp f), Lp.coeFn_smul c.im (reLp f),
    reLp_ae f, imLp_ae f] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  change (imLp (c • f)) x = _ at h₁
  simp only [Pi.smul_apply, Pi.add_apply] at h₂ h₃ h₄ h₅
  rw [h₁, h₂, h₃, h₄, h₅]
  change (c * f x).im = c.re * (imLp f) x + c.im * (reLp f) x
  rw [h₆, h₇, Complex.mul_im]

@[simp] lemma reLp_ofRealLp (f : RealL1 d) : reLp (ofRealLp f) = f := by
  apply Lp.ext
  filter_upwards [reLp_ae (ofRealLp f),
    ofRealLp_ae f] with x hx hy
  rw [hx, hy]
  simp

@[simp] lemma imLp_ofRealLp (f : RealL1 d) : imLp (ofRealLp f) = 0 := by
  apply Lp.ext
  filter_upwards [imLp_ae (ofRealLp f),
    ofRealLp_ae f, Lp.coeFn_zero ℝ 1 (volume : Measure (Euclidean d))] with x hx hy hz
  rw [hx, hy, hz]
  simp

lemma complex_decompose (f : L1 d) : ofRealLp (reLp f) + Complex.I • ofRealLp (imLp f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (ofRealLp (reLp f)) (Complex.I • ofRealLp (imLp f)),
    Lp.coeFn_smul Complex.I (ofRealLp (imLp f)),
    ofRealLp_ae (reLp f), ofRealLp_ae (imLp f),
    reLp_ae f, imLp_ae f] with x h₁ h₂ h₃ h₄ h₅ h₆
  simp only [Pi.add_apply, Pi.smul_apply] at h₁ h₂
  rw [h₁, h₂, h₃, h₄, h₅, h₆]
  simp only [smul_eq_mul]
  rw [mul_comm, Complex.re_add_im]

/-- Scalar continuous linear maps commute with translation on a.e. classes. -/
lemma compLp_translate {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (y : Euclidean d) (f : Lp E 1 (volume : Measure (Euclidean d))) :
    A.compLp (Lp.compMeasurePreserving (fun x => x - y) (measurePreserving_sub_right volume y) f) =
      Lp.compMeasurePreserving (fun x => x - y) (measurePreserving_sub_right volume y) (A.compLp f) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLp (Lp.compMeasurePreserving (fun x => x - y)
      (measurePreserving_sub_right volume y) f),
    Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume y),
    Lp.coeFn_compMeasurePreserving (A.compLp f) (measurePreserving_sub_right volume y),
    (measurePreserving_sub_right volume y).quasiMeasurePreserving.ae (A.coeFn_compLp f)] with x h₁ h₂ h₃ h₄
  simpa only [h₂, h₃, Function.comp_def, h₄] using h₁

def complexification (Y : Submodule ℝ (RealL1 d)) : Submodule ℂ (L1 d) where
  carrier := {f | reLp f ∈ Y ∧ imLp f ∈ Y}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact ⟨by simpa using Y.add_mem hf.1 hg.1, by simpa using Y.add_mem hf.2 hg.2⟩
  smul_mem' := by
    intro c f hf
    exact ⟨by rw [reLp_smul]; exact Y.sub_mem (Y.smul_mem _ hf.1) (Y.smul_mem _ hf.2),
      by rw [imLp_smul]; exact Y.add_mem (Y.smul_mem _ hf.2) (Y.smul_mem _ hf.1)⟩

lemma complexification_closed (Y : Submodule ℝ (RealL1 d)) (hY : IsClosed (Y : Set (RealL1 d))) :
    IsClosed (complexification Y : Set (L1 d)) :=
  (hY.preimage reLp.continuous).inter (hY.preimage imLp.continuous)

lemma complexification_invariant (Y : Submodule ℝ (RealL1 d)) (hY : RealTranslationInvariant Y) :
    TranslationInvariant (complexification Y) := by
  intro y f hf
  change reLp (translate y f) ∈ Y ∧ imLp (translate y f) ∈ Y
  have hre : reLp (translate y f) = realTranslate y (reLp f) :=
    compLp_translate Complex.reCLM y f
  have him : imLp (translate y f) = realTranslate y (imLp f) :=
    compLp_translate Complex.imCLM y f
  rw [hre, him]
  exact ⟨hY y _ hf.1, hY y _ hf.2⟩

def realEvaluation (ξ : Euclidean d) : RealL1 d →L[ℝ] ℂ :=
  ((evaluation ξ).restrictScalars ℝ).comp ofRealLp

lemma realEvaluation_apply (ξ : Euclidean d) (f : RealL1 d) :
    realEvaluation ξ f = integralFourier (fun x => (f x : ℂ)) ξ := by
  change evaluation ξ (ofRealLp f) = _
  rw [evaluation_apply, integralFourier_eq_native]
  exact Real.fourier_congr_ae (Complex.ofRealCLM.coeFn_compLp f) ξ

lemma realEvaluation_translate (ξ y : Euclidean d) (f : RealL1 d) :
    realEvaluation ξ (realTranslate y f) = phase ξ y * realEvaluation ξ f := by
  change evaluation ξ (ofRealLp (realTranslate y f)) = _
  have h : ofRealLp (realTranslate y f) = translate y (ofRealLp f) :=
    compLp_translate Complex.ofRealCLM y f
  rw [h]
  exact evaluation_translate ξ y (ofRealLp f)

lemma exists_realEvaluation_ne_zero (ξ : Euclidean d) : ∃ f : RealL1 d, realEvaluation ξ f ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_evaluation_one ξ
  by_contra! h
  have heq := congrArg (evaluation ξ) (complex_decompose f)
  change evaluation ξ (ofRealLp (reLp f) + Complex.I • ofRealLp (imLp f)) = _ at heq
  simp only [map_add, map_smul, smul_eq_mul] at heq
  change realEvaluation ξ (reLp f) + Complex.I * realEvaluation ξ (imLp f) = _ at heq
  rw [h, h, mul_zero, add_zero, hf] at heq
  exact zero_ne_one heq

theorem real_subspace_criterion : Specs.ExpandedFA.PartIV.WienerDensity.RealSubspaceCriterion := by
  intro d Y hY htrans
  constructor
  · intro htop ξ
    obtain ⟨f, hf⟩ := exists_realEvaluation_ne_zero ξ
    exact ⟨f, htop ▸ Submodule.mem_top, by rwa [← realEvaluation_apply]⟩
  · intro hno
    have hC : complexification Y = ⊤ := by
      apply eq_top_of_no_common_zero _ (complexification_closed Y hY) (complexification_invariant Y htrans)
      intro ξ
      obtain ⟨f, hf, hξ⟩ := hno ξ
      refine ⟨ofRealLp f, ?_, ?_⟩
      · change reLp (ofRealLp f) ∈ Y ∧ imLp (ofRealLp f) ∈ Y
        simpa using And.intro hf Y.zero_mem
      · rw [integralFourier_eq_native]
        change realEvaluation ξ f ≠ 0
        rwa [realEvaluation_apply]
    apply top_unique
    intro f _
    have hf : ofRealLp f ∈ complexification Y := hC ▸ Submodule.mem_top
    have hr := hf.1
    simpa using hr

lemma ofRealLp_injective : Function.Injective (ofRealLp (d := d)) := by
  intro f g h
  simpa only [reLp_ofRealLp] using congrArg reLp h

lemma ofRealLp_translate (y : Euclidean d) (f : RealL1 d) :
    ofRealLp (realTranslate y f) = translate y (ofRealLp f) :=
  compLp_translate Complex.ofRealCLM y f

@[simp] lemma realTranslate_zero (f : RealL1 d) : realTranslate 0 f = f := by
  apply ofRealLp_injective
  rw [ofRealLp_translate]
  exact ExpandedFA.PartIV.WienerLocal.translate_zero _

lemma realTranslate_translate (y z : Euclidean d) (f : RealL1 d) :
    realTranslate y (realTranslate z f) = realTranslate (y + z) f := by
  apply ofRealLp_injective
  simp only [ofRealLp_translate, translate_translate]

def realTranslationCLM (y : Euclidean d) : RealL1 d →L[ℝ] RealL1 d :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x => x - y)
    (measurePreserving_sub_right volume y)).toContinuousLinearMap

@[simp] lemma realTranslationCLM_apply (y : Euclidean d) (f : RealL1 d) :
    realTranslationCLM y f = realTranslate y f := rfl

lemma kernel_mem_closedRealTranslateSpan (K : RealL1 d) : K ∈ closedRealTranslateSpan K := by
  have hh : realTranslate (0 : Euclidean d) K ∈ closedRealTranslateSpan K :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self 0))
  simpa only [realTranslate_zero] using hh

lemma closedRealTranslateSpan_invariant (K : RealL1 d) :
    RealTranslationInvariant (closedRealTranslateSpan K) := by
  intro y f hf
  let S := Submodule.span ℝ (range (fun z => realTranslate z K))
  have hS : ∀ g ∈ S, realTranslationCLM y g ∈ S := by
    have hle : S ≤ S.comap (realTranslationCLM y).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z, rfl⟩
      change realTranslate y (realTranslate z K) ∈ S
      rw [realTranslate_translate]
      exact Submodule.subset_span (mem_range_self (y + z))
    exact fun g hg => hle hg
  have hm : MapsTo (realTranslationCLM y) (S : Set (RealL1 d)) (S : Set (RealL1 d)) := hS
  exact hm.closure (realTranslationCLM y).continuous hf

lemma closedRealTranslateSpan_le_evaluation_ker (K : RealL1 d) (ξ : Euclidean d)
    (hzero : integralFourier (fun x => (K x : ℂ)) ξ = 0) :
    closedRealTranslateSpan K ≤ (realEvaluation ξ).ker := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨y, rfl⟩
    change realEvaluation ξ (realTranslate y K) = 0
    rw [realEvaluation_translate, realEvaluation_apply, hzero, mul_zero]
  · exact (realEvaluation ξ).isClosed_ker

theorem real_translate_criterion : Specs.ExpandedFA.PartIV.WienerDensity.RealTranslateCriterion := by
  intro d K
  constructor
  · intro htop ξ hzero
    have hker := closedRealTranslateSpan_le_evaluation_ker K ξ hzero
    obtain ⟨f, hf⟩ := exists_realEvaluation_ne_zero ξ
    exact hf (hker (htop ▸ Submodule.mem_top))
  · intro hK
    apply (real_subspace_criterion d (closedRealTranslateSpan K)
      (Submodule.isClosed_topologicalClosure _) (closedRealTranslateSpan_invariant K)).mpr
    intro ξ
    exact ⟨K, kernel_mem_closedRealTranslateSpan K, hK ξ⟩

end ExpandedFA.PartIV.WienerDensity
