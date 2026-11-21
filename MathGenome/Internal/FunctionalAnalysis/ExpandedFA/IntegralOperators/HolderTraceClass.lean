import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.HolderTraceClass
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.IntegralOperators.HolderSingularTail
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.IntegralOperators.ContinuousTraceDiagonal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.IntegralOperators.Mercer
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.Lidskii
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.RegularizedEigenvalueProduct
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Topology.UnitInterval

noncomputable section
open MeasureTheory Filter
open scoped Topology
universe u
namespace ExpandedFA.IntegralOperators.HolderTraceClass
open HolderSingularTail.Spec ContinuousTraceDiagonal.Spec
open TraceIdeals.TraceClassDefinitions.Spec TraceIdeals.Lidskii.Spec
open FredholmDeterminant.ClassicalDefinitions.Spec

/-- Absolute eigenvalue summability directly gives normal convergence of the
unregularized factors. This works even at zeros of the finite products. -/
lemma uniform_linear_product {ι : Type*} (a : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖)) (R : ℝ) :
    TendstoUniformlyOn (fun s : Finset ι => fun z : ℂ => ∏ i ∈ s, (1 - z * a i))
      (fun z => ∏' i, (1 - z * a i)) atTop (Metric.closedBall 0 R) := by
  have hb : ∀ᶠ i in cofinite, ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖-(z * a i)‖ ≤ R * ‖a i‖ := by
    filter_upwards [] with i z hz
    rw [norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.mp hz) (norm_nonneg _)
  have hu := Summable.hasProdUniformlyOn_one_add (R := ℂ)
    (f := fun i z => -(z * a i)) (isCompact_closedBall 0 R) (ha.mul_left R) hb
    (fun i => ((continuous_id.mul continuous_const).neg).continuousOn)
  simpa only [sub_eq_add_neg] using hu.tendstoUniformlyOn

/-- Cancel the exponential factors using Lidskii's absolutely convergent sum.
Convergence to the actual Fredholm series is asserted via HasProd. -/
lemma unregularized_hasProd {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (ν : Measure Q) [IsFiniteMeasure ν]
    (k : C(Q × Q, ℂ))
    (hs : HasSum (eigenvalue (continuousKernelOperator ν k)) (∫ t, k (t,t) ∂ν)) (z : ℂ) :
    HasProd (fun i : EigenvalueIndex (continuousKernelOperator ν k) =>
      1 - z * eigenvalue (continuousKernelOperator ν k) i)
      (FredholmDeterminantValue ν k z) := by
  have he := (hs.mul_left (-z)).cexp
  have hr := FredholmDeterminant.RegularizedEigenvalueProduct.product_formula ν k z
  have hp := hr.mul he
  have hc (w : ℂ) :
      FredholmDeterminant.RegularizedEigenvalueProduct.Spec.Data.factor w *
        Complex.exp (-w) = 1 - w := by
    rw [FredholmDeterminant.RegularizedEigenvalueProduct.Spec.Data.factor,
      mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  have hlim : (Complex.exp (z * ∫ t, k (t,t) ∂ν) * FredholmDeterminantValue ν k z) *
      Complex.exp (-z * ∫ t, k (t,t) ∂ν) = FredholmDeterminantValue ν k z := by
    rw [mul_right_comm, ← Complex.exp_add]
    simp
  rw [hlim] at hp
  convert hp using 1
  funext i
  simpa only [Function.comp_apply, neg_mul] using (hc (z * eigenvalue _ i)).symm

theorem traceClass_spectral : Spec.TraceClassSpectral.{u} := by
  intro Q _ _ _ _ ν _ k hk
  have hd := ContinuousTraceDiagonal.diagonal_trace Q ν k hk
  obtain ⟨ha, hs⟩ := TraceIdeals.Lidskii.lidskii _ _ hk
  rw [hd] at hs
  refine ⟨hd, ha, hs, ?_, ?_⟩
  · intro z
    refine ⟨?_, unregularized_hasProd ν k hs z⟩
    simpa only [sub_sub_cancel_left, norm_neg, norm_mul] using ha.mul_left ‖z‖
  · intro R _
    have hu := uniform_linear_product _ ha R
    have heq : (fun z => ∏' i : EigenvalueIndex (continuousKernelOperator ν k),
        (1 - z * eigenvalue (continuousKernelOperator ν k) i)) =
        FredholmDeterminantValue ν k := by
      funext z
      exact (unregularized_hasProd ν k hs z).tprod_eq
    rwa [heq] at hu

theorem firstVariable : Spec.FirstVariable := by
  intro k α H hα hα' hk
  obtain ⟨hT, hb⟩ := HolderSingularTail.firstVariable ℂ k α H hα hα' hk
  exact ⟨hT, hb, traceClass_spectral μ k hT⟩

theorem secondVariable : Spec.SecondVariable := by
  intro k α H hα hα' hk
  obtain ⟨hT, hb⟩ := HolderSingularTail.secondVariable ℂ k α H hα hα' hk
  exact ⟨hT, hb, traceClass_spectral μ k hT⟩

lemma holderFirst_of_contDiffOn {𝕜 : Type} [RCLike 𝕜]
    (k : C(I × I, 𝕜)) (f : ℝ × ℝ → 𝕜)
    (hf : ∀ p : I × I, f (p.1.val, p.2.val) = k p)
    (hd : ContDiffOn ℝ 1 f Spec.square) : ∃ H : ℝ, HolderFirst k 1 H := by
  obtain ⟨C, hC⟩ := hd.exists_lipschitzOnWith (by norm_num)
    ((convex_Icc (0 : ℝ) 1).prod (convex_Icc (0 : ℝ) 1))
    (isCompact_Icc.prod isCompact_Icc)
  refine ⟨C, ?_⟩
  intro x x' y
  have h := hC.dist_le_mul ((x : ℝ), (y : ℝ))
    (show ((x : ℝ), (y : ℝ)) ∈ Spec.square from ⟨x.property, y.property⟩)
    ((x' : ℝ), (y : ℝ)) (show ((x' : ℝ), (y : ℝ)) ∈ Spec.square from ⟨x'.property, y.property⟩)
  rw [hf (x,y), hf (x',y)] at h
  simpa [dist_eq_norm, Prod.norm_def, Real.norm_eq_abs] using h


theorem continuouslyDifferentiable_quantitative : Spec.C1Quantitative := by
  intro 𝕜 _ k f hf hd
  obtain ⟨H, hH⟩ := holderFirst_of_contDiffOn k f hf hd
  obtain ⟨hT, hb⟩ := HolderSingularTail.firstVariable 𝕜 k 1 H (by norm_num) le_rfl hH
  exact ⟨H, hH, hT, hb⟩

theorem continuouslyDifferentiable : Spec.ContinuouslyDifferentiable := by
  intro k f hf hd
  obtain ⟨H, hH⟩ := holderFirst_of_contDiffOn k f hf hd
  obtain ⟨hT, hb, hs⟩ := firstVariable k 1 H (by norm_num) le_rfl hH
  exact ⟨⟨H, hH, hb⟩, hT, hs⟩

theorem smooth : Spec.Smooth := by
  intro k f hf hd
  exact (continuouslyDifferentiable k f hf (hd.of_le (by simp))).2


open MeasureTheory.Measure

section Scale
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type*} [MeasurableSpace X] (ν : Measure X) (c : ℝ) (hc : 0 < c)

include hc in
lemma memLp_unscale (f : Lp 𝕜 2 (ENNReal.ofReal c • ν)) : MemLp (f : X → 𝕜) 2 ν := by
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  have hh := (Lp.memLp f).smul_measure (c := (ENNReal.ofReal c)⁻¹)
    (ENNReal.inv_ne_top.mpr hc0)
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul] using hh

def changeMeasureToLp (f : Lp 𝕜 2 ν) : Lp 𝕜 2 (ENNReal.ofReal c • ν) :=
  ((Lp.memLp f).smul_measure (by simp)).toLp f

lemma changeMeasureToLp_ae (f : Lp 𝕜 2 ν) :
    (changeMeasureToLp ν c f : X → 𝕜) =ᵐ[ENNReal.ofReal c • ν] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).smul_measure (by simp))

def changeMeasureLp : Lp 𝕜 2 ν ≃ₗ[𝕜] Lp 𝕜 2 (ENNReal.ofReal c • ν) where
  toFun := changeMeasureToLp ν c
  invFun f := (memLp_unscale ν c hc f).toLp f
  left_inv f := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans
      ((ae_ennreal_smul_measure_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hc))).mp
        (changeMeasureToLp_ae ν c f))
  right_inv f := by
    apply Lp.ext
    exact (changeMeasureToLp_ae ν c _).trans (ae_smul_measure (MemLp.coeFn_toLp _) _)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [changeMeasureToLp_ae ν c (f+g),
      Lp.coeFn_add (changeMeasureToLp ν c f) (changeMeasureToLp ν c g),
      changeMeasureToLp_ae ν c f, changeMeasureToLp_ae ν c g,
      ae_smul_measure (Lp.coeFn_add f g) (ENNReal.ofReal c)] with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at *
    exact h₁.trans (h₅.trans (h₂.trans (congrArg₂ (·+·) h₃ h₄)).symm)
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [changeMeasureToLp_ae ν c (z • f),
      Lp.coeFn_smul z (changeMeasureToLp ν c f), changeMeasureToLp_ae ν c f,
      ae_smul_measure (Lp.coeFn_smul z f) (ENNReal.ofReal c)] with x h₁ h₂ h₃ h₄
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at *
    exact h₁.trans (h₄.trans (h₂.trans (congrArg (z*·) h₃)).symm)

lemma changeMeasureLp_ae (f : Lp 𝕜 2 ν) :
    (changeMeasureLp ν c hc f : X → 𝕜) =ᵐ[ENNReal.ofReal c • ν] f :=
  changeMeasureToLp_ae ν c f

lemma changeMeasureLp_norm (f : Lp 𝕜 2 ν) :
    ‖changeMeasureLp ν c hc f‖ = Real.sqrt c * ‖f‖ := by
  change ‖((Lp.memLp f).smul_measure (c := ENNReal.ofReal c) (by simp)).toLp f‖ = _
  rw [Lp.norm_toLp,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)]
  simp only [smul_eq_mul, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hc.le, Lp.norm_def]
  norm_num [Real.sqrt_eq_rpow]

/-- Changing a finite positive scalar multiple of a measure, with the
reciprocal square-root factor, is a unitary of the ordinary L² spaces. -/
def measureScaleUnitary : Lp 𝕜 2 ν ≃ₗᵢ[𝕜] Lp 𝕜 2 (ENNReal.ofReal c • ν) := by
  let d : 𝕜 := (Real.sqrt c : 𝕜)⁻¹
  have hd : d ≠ 0 := inv_ne_zero (RCLike.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hc).ne')
  let V : Lp 𝕜 2 ν →ₗᵢ[𝕜] Lp 𝕜 2 (ENNReal.ofReal c • ν) :=
    { toLinearMap := d • (changeMeasureLp ν c hc).toLinearMap
      norm_map' := by
        intro f
        change ‖d • changeMeasureLp ν c hc f‖ = ‖f‖
        rw [norm_smul, changeMeasureLp_norm ν c hc]
        simp [d, norm_inv,
          abs_of_nonneg (Real.sqrt_nonneg c), ← mul_assoc,
          inv_mul_cancel₀ (Real.sqrt_pos.mpr hc).ne'] }
  exact LinearIsometryEquiv.ofSurjective V (by
    intro g
    obtain ⟨f, hf⟩ := (changeMeasureLp ν c hc).surjective (d⁻¹ • g)
    refine ⟨f, ?_⟩
    change d • changeMeasureLp ν c hc f = g
    rw [hf, smul_inv_smul₀ hd])

lemma measureScaleUnitary_ae (f : Lp 𝕜 2 ν) :
    (measureScaleUnitary ν c hc f : X → 𝕜) =ᵐ[ENNReal.ofReal c • ν]
      fun x => (Real.sqrt c : 𝕜)⁻¹ * f x := by
  have h := Lp.coeFn_smul (Real.sqrt c : 𝕜)⁻¹ (changeMeasureLp ν c hc f)
  exact h.trans ((changeMeasureLp_ae ν c hc f).fun_comp (fun z => (Real.sqrt c : 𝕜)⁻¹ * z))

end Scale
section Composition
variable {𝕜 : Type} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure Y} {ξ : Measure X}

def measurePreservingUnitary (e : X ≃ᵐ Y) (he : MeasurePreserving e ξ ν) :
    Lp 𝕜 2 ν ≃ₗᵢ[𝕜] Lp 𝕜 2 ξ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ 𝕜 e he) (by
    intro g
    refine ⟨Lp.compMeasurePreserving e.symm (he.symm e) g, ?_⟩
    apply Lp.ext
    have h₁ := Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving e.symm (he.symm e) g) he
    have h₂ := he.quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving g (he.symm e))
    filter_upwards [h₁, h₂] with x hx hy
    change (Lp.compMeasurePreserving e he
      (Lp.compMeasurePreserving e.symm (he.symm e) g) : X → 𝕜) x = g x
    simpa only [Function.comp_apply, e.symm_apply_apply] using hx.trans hy)

lemma measurePreservingUnitary_ae (e : X ≃ᵐ Y) (he : MeasurePreserving e ξ ν)
    (f : Lp 𝕜 2 ν) :
    (measurePreservingUnitary e he f : X → 𝕜) =ᵐ[ξ] fun x => f (e x) :=
  Lp.coeFn_compMeasurePreserving f he

/-- A change of variables with a constant positive density. -/
def weightedCompositionUnitary (e : X ≃ᵐ Y) (c : ℝ) (hc : 0 < c)
    (he : MeasurePreserving e ξ (ENNReal.ofReal c • ν)) :
    Lp 𝕜 2 ν ≃ₗᵢ[𝕜] Lp 𝕜 2 ξ :=
  (measureScaleUnitary ν c hc).trans (measurePreservingUnitary e he)

lemma weightedCompositionUnitary_ae (e : X ≃ᵐ Y) (c : ℝ) (hc : 0 < c)
    (he : MeasurePreserving e ξ (ENNReal.ofReal c • ν)) (f : Lp 𝕜 2 ν) :
    (weightedCompositionUnitary e c hc he f : X → 𝕜) =ᵐ[ξ]
      fun x => (Real.sqrt c : 𝕜)⁻¹ * f (e x) :=
  (measurePreservingUnitary_ae e he _).trans
    (he.quasiMeasurePreserving.ae_eq_comp (measureScaleUnitary_ae ν c hc f))
end Composition

def affineInterval (a b : ℝ) (hab : a < b) : I ≃ₜ Spec.Interval a b :=
  (iccHomeoI a b hab).symm

lemma affineInterval_coe (a b : ℝ) (hab : a < b) (t : I) :
    (affineInterval a b hab t : ℝ) = a + (b-a) * (t : ℝ) := by
  simp [affineInterval, add_comm]

lemma affineInterval_measure (a b : ℝ) (hab : a < b) :
    Measure.map (affineInterval a b hab) μ =
      ENNReal.ofReal (b-a)⁻¹ • Spec.intervalMeasure a b := by
  let e := affineInterval a b hab
  let f : ℝ → ℝ := fun x => a + (b-a)*x
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he : Measurable e := e.continuous.measurable
  have hfmap : Measure.map f volume = ENNReal.ofReal (b-a)⁻¹ • (volume : Measure ℝ) := by
    have hl : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    have hc : f = (fun x : ℝ => a+x) ∘ (fun x : ℝ => (b-a)*x) := rfl
    rw [hc, ← Measure.map_map (by fun_prop) (by fun_prop),
      Real.map_volume_mul_left hl, Measure.map_smul]
    simp [abs_of_pos (inv_pos.mpr (sub_pos.mpr hab)), map_add_left_eq_self]
    fun_prop
  have hpre : f ⁻¹' Set.Icc a b = Set.Icc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc, f]
    constructor
    · rintro ⟨hx, hy⟩
      constructor <;> nlinarith [sub_pos.mpr hab]
    · rintro ⟨hx, hy⟩
      constructor <;> nlinarith [sub_pos.mpr hab]
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  rw [Measure.map_smul, map_comap_subtype_coe measurableSet_Icc,
    Measure.map_map measurable_subtype_coe he]
  have hcomp : (Subtype.val : Spec.Interval a b → ℝ) ∘ e =
      f ∘ (Subtype.val : I → ℝ) := by
    funext x
    exact affineInterval_coe a b hab x
  rw [hcomp, ← Measure.map_map hf measurable_subtype_coe,
    map_comap_subtype_coe measurableSet_Icc, ← hpre,
    ← Measure.restrict_map hf measurableSet_Icc, hfmap, Measure.restrict_smul]
  fun_prop


section AffineKernel
variable {𝕜 : Type} [RCLike 𝕜]

/-- The canonical ordinary L² assignment, for either manuscript scalar field. -/
abbrev kernelOperatorOn {Q : Type*} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (ν : Measure Q) [IsFiniteMeasure ν]
    (k : C(Q × Q, 𝕜)) : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 ν :=
  PartV.L2KernelSpec.OperatorValue ν ν (ContinuousMap.toLp (E := 𝕜) 2 (ν.prod ν) 𝕜 k)

lemma kernelOperatorOn_ae {Q : Type*} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (ν : Measure Q) [IsFiniteMeasure ν]
    (k : C(Q × Q, 𝕜)) (f : Lp 𝕜 2 ν) :
    (kernelOperatorOn ν k f : Q → 𝕜) =ᵐ[ν] fun x => ∫ y, k (x,y) * f y ∂ν := by
  have hk := ContinuousMap.memLp (p := 2) (ν.prod ν) 𝕜 k
  have hc : hk.toLp k = ContinuousMap.toLp (E := 𝕜) 2 (ν.prod ν) 𝕜 k := by
    apply Lp.ext
    exact hk.coeFn_toLp.trans (ContinuousMap.coeFn_toLp (ν.prod ν) k).symm
  have hh := PartV.L2Kernel.kernel_representative_formula ν ν k f hk (Lp.memLp f)
  simpa only [hc, Lp.toLp_coeFn] using hh

def intervalUnitary (a b : ℝ) (hab : a < b) :
    Lp 𝕜 2 (Spec.intervalMeasure a b) ≃ₗᵢ[𝕜] L2 𝕜 :=
  weightedCompositionUnitary (affineInterval a b hab).toMeasurableEquiv
    (b-a)⁻¹ (inv_pos.mpr (sub_pos.mpr hab))
    ⟨(affineInterval a b hab).continuous.measurable, affineInterval_measure a b hab⟩

lemma intervalUnitary_ae (a b : ℝ) (hab : a < b)
    (f : Lp 𝕜 2 (Spec.intervalMeasure a b)) :
    (intervalUnitary a b hab f : I → 𝕜) =ᵐ[μ]
      fun t => (Real.sqrt (b-a) : 𝕜) * f (affineInterval a b hab t) := by
  have hh := weightedCompositionUnitary_ae
    (affineInterval a b hab).toMeasurableEquiv
    (b-a)⁻¹ (inv_pos.mpr (sub_pos.mpr hab))
    ⟨(affineInterval a b hab).continuous.measurable, affineInterval_measure a b hab⟩ f
  simpa [intervalUnitary, Real.sqrt_inv] using hh

def affineKernel (a b : ℝ) (hab : a < b)
    (k : C(Spec.Interval a b × Spec.Interval a b, 𝕜)) : C(I × I, 𝕜) :=
  (b-a : 𝕜) • k.comp
    ⟨fun p => (affineInterval a b hab p.1, affineInterval a b hab p.2),
      (affineInterval a b hab).continuous.prodMap (affineInterval a b hab).continuous⟩

lemma affineKernel_apply (a b : ℝ) (hab : a < b)
    (k : C(Spec.Interval a b × Spec.Interval a b, 𝕜)) (p : I × I) :
    affineKernel a b hab k p =
      (b-a : 𝕜) * k (affineInterval a b hab p.1, affineInterval a b hab p.2) := rfl

lemma affineInterval_dist (a b : ℝ) (hab : a < b) (x y : I) :
    |(affineInterval a b hab x : ℝ) - (affineInterval a b hab y : ℝ)| =
      (b-a) * |(x : ℝ) - (y : ℝ)| := by
  rw [affineInterval_coe, affineInterval_coe,
    show a + (b-a)*(x : ℝ) - (a + (b-a)*(y : ℝ)) = (b-a)*((x:ℝ)-(y:ℝ)) by ring,
    abs_mul, abs_of_pos (sub_pos.mpr hab)]

lemma affineKernel_holderFirst (a b : ℝ) (hab : a < b)
    (k : C(Spec.Interval a b × Spec.Interval a b, 𝕜)) (α H : ℝ)
    (hk : ∀ x x' y : Spec.Interval a b,
      ‖k (x,y) - k (x',y)‖ ≤ H * |(x : ℝ) - (x' : ℝ)| ^ α) :
    HolderFirst (affineKernel a b hab k) α (H * (b-a) ^ (α+1)) := by
  intro x x' y
  rw [affineKernel_apply, affineKernel_apply, ← mul_sub, norm_mul, ← RCLike.ofReal_sub,
    RCLike.norm_ofReal, abs_of_pos (sub_pos.mpr hab)]
  calc
    _ ≤ (b-a) * (H * |(affineInterval a b hab x : ℝ) -
        (affineInterval a b hab x' : ℝ)| ^ α) :=
      mul_le_mul_of_nonneg_left (hk _ _ _) (sub_pos.mpr hab).le
    _ = _ := by
      rw [affineInterval_dist, Real.mul_rpow (sub_pos.mpr hab).le (abs_nonneg _),
        Real.rpow_add (sub_pos.mpr hab), Real.rpow_one]
      ring

lemma affineKernel_holderSecond (a b : ℝ) (hab : a < b)
    (k : C(Spec.Interval a b × Spec.Interval a b, 𝕜)) (α H : ℝ)
    (hk : ∀ x y y' : Spec.Interval a b,
      ‖k (x,y) - k (x,y')‖ ≤ H * |(y : ℝ) - (y' : ℝ)| ^ α) :
    HolderSecond (affineKernel a b hab k) α (H * (b-a) ^ (α+1)) := by
  intro x y y'
  rw [affineKernel_apply, affineKernel_apply, ← mul_sub, norm_mul, ← RCLike.ofReal_sub,
    RCLike.norm_ofReal, abs_of_pos (sub_pos.mpr hab)]
  calc
    _ ≤ (b-a) * (H * |(affineInterval a b hab y : ℝ) -
        (affineInterval a b hab y' : ℝ)| ^ α) :=
      mul_le_mul_of_nonneg_left (hk _ _ _) (sub_pos.mpr hab).le
    _ = _ := by
      rw [affineInterval_dist, Real.mul_rpow (sub_pos.mpr hab).le (abs_nonneg _),
        Real.rpow_add (sub_pos.mpr hab), Real.rpow_one]
      ring

lemma affineInterval_integral (a b : ℝ) (hab : a < b)
    (f : Spec.Interval a b → 𝕜) :
    (∫ y, f y ∂Spec.intervalMeasure a b) =
      (b-a : 𝕜) * ∫ t, f (affineInterval a b hab t) ∂μ := by
  let e := (affineInterval a b hab).toMeasurableEquiv
  have hm : MeasurePreserving e μ
      (ENNReal.ofReal (b-a)⁻¹ • Spec.intervalMeasure a b) :=
    ⟨e.measurable, affineInterval_measure a b hab⟩
  have hh := hm.integral_comp e.measurableEmbedding f
  rw [integral_smul_measure] at hh
  change (∫ t, f (affineInterval a b hab t) ∂μ) = _ at hh
  rw [hh]
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (sub_pos.mpr hab).le),
    RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv, ← mul_assoc, ← RCLike.ofReal_sub,
    mul_inv_cancel₀ (show (↑(b-a) : 𝕜) ≠ 0 from
      RCLike.ofReal_ne_zero.mpr (sub_pos.mpr hab).ne'), one_mul]

lemma intervalUnitary_intertwines (a b : ℝ) (hab : a < b)
    (k : C(Spec.Interval a b × Spec.Interval a b, 𝕜))
    (f : Lp 𝕜 2 (Spec.intervalMeasure a b)) :
    intervalUnitary a b hab (kernelOperatorOn
      (Spec.intervalMeasure a b) k f) =
      kernel (affineKernel a b hab k) (intervalUnitary a b hab f) := by
  let hm : MeasurePreserving (affineInterval a b hab) μ
      (ENNReal.ofReal (b-a)⁻¹ • Spec.intervalMeasure a b) :=
    ⟨(affineInterval a b hab).continuous.measurable, affineInterval_measure a b hab⟩
  apply Lp.ext
  have hleft := intervalUnitary_ae a b hab
    (kernelOperatorOn (Spec.intervalMeasure a b) k f)
  have hmid := hm.quasiMeasurePreserving.ae_eq_comp
    (ae_smul_measure (kernelOperatorOn_ae
      (Spec.intervalMeasure a b) k f) (ENNReal.ofReal (b-a)⁻¹))
  have hright := kernelOperatorOn_ae μ
    (affineKernel a b hab k) (intervalUnitary a b hab f)
  filter_upwards [hleft, hmid, hright] with x hx hy hz
  simp only [Function.comp_apply] at hy
  rw [hx, hy, hz, affineInterval_integral a b hab,
    ← mul_assoc, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [intervalUnitary_ae a b hab f] with t ht
  rw [affineKernel_apply, ht]
  ring

section UnitaryIdeal
open TraceIdeals.TraceClassDefinitions.Spec
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]

lemma unitary_traceNorm_le (U : E ≃ₗᵢ[𝕜] F) (T : E →L[𝕜] E) (R : F →L[𝕜] F)
    (hT : IsTraceClassValue T) (h : ∀ x, U (T x) = R (U x)) :
    IsTraceClassValue R ∧ TraceNormValue R ≤ TraceNormValue T := by
  let A := U.toContinuousLinearEquiv.toContinuousLinearMap
  let B := U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hR : R = A.comp (T.comp B) := by
    ext x
    simpa [A, B] using (h (U.symm x)).symm
  have hA : ‖A‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound A zero_le_one (by
    intro x; simp [A])
  have hB : ‖B‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound B zero_le_one (by
    intro x; simp [B])
  have ht0 := ((TraceIdeals.TraceNormIdeal.normed_ideal_axioms 𝕜 E E).2.2.1 T hT).1
  obtain ⟨hTC, hbound⟩ := TraceIdeals.TraceNormIdeal.two_sided_ideal 𝕜 E E F F T A B hT
  rw [← hR] at hTC hbound
  refine ⟨hTC, hbound.trans ?_⟩
  calc
    ‖A‖ * TraceNormValue T * ‖B‖ ≤ 1 * TraceNormValue T * 1 := by gcongr
    _ = TraceNormValue T := by ring

lemma unitary_traceClass_iff_norm (U : E ≃ₗᵢ[𝕜] F)
    (T : E →L[𝕜] E) (R : F →L[𝕜] F) (h : ∀ x, U (T x) = R (U x)) :
    (IsTraceClassValue R ↔ IsTraceClassValue T) ∧
    (IsTraceClassValue R → TraceNormValue R = TraceNormValue T) := by
  have hinv : ∀ y, U.symm (R y) = T (U.symm y) := by
    intro y
    simpa using (congrArg U.symm (h (U.symm y))).symm
  have hf := unitary_traceNorm_le U T R
  have hb := unitary_traceNorm_le U.symm R T
  refine ⟨⟨fun hR => (hb hR hinv).1, fun hT => (hf hT h).1⟩, ?_⟩
  intro hR
  exact le_antisymm (hf (hb hR hinv).1 h).2 (hb hR hinv).2
end UnitaryIdeal

lemma affineKernel_norm (a b : ℝ) (hab : a < b)
    (k : C(Spec.Interval a b × Spec.Interval a b, 𝕜)) :
    ‖kernelClass (affineKernel a b hab k)‖ = ‖Spec.intervalKernelClass k‖ := by
  let ν := Spec.intervalMeasure a b
  let e := (affineInterval a b hab).toMeasurableEquiv
  let c := (b-a)⁻¹ * (b-a)⁻¹
  have hc : 0 < c := mul_pos (inv_pos.mpr (sub_pos.mpr hab))
    (inv_pos.mpr (sub_pos.mpr hab))
  have hm : MeasurePreserving e μ (ENNReal.ofReal (b-a)⁻¹ • ν) :=
    ⟨e.measurable, affineInterval_measure a b hab⟩
  have hp : MeasurePreserving (e.prodCongr e) (μ.prod μ)
      (ENNReal.ofReal c • ν.prod ν) := by
    convert hm.prod hm using 1
    · rfl
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (sub_pos.mpr hab).le)]
  let W := weightedCompositionUnitary (𝕜 := 𝕜) (e.prodCongr e) c hc hp
  have hscalar : (Real.sqrt c : 𝕜)⁻¹ = (b-a : 𝕜) := by
    dsimp [c]
    rw [Real.sqrt_mul_self (inv_nonneg.mpr (sub_pos.mpr hab).le),
      RCLike.ofReal_inv, inv_inv, RCLike.ofReal_sub]
  have hW : W (Spec.intervalKernelClass k) = kernelClass (affineKernel a b hab k) := by
    apply Lp.ext
    have h₁ := weightedCompositionUnitary_ae (e.prodCongr e) c hc hp
      (Spec.intervalKernelClass k)
    have h₂ := hp.quasiMeasurePreserving.ae_eq_comp
      (ae_smul_measure (ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (ν.prod ν) k) (ENNReal.ofReal c))
    have h₃ := ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (μ.prod μ) (affineKernel a b hab k)
    filter_upwards [h₁, h₂, h₃] with p hx hy hz
    rw [hx, hz, hscalar, affineKernel_apply]
    change (b-a : 𝕜) * (Spec.intervalKernelClass k) (e p.1, e p.2) = _
    rw [show (Spec.intervalKernelClass k) (e p.1,e p.2) = k (e p.1,e p.2) from hy]
    rfl
  exact (congrArg norm hW).symm.trans (W.norm_map _)

end AffineKernel

/-- The affine unitary and its two norm identities use the original scalar
field, including the actual real-valued L² space. -/
theorem scalarAffineTransport : Spec.ScalarAffineTransport := by
  intro 𝕜 _ a b hab k
  let e := affineInterval a b hab
  let q := affineKernel a b hab k
  let U := intervalUnitary (𝕜 := 𝕜) a b hab
  have hi := unitary_traceClass_iff_norm U
    (Spec.intervalKernelOperator k)
    (kernel q) (intervalUnitary_intertwines a b hab k)
  refine ⟨⟨e, e.continuous⟩, affineInterval_coe a b hab, q,
    affineKernel_apply a b hab k, U, intervalUnitary_ae a b hab,
    intervalUnitary_intertwines a b hab k, hi.1, hi.2,
    affineKernel_norm a b hab k, ?_, ?_⟩
  · intro α H _ _ hk
    exact affineKernel_holderFirst a b hab k α H hk
  · intro α H _ _ hk
    exact affineKernel_holderSecond a b hab k α H hk

/-- The actual affine change of variables, including both Jacobians and the
trace norm identity, for every nondegenerate compact interval. -/
theorem affineTransport : Spec.AffineTransport := scalarAffineTransport ℂ


/-- Assembly from an actual affine unitary and the scaled kernel, rather than
assuming a trace-class certificate for the interval operator. -/
theorem intervalFirstVariable_of_affineTransport
    (h : Spec.AffineTransport) : Spec.IntervalFirstVariable := by
  intro a b hab k α H hα hα' hk
  obtain ⟨φ, hφ, q, hq, U, hU, hint, hc, hn, hL, hfirst, hsecond⟩ := h a b hab k
  obtain ⟨hT, hb, _⟩ := firstVariable q α (H * (b-a) ^ (α+1)) hα hα'
    (hfirst α H hα hα' hk)
  have hI := hc.mp hT
  rw [hn hT, hL] at hb
  exact ⟨hI, hb, traceClass_spectral (Spec.intervalMeasure a b) k hI⟩

theorem intervalSecondVariable_of_affineTransport
    (h : Spec.AffineTransport) : Spec.IntervalSecondVariable := by
  intro a b hab k α H hα hα' hk
  obtain ⟨φ, hφ, q, hq, U, hU, hint, hc, hn, hL, hfirst, hsecond⟩ := h a b hab k
  obtain ⟨hT, hb, _⟩ := secondVariable q α (H * (b-a) ^ (α+1)) hα hα'
    (hsecond α H hα hα' hk)
  have hI := hc.mp hT
  rw [hn hT, hL] at hb
  exact ⟨hI, hb, traceClass_spectral (Spec.intervalMeasure a b) k hI⟩

lemma interval_holderFirst_of_contDiffOn {𝕜 : Type} [RCLike 𝕜] (a b : ℝ)
    (k : C(Spec.Interval a b × Spec.Interval a b, 𝕜)) (f : ℝ × ℝ → 𝕜)
    (hf : ∀ p : Spec.Interval a b × Spec.Interval a b, f (p.1.val, p.2.val) = k p)
    (hd : ContDiffOn ℝ 1 f (Set.Icc a b ×ˢ Set.Icc a b)) :
    ∃ H : ℝ, ∀ x x' y : Spec.Interval a b,
      ‖k (x,y) - k (x',y)‖ ≤ H * |(x : ℝ) - (x' : ℝ)| ^ (1 : ℝ) := by
  obtain ⟨C, hC⟩ := hd.exists_lipschitzOnWith (by norm_num)
    ((convex_Icc a b).prod (convex_Icc a b)) (isCompact_Icc.prod isCompact_Icc)
  refine ⟨C, ?_⟩
  intro x x' y
  have h := hC.dist_le_mul ((x : ℝ), (y : ℝ))
    (show ((x : ℝ), (y : ℝ)) ∈ Set.Icc a b ×ˢ Set.Icc a b from ⟨x.property, y.property⟩)
    ((x' : ℝ), (y : ℝ))
    (show ((x' : ℝ), (y : ℝ)) ∈ Set.Icc a b ×ˢ Set.Icc a b from ⟨x'.property, y.property⟩)
  rw [hf (x,y), hf (x',y)] at h
  simpa [dist_eq_norm, Prod.norm_def, Real.norm_eq_abs] using h

theorem intervalContinuouslyDifferentiable_of_firstVariable
    (h : Spec.IntervalFirstVariable) : Spec.IntervalContinuouslyDifferentiable := by
  intro a b hab k f hf hd
  obtain ⟨H, hH⟩ := interval_holderFirst_of_contDiffOn a b k f hf hd
  obtain ⟨hT, _, hs⟩ := h a b hab k 1 H (by norm_num) le_rfl hH
  exact ⟨hT, hs⟩

theorem intervalSmooth_of_continuouslyDifferentiable
    (h : Spec.IntervalContinuouslyDifferentiable) : Spec.IntervalSmooth := by
  intro a b hab k f hf hd
  exact h a b hab k f hf (hd.of_le (by simp))

/-- The quantitative first-variable criterion on the original interval measure. -/
theorem intervalFirstVariable : Spec.IntervalFirstVariable :=
  intervalFirstVariable_of_affineTransport affineTransport

/-- The quantitative second-variable criterion on the original interval measure. -/
theorem intervalSecondVariable : Spec.IntervalSecondVariable :=
  intervalSecondVariable_of_affineTransport affineTransport

theorem intervalContinuouslyDifferentiable : Spec.IntervalContinuouslyDifferentiable :=
  intervalContinuouslyDifferentiable_of_firstVariable intervalFirstVariable

theorem intervalSmooth : Spec.IntervalSmooth :=
  intervalSmooth_of_continuouslyDifferentiable intervalContinuouslyDifferentiable

/-- First-variable regularity on either scalar-valued interval L² space. -/
theorem scalarIntervalFirstVariable : Spec.ScalarIntervalFirstVariable := by
  intro 𝕜 _ a b hab k α H hα hα' hk
  obtain ⟨φ, hφ, q, hq, U, hU, hint, hc, hn, hL, hfirst, hsecond⟩ :=
    scalarAffineTransport 𝕜 a b hab k
  obtain ⟨hT, hb⟩ := HolderSingularTail.firstVariable 𝕜 q α
    (H * (b-a) ^ (α+1)) hα hα' (hfirst α H hα hα' hk)
  rw [hn hT, hL] at hb
  exact ⟨hc.mp hT, hb⟩

/-- The second-variable estimate has the same transported constant. -/
theorem scalarIntervalSecondVariable : Spec.ScalarIntervalSecondVariable := by
  intro 𝕜 _ a b hab k α H hα hα' hk
  obtain ⟨φ, hφ, q, hq, U, hU, hint, hc, hn, hL, hfirst, hsecond⟩ :=
    scalarAffineTransport 𝕜 a b hab k
  obtain ⟨hT, hb⟩ := HolderSingularTail.secondVariable 𝕜 q α
    (H * (b-a) ^ (α+1)) hα hα' (hsecond α H hα hα' hk)
  rw [hn hT, hL] at hb
  exact ⟨hc.mp hT, hb⟩

/-- Differentiability within the closed square supplies a bounded Lipschitz
constant, without requiring an extension to a neighborhood. -/
theorem scalarIntervalContinuouslyDifferentiable :
    Spec.ScalarIntervalContinuouslyDifferentiable := by
  intro 𝕜 _ a b hab k f hf hd
  obtain ⟨H, hH⟩ := interval_holderFirst_of_contDiffOn a b k f hf hd
  obtain ⟨hT, hb⟩ := scalarIntervalFirstVariable 𝕜 a b hab k 1 H
    (by norm_num) le_rfl hH
  refine ⟨H, ?_, hT, ?_⟩
  · simpa only [Real.rpow_one] using hH
  · convert hb using 1; norm_num

open scoped ContDiff in
/-- Smoothness means order infinity, and hence implies the C¹ criterion. -/
theorem scalarIntervalSmooth : Spec.ScalarIntervalSmooth := by
  intro 𝕜 _ a b hab k f hf hd
  obtain ⟨H, hH, hT, hb⟩ := scalarIntervalContinuouslyDifferentiable
    𝕜 a b hab k f hf (hd.of_le (by simp))
  exact hT


/-- Ordinary interval Lebesgue measure has full support when a < b. -/
lemma intervalMeasure_openPos (a b : ℝ) (hab : a < b) :
    (Spec.intervalMeasure a b).IsOpenPosMeasure := by
  constructor
  intro U hU hne
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  obtain ⟨x, hx⟩ := hne
  have hxc : (x : ℝ) ∈ closure (interior (Set.Icc a b)) := by
    rw [closure_interior_Icc hab.ne]
    exact x.property
  have hxV : x ∈ (Subtype.val : Set.Icc a b → ℝ) ⁻¹' V := by rwa [hVU]
  have hxn : (V ∩ interior (Set.Icc a b)).Nonempty :=
    mem_closure_iff.mp hxc V hV hxV
  have hp : 0 < volume (V ∩ interior (Set.Icc a b)) :=
    (hV.inter isOpen_interior).measure_pos volume hxn
  rw [comap_subtype_coe_apply measurableSet_Icc]
  apply ne_of_gt
  apply hp.trans_le (measure_mono ?_)
  intro y hy
  refine ⟨⟨y, interior_subset hy.2⟩, ?_, rfl⟩
  rw [← hVU]
  exact hy.1


/-- Specialize the genuine real diagonal trace identity to interval L². -/
theorem realIntervalDiagonalTrace : Spec.RealIntervalDiagonalTrace := by
  intro a b hab k hk
  letI : (Spec.intervalMeasure a b).IsOpenPosMeasure := intervalMeasure_openPos a b hab
  exact Mercer.real_diagonal_trace (Spec.Interval a b) (Spec.intervalMeasure a b) k hk

/-- Ordinary Lebesgue measure of a zero-length or empty interval is zero. -/
lemma intervalMeasure_eq_zero_of_le (a b : ℝ) (hab : b ≤ a) :
    Spec.intervalMeasure a b = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  change (volume.comap (Subtype.val : Spec.Interval a b → ℝ)) Set.univ = 0
  rw [comap_subtype_coe_apply measurableSet_Icc, Set.image_univ, Subtype.range_coe,
    Real.volume_Icc]
  exact ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hab)

/-- The actual integral operator and its trace data vanish for degenerate intervals. -/
theorem scalarDegenerateInterval : Spec.ScalarDegenerateInterval := by
  intro 𝕜 _ a b hab k
  have hμ := intervalMeasure_eq_zero_of_le a b hab
  have hzero : Spec.intervalKernelOperator k = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    have hae : ae (Spec.intervalMeasure a b) = ⊥ := by rw [hμ]; simp
    rw [hae]
    exact Filter.eventually_bot
  refine ⟨hzero, ?_, ?_, ?_, ?_⟩
  · rw [hzero]
    exact TraceIdeals.TraceNormIdeal.traceClass_zero
  · rw [hzero]
    exact TraceIdeals.TraceNormIdeal.traceNorm_zero
  · simp only [hzero, TraceValue, zero_apply, inner_zero_right, tsum_zero]
  · rw [hμ, integral_zero_measure]

end ExpandedFA.IntegralOperators.HolderTraceClass
