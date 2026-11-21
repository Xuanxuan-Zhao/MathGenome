import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachGeometry.EndpointInterpolation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08ClosedGraph
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Interpolation.RieszThorin

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
universe u

namespace ExpandedFA.BanachGeometry.EndpointInterpolation
open EndpointInterpolationSpec

variable {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {𝕜 : Type*} [RCLike 𝕜]

@[simp] theorem coe_toL1 (p : ℝ≥0∞) (hp : 1 ≤ p) (f : Lp 𝕜 p μ) :
    (toL1 p hp f : X →ₘ[μ] 𝕜) = f := rfl

theorem toL1_injective (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Function.Injective (toL1 (𝕜 := 𝕜) (μ := μ) p hp) := by
  intro f g h
  exact Subtype.ext (congrArg (fun x : Lp 𝕜 1 μ => (x : X →ₘ[μ] 𝕜)) h)

/-- The finite-measure inclusion is bounded, even when μ=0. -/
theorem toL1_bound (p : ℝ≥0∞) (hp : 1 ≤ p) [Fact (1 ≤ p)] (f : Lp 𝕜 p μ) :
    ‖toL1 p hp f‖ ≤ (μ Set.univ ^ (1 - 1 / p.toReal)).toReal * ‖f‖ := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (Lp.aestronglyMeasurable f)
  simp only [ENNReal.toReal_one, div_one] at h
  have hc : μ Set.univ ^ (1 - 1 / p.toReal) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · have hi : 1 / p.toReal ≤ 1 := by
        by_cases ht : p = ∞
        · simp [ht]
        · have hpr : 1 ≤ p.toReal := by
            simpa using ENNReal.toReal_mono ht hp
          exact (div_le_one (by linarith : 0 < p.toReal)).2 hpr
      linarith
    · exact measure_ne_top μ Set.univ
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hc) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_one, div_one, Lp.norm_def,
    coe_toL1, mul_comm] using hr

def toL1Continuous (p : ℝ≥0∞) (hp : 1 ≤ p) [Fact (1 ≤ p)] :
    Lp 𝕜 p μ →L[𝕜] Lp 𝕜 1 μ :=
  (toL1 p hp).mkContinuous (μ Set.univ ^ (1 - 1 / p.toReal)).toReal
    (toL1_bound p hp)

/-- The algebraic restriction exists from setwise invariance alone. -/
def infinityRestriction (T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ)
    (hT : PreservesInfinity T) : Lp 𝕜 ∞ μ →ₗ[𝕜] Lp 𝕜 ∞ μ where
  toFun f := ⟨(T (toL1 ∞ le_top f) : X →ₘ[μ] 𝕜), (hT f).eLpNorm_lt_top⟩
  map_add' f g := Subtype.ext (by simp only [map_add, AddSubgroup.coe_add])
  map_smul' c f := by
    apply Subtype.ext
    change (T (toL1 ∞ le_top (c • f)) : X →ₘ[μ] 𝕜) =
      c • (T (toL1 ∞ le_top f) : X →ₘ[μ] 𝕜)
    rw [map_smul, map_smul]
    rfl

@[simp] theorem toL1_infinityRestriction (T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ)
    (hT : PreservesInfinity T) (f : Lp 𝕜 ∞ μ) :
    toL1 ∞ le_top (infinityRestriction T hT f) = T (toL1 ∞ le_top f) := rfl

/-- Closed graph in L∞ follows by applying the continuous injection into L¹
and uniqueness of limits there. -/
theorem infinityRestriction_continuous (T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ)
    (hT : PreservesInfinity T) : Continuous (infinityRestriction T hT) := by
  apply LinearMap.continuous_of_isClosed_graph
  apply IsSeqClosed.isClosed
  intro z a hz ha
  have hx := (continuous_fst.tendsto a).comp ha
  have hy := (continuous_snd.tendsto a).comp ha
  have hTx := T.continuous.tendsto (toL1 ∞ le_top a.1) |>.comp
    ((toL1Continuous (𝕜 := 𝕜) (μ := μ) ∞ le_top).continuous.tendsto a.1 |>.comp hx)
  have hTy := (toL1Continuous (𝕜 := 𝕜) (μ := μ) ∞ le_top).continuous.tendsto a.2
    |>.comp hy
  have heq : (fun n => toL1 ∞ le_top (z n).2) =
      (fun n => T (toL1 ∞ le_top (z n).1)) := by
    funext n
    rw [show (z n).2 = infinityRestriction T hT (z n).1 from hz n]
    rfl
  change Tendsto (fun n => toL1 ∞ le_top (z n).2) atTop (𝓝 (toL1 ∞ le_top a.2)) at hTy
  rw [heq] at hTy
  exact toL1_injective ∞ le_top ((tendsto_nhds_unique hTy hTx).trans
    (toL1_infinityRestriction T hT a.1).symm)

/-- Automatic endpoint boundedness for both real and complex scalars. -/
theorem endpoint_bounded : EndpointBounded.{u} := by
  intro X _ μ _ 𝕜 _ T hT
  refine ⟨⟨infinityRestriction T hT, infinityRestriction_continuous T hT⟩, ?_⟩
  exact toL1_infinityRestriction T hT


open ExpandedFA.Interpolation.RieszThorinSpec

/-- On a finite measure space the endpoint sum embeds in L¹ with unchanged
underlying a.e. classes. -/
def sumToL1 : SumSpace μ 1 ∞ →ₗ[ℂ] Lp ℂ 1 μ where
  toFun f := ⟨f.val, (show SumSpace μ 1 ∞ ≤ Lp.LpSubmodule ℂ ℂ 1 μ from
    sup_le le_rfl (by
      intro g hg
      exact ((Lp.memLp (⟨g, hg⟩ : Lp ℂ ∞ μ)).mono_exponent le_top).eLpNorm_lt_top)) f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original L¹ operator, viewed on the Riesz–Thorin common domain. -/
def commonOperator (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) :
    SumSpace μ 1 ∞ →ₗ[ℂ] (X →ₘ[μ] ℂ) where
  toFun f := T (sumToL1 f)
  map_add' _ _ := by simp only [map_add, AddSubgroup.coe_add]
  map_smul' c f := by
    change (T (sumToL1 (c • f)) : X →ₘ[μ] ℂ) =
      c • (T (sumToL1 f) : X →ₘ[μ] ℂ)
    rw [map_smul, map_smul]
    rfl

/-- The sharp endpoint bounds belong to the same original operator. -/
theorem commonOperator_one_bound (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) :
    EndpointBound (commonOperator T) 1 1 ‖T‖ := by
  intro f _hf
  let g := sumToL1 f
  refine ⟨Lp.memLp (T g), ?_⟩
  change eLpNorm (T g) 1 μ ≤ ENNReal.ofReal ‖T‖ * eLpNorm g 1 μ
  have h := ENNReal.ofReal_le_ofReal (T.le_opNorm g)
  simpa only [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, Lp.enorm_def] using h

theorem commonOperator_infinity_bound (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ)
    (S : Lp ℂ ∞ μ →L[ℂ] Lp ℂ ∞ μ)
    (hS : ∀ f, toL1 ∞ le_top (S f) = T (toL1 ∞ le_top f)) :
    EndpointBound (commonOperator T) ∞ ∞ ‖S‖ := by
  intro f hf
  let g : Lp ℂ ∞ μ := ⟨f, hf.eLpNorm_lt_top⟩
  have heq : commonOperator T f = (S g : X →ₘ[μ] ℂ) :=
    congrArg (fun z : Lp ℂ 1 μ => (z : X →ₘ[μ] ℂ)) (hS g).symm
  rw [heq]
  refine ⟨Lp.memLp (S g), ?_⟩
  have h := ENNReal.ofReal_le_ofReal (S.le_opNorm g)
  simpa only [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, Lp.enorm_def] using h

/-- The reciprocal-exponent formula at the endpoints 1 and ∞. -/
theorem interpolates_one_top (p : ℝ≥0∞) (hp : 1 < p) (_hpt : p < ∞) :
    Interpolates 1 ∞ p (1 - 1 / p.toReal) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by simp) hp)
  simp only [Interpolates, inv_one, ENNReal.inv_top, mul_one, mul_zero, add_zero]
  rw [sub_sub_cancel, one_div, ← ENNReal.toReal_inv,
    ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hp0)]

/-- Membership and the sharp estimate for T itself on an intermediate Lp. -/
theorem complex_image_bound (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ)
    (S : Lp ℂ ∞ μ →L[ℂ] Lp ℂ ∞ μ)
    (hS : ∀ f, toL1 ∞ le_top (S f) = T (toL1 ∞ le_top f))
    (p : ℝ≥0∞) (hp : 1 < p) (hpt : p < ∞) [Fact (1 ≤ p)]
    (f : Lp ℂ p μ) :
    MemLp (T (toL1 p hp.le f)) p μ ∧
      (eLpNorm (T (toL1 p hp.le f)) p μ).toReal ≤
        ‖T‖ ^ (1 / p.toReal) * ‖S‖ ^ (1 - 1 / p.toReal) * ‖f‖ := by
  have hpr : 1 < p.toReal := by
    exact (ENNReal.toReal_lt_toReal (by simp) hpt.ne).2 hp
  have hθ₀ : 0 < 1 - 1 / p.toReal := by
    have hi := (div_lt_one (by linarith : 0 < p.toReal)).2 hpr
    linarith
  have hθ₁ : 1 - 1 / p.toReal < 1 := by
    have hi : 0 < 1 / p.toReal := by positivity
    linarith
  obtain ⟨hf, hmem, hbound⟩ := ExpandedFA.Interpolation.riesz_thorin μ μ
    1 ∞ 1 ∞ p p (1 - 1 / p.toReal) ‖T‖ ‖S‖ hθ₀ hθ₁
    (norm_nonneg _) (norm_nonneg _) (interpolates_one_top p hp hpt)
    (interpolates_one_top p hp hpt) (commonOperator T)
    (commonOperator_one_bound T) (commonOperator_infinity_bound T S hS) f
  have heq : commonOperator T ⟨f, hf⟩ =
      (T (toL1 p hp.le f) : X →ₘ[μ] ℂ) := rfl
  rw [heq] at hmem hbound
  exact ⟨hmem, by simpa only [sub_sub_cancel] using hbound⟩

/-- The complex case, with the original T on every intermediate Lp. -/
theorem complex_interpolation : ComplexInterpolation.{u} := by
  intro X _ μ _ T hT
  obtain ⟨S, hS⟩ := endpoint_bounded μ ℂ T hT
  refine ⟨S, hS, ?_⟩
  intro p hp hpt _
  let U : Lp ℂ p μ →ₗ[ℂ] Lp ℂ p μ :=
    { toFun := fun f => ⟨(T (toL1 p hp.le f) : X →ₘ[μ] ℂ),
        (complex_image_bound T S hS p hp hpt f).1.eLpNorm_lt_top⟩
      map_add' := fun f g => Subtype.ext (by simp only [map_add, AddSubgroup.coe_add])
      map_smul' := fun c f => by
        apply Subtype.ext
        change (T (toL1 p hp.le (c • f)) : X →ₘ[μ] ℂ) =
          c • (T (toL1 p hp.le f) : X →ₘ[μ] ℂ)
        rw [map_smul, map_smul]
        rfl }
  let C := ‖T‖ ^ (1 / p.toReal) * ‖S‖ ^ (1 - 1 / p.toReal)
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _)
  have hU : ∀ f, ‖U f‖ ≤ C * ‖f‖ := fun f =>
    (complex_image_bound T S hS p hp hpt f).2
  refine ⟨U.mkContinuous C hU, (fun f => rfl), ?_⟩
  exact ContinuousLinearMap.opNorm_le_bound _ hC hU


omit [IsFiniteMeasure μ] in
/-- Pointwise real inclusion preserves every Lp norm. -/
theorem norm_ofReal_compLp (p : ℝ≥0∞) (f : Lp ℝ p μ) :
    ‖Complex.ofRealCLM.compLp f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx
  rw [hx]
  exact Complex.norm_real (f x)

omit [IsFiniteMeasure μ] in
/-- Lp is the complex span of its real-valued functions. -/
theorem complex_lp_decomposition (p : ℝ≥0∞) (f : Lp ℂ p μ) :
    Complex.ofRealCLM.compLp (Complex.reCLM.compLp f) +
      Complex.I • Complex.ofRealCLM.compLp (Complex.imCLM.compLp f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (Complex.ofRealCLM.compLp (Complex.reCLM.compLp f))
      (Complex.I • Complex.ofRealCLM.compLp (Complex.imCLM.compLp f)),
    Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLp (Complex.imCLM.compLp f)),
    Complex.ofRealCLM.coeFn_compLp (Complex.reCLM.compLp f),
    Complex.ofRealCLM.coeFn_compLp (Complex.imCLM.compLp f),
    Complex.reCLM.coeFn_compLp f, Complex.imCLM.coeFn_compLp f] with x ha hs hr hi hfr hfi
  simp only [ha, hs, Pi.add_apply, Pi.smul_apply, hr, hi, hfr, hfi,
    Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  rw [mul_comm Complex.I]
  exact Complex.re_add_im (f x)

/-- Independently complexified endpoints still restrict the same original
operator. Agreement on real classes determines agreement on complex classes. -/
theorem complexifications_compatible
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (S : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ)
    (hS : ∀ f, toL1 ∞ le_top (S f) = T (toL1 ∞ le_top f))
    (C : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (D : Lp ℂ ∞ μ →L[ℂ] Lp ℂ ∞ μ)
    (hC : ∀ f, C (Complex.ofRealCLM.compLp f) = Complex.ofRealCLM.compLp (T f))
    (hD : ∀ f, D (Complex.ofRealCLM.compLp f) = Complex.ofRealCLM.compLp (S f)) :
    ∀ f, toL1 ∞ le_top (D f) = C (toL1 ∞ le_top f) := by
  have hreal : ∀ g : Lp ℝ ∞ μ,
      toL1 ∞ le_top (D (Complex.ofRealCLM.compLp g)) =
        C (toL1 ∞ le_top (Complex.ofRealCLM.compLp g)) := by
    intro g
    rw [hD]
    change Complex.ofRealCLM.compLp (toL1 ∞ le_top (S g)) =
      C (Complex.ofRealCLM.compLp (toL1 ∞ le_top g))
    rw [hS, hC]
  intro f
  conv_lhs => rw [← complex_lp_decomposition ∞ f]
  rw [map_add, map_smul, map_add, map_smul, hreal, hreal]
  rw [← map_smul C, ← map_add C]
  congr 1
  rw [← map_smul, ← map_add, complex_lp_decomposition]

/-- Complete real assembly once the independent, norm-preserving endpoint
complexifications have been constructed. No loss of constant is introduced. -/
theorem real_interpolation_of_complexification :
    RealInterpolationFromComplexification.{u} := by
  intro hOne hTop X _ μ _ T hT
  obtain ⟨S, hS⟩ := endpoint_bounded μ ℝ T hT
  obtain ⟨C, hCn, hC⟩ := hOne μ T
  obtain ⟨D, hDn, hD⟩ := hTop μ S
  have hCD := complexifications_compatible T S hS C D hC hD
  refine ⟨S, hS, ?_⟩
  intro p hp hpt _
  have hbound (f : Lp ℝ p μ) :
      MemLp (T (toL1 p hp.le f)) p μ ∧
        (eLpNorm (T (toL1 p hp.le f)) p μ).toReal ≤
          ‖T‖ ^ (1 / p.toReal) * ‖S‖ ^ (1 - 1 / p.toReal) * ‖f‖ := by
    have h := complex_image_bound C D hCD p hp hpt (Complex.ofRealCLM.compLp f)
    have hinc : toL1 p hp.le (Complex.ofRealCLM.compLp f) =
        Complex.ofRealCLM.compLp (toL1 p hp.le f) := rfl
    rw [hinc, hC] at h
    have heq : eLpNorm (Complex.ofRealCLM.compLp (T (toL1 p hp.le f))) p μ =
        eLpNorm (T (toL1 p hp.le f)) p μ := by
      apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      filter_upwards [Complex.ofRealCLM.coeFn_compLp (T (toL1 p hp.le f))] with x hx
      rw [hx]
      exact Complex.norm_real _
    have hmem : MemLp (T (toL1 p hp.le f)) p μ := by
      change eLpNorm (T (toL1 p hp.le f)) p μ < ∞
      rw [← heq]
      exact h.1.eLpNorm_lt_top
    refine ⟨hmem, ?_⟩
    simpa only [heq, hCn, hDn, norm_ofReal_compLp] using h.2
  let U : Lp ℝ p μ →ₗ[ℝ] Lp ℝ p μ :=
    { toFun := fun f => ⟨(T (toL1 p hp.le f) : X →ₘ[μ] ℝ),
        (hbound f).1.eLpNorm_lt_top⟩
      map_add' := fun f g => Subtype.ext (by simp only [map_add, AddSubgroup.coe_add])
      map_smul' := fun c f => by
        apply Subtype.ext
        change (T (toL1 p hp.le (c • f)) : X →ₘ[μ] ℝ) =
          c • (T (toL1 p hp.le f) : X →ₘ[μ] ℝ)
        rw [map_smul, map_smul]
        rfl }
  let K := ‖T‖ ^ (1 / p.toReal) * ‖S‖ ^ (1 - 1 / p.toReal)
  have hK : 0 ≤ K := mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _)
  have hU : ∀ f, ‖U f‖ ≤ K * ‖f‖ := fun f => (hbound f).2
  refine ⟨U.mkContinuous K hU, (fun f => rfl), ?_⟩
  exact ContinuousLinearMap.opNorm_le_bound _ hK hU

section Complexification
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

private abbrev realInclusion : Lp ℝ p μ →L[ℝ] Lp ℂ p μ :=
  Complex.ofRealCLM.compLpL p μ
private abbrev realPart : Lp ℂ p μ →L[ℝ] Lp ℝ p μ :=
  Complex.reCLM.compLpL p μ
private abbrev imagPart : Lp ℂ p μ →L[ℝ] Lp ℝ p μ :=
  Complex.imCLM.compLpL p μ

omit [IsFiniteMeasure μ] in
private theorem realPart_I (f : Lp ℂ p μ) :
    realPart p (Complex.I • f) = -imagPart p f := by
  change Complex.reCLM.compLp (Complex.I • f) = -Complex.imCLM.compLp f
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLp (Complex.I • f), Lp.coeFn_smul Complex.I f,
    Lp.coeFn_neg (Complex.imCLM.compLp f), Complex.imCLM.coeFn_compLp f] with x hr hs hn hi
  rw [hn, hr, hs]
  simp only [Pi.neg_apply, Pi.smul_apply]
  rw [hi]
  simp [Complex.mul_re]

omit [IsFiniteMeasure μ] in
private theorem imagPart_I (f : Lp ℂ p μ) :
    imagPart p (Complex.I • f) = realPart p f := by
  change Complex.imCLM.compLp (Complex.I • f) = Complex.reCLM.compLp f
  apply Lp.ext
  filter_upwards [Complex.imCLM.coeFn_compLp (Complex.I • f), Lp.coeFn_smul Complex.I f,
    Complex.reCLM.coeFn_compLp f] with x hi hs hr
  simp [hi, hs, hr, Complex.mul_im]

omit [IsFiniteMeasure μ] in
private theorem realPart_inclusion (f : Lp ℝ p μ) :
    realPart p (realInclusion p f) = f := by
  change Complex.reCLM.compLp (Complex.ofRealCLM.compLp f) = f
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLp (Complex.ofRealCLM.compLp f),
    Complex.ofRealCLM.coeFn_compLp f] with x hr hj
  simp [hr, hj]

omit [IsFiniteMeasure μ] in
private theorem imagPart_inclusion (f : Lp ℝ p μ) :
    imagPart p (realInclusion p f) = 0 := by
  change Complex.imCLM.compLp (Complex.ofRealCLM.compLp f) = 0
  apply Lp.ext
  filter_upwards [Complex.imCLM.coeFn_compLp (Complex.ofRealCLM.compLp f),
    Complex.ofRealCLM.coeFn_compLp f, Lp.coeFn_zero ℝ p μ] with x hi hj hz
  rw [hz, hi, hj]
  simp

/-- The canonical extension defined using real and imaginary parts. -/
def complexify (T : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) : Lp ℂ p μ →L[ℂ] Lp ℂ p μ := by
  let F : Lp ℂ p μ →L[ℝ] Lp ℂ p μ :=
    ((realInclusion p).comp T).comp (realPart p) +
      Complex.I • ((realInclusion p).comp T).comp (imagPart p)
  have hI (f : Lp ℂ p μ) : F (Complex.I • f) = Complex.I • F f := by
    simp only [F, add_apply, ContinuousLinearMap.comp_apply,
      smul_apply, realPart_I, imagPart_I, map_neg, smul_add, smul_smul]
    simp [Complex.I_mul_I, add_comm]
  exact
    { toLinearMap :=
        { toFun := F
          map_add' := F.map_add
          map_smul' := fun c f => by
            calc
              F (c • f) = F (c.re • f + c.im • (Complex.I • f)) := by
                congr 1
                rw [← IsScalarTower.algebraMap_smul ℂ c.re,
                  ← IsScalarTower.algebraMap_smul ℂ c.im, smul_smul,
                  ← add_smul]
                simp only [Complex.coe_algebraMap, Complex.re_add_im]
              _ = c.re • F f + c.im • (Complex.I • F f) := by
                rw [map_add, map_smul, map_smul, hI]
              _ = c • F f := by
                rw [← IsScalarTower.algebraMap_smul ℂ c.re,
                  ← IsScalarTower.algebraMap_smul ℂ c.im, smul_smul,
                  ← add_smul]
                simp only [Complex.coe_algebraMap, Complex.re_add_im] }
      cont := F.continuous }

@[simp] theorem complexify_apply (T : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (f : Lp ℂ p μ) :
    complexify p T f = realInclusion p (T (realPart p f)) +
      Complex.I • realInclusion p (T (imagPart p f)) := rfl

@[simp] theorem complexify_inclusion (T : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (f : Lp ℝ p μ) :
    complexify p T (Complex.ofRealCLM.compLp f) = Complex.ofRealCLM.compLp (T f) := by
  change complexify p T (realInclusion p f) = realInclusion p (T f)
  simp [realPart_inclusion, imagPart_inclusion]

/-- Restriction to the real isometric copy gives the reverse norm inequality. -/
theorem norm_le_complexify (T : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) : ‖T‖ ≤ ‖complexify p T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  have h := (complexify p T).le_opNorm (Complex.ofRealCLM.compLp f)
  simpa only [complexify_inclusion, norm_ofReal_compLp] using h

/-- Real part commutes with the canonical extension. -/
theorem realPart_complexify (T : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (f : Lp ℂ p μ) :
    realPart p (complexify p T f) = T (realPart p f) := by
  rw [complexify_apply, map_add, realPart_inclusion, realPart_I, imagPart_inclusion]
  simp

omit [IsFiniteMeasure μ] in
private theorem norm_realPart_le (f : Lp ℂ p μ) : ‖realPart p f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Complex.reCLM.coeFn_compLp f] with x hx
  change ‖(Complex.reCLM.compLp f) x‖ ≤ ‖f x‖
  rw [hx]
  exact Complex.abs_re_le_norm _

end Complexification

omit [IsFiniteMeasure μ] in
/-- An L∞ class is a.e. bounded by its norm, also for the zero measure. -/
theorem ae_norm_le_top {E : Type*} [NormedAddCommGroup E] (f : Lp E ∞ μ) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  have h := ae_le_eLpNormEssSup (f := (f : X → E)) (μ := μ)
  have hfin : eLpNormEssSup (f : X → E) μ ≠ ∞ := by
    rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
    exact Lp.eLpNorm_ne_top f
  filter_upwards [h] with x hx
  have hreal := ENNReal.toReal_mono hfin hx
  simpa only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, Lp.norm_def,
    eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] using hreal

/-- Countably many real projections norm a complex L∞ function. -/
theorem norm_top_le_of_real_projections (g : Lp ℂ ∞ μ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ c : ℂ, ‖realPart ∞ (c • g)‖ ≤ ‖c‖ * K) : ‖g‖ ≤ K := by
  obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable s := hs.to_subtype
  have hall : ∀ᵐ x ∂μ, ∀ c : s, |((c : ℂ) * g x).re| ≤ ‖(c : ℂ)‖ * K := by
    apply ae_all_iff.mpr
    intro c
    filter_upwards [ae_norm_le_top (realPart ∞ ((c : ℂ) • g)),
      Complex.reCLM.coeFn_compLp ((c : ℂ) • g), Lp.coeFn_smul (c : ℂ) g] with x hb hr hs
    change ‖(Complex.reCLM.compLp ((c : ℂ) • g)) x‖ ≤ _ at hb
    rw [hr, hs] at hb
    exact hb.trans (h c)
  have hb : ∀ᵐ x ∂μ, ‖g x‖ ≤ K := by
    filter_upwards [hall] with x hx
    have hclosed : IsClosed {c : ℂ | |(c * g x).re| ≤ ‖c‖ * K} :=
      isClosed_le ((Complex.continuous_re.comp (continuous_id.mul continuous_const)).abs)
        (continuous_norm.mul continuous_const)
    have hh : ∀ c : ℂ, |(c * g x).re| ≤ ‖c‖ * K := fun c =>
      hd.denseRange_val.induction_on c hclosed hx
    have hc := hh (starRingEnd ℂ (g x))
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
      abs_of_nonneg (sq_nonneg _), Complex.norm_conj] at hc
    nlinarith [norm_nonneg (g x)]
  simpa only [ENNReal.toReal_top, inv_zero, Real.rpow_zero, one_mul] using
    (Lp.norm_le_of_ae_bound hK hb)

/-- The canonical complexification preserves the L∞ operator norm. -/
theorem norm_complexify_top (T : Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ) :
    ‖complexify ∞ T‖ = ‖T‖ := by
  apply le_antisymm _ (norm_le_complexify ∞ T)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  apply norm_top_le_of_real_projections _ _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro c
  rw [← map_smul, realPart_complexify]
  calc
    ‖T (realPart ∞ (c • f))‖ ≤ ‖T‖ * ‖realPart ∞ (c • f)‖ := T.le_opNorm _
    _ ≤ ‖T‖ * ‖c • f‖ := mul_le_mul_of_nonneg_left (norm_realPart_le ∞ _) (norm_nonneg _)
    _ = ‖c‖ * (‖T‖ * ‖f‖) := by rw [norm_smul]; ring

/-- Norm-preserving complexification at the upper endpoint. -/
theorem complexification_top : ComplexificationAt.{u} ∞ := by
  intro X _ μ _ T
  exact ⟨complexify ∞ T, norm_complexify_top T, complexify_inclusion ∞ T⟩


omit [IsFiniteMeasure μ] in
/-- Indicators with complex coefficients are scalar multiples of real indicators. -/
theorem indicator_complex_smul_real (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℂ) :
    indicatorConstLp p hs hμs c =
      c • Complex.ofRealCLM.compLp (indicatorConstLp p hs hμs (1 : ℝ)) := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := p) (c := c) (hs := hs) (hμs := hμs),
    Lp.coeFn_smul c (Complex.ofRealCLM.compLp (indicatorConstLp p hs hμs (1 : ℝ))),
    Complex.ofRealCLM.coeFn_compLp (indicatorConstLp p hs hμs (1 : ℝ)),
    indicatorConstLp_coeFn (p := p) (c := (1 : ℝ)) (hs := hs) (hμs := hμs)] with x hc hsm hj hr
  rw [hc, hsm]
  simp only [Pi.smul_apply]
  rw [hj, hr]
  by_cases hx : x ∈ s <;> simp [hx]

omit [IsFiniteMeasure μ] in
/-- On disjoint supports the L¹ norm is additive. -/
theorem norm_toLp_add_disjoint {f g : X → ℂ} (hf : MemLp f 1 μ) (hg : MemLp g 1 μ)
    (hd : Disjoint (Function.support f) (Function.support g)) :
    ‖hf.toLp f + hg.toLp g‖ = ‖hf.toLp f‖ + ‖hg.toLp g‖ := by
  have hfi : Integrable f μ := memLp_one_iff_integrable.mp hf
  have hgi : Integrable g μ := memLp_one_iff_integrable.mp hg
  have hpoint : ∀ x, ‖f x + g x‖ = ‖f x‖ + ‖g x‖ := by
    intro x
    by_cases hfx : f x = 0
    · simp [hfx]
    · have hgx : g x = 0 := by
        by_contra hgx
        exact Set.disjoint_left.mp hd hfx hgx
      simp [hgx]
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  have heq : ∀ᵐ x ∂μ, ‖(hf.toLp f + hg.toLp g) x‖ = ‖(hf.toLp f) x‖ + ‖(hg.toLp g) x‖ := by
    filter_upwards [Lp.coeFn_add (hf.toLp f) (hg.toLp g), hf.coeFn_toLp,
      hg.coeFn_toLp] with x ha hfx hgx
    rw [ha]
    simpa only [Pi.add_apply, hfx, hgx] using hpoint x
  rw [integral_congr_ae heq]
  exact integral_add
    ((memLp_one_iff_integrable.mp (Lp.memLp (hf.toLp f))).norm)
    ((memLp_one_iff_integrable.mp (Lp.memLp (hg.toLp g))).norm)

/-- The sharp L¹ bound first holds for indicators, then disjoint simple sums,
and finally all L¹ functions by density and continuity. -/
theorem complexify_one_bound (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (f : Lp ℂ 1 μ) :
    ‖complexify 1 T f‖ ≤ ‖T‖ * ‖f‖ := by
  apply Lp.induction (p := 1) (by simp)
    (fun f : Lp ℂ 1 μ => ‖complexify 1 T f‖ ≤ ‖T‖ * ‖f‖) _ _ _ f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    rw [indicator_complex_smul_real 1 hs hμs.ne c, map_smul, complexify_inclusion,
      norm_smul, norm_ofReal_compLp, norm_smul, norm_ofReal_compLp]
    calc
      ‖c‖ * ‖T (indicatorConstLp 1 hs hμs.ne (1 : ℝ))‖ ≤
          ‖c‖ * (‖T‖ * ‖indicatorConstLp 1 hs hμs.ne (1 : ℝ)‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  · intro f g hf hg hd hfb hgb
    rw [map_add]
    calc
      ‖complexify 1 T (hf.toLp f) + complexify 1 T (hg.toLp g)‖ ≤
          ‖complexify 1 T (hf.toLp f)‖ + ‖complexify 1 T (hg.toLp g)‖ := norm_add_le _ _
      _ ≤ ‖T‖ * ‖hf.toLp f‖ + ‖T‖ * ‖hg.toLp g‖ := add_le_add hfb hgb
      _ = ‖T‖ * ‖hf.toLp f + hg.toLp g‖ := by rw [norm_toLp_add_disjoint hf hg hd, mul_add]
  · exact isClosed_le (complexify 1 T).continuous.norm (continuous_const.mul continuous_norm)

/-- The exact lower endpoint operator norm is preserved. -/
theorem norm_complexify_one (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) :
    ‖complexify 1 T‖ = ‖T‖ :=
  le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (complexify_one_bound T))
    (norm_le_complexify 1 T)

/-- Norm-preserving complexification at the lower endpoint. -/
theorem complexification_one : ComplexificationAt.{u} 1 := by
  intro X _ μ _ T
  exact ⟨complexify 1 T, norm_complexify_one T, complexify_inclusion 1 T⟩

/-- The full endpoint-invariance bridge for both scalar fields. -/
theorem endpoint_interpolation : EndpointInterpolation.{u} :=
  ⟨complex_interpolation,
    real_interpolation_of_complexification complexification_one complexification_top⟩

end ExpandedFA.BanachGeometry.EndpointInterpolation
