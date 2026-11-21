import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.RealHolderSpectralBridge
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.IntegralOperators.HolderTraceClass
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.RealComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.RealExteriorDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.ClassicalLogDerivative
import Mathlib.Tactic.Module

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal InnerProductSpace
universe u v
namespace ExpandedFA.IntegralOperators.RealHolderSpectralBridge
open HolderTraceClass.Spec
open TraceIdeals.TraceClassDefinitions.Spec TraceIdeals.Lidskii.Spec
open Hilbert.PreHilbertCompactSpectral.Spec.Complexification

section L2Geometry
variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

/-- The actual real-valued L² inclusion, applied to a.e. classes. -/
def ofRealL2 : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ := Complex.ofRealCLM.compLpL 2 μ

lemma ofRealL2_ae (f : Lp ℝ 2 μ) :
    (ofRealL2 μ f : X → ℂ) =ᵐ[μ] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

/-- Synthesis of real and imaginary a.e. classes. -/
def synthesis (p : TraceIdeals.RealComplexification.Space (Lp ℝ 2 μ)) : Lp ℂ 2 μ :=
  ofRealL2 μ p.1 + Complex.I • ofRealL2 μ p.2

lemma synthesis_ae (p : TraceIdeals.RealComplexification.Space (Lp ℝ 2 μ)) :
    (synthesis μ p : X → ℂ) =ᵐ[μ] fun x => (p.1 x : ℂ) + Complex.I * (p.2 x : ℂ) := by
  filter_upwards [Lp.coeFn_add (ofRealL2 μ p.1) (Complex.I • ofRealL2 μ p.2),
    Lp.coeFn_smul Complex.I (ofRealL2 μ p.2), ofRealL2_ae μ p.1, ofRealL2_ae μ p.2]
    with x ha hs hr hi
  simp only [synthesis, ha, hs, hr, hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

def synthesisLinear : TraceIdeals.RealComplexification.Space (Lp ℝ 2 μ) →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := synthesis μ
  map_add' p q := by
    change ofRealL2 μ (p.1 + q.1) + Complex.I • ofRealL2 μ (p.2 + q.2) = _
    simp only [map_add, synthesis, smul_add]
    abel
  map_smul' a p := by
    rw [csmul]
    change ofRealL2 μ (a.re • p.1 - a.im • p.2) +
      Complex.I • ofRealL2 μ (a.im • p.1 + a.re • p.2) = _
    simp only [map_sub, map_add, map_smul, synthesis, smul_add,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    have ha : a = (a.re : ℂ) + Complex.I * (a.im : ℂ) := by
      simpa only [mul_comm] using (Complex.re_add_im a).symm
    conv_rhs => rw [ha]
    match_scalars <;> simp only [id_eq] <;> ring_nf <;> simp [Complex.I_sq, add_comm]

lemma lp_norm_sq {𝕜 : Type} [RCLike 𝕜] (f : Lp 𝕜 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  simpa only [Lp.toLp_coeFn] using
    (PartV.L2Kernel.integral_sq_norm (f : X → 𝕜) (Lp.memLp f)).symm

lemma synthesis_norm (p : TraceIdeals.RealComplexification.Space (Lp ℝ 2 μ)) :
    ‖synthesis μ p‖ = ‖p‖ := by
  have hn : ‖synthesis μ p‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
    rw [lp_norm_sq]
    have he : (fun x => ‖synthesis μ p x‖ ^ 2) =ᵐ[μ]
        fun x => ‖p.1 x‖ ^ 2 + ‖p.2 x‖ ^ 2 := by
      filter_upwards [synthesis_ae μ p] with x hx
      rw [hx, ← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply, Real.norm_eq_abs, sq_abs]
      ring
    rw [integral_congr_ae he, integral_add, ← lp_norm_sq, ← lp_norm_sq]
    · exact (memLp_two_iff_integrable_sq_norm (Lp.memLp p.1).aestronglyMeasurable).mp (Lp.memLp p.1)
    · exact (memLp_two_iff_integrable_sq_norm (Lp.memLp p.2).aestronglyMeasurable).mp (Lp.memLp p.2)
  have hp := TraceIdeals.RealComplexification.Spec.norm_sq p
  nlinarith [norm_nonneg (synthesis μ p), norm_nonneg p]

/-- Unitary identification with genuine complex-valued L². -/
def l2Unitary : TraceIdeals.RealComplexification.Space (Lp ℝ 2 μ) ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := synthesisLinear μ, norm_map' := synthesis_norm μ }
    (by
      intro f
      let r := Complex.reCLM.compLpL 2 μ f
      let i := Complex.imCLM.compLpL 2 μ f
      refine ⟨complexPair (Lp ℝ 2 μ) r i, ?_⟩
      apply Lp.ext
      filter_upwards [synthesis_ae μ (complexPair (Lp ℝ 2 μ) r i),
        Complex.reCLM.coeFn_compLpL f, Complex.imCLM.coeFn_compLpL f] with x hx hr hi
      change synthesis μ _ x = f x
      rw [hx]
      change (r x : ℂ) + Complex.I * (i x : ℂ) = f x
      rw [hr, hi]
      simpa only [Complex.reCLM_apply, Complex.imCLM_apply, mul_comm] using Complex.re_add_im (f x))

lemma l2Unitary_ae (p : TraceIdeals.RealComplexification.Space (Lp ℝ 2 μ)) :
    (l2Unitary μ p : X → ℂ) =ᵐ[μ] fun x => (p.1 x : ℂ) + Complex.I * (p.2 x : ℂ) :=
  synthesis_ae μ p

end L2Geometry

lemma l2Unitary_intertwines (a b : ℝ)
    (k : C(Interval a b × Interval a b, ℝ))
    (p : TraceIdeals.RealComplexification.Space (Lp ℝ 2 (intervalMeasure a b))) :
    l2Unitary (intervalMeasure a b)
        (TraceIdeals.RealComplexification.Spec.operator (Spec.realOperator k) p) =
      Spec.complexOperator k (l2Unitary (intervalMeasure a b) p) := by
  change ofRealL2 _ (Spec.realOperator k p.1) +
    Complex.I • ofRealL2 _ (Spec.realOperator k p.2) =
      Spec.complexOperator k (ofRealL2 _ p.1 + Complex.I • ofRealL2 _ p.2)
  rw [map_add, map_smul]
  congr 1
  · exact Mercer.ofRealL2_kernel (intervalMeasure a b) k p.1
  · exact congrArg (fun f => Complex.I • f)
      (Mercer.ofRealL2_kernel (intervalMeasure a b) k p.2)

theorem l2_complexification : Spec.L2Complexification := by
  intro a b
  exact ⟨l2Unitary (intervalMeasure a b), l2Unitary_ae _, l2Unitary_intertwines a b⟩

/-- Trace class and trace norm use the canonical complexification first, then
unitary transport; the trace comparison uses scalar extension of the real trace. -/
theorem trace_transport : Spec.TraceTransport := by
  intro a b k hk
  let := TraceIdeals.RealComplexification.Spec.completeSpace
    (H := Lp ℝ 2 (intervalMeasure a b))
  let T := TraceIdeals.RealComplexification.Spec.operator (Spec.realOperator k)
  let U := l2Unitary (intervalMeasure a b)
  have ht : IsTraceClassValue T :=
    (TraceIdeals.RealComplexification.trace_ideal _ _ (Spec.realOperator k)).1.mp hk
  have hn := HolderTraceClass.unitary_traceClass_iff_norm U T (Spec.complexOperator k)
    (l2Unitary_intertwines a b k)
  have hc : IsTraceClassValue (Spec.complexOperator k) := hn.1.mpr ht
  have htrace := ContinuousTraceDiagonal.trace_of_unitary_intertwining U T
    (Spec.complexOperator k) ht (by
      apply ContinuousLinearMap.ext
      intro p
      exact l2Unitary_intertwines a b k p)
  refine ⟨hc, ?_, ?_⟩
  · exact (hn.2 hc).trans ((TraceIdeals.RealComplexification.trace_ideal _ _
      (Spec.realOperator k)).2 hk)
  · exact htrace.2.symm.trans (TraceIdeals.RealComplexification.trace _ _ hk)

section DeterminantTransport
variable {H : Type u} {K : Type v} [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace ℂ H] [InnerProductSpace ℂ K] [CompleteSpace H] [CompleteSpace K]

/-- Transport a Hilbert basis with an actual unitary, preserving its index. -/
def transportedBasis {ι : Type*} (U : H ≃ₗᵢ[ℂ] K) (b : HilbertBasis ι ℂ H) :
    HilbertBasis ι ℂ K := ⟨U.symm.trans b.repr⟩

omit [CompleteSpace H] [CompleteSpace K] in
lemma transportedBasis_apply {ι : Type*} (U : H ≃ₗᵢ[ℂ] K) (b : HilbertBasis ι ℂ H)
    (i : ι) : transportedBasis U b i = U (b i) := by
  classical
  change (U.symm.trans b.repr).symm (lp.single 2 i (1 : ℂ)) = _
  simp only [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.trans_apply, HilbertBasis.repr_symm_single]

lemma determinant_unitary (U : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) (R : K →L[ℂ] K)
    (hT : IsTraceClassValue T) (h : ∀ p, U (T p) = R (U p)) (z : ℂ) :
    FredholmDeterminant.TraceClassDefinitions.Spec.FredholmDeterminantValue T z =
      FredholmDeterminant.TraceClassDefinitions.Spec.FredholmDeterminantValue R z := by
  classical
  have hR := (HolderTraceClass.unitary_traceClass_iff_norm U T R h).1.mpr hT
  have he (n : ℕ) :
      FredholmDeterminant.TraceClassDefinitions.Spec.ExteriorTraceValue T n =
        FredholmDeterminant.TraceClassDefinitions.Spec.ExteriorTraceValue R n := by
    let b := TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℂ) (H := H)
    change FredholmDeterminant.TraceClassDefinitions.exteriorTrace T n =
      FredholmDeterminant.TraceClassDefinitions.exteriorTrace R n
    rw [FredholmDeterminant.TraceDeterminantContinuity.exteriorTrace_eq_tsum_principalMinor
        T hT b n,
      FredholmDeterminant.TraceDeterminantContinuity.exteriorTrace_eq_tsum_principalMinor
        R hR (transportedBasis U b) n]
    apply tsum_congr
    intro s
    unfold FredholmDeterminant.TraceClassDefinitions.principalMinor
      FredholmDeterminant.TraceClassDefinitions.Spec.PrincipalMinorValue
    congr 1
    ext i j
    rw [transportedBasis_apply, transportedBasis_apply, ← h, U.inner_map_map]
  unfold FredholmDeterminant.TraceClassDefinitions.Spec.FredholmDeterminantValue
  apply tsum_congr
  intro n
  rw [he]

end DeterminantTransport

lemma determinant_comparison (a b : ℝ)
    (k : C(Interval a b × Interval a b, ℝ))
    (hk : IsTraceClassValue (Spec.realOperator k)) (z : ℂ) :
    FredholmDeterminant.ClassicalDefinitions.Spec.FredholmDeterminantValue
        (intervalMeasure a b) (Spec.complexKernel k) z =
      FredholmDeterminant.RealExteriorDefinitions.Spec.ComplexParameterDeterminantValue
        (Spec.realOperator k) (-z) := by
  let := TraceIdeals.RealComplexification.Spec.completeSpace
    (H := Lp ℝ 2 (intervalMeasure a b))
  have hc := (trace_transport a b k hk).1
  rw [FredholmDeterminant.ClassicalLogDerivative.trace_determinant_comparison _ _ hc]
  have ht := (TraceIdeals.RealComplexification.trace_ideal _ _ (Spec.realOperator k)).1.mp hk
  exact (determinant_unitary (l2Unitary (intervalMeasure a b))
    (TraceIdeals.RealComplexification.Spec.operator (Spec.realOperator k))
    (Spec.complexOperator k) ht (l2Unitary_intertwines a b k) (-z)).symm.trans
    (FredholmDeterminant.RealExteriorDefinitions.determinant_complexification
      (Spec.realOperator k) hk (-z)).symm

/-- Apply the general complex spectral theorem only after proving the actual
real/complex operator, trace, and determinant identifications. -/
theorem traceClass_spectral : Spec.TraceClassSpectral := by
  intro a b k hk
  have ht := trace_transport a b k hk
  obtain ⟨hd, ha, hs, hp, hu⟩ := HolderTraceClass.traceClass_spectral
    (intervalMeasure a b) (Spec.complexKernel k) ht.1
  have hd' : TraceValue (Spec.complexOperator k) =
      ((∫ t, k (t,t) ∂(intervalMeasure a b) : ℝ) : ℂ) :=
    hd.trans integral_complex_ofReal
  have hr : TraceValue (Spec.realOperator k) = ∫ t, k (t,t) ∂(intervalMeasure a b) :=
    Complex.ofReal_injective (ht.2.2.symm.trans hd')
  refine ⟨hr, hd', ha, ?_, ?_, hu⟩
  · change HasSum _ (∫ t, (k (t,t) : ℂ) ∂(intervalMeasure a b)) at hs
    rw [integral_complex_ofReal] at hs
    exact hs
  · intro z
    exact ⟨determinant_comparison a b k hk z, hp z⟩

theorem firstVariable : Spec.FirstVariable := by
  intro a b hab k α H hα hα' h
  obtain ⟨ht, hb⟩ := HolderTraceClass.scalarIntervalFirstVariable ℝ a b hab k α H hα hα' h
  exact ⟨ht, hb, traceClass_spectral a b k ht⟩

theorem secondVariable : Spec.SecondVariable := by
  intro a b hab k α H hα hα' h
  obtain ⟨ht, hb⟩ := HolderTraceClass.scalarIntervalSecondVariable ℝ a b hab k α H hα hα' h
  exact ⟨ht, hb, traceClass_spectral a b k ht⟩

theorem continuouslyDifferentiable : Spec.ContinuouslyDifferentiable := by
  intro a b hab k f hf hc
  obtain ⟨H, hH, ht, hb⟩ :=
    HolderTraceClass.scalarIntervalContinuouslyDifferentiable ℝ a b hab k f hf hc
  exact ⟨⟨H, hH, hb⟩, ht, traceClass_spectral a b k ht⟩

theorem smooth : Spec.Smooth := by
  intro a b hab k f hf hc
  have ht := HolderTraceClass.scalarIntervalSmooth ℝ a b hab k f hf hc
  exact ⟨ht, traceClass_spectral a b k ht⟩


/-- Zero and empty intervals have no nonzero eigenvalues, so both actual
Fredholm determinants are one and the same sum/product conclusions apply. -/
theorem degenerateInterval : Spec.DegenerateInterval := by
  intro a b hab k
  obtain ⟨hr, ht, hn, htrace, hd⟩ := HolderTraceClass.scalarDegenerateInterval ℝ a b hab k
  have hc := (HolderTraceClass.scalarDegenerateInterval ℂ a b hab (Spec.complexKernel k)).1
  have hempty : IsEmpty (EigenvalueIndex (Spec.complexOperator k)) := by
    constructor
    intro i
    obtain ⟨v, hv⟩ := i.1.property.2.exists_hasEigenvector
    have he : i.1.val • v = 0 := by
      rw [← hv.apply_eq_smul]
      change Spec.complexOperator k v = 0
      change Spec.complexOperator k = 0 at hc
      rw [hc]
      rfl
    exact hv.2 ((smul_eq_zero.mp he).resolve_left i.1.property.1)
  let := hempty
  have hμ := HolderTraceClass.intervalMeasure_eq_zero_of_le a b hab
  have hz : Subsingleton (Lp ℂ 2 (intervalMeasure a b)) := ⟨fun f g => by
    apply Lp.ext
    have hae : ae (intervalMeasure a b) = ⊥ := by rw [hμ]; simp
    rw [hae]
    exact Filter.eventually_bot⟩
  let := hz
  have hspec : spectrum ℂ (Spec.complexOperator k) = ∅ := spectrum.of_subsingleton (R := ℂ) _
  have hs := traceClass_spectral a b k ht
  have hone (z : ℂ) :
      FredholmDeterminant.ClassicalDefinitions.Spec.FredholmDeterminantValue
        (intervalMeasure a b) (Spec.complexKernel k) z = 1 := by
    have hp := (hs.2.2.2.2.1 z).2.2.tprod_eq
    simpa only [tprod_empty] using hp.symm
  refine ⟨hr, hc, hn, htrace, hd, hempty, ?_, ?_, hs⟩
  · rw [hspec]; simp
  · intro z
    refine ⟨hone z, ?_⟩
    have he := determinant_comparison a b k ht (-z)
    simpa only [neg_neg] using he.symm.trans (hone (-z))

end ExpandedFA.IntegralOperators.RealHolderSpectralBridge
