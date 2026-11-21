import MathGenome.Internal.LinearPDE.P201Specs.Common.NormalTrace
import MathGenome.Internal.LinearPDE.P201.Common.ExactTrace
import MathGenome.Internal.LinearPDE.P201.Common.InteriorTesting
import MathGenome.Internal.LinearPDE.P201.Common.SmoothFlux
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace P201.NormalTrace
open P201Specs.NormalTrace

/-- The bounded bulk functional whose descent is the normal trace. -/
def bulkFunctional {n : ℕ} (Ω : Domain n) (F : VectorL2 Ω) (d : Lp ℝ Ω 2) :
    H ℝ Ω 1 →L[ℝ] ℝ :=
  InteriorTesting.fluxFunctional Ω F +
    (innerSL ℝ d).comp (P201Specs.hUnderlying Ω 1)

lemma bulkFunctional_integral {n : ℕ} (Ω : Domain n) (F : VectorL2 Ω)
    (d : Lp ℝ Ω 2) (v : H ℝ Ω 1) :
    bulkFunctional Ω F d v =
      ∫ x in Ω, inner ℝ (F x) (P201Specs.hGradient v x) + d x * P201Specs.hUnderlying Ω 1 v x := by
  have hi : IntegrableOn (fun x => inner ℝ (F x) (P201Specs.hGradient v x)) Ω volume :=
    L2.integrable_inner F (P201Specs.hGradient v)
  have hd : IntegrableOn (fun x => d x * P201Specs.hUnderlying Ω 1 v x) Ω volume :=
    (Lp.memLp d).integrable_mul (Lp.memLp (P201Specs.hUnderlying Ω 1 v))
  rw [integral_add hi hd]
  simp only [bulkFunctional, add_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    InteriorTesting.fluxFunctional_integral, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp [RCLike.inner_apply, mul_comm]

lemma coordinate_norm_le {n : ℕ} (Ω : Domain n) (F : VectorL2 Ω) (i : Fin n) :
    ‖(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).compLp F‖ ≤ ‖F‖ := by
  have hp : ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa using PiLp.norm_apply_le x i
  exact (ContinuousLinearMap.norm_compLp_le _ F).trans (by
    simpa using mul_le_mul_of_nonneg_right hp (norm_nonneg F))

lemma firstDerivative_norm_le {n : ℕ} (Ω : Domain n) (v : H ℝ Ω 1) (i : Fin n) :
    ‖P201Specs.hFirstDerivative v i‖ ≤ ‖v‖ :=
  PiLp.norm_apply_le v.val (⟨{i}, by simp⟩ : P102.U4.SobolevIndex n 1)

lemma underlying_norm_le {n : ℕ} (Ω : Domain n) (v : H ℝ Ω 1) :
    ‖P201Specs.hUnderlying Ω 1 v‖ ≤ ‖v‖ :=
  PiLp.norm_apply_le v.val (P102.U4.zeroSobolevIndex n 1)

lemma bulkFunctional_bound {n : ℕ} (Ω : Domain n) (F : VectorL2 Ω)
    (d : Lp ℝ Ω 2) (v : H ℝ Ω 1) :
    ‖bulkFunctional Ω F d v‖ ≤ ((n : ℝ) * ‖F‖ + ‖d‖) * ‖v‖ := by
  have hflux : ‖InteriorTesting.fluxFunctional Ω F v‖ ≤ (n : ℝ) * ‖F‖ * ‖v‖ := by
    simp only [InteriorTesting.fluxFunctional, sum_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, InteriorTesting.firstDerivativeMap_apply]
    change ‖∑ i : Fin n, inner ℝ
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).compLp F)
      (P201Specs.hFirstDerivative v i)‖ ≤ _
    calc
      _ ≤ ∑ i : Fin n, ‖inner ℝ
          ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).compLp F)
          (P201Specs.hFirstDerivative v i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, ‖F‖ * ‖v‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact (norm_inner_le_norm _ _).trans (mul_le_mul
          (coordinate_norm_le Ω F i) (firstDerivative_norm_le Ω v i)
          (norm_nonneg _) (norm_nonneg _))
      _ = _ := by simp [mul_assoc]
  have hd : ‖inner ℝ d (P201Specs.hUnderlying Ω 1 v)‖ ≤ ‖d‖ * ‖v‖ :=
    (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (underlying_norm_le Ω v) (norm_nonneg d))
  exact (norm_add_le _ _).trans ((add_le_add hflux hd).trans_eq (by ring))

/-- Distributional divergence makes the bulk functional vanish on H¹₀. -/
lemma bulkFunctional_zero {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (F : VectorL2 Ω) (d : Lp ℝ Ω 2) (hd : HasDivergence Ω F d)
    (w : H10 ℝ Ω) : bulkFunctional Ω F d w.val = 0 := by
  have he : ∀ (φ : Test ℝ Ω) (z : H10 ℝ Ω),
      P201Specs.hZeroUnderlying Ω z = P102.U4.testToDomainLp Ω 2 φ →
      P201Specs.negativeDivergenceDistribution Ω F φ = (-pivot Ω d) z := by
    intro φ z hz
    have h := congrArg (fun T : Distribution ℝ Ω => T φ) hd
    change P201Specs.negativeDivergenceDistribution Ω F φ = -P201Specs.regularDistribution Ω d φ at h
    rw [h]
    change -P201Specs.regularDistribution Ω d φ = -(pivot Ω d z)
    rw [pivotPairing, hz]
    rw [P102.U4.regular_pairing n ℝ Ω d
      (P102.U4.domainLp_locallyIntegrable Ω 2 d) φ]
    congr 1
    apply integral_congr_ae
    filter_upwards [P102.U4.testToDomainLp_ae Ω 2 φ] with x hx
    rw [hx, mul_comm]
  have h := InteriorTesting.energyTesting hn Ω F (-pivot Ω d) he w
  simp only [bulkFunctional, add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [InteriorTesting.fluxFunctional_integral, h]
  change -inner ℝ d (P201Specs.hZeroUnderlying Ω w) +
    inner ℝ d (P201Specs.hUnderlying Ω 1 w.val) = 0
  exact neg_add_cancel _

/-- Descent through the bounded section; the divergence condition proves
independence of the chosen lift. -/
def normalTrace {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : TraceData Ω hΩ) (F : VectorL2 Ω) (d : Lp ℝ Ω 2) : HminusHalf Ω hΩ :=
  (bulkFunctional Ω F d).comp D.lift

lemma normalTrace_pairing {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (D : TraceData Ω hΩ)
    (F : VectorL2 Ω) (d : Lp ℝ Ω 2) (hd : HasDivergence Ω F d) :
    Pairing D F d (normalTrace D F d) := by
  intro v
  have hk : v - D.lift (D.trace v) ∈ P201Specs.hZeroSubmodule ℝ Ω := by
    rw [← D.kernel]
    change D.trace (v - D.lift (D.trace v)) = 0
    rw [map_sub, D.right_inverse, sub_self]
  have hz := bulkFunctional_zero (by omega) Ω F d hd ⟨_, hk⟩
  change bulkFunctional Ω F d (v - D.lift (D.trace v)) = 0 at hz
  rw [map_sub, sub_eq_zero] at hz
  change bulkFunctional Ω F d (D.lift (D.trace v)) = _
  rw [← hz, bulkFunctional_integral]

lemma pairing_unique {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : TraceData Ω hΩ) (F : VectorL2 Ω) (d : Lp ℝ Ω 2)
    (τ σ : HminusHalf Ω hΩ) (hτ : Pairing D F d τ) (hσ : Pairing D F d σ) : τ = σ := by
  ext g
  rw [← D.right_inverse g, hτ, hσ]

lemma normalTrace_bound {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : TraceData Ω hΩ) (F : VectorL2 Ω) (d : Lp ℝ Ω 2) :
    ‖normalTrace D F d‖ ≤ ((m + 1 : ℕ) : ℝ) * (‖D.lift‖ + 1) * (‖F‖ + ‖d‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro g
  change ‖bulkFunctional Ω F d (D.lift g)‖ ≤ _
  calc
    _ ≤ (((m + 1 : ℕ) : ℝ) * ‖F‖ + ‖d‖) * ‖D.lift g‖ := bulkFunctional_bound Ω F d _
    _ ≤ (((m + 1 : ℕ) : ℝ) * ‖F‖ + ‖d‖) * (‖D.lift‖ * ‖g‖) :=
      mul_le_mul_of_nonneg_left (D.lift.le_opNorm g) (by positivity)
    _ ≤ (((m + 1 : ℕ) : ℝ) * (‖F‖ + ‖d‖)) * ((‖D.lift‖ + 1) * ‖g‖) := by
      apply mul_le_mul
      · have hn : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by simp
        nlinarith [norm_nonneg d]
      · exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg g)
      · positivity
      · positivity
    _ = _ := by ring

theorem forEveryTrace : P201Specs.NormalTrace.ForEveryTraceStatement := by
  intro m Ω hΩ D
  refine ⟨((m + 1 : ℕ) : ℝ) * (‖D.lift‖ + 1), by positivity, ?_⟩
  intro F d hd
  refine ⟨normalTrace D F d, normalTrace_pairing Ω hΩ D F d hd,
    normalTrace_bound D F d, ?_⟩
  intro σ hσ
  exact pairing_unique D F d σ _ hσ (normalTrace_pairing Ω hΩ D F d hd)

theorem existence : P201Specs.NormalTrace.ExistenceStatement := by
  intro m Ω hΩ
  obtain ⟨T, L, hT, _, hL, hk⟩ := Trace.exact_trace m Ω hΩ
  let D : TraceData Ω hΩ := ⟨T, L, hT, hL, hk⟩
  exact ⟨D, forEveryTrace Ω hΩ D⟩

lemma regular_gradient_component {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) (i : Fin n) :
    P201Specs.regularDistribution Ω (fun x => P201Specs.hGradient u x i) =
      P201Specs.regularDistribution Ω (P201Specs.hFirstDerivative u i) := by
  have hg : (P201Specs.hGradient u : Space n → Space n) =ᵐ[domainMeasure Ω]
      (fun x => WithLp.toLp 2 (fun j => P201Specs.hFirstDerivative u j x)) :=
    MemLp.coeFn_toLp _
  apply (P102.U4.regular_injectivity n ℝ Ω _ _
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      (((Lp.memLp (P201Specs.hGradient u)).eval_piLp i).locallyIntegrable (by norm_num)))
    (P102.U4.domainLp_locallyIntegrable Ω 2 (P201Specs.hFirstDerivative u i))).mpr
  filter_upwards [hg] with x hx
  exact congrArg (fun z : Space n => z i) hx

theorem gradientDivergence : P201Specs.NormalTrace.GradientDivergenceStatement := by
  intro n Ω u d hd
  change -∑ i : Fin n, P201Specs.distributionDerivative {i}
    (P201Specs.regularDistribution Ω (fun x => P201Specs.hGradient u x i)) = -P201Specs.regularDistribution Ω d
  congr 1
  change (∑ i : Fin n, P201Specs.distributionDerivative {i, i}
    (P201Specs.regularDistribution Ω (P201Specs.hUnderlying Ω 1 u))) = P201Specs.regularDistribution Ω d at hd
  rw [← hd]
  apply Finset.sum_congr rfl
  intro i hi
  rw [regular_gradient_component]
  have he := hilbertDerivativeDistribution Ω 1 u
    (⟨{i}, by simp⟩ : P102.U4.SobolevIndex n 1)
  change P201Specs.distributionDerivative {i}
    (P201Specs.regularDistribution Ω (P201Specs.hUnderlying Ω 1 u)) =
      P201Specs.regularDistribution Ω (P201Specs.hFirstDerivative u i) at he
  rw [← he]
  exact (P102.U4.derivative_add n ℝ Ω {i} {i} _).symm

theorem green : P201Specs.NormalTrace.GreenStatement := by
  intro m Ω hΩ D u v du dv hu hv
  let τu := normalTrace D (P201Specs.hGradient u) du
  let τv := normalTrace D (P201Specs.hGradient v) dv
  have hτu := normalTrace_pairing Ω hΩ D _ _ (gradientDivergence Ω u du hu)
  have hτv := normalTrace_pairing Ω hΩ D _ _ (gradientDivergence Ω v dv hv)
  refine ⟨τu, τv, hτu, hτv, ?_⟩
  rw [hτv u, hτu v]
  have hi (w z : H ℝ Ω 1) :
      IntegrableOn (fun x => inner ℝ (P201Specs.hGradient w x) (P201Specs.hGradient z x)) Ω volume :=
    L2.integrable_inner _ _
  have hm (d : Lp ℝ Ω 2) (w : H ℝ Ω 1) :
      IntegrableOn (fun x => d x * P201Specs.hUnderlying Ω 1 w x) Ω volume :=
    (Lp.memLp d).integrable_mul (Lp.memLp (P201Specs.hUnderlying Ω 1 w))
  calc
    _ = ∫ x in Ω,
        (inner ℝ (P201Specs.hGradient v x) (P201Specs.hGradient u x) +
          dv x * P201Specs.hUnderlying Ω 1 u x) -
        (inner ℝ (P201Specs.hGradient u x) (P201Specs.hGradient v x) +
          du x * P201Specs.hUnderlying Ω 1 v x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [real_inner_comm (P201Specs.hGradient v x) (P201Specs.hGradient u x)]
      ring
    _ = _ := integral_sub ((hi v u).add (hm dv u)) ((hi u v).add (hm du v))

/-- Continuous data near a bounded domain's closure are in L². -/
lemma continuousOn_closure_memLp {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) {E : Type} [NormedAddCommGroup E]
    (f : Space (m + 1) → E) (hf : ContinuousOn f (closure (Ω : Set (Space (m + 1))))) :
    MemLp f 2 (domainMeasure Ω) := by
  have hK := SmoothFlux.compact_closure Ω hΩ
  haveI : IsFiniteMeasure (domainMeasure Ω) := by
    constructor
    change (volume.restrict (Ω : Set (Space (m + 1)))) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hK.measure_lt_top
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  apply MemLp.of_bound ((hf.mono subset_closure).aestronglyMeasurable Ω.isOpen.measurableSet) C
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact hC x (subset_closure hx)

lemma smooth_realization {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (U : Set (Space (m + 1)))
    (F₀ : Space (m + 1) → Space (m + 1)) (hU : IsOpen U)
    (hΩU : closure (Ω : Set (Space (m + 1))) ⊆ U) (hF : ContDiffOn ℝ 1 F₀ U) :
    ∃ (F : VectorL2 Ω) (d : Lp ℝ Ω 2),
      (F : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure Ω] F₀ ∧
      (d : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] divergence F₀ ∧
      HasDivergence Ω F d := by
  have hFm := continuousOn_closure_memLp Ω hΩ F₀ (hF.continuousOn.mono hΩU)
  have hdm := continuousOn_closure_memLp Ω hΩ (divergence F₀)
    ((SmoothFlux.continuousOn_divergence hU hF).mono hΩU)
  let F := hFm.toLp F₀
  let d := hdm.toLp (divergence F₀)
  have hFa : (F : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure Ω] F₀ := hFm.coeFn_toLp
  have hda : (d : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] divergence F₀ := hdm.coeFn_toLp
  refine ⟨F, d, hFa, hda, ?_⟩
  ext φ
  change P201Specs.negativeDivergenceDistribution Ω F φ =
    -P201Specs.regularDistribution Ω d φ
  rw [InteriorTesting.negativeDivergenceDistribution_pairing]
  have he : P201Specs.weakNegativeDivergence Ω F φ =
      P201Specs.weakNegativeDivergence Ω F₀ φ := by
    apply integral_congr_ae
    filter_upwards [hFa] with x hx
    rw [hx]
  rw [he, InteriorTesting.flux_testing_identity Ω (hF.mono (subset_trans subset_closure hΩU))]
  rw [P102.U4.regular_pairing (m + 1) ℝ Ω d (P102.U4.domainLp_locallyIntegrable Ω 2 d)]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [hda] with x hx
  rw [hx]
  ring

/-- Weak and classical gradients agree for smooth representatives of H¹ data. -/
lemma smooth_gradient_ae {m : ℕ} (Ω : Domain (m + 1)) (v : H ℝ Ω 1)
    (f : Space (m + 1) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hv : P201Specs.hUnderlying Ω 1 v =ᵐ[domainMeasure Ω] f) :
    (P201Specs.hGradient v : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure Ω]
      gradient f := by
  have hreg : P201Specs.regularDistribution Ω (P201Specs.hUnderlying Ω 1 v) =
      P201Specs.regularDistribution Ω f :=
    (P102.U4.regular_injectivity (m + 1) ℝ Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω 2 _) (hf.continuous.continuousOn.locallyIntegrableOn
        Ω.isOpen.measurableSet)).mpr hv
  have hi (i : Fin (m + 1)) :
      (P201Specs.hFirstDerivative v i : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω]
        (fun x => fderiv ℝ f x (coordinate (m + 1) i)) := by
    have hdf : ContinuousOn (fun x => fderiv ℝ f x (coordinate (m + 1) i)) Ω :=
      (hf.continuous_fderiv (by simp)).clm_apply continuous_const |>.continuousOn
    have he := hilbertDerivativeDistribution Ω 1 v
      (⟨{i}, by simp⟩ : P102.U4.SobolevIndex (m + 1) 1)
    change P201Specs.distributionDerivative {i}
      (P201Specs.regularDistribution Ω (P201Specs.hUnderlying Ω 1 v)) =
        P201Specs.regularDistribution Ω (P201Specs.hFirstDerivative v i) at he
    rw [hreg] at he
    change P102.U4.distributionPartial {i} (P102.U4.regularDistribution Ω f) = _ at he
    rw [P102.U4.derivative_classicalCompatibility (m + 1) ℝ Ω {i} f
      (hf.of_le (by simp)).contDiffOn] at he
    apply (P102.U4.regular_injectivity (m + 1) ℝ Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω 2 _)
      (hdf.locallyIntegrableOn Ω.isOpen.measurableSet)).mp
    simpa [P102.U4.multiPartial, P102.U4.partialWord] using he.symm
  have hg : (P201Specs.hGradient v : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure Ω]
      (fun x => WithLp.toLp 2 (fun j => P201Specs.hFirstDerivative v j x)) := MemLp.coeFn_toLp _
  filter_upwards [hg, ae_all_iff.mpr hi] with x hx hxi
  rw [hx]
  apply PiLp.ext
  intro i
  exact hxi i

/-- Smooth outward flux is square integrable on the physical surface. -/
lemma boundary_flux_memLp {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (ν : Space (m + 1) → Space (m + 1))
    (hν : P201Specs.SmoothFlux.IsGeometricNormalField Ω ν)
    (F₀ : Space (m + 1) → Space (m + 1))
    (hF : ContinuousOn F₀ (frontier (Ω : Set (Space (m + 1))))) :
    MemLp (fun x => inner ℝ (F₀ x) (ν x)) 2 (boundaryMeasure Ω) := by
  haveI : IsFiniteMeasure (boundaryMeasure Ω) := ⟨SmoothFlux.boundary_finite Ω hΩ⟩
  have hK : IsCompact (frontier (Ω : Set (Space (m + 1)))) :=
    (SmoothFlux.compact_closure Ω hΩ).of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  apply MemLp.of_bound ((hF.aestronglyMeasurable isClosed_frontier.measurableSet).inner hν.1) C
  filter_upwards [P102.Trace.Ordinary.boundaryMeasure_ae_frontier Ω, hν.2] with x hx hn
  have hn1 : ‖ν x‖ = 1 := by simpa only [LinearIsometryEquiv.norm_map] using hn.1
  exact (norm_inner_le_norm _ _).trans (by simpa [hn1] using hC x hx)

/-- Density extends the geometric identity from smooth bulk tests to every
boundary datum, using its physical L² inclusion. -/
lemma smooth_pairing_extension {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (D : TraceData Ω hΩ)
    (ν : Space (m + 1) → Space (m + 1))
    (hν : P201Specs.SmoothFlux.IsGeometricNormalField Ω ν)
    (U : Set (Space (m + 1))) (F₀ : Space (m + 1) → Space (m + 1))
    (_hU : IsOpen U) (hΩU : closure (Ω : Set (Space (m + 1))) ⊆ U)
    (hF : ContDiffOn ℝ 1 F₀ U)
    (hflux : ∀ f : Space (m + 1) → ℝ, ContDiff ℝ ∞ f →
      (∫ x in Ω, inner ℝ (F₀ x) (gradient f x) + divergence F₀ x * f x) =
        ∫ x, f x * inner ℝ (F₀ x) (ν x) ∂boundaryMeasure Ω)
    (F : VectorL2 Ω) (d : Lp ℝ Ω 2)
    (hFa : (F : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure Ω] F₀)
    (hda : (d : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] divergence F₀)
    (τ : HminusHalf Ω hΩ) (hτ : Pairing D F d τ) :
    ∀ g : Hhalf Ω hΩ,
      Integrable (fun x => P201Specs.Trace.inclusion Ω hΩ g x * inner ℝ (F₀ x) (ν x))
        (boundaryMeasure Ω) ∧
      τ g = ∫ x, P201Specs.Trace.inclusion Ω hΩ g x * inner ℝ (F₀ x) (ν x)
        ∂boundaryMeasure Ω := by
  have hb := boundary_flux_memLp Ω hΩ ν hν F₀
    (hF.continuousOn.mono (frontier_subset_closure.trans hΩU))
  let b : P201Specs.Trace.BoundaryL2 Ω := hb.toLp (fun x => inner ℝ (F₀ x) (ν x))
  let B : Hhalf Ω hΩ →L[ℝ] ℝ := (innerSL ℝ b).comp (P201Specs.Trace.inclusion Ω hΩ)
  have hB (g : Hhalf Ω hΩ) : B g =
      ∫ x, P201Specs.Trace.inclusion Ω hΩ g x * inner ℝ (F₀ x) (ν x) ∂boundaryMeasure Ω := by
    change inner ℝ b (P201Specs.Trace.inclusion Ω hΩ g) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hb.coeFn_toLp] with x hx
    simp only [RCLike.inner_apply, RCLike.conj_to_real]
    rw [hx]
  have heq (v : H ℝ Ω 1) : τ (D.trace v) = B (D.trace v) := by
    let e := P201Specs.hToW ℝ Ω 1
    let A' := (τ.comp D.trace).comp e.symm.toContinuousLinearMap
    let B' := (B.comp D.trace).comp e.symm.toContinuousLinearMap
    have hc : IsClosed {w : W ℝ Ω 1 2 | A' w = B' w} := isClosed_eq A'.continuous B'.continuous
    have hs : (P102.Trace.Ordinary.smoothRestrictionSubmodule ℝ Ω 2 : Set (W ℝ Ω 1 2)) ⊆
        {w | A' w = B' w} := by
      rintro w ⟨f, hf, hw⟩
      let z := e.symm w
      have hz : P201Specs.hUnderlying Ω 1 z =ᵐ[domainMeasure Ω] f := by
        change P102.U4.sobolevUnderlying (e (e.symm w)) =ᵐ[_] f
        simpa using hw
      change τ (D.trace z) = B (D.trace z)
      rw [hτ z, hB]
      have hg := smooth_gradient_ae Ω z f hf hz
      have ht := D.smooth z f hf hz
      calc
        _ = ∫ x in Ω, inner ℝ (F₀ x) (gradient f x) + divergence F₀ x * f x := by
          apply integral_congr_ae
          filter_upwards [hFa, hda, hg, hz] with x hx hd hxg hxz
          rw [hx, hd, hxg, hxz]
        _ = ∫ x, f x * inner ℝ (F₀ x) (ν x) ∂boundaryMeasure Ω := hflux f hf
        _ = _ := integral_congr_ae (ht.mono fun x hx => by rw [hx]) |>.symm
    have hdense := P102.Trace.Ordinary.smooth_restrictions_dense
      P102.Sobolev.Extension.lipschitz_ambient_density (graphFrame m) Ω hΩ ℝ 2 (by norm_num)
    have he := closure_minimal hs hc (hdense (e v))
    simpa [A', B', e] using he
  intro g
  refine ⟨?_, ?_⟩
  · exact (Lp.memLp (P201Specs.Trace.inclusion Ω hΩ g)).integrable_mul hb
  · rw [← D.right_inverse g, heq, hB]

theorem smoothAgreement : P201Specs.NormalTrace.SmoothAgreementStatement := by
  intro m Ω hΩ
  obtain ⟨ν, hν, hflux⟩ := SmoothFlux.smooth_flux m Ω hΩ
  refine ⟨ν, hν, ?_⟩
  intro D U F₀ hU hΩU hF
  obtain ⟨F, d, hFa, hda, hd⟩ := smooth_realization Ω hΩ U F₀ hU hΩU hF
  refine ⟨F, d, hFa, hda, hd, ?_⟩
  intro τ hτ
  apply smooth_pairing_extension Ω hΩ D ν hν U F₀ hU hΩU hF
    (fun f hf => (hflux U F₀ f hU hΩU hF (hf.of_le (by simp)).contDiffOn).2.2)
    F d hFa hda τ hτ

theorem endpoint : P201Specs.NormalTrace.EndpointStatement := by
  refine ⟨?_, SmoothFlux.interval_flux⟩
  intro Ω hΩ
  exact ⟨boundaryCountingMeasure Ω, (Trace.endpoint_space Ω hΩ).2.1⟩

end P201.NormalTrace
