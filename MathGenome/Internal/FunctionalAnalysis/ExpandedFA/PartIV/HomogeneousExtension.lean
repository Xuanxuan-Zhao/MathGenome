import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HomogeneousExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HomogeneousMeromorphic
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.PointSupportedDistributions
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Algebra.MvPolynomial.Funext

/-! Homogeneous extension, the critical obstruction, and exact ambiguity.
All jets, residues, Schwartz maps, and dilations below use the accepted
meromorphic-family objects; competing extensions range over the full LF dual. -/

open MeasureTheory Filter
open scoped SchwartzMap ContDiff Topology

noncomputable section

namespace ExpandedFA.PartIV.HomogeneousExtension
open ExpandedFA.Fourier ExpandedFA.PartIV.HomogeneousMeromorphic

variable {d : ℕ}

@[simp] theorem testToSchwartz_apply (φ : CompactTest d) (x : Euclidean d) :
    testToSchwartz φ x = φ x := rfl

@[simp] theorem compactTestDilation_apply (a : ℝ) (ha : 0 < a)
    (φ : CompactTest d) (x : Euclidean d) : compactTestDilation a ha φ x = φ (a⁻¹ • x) := rfl

/-- The compact-test and Schwartz dilation formulas agree as actual functions. -/
theorem testToSchwartz_dilation (a : ℝ) (ha : 0 < a) (φ : CompactTest d) :
    testToSchwartz (compactTestDilation a ha φ) = testDilation a ha (testToSchwartz φ) := by
  ext x
  rfl

/-- A test supported away from zero has every jet at zero equal to zero. -/
theorem jet_eq_zero_of_off_zero (φ : Schwartz ℂ d) (hφ : (0 : Euclidean d) ∉ tsupport φ)
    (α : MultiIndex d) : jet α φ = 0 := by
  rw [jet_apply, partialDerivative, wordDerivative_apply_eq_iteratedFDeriv]
  have hz : iteratedFDeriv ℝ (derivativeWord α).length φ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hφ (tsupport_iteratedFDeriv_subset _ h))
  rw [hz]
  rfl

theorem taylorPolynomial_eq_zero_of_off_zero (N : ℕ) (φ : Schwartz ℂ d)
    (hφ : (0 : Euclidean d) ∉ tsupport φ) (x : Euclidean d) :
    taylorPolynomial N φ x = 0 := by
  classical
  simp [taylorPolynomial, jet_eq_zero_of_off_zero φ hφ]

theorem polarPart_apply_eq_zero_of_off_zero (k : Euclidean d → ℂ) (N : ℕ)
    (z : ℂ) (φ : Schwartz ℂ d) (hφ : (0 : Euclidean d) ∉ tsupport φ) :
    polarPart k N z φ = 0 := by
  classical
  simp [polarPart, taylorCoefficient, jet_eq_zero_of_off_zero φ hφ]

theorem residue_apply_eq_zero_of_off_zero (k : Euclidean d → ℂ) (m : ℕ)
    (φ : Schwartz ℂ d) (hφ : (0 : Euclidean d) ∉ tsupport φ) : residue k m φ = 0 := by
  classical
  simp [residue_eq_taylorCoefficient, taylorCoefficient, jet_eq_zero_of_off_zero φ hφ]

/-- Taylor subtraction has no effect on a test supported off zero. -/
theorem remainder_off_zero (k : Euclidean d → ℂ) (lam : ℂ) (N : ℕ) (z : ℂ)
    (φ : Schwartz ℂ d) (hφ : (0 : Euclidean d) ∉ tsupport φ)
    (hi : IntegrableOn (innerIntegrand k lam N z φ) (Metric.closedBall 0 1))
    (ho : IntegrableOn (outerIntegrand k lam z φ) (Metric.closedBall 0 1)ᶜ) :
    taylorRemainder k lam N z φ = initialPairing k lam z φ := by
  have hinner : innerIntegrand k lam N z φ = outerIntegrand k lam z φ := by
    funext x
    simp [innerIntegrand, outerIntegrand, taylorPolynomial_eq_zero_of_off_zero N φ hφ]
  rw [hinner] at hi
  have hint : Integrable (outerIntegrand k lam z φ) := by simpa using hi.union ho
  change (∫ x in Metric.closedBall (0 : Euclidean d) 1, innerIntegrand k lam N z φ x) +
    (∫ x in (Metric.closedBall (0 : Euclidean d) 1)ᶜ, outerIntegrand k lam z φ x) = _
  rw [hinner]
  exact integral_add_compl measurableSet_closedBall hint

/-- At the original exponent the weighted kernel equals k away from zero;
the value assigned to k at zero never affects an off-zero test. -/
theorem initialPairing_self_off_zero (k : Euclidean d → ℂ) (lam : ℂ)
    (φ : Schwartz ℂ d) (hφ : (0 : Euclidean d) ∉ tsupport φ) :
    initialPairing k lam lam φ = ∫ x, k x * φ x := by
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x = 0
  · subst x
    have : φ 0 = 0 := image_eq_zero_of_notMem_tsupport hφ
    simp [kernelWeight, this]
  · simp [kernelWeight, hx]

/-- The supplied regular meromorphic value really agrees with the kernel. -/
theorem regular_tempered_extension :
    Specs.ExpandedFA.PartIV.HomogeneousExtension.regularTemperedExtensionType := by
  intro d k lam hk hlam
  obtain ⟨I, E, _, hE, _, hformula, _, _, hscale⟩ := construct_family d k lam hk
  refine ⟨I lam, ?_, fun a ha => hscale a ha lam hlam⟩
  intro φ _ hφ
  obtain ⟨N, hN⟩ := mem_some_halfPlane (d := d) lam
  have he := hE N lam hN φ
  calc
    I lam φ = E N lam φ := by
      rw [hformula N lam hN hlam, add_apply,
        polarPart_apply_eq_zero_of_off_zero k N lam φ hφ, zero_add]
    _ = taylorRemainder k lam N lam φ := he.2.2
    _ = initialPairing k lam lam φ := remainder_off_zero k lam N lam φ hφ he.1 he.2.1
    _ = ∫ x, k x * φ x := initialPairing_self_off_zero k lam φ hφ

/-- The critical poles have no accumulation point in the finite plane. -/
theorem regular_near_pole (d m : ℕ) :
    ∀ᶠ z in 𝓝[≠] (pole d m), z ∈ regularSet d := by
  have hb : Metric.ball (pole d m) (1 / 2 : ℝ) ∈ 𝓝 (pole d m) :=
    Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hb, self_mem_nhdsWithin] with z hz hne
  intro j hj
  have hne' : j ≠ m := by
    intro h
    subst j
    exact hne hj
  have hdist : ‖pole d j - pole d m‖ < (1 / 2 : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm, hj] using hz
  have habs := (Complex.abs_re_le_norm (pole d j - pole d m)).trans_lt hdist
  simp only [Complex.sub_re, pole_re] at habs
  rcases lt_or_gt_of_ne hne' with h | h
  · have hh : (j : ℝ) + 1 ≤ m := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)] at habs
    linarith
  · have hh : (m : ℝ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)] at habs
    linarith

/-- Comparing constant Laurent coefficients, justified by differentiation of
an identity of analytic functions after multiplication by the local parameter.
This lemma does not assume the desired finite-part scaling law. -/
theorem laurent_scaling (I H : ℂ → Tempered ℂ d) (R : Tempered ℂ d) (p : ℂ)
    (hH : ∀ φ : Schwartz ℂ d, AnalyticAt ℂ (fun z => H z φ) p)
    (hLaurent : ∀ᶠ z in 𝓝[≠] p, I z = (z - p)⁻¹ • R + H z)
    (hscale : ∀ (a : ℝ) (ha : 0 < a), ∀ᶠ z in 𝓝[≠] p,
      dilation a ha (I z) = (a : ℂ) ^ z • I z) :
    ∀ (a : ℝ) (ha : 0 < a),
      dilation a ha (H p) = (a : ℂ) ^ p • (H p + (Real.log a : ℂ) • R) := by
  intro a ha
  ext φ
  let b : ℂ := ((a : ℂ) ^ d)⁻¹
  let ψ := testDilation a ha φ
  let f : ℂ → ℂ := fun z => b * (R ψ + (z - p) * H z ψ)
  let g : ℂ → ℂ := fun z => (a : ℂ) ^ z * (R φ + (z - p) * H z φ)
  have heq : f =ᶠ[𝓝[≠] p] g := by
    filter_upwards [hLaurent, hscale a ha, self_mem_nhdsWithin] with z hz hsz hzp
    have hpz : z - p ≠ 0 := sub_ne_zero.mpr hzp
    have hm (χ : Schwartz ℂ d) : (z - p) * I z χ = R χ + (z - p) * H z χ := by
      rw [hz]
      simp only [add_apply, smul_apply, smul_eq_mul]
      field_simp
    have hs := congrArg (fun u : Tempered ℂ d => u φ) hsz
    change b * I z ψ = (a : ℂ) ^ z * I z φ at hs
    dsimp [f, g]
    rw [← hm ψ, ← hm φ]
    linear_combination (z - p) * hs
  have hc : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hf : HasDerivAt f (b * H p ψ) p := by
    convert (((hasDerivAt_const p (R ψ)).add
      (((hasDerivAt_id p).sub_const p).mul (hH ψ).differentiableAt.hasDerivAt)).const_mul b) using 1 <;>
      simp [f]
  have hg : HasDerivAt g
      ((a : ℂ) ^ p * Complex.log a * R φ + (a : ℂ) ^ p * H p φ) p := by
    convert (Complex.hasStrictDerivAt_const_cpow (x := (a : ℂ)) (y := p) (Or.inl hc)).hasDerivAt.mul
      ((hasDerivAt_const p (R φ)).add
        (((hasDerivAt_id p).sub_const p).mul (hH φ).differentiableAt.hasDerivAt)) using 1 <;>
      (simp [g] <;> rfl)
  have hpoint : f p = g p := tendsto_nhds_unique_of_eventuallyEq
    (hf.continuousAt.mono_left nhdsWithin_le_nhds)
    (hg.continuousAt.mono_left nhdsWithin_le_nhds) heq
  have heq' : f =ᶠ[𝓝 p] g := by
    rw [← nhdsNE_sup_pure p]
    exact Filter.eventually_sup.mpr ⟨heq, by simpa using hpoint⟩
  have hd := hf.unique (hg.congr_of_eventuallyEq heq')
  change b * H p ψ = (a : ℂ) ^ p * (H p φ + (Real.log a : ℂ) * R φ)
  rw [Complex.ofReal_log ha.le]
  linear_combination hd

/-- The Laurent constant term agrees with the kernel on the punctured space.
The comparison uses actual continuous scalar pairings, not an assumed extension
certificate. -/
theorem laurent_off_zero (k : Euclidean d → ℂ) (lam : ℂ)
    (I : ℂ → Tempered ℂ d) (E : ℕ → ℂ → Tempered ℂ d)
    (hE : ∀ N z, z ∈ halfPlane d N → ∀ φ : Schwartz ℂ d,
      IntegrableOn (innerIntegrand k lam N z φ) (Metric.closedBall 0 1) ∧
      IntegrableOn (outerIntegrand k lam z φ) (Metric.closedBall 0 1)ᶜ ∧
      E N z φ = taylorRemainder k lam N z φ)
    (hEa : ∀ N φ, AnalyticOnNhd ℂ (fun z => E N z φ) (halfPlane d N))
    (hformula : ∀ N z, z ∈ halfPlane d N → z ∈ regularSet d →
      I z = polarPart k N z + E N z)
    (m : ℕ) (hlam : lam = pole d m) (H : ℂ → Tempered ℂ d)
    (hHa : ∀ φ : Schwartz ℂ d, AnalyticAt ℂ (fun z => H z φ) lam)
    (hH : ∀ᶠ z in 𝓝[≠] lam, I z = (z - lam)⁻¹ • residue k m + H z) :
    TemperedAgreesOffZero (H lam) k := by
  subst lam
  intro φ _ hφ
  obtain ⟨N, hN⟩ := mem_some_halfPlane (d := d) (pole d m)
  have heq : (fun z => H z φ) =ᶠ[𝓝[≠] (pole d m)] (fun z => E N z φ) := by
    filter_upwards [hH, regular_near_pole d m,
      mem_nhdsWithin_of_mem_nhds ((isOpen_halfPlane d N).mem_nhds hN)] with z hz hreg hzN
    have h₁ := congrArg (fun T : Tempered ℂ d => T φ) hz
    have h₂ := congrArg (fun T : Tempered ℂ d => T φ) (hformula N z hzN hreg)
    simp only [add_apply, smul_apply, smul_eq_mul,
      residue_apply_eq_zero_of_off_zero k m φ hφ, mul_zero, zero_add] at h₁
    simp only [add_apply, polarPart_apply_eq_zero_of_off_zero k N z φ hφ, zero_add] at h₂
    exact h₁.symm.trans h₂
  have hlim : H (pole d m) φ = E N (pole d m) φ :=
    tendsto_nhds_unique_of_eventuallyEq
      ((hHa φ).continuousAt.mono_left nhdsWithin_le_nhds)
      ((hEa N φ (pole d m) hN).continuousAt.mono_left nhdsWithin_le_nhds) heq
  obtain ⟨hi, ho, he⟩ := hE N (pole d m) hN φ
  exact hlim.trans (he.trans ((remainder_off_zero k (pole d m) N (pole d m) φ hφ hi ho).trans
    (initialPairing_self_off_zero k (pole d m) φ hφ)))

/-- The full tempered finite-part assertion, with the source residue and sign. -/
theorem finite_part : Specs.ExpandedFA.PartIV.HomogeneousExtension.finitePartType := by
  intro d k m hk
  obtain ⟨I, E, _, hE, hEa, hformula, _, hcharts, hscale⟩ :=
    construct_family d k (pole d m) hk
  obtain ⟨V, H, hV, hHa, _, hchart⟩ := hcharts m
  have hpV : pole d m ∈ V := mem_of_mem_nhds hV
  have hH : ∀ φ : Schwartz ℂ d, AnalyticAt ℂ (fun z => H z φ) (pole d m) :=
    fun φ => hHa φ (pole d m) hpV
  have hL : ∀ᶠ z in 𝓝[≠] (pole d m), I z = (z - pole d m)⁻¹ • residue k m + H z := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hV, self_mem_nhdsWithin] with z hz hne
    exact hchart z hz hne
  refine ⟨H (pole d m), ?_, ?_⟩
  · exact laurent_off_zero k (pole d m) I E hE (fun N => (hEa N).1)
      hformula m rfl H hH hL
  · apply laurent_scaling I H (residue k m) (pole d m) hH hL
    intro a ha
    exact (regular_near_pole d m).mono (fun z hz => hscale a ha z hz)

/-- Vanishing of the specified moments kills the actual distributional residue. -/
theorem residue_eq_zero_of_moments (k : Euclidean d → ℂ) (m : ℕ)
    (h : MomentsVanish k m) : residue k m = 0 := by
  classical
  unfold residue
  apply Finset.sum_eq_zero
  intro α hα
  rw [h α ((mem_indices α m).mp hα), mul_zero]
  exact zero_smul ℂ (deltaDerivative α)

/-- The constructive sufficiency direction, on Schwartz space. No moment
condition is needed to construct the finite part itself. -/
theorem critical_tempered_extension_of_moments (k : Euclidean d → ℂ) (m : ℕ)
    (hk : SmoothHomogeneous k (pole d m)) (hm : MomentsVanish k m) :
    ∃ T : Tempered ℂ d, TemperedAgreesOffZero T k ∧
      ∀ (a : ℝ) (ha : 0 < a), dilation a ha T = (a : ℂ) ^ (pole d m) • T := by
  obtain ⟨F, hF, hscale⟩ := finite_part d k m hk
  refine ⟨F, hF, fun a ha => ?_⟩
  have hs := hscale a ha
  rw [residue_eq_zero_of_moments k m hm] at hs
  ext φ
  have hsφ := congrArg (fun T : Tempered ℂ d => T φ) hs
  simpa only [add_apply, smul_apply, smul_eq_mul, zero_apply, mul_zero, add_zero] using hsφ

/-- The algebraic compact-step inclusion is the actual unchanged function. -/
def stepToSchwartzLM (K : TopologicalSpace.Compacts (Euclidean d)) :
    ContDiffMapSupportedIn (Euclidean d) ℂ ⊤ K →ₗ[ℂ] Schwartz ℂ d where
  toFun φ := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

/-- Compact support bounds polynomial weights, so the inclusion from a fixed
step into Schwartz space is continuous in its genuine derivative topology. -/
theorem continuous_stepToSchwartz (K : TopologicalSpace.Compacts (Euclidean d)) :
    Continuous (stepToSchwartzLM K) := by
  classical
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.exists_norm_le
  let C := max R 0
  have hC : 0 ≤ C := le_max_right _ _
  apply WithSeminorms.continuous_of_isBounded
    (ContDiffMapSupportedIn.withSeminorms ℂ (Euclidean d) ℂ ⊤ K)
    (schwartz_withSeminorms ℂ (Euclidean d) ℂ) (stepToSchwartzLM K)
  apply Seminorm.IsBounded.of_real
  intro n
  refine ⟨{n.2}, C ^ n.1, fun φ => ?_⟩
  simp only [Finset.sup_singleton]
  apply SchwartzMap.seminorm_le_bound ℂ n.1 n.2 (stepToSchwartzLM K φ)
    (mul_nonneg (pow_nonneg hC _) (apply_nonneg _ _))
  intro x
  change ‖x‖ ^ n.1 * ‖iteratedFDeriv ℝ n.2 φ x‖ ≤ _
  by_cases hx : x ∈ K
  · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ((hR x hx).trans (le_max_left _ _)) _)
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ)
      (norm_nonneg _) (pow_nonneg hC _)
  · have hz : iteratedFDeriv ℝ n.2 φ x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hx (φ.tsupport_subset (tsupport_iteratedFDeriv_subset _ h))
    rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (pow_nonneg hC _) (apply_nonneg _ _)

/-- The LF universal property proves continuity of the canonical inclusion.
This is not a sequential surrogate for continuity. -/
def testToSchwartzCLM : CompactTest d →L[ℂ] Schwartz ℂ d :=
  TestFunction.limitCLM ℂ testToSchwartz
    (fun K _ => ⟨stepToSchwartzLM K, continuous_stepToSchwartz K⟩)
    (fun _ _ _ => rfl)

@[simp] theorem testToSchwartzCLM_apply (φ : CompactTest d) :
    testToSchwartzCLM φ = testToSchwartz φ := rfl

/-- Every constructed tempered object gives an ordinary distribution. -/
def restrictTempered (T : Tempered ℂ d) : Distribution d := T.comp testToSchwartzCLM

@[simp] theorem restrictTempered_apply (T : Tempered ℂ d) (φ : CompactTest d) :
    restrictTempered T φ = T (testToSchwartz φ) := rfl

theorem restrictTempered_represents (T : Tempered ℂ d) : Represents T (restrictTempered T) :=
  fun _ => rfl

theorem restrictTempered_agrees (T : Tempered ℂ d) (k : Euclidean d → ℂ)
    (hT : TemperedAgreesOffZero T k) : AgreesOffZero (restrictTempered T) k := by
  intro φ hφ
  exact hT (testToSchwartz φ) φ.hasCompactSupport hφ

theorem restrictTempered_homogeneous (T : Tempered ℂ d) (lam : ℂ)
    (hT : ∀ (a : ℝ) (ha : 0 < a), dilation a ha T = (a : ℂ) ^ lam • T) :
    Homogeneous (restrictTempered T) lam := by
  intro a ha φ
  have hs := congrArg (fun S : Tempered ℂ d => S (testToSchwartz φ)) (hT a ha)
  change ((a : ℂ) ^ d)⁻¹ * T (testDilation a ha (testToSchwartz φ)) =
    (a : ℂ) ^ lam * T (testToSchwartz φ) at hs
  simpa only [restrictTempered_apply, testToSchwartz_dilation] using hs

/-- Existence in the full distribution space at every regular degree. -/
theorem regular_extension_exists (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (hlam : lam ∈ regularSet d) :
    ∃ u : Distribution d, IsHomogeneousExtension u k lam := by
  obtain ⟨T, hT, hhom⟩ := regular_tempered_extension d k lam hk hlam
  exact ⟨restrictTempered T, restrictTempered_homogeneous T lam hhom,
    restrictTempered_agrees T k hT⟩

/-- The sufficiency direction at critical degrees in the full distribution
space, without a temperedness assumption on the statement of existence. -/
theorem critical_extension_exists_of_moments (k : Euclidean d → ℂ) (m : ℕ)
    (hk : SmoothHomogeneous k (pole d m)) (hm : MomentsVanish k m) :
    ∃ u : Distribution d, IsHomogeneousExtension u k (pole d m) := by
  obtain ⟨T, hT, hhom⟩ := critical_tempered_extension_of_moments k m hk hm
  exact ⟨restrictTempered T, restrictTempered_homogeneous T (pole d m) hhom,
    restrictTempered_agrees T k hT⟩

/-- Coordinate jets obey the actual chain rule under test dilation. -/
theorem jet_testDilation (α : MultiIndex d) (a : ℝ) (ha : 0 < a) (φ : Schwartz ℂ d) :
    jet α (testDilation a ha φ) = ((a⁻¹ : ℝ) ^ order α : ℂ) * jet α φ := by
  simp only [jet_apply, partialDerivative, wordDerivative_apply_eq_iteratedFDeriv]
  have hc : (⇑(testDilation a ha φ) : Euclidean d → ℂ) = fun x => φ (a⁻¹ • x) := rfl
  rw [hc, iteratedFDeriv_comp_const_smul a⁻¹
    (φ.smooth ((derivativeWord α).length))]
  simp only [smul_zero, smul_apply,
    derivativeWord_length, Complex.real_smul, Complex.ofReal_pow]

/-- Source complex powers at a critical degree agree with the integer
Jacobian and jet factors. -/
theorem cpow_pole (a : ℝ) (ha : 0 < a) (d m : ℕ) :
    (a : ℂ) ^ (pole d m) = ((a : ℂ) ^ d)⁻¹ * ((a⁻¹ : ℝ) ^ m : ℂ) := by
  have hc : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  simp only [pole, sub_eq_add_neg, Complex.cpow_add _ _ hc, Complex.cpow_neg,
    Complex.cpow_natCast, Complex.ofReal_inv, inv_pow]

/-- Every Dirac derivative has exactly its source degree, with the same sign
convention as the residue. -/
theorem deltaDerivative_dilation (α : MultiIndex d) (a : ℝ) (ha : 0 < a) :
    dilation a ha (deltaDerivative α) = (a : ℂ) ^ (pole d (order α)) • deltaDerivative α := by
  ext φ
  change ((a : ℂ) ^ d)⁻¹ * deltaDerivative α (testDilation a ha φ) =
    (a : ℂ) ^ (pole d (order α)) * deltaDerivative α φ
  rw [deltaDerivative_apply, jet_testDilation, deltaDerivative_apply, cpow_pole a ha]
  ring

/-- Dilation is linear on the existing continuous Schwartz dual. -/
theorem dilation_add (a : ℝ) (ha : 0 < a) (T S : Tempered ℂ d) :
    dilation a ha (T + S) = dilation a ha T + dilation a ha S := by
  ext φ
  simp only [dilation, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, mul_add]

theorem deltaCombination_dilation (m : ℕ) (c : MultiIndex d → ℂ) (a : ℝ) (ha : 0 < a) :
    dilation a ha (deltaCombination m c) = (a : ℂ) ^ (pole d m) • deltaCombination m c := by
  classical
  ext φ
  change ((a : ℂ) ^ d)⁻¹ * deltaCombination m c (testDilation a ha φ) =
    (a : ℂ) ^ (pole d m) * deltaCombination m c φ
  simp only [deltaCombination, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have hs := congrArg (fun T : Tempered ℂ d => T φ) (deltaDerivative_dilation α a ha)
  change ((a : ℂ) ^ d)⁻¹ * deltaDerivative α (testDilation a ha φ) =
    (a : ℂ) ^ (pole d (order α)) * deltaDerivative α φ at hs
  rw [(mem_indices α m).mp hα] at hs
  linear_combination c α * hs

theorem deltaCombination_off_zero (m : ℕ) (c : MultiIndex d → ℂ)
    (φ : Schwartz ℂ d) (hφ : (0 : Euclidean d) ∉ tsupport φ) : deltaCombination m c φ = 0 := by
  classical
  simp [deltaCombination, deltaDerivative_apply, jet_eq_zero_of_off_zero φ hφ]

theorem homogeneous_add (u v : Distribution d) (lam : ℂ)
    (hu : Homogeneous u lam) (hv : Homogeneous v lam) : Homogeneous (u + v) lam := by
  intro a ha φ
  simp only [add_apply, mul_add]
  rw [hu a ha φ, hv a ha φ]

/-- Every exact-order delta combination gives an extension whenever a base
homogeneous extension exists; its coefficients are completely unrestricted. -/
theorem critical_perturbation (k : Euclidean d → ℂ) (m : ℕ)
    (u : Distribution d) (hu : IsHomogeneousExtension u k (pole d m))
    (c : MultiIndex d → ℂ) :
    IsHomogeneousExtension (u + restrictTempered (deltaCombination m c)) k (pole d m) ∧
      Represents (deltaCombination m c) ((u + restrictTempered (deltaCombination m c)) - u) := by
  constructor
  · constructor
    · exact homogeneous_add u _ (pole d m) hu.1
        (restrictTempered_homogeneous _ _ (deltaCombination_dilation m c))
    · intro φ hφ
      simp only [add_apply, restrictTempered_apply, deltaCombination_off_zero m c (testToSchwartz φ) hφ, add_zero]
      exact hu.2 φ hφ
  · intro φ
    simp only [sub_apply, add_apply, restrictTempered_apply]
    ring

/-- Agreement off zero for two extensions gives the point-support vanishing
condition needed in the remaining classification. No finite-order claim is
assumed here. -/
theorem difference_off_zero (u v : Distribution d) (k : Euclidean d → ℂ)
    (hu : AgreesOffZero u k) (hv : AgreesOffZero v k) :
    ∀ φ : CompactTest d, (0 : Euclidean d) ∉ tsupport φ → (v - u) φ = 0 := by
  intro φ hφ
  simp only [sub_apply, hu φ hφ, hv φ hφ, sub_self]

/-- Change of coordinates on compact tests, with continuity in the LF topology. -/
def precomposeTest {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F)
    (φ : TestFunction (⊤ : TopologicalSpace.Opens F) ℂ ⊤) :
    TestFunction (⊤ : TopologicalSpace.Opens E) ℂ ⊤ where
  toFun := φ ∘ e
  contDiff' := φ.contDiff.comp e.contDiff
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph e.toHomeomorph
  tsupport_subset' := Set.subset_univ _

def precomposeStep {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F)
    (K : TopologicalSpace.Compacts F) :
    ContDiffMapSupportedIn F ℂ ⊤ K →ₗ[ℂ]
      ContDiffMapSupportedIn E ℂ ⊤ (K.map e.symm e.symm.continuous) where
  toFun φ := .of_support_subset (φ.contDiff.comp e.contDiff) (by
    intro x hx
    refine ⟨e x, φ.tsupport_subset (subset_tsupport φ hx), ?_⟩
    exact e.symm_apply_apply x)
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

theorem continuous_precomposeStep {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F)
    (K : TopologicalSpace.Compacts F) : Continuous (precomposeStep e K) := by
  apply WithSeminorms.continuous_of_isBounded
    (ContDiffMapSupportedIn.withSeminorms ℂ F ℂ ⊤ K)
    (ContDiffMapSupportedIn.withSeminorms ℂ E ℂ ⊤ (K.map e.symm e.symm.continuous))
    (precomposeStep e K)
  apply Seminorm.IsBounded.of_real
  intro n
  refine ⟨{n}, ‖e.toContinuousLinearMap‖ ^ n, fun φ => ?_⟩
  simp only [Finset.sup_singleton]
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (by positivity) n _).mpr
  intro x _
  change ‖iteratedFDeriv ℝ n (φ ∘ e.toContinuousLinearMap) x‖ ≤ _
  rw [e.toContinuousLinearMap.iteratedFDeriv_comp_right φ.contDiff x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ
      (f := φ) (x := e x) (i := n)) (pow_nonneg (norm_nonneg _) n)

def precomposeTestCLM {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) :
    TestFunction (⊤ : TopologicalSpace.Opens F) ℂ ⊤ →L[ℂ]
      TestFunction (⊤ : TopologicalSpace.Opens E) ℂ ⊤ :=
  TestFunction.limitCLM ℂ (precomposeTest e)
    (fun K _ => (TestFunction.ofSupportedInCLM ℂ (Set.subset_univ _)).comp
      ⟨precomposeStep e K, continuous_precomposeStep e K⟩)
    (fun _ _ _ => by ext x; rfl)

/-- The equivalence is between the actual Euclidean and coordinate normed spaces. -/
def euclideanCoordinates : Euclidean d ≃L[ℝ] ExpandedFA.Distributions.Domain d :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

/-- Count the occurrences of each coordinate in an ordered derivative word. -/
def wordCounts (w : List (Fin d)) : MultiIndex d := fun i => w.count i

@[simp] theorem count_derivativeWord (α : MultiIndex d) (i : Fin d) :
    (derivativeWord α).count i = α i := by
  classical
  simp [derivativeWord, List.count_flatten, List.map_ofFn, List.sum_ofFn,
    List.count_replicate, Function.comp_def]

theorem derivativeWord_perm (w : List (Fin d)) :
    (derivativeWord (wordCounts w)).Perm w := by
  apply List.perm_iff_count.mpr
  intro i
  exact count_derivativeWord _ i

theorem order_wordCounts (w : List (Fin d)) : order (wordCounts w) = w.length := by
  rw [← derivativeWord_length, (derivativeWord_perm w).length_eq]

theorem wordDerivative_counts (w : List (Fin d)) :
    wordDerivative w = partialDerivative (wordCounts w) := by
  rw [partialDerivative, wordDerivative_eq_prod, wordDerivative_eq_prod]
  apply ((derivativeWord_perm w).symm.map _).prod_eq'
  apply List.pairwise_map.mpr
  apply List.pairwise_of_forall
  intro i j
  exact lineDerivOpCLM_commute _ _

theorem coordinate_delta_transport {n : ℕ} (w : Fin n → Fin d) (φ : CompactTest d) :
    ExpandedFA.Distributions.deltaCoordinateDerivative ℂ ⊤ 0 w
      (precomposeTest euclideanCoordinates.symm φ) =
    deltaDerivative (wordCounts (List.ofFn w)) (testToSchwartz φ) := by
  rw [ExpandedFA.Distributions.deltaCoordinateDerivative_apply, deltaDerivative_apply,
    order_wordCounts, List.length_ofFn, jet_apply, ← wordDerivative_counts,
    wordDerivative_apply_eq_iteratedFDeriv]
  change (-1 : ℂ) ^ n *
      iteratedFDeriv ℝ n (φ ∘ euclideanCoordinates.symm.toContinuousLinearMap) 0
        (fun j => ExpandedFA.Distributions.coordinateVector (w j)) = _
  rw [euclideanCoordinates.symm.toContinuousLinearMap.iteratedFDeriv_comp_right
    φ.contDiff 0 (by simp)]
  simp only [map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    List.get_eq_getElem, List.getElem_ofFn]
  congr 1
  have hh : ∀ (k : ℕ) (h : k = n),
      iteratedFDeriv ℝ k φ 0 (fun i : Fin k => basisVector (w (Fin.cast h i))) =
        iteratedFDeriv ℝ n φ 0 (fun i => basisVector (w i)) := by
    intro k h
    subst k
    rfl
  change iteratedFDeriv ℝ n φ 0 (fun i => basisVector (w i)) = _
  exact (hh _ (List.length_ofFn (f := w))).symm

/-- Every distribution annihilating off-zero tests has a finite expansion in
actual multi-index Dirac derivatives on Euclidean space. -/
theorem point_supported_expansion (u : Distribution d)
    (hu : ∀ φ : CompactTest d, (0 : Euclidean d) ∉ tsupport φ → u φ = 0) :
    ∃ (N : ℕ) (c : ExpandedFA.Distributions.JetIndex d N → ℂ),
      ∀ φ : CompactTest d, u φ =
        ∑ i, c i * deltaDerivative (wordCounts (List.ofFn i.2)) (testToSchwartz φ) := by
  classical
  let e : Euclidean d ≃L[ℝ] ExpandedFA.Distributions.Domain d := euclideanCoordinates
  let v : ExpandedFA.Distributions.ScalarDistribution ℂ ⊤ := u.comp (precomposeTestCLM e)
  have hv : ExpandedFA.Distributions.distributionSupport v ⊆ {0} := by
    intro x hx
    by_contra hx0
    apply hx.2
    refine Set.mem_sUnion.mpr ⟨{0}ᶜ, ⟨isClosed_singleton.isOpen_compl,
      Set.subset_univ _, ?_⟩, hx0⟩
    intro φ hφ
    apply hu (precomposeTest e φ)
    rw [notMem_tsupport_iff_eventuallyEq]
    have hz : (0 : ExpandedFA.Distributions.Domain d) ∉ tsupport φ :=
      fun h => hφ h (Set.mem_singleton 0)
    have he : Filter.Tendsto e (𝓝 0) (𝓝 0) := by simpa using e.continuous.tendsto 0
    exact (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto he
  obtain ⟨N, c, hc⟩ := ExpandedFA.Distributions.point_supported_distributions
    ℂ d ⊤ 0 (Set.mem_univ _) v hv
  refine ⟨N, c, fun φ => ?_⟩
  have hh := congrArg (fun v : ExpandedFA.Distributions.ScalarDistribution ℂ ⊤ =>
    v (precomposeTest e.symm φ)) hc
  have heq : precomposeTest e (precomposeTest e.symm φ) = φ := by
    ext x
    exact congrArg φ (e.symm_apply_apply x)
  change u (precomposeTest e (precomposeTest e.symm φ)) = _ at hh
  rw [heq] at hh
  simpa only [sum_apply, smul_apply, smul_eq_mul, e, coordinate_delta_transport] using hh

/-- Repeated coordinate words can be collected into the canonical coefficients. -/
theorem sum_delta_eq_combination {ι : Type*} [Fintype ι] (m : ℕ)
    (A : ι → MultiIndex d) (c : ι → ℂ) (hA : ∀ i, order (A i) = m) :
    (∑ i, c i • deltaDerivative (A i)) =
      deltaCombination m (fun α => ∑ i, if A i = α then c i else 0) := by
  classical
  ext φ
  simp only [deltaCombination, sum_apply, smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hi : A i ∈ indices d m := (mem_indices _ _).mpr (hA i)
  rw [Finset.sum_eq_single (A i)]
  · simp only [ite_true]
  · intro α _ hα
    simp [Ne.symm hα]
  · exact fun h => (h hi).elim

/-- A finite point-supported expansion, grouped by total derivative order. -/
theorem point_supported_decomposition (u : Distribution d)
    (hu : ∀ φ : CompactTest d, (0 : Euclidean d) ∉ tsupport φ → u φ = 0) :
    ∃ (N : ℕ) (T : Fin (N + 1) → Tempered ℂ d),
      (∀ j, ∃ c, T j = deltaCombination j.val c) ∧
      u = ∑ j, restrictTempered (T j) := by
  classical
  obtain ⟨N, c, hc⟩ := point_supported_expansion u hu
  let T (j : Fin (N + 1)) : Tempered ℂ d :=
    ∑ w : Fin j.val → Fin d, c ⟨j, w⟩ • deltaDerivative (wordCounts (List.ofFn w))
  refine ⟨N, T, fun j => ?_, ?_⟩
  · exact ⟨_, sum_delta_eq_combination j.val _ _
      (fun w => by rw [order_wordCounts, List.length_ofFn])⟩
  · ext φ
    rw [hc φ, Fintype.sum_sigma]
    simp only [T, sum_apply, smul_apply, smul_eq_mul, restrictTempered_apply]

/-- Dilation as a linear operator on the entire ordinary distribution dual. -/
def distributionDilation (a : ℝ) (ha : 0 < a) : Module.End ℂ (Distribution d) where
  toFun u := ((a : ℂ) ^ d)⁻¹ • u.comp
    (precomposeTestCLM (scalingEquiv a⁻¹ (inv_ne_zero ha.ne')))
  map_add' u v := by ext φ; simp
  map_smul' c u := by ext φ; simp [mul_left_comm]

@[simp] theorem distributionDilation_apply (a : ℝ) (ha : 0 < a)
    (u : Distribution d) (φ : CompactTest d) :
    distributionDilation a ha u φ = ((a : ℂ) ^ d)⁻¹ * u (compactTestDilation a ha φ) := rfl

theorem distributionDilation_restrict (a : ℝ) (ha : 0 < a) (T : Tempered ℂ d) :
    distributionDilation a ha (restrictTempered T) = restrictTempered (dilation a ha T) := by
  ext φ
  exact congrArg (fun ψ => ((a : ℂ) ^ d)⁻¹ * T ψ) (testToSchwartz_dilation a ha φ)

theorem homogeneous_sub (u v : Distribution d) (lam : ℂ)
    (hu : Homogeneous u lam) (hv : Homogeneous v lam) : Homogeneous (u - v) lam := by
  intro a ha φ
  simp only [sub_apply, mul_sub]
  rw [hu a ha φ, hv a ha φ]


def expLinear (z : Fin d → ℂ) : Euclidean d →L[ℝ] ℂ where
  toFun x := ∑ i, z i * (x i : ℂ)
  map_add' x y := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]
  cont := by fun_prop

@[simp] theorem expLinear_basis (z : Fin d → ℂ) (i : Fin d) :
    expLinear z (basisVector i) = z i := by
  classical
  simp [expLinear, basisVector, PiLp.single_apply, apply_ite]


theorem wordDerivative_exp_eventually (z : Fin d → ℂ) (φ : Schwartz ℂ d)
    (hφ : (φ : Euclidean d → ℂ) =ᶠ[𝓝 0] fun x => Complex.exp (expLinear z x))
    (w : List (Fin d)) :
    ((wordDerivative w φ : Schwartz ℂ d) : Euclidean d → ℂ) =ᶠ[𝓝 0]
      fun x => (w.map z).prod * Complex.exp (expLinear z x) := by
  induction w with
  | nil => simpa [wordDerivative] using hφ
  | cons i w ih =>
    have hD := ih.fderiv (𝕜 := ℝ)
    filter_upwards [hD] with x hx
    change fderiv ℝ (wordDerivative w φ) x (basisVector i) = _
    rw [hx, ((expLinear z).hasFDerivAt.cexp.const_mul _).fderiv]
    simp [List.prod_cons, mul_assoc, mul_comm, mul_left_comm]


@[simp] theorem prod_derivativeWord (z : Fin d → ℂ) (α : MultiIndex d) :
    ((derivativeWord α).map z).prod = ∏ i, z i ^ α i := by
  simp [derivativeWord, List.map_flatten, List.map_ofFn, List.prod_flatten,
    List.prod_ofFn, Function.comp_def]

def exponentialTest (z : Fin d → ℂ) : CompactTest d := by
  let b : ContDiffBump (0 : Euclidean d) := ⟨1, 2, by norm_num, by norm_num⟩
  refine ⟨fun x => (b x : ℂ) * Complex.exp (expLinear z x), ?_, ?_, Set.subset_univ _⟩
  · exact ((Complex.ofRealCLM.contDiff.comp b.contDiff).mul
      ((expLinear z).contDiff.cexp))
  · exact (b.hasCompactSupport.comp_left (by simp : Complex.ofReal 0 = 0)).mul_right

theorem exponentialTest_eventually (z : Fin d → ℂ) :
    ((testToSchwartz (exponentialTest z)) : Euclidean d → ℂ) =ᶠ[𝓝 0]
      fun x => Complex.exp (expLinear z x) := by
  let b : ContDiffBump (0 : Euclidean d) := ⟨1, 2, by norm_num, by norm_num⟩
  filter_upwards [b.eventuallyEq_one] with x hx
  change (b x : ℂ) * Complex.exp (expLinear z x) = _
  simp only [hx, Pi.one_apply, Complex.ofReal_one, one_mul]

@[simp] theorem jet_exponentialTest (z : Fin d → ℂ) (α : MultiIndex d) :
    jet α (testToSchwartz (exponentialTest z)) = ∏ i, z i ^ α i := by
  have h := (wordDerivative_exp_eventually z _ (exponentialTest_eventually z)
    (derivativeWord α)).eq_of_nhds
  simpa [jet_apply, partialDerivative] using h

theorem moments_of_residue_restrict_zero (k : Euclidean d → ℂ) (m : ℕ)
    (h : ∀ φ : CompactTest d, residue k m (testToSchwartz φ) = 0) :
    MomentsVanish k m := by
  classical
  let e : MultiIndex d ≃ (Fin d →₀ ℕ) := Finsupp.equivFunOnFinite.symm
  let P : MvPolynomial (Fin d) ℂ :=
    ∑ α ∈ indices d m, MvPolynomial.monomial (e α)
      (moment k α / (multiFactorial α : ℂ))
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro z
    have hz := h (exponentialTest z)
    rw [residue_eq_taylorCoefficient] at hz
    simp only [taylorCoefficient, sum_apply, smul_apply, smul_eq_mul,
      jet_exponentialTest] at hz
    simpa only [P, map_sum, MvPolynomial.eval_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      e, Finsupp.coe_equivFunOnFinite_symm, map_zero] using hz
  intro α hα
  have hcoeff := congrArg (fun Q : MvPolynomial (Fin d) ℂ => Q.coeff (e α)) hP
  have hi : α ∈ indices d m := (mem_indices α m).mpr hα
  have he : ∀ β, e β = e α ↔ β = α := fun β => e.injective.eq_iff
  simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, he,
    Finset.sum_ite_eq', hi, ite_true, AddMonoidAlgebra.coeff_zero] at hcoeff
  exact (div_eq_zero_iff).mp hcoeff |>.resolve_right (by exact_mod_cast multiFactorial_ne_zero α)


/-- A vector in the sum of eigenspaces has no nontrivial generalized-eigenvector part. -/
theorem eigen_sum_no_jordan {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} [Fintype ι]
    (f : Module.End ℂ V) (μ : ℂ) (v : ι → V) (a : ι → ℂ)
    (hv : ∀ i, f (v i) = a i • v i)
    (hw : f (f (∑ i, v i) - μ • ∑ i, v i) =
      μ • (f (∑ i, v i) - μ • ∑ i, v i)) :
    f (∑ i, v i) = μ • ∑ i, v i := by
  classical
  let p : Submodule ℂ V := ⨆ (z : ℂ) (_ : z ≠ μ), f.eigenspace z
  have hmem : f (∑ i, v i) - μ • ∑ i, v i ∈ p := by
    rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : a i = μ
    · simp [hv i, hi]
    · apply (le_iSup_of_le (a i) (le_iSup_of_le hi le_rfl) : f.eigenspace (a i) ≤ p)
      apply Module.End.mem_eigenspace_iff.mpr
      simp only [map_sub, map_smul, hv]
      module
  have h₁ : f (∑ i, v i) - μ • ∑ i, v i ∈ f.eigenspace μ :=
    Module.End.mem_eigenspace_iff.mpr hw
  have hz : f (∑ i, v i) - μ • ∑ i, v i = 0 := by
    exact (Submodule.disjoint_def.mp (f.eigenspaces_iSupIndep μ)) _ h₁ hmem
  exact sub_eq_zero.mp hz


/-- A finite point-supported expansion cannot carry a logarithmic dilation term. -/
theorem point_supported_no_anomaly (u R : Distribution d) (m : ℕ)
    (hu : ∀ φ : CompactTest d, (0 : Euclidean d) ∉ tsupport φ → u φ = 0)
    (hR : Homogeneous R (pole d m))
    (hscale : ∀ (a : ℝ) (ha : 0 < a),
      distributionDilation a ha u = (a : ℂ) ^ pole d m • (u - (Real.log a : ℂ) • R)) :
    R = 0 := by
  classical
  obtain ⟨N, T, hT, hsum⟩ := point_supported_decomposition u hu
  let a : ℝ := Real.exp 1
  have ha : 0 < a := Real.exp_pos 1
  let f : Module.End ℂ (Distribution d) := distributionDilation a ha
  let μ : ℂ := (a : ℂ) ^ pole d m
  have hμ : μ ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))
  have hRu : f R = μ • R := by ext φ; exact hR a ha φ
  have hfu : f u = μ • (u - R) := by
    simpa only [a, Real.log_exp, Complex.ofReal_one, one_smul] using hscale a ha
  have hw : f u - μ • u = -μ • R := by rw [hfu]; module
  have hw' : f (f u - μ • u) = μ • (f u - μ • u) := by
    rw [hw, map_smul, hRu]
    module
  have hdiag : ∀ j, f (restrictTempered (T j)) =
      (a : ℂ) ^ pole d j.val • restrictTempered (T j) := by
    intro j
    obtain ⟨c, hc⟩ := hT j
    change distributionDilation a ha _ = _
    rw [hc, distributionDilation_restrict, deltaCombination_dilation]
    ext φ
    rfl
  have hsimple := eigen_sum_no_jordan f μ (fun j => restrictTempered (T j))
    (fun j => (a : ℂ) ^ pole d j.val) hdiag (by simpa only [← hsum] using hw')
  rw [← hsum] at hsimple
  have hz : -μ • R = 0 := by rw [← hw, hsimple, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hμ)

/-- The source residue is an exact-order Dirac combination. -/
theorem residue_eq_deltaCombination (k : Euclidean d → ℂ) (m : ℕ) :
    residue k m = deltaCombination m
      (fun α => ((-1 : ℂ) ^ m / (multiFactorial α : ℂ)) * moment k α) := rfl

/-- Every homogeneous critical extension forces all of the spherical moments
of the critical order to vanish. Competing extensions are arbitrary distributions. -/
theorem critical_moments_necessary (k : Euclidean d → ℂ) (m : ℕ)
    (hk : SmoothHomogeneous k (pole d m)) (u : Distribution d)
    (hu : IsHomogeneousExtension u k (pole d m)) : MomentsVanish k m := by
  obtain ⟨F, hF, hscale⟩ := finite_part d k m hk
  let R := restrictTempered (residue k m)
  have hR : Homogeneous R (pole d m) := by
    apply restrictTempered_homogeneous
    rw [residue_eq_deltaCombination]
    exact deltaCombination_dilation _ _
  have hS : ∀ φ : CompactTest d, (0 : Euclidean d) ∉ tsupport φ →
      (u - restrictTempered F) φ = 0 :=
    difference_off_zero (restrictTempered F) u k (restrictTempered_agrees F k hF) hu.2
  have hSscale : ∀ (a : ℝ) (ha : 0 < a),
      distributionDilation a ha (u - restrictTempered F) =
        (a : ℂ) ^ pole d m • ((u - restrictTempered F) - (Real.log a : ℂ) • R) := by
    intro a ha
    ext φ
    have hf := congrArg (fun T : Tempered ℂ d => T (testToSchwartz φ)) (hscale a ha)
    change ((a : ℂ) ^ d)⁻¹ * F (testDilation a ha (testToSchwartz φ)) =
      (a : ℂ) ^ pole d m * (F (testToSchwartz φ) +
        (Real.log a : ℂ) * residue k m (testToSchwartz φ)) at hf
    simp only [distributionDilation_apply, sub_apply, restrictTempered_apply,
      testToSchwartz_dilation, smul_apply, smul_eq_mul, mul_sub]
    rw [hu.1 a ha φ, hf]
    change _ = _ - _ - (a : ℂ) ^ pole d m * ((Real.log a : ℂ) * residue k m (testToSchwartz φ))
    ring
  have hz : R = 0 := point_supported_no_anomaly _ R m hS hR hSscale
  apply moments_of_residue_restrict_zero
  intro φ
  exact congrArg (fun S : Distribution d => S φ) hz

/-- Existence at a critical degree is equivalent to precisely the source moments. -/
theorem critical_extension : Specs.ExpandedFA.PartIV.HomogeneousExtension.criticalExtensionType := by
  intro d k m hk
  constructor
  · rintro ⟨u, hu⟩
    exact critical_moments_necessary k m hk u hu
  · exact critical_extension_exists_of_moments k m hk


/-- Different critical degrees give different characters at the scale e. -/
theorem cpow_pole_exp_injective (d : ℕ) :
    Function.Injective (fun m : ℕ => (Real.exp 1 : ℂ) ^ pole d m) := by
  intro m n h
  have hc : (Real.exp 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos 1).ne'
  simp only [Complex.cpow_def_of_ne_zero hc, ← Complex.ofReal_log (Real.exp_pos 1).le,
    Real.log_exp, Complex.ofReal_one, one_mul] at h
  have he : pole d m = pole d n :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi (by simpa [pole] using Real.pi_pos)
      (by simpa [pole] using Real.pi_pos.le)
      (by simpa [pole] using Real.pi_pos) (by simpa [pole] using Real.pi_pos.le) h
  have hre := congrArg Complex.re he
  simp only [pole_re] at hre
  exact_mod_cast (by linarith : (m : ℝ) = (n : ℝ))

/-- A zero sum of vectors from distinct eigenspaces has zero components. -/
theorem eigensum_eq_zero_components {ι M : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℂ M] (f : Module.End ℂ M)
    (μ : ι → ℂ) (hμ : Function.Injective μ) (v : ι → M)
    (hv : ∀ i, f (v i) = μ i • v i) (h : ∑ i, v i = 0) : ∀ i, v i = 0 := by
  classical
  have hind := f.eigenspaces_iSupIndep.comp hμ
  have hh := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind
  exact fun i => hh Finset.univ v (fun i _ => (Module.End.mem_eigenspace_iff).mpr (hv i)) h i (Finset.mem_univ i)


/-- Applying an operator to an eigenvector sum isolates each component. -/
theorem eigen_sum_component_eq_zero {ι M : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℂ M] (f : Module.End ℂ M)
    (μ : ι → ℂ) (hμ : Function.Injective μ) (v : ι → M)
    (hv : ∀ i, f (v i) = μ i • v i) (lam : ℂ)
    (h : f (∑ i, v i) = lam • ∑ i, v i) :
    ∀ i, μ i ≠ lam → v i = 0 := by
  classical
  have hsum : ∑ i, (μ i - lam) • v i = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum]
    have hleft : ∑ i, μ i • v i = f (∑ i, v i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => (hv i).symm)
    rw [hleft, h, sub_self]
  have hh := eigensum_eq_zero_components f μ hμ (fun i => (μ i - lam) • v i)
    (fun i => by simp [map_smul, hv, smul_smul, mul_comm]) hsum
  intro i hi
  exact (smul_eq_zero.mp (hh i)).resolve_left (sub_ne_zero.mpr hi)

/-- Pole characters are distinct at every positive exponential scale. -/
theorem cpow_pole_exp_scale_injective (d : ℕ) (t : ℝ) (ht : 0 < t) :
    Function.Injective (fun m : ℕ => (Real.exp t : ℂ) ^ pole d m) := by
  intro m n h
  have hc : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  simp only [Complex.cpow_def_of_ne_zero hc, ← Complex.ofReal_log (Real.exp_pos t).le,
    Real.log_exp] at h
  have he : (t : ℂ) * pole d m = (t : ℂ) * pole d n :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi (by simpa [pole] using Real.pi_pos)
      (by simpa [pole] using Real.pi_pos.le)
      (by simpa [pole] using Real.pi_pos) (by simpa [pole] using Real.pi_pos.le) h
  have he' : pole d m = pole d n := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne') he
  have hre := congrArg Complex.re he'
  simp only [pole_re] at hre
  exact_mod_cast (by linarith : (m : ℝ) = (n : ℝ))

/-- A positive scale can distinguish any regular degree from every pole. -/
theorem exists_scale_separating_poles (d : ℕ) (lam : ℂ) (hlam : lam ∈ regularSet d) :
    ∃ t : ℝ, 0 < t ∧ ∀ m : ℕ, (Real.exp t : ℂ) ^ pole d m ≠ (Real.exp t : ℂ) ^ lam := by
  let t : ℝ := Real.pi * (|lam.im| + 1)⁻¹
  have ht : 0 < t := mul_pos Real.pi_pos (inv_pos.mpr (by positivity))
  refine ⟨t, ht, fun m h => ?_⟩
  have hc : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  simp only [Complex.cpow_def_of_ne_zero hc, ← Complex.ofReal_log (Real.exp_pos t).le,
    Real.log_exp] at h
  have habs : |t * lam.im| < Real.pi := by
    rw [abs_mul, abs_of_pos ht]
    dsimp [t]
    rw [mul_assoc, inv_mul_eq_div]
    exact (mul_lt_iff_lt_one_right Real.pi_pos).mpr ((div_lt_one (by positivity)).mpr (by linarith))
  have him : ((t : ℂ) * lam).im = t * lam.im := by simp
  have hlo : -Real.pi < ((t : ℂ) * lam).im := by
    rw [him]
    have := (abs_lt.mp habs).1
    linarith
  have hhi : ((t : ℂ) * lam).im ≤ Real.pi := by
    rw [him]
    have := (abs_lt.mp habs).2
    linarith
  have he : (t : ℂ) * pole d m = (t : ℂ) * lam :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi (by simpa [pole] using Real.pi_pos)
      (by simpa [pole] using Real.pi_pos.le) hlo hhi h
  exact hlam m (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne') he).symm


variable {d : ℕ}

/-- Every grouped point-supported summand is a genuine eigenvector. -/
theorem point_supported_summand_dilation (j : ℕ) (T : Tempered ℂ d)
    (hT : ∃ c, T = deltaCombination j c) (a : ℝ) (ha : 0 < a) :
    distributionDilation a ha (restrictTempered T) =
      (a : ℂ) ^ pole d j • restrictTempered T := by
  obtain ⟨c, rfl⟩ := hT
  rw [distributionDilation_restrict, deltaCombination_dilation]
  ext φ
  rfl

/-- A point-supported homogeneous distribution vanishes at every regular degree. -/
theorem point_supported_homogeneous_zero (u : Distribution d) (lam : ℂ)
    (hu : ∀ φ : CompactTest d, (0 : Euclidean d) ∉ tsupport φ → u φ = 0)
    (hhom : Homogeneous u lam) (hlam : lam ∈ regularSet d) : u = 0 := by
  classical
  obtain ⟨N, T, hT, hsum⟩ := point_supported_decomposition u hu
  obtain ⟨t, ht, hsep⟩ := exists_scale_separating_poles d lam hlam
  let a : ℝ := Real.exp t
  have ha : 0 < a := Real.exp_pos t
  let f : Module.End ℂ (Distribution d) := distributionDilation a ha
  have hdiag : ∀ j, f (restrictTempered (T j)) =
      (a : ℂ) ^ pole d j.val • restrictTempered (T j) :=
    fun j => point_supported_summand_dilation j.val (T j) (hT j) a ha
  have hscale : f u = (a : ℂ) ^ lam • u := by ext φ; exact hhom a ha φ
  have hh := eigen_sum_component_eq_zero f
    (fun j : Fin (N + 1) => (a : ℂ) ^ pole d j.val)
    ((cpow_pole_exp_scale_injective d t ht).comp Fin.val_injective)
    (fun j => restrictTempered (T j)) hdiag ((a : ℂ) ^ lam)
    (by simpa only [← hsum] using hscale)
  rw [hsum]
  exact Finset.sum_eq_zero (fun j _ => hh j (hsep j.val))

/-- At a critical degree precisely the delta derivatives of that order remain. -/
theorem point_supported_homogeneous_pole (u : Distribution d) (m : ℕ)
    (hu : ∀ φ : CompactTest d, (0 : Euclidean d) ∉ tsupport φ → u φ = 0)
    (hhom : Homogeneous u (pole d m)) :
    ∃ c : MultiIndex d → ℂ, Represents (deltaCombination m c) u := by
  classical
  obtain ⟨N, T, hT, hsum⟩ := point_supported_decomposition u hu
  let a : ℝ := Real.exp 1
  have ha : 0 < a := Real.exp_pos 1
  let f : Module.End ℂ (Distribution d) := distributionDilation a ha
  have hdiag : ∀ j, f (restrictTempered (T j)) =
      (a : ℂ) ^ pole d j.val • restrictTempered (T j) :=
    fun j => point_supported_summand_dilation j.val (T j) (hT j) a ha
  have hscale : f u = (a : ℂ) ^ pole d m • u := by ext φ; exact hhom a ha φ
  have hh := eigen_sum_component_eq_zero f
    (fun j : Fin (N + 1) => (a : ℂ) ^ pole d j.val)
    ((cpow_pole_exp_injective d).comp Fin.val_injective)
    (fun j => restrictTempered (T j)) hdiag ((a : ℂ) ^ pole d m)
    (by simpa only [← hsum] using hscale)
  have hvan : ∀ j : Fin (N + 1), j.val ≠ m → restrictTempered (T j) = 0 := by
    intro j hj
    apply hh j
    exact fun he => hj ((cpow_pole_exp_injective d) he)
  by_cases hm : m < N + 1
  · let j : Fin (N + 1) := ⟨m, hm⟩
    obtain ⟨c, hc⟩ := hT j
    refine ⟨c, ?_⟩
    have huT : u = restrictTempered (T j) := by
      rw [hsum]
      apply Finset.sum_eq_single j
      · intro i _ hij
        exact hvan i (fun he => hij (Fin.ext he))
      · simp
    intro φ
    rw [huT, hc]
    rfl
  · have hz : u = 0 := by
      rw [hsum]
      apply Finset.sum_eq_zero
      intro j _
      exact hvan j (by omega)
    refine ⟨0, ?_⟩
    intro φ
    simp [hz, deltaCombination]


/-- Uniqueness at every noncritical complex degree, in the full LF dual. -/
theorem regular_extension : Specs.ExpandedFA.PartIV.HomogeneousExtension.regularExtensionType := by
  intro d k lam hk hlam
  obtain ⟨u, hu⟩ := regular_extension_exists k lam hk hlam
  refine ⟨u, hu, fun v hv => ?_⟩
  apply sub_eq_zero.mp
  exact point_supported_homogeneous_zero (v - u) lam
    (difference_off_zero u v k hu.2 hv.2) (homogeneous_sub v u lam hv.1 hu.1) hlam

/-- The exact ambiguity consists of all, and only, order-m Dirac derivatives. -/
theorem critical_ambiguity : Specs.ExpandedFA.PartIV.HomogeneousExtension.criticalAmbiguityType := by
  intro d k m _ u hu
  constructor
  · intro v
    constructor
    · intro hv
      exact point_supported_homogeneous_pole (v - u) m
        (difference_off_zero u v k hu.2 hv.2)
        (homogeneous_sub v u (pole d m) hv.1 hu.1)
    · rintro ⟨c, hc⟩
      have hv : v = u + restrictTempered (deltaCombination m c) := by
        ext φ
        have hφ := hc φ
        simp only [sub_apply] at hφ
        simp only [add_apply, restrictTempered_apply]
        linear_combination hφ
      rw [hv]
      exact (critical_perturbation k m u hu c).1
  · intro c
    exact ⟨_, critical_perturbation k m u hu c⟩

end ExpandedFA.PartIV.HomogeneousExtension
