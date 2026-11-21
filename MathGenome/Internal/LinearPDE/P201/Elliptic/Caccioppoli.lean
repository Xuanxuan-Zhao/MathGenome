import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.Caccioppoli
import MathGenome.Internal.LinearPDE.P201.Common.Cutoff
import MathGenome.Internal.LinearPDE.P201.Common.InteriorTesting
import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzExtension
import MathGenome.Internal.FourierSobolev.P102.Trace.OrdinaryTrace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace P201.Caccioppoli

/-- Young's inequality with exactly the constants needed for the source term
coefficient 2/lam after absorption. -/
lemma crossTerm_young (M lam a b : ℝ) (hlam : 0 < lam) :
    2 * M * a * b ≤ lam / 2 * a ^ 2 + (2 * M ^ 2 / lam) * b ^ 2 := by
  have hs := sq_nonneg (lam * a - 2 * M * b)
  apply (mul_le_mul_iff_right₀ hlam).mp
  field_simp
  nlinarith

/-- Absorption of the cross term preserves the exact source coefficient. -/
lemma absorb_energy (M lam E B S : ℝ) (hlam : 0 < lam)
    (h : lam * E ≤ S + (lam / 2 * E + (2 * M ^ 2 / lam) * B)) :
    E ≤ (4 * M ^ 2 / lam ^ 2) * B + (2 / lam) * S := by
  apply (mul_le_mul_iff_right₀ hlam).mp
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  field_simp
  field_simp at h
  nlinarith

/-- Compact support can always be surrounded by a relatively compact open set,
including when the original domain is unbounded or the support is empty. -/
lemma exists_cutoff_neighborhood {n : ℕ} (Ω V : P201Specs.Domain n)
    (η : P201Specs.Test ℝ Ω) (hV : tsupport η ⊆ V) :
    ∃ U : P201Specs.Domain n, tsupport η ⊆ U ∧
      IsCompact (closure (U : Set (P201Specs.Space n))) ∧
      closure (U : Set (P201Specs.Space n)) ⊆ (Ω : Set (P201Specs.Space n)) ∩ V := by
  obtain ⟨U, hU, hηU, hUV, hUc⟩ := exists_open_between_and_isCompact_closure
    η.hasCompactSupport (Ω.isOpen.inter V.isOpen) (subset_inter η.tsupport_subset hV)
  exact ⟨⟨U, hU⟩, hηU, hUc, hUV⟩

/-- The H¹₀ definition gives approximation in the full Hilbert norm, on any
open set. Every approximant is identified by its L² class with a smooth test. -/
lemma exists_smooth_approximation {n : ℕ} (Ω : P201Specs.Domain n)
    (v : P201Specs.H10 ℝ Ω) :
    ∃ (φ : ℕ → P201Specs.Test ℝ Ω) (w : ℕ → P201Specs.H ℝ Ω 1),
      (∀ k, P201Specs.hUnderlying Ω 1 (w k) = P102.U4.testToDomainLp Ω 2 (φ k)) ∧
      Tendsto w atTop (𝓝 v.val) := by
  have hv : v.val ∈ closure
      ((P102.U4.smoothSobolevSubmodule ℝ Ω 1 2).comap
        (P201Specs.hToW ℝ Ω 1).toLinearMap : Set (P201Specs.H ℝ Ω 1)) := v.property
  obtain ⟨w, hw, ht⟩ := mem_closure_iff_seq_limit.mp hv
  choose φ hφ using hw
  exact ⟨φ, w, fun k => (hφ k).symm, ht⟩

open P201Specs.Caccioppoli
open P102.Sobolev.Extension

lemma hGradient_ae {n : ℕ} {Ω : Domain n} (w : H ℝ Ω 1) :
    (hGradient w : Space n → Space n) =ᵐ[domainMeasure Ω]
      (fun x => WithLp.toLp 2 (fun i => hFirstDerivative w i x)) :=
  MemLp.coeFn_toLp _

/-- A smooth compact cutoff of a local H¹ function is in global H¹₀.
This constructs its class and every derivative; it assumes no global H¹ norm
for the original function. -/
lemma local_test_product {n : ℕ} (Ω : Domain n) (u : Space n → ℝ)
    (g : Space n → Space n) (hu : IsLocalH1 Ω u g) (a : Test ℝ Ω) :
    ∃ v : H10 ℝ Ω,
      (hZeroUnderlying Ω v : Space n → ℝ) =ᵐ[domainMeasure Ω]
        (fun x => a x * u x) ∧
      (hGradient v.val : Space n → Space n) =ᵐ[domainMeasure Ω]
        (fun x => a x • g x + u x • gradient a x) := by
  obtain ⟨U, haU, hUc, hUΩ⟩ := exists_cutoff_neighborhood Ω Ω a a.tsupport_subset
  have hUΩ' : closure (U : Set (Space n)) ⊆ Ω := fun x hx => (hUΩ hx).1
  obtain ⟨w, hwu, hwg⟩ := hu U hUc hUΩ'
  let aw : P102.U4.WholeTests n ℝ := ⟨a, a.contDiff, a.hasCompactSupport, subset_univ _⟩
  have ha : tsupport aw ∩ (Ω : Set (Space n)) ⊆ U := fun x hx => haU hx.1
  let z := relativeCutoffSobolev U Ω 2 aw ha (hToW ℝ U 1 w)
  let v := (hToW ℝ Ω 1).symm z
  have hvu : (hUnderlying Ω 1 v : Space n → ℝ) =ᵐ[domainMeasure Ω]
      (fun x => a x * u x) := by
    have hz := relativeCutoffSobolev_underlying_ae U Ω 2 aw ha (hToW ℝ U 1 w)
    have hw := (ae_restrict_iff' U.isOpen.measurableSet).mp hwu
    filter_upwards [hz, ae_restrict_of_ae hw] with x hx hxw
    change P102.U4.sobolevUnderlying z x = _
    rw [hx]
    by_cases hxU : x ∈ U
    · rw [show P102.U4.sobolevUnderlying (hToW ℝ U 1 w) x = u x from hxw hxU]
      rfl
    · have hz : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxU (haU h))
      change a x * _ = a x * _
      simp [hz]
  have hvc : P102.U4.HasCompactSupportIn (P102.U4.sobolevUnderlying z) := by
    refine ⟨⟨tsupport a, a.hasCompactSupport⟩, a.tsupport_subset, ?_⟩
    filter_upwards [hvu] with x hx hxa
    change P102.U4.sobolevUnderlying z x = _ at hx
    rw [hx, image_eq_zero_of_notMem_tsupport hxa, zero_mul]
  have hvzero : v ∈ P201Specs.hZeroSubmodule ℝ Ω := by
    rw [hZeroClosureBridge]
    change hToW ℝ Ω 1 v ∈ P102.U4.sobolevZeroSubmodule ℝ Ω 1 2
    simpa only [v, ContinuousLinearEquiv.apply_symm_apply] using
      P102.Trace.Ordinary.mem_sobolevZero_of_compactSupport (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z hvc
  refine ⟨⟨v, hvzero⟩, hvu, ?_⟩
  have hwj (j : Fin n) : (hFirstDerivative w j : Space n → ℝ) =ᵐ[domainMeasure U]
      (fun x => g x j) := by
    filter_upwards [hGradient_ae w, hwg] with x hx hy
    exact congrArg (fun y : Space n => y j) (hx.symm.trans hy)
  have hj (j : Fin n) : (hFirstDerivative v j : Space n → ℝ) =ᵐ[domainMeasure Ω]
      (fun x => a x * g x j + u x * gradient a x j) := by
    have hwd := (ae_restrict_iff' U.isOpen.measurableSet).mp (hwj j)
    have hwu' := (ae_restrict_iff' U.isOpen.measurableSet).mp hwu
    have he : hFirstDerivative v j = relativeZeroLp U Ω 2
        (P102.U4.firstWeakDerivative
          (domainTestMulSobolev U 2 aw (hToW ℝ U 1 w)) j) := rfl
    rw [he, domainTestMulSobolev_derivative]
    have hz := relativeZeroLp_ae U Ω 2
      (domainTestMul U 2 (P102.U4.testPartialWord ⊤ [j] aw)
        (P102.U4.sobolevUnderlying (hToW ℝ U 1 w)) +
        domainTestMul U 2 aw (P102.U4.firstWeakDerivative (hToW ℝ U 1 w) j))
    have hm := (ae_restrict_iff' U.isOpen.measurableSet).mp
      (domainTestMul_ae U 2 (P102.U4.testPartialWord ⊤ [j] aw)
        (P102.U4.sobolevUnderlying (hToW ℝ U 1 w)))
    have hm' := (ae_restrict_iff' U.isOpen.measurableSet).mp
      (domainTestMul_ae U 2 aw (P102.U4.firstWeakDerivative (hToW ℝ U 1 w) j))
    have hadd := (ae_restrict_iff' U.isOpen.measurableSet).mp
      (Lp.coeFn_add
        (domainTestMul U 2 (P102.U4.testPartialWord ⊤ [j] aw)
          (P102.U4.sobolevUnderlying (hToW ℝ U 1 w)))
        (domainTestMul U 2 aw (P102.U4.firstWeakDerivative (hToW ℝ U 1 w) j)))
    filter_upwards [hz, ae_restrict_of_ae hm, ae_restrict_of_ae hm',
      ae_restrict_of_ae hadd, ae_restrict_of_ae hwd, ae_restrict_of_ae hwu']
        with x hx hx1 hx2 hxa hxd hxu
    rw [hx]
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU, hxa hxU, Pi.add_apply, hx1 hxU, hx2 hxU]
      change P102.U4.testPartialWord ⊤ [j] aw x * hUnderlying U 1 w x +
        a x * hFirstDerivative w j x = _
      rw [hxu hxU, hxd hxU]
      have hder := congrFun (P102.U4.testPartialWord_coe ⊤ [j] aw) x
      change P102.U4.testPartialWord ⊤ [j] aw x = gradient a x j at hder
      rw [hder]
      ring
    · rw [indicator_of_notMem hxU]
      have hxout : x ∉ tsupport a := fun h => hxU (haU h)
      have hax := image_eq_zero_of_notMem_tsupport hxout
      have hdax := fderiv_of_notMem_tsupport (𝕜 := ℝ) hxout
      simp [hax, hdax]
  filter_upwards [hGradient_ae v, ae_all_iff.mpr hj] with x hx hjx
  rw [hx]
  apply PiLp.ext
  intro j
  exact hjx j

/-- Squaring a test preserves its compact interior support. -/
def squareTest {n : ℕ} {Ω : Domain n} (η : Test ℝ Ω) : Test ℝ Ω :=
  ⟨fun x => η x * η x, η.contDiff.mul η.contDiff,
    η.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans η.tsupport_subset⟩

lemma gradient_squareTest {n : ℕ} {Ω : Domain n} (η : Test ℝ Ω) (x : Space n) :
    gradient (squareTest η) x = (2 * η x) • gradient η x := by
  apply PiLp.ext
  intro j
  change fderiv ℝ ((η : Space n → ℝ) * (η : Space n → ℝ)) x (coordinate n j) = _
  rw [fderiv_mul (η.contDiff.differentiable (by simp) x)
    (η.contDiff.differentiable (by simp) x)]
  simp only [add_apply, smul_apply,
    smul_eq_mul, PiLp.smul_apply, gradient, P201Specs.gradient]
  ring

/-- The full compact-support/approximation part of the source proposition. -/
theorem cutoffAdmissibility : P201Specs.Caccioppoli.CutoffAdmissibilityStatement := by
  intro n hn Ω u g hu η
  obtain ⟨v, hv, hd⟩ := local_test_product Ω u g hu (squareTest η)
  refine ⟨v, ?_, ?_, exists_smooth_approximation Ω v⟩
  · filter_upwards [hv] with x hx
    change hZeroUnderlying Ω v x = η x * η x * u x at hx
    simpa only [pow_two] using hx
  · filter_upwards [hd] with x hx
    rw [hx, gradient_squareTest]
    simp only [squareTest, pow_two, smul_smul]
    congr 1
    congr 1
    ring

/-- The upstream density theorem specialized to an L² source and actual
integral weak tests, on any open set. -/
lemma testing_L2 {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (F : MeasureTheory.Lp (Space n) 2 (domainMeasure Ω)) (f : Lp ℝ Ω 2)
    (h : ∀ φ : Test ℝ Ω, weakNegativeDivergence Ω F φ = ∫ x in Ω, f x * φ x)
    (v : H10 ℝ Ω) :
    (∫ x in Ω, inner ℝ (F x) (hGradient v.val x)) =
      ∫ x in Ω, f x * hZeroUnderlying Ω v x := by
  rw [← pivotPairing]
  apply P201.InteriorTesting.energyTesting hn Ω F (pivot Ω f)
  intro φ w hw
  rw [P201.InteriorTesting.negativeDivergenceDistribution_pairing]
  change weakNegativeDivergence Ω F φ = _
  rw [h, pivotPairing]
  apply integral_congr_ae
  filter_upwards [show (hZeroUnderlying Ω w : Space n → ℝ) =ᵐ[domainMeasure Ω] φ from by
    rw [hw]; exact P102.U4.testToDomainLp_ae Ω 2 φ] with x hx
  rw [hx]

/-- Pointwise coercivity and the operator norm suffice; the matrix need not
be symmetric. This form avoids separately integrating the expanded cross term. -/
lemma pointwise_energy {n : ℕ} (A : Space n →L[ℝ] Space n)
    (M lam a b : ℝ) (ξ d : Space n) (_hM : 0 ≤ M) (hlam : 0 < lam)
    (hA : ‖A‖ ≤ M) (hell : lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ) :
    lam / 2 * (a ^ 2 * ‖ξ‖ ^ 2) ≤
      (2 * M ^ 2 / lam) * (‖d‖ ^ 2 * |b| ^ 2) +
        inner ℝ (A ξ) ((a ^ 2) • ξ + (2 * a * b) • d) := by
  have hnorm : ‖A ξ‖ ≤ M * ‖ξ‖ :=
    (A.le_opNorm ξ).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg ξ))
  have hc : |2 * a * b * inner ℝ (A ξ) d| ≤
      2 * M * (|a| * ‖ξ‖) * (|b| * ‖d‖) := by
    calc
      _ = 2 * |a| * |b| * |inner ℝ (A ξ) d| := by rw [abs_mul, abs_mul, abs_mul]; norm_num
      _ ≤ 2 * |a| * |b| * (‖A ξ‖ * ‖d‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
      _ ≤ 2 * |a| * |b| * ((M * ‖ξ‖) * ‖d‖) := by gcongr
      _ = _ := by ring
  have hy := crossTerm_young M lam (|a| * ‖ξ‖) (|b| * ‖d‖) hlam
  simp only [mul_pow, sq_abs] at hy
  have hl := mul_le_mul_of_nonneg_left hell (sq_nonneg a)
  have hn := neg_abs_le (2 * a * b * inner ℝ (A ξ) d)
  simp only [inner_add_right, real_inner_smul_right, sq_abs]
  nlinarith

/-- Integration followed by absorption; all integrability premises are
explicit, so the zero convention for nonintegrable Bochner integrals is unused. -/
lemma integrated_energy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (M lam : ℝ) (hlam : 0 < lam) (E B Q S : X → ℝ)
    (hE : Integrable E μ) (hB : Integrable B μ)
    (hQ : Integrable Q μ) (hS : Integrable S μ)
    (he : ∀ᵐ x ∂μ, lam / 2 * E x ≤ (2 * M ^ 2 / lam) * B x + Q x)
    (hweak : (∫ x, Q x ∂μ) = ∫ x, S x ∂μ) :
    (∫ x, E x ∂μ) ≤ (4 * M ^ 2 / lam ^ 2) * (∫ x, B x ∂μ) +
      (2 / lam) * (∫ x, |S x| ∂μ) := by
  have hi := integral_mono_ae (hE.const_mul (lam / 2))
    ((hB.const_mul (2 * M ^ 2 / lam)).add hQ) he
  change (∫ x, lam / 2 * E x ∂μ) ≤ ∫ x, (2 * M ^ 2 / lam) * B x + Q x ∂μ at hi
  rw [integral_add (hB.const_mul _) hQ, integral_const_mul, integral_const_mul, hweak] at hi
  have hs := integral_mono_ae hS hS.abs (Eventually.of_forall fun x => le_abs_self (S x))
  apply absorb_energy M lam _ _ _ hlam
  linarith

lemma gradient_zero_on_compl {n : ℕ} {Ω : Domain n} (φ : Test ℝ Ω)
    {x : Space n} (hx : x ∉ Ω) : gradient φ x = 0 := by
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx (φ.tsupport_subset h))
  apply PiLp.ext
  intro j
  simp [hd]

/-- Restricting the equation to an arbitrary open subdomain uses the actual
same ambient tests and their compact support. -/
lemma restrict_testing {n : ℕ} (Ω U : Domain n) (hUΩ : U ≤ Ω)
    (F : Space n → Space n) (f : Space n → ℝ)
    (h : ∀ φ : Test ℝ Ω, weakNegativeDivergence Ω F φ = ∫ x in Ω, f x * φ x)
    (φ : Test ℝ U) :
    weakNegativeDivergence U F φ = ∫ x in U, f x * φ x := by
  let ψ : Test ℝ Ω := ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hUΩ⟩
  have hflux (V : Domain n) (θ : Test ℝ V) :
      weakNegativeDivergence V F θ = ∫ x, inner ℝ (F x) (gradient θ x) := by
    change (∫ x in V, inner ℝ (F x) (gradient θ x)) = _
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [gradient_zero_on_compl θ hx, inner_zero_right]
  calc
    weakNegativeDivergence U F φ = ∫ x, inner ℝ (F x) (gradient φ x) := hflux U φ
    _ = weakNegativeDivergence Ω F ψ := (hflux Ω ψ).symm
    _ = ∫ x in Ω, f x * ψ x := h ψ
    _ = ∫ x, f x * φ x := P102.U4.setIntegral_mul_test Ω f ψ
    _ = ∫ x in U, f x * φ x := (P102.U4.setIntegral_mul_test U f φ).symm

lemma test_gradient_memLp {n : ℕ} {Ω : Domain n} (φ : Test ℝ Ω)
    (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ] (p : ℝ≥0∞) : MemLp (gradient φ) p μ := by
  apply MemLp.of_eval_piLp
  intro j
  have h := (P102.U4.testPartialWord Ω [j] φ).continuous.memLp_of_hasCompactSupport
    (μ := μ) (p := p) (P102.U4.testPartialWord Ω [j] φ).hasCompactSupport
  change MemLp (fun x => fderiv ℝ φ x (coordinate n j)) p μ
  convert h using 1
  exact (P102.U4.testPartialWord_coe Ω [j] φ).symm

/-- Passing from the local estimate to the original domain uses compact
support, so Ω is allowed to be unbounded. -/
lemma setIntegral_eq_of_support {n : ℕ} (Ω U : Domain n) (η : Test ℝ Ω)
    (hηU : tsupport η ⊆ U) (k : Space n → ℝ)
    (hk : ∀ x, x ∉ tsupport η → k x = 0) :
    (∫ x in Ω, k x) = ∫ x in U, k x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => hk x (fun h => hx (η.tsupport_subset h))),
    setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => hk x (fun h => hx (hηU h)))]

/-- Caccioppoli's estimate for a local weak solution, with no symmetry,
bounded-domain, or global-H¹ premise. -/
theorem caccioppoli : P201Specs.Caccioppoli.CaccioppoliStatement := by
  intro n hn Ω A u f g hu hf hweak η M lam hM hlam hbounds
  obtain ⟨V, hηV, hAV⟩ := hbounds
  obtain ⟨U, hηU, hUc, hUΩV⟩ := exists_cutoff_neighborhood Ω V η hηV
  have hUΩ : U ≤ Ω := fun x hx => (hUΩV (subset_closure hx)).1
  have hUV : U ≤ V := fun x hx => (hUΩV (subset_closure hx)).2
  have hAU : ∀ᵐ x ∂domainMeasure U,
      ‖A x‖ ≤ M ∧ ∀ ξ : Space n, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ :=
    ae_restrict_of_ae_restrict_of_subset hUV hAV
  have hUcΩ : closure (U : Set (Space n)) ⊆ Ω := fun x hx => (hUΩV hx).1
  obtain ⟨w, hwu, hwg⟩ := hu U hUc hUcΩ
  have huLp : MemLp u 2 (domainMeasure U) := MemLp.ae_eq hwu (Lp.memLp (hUnderlying U 1 w))
  have hgLp : MemLp g 2 (domainMeasure U) := MemLp.ae_eq hwg (Lp.memLp (hGradient w))
  have hfLp := hf U hUc hUcΩ
  have hFLp : MemLp (fun x => A x (g x)) 2 (domainMeasure U) := by
    apply hgLp.of_le_mul ((hweak.1.mono_set hUΩ).aestronglyMeasurable)
    filter_upwards [hAU] with x hx
    exact ((A x).le_opNorm (g x)).trans
      (mul_le_mul_of_nonneg_right hx.1 (norm_nonneg _))
  let F := hFLp.toLp (fun x => A x (g x))
  let fU := hfLp.toLp f
  have hF : (F : Space n → Space n) =ᵐ[domainMeasure U] (fun x => A x (g x)) := hFLp.coeFn_toLp
  have hfu : (fU : Space n → ℝ) =ᵐ[domainMeasure U] f := hfLp.coeFn_toLp
  let ηU : Test ℝ U := ⟨η, η.contDiff, η.hasCompactSupport, hηU⟩
  have huU : IsLocalH1 U u g := by
    intro W hWc hWU
    exact hu W hWc (hWU.trans hUΩ)
  obtain ⟨v, hv, hdv, _⟩ := cutoffAdmissibility hn U u g huU ηU
  have htest : ∀ φ : Test ℝ U,
      weakNegativeDivergence U F φ = ∫ x in U, fU x * φ x := by
    intro φ
    calc
      weakNegativeDivergence U F φ = weakNegativeDivergence U (fun x => A x (g x)) φ := by
        apply integral_congr_ae
        filter_upwards [hF] with x hx
        rw [hx]
      _ = ∫ x in U, f x * φ x := restrict_testing Ω U hUΩ _ _ hweak.2.2 φ
      _ = ∫ x in U, fU x * φ x := by
        apply integral_congr_ae
        filter_upwards [hfu] with x hx
        rw [hx]
  have heq := testing_L2 hn U F fU htest v
  have hηLp : MemLp η ∞ (domainMeasure U) :=
    η.continuous.memLp_of_hasCompactSupport η.hasCompactSupport
  have hdηLp : MemLp (gradient η) ∞ (domainMeasure U) := test_gradient_memLp η _ _
  have hE : IntegrableOn (fun x => η x ^ 2 * ‖g x‖ ^ 2) U := by
    change Integrable _ (domainMeasure U)
    simpa only [Pi.mul_apply, mul_pow] using (hηLp.mul hgLp.norm).integrable_sq
  have hB : IntegrableOn (fun x => ‖gradient η x‖ ^ 2 * |u x| ^ 2) U := by
    change Integrable _ (domainMeasure U)
    simpa only [Pi.mul_apply, mul_pow, Real.norm_eq_abs] using (hdηLp.norm.mul huLp.norm).integrable_sq
  have hQ : IntegrableOn (fun x => inner ℝ (F x) (hGradient v.val x)) U := L2.integrable_inner F _
  have hS : IntegrableOn (fun x => fU x * hZeroUnderlying U v x) U :=
    (Lp.memLp fU).integrable_mul (Lp.memLp (hZeroUnderlying U v))
  have hest := integrated_energy (domainMeasure U) M lam hlam
    (fun x => η x ^ 2 * ‖g x‖ ^ 2)
    (fun x => ‖gradient η x‖ ^ 2 * |u x| ^ 2)
    (fun x => inner ℝ (F x) (hGradient v.val x))
    (fun x => fU x * hZeroUnderlying U v x) hE hB hQ hS (by
      filter_upwards [hF, hdv, hAU] with x hx hd hAx
      rw [hx, hd]
      exact pointwise_energy (A x) M lam (η x) (u x) (g x) (gradient η x)
        hM hlam hAx.1 (hAx.2 (g x))) heq
  have hs : (∫ x in U, |fU x * hZeroUnderlying U v x|) =
      ∫ x in U, |η x ^ 2 * f x * u x| := by
    apply integral_congr_ae
    filter_upwards [hfu, hv] with x hx hy
    rw [hx, hy]
    congr 1
    change f x * (η x ^ 2 * u x) = _
    ring
  rw [hs] at hest
  rw [setIntegral_eq_of_support Ω U η hηU _ (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx]; simp),
    setIntegral_eq_of_support Ω U η hηU _ (fun x hx => by
      have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hx
      have hgrad : P201Specs.gradient η x = 0 := by
        apply PiLp.ext; intro j; simp [hd]
      rw [hgrad]; simp),
    setIntegral_eq_of_support Ω U η hηU _ (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx]; simp)]
  exact hest

end P201.Caccioppoli
