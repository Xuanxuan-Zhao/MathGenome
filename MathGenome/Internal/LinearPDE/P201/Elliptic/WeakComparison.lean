import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.WeakComparison
import MathGenome.Internal.LinearPDE.P201.Elliptic.Truncation
import MathGenome.Internal.LinearPDE.P201.Elliptic.WeakDirichlet

noncomputable section
set_option maxHeartbeats 800000
open Set TopologicalSpace MeasureTheory Filter
open scoped Matrix.Norms.Elementwise ENNReal InnerProductSpace
namespace P201.WeakComparison
open P201Specs.WeakComparison

/-- Multiplication by the actual bounded measurable zeroth-order coefficient. -/
def weightedUnderlying {n : ℕ} (Ω : Domain n) (c : Space n → ℝ)
    (hc : MemLp c ∞ (domainMeasure Ω)) : H ℝ Ω 1 →L[ℝ] P201.Lp ℝ Ω 2 :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL (domainMeasure Ω) ∞ 2 2
    (hc.toLp c)).comp (hUnderlying Ω 1)

theorem weightedUnderlying_ae {n : ℕ} (Ω : Domain n) (c : Space n → ℝ)
    (hc : MemLp c ∞ (domainMeasure Ω)) (u : H ℝ Ω 1) :
    (weightedUnderlying Ω c hc u : Space n → ℝ) =ᵐ[domainMeasure Ω]
      fun x => c x * hUnderlying Ω 1 u x := by
  exact ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
    (hc.toLp c) (hUnderlying Ω 1 u)).trans
      (hc.coeFn_toLp.mul Filter.EventuallyEq.rfl)

def reactionForm {n : ℕ} (Ω : Domain n) (c : Space n → ℝ)
    (hc : MemLp c ∞ (domainMeasure Ω)) :
    H ℝ Ω 1 →L[ℝ] H ℝ Ω 1 →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (weightedUnderlying Ω c hc) (hUnderlying Ω 1)

theorem reaction_integrable {n : ℕ} (Ω : Domain n) (c : Space n → ℝ)
    (hc : MemLp c ∞ (domainMeasure Ω)) (u v : H ℝ Ω 1) :
    Integrable (fun x => c x * hUnderlying Ω 1 u x * hUnderlying Ω 1 v x)
      (domainMeasure Ω) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (weightedUnderlying Ω c hc u)
    (hUnderlying Ω 1 v)).congr
  filter_upwards [weightedUnderlying_ae Ω c hc u] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

theorem reactionForm_apply {n : ℕ} (Ω : Domain n) (c : Space n → ℝ)
    (hc : MemLp c ∞ (domainMeasure Ω)) (u v : H ℝ Ω 1) :
    reactionForm Ω c hc u v =
      ∫ x, c x * hUnderlying Ω 1 u x * hUnderlying Ω 1 v x ∂domainMeasure Ω := by
  change inner ℝ (weightedUnderlying Ω c hc u) (hUnderlying Ω 1 v) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weightedUnderlying_ae Ω c hc u] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

/-- The full differential expression is a bounded bilinear form; in particular
it is continuous in the test in the full H¹ norm. -/
def form {n : ℕ} (Ω : Domain n) (A : P201Specs.Dirichlet.MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (c : Space n → ℝ)
    (hc : MemLp c ∞ (domainMeasure Ω)) :
    H ℝ Ω 1 →L[ℝ] H ℝ Ω 1 →L[ℝ] ℝ :=
  Dirichlet.form Ω A hA + reactionForm Ω c hc

theorem form_apply {n : ℕ} (Ω : Domain n) (A : P201Specs.Dirichlet.MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (c : Space n → ℝ)
    (hc : MemLp c ∞ (domainMeasure Ω)) (u v : H ℝ Ω 1) :
    form Ω A hA c hc u v = energy Ω A c u v := by
  simp only [form, add_apply, Dirichlet.form_apply,
    reactionForm_apply, energy]

/-- The canonical H¹ inclusion has the ordinary smooth test derivatives. -/
theorem testToH_derivative {n : ℕ} (Ω : Domain n) (φ : Test ℝ Ω) (j : Fin n) :
    (hFirstDerivative (Truncation.testToH Ω φ) j : Space n → ℝ)
      =ᵐ[domainMeasure Ω] fun x => gradient φ x j := by
  have hu : P102.U4.sobolevUnderlying (hToW ℝ Ω 1 (Truncation.testToH Ω φ)) =
      P102.U4.testToDomainLp Ω 2 φ := by
    change P102.U4.sobolevUnderlying ((hToW ℝ Ω 1) ((hToW ℝ Ω 1).symm _)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (P102.U4.zeroExtension_smoothInclusion Ω 1 2 φ).choose_spec
  have hd := P102.U4.SlabPoincareProof.smooth_sobolev_firstDerivative
    (hToW ℝ Ω 1 (Truncation.testToH Ω φ)) φ hu j
  change (P102.U4.SlabPoincareData.sobolevFirstDerivative
    (hToW ℝ Ω 1 (Truncation.testToH Ω φ)) j : Space n → ℝ) =ᵐ[_] _
  rw [hd]
  simpa only [P201.gradient, P201Specs.gradient, PiLp.toLp_apply,
    P201.coordinate, P201Specs.coordinate, P102.U4.testPartialWord_coe,
    P102.U4.partialWord] using
    P102.U4.testToDomainLp_ae Ω 2 (P102.U4.testPartialWord Ω [j] φ)

/-- Equality with the literal smooth-test integral, including integrability
needed to combine the diffusion and zeroth-order terms. -/
theorem energy_test {n : ℕ} (Ω : Domain n)
    (A : P201Specs.Dirichlet.MatrixField n) (hA : MemLp A ∞ (domainMeasure Ω))
    (c : Space n → ℝ) (hc : MemLp c ∞ (domainMeasure Ω))
    (u : H ℝ Ω 1) (φ : Test ℝ Ω) :
    energy Ω A c u (Truncation.testToH Ω φ) = testEnergy Ω A c u φ := by
  unfold energy P201Specs.ellipticEnergyForm testEnergy
  simp only [star_trivial]
  rw [← integral_add (Dirichlet.integrand_integrable Ω A hA u (Truncation.testToH Ω φ))
    (reaction_integrable Ω c hc u (Truncation.testToH Ω φ))]
  apply integral_congr_ae
  have hd := ae_all_iff.mpr (testToH_derivative Ω φ)
  filter_upwards [hd, Truncation.testToH_underlying Ω φ] with x hx hφ
  simp only [hx, hφ]

theorem test_extension : P201Specs.WeakComparison.TestExtensionStatement := by
  intro n Ω A hA c hc u hu w hw
  obtain ⟨φ, hφ, hlim⟩ := Truncation.nonnegative_density Ω w hw
  have ht := (form Ω A hA c hc u).continuous.continuousAt.tendsto.comp hlim
  have hle : ∀ k, form Ω A hA c hc u (Truncation.testToH Ω (φ k)) ≤ 0 := by
    intro k
    rw [form_apply, energy_test Ω A hA c hc]
    exact hu (φ k) (hφ k)
  rw [← form_apply Ω A hA c hc u w.val]
  exact le_of_tendsto ht (Eventually.of_forall hle)

/-- Truncation preserves the diffusion integral when the second factor is
u⁺, including for nonsymmetric matrix fields. -/
theorem diffusion_positivePart {n : ℕ} (Ω : Domain n)
    (A : P201Specs.Dirichlet.MatrixField n) (u : H ℝ Ω 1) :
    ellipticEnergyForm Ω A u (Truncation.positivePart Ω u) =
      ellipticEnergyForm Ω A (Truncation.positivePart Ω u)
        (Truncation.positivePart Ω u) := by
  apply integral_congr_ae
  have hd : ∀ᵐ x ∂domainMeasure Ω, ∀ j : Fin n,
      hFirstDerivative (Truncation.positivePart Ω u) j x =
        if 0 < hUnderlying Ω 1 u x then hFirstDerivative u j x else 0 :=
    ae_all_iff.mpr (Truncation.positivePart_derivative Ω u)
  filter_upwards [hd] with x hx
  by_cases h : 0 < hUnderlying Ω 1 u x
  · simp only [hx, ite_eq_left h]
  · simp only [hx, ite_eq_right h, star_zero, mul_zero, Finset.sum_const_zero]

theorem reaction_positivePart_nonneg {n : ℕ} (Ω : Domain n)
    (c : Space n → ℝ) (hc : ∀ᵐ x ∂domainMeasure Ω, 0 ≤ c x)
    (u : H ℝ Ω 1) :
    0 ≤ ∫ x, c x * hUnderlying Ω 1 u x *
      hUnderlying Ω 1 (Truncation.positivePart Ω u) x ∂domainMeasure Ω := by
  apply integral_nonneg_of_ae
  filter_upwards [hc, Truncation.positivePart_underlying Ω u] with x hx hp
  rw [hp]
  by_cases h : 0 ≤ hUnderlying Ω 1 u x
  · exact mul_nonneg (mul_nonneg hx h) (le_max_right _ _)
  · simp only [max_eq_right (le_of_not_ge h), mul_zero, Pi.zero_apply, le_refl]

theorem maximum : P201Specs.WeakComparison.MaximumStatement := by
  intro n hn Ω hΩ A hA lam hlam hEll c hc hcpos u hup hu
  let p : H10 ℝ Ω := ⟨Truncation.positivePart Ω u, hup⟩
  have hpnonneg : ∀ᵐ x ∂domainMeasure Ω, 0 ≤ hZeroUnderlying Ω p x := by
    filter_upwards [Truncation.positivePart_underlying Ω u] with x hx
    exact hx.symm ▸ le_max_right _ _
  have htest := test_extension Ω A hA c hc u hu p hpnonneg
  have hre := reaction_positivePart_nonneg Ω c hcpos u
  have hco := Dirichlet.form_gradient_coercive Ω A hA lam hEll p.val
  rw [Dirichlet.form_apply, ← diffusion_positivePart Ω A u] at hco
  have hgrad : hGradient p.val = 0 := by
    have hnonpos : lam * ‖hGradient p.val‖ ^ 2 ≤ 0 := by
      change ellipticEnergyForm Ω A u p.val + _ ≤ 0 at htest
      linarith
    have hsq : ‖hGradient p.val‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖hGradient p.val‖]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (hGradient p.val)])
  obtain ⟨C, _, hP⟩ := Dirichlet.full_norm_le_gradient hn Ω hΩ
  have hpzero : p.val = 0 := by
    have hh := hP p
    rw [hgrad, norm_zero, mul_zero] at hh
    exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
  have hpunder : hUnderlying Ω 1 (Truncation.positivePart Ω u) = 0 := by
    change hUnderlying Ω 1 p.val = 0
    rw [hpzero, map_zero]
  have hpformula := Truncation.positivePart_underlying Ω u
  rw [hpunder] at hpformula
  filter_upwards [hpformula, Lp.coeFn_zero ℝ 2 (domainMeasure Ω)] with x hx hz
  have hh : max (hUnderlying Ω 1 u x) 0 = 0 := hx.symm.trans hz
  exact (le_max_left _ _).trans hh.le

theorem energy_sub_left {n : ℕ} (Ω : Domain n)
    (A : P201Specs.Dirichlet.MatrixField n) (hA : MemLp A ∞ (domainMeasure Ω))
    (c : Space n → ℝ) (hc : MemLp c ∞ (domainMeasure Ω)) (u v w : H ℝ Ω 1) :
    energy Ω A c (u - v) w = energy Ω A c u w - energy Ω A c v w := by
  simp only [← form_apply Ω A hA c hc, map_sub, sub_apply]

theorem comparison : P201Specs.WeakComparison.ComparisonStatement := by
  intro n hn Ω hΩ A hA lam hlam hEll c hc hcpos f u v hup hu hv
  have hsub : Subsolution Ω A c (fun _ => 0) (u - v) := by
    intro φ hφ
    rw [← energy_test Ω A hA c hc, energy_sub_left Ω A hA c hc,
      energy_test Ω A hA c hc, energy_test Ω A hA c hc]
    exact sub_nonpos.mpr ((hu φ hφ).trans (hv φ hφ))
  have hmax := maximum hn Ω hΩ A hA lam hlam hEll c hc hcpos (u - v) hup hsub
  rw [map_sub] at hmax
  filter_upwards [hmax, Lp.coeFn_sub (hUnderlying Ω 1 u) (hUnderlying Ω 1 v)]
    with x hx hs
  exact sub_nonpos.mp (by simpa only [hs, Pi.sub_apply] using hx)

theorem ordered_trace : P201Specs.WeakComparison.OrderedTraceStatement := by
  intro m Ω hΩ T hT A hA lam hlam hEll c hc hcpos f u v huv hu hv
  exact comparison (by omega) Ω (Dirichlet.lipschitz_isBounded Ω hΩ)
    A hA lam hlam hEll c hc hcpos f u v
    (Truncation.ordered_trace Ω hΩ T hT u v huv) hu hv

end P201.WeakComparison
