import Specs.ExpandedFA.PartV.VolterraResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.VolterraFactorial
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Ring

/-!
Full-interval inverse and iteration conclusions of paper.tex:21872–21907,
`fa2:p5:volterra-resolvent`. The accepted factorial estimate supplies an
exponential majorant for every scalar parameter, with no smallness assumption.
Summing the powers produces a two-sided inverse in operator norm. The affine
iteration error is the nth power applied to its initial error; factorial decay
therefore gives convergence in the supremum norm and uniformly on the interval.

The spectral proof uses the inverse at the reciprocal of each nonzero scalar.
Evaluation at the left endpoint annihilates the range, so a nonzero constant
function witnesses nonsurjectivity and puts zero in the complex spectrum.
We work on any [a,b], including a=b, and retain zero state spaces for all
inverse and solvability conclusions. The continuous resolvent kernel is a
separate allocated obligation, `app_volterra_resolvent_kernel`.
-/

set_option maxHeartbeats 800000

noncomputable section
open Filter
open scoped Topology
namespace ExpandedFA.PartV

/-- Power and norm identities for scalar multiples of an endomorphism. -/
theorem scaled_operator_power {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (A : X →L[𝕜] X) (lam : 𝕜) (n : ℕ) :
    (lam • A) ^ n = lam ^ n • A ^ n := smul_pow lam A n

theorem norm_scaled_operator_power {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (A : X →L[𝕜] X) (lam : 𝕜) (n : ℕ) :
    ‖(lam • A) ^ n‖ = ‖lam‖ ^ n * ‖A ^ n‖ := by
  rw [smul_pow, norm_smul, norm_pow]

/-- The exponential majorant makes a geometric series invert on both sides. -/
theorem factorial_resolvent {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (A : X →L[𝕜] X) (c : ℝ)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ c ^ n / (n.factorial : ℝ)) :
    ∃ S : X →L[𝕜] X,
      Summable (fun n : ℕ => ‖A ^ n‖) ∧ HasSum (fun n : ℕ => A ^ n) S ∧
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, A ^ n) atTop (𝓝 S) ∧
      (1 - A) * S = 1 ∧ S * (1 - A) = 1 ∧ ‖S‖ ≤ Real.exp c := by
  have hn : Summable (fun n : ℕ => ‖A ^ n‖) :=
    (Real.summable_pow_div_factorial c).of_nonneg_of_le (fun _ => norm_nonneg _) hA
  have hs : Summable (fun n : ℕ => A ^ n) := hn.of_norm
  have he : HasSum (fun n : ℕ => c ^ n / (n.factorial : ℝ)) (Real.exp c) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  exact ⟨∑' n : ℕ, A ^ n, hn, hs.hasSum, hs.hasSum.tendsto_sum_nat,
    hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub,
    hs.hasSum.norm_le_of_bounded he hA⟩

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
  (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜)

/-- Scaling preserves the factorial decay with the constant `|lam| M L`. -/
theorem volterra_scaled_pow_norm (n : ℕ) :
    ‖(lam • VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k) ^ n‖ ≤
      (‖lam‖ * ‖k‖ * (b - a)) ^ n / (n.factorial : ℝ) := by
  rw [norm_scaled_operator_power]
  calc
    _ ≤ ‖lam‖ ^ n * (‖k‖ ^ n * (b - a) ^ n / (n.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (volterra_pow_norm hab k n) (by positivity)
    _ = _ := by simp only [mul_pow]; ring


end

/-- Exact error identity for the affine recurrence associated to a linear map. -/
theorem affine_iterate_error {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (A : X →L[𝕜] X) (f u u₀ : X) (hu : u - A u = f) (n : ℕ) :
    (fun v => f + A v)^[n] u₀ - u = (A ^ n) (u₀ - u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', mul_apply_eq_comp]
    calc
      f + A ((fun v => f + A v)^[n] u₀) - u =
          A ((fun v => f + A v)^[n] u₀ - u) := by
        rw [map_sub]
        rw [← hu]
        abel
      _ = _ := by rw [ih]

/-- Solving and iterating an affine map whose linear part has factorial decay. -/
theorem factorial_affine_solvability {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (A : X →L[𝕜] X) (c : ℝ)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ c ^ n / (n.factorial : ℝ)) (f : X) :
    ∃ u : X, u - A u = f ∧ (∀ v, v - A v = f → v = u) ∧
      HasSum (fun n : ℕ => (A ^ n) f) u ∧ ‖u‖ ≤ Real.exp c * ‖f‖ ∧
      ∀ u₀ : X,
        (∀ n : ℕ, ‖(fun v => f + A v)^[n] u₀ - u‖ ≤
          c ^ n / (n.factorial : ℝ) * ‖u₀ - u‖) ∧
        Tendsto (fun n : ℕ => (fun v => f + A v)^[n] u₀) atTop (𝓝 u) := by
  obtain ⟨S, _, hs, _, hl, hr, hb⟩ := factorial_resolvent A c hA
  have hu : S f - A (S f) = f := by
    change (1 - A) (S f) = f
    rw [← mul_apply_eq_comp, hl]
    rfl
  refine ⟨S f, hu, ?_, ?_, ?_, ?_⟩
  · intro v hv
    calc
      v = (S * (1 - A)) v := by rw [hr]; rfl
      _ = S f := by rw [mul_apply_eq_comp]; change S (v - A v) = S f; rw [hv]
  · exact hs.mapL (ContinuousLinearMap.apply 𝕜 X f)
  · exact (S.le_opNorm f).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg f))
  · intro u₀
    have he : ∀ n : ℕ, ‖(fun v => f + A v)^[n] u₀ - S f‖ ≤
        c ^ n / (n.factorial : ℝ) * ‖u₀ - S f‖ := by
      intro n
      rw [affine_iterate_error A f (S f) u₀ hu n]
      exact ((A ^ n).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _))
    refine ⟨he, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
    apply squeeze_zero (fun _ => norm_nonneg _) he
    simpa using (Real.summable_pow_div_factorial c).tendsto_atTop_zero.mul_const ‖u₀ - S f‖

theorem volterra_resolvent : VolterraResolventSpec.Resolvent := by
  intro 𝕜 E _ _ _ _ a b hab k lam
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  let A := lam • V
  obtain ⟨S, hn, hs, ht, hl, hr, hb⟩ := factorial_resolvent A
    (‖lam‖ * ‖k‖ * (b - a)) (volterra_scaled_pow_norm hab k lam)
  refine ⟨S, ?_, ?_, ?_, hl, hr, hb⟩
  · simpa only [A, scaled_operator_power] using hn
  · simpa only [A, scaled_operator_power] using hs
  · simpa only [A, scaled_operator_power] using ht

theorem volterra_solvability_and_iteration :
    VolterraResolventSpec.SolvabilityAndIteration := by
  intro 𝕜 E _ _ _ _ a b hab k lam f
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  let A := lam • V
  obtain ⟨u, hu, huniq, hs, hb, hi⟩ := factorial_affine_solvability A
    (‖lam‖ * ‖k‖ * (b - a)) (volterra_scaled_pow_norm hab k lam) f
  refine ⟨u, hu, huniq, ?_, hb, ?_⟩
  · simpa only [A, scaled_operator_power, smul_apply] using hs
  · intro u₀
    obtain ⟨he, ht⟩ := hi u₀
    refine ⟨he, ht, ?_⟩
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp ht ε hε] with n hn
    intro t
    exact (ContinuousMap.dist_apply_le_dist t).trans_lt (by simpa only [A, V, smul_apply, dist_comm] using hn)

/-- Identify a two-sided inverse with the native ring inverse. -/
theorem ring_inverse_eq_of_two_sided {A : Type*} [Ring A] (x y : A)
    (hxy : x * y = 1) (hyx : y * x = 1) :
    IsUnit x ∧ Ring.inverse x = y := by
  have hu : IsUnit x := ⟨⟨x, y, hxy, hyx⟩, rfl⟩
  refine ⟨hu, ?_⟩
  calc
    Ring.inverse x = Ring.inverse x * (x * y) := by rw [hxy, mul_one]
    _ = y := Ring.inverse_mul_cancel_left x y hu

theorem volterra_inverse_series : VolterraResolventSpec.InverseSeries := by
  intro 𝕜 E _ _ _ _ a b hab k lam
  obtain ⟨S, _, hs, _, hl, hr, hb⟩ := volterra_resolvent 𝕜 E a b hab k lam
  obtain ⟨hu, hi⟩ := ring_inverse_eq_of_two_sided _ S hl hr
  exact ⟨hu, hi.symm ▸ hs, hi.symm ▸ hb⟩

theorem volterra_uniform_inverse_bound : VolterraResolventSpec.UniformInverseBound := by
  intro 𝕜 E _ _ _ _ a b hab k M hM lam
  have hM0 : 0 ≤ M :=
    (norm_nonneg (k ⟨(a, a), le_rfl, le_rfl, hab⟩)).trans
      (hM ⟨(a, a), le_rfl, le_rfl, hab⟩)
  have hk : ‖k‖ ≤ M := (ContinuousMap.norm_le k hM0).mpr hM
  apply (volterra_inverse_series 𝕜 E a b hab k lam).2.2.trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk (norm_nonneg lam)) (sub_nonneg.mpr hab)

theorem volterra_evaluation_at_left : VolterraResolventSpec.EvaluationAtLeft := by
  intro 𝕜 E _ _ _ _ a b hab k u
  rw [(volterra_operator_properties 𝕜 E a b hab k).1]
  simp [volterraIntegralValue]

theorem volterra_not_surjective : VolterraResolventSpec.NotSurjective := by
  intro 𝕜 E _ _ _ _ _ a b hab k hs
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  obtain ⟨u, hu⟩ := hs (ContinuousMap.const _ x)
  have he := congrArg (fun f : C(VolterraInterval a b, E) => f ⟨a, le_rfl, hab⟩) hu
  exact hx (he.symm.trans (volterra_evaluation_at_left 𝕜 E a b hab k u))

/-- A unit endomorphism is surjective, with preimage supplied by its inverse. -/
theorem surjective_of_isUnit_operator {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] {A : X →L[𝕜] X}
    (hA : IsUnit A) : Function.Surjective A := by
  rcases hA with ⟨U, rfl⟩
  intro x
  refine ⟨(↑(U⁻¹) : X →L[𝕜] X) x, ?_⟩
  exact congrArg (fun B : X →L[𝕜] X => B x) U.mul_inv

theorem volterra_complex_spectrum : VolterraResolventSpec.ComplexSpectrum := by
  intro E _ _ _ _ a b hab k
  let X := C(VolterraInterval a b, E)
  let V : X →L[ℂ] X := VolterraOperatorSpec.OperatorValue ℂ E a b hab k
  have hzero : (0 : ℂ) ∈ spectrum ℂ V := by
    apply (spectrum.zero_mem_iff ℂ).mpr
    intro hV
    exact volterra_not_surjective ℂ E a b hab k (surjective_of_isUnit_operator hV)
  apply Set.Subset.antisymm
  · intro z hz
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    have hu := (volterra_inverse_series ℂ E a b hab k z⁻¹).1
    have hscalar : IsUnit (algebraMap ℂ (X →L[ℂ] X) z) :=
      (isUnit_iff_ne_zero.mpr hne).map (algebraMap ℂ (X →L[ℂ] X))
    have heq : algebraMap ℂ (X →L[ℂ] X) z * (1 - z⁻¹ • V) =
        algebraMap ℂ (X →L[ℂ] X) z - V := by
      simp [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul, hne]
    exact (spectrum.mem_iff.mp hz) (heq ▸ hscalar.mul hu)
  · intro z hz
    simpa only [Set.mem_singleton_iff.mp hz] using hzero

theorem volterra_singleton_resolvent : VolterraResolventSpec.SingletonResolvent := by
  intro 𝕜 E _ _ _ _ a k
  have hzero := volterra_singleton_zero 𝕜 E a k
  refine ⟨hzero, ?_⟩
  intro lam
  simp [hzero]

end ExpandedFA.PartV
