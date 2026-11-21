import MathGenome.Internal.LinearPDE.P201Specs.Integral.Volterra
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.IntegralOperators.VolterraResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.VolterraResolventKernel

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace P201.Integral.Volterra
open ExpandedFA.PartV
open ExpandedFA.IntegralOperators.VolterraResolvent

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}

/-- Multiplication by a scalar preserves its norm in the operator model. -/
theorem multiplicationKernel_norm (k : C(volterraTriangle a b, 𝕜)) :
    ‖multiplicationKernel k‖ = ‖k‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le (multiplicationKernel k) (norm_nonneg k)).mpr
    intro p
    rw [(scalar_formula 𝕜 a b (by
      exact p.property.1.trans (p.property.2.1.trans p.property.2.2)) k).2.2 p]
    exact k.norm_coe_le_norm p
  · apply (ContinuousMap.norm_le k (norm_nonneg (multiplicationKernel k))).mpr
    intro p
    rw [← (scalar_formula 𝕜 a b
      (p.property.1.trans (p.property.2.1.trans p.property.2.2)) k).2.2 p]
    exact (multiplicationKernel k).norm_coe_le_norm p

theorem operator_formula : Spec.OperatorFormula := by
  intro 𝕜 _ a b hab k
  refine ⟨(scalar_formula 𝕜 a b hab k).1, (scalar_formula 𝕜 a b hab k).2.1, ?_⟩
  simpa only [multiplicationKernel_norm] using
    (volterra_operator_properties 𝕜 𝕜 a b hab (multiplicationKernel k)).2.2

theorem factorial : Spec.Factorial := by
  intro 𝕜 _ a b hab k
  constructor
  · intro n u t
    have h := volterra_pow_pointwise hab (multiplicationKernel k) n u t
    rw [multiplicationKernel_norm] at h
    convert h using 1; ring
  · intro n
    simpa only [multiplicationKernel_norm] using
      volterra_pow_norm hab (multiplicationKernel k) n

theorem inverse_series : Spec.InverseSeries := by
  intro 𝕜 _ a b hab k lam
  obtain ⟨hu, hs, hb⟩ := volterra_inverse_series 𝕜 𝕜 a b hab (multiplicationKernel k) lam
  refine ⟨hu, (ExpandedFA.IntegralOperators.VolterraResolvent.inverse_series
    𝕜 a b hab k lam).2.1, hs, ?_⟩
  simpa only [multiplicationKernel_norm] using hb

/-- Every linear endomorphism of the scalar field is multiplication by A(1). -/
lemma scalar_map_apply (A : 𝕜 →L[𝕜] 𝕜) (z : 𝕜) : A z = A 1 * z := by
  simpa only [smul_eq_mul, mul_one, mul_comm] using A.map_smul z (1 : 𝕜)

/-- The independent scalar recurrence is exactly the scalar operator recurrence,
with n corresponding to the source's k_(n+1). -/
theorem iteratedKernel_bridge (k : C(volterraTriangle a b, 𝕜)) (n : ℕ)
    (p : volterraTriangle a b) (z : 𝕜) :
    iteratedVolterraKernel (multiplicationKernel k) n p z = iteratedKernel k n p * z := by
  induction n generalizing p z with
  | zero => rfl
  | succ n ih =>
    have hc := (continuous_kernelConvolution_integrand (multiplicationKernel k).continuous
      (continuous_iteratedVolterraKernel (multiplicationKernel k) n)).comp
      (continuous_const.prodMk continuous_id : Continuous (fun r : ℝ => (p,r)))
    unfold iteratedVolterraKernel kernelConvolution
    rw [instNormedSpaceReal_specs_2, NormedSpace.restrictScalars_eq]
    change (∫ r in p.val.2..p.val.1,
      (multiplicationKernel k (kernelLeftPoint p r)).comp
        (iteratedVolterraKernel (multiplicationKernel k) n (kernelRightPoint p r))) z = _
    have hi := ContinuousLinearMap.intervalIntegral_apply
      (hc.intervalIntegrable (μ := volume) p.val.2 p.val.1) z
    simp only [Function.comp_def] at hi
    rw [hi]
    change (∫ r in p.val.2..p.val.1,
      k (kernelLeftPoint p r) *
        (iteratedVolterraKernel (multiplicationKernel k) n (kernelRightPoint p r) z)) = _
    simp_rw [ih, ← mul_assoc]
    exact intervalIntegral.integral_mul_const z _

lemma continuous_iteratedKernel (k : C(volterraTriangle a b, 𝕜)) (n : ℕ) :
    Continuous (iteratedKernel k n) := by
  have h := (continuous_iteratedVolterraKernel (multiplicationKernel k) n).clm_apply
    (continuous_const : Continuous (fun _ : volterraTriangle a b => (1 : 𝕜)))
  simpa only [iteratedKernel_bridge, mul_one] using h

lemma norm_iteratedKernel (k : C(volterraTriangle a b, 𝕜)) (n : ℕ)
    (p : volterraTriangle a b) :
    ‖iteratedKernel k n p‖ = ‖iteratedVolterraKernel (multiplicationKernel k) n p‖ := by
  have he : iteratedVolterraKernel (multiplicationKernel k) n p =
      ContinuousLinearMap.mul 𝕜 𝕜 (iteratedKernel k n p) := by
    apply ContinuousLinearMap.ext
    intro z
    exact iteratedKernel_bridge k n p z
  rw [he, ContinuousLinearMap.opNorm_mul_apply]

theorem kernels : Spec.Kernels := by
  intro 𝕜 _ a b hab k
  refine ⟨fun _ => rfl, (volterra_kernel_recursion 𝕜 𝕜 a b hab
    (multiplicationKernel k)).2.2, continuous_iteratedKernel k, ?_, ?_⟩
  · intro n p
    rw [norm_iteratedKernel]
    simpa only [multiplicationKernel_norm] using
      norm_iteratedVolterraKernel (multiplicationKernel k) n p
  · intro n u t
    have h := volterra_kernel_iterate_representation 𝕜 𝕜 a b hab
      (multiplicationKernel k) n u t
    rw [NormedSpace.restrictScalars_eq] at h
    simpa only [iteratedKernel_bridge] using h


/-- A uniform exponential majorant for the scalar series terms. -/
lemma scaled_kernel_bound (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜))
    (lam : 𝕜) (n : ℕ) (p : volterraTriangle a b) :
    ‖lam ^ n * iteratedKernel k n p‖ ≤
      ‖k‖ * ((‖lam‖ * ‖k‖ * (b-a))^n / (n.factorial : ℝ)) := by
  have h := norm_scaled_iteratedVolterraKernel hab (multiplicationKernel k) lam n p
  simpa only [norm_smul, norm_mul, norm_pow, ← norm_iteratedKernel,
    multiplicationKernel_norm] using h

/-- The reduced operator-valued series evaluates to the independently defined
scalar reduced series, including at λ=0. -/
theorem reducedResolvent_bridge (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜))
    (lam : 𝕜) (p : volterraTriangle a b) (z : 𝕜) :
    volterraReducedResolventKernel (multiplicationKernel k) lam p z =
      reducedResolvent k lam p * z := by
  have hs := ((volterra_kernel_series hab (multiplicationKernel k) lam).2.1 p).2.mapL
    (ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜))
  have hs' : HasSum (fun n : ℕ => lam ^ n * iteratedKernel k n p)
      (volterraReducedResolventKernel (multiplicationKernel k) lam p 1) := by
    simpa only [ContinuousLinearMap.apply_apply, smul_apply,
      iteratedKernel_bridge, mul_one, smul_eq_mul] using hs
  rw [scalar_map_apply, ← hs'.tsum_eq]
  rfl

/-- Scalar evaluation commutes with the actual convolution integral. -/
lemma convolution_eval_one
    (h g : volterraTriangle a b → 𝕜 →L[𝕜] 𝕜)
    (hh : Continuous h) (hg : Continuous g) (p : volterraTriangle a b) :
    kernelConvolution h g p 1 = ∫ r in p.val.2..p.val.1,
      h (kernelLeftPoint p r) 1 * g (kernelRightPoint p r) 1 := by
  have hc := (continuous_kernelConvolution_integrand hh hg).comp
    (continuous_const.prodMk continuous_id : Continuous (fun r : ℝ => (p,r)))
  unfold kernelConvolution
  rw [instNormedSpaceReal_specs_2, NormedSpace.restrictScalars_eq]
  have hi := ContinuousLinearMap.intervalIntegral_apply
    (hc.intervalIntegrable (μ := volume) p.val.2 p.val.1) (1 : 𝕜)
  simp only [Function.comp_def] at hi
  rw [hi]
  apply intervalIntegral.integral_congr
  intro r _
  exact scalar_map_apply (h (kernelLeftPoint p r)) (g (kernelRightPoint p r) 1)

theorem resolvent_series : Spec.ResolventSeries := by
  intro 𝕜 _ a b hab k lam
  let B := fun n : ℕ => ‖k‖ * ((‖lam‖ * ‖k‖ * (b-a))^n / (n.factorial : ℝ))
  have hB : Summable B := (Real.summable_pow_div_factorial _).mul_left ‖k‖
  have hb := scaled_kernel_bound hab k lam
  refine ⟨?_, ?_, tendstoUniformly_tsum_nat hB hb, ?_, ?_⟩
  · exact continuous_tsum
      (fun n => continuous_const.mul (continuous_iteratedKernel k n)) hB hb
  · intro p
    have hn := hB.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hb n p)
    exact ⟨hn, hn.of_norm.hasSum⟩
  · apply tendstoUniformly_tsum_nat hB
    intro n p
    simpa only [Real.norm_eq_abs, abs_norm] using hb n p
  · intro p
    have h := congrArg (fun A : 𝕜 →L[𝕜] 𝕜 => A 1)
      ((volterra_resolvent_kernel_identities hab (multiplicationKernel k) lam).1 p)
    simp only [add_apply, smul_apply] at h
    rw [convolution_eval_one _ _ (multiplicationKernel k).continuous
      (volterra_kernel_series hab (multiplicationKernel k) lam).1 p] at h
    simp only [reducedResolvent_bridge hab, mul_one, smul_eq_mul] at h
    simpa only [multiplicationKernel, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, ContinuousLinearMap.mul_apply', mul_one] using h


/-- Pointwise scalar integral equation and its bounded-operator form agree. -/
theorem isSolution_iff (hab : a ≤ b) (k : C(volterraTriangle a b, 𝕜))
    (lam : 𝕜) (g u : C(VolterraInterval a b, 𝕜)) :
    IsSolution hab k lam g u ↔ u - lam • operator hab k u = g := by
  constructor
  · intro h
    apply ContinuousMap.ext
    intro t
    change u t - lam * operator hab k u t = g t
    rw [(operator_formula 𝕜 a b hab k).1]
    exact sub_eq_iff_eq_add.mpr (h t)
  · intro h t
    have ht := congrArg (fun v : C(VolterraInterval a b, 𝕜) => v t) h
    change u t - lam * operator hab k u t = g t at ht
    rw [(operator_formula 𝕜 a b hab k).1] at ht
    exact sub_eq_iff_eq_add.mp ht

theorem solvability : Spec.Solvability := by
  intro 𝕜 _ a b hab k lam g
  obtain ⟨u, hu, huniq, _, _, hi⟩ := volterra_solvability_and_iteration
    𝕜 𝕜 a b hab (multiplicationKernel k) lam g
  refine ⟨u, (isSolution_iff hab k lam g u).mpr hu, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact huniq v ((isSolution_iff hab k lam g v).mp hv)
  · have hunit := (inverse_series 𝕜 a b hab k lam).1
    calc
      u = (Ring.inverse (1 - lam • operator hab k) * (1 - lam • operator hab k)) u := by
        rw [Ring.inverse_mul_cancel _ hunit]
        rfl
      _ = Ring.inverse (1 - lam • operator hab k) g := by
        rw [mul_apply_eq_comp]
        congr 1
  · intro t
    have ht := volterra_solution_kernel_formula hab (multiplicationKernel k) lam g u hu t
    rw [instNormedSpaceReal_mathGenome_2, NormedSpace.restrictScalars_eq] at ht
    simpa only [reducedResolvent_bridge hab, smul_eq_mul] using ht
  · intro u₀
    exact ⟨(hi u₀).2.1, (hi u₀).2.2⟩

theorem boundary_cases : Spec.BoundaryCases := by
  constructor
  · intro 𝕜 _ a k
    have hzero : operator (le_refl a) k = 0 :=
      (volterra_singleton_resolvent 𝕜 𝕜 a (multiplicationKernel k)).1
    refine ⟨hzero, ?_, ?_⟩
    · intro n p
      have hp : p.val.1 = p.val.2 := by
        linarith [p.property.1, p.property.2.1, p.property.2.2]
      simp only [iteratedKernel, hp, intervalIntegral.integral_same]
    · intro lam g u
      rw [isSolution_iff, hzero]
      simp
  · intro 𝕜 _ a b hab k
    refine ⟨?_, ?_, ?_⟩
    · intro p
      simp [reducedResolvent, zero_pow_eq, iteratedKernel]
    · intro g u
      rw [isSolution_iff]
      simp
    · simp only [zero_smul 𝕜 (operator hab k), sub_zero, Ring.inverse_one]

end P201.Integral.Volterra
