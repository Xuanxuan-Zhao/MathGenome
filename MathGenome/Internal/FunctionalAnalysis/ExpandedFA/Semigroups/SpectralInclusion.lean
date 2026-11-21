import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.SpectralInclusion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.LaplaceResolvent

/-! Spectral inclusion for an arbitrary real or complex Banach C₀ semigroup.
We integrate the weighted orbit on a finite interval, establish both exact
 generator identities, and construct a resolvent if exp(tζ)I − T(t) is a unit.
No continuity in operator norm is used. -/

noncomputable section
open scoped NNReal
open MeasureTheory Filter Set Topology

namespace ExpandedFA.Semigroups.SpectralInclusion
open LaplaceResolventSpec

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

local instance (priority := low) : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance (priority := low) : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X

/-- The finite Laplace integral is bounded using strong continuity and a local
 operator bound; it is not an operator-valued Bochner integral. -/
def finiteLaplace (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (t : ℝ≥0) : X →L[𝕜] X := by
  let L : X →ₗ[𝕜] X :=
    { toFun := fun x => ∫ s in (0 : ℝ)..(t : ℝ), orbit T ζ x s
      map_add' := by
        intro x y
        simp only [orbit, map_add, smul_add]
        exact intervalIntegral.integral_add
          ((LaplaceResolvent.continuous_orbit T ζ x).intervalIntegrable _ _)
          ((LaplaceResolvent.continuous_orbit T ζ y).intervalIntegrable _ _)
      map_smul' := by
        intro c x
        simp only [orbit, map_smul, RingHom.id_apply, smul_comm _ c]
        exact intervalIntegral.integral_smul c _ }
  apply L.mkContinuousOfExistsBound
  obtain ⟨C, hC, hbound⟩ := T.bounded_on_interval t
  refine ⟨(Real.exp (|RCLike.re ζ| * (t : ℝ)) * C) * (t : ℝ), fun x => ?_⟩
  change ‖∫ s in (0 : ℝ)..(t : ℝ), orbit T ζ x s‖ ≤ _
  calc
    _ ≤ ((Real.exp (|RCLike.re ζ| * (t : ℝ)) * C) * ‖x‖) * |(t : ℝ) - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le t.coe_nonneg] at hs
      rw [orbit, norm_smul, LaplaceResolvent.norm_kernel]
      have hsT : ‖T.operators s.toNNReal x‖ ≤ C * ‖x‖ :=
        ((T.operators s.toNNReal).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hbound _ (by
            simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2))
            (norm_nonneg x))
      have hsK : Real.exp (-RCLike.re ζ * s) ≤ Real.exp (|RCLike.re ζ| * (t : ℝ)) := by
        apply Real.exp_le_exp.mpr
        exact (mul_le_mul_of_nonneg_right (neg_le_abs (RCLike.re ζ)) hs.1.le).trans
          (mul_le_mul_of_nonneg_left hs.2 (abs_nonneg _))
      exact (mul_le_mul_of_nonneg_left hsT (Real.exp_pos _).le).trans
        ((mul_le_mul_of_nonneg_right hsK (mul_nonneg (by linarith) (norm_nonneg x))).trans_eq (by ring))
    _ = _ := by rw [sub_zero, abs_of_nonneg t.coe_nonneg]; ring

@[simp] theorem finiteLaplace_apply (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (t : ℝ≥0) (x : X) :
    finiteLaplace T ζ t x = ∫ s in (0 : ℝ)..(t : ℝ), orbit T ζ x s := rfl

/-- The finite weighted integration-by-parts identity on the exact domain. -/
theorem finiteLaplace_difference (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (t : ℝ≥0)
    (x : (generator T).domain) :
    ζ • finiteLaplace T ζ t x - finiteLaplace T ζ t (generator T x) =
      (x : X) - kernel ζ t • T.operators t x := by
  have hf (y : X) : IntervalIntegrable (orbit T ζ y) volume 0 (t : ℝ) :=
    (LaplaceResolvent.continuous_orbit T ζ y).intervalIntegrable _ _
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.coe_nonneg
    (LaplaceResolvent.continuous_orbit T ζ (x : X)).continuousOn
    (fun s hs => LaplaceResolvent.hasDerivAt_orbit T ζ x hs.1)
    ((hf (generator T x)).sub ((hf x).smul ζ))
  erw [intervalIntegral.integral_sub (hf (generator T x)) ((hf x).smul ζ),
    intervalIntegral.integral_smul] at hi
  have hzero : orbit T ζ (x : X) 0 = x := by
    simp only [orbit, LaplaceResolvent.kernel_zero, Real.toNNReal_zero, T.zero_apply, one_smul]
  rw [hzero] at hi
  simpa only [finiteLaplace_apply, orbit, Real.toNNReal_coe, neg_sub] using congrArg Neg.neg hi

/-- Weighted integration preserves the closed generator graph on its domain. -/
theorem finiteLaplace_graph (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (t : ℝ≥0)
    (x : (generator T).domain) :
    (finiteLaplace T ζ t x, finiteLaplace T ζ t (generator T x)) ∈ (generator T).graph := by
  let S : Submodule ℝ (X × X) := (generator T).graph.restrictScalars ℝ
  have hf (y : X) : IntervalIntegrable (orbit T ζ y) volume 0 (t : ℝ) :=
    (LaplaceResolvent.continuous_orbit T ζ y).intervalIntegrable _ _
  have hm : ∀ s : ℝ, (orbit T ζ x s, orbit T ζ (generator T x) s) ∈ S := by
    intro s
    have hg : (T.operators s.toNNReal x,
        T.operators s.toNNReal (generator T x)) ∈ (generator T).graph :=
      (mem_generator_graph_iff T _ _).mpr
        (T.hasGeneratorLimit_map s.toNNReal (generator_has_limit T x))
    exact (generator T).graph.smul_mem (kernel ζ s) hg
  have hi := LaplaceResolvent.integral_mem_closed_submodule S T.generator_graph_closed
    ((hf x).1.prodMk (hf (generator T x)).1) (Eventually.of_forall hm)
  change (_, _) ∈ S
  simpa only [integral_pair (hf x).1 (hf (generator T x)).1,
    ← intervalIntegral.integral_of_le t.coe_nonneg, finiteLaplace_apply] using hi

/-- B(ζ,t) from the paper, represented using a finite Laplace integral. -/
def integratedOperator (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (t : ℝ≥0) : X →L[𝕜] X :=
  NormedSpace.exp ((t : ℝ) • ζ) • finiteLaplace T ζ t

/-- The bounded defect appearing in both exact generator identities. -/
def defect (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (t : ℝ≥0) : X →L[𝕜] X :=
  algebraMap 𝕜 (X →L[𝕜] X) (NormedSpace.exp ((t : ℝ) • ζ)) - T.operators t

@[simp] theorem defect_apply (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (t : ℝ≥0) (x : X) :
    defect T ζ t x = NormedSpace.exp ((t : ℝ) • ζ) • x - T.operators t x := by
  simp [defect, Algebra.algebraMap_eq_smul_one]

theorem exp_mul_kernel (ζ : 𝕜) (t : ℝ) :
    NormedSpace.exp (t • ζ) * kernel ζ t = 1 := by
  rw [kernel, ← NormedSpace.exp_add, ← add_smul t (-t) ζ, add_neg_cancel, zero_smul,
    NormedSpace.exp_zero]

/-- B(ζ,t) is the integral with the precise exponential weight in the source. -/
theorem integratedOperator_apply (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (t : ℝ≥0) (x : X) :
    integratedOperator T ζ t x =
      ∫ s in (0 : ℝ)..(t : ℝ), NormedSpace.exp (((t : ℝ) - s) • ζ) • T.operators s.toNNReal x := by
  change NormedSpace.exp ((t : ℝ) • ζ) • (∫ s in (0 : ℝ)..(t : ℝ), orbit T ζ x s) = _
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [orbit, smul_smul, kernel, ← NormedSpace.exp_add]
  rw [← add_smul (t : ℝ) (-s) ζ, sub_eq_add_neg]

/-- B(ζ,t)(ζ − A)x = (exp(tζ)I − T(t))x on the full derivative domain. -/
theorem integratedOperator_left_identity (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (t : ℝ≥0)
    (x : (generator T).domain) :
    integratedOperator T ζ t (ζ • (x : X) - generator T x) = defect T ζ t x := by
  rw [map_sub, map_smul]
  change ζ • (NormedSpace.exp ((t : ℝ) • ζ) • finiteLaplace T ζ t x) -
    NormedSpace.exp ((t : ℝ) • ζ) • finiteLaplace T ζ t (generator T x) = _
  rw [smul_comm ζ, ← smul_sub, finiteLaplace_difference, defect_apply, smul_sub,
    smul_smul, exp_mul_kernel, one_smul]

/-- On D(A), B(ζ,t) commutes with A, as a statement about the exact graph. -/
theorem integratedOperator_graph_on_domain (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (t : ℝ≥0)
    (x : (generator T).domain) :
    (integratedOperator T ζ t x, integratedOperator T ζ t (generator T x)) ∈
      (generator T).graph :=
  (generator T).graph.smul_mem (NormedSpace.exp ((t : ℝ) • ζ)) (finiteLaplace_graph T ζ t x)

/-- Closedness and density give (ζ − A)B(ζ,t) = exp(tζ)I − T(t) on every vector,
 including the assertion that B(ζ,t) takes values in the exact domain. -/
theorem integratedOperator_graph (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (t : ℝ≥0) (x : X) :
    (integratedOperator T ζ t x,
      ζ • integratedOperator T ζ t x - defect T ζ t x) ∈ (generator T).graph := by
  let B := integratedOperator T ζ t
  let C := defect T ζ t
  let S : Set X := {y | (B y, ζ • B y - C y) ∈ (generator T).graph}
  have hc : IsClosed S := T.generator_graph_closed.preimage
    (B.continuous.prodMk ((B.continuous.const_smul ζ).sub C.continuous))
  have hs : ((generator T).domain : Set X) ⊆ S := by
    intro y hy
    have hi := integratedOperator_left_identity T ζ t ⟨y, hy⟩
    rw [map_sub, map_smul] at hi
    have heq : B (generator T ⟨y, hy⟩) = ζ • B y - C y := by
      change ζ • B y - B (generator T ⟨y, hy⟩) = C y at hi
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp hi).symm
    have hg := integratedOperator_graph_on_domain T ζ t ⟨y, hy⟩
    change (B y, B (generator T ⟨y, hy⟩)) ∈ (generator T).graph at hg
    change (B y, ζ • B y - C y) ∈ (generator T).graph
    simpa only [heq] using hg
  have hall := closure_minimal hs hc
  rw [T.generator_domain_dense.closure_eq] at hall
  exact hall (mem_univ x)

/-- Invertibility of the time defect produces a bounded two-sided inverse of
 ζ − A. Injectivity follows from the reverse integrated identity; no domain
 invariance of an arbitrary bounded inverse is presumed. -/
def resolventOfUnit (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (t : ℝ≥0)
    (u : (X →L[𝕜] X)ˣ) (hu : (u : X →L[𝕜] X) = defect T ζ t) :
    Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ where
  inverse := (integratedOperator T ζ t).comp (↑u⁻¹ : X →L[𝕜] X)
  mem_domain y := ((Unbounded.mem_graph_iff (generator T) _).mp
    (integratedOperator_graph T ζ t ((↑u⁻¹ : X →L[𝕜] X) y))).choose
  right_inverse y := by
    have hg := ((Unbounded.mem_graph_iff (generator T) _).mp
      (integratedOperator_graph T ζ t ((↑u⁻¹ : X →L[𝕜] X) y))).choose_spec
    dsimp only at hg
    erw [hg]
    have hc : defect T ζ t ((↑u⁻¹ : X →L[𝕜] X) y) = y := by
      rw [← hu]
      change ((u : X →L[𝕜] X) * (↑u⁻¹ : X →L[𝕜] X)) y = y
      simp
    simp only [ContinuousLinearMap.comp_apply, sub_sub_cancel, hc]
  left_inverse x := by
    let B := integratedOperator T ζ t
    let C := defect T ζ t
    let y : X := ζ • (x : X) - generator T x
    let z : X := B ((↑u⁻¹ : X →L[𝕜] X) y)
    obtain ⟨hz, hAz⟩ := (Unbounded.mem_graph_iff (generator T) _).mp
      (integratedOperator_graph T ζ t ((↑u⁻¹ : X →L[𝕜] X) y))
    have hc : C ((↑u⁻¹ : X →L[𝕜] X) y) = y := by
      change defect T ζ t _ = y
      rw [← hu]
      change ((u : X →L[𝕜] X) * (↑u⁻¹ : X →L[𝕜] X)) y = y
      simp
    have hshift : ζ • z - generator T ⟨z, hz⟩ = y := by
      change generator T ⟨z, hz⟩ = ζ • z - C ((↑u⁻¹ : X →L[𝕜] X) y) at hAz
      rw [hAz, hc, sub_sub_cancel]
    have hzC := integratedOperator_left_identity T ζ t ⟨z, hz⟩
    have hxC := integratedOperator_left_identity T ζ t x
    have heq : C z = C x := by
      change B (ζ • z - generator T ⟨z, hz⟩) = C z at hzC
      rw [hshift] at hzC
      exact hzC.symm.trans hxC
    have huC : (↑u⁻¹ : X →L[𝕜] X).comp C = ContinuousLinearMap.id 𝕜 X := by
      change (↑u⁻¹ : X →L[𝕜] X) * C = 1
      change (↑u⁻¹ : X →L[𝕜] X) * defect T ζ t = 1
      rw [← hu]
      simp
    have hinj : Function.Injective C := by
      apply Function.LeftInverse.injective (g := (↑u⁻¹ : X →L[𝕜] X))
      intro w
      exact congrArg (fun f : X →L[𝕜] X => f w) huC
    exact hinj heq

/-- Spectral inclusion over the original scalar field. The inverse is built
on the exact generator domain, including when the Banach space is zero. -/
theorem scalar_spectral_inclusion (T : C0Semigroup 𝕜 X) (t : ℝ≥0) :
    (fun ζ : 𝕜 => NormedSpace.exp ((t : ℝ) • ζ)) ''
      C0SemigroupSpec.spectrumValue (C0SemigroupSpec.generatorValue T) ⊆
    _root_.spectrum 𝕜 (T.operators t) \ {0} := by
  rintro z ⟨ζ, hζ, rfl⟩
  refine ⟨?_, ?_⟩
  · apply _root_.spectrum.mem_iff.mpr
    intro hunit
    obtain ⟨u, hu⟩ := hunit
    have hu' : (u : X →L[𝕜] X) = defect T ζ t := hu
    exact hζ ⟨resolventOfUnit T ζ t u hu'⟩
  · exact (NormedSpace.isUnit_exp ((t : ℝ) • ζ)).ne_zero

/-- The full complex generator spectrum maps into the time-operator spectrum. -/
theorem spectral_inclusion : SpectralInclusionSpec.SpectralInclusion := by
  intro X _ _ _ T t _ht
  simpa only [Complex.exp_eq_exp_ℂ] using scalar_spectral_inclusion T t

/-- The real generator spectrum maps into the spectrum of the original real
 time operator, with no complexification. -/
theorem real_spectral_inclusion : SpectralInclusionSpec.RealSpectralInclusion := by
  intro X _ _ _ T t _ht
  simpa only [Real.exp_eq_exp_ℝ, smul_eq_mul] using scalar_spectral_inclusion T t

end ExpandedFA.Semigroups.SpectralInclusion
