import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SchwartzRestriction
import MathGenome.Internal.FourierSobolev.P102.U4.TestSpace
import MathGenome.Internal.FourierSobolev.P102.U3.SchwartzFourier
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.Positivity

/-! The cutoff estimate below adapts the public Mathlib CompactSupport proof
(Copyright 2026 Terence Tao, Apache 2.0), retrieved at
https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Analysis/Distribution/SchwartzSpace/CompactSupport.lean .
It is generalized here to real or complex cutoffs and checked against the pinned APIs. -/
noncomputable section
open Set TopologicalSpace Filter Metric Real Finset Function
open scoped SchwartzMap Topology ContDiff
namespace P102.U4

section Approximation
open SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {φ : E → 𝕜} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ1 : φ =ᶠ[𝓝 0] 1)
  (f : SchwartzMap E 𝕜)

include hφ hφc hφ1 in
/-- Multiplying a Schwartz function `f` by the rescaled cutoff `fun x ↦ φ (ε • x)` converges to
`f` in each Schwartz seminorm as `ε → 0`, when `φ` is smooth, compactly supported, and equal to
`1` near the origin. -/
lemma tendsto_seminorm_smulLeftCLM_comp_smul_sub (k n : ℕ) :
    Tendsto
      (fun ε : ℝ ↦ (smulLeftCLM 𝕜 (fun x ↦ φ (ε • x)) f - f).seminorm ℝ k n) (𝓝 0) (𝓝 0) := by
  obtain ⟨r, hr, hφr⟩ := eventually_nhds_iff_ball.mp hφ1
  obtain ⟨A, hA0, hA⟩ := hφc.exists_bound_iteratedFDeriv hφ n
  have hψ : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i (fun z ↦ φ z - 1) y‖ ≤ A + 1 := by
    rintro (- | i) hi y
    · grind [norm_iteratedFDeriv_zero, norm_sub_le, norm_one, hA 0 hi y]
    · rw [fun_iteratedFDeriv_sub_apply (hφ.contDiffAt.of_le (mod_cast le_top)) contDiffAt_const,
        iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
      linarith [hA _ hi y]
  refine squeeze_zero' (g := fun ε ↦
      ‖ε‖ * (∑ i ∈ range (n + 1), n.choose i * (A + 1) * f.seminorm ℝ (k + 1) (n - i)) / r)
    (.of_forall fun _ ↦ apply_nonneg _ _) ?_
    (by simpa only [zero_mul, zero_div] using (tendsto_norm_zero.mul_const _).div_const r)
  filter_upwards [closedBall_mem_nhds (0 : ℝ) one_pos] with ε hε
  have hg : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (fun y ↦ φ (ε • y) - 1) x‖ ≤ A + 1 := by
    intro i hi x
    rw [iteratedFDeriv_comp_const_smul (f := fun z ↦ φ z - 1) _
      ((hφ.sub contDiff_const).of_le (mod_cast le_top)), norm_smul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hε))).trans (hψ i hi _)
  have hsmul : ⇑(smulLeftCLM 𝕜 (fun x ↦ φ (ε • x)) f - f) = fun x ↦ (φ (ε • x) - 1) • f x := by
    ext x
    simp [show (fun x ↦ φ (ε • x)).HasTemperateGrowth by fun_prop, sub_mul]
  refine seminorm_le_bound ℝ k n _ (by positivity) fun x ↦ ?_
  rw [hsmul, le_div_iff₀ hr]
  rcases lt_or_ge ‖ε • x‖ r with hx | hx
  · have : (fun y ↦ (φ (ε • y) - 1) • f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isOpen_ball.preimage (continuous_const_smul ε)).mem_nhds
        (mem_ball_zero_iff.mpr hx)] with y hy
      simp [hφr (ε • y) hy]
    calc
      _ = (0 : ℝ) := by rw [(this.iteratedFDeriv ℝ n).eq_of_nhds]; simp
      _ ≤ _ := by positivity
  · rw [norm_smul] at hx
    calc
      _ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ (φ (ε • y) - 1) • f y) x‖ * (‖ε‖ * ‖x‖) := by
          gcongr
      _ ≤ ‖ε‖ * ∑ i ∈ range (n + 1), n.choose i *
            ‖iteratedFDeriv ℝ i (fun y ↦ φ (ε • y) - 1) x‖ *
            (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
          grw [norm_iteratedFDeriv_smul_le (by fun_prop) (f.smooth ⊤) x (mod_cast le_top)]
          simp only [mul_sum, sum_mul]
          exact (sum_congr rfl fun _ _ ↦ by ring).le
      _ ≤ _ := by
          gcongr with i hi
          · exact hg i (by grind) x
          · exact le_seminorm ℝ _ _ f x

include hφ hφc hφ1 in
/-- As `ε → 0`, multiplying `f` by the rescaled cutoff `fun x ↦ φ (ε • x)` converges to `f` in
the Schwartz topology, for any smooth, compactly supported `φ` equal to `1` near the origin. -/
theorem tendsto_smulLeftCLM_comp_smul :
    Tendsto (fun ε : ℝ ↦ smulLeftCLM 𝕜 (fun x ↦ φ (ε • x)) f) (𝓝 0) (𝓝 f) := by
  rw [(schwartz_withSeminorms ℝ E 𝕜).tendsto_nhds]
  rintro ⟨k, n⟩ δ hδ
  simpa using (tendsto_seminorm_smulLeftCLM_comp_smul_sub hφ hφc hφ1 f k n).eventually
    (isOpen_Iio.mem_nhds hδ)


end Approximation

/-- On a fixed support, each Schwartz seminorm is bounded by the corresponding
unweighted derivative seminorm times a bound for the polynomial weight. -/
theorem fixedSupport_schwartz_bound {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : FixedSupport d 𝕜 K,
      SchwartzMap.seminorm 𝕜 k n
        (testToSchwartz d 𝕜 (stageInclusion 𝕜 (show (K : Set (Space d)) ⊆ ⊤ from subset_univ _) f)) ≤
      C * frechetSeminorm 𝕜 K n f := by
  obtain ⟨M, hM⟩ := K.isCompact.isBounded.exists_norm_le
  refine ⟨(max M 0) ^ k, by positivity, fun f => ?_⟩
  apply SchwartzMap.seminorm_le_bound 𝕜 k n _ (by positivity)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ _
  by_cases hx : x ∈ K
  · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ((hM x hx).trans (le_max_left _ _)) k)
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜)
      (norm_nonneg _) (by positivity)
  · rw [f.iteratedFDeriv_zero_on_compl hx]
    simp only [Pi.zero_apply, norm_zero, mul_zero]
    positivity

/-- Continuity of the canonical inclusion follows from the final locally convex topology. -/
theorem testToSchwartz_continuous (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    Continuous (testToSchwartz d 𝕜) := by
  classical
  apply (finalTopology d 𝕜 ⊤ (SchwartzTests d 𝕜) (testToSchwartz d 𝕜)).mpr
  intro K hK
  apply WithSeminorms.continuous_of_isBounded
    (ContDiffMapSupportedIn.withSeminorms 𝕜 (Space d) 𝕜 ⊤ K)
    (schwartz_withSeminorms 𝕜 (Space d) 𝕜)
    ((testToSchwartz d 𝕜).comp (stageInclusion 𝕜 hK).toLinearMap)
  intro p
  obtain ⟨C, hC, h⟩ := fixedSupport_schwartz_bound 𝕜 K p.1 p.2
  refine ⟨{p.2}, ⟨C, hC⟩, fun f => ?_⟩
  rw [Finset.sup_singleton]
  change SchwartzMap.seminorm 𝕜 p.1 p.2 (testToSchwartz d 𝕜 (stageInclusion 𝕜 hK f)) ≤
    C * frechetSeminorm 𝕜 K p.2 f
  exact h f

/-- The inclusion as a continuous scalar-linear map. -/
def testToSchwartzCLM (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    WholeTests d 𝕜 →L[𝕜] SchwartzTests d 𝕜 :=
  ⟨testToSchwartz d 𝕜, testToSchwartz_continuous d 𝕜⟩

@[simp] theorem testToSchwartz_apply {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : WholeTests d 𝕜) (x : Space d) : testToSchwartz d 𝕜 f x = f x := rfl

/-- Equality near the closed unit ball implies equality near the origin. -/
theorem cutoff_eventually_one {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (χ : WholeTests d 𝕜)
    (hχ : ∃ U : Opens (Space d), closedBall (0 : Space d) 1 ⊆ (U : Set (Space d)) ∧
      ∀ x ∈ U, χ x = 1) : (χ : Space d → 𝕜) =ᶠ[𝓝 0] 1 := by
  obtain ⟨U, hU, hχU⟩ := hχ
  filter_upwards [U.isOpen.mem_nhds (hU (by simp))] with x hx
  exact hχU x hx

/-- The explicit truncations converge in the Schwartz topology and every native seminorm. -/
theorem cutoffApproximation : RestrictionExpected.CutoffApproximation := by
  intro d 𝕜 _ χ hχ f
  have hg (R : ℝ) : (fun x : Space d => χ (R⁻¹ • x)).HasTemperateGrowth := by
    exact χ.hasCompactSupport.hasTemperateGrowth (χ.contDiff.of_le (by simp)) |>.comp
      (by fun_prop : (fun x : Space d => R⁻¹ • x).HasTemperateGrowth)
  have ht : Tendsto (cutoffSchwartz χ f) atTop (𝓝 f) :=
    (tendsto_smulLeftCLM_comp_smul (χ.contDiff.of_le (by simp)) χ.hasCompactSupport
      (cutoff_eventually_one χ hχ) f).comp tendsto_inv_atTop_zero
  refine ⟨?_, ?_, ht, ?_⟩
  · intro R x
    exact SchwartzMap.smulLeftCLM_apply_apply (hg R) f x
  · intro R hR
    rw [cutoffSchwartz, SchwartzMap.smulLeftCLM_apply (hg R)]
    exact (χ.hasCompactSupport.comp_smul (inv_ne_zero hR)).smul_right
  · intro k n
    have hc : Continuous (SchwartzMap.seminorm 𝕜 k n : SchwartzTests d 𝕜 → ℝ) :=
      (schwartz_withSeminorms 𝕜 (Space d) 𝕜).continuous_seminorm (k, n)
    simpa only [Function.comp_def, sub_self, map_zero] using hc.continuousAt.tendsto.comp (ht.sub_const f)

/-- The manuscript's coordinate seminorms give the same cutoff convergence. -/
theorem manuscriptCutoffApproximation : RestrictionExpected.ManuscriptCutoffApproximation := by
  intro d χ hχ f N k
  have ht := (cutoffApproximation d ℂ χ hχ f).2.2.1
  have hc := (P102.U3.manuscript_withSeminorms d).continuous_seminorm (N, k)
  simpa only [Function.comp_def, sub_self, map_zero, P102.U3.manuscriptFamily] using hc.continuousAt.tendsto.comp (ht.sub_const f)


/-- Smooth cutoffs with the exact hypothesis required for the dilation argument. -/
theorem exists_unit_cutoff (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    ∃ χ : WholeTests d 𝕜, ∃ U : Opens (Space d),
      closedBall (0 : Space d) 1 ⊆ (U : Set (Space d)) ∧ ∀ x ∈ U, χ x = 1 := by
  let K : Compacts (Space d) := ⟨closedBall 0 1, isCompact_closedBall _ _⟩
  obtain ⟨χ, _, U, hKU, _, hχU⟩ := cutoff d ⊤ K (subset_univ _)
  let χ𝕜 : WholeTests d 𝕜 := TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) χ
  refine ⟨χ𝕜, U, hKU, fun x hx => ?_⟩
  change RCLike.ofReal (χ x) = 1
  rw [hχU x hx, RCLike.ofReal_one]

/-- Every Schwartz function is the limit of compactly supported smooth truncations. -/
theorem testToSchwartz_denseRange (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    DenseRange (testToSchwartz d 𝕜) := by
  obtain ⟨χ, hχ⟩ := exists_unit_cutoff d 𝕜
  intro f
  have h := cutoffApproximation d 𝕜 χ hχ f
  apply mem_closure_of_tendsto h.2.2.1
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  let g : WholeTests d 𝕜 := ⟨cutoffSchwartz χ f R,
    (cutoffSchwartz χ f R).smooth ⊤, h.2.1 R (ne_of_gt hR), subset_univ _⟩
  exact ⟨g, by ext x; rfl⟩

/-- The continuous, injective inclusion has dense image. -/
theorem schwartzInclusion : RestrictionExpected.Inclusion := by
  intro d 𝕜 _
  refine ⟨testToSchwartz_continuous d 𝕜, ?_, testToSchwartz_denseRange d 𝕜⟩
  intro f g h
  ext x
  exact congrArg (fun u : SchwartzTests d 𝕜 => u x) h

/-- Restriction on strong duals (uniform convergence on bounded sets). -/
def restrictSchwartzStrong (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    (SchwartzTests d 𝕜 →L[𝕜] 𝕜) →L[𝕜] (WholeTests d 𝕜 →L[𝕜] 𝕜) :=
  ContinuousLinearMap.precomp 𝕜 (testToSchwartzCLM d 𝕜)

/-- Restriction on pointwise duals. -/
def restrictSchwartzWeak (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    (SchwartzTests d 𝕜 →Lₚₜ[𝕜] 𝕜) →L[𝕜] (WholeTests d 𝕜 →Lₚₜ[𝕜] 𝕜) :=
  PointwiseConvergenceCLM.precomp 𝕜 (testToSchwartzCLM d 𝕜)

/-- The two transpose maps have their prescribed bilinear values and are injective. -/
theorem dualRestriction : RestrictionExpected.DualRestriction := by
  intro d 𝕜 _
  have hi (T S : SchwartzTests d 𝕜 →L[𝕜] 𝕜)
      (h : ∀ f, T (testToSchwartz d 𝕜 f) = S (testToSchwartz d 𝕜 f)) : T = S := by
    exact DFunLike.coe_injective ((testToSchwartz_denseRange d 𝕜).equalizer
      T.continuous S.continuous (funext h))
  constructor
  · refine ⟨restrictSchwartzStrong d 𝕜, fun _ _ => rfl, ?_⟩
    intro T S h
    exact hi T S (fun f => congrArg (fun U : WholeTests d 𝕜 →L[𝕜] 𝕜 => U f) h)
  · refine ⟨restrictSchwartzWeak d 𝕜, fun _ _ => rfl, ?_⟩
    intro T S h
    exact hi T S (fun f => congrArg (fun U : WholeTests d 𝕜 →Lₚₜ[𝕜] 𝕜 => U f) h)


/-- Real tests included in the complex Schwartz space, using the same ambient function. -/
def realTestToSchwartzCLM (d : ℕ) : WholeTests d ℝ →L[ℝ] SchwartzTests d ℂ :=
  ((testToSchwartzCLM d ℂ).restrictScalars ℝ).comp (complexifyTest ⊤)

/-- The real-test realization of a tempered distribution, with strong topology. -/
def restrictSchwartzRealStrong (d : ℕ) :
    (SchwartzTests d ℂ →L[ℂ] ℂ) →L[ℝ] (WholeTests d ℝ →L[ℝ] ℂ) :=
  (ContinuousLinearMap.precomp ℂ (realTestToSchwartzCLM d)).comp
    (ContinuousLinearMap.restrictScalarsL ℂ (SchwartzTests d ℂ) ℂ ℝ ℝ)

/-- Scalar restriction is also continuous for pointwise convergence on Schwartz tests. -/
def weakTemperedRestrictScalars (d : ℕ) :
    (SchwartzTests d ℂ →Lₚₜ[ℂ] ℂ) →L[ℝ] (SchwartzTests d ℂ →Lₚₜ[ℝ] ℂ) where
  toFun T := T.restrictScalars ℝ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval
    (fun f => continuous_eval_const f)

/-- The real-test realization of a tempered distribution, with pointwise topology. -/
def restrictSchwartzRealWeak (d : ℕ) :
    (SchwartzTests d ℂ →Lₚₜ[ℂ] ℂ) →L[ℝ] (WholeTests d ℝ →Lₚₜ[ℝ] ℂ) :=
  (PointwiseConvergenceCLM.precomp ℂ (realTestToSchwartzCLM d)).comp
    (weakTemperedRestrictScalars d)

/-- Decomposition into real tests commutes with the Schwartz inclusion. -/
theorem testToSchwartz_decomposition {d : ℕ} (f : WholeTests d ℂ) :
    testToSchwartz d ℂ f =
      testToSchwartz d ℂ (complexifyTest ⊤ (realPart ⊤ f)) +
        Complex.I • testToSchwartz d ℂ (complexifyTest ⊤ (imagPart ⊤ f)) := by
  ext x
  simp only [testToSchwartz_apply, add_apply, smul_apply, realPart_apply, imagPart_apply,
    complexifyTest_apply, smul_eq_mul]
  exact (Complex.re_add_im (f x)).symm.trans (by ring)

/-- Every complex-test value is recovered bilinearly from two real-test values. -/
theorem restrictSchwartzReal_formula {d : ℕ} (T : SchwartzTests d ℂ →L[ℂ] ℂ)
    (f : WholeTests d ℂ) :
    T (testToSchwartz d ℂ f) =
      T (testToSchwartz d ℂ (complexifyTest ⊤ (realPart ⊤ f))) +
        Complex.I * T (testToSchwartz d ℂ (complexifyTest ⊤ (imagPart ⊤ f))) := by
  conv_lhs => rw [testToSchwartz_decomposition f]
  simp only [map_add, map_smul, smul_eq_mul]

/-- The real and complex test conventions yield compatible restriction maps, each
injective and continuous in both requested dual topologies. -/
theorem realTestBridge : RestrictionExpected.RealTestBridge := by
  intro d
  have hi (T S : SchwartzTests d ℂ →L[ℂ] ℂ)
      (h : ∀ f : WholeTests d ℝ,
        T (testToSchwartz d ℂ (complexifyTest ⊤ f)) =
          S (testToSchwartz d ℂ (complexifyTest ⊤ f))) : T = S := by
    apply DFunLike.coe_injective
    apply (testToSchwartz_denseRange d ℂ).equalizer T.continuous S.continuous
    funext f
    change T (testToSchwartz d ℂ f) = S (testToSchwartz d ℂ f)
    rw [restrictSchwartzReal_formula T f, restrictSchwartzReal_formula S f,
      h (realPart ⊤ f), h (imagPart ⊤ f)]
  constructor
  · refine ⟨restrictSchwartzRealStrong d, fun _ _ => rfl, ?_, ?_⟩
    · intro T S h
      apply hi T S
      intro f
      exact congrArg (fun U : WholeTests d ℝ →L[ℝ] ℂ => U f) h
    · exact restrictSchwartzReal_formula
  · refine ⟨restrictSchwartzRealWeak d, fun _ _ => rfl, ?_, ?_⟩
    · intro T S h
      apply hi T S
      intro f
      exact congrArg (fun U : WholeTests d ℝ →Lₚₜ[ℝ] ℂ => U f) h
    · exact restrictSchwartzReal_formula

end P102.U4

/- Mathlib proof attribution
Adapted portion near line 30:
The compactly supported approximation in Schwartz space, adapted to real and
complex cutoffs.

Upstream: Mathlib/Analysis/Distribution/SchwartzSpace/CompactSupport.lean (around line 39)
Revision: b2115b96757894e56b53fd0f94bd63acd64d8025
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
