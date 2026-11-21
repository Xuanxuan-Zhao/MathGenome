import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionRegularization
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.SmoothApproximateIdentities
import Mathlib.Topology.ContinuousMap.CompactlySupported

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set TopologicalSpace Filter MeasureTheory
open scoped Topology ContDiff Distributions BoundedContinuousFunction

namespace ExpandedFA.Distributions
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

/-- Convolution of an arbitrary distribution with a test function. -/
def distributionConvolution :
    Specs.ExpandedFA.Distributions.DistributionRegularization.convolutionType :=
  Specs.ExpandedFA.Distributions.DistributionRegularization.convolutionValue

@[simp] theorem distributionConvolution_apply
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (x : Domain d) :
    distributionConvolution u φ x = u (reflectedTranslate φ x) := rfl

@[simp] theorem reflectedTranslate_apply
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (x y : Domain d) :
    reflectedTranslate φ x y = φ (x-y) := rfl

/-- Translated tests have a common compact support for x in any compact set. -/
theorem reflectedTranslate_common_support
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (A : Set (Domain d)) (hA : IsCompact A) :
    ∃ K : Compacts (Domain d), ∀ x ∈ A, tsupport (reflectedTranslate φ x) ⊆ K := by
  let S := (fun p : Domain d × Domain d => p.1-p.2) '' (A ×ˢ tsupport φ)
  have hS : IsCompact S :=
    (hA.prod φ.hasCompactSupport).image (continuous_fst.sub continuous_snd)
  refine ⟨⟨S, hS⟩, ?_⟩
  intro x hx
  apply closure_minimal
  · intro y hy
    exact ⟨(x, x-y), ⟨hx, subset_tsupport φ hy⟩, sub_sub_cancel x y⟩
  · exact hS.isClosed

@[simp] theorem scaledMollifierTest_apply
    (ρ : Domain d → ℝ) (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ)
    (ε : ℝ) (hε : ε ≠ 0) (x : Domain d) :
    (scaledMollifierTest ρ hρ ε : Tests 𝕜 (⊤ : Opens (Domain d))) x =
      (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε x : 𝕜) := by
  unfold scaledMollifierTest
  rw [dite_eq_right hε]
  rfl

/-- The actual scaled-test convolution has the source's exact pairing for every
positive scale, without any symmetry assumption on the mollifier. -/
theorem distributionConvolution_mollifier_pairing
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (ρ : Domain d → ℝ) (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ)
    (ε : ℝ) (hε : 0 < ε) (x : Domain d) :
    ∃ θ : Tests 𝕜 (⊤ : Opens (Domain d)),
      (∀ y, θ y = (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε (x-y) : 𝕜)) ∧
      distributionConvolution u (scaledMollifierTest ρ hρ ε) x = u θ := by
  refine ⟨reflectedTranslate (scaledMollifierTest ρ hρ ε) x, ?_, rfl⟩
  intro y
  exact scaledMollifierTest_apply ρ hρ ε hε.ne' (x-y)

/-- Differentiating the reflected test introduces a minus sign. -/
theorem testPartial_reflectedTranslate_single
    (i : Fin d) (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (x : Domain d) :
    testPartialCLM [i] (reflectedTranslate φ x) =
      -reflectedTranslate (testPartialCLM [i] φ) x := by
  ext y
  rw [testPartial_single_apply]
  change fderiv ℝ (fun z => φ (x-z)) y (coordinateVector i) =
    -testPartialCLM [i] φ (x-y)
  rw [fderiv_fun_comp y
    (φ.contDiff.differentiable (by simp) (x-y))
    (differentiableAt_const x |>.sub differentiableAt_id), fderiv_const_sub]
  simp [testPartial_single_apply]

/-- The sign from the reflected test cancels the distributional derivative sign. -/
theorem distributionConvolution_derivative_single
    (i : Fin d) (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    distributionConvolution (distributionDerivative 𝕜 d ⊤ [i] u) φ =
      distributionConvolution u (testPartialCLM [i] φ) := by
  funext x
  simp [distributionConvolution_apply, distributionDerivative_apply,
    testPartial_reflectedTranslate_single]

/-- The same reflection rule for every ordered coordinate derivative. -/
theorem testPartial_reflectedTranslate
    (w : List (Fin d)) (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (x : Domain d) :
    testPartialCLM w (reflectedTranslate φ x) =
      (-1 : 𝕜) ^ w.length • reflectedTranslate (testPartialCLM w φ) x := by
  induction w with
  | nil => simp [testPartialCLM]
  | cons i w ih =>
    change testPartialCLM [i] (testPartialCLM w (reflectedTranslate φ x)) = _
    rw [ih, map_smul, testPartial_reflectedTranslate_single]
    simp [pow_succ, testPartialCLM]

/-- All distribution derivatives can be transferred to the smoothing test.
This identity alone does not assert differentiability of the resulting function. -/
theorem distributionConvolution_derivative
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (w : List (Fin d)) :
    distributionConvolution (distributionDerivative 𝕜 d ⊤ w u) φ =
      distributionConvolution u (testPartialCLM w φ) := by
  funext x
  simp only [distributionConvolution_apply, distributionDerivative_apply,
    testPartial_reflectedTranslate, map_smul, smul_eq_mul]
  rw [← mul_assoc, ← mul_pow]
  simp

section BoundedTranslation
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bounded continuous field of linear maps, viewed as a linear map into
bounded continuous functions. -/
def boundedFunctionFlip : (E →ᵇ (E →L[ℝ] F)) →L[ℝ] (E →L[ℝ] (E →ᵇ F)) :=
  LinearMap.mkContinuous
    { toFun := fun g => LinearMap.mkContinuous
        { toFun := fun h => (ContinuousLinearMap.apply ℝ F h).compLeftContinuousBounded E g
          map_add' := by intros; ext; simp
          map_smul' := by intros; ext; simp }
        ‖g‖ (fun h => by
          apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
          intro y
          exact ((g y).le_opNorm h).trans
            (mul_le_mul_of_nonneg_right (g.norm_coe_le_norm y) (norm_nonneg h)))
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    1 (fun g => by
      simpa using ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) (fun h => by
        apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        intro y
        exact ((g y).le_opNorm h).trans
            (mul_le_mul_of_nonneg_right (g.norm_coe_le_norm y) (norm_nonneg h))))

@[simp] theorem boundedFunctionFlip_apply (g : E →ᵇ (E →L[ℝ] F)) (h y : E) :
    boundedFunctionFlip g h y = g y h := rfl

/-- Reflection and translation, with values in the sup norm space. -/
def boundedReflectedTranslate (f : E → F) (hf : Continuous f) (hs : HasCompactSupport f)
    (x : E) : E →ᵇ F :=
  (⟨⟨fun y => f (x-y), hf.comp (continuous_const.sub continuous_id)⟩,
    hs.comp_isClosedEmbedding (Homeomorph.subLeft x).isClosedEmbedding⟩ : CompactlySupportedContinuousMap E F).toBoundedContinuousFunction

@[simp] theorem boundedReflectedTranslate_apply (f : E → F) (hf : Continuous f)
    (hs : HasCompactSupport f) (x y : E) :
    boundedReflectedTranslate f hf hs x y = f (x-y) := rfl

/-- Uniform differentiability of the translated function in the sup norm. -/
theorem boundedReflectedTranslate_hasFDerivAt (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (hf' : Continuous (fderiv ℝ f)) (hs' : HasCompactSupport (fderiv ℝ f)) (x : E) :
    HasFDerivAt (boundedReflectedTranslate f hf.continuous hs)
      (boundedFunctionFlip (boundedReflectedTranslate (fderiv ℝ f)
        hf' hs' x)) x := by
  have huc : UniformContinuous (fderiv ℝ f) :=
    hf'.uniformContinuous_of_tendsto_cocompact
      hs'.is_zero_at_infty
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp huc c hc
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hc.le (norm_nonneg h))).mpr
  intro y
  change ‖f (x+h-y) - f (x-y) - fderiv ℝ f (x-y) h‖ ≤ c * ‖h‖
  have hb : x-y ∈ Metric.ball (x-y) δ := by simpa using hδ
  have hb' : x+h-y ∈ Metric.ball (x-y) δ := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_sub_sub_cancel_right, add_sub_cancel_left] using hh
  have he := (convex_ball (x-y) δ).norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (f := f) (φ := fderiv ℝ f (x-y))
    (fun z _ => hf.differentiable (by simp) z)
    (fun z hz => by simpa only [dist_eq_norm] using (hd (a := z) (b := x-y) hz).le) hb hb'
  simpa only [sub_sub_sub_cancel_right, add_sub_cancel_left] using he

/-- All orders of smoothness of translation in the sup norm. -/
theorem boundedReflectedTranslate_contDiff (n : ℕ) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ContDiff ℝ n (boundedReflectedTranslate f hf.continuous hs) := by
  induction n generalizing F with
  | zero =>
    simp only [Nat.cast_zero]
    rw [contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun x =>
      (boundedReflectedTranslate_hasFDerivAt f hf hs
        (hf.fderiv_right (m := ∞) (by simp)).continuous
        (hs.fderiv (𝕜 := ℝ)) x).continuousAt
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    rw [contDiff_succ_iff_hasFDerivAt]
    have hf' : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hflip : ContDiff ℝ n (boundedFunctionFlip (E := E) (F := F)) :=
      ContinuousLinearMap.contDiff _
    refine ⟨fun x => boundedFunctionFlip
      (boundedReflectedTranslate (fderiv ℝ f) hf'.continuous (hs.fderiv (𝕜 := ℝ)) x),
      hflip.comp (ih (fderiv ℝ f) hf' (hs.fderiv (𝕜 := ℝ))),
      fun x => boundedReflectedTranslate_hasFDerivAt f hf hs hf'.continuous
        (hs.fderiv (𝕜 := ℝ)) x⟩

end BoundedTranslation

/-- Indices for the finite collection of coordinate derivatives through order m. -/
abbrev FiniteJetIndex (d m : ℕ) := Σ k : Fin (m+1), Fin k.val → Fin d

/-- A finite jet with the sup norm on each derivative and on the finite product. -/
abbrev FiniteJet (𝕜 : Type) [RCLike 𝕜] (d m : ℕ) :=
  FiniteJetIndex d m → (Domain d →ᵇ 𝕜)

/-- The finite-jet map of a compactly supported smooth function. -/
def finiteJetMap (K : Compacts (Domain d)) (m : ℕ) :
    Step 𝕜 K →L[𝕜] FiniteJet 𝕜 d m :=
  ContinuousLinearMap.pi (fun a => coordinateDerivative 𝕜 K a.2)

@[simp] theorem finiteJetMap_apply (K : Compacts (Domain d)) (m : ℕ)
    (φ : Step 𝕜 K) (a : FiniteJetIndex d m) (y : Domain d) :
    finiteJetMap K m φ a y =
      iteratedFDeriv ℝ a.1.val φ y (fun j => coordinateVector (a.2 j)) := by
  exact coordinateDerivative_apply K a.2 φ y

/-- The manuscript's seminorm is exactly the norm of its finite jet. -/
theorem norm_finiteJetMap (K : Compacts (Domain d)) (m : ℕ) (φ : Step 𝕜 K) :
    ‖finiteJetMap K m φ‖ = stepSeminorm 𝕜 K m φ := by
  classical
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).mpr
    intro a
    exact coordinate_le_stepSeminorm K a.2 (Nat.le_of_lt_succ a.1.isLt) φ
  · apply (step_seminorm_formula 𝕜 d K m φ _ (norm_nonneg _)).mpr
    intro k hk a x
    rw [← finiteJetMap_apply K m φ (⟨⟨k, Nat.lt_succ_of_le hk⟩, a⟩ : FiniteJetIndex d m)]
    exact (BoundedContinuousFunction.norm_coe_le_norm _ x).trans
      (norm_le_pi_norm (finiteJetMap K m φ) (⟨⟨k, Nat.lt_succ_of_le hk⟩, a⟩ : FiniteJetIndex d m))

/-- Order zero is included, so the finite-jet map is injective in every dimension. -/
theorem finiteJetMap_injective (K : Compacts (Domain d)) (m : ℕ) :
    Function.Injective (finiteJetMap (𝕜 := 𝕜) K m) := by
  intro φ ψ h
  ext x
  have hx := congrArg (fun f : FiniteJet 𝕜 d m =>
    f ⟨⟨0, Nat.zero_lt_succ m⟩, Fin.elim0⟩ x) h
  simpa only [finiteJetMap_apply, iteratedFDeriv_zero_apply] using hx

/-- A distribution on a fixed compact step factors through a bounded functional
on finitely many derivative functions. This is an application of Hahn--Banach,
not an additional regularity hypothesis on the distribution. -/
theorem distribution_finiteJet_factorization
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) (K : Compacts (Domain d)) :
    ∃ m : ℕ, ∃ L : FiniteJet 𝕜 d m →L[𝕜] 𝕜, ∀ φ : Step 𝕜 K,
      L (finiteJetMap K m φ) = u (TestFunction.ofSupportedIn (Ω := (⊤ : Opens (Domain d))) (show (K : Set (Domain d)) ⊆ (⊤ : Opens (Domain d)) from subset_univ _) φ) := by
  let inc := TestFunction.ofSupportedInCLM (F := 𝕜) (n := ⊤) (Ω := (⊤ : Opens (Domain d))) 𝕜 (show (K : Set (Domain d)) ⊆ (⊤ : Opens (Domain d)) from subset_univ _)
  obtain ⟨C, hC, m, hm⟩ := (continuous_step_iff_finite_order K
    (u.comp inc).toLinearMap).mp (u.comp inc).continuous
  let J := finiteJetMap (𝕜 := 𝕜) K m
  let e := LinearEquiv.ofInjective J.toLinearMap (finiteJetMap_injective K m)
  let v : J.range →ₗ[𝕜] 𝕜 := (u.comp inc).toLinearMap.comp e.symm.toLinearMap
  have hv : ∀ z : J.range, ‖v z‖ ≤ C * ‖z‖ := by
    intro z
    have hj : J (e.symm z) = z.val := congrArg Subtype.val (e.apply_symm_apply z)
    change ‖u (inc (e.symm z))‖ ≤ C * ‖z‖
    calc
      _ ≤ C * stepSeminorm 𝕜 K m (e.symm z) := hm (e.symm z)
      _ = C * ‖z‖ := by
        rw [← norm_finiteJetMap K m]
        change C * ‖J (e.symm z)‖ = C * ‖z‖
        rw [hj]
        rfl
  obtain ⟨L, hL, _⟩ := exists_extension_norm_eq J.range (v.mkContinuous C hv)
  refine ⟨m, L, fun φ => ?_⟩
  have he := hL (e φ)
  simpa [v, e, inc] using he

/-- Evaluation of a multilinear map at a fixed tuple. -/
def multilinearEvaluation {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} (v : Fin k → E) :
    (E [×k]→L[ℝ] F) →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun A => A v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (∏ j, ‖v j‖) (fun A => by simpa [mul_comm] using A.le_opNorm v)

/-- The coordinate derivative of a reflected function, with the signs carried
by the coordinate vectors. -/
def reflectedCoordinateFunction {k : ℕ}
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (a : Fin k → Fin d) : Domain d → 𝕜 :=
  fun z => iteratedFDeriv ℝ k φ z (fun j => -coordinateVector (a j))

theorem reflectedCoordinateFunction_contDiff {k : ℕ}
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (a : Fin k → Fin d) :
    ContDiff ℝ ∞ (reflectedCoordinateFunction φ a) := by
  have he : ContDiff ℝ ∞ (multilinearEvaluation (F := 𝕜) (fun j => -coordinateVector (a j))) :=
    ContinuousLinearMap.contDiff _
  exact he.comp (φ.contDiff.iteratedFDeriv_right (m := ∞) (by simp))

theorem reflectedCoordinateFunction_hasCompactSupport {k : ℕ}
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (a : Fin k → Fin d) :
    HasCompactSupport (reflectedCoordinateFunction φ a) := by
  exact (φ.hasCompactSupport.iteratedFDeriv k).comp_left
    (g := fun A : (Domain d) [×k]→L[ℝ] 𝕜 => A (fun j => -coordinateVector (a j))) (by simp)

theorem iteratedFDeriv_reflectedTranslate {k : ℕ}
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (x y : Domain d) (a : Fin k → Fin d) :
    iteratedFDeriv ℝ k (reflectedTranslate φ x) y (fun j => coordinateVector (a j)) =
      reflectedCoordinateFunction φ a (x-y) := by
  let N : Domain d →L[ℝ] Domain d := -ContinuousLinearMap.id ℝ _
  have heq : ⇑(reflectedTranslate φ x) = (fun z => φ (x+z)) ∘ N := by
    funext z
    simp [N, sub_eq_add_neg]
  rw [heq, N.iteratedFDeriv_comp_right (f := fun z => φ (x+z))
    (φ.contDiff.comp (contDiff_const.add contDiff_id)) y (i := k) (by simp)]
  simp [N, iteratedFDeriv_comp_add_left, reflectedCoordinateFunction, sub_eq_add_neg]

/-- A globally smooth normed-space model of the finite jet of translated tests. -/
def reflectedJet (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (m : ℕ) (x : Domain d) :
    FiniteJet 𝕜 d m :=
  fun a => boundedReflectedTranslate (reflectedCoordinateFunction φ a.2)
    (reflectedCoordinateFunction_contDiff φ a.2).continuous
    (reflectedCoordinateFunction_hasCompactSupport φ a.2) x

theorem reflectedJet_contDiff (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (m : ℕ) :
    ContDiff ℝ ∞ (reflectedJet φ m) := by
  rw [contDiff_infty]
  intro n
  apply contDiff_pi.mpr
  intro a
  exact boundedReflectedTranslate_contDiff n _ (reflectedCoordinateFunction_contDiff φ a.2)
    (reflectedCoordinateFunction_hasCompactSupport φ a.2)

/-- The normed model is the actual finite jet, for any compact support witness. -/
theorem reflectedJet_eq_finiteJetMap (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (m : ℕ)
    (K : Compacts (Domain d)) (x : Domain d) (hx : tsupport (reflectedTranslate φ x) ⊆ K) :
    reflectedJet φ m x = finiteJetMap K m
      (ContDiffMapSupportedIn.of_support_subset (reflectedTranslate φ x).contDiff
        ((subset_tsupport _).trans hx)) := by
  ext a y
  rw [finiteJetMap_apply]
  exact (iteratedFDeriv_reflectedTranslate φ x y a.2).symm

/-- Differentiation commutes with evaluating any iterated derivative, including
in the direction that is added at the other end of the derivative tuple. -/
theorem fderiv_iteratedFDeriv_evaluation {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : E → F) (hf : ContDiff ℝ ∞ f) (v : Fin k → E) (h x : E) :
    fderiv ℝ (fun z => iteratedFDeriv ℝ k f z v) x h =
      iteratedFDeriv ℝ k (fun z => fderiv ℝ f z h) x v := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    let g : E → F := fun z => iteratedFDeriv ℝ k f z (Fin.tail v)
    have hg : ContDiff ℝ ∞ g := by
      have hev : ContDiff ℝ ∞ (multilinearEvaluation (F := F) (Fin.tail v)) :=
        ContinuousLinearMap.contDiff _
      exact hev.comp (hf.iteratedFDeriv_right (m := ∞) (by simp))
    have hh : ContDiff ℝ ∞ (fun z => fderiv ℝ f z h) :=
      (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hl : (fun z => iteratedFDeriv ℝ (k+1) f z v) = fun z => fderiv ℝ g z (v 0) := by
      funext z
      exact ((hf.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp) z).iteratedFDeriv_succ_apply_left'
    have hr : iteratedFDeriv ℝ (k+1) (fun z => fderiv ℝ f z h) x v =
        fderiv ℝ (fun z => iteratedFDeriv ℝ k (fun z => fderiv ℝ f z h) z (Fin.tail v)) x (v 0) :=
      ((hh.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp) x).iteratedFDeriv_succ_apply_left'
    rw [hl, hr]
    have hswap : fderiv ℝ (fun z => fderiv ℝ g z (v 0)) x h =
        fderiv ℝ (fun z => fderiv ℝ g z h) x (v 0) := by
      simp only [fderiv_clm_apply ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
        (differentiableAt_const _), fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero,
        zero_add, ContinuousLinearMap.flip_apply]
      exact hg.contDiffAt.isSymmSndFDerivAt (by simp) h (v 0)
    rw [hswap]
    have hgi : (fun z => fderiv ℝ g z h) =
        fun z => iteratedFDeriv ℝ k (fun z => fderiv ℝ f z h) z (Fin.tail v) :=
      funext (fun z => ih (Fin.tail v) z)
    rw [hgi]

/-- Convolution of an arbitrary distribution with a test is smooth. -/
theorem distributionConvolution_smooth :
    Specs.ExpandedFA.Distributions.DistributionRegularization.smoothType := by
  intro 𝕜 _ d u φ
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨K, hK⟩ := reflectedTranslate_common_support φ (Metric.closedBall x 1) (isCompact_closedBall x 1)
  obtain ⟨m, L, hL⟩ := distribution_finiteJet_factorization u K
  have hmodel : ContDiff ℝ ∞ (fun z => L (reflectedJet φ m z)) :=
    (L.restrictScalars ℝ).contDiff.comp (reflectedJet_contDiff φ m)
  apply hmodel.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with z hz
  rw [reflectedJet_eq_finiteJetMap φ m K z (hK z hz), hL]
  rfl

theorem reflectedJet_fderiv_coordinate (φ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (m : ℕ) (i : Fin d) (x : Domain d) :
    fderiv ℝ (reflectedJet φ m) x (coordinateVector i) =
      reflectedJet (testPartialCLM [i] φ) m x := by
  have hdiff : ∀ a : FiniteJetIndex d m, DifferentiableAt ℝ
      (fun z => reflectedJet φ m z a) x := by
    intro a
    exact (boundedReflectedTranslate_contDiff 1 _ (reflectedCoordinateFunction_contDiff φ a.2)
      (reflectedCoordinateFunction_hasCompactSupport φ a.2)).differentiable (by norm_num) x
  rw [show reflectedJet φ m = (fun z a => reflectedJet φ m z a) from rfl, fderiv_pi hdiff]
  ext a y
  change fderiv ℝ (fun z => reflectedJet φ m z a) x (coordinateVector i) y = _
  let f := reflectedCoordinateFunction φ a.2
  have hf := reflectedCoordinateFunction_contDiff φ a.2
  have hs := reflectedCoordinateFunction_hasCompactSupport φ a.2
  change fderiv ℝ (boundedReflectedTranslate f hf.continuous hs) x (coordinateVector i) y = _
  rw [(boundedReflectedTranslate_hasFDerivAt f hf hs
    (hf.fderiv_right (m := ∞) (by simp)).continuous (hs.fderiv (𝕜 := ℝ)) x).fderiv]
  change fderiv ℝ f (x-y) (coordinateVector i) =
    reflectedCoordinateFunction (testPartialCLM [i] φ) a.2 (x-y)
  unfold f reflectedCoordinateFunction
  rw [fderiv_iteratedFDeriv_evaluation _ _ φ.contDiff]
  congr 1

/-- Differentiating convolution in a coordinate direction differentiates its test. -/
theorem distributionConvolution_fderiv_coordinate
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (i : Fin d) (x : Domain d) :
    fderiv ℝ (distributionConvolution u φ) x (coordinateVector i) =
      distributionConvolution u (testPartialCLM [i] φ) x := by
  let A := Metric.closedBall x 1
  obtain ⟨K, hK⟩ := reflectedTranslate_common_support φ A (isCompact_closedBall x 1)
  obtain ⟨K', hK'⟩ := reflectedTranslate_common_support (testPartialCLM [i] φ) A (isCompact_closedBall x 1)
  obtain ⟨m, L, hL⟩ := distribution_finiteJet_factorization u (K ⊔ K')
  have heq : (fun z => L (reflectedJet φ m z)) =ᶠ[𝓝 x] distributionConvolution u φ := by
    filter_upwards [Metric.closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with z hz
    rw [reflectedJet_eq_finiteJetMap φ m (K ⊔ K') z
      ((hK z hz).trans (show (K : Set (Domain d)) ⊆ K ⊔ K' from le_sup_left)), hL]
    rfl
  rw [← heq.fderiv_eq]
  have hder := (L.restrictScalars ℝ).hasFDerivAt.comp x
    ((reflectedJet_contDiff φ m).differentiable (by simp) x).hasFDerivAt
  change fderiv ℝ ((L.restrictScalars ℝ) ∘ reflectedJet φ m) x (coordinateVector i) = _
  rw [hder.fderiv, ContinuousLinearMap.comp_apply, reflectedJet_fderiv_coordinate]
  change L (reflectedJet (testPartialCLM [i] φ) m x) = _
  rw [reflectedJet_eq_finiteJetMap (testPartialCLM [i] φ) m (K ⊔ K') x
    ((hK' x (by simp [A])).trans
      (show (K' : Set (Domain d)) ⊆ K ⊔ K' from le_sup_right)), hL]
  rfl

/-- Every ordered coordinate derivative is the convolution with that derivative of the test. -/
theorem partialFunction_distributionConvolution
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (w : List (Fin d)) :
    partialFunction w (distributionConvolution u φ) =
      distributionConvolution u (testPartialCLM w φ) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (fun x => fderiv ℝ (partialFunction w (distributionConvolution u φ)) x
      (coordinateVector i)) = _
    rw [ih]
    funext x
    exact distributionConvolution_fderiv_coordinate u (testPartialCLM w φ) i x

/-- Both derivative identities for every coordinate word. -/
theorem distributionConvolution_derivatives :
    Specs.ExpandedFA.Distributions.DistributionRegularization.derivativesType := by
  intro 𝕜 _ d u φ w
  have ht := distributionConvolution_derivative u φ w
  exact ⟨(partialFunction_distributionConvolution u φ w).trans ht.symm, ht⟩

/-- Evaluation of an iterated derivative of a smooth compactly supported function
is again smooth and compactly supported. -/
theorem iteratedFDeriv_evaluation_regular (f : Domain d → 𝕜)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) {k : ℕ} (v : Fin k → Domain d) :
    ContDiff ℝ ∞ (fun z => iteratedFDeriv ℝ k f z v) ∧
      HasCompactSupport (fun z => iteratedFDeriv ℝ k f z v) := by
  constructor
  · have he : ContDiff ℝ ∞ (multilinearEvaluation (F := 𝕜) v) :=
      ContinuousLinearMap.contDiff _
    exact he.comp (hf.iteratedFDeriv_right (m := ∞) (by simp))
  · exact (hs.iteratedFDeriv k).comp_left
      (g := fun A : (Domain d) [×k]→L[ℝ] 𝕜 => A v) (by simp)

/-- Repeated integration by parts. Each derivative in a negative direction on the
first factor becomes the derivative in the positive direction on the second. -/
theorem integral_iteratedFDeriv_neg_mul (k : ℕ) (f g : Domain d → 𝕜)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (ht : HasCompactSupport g) (v : Fin k → Domain d) :
    (∫ z, iteratedFDeriv ℝ k f z (fun j => -v j) * g z) =
      ∫ z, f z * iteratedFDeriv ℝ k g z v := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    let H : Domain d → 𝕜 := fun z => iteratedFDeriv ℝ k f z (fun j => -Fin.tail v j)
    obtain ⟨hH, hsH⟩ := iteratedFDeriv_evaluation_regular f hf hs (fun j => -Fin.tail v j)
    let g' : Domain d → 𝕜 := fun z => fderiv ℝ g z (v 0)
    have hg' : ContDiff ℝ ∞ g' :=
      (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hsg' : HasCompactSupport g' := ht.fderiv_apply ℝ (v 0)
    have hH' : Continuous (fun z => fderiv ℝ H z (v 0)) :=
      ((hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
    have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure (Domain d))) (v := v 0)
      ((hH'.mul hg.continuous).integrable_of_hasCompactSupport (ht.mul_left))
      ((hH.continuous.mul hg'.continuous).integrable_of_hasCompactSupport (hsH.mul_right))
      ((hH.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hsH.mul_right))
      (fun z _ => hH.differentiable (by simp) z) (fun z _ => hg.differentiable (by simp) z)
    have hleft : ∀ z, iteratedFDeriv ℝ (k+1) f z (fun j => -v j) =
        -fderiv ℝ H z (v 0) := by
      intro z
      rw [((hf.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp) z).iteratedFDeriv_succ_apply_left']
      change fderiv ℝ H z (-v 0) = _
      simp
    calc
      _ = -∫ z, fderiv ℝ H z (v 0) * g z := by
        simp_rw [hleft, neg_mul, integral_neg]
      _ = ∫ z, H z * g' z := hparts.symm
      _ = ∫ z, f z * iteratedFDeriv ℝ k g' z (Fin.tail v) :=
        ih g' hg' hsg' (Fin.tail v)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with z
        congr 1
        rw [← fderiv_iteratedFDeriv_evaluation k g hg (Fin.tail v) (v 0) z]
        exact ((hg.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp) z).iteratedFDeriv_succ_apply_left'.symm


/-- One compact set supports all reflected mollifiers seen by a fixed outer test,
for all sufficiently small positive scales. -/
theorem scaledMollifier_reflected_common_support
    (ρ : Domain d → ℝ) (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ)
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    ∃ K : Compacts (Domain d), tsupport ψ ⊆ K ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ tsupport ψ,
        tsupport (reflectedTranslate (scaledMollifierTest ρ hρ ε : Tests 𝕜 ⊤) x) ⊆ K := by
  let S : Set (Domain d) :=
    (fun p : Domain d × Domain d => p.1 - p.2) ''
      (tsupport ψ ×ˢ Metric.closedBall 0 1)
  have hS : IsCompact S :=
    (ψ.hasCompactSupport.prod (isCompact_closedBall (0 : Domain d) 1)).image
      (continuous_fst.sub continuous_snd)
  let K : Compacts (Domain d) := ⟨tsupport ψ ∪ S, ψ.hasCompactSupport.union hS⟩
  refine ⟨K, subset_union_left, ?_⟩
  filter_upwards [scaledKernel_support_eventually ρ hρ.2.1 (by norm_num : (0 : ℝ) < 1),
    self_mem_nhdsWithin] with ε hεs hε x hx
  apply closure_minimal
  · intro y hy
    have hr : SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε (x-y) ≠ 0 := by
      intro hz
      apply hy
      change (scaledMollifierTest ρ hρ ε : Tests 𝕜 ⊤) (x-y) = 0
      rw [scaledMollifierTest_apply ρ hρ ε hε.ne', hz]
      simp
    have hz : x-y ∈ Metric.closedBall (0 : Domain d) 1 :=
      Metric.ball_subset_closedBall (hεs hr)
    exact Or.inr ⟨(x,x-y), ⟨hx,hz⟩, sub_sub_cancel x y⟩
  · exact K.isCompact.isClosed


/-- Integrate the jets of a smoothing test against an outer test. -/
def integratedReflectedJet
    (φ ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (m : ℕ) : FiniteJet 𝕜 d m :=
  ∫ x, ψ x • reflectedJet φ m x

theorem integratedReflectedJet_integrable
    (φ ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (m : ℕ) :
    Integrable (fun x => ψ x • reflectedJet φ m x) := by
  exact (ψ.continuous.smul (reflectedJet_contDiff φ m).continuous).integrable_of_hasCompactSupport
    ψ.hasCompactSupport.smul_right

theorem integratedReflectedJet_apply
    (φ ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (m : ℕ)
    (a : FiniteJetIndex d m) (y : Domain d) :
    integratedReflectedJet φ ψ m a y =
      ∫ x, ψ x * reflectedCoordinateFunction φ a.2 (x-y) := by
  let ev : FiniteJet 𝕜 d m →L[𝕜] 𝕜 :=
    (BoundedContinuousFunction.evalCLM 𝕜 y).comp (ContinuousLinearMap.proj a)
  have he := ev.integral_comp_comm (integratedReflectedJet_integrable φ ψ m)
  exact he.symm

theorem distributionConvolution_transpose_finiteJet
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (φ ψ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (K : Compacts (Domain d))
    (hK : ∀ x ∈ tsupport ψ, tsupport (reflectedTranslate φ x) ⊆ K)
    (m : ℕ) (L : FiniteJet 𝕜 d m →L[𝕜] 𝕜)
    (hL : ∀ θ : Step 𝕜 K,
      L (finiteJetMap K m θ) = u (TestFunction.ofSupportedIn
        (Ω := (⊤ : Opens (Domain d))) (show (K : Set (Domain d)) ⊆
        (⊤ : Opens (Domain d)) from subset_univ _) θ)) :
    (∫ x, distributionConvolution u φ x * ψ x) = L (integratedReflectedJet φ ψ m) := by
  unfold integratedReflectedJet
  rw [← L.integral_comp_comm (integratedReflectedJet_integrable φ ψ m)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport ψ
  · rw [map_smul, reflectedJet_eq_finiteJetMap φ m K x (hK x hx), hL]
    change _ = ψ x * u (reflectedTranslate φ x)
    exact mul_comm _ _
  · have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hz]

/-- Moving the derivatives off the smoothing kernel in the integrated finite jet. -/
theorem integratedReflectedJet_apply_by_parts
    (φ ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (m : ℕ)
    (a : FiniteJetIndex d m) (y : Domain d) :
    integratedReflectedJet φ ψ m a y =
      ∫ z, φ z * iteratedFDeriv ℝ a.1.val ψ (z+y)
        (fun j => coordinateVector (a.2 j)) := by
  rw [integratedReflectedJet_apply]
  let g : Domain d → 𝕜 := fun z => ψ (z+y)
  have hg : ContDiff ℝ ∞ g := ψ.contDiff.comp (contDiff_id.add contDiff_const)
  have hgs : HasCompactSupport g := ψ.hasCompactSupport.comp_isClosedEmbedding
    (Homeomorph.addRight y).isClosedEmbedding
  calc
    _ = ∫ z, reflectedCoordinateFunction φ a.2 z * ψ (z+y) := by
      have ht := integral_sub_right_eq_self (μ := (volume : Measure (Domain d)))
        (fun z => reflectedCoordinateFunction φ a.2 z * ψ (z+y)) y
      simpa only [sub_add_cancel, mul_comm] using ht
    _ = ∫ z, φ z * iteratedFDeriv ℝ a.1.val g z
        (fun j => coordinateVector (a.2 j)) :=
      integral_iteratedFDeriv_neg_mul _ φ g φ.contDiff φ.hasCompactSupport
        hg hgs (fun j => coordinateVector (a.2 j))
    _ = _ := by simp only [g, iteratedFDeriv_comp_add_right]

open SmoothApproximateIdentitiesSpec

theorem mollifier_reflection (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) :
    IsMollifier (fun x => ρ (-x)) := by
  refine ⟨hρ.1.comp contDiff_neg, ?_, fun x => hρ.2.2.1 (-x), ?_⟩
  · exact hρ.2.1.comp_isClosedEmbedding (Homeomorph.neg (Domain d)).isClosedEmbedding
  · rw [integral_neg_eq_self, hρ.2.2.2]

theorem scaledKernel_reflection (ρ : Domain d → ℝ) (ε : ℝ) (x : Domain d) :
    ScaledKernelValue (fun y => ρ (-y)) ε x = ScaledKernelValue ρ ε (-x) := by
  simp [ScaledKernelValue]

theorem finiteJetMap_uniformContinuous (K : Compacts (Domain d)) (m : ℕ)
    (ψ : Step 𝕜 K) (a : FiniteJetIndex d m) :
    UniformContinuous (finiteJetMap K m ψ a) := by
  have hreg := iteratedFDeriv_evaluation_regular (ψ : Domain d → 𝕜) ψ.contDiff
    ψ.hasCompactSupport (fun j => coordinateVector (a.2 j))
  have heq : (finiteJetMap K m ψ a : Domain d → 𝕜) =
      fun x => iteratedFDeriv ℝ a.1.val ψ x (fun j => coordinateVector (a.2 j)) := by
    funext x
    exact finiteJetMap_apply K m ψ a x
  rw [heq]
  exact hreg.1.continuous.uniformContinuous_of_tendsto_cocompact hreg.2.is_zero_at_infty

theorem integral_scaledKernel_mul_add (ρ : Domain d → ℝ) (ε : ℝ)
    (g : Domain d → 𝕜) (y : Domain d) :
    (∫ x, (ScaledKernelValue ρ ε x : 𝕜) * g (x+y)) =
      MollifyValue (fun x => ρ (-x)) ε g y := by
  rw [← integral_neg_eq_self (fun x => (ScaledKernelValue ρ ε x : 𝕜) * g (x+y)) volume]
  unfold MollifyValue convolution
  apply integral_congr_ae
  filter_upwards with x
  change (ScaledKernelValue ρ ε (-x) : 𝕜) * g (-x+y) =
    ScaledKernelValue (fun x => ρ (-x)) ε x • g (y-x)
  rw [scaledKernel_reflection, RCLike.real_smul_eq_coe_mul]
  congr 2
  abel_nf

theorem finiteJet_tendsto_of_kernel_add_values
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) (m : ℕ)
    (g : FiniteJet 𝕜 d m) (hg : ∀ a, UniformContinuous (g a))
    (F : ℝ → FiniteJet 𝕜 d m)
    (hF : ∀ ε > 0, ∀ a y, F ε a y =
      ∫ x, (ScaledKernelValue ρ ε x : 𝕜) * g a (x+y)) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 g) := by
  apply tendsto_pi_nhds.mpr
  intro a
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
  have ht := mollify_uniform (fun x => ρ (-x)) (mollifier_reflection ρ hρ) (g a) (hg a)
  have heq : (fun ε => MollifyValue (fun x => ρ (-x)) ε (g a)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => (F ε a : Domain d → 𝕜)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    funext y
    rw [hF ε hε a y, integral_scaledKernel_mul_add]
  exact (tendstoUniformly_congr heq).mp ht

theorem integratedReflectedJet_mollifier_tendsto
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ)
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (m : ℕ) (K : Compacts (Domain d))
    (hψ : tsupport ψ ⊆ K) :
    Tendsto (fun ε => integratedReflectedJet (scaledMollifierTest ρ hρ ε) ψ m)
      (𝓝[>] (0 : ℝ))
      (𝓝 (finiteJetMap K m (ContDiffMapSupportedIn.of_support_subset ψ.contDiff
        ((subset_tsupport ψ).trans hψ)))) := by
  apply finiteJet_tendsto_of_kernel_add_values ρ hρ m _ (finiteJetMap_uniformContinuous K m _)
  intro ε hε a y
  rw [integratedReflectedJet_apply_by_parts]
  apply integral_congr_ae
  filter_upwards with x
  rw [scaledMollifierTest_apply ρ hρ ε hε.ne', finiteJetMap_apply]
  rfl

/-- Smooth regularizations converge to the original distribution on every test. -/
theorem distributionConvolution_approximation :
    Specs.ExpandedFA.Distributions.DistributionRegularization.approximationType := by
  intro 𝕜 _ d u ρ hρ ψ
  obtain ⟨K, hψ, hK⟩ := scaledMollifier_reflected_common_support ρ hρ ψ
  obtain ⟨m, L, hL⟩ := distribution_finiteJet_factorization u K
  have ht := L.continuous.tendsto _ |>.comp
    (integratedReflectedJet_mollifier_tendsto ρ hρ ψ m K hψ)
  rw [hL] at ht
  change Tendsto (fun ε => L (integratedReflectedJet (scaledMollifierTest ρ hρ ε) ψ m))
    (𝓝[>] (0 : ℝ)) (𝓝 (u ψ)) at ht
  apply ht.congr'
  filter_upwards [hK] with ε hε
  exact (distributionConvolution_transpose_finiteJet u
    (scaledMollifierTest ρ hρ ε) ψ K hε m L hL).symm


end ExpandedFA.Distributions
