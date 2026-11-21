import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SmoothDistributionPullback
import MathGenome.Internal.FourierSobolev.P102.U4.TestSpace
import MathGenome.Internal.FourierSobolev.P102.U4.RegularDerivatives
import MathGenome.Internal.FourierSobolev.P102.U4.LocalOrder
import MathGenome.Internal.FourierSobolev.P102.U4.ChainProduct
import MathGenome.Internal.FourierSobolev.P102.U4.Truncations
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Function.Jacobian

import MathGenome.Internal.FourierSobolev.P102.U4.BiLipschitzPullback
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions ENNReal Topology
namespace P102.U4

namespace SmoothChart

variable {d : ℕ} {U V W : Opens (Space d)}

lemma hasFDerivAt (g : SmoothChart U V) {x : Space d} (hx : x ∈ V) :
    HasFDerivAt g.toFun (fderiv ℝ g.toFun x) x :=
  (g.smooth.contDiffAt (V.isOpen.mem_nhds hx)).differentiableAt (by simp) |>.hasFDerivAt

lemma inv_hasFDerivAt (g : SmoothChart U V) {y : Space d} (hy : y ∈ U) :
    HasFDerivAt g.invFun (fderiv ℝ g.invFun y) y :=
  (g.inv_smooth.contDiffAt (U.isOpen.mem_nhds hy)).differentiableAt (by simp) |>.hasFDerivAt

lemma inverseJacobian_comp (g : SmoothChart U V) (h : SmoothChart V W)
    {y : Space d} (hy : y ∈ U) :
    (g.comp h).inverseJacobian y =
      g.inverseJacobian y * h.inverseJacobian (g.invFun y) := by
  have hd := (h.inv_hasFDerivAt (g.inv_mapsTo hy)).comp y (g.inv_hasFDerivAt hy)
  unfold inverseJacobian
  change |(fderiv ℝ (h.invFun ∘ g.invFun) y).det| = _
  rw [hd.fderiv]
  change |LinearMap.det ((fderiv ℝ h.invFun (g.invFun y)).toLinearMap.comp
    (fderiv ℝ g.invFun y).toLinearMap)| = _
  rw [LinearMap.det_comp, abs_mul, mul_comm]

@[simp] lemma inverseJacobian_refl (U : Opens (Space d)) (x : Space d) :
    (refl U).inverseJacobian x = 1 := by
  simp [inverseJacobian, refl, fderiv_id, ContinuousLinearMap.det]

lemma transportFunction_refl {𝕜 : Type} [RCLike 𝕜] (U : Opens (Space d))
    (φ : TestSpace 𝕜 U) : (refl U).transportFunction φ = φ := by
  funext x
  by_cases hx : x ∈ U
  · simp only [transportFunction, indicator_of_mem hx, inverseJacobian_refl]
    exact one_smul ℝ (φ x)
  · simp [transportFunction, hx, φ.zero_on_compl hx]

lemma transportFunction_comp {𝕜 : Type} [RCLike 𝕜]
    (g : SmoothChart U V) (h : SmoothChart V W) (φ : Space d → 𝕜) :
    (g.comp h).transportFunction φ = g.transportFunction (h.transportFunction φ) := by
  funext y
  by_cases hy : y ∈ U
  · simp only [transportFunction, indicator_of_mem hy,
      indicator_of_mem (g.inv_mapsTo hy)]
    rw [inverseJacobian_comp g h hy, mul_smul]
    rfl
  · simp [transportFunction, hy]

/-- The support moves by the forward chart. This uses the indicator at U,
so it places no condition on the ambient representative outside U. -/
lemma support_transport_subset {𝕜 : Type} [RCLike 𝕜]
    (g : SmoothChart U V) (φ : Space d → 𝕜) :
    Function.support (g.transportFunction φ) ⊆ g.toFun '' Function.support φ := by
  intro y hy
  have hyU : y ∈ U := by
    by_contra hn
    exact hy (by simp [transportFunction, hn])
  refine ⟨g.invFun y, ?_, g.right_inv y hyU⟩
  intro hz
  exact hy (by simp [transportFunction, hyU, hz])

lemma tsupport_transport_subset {𝕜 : Type} [RCLike 𝕜]
    (g : SmoothChart U V) (φ : TestSpace 𝕜 V) :
    tsupport (g.transportFunction φ) ⊆ g.toFun '' tsupport φ := by
  apply closure_minimal
  · exact (g.support_transport_subset φ).trans (image_mono subset_closure)
  · exact (φ.hasCompactSupport.image_of_continuousOn
      (g.smooth.continuousOn.mono φ.tsupport_subset)).isClosed

/-- The differential of the inverse is nonsingular at every point of U. -/
lemma inv_det_ne_zero (g : SmoothChart U V) {y : Space d} (hy : y ∈ U) :
    (fderiv ℝ g.invFun y).det ≠ 0 := by
  have hd := (g.hasFDerivAt (g.inv_mapsTo hy)).comp y (g.inv_hasFDerivAt hy)
  have he : id =ᶠ[𝓝 y] g.toFun ∘ g.invFun := by
    filter_upwards [U.isOpen.mem_nhds hy] with z hz
    exact (g.right_inv z hz).symm
  have hc := (hd.congr_of_eventuallyEq he).unique (hasFDerivAt_id y)
  have hdet := congrArg ContinuousLinearMap.det hc
  change LinearMap.det ((fderiv ℝ g.toFun (g.invFun y)).toLinearMap.comp
    (fderiv ℝ g.invFun y).toLinearMap) = LinearMap.det LinearMap.id at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  intro hn
  change LinearMap.det (fderiv ℝ g.invFun y).toLinearMap = 0 at hn
  rw [hn, mul_zero] at hdet
  exact zero_ne_one hdet

/-- The determinant is a finite polynomial in the entries of the differential. -/
private lemma contDiffOn_det {F : Space d → (Space d →L[ℝ] Space d)}
    {S : Set (Space d)} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (F y).det) S := by
  classical
  have he (y : Space d) : (F y).det =
      ∑ σ : Equiv.Perm (Fin d), Equiv.Perm.sign σ •
        ∏ i : Fin d, (F y (coordinateVector d i)) (σ i) := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis, Matrix.det_apply]
    congr 1
    funext σ
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp [LinearMap.toMatrix_apply, coordinateVector]
  simp_rw [he]
  apply ContDiffOn.sum
  intro σ _
  apply ContDiffOn.const_smul
  apply contDiffOn_prod
  intro i _
  exact (EuclideanSpace.proj (σ i)).contDiff.comp_contDiffOn
    (hF.clm_apply contDiffOn_const)

lemma inverseJacobian_smooth (g : SmoothChart U V) :
    ContDiffOn ℝ (⊤ : ℕ∞) g.inverseJacobian U := by
  exact (contDiffOn_det (g.inv_smooth.fderiv_of_isOpen U.isOpen (by simp))).abs
    (fun _ hy => g.inv_det_ne_zero hy)

/-- The transported expression is an actual globally smooth, compactly
supported U-test, using the canonical zero-extension representation. -/
def transportTest {𝕜 : Type} [RCLike 𝕜] (g : SmoothChart U V)
    (φ : TestSpace 𝕜 V) : TestSpace 𝕜 U := by
  have hs := g.tsupport_transport_subset φ
  have hc : IsCompact (g.toFun '' tsupport φ) :=
    φ.hasCompactSupport.image_of_continuousOn
      (g.smooth.continuousOn.mono φ.tsupport_subset)
  have hsub : tsupport (g.transportFunction φ) ⊆ U :=
    hs.trans (image_subset_iff.mpr (fun _ hx => g.mapsTo (φ.tsupport_subset hx)))
  refine ⟨g.transportFunction φ, ?_, hc.of_isClosed_subset isClosed_closure hs, hsub⟩
  apply smoothZeroExtension d 𝕜 U _ _ hsub
  exact (g.inverseJacobian_smooth.smul
    (φ.contDiff.contDiffOn.comp g.inv_smooth (mapsTo_univ _ _))).congr
      (fun y hy => by simp [transportFunction, hy])

@[simp] lemma transportTest_apply {𝕜 : Type} [RCLike 𝕜] (g : SmoothChart U V)
    (φ : TestSpace 𝕜 V) (y : Space d) : transportTest g φ y = g.transportFunction φ y := rfl

/-- The forward image is compact and remains inside the target open set. -/
def imageCompact (g : SmoothChart U V) (K : Compacts (Space d))
    (hK : (K : Set (Space d)) ⊆ V) : Compacts (Space d) :=
  ⟨g.toFun '' (K : Set (Space d)),
    K.isCompact.image_of_continuousOn (g.smooth.continuousOn.mono hK)⟩

lemma imageCompact_subset (g : SmoothChart U V) (K : Compacts (Space d))
    (hK : (K : Set (Space d)) ⊆ V) : (g.imageCompact K hK : Set (Space d)) ⊆ U := by
  rintro y ⟨x, hx, rfl⟩
  exact g.mapsTo (hK hx)

private lemma compact_derivative_bounds (g : SmoothChart U V)
    (J : Compacts (Space d)) (hJ : (J : Set (Space d)) ⊆ U) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ n, ∀ y ∈ J,
      ‖iteratedFDerivWithin ℝ i g.invFun U y‖ ≤ D ∧
      ‖iteratedFDerivWithin ℝ i g.inverseJacobian U y‖ ≤ D := by
  have H (i : Fin (n+1)) : ∃ c : ℝ, 1 ≤ c ∧ ∀ y ∈ J,
      ‖iteratedFDerivWithin ℝ i.val g.invFun U y‖ ≤ c ∧
      ‖iteratedFDerivWithin ℝ i.val g.inverseJacobian U y‖ ≤ c := by
    obtain ⟨a, ha⟩ := J.isCompact.exists_bound_of_continuousOn
      ((g.inv_smooth.continuousOn_iteratedFDerivWithin (by simp)
        U.isOpen.uniqueDiffOn).mono hJ)
    obtain ⟨b, hb⟩ := J.isCompact.exists_bound_of_continuousOn
      ((g.inverseJacobian_smooth.continuousOn_iteratedFDerivWithin (by simp)
        U.isOpen.uniqueDiffOn).mono hJ)
    exact ⟨max 1 (max a b), le_max_left _ _, fun y hy =>
      ⟨(ha y hy).trans ((le_max_left a b).trans (le_max_right _ _)),
       (hb y hy).trans ((le_max_right a b).trans (le_max_right _ _))⟩⟩
  choose c hc hc' using H
  refine ⟨1 + ∑ i, c i, ?_, ?_⟩
  · have : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ => (hc i).trans' zero_le_one)
    linarith
  · intro i hi y hy
    let j : Fin (n+1) := ⟨i, by omega⟩
    have hj : c j ≤ 1 + ∑ i, c i := by
      have := Finset.single_le_sum (s := Finset.univ)
        (fun k _ => (hc k).trans' zero_le_one) (Finset.mem_univ j)
      linarith
    exact ⟨((hc' j y hy).1).trans hj, ((hc' j y hy).2).trans hj⟩

/-- The finite order estimate is proved within U; no smooth extension of the
chart to the boundary or globally bounded derivatives are assumed. -/
lemma transport_derivative_bound {𝕜 : Type} [RCLike 𝕜]
    (g : SmoothChart U V) (K : Compacts (Space d))
    (hK : (K : Set (Space d)) ⊆ V) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : FixedSupport d 𝕜 K)
      (y : Space d), y ∈ g.imageCompact K hK →
      ‖iteratedFDeriv ℝ m (g.transportFunction φ) y‖ ≤
        C * frechetSupSeminorm 𝕜 K m φ := by
  obtain ⟨D, hD, hb⟩ := g.compact_derivative_bounds (g.imageCompact K hK)
    (g.imageCompact_subset K hK) m
  let C : ℝ := ∑ i ∈ Finset.range (m+1),
    (m.choose i : ℝ) * D * (m-i).factorial * D ^ (m-i)
  refine ⟨C, Finset.sum_nonneg (fun _ _ => by positivity), ?_⟩
  intro φ y hy
  have hyU := g.imageCompact_subset K hK hy
  have heq : EqOn (g.transportFunction φ)
      (fun z => g.inverseJacobian z • φ (g.invFun z)) U :=
    fun z hz => by simp [transportFunction, hz]
  rw [← iteratedFDerivWithin_of_isOpen m U.isOpen hyU,
    iteratedFDerivWithin_congr heq hyU m]
  have hcomp (k : ℕ) (hk : k ≤ m) :
      ‖iteratedFDerivWithin ℝ k (φ ∘ g.invFun) U y‖ ≤
        k.factorial * frechetSupSeminorm 𝕜 K m φ * D ^ k := by
    apply norm_iteratedFDerivWithin_comp_le φ.contDiff.contDiffOn g.inv_smooth
      (by simp) uniqueDiffOn_univ U.isOpen.uniqueDiffOn (mapsTo_univ _ _) hyU
    · intro i hi
      rw [iteratedFDerivWithin_univ]
      exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜).trans
        ((Finset.le_sup (f := ContDiffMapSupportedIn.seminorm 𝕜 (Space d) 𝕜 ⊤ K)
          (Finset.mem_Iic.mpr (hi.trans hk))) φ)
    · intro i hi hik
      exact ((hb i (hik.trans hk) y hy).1).trans
        (by simpa using pow_le_pow_right₀ hD hi)
  calc
    _ ≤ ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i g.inverseJacobian U y‖ *
        ‖iteratedFDerivWithin ℝ (m-i) (φ ∘ g.invFun) U y‖ :=
      norm_iteratedFDerivWithin_smul_le g.inverseJacobian_smooth
        (φ.contDiff.contDiffOn.comp g.inv_smooth (mapsTo_univ _ _))
        U.isOpen.uniqueDiffOn hyU (by simp)
    _ ≤ ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * D *
        ((m-i).factorial * frechetSupSeminorm 𝕜 K m φ * D ^ (m-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      gcongr
      · exact (hb i him y hy).2
      · exact hcomp (m-i) (Nat.sub_le _ _)
    _ = C * frechetSupSeminorm 𝕜 K m φ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The fixed-support map with the exact transported support. -/
def stageTransport {𝕜 : Type} [RCLike 𝕜] (g : SmoothChart U V)
    (K : Compacts (Space d)) (hK : (K : Set (Space d)) ⊆ V) :
    FixedSupport d 𝕜 K →L[𝕜] FixedSupport d 𝕜 (g.imageCompact K hK) :=
  ContDiffMapSupportedIn.mkCLM 𝕜 (fun φ => g.transportFunction φ)
    (by intro φ ψ x; by_cases hx : x ∈ U <;>
        simp [transportFunction, hx, smul_add])
    (by intro c φ x; by_cases hx : x ∈ U <;>
        simp [transportFunction, hx])
    (fun φ => (g.transportTest (stageInclusion 𝕜 hK φ)).contDiff)
    (by
      intro φ x hx
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hx ((image_mono φ.tsupport_subset)
        (g.tsupport_transport_subset (stageInclusion 𝕜 hK φ) h)))
    (by
      intro m _
      obtain ⟨C, hC, hb⟩ := g.transport_derivative_bound (𝕜 := 𝕜) K hK m
      exact ⟨Finset.Iic m, C, hC, hb⟩)

/-- Continuity follows from the fixed-support maps and the final locally
convex test topology. -/
def testTransport {𝕜 : Type} [RCLike 𝕜] (g : SmoothChart U V) :
    TestSpace 𝕜 V →L[𝕜] TestSpace 𝕜 U :=
  TestFunction.mkCLM 𝕜 g.transportTest
    (by intro φ ψ; ext x; by_cases hx : x ∈ U <;>
        simp [transportFunction, hx, smul_add])
    (by intro c φ; ext x; by_cases hx : x ∈ U <;>
        simp [transportFunction, hx])
    (by
      intro K hK
      exact ((stageInclusion 𝕜 (g.imageCompact_subset K hK)).comp
        (g.stageTransport K hK)).continuous)

lemma testTransport_graph {𝕜 : Type} [RCLike 𝕜] (g : SmoothChart U V) :
    g.HasTestTransportGraph (g.testTransport (𝕜 := 𝕜)) := fun _ _ => rfl

lemma injOn (g : SmoothChart U V) : InjOn g.toFun V := by
  intro x hx y hy he
  rw [← g.left_inv x hx, ← g.left_inv y hy, he]

lemma inv_image (g : SmoothChart U V) : g.invFun '' (U : Set (Space d)) = V := by
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact g.inv_mapsTo hy
  · intro x hx
    exact ⟨g.toFun x, g.mapsTo hx, g.left_inv x hx⟩

/-- Local integrability follows by change of variables on each compact set,
then division by the nonvanishing, continuous forward Jacobian there. -/
lemma locallyIntegrableOn_comp {𝕜 : Type} [RCLike 𝕜]
    (g : SmoothChart U V) (f : Space d → 𝕜) (hf : LocallyIntegrableOn f U volume) :
    LocallyIntegrableOn (f ∘ g.toFun) V volume := by
  apply (locallyIntegrableOn_iff V.isOpen.isLocallyClosed).mpr
  intro K hK hcompact
  have himg : IsCompact (g.toFun '' K) :=
    hcompact.image_of_continuousOn (g.smooth.continuousOn.mono hK)
  have himgU : g.toFun '' K ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact g.mapsTo (hK hx)
  have hi := hf.integrableOn_compact_subset himgU himg
  have hw := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    hcompact.measurableSet (fun x hx => (g.hasFDerivAt (hK hx)).hasFDerivWithinAt)
      (g.injOn.mono hK) f).mp hi
  have hn (x : Space d) (hx : x ∈ K) : g.symm.inverseJacobian x ≠ 0 :=
    abs_ne_zero.mpr (g.symm.inv_det_ne_zero (hK hx))
  have hc : ContinuousOn (fun x => (g.symm.inverseJacobian x)⁻¹) K :=
    (g.symm.inverseJacobian_smooth.continuousOn.mono hK).inv₀ hn
  have h := hw.continuousOn_smul hc hcompact
  apply h.congr_fun _ hcompact.measurableSet
  intro x hx
  exact inv_smul_smul₀ (hn x hx) _

lemma regular_comp {𝕜 : Type} [RCLike 𝕜] (g : SmoothChart U V)
    (A : TestSpace 𝕜 V →L[𝕜] TestSpace 𝕜 U) (hA : g.HasTestTransportGraph A)
    (f : Space d → 𝕜) (hf : LocallyIntegrableOn f U volume) :
    (regularDistribution U f).comp A = regularDistribution V (f ∘ g.toFun) := by
  have hcomp := g.locallyIntegrableOn_comp f hf
  ext φ
  change regularDistribution U f (A φ) = regularDistribution V (f ∘ g.toFun) φ
  rw [regular_pairing d 𝕜 U f hf, regular_pairing d 𝕜 V _ hcomp]
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume
    U.isOpen.measurableSet (fun y hy => (g.inv_hasFDerivAt hy).hasFDerivWithinAt)
    g.symm.injOn (fun x => (f ∘ g.toFun) x * φ x)
  rw [g.inv_image] at hcov
  rw [hcov]
  apply setIntegral_congr_fun U.isOpen.measurableSet
  intro y hy
  dsimp only
  rw [hA φ y]
  simp only [transportFunction, indicator_of_mem hy, Function.comp_apply,
    g.right_inv y hy, inverseJacobian, mul_smul_comm]

/-- Transposition is strongly continuous as soon as the test transport has
been constructed. This is an actual CLM between the ordinary dual spaces. -/
def transpose {𝕜 : Type} [RCLike 𝕜]
    (A : TestSpace 𝕜 V →L[𝕜] TestSpace 𝕜 U) :
    DistributionSpace 𝕜 U →L[𝕜] DistributionSpace 𝕜 V :=
  ContinuousLinearMap.precomp 𝕜 A

@[simp] lemma transpose_apply {𝕜 : Type} [RCLike 𝕜]
    (A : TestSpace 𝕜 V →L[𝕜] TestSpace 𝕜 U)
    (T : DistributionSpace 𝕜 U) (φ : TestSpace 𝕜 V) :
    transpose A T φ = T (A φ) := rfl

end SmoothChart

theorem smoothDistribution_admissibility_conditional
    (_hDerivative : BiLipschitzPullbackExpected.Derivative)
    (_hDistortion : BiLipschitzPullbackExpected.Distortion)
    (_hLp : BiLipschitzPullbackExpected.LpPullback)
    (_hSobolev : BiLipschitzPullbackExpected.SobolevPullback) :
    SmoothDistributionPullbackExpected.Admissibility := by
  intro d 𝕜 _ U V g φ
  exact ⟨g.transportTest φ, fun _ => rfl, g.tsupport_transport_subset φ⟩

theorem smoothDistribution_fixedSupportContinuity_conditional
    (_hDerivative : BiLipschitzPullbackExpected.Derivative)
    (_hDistortion : BiLipschitzPullbackExpected.Distortion)
    (_hLp : BiLipschitzPullbackExpected.LpPullback)
    (_hSobolev : BiLipschitzPullbackExpected.SobolevPullback) :
    SmoothDistributionPullbackExpected.FixedSupportContinuity := by
  intro d 𝕜 _ U V g K hK
  let J := g.imageCompact K hK
  let A := g.stageTransport (𝕜 := 𝕜) K hK
  refine ⟨J, g.imageCompact_subset K hK, A, rfl, fun _ _ => rfl, ?_⟩
  intro m
  let q : Seminorm 𝕜 (FixedSupport d 𝕜 K) :=
    (coordinateSupSeminorm 𝕜 J m).comp A.toLinearMap
  have hq : Continuous q :=
    ((coordinateStageTopology d 𝕜 J).continuous_seminorm m).comp A.continuous
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous
    (coordinateStageTopology d 𝕜 K) q hq
  refine ⟨C, C.coe_nonneg, s.sup id, fun φ => ?_⟩
  have hs : s.sup (coordinateSupSeminorm 𝕜 K) ≤
      coordinateSupSeminorm 𝕜 K (s.sup id) := by
    apply Finset.sup_le
    intro n hn
    exact coordinateSupSeminorm_monotone 𝕜 K (Finset.le_sup (f := id) hn)
  exact (hC φ).trans (mul_le_mul_of_nonneg_left (hs φ) C.coe_nonneg)

theorem smoothDistribution_construction_conditional
    (_hDerivative : BiLipschitzPullbackExpected.Derivative)
    (_hDistortion : BiLipschitzPullbackExpected.Distortion)
    (_hLp : BiLipschitzPullbackExpected.LpPullback)
    (_hSobolev : BiLipschitzPullbackExpected.SobolevPullback) :
    SmoothDistributionPullbackExpected.Construction := by
  intro d 𝕜 _ U V g
  exact ⟨g.testTransport, g.testTransport_graph,
    SmoothChart.transpose g.testTransport, fun _ _ => rfl⟩

theorem smoothDistribution_regularCompatibility_conditional
    (_hDerivative : BiLipschitzPullbackExpected.Derivative)
    (_hDistortion : BiLipschitzPullbackExpected.Distortion)
    (_hLp : BiLipschitzPullbackExpected.LpPullback)
    (_hSobolev : BiLipschitzPullbackExpected.SobolevPullback) :
    SmoothDistributionPullbackExpected.RegularCompatibility := by
  intro d 𝕜 _ U V g A hA f hf
  exact ⟨g.locallyIntegrableOn_comp f hf, g.regular_comp A hA f hf⟩

/-- Identity in the exact ordered conditional contract. -/
theorem smoothDistribution_identity_conditional
    (_hDerivative : BiLipschitzPullbackExpected.Derivative)
    (_hDistortion : BiLipschitzPullbackExpected.Distortion)
    (_hLp : BiLipschitzPullbackExpected.LpPullback)
    (_hSobolev : BiLipschitzPullbackExpected.SobolevPullback) :
    SmoothDistributionPullbackExpected.Identity := by
  intro d 𝕜 _ U A hA
  have he : A = ContinuousLinearMap.id 𝕜 _ := by
    ext φ x
    change A φ x = φ x
    simpa only [SmoothChart.transportFunction_refl] using hA φ x
  exact ⟨he, fun T => by rw [he]; rfl⟩

/-- Determinant factors and the contravariant distribution law. -/
theorem smoothDistribution_composition_conditional
    (_hDerivative : BiLipschitzPullbackExpected.Derivative)
    (_hDistortion : BiLipschitzPullbackExpected.Distortion)
    (_hLp : BiLipschitzPullbackExpected.LpPullback)
    (_hSobolev : BiLipschitzPullbackExpected.SobolevPullback) :
    SmoothDistributionPullbackExpected.Composition := by
  intro d 𝕜 _ U V W g h
  refine ⟨fun _ hy => g.inverseJacobian_comp h hy, ?_⟩
  intro Ag Ah Agh hg hh hgh
  have he : Agh = Ag.comp Ah := by
    ext φ y
    rw [hgh, ContinuousLinearMap.comp_apply, hg]
    rw [g.transportFunction_comp]
    congr 1
    funext x
    exact (hh φ x).symm
  exact ⟨he, fun T => by rw [he]; rfl⟩

/-- The complete previously supplied weak calculus, with the four pending
coordinate results used only as explicit parameters. -/
theorem smoothDistribution_retainedClauses_conditional
    (hDerivative : BiLipschitzPullbackExpected.Derivative)
    (hDistortion : BiLipschitzPullbackExpected.Distortion)
    (hLp : BiLipschitzPullbackExpected.LpPullback)
    (hSobolev : BiLipschitzPullbackExpected.SobolevPullback) :
    SmoothDistributionPullbackExpected.RetainedClauses :=
  ⟨chain_rule, product_rule, truncation_level_set, truncation_rule,
    lower_truncation_rule, upper_truncation_rule,
    hDerivative, hDistortion, hLp, hSobolev⟩

end P102.U4

theorem _root_.«P102».«U4».«smoothDistribution_admissibility» : _root_.«P102».«U4».«SmoothDistributionPullbackExpected».«Admissibility» :=
  @_root_.«P102».«U4».«smoothDistribution_admissibility_conditional» (@_root_.«P102».«U4».«bilipschitz_derivative») (@_root_.«P102».«U4».«bilipschitz_distortion») (@_root_.«P102».«U4».«bilipschitz_lpPullback») (@_root_.«P102».«U4».«bilipschitz_sobolevPullback»)
theorem _root_.«P102».«U4».«smoothDistribution_composition» : _root_.«P102».«U4».«SmoothDistributionPullbackExpected».«Composition» :=
  @_root_.«P102».«U4».«smoothDistribution_composition_conditional» (@_root_.«P102».«U4».«bilipschitz_derivative») (@_root_.«P102».«U4».«bilipschitz_distortion») (@_root_.«P102».«U4».«bilipschitz_lpPullback») (@_root_.«P102».«U4».«bilipschitz_sobolevPullback»)
theorem _root_.«P102».«U4».«smoothDistribution_construction» : _root_.«P102».«U4».«SmoothDistributionPullbackExpected».«Construction» :=
  @_root_.«P102».«U4».«smoothDistribution_construction_conditional» (@_root_.«P102».«U4».«bilipschitz_derivative») (@_root_.«P102».«U4».«bilipschitz_distortion») (@_root_.«P102».«U4».«bilipschitz_lpPullback») (@_root_.«P102».«U4».«bilipschitz_sobolevPullback»)
theorem _root_.«P102».«U4».«smoothDistribution_fixedSupportContinuity» : _root_.«P102».«U4».«SmoothDistributionPullbackExpected».«FixedSupportContinuity» :=
  @_root_.«P102».«U4».«smoothDistribution_fixedSupportContinuity_conditional» (@_root_.«P102».«U4».«bilipschitz_derivative») (@_root_.«P102».«U4».«bilipschitz_distortion») (@_root_.«P102».«U4».«bilipschitz_lpPullback») (@_root_.«P102».«U4».«bilipschitz_sobolevPullback»)
theorem _root_.«P102».«U4».«smoothDistribution_identity» : _root_.«P102».«U4».«SmoothDistributionPullbackExpected».«Identity» :=
  @_root_.«P102».«U4».«smoothDistribution_identity_conditional» (@_root_.«P102».«U4».«bilipschitz_derivative») (@_root_.«P102».«U4».«bilipschitz_distortion») (@_root_.«P102».«U4».«bilipschitz_lpPullback») (@_root_.«P102».«U4».«bilipschitz_sobolevPullback»)
theorem _root_.«P102».«U4».«smoothDistribution_regularCompatibility» : _root_.«P102».«U4».«SmoothDistributionPullbackExpected».«RegularCompatibility» :=
  @_root_.«P102».«U4».«smoothDistribution_regularCompatibility_conditional» (@_root_.«P102».«U4».«bilipschitz_derivative») (@_root_.«P102».«U4».«bilipschitz_distortion») (@_root_.«P102».«U4».«bilipschitz_lpPullback») (@_root_.«P102».«U4».«bilipschitz_sobolevPullback»)
theorem _root_.«P102».«U4».«smoothDistribution_retainedClauses» : _root_.«P102».«U4».«SmoothDistributionPullbackExpected».«RetainedClauses» :=
  @_root_.«P102».«U4».«smoothDistribution_retainedClauses_conditional» (@_root_.«P102».«U4».«bilipschitz_derivative») (@_root_.«P102».«U4».«bilipschitz_distortion») (@_root_.«P102».«U4».«bilipschitz_lpPullback») (@_root_.«P102».«U4».«bilipschitz_sobolevPullback»)
