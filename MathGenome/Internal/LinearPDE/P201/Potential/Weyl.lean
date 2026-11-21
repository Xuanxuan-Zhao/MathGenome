import MathGenome.Internal.LinearPDE.P201Specs.Potential.Weyl
import MathGenome.Internal.LinearPDE.P201.Potential.MeanValues
import MathGenome.Internal.FourierSobolev.P102.U4.LocalConvolution
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionMollification
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionSupport
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Metric MeasureTheory TopologicalSpace Filter
open scoped ContDiff Topology

namespace P201.Weyl

theorem continuous_representative_unique :
    P201Specs.Weyl.ContinuousRepresentativeUniqueStatement := by
  intro n 𝕜 _ Ω u v hu hv he
  exact Measure.eqOn_open_of_ae_eq
    ((P102.U4.regular_injectivity n 𝕜 Ω u v
      (hu.locallyIntegrableOn Ω.isOpen.measurableSet)
      (hv.locallyIntegrableOn Ω.isOpen.measurableSet)).mp he) Ω.isOpen hu hv

/-- Derivatives may be moved from a reflected translate onto the distribution. -/
theorem convolution_distribution_derivative {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (U : Distribution 𝕜 Ω) (ρ : Test 𝕜 (⊤ : Domain n))
    (α : MultiIndex n) (x : Space n) (hx : x ∈ P102.U4.convolutionDomain Ω ρ) :
    multiPartial (P102.U4.localConvolution U ρ) α x =
      P102.U4.localConvolution (distributionDerivative α U) ρ x := by
  change P102.U4.multiPartial (P102.U4.localConvolution U ρ) α x = _
  rw [P102.U4.localConvolution_derivative n 𝕜 Ω α U ρ x hx]
  rw [P102.U4.localConvolution_pairing n 𝕜 Ω _ ρ x hx]
  have hx' := P102.U4.localConvolution_derivativeDomain n 𝕜 Ω α ρ hx
  rw [P102.U4.localConvolution_pairing n 𝕜 Ω _ _ x hx']
  change U (P102.U4.convolutionTest (P102.U4.kernelPartial α ρ) x hx') =
    (-1 : 𝕜) ^ α.card * U (P102.U4.testPartialWord Ω (α.sort (· ≤ ·))
      (P102.U4.convolutionTest ρ x hx))
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext y
  change P102.U4.kernelPartial α ρ (x - y) =
    (-1 : 𝕜) ^ α.card • ((P102.U4.testPartialWord Ω (α.sort (· ≤ ·)))
      (P102.U4.convolutionTest ρ x hx)) y
  rw [P102.U4.testPartialWord_coe]
  change P102.U4.kernelPartial α ρ (x - y) =
    (-1 : 𝕜) ^ α.card • P102.U4.partialWord (fun y => ρ (x - y))
      (α.sort (· ≤ ·)) y
  rw [P102.U4.partialWord_const_sub ρ.contDiff]
  rw [(P102.U4.localConvolution_kernelDerivative n 𝕜 α ρ).1]
  simp [P102.U4.multiPartial, smul_eq_mul, ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul]

/-- The zero extension outside the admissible domain imposes no boundary claim. -/
theorem harmonic_convolution : P201Specs.Weyl.HarmonicConvolutionStatement := by
  intro n 𝕜 _ Ω U hU ρ
  refine ⟨P102.U4.localConvolution_smooth n 𝕜 Ω U ρ, ?_⟩
  intro x hx
  change (∑ i : Fin n, multiPartial (P102.U4.localConvolution U ρ) {i, i} x) = 0
  simp_rw [convolution_distribution_derivative Ω U ρ _ x hx]
  simp_rw [P102.U4.localConvolution_pairing n 𝕜 Ω _ ρ x hx]
  change (∑ i : Fin n, distributionDerivative {i, i} U
    (P102.U4.convolutionTest ρ x hx)) = 0
  have h := congrArg (fun T : Distribution 𝕜 Ω => T (P102.U4.convolutionTest ρ x hx)) hU
  simpa only [distributionLaplacian, P201Specs.distributionLaplacian,
    sum_apply, zero_apply] using h

/-- Whole-space integral pairing; compact test support localizes the integral. -/
theorem regular_apply {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (hu : LocallyIntegrableOn u Ω volume)
    (φ : Test 𝕜 Ω) : regularDistribution Ω u φ = ∫ x, u x * φ x := by
  change P102.U4.regularDistribution Ω u φ = _
  rw [P102.U4.regularDistribution, TestFunction.integralAgainstBilinCLM_eq_integral hu]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => mul_comm _ _

/-- Restriction preserves the actual ambient function of a regular distribution. -/
theorem regular_restriction {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω V : Domain n} (h : V ≤ Ω) (u : Space n → 𝕜)
    (hu : LocallyIntegrableOn u Ω volume) :
    P102.U4.restrictDistribution h (regularDistribution Ω u) =
      regularDistribution V u := by
  ext φ
  change regularDistribution Ω u (P102.U4.zeroExtension 𝕜 h φ) = _
  rw [regular_apply Ω u hu, regular_apply V u (hu.mono_set h)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change u x * (P102.U4.zeroExtension 𝕜 h φ) x = u x * φ x
    rw [(P102.U4.zeroExtensionProperties n 𝕜 V Ω h φ).1]

/-- Local representatives of the same distribution agree pointwise on overlaps. -/
theorem representatives_agree {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (U : Distribution 𝕜 Ω) (V W : Domain n)
    (hV : V ≤ Ω) (hW : W ≤ Ω) (u v : Space n → 𝕜)
    (hu : ContinuousOn u V) (hv : ContinuousOn v W)
    (hru : regularDistribution V u = P102.U4.restrictDistribution hV U)
    (hrv : regularDistribution W v = P102.U4.restrictDistribution hW U) :
    EqOn u v (V ⊓ W : Domain n) := by
  apply continuous_representative_unique (V ⊓ W) u v
    (hu.mono inf_le_left) (hv.mono inf_le_right)
  change regularDistribution (V ⊓ W) u = regularDistribution (V ⊓ W) v
  rw [← regular_restriction (show V ⊓ W ≤ V from inf_le_left) u
      (hu.locallyIntegrableOn V.isOpen.measurableSet),
    ← regular_restriction (show V ⊓ W ≤ W from inf_le_right) v
      (hv.locallyIntegrableOn W.isOpen.measurableSet), hru, hrv]
  exact (P102.U4.restrictionTransitive n 𝕜 (V ⊓ W) V Ω inf_le_left hV U).trans
    (P102.U4.restrictionTransitive n 𝕜 (V ⊓ W) W Ω inf_le_right hW U).symm

/-- Smooth local representatives glue without connectedness assumptions. -/
theorem local_to_global {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (U : Distribution 𝕜 Ω)
    (hloc : ∀ a ∈ Ω, ∃ (V : Domain n) (hV : V ≤ Ω), a ∈ V ∧
      ∃ u : Space n → 𝕜, ContDiffOn ℝ (⊤ : ℕ∞) u V ∧
        regularDistribution V u = P102.U4.restrictDistribution hV U) :
    ∃ u : Space n → 𝕜, ContDiffOn ℝ (⊤ : ℕ∞) u Ω ∧
      regularDistribution Ω u = U := by
  classical
  choose V hV ha f hf hr using fun a : Ω => hloc a a.property
  let u : Space n → 𝕜 := fun x => if hx : x ∈ Ω then f ⟨x, hx⟩ x else 0
  have heq (a : Ω) : EqOn u (f a) (V a) := by
    intro x hx
    have hxΩ := hV a hx
    dsimp only [u]
    rw [dite_eq_left hxΩ]
    exact representatives_agree Ω U (V ⟨x, hxΩ⟩) (V a) (hV _) (hV a)
      (f _) (f a) (hf _).continuousOn (hf a).continuousOn (hr _) (hr a)
      ⟨ha ⟨x, hxΩ⟩, hx⟩
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) u Ω := by
    intro x hx
    let a : Ω := ⟨x, hx⟩
    have he : u =ᶠ[𝓝 x] f a :=
      Filter.eventuallyEq_of_mem ((V a).isOpen.mem_nhds (ha a)) (heq a)
    exact ((hf a).contDiffAt ((V a).isOpen.mem_nhds (ha a))).congr_of_eventuallyEq
      he |>.contDiffWithinAt
  refine ⟨u, hsm, ?_⟩
  have hli : LocallyIntegrableOn u Ω volume :=
    hsm.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  let T : Distribution 𝕜 Ω := regularDistribution Ω u - U
  have hvan (a : Ω) : P102.U4.VanishesOn T (V a) := by
    intro φ hφ
    let ψ : Test 𝕜 (V a) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩
    have hext : P102.U4.zeroExtension 𝕜 (hV a) ψ = φ := by
      ext x
      exact (P102.U4.zeroExtensionProperties n 𝕜 (V a) Ω (hV a) ψ).1 x
    have hre : regularDistribution (V a) u = regularDistribution (V a) (f a) := by
      exact (P102.U4.regular_injectivity n 𝕜 (V a) u (f a)
        (hli.mono_set (hV a))
        ((hf a).continuousOn.locallyIntegrableOn (V a).isOpen.measurableSet)).mpr
        ((ae_restrict_mem (V a).isOpen.measurableSet).mono fun x hx => heq a hx)
    have hh := congrArg (fun S : Distribution 𝕜 (V a) => S ψ)
      ((regular_restriction (hV a) u hli).trans (hre.trans (hr a)))
    change regularDistribution Ω u (P102.U4.zeroExtension 𝕜 (hV a) ψ) =
      U (P102.U4.zeroExtension 𝕜 (hV a) ψ) at hh
    change regularDistribution Ω u φ - U φ = 0
    exact sub_eq_zero.mpr (hext ▸ hh)
  have hc : (Ω : Set (Space n)) ⊆ ⋃ a : Ω, (V a : Set (Space n)) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, ha ⟨x, hx⟩⟩
  have hv := P102.U4.vanishesOn_iUnion T (fun a : Ω => (V a : Set (Space n)))
    (fun a => (V a).isOpen) hvan
  ext φ
  exact sub_eq_zero.mp (hv φ (φ.tsupport_subset.trans hc))

/-- Germ locality of the coordinate differential operator. -/
theorem laplacian_eq_of_eventuallyEq {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u v : Space n → 𝕜} {x : Space n} (h : u =ᶠ[𝓝 x] v) :
    laplacian u x = laplacian v x := by
  have hw (l : List (Fin n)) :
      P102.U4.partialWord u l =ᶠ[𝓝 x] P102.U4.partialWord v l := by
    induction l with
    | nil => exact h
    | cons i l ih =>
      exact (ih.fderiv (𝕜 := ℝ)).mono fun y hy =>
        congrArg (fun A : Space n →L[ℝ] 𝕜 => A (coordinate n i)) hy
  apply Finset.sum_congr rfl
  intro i _
  exact (hw (({i, i} : MultiIndex n).sort (· ≤ ·))).eq_of_nhds

/-- Harmonicity also glues as pointwise equality of the local functions. -/
theorem local_to_global_harmonic {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (U : Distribution 𝕜 Ω)
    (hloc : ∀ a ∈ Ω, ∃ (V : Domain n) (hV : V ≤ Ω), a ∈ V ∧
      ∃ u : Space n → 𝕜, ContDiffOn ℝ (⊤ : ℕ∞) u V ∧
        P201.MeanValues.IsHarmonic V u ∧
        regularDistribution V u = P102.U4.restrictDistribution hV U) :
    ∃ u : Space n → 𝕜, ContDiffOn ℝ (⊤ : ℕ∞) u Ω ∧
      P201.MeanValues.IsHarmonic Ω u ∧ regularDistribution Ω u = U := by
  obtain ⟨u, hu, hrep⟩ := local_to_global Ω U (by
    intro a ha
    obtain ⟨V, hV, haV, f, hf, _, hr⟩ := hloc a ha
    exact ⟨V, hV, haV, f, hf, hr⟩)
  refine ⟨u, hu, ⟨hu.of_le (by simp), ?_⟩, hrep⟩
  intro a ha
  obtain ⟨V, hV, haV, f, hf, hh, hr⟩ := hloc a ha
  have hre : regularDistribution V u = regularDistribution V f := by
    rw [← regular_restriction hV u
      (hu.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet), hrep, hr]
  have he := continuous_representative_unique V u f
    (hu.continuousOn.mono hV) hf.continuousOn hre
  change laplacian u a = 0
  rw [laplacian_eq_of_eventuallyEq (Filter.eventuallyEq_of_mem (V.isOpen.mem_nhds haV) he)]
  exact hh.2 a haV

open P201.MeanValues
open scoped Convolution

/-- The radial kernel from the mean-value proof, now as a scalar-valued test. -/
def radialTest {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (r : ℝ) (hr : 0 < r) :
    Test 𝕜 (⊤ : Domain n) where
  toFun x := (radialKernel r x : 𝕜)
  contDiff' := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (radialKernel_contDiff r)
  hasCompactSupport' := (radialKernel_hasCompactSupport hr).comp_left (by simp)
  tsupport_subset' := subset_univ _

theorem radialTest_support {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (r : ℝ) (hr : 0 < r) :
    tsupport (radialTest (n := n) 𝕜 r hr) ⊆ closedBall 0 r := by
  have hs : tsupport (radialKernel (n := n) r) = closedBall 0 r := by
    rw [tsupport, radialKernel_support hr, closure_ball 0 hr.ne']
  exact (tsupport_comp_subset (map_zero (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜))
    (radialKernel r)).trans hs.subset

/-- A normalized radial test supplies a genuine approximate identity. -/
def unitRadialTest {n : ℕ} (𝕜 : Type) [RCLike 𝕜] : Test 𝕜 (⊤ : Domain n) :=
  (∫ x : Space n, radialKernel 1 x)⁻¹ • radialTest 𝕜 1 zero_lt_one

theorem unitRadialTest_integral {n : ℕ} (𝕜 : Type) [RCLike 𝕜] :
    (∫ x : Space n, unitRadialTest 𝕜 x) = 1 := by
  change (∫ x : Space n, (∫ y : Space n, radialKernel 1 y)⁻¹ •
    (radialKernel 1 x : 𝕜)) = 1
  rw [integral_smul, integral_ofReal]
  simp only [RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_mul,
    inv_mul_cancel₀ (radialKernel_integral_pos (n := n) zero_lt_one).ne', RCLike.ofReal_one]

/-- Mean values reproduce harmonic functions under this radial convolution. -/
theorem radial_regular_convolution {n : ℕ} (hn : 1 ≤ n)
    {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (u : Space n → 𝕜)
    (hu : IsHarmonic Ω u) (a : Space n) (r : ℝ) (hr : 0 < r)
    (hball : closedBall a r ⊆ (Ω : Set (Space n))) :
    P102.U4.localConvolution (regularDistribution Ω u) (radialTest 𝕜 r hr) a =
      (∫ t : Space n, radialKernel r t) • u a := by
  have hadm : a ∈ P102.U4.convolutionDomain Ω (radialTest 𝕜 r hr) := by
    intro z hz
    apply hball
    have hz' := radialTest_support 𝕜 r hr hz
    simpa only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      sub_zero] using hz'
  have hli : LocallyIntegrableOn u Ω volume :=
    hu.1.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  let f : Space n → 𝕜 := (closedBall a r).indicator u
  have hfi : Integrable f volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      ((hu.1.continuousOn.mono hball).integrableOn_compact (isCompact_closedBall a r))
  have hmean (s : ℝ) (hs : 0 < s) (hsr : s < r) :
      (∫ θ, f (a + s • θ) ∂P201Specs.unitSurface n) = P201Specs.omega n • f a := by
    have hsball : closedBall a s ⊆ (Ω : Set (Space n)) :=
      (closedBall_subset_closedBall hsr.le).trans hball
    have he : (∫ θ, f (a + s • θ) ∂P201Specs.unitSurface n) =
        ∫ θ, u (a + s • θ) ∂P201Specs.unitSurface n := by
      apply integral_congr_ae
      filter_upwards [unitSurface_ae_mem n] with θ hθ
      apply indicator_of_mem
      have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, hθn, mul_one, abs_of_pos hs]
      exact hsr.le
    rw [he, show f a = u a from indicator_of_mem (mem_closedBall_self hr.le) u]
    have hm := (mean_values hn Ω u hu a s hs hsball).1
    rw [sphere_mean_normalization hn u a s hs] at hm
    calc
      _ = P201Specs.omega n • unitSphereMean u a s := by
        simp [unitSphereMean, P201Specs.MeanValues.unitSphereMean, smul_smul,
          mul_inv_cancel₀ (omega_pos hn).ne']
      _ = _ := congrArg (P201Specs.omega n • ·) hm.symm
  rw [P102.U4.localConvolution_pairing n 𝕜 Ω _ _ a hadm,
    regular_apply Ω u hli]
  have he : (∫ x, u x * (P102.U4.convolutionTest (radialTest 𝕜 r hr) a hadm) x) =
      (radialKernel r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) a := by
    rw [convolution_eq_swap]
    apply integral_congr_ae
    filter_upwards [] with x
    change u x * (radialKernel r (a - x) : 𝕜) = radialKernel r (a - x) • f x
    by_cases hx : x ∈ closedBall a r
    · rw [show f x = u x from indicator_of_mem hx u, RCLike.real_smul_eq_coe_mul, mul_comm]
    · have hk : radialKernel r (a - x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        have hs : tsupport (radialKernel (n := n) r) = closedBall 0 r := by
          rw [tsupport, radialKernel_support hr, closure_ball 0 hr.ne']
        rw [hs]
        simpa only [mem_closedBall, dist_eq_norm, sub_zero, norm_sub_rev] using hx
      simp [hk]
  rw [he, radialKernel_convolution_eq hn hfi.locallyIntegrable a hr hmean,
    show f a = u a from indicator_of_mem (mem_closedBall_self hr.le) u]

/-- Transpose the radial reproduction identity onto a compact smooth test. -/
theorem radial_pairing {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (hu : IsHarmonic Ω u)
    (r : ℝ) (hr : 0 < r) (φ ψ : Test 𝕜 Ω)
    (hball : ∀ x ∈ tsupport φ, closedBall x r ⊆ (Ω : Set (Space n)))
    (hψ : ∀ y, ψ y = P102.U4.Mollification.reflectedSmoothing (radialTest 𝕜 r hr) φ y) :
    (∫ x, u x * ψ x) = (∫ t : Space n, radialKernel r t) • (∫ x, u x * φ x) := by
  have hli : LocallyIntegrableOn u Ω volume :=
    hu.1.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hadm : tsupport φ ⊆ P102.U4.convolutionDomain Ω (radialTest 𝕜 r hr) := by
    intro x hx z hz
    apply hball x hx
    have hz' := radialTest_support 𝕜 r hr hz
    simpa only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      sub_zero] using hz'
  obtain ⟨ψ', hψ', _, hp⟩ := P102.U4.Mollification.integralPairing n 𝕜 Ω
    (regularDistribution Ω u) (radialTest 𝕜 r hr) φ hadm
  have heψ : ψ' = ψ := by
    ext y
    exact (hψ' y).trans (hψ y).symm
  rw [heψ, regular_apply Ω u hli] at hp
  rw [← hp, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  change P102.U4.localConvolution (regularDistribution Ω u) (radialTest 𝕜 r hr) x * φ x =
    (∫ t : Space n, radialKernel r t) • (u x * φ x)
  by_cases hx : φ x = 0
  · simp [hx]
  · rw [radial_regular_convolution hn Ω u hu x r hr (hball x (subset_tsupport _ hx))]
    exact smul_mul_assoc _ _ _

/-- On a small ball, a fixed radial smoothing is the distribution itself. -/
theorem local_representative {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (U : Distribution 𝕜 Ω) (hU : distributionLaplacian U = 0)
    (a : Space n) (r : ℝ) (hr : 0 < r)
    (hbig : closedBall a (4 * r) ⊆ (Ω : Set (Space n))) :
    let V : Domain n := ⟨ball a r, isOpen_ball⟩
    ∃ g : Space n → 𝕜, ContDiffOn ℝ (⊤ : ℕ∞) g V ∧ IsHarmonic V g ∧
      ∀ φ : Test 𝕜 V, regularDistribution V g φ =
        U (P102.U4.zeroExtension 𝕜
          (show V ≤ Ω from ball_subset_closedBall.trans
            ((closedBall_subset_closedBall (by linarith)).trans hbig)) φ) := by
  dsimp only
  let V : Domain n := ⟨ball a r, isOpen_ball⟩
  let W : Domain n := ⟨ball a (3 * r), isOpen_ball⟩
  let ρ : Test 𝕜 (⊤ : Domain n) := radialTest 𝕜 r hr
  let m : ℝ := ∫ t : Space n, radialKernel r t
  have hm : m ≠ 0 := (radialKernel_integral_pos hr).ne'
  have hVΩ : V ≤ Ω := ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith)).trans hbig)
  have hWΩ : W ≤ Ω := ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith)).trans hbig)
  have hballW (x : Space n) (hx : x ∈ V) : closedBall x r ⊆ (W : Set (Space n)) :=
    closedBall_subset_ball' (by have hx' : dist x a < r := hx; linarith)
  have hadmW (x : Space n) (hx : x ∈ V) : x ∈ P102.U4.convolutionDomain W ρ := by
    intro z hz
    apply hballW x hx
    have hz' := radialTest_support 𝕜 r hr hz
    simpa only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      sub_zero] using hz'
  have hadmΩ : (V : Set (Space n)) ⊆ P102.U4.convolutionDomain Ω ρ := by
    intro x hx z hz
    exact hWΩ (hadmW x hx z hz)
  have hc := harmonic_convolution Ω U hU ρ
  have hcv : ContDiffOn ℝ (⊤ : ℕ∞) (P102.U4.localConvolution U ρ) V := hc.1.mono hadmΩ
  have hhv : IsHarmonic V (P102.U4.localConvolution U ρ) :=
    ⟨hcv.of_le (by simp), fun x hx => hc.2 x (hadmΩ hx)⟩
  let g : Space n → 𝕜 := m⁻¹ • P102.U4.localConvolution U ρ
  have hgc : ContDiffOn ℝ (⊤ : ℕ∞) g V := hcv.const_smul m⁻¹
  have hgh : IsHarmonic V g := (harmonic_bridge V g).mpr
    (((harmonic_bridge V _).mp hhv).const_smul (c := m⁻¹))
  refine ⟨g, hgc, hgh, ?_⟩
  intro φ
  let φΩ : Test 𝕜 Ω := P102.U4.zeroExtension 𝕜 hVΩ φ
  let φW : Test 𝕜 W :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport,
      φ.tsupport_subset.trans (ball_subset_ball (by linarith))⟩
  have heφΩ : (φΩ : Space n → 𝕜) = φ :=
    funext (P102.U4.zeroExtensionProperties n 𝕜 V Ω hVΩ φ).1
  have hφadm : tsupport φΩ ⊆ P102.U4.convolutionDomain Ω ρ := by
    rw [heφΩ]
    exact φ.tsupport_subset.trans hadmΩ
  obtain ⟨ψ, hψ, _, hp⟩ := P102.U4.Mollification.integralPairing n 𝕜 Ω U ρ φΩ hφadm
  have hψW : tsupport ψ ⊆ (W : Set (Space n)) := by
    have heψ : (ψ : Space n → 𝕜) = P102.U4.Mollification.reflectedSmoothing ρ φΩ :=
      funext hψ
    rw [heψ]
    apply (P102.U4.Mollification.reflectedSmoothing_support ρ φΩ).trans
    rintro y ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
    rw [heφΩ] at hx
    exact hadmW x (φ.tsupport_subset hx) z hz
  let ψW : Test 𝕜 W := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hψW⟩
  have hψ' : ∀ y, ψW y = P102.U4.Mollification.reflectedSmoothing ρ φW y := by
    intro y
    change ψ y = P102.U4.Mollification.reflectedSmoothing ρ (φ : Space n → 𝕜) y
    rw [← heφΩ]
    exact hψ y
  let η : Test 𝕜 (⊤ : Domain n) := unitRadialTest 𝕜
  let uε : ℝ → Space n → 𝕜 := fun ε =>
    P102.U4.localConvolution U (P102.U4.Mollification.scaledKernel η ε)
  have hWclosure : closure (W : Set (Space n)) = closedBall a (3 * r) :=
    closure_ball a (by positivity : 3 * r ≠ 0)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (W : Set (Space n)) ⊆ P102.U4.convolutionDomain Ω
        (P102.U4.Mollification.scaledKernel η ε) :=
    P102.U4.Mollification.relativelyCompactDomain n 𝕜 Ω W η
      (hWclosure ▸ isCompact_closedBall a (3 * r))
      (by rw [hWclosure]; exact (closedBall_subset_closedBall (by linarith)).trans hbig)
  have he : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ x, uε ε x * ψ x) = m • (∫ x, uε ε x * φΩ x) := by
    filter_upwards [hev] with ε hε
    have hhc := harmonic_convolution Ω U hU (P102.U4.Mollification.scaledKernel η ε)
    have hh : IsHarmonic W (uε ε) :=
      ⟨(hhc.1.mono hε).of_le (by simp), fun x hx => hhc.2 x (hε hx)⟩
    rw [heφΩ]
    exact radial_pairing hn W (uε ε) hh r hr φW ψW
      (fun x hx => hballW x (φ.tsupport_subset hx)) hψ'
  have htφ := P102.U4.Mollification.distributionLimit n 𝕜 Ω U η
    (unitRadialTest_integral 𝕜) φΩ
  have htψ := P102.U4.Mollification.distributionLimit n 𝕜 Ω U η
    (unitRadialTest_integral 𝕜) ψ
  have hUψ : U ψ = m • U φΩ :=
    tendsto_nhds_unique htψ ((tendsto_const_nhds.smul htφ).congr' (he.mono fun ε h => h.symm))
  have hgli : LocallyIntegrableOn g V volume :=
    hgc.continuousOn.locallyIntegrableOn V.isOpen.measurableSet
  change regularDistribution V g φ = U φΩ
  rw [regular_apply V g hgli]
  calc
    (∫ x, g x * φ x) = m⁻¹ • (∫ x, P102.U4.localConvolution U ρ x * φΩ x) := by
      simp only [g, Pi.smul_apply, smul_mul_assoc, integral_smul, heφΩ]
    _ = m⁻¹ • U ψ := congrArg (m⁻¹ • ·) hp
    _ = U φΩ := by rw [hUψ, smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- Weyl's lemma for arbitrary distributions on arbitrary open domains. -/
theorem weyl : P201Specs.Weyl.WeylStatement := by
  intro n hn 𝕜 _ Ω U hU
  obtain ⟨u, hu, hh, hrep⟩ := local_to_global_harmonic Ω U (by
    intro a ha
    obtain ⟨R, hR, hRΩ⟩ : ∃ R : ℝ, 0 < R ∧ closedBall a R ⊆ (Ω : Set _) :=
      Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds ha)
    let r : ℝ := R / 4
    have hr : 0 < r := by dsimp [r]; positivity
    have hrad : 4 * r = R := by dsimp [r]; ring
    have hbig : closedBall a (4 * r) ⊆ (Ω : Set (Space n)) := by rwa [hrad]
    let V : Domain n := ⟨ball a r, isOpen_ball⟩
    have hV : V ≤ Ω := ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (by linarith)).trans hbig)
    obtain ⟨g, hg, hgh, hgr⟩ := local_representative hn Ω U hU a r hr hbig
    refine ⟨V, hV, mem_ball_self hr, g, hg, hgh, ?_⟩
    ext φ
    exact hgr φ)
  refine ⟨u, hu, hh, hrep, ?_⟩
  intro v hv hvr
  exact continuous_representative_unique Ω v u hv hu.continuousOn (hvr.trans hrep.symm)

/-- The complete mean-value and distributional-harmonicity source theorem. -/
theorem mean_values_and_weyl : P201Specs.Weyl.MeanValuesAndWeylStatement :=
  ⟨P201.MeanValues.mean_values, P201.MeanValues.ball_converse,
    P201.MeanValues.sphere_converse, weyl⟩

end P201.Weyl
