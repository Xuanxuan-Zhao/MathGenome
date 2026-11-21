import MathGenome.Internal.LinearPDE.P201Specs.Heat.CubeHarnack
import MathGenome.Internal.LinearPDE.P201.Heat.ClassicalMaximum
import MathGenome.Internal.LinearPDE.P201.Heat.LocalDerivativeEstimate
import MathGenome.Internal.LinearPDE.P201.Heat.HeatBallMeanValue
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

import MathGenome.Internal.LinearPDE.P201.Heat.CubeDirichletKernel
/-! Conditional one-cube Harnack derivation from the frozen cube-kernel
interfaces. The pending cube-kernel implementation is deliberately not imported.
The public conditional targets retain every prescribed kernel premise in order.
-/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace P201.Heat.CubeHarnack
open P201Specs (Space Domain spatialMeasure)
open P201Specs.Heat (SpaceTime IsClassicalCaloricOn)
open P201Specs.Heat.Cube

lemma cube_subset_closedCube {n : ℕ} (ℓ : ℝ) (a : Space n) :
    cube ℓ a ⊆ closedCube ℓ a := by
  intro x hx j
  exact ⟨(hx j).1.le, (hx j).2.le⟩

lemma isClosed_closedCube {n : ℕ} (ℓ : ℝ) (a : Space n) :
    IsClosed (closedCube ℓ a) := by
  change IsClosed {x : Space n | ∀ j, a j ≤ x j ∧ x j ≤ a j + ℓ}
  simp only [ofPred_forall]
  apply isClosed_iInter (fun j => ?_)
  exact (isClosed_le (continuous_const : Continuous (fun _ : Space n => a j))
    (PiLp.continuous_apply 2 _ j)).inter
    (isClosed_le (PiLp.continuous_apply 2 _ j) continuous_const)

lemma isCompact_closedCube {n : ℕ} (ℓ : ℝ) (a : Space n) :
    IsCompact (closedCube ℓ a) := by
  let e := PiLp.homeomorph 2 (fun _ : Fin n => ℝ)
  have hc : IsCompact (Set.univ.pi (fun j : Fin n => Icc (a j) (a j + ℓ))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have he : closedCube ℓ a = e ⁻¹' (Set.univ.pi (fun j : Fin n => Icc (a j) (a j + ℓ))) := by
    ext x
    change (∀ j, a j ≤ x j ∧ x j ≤ a j + ℓ) ↔
      ∀ j ∈ (univ : Set (Fin n)), a j ≤ x j ∧ x j ≤ a j + ℓ
    simp only [mem_univ, forall_true_left]
  rw [he]
  exact e.isCompact_preimage.mpr hc

lemma closure_cube_subset_closedCube {n : ℕ} (ℓ : ℝ) (a : Space n) :
    closure (cube ℓ a) ⊆ closedCube ℓ a :=
  closure_minimal (cube_subset_closedCube ℓ a) (isClosed_closedCube ℓ a)

lemma isOpen_cube {n : ℕ} (ℓ : ℝ) (a : Space n) : IsOpen (cube ℓ a) := by
  change IsOpen {x : Space n | ∀ j, a j < x j ∧ x j < a j + ℓ}
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  exact (isOpen_lt (continuous_const : Continuous (fun _ : Space n => a j))
    (PiLp.continuous_apply 2 _ j)).inter
    (isOpen_lt (PiLp.continuous_apply 2 _ j) continuous_const)

lemma closedBall_subset_outer_cube {n : ℕ} {ℓ ℓ' r : ℝ} {a a' x : Space n}
    (hr : 0 < r) (hball : ball x r ⊆ cube ℓ' a')
    (hnest : closedCube ℓ' a' ⊆ cube ℓ a) :
    closedBall x r ⊆ cube ℓ a := by
  rw [← closure_ball x hr.ne']
  exact (closure_mono hball).trans ((closure_cube_subset_closedCube ℓ' a').trans hnest)

/-- Only continuity is needed for spatial integrability; the initial values
need not vanish on any face. -/
lemma slice_integrable {n : ℕ} {ℓ : ℝ} {a : Space n} {g : Space n → ℝ}
    (hg : ContinuousOn g (closedCube ℓ a)) :
    IntegrableOn g (cube ℓ a) (spatialMeasure n) :=
  (hg.integrableOn_compact (isCompact_closedCube ℓ a)).mono_set
    (cube_subset_closedCube ℓ a)

/-- The spatial inequality used before integrating in time. It assumes the
comparison inequality explicitly; proving comparison is a separate obligation. -/
lemma ball_mass_le_of_kernel_comparison
    (hIntegral : kernelIntegralStatement) (hNonnegative : kernelNonnegativeStatement)
    {n : ℕ} (hn : 1 ≤ n) {ℓ τ c : ℝ} (hℓ : 0 < ℓ) (hτ : 0 < τ)
    {a x y : Space n} {r U : ℝ} {g : Space n → ℝ}
    (hy : y ∈ closedCube ℓ a) (hg : ContinuousOn g (closedCube ℓ a))
    (hgn : ∀ z ∈ cube ℓ a, 0 ≤ g z)
    (hball : ball x r ⊆ cube ℓ a)
    (hlower : ∀ z ∈ ball x r, c ≤ cubeKernel ℓ a τ y z)
    (hcomp : kernelSolution ℓ a g τ y ≤ U) :
    c * (∫ z in ball x r, g z ∂spatialMeasure n) ≤ U := by
  have hgint := (slice_integrable hg).mono_set hball
  have hkint : IntegrableOn (fun z => cubeKernel ℓ a τ y z * g z)
      (cube ℓ a) (spatialMeasure n) := hIntegral n hn ℓ hℓ a g hg τ hτ y
  have hi : (∫ z in ball x r, c * g z ∂spatialMeasure n) ≤
      ∫ z in ball x r, cubeKernel ℓ a τ y z * g z ∂spatialMeasure n := by
    apply integral_mono_ae (hgint.const_mul c) (hkint.mono_set hball)
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact mul_le_mul_of_nonneg_right (hlower z hz) (hgn z (hball hz))
  rw [integral_const_mul] at hi
  apply (hi.trans ?_).trans hcomp
  apply setIntegral_mono_set hkint
  · filter_upwards [ae_restrict_mem (isOpen_cube ℓ a).measurableSet] with z hz
    exact mul_nonneg (hNonnegative n hn ℓ hℓ a τ hτ y hy z
      (cube_subset_closedCube ℓ a hz)) (hgn z hz)
  · exact Filter.Eventually.of_forall (fun z hz => hball hz)

/-- Integrate the comparison lower bound over the backward time interval.
The positive kernel constant is fixed using only compact sets, r, and δ. -/
lemma exists_cylinder_mass_bound_of_comparison
    (hIntegral : kernelIntegralStatement) (hNonnegative : kernelNonnegativeStatement)
    (hLower : kernelLowerBoundStatement)
    (hComparison : P201Specs.Heat.CubeHarnack.kernelComparisonStatement)
    {n : ℕ} (hn : 1 ≤ n) {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Space n)
    (Kx Ky : Set (Space n)) (hKx : IsCompact Kx) (hKxQ : Kx ⊆ cube ℓ a)
    (hKy : IsCompact Ky) (hKyQ : Ky ⊆ cube ℓ a)
    {r δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω : Domain n) (T : ℝ), 0 < T → closedCube ℓ a ⊆ (Ω : Set (Space n)) →
      ∀ (u : SpaceTime n → ℝ),
        IsClassicalCaloricOn u ((Ω : Set (Space n)) ×ˢ Ioo 0 T) →
        (∀ z ∈ (Ω : Set (Space n)) ×ˢ Ioo 0 T, 0 ≤ u z) →
      ∀ (x y : Space n), y ∈ Kx → ball x r ⊆ Ky →
      ∀ t : ℝ, r^2 < t → t + δ < T →
        c * (∫ s in Icc (t-r^2) t, ∫ z in ball x r, u (z,s) ∂spatialMeasure n) ≤
          r^2 * u (y,t+δ) := by
  obtain ⟨c, hc, hlower⟩ := hLower n hn ℓ hℓ a Kx Ky hKx hKxQ hKy hKyQ
    δ (δ+r^2) hδ (by nlinarith [sq_nonneg r])
  refine ⟨c, hc, ?_⟩
  intro Ω T hT hQ u hu hun x y hy hball t ht htd
  have hQt : cube ℓ a ⊆ (Ω : Set (Space n)) := (cube_subset_closedCube ℓ a).trans hQ
  have hspos (s : ℝ) (hs : s ∈ Icc (t-r^2) t) : 0 < s := by linarith [hs.1]
  have hsT (s : ℝ) (hs : s ∈ Icc (t-r^2) t) : s < T := by linarith [hs.2]
  have hgn (s : ℝ) (hs : s ∈ Icc (t-r^2) t) :
      ∀ z ∈ cube ℓ a, 0 ≤ u (z,s) := by
    intro z hz
    exact hun (z,s) ⟨hQt hz, hspos s hs, hsT s hs⟩
  have hslice (s : ℝ) (hs : s ∈ Icc (t-r^2) t) :
      ContinuousOn (fun z => u (z,s)) (closedCube ℓ a) :=
    hu.1.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun z hz => ⟨hQ hz, hspos s hs, hsT s hs⟩)
  have hpoint (s : ℝ) (hs : s ∈ Icc (t-r^2) t) :
      c * (∫ z in ball x r, u (z,s) ∂spatialMeasure n) ≤ u (y,t+δ) := by
    have hτ : 0 < t+δ-s := by linarith [hs.2]
    apply ball_mass_le_of_kernel_comparison hIntegral hNonnegative hn hℓ hτ
      (cube_subset_closedCube ℓ a (hKxQ hy)) (hslice s hs) (hgn s hs)
      (hball.trans hKyQ)
    · intro z hz
      exact hlower (t+δ-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ y hy z (hball hz)
    · exact hComparison n hn ℓ hℓ a Ω T hT hQ u hu hun s (t+δ)
        (hspos s hs) (by linarith [hs.2]) htd y
        (cube_subset_closedCube ℓ a (hKxQ hy))
  have hi : (∫ s in Icc (t-r^2) t,
      c * (∫ z in ball x r, u (z,s) ∂spatialMeasure n)) ≤
      ∫ s in Icc (t-r^2) t, u (y,t+δ) := by
    refine integral_mono_of_nonneg ?_ (integrable_const _) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      apply mul_nonneg hc.le
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      exact hgn s hs z (hKyQ (hball hz))
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact hpoint s hs
  rw [integral_const_mul, integral_const] at hi
  have hvol : (volume.restrict (Icc (t-r^2) t)).real univ = r^2 := by
    simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by nlinarith [sq_nonneg r] : 0 ≤ t - (t-r^2))]
    ring
  simpa only [smul_eq_mul, hvol] using hi

/-- Directional differentiation under the fixed space-time coordinate map. -/
lemma fderiv_comp_coordinates_symm {n : ℕ} {F : Space (n+1) → ℝ}
    (hF : ContDiff ℝ ∞ F) (p v : SpaceTime n) :
    fderiv ℝ (F ∘ (P201Specs.Heat.spaceTimeCoordinates n).symm) p v =
      fderiv ℝ F ((P201Specs.Heat.spaceTimeCoordinates n).symm p)
        ((P201Specs.Heat.spaceTimeCoordinates n).symm v) := by
  rw [fderiv_comp p (hF.differentiable (by simp) _)
    (P201Specs.Heat.spaceTimeCoordinates n).symm.differentiableAt]
  rw [ContinuousLinearEquiv.fderiv]
  rfl

lemma second_fderiv_comp_coordinates_symm {n : ℕ} {F : Space (n+1) → ℝ}
    (hF : ContDiff ℝ ∞ F) (p v w : SpaceTime n) :
    fderiv ℝ (fun q => fderiv ℝ (F ∘ (P201Specs.Heat.spaceTimeCoordinates n).symm) q v) p w =
      fderiv ℝ (fun z => fderiv ℝ F z
        ((P201Specs.Heat.spaceTimeCoordinates n).symm v))
        ((P201Specs.Heat.spaceTimeCoordinates n).symm p)
        ((P201Specs.Heat.spaceTimeCoordinates n).symm w) := by
  have he : (fun q => fderiv ℝ (F ∘ (P201Specs.Heat.spaceTimeCoordinates n).symm) q v) =
      (fun z => fderiv ℝ F z ((P201Specs.Heat.spaceTimeCoordinates n).symm v)) ∘
        (P201Specs.Heat.spaceTimeCoordinates n).symm := by
    funext q
    exact fderiv_comp_coordinates_symm hF q v
  rw [he]
  exact fderiv_comp_coordinates_symm
    ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const) p w

/-- A C^{2,1} caloric function is a solution in the shared distribution space.
This bridge uses compact tests, so it imposes no boundary regularity. -/
lemma classicalCaloric_distributionHeat_zero {n : ℕ}
    (Ω : Domain (n+1)) {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u
      ((P201Specs.Heat.spaceTimeCoordinates n).symm ⁻¹' (Ω : Set (Space (n+1))))) :
    P201Specs.Heat.distributionHeat
      (P201Specs.regularDistribution Ω (u ∘ P201Specs.Heat.spaceTimeCoordinates n)) = 0 := by
  classical
  let c := P201Specs.Heat.spaceTimeCoordinates n
  let f : Space (n+1) → ℝ := u ∘ c
  have hf : ContinuousOn f Ω :=
    hu.1.comp c.continuous.continuousOn (fun z hz => by simpa [c] using hz)
  have hfloc : LocallyIntegrableOn f Ω volume := hf.locallyIntegrableOn Ω.isOpen.measurableSet
  ext φ
  let q : SpaceTime n → ℝ := φ ∘ c.symm
  have hq : ContDiff ℝ ∞ q := φ.contDiff.comp c.symm.contDiff
  have hqk : HasCompactSupport q := φ.hasCompactSupport.comp_homeomorph c.symm.toHomeomorph
  have hqs : tsupport q ⊆ c.symm ⁻¹' (Ω : Set (Space (n+1))) := by
    exact (tsupport_comp_subset_preimage φ c.symm.continuous).trans
      (preimage_mono φ.tsupport_subset)
  let φt := P102.U4.testPartialWord Ω [0] φ
  let φii := fun i : Fin n => P102.U4.testPartialWord Ω [i.succ,i.succ] φ
  have qt (z : Space (n+1)) : fderiv ℝ q (c z) (0,1) = φt z := by
    rw [fderiv_comp_coordinates_symm φ.contDiff]
    simp only [c, ContinuousLinearEquiv.symm_apply_apply, spaceTimeCoordinates_symm_time]
    change _ = fderiv ℝ φ z (P201Specs.coordinate (n+1) 0)
    rfl
  have qi (i : Fin n) (z : Space (n+1)) :
      fderiv ℝ (fun p => fderiv ℝ q p (P201Specs.coordinate n i,0))
        (c z) (P201Specs.coordinate n i,0) = φii i z := by
    rw [second_fderiv_comp_coordinates_symm φ.contDiff]
    simp only [c, ContinuousLinearEquiv.symm_apply_apply, spaceTimeCoordinates_symm_spatial]
    rfl
  have ht : (∫ p, u p * fderiv ℝ q p (0,1) ∂P201Specs.Heat.spaceTimeMeasure n) =
      ∫ z, f z * φt z := by
    have he := (spaceTimeCoordinates_measurePreserving n).integral_comp
      c.toHomeomorph.measurableEmbedding
      (fun p => u p * fderiv ℝ q p (0,1))
    calc
      _ = ∫ z, u (c z) * fderiv ℝ q (c z) (0,1) := he.symm
      _ = _ := integral_congr_ae (Eventually.of_forall (fun z => by dsimp only; rw [qt]; rfl))
  have hi (i : Fin n) :
      (∫ p, u p * fderiv ℝ (fun v => fderiv ℝ q v (P201Specs.coordinate n i,0))
        p (P201Specs.coordinate n i,0) ∂P201Specs.Heat.spaceTimeMeasure n) =
      ∫ z, f z * φii i z := by
    have he := (spaceTimeCoordinates_measurePreserving n).integral_comp
      c.toHomeomorph.measurableEmbedding
      (fun p => u p * fderiv ℝ (fun v => fderiv ℝ q v (P201Specs.coordinate n i,0))
        p (P201Specs.coordinate n i,0))
    calc
      _ = ∫ z, u (c z) * fderiv ℝ (fun v => fderiv ℝ q v (P201Specs.coordinate n i,0))
          (c z) (P201Specs.coordinate n i,0) := he.symm
      _ = _ := integral_congr_ae (Eventually.of_forall (fun z => by dsimp only; rw [qi]; rfl))
  have hw := integral_caloric_compact_test hu (hq.of_le (by simp) : ContDiff ℝ 2 q) hqk hqs
  rw [ht] at hw
  simp_rw [hi] at hw
  have hti : Integrable (fun z => f z * φt z) :=
    (φt.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hfloc).congr
      (Eventually.of_forall (fun _ => mul_comm _ _))
  have hii (i : Fin n) : Integrable (fun z => f z * φii i z) :=
    ((φii i).integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hfloc).congr
      (Eventually.of_forall (fun _ => mul_comm _ _))
  rw [distributionHeat_pairing, P102.U4.regular_pairing _ ℝ Ω f hfloc]
  change (∫ z in (Ω : Set (Space (n+1))), f z * heatAdjointTest φ z) = 0
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
    simp only [(heatAdjointTest φ).zero_on_compl hz, Pi.zero_apply, mul_zero])]
  simp only [heatAdjointTest, sub_apply, neg_apply, sum_apply, mul_sub, mul_neg,
    Finset.mul_sum]
  have hsum : Integrable (fun z => ∑ i : Fin n, f z * φii i z) :=
    integrable_finsetSum Finset.univ (fun i _ => hii i)
  calc
    _ = (∫ z, -(f z * φt z)) - ∫ z, ∑ i : Fin n, f z * φii i z :=
      integral_sub hti.neg hsum
    _ = -(∫ z, f z * φt z) - ∑ i : Fin n, ∫ z, f z * φii i z := by
      rw [integral_neg, integral_finsetSum Finset.univ (fun i _ => hii i)]
    _ = 0 := by linarith [hw]

/-- Interior regularity upgrades exactly the classical hypothesis used here;
no smoothness assumption is added to the Harnack statement. -/
lemma classicalCaloric_contDiffOn_coords {n : ℕ} (hn : 1 ≤ n)
    (Ω : Domain (n+1)) {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u
      ((P201Specs.Heat.spaceTimeCoordinates n).symm ⁻¹' (Ω : Set (Space (n+1))))) :
    ContDiffOn ℝ ∞ (u ∘ P201Specs.Heat.spaceTimeCoordinates n) Ω := by
  let f := u ∘ P201Specs.Heat.spaceTimeCoordinates n
  have hf : ContinuousOn f Ω :=
    hu.1.comp (P201Specs.Heat.spaceTimeCoordinates n).continuous.continuousOn
      (fun z hz => by
        change (P201Specs.Heat.spaceTimeCoordinates n).symm
          (P201Specs.Heat.spaceTimeCoordinates n z) ∈ Ω
        rw [ContinuousLinearEquiv.symm_apply_apply]
        exact hz)
  have hfloc : LocallyIntegrableOn f Ω volume := hf.locallyIntegrableOn Ω.isOpen.measurableSet
  obtain ⟨g, hg, hrep, _⟩ := distributionRegularity n hn Ω
    (P201Specs.regularDistribution Ω f) (classicalCaloric_distributionHeat_zero Ω hu)
  have hae := (P102.U4.regular_injectivity (n+1) ℝ Ω g f
    (hg.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) hfloc).mp hrep
  have heq : EqOn g f Ω := Measure.eqOn_open_of_ae_eq hae Ω.isOpen hg.continuousOn hf
  exact hg.congr (fun z hz => (heq hz).symm)

lemma classicalCaloric_isCaloric_coords {n : ℕ} (Ω : Domain (n+1))
    {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u
      ((P201Specs.Heat.spaceTimeCoordinates n).symm ⁻¹' (Ω : Set (Space (n+1))))) :
    P201Specs.Heat.IsCaloric Ω (u ∘ P201Specs.Heat.spaceTimeCoordinates n) := by
  intro z hz
  have hcz : (P201Specs.Heat.spaceTimeCoordinates n z) ∈
      (P201Specs.Heat.spaceTimeCoordinates n).symm ⁻¹' (Ω : Set (Space (n+1))) := by
    change (P201Specs.Heat.spaceTimeCoordinates n).symm
      (P201Specs.Heat.spaceTimeCoordinates n z) ∈ Ω
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hz
  simpa only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using
    (hu.2.2.2.2 _ hcz).2.2

/-- The zeroth-order local estimate for the original classical solution,
expressed directly in space × time coordinates. -/
lemma classical_center_estimate (n : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Ω : Domain (n+1)) (u : SpaceTime n → ℝ),
      IsClassicalCaloricOn u
        ((P201Specs.Heat.spaceTimeCoordinates n).symm ⁻¹' (Ω : Set (Space (n+1)))) →
      ∀ (z : SpaceTime n) (r : ℝ), 0 < r →
        P201Specs.Heat.LocalEstimate.CylinderIn Ω z r →
        |u z| ≤ A * (r^(n+2))⁻¹ *
          (∫ s in Icc (z.2-r^2) z.2, ∫ y in ball z.1 r, |u (y,s)| ∂spatialMeasure n) := by
  obtain ⟨A, hA, hest⟩ := LocalEstimate.classicalEstimate n hn 0 0
  refine ⟨A, hA, ?_⟩
  intro Ω u hu z r hr hc
  have hf := classicalCaloric_contDiffOn_coords hn Ω hu
  have hP := classicalCaloric_isCaloric_coords Ω hu
  have hb := (hest Ω _ hf hP z r hr hc).2
  simpa [P201Specs.Heat.LocalEstimate.Bound, P201Specs.Heat.LocalEstimate.mixedDerivative,
    P201Specs.Heat.LocalEstimate.cylinderMass, P201Specs.multiPartial, P102.U4.multiPartial, P102.U4.partialWord,
    Function.comp_def] using hb

/-- All of the one-cube argument after comparison, for the original C^{2,1}
hypotheses. The remaining premise here is exactly the independent comparison
statement, rather than a smoothness or boundary certificate. -/
lemma oneCubeHarnack_of_comparison
    (hIntegral : kernelIntegralStatement) (hNonnegative : kernelNonnegativeStatement)
    (hLower : kernelLowerBoundStatement)
    (hComparison : P201Specs.Heat.CubeHarnack.kernelComparisonStatement) :
    P201Specs.Heat.CubeHarnack.oneCubeHarnackStatement := by
  intro n hn ℓ hℓ a ℓ' hℓ' a' ℓstar hℓstar astar hstar hprime r δ hr hδ hball
  obtain ⟨A, hA, hcenter⟩ := classical_center_estimate n hn
  have hstarQ : closedCube ℓstar astar ⊆ cube ℓ a :=
    hstar.trans ((cube_subset_closedCube ℓ' a').trans hprime)
  obtain ⟨c, hc, hmass⟩ := exists_cylinder_mass_bound_of_comparison
    hIntegral hNonnegative hLower hComparison hn hℓ a
    (closedCube ℓstar astar) (closedCube ℓ' a')
    (isCompact_closedCube ℓstar astar) hstarQ (isCompact_closedCube ℓ' a') hprime
    (r := r) hδ
  let C : ℝ := A * (r^(n+2))⁻¹ * (r^2 / c)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro Ω T hT hQ t₁ t₂ ht₁ ht₁₂ ht₂T hrt u hu hun x hx y hy t htt₁ htt₂
  let e := P201Specs.Heat.spaceTimeCoordinates n
  let D : Domain (n+1) := ⟨e ⁻¹' ((Ω : Set (Space n)) ×ˢ Ioo 0 T),
    (Ω.isOpen.prod isOpen_Ioo).preimage e.continuous⟩
  have hD : e.symm ⁻¹' (D : Set (Space (n+1))) = (Ω : Set (Space n)) ×ˢ Ioo 0 T := by
    ext p
    simp only [D, TopologicalSpace.Opens.coe_mk, mem_preimage,
      ContinuousLinearEquiv.apply_symm_apply]
  have huD : IsClassicalCaloricOn u (e.symm ⁻¹' (D : Set (Space (n+1)))) := by
    rw [hD]
    exact hu
  have hballQ : ball x r ⊆ cube ℓ a := (hball x hx).trans
    ((cube_subset_closedCube ℓ' a').trans hprime)
  have htime (s : ℝ) (hs : s ∈ Icc (t-r^2) t) : s ∈ Ioo 0 T := by
    constructor <;> linarith [hs.1, hs.2]
  have hQcyl : P201Specs.Heat.LocalEstimate.CylinderIn D (x,t) r := by
    intro p hp
    change p ∈ e.symm ⁻¹' (D : Set (Space (n+1)))
    rw [hD]
    exact ⟨hQ (cube_subset_closedCube ℓ a
      (closedBall_subset_outer_cube hr (hball x hx) hprime hp.1)), htime p.2 hp.2⟩
  have huest := hcenter D u huD (x,t) r hr hQcyl
  have habs :
      (∫ s in Icc (t-r^2) t, ∫ z in ball x r, |u (z,s)| ∂spatialMeasure n) =
      ∫ s in Icc (t-r^2) t, ∫ z in ball x r, u (z,s) ∂spatialMeasure n := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    exact abs_of_nonneg (hun (z,s) ⟨hQ (cube_subset_closedCube ℓ a (hballQ hz)), htime s hs⟩)
  have hm := hmass Ω T hT hQ u hu hun x y (cube_subset_closedCube ℓstar astar hy)
    ((hball x hx).trans (cube_subset_closedCube ℓ' a')) t (by linarith) (by linarith)
  have hm' :
      (∫ s in Icc (t-r^2) t, ∫ z in ball x r, u (z,s) ∂spatialMeasure n) ≤
        (r^2 / c) * u (y,t+δ) := by
    calc
      _ ≤ (r^2 * u (y,t+δ)) / c :=
        (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hm)
      _ = _ := by ring
  have huest' : u (x,t) ≤ A * (r^(n+2))⁻¹ *
      (∫ s in Icc (t-r^2) t, ∫ z in ball x r, u (z,s) ∂spatialMeasure n) := by
    apply (le_abs_self _).trans
    simpa only [habs] using huest
  calc
    u (x,t) ≤ A * (r^(n+2))⁻¹ *
      (∫ s in Icc (t-r^2) t, ∫ z in ball x r, u (z,s) ∂spatialMeasure n) := huest'
    _ ≤ A * (r^(n+2))⁻¹ * ((r^2 / c) * u (y,t+δ)) :=
      mul_le_mul_of_nonneg_left hm' (by positivity)
    _ = C * u (y,t+δ) := by dsimp [C]; ring

/-- Compact smooth cutoffs exhaust any open spatial set. They are exactly one
eventually at each point, not merely almost everywhere convergent. -/
lemma exists_cutoff_sequence {n : ℕ} (Ω : Domain n) :
    ∃ η : ℕ → P201Specs.Test ℝ Ω,
      (∀ m x, 0 ≤ η m x ∧ η m x ≤ 1) ∧
      ∀ x ∈ Ω, ∀ᶠ m in atTop, η m x = 1 := by
  classical
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let K : ℕ → Set (Space n) := fun m =>
    Subtype.val '' compactCovering Ω m
  have hK (m : ℕ) : IsCompact (K m) :=
    (isCompact_compactCovering Ω m).image continuous_subtype_val
  have hKΩ (m : ℕ) : K m ⊆ Ω := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hex (m : ℕ) : ∃ η : P201Specs.Test ℝ Ω,
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ ∀ x ∈ K m, η x = 1 := by
    obtain ⟨η, hη, U, hKU, _, hone⟩ := P102.U4.cutoff n Ω ⟨K m,hK m⟩ (hKΩ m)
    exact ⟨η, hη, fun x hx => hone x (hKU hx)⟩
  choose η hη hone using hex
  refine ⟨η, hη, ?_⟩
  intro x hx
  obtain ⟨m, hm⟩ := exists_mem_compactCovering (⟨x,hx⟩ : Ω)
  filter_upwards [eventually_ge_atTop m] with k hk
  apply hone k x
  exact ⟨⟨x,hx⟩, compactCovering_subset Ω hk hm, rfl⟩

/-- Internal comparison interface for compact smooth initial data. It is
proved below by the classical maximum principle. -/
def SmoothDataComparison : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ (Ω : Domain n) (T : ℝ), 0 < T → closedCube ℓ a ⊆ (Ω : Set (Space n)) →
  ∀ u : SpaceTime n → ℝ,
    IsClassicalCaloricOn u ((Ω : Set (Space n)) ×ˢ Ioo 0 T) →
    (∀ z ∈ (Ω : Set (Space n)) ×ˢ Ioo 0 T, 0 ≤ u z) →
  ∀ s q : ℝ, 0 < s → s < q → q < T →
  ∀ (g : Space n → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ cube ℓ a →
    (∀ z ∈ cube ℓ a, g z ≤ u (z,s)) →
  ∀ y ∈ closedCube ℓ a,
    kernelSolution ℓ a g (q-s) y ≤ u (y,q)

/-- The source's approximation step removes all compatibility restrictions on
the initial slice. No compact-support assumption is placed on u itself. -/
lemma kernelComparison_of_smoothData
    (hIntegral : kernelIntegralStatement) (hSmoothData : SmoothDataComparison) :
    P201Specs.Heat.CubeHarnack.kernelComparisonStatement := by
  intro n hn ℓ hℓ a Ω T hT hQ u hu hun s q hs hsq hqT y hy
  let Q : Domain n := ⟨cube ℓ a, isOpen_cube ℓ a⟩
  obtain ⟨η, hη, hηlim⟩ := exists_cutoff_sequence Q
  let e := P201Specs.Heat.spaceTimeCoordinates n
  let D : Domain (n+1) := ⟨e ⁻¹' ((Ω : Set (Space n)) ×ˢ Ioo 0 T),
    (Ω.isOpen.prod isOpen_Ioo).preimage e.continuous⟩
  have huD : IsClassicalCaloricOn u (e.symm ⁻¹' (D : Set (Space (n+1)))) := by
    have he : e.symm ⁻¹' (D : Set (Space (n+1))) = (Ω : Set (Space n)) ×ˢ Ioo 0 T := by
      ext p
      simp only [D, TopologicalSpace.Opens.coe_mk, mem_preimage,
        ContinuousLinearEquiv.apply_symm_apply]
    rw [he]
    exact hu
  have hsT : s < T := hsq.trans hqT
  have hslice : ContDiffOn ℝ ∞ (fun z => u (z,s)) Q := by
    have hf := classicalCaloric_contDiffOn_coords hn D huD
    have hmap : MapsTo (fun z : Space n => e.symm (z,s)) (Q : Set (Space n)) D := by
      intro z hz
      change e (e.symm (z,s)) ∈ (Ω : Set (Space n)) ×ˢ Ioo 0 T
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact ⟨hQ (cube_subset_closedCube ℓ a hz), hs, hsT⟩
    have he : ContDiffOn ℝ ∞ (fun z : Space n => e.symm (z,s)) Q :=
      e.symm.contDiff.contDiffOn.comp (contDiffOn_id.prodMk contDiffOn_const)
        (mapsTo_univ _ _)
    apply (hf.comp he hmap).congr
    intro z hz
    change u (z,s) = u (e (e.symm (z,s)))
    rw [ContinuousLinearEquiv.apply_symm_apply]
  let g : ℕ → P201Specs.Test ℝ Q := fun m =>
    P102.U4.coefficientTestProduct ⟨fun z => u (z,s), hslice⟩ (η m)
  have hgval (m : ℕ) (z : Space n) : g m z = u (z,s) * η m z := rfl
  have hgslice : ContinuousOn (fun z => u (z,s)) (closedCube ℓ a) :=
    hu.1.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun z hz => ⟨hQ hz, hs, hsT⟩)
  have hki : IntegrableOn (fun z => cubeKernel ℓ a (q-s) y z * u (z,s))
      (cube ℓ a) (spatialMeasure n) :=
    hIntegral n hn ℓ hℓ a _ hgslice (q-s) (sub_pos.mpr hsq) y
  have hgki (m : ℕ) : IntegrableOn (fun z => cubeKernel ℓ a (q-s) y z * g m z)
      (cube ℓ a) (spatialMeasure n) :=
    hIntegral n hn ℓ hℓ a _ (g m).continuous.continuousOn (q-s) (sub_pos.mpr hsq) y
  have hlim : Tendsto (fun m => kernelSolution ℓ a (g m) (q-s) y) atTop
      (𝓝 (kernelSolution ℓ a (fun z => u (z,s)) (q-s) y)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun z => ‖cubeKernel ℓ a (q-s) y z * u (z,s)‖)
      (fun m => (hgki m).aestronglyMeasurable) hki.norm
    · intro m
      filter_upwards [ae_restrict_mem (isOpen_cube ℓ a).measurableSet] with z hz
      rw [hgval, ← mul_assoc, norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (hη m z).1]
      exact (hη m z).2
    · filter_upwards [ae_restrict_mem (isOpen_cube ℓ a).measurableSet] with z hz
      apply tendsto_const_nhds.congr'
      filter_upwards [hηlim z hz] with m hm
      rw [hgval, hm, mul_one]
  apply le_of_tendsto hlim
  filter_upwards [] with m
  apply hSmoothData n hn ℓ hℓ a Ω T hT hQ u hu hun s q hs hsq hqT
    (g m) (g m).contDiff (g m).hasCompactSupport (g m).tsupport_subset _ y hy
  intro z hz
  rw [hgval]
  exact mul_le_of_le_one_right (hun (z,s) ⟨hQ (cube_subset_closedCube ℓ a hz), hs, hsT⟩)
    (hη m z).2

/-- Compact-support parametric integrals are smooth. This is obtained from
Mathlib's convolution theorem by reflecting the integration variable and
restricting the extra translation parameter to zero. -/
lemma integral_contDiffOn_compact_support {n : ℕ} {S : Set (SpaceTime n)}
    (hS : IsOpen S) {K : Set (Space n)} (hK : IsCompact K)
    {F : SpaceTime n × Space n → ℝ}
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ))
    (hFs : ∀ p ∈ S, ∀ z ∉ K, F (p,z) = 0) :
    ContDiffOn ℝ ∞ (fun p => ∫ z, F (p,z) ∂spatialMeasure n) S := by
  let G : SpaceTime n → Space n → ℝ := fun p z => F (p,-z)
  have hG : ContDiffOn ℝ ∞ (Function.uncurry G) (S ×ˢ univ) := by
    have hc : ContDiffOn ℝ ∞ (fun z : SpaceTime n × Space n => (z.1,-z.2)) (S ×ˢ univ) :=
      contDiffOn_fst.prodMk contDiffOn_snd.neg
    exact hF.comp hc (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hconv := contDiffOn_convolution_right_with_param
    (μ := spatialMeasure n) (ContinuousLinearMap.mul ℝ ℝ) hS hK.neg
    (g := G) (f := fun _ : Space n => (1 : ℝ))
    (fun p z hp hz => hFs p hp (-z) (by simpa only [Set.mem_neg, neg_neg] using hz))
    (locallyIntegrable_const (1 : ℝ)) hG
  have hc : ContDiffOn ℝ ∞ (fun p : SpaceTime n => (p,(0 : Space n))) S :=
    contDiffOn_id.prodMk contDiffOn_const
  have hmap : MapsTo (fun p : SpaceTime n => (p,(0 : Space n))) S (S ×ˢ univ) :=
    fun _ hp => ⟨hp, mem_univ _⟩
  simpa [convolution, G, Function.comp_def, ContinuousLinearMap.mul_apply'] using hconv.comp hc hmap

lemma kernelSolution_eq_integral {n : ℕ} {ℓ τ : ℝ} {a x : Space n}
    {g : Space n → ℝ} (hgs : tsupport g ⊆ cube ℓ a) :
    kernelSolution ℓ a g τ x = ∫ z, cubeKernel ℓ a τ x z * g z ∂spatialMeasure n := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hgs h)), mul_zero]

/-- Smoothness of the integrated kernel for smooth compactly supported data. -/
lemma kernelSolution_smooth (hSmooth : kernelSmoothStatement)
    {n : ℕ} (hn : 1 ≤ n) {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Space n)
    {g : Space n → ℝ} (hg : ContDiff ℝ ∞ g) (hgk : HasCompactSupport g)
    (hgs : tsupport g ⊆ cube ℓ a) :
    ContDiffOn ℝ ∞ (fun p : SpaceTime n => kernelSolution ℓ a g p.2 p.1)
      {p | 0 < p.2} := by
  have hS : IsOpen {p : SpaceTime n | 0 < p.2} := isOpen_lt continuous_const continuous_snd
  have hmap : ContDiffOn ℝ ∞
      (fun p : SpaceTime n × Space n => (p.1.1,p.2,p.1.2))
      ({p : SpaceTime n | 0 < p.2} ×ˢ univ) := by fun_prop
  have hk := (hSmooth n hn ℓ hℓ a).comp hmap (fun p hp => hp.1)
  have hF : ContDiffOn ℝ ∞
      (fun p : SpaceTime n × Space n => cubeKernel ℓ a p.1.2 p.1.1 p.2 * g p.2)
      ({p : SpaceTime n | 0 < p.2} ×ˢ univ) :=
    hk.mul (hg.contDiffOn.comp contDiffOn_snd (mapsTo_univ _ _))
  have hi := integral_contDiffOn_compact_support hS hgk hF
    (fun p hp z hz => by rw [image_eq_zero_of_notMem_tsupport hz, mul_zero])
  exact hi.congr (fun p hp => kernelSolution_eq_integral hgs)

/-- Differentiate a jointly smooth function under integration over a fixed
compact set. The derivative bound follows from a compact parameter ball. -/
lemma hasFDerivAt_integral_compact {n : ℕ} {S : Set (SpaceTime n)}
    (hS : IsOpen S) {K : Set (Space n)} (hK : IsCompact K)
    {F : SpaceTime n × Space n → ℝ}
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) {p : SpaceTime n} (hp : p ∈ S) :
    HasFDerivAt (fun q => ∫ z in K, F (q,z) ∂spatialMeasure n)
      (∫ z in K, (fderiv ℝ F (p,z)).comp
        (ContinuousLinearMap.inl ℝ (SpaceTime n) (Space n)) ∂spatialMeasure n) p := by
  let D : SpaceTime n × Space n → SpaceTime n →L[ℝ] ℝ := fun q =>
    (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ (SpaceTime n) (Space n))
  have hD : ContinuousOn D (S ×ˢ univ) :=
    (hF.continuousOn_fderiv_of_isOpen (hS.prod isOpen_univ) (by simp)).clm_comp continuousOn_const
  have hFslice (q : SpaceTime n) (hq : q ∈ S) : ContinuousOn (fun z => F (q,z)) K :=
    hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨hq, mem_univ _⟩)
  have hDslice (q : SpaceTime n) (hq : q ∈ S) : ContinuousOn (fun z => D (q,z)) K :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨hq, mem_univ _⟩)
  obtain ⟨ρ, hρ, hρS⟩ := Metric.isOpen_iff.mp hS p hp
  let ε := ρ/2
  have hε : 0 < ε := half_pos hρ
  have hclosed : closedBall p ε ⊆ S :=
    (closedBall_subset_ball (by dsimp [ε]; linarith)).trans hρS
  have hDK := hD.mono (Set.prod_mono hclosed (subset_univ K))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p ε).prod hK).exists_bound_of_continuousOn hDK
  have hdiff (q : SpaceTime n) (hq : q ∈ S) (z : Space n) :
      HasFDerivAt (fun q => F (q,z)) (D (q,z)) q := by
    have hf := (hF.contDiffAt ((hS.prod isOpen_univ).mem_nhds (x := (q,z)) ⟨hq,mem_univ z⟩)).differentiableAt
      (by simp)
    exact hf.hasFDerivAt.comp q ((hasFDerivAt_id q).prodMk (hasFDerivAt_const z q))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball p ε) (F' := fun q z => D (q,z)) (bound := fun _ => C) (ball_mem_nhds p hε)
  · filter_upwards [hS.mem_nhds hp] with q hq
    exact (hFslice q hq).aestronglyMeasurable hK.measurableSet
  · exact (hFslice p hp).integrableOn_compact hK
  · exact (hDslice p hp).aestronglyMeasurable hK.measurableSet
  · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz q hq
    exact hC (q,z) ⟨ball_subset_closedBall hq,hz⟩
  · exact integrableOn_const hK.measure_ne_top
  · filter_upwards [] with z q hq
    exact hdiff q (hclosed (ball_subset_closedBall hq)) z

lemma kernelSolution_boundary (hBoundary : kernelBoundaryStatement)
    {n : ℕ} (hn : 1 ≤ n) {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Space n)
    {τ : ℝ} (hτ : 0 < τ) (g : Space n → ℝ)
    {x : Space n} (hx : x ∈ closedCube ℓ a \ cube ℓ a) :
    kernelSolution ℓ a g τ x = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  rw [hBoundary n hn ℓ hℓ a τ hτ x y (Or.inl hx), zero_mul]

lemma fderiv_integral_compact_apply {n : ℕ} {S : Set (SpaceTime n)}
    (hS : IsOpen S) {K : Set (Space n)} (hK : IsCompact K)
    {F : SpaceTime n × Space n → ℝ}
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) {p : SpaceTime n} (hp : p ∈ S)
    (v : SpaceTime n) :
    fderiv ℝ (fun q => ∫ z in K, F (q,z) ∂spatialMeasure n) p v =
      ∫ z in K, fderiv ℝ F (p,z) (v,0) ∂spatialMeasure n := by
  have hD : ContinuousOn
      (fun z => (fderiv ℝ F (p,z)).comp (ContinuousLinearMap.inl ℝ (SpaceTime n) (Space n))) K :=
    ((hF.continuousOn_fderiv_of_isOpen (hS.prod isOpen_univ) (by simp)).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨hp, mem_univ _⟩)).clm_comp continuousOn_const
  rw [(hasFDerivAt_integral_compact hS hK hF hp).fderiv,
    ContinuousLinearMap.integral_apply (hD.integrableOn_compact hK)]
  rfl

/-- The second directional derivative can also be moved inside the compact
integral. The first derivative identity holds on an open neighborhood, which
justifies differentiating that identity again. -/
lemma second_fderiv_integral_compact_apply {n : ℕ} {S : Set (SpaceTime n)}
    (hS : IsOpen S) {K : Set (Space n)} (hK : IsCompact K)
    {F : SpaceTime n × Space n → ℝ}
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) {p : SpaceTime n} (hp : p ∈ S)
    (v w : SpaceTime n) :
    fderiv ℝ (fun q =>
      fderiv ℝ (fun q => ∫ z in K, F (q,z) ∂spatialMeasure n) q v) p w =
      ∫ z in K, fderiv ℝ (fun z => fderiv ℝ F z (v,0)) (p,z) (w,0)
        ∂spatialMeasure n := by
  let Fv : SpaceTime n × Space n → ℝ := fun z => fderiv ℝ F z (v,0)
  have hFv : ContDiffOn ℝ ∞ Fv (S ×ˢ univ) :=
    (hF.fderiv_of_isOpen (hS.prod isOpen_univ) (by simp)).clm_apply contDiffOn_const
  have he : (fun q => fderiv ℝ (fun q => ∫ z in K, F (q,z) ∂spatialMeasure n) q v) =ᶠ[𝓝 p]
      (fun q => ∫ z in K, Fv (q,z) ∂spatialMeasure n) := by
    filter_upwards [hS.mem_nhds hp] with q hq
    exact fderiv_integral_compact_apply hS hK hF hq v
  rw [he.fderiv_eq]
  exact fderiv_integral_compact_apply hS hK hFv hp w

/-- Combine the cutoff approximation and the one-cube mass estimate. -/
lemma oneCubeHarnack_of_smoothData
    (hIntegral : kernelIntegralStatement) (hNonnegative : kernelNonnegativeStatement)
    (hLower : kernelLowerBoundStatement) (hSmoothData : SmoothDataComparison) :
    P201Specs.Heat.CubeHarnack.oneCubeHarnackStatement :=
  oneCubeHarnack_of_comparison hIntegral hNonnegative hLower
    (kernelComparison_of_smoothData hIntegral hSmoothData)

/-- The heat operator written in ambient space-time directional derivatives.
This is a calculus helper, not a different notion of caloric solution. -/
def fullHeat {n : ℕ} (f : SpaceTime n → ℝ) (p : SpaceTime n) : ℝ :=
  fderiv ℝ f p (0,1) - ∑ i : Fin n,
    fderiv ℝ (fun q => fderiv ℝ f q (P201Specs.coordinate n i,0)) p
      (P201Specs.coordinate n i,0)

lemma fderiv_space_slice_apply {n : ℕ} {S : Set (SpaceTime n)} (hS : IsOpen S)
    {f : SpaceTime n → ℝ} (hf : ContDiffOn ℝ ∞ f S)
    {p : SpaceTime n} (hp : p ∈ S) (v : Space n) :
    fderiv ℝ (fun x => f (x,p.2)) p.1 v = fderiv ℝ f p (v,0) := by
  have hd := (hf.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)
  have hmap : HasFDerivAt (fun x : Space n => (x,p.2))
      (ContinuousLinearMap.inl ℝ (Space n) ℝ) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have he := hd.hasFDerivAt.comp p.1 hmap
  exact congrArg (fun L => L v) he.fderiv

lemma deriv_time_slice_eq {n : ℕ} {S : Set (SpaceTime n)} (hS : IsOpen S)
    {f : SpaceTime n → ℝ} (hf : ContDiffOn ℝ ∞ f S)
    {p : SpaceTime n} (hp : p ∈ S) :
    deriv (fun t => f (p.1,t)) p.2 = fderiv ℝ f p (0,1) := by
  have hd := (hf.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)
  exact (hd.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

lemma second_fderiv_space_slice_apply {n : ℕ} {S : Set (SpaceTime n)} (hS : IsOpen S)
    {f : SpaceTime n → ℝ} (hf : ContDiffOn ℝ ∞ f S)
    {p : SpaceTime n} (hp : p ∈ S) (v w : Space n) :
    fderiv ℝ (fun x => fderiv ℝ (fun y => f (y,p.2)) x v) p.1 w =
      fderiv ℝ (fun q => fderiv ℝ f q (v,0)) p (w,0) := by
  have hneigh : ∀ᶠ x in 𝓝 p.1, (x,p.2) ∈ S :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually (hS.mem_nhds hp)
  have he : (fun x => fderiv ℝ (fun y => f (y,p.2)) x v) =ᶠ[𝓝 p.1]
      (fun x => fderiv ℝ f (x,p.2) (v,0)) := by
    filter_upwards [hneigh] with x hx
    exact fderiv_space_slice_apply hS hf hx v
  rw [he.fderiv_eq]
  exact fderiv_space_slice_apply hS
    ((hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const) hp w

lemma laplacian_space_slice_eq {n : ℕ} {S : Set (SpaceTime n)} (hS : IsOpen S)
    {f : SpaceTime n → ℝ} (hf : ContDiffOn ℝ ∞ f S)
    {p : SpaceTime n} (hp : p ∈ S) :
    P201Specs.laplacian (fun x => f (x,p.2)) p.1 = ∑ i : Fin n,
      fderiv ℝ (fun q => fderiv ℝ f q (P201Specs.coordinate n i,0)) p
        (P201Specs.coordinate n i,0) := by
  rw [laplacian_eq_sum_partialWord]
  apply Finset.sum_congr rfl
  intro i hi
  exact second_fderiv_space_slice_apply hS hf hp (P201Specs.coordinate n i)
    (P201Specs.coordinate n i)

lemma fullHeat_eq_time_sub_laplacian {n : ℕ} {S : Set (SpaceTime n)} (hS : IsOpen S)
    {f : SpaceTime n → ℝ} (hf : ContDiffOn ℝ ∞ f S)
    {p : SpaceTime n} (hp : p ∈ S) :
    fullHeat f p = deriv (fun t => f (p.1,t)) p.2 -
      P201Specs.laplacian (fun x => f (x,p.2)) p.1 := by
  rw [deriv_time_slice_eq hS hf hp, laplacian_space_slice_eq hS hf hp]
  rfl

lemma fullHeat_eq_zero_of_classical {n : ℕ} {S : Set (SpaceTime n)} (hS : IsOpen S)
    {f : SpaceTime n → ℝ} (hf : ContDiffOn ℝ ∞ f S)
    (hc : IsClassicalCaloricOn f S) {p : SpaceTime n} (hp : p ∈ S) :
    fullHeat f p = 0 := by
  rw [fullHeat_eq_time_sub_laplacian hS hf hp]
  exact sub_eq_zero.mpr (hc.2.2.2.2 p hp).2.2



lemma classicalCaloric_contDiffOn {n : ℕ} (hn : 1 ≤ n)
    {S : Set (SpaceTime n)} (hS : IsOpen S) {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u S) : ContDiffOn ℝ ∞ u S := by
  let e := P201Specs.Heat.spaceTimeCoordinates n
  let D : Domain (n+1) := ⟨e ⁻¹' S, hS.preimage e.continuous⟩
  have he : e.symm ⁻¹' (D : Set (Space (n+1))) = S := by
    ext p
    simp only [D, TopologicalSpace.Opens.coe_mk, mem_preimage,
      ContinuousLinearEquiv.apply_symm_apply]
  have huD : IsClassicalCaloricOn u (e.symm ⁻¹' (D : Set (Space (n+1)))) := he ▸ hu
  have hf := classicalCaloric_contDiffOn_coords hn D huD
  have hg := hf.comp e.symm.contDiff.contDiffOn (fun p hp => by
    change e (e.symm p) ∈ S
    simpa using hp)
  simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply, e] using hg

lemma fullHeat_add_time {n : ℕ} (f : SpaceTime n → ℝ) (s : ℝ) (p : SpaceTime n) :
    fullHeat (fun q => f (q.1,q.2+s)) p = fullHeat f (p.1,p.2+s) := by
  have he : (fun q : SpaceTime n => f (q.1,q.2+s)) = (fun q => f (q+(0,s))) := by
    funext q
    congr 1
    exact (Prod.ext (add_zero _).symm rfl)
  rw [he]
  unfold fullHeat
  have hsecond (v : SpaceTime n) :
      fderiv ℝ (fun q => fderiv ℝ f (q+(0,s)) v) p =
      fderiv ℝ (fun q => fderiv ℝ f q v) (p+(0,s)) :=
    fderiv_comp_add_right (f := fun q => fderiv ℝ f q v) (0,s)
  simp only [fderiv_comp_add_right, hsecond]
  have hp' : p + (0,s) = (p.1,p.2+s) := by
    ext <;> simp
  rw [hp']

lemma fullHeat_sub {n : ℕ} {S : Set (SpaceTime n)} (hS : IsOpen S)
    {f g : SpaceTime n → ℝ} (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g S)
    {p : SpaceTime n} (hp : p ∈ S) :
    fullHeat (f-g) p = fullHeat f p - fullHeat g p := by
  have hdF (q : SpaceTime n) (hq : q ∈ S) :=
    (hf.contDiffAt (hS.mem_nhds hq)).differentiableAt (by simp)
  have hdG (q : SpaceTime n) (hq : q ∈ S) :=
    (hg.contDiffAt (hS.mem_nhds hq)).differentiableAt (by simp)
  have hfirst (v : SpaceTime n) :
      (fun q => fderiv ℝ (f-g) q v) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ f q v - fderiv ℝ g q v) := by
    filter_upwards [hS.mem_nhds hp] with q hq
    rw [fderiv_sub (hdF q hq) (hdG q hq)]
    rfl
  have hsnd (v : SpaceTime n) :
      fderiv ℝ (fun q => fderiv ℝ (f-g) q v) p v =
        fderiv ℝ (fun q => fderiv ℝ f q v) p v -
        fderiv ℝ (fun q => fderiv ℝ g q v) p v := by
    rw [(hfirst v).fderiv_eq]
    rw [fderiv_fun_sub]
    · rfl
    · exact (((hf.fderiv_of_isOpen (m := ∞) hS (by simp)).clm_apply contDiffOn_const).contDiffAt
        (hS.mem_nhds hp)).differentiableAt (by simp)
    · exact (((hg.fderiv_of_isOpen (m := ∞) hS (by simp)).clm_apply contDiffOn_const).contDiffAt
        (hS.mem_nhds hp)).differentiableAt (by simp)
  unfold fullHeat
  rw [fderiv_sub (hdF p hp) (hdG p hp)]
  simp only [sub_apply, hsnd, Finset.sum_sub_distrib]
  ring


lemma continuousOn_initial_extension {X : Type*} [TopologicalSpace X]
    {s : Set X} {f : ℝ → X → ℝ} {g : X → ℝ} {L : ℝ}
    (hg : ContinuousOn g s)
    (hf : ContinuousOn (fun p : X × ℝ => f p.2 p.1) (s ×ˢ Ioi 0))
    (hlim : TendstoUniformlyOn f g (𝓝[>] (0 : ℝ)) s) :
    ContinuousOn (fun p : X × ℝ => if p.2 = 0 then g p.1 else f p.2 p.1)
      (s ×ˢ Icc 0 L) := by
  intro p hp
  by_cases hp0 : p.2 = 0
  · apply Metric.continuousWithinAt_iff'.mpr
    intro ε hε
    have hsmall := Metric.tendstoUniformlyOn_iff.mp hlim (ε/2) (half_pos hε)
    have ht : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t → ∀ x ∈ s, dist (g x) (f t x) < ε/2 :=
      eventually_nhdsWithin_iff.mp hsmall
    have ht' : ∀ᶠ q : X × ℝ in 𝓝 p,
        0 < q.2 → ∀ x ∈ s, dist (g x) (f q.2 x) < ε/2 := by
      have hsnd : Tendsto (fun q : X × ℝ => q.2) (𝓝 p) (𝓝 (0 : ℝ)) := by
        simpa [hp0] using (continuous_snd.tendsto p)
      exact hsnd.eventually ht
    have hgfst : ContinuousWithinAt (fun q : X × ℝ => g q.1) (s ×ˢ Icc 0 L) p :=
      (hg p.1 hp.1).comp continuous_fst.continuousWithinAt (fun q hq => hq.1)
    have hgsmall := Metric.continuousWithinAt_iff'.mp hgfst (ε/2) (half_pos hε)
    filter_upwards [ht'.filter_mono nhdsWithin_le_nhds, hgsmall,
      self_mem_nhdsWithin] with q hqt hqg hq
    simp only [hp0, ↓reduceIte]
    split_ifs with hq0
    · exact hqg.trans (half_lt_self hε)
    · have hqpos : 0 < q.2 := lt_of_le_of_ne hq.2.1 (Ne.symm hq0)
      calc
        dist (f q.2 q.1) (g p.1) ≤ dist (f q.2 q.1) (g q.1) + dist (g q.1) (g p.1) := dist_triangle _ _ _
        _ < ε/2 + ε/2 := add_lt_add (by simpa only [dist_comm] using hqt hqpos q.1 hq.1) hqg
        _ = ε := by ring
  · have hpos : 0 < p.2 := lt_of_le_of_ne hp.2.1 (Ne.symm hp0)
    have hposN : ∀ᶠ q : X × ℝ in 𝓝 p, 0 < q.2 :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds hpos
    have hset : s ×ˢ Ioi (0 : ℝ) ∈ 𝓝[s ×ˢ Icc 0 L] p := by
      filter_upwards [hposN.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hqp hq
      exact ⟨hq.1,hqp⟩
    have hfc := (hf p ⟨hp.1,hpos⟩).mono_of_mem_nhdsWithin hset
    apply hfc.congr_of_eventuallyEq _ (by simp [hp0])
    filter_upwards [hposN.filter_mono nhdsWithin_le_nhds] with q hq
    simp [ne_of_gt hq]

lemma kernelSolution_initial_extension_continuousOn
    (hInitial : kernelInitialStatement) (hSmooth : kernelSmoothStatement)
    {n : ℕ} (hn : 1 ≤ n) {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Space n)
    {g : Space n → ℝ} (hg : ContDiff ℝ ∞ g) (hgk : HasCompactSupport g)
    (hgs : tsupport g ⊆ cube ℓ a) (L : ℝ) :
    ContinuousOn (fun p : SpaceTime n =>
      if p.2 = 0 then g p.1 else kernelSolution ℓ a g p.2 p.1)
      (closedCube ℓ a ×ˢ Icc 0 L) := by
  apply continuousOn_initial_extension hg.continuous.continuousOn
  · exact (kernelSolution_smooth hSmooth hn hℓ a hg hgk hgs).continuousOn.mono
      (fun p hp => hp.2)
  · exact hInitial n hn ℓ hℓ a g hg hgk hgs

lemma classical_of_smooth_fullHeat {n : ℕ} {S : Set (SpaceTime n)} (hS : IsOpen S)
    {f : SpaceTime n → ℝ} (hf : ContDiffOn ℝ ∞ f S)
    (hh : ∀ p ∈ S, fullHeat f p = 0) : IsClassicalCaloricOn f S := by
  let J : Space n →L[ℝ] SpaceTime n := ContinuousLinearMap.inl ℝ (Space n) ℝ
  let G : SpaceTime n → (Space n →L[ℝ] ℝ) := fun p => (fderiv ℝ f p).comp J
  have hG : ContDiffOn ℝ ∞ G S :=
    (hf.fderiv_of_isOpen hS (by simp)).clm_comp contDiffOn_const
  have hGe (p : SpaceTime n) (hp : p ∈ S) :
      fderiv ℝ (fun x => f (x,p.2)) p.1 = G p := by
    ext v
    exact fderiv_space_slice_apply hS hf hp v
  have hG2e (p : SpaceTime n) (hp : p ∈ S) :
      fderiv ℝ (fun x => fderiv ℝ (fun y => f (y,p.2)) x) p.1 =
        (fderiv ℝ G p).comp J := by
    have he : (fun x => fderiv ℝ (fun y => f (y,p.2)) x) =ᶠ[𝓝 p.1]
        (fun x => G (x,p.2)) := by
      have hn : ∀ᶠ x in 𝓝 p.1, (x,p.2) ∈ S :=
        (continuous_id.prodMk continuous_const).continuousAt.eventually (hS.mem_nhds hp)
      filter_upwards [hn] with x hx
      exact hGe (x,p.2) hx
    rw [he.fderiv_eq]
    have hd := (hG.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)
    have hm : HasFDerivAt (fun x : Space n => (x,p.2)) J p.1 :=
      (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
    exact (hd.hasFDerivAt.comp p.1 hm).fderiv
  refine ⟨hf.continuousOn, ?_, ?_, ?_, ?_⟩
  · exact ((hf.continuousOn_fderiv_of_isOpen hS (by simp)).clm_apply continuousOn_const).congr
      (fun p hp => deriv_time_slice_eq hS hf hp)
  · exact hG.continuousOn.congr (fun p hp => hGe p hp)
  · exact ((hG.continuousOn_fderiv_of_isOpen hS (by simp)).clm_comp continuousOn_const).congr
      (fun p hp => hG2e p hp)
  · intro p hp
    have hmap : ContDiffAt ℝ ∞ (fun x : Space n => (x,p.2)) p.1 :=
      contDiffAt_id.prodMk contDiffAt_const
    have htime : ContDiffAt ℝ ∞ (fun t : ℝ => (p.1,t)) p.2 :=
      contDiffAt_const.prodMk contDiffAt_id
    refine ⟨((hf.contDiffAt (hS.mem_nhds hp)).comp p.2 htime).differentiableAt (by simp),
      ((hf.contDiffAt (hS.mem_nhds hp)).comp p.1 hmap).of_le (by simp), ?_⟩
    exact sub_eq_zero.mp ((fullHeat_eq_time_sub_laplacian hS hf hp) ▸ hh p hp)

lemma fderiv_param_slice_apply {n : ℕ} {S : Set (SpaceTime n)} (hS : IsOpen S)
    {F : SpaceTime n × Space n → ℝ} (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ))
    {p : SpaceTime n} (hp : p ∈ S) (z : Space n) (v : SpaceTime n) :
    fderiv ℝ (fun q => F (q,z)) p v = fderiv ℝ F (p,z) (v,0) := by
  have hd := (hF.contDiffAt ((hS.prod isOpen_univ).mem_nhds (x := (p,z)) ⟨hp,mem_univ z⟩)).differentiableAt
    (by simp)
  have hm : HasFDerivAt (fun q : SpaceTime n => (q,z))
      (ContinuousLinearMap.inl ℝ (SpaceTime n) (Space n)) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const z p)
  exact congrArg (fun L => L v) (hd.hasFDerivAt.comp p hm).fderiv

lemma second_fderiv_param_slice_apply {n : ℕ} {S : Set (SpaceTime n)} (hS : IsOpen S)
    {F : SpaceTime n × Space n → ℝ} (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ))
    {p : SpaceTime n} (hp : p ∈ S) (z : Space n) (v w : SpaceTime n) :
    fderiv ℝ (fun q => fderiv ℝ (fun r => F (r,z)) q v) p w =
      fderiv ℝ (fun q => fderiv ℝ F q (v,0)) (p,z) (w,0) := by
  have he : (fun q => fderiv ℝ (fun r => F (r,z)) q v) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ F (q,z) (v,0)) := by
    filter_upwards [hS.mem_nhds hp] with q hq
    exact fderiv_param_slice_apply hS hF hq z v
  rw [he.fderiv_eq]
  exact fderiv_param_slice_apply hS
    ((hF.fderiv_of_isOpen (hS.prod isOpen_univ) (by simp)).clm_apply contDiffOn_const) hp z w

lemma fullHeat_integral_compact {n : ℕ} {S : Set (SpaceTime n)}
    (hS : IsOpen S) {K : Set (Space n)} (hK : IsCompact K)
    {F : SpaceTime n × Space n → ℝ}
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) {p : SpaceTime n} (hp : p ∈ S) :
    fullHeat (fun q => ∫ z in K, F (q,z) ∂spatialMeasure n) p =
      ∫ z in K, fullHeat (fun q => F (q,z)) p ∂spatialMeasure n := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ F) (S ×ˢ univ) :=
    hF.fderiv_of_isOpen (hS.prod isOpen_univ) (by simp)
  have hc (v : SpaceTime n) : ContinuousOn
      (fun z => fderiv ℝ F (p,z) (v,0)) K :=
    (hD.continuousOn.clm_apply continuousOn_const).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun z hz => ⟨hp,mem_univ z⟩)
  have hc2 (v w : SpaceTime n) : ContinuousOn
      (fun z => fderiv ℝ (fun q => fderiv ℝ F q (v,0)) (p,z) (w,0)) K :=
    (((hD.clm_apply contDiffOn_const).continuousOn_fderiv_of_isOpen
      (hS.prod isOpen_univ) (by simp)).clm_apply continuousOn_const).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun z hz => ⟨hp,mem_univ z⟩)
  unfold fullHeat
  rw [fderiv_integral_compact_apply hS hK hF hp]
  simp_rw [second_fderiv_integral_compact_apply hS hK hF hp]
  simp_rw [fderiv_param_slice_apply hS hF hp,
    second_fderiv_param_slice_apply hS hF hp]
  rw [integral_sub ((hc _).integrableOn_compact hK)
      (integrable_finsetSum _ (fun i hi => (hc2 _ _).integrableOn_compact hK)),
    integral_finsetSum _ (fun i hi => (hc2 _ _).integrableOn_compact hK)]

lemma fullHeat_mul_const {n : ℕ} {S : Set (SpaceTime n)} (hS : IsOpen S)
    {f : SpaceTime n → ℝ} (hf : ContDiffOn ℝ ∞ f S)
    {p : SpaceTime n} (hp : p ∈ S) (c : ℝ) :
    fullHeat (fun q => f q * c) p = fullHeat f p * c := by
  have he (q : SpaceTime n) (hq : q ∈ S) (v : SpaceTime n) :
      fderiv ℝ (fun r => f r * c) q v = fderiv ℝ f q v * c := by
    rw [fderiv_mul_const ((hf.contDiffAt (hS.mem_nhds hq)).differentiableAt (by simp))]
    simp [mul_comm]
  have he2 (v w : SpaceTime n) :
      fderiv ℝ (fun q => fderiv ℝ (fun r => f r * c) q v) p w =
        fderiv ℝ (fun q => fderiv ℝ f q v) p w * c := by
    have hevent : (fun q => fderiv ℝ (fun r => f r * c) q v) =ᶠ[𝓝 p]
        (fun q => fderiv ℝ f q v * c) := by
      filter_upwards [hS.mem_nhds hp] with q hq
      exact he q hq v
    have hv : ContDiffOn ℝ ∞ (fun q => fderiv ℝ f q v) S :=
      (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
    rw [hevent.fderiv_eq, fderiv_mul_const
      ((hv.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp))]
    simp [mul_comm]
  unfold fullHeat
  rw [he p hp]
  simp_rw [he2]
  rw [← Finset.sum_mul, sub_mul]

lemma kernelSolution_caloric (hSmooth : kernelSmoothStatement) (hCaloric : kernelCaloricStatement)
    {n : ℕ} (hn : 1 ≤ n) {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Space n)
    {g : Space n → ℝ} (hg : ContDiff ℝ ∞ g) (hgk : HasCompactSupport g)
    (hgs : tsupport g ⊆ cube ℓ a) :
    IsClassicalCaloricOn (fun p : SpaceTime n => kernelSolution ℓ a g p.2 p.1)
      (cube ℓ a ×ˢ Ioi 0) := by
  let S : Set (SpaceTime n) := cube ℓ a ×ˢ Ioi 0
  have hS : IsOpen S := (isOpen_cube ℓ a).prod isOpen_Ioi
  have hpos : IsOpen {p : SpaceTime n | 0 < p.2} := isOpen_lt continuous_const continuous_snd
  have hSub : S ⊆ {p : SpaceTime n | 0 < p.2} := fun p hp => hp.2
  have hks := kernelSolution_smooth hSmooth hn hℓ a hg hgk hgs
  apply classical_of_smooth_fullHeat hS (hks.mono hSub)
  intro p hp
  let F : SpaceTime n × Space n → ℝ := fun q => cubeKernel ℓ a q.1.2 q.1.1 q.2 * g q.2
  have hmap : ContDiffOn ℝ ∞
      (fun p : SpaceTime n × Space n => (p.1.1,p.2,p.1.2)) (S ×ˢ univ) := by fun_prop
  have hF : ContDiffOn ℝ ∞ F (S ×ˢ univ) :=
    ((hSmooth n hn ℓ hℓ a).comp hmap (fun q hq => hq.1.2)).mul
      (hg.contDiffOn.comp contDiffOn_snd (mapsTo_univ _ _))
  have he (q : SpaceTime n) :
      kernelSolution ℓ a g q.2 q.1 = ∫ z in tsupport g, F (q,z) ∂spatialMeasure n := by
    rw [kernelSolution_eq_integral hgs]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero])).symm
  have heq : (fun q : SpaceTime n => kernelSolution ℓ a g q.2 q.1) =
      (fun q => ∫ z in tsupport g, F (q,z) ∂spatialMeasure n) := funext he
  rw [heq, fullHeat_integral_compact hS hgk hF hp]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro z hz
  have hzmap : ContDiffOn ℝ ∞ (fun q : SpaceTime n => (q.1,z,q.2)) S := by fun_prop
  have hk : ContDiffOn ℝ ∞ (fun q : SpaceTime n => cubeKernel ℓ a q.2 q.1 z) S :=
    (hSmooth n hn ℓ hℓ a).comp hzmap (fun q hq => hq.2)
  dsimp [F]
  rw [fullHeat_mul_const hS hk hp]
  rw [fullHeat_eq_zero_of_classical hS hk (hCaloric n hn ℓ hℓ a z) hp, zero_mul]


open P201Specs.HeatMaximum
lemma heat_bound_of_fullHeat {n : ℕ} {Q : Domain n} {L : ℝ}
    (hQ : Bornology.IsBounded (Q : Set (Space n)))
    (hne : (Q : Set (Space n)).Nonempty) (hL : 0 < L)
    {f : SpaceTime n → ℝ} (hf : ContinuousOn f (closedCylinder Q L))
    {S : Set (SpaceTime n)} (hSo : IsOpen S) (hfs : ContDiffOn ℝ ∞ f S)
    (hS : activeCylinder Q L ⊆ S)
    (hheat : ∀ z ∈ activeCylinder Q L, fullHeat f z ≤ 0)
    (M : ℝ) (hb : ∀ z ∈ parabolicBoundary Q L, f z ≤ M) :
    ∀ z ∈ closedCylinder Q L, f z ≤ M := by
  classical
  let C : Coefficients n := ⟨fun _ => 1, fun _ _ => 0, fun _ => 0⟩
  have hfat (z : SpaceTime n) (hz : z ∈ activeCylinder Q L) : ContDiffAt ℝ ∞ f z :=
    hfs.contDiffAt (hSo.mem_nhds (hS hz))
  have hspace (z : SpaceTime n) (hz : z ∈ activeCylinder Q L) :
      ContDiffAt ℝ 2 (fun x => f (x,z.2)) z.1 :=
    ((hfat z hz).comp z.1 (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
  have htime (z : SpaceTime n) (hz : z ∈ activeCylinder Q L) :
      DifferentiableAt ℝ (fun t => f (z.1,t)) z.2 :=
    ((hfat z hz).differentiableAt (by simp)).comp z.2
      (differentiableAt_const z.1 |>.prodMk differentiableAt_id)
  apply P201.Heat.bound_of_boundary_bound hQ hne hL (C := C)
    (fun _ _ => Matrix.PosSemidef.one) (fun _ _ => le_rfl) hf
  · intro t ht x hx
    exact (hspace (x,t) ⟨hx,ht⟩).contDiffWithinAt
  · intro z hz
    exact (htime z hz).differentiableWithinAt
  · intro z hz
    have ht := (htime z hz).derivWithin (uniqueDiffOn_Iic L z.2 hz.2.2)
    have heq : operator C L f z = fullHeat f z := by
      rw [fullHeat_eq_time_sub_laplacian hSo hfs (hS hz)]
      simp only [operator, timeDerivative, C, ht, Matrix.one_apply, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero,
        sub_zero]
      rw [P201.Heat.laplacian_eq_sum_fderiv (hspace z hz)]
      rfl
    rw [heq]
    exact hheat z hz
  · intro z hz
    simp [C]
  · exact hb


lemma fullHeat_congr_of_eventuallyEq {n : ℕ} {f g : SpaceTime n → ℝ} {p : SpaceTime n}
    (he : f =ᶠ[𝓝 p] g) : fullHeat f p = fullHeat g p := by
  unfold fullHeat
  rw [he.fderiv_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hd : (fun q => fderiv ℝ f q (P201Specs.coordinate n i,0)) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ g q (P201Specs.coordinate n i,0)) :=
    he.fderiv.fun_comp (fun L => L (P201Specs.coordinate n i,0))
  rw [hd.fderiv_eq]

/-- Comparison for compact smooth initial data, with a continuous extension at
zero. The maximum principle is applied on the shifted closed cylinder. -/
lemma smoothDataComparison
    (hBoundary : kernelBoundaryStatement) (hCaloric : kernelCaloricStatement)
    (hInitial : kernelInitialStatement) (hSmooth : kernelSmoothStatement) :
    SmoothDataComparison := by
  intro n hn ℓ hℓ a Ω T hT hQ u hu hun s q hs hsq hqT g hg hgk hgs hgu y hy
  by_cases hyin : y ∈ cube ℓ a
  swap
  · rw [kernelSolution_boundary hBoundary hn hℓ a (sub_pos.mpr hsq) g ⟨hy,hyin⟩]
    exact hun (y,q) ⟨hQ hy, hs.trans hsq, hqT⟩
  let Q : Domain n := ⟨cube ℓ a, isOpen_cube ℓ a⟩
  let L : ℝ := q-s
  have hL : 0 < L := sub_pos.mpr hsq
  have hcl : closure (Q : Set (Space n)) ⊆ closedCube ℓ a :=
    closure_cube_subset_closedCube ℓ a
  have hbounded : Bornology.IsBounded (Q : Set (Space n)) :=
    (isCompact_closedCube ℓ a).isBounded.subset (cube_subset_closedCube ℓ a)
  let V : SpaceTime n → ℝ := fun p => if p.2 = 0 then g p.1 else kernelSolution ℓ a g p.2 p.1
  let U : SpaceTime n → ℝ := fun p => u (p.1,p.2+s)
  let W : SpaceTime n → ℝ := V-U
  have hVc : ContinuousOn V (closedCylinder Q L) :=
    (kernelSolution_initial_extension_continuousOn hInitial hSmooth hn hℓ a hg hgk hgs L).mono
      (Set.prod_mono hcl (Subset.refl _))
  have hUmap : MapsTo (fun p : SpaceTime n => (p.1,p.2+s)) (closedCylinder Q L)
      ((Ω : Set (Space n)) ×ˢ Ioo 0 T) := by
    intro p hp
    refine ⟨hQ (hcl hp.1), ?_, ?_⟩
    · linarith [hp.2.1]
    · have := hp.2.2
      dsimp [L] at this
      linarith
  have hUc : ContinuousOn U (closedCylinder Q L) :=
    hu.1.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)).continuousOn hUmap
  have hWc : ContinuousOn W (closedCylinder Q L) := hVc.sub hUc
  let S : Set (SpaceTime n) := cube ℓ a ×ˢ Ioo 0 (T-s)
  have hSo : IsOpen S := (isOpen_cube ℓ a).prod isOpen_Ioo
  have hS : activeCylinder Q L ⊆ S := by
    intro p hp
    exact ⟨hp.1, hp.2.1, by dsimp [L] at hp; linarith [hp.2.2]⟩
  have huSmooth := classicalCaloric_contDiffOn hn (Ω.isOpen.prod isOpen_Ioo) hu
  have hUs : ContDiffOn ℝ ∞ U S := by
    apply huSmooth.comp (contDiffOn_fst.prodMk (contDiffOn_snd.add contDiffOn_const))
    intro p hp
    refine ⟨hQ (cube_subset_closedCube ℓ a hp.1), ?_, ?_⟩ <;> linarith [hp.2.1,hp.2.2]
  have hraw : ContDiffOn ℝ ∞ (fun p : SpaceTime n => kernelSolution ℓ a g p.2 p.1) S :=
    (kernelSolution_smooth hSmooth hn hℓ a hg hgk hgs).mono (fun p hp => hp.2.1)
  have hVeq : EqOn V (fun p : SpaceTime n => kernelSolution ℓ a g p.2 p.1) S := by
    intro p hp
    simp only [V, ite_eq_right (ne_of_gt hp.2.1)]
  have hVs : ContDiffOn ℝ ∞ V S := hraw.congr hVeq
  have hWs : ContDiffOn ℝ ∞ W S := hVs.sub hUs
  have hheat : ∀ p ∈ activeCylinder Q L, fullHeat W p ≤ 0 := by
    intro p hp
    have hpS := hS hp
    change fullHeat (V-U) p ≤ 0
    rw [fullHeat_sub hSo hVs hUs hpS]
    have hVheat : fullHeat V p = 0 := by
      have he : V =ᶠ[𝓝 p] (fun z : SpaceTime n => kernelSolution ℓ a g z.2 z.1) :=
        by
          filter_upwards [hSo.mem_nhds hpS] with z hz
          exact hVeq hz
      rw [fullHeat_congr_of_eventuallyEq he]
      exact fullHeat_eq_zero_of_classical hSo hraw
        (IsClassicalCaloricOn.mono
          (kernelSolution_caloric hSmooth hCaloric hn hℓ a hg hgk hgs)
          (fun z hz => ⟨hz.1,hz.2.1⟩)) hpS
    have hUheat : fullHeat U p = 0 := by
      rw [fullHeat_add_time]
      exact fullHeat_eq_zero_of_classical (Ω.isOpen.prod isOpen_Ioo) huSmooth hu
        ⟨hQ (cube_subset_closedCube ℓ a hpS.1), by linarith [hpS.2.1], by linarith [hpS.2.2]⟩
    rw [hVheat,hUheat]
    simp only [sub_zero, le_refl]
  have hgc : ∀ z ∈ closedCube ℓ a, g z ≤ u (z,s) := by
    intro z hz
    by_cases hzQ : z ∈ cube ℓ a
    · exact hgu z hzQ
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hzQ (hgs h))]
      exact hun (z,s) ⟨hQ hz,hs,hsq.trans hqT⟩
  have hb : ∀ p ∈ parabolicBoundary Q L, W p ≤ 0 := by
    intro p hp
    rcases hp with hp | hp
    · have hp0 : p.2 = 0 := hp.2
      change (if p.2 = 0 then g p.1 else _) - u (p.1,p.2+s) ≤ 0
      rw [ite_eq_left hp0, hp0, zero_add]
      exact sub_nonpos.mpr (hgc p.1 (hcl hp.1))
    · have hpcl : p.1 ∈ closure (Q : Set (Space n)) := frontier_subset_closure hp.1
      have hpQ : p.1 ∉ cube ℓ a := by
        have hf := hp.1
        change p.1 ∈ frontier (cube ℓ a) at hf
        rw [frontier, (isOpen_cube ℓ a).interior_eq] at hf
        exact hf.2
      by_cases hp0 : p.2 = 0
      · change (if p.2 = 0 then g p.1 else _) - u (p.1,p.2+s) ≤ 0
        rw [ite_eq_left hp0, hp0, zero_add]
        exact sub_nonpos.mpr (hgc p.1 (hcl hpcl))
      · have hppos : 0 < p.2 := lt_of_le_of_ne hp.2.1 (Ne.symm hp0)
        change (if p.2 = 0 then g p.1 else _) - u (p.1,p.2+s) ≤ 0
        rw [ite_eq_right hp0, kernelSolution_boundary hBoundary hn hℓ a hppos g ⟨hcl hpcl,hpQ⟩]
        exact sub_nonpos.mpr (hun (p.1,p.2+s)
          (hUmap ⟨hpcl,hp.2⟩))
  have hbound := heat_bound_of_fullHeat hbounded ⟨y,hyin⟩ hL hWc hSo hWs hS hheat 0 hb
    (y,L) ⟨subset_closure hyin, hL.le, le_rfl⟩
  have hVL : V (y,L) = kernelSolution ℓ a g (q-s) y := by simp [V,L,ne_of_gt hL]
  change V (y,L) - u (y,L+s) ≤ 0 at hbound
  rw [hVL] at hbound
  simpa only [L, sub_add_cancel] using sub_nonpos.mp hbound


/-- The original kernel comparison, conditional on the complete ordered frozen
cube-kernel interface. No initial-edge compatibility is required of u. -/
theorem kernelComparison_conditional
    (hBoundary : kernelBoundaryStatement)
    (hCaloric : kernelCaloricStatement)
    (_hContinuous : kernelContinuousStatement)
    (_hDerivative : kernelDerivativeStatement)
    (hInitial : kernelInitialStatement)
    (hIntegral : kernelIntegralStatement)
    (_hLower : kernelLowerBoundStatement)
    (_hNonnegative : kernelNonnegativeStatement)
    (_hPositive : kernelPositiveStatement)
    (_hSeries : kernelSeriesStatement)
    (hSmooth : kernelSmoothStatement)
    (_hSummable : kernelSummableStatement)
    (_hTimeSeries : kernelTimeSeriesStatement)
    (_hUniform : kernelUniformStatement) :
    P201Specs.Heat.CubeHarnack.kernelComparisonStatement :=
  kernelComparison_of_smoothData hIntegral
    (smoothDataComparison hBoundary hCaloric hInitial hSmooth)

/-- The original one-cube Harnack statement, conditional on the same complete
ordered interface. The constant is chosen independently of the solution. -/
theorem oneCubeHarnack_conditional
    (hBoundary : kernelBoundaryStatement)
    (hCaloric : kernelCaloricStatement)
    (_hContinuous : kernelContinuousStatement)
    (_hDerivative : kernelDerivativeStatement)
    (hInitial : kernelInitialStatement)
    (hIntegral : kernelIntegralStatement)
    (hLower : kernelLowerBoundStatement)
    (hNonnegative : kernelNonnegativeStatement)
    (_hPositive : kernelPositiveStatement)
    (_hSeries : kernelSeriesStatement)
    (hSmooth : kernelSmoothStatement)
    (_hSummable : kernelSummableStatement)
    (_hTimeSeries : kernelTimeSeriesStatement)
    (_hUniform : kernelUniformStatement) :
    P201Specs.Heat.CubeHarnack.oneCubeHarnackStatement :=
  oneCubeHarnack_of_smoothData hIntegral hNonnegative hLower
    (smoothDataComparison hBoundary hCaloric hInitial hSmooth)

end P201.Heat.CubeHarnack

theorem _root_.«P201».«Heat».«CubeHarnack».«kernelComparison» : _root_.«P201Specs».«Heat».«CubeHarnack».«kernelComparisonStatement» :=
  @_root_.«P201».«Heat».«CubeHarnack».«kernelComparison_conditional» (@_root_.«P201».«Heat».«Cube».«kernelBoundary») (@_root_.«P201».«Heat».«Cube».«kernelCaloric») (@_root_.«P201».«Heat».«Cube».«kernelContinuous») (@_root_.«P201».«Heat».«Cube».«kernelDerivative») (@_root_.«P201».«Heat».«Cube».«kernelInitial») (@_root_.«P201».«Heat».«Cube».«kernelIntegral») (@_root_.«P201».«Heat».«Cube».«kernelLowerBound») (@_root_.«P201».«Heat».«Cube».«kernelNonnegative») (@_root_.«P201».«Heat».«Cube».«kernelPositive») (@_root_.«P201».«Heat».«Cube».«kernelSeries») (@_root_.«P201».«Heat».«Cube».«kernelSmooth») (@_root_.«P201».«Heat».«Cube».«kernelSummable») (@_root_.«P201».«Heat».«Cube».«kernelTimeSeries») (@_root_.«P201».«Heat».«Cube».«kernelUniform»)
theorem _root_.«P201».«Heat».«CubeHarnack».«oneCubeHarnack» : _root_.«P201Specs».«Heat».«CubeHarnack».«oneCubeHarnackStatement» :=
  @_root_.«P201».«Heat».«CubeHarnack».«oneCubeHarnack_conditional» (@_root_.«P201».«Heat».«Cube».«kernelBoundary») (@_root_.«P201».«Heat».«Cube».«kernelCaloric») (@_root_.«P201».«Heat».«Cube».«kernelContinuous») (@_root_.«P201».«Heat».«Cube».«kernelDerivative») (@_root_.«P201».«Heat».«Cube».«kernelInitial») (@_root_.«P201».«Heat».«Cube».«kernelIntegral») (@_root_.«P201».«Heat».«Cube».«kernelLowerBound») (@_root_.«P201».«Heat».«Cube».«kernelNonnegative») (@_root_.«P201».«Heat».«Cube».«kernelPositive») (@_root_.«P201».«Heat».«Cube».«kernelSeries») (@_root_.«P201».«Heat».«Cube».«kernelSmooth») (@_root_.«P201».«Heat».«Cube».«kernelSummable») (@_root_.«P201».«Heat».«Cube».«kernelTimeSeries») (@_root_.«P201».«Heat».«Cube».«kernelUniform»)
