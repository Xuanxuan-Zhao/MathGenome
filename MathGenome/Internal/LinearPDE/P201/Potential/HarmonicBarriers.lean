import MathGenome.Internal.LinearPDE.P201Specs.Potential.HarmonicBarriers
import MathGenome.Internal.LinearPDE.P201.Potential.MeanValues
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Strict exterior spheres and harmonic barriers from the shared C² charts.
The geometric argument uses a local defining function and a quadratic Taylor
estimate. The radial profile is integrated in squared-radius coordinates,
which treats every required dimension with the same formula.
-/
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace P201.HarmonicBarriers
open P201Specs

abbrev HasHarmonicBarrierAt : P201Specs.HarmonicBarriers.HasHarmonicBarrierAtType :=
  @P201Specs.HarmonicBarriers.HasHarmonicBarrierAt

/-- A local quadratic Taylor estimate, obtained by applying the mean value
inequality to a locally Lipschitz first derivative. -/
theorem quadratic_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) :
    ∃ (K δ : ℝ), 0 ≤ K ∧ 0 < δ ∧ ∀ x ∈ ball z δ,
      ‖f x - f z - fderiv ℝ f z (x - z)‖ ≤ K * ‖x - z‖ ^ 2 := by
  obtain ⟨K, t, ht, hK⟩ :=
    (hf.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  have hd : ∀ᶠ x in 𝓝 z, DifferentiableAt ℝ f x :=
    (hf.eventually (by norm_num)).mono fun _ h => h.differentiableAt (by norm_num)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem ht hd)
  refine ⟨K, δ, K.coe_nonneg, hδ, fun x hx => ?_⟩
  have hz : z ∈ ball z δ := mem_ball_self hδ
  have hs : segment ℝ z x ⊆ ball z δ := (convex_ball z δ).segment_subset hz hx
  have hest := (convex_segment z x).norm_image_sub_le_of_norm_fderiv_le'
    (fun w hw => (hsub (hs hw)).2)
    (φ := fderiv ℝ f z)
    (C := (K : ℝ) * ‖x - z‖)
    (fun w hw => (hK.norm_sub_le (hsub (hs hw)).1 (hsub hz).1).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hw) K.coe_nonneg))
    (left_mem_segment ℝ z x) (right_mem_segment ℝ z x)
  simpa [pow_two, mul_assoc] using hest

/-- A quadratic exterior support yields an actual strictly touching sphere.
The local support is sufficient: a smaller sphere separates the distant points
by the triangle inequality. -/
theorem exterior_sphere_of_quadratic_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E} {z v : E} (hv : v ≠ 0) {K δ : ℝ}
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hs : ∀ x ∈ S, dist x z < δ → inner ℝ v (x - z) ≤ K * ‖x - z‖ ^ 2) :
    ∃ (y : E) (r : ℝ), 0 < r ∧ dist z y = r ∧
      ∀ x ∈ S, x ≠ z → r < dist x y := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let t := min (1 / (4 * (K + 1))) (δ / (4 * ‖v‖))
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htK : 2 * t * K < 1 := by
    have h1 : t ≤ 1 / (4 * (K + 1)) := min_le_left _ _
    have h2 : t * (4 * (K + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp h1
    nlinarith
  have htδ : 2 * (t * ‖v‖) < δ := by
    have h1 : t ≤ δ / (4 * ‖v‖) := min_le_right _ _
    have h2 := (le_div_iff₀ (by positivity)).mp h1
    nlinarith
  refine ⟨z + t • v, t * ‖v‖, mul_pos ht hvp, ?_, ?_⟩
  · simp [dist_eq_norm, norm_smul, abs_of_pos ht]
  · intro x hx hne
    by_cases hnear : dist x z < δ
    · have hpos : 0 < ‖x - z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
      have hsupport := hs x hx hnear
      have heq : ‖x - (z + t • v)‖ ^ 2 =
          ‖x - z‖ ^ 2 - 2 * t * inner ℝ v (x - z) + (t * ‖v‖) ^ 2 := by
        rw [show x - (z + t • v) = (x - z) - t • v by abel,
          norm_sub_sq_real]
        simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        rw [real_inner_comm]
        ring
      have hlt : (t * ‖v‖) ^ 2 < ‖x - (z + t • v)‖ ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hsupport (by positivity : 0 ≤ 2 * t)
        have hp := mul_pos (sub_pos.mpr htK) hpos
        nlinarith
      simpa only [dist_eq_norm] using (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mp hlt
    · have hd : δ ≤ dist x z := le_of_not_gt hnear
      have htri := dist_triangle x (z + t • v) z
      have heq : dist (z + t • v) z = t * ‖v‖ := by
        simp [dist_eq_norm, norm_smul, abs_of_pos ht]
      rw [heq] at htri
      linarith

/-- A local C² defining function with nonzero differential provides a strict
exterior tangent sphere. The function need only have the indicated sign locally. -/
theorem exterior_sphere_of_defining_function
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} {z : E} {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f z) (hz : f z = 0) (hd : fderiv ℝ f z ≠ 0)
    (hside : ∀ᶠ x in 𝓝 z, x ∈ S → f x ≤ 0) :
    ∃ (y : E) (r : ℝ), 0 < r ∧ dist z y = r ∧
      ∀ x ∈ S, x ≠ z → r < dist x y := by
  obtain ⟨K, δ, hK, hδ, hbound⟩ := quadratic_remainder hf
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (ball_mem_nhds z hδ) hside)
  let v := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z)
  have hv : v ≠ 0 := by
    intro hv
    apply hd
    have := congrArg (InnerProductSpace.toDual ℝ E) hv
    simpa [v] using this
  apply exterior_sphere_of_quadratic_support hv hK hε
  intro x hx hnear
  have hb := hbound x (hsub hnear).1
  have hsign := (hsub hnear).2 hx
  rw [InnerProductSpace.toDual_symm_apply]
  have habs := neg_abs_le (f x - f z - fderiv ℝ f z (x - z))
  rw [Real.norm_eq_abs, hz] at hb
  rw [hz] at habs
  linarith

/-- Local weak inequalities extend to the closure at continuity points. -/
theorem eventually_closure_nonpos {E : Type*} [TopologicalSpace E]
    {T : Set E} {z : E} {f : E → ℝ}
    (hf : ∀ᶠ x in 𝓝 z, ContinuousAt f x)
    (hs : ∀ᶠ x in 𝓝 z, x ∈ T → f x ≤ 0) :
    ∀ᶠ x in 𝓝 z, x ∈ closure T → f x ≤ 0 := by
  filter_upwards [hf, hs.eventually_nhds] with x hfx hsx hx
  have : NeBot (𝓝[T] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  apply le_of_tendsto (hfx.mono_left (nhdsWithin_le_nhds (s := T)))
  filter_upwards [hsx.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyt
  exact hy hyt

open P102.U4.GraphPieces P102.Sobolev.Geometry in
/-- The actual one-sided C² chart implies a strict exterior tangent sphere.
No sphere condition is part of `BoundaryChart`. -/
theorem chart_exterior_sphere {m : ℕ} {G : Set (Ambient m)}
    (C : BoundaryChart G)
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius)) :
    ∃ (y : Ambient m) (r : ℝ), 0 < r ∧
      dist (C.frame (graph C.graphFunction C.center)) y = r ∧
      ∀ x ∈ closure G, x ≠ C.frame (graph C.graphFunction C.center) → r < dist x y := by
  let π : Ambient m →L[ℝ] P102.U4.Space m := WithLp.fstL 2 ℝ _ _
  let τ : Ambient m →L[ℝ] ℝ := WithLp.sndL 2 ℝ _ _
  let f : Ambient m → ℝ := fun w => C.graphFunction (π w) - τ w
  let z := graph C.graphFunction C.center
  let T : Set (Ambient m) := C.frame ⁻¹' G
  have hπz : π z = C.center := rfl
  have hfz : f z = 0 := sub_self _
  have hγc : ContDiffAt ℝ 2 C.graphFunction C.center :=
    hγ.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self C.radius_pos))
  have hfc : ContDiffAt ℝ 2 f z :=
    (hγc.comp z π.contDiff.contDiffAt).sub τ.contDiff.contDiffAt
  have hfd : fderiv ℝ f z = (fderiv ℝ C.graphFunction C.center).comp π - τ := by
    exact (((hγc.differentiableAt (by norm_num)).hasFDerivAt.comp z π.hasFDerivAt).sub
      τ.hasFDerivAt).fderiv
  have hne : fderiv ℝ f z ≠ 0 := by
    intro heq
    have he := congrArg (fun L : Ambient m →L[ℝ] ℝ => L (WithLp.toLp 2 (0, 1))) heq
    rw [hfd] at he
    norm_num [π, τ] at he
  have hU : ∀ᶠ w in 𝓝 z,
      π w ∈ ball C.center C.radius ∧ f w ∈ Ioo (-C.height) C.height := by
    have h1 : ∀ᶠ w in 𝓝 z, π w ∈ ball C.center C.radius :=
      π.continuous.continuousAt.preimage_mem_nhds
        (isOpen_ball.mem_nhds (by simpa only [hπz] using mem_ball_self C.radius_pos))
    have h2 : ∀ᶠ w in 𝓝 z, f w ∈ Ioo (-C.height) C.height :=
      hfc.continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds (by rw [hfz]; exact ⟨neg_neg_of_pos C.height_pos, C.height_pos⟩))
    exact h1.and h2
  have hside : ∀ᶠ w in 𝓝 z, w ∈ T → f w ≤ 0 := by
    filter_upwards [hU] with w hw hwT
    let q := WithLp.toLp 2 (π w, τ w - C.graphFunction (π w))
    have hq : q ∈ cylinder C.center C.radius C.height := by
      refine ⟨hw.1, ?_⟩
      change -C.height < τ w - C.graphFunction (π w) ∧
        τ w - C.graphFunction (π w) < C.height
      have hw2 : -C.height < C.graphFunction (π w) - τ w ∧
          C.graphFunction (π w) - τ w < C.height := hw.2
      constructor <;> linarith [hw2.1, hw2.2]
    have hshear : shear C.graphFunction q = w := by
      apply (WithLp.ofLp_injective 2)
      apply Prod.ext
      · rfl
      · change C.graphFunction (π w) + (τ w - C.graphFunction (π w)) = τ w
        ring
    have hwchart : C.frame w ∈ chartImage C.frame C.graphFunction
        C.center C.radius C.height :=
      ⟨w, ⟨q, hq, hshear⟩, rfl⟩
    have hin : C.frame w ∈ C.frame '' (shear C.graphFunction ''
        upperCylinder C.center C.radius C.height) := by
      rw [← C.side]
      exact ⟨hwT, hwchart⟩
    rcases hin with ⟨w', ⟨q', hq', rfl⟩, heq⟩
    have heqw : shear C.graphFunction q' = w := C.frame.injective heq
    have hheight := congrArg τ heqw
    have hhorizontal := congrArg π heqw
    change C.graphFunction q'.ofLp.1 + q'.ofLp.2 = τ w at hheight
    change q'.ofLp.1 = π w at hhorizontal
    change C.graphFunction (π w) - τ w ≤ 0
    rw [← hhorizontal] at *
    linarith [hq'.2.1]
  have hclosure := eventually_closure_nonpos
    ((hfc.eventually (by norm_num)).mono fun _ h => h.continuousAt) hside
  obtain ⟨y, r, hr, hzy, hsep⟩ :=
    exterior_sphere_of_defining_function hfc hfz hne hclosure
  refine ⟨C.frame y, r, hr, ?_, fun x hx hneq => ?_⟩
  · simpa only [AffineIsometryEquiv.dist_map] using hzy
  · have hxT : C.frame.symm x ∈ closure T := by
      change C.frame.symm x ∈ closure (C.frame.toHomeomorph ⁻¹' G)
      rw [← C.frame.toHomeomorph.preimage_closure]
      simpa using hx
    have hn : C.frame.symm x ≠ z := by
      intro heq
      apply hneq
      simpa only [AffineIsometryEquiv.apply_symm_apply] using congrArg C.frame heq
    have h := hsep _ hxT hn
    rw [← C.frame.dist_map (C.frame.symm x) y, C.frame.apply_symm_apply] at h
    exact h

/-- The shared C² boundary condition implies the strict exterior sphere
condition in the original Euclidean coordinates, also for unbounded open sets. -/
theorem c2_exterior_sphere {m : ℕ} (Ω : Domain (m + 1))
    (hC : HasCkBoundary Ω 2) {z : Space (m + 1)}
    (hz : z ∈ frontier (Ω : Set (Space (m + 1)))) :
    ∃ (y : Space (m + 1)) (r : ℝ), 0 < r ∧ dist z y = r ∧
      ∀ x ∈ closure (Ω : Set (Space (m + 1))), x ≠ z → r < dist x y := by
  let e := graphFrame m
  let G := P102.Sobolev.Extension.geometricOpen e Ω
  have hze : e.symm z ∈ frontier (G : Set _) := by
    change e.symm z ∈ frontier (e.toHomeomorph ⁻¹' (Ω : Set _))
    rw [← e.toHomeomorph.preimage_frontier]
    change e (e.symm z) ∈ frontier (Ω : Set _)
    simpa only [e.apply_symm_apply] using hz
  obtain ⟨C, hCz, hγ⟩ := hC _ hze
  obtain ⟨y, r, hr, hzy, hsep⟩ := chart_exterior_sphere C hγ
  have hez : e (C.frame (P102.U4.GraphPieces.graph C.graphFunction C.center)) = z := by
    rw [hCz, e.apply_symm_apply]
  refine ⟨e y, r, hr, ?_, fun x hx hne => ?_⟩
  · rw [← hez, e.dist_map]
    exact hzy
  · have hxe : e.symm x ∈ closure (G : Set _) := by
      change e.symm x ∈ closure (e.toHomeomorph ⁻¹' (Ω : Set _))
      rw [← e.toHomeomorph.preimage_closure]
      change e (e.symm x) ∈ closure (Ω : Set _)
      simpa only [e.apply_symm_apply] using hx
    have hneq : e.symm x ≠ C.frame (P102.U4.GraphPieces.graph C.graphFunction C.center) := by
      intro heq
      apply hne
      simpa only [e.apply_symm_apply, hez] using congrArg e heq
    have h := hsep _ hxe hneq
    rw [← e.dist_map (e.symm x) y, e.apply_symm_apply] at h
    exact h

/-- The derivative of the increasing radial harmonic profile, in squared
radius coordinates. Using its integral treats the logarithmic case uniformly. -/
def radialWeight (n : ℕ) (s : ℝ) : ℝ := s ^ (-(n : ℝ) / 2)

def radialPrimitive (n : ℕ) (s : ℝ) : ℝ := ∫ t in (1 : ℝ)..s, radialWeight n t

theorem radialWeight_contDiffAt (n : ℕ) {s : ℝ} (hs : 0 < s)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k (radialWeight n) s :=
  Real.contDiffAt_rpow_const_of_ne hs.ne'

theorem radialWeight_intervalIntegrable (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (radialWeight n) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro s hs
  exact (radialWeight_contDiffAt n ((lt_min ha hb).trans_le hs.1) 0).continuousAt.continuousWithinAt

theorem radialPrimitive_hasDerivAt (n : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (radialPrimitive n) (radialWeight n s) s := by
  have hc : ContinuousOn (radialWeight n) (Ioi (0 : ℝ)) :=
    fun t ht => (radialWeight_contDiffAt n ht 0).continuousAt.continuousWithinAt
  exact intervalIntegral.integral_hasDerivAt_right
    (radialWeight_intervalIntegrable n zero_lt_one hs)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hc s hs)
    (radialWeight_contDiffAt n hs 0).continuousAt

theorem radialPrimitive_contDiffOn (n : ℕ) :
    ContDiffOn ℝ 2 (radialPrimitive n) (Ioi (0 : ℝ)) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun s hs => (radialPrimitive_hasDerivAt n hs).differentiableAt.differentiableWithinAt,
    by norm_num, ?_⟩
  apply (show ContDiffOn ℝ 1 (radialWeight n) (Ioi (0 : ℝ)) from
    fun s hs => (radialWeight_contDiffAt n hs 1).contDiffWithinAt).congr
  intro s hs
  exact (radialPrimitive_hasDerivAt n hs).deriv

theorem radialPrimitive_strictMonoOn (n : ℕ) :
    StrictMonoOn (radialPrimitive n) (Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  rw [← sub_pos]
  change 0 < (∫ t in (1 : ℝ)..b, radialWeight n t) -
    ∫ t in (1 : ℝ)..a, radialWeight n t
  rw [intervalIntegral.integral_interval_sub_left
    (radialWeight_intervalIntegrable n zero_lt_one hb)
    (radialWeight_intervalIntegrable n zero_lt_one ha)]
  apply intervalIntegral.integral_pos hab
  · exact fun s hs =>
      (radialWeight_contDiffAt n (ha.trans_le hs.1) 0).continuousAt.continuousWithinAt
  · exact fun s hs => (Real.rpow_pos_of_pos (ha.trans hs.1) _).le
  · exact ⟨a, ⟨le_rfl, hab.le⟩, Real.rpow_pos_of_pos ha _⟩

/-- First directional derivatives of a function of squared distance. -/
theorem radial_fderiv_apply {n : ℕ} {ψ ψ' : ℝ → ℝ}
    (hψ : ∀ s, 0 < s → HasDerivAt ψ (ψ' s) s)
    (y x v : Space n) (hx : x ≠ y) :
    fderiv ℝ (fun w => ψ (‖w - y‖ ^ 2)) x v =
      2 * ψ' (‖x - y‖ ^ 2) * inner ℝ (x - y) v := by
  have hq := ((hasFDerivAt_id x).sub_const y).norm_sq
  have hd := (hψ _ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)))).comp_hasFDerivAt x hq
  have hdf := hd.fderiv
  dsimp only [Function.comp_def, id_eq] at hdf
  rw [hdf]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- Second directional derivatives, before summing over the orthonormal basis. -/
theorem radial_second_direction {n : ℕ} {ψ ψ' ψ'' : ℝ → ℝ}
    (hψ : ∀ s, 0 < s → HasDerivAt ψ (ψ' s) s)
    (hψ' : ∀ s, 0 < s → HasDerivAt ψ' (ψ'' s) s)
    (y x v : Space n) (hx : x ≠ y) :
    fderiv ℝ (fun w => fderiv ℝ (fun a => ψ (‖a - y‖ ^ 2)) w v) x v =
      4 * ψ'' (‖x - y‖ ^ 2) * (inner ℝ (x - y) v) ^ 2 +
      2 * ψ' (‖x - y‖ ^ 2) * ‖v‖ ^ 2 := by
  have heq : (fun w => fderiv ℝ (fun a => ψ (‖a - y‖ ^ 2)) w v) =ᶠ[𝓝 x]
      (fun w => 2 * ψ' (‖w - y‖ ^ 2) * inner ℝ (w - y) v) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with w hw
    exact radial_fderiv_apply hψ y w v hw
  rw [heq.fderiv_eq]
  have hp := (hψ' _ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)))).comp_hasFDerivAt x
    (((hasFDerivAt_id x).sub_const y).norm_sq)
  have hi := ((hasFDerivAt_id x).sub_const y).inner ℝ (hasFDerivAt_const v x)
  have hdf := ((hp.const_mul 2).mul hi).fderiv
  dsimp only [Function.comp_def, id_eq, Pi.mul_apply] at hdf
  change fderiv ℝ (fun w => 2 * ψ' (‖w - y‖ ^ 2) * inner ℝ (w - y) v) x = _ at hdf
  rw [hdf]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, fderivInnerCLM_apply]
  simp [inner_self_eq_norm_sq_to_K]
  ring

/-- The coordinate Laplacian of a radial composition, calculated from actual
first and second derivatives of its one-variable profile. -/
theorem radial_laplacian {n : ℕ} {ψ ψ' ψ'' : ℝ → ℝ}
    (hψ : ∀ s, 0 < s → HasDerivAt ψ (ψ' s) s)
    (hψ' : ∀ s, 0 < s → HasDerivAt ψ' (ψ'' s) s)
    (y x : Space n) (hx : x ≠ y) :
    laplacian (fun w => ψ (‖w - y‖ ^ 2)) x =
      4 * ψ'' (‖x - y‖ ^ 2) * ‖x - y‖ ^ 2 +
      2 * (n : ℝ) * ψ' (‖x - y‖ ^ 2) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hcoord (i : Fin n) :
      multiPartial (fun w => ψ (‖w - y‖ ^ 2)) ({i, i} : MultiIndex n) x =
      4 * ψ'' (‖x - y‖ ^ 2) * (inner ℝ (x - y) (e i)) ^ 2 +
      2 * ψ' (‖x - y‖ ^ 2) := by
    have hs : ({i, i} : Multiset (Fin n)).sort (· ≤ ·) = [i, i] := by
      rw [Multiset.insert_eq_cons, Multiset.sort_cons i {i} (· ≤ ·) (by simp),
        Multiset.sort_singleton]
    simp only [multiPartial, P102.U4.multiPartial, hs, P102.U4.partialWord]
    rw [radial_second_direction hψ hψ' y x _ hx]
    simp only [P102.U4.coordinateVector, e, (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one,
      one_pow, mul_one]
  change (∑ i : Fin n, multiPartial _ ({i, i} : MultiIndex n) x) = _
  simp_rw [hcoord]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e.sum_sq_inner_left]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The integrated radial profile is harmonic away from its center. -/
theorem radialPrimitive_laplacian {n : ℕ} (y x : Space n) (hx : x ≠ y) :
    laplacian (fun w => radialPrimitive n (‖w - y‖ ^ 2)) x = 0 := by
  let p : ℝ := -(n : ℝ) / 2
  have hq : 0 < ‖x - y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx))
  rw [radial_laplacian (fun s hs => radialPrimitive_hasDerivAt n hs)
    (ψ'' := fun s => p * s ^ (p - 1))
    (fun s hs => Real.hasDerivAt_rpow_const (Or.inl hs.ne')) y x hx]
  change 4 * (p * (‖x - y‖ ^ 2) ^ (p - 1)) * ‖x - y‖ ^ 2 +
    2 * (n : ℝ) * (‖x - y‖ ^ 2) ^ p = 0
  have he : (‖x - y‖ ^ 2) ^ (p - 1) * ‖x - y‖ ^ 2 = (‖x - y‖ ^ 2) ^ p := by
    rw [Real.rpow_sub_one hq.ne', div_mul_cancel₀ _ hq.ne']
  calc
    _ = 4 * p * ((‖x - y‖ ^ 2) ^ (p - 1) * ‖x - y‖ ^ 2) +
        2 * (n : ℝ) * (‖x - y‖ ^ 2) ^ p := by ring
    _ = 0 := by rw [he]; dsimp [p]; ring

/-- A strict exterior sphere gives a positive harmonic barrier. The integral
profile is an increasing positive multiple of the logarithmic or Newtonian
profile in the source, after subtracting its value at the contact radius. -/
theorem harmonic_barrier_of_exterior_sphere {n : ℕ} (Ω : Domain n)
    (z y : Space n) (r : ℝ) (hr : 0 < r) (hzy : dist z y = r)
    (hsep : ∀ x ∈ closure (Ω : Set (Space n)), x ≠ z → r < dist x y) :
    HasHarmonicBarrierAt Ω z := by
  have hdist : ∀ x ∈ closure (Ω : Set (Space n)), r ≤ dist x y := by
    intro x hx
    by_cases h : x = z
    · simpa only [h, hzy] using (le_refl r)
    · exact (hsep x hx h).le
  have hne : ∀ x ∈ closure (Ω : Set (Space n)), x ≠ y := by
    intro x hx heq
    have h := hdist x hx
    rw [heq, dist_self] at h
    linarith
  have hq : ∀ x ∈ closure (Ω : Set (Space n)), 0 < ‖x - y‖ ^ 2 :=
    fun x hx => sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne x hx)))
  have hc : ∀ x ∈ closure (Ω : Set (Space n)),
      ContDiffAt ℝ 2 (fun w => radialPrimitive n (‖w - y‖ ^ 2)) x := by
    intro x hx
    exact ((radialPrimitive_contDiffOn n).contDiffAt (Ioi_mem_nhds (hq x hx))).comp x
      ((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ)
  have hh : P201Specs.MeanValues.IsHarmonic Ω
      (fun w => radialPrimitive n (‖w - y‖ ^ 2)) :=
    ⟨fun x hx => (hc x (subset_closure hx)).contDiffWithinAt,
      fun x hx => radialPrimitive_laplacian y x (hne x (subset_closure hx))⟩
  refine ⟨fun w => radialPrimitive n (‖w - y‖ ^ 2) - radialPrimitive n (r ^ 2), ?_, ?_, ?_, ?_⟩
  · exact (P201.MeanValues.harmonic_bridge Ω _).mpr
      (((P201.MeanValues.harmonic_bridge Ω _).mp hh).sub
        (InnerProductSpace.harmonicOnNhd_const _))
  · have hc' : ContinuousOn (fun w => radialPrimitive n (‖w - y‖ ^ 2))
        (closure (Ω : Set (Space n))) :=
      fun x hx => (hc x hx).continuousAt.continuousWithinAt
    exact hc'.sub continuousOn_const
  · change radialPrimitive n (‖z - y‖ ^ 2) - radialPrimitive n (r ^ 2) = 0
    rw [← dist_eq_norm, hzy, sub_self]
  · intro x hx hxz
    apply sub_pos.mpr
    apply radialPrimitive_strictMonoOn n (sq_pos_of_pos hr) (hq x hx)
    have h := (sq_lt_sq₀ hr.le dist_nonneg).mpr (hsep x hx hxz)
    simpa only [dist_eq_norm] using h

/-- Barriers at every boundary point under exactly the shared C² assumptions. -/
theorem c2_harmonic_barriers : P201Specs.HarmonicBarriers.C2HarmonicBarriersStatement := by
  intro m _ Ω _ hC z hz
  obtain ⟨y, r, hr, hzy, hsep⟩ := c2_exterior_sphere Ω hC hz
  exact harmonic_barrier_of_exterior_sphere Ω z y r hr hzy hsep

end P201.HarmonicBarriers
