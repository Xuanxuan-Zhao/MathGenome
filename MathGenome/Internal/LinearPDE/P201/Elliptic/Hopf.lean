import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.Hopf
import MathGenome.Internal.LinearPDE.P201.Elliptic.MaximumComparison

noncomputable section
open Set TopologicalSpace Metric Filter
open scoped ContDiff RealInnerProductSpace Topology
namespace P201.Elliptic
open P201Specs.Elliptic

/-- Strict comparison on a ball whose sphere may meet the ambient boundary.
Only the open ball has to lie in the domain. -/
theorem strictMaximum_boundaryBall_nonpos {n : ℕ}
    {D : P201Specs.Domain n}
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c f : P201Specs.Space n → ℝ}
    (hcoeff : EllipticCoefficients D a b c)
    (hc : ∀ x ∈ (D : Set _), c x ≤ 0)
    (hf : ContDiffOn ℝ 2 f (D : Set _))
    {y : P201Specs.Space n} {R r : ℝ}
    (hball : ball y R ⊆ (D : Set _))
    (hcont : ContinuousOn f (closedBall y R))
    (hinner : ∀ x ∈ closedBall y r, f x ≤ 0)
    (houter : ∀ x ∈ sphere y R, f x ≤ 0)
    (hLf : ∀ x ∈ ball y R, r < dist x y →
      0 < nondivergenceOperator a b c f x) :
    ∀ x ∈ closedBall y R, f x ≤ 0 := by
  intro x hx
  by_contra hn
  have hxpos : 0 < f x := lt_of_not_ge hn
  obtain ⟨z, hz, hzmax⟩ := (isCompact_closedBall y R).exists_isMaxOn ⟨x, hx⟩ hcont
  have hzpos : 0 < f z := hxpos.trans_le (hzmax hx)
  have hzoff : dist z y ≠ R := by
    intro hdist
    exact (houter z (mem_sphere.mpr hdist)).not_gt hzpos
  have hzball : z ∈ ball y R :=
    mem_ball.mpr (lt_of_le_of_ne (mem_closedBall.mp hz) hzoff)
  have hzinner : r < dist z y := by
    by_contra h
    exact (hinner z (mem_closedBall.mpr (le_of_not_gt h))).not_gt hzpos
  have hlocal : IsLocalMax f z :=
    hzmax.isLocalMax (Filter.mem_of_superset (isOpen_ball.mem_nhds hzball)
      ball_subset_closedBall)
  exact (nondivergenceOperator_nonpos_at_positive_local_max hcoeff hc hf
    (hball hzball) hlocal hzpos.le).not_gt (hLf z hzball hzinner)


/-- The barrier estimate with explicit bounds on the OPEN ball. -/
theorem exists_gaussianBarrier_strict_of_bound {n : ℕ} {Ω : P201Specs.Domain n}
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c : P201Specs.Space n → ℝ}
    (hcoeff : EllipticCoefficients Ω a b c)
    {y : P201Specs.Space n} {R : ℝ} (hR : 0 < R)
    (hball : ball y R ⊆ (Ω : Set (P201Specs.Space n)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ ball y R,
      (∀ i j, |a x i j| ≤ C) ∧ (∀ i, |b x i| ≤ C) ∧ |c x| ≤ C) :
    ∃ k : ℝ, 0 < k ∧ ∀ x : P201Specs.Space n,
      R/2 < dist x y → dist x y < R →
        0 < nondivergenceOperator a b c (gaussianBarrier y R k) x := by
  obtain ⟨ell, hell, hellbound⟩ := hcoeff.2.2.2.2
  have hA : 0 < 4*ell*(R/2)^2 := by positivity
  obtain ⟨k, hk, hparam⟩ := exists_positive_quadratic_parameter
    (B := 2*(n:ℝ)*C + 2*(n:ℝ)*C*R) hA hC
  refine ⟨k, hk, ?_⟩
  intro x hxinner hxouter
  have hxball : x ∈ ball y R := mem_ball.mpr hxouter
  have hxΩ := hball hxball
  obtain ⟨ha, hb, hc⟩ := hbound x hxball
  have hxnorm : ‖x-y‖ < R := by simpa [dist_eq_norm] using hxouter
  have hxinorm : R/2 < ‖x-y‖ := by simpa [dist_eq_norm] using hxinner
  have htrace : (∑ i, a x i i) ≤ (n:ℝ)*C := by
    calc
      (∑ i, a x i i) ≤ ∑ _i : Fin n, C := by
        apply Finset.sum_le_sum
        intro i _
        exact (le_abs_self _).trans (ha i i)
      _ = (n:ℝ)*C := by simp
  have hdrift : (∑ i, b x i * (x i-y i)) ≤ (n:ℝ)*C*R := by
    calc
      (∑ i, b x i * (x i-y i)) ≤ ∑ _i : Fin n, C*R := by
        apply Finset.sum_le_sum
        intro i _
        have hcoord : |x i-y i| ≤ R := by
          calc
            |x i-y i| = ‖(x-y) i‖ := by simp
            _ ≤ ‖x-y‖ := PiLp.norm_apply_le _ _
            _ ≤ R := hxnorm.le
        calc
          b x i * (x i-y i) ≤ |b x i * (x i-y i)| := le_abs_self _
          _ = |b x i| * |x i-y i| := abs_mul _ _
          _ ≤ C*R := mul_le_mul (hb i) hcoord (abs_nonneg _) hC
      _ = (n:ℝ)*C*R := by simp [mul_assoc]
  have hQ : ell*(R/2)^2 ≤ ∑ i, ∑ j, a x i j * (x i-y i) * (x j-y j) := by
    have hsq : (R/2)^2 ≤ ‖x-y‖^2 := by nlinarith [norm_nonneg (x-y)]
    exact (mul_le_mul_of_nonneg_left hsq hell.le).trans
      (by simpa only [PiLp.sub_apply] using hellbound x hxΩ (x-y))
  let E : ℝ := Real.exp (-k*‖x-y‖^2)
  have hE : 0 < E := Real.exp_pos _
  have hψnonneg : 0 ≤ gaussianBarrier y R k x := by
    unfold gaussianBarrier
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    have hsq : ‖x-y‖^2 ≤ R^2 := by nlinarith [norm_nonneg (x-y)]
    exact mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hk.le)
  have hψle : gaussianBarrier y R k x ≤ E := by
    dsimp [gaussianBarrier, E]
    linarith [Real.exp_pos (-k*R^2)]
  have hcψ : -C*E ≤ c x * gaussianBarrier y R k x := by
    have hcLower : -C ≤ c x := (abs_le.mp hc).1
    calc
      -C*E ≤ -C*gaussianBarrier y R k x :=
        mul_le_mul_of_nonpos_left hψle (neg_nonpos.mpr hC)
      _ ≤ c x*gaussianBarrier y R k x :=
        mul_le_mul_of_nonneg_right hcLower hψnonneg
  have hmain : 4*ell*(R/2)^2*k^2 - (2*(n:ℝ)*C+2*(n:ℝ)*C*R)*k-C ≤
      4*k^2*(∑ i, ∑ j, a x i j*(x i-y i)*(x j-y j)) -
        2*k*(∑ i, a x i i)-2*k*(∑ i, b x i*(x i-y i))-C := by
    have hq := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 4*k^2 by positivity)
    have ht := mul_le_mul_of_nonneg_left htrace (show 0 ≤ 2*k by positivity)
    have hd := mul_le_mul_of_nonneg_left hdrift (show 0 ≤ 2*k by positivity)
    nlinarith
  rw [gaussianBarrier_operator_expansion]
  change 0 < E*(4*k^2*(∑ i, ∑ j, a x i j*(x i-y i)*(x j-y j))-
      2*k*(∑ i, a x i i)-2*k*(∑ i, b x i*(x i-y i))) +
    c x*gaussianBarrier y R k x
  calc
    0 < E*(4*ell*(R/2)^2*k^2-(2*(n:ℝ)*C+2*(n:ℝ)*C*R)*k-C) := mul_pos hE hparam
    _ ≤ E*(4*k^2*(∑ i, ∑ j, a x i j*(x i-y i)*(x j-y j))-
      2*k*(∑ i, a x i i)-2*k*(∑ i, b x i*(x i-y i))-C) :=
        mul_le_mul_of_nonneg_left hmain hE.le
    _ ≤ E*(4*k^2*(∑ i, ∑ j, a x i j*(x i-y i)*(x j-y j))-
      2*k*(∑ i, a x i i)-2*k*(∑ i, b x i*(x i-y i))) +
        c x*gaussianBarrier y R k x := by nlinarith [hcψ]



/-- A boundary supersolution dominates a positive Gaussian barrier. No
boundary differentiability or coefficient values on the sphere are used. -/
theorem boundaryBall_gaussian_comparison {n : ℕ}
    {D : P201Specs.Domain n}
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c w : P201Specs.Space n → ℝ}
    (hcoeff : EllipticCoefficients D a b c)
    (hc : ∀ x ∈ (D : Set _), c x ≤ 0)
    (hw : ContDiffOn ℝ 2 w (D : Set _))
    (hLw : ∀ x ∈ (D : Set _), nondivergenceOperator a b c w x ≤ 0)
    {y : P201Specs.Space n} {R : ℝ} (hR : 0 < R)
    (hball : ball y R ⊆ (D : Set _))
    (hwcont : ContinuousOn w (closedBall y R))
    (hpos : ∀ x ∈ ball y R, 0 < w x)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ ball y R,
      (∀ i j, |a x i j| ≤ C) ∧ (∀ i, |b x i| ≤ C) ∧ |c x| ≤ C) :
    ∃ k ε : ℝ, 0 < k ∧ 0 < ε ∧
      ∀ x ∈ closedBall y R, ε * gaussianBarrier y R k x ≤ w x := by
  obtain ⟨k, hk, hLψ⟩ := exists_gaussianBarrier_strict_of_bound hcoeff hR hball hC hbound
  let ψ := gaussianBarrier y R k
  have hψ : ContDiffOn ℝ 2 ψ (D : Set _) :=
    (gaussianBarrier_contDiff y R k).contDiffOn.of_le (by simp)
  have hinner : closedBall y (R/2) ⊆ ball y R := by
    intro x hx
    exact mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by linarith))
  obtain ⟨ε, hε, hεcomp⟩ := exists_positive_comparison_factor
    (ψ := ψ) (isCompact_closedBall y (R/2))
    ⟨y, mem_closedBall_self (by linarith)⟩
    (hwcont.mono (closedBall_subset_closedBall (by linarith)))
    (fun x hx => hpos x (hinner hx))
    (fun x _hx => gaussianBarrier_le_one y x R k hk)
  have hwclosed : ∀ x ∈ closedBall y R, 0 ≤ w x := by
    have hwcl : ContinuousOn w (closure (ball y R)) := by
      simpa only [closure_ball y hR.ne'] using hwcont
    intro x hx
    apply le_on_closure (fun x hx => (hpos x hx).le) continuousOn_const hwcl
    simpa only [closure_ball y hR.ne'] using hx
  have hf : ContDiffOn ℝ 2 (fun x => ε * ψ x - w x) (D : Set _) :=
    (contDiffOn_const.mul hψ).sub hw
  have hfcont : ContinuousOn (fun x => ε * ψ x - w x) (closedBall y R) :=
    (continuousOn_const.mul (gaussianBarrier_contDiff y R k).continuous.continuousOn).sub hwcont
  refine ⟨k, ε, hk, hε, ?_⟩
  have hcompare := strictMaximum_boundaryBall_nonpos hcoeff hc hf hball hfcont
    (r := R/2)
    (fun x hx => sub_nonpos.mpr (hεcomp x hx))
    (fun x hx => by
      have hψx : ψ x = 0 := gaussianBarrier_eq_zero_of_mem_sphere y x R k hx
      simp only [hψx, mul_zero, zero_sub, neg_nonpos]
      exact hwclosed x (sphere_subset_closedBall hx))
    (fun x hx hxinner => by
      rw [nondivergenceOperator_mul_sub a b c hψ hw ε (hball hx)]
      have hp := mul_pos hε (hLψ x hxinner (mem_ball.mp hx))
      linarith [hLw x (hball hx)])
  intro x hx
  exact sub_nonpos.mp (hcompare x hx)


/-- Shrinking a tangent ball toward its contact point preserves its unit
radial direction and puts its entire closure in any prescribed neighborhood. -/
theorem exists_smaller_tangent_ball {n : ℕ} {y z : P201Specs.Space n} {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hz : z ∈ sphere y R) :
    ∃ q : P201Specs.Space n, ∃ r : ℝ, 0 < r ∧
      ball q r ⊆ ball y R ∧ closedBall q r ⊆ ball z δ ∧
      z ∈ sphere q r ∧ outwardRadial q z r = outwardRadial y z R := by
  obtain ⟨t, ht0, ht⟩ := exists_between
    (lt_min zero_lt_one (div_pos hδ (show 0 < 2*R by positivity)))
  have ht1 : t < 1 := ht.trans_le (min_le_left _ _)
  have htd : 2*t*R < δ := by
    have := (lt_div_iff₀ (show 0 < 2*R by positivity)).mp
      (ht.trans_le (min_le_right _ _))
    nlinarith
  let q := z + t • (y-z)
  let r := t*R
  have hzR : ‖z-y‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hz
  have hzq : z-q = t • (z-y) := by dsimp [q]; module
  have hqy : q-y = (1-t) • (z-y) := by dsimp [q]; module
  have hdistzq : dist z q = r := by
    rw [dist_eq_norm, hzq, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hzR]
  have hdistqy : dist q y = (1-t)*R := by
    rw [dist_eq_norm, hqy, norm_smul, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr ht1), hzR]
  refine ⟨q, r, mul_pos ht0 hR, ?_, ?_, mem_sphere.mpr hdistzq, ?_⟩
  · intro x hx
    have hxy := dist_triangle x q y
    have hxq := mem_ball.mp hx
    apply mem_ball.mpr
    dsimp [r] at hxq
    rw [hdistqy] at hxy
    nlinarith
  · intro x hx
    have hxz := dist_triangle x q z
    have hxq := mem_closedBall.mp hx
    have hdistqz : dist q z = r := by simpa [dist_comm] using hdistzq
    rw [hdistqz] at hxz
    exact mem_ball.mpr (lt_of_le_of_lt hxz (by dsimp [r] at hxq ⊢; linarith))
  · unfold outwardRadial
    rw [hzq, smul_smul]
    congr 1
    dsimp [r]
    field_simp


theorem outwardRadial_norm {n : ℕ} {y z : P201Specs.Space n} {R : ℝ}
    (hR : 0 < R) (hz : z ∈ sphere y R) : ‖outwardRadial y z R‖ = 1 := by
  have hzR : ‖z-y‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hz
  simp only [outwardRadial, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), hzR]
  exact inv_mul_cancel₀ hR.ne'

theorem inward_segment_mem_ball {n : ℕ} {y z : P201Specs.Space n} {R h : ℝ}
    (hR : 0 < R) (hz : z ∈ sphere y R) (hh : 0 < h) (hhR : h < R) :
    z-h • outwardRadial y z R ∈ ball y R := by
  have hzR : ‖z-y‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hz
  have he : z-h • outwardRadial y z R-y = (1-h/R) • (z-y) := by
    unfold outwardRadial
    rw [smul_smul, div_eq_mul_inv]
    module
  have hhdiv : h/R < 1 := (div_lt_one hR).mpr hhR
  rw [mem_ball, dist_eq_norm, he, norm_smul, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr hhdiv), hzR]
  have hcancel : h/R*R = h := div_mul_cancel₀ h hR.ne'
  nlinarith

/-- A Gaussian comparison gives a positive lower bound for all sufficiently
small positive difference quotients, hence also for the extended-real liminf. -/
theorem hopfConclusion_of_gaussian_comparison {n : ℕ}
    {u : P201Specs.Space n → ℝ} {y z : P201Specs.Space n} {R k ε : ℝ}
    (hR : 0 < R) (hz : z ∈ sphere y R) (hk : 0 < k) (hε : 0 < ε)
    (hcomp : ∀ x ∈ closedBall y R, ε * gaussianBarrier y R k x ≤ u z-u x) :
    HopfConclusion u z (outwardRadial y z R) := by
  let ν := outwardRadial y z R
  let ψ := gaussianBarrier y R k
  let d := fderiv ℝ ψ z (-ν)
  have hν : -ν = R⁻¹ • (y-z) := by
    dsimp [ν, outwardRadial]
    rw [← smul_neg]
    congr 1
    abel
  have hd : 0 < d := by
    dsimp [d, ψ]
    rw [hν, map_smul, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hR) (gaussianBarrier_inward_derivative_pos y z R k hR hk hz)
  have hcurve : HasDerivAt (fun h : ℝ => z-h • ν) (-ν) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const ν).const_sub z)
  have hψderiv : HasDerivAt (fun h : ℝ => ψ (z-h • ν)) d 0 := by
    have hdiff := (gaussianBarrier_contDiff y R k).differentiable (by simp)
    exact (hdiff z).hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (by simp)
  have hψzero : ψ z = 0 := gaussianBarrier_eq_zero_of_mem_sphere y z R k hz
  have hlim : Tendsto (fun h : ℝ => ε*ψ (z-h • ν)/h) (𝓝[>] 0) (𝓝 (ε*d)) := by
    have ht := hψderiv.tendsto_slope_zero_right.const_mul ε
    simpa [hψzero, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using ht
  have hεδ : 0 < ε*d := mul_pos hε hd
  have hevent : ∀ᶠ h : ℝ in 𝓝[>] 0, ε*d/2 ≤ boundaryQuotient u z ν h := by
    have hlt : ∀ᶠ h : ℝ in 𝓝[>] 0, ε*d/2 < ε*ψ (z-h • ν)/h :=
      hlim.eventually (eventually_gt_nhds (by linarith))
    filter_upwards [hlt, self_mem_nhdsWithin, (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with h hh hh0 hhR
    have hmem := inward_segment_mem_ball hR hz hh0 hhR
    have hle := div_le_div_of_nonneg_right (hcomp _ (ball_subset_closedBall hmem)) hh0.le
    exact hh.le.trans hle
  refine ⟨?_, ?_⟩
  · have hlower : ((ε*d/2 : ℝ) : EReal) ≤ boundaryLowerSlope u z ν := by
      exact le_liminf_of_le (by isBoundedDefault)
        (hevent.mono (fun h hh => EReal.coe_le_coe_iff.mpr hh))
    exact (show (0 : EReal) < ((ε*d/2 : ℝ) : EReal) by
      exact_mod_cast (show (0 : ℝ) < ε*d/2 by positivity)).trans_le hlower
  · intro v hv
    have hle : ε*d/2 ≤ v := ge_of_tendsto hv hevent
    exact (show (0 : ℝ) < ε*d/2 by positivity).trans_le hle


/-- The local Hopf proof, with precisely the two allowed zero-order cases. -/
theorem hopf_of_sign {n : ℕ} {Ω : P201Specs.Domain n}
    {a : P201Specs.Space n → Matrix (Fin n) (Fin n) ℝ}
    {b : P201Specs.Space n → P201Specs.Space n} {c u : P201Specs.Space n → ℝ}
    {y z : P201Specs.Space n} {R : ℝ}
    (H : HopfHypotheses Ω a b c u y z R)
    (hsign : 0 ≤ u z ∨ ∀ x ∈ (Ω : Set _), c x = 0) :
    HopfConclusion u z (outwardRadial y z R) := by
  obtain ⟨ha, hb, hc, δ, C, ell, hδ, hC, hell, hlocal⟩ := H.coefficients
  obtain ⟨q, r, hr, hsmall, hcap, hz, hν⟩ :=
    exists_smaller_tangent_ball H.radius_pos hδ H.contact_sphere
  let D : P201Specs.Domain n := ⟨ball q r, isOpen_ball⟩
  have hDΩ : (D : Set (P201Specs.Space n)) ⊆ (Ω : Set (P201Specs.Space n)) :=
    hsmall.trans H.ball_subset
  have hDlocal : (D : Set _) ⊆ ball y R ∩ ball z δ :=
    fun x hx => ⟨hsmall hx, hcap (ball_subset_closedBall hx)⟩
  have hcoeff : EllipticCoefficients D a b c := by
    refine ⟨ha.mono hDΩ, hb.mono hDΩ, hc.mono hDΩ, ?_, ell, hell, ?_⟩
    · intro x hx
      exact (hlocal x (hDlocal hx)).1
    · intro x hx
      exact (hlocal x (hDlocal hx)).2.1
  have hcD : ∀ x ∈ (D : Set _), c x ≤ 0 := fun x hx => H.nonpositive x (hDΩ hx)
  have hw : ContDiffOn ℝ 2 (fun x => u z-u x) (D : Set _) :=
    contDiffOn_const.sub (H.smooth.mono hDΩ)
  have hLw : ∀ x ∈ (D : Set _),
      nondivergenceOperator a b c (fun x => u z-u x) x ≤ 0 := by
    apply fun x hx => maximum_defect_supersolution Ω a b c u (u z) H.subsolution
      (hsign.elim (fun h => Or.inl ⟨h, H.nonpositive⟩) Or.inr) x (hDΩ hx)
  have hclosed : closedBall q r ⊆ closure (Ω : Set _) := by
    rw [← closure_ball q hr.ne']
    exact closure_mono hDΩ
  have hwcont : ContinuousOn (fun x => u z-u x) (closedBall q r) :=
    continuousOn_const.sub (H.continuous.mono hclosed)
  have hpos : ∀ x ∈ ball q r, 0 < u z-u x :=
    fun x hx => sub_pos.mpr (H.strict x (hsmall hx))
  have hbound : ∀ x ∈ ball q r,
      (∀ i j, |a x i j| ≤ C) ∧ (∀ i, |b x i| ≤ C) ∧ |c x| ≤ C :=
    fun x hx => (hlocal x (hDlocal hx)).2.2
  obtain ⟨k, ε, hk, hε, hcomp⟩ := boundaryBall_gaussian_comparison
    hcoeff hcD hw hLw hr (Subset.rfl) hwcont hpos hC hbound
  rw [← hν]
  exact hopfConclusion_of_gaussian_comparison hr hz hk hε hcomp

/-- Hopf's boundary inequality and its directional-derivative consequence,
for a nonnegative boundary maximum and c ≤ 0. -/
theorem hopf : P201Specs.Elliptic.hopfStatement := by
  intro n _hn Ω a b c u y z R H hM
  exact hopf_of_sign H (Or.inl hM)

/-- The zero-order-free Hopf assertion has no sign restriction on u(z). -/
theorem hopfZeroOrderFree : P201Specs.Elliptic.hopfZeroOrderFreeStatement := by
  intro n _hn Ω a b c u y z R H hc
  exact hopf_of_sign H (Or.inr hc)


/-- Every direction strictly into the radial half-space enters the tangent
ball for all sufficiently small positive times. -/
theorem inward_direction_eventually_mem_ball {n : ℕ}
    {y z v : P201Specs.Space n} {R : ℝ} (hR : 0 < R) (hz : z ∈ sphere y R)
    (hv : ⟪outwardRadial y z R, v⟫ < 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, z+t • v ∈ ball y R := by
  have hzR : ‖z-y‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hz
  have hzvec : z-y = R • outwardRadial y z R := by
    simp only [outwardRadial, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hinner : ⟪z-y, v⟫ < 0 := by
    rw [hzvec, real_inner_smul_left]
    exact mul_neg_of_pos_of_neg hR hv
  have hline : HasDerivAt (fun t : ℝ => z+t • v-y) v 0 := by
    simpa using ((((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z).sub_const y)
  have hg : HasDerivAt (fun t : ℝ => ‖z+t • v-y‖^2) (2*⟪z-y,v⟫) 0 := by
    simpa using hline.norm_sq
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (‖z+t • v-y‖^2-R^2)/t < 0 := by
    have ht := hg.tendsto_slope_zero_right.eventually
      (eventually_lt_nhds (mul_neg_of_pos_of_neg (by norm_num : (0:ℝ)<2) hinner))
    simpa [hzR, smul_eq_mul, div_eq_mul_inv, mul_comm] using ht
  filter_upwards [he, self_mem_nhdsWithin] with t ht ht0
  have hs : ‖z+t • v-y‖^2 < R^2 := by
    have := (div_lt_iff₀ ht0).mp ht
    nlinarith
  apply mem_ball.mpr
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (z+t • v-y)]

/-- At a differentiable boundary point an interior tangent ball determines
exactly the outward unit normal, even for merely pointwise differentiability
of a local defining function. -/
theorem tangentBallNormal : P201Specs.Elliptic.tangentBallNormalStatement := by
  intro n _hn Ω y z N R hR hball hz hnormal
  obtain ⟨hN, ρ, hρz, hρ, V, hV, hside⟩ := hnormal
  let ν := outwardRadial y z R
  have hν : ‖ν‖ = 1 := outwardRadial_norm hR hz
  have hnonpos : ∀ v : P201Specs.Space n, ⟪ν,v⟫ < 0 → ⟪N,v⟫ ≤ 0 := by
    intro v hv
    have hmem := inward_direction_eventually_mem_ball hR hz hv
    have hline : HasDerivAt (fun t : ℝ => z+t • v) v 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z)
    have hlinecont : Tendsto (fun t : ℝ => z+t • v) (𝓝[>] 0) (𝓝 z) := by
      simpa using hline.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hρline : HasDerivAt (fun t : ℝ => ρ (z+t • v)) ⟪N,v⟫ 0 := by
      simpa only [Function.comp_def, innerSL_apply_apply] using
        hρ.comp_hasDerivAt_of_eq 0 hline (by simp)
    have ht : Tendsto (fun t : ℝ => ρ (z+t • v)/t) (𝓝[>] 0) (𝓝 ⟪N,v⟫) := by
      simpa [hρz, smul_eq_mul, div_eq_mul_inv, mul_comm] using
        hρline.tendsto_slope_zero_right
    apply le_of_tendsto ht
    filter_upwards [hmem, hlinecont hV, self_mem_nhdsWithin] with t htball htV ht0
    have hρneg := (hside _ htV).mp (hball htball)
    exact div_nonpos_of_nonpos_of_nonneg hρneg.le ht0.le
  by_contra hne
  have hlt : ⟪ν,N⟫ < 1 := (inner_lt_one_iff_real_of_norm_eq_one hν hN).mpr hne
  have hvin : ⟪ν,N-ν⟫ < 0 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hν]
    nlinarith
  have hvout := hnonpos (N-ν) hvin
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hN, ← real_inner_comm N ν] at hvout
  nlinarith

end P201.Elliptic
