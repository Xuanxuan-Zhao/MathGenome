import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SingularityCoefficients
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.Laurent
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.Singularities
import Mathlib.Tactic.Positivity

noncomputable section
open Set Metric Filter
open scoped Topology NNReal ENNReal

namespace D12Complex.SingularityCoefficients
open Laurent

/-- The real-radius and extended-radius punctured disks are the same set. -/
theorem annulus_ofReal (a : ℂ) (r : ℝ) :
    annulus a 0 (ENNReal.ofReal r) = puncturedDisk a r := by
  ext z
  simp only [annulus, puncturedDisk, mem_ofPred_eq]
  rw [← ENNReal.ofReal_coe_nnreal]
  change (0 < ‖z - a‖ ∧ ENNReal.ofReal ‖z - a‖ < ENNReal.ofReal r) ↔ _
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)]

theorem isolated_of_holomorphic {f : ℂ → ℂ} {a : ℂ} {R : ℝ≥0∞}
    (hR : 0 < R) (hf : HolomorphicOn (annulus a 0 R) f) :
    IsolatedSingularityAt f a := by
  obtain ⟨r, hr, hrR⟩ := exists_admissible_radius (t := 0) le_rfl (by simpa using hR)
  refine ⟨r, hr, ?_⟩
  have hsub : puncturedDisk a r ⊆ annulus a 0 R := by
    intro z hz
    exact ⟨hz.1, (by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr hz.2 |>.trans hrR)⟩
  refine ⟨?_, fun z hz => hf.2 z (hsub hz)⟩
  exact (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).inter
    (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)



/-- A circle small enough to lie in both a prescribed local disk and the
original Laurent annulus. -/
theorem exists_small_radius {R : ℝ≥0∞} {r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ ENNReal.ofReal ρ < R := by
  obtain ⟨s, hs, hsR⟩ := exists_admissible_radius (t := 0) le_rfl (by simpa using hR)
  obtain ⟨ρ, hρ, hρs⟩ := exists_between (lt_min hr hs)
  exact ⟨ρ, hρ, hρs.trans_le (min_le_left _ _),
    (ENNReal.ofReal_le_ofReal (hρs.le.trans (min_le_right _ _))).trans_lt hsR⟩

/-- All negative Cauchy coefficients of a holomorphic disk function vanish,
and its zeroth coefficient is its value at the center. -/
theorem coefficientIntegral_holomorphic {g : ℂ → ℂ} {a : ℂ} {r ρ : ℝ}
    (hg : HolomorphicOn (ball a r) g) (hρ : 0 < ρ) (hρr : ρ < r) :
    coefficientIntegral g a ρ 0 = g a ∧
      ∀ n : ℤ, n < 0 → coefficientIntegral g a ρ n = 0 := by
  have hd : DifferentiableOn ℂ g (closedBall a ρ) := by
    intro z hz
    exact (hg.2 z (mem_ball.mpr ((mem_closedBall.mp hz).trans_lt hρr))).differentiableWithinAt
  constructor
  · have hi := hd.circleIntegral_sub_inv_smul (mem_ball_self hρ)
    have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero
    simp only [coefficientIntegral, zero_add, zpow_one, div_eq_inv_mul]
    simpa only [smul_eq_mul, inv_mul_cancel_left₀ hπ] using congrArg
      (fun v : ℂ => (2 * Real.pi * Complex.I : ℂ)⁻¹ * v) hi
  · intro n hn
    let k : ℕ := (-(n + 1)).toNat
    have hk : -(n + 1) = (k : ℤ) := by dsimp [k]; omega
    have hpoly : DiffContOnCl ℂ (fun z => g z * (z - a) ^ k) (ball a ρ) := by
      apply DifferentiableOn.diffContOnCl
      intro z hz
      have hz' : z ∈ ball a r :=
        mem_ball.mpr ((closure_ball_subset_closedBall hz |> mem_closedBall.mp).trans_lt hρr)
      exact ((hg.2 z hz').mul ((differentiableAt_id.sub_const a).pow k)).differentiableWithinAt
    simp only [coefficientIntegral, div_eq_mul_inv, ← zpow_neg, hk, zpow_natCast]
    rw [hpoly.circleIntegral_eq_zero hρ.le, mul_zero]

/-- The regular part of a Laurent expansion is holomorphic on a full disk
about its center, even though the original function is defined only puncturedly. -/
theorem positivePart_extension {f : ℂ → ℂ} {a : ℂ} {R : ℝ≥0∞} {c : ℤ → ℂ}
    (hR : 0 < R) (hf : HolomorphicOn (annulus a 0 R) f)
    (hc : HasLaurentSeriesOn f a 0 R c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ENNReal.ofReal ρ < R ∧
      HolomorphicOn (ball a ρ) (positivePart c a) := by
  obtain ⟨ρ, hρ, hρR⟩ := exists_admissible_radius (t := 0) le_rfl (by simpa using hR)
  have hconv := convergent_of_hasLaurentSeriesOn hc
  have hcoef (n : ℤ) : c n = coefficientIntegral f a ρ n :=
    coefficientFormula_of_convergent le_rfl hconv hρ hρR n
  have hci : CircleIntegrable f a ρ := (continuousOn_circle hf hρ hρR).circleIntegrable hρ.le
  let F : ℂ → ℂ := fun z => (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    circleIntegral (fun w => (w - z)⁻¹ * f w) a ρ
  have heq : EqOn (positivePart c a) F (ball a ρ) := by
    intro z hz
    have hs := hasSum_positive_coefficientIntegral f a z ρ hci (mem_ball_iff_norm.mp hz)
    simp_rw [← hcoef] at hs
    simpa only [positivePart, positiveTerm, F, div_eq_inv_mul] using hs.tsum_eq
  refine ⟨ρ, hρ, hρR, isOpen_ball, ?_⟩
  intro z hz
  have hzS : z ∉ sphere a |ρ| := by
    rw [abs_of_pos hρ]
    exact fun h => (mem_ball.mp hz).ne (mem_sphere.mp h)
  have hd : DifferentiableAt ℂ F z := by
    exact ((Complex.hasDerivAt_circleIntegral_sub_inv_smul hci hzS).const_mul
      (2 * Real.pi * Complex.I : ℂ)⁻¹).differentiableAt
  exact hd.congr_of_eventuallyEq (heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz))

theorem positivePart_center (c : ℤ → ℂ) (a : ℂ) : positivePart c a a = c 0 := by
  unfold positivePart
  rw [tsum_eq_single 0]
  · simp [positiveTerm]
  · intro n hn
    simp [positiveTerm, zero_pow hn]



/-- Equal values on a positive circle give equal Laurent coefficient integrals. -/
theorem coefficientIntegral_congr {f g : ℂ → ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (h : EqOn f g (sphere a ρ)) (n : ℤ) :
    coefficientIntegral f a ρ n = coefficientIntegral g a ρ n := by
  unfold coefficientIntegral
  congr 1
  apply circleIntegral.integral_congr hρ.le
  intro z hz
  dsimp only
  rw [h hz]

/-- Multiplication by an integer monomial translates the coefficient indices. -/
theorem coefficientIntegral_mul_zpow (f : ℂ → ℂ) (a : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (m n : ℤ) :
    coefficientIntegral (fun z => (z-a)^m * f z) a ρ n =
      coefficientIntegral f a ρ (n-m) := by
  unfold coefficientIntegral
  congr 1
  apply circleIntegral.integral_congr hρ.le
  intro z hz
  have hz0 : z-a ≠ 0 := by
    have := mem_sphere_iff_norm.mp hz
    exact norm_ne_zero_iff.mp (this ▸ ne_of_gt hρ)
  simp only [div_eq_mul_inv, ← zpow_neg]
  calc
    (z-a)^m * f z * (z-a)^(-(n+1)) =
        f z * ((z-a)^m * (z-a)^(-(n+1))) := by ring
    _ = f z * (z-a)^(m + -(n+1)) := by rw [zpow_add₀ hz0]
    _ = _ := by congr 2; omega

/-- If the negative part vanishes, the regular part extends f, with value c₀. -/
theorem extension_of_negative_zero {f : ℂ → ℂ} {a : ℂ} {R : ℝ≥0∞} {c : ℤ → ℂ}
    (hR : 0 < R) (hf : HolomorphicOn (annulus a 0 R) f)
    (hc : HasLaurentSeriesOn f a 0 R c) (hz : ∀ n : ℤ, n < 0 → c n = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ, HolomorphicOn (ball a r) g ∧
      g a = c 0 ∧ ∀ z ∈ puncturedDisk a r, f z = g z := by
  obtain ⟨r, hr, hrR, hg⟩ := positivePart_extension hR hf hc
  refine ⟨r, hr, positivePart c a, hg, positivePart_center c a, ?_⟩
  intro z hzr
  have hzA : z ∈ annulus a 0 R := by
    rw [← annulus_ofReal] at hzr
    exact ⟨hzr.1, hzr.2.trans hrR⟩
  rw [(hc z hzA).2.2]
  have hn : negativePart c a z = 0 := by
    have hterm (n : ℕ) : negativeTerm c a n z = 0 := by
      unfold negativeTerm
      rw [hz _ (by omega), zero_mul]
    simp only [negativePart, hterm, tsum_zero]
  rw [hn, add_zero]

/-- The coefficient c₀ is the value of any local holomorphic extension;
all negative coefficients vanish. -/
theorem coefficients_of_extension {f g : ℂ → ℂ} {a : ℂ} {R : ℝ≥0∞}
    {c : ℤ → ℂ} {r : ℝ} (hR : 0 < R) (hc : HasLaurentSeriesOn f a 0 R c)
    (hr : 0 < r) (hg : HolomorphicOn (ball a r) g)
    (hfg : ∀ z ∈ puncturedDisk a r, f z = g z) :
    c 0 = g a ∧ ∀ n : ℤ, n < 0 → c n = 0 := by
  obtain ⟨ρ, hρ, hρr, hρR⟩ := exists_small_radius hR hr
  have hcoef (n : ℤ) : c n = coefficientIntegral g a ρ n := by
    rw [coefficientFormula_of_convergent le_rfl (convergent_of_hasLaurentSeriesOn hc) hρ hρR n]
    apply coefficientIntegral_congr hρ
    intro z hz
    apply hfg
    exact ⟨(mem_sphere_iff_norm.mp hz).symm ▸ hρ,
      (mem_sphere_iff_norm.mp hz).trans_lt hρr⟩
  simpa only [← hcoef] using coefficientIntegral_holomorphic hg hρ hρr

theorem removable_iff : Specs.D12Complex.Ch07.SingularityCoefficients.removable_iff_type := by
  intro f a R c hR hf hc
  constructor
  · rintro ⟨_, r, hr, g, hg, hfg⟩
    exact (coefficients_of_extension hR hc hr hg hfg).2
  · intro hz
    obtain ⟨r, hr, g, hg, _, hfg⟩ := extension_of_negative_zero hR hf hc hz
    exact ⟨isolated_of_holomorphic hR hf, r, hr, g, hg, hfg⟩



/-- A local pole factorization determines its leading coefficient and all
coefficients below it, without imposing a value on f at the puncture. -/
theorem coefficients_of_pole {f : ℂ → ℂ} {a : ℂ} {R : ℝ≥0∞} {c : ℤ → ℂ}
    {m : ℕ} (hR : 0 < R) (hc : HasLaurentSeriesOn f a 0 R c)
    (hp : PoleOfOrderAt f a m) :
    c (-(m : ℤ)) ≠ 0 ∧ ∀ n : ℤ, n < -(m : ℤ) → c n = 0 := by
  obtain ⟨_, _, r, hr, g, hg, hga, hfg⟩ := hp
  obtain ⟨ρ, hρ, hρr, hρR⟩ := exists_small_radius hR hr
  have hcoef (n : ℤ) : c n = coefficientIntegral g a ρ (n + m) := by
    rw [coefficientFormula_of_convergent le_rfl (convergent_of_hasLaurentSeriesOn hc) hρ hρR n]
    have heq : EqOn (fun z => (z-a)^(m : ℤ) * f z) g (sphere a ρ) := by
      intro z hz
      have hzr : z ∈ puncturedDisk a r :=
        ⟨(mem_sphere_iff_norm.mp hz).symm ▸ hρ,
          (mem_sphere_iff_norm.mp hz).trans_lt hρr⟩
      have hz0 : z-a ≠ 0 := norm_pos_iff.mp hzr.1
      dsimp only
      rw [hfg z hzr, zpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hz0), one_mul]
    have hi := coefficientIntegral_congr hρ heq (n + m)
    rw [coefficientIntegral_mul_zpow f a hρ] at hi
    simpa using hi
  obtain ⟨hg0, hgn⟩ := coefficientIntegral_holomorphic hg hρ hρr
  constructor
  · simpa only [hcoef, neg_add_cancel, hg0] using hga
  · intro n hn
    rw [hcoef]
    exact hgn _ (by omega)

theorem poleOfOrder_iff : Specs.D12Complex.Ch07.SingularityCoefficients.poleOfOrder_iff_type := by
  intro f a R c hR hf hc m hm
  constructor
  · exact coefficients_of_pole hR hc
  · rintro ⟨hlead, hzero⟩
    let F : ℂ → ℂ := fun z => (z-a)^m * f z
    have hF : HolomorphicOn (annulus a 0 R) F :=
      ⟨hf.1, fun z hz => ((differentiableAt_id.sub_const a).pow m).mul (hf.2 z hz)⟩
    obtain ⟨d, hd, hdi, _⟩ := laurent_exists a 0 R F le_rfl (by simpa using hR) hF
    obtain ⟨ρ, hρ, hρR⟩ := exists_admissible_radius (t := 0) le_rfl (by simpa using hR)
    have hshift (n : ℤ) : d n = c (n - m) := by
      rw [hdi ρ hρ hρR n]
      change coefficientIntegral (fun z => (z-a)^(m : ℤ) * f z) a ρ n = _
      rw [coefficientIntegral_mul_zpow f a hρ]
      exact (coefficientFormula_of_convergent le_rfl
        (convergent_of_hasLaurentSeriesOn hc) hρ hρR (n-m)).symm
    have hdz : ∀ n : ℤ, n < 0 → d n = 0 := by
      intro n hn
      rw [hshift]
      exact hzero _ (by omega)
    obtain ⟨r, hr, g, hg, hga, hFg⟩ := extension_of_negative_zero hR hF hd hdz
    refine ⟨hm, isolated_of_holomorphic hR hf, r, hr, g, hg, ?_, ?_⟩
    · simpa only [hga, hshift, zero_sub] using hlead
    · intro z hz
      have hz0 : (z-a)^m ≠ 0 := pow_ne_zero m (norm_pos_iff.mp hz.1)
      rw [← hFg z hz]
      change f z = ((z-a)^m)⁻¹ * ((z-a)^m * f z)
      rw [inv_mul_cancel_left₀ hz0]



/-- Any isolated singularity has an actual Laurent expansion on a whole
punctured disk, so the coefficient criteria apply to the local definitions. -/
theorem laurent_of_isolated {f : ℂ → ℂ} {a : ℂ} (hi : IsolatedSingularityAt f a) :
    ∃ (R : ℝ≥0∞) (c : ℤ → ℂ), 0 < R ∧ HolomorphicOn (annulus a 0 R) f ∧
      HasLaurentSeriesOn f a 0 R c := by
  obtain ⟨r, hr, hf⟩ := hi
  have hR : 0 < ENNReal.ofReal r := ENNReal.ofReal_pos.mpr hr
  have hf' : HolomorphicOn (annulus a 0 (ENNReal.ofReal r)) f := by
    rwa [annulus_ofReal]
  obtain ⟨c, hc, _⟩ := laurent_exists a 0 (ENNReal.ofReal r) f le_rfl
    (by simpa using hR) hf'
  exact ⟨ENNReal.ofReal r, c, hR, hf', hc⟩

theorem pole_order_unique : Specs.D12Complex.Ch07.SingularityCoefficients.pole_order_unique_type := by
  intro f a m k hm hk
  obtain ⟨R, c, hR, _, hc⟩ := laurent_of_isolated hm.2.1
  obtain ⟨hcm, hzm⟩ := coefficients_of_pole hR hc hm
  obtain ⟨hck, hzk⟩ := coefficients_of_pole hR hc hk
  apply le_antisymm
  · by_contra h
    exact hcm (hzk _ (by omega))
  · by_contra h
    exact hck (hzm _ (by omega))

/-- A removable singularity cannot also have a finite exact pole order. -/
theorem not_removable_of_pole {f : ℂ → ℂ} {a : ℂ} (hp : PoleAt f a) :
    ¬RemovableSingularityAt f a := by
  obtain ⟨m, hm⟩ := hp
  obtain ⟨R, c, hR, hf, hc⟩ := laurent_of_isolated hm.2.1
  intro hr
  exact (coefficients_of_pole hR hc hm).1
    ((removable_iff f a R c hR hf hc).mp hr _ (by have := hm.1; omega))

/-- A finite, nonempty negative support has a lowest nonzero coefficient. -/
theorem pole_of_finite_negative_support {f : ℂ → ℂ} {a : ℂ} {R : ℝ≥0∞} {c : ℤ → ℂ}
    (hR : 0 < R) (hf : HolomorphicOn (annulus a 0 R) f)
    (hc : HasLaurentSeriesOn f a 0 R c)
    (hfin : {n : ℤ | n < 0 ∧ c n ≠ 0}.Finite)
    (hne : {n : ℤ | n < 0 ∧ c n ≠ 0}.Nonempty) : PoleAt f a := by
  obtain ⟨n, hn, hmin⟩ := Set.exists_min_image _ (fun n : ℤ => n) hfin hne
  have hn0 : n < 0 := hn.1
  let m : ℕ := (-n).toNat
  have hnm : -(m : ℤ) = n := by dsimp [m]; omega
  have hm : 1 ≤ m := by dsimp [m]; omega
  refine ⟨m, (poleOfOrder_iff f a R c hR hf hc m hm).mpr ?_⟩
  rw [hnm]
  refine ⟨hn.2, fun k hk => ?_⟩
  by_contra hck
  have := hmin k ⟨hk.trans hn.1, hck⟩
  change n ≤ k at this
  omega

theorem essential_iff : Specs.D12Complex.Ch07.SingularityCoefficients.essential_iff_type := by
  intro f a R c hR hf hc
  classical
  constructor
  · intro he
    by_contra h
    have hfin : {n : ℤ | n < 0 ∧ c n ≠ 0}.Finite := Set.not_infinite.mp h
    by_cases hne : {n : ℤ | n < 0 ∧ c n ≠ 0}.Nonempty
    · exact he.2.2 (pole_of_finite_negative_support hR hf hc hfin hne)
    · apply he.2.1
      apply (removable_iff f a R c hR hf hc).mpr
      intro n hn
      by_contra hcn
      exact hne ⟨n, hn, hcn⟩
  · intro hinf
    refine ⟨isolated_of_holomorphic hR hf, ?_, ?_⟩
    · intro hr
      have hz := (removable_iff f a R c hR hf hc).mp hr
      exact hinf.not_finite (Set.finite_empty.subset (by
        intro n hn; exact (hn.2 (hz n hn.1)).elim))
    · rintro ⟨m, hm⟩
      have hz := (coefficients_of_pole hR hc hm).2
      apply hinf.not_finite
      apply (Set.finite_Icc (-(m : ℤ)) (-1)).subset
      intro n hn
      constructor
      · by_contra h
        exact hn.2 (hz n (by omega))
      · exact Int.le_sub_one_of_lt hn.1

theorem singularity_trichotomy :
    Specs.D12Complex.Ch07.SingularityCoefficients.singularity_trichotomy_type := by
  intro f a hi
  classical
  by_cases hr : RemovableSingularityAt f a
  · exact Or.inl ⟨hr, fun hp => not_removable_of_pole hp hr, fun he => he.2.1 hr⟩
  · by_cases hp : PoleAt f a
    · obtain ⟨m, hm⟩ := hp
      exact Or.inr (Or.inl ⟨⟨m, hm, fun k hk => pole_order_unique f a k m hk hm⟩,
        hr, fun he => he.2.2 ⟨m, hm⟩⟩)
    · exact Or.inr (Or.inr ⟨⟨hi, hr, hp⟩, hr, hp⟩)

end D12Complex.SingularityCoefficients
