import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.QuantitativeBloch
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.UnivalentHolomorphicInverse
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
Quantitative Bloch theorem, paper.tex:4132–4162.

The weighted maximum on the half-radius closed disk gives a disk on which
|f'| is bounded by twice its central value. Schwarz's lemma makes f'/A-1
small on a smaller disk. A mean-value estimate gives a linear approximation
with error 1/2; the quantitative inverse-function theorem supplies injectivity
and image coverage on still smaller closed disks. These closed disks remain
inside the open domain. The resulting radius is at least M/32 ≥ 1/64.
Affine normalization gives the general derivative-scaled theorem. The inverse
is the restriction of the previously proved holomorphic inverse on the image
of the univalence disk.
-/

noncomputable section
open Set Metric
open scoped Topology

namespace D12Complex.QuantitativeBloch

lemma exists_deriv_control (f : ℂ → ℂ) (hf : HolomorphicOn (ball 0 1) f)
    (hder : deriv f 0 = 1) :
    ∃ (b : ℂ) (δ : ℝ), 0 < δ ∧ ball b δ ⊆ ball 0 1 ∧ deriv f b ≠ 0 ∧
      (1 : ℝ)/64 ≤ ‖deriv f b‖ * δ / 16 ∧
      ∀ z ∈ ball b δ, ‖deriv f z‖ ≤ 2 * ‖deriv f b‖ := by
  have hd : DifferentiableOn ℂ f (ball 0 1) :=
    fun z hz => (hf.2 z hz).differentiableWithinAt
  have hclosed : closedBall (0 : ℂ) (1/2) ⊆ ball 0 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball_zero_iff]
    linarith
  let m : ℂ → ℝ := fun z => ((1/2 : ℝ) - ‖z‖) * ‖deriv f z‖
  have hm : ContinuousOn m (closedBall 0 (1/2)) :=
    (continuousOn_const.sub continuous_norm.continuousOn).mul
      (((hd.deriv isOpen_ball).continuousOn.mono hclosed).norm)
  obtain ⟨b, hb, hmax⟩ := (isCompact_closedBall (0 : ℂ) (1/2)).exists_isMaxOn
    (show (closedBall (0 : ℂ) (1/2 : ℝ)).Nonempty from ⟨0, by norm_num⟩) hm
  have hlow : (1/2 : ℝ) ≤ ((1/2 : ℝ) - ‖b‖) * ‖deriv f b‖ := by
    simpa [m, hder] using hmax (show (0 : ℂ) ∈ closedBall 0 (1/2 : ℝ) by norm_num)
  have hble : ‖b‖ ≤ (1/2 : ℝ) := mem_closedBall_zero_iff.mp hb
  have hblt : ‖b‖ < (1/2 : ℝ) := by
    by_contra hn
    have he : ‖b‖ = (1/2 : ℝ) := le_antisymm hble (le_of_not_gt hn)
    rw [he, sub_self, zero_mul] at hlow
    norm_num at hlow
  have hA : deriv f b ≠ 0 := by
    intro he
    rw [he, norm_zero, mul_zero] at hlow
    norm_num at hlow
  let δ : ℝ := ((1/2 : ℝ) - ‖b‖)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hsmall : ∀ z ∈ ball b δ, ‖z‖ < (1/2 : ℝ) := by
    intro z hz
    have hz' : ‖z-b‖ < δ := by simpa [mem_ball, dist_eq_norm] using hz
    have htri : ‖z‖ ≤ ‖z-b‖ + ‖b‖ := norm_le_norm_sub_add z b
    dsimp [δ] at hz'
    linarith
  refine ⟨b, δ, hδ, ?_, hA, ?_, ?_⟩
  · intro z hz
    exact mem_ball_zero_iff.mpr (by linarith [hsmall z hz])
  · dsimp [δ]
    nlinarith [hlow]
  · intro z hz
    have hz' : ‖z-b‖ < δ := by simpa [mem_ball, dist_eq_norm] using hz
    have htri : ‖z‖ ≤ ‖z-b‖ + ‖b‖ := norm_le_norm_sub_add z b
    have hzcl : z ∈ closedBall (0 : ℂ) (1/2) :=
      mem_closedBall_zero_iff.mpr (hsmall z hz).le
    have hmz : ((1/2 : ℝ) - ‖z‖) * ‖deriv f z‖ ≤
        ((1/2 : ℝ) - ‖b‖) * ‖deriv f b‖ := hmax hzcl
    have hden : δ ≤ (1/2 : ℝ) - ‖z‖ := by
      dsimp [δ] at hz' ⊢
      linarith
    have hmul := (mul_le_mul_of_nonneg_right hden (norm_nonneg (deriv f z))).trans hmz
    have he : (1/2 : ℝ) - ‖b‖ = 2*δ := by dsimp [δ]; ring
    rw [he] at hmul
    nlinarith

theorem bloch_schwarz_bound {h : ℂ → ℂ} {b : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hd : DifferentiableOn ℂ h (ball b δ)) (h0 : h b = 0)
    (hb : ∀ z ∈ ball b δ, ‖h z‖ ≤ 3) :
    ∀ z ∈ ball b (δ / 6), ‖h z‖ ≤ 1 / 2 := by
  intro z hz
  have hz' : z ∈ ball b δ := ball_subset_ball (by linarith) hz
  have hm : MapsTo h (ball b δ) (closedBall (h b) 3) := by
    intro w hw
    simpa [mem_closedBall, dist_eq_norm, h0] using hb w hw
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm hz'
  rw [h0, dist_zero_right] at hs
  have hdist : dist z b < δ / 6 := hz
  have hfrac : 0 < 3 / δ := by positivity
  have hmult := mul_lt_mul_of_pos_left hdist hfrac
  have heq : 3 / δ * (δ / 6) = (1 / 2 : ℝ) := by field_simp; ring
  rw [heq] at hmult
  exact hs.trans (le_of_lt hmult)

 theorem bloch_normalized_deriv_bound {f : ℂ → ℂ} {b : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hA : deriv f b ≠ 0)
    (hd : DifferentiableOn ℂ (fun z => deriv f z / deriv f b - 1) (ball b δ))
    (hb : ∀ z ∈ ball b δ, ‖deriv f z‖ ≤ 2 * ‖deriv f b‖) :
    ∀ z ∈ ball b (δ / 6), ‖deriv f z / deriv f b - 1‖ ≤ 1 / 2 := by
  apply bloch_schwarz_bound hδ hd
  · simp [hA]
  · intro z hz
    have hpos : 0 < ‖deriv f b‖ := norm_pos_iff.mpr hA
    calc
      ‖deriv f z / deriv f b - 1‖ ≤ ‖deriv f z / deriv f b‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 := by
        rw [norm_div, norm_one]
        have hdiv : ‖deriv f z‖ / ‖deriv f b‖ ≤ 2 :=
          (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using hb z hz)
        linarith


lemma normalized_univalent_image {g : ℂ → ℂ} {b : ℂ} {s : ℝ} (hs : 0 < s)
    (hg : ∀ z ∈ ball b s, DifferentiableAt ℂ g z)
    (hd : ∀ z ∈ ball b s, ‖deriv g z - 1‖ ≤ (1/2 : ℝ)) :
    InjOn g (ball b s) ∧ ball (g b) (s/2) ⊆ g '' ball b s := by
  have he : ∀ z ∈ ball b s, HasDerivWithinAt (fun z => g z - z)
      (deriv g z - 1) (ball b s) z := by
    intro z hz
    exact ((hg z hz).hasDerivAt.sub (hasDerivAt_id z)).hasDerivWithinAt
  have hap : ApproximatesLinearOn g (ContinuousLinearMap.id ℂ ℂ) (ball b s) (1/2) := by
    intro x hx y hy
    have hh := (convex_ball b s).norm_image_sub_le_of_norm_hasDerivWithin_le he hd hy hx
    have heq : g x - g y - (x-y) = (g x-x) - (g y-y) := by ring
    simpa only [ContinuousLinearMap.id_apply, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat, heq] using hh
  have hi : InjOn g (ball b s) := by
    apply ApproximatesLinearOn.injOn (f' := ContinuousLinearEquiv.refl ℂ ℂ) hap
    exact Or.inr (by norm_num)
  refine ⟨hi, ?_⟩
  intro y hy
  have hy' : dist y (g b) * 2 < s := by
    have := mem_ball.mp hy
    linarith
  obtain ⟨t, ht1, ht2⟩ := exists_between hy'
  have ht : 0 ≤ t := by linarith [dist_nonneg (x := y) (y := g b)]
  have htsub : closedBall b t ⊆ ball b s := by
    intro z hz
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt ht2)
  let invId : (ContinuousLinearMap.id ℂ ℂ).NonlinearRightInverse :=
    { toFun := id
      nnnorm := 1
      bound' := by intro z; simp
      right_inv' := by intro z; rfl }
  have hcover := hap.surjOn_closedBall_of_nonlinearRightInverse invId ht htsub
  have hyt : y ∈ closedBall (g b) (((invId.nnnorm : ℝ)⁻¹ - (1/2 : NNReal)) * t) := by
    change dist y (g b) ≤ ((1 : ℝ)⁻¹ - ((1/2 : NNReal) : ℝ)) * t
    norm_num
    linarith
  obtain ⟨z, hz, hzy⟩ := hcover hyt
  exact ⟨z, htsub hz, hzy⟩

lemma derivative_ratio_univalent_image {f : ℂ → ℂ} {b A : ℂ} {s : ℝ}
    (hs : 0 < s) (hA : A ≠ 0)
    (hf : ∀ z ∈ ball b s, DifferentiableAt ℂ f z)
    (hd : ∀ z ∈ ball b s, ‖deriv f z / A - 1‖ ≤ (1/2 : ℝ)) :
    InjOn f (ball b s) ∧ ball (f b) (‖A‖ * s / 2) ⊆ f '' ball b s := by
  let g : ℂ → ℂ := fun z => f z / A
  have hg : ∀ z ∈ ball b s, DifferentiableAt ℂ g z := by
    intro z hz
    exact (hf z hz).div_const A
  have hgd : ∀ z ∈ ball b s, ‖deriv g z - 1‖ ≤ (1/2 : ℝ) := by
    intro z hz
    change ‖deriv (fun z => f z / A) z - 1‖ ≤ _
    rw [((hf z hz).hasDerivAt.div_const A).deriv]
    exact hd z hz
  obtain ⟨hi, hcover⟩ := normalized_univalent_image hs hg hgd
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    apply hi hx hy
    change f x / A = f y / A
    rw [hxy]
  · intro y hy
    have hnorm : 0 < ‖A‖ := norm_pos_iff.mpr hA
    have hy' : y/A ∈ ball (g b) (s/2) := by
      rw [mem_ball, dist_eq_norm]
      change ‖y/A - f b/A‖ < s/2
      rw [← sub_div, norm_div]
      apply (div_lt_iff₀ hnorm).mpr
      have h := mem_ball.mp hy
      rw [dist_eq_norm] at h
      nlinarith
    obtain ⟨z, hz, hzy⟩ := hcover hy'
    refine ⟨z, hz, ?_⟩
    exact (div_left_inj' hA).mp hzy

lemma derivative_ratio_univalent_cover {f : ℂ → ℂ} {b A : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hA : A ≠ 0)
    (hf : ∀ z ∈ ball b (δ/6), DifferentiableAt ℂ f z)
    (hd : ∀ z ∈ ball b (δ/6), ‖deriv f z / A - 1‖ ≤ (1/2 : ℝ)) :
    InjOn f (ball b (δ/6)) ∧ ball (f b) (‖A‖ * δ / 16) ⊆ f '' ball b (δ/6) := by
  obtain ⟨hi, hc⟩ := derivative_ratio_univalent_image (by linarith : 0 < δ/6) hA hf hd
  refine ⟨hi, Subset.trans (ball_subset_ball ?_) hc⟩
  nlinarith [norm_nonneg A]


/-- The normalized geometric conclusion, before selecting its holomorphic inverse. -/
lemma normalized_univalence (f : ℂ → ℂ) (hf : HolomorphicOn (ball 0 1) f)
    (hder : deriv f 0 = 1) :
    ∃ (b : ℂ) (s : ℝ), 0 < s ∧ ball b s ⊆ ball 0 1 ∧ InjOn f (ball b s) ∧
      ∃ c : ℂ, ball c (1/64) ⊆ f '' ball b s := by
  obtain ⟨b, δ, hδ, hsub, hA, hradius, hbound⟩ := exists_deriv_control f hf hder
  have hd : DifferentiableOn ℂ f (ball 0 1) :=
    fun z hz => (hf.2 z hz).differentiableWithinAt
  have hdd : DifferentiableOn ℂ (fun z => deriv f z / deriv f b - 1) (ball b δ) :=
    (((hd.deriv isOpen_ball).mono hsub).div_const (deriv f b)).sub_const 1
  have hclose := bloch_normalized_deriv_bound hδ hA hdd hbound
  have hsmall : ball b (δ/6) ⊆ ball b δ := ball_subset_ball (by linarith)
  obtain ⟨hi, hc⟩ := derivative_ratio_univalent_cover hδ hA
    (fun z hz => hf.2 z (hsub (hsmall hz))) hclose
  exact ⟨b, δ/6, by linarith, hsmall.trans hsub, hi, f b,
    (ball_subset_ball hradius).trans hc⟩


open D12Complex

lemma affine_mem_ball_iff (a b q z : ℂ) (hq : q ≠ 0) (s : ℝ) :
    a + q * z ∈ ball (a + q * b) (‖q‖ * s) ↔ z ∈ ball b s := by
  simp only [mem_ball, dist_eq_norm]
  have he : a + q * z - (a + q * b) = q * (z-b) := by ring
  rw [he, norm_mul]
  exact mul_lt_mul_iff_right₀ (norm_pos_iff.mpr hq)

lemma affine_inverse (a q z : ℂ) (hq : q ≠ 0) :
    a + q * ((z - a) / q) = z := by field_simp; ring

lemma inv_affine_mem_ball_iff (a b q z : ℂ) (hq : q ≠ 0) (s : ℝ) :
    (z - a) / q ∈ ball b s ↔ z ∈ ball (a + q*b) (‖q‖*s) := by
  rw [← affine_mem_ball_iff a b q ((z-a)/q) hq s, affine_inverse a q z hq]

lemma inverse_on_subball (f : ℂ → ℂ) (b c : ℂ) (s t : ℝ)
    (hs : 0 < s) (hf : HolomorphicOn (ball b s) f)
    (hi : InjOn f (ball b s)) (himage : ball c t ⊆ f '' ball b s) :
    ∃ g : ℂ → ℂ, HolomorphicOn (ball c t) g ∧
      MapsTo g (ball c t) (ball b s) ∧ LeftInvOn g f (ball b s) ∧
      RightInvOn g f (ball c t) := by
  have hd : IsDomain (ball b s) :=
    ⟨nonempty_ball.mpr hs, isOpen_ball, (convex_ball b s).isPreconnected⟩
  obtain ⟨g, hp, _⟩ :=
    UnivalentHolomorphicInverse.injective_holomorphic_inverse (ball b s) f hd hf hi
  exact ⟨g, ⟨isOpen_ball, fun z hz => hp.2.1.2 z (himage hz)⟩,
    fun z hz => hp.2.2.2.1 (himage hz), hp.2.2.2.2.1,
    fun z hz => hp.2.2.2.2.2 (himage hz)⟩

lemma scaled_of_normalized
    (hnormal : ∀ F : ℂ → ℂ, HolomorphicOn (ball 0 1) F → deriv F 0 = 1 →
      ∃ b : ℂ, ∃ s : ℝ, 0 < s ∧ ball b s ⊆ ball 0 1 ∧ InjOn F (ball b s) ∧
        ∃ c : ℂ, ball c (1/64) ⊆ F '' ball b s)
    (f : ℂ → ℂ) (a : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : HolomorphicOn (ball a R) f) (hd : deriv f a ≠ 0) :
    ∃ b : ℂ, ∃ s : ℝ, 0 < s ∧ ball b s ⊆ ball a R ∧ InjOn f (ball b s) ∧
      ∃ c : ℂ, ball c (R * ‖deriv f a‖ / 64) ⊆ f '' ball b s ∧
        ∃ g : ℂ → ℂ, HolomorphicOn (ball c (R * ‖deriv f a‖ / 64)) g ∧
          MapsTo g (ball c (R * ‖deriv f a‖ / 64)) (ball b s) ∧
          LeftInvOn g f (ball b s) ∧
          RightInvOn g f (ball c (R * ‖deriv f a‖ / 64)) := by
  have hRc : (R:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
  have hnR : ‖(R:ℂ)‖ = R := by simp [Complex.norm_real, abs_of_pos hR]
  let Q : ℂ := (R:ℂ) * deriv f a
  have hQ : Q ≠ 0 := mul_ne_zero hRc hd
  let F : ℂ → ℂ := fun z => (f (a + (R:ℂ)*z) - f a)/Q
  have hmap : ∀ z ∈ ball (0:ℂ) 1, a + (R:ℂ)*z ∈ ball a R := by
    intro z hz
    simpa [hnR, abs_of_pos hR] using (affine_mem_ball_iff a 0 R z hRc 1).mpr hz
  have hF : HolomorphicOn (ball 0 1) F := by
    refine ⟨isOpen_ball, fun z hz => ?_⟩
    exact (((hf.2 _ (hmap z hz)).comp z
      (((differentiableAt_id.const_mul (R:ℂ)).const_add a))).sub_const (f a)).div_const Q
  have hder : deriv F 0 = 1 := by
    have hfa := (hf.2 a (mem_ball_self hR)).hasDerivAt
    have hlin : HasDerivAt (fun z : ℂ => a + (R:ℂ)*z) (R:ℂ) 0 := by
      simpa using ((hasDerivAt_id (0:ℂ)).const_mul (R:ℂ)).const_add a
    have hfa' : HasDerivAt f (deriv f a) (a + (R:ℂ)*0) := by simpa using hfa
    have hcomp := ((hfa'.comp 0 hlin).sub_const (f a)).div_const Q
    have he : deriv f a * (R:ℂ) / Q = 1 := by dsimp [Q]; field_simp
    exact hcomp.deriv.trans he
  obtain ⟨b, s, hs, hsub, hi, c, hc⟩ := hnormal F hF hder
  let B : ℂ := a + (R:ℂ)*b
  let S : ℝ := R*s
  have hS : 0 < S := mul_pos hR hs
  have hback : ∀ z ∈ ball B S, (z-a)/(R:ℂ) ∈ ball b s := by
    intro z hz
    apply (inv_affine_mem_ball_iff a b R z hRc s).mpr
    simpa [B, S, hnR, abs_of_pos hR] using hz
  have hsub' : ball B S ⊆ ball a R := by
    intro z hz
    have hm := hmap _ (hsub (hback z hz))
    simpa [affine_inverse a R z hRc] using hm
  have hi' : InjOn f (ball B S) := by
    intro z hz w hw he
    have hh := hi (hback z hz) (hback w hw)
      (show F ((z-a)/(R:ℂ)) = F ((w-a)/(R:ℂ)) by
        dsimp [F]; rw [affine_inverse a R z hRc, affine_inverse a R w hRc, he])
    have hh' := congrArg (fun t : ℂ => a+(R:ℂ)*t) hh
    simpa [affine_inverse a R z hRc, affine_inverse a R w hRc] using hh'
  let C : ℂ := f a + Q*c
  have hnQ : ‖Q‖ = R * ‖deriv f a‖ := by dsimp [Q]; rw [norm_mul, hnR]
  have hc' : ball C (R * ‖deriv f a‖ / 64) ⊆ f '' ball B S := by
    intro w hw
    have hw' : (w-f a)/Q ∈ ball c (1/64) := by
      apply (inv_affine_mem_ball_iff (f a) c Q w hQ (1/64)).mpr
      simpa [C, hnQ, div_eq_mul_inv] using hw
    obtain ⟨z, hz, hzw⟩ := hc hw'
    refine ⟨a + (R:ℂ)*z, ?_, ?_⟩
    · simpa [B, S, hnR, abs_of_pos hR] using (affine_mem_ball_iff a b R z hRc s).mpr hz
    · have he := congrArg (fun t : ℂ => f a+Q*t) hzw
      simpa [F, affine_inverse (f a) Q w hQ, affine_inverse (f a) Q (f (a+(R:ℂ)*z)) hQ] using he
  refine ⟨B, S, hS, hsub', hi', C, hc', ?_⟩
  exact inverse_on_subball f B C S (R * ‖deriv f a‖ / 64) hS
    ⟨isOpen_ball, fun z hz => hf.2 z (hsub' hz)⟩ hi' hc'

/-- Every disk has the stated Bloch disk with the derivative scaling factor. -/
theorem scaled : Specs.D12Complex.Ch23.QuantitativeBloch.scaled_type := by
  intro a R f hR hf hd
  obtain ⟨b, s, hs, hsub, hi, c, hc, g, hg, hmaps, hl, hr⟩ :=
    scaled_of_normalized normalized_univalence f a R hR hf hd
  exact ⟨b, s, c, g, hs, hsub, hi, hc, hg, hmaps, hl, hr⟩

/-- The unit disk conclusion, including its holomorphic inverse. -/
theorem normalized : Specs.D12Complex.Ch23.QuantitativeBloch.normalized_type := by
  intro f hf hd
  have hne : deriv f 0 ≠ 0 := by rw [hd]; exact one_ne_zero
  simpa [hd] using scaled 0 1 f zero_lt_one hf hne

end D12Complex.QuantitativeBloch
