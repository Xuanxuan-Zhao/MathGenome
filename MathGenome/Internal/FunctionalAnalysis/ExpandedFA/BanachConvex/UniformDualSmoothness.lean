import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.UniformDualSmoothness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.StrictDualSmoothness
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The uniform part of `fa2:p2:duality-smoothness`.
Uniform convexity of the real dual is equivalent to single-valuedness and
uniform norm continuity of the normalized duality map on every bounded set.
The supporting inequalities then give the Fréchet derivative and C¹ regularity.
The preceding strictness, weak-star continuity and inverse conclusions are
provided by the imported accepted `StrictDualSmoothness` module. -/
namespace ExpandedFA.BanachConvex
open Set Filter
open scoped Topology
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A quantitative estimate on a pair of duality elements. Normalize both
functionals by the larger primal norm, and test their sum on that primal
vector. The modulus of convexity then bounds their separation. -/
lemma duality_separation_estimate [UniformConvexSpace (X →L[ℝ] ℝ)]
    {R ε δ : ℝ} (_hR : 0 < R) (hε : 0 < ε) (hδ : 0 < δ)
    (hc : ∀ {f g : X →L[ℝ] ℝ}, ‖f‖ ≤ 1 → ‖g‖ ≤ 1 →
      ε / R ≤ ‖f - g‖ → ‖f + g‖ ≤ 2 - δ)
    {x y : X} {f g : X →L[ℝ] ℝ}
    (hf : f ∈ dualityMap X x) (hg : g ∈ dualityMap X y)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ ‖x‖) (hsep : ε ≤ ‖f - g‖) :
    δ * ε ^ 2 ≤ 12 * R * ‖x - y‖ := by
  have hsep' : ε ≤ 2 * ‖x‖ := by
    calc
      ε ≤ ‖f - g‖ := hsep
      _ ≤ ‖f‖ + ‖g‖ := norm_sub_le _ _
      _ ≤ 2 * ‖x‖ := by rw [hf.1, hg.1]; linarith
  have hxp : 0 < ‖x‖ := by linarith
  have hfn : ‖‖x‖⁻¹ • f‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hxp.le), hf.1,
      inv_mul_cancel₀ hxp.ne']
  have hgn : ‖‖x‖⁻¹ • g‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hxp.le), hg.1]
    exact (inv_mul_le_one₀ hxp).mpr hy
  have hnormsep : ε / R ≤ ‖‖x‖⁻¹ • f - ‖x‖⁻¹ • g‖ := by
    rw [← smul_sub (‖x‖⁻¹) f g, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hxp.le),
      ← div_eq_inv_mul]
    exact (div_le_div_of_nonneg_left hε.le hxp hx).trans
      (div_le_div_of_nonneg_right hsep hxp.le)
  have hs := hc hfn hgn hnormsep
  rw [← smul_add (‖x‖⁻¹) f g, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hxp.le),
    ← div_eq_inv_mul, div_le_iff₀ hxp] at hs
  have heval : ‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖y‖ * ‖x - y‖ ≤ (f + g) x := by
    have hb := g.le_opNorm (x - y)
    rw [Real.norm_eq_abs, hg.1, map_sub] at hb
    have hl := (abs_le.mp hb).1
    simp only [add_apply, hf.2, hg.2] at *
    linarith
  have hu : (f + g) x ≤ (2 - δ) * ‖x‖ ^ 2 := by
    calc
      (f + g) x ≤ |(f + g) x| := le_abs_self _
      _ ≤ ‖f + g‖ * ‖x‖ := (f + g).le_opNorm x
      _ ≤ ((2 - δ) * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hs hxp.le
      _ = (2 - δ) * ‖x‖ ^ 2 := by ring
  have hnorm : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le _ _
  have hsum : ‖x‖ + ‖y‖ ≤ 2 * R := by linarith
  have hsq : ‖x‖ ^ 2 - ‖y‖ ^ 2 ≤ 2 * R * ‖x - y‖ := by
    calc
      ‖x‖ ^ 2 - ‖y‖ ^ 2 = (‖x‖ - ‖y‖) * (‖x‖ + ‖y‖) := by ring
      _ ≤ ‖x - y‖ * (2 * R) :=
        mul_le_mul hnorm hsum (add_nonneg (norm_nonneg _) (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  have hyd : ‖y‖ * ‖x - y‖ ≤ R * ‖x - y‖ :=
    mul_le_mul_of_nonneg_right (hy.trans hx) (norm_nonneg _)
  have hgap : δ * ‖x‖ ^ 2 ≤ 3 * R * ‖x - y‖ := by nlinarith
  have hep : ε ^ 2 ≤ 4 * ‖x‖ ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hep hδ.le
  nlinarith

lemma duality_uniformContinuousOn [UniformConvexSpace (X →L[ℝ] ℝ)]
    (J : X → (X →L[ℝ] ℝ))
    (hJ : ∀ x, Spec.DualityMapValue X x = {J x})
    (s : Set X) (hs : Bornology.IsBounded s) : UniformContinuousOn J s := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : X)).mp hs
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hb : ∀ x ∈ s, ‖x‖ ≤ R := by
    intro x hx
    exact (mem_closedBall_zero_iff.mp (hr hx)).trans (le_max_left _ _)
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := exists_forall_closed_ball_dist_add_le_two_sub
    (X →L[ℝ] ℝ) (div_pos hε hR)
  refine ⟨δ * ε ^ 2 / (12 * R), by positivity, ?_⟩
  intro x hx y hy hxy
  rw [dist_eq_norm] at hxy ⊢
  by_contra hn
  have hsep : ε ≤ ‖J x - J y‖ := le_of_not_gt hn
  have hh : δ * ε ^ 2 ≤ 12 * R * ‖x - y‖ := by
    rcases le_total ‖y‖ ‖x‖ with hle | hle
    · exact duality_separation_estimate (X := X) hR hε hδ (fun {f g} hf hg hsep => hc hf hg hsep)
        (selection_mem J hJ x) (selection_mem J hJ y) (hb x hx) hle hsep
    · have hp := duality_separation_estimate (X := X) hR hε hδ (fun {f g} hf hg hsep => hc hf hg hsep)
        (selection_mem J hJ y) (selection_mem J hJ x) (hb y hy) hle
        (by simpa only [norm_sub_rev] using hsep)
      simpa only [norm_sub_rev] using hp
  have hlt := (lt_div_iff₀ (show 0 < 12 * R by positivity)).mp hxy
  linarith

/-- The error in the supporting affine approximation is squeezed by the
variation of the duality map. -/
lemma halfNormSquare_remainder (J : X → (X →L[ℝ] ℝ))
    (hJ : ∀ x, Spec.DualityMapValue X x = {J x}) (x z : X) :
    0 ≤ ‖z‖ ^ 2 / 2 - ‖x‖ ^ 2 / 2 - J x (z - x) ∧
    ‖z‖ ^ 2 / 2 - ‖x‖ ^ 2 / 2 - J x (z - x) ≤
      ‖J z - J x‖ * ‖z - x‖ := by
  have hl := halfNormSquare_support J hJ x z
  have hu := halfNormSquare_support J hJ z x
  have hb := (J z - J x).le_opNorm (z - x)
  rw [Real.norm_eq_abs] at hb
  have hn : J z (x - z) = - J z (z - x) := by rw [← map_neg, neg_sub]
  rw [hn] at hu
  simp only [sub_apply] at hb
  exact ⟨by linarith, by linarith [(abs_le.mp hb).2]⟩

lemma duality_continuous_of_uniformOnBounded (J : X → (X →L[ℝ] ℝ))
    (hU : ∀ s : Set X, Bornology.IsBounded s → UniformContinuousOn J s) :
    Continuous J := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hU (Metric.closedBall x 1) Metric.isBounded_closedBall).continuousOn.continuousAt
    (Metric.closedBall_mem_nhds x zero_lt_one)

theorem halfNormSquare_frechetC1 : UniformDualSpec.FrechetC1.{u} := by
  intro X _ _ _ J hJ hU
  have hcont := duality_continuous_of_uniformOnBounded J hU
  have hderiv : ∀ x : X, HasFDerivAt (fun z : X => ‖z‖ ^ 2 / 2) (J x) x := by
    intro x
    rw [hasFDerivAt_iff_isLittleO]
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have he : ∀ᶠ z in 𝓝 x, ‖J z - J x‖ < ε := by
      simpa only [Metric.mem_ball, dist_eq_norm] using
        (hcont.continuousAt (x := x)).eventually (Metric.ball_mem_nhds (J x) hε)
    filter_upwards [he] with z hz
    obtain ⟨hl, hu⟩ := halfNormSquare_remainder J hJ x z
    rw [Real.norm_eq_abs, abs_of_nonneg hl]
    exact hu.trans (mul_le_mul_of_nonneg_right hz.le (norm_nonneg _))
  exact ⟨hderiv, contDiff_one_iff_hasFDerivAt.mpr ⟨J, hcont, hderiv⟩,
    fun x => (hderiv x).fderiv⟩

/-- Young's inequality for the primal and dual quadratic norms. -/
lemma normSquare_fenchel (f : X →L[ℝ] ℝ) (z : X) :
    f z ≤ ‖z‖ ^ 2 / 2 + ‖f‖ ^ 2 / 2 := by
  have hb := f.le_opNorm z
  rw [Real.norm_eq_abs] at hb
  have ha := le_abs_self (f z)
  nlinarith [sq_nonneg (‖z‖ - ‖f‖)]

/-- Uniform continuity on the radius-two ball controls the symmetric
second difference on the unit ball. -/
lemma halfNormSquare_symmetric_bound (J : X → (X →L[ℝ] ℝ))
    (hJ : ∀ x, Spec.DualityMapValue X x = {J x})
    {η t d : ℝ} (hη : 0 < η) (ht : 0 < t) (ht1 : t ≤ 1) (htd : t < d)
    (hU : ∀ a ∈ Metric.closedBall (0 : X) 2,
      ∀ b ∈ Metric.closedBall (0 : X) 2, dist a b < d → dist (J a) (J b) < η)
    {x y : X} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x + t • y‖ ^ 2 / 2 + ‖x - t • y‖ ^ 2 / 2 ≤ 1 + 2 * t * η := by
  have hstep : ‖t • y‖ ≤ t := by
    rw [norm_smul, Real.norm_of_nonneg ht.le]
    exact mul_le_of_le_one_right ht.le hy
  have hx2 : x ∈ Metric.closedBall (0 : X) 2 := by
    rw [mem_closedBall_zero_iff]; linarith
  have hp2 : x + t • y ∈ Metric.closedBall (0 : X) 2 := by
    rw [mem_closedBall_zero_iff]
    exact (norm_add_le _ _).trans (by linarith)
  have hm2 : x - t • y ∈ Metric.closedBall (0 : X) 2 := by
    rw [mem_closedBall_zero_iff]
    exact (norm_sub_le _ _).trans (by linarith)
  have hpd : dist (x + t • y) x < d := by
    rw [dist_eq_norm, add_sub_cancel_left]; exact hstep.trans_lt htd
  have hmd : dist (x - t • y) x < d := by
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hstep.trans_lt htd
  have hp := hU _ hp2 _ hx2 hpd
  have hm := hU _ hm2 _ hx2 hmd
  rw [dist_eq_norm] at hp hm
  have hrp := (halfNormSquare_remainder J hJ x (x + t • y)).2
  have hrm := (halfNormSquare_remainder J hJ x (x - t • y)).2
  simp only [add_sub_cancel_left, sub_sub_cancel_left, map_neg, norm_neg] at hrp hrm
  have hbp : ‖J (x + t • y) - J x‖ * ‖t • y‖ ≤ η * t :=
    mul_le_mul hp.le hstep (norm_nonneg _) hη.le
  have hbm : ‖J (x - t • y) - J x‖ * ‖t • y‖ ≤ η * t :=
    mul_le_mul hm.le hstep (norm_nonneg _) hη.le
  have hx0 := norm_nonneg x
  nlinarith [sq_nonneg (1 - ‖x‖)]

/-- Uniform continuity of the normalized duality selection forces uniform
convexity of the entire dual ball; no norm-attainment assumption is used. -/
lemma uniformConvexDual_of_uniformOnBounded (J : X → (X →L[ℝ] ℝ))
    (hJ : ∀ x, Spec.DualityMapValue X x = {J x})
    (hU : ∀ s : Set X, Bornology.IsBounded s → UniformContinuousOn J s) :
    UniformConvexSpace (X →L[ℝ] ℝ) := by
  constructor
  intro ε hε
  obtain ⟨d, hd, hdu⟩ := Metric.uniformContinuousOn_iff.mp
    (hU (Metric.closedBall (0 : X) 2) Metric.isBounded_closedBall)
      (ε / 16) (by positivity)
  let t := min (d / 2) (1 / 2)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have htd : t < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨t * ε / 4, by positivity, ?_⟩
  intro f hf g hg hsep
  have heps : ε ≤ 2 := by
    calc
      ε ≤ ‖f - g‖ := hsep
      _ ≤ ‖f‖ + ‖g‖ := norm_sub_le _ _
      _ = 2 := by rw [hf, hg]; norm_num
  obtain ⟨y, hy, hval⟩ := (f - g).exists_lt_apply_of_lt_opNorm
    (show ε / 2 < ‖f - g‖ by linarith)
  rw [Real.norm_eq_abs] at hval
  obtain ⟨y, hy, hval⟩ : ∃ y : X, ‖y‖ ≤ 1 ∧ ε / 2 < (f - g) y := by
    by_cases hn : (f - g) y < 0
    · refine ⟨-y, by simpa only [norm_neg] using hy.le, ?_⟩
      rw [map_neg]
      rw [abs_of_neg hn] at hval
      exact hval
    · exact ⟨y, hy.le, by rwa [abs_of_nonneg (le_of_not_gt hn)] at hval⟩
  have heval : ∀ x : X, ‖x‖ ≤ 1 → (f + g) x ≤ 2 - t * ε / 4 := by
    intro x hx
    have hsym := halfNormSquare_symmetric_bound J hJ
      (show 0 < ε / 16 by positivity) ht ht1 htd hdu hx hy
    have hp := normSquare_fenchel f (x + t • y)
    have hm := normSquare_fenchel g (x - t • y)
    rw [hf] at hp
    rw [hg] at hm
    simp only [map_add, map_sub, map_smul, smul_eq_mul, one_pow, add_apply,
      sub_apply] at *
    have hmul := mul_lt_mul_of_pos_left hval ht
    nlinarith
  have hM : 0 ≤ 2 - t * ε / 4 := by
    have hh := heval 0 (by simp)
    simpa only [map_zero] using hh
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
  intro x hx
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hh := heval (-x) (by simp only [norm_neg, hx, le_refl])
    rw [map_neg] at hh
    linarith
  · exact heval x hx.le

theorem uniformDuality_equivalence : UniformDualSpec.Equivalence.{u} := by
  intro X _ _ _
  constructor
  · intro h
    let := h
    obtain ⟨J, hJ⟩ := dualityMap_singleton X
    exact ⟨J, hJ, duality_uniformContinuousOn J hJ⟩
  · rintro ⟨J, hJ, hU⟩
    exact uniformConvexDual_of_uniformOnBounded J hJ hU

end ExpandedFA.BanachConvex
