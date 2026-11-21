import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.JordanLocalEstimate
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.KernelPrimitiveBound
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.OneSided
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.SecondMeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace SingleVariableAnalysis.Fourier
open Set Filter Riemann BV
open scoped Topology

/-- The available right approach on a nondegenerate closed interval is nontrivial. -/
theorem rightIntervalFilter_neBot {b : ℝ} (hb : 0 < b) :
    NeBot (𝓝[Icc 0 b ∩ Ioi 0] (0 : ℝ)) := by
  have he : Icc (0 : ℝ) b ∩ Ioi 0 = Ioc 0 b := by
    ext t
    constructor
    · rintro ⟨ht, hp⟩
      exact ⟨hp, ht.2⟩
    · intro ht
      exact ⟨⟨ht.1.le, ht.2⟩, ht.1⟩
  rw [he]
  exact left_nhdsWithin_Ioc_neBot hb

/-- A nondecreasing function's right limit bounds all its positive arguments
from below, even if its value at zero has a jump. -/
theorem rightLimit_le_of_monotoneOn {g : ℝ → ℝ} {b L : ℝ} (hb : 0 < b)
    (hg : MonotoneOn g (Icc 0 b)) (hL : RightRelativeLimit g (Icc 0 b) 0 L)
    {t : ℝ} (ht : t ∈ Ioc 0 b) : L ≤ g t := by
  have := rightIntervalFilter_neBot hb
  apply le_of_tendsto ((rightRelativeLimit_filter_iff _ _ _ _).mp hL).2
  have hlt : ∀ᶠ x in 𝓝[Icc 0 b ∩ Ioi 0] (0 : ℝ), x < t :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.1)
  filter_upwards [hlt, self_mem_nhdsWithin] with x hx hI
  exact hg hI.1 ⟨ht.1.le, ht.2⟩ hx.le

/-- Recenter a monotone function at its right limit and assign zero at the
endpoint. The possibly discontinuous original endpoint is deliberately reset. -/
def rightRecenter (g : ℝ → ℝ) (L t : ℝ) : ℝ :=
  if t = 0 then 0 else g t - L

theorem rightRecenter_properties {g : ℝ → ℝ} {b L : ℝ} (hb : 0 < b)
    (hg : MonotoneOn g (Icc 0 b)) (hL : RightRelativeLimit g (Icc 0 b) 0 L) :
    MonotoneOn (rightRecenter g L) (Icc 0 b) ∧
    (∀ t ∈ Icc 0 b, 0 ≤ rightRecenter g L t) ∧
    RightRelativeLimit (rightRecenter g L) (Icc 0 b) 0 0 := by
  have hn : ∀ t ∈ Icc 0 b, 0 ≤ rightRecenter g L t := by
    intro t ht
    by_cases hz : t = 0
    · simp [rightRecenter, hz]
    · have hp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
      simpa only [rightRecenter, ite_eq_right hz, sub_nonneg] using
        rightLimit_le_of_monotoneOn hb hg hL ⟨hp, ht.2⟩
  refine ⟨?_, hn, ?_⟩
  · intro x hx y hy hxy
    by_cases hx0 : x = 0
    · simpa [rightRecenter, hx0] using hn y hy
    · have hy0 : y ≠ 0 := by intro he; subst y; exact hx0 (le_antisymm hxy hx.1)
      simp only [rightRecenter, ite_eq_right hx0, ite_eq_right hy0]
      exact sub_le_sub_right (hg hx hy hxy) L
  · apply (rightRelativeLimit_filter_iff _ _ _ _).mpr
    refine ⟨((rightRelativeLimit_filter_iff _ _ _ _).mp hL).1, ?_⟩
    have hT := ((rightRelativeLimit_filter_iff _ _ _ _).mp hL).2.sub
      (tendsto_const_nhds (x := L))
    have hT' : Tendsto (fun t => g t - L) (𝓝[Icc 0 b ∩ Ioi 0] 0) (𝓝 0) := by
      simpa only [sub_self] using hT
    apply hT'.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht.2
    simp [rightRecenter, ne_of_gt ht0]

/-- The small components are obtained from Jordan components by subtracting
their right limits. Equality of those limits is proved from h → 0. -/
theorem jordan_small_components :
    Specs.SingleVariableAnalysis.Ch19.JordanLocalEstimate.smallJordanComponents := by
  intro h b hb hBV h0 hlim
  obtain ⟨g, q, hg, hq, heq⟩ := (jordan_iff h hb.le).mp hBV
  obtain ⟨Lg, hLg⟩ := monotoneOn_closedInterval_right_limit hg (show 0 ∈ Ico 0 b from ⟨le_rfl, hb⟩)
  obtain ⟨Lq, hLq⟩ := monotoneOn_closedInterval_right_limit hq (show 0 ∈ Ico 0 b from ⟨le_rfl, hb⟩)
  have := rightIntervalFilter_neBot hb
  have hd : Tendsto h (𝓝[Icc 0 b ∩ Ioi 0] 0) (𝓝 (Lg - Lq)) := by
    apply (((rightRelativeLimit_filter_iff _ _ _ _).mp hLg).2.sub
      ((rightRelativeLimit_filter_iff _ _ _ _).mp hLq).2).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (heq t ht.1).symm
  have hzero : Lg - Lq = 0 := tendsto_nhds_unique hd
    ((rightRelativeLimit_filter_iff _ _ _ _).mp hlim).2
  obtain ⟨hgu, hgn, hgl⟩ := rightRecenter_properties hb hg hLg
  obtain ⟨hqv, hqn, hql⟩ := rightRecenter_properties hb hq hLq
  refine ⟨rightRecenter g Lg, rightRecenter q Lq, hgu, hqv,
    by simp [rightRecenter], by simp [rightRecenter], ?_, hgl, hql⟩
  intro t ht
  refine ⟨hgn t ht, hqn t ht, ?_⟩
  by_cases hz : t = 0
  · simp [hz, h0, rightRecenter]
  · simp only [rightRecenter, ite_eq_right hz]
    rw [heq t ht]
    linarith

/-- Reflected second mean value: cancellation of the unweighted kernel controls
a nonnegative nondecreasing weight by its final value. -/
theorem monotone_weight_integral_bound {f g : ℝ → ℝ} {a b C : ℝ}
    (hf : RealIntegrable f a b) (hg0 : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hg : MonotoneOn g (Icc a b))
    (hB : ∀ ξ ∈ Icc a b, ∀ hi : RealIntegrable f ξ b,
      |realIntegral f hi| ≤ C) :
    ∃ hi : RealIntegrable (fun t => g t * f t) a b,
      |realIntegral _ hi| ≤ g b * C := by
  obtain ⟨_, hi, ξ, hξ, hξi, he⟩ := second_mean_value_monotone f g hf hg0 hg
  refine ⟨hi, ?_⟩
  change realIntegral _ hi = g b * realIntegral f hξi at he
  rw [he, abs_mul, abs_of_nonneg (hg0 b ⟨hf.ordered, le_rfl⟩)]
  exact mul_le_mul_of_nonneg_left (hB ξ hξ hξi) (hg0 b ⟨hf.ordered, le_rfl⟩)

/-- Local Dirichlet–Jordan estimate. Both the choice of interval and the
integral bound are uniform in N; no absolute-integrability condition at zero
is used. The same C also bounds all unweighted kernel primitives. -/
theorem jordan_local_estimate :
    Specs.SingleVariableAnalysis.Ch19.JordanLocalEstimate.localEstimate := by
  obtain ⟨C, hC, hkernel⟩ := dirichlet_kernel_primitive_bound
  refine ⟨C, hC, hkernel, ?_⟩
  intro h b hb hBV h0 hlim ε hε
  obtain ⟨u, v, hu, hv, _hu0, _hv0, hvalues, hulim, hvlim⟩ :=
    jordan_small_components h hb hBV h0 hlim
  obtain ⟨du, hdu, huε⟩ := ((rightRelativeLimit_iff _ _ _ _).mp hulim).2 ε hε
  obtain ⟨dv, hdv, hvε⟩ := ((rightRelativeLimit_iff _ _ _ _).mp hvlim).2 ε hε
  let r := min b (min Real.pi (min du dv))
  have hr : 0 < r := lt_min hb (lt_min Real.pi_pos (lt_min hdu hdv))
  let δ := r / 2
  have hδ : 0 < δ := half_pos hr
  have hδr : δ < r := half_lt_self hr
  have hδb : δ ≤ b := hδr.le.trans (min_le_left _ _)
  have hδπ : δ ≤ Real.pi := hδr.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδdu : δ < du := hδr.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδdv : δ < dv := hδr.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδI : δ ∈ Icc 0 b := ⟨hδ.le, hδb⟩
  have huδ : u δ < ε := by
    have he := huε δ hδI hδ (by simpa only [zero_add] using hδdu)
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hvalues δ hδI).1] using he
  have hvδ : v δ < ε := by
    have he := hvε δ hδI hδ (by simpa only [zero_add] using hδdv)
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hvalues δ hδI).2.1] using he
  have hreal : ∀ (N : ℕ) (x y : ℝ), 0 ≤ x → x ≤ y → y ≤ Real.pi →
      ∀ hi : RealIntegrable (fun t => (dirichletKernel N t).re) x y,
        |realIntegral _ hi| ≤ C := by
    intro N x y hx hxy hy hi
    obtain ⟨hk, hkB⟩ := hkernel N x y hx hxy hy
    have he := (complexIntegral_components (dirichletKernel N) hk).1
    calc
      _ = |(complexIntegral (dirichletKernel N) hk).re| := by rw [he]
      _ ≤ ‖complexIntegral (dirichletKernel N) hk‖ := Complex.abs_re_le_norm _
      _ ≤ C := hkB
  refine ⟨δ, hδ, hδb, hδπ, ?_⟩
  intro N
  obtain ⟨hk, _⟩ := hkernel N 0 δ le_rfl hδ.le hδπ
  have hsub : Icc 0 δ ⊆ Icc 0 b := Icc_subset_Icc le_rfl hδb
  have hB : ∀ ξ ∈ Icc 0 δ,
      ∀ hi : RealIntegrable (fun t => (dirichletKernel N t).re) ξ δ,
        |realIntegral _ hi| ≤ C :=
    fun ξ hξ hi => hreal N ξ δ hξ.1 hξ.2 hδπ hi
  obtain ⟨hui, huB⟩ := monotone_weight_integral_bound hk.1
    (fun t ht => (hvalues t (hsub ht)).1) (hu.mono hsub) hB
  obtain ⟨hvi, hvB⟩ := monotone_weight_integral_bound hk.1
    (fun t ht => (hvalues t (hsub ht)).2.1) (hv.mono hsub) hB
  obtain ⟨hneg, hnegE⟩ := real_mul_value hvi (-1)
  obtain ⟨hs, hsE⟩ := real_add_value hui hneg
  obtain ⟨hi, hiE⟩ := real_endpoint_extensions _
    (fun t => h t * (dirichletKernel N t).re) 0 δ (by
      intro t ht
      rw [(hvalues t (hsub (Ioo_subset_Icc_self ht))).2.2]
      ring) hs
  refine ⟨hi, ?_⟩
  change realIntegral _ hi = realIntegral _ hs at hiE
  change |realIntegral _ hi| ≤ 2 * C * ε
  rw [hiE, hsE, hnegE]
  calc
    _ ≤ |realIntegral _ hui| + |realIntegral _ hvi| := by
      simpa only [neg_one_mul, ← sub_eq_add_neg] using
        abs_sub (realIntegral _ hui) (realIntegral _ hvi)
    _ ≤ u δ * C + v δ * C := add_le_add huB hvB
    _ ≤ 2 * C * ε := by
      have huC := mul_le_mul_of_nonneg_right huδ.le hC
      have hvC := mul_le_mul_of_nonneg_right hvδ.le hC
      nlinarith


/-- A real weight times the original finite kernel has the real integral
computed above and zero imaginary part. This identifies the two integral
representations with their actual integrability certificates. -/
theorem real_kernel_product_integral (h : ℝ → ℝ) (N : ℕ) {a b : ℝ}
    (hi : RealIntegrable (fun t => h t * (dirichletKernel N t).re) a b) :
    ∃ hc : ComplexIntegrable (fun t => (h t : ℂ) * dirichletKernel N t) a b,
      complexIntegral _ hc = (realIntegral _ hi : ℂ) := by
  have hre : (fun t => ((h t : ℂ) * dirichletKernel N t).re) =
      (fun t => h t * (dirichletKernel N t).re) := by
    funext t
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have him : (fun t => ((h t : ℂ) * dirichletKernel N t).im) = (fun _ => 0) := by
    funext t
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    have hzero : (dirichletKernel N t).im = 0 := dirichletKernel_real N t
    rw [hzero, mul_zero]
  obtain ⟨hz, hzE⟩ := real_zero_value hi.ordered
  have hc : ComplexIntegrable (fun t => (h t : ℂ) * dirichletKernel N t) a b :=
    ⟨by rw [hre]; exact hi, by rw [him]; exact hz⟩
  refine ⟨hc, ?_⟩
  rw [integral_re_im hc hi hz hre him, hzE]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]

/-- The uniform local estimate for h D_N using the original complex finite
Dirichlet kernel, with the same common primitive constant and cutoff. -/
theorem jordan_local_estimate_complex :
    Specs.SingleVariableAnalysis.Ch19.JordanLocalEstimate.complexLocalEstimate := by
  obtain ⟨C, hC, hkernel, hlocal⟩ := jordan_local_estimate
  refine ⟨C, hC, hkernel, ?_⟩
  intro h b hb hBV h0 hlim ε hε
  obtain ⟨δ, hδ, hδb, hδπ, hN⟩ := hlocal h hb hBV h0 hlim ε hε
  refine ⟨δ, hδ, hδb, hδπ, ?_⟩
  intro N
  obtain ⟨hi, hiB⟩ := hN N
  obtain ⟨hc, he⟩ := real_kernel_product_integral h N hi
  refine ⟨hc, ?_⟩
  change ‖complexIntegral _ hc‖ ≤ 2 * C * ε
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact hiB

end SingleVariableAnalysis.Fourier
