import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Dirichlet
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.AccumulationParts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace SingleVariableAnalysis.Riemann.Improper
open Set
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open Specs.SingleVariableAnalysis.Ch10.Dirichlet

/-- A continuous derivative of a monotone function has constant weak sign,
including endpoints where only the continuous extension is prescribed. -/
theorem derivative_nonneg_on_interval {g g' : ℝ → ℝ} {u v : ℝ}
    (huv : u < v) (hgp : ContinuousOn g' (Icc u v))
    (hd : ∀ x ∈ Ioo u v, HasDerivAt g (g' x) x)
    (hm : MonotoneOn g (Icc u v)) : ∀ x ∈ Icc u v, 0 ≤ g' x := by
  have hi : ∀ x ∈ Ioo u v, 0 ≤ g' x := by
    intro x hx
    have hh := hm.derivWithin_nonneg (x := x)
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2), (hd x hx).deriv] at hh
    exact hh
  intro x hx
  apply le_on_closure hi continuousOn_const
    (by simpa only [closure_Ioo huv.ne] using hgp)
  simpa only [closure_Ioo huv.ne] using hx

/-- Total variation of a C¹ monotone real function, as a proper integral. -/
theorem integral_abs_derivative {g g' : ℝ → ℝ} {u v : ℝ}
    (huv : u < v) (hg : ContinuousOn g (Icc u v))
    (hgp : ContinuousOn g' (Icc u v))
    (hd : ∀ x ∈ Ioo u v, HasDerivAt g (g' x) x)
    (hm : MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v)) :
    ∃ hn : RealIntegrable (fun x => |g' x|) u v,
      realIntegral _ hn = |g v - g u| := by
  have hp := realIntegrable_of_continuousOn huv.le hgp
  have he : realIntegral g' hp = g v - g u :=
    real_ftc_second g g' u v huv.le hg hd hp
  rcases hm with hm | hm
  · have hs := derivative_nonneg_on_interval huv hgp hd hm
    obtain ⟨hn, hnval⟩ := realIntegral_congr_on hp
      (fun x hx => (abs_of_nonneg (hs x hx)).symm)
    exact ⟨hn, hnval.trans (he.trans (abs_of_nonneg
      (sub_nonneg.mpr (hm ⟨le_rfl, huv.le⟩ ⟨huv.le, le_rfl⟩ huv.le))).symm)⟩
  · have hs := derivative_nonneg_on_interval huv hgp.neg
      (fun x hx => (hd x hx).neg) hm.neg
    obtain ⟨hn, hnv⟩ := real_mul_value hp (-1)
    obtain ⟨ha, hav⟩ := realIntegral_congr_on hn (fun x hx => by
      simpa only [neg_one_mul] using (abs_of_nonpos (by have hh : 0 ≤ -g' x := hs x hx; linarith)).symm)
    refine ⟨ha, ?_⟩
    rw [hav, hnv, he, neg_one_mul, abs_of_nonpos
      (sub_nonpos.mpr (hm ⟨le_rfl, huv.le⟩ ⟨huv.le, le_rfl⟩ huv.le))]

/-- The parts integral is bounded by primitive size times variation. -/
theorem real_weighted_tail_bound {f g g' : ℝ → ℝ} {u v M : ℝ}
    (huv : u < v) (hf : RealIntegrable f u v) (_hM : 0 ≤ M)
    (hb : ∀ (x : Icc u v) (h : RealIntegrable f u x), |realIntegral f h| ≤ M)
    (hg : ContinuousOn g (Icc u v)) (hgp : ContinuousOn g' (Icc u v))
    (hd : ∀ x ∈ Ioo u v, HasDerivAt g (g' x) x)
    (hm : MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v)) :
    ∃ hfg : RealIntegrable (fun x => f x * g x) u v,
      |realIntegral _ hfg| ≤ M * (|g v| + |g v - g u|) := by
  obtain ⟨H, F, hF, hfg, hFg, he⟩ := real_accumulation_parts f g g' hf hg hgp hd
  have hFb (x : ℝ) (hx : x ∈ Icc u v) : |F x| ≤ M := by
    rw [hF ⟨x, hx⟩]
    exact hb ⟨x, hx⟩ (H ⟨x, hx⟩)
  obtain ⟨hn, hnval⟩ := integral_abs_derivative huv hg hgp hd hm
  obtain ⟨hmn, hmnval⟩ := real_mul_value hn M
  obtain ⟨habs, hle, _⟩ := real_norm_estimate _ hFg
  have horder := realIntegral_mono _ _ habs hmn (fun x hx => by
    change |F x * g' x| ≤ M * |g' x|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hFb x hx) (abs_nonneg _))
  change realIntegral _ habs ≤ realIntegral _ hmn at horder
  rw [hmnval, hnval] at horder
  have hbound : |realIntegral _ hFg| ≤ M * |g v - g u| := hle.trans horder
  refine ⟨hfg, ?_⟩
  change realIntegral _ hfg = _ at he
  rw [he]
  calc
    |F v * g v - realIntegral _ hFg| ≤ |F v * g v| + |realIntegral _ hFg| := abs_sub _ _
    _ ≤ M * |g v| + M * |g v - g u| := add_le_add
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hFb v ⟨huv.le, le_rfl⟩) (abs_nonneg _)) hbound
    _ = _ := by ring

/-- Continuous real multiplication preserves proper scalar integrability. -/
theorem weighted_integrable (k : ScalarKind) (f : ℝ → S.scalarValue k)
    (g : ℝ → ℝ) {u v : ℝ} (huv : u ≤ v)
    (hf : I.scalarIntegrableValue k f u v) (hg : ContinuousOn g (Icc u v)) :
    I.scalarIntegrableValue k (weighted k f g) u v := by
  have hgint := realIntegrable_of_continuousOn huv hg
  cases k with
  | real => exact real_product hf hgint
  | complex =>
    change ℝ → ℂ at f
    change ComplexIntegrable (fun x => f x * (g x : ℂ)) u v
    constructor
    · simpa only [weighted, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero] using real_product hf.1 hgint
    · simpa only [weighted, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, zero_add] using real_product hf.2 hgint

/-- A common real/complex tail estimate. The factor 2 in the complex case
comes from the two real components, and its size is immaterial for convergence. -/
theorem weighted_tail_bound (k : ScalarKind) (f : ℝ → S.scalarValue k)
    (g g' : ℝ → ℝ) {u v M : ℝ} (huv : u < v)
    (hf : I.scalarIntegrableValue k f u v) (hM : 0 ≤ M)
    (hb : ∀ (x : Icc u v) (h : I.scalarIntegrableValue k f u x),
      ‖I.scalarIntegralValue k f h‖ ≤ M)
    (hg : ContinuousOn g (Icc u v)) (hgp : ContinuousOn g' (Icc u v))
    (hd : ∀ x ∈ Ioo u v, HasDerivAt g (g' x) x)
    (hm : MonotoneOn g (Icc u v) ∨ AntitoneOn g (Icc u v)) :
    ∃ hfg : I.scalarIntegrableValue k (weighted k f g) u v,
      ‖I.scalarIntegralValue k _ hfg‖ ≤ 2 * M * (|g v| + |g v - g u|) := by
  cases k with
  | real =>
    obtain ⟨hr, hrv⟩ := real_weighted_tail_bound huv hf hM hb hg hgp hd hm
    refine ⟨hr, hrv.trans ?_⟩
    have : 0 ≤ |g v| + |g v - g u| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith
  | complex =>
    change ℝ → ℂ at f
    change ComplexIntegrable f u v at hf
    have hbr (x : Icc u v) (h : RealIntegrable (fun t => (f t).re) u x) :
        |realIntegral _ h| ≤ M := by
      have hx := ComplexIntegrable.subinterval hf le_rfl x.property.1 x.property.2
      have he : (complexIntegral f hx).re = realIntegral _ h := (complexIntegral_components f hx).1
      rw [← he]
      exact (Complex.abs_re_le_norm _).trans (hb x hx)
    have hbi (x : Icc u v) (h : RealIntegrable (fun t => (f t).im) u x) :
        |realIntegral _ h| ≤ M := by
      have hx := ComplexIntegrable.subinterval hf le_rfl x.property.1 x.property.2
      have he : (complexIntegral f hx).im = realIntegral _ h := (complexIntegral_components f hx).2
      rw [← he]
      exact (Complex.abs_im_le_norm _).trans (hb x hx)
    obtain ⟨hr, hrv⟩ := real_weighted_tail_bound huv hf.1 hM hbr hg hgp hd hm
    obtain ⟨hi, hiv⟩ := real_weighted_tail_bound huv hf.2 hM hbi hg hgp hd hm
    have hfg : ComplexIntegrable (fun x => f x * (g x : ℂ)) u v :=
      weighted_integrable .complex f g huv.le hf hg
    have her : (complexIntegral _ hfg).re = realIntegral _ hr := by
      have hc := (complexIntegral_components _ hfg).1
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero] using hc
    have hei : (complexIntegral _ hfg).im = realIntegral _ hi := by
      have hc := (complexIntegral_components _ hfg).2
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, zero_add] using hc
    refine ⟨hfg, ?_⟩
    change ‖complexIntegral _ hfg‖ ≤ _
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    rw [her, hei]
    linarith

/-- A convenient positive tolerance, also covering the zero primitive bound. -/
private theorem small_tail_arithmetic {C ε u v J : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hu : |u| < ε / (12 * C + 1)) (hv : |v| < ε / (12 * C + 1))
    (hJ : J ≤ 2 * (2 * C) * (|v| + |v - u|)) : J < ε := by
  let δ := ε / (12 * C + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hd : δ * (12 * C + 1) = ε := div_mul_cancel₀ ε (by positivity)
  have hsum : |v| + |v - u| ≤ 3 * δ := by
    have := abs_sub v u
    change |u| < δ at hu
    change |v| < δ at hv
    linarith
  have hb := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * (2 * C) by positivity)
  nlinarith

/-- Dirichlet's test at a right singular endpoint. `b = ⊤` is the original
infinite-interval theorem; a finite `b` is approached from the left. -/
theorem right_dirichlet : rightDirichlet := by
  intro k f g g' a b hf C hbound hc1 hm hzero
  have hC : 0 ≤ C := by
    obtain ⟨t⟩ := right_index_nonempty hf
    exact (norm_nonneg _).trans (hbound t)
  have hfg : RightRegular k (weighted k f g) a b :=
    ⟨hf.1, fun t => weighted_integrable k f g t.property.1.le (hf.2 t) (hc1 t).1⟩
  apply (right_cauchy_criterion k _ a b hfg).mpr
  intro ε hε
  obtain ⟨r, hr⟩ := hzero (ε / (12 * C + 1)) (by positivity)
  refine ⟨r, fun u v hru huv => ?_⟩
  have huv' : u.val < v.val := huv
  have hfuv := scalar_integrable_subinterval k f (hf.2 v) u.property.1.le huv.le le_rfl
  have hprimitive (x : Icc u.val v.val)
      (h : I.scalarIntegrableValue k f u.val x) : ‖I.scalarIntegralValue k f h‖ ≤ 2 * C := by
    let xi : RightIndex a b := ⟨x, u.property.1.trans_le x.property.1,
      (WithTop.coe_le_coe.mpr x.property.2).trans_lt v.property.2⟩
    have he : RightTruncation k f a b hf xi =
        RightTruncation k f a b hf u + I.scalarIntegralValue k f h :=
      scalar_integral_split k f u.property.1.le x.property.1 (hf.2 xi) (hf.2 u) h
    calc
      ‖I.scalarIntegralValue k f h‖ =
          ‖RightTruncation k f a b hf xi - RightTruncation k f a b hf u‖ := by
        rw [he, add_sub_cancel_left]
      _ ≤ ‖RightTruncation k f a b hf xi‖ + ‖RightTruncation k f a b hf u‖ := norm_sub_le _ _
      _ ≤ 2 * C := by linarith [hbound xi, hbound u]
  have hsub : Icc u.val v.val ⊆ {x | a ≤ x ∧ (x : WithTop ℝ) < b} := by
    intro x hx
    exact ⟨u.property.1.le.trans hx.1, (WithTop.coe_le_coe.mpr hx.2).trans_lt v.property.2⟩
  obtain ⟨ht, htval⟩ := weighted_tail_bound k f g g' huv' hfuv (by positivity)
    hprimitive ((hc1 v).1.mono (Icc_subset_Icc u.property.1.le le_rfl))
    ((hc1 v).2.1.mono (Icc_subset_Icc u.property.1.le le_rfl))
    (fun x hx => (hc1 v).2.2 x ⟨u.property.1.trans hx.1, hx.2⟩)
    (hm.imp (fun h => h.mono hsub) (fun h => h.mono hsub))
  exact ⟨ht, small_tail_arithmetic hC hε (hr u hru) (hr v (hru.trans huv)) htval⟩

/-- Dirichlet's test with a singular left endpoint. The accumulation is
∫ₓᵇf and the cofinal truncations decrease toward `a`, including a finite `a`. -/
theorem left_dirichlet : leftDirichlet := by
  intro k f g g' a b hf C hbound hc1 hm hzero
  have hC : 0 ≤ C := by
    obtain ⟨t⟩ := left_index_nonempty hf
    exact (norm_nonneg _).trans (hbound t)
  have hfg : LeftRegular k (weighted k f g) a b :=
    ⟨hf.1, fun t => weighted_integrable k f g t.property.2.le (hf.2 t) (hc1 t).1⟩
  apply (left_cauchy_criterion k _ a b hfg).mpr
  intro ε hε
  obtain ⟨r, hr⟩ := hzero (ε / (12 * C + 1)) (by positivity)
  refine ⟨r, fun u v huv hvr => ?_⟩
  have huv' : u.val < v.val := huv
  have hfuv := scalar_integrable_subinterval k f (hf.2 u) le_rfl huv.le v.property.2.le
  have hprimitive (x : Icc u.val v.val)
      (h : I.scalarIntegrableValue k f u.val x) : ‖I.scalarIntegralValue k f h‖ ≤ 2 * C := by
    let xi : LeftIndex a b := ⟨x,
      u.property.1.trans_le (WithBot.coe_le_coe.mpr x.property.1),
      x.property.2.trans_lt v.property.2⟩
    have he : LeftTruncation k f a b hf u =
        I.scalarIntegralValue k f h + LeftTruncation k f a b hf xi :=
      scalar_integral_split k f x.property.1 xi.property.2.le (hf.2 u) h (hf.2 xi)
    calc
      ‖I.scalarIntegralValue k f h‖ =
          ‖LeftTruncation k f a b hf u - LeftTruncation k f a b hf xi‖ := by
        rw [he, add_sub_cancel_right]
      _ ≤ ‖LeftTruncation k f a b hf u‖ + ‖LeftTruncation k f a b hf xi‖ := norm_sub_le _ _
      _ ≤ 2 * C := by linarith [hbound u, hbound xi]
  have hsub : Icc u.val v.val ⊆ {x | a < (x : WithBot ℝ) ∧ x ≤ b} := by
    intro x hx
    exact ⟨u.property.1.trans_le (WithBot.coe_le_coe.mpr hx.1), hx.2.trans v.property.2.le⟩
  obtain ⟨ht, htval⟩ := weighted_tail_bound k f g g' huv' hfuv (by positivity)
    hprimitive ((hc1 u).1.mono (Icc_subset_Icc le_rfl v.property.2.le))
    ((hc1 u).2.1.mono (Icc_subset_Icc le_rfl v.property.2.le))
    (fun x hx => (hc1 u).2.2 x ⟨hx.1, hx.2.trans v.property.2⟩)
    (hm.imp (fun h => h.mono hsub) (fun h => h.mono hsub))
  exact ⟨ht, small_tail_arithmetic hC hε (hr u (huv.trans hvr)) (hr v hvr) htval⟩

end SingleVariableAnalysis.Riemann.Improper
