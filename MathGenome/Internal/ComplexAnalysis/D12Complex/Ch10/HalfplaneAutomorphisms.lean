import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.HalfplaneAutomorphisms
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.DiskAutomorphisms
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch10.ElementaryMaps
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch10.TriplesCrossRatio
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

noncomputable section
open Set Metric
namespace D12Complex.HalfplaneAutomorphisms

namespace Definitions
/-- Candidate-owned export of the canonical fraction used by the independent Spec. -/
abbrev realFraction :
    Specs.D12Complex.Ch10.HalfplaneAutomorphisms.realFraction_type :=
  D12Complex.HalfplaneAutomorphisms.realFraction
end Definitions

lemma unitDisk_eq_ball : unitDisk = ball (0 : ℂ) 1 := by
  ext z
  simp [unitDisk]

lemma pair_comp {U V W : Set ℂ} {f g F G : ℂ → ℂ}
    (h : BiholomorphicPair U V f g) (H : BiholomorphicPair V W F G) :
    BiholomorphicPair U W (F ∘ f) (g ∘ G) := by
  rcases h with ⟨hf, hg, hfm, hgm, hl, hr⟩
  rcases H with ⟨hF, hG, hFm, hGm, hL, hR⟩
  refine ⟨⟨hf.1, fun z hz => (hF.2 _ (hfm hz)).comp z (hf.2 z hz)⟩,
    ⟨hG.1, fun z hz => (hg.2 _ (hGm hz)).comp z (hG.2 z hz)⟩,
    hFm.comp hfm, hgm.comp hGm, ?_, ?_⟩
  · intro z hz
    simp only [Function.comp_apply, hL (hfm hz), hl hz]
  · intro z hz
    simp only [Function.comp_apply, hr (hGm hz), hR hz]

lemma pair_symm {U V : Set ℂ} {f g : ℂ → ℂ} (h : BiholomorphicPair U V f g) :
    BiholomorphicPair V U g f :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

lemma biholomorphism_congr {U V : Set ℂ} {f F : ℂ → ℂ}
    (h : IsBiholomorphism U V f) (he : EqOn f F U) : IsBiholomorphism U V F := by
  obtain ⟨g, hf, hg, hm, hgm, hl, hr⟩ := h
  refine ⟨g, ⟨hf.1, fun z hz => ?_⟩, hg, ?_, hgm, ?_, ?_⟩
  · apply (hf.2 z hz).congr_of_eventuallyEq
    filter_upwards [hf.1.mem_nhds hz] with w hw
    exact (he hw).symm
  · intro z hz
    rw [← he hz]
    exact hm hz
  · intro z hz
    rw [← he hz]
    exact hl hz
  · intro w hw
    rw [← he (hgm hw)]
    exact hr hw

theorem disk_classification :
    Specs.D12Complex.Ch10.HalfplaneAutomorphisms.disk_classification_type := by
  intro f
  constructor
  · intro hf
    rw [unitDisk_eq_ball] at hf
    obtain ⟨⟨a,c⟩, ⟨ha,hc,he⟩, _⟩ := DiskAutomorphisms.classification f hf
    refine ⟨a, c.arg, mem_ball_zero_iff.mp ha, ?_⟩
    have hc' : Complex.exp ((c.arg : ℂ) * Complex.I) = c := by
      simpa [hc] using Complex.norm_mul_exp_arg_mul_I c
    simpa only [unitDisk_eq_ball, hc'] using he
  · rintro ⟨a, θ, ha, he⟩
    have hc : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
      simp [Complex.norm_exp]
    have h := DiskAutomorphisms.rotation_phi_automorphism a
      (mem_ball_zero_iff.mpr ha) _ hc
    rw [← unitDisk_eq_ball] at h
    exact biholomorphism_congr h he.symm

theorem imaginary_part :
    Specs.D12Complex.Ch10.HalfplaneAutomorphisms.imaginary_part_type := by
  intro M z
  simp only [realFraction, Complex.div_im, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im,
    Complex.mul_im, add_zero, Matrix.det_fin_two,
    ← Complex.normSq_eq_norm_sq]
  ring

theorem denominator_ne_zero :
    Specs.D12Complex.Ch10.HalfplaneAutomorphisms.denominator_ne_zero_type := by
  intro M hM z hz he
  have hi := congrArg Complex.im he
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.zero_im] at hi
  have hc : M 1 0 = 0 := (mul_eq_zero.mp hi).resolve_right (ne_of_gt hz)
  have hd : M 1 1 = 0 := by
    simpa [hc] using congrArg Complex.re he
  exact hM (by simp [Matrix.det_fin_two, hc, hd])

lemma mapsTo_of_positive (M : RealCoefficients) (hM : 0 < M.det) :
    MapsTo (realFraction M) upperHalfPlane upperHalfPlane := by
  intro z hz
  change 0 < (realFraction M z).im
  rw [imaginary_part]
  exact div_pos (mul_pos hM hz)
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (denominator_ne_zero M hM.ne' z hz)))

lemma realFraction_holomorphic (M : RealCoefficients) (hM : M.det ≠ 0) :
    HolomorphicOn upperHalfPlane (realFraction M) := by
  refine ⟨isOpen_lt continuous_const Complex.continuous_im, fun z hz => ?_⟩
  exact (differentiableAt_id.const_mul _ |>.add_const _).div
    (differentiableAt_id.const_mul _ |>.add_const _)
    (denominator_ne_zero M hM z hz)

lemma inverse_det (M : RealCoefficients) :
    (!![M 1 1, -M 0 1; -M 1 0, M 0 0] : RealCoefficients).det = M.det := by
  simp [Matrix.det_fin_two]
  ring

lemma inverse_fraction (M : RealCoefficients) (hM : 0 < M.det)
    (z : ℂ) (hz : z ∈ upperHalfPlane) :
    realFraction !![M 1 1, -M 0 1; -M 1 0, M 0 0] (realFraction M z) = z := by
  have hd := denominator_ne_zero M hM.ne' z hz
  have hi := denominator_ne_zero _ (by rw [inverse_det]; exact hM.ne')
    (realFraction M z) (mapsTo_of_positive M hM hz)
  dsimp [realFraction] at hi ⊢
  push_cast at hi ⊢
  rw [div_eq_iff hi]
  simp only [div_eq_mul_inv]
  have hcancel := mul_inv_cancel₀ hd
  linear_combination ((M 0 0 : ℂ) * z + M 0 1) * hcancel

theorem positive_biholomorphicPair :
    Specs.D12Complex.Ch10.HalfplaneAutomorphisms.positive_biholomorphicPair_type := by
  intro M hM
  have hI : 0 < (!![M 1 1, -M 0 1; -M 1 0, M 0 0] : RealCoefficients).det := by
    rw [inverse_det]; exact hM
  refine ⟨realFraction_holomorphic M hM.ne', realFraction_holomorphic _ hI.ne',
    mapsTo_of_positive M hM, mapsTo_of_positive _ hI,
    fun z hz => inverse_fraction M hM z hz, ?_⟩
  intro z hz
  have h := inverse_fraction _ hI z hz
  have he : (!![M 0 0, M 0 1; M 1 0, M 1 1] : RealCoefficients) = M := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  simpa [he] using h

/-- Every unit rotation has a unit square root, obtained without a choice of
boundary values of the automorphism. -/
lemma unit_square_root (c : ℂ) (hc : ‖c‖ = 1) :
    ∃ e : ℂ, ‖e‖ = 1 ∧ e ^ 2 = c := by
  refine ⟨Complex.exp (((c.arg / 2 : ℝ) : ℂ) * Complex.I), ?_, ?_⟩
  · simp [Complex.norm_exp]
  · rw [pow_two, ← Complex.exp_add]
    have he : (((c.arg / 2 : ℝ) : ℂ) * Complex.I) +
        (((c.arg / 2 : ℝ) : ℂ) * Complex.I) = (c.arg : ℂ) * Complex.I := by
      push_cast; ring
    rw [he]
    simpa [hc] using Complex.norm_mul_exp_arg_mul_I c

lemma rotation_lift (c : ℂ) (hc : ‖c‖ = 1) :
    ∃ s t : ℝ, s ^ 2 + t ^ 2 = 1 ∧
      ∀ z ∈ upperHalfPlane,
        cayley (realFraction !![s,t;-t,s] z) = c * cayley z := by
  obtain ⟨e, he, hec⟩ := unit_square_root c hc
  have hst : e.re ^ 2 + e.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq e
    simpa [Complex.normSq_apply, he, pow_two] using h
  refine ⟨e.re, e.im, hst, fun z hz => ?_⟩
  have hdet : (0 : ℝ) < (!![e.re,e.im;-e.im,e.re] : RealCoefficients).det := by
    simpa [Matrix.det_fin_two, sub_neg_eq_add, ← pow_two] using hst ▸ zero_lt_one
  have hd := denominator_ne_zero _ hdet.ne' z hz
  have hp := ElementaryMaps.cayley_denominator (mapsTo_of_positive _ hdet hz)
  have hz' := ElementaryMaps.cayley_denominator hz
  have hce : c = ((e.re : ℂ) + (e.im : ℂ) * Complex.I) ^ 2 := by
    rw [Complex.re_add_im]; exact hec.symm
  rw [hce]
  dsimp [cayley, realFraction] at hd hp ⊢
  push_cast at hd hp ⊢
  rw [div_sub' hd, div_add' _ _ _ hd, div_div_div_cancel_right₀ hd]
  rw [← mul_div_assoc, div_eq_div_iff _ hz']
  · apply Complex.ext
    · simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im,
        Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
      linear_combination (-e.re * (z.re^2-z.im^2+1) + 2*e.im*z.re*z.im) * hst
    · simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im,
        Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
      linear_combination (-e.im * (z.re^2-z.im^2+1) - 2*e.re*z.re*z.im) * hst
  · intro hzero
    apply hp
    rw [div_add' _ _ _ hd, hzero, zero_div]


lemma exists_real_parameters (f : ℂ → ℂ)
    (hf : IsBiholomorphism upperHalfPlane upperHalfPlane f) :
    ∃ M : RealCoefficients, 0 < M.det ∧ EqOn f (realFraction M) upperHalfPlane := by
  obtain ⟨finv, hfp⟩ := hf
  have hI : Complex.I ∈ upperHalfPlane := by simp [upperHalfPlane]
  let u := (f Complex.I).re
  let v := (f Complex.I).im
  have hv : 0 < v := hfp.2.2.1 hI
  let A : RealCoefficients := !![v,u;0,1]
  let B : RealCoefficients := !![1,-u;0,v]
  have hA : BiholomorphicPair upperHalfPlane upperHalfPlane (realFraction A)
      (realFraction B) := by
    simpa [A, B] using positive_biholomorphicPair A
      (by simpa [A, Matrix.det_fin_two] using hv)
  have hB (z : ℂ) : realFraction B z = (z - (u : ℂ)) / (v : ℂ) := by
    simp [B, realFraction, sub_eq_add_neg]
  let g := realFraction B ∘ f
  have hgp := pair_comp hfp (pair_symm hA)
  have hgI : g Complex.I = Complex.I := by
    change realFraction B (f Complex.I) = Complex.I
    rw [hB, div_eq_iff (Complex.ofReal_ne_zero.mpr hv.ne')]
    apply Complex.ext <;> simp [u, v]
  have hC := ElementaryMaps.cayley_biholomorphicPair
  have hK := pair_comp (pair_comp (pair_symm hC) hgp) hC
  have hK0 : (cayley ∘ (g ∘ cayleyInverse)) 0 = 0 := by
    change cayley (g (cayleyInverse 0)) = 0
    rw [show cayleyInverse 0 = Complex.I by simp [cayleyInverse], hgI]
    simp [cayley]
  rw [unitDisk_eq_ball] at hK
  obtain ⟨c,hc,he⟩ := DiskAutomorphisms.rotation_of_pair_fix_zero hK hK0
  obtain ⟨s,t,hst,hlift⟩ := rotation_lift c hc
  let R : RealCoefficients := !![s,t;-t,s]
  have hR : 0 < R.det := by
    rw [Matrix.det_fin_two]
    change 0 < s*s-t*(-t)
    nlinarith [hst]
  have hg (z : ℂ) (hz : z ∈ upperHalfPlane) : g z = realFraction R z := by
    have hcz : cayley (g z) = c * cayley z := by
      have h := he (show cayley z ∈ ball (0 : ℂ) 1 by
        rw [← unitDisk_eq_ball]; exact ElementaryMaps.cayley_mapsTo hz)
      simpa only [g, Function.comp_apply, ElementaryMaps.cayley_left_inverse hz] using h
    have hcR := hlift z hz
    calc
      g z = cayleyInverse (cayley (g z)) :=
        (ElementaryMaps.cayley_left_inverse (hgp.2.2.1 hz)).symm
      _ = cayleyInverse (cayley (realFraction R z)) := by rw [hcz, hcR]
      _ = realFraction R z :=
        ElementaryMaps.cayley_left_inverse (mapsTo_of_positive R hR hz)
  refine ⟨!![v*s-u*t, v*t+u*s; -t,s], ?_, fun z hz => ?_⟩
  · have heq : (!![v*s-u*t, v*t+u*s; -t,s] : RealCoefficients).det = v := by
      rw [Matrix.det_fin_two]
      change (v*s-u*t)*s-(v*t+u*s)*(-t) = v
      linear_combination v * hst
    rw [heq]
    exact hv
  · have hn := hg z hz
    change realFraction B (f z) = realFraction R z at hn
    rw [hB] at hn
    have hfz : f z = (u : ℂ) + (v : ℂ) * realFraction R z := by
      have h := (div_eq_iff (Complex.ofReal_ne_zero.mpr hv.ne')).mp hn
      linear_combination h
    rw [hfz]
    have hd := denominator_ne_zero R hR.ne' z hz
    dsimp [realFraction, R] at hd ⊢
    push_cast at hd ⊢
    rw [← mul_div_assoc, add_div' _ _ _ hd]
    congr 1; ring

theorem classification :
    Specs.D12Complex.Ch10.HalfplaneAutomorphisms.classification_type := by
  intro f
  constructor
  · exact exists_real_parameters f
  · rintro ⟨M,hM,he⟩
    exact biholomorphism_congr ⟨_, positive_biholomorphicPair M hM⟩ he.symm

private def complexMatrix (M : RealCoefficients) : Mobius.Coefficients :=
  fun i j => (M i j : ℂ)

private lemma complexMatrix_regular (M : RealCoefficients) (hM : M.det ≠ 0) :
    Mobius.Regular (complexMatrix M) := by
  change (complexMatrix M).det ≠ 0
  simpa only [Matrix.det_fin_two, complexMatrix, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, ne_eq, Complex.ofReal_eq_zero] using hM

private lemma complexMatrix_finite (M : RealCoefficients) (hM : M.det ≠ 0)
    (z : ℂ) (hz : z ∈ upperHalfPlane) :
    Mobius.mobiusMap (complexMatrix M) (sphereFinite z) = sphereFinite (realFraction M z) :=
  Mobius.mobiusMap_finite _ z (denominator_ne_zero M hM z hz)

private lemma finite_ne_of_re_ne {z w : ℂ} (h : z.re ≠ w.re) :
    sphereFinite z ≠ sphereFinite w := by
  intro he
  exact h (congrArg Complex.re (sphereFinite_injective he))

theorem real_scalar_iff :
    Specs.D12Complex.Ch10.HalfplaneAutomorphisms.real_scalar_iff_type := by
  intro M N hM hN
  constructor
  · intro he
    have hm := complexMatrix_regular M hM
    have hn := complexMatrix_regular N hN
    have hmap (z : ℂ) (hz : z ∈ upperHalfPlane) :
        Mobius.mobiusMap (complexMatrix M) (sphereFinite z) =
          Mobius.mobiusMap (complexMatrix N) (sphereFinite z) := by
      rw [complexMatrix_finite M hM z hz, complexMatrix_finite N hN z hz, he hz]
    have hmaps : Mobius.mobiusMap (complexMatrix M) = Mobius.mobiusMap (complexMatrix N) := by
      apply Mobius.mobiusMap_eq_of_triple _ _ hm hn
        (sphereFinite Complex.I) (sphereFinite (1+Complex.I)) (sphereFinite (2+Complex.I))
      · apply finite_ne_of_re_ne; norm_num
      · apply finite_ne_of_re_ne; norm_num
      · apply finite_ne_of_re_ne; norm_num
      · exact hmap _ (by simp [upperHalfPlane])
      · exact hmap _ (by simp [upperHalfPlane])
      · exact hmap _ (by simp [upperHalfPlane])
    obtain ⟨k,hk,hke⟩ := (Mobius.mobiusMap_eq_iff _ _ hm hn).mp hmaps
    have hnentry : ∃ i j, N i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hN (by simp [Matrix.det_fin_two, h])
    obtain ⟨i,j,hij⟩ := hnentry
    have heij : (M i j : ℂ) = k * (N i j : ℂ) := congrArg (fun A => A i j) hke
    have hki : k.im = 0 := by
      have h := congrArg Complex.im heij
      simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero,
        zero_add] at h
      exact (mul_eq_zero.mp h.symm).resolve_right hij
    refine ⟨k.re, ?_, ?_⟩
    · intro h
      apply hk
      exact Complex.ext (by simpa using h) (by simpa using hki)
    · ext i j
      have h : (M i j : ℂ) = k * (N i j : ℂ) := congrArg (fun A => A i j) hke
      simpa using congrArg Complex.re h
  · rintro ⟨r,hr,rfl⟩
    intro z _
    dsimp [realFraction]
    simp only [Complex.ofReal_mul]
    rw [show (r : ℂ) * (N 0 0 : ℂ) * z + (r : ℂ) * N 0 1 =
      (r : ℂ) * ((N 0 0 : ℂ) * z + N 0 1) by ring]
    rw [show (r : ℂ) * (N 1 0 : ℂ) * z + (r : ℂ) * N 1 1 =
      (r : ℂ) * ((N 1 0 : ℂ) * z + N 1 1) by ring]
    exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hr)

end D12Complex.HalfplaneAutomorphisms
