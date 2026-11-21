import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.ExponentialTypePolynomialDivision
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.DistributionPaleyWiener
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! Polynomial division preserves exact compact convex exponential type.
We use Jensen's formula on one-dimensional complex lines. The directions may
be complex: their bounded displacement on the unit circle contributes only a
constant to the support-function bound. -/

noncomputable section
namespace ExpandedFA.Fourier.ExponentialTypePolynomialDivision
open Set Metric Filter Real MeromorphicOn
open ExpandedFA.Fourier.PaleyWiener ExpandedFA.Fourier.DistributionPaleyWiener
lemma log_norm_center_le_circleAverage {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g univ) (h0 : g 0 ≠ 0) :
    Real.log ‖g 0‖ ≤ circleAverage (fun t => Real.log ‖g t‖) 0 1 := by
  have ha : AnalyticOnNhd ℂ g (closedBall 0 |(1 : ℝ)|) := hg.mono (subset_univ _)
  rw [ha.circleAverage_log_norm one_ne_zero h0]
  apply le_add_of_nonneg_left
  apply finsum_nonneg
  intro u
  by_cases hz : u = 0
  · subst u
    rw [ha.divisor_apply (by simp), (hg 0 (mem_univ _)).analyticOrderAt_eq_zero.mpr h0]
    simp
  by_cases hu : u ∈ closedBall (0 : ℂ) |(1 : ℝ)|
  · apply mul_nonneg
    · exact_mod_cast ha.divisor_nonneg u
    · apply Real.log_nonneg
      have hun : ‖u‖ ≤ 1 := by simpa using hu
      have hp : 0 < ‖u‖ := norm_pos_iff.mpr hz
      simpa using (one_le_inv₀ hp).mpr hun
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

lemma polynomial_mul_center_bound (p : Polynomial ℂ) (hp : p ≠ 0)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g univ) {B : ℝ} (hB : 0 < B)
    (hb : ∀ t : ℂ, ‖t‖ = 1 → ‖p.eval t * g t‖ ≤ B) :
    ‖p.leadingCoeff‖ * ‖g 0‖ ≤ B := by
  by_cases h0 : g 0 = 0
  · simp [h0, hB.le]
  have ha : AnalyticOnNhd ℂ (fun t => p.eval t) univ :=
    analyticOnNhd_id.aeval_polynomial p
  obtain ⟨w, hw⟩ : ∃ w : ℂ, p.eval w ≠ 0 := by
    by_contra! h
    exact hp (Polynomial.funext fun w => by simpa using h w)
  have hpn : ∀ᶠ t in codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|), p.eval t ≠ 0 :=
    codiscreteWithin_mono (subset_univ _)
      (ha.preimage_zero_mem_codiscreteWithin hw (mem_univ _) isConnected_univ)
  have hgn : ∀ᶠ t in codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|), g t ≠ 0 :=
    codiscreteWithin_mono (subset_univ _)
      (hg.preimage_zero_mem_codiscreteWithin h0 (mem_univ _) isConnected_univ)
  let f : ℂ → ℂ := fun t => (p.eval t * g t) / (B : ℂ)
  have hf : AnalyticOnNhd ℂ f univ := (ha.mul hg).div_const
  have hi := (ha.mono (subset_univ _)).meromorphicOn.circleIntegrable_log_norm (c := 0) (R := 1)
  have hj := (hg.mono (subset_univ _)).meromorphicOn.circleIntegrable_log_norm (c := 0) (R := 1)
  have hk := (hf.mono (subset_univ _)).meromorphicOn.circleIntegrable_log_norm (c := 0) (R := 1)
  have heq : circleAverage (fun t => Real.log ‖f t‖) 0 1 =
      circleAverage (fun t => Real.log ‖p.eval t‖) 0 1 +
      circleAverage (fun t => Real.log ‖g t‖) 0 1 - Real.log B := by
    calc
      _ = circleAverage (fun t => Real.log ‖p.eval t‖ + Real.log ‖g t‖ - Real.log B) 0 1 := by
        apply circleAverage_congr_codiscreteWithin _ one_ne_zero
        filter_upwards [hpn, hgn] with t hpt hgt
        simp only [f, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
        rw [Real.log_div (mul_ne_zero (norm_ne_zero_iff.mpr hpt) (norm_ne_zero_iff.mpr hgt)) hB.ne',
          Real.log_mul (norm_ne_zero_iff.mpr hpt) (norm_ne_zero_iff.mpr hgt)]
      _ = _ := by
        rw [circleAverage_fun_sub (f₁ := fun t => Real.log ‖p.eval t‖ + Real.log ‖g t‖)
          (f₂ := fun _ : ℂ => Real.log B) (hi.add hj) (circleIntegrable_const _ _ _),
          circleAverage_fun_add hi hj, circleAverage_const]
  have hav : circleAverage (fun t => Real.log ‖f t‖) 0 1 ≤ 0 := by
    apply circleAverage_mono_on_of_le_circle hk
    intro t ht
    apply Real.log_nonpos (norm_nonneg _)
    have ht' : ‖t‖ = 1 := by simpa using ht
    dsimp [f]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    exact (div_le_one hB).mpr (hb t ht')
  have hma : Real.log ‖p.leadingCoeff‖ ≤
      circleAverage (fun t => Real.log ‖p.eval t‖) 0 1 := by
    change _ ≤ p.logMahlerMeasure
    rw [Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
    exact Real.log_le_log (norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))
      p.leadingCoeff_le_mahlerMeasure
  have hlog : Real.log (‖p.leadingCoeff‖ * ‖g 0‖) ≤ Real.log B := by
    rw [Real.log_mul (norm_ne_zero_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))
      (norm_ne_zero_iff.mpr h0)]
    linarith [log_norm_center_le_circleAverage hg h0]
  have hlc : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  exact (Real.log_le_log_iff (mul_pos hlc (norm_pos_iff.mpr h0)) hB).mp hlog

lemma polynomial_prod_top {ι : Type*} (s : Finset ι) (q : ι → Polynomial ℂ)
    (n : ι → ℕ) (h : ∀ i ∈ s, (q i).natDegree ≤ n i) :
    (∏ i ∈ s, q i).natDegree ≤ ∑ i ∈ s, n i ∧
    (∏ i ∈ s, q i).coeff (∑ i ∈ s, n i) = ∏ i ∈ s, (q i).coeff (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨hd, hc⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hqa := h a (Finset.mem_insert_self a s)
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add hqa hd),
      (Polynomial.coeff_mul_add_eq_of_natDegree_le hqa hd).trans (by rw [hc])⟩

def linePolynomial {σ : Type*} (P : MvPolynomial σ ℂ) (z v : σ → ℂ) : Polynomial ℂ :=
  P.eval₂ Polynomial.C (fun j => Polynomial.C (z j) + Polynomial.C (v j) * Polynomial.X)

lemma line_monomial_top {σ : Type*} (α : σ →₀ ℕ) (c : ℂ) (z v : σ → ℂ) :
    (linePolynomial (MvPolynomial.monomial α c) z v).natDegree ≤ α.sum (fun _ e => e) ∧
    (linePolynomial (MvPolynomial.monomial α c) z v).coeff (α.sum (fun _ e => e)) =
      c * α.prod (fun j e => v j ^ e) := by
  classical
  have hlin (j : σ) :
      (Polynomial.C (z j) + Polynomial.C (v j) * Polynomial.X).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  have hpow (j : σ) (e : ℕ) :
      ((Polynomial.C (z j) + Polynomial.C (v j) * Polynomial.X) ^ e).natDegree ≤ e := by
    exact Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left e (hlin j))
  have hcoeff (j : σ) (e : ℕ) :
      ((Polynomial.C (z j) + Polynomial.C (v j) * Polynomial.X) ^ e).coeff e = v j ^ e := by
    simpa using (Polynomial.coeff_pow_of_natDegree_le (m := e) (hlin j))
  dsimp [linePolynomial]
  rw [MvPolynomial.eval₂_monomial]
  change (Polynomial.C c * ∏ j ∈ α.support,
    (Polynomial.C (z j) + Polynomial.C (v j) * Polynomial.X) ^ α j).natDegree ≤ _ ∧ _
  obtain ⟨hd, hc⟩ := polynomial_prod_top α.support
    (fun j => (Polynomial.C (z j) + Polynomial.C (v j) * Polynomial.X) ^ α j)
    (fun j => α j) (fun j _ => hpow j (α j))
  constructor
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hd
  · simp only [Polynomial.coeff_C_mul, Finsupp.prod, Finsupp.sum]
    rw [hc]
    simp only [hcoeff]

lemma linePolynomial_natDegree_le {σ : Type*} (P : MvPolynomial σ ℂ) (z v : σ → ℂ) :
    (linePolynomial P z v).natDegree ≤ P.totalDegree := by
  classical
  have hsum : linePolynomial P z v = ∑ α ∈ P.support,
      linePolynomial (MvPolynomial.monomial α (P.coeff α)) z v := by
    conv_lhs => rw [P.as_sum]
    simp only [linePolynomial, MvPolynomial.eval₂_sum]
  rw [hsum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro α hα
  exact (line_monomial_top α _ z v).1 |>.trans (MvPolynomial.le_totalDegree hα)

lemma linePolynomial_coeff_top {σ : Type*} (P : MvPolynomial σ ℂ) (z v : σ → ℂ) :
    (linePolynomial P z v).coeff P.totalDegree =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  classical
  have hsum : linePolynomial P z v = ∑ α ∈ P.support,
      linePolynomial (MvPolynomial.monomial α (P.coeff α)) z v := by
    conv_lhs => rw [P.as_sum]
    simp only [linePolynomial, MvPolynomial.eval₂_sum]
  rw [hsum, Polynomial.finsetSum_coeff]
  rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α hα
  have hle := MvPolynomial.le_totalDegree hα
  by_cases heq : α.sum (fun _ e => e) = P.totalDegree
  · have heq' : α.degree = P.totalDegree := heq
    simp only [heq', ite_true, MvPolynomial.eval_monomial]
    simpa only [heq] using (line_monomial_top α (P.coeff α) z v).2
  · have hlt : α.sum (fun _ e => e) < P.totalDegree := lt_of_le_of_ne hle heq
    have heq' : α.degree ≠ P.totalDegree := heq
    simp only [heq', ite_false]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((line_monomial_top α _ z v).1.trans_lt hlt)

lemma homogeneousComponent_totalDegree_ne_zero {σ : Type*} (P : MvPolynomial σ ℂ)
    (hp : P ≠ 0) : MvPolynomial.homogeneousComponent P.totalDegree P ≠ 0 := by
  classical
  obtain ⟨α, hα, hm⟩ := P.support.exists_mem_eq_sup (MvPolynomial.support_nonempty.mpr hp)
    (fun α => α.sum (fun _ e => e))
  intro h
  have hc := congrArg (fun Q : MvPolynomial σ ℂ => Q.coeff α) h
  have hm' : α.degree = P.totalDegree := hm.symm
  simp only [MvPolynomial.coeff_homogeneousComponent, hm', ite_true, AddMonoidAlgebra.coeff_zero] at hc
  exact (MvPolynomial.mem_support_iff.mp hα) hc

lemma exists_linePolynomial_leadingCoeff {σ : Type*} (P : MvPolynomial σ ℂ) (hp : P ≠ 0) :
    ∃ (v : σ → ℂ) (a : ℂ), a ≠ 0 ∧
      ∀ z : σ → ℂ, (linePolynomial P z v).leadingCoeff = a := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : σ → ℂ,
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent P.totalDegree P) ≠ 0 := by
    by_contra! h
    exact homogeneousComponent_totalDegree_ne_zero P hp
      (MvPolynomial.funext fun v => by simpa using h v)
  refine ⟨v, _, hv, fun z => ?_⟩
  have hc := linePolynomial_coeff_top P z v
  have hd : (linePolynomial P z v).natDegree = P.totalDegree :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (linePolynomial_natDegree_le P z v)
      (hc ▸ hv)
  rw [Polynomial.leadingCoeff, hd, hc]

lemma linePolynomial_eval {σ : Type*} (P : MvPolynomial σ ℂ) (z v : σ → ℂ) (t : ℂ) :
    (linePolynomial P z v).eval t = MvPolynomial.eval (fun j => z j + t * v j) P := by
  change Polynomial.evalRingHom t (P.eval₂ Polynomial.C _) = _
  rw [MvPolynomial.eval₂_comp_left]
  simp only [Function.comp_def, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  have hcomp : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
    ext c
    simp
  rw [hcomp, MvPolynomial.eval₂_id]
  change MvPolynomial.eval (fun j => z j + v j * t) P = _
  have heq : (fun j => z j + v j * t) = (fun j => z j + t * v j) := by
    funext j
    ring
  rw [heq]

lemma supportFunction_imaginary_add_le {d : ℕ} {K : Set (Euclidean d)}
    (hne : K.Nonempty) (hK : IsCompact K) {R : ℝ} (hR : 0 ≤ R)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (z w : ComplexEuclidean d) :
    supportFunction K (imaginaryPart (z + w)) ≤
      supportFunction K (imaginaryPart z) + R * ‖w‖ := by
  have hadd : imaginaryPart (z + w) = imaginaryPart z + imaginaryPart w := by
    ext j
    simp [PaleyWiener.imaginaryPart]
  rw [hadd]
  apply csSup_le (hne.image _)
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  rw [inner_add_right]
  apply add_le_add (inner_le_supportFunction hK hx _) _
  calc
    inner ℝ x (imaginaryPart w) ≤ ‖x‖ * ‖imaginaryPart w‖ := real_inner_le_norm _ _
    _ ≤ R * ‖w‖ := mul_le_mul (hKR x hx) (norm_imaginaryPart_le w) (norm_nonneg _) hR

lemma growth_bound_on_translates {d : ℕ} {K : Set (Euclidean d)}
    (hne : K.Nonempty) (hK : IsCompact K) {R A C : ℝ} (hR : 0 ≤ R)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hA : 0 ≤ A) (hC : 0 ≤ C) (M : ℕ)
    (F : ComplexEuclidean d → ℂ)
    (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ M *
      Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)))
    (z w : ComplexEuclidean d) (hw : ‖w‖ ≤ A) :
    ‖F (z + w)‖ ≤
      (C * (1 + A) ^ M * Real.exp (2 * Real.pi * R * A)) *
        (1 + ‖z‖) ^ M * Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)) := by
  have hn : 1 + ‖z + w‖ ≤ (1 + A) * (1 + ‖z‖) := by
    have hzw := norm_add_le z w
    nlinarith [mul_nonneg hA (norm_nonneg z)]
  have hs : supportFunction K (imaginaryPart (z + w)) ≤
      supportFunction K (imaginaryPart z) + R * A :=
    (supportFunction_imaginary_add_le hne hK hR hKR z w).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hw hR))
  calc
    _ ≤ C * ((1 + A) * (1 + ‖z‖)) ^ M *
        Real.exp (2 * Real.pi * (supportFunction K (imaginaryPart z) + R * A)) := by
      apply (hb (z + w)).trans
      gcongr
    _ = _ := by
      rw [mul_pow, mul_add, Real.exp_add]
      ring

/-- Entire polynomial division preserves the original type K, even for
constant polynomials, dimension zero, and compact sets with empty interior. -/
theorem polynomial_division :
    Specs.ExpandedFA.Fourier.ExponentialTypePolynomialDivision.polynomialDivisionType := by
  intro d K hne hK _hconv P hP G hG hPG
  obtain ⟨v0, a, ha, hlead⟩ := exists_linePolynomial_leadingCoeff P hP
  let v : ComplexEuclidean d := WithLp.toLp 2 v0
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨M, C, hC, hb⟩ := hPG
  let F : ComplexEuclidean d → ℂ := fun z => MvPolynomial.eval (fun j => z j) P * G z
  have hb' (z : ComplexEuclidean d) :
      ‖F z‖ ≤ (C + 1) * (1 + ‖z‖) ^ M *
        Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)) := by
    apply (hb z).trans
    gcongr
    linarith
  let D : ℝ := (C + 1) * (1 + ‖v‖) ^ M * Real.exp (2 * Real.pi * R * ‖v‖)
  have hD : 0 < D := by dsimp [D]; positivity
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  refine ⟨M, D / ‖a‖, (div_pos hD ha').le, fun z => ?_⟩
  let p := linePolynomial P (fun j => z j) v0
  have hp : p ≠ 0 := by
    intro hp
    have he := hlead (fun j => z j)
    change p.leadingCoeff = a at he
    rw [hp, Polynomial.leadingCoeff_zero] at he
    exact ha he.symm
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => G (z + t • v)) univ := by
    have hd : Differentiable ℂ (fun t : ℂ => G (z + t • v)) :=
      hG.comp ((differentiable_id.smul_const v).const_add z)
    exact hd.differentiableOn.analyticOnNhd isOpen_univ
  have hB : 0 < D * (1 + ‖z‖) ^ M *
      Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)) := by positivity
  have hlocal := polynomial_mul_center_bound p hp hg hB (fun t ht => by
    have hw : ‖t • v‖ ≤ ‖v‖ := by simp [norm_smul, ht]
    have h := growth_bound_on_translates hne hK hR.le hKR (norm_nonneg v)
      (by linarith : 0 ≤ C + 1) M F hb' z (t • v) hw
    simpa only [p, linePolynomial_eval, F, D, v, PiLp.add_apply, PiLp.smul_apply,
      PiLp.toLp_apply, smul_eq_mul] using h)
  have hcenter : ‖a‖ * ‖G z‖ ≤ D * (1 + ‖z‖) ^ M *
      Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)) := by
    simpa only [p, hlead, zero_smul, add_zero] using hlocal
  calc
    ‖G z‖ ≤ (D * (1 + ‖z‖) ^ M *
        Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z))) / ‖a‖ :=
      (le_div_iff₀ ha').mpr (by simpa only [mul_comm] using hcenter)
    _ = _ := by ring

end ExpandedFA.Fourier.ExponentialTypePolynomialDivision
