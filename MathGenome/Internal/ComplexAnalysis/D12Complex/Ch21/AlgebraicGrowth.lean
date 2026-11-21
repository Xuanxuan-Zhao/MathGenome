import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.AlgebraicGrowth
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SingularityGrowth
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SingularityCoefficients
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.Laurent
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open Filter Asymptotics Polynomial Bornology
open scoped Topology ENNReal NNReal
open Finset

namespace D12Complex.AlgebraicGrowth
open D12Complex.AlgebraicCovering

-- The norm estimate with a common bound on the normalized coefficients.
theorem root_norm_le_of_coeff_bound {p : Polynomial ℂ} {w : ℂ} {B : ℝ}
    (hp : p ≠ 0) (hw : p.IsRoot w) (hB : 0 ≤ B)
    (hcoeff : ∀ j < p.natDegree, ‖p.coeff j‖ / ‖p.leadingCoeff‖ ≤ B) :
    ‖w‖ ≤ 1 + B := by
  have hs : Finset.sup (Finset.range p.natDegree) (fun j => ‖p.coeff j‖₊) /
      ‖p.leadingCoeff‖₊ ≤ (NNReal.mk B hB) := by
    have hl : (0 : ℝ≥0) < ‖p.leadingCoeff‖₊ := by simpa using hp
    apply (div_le_iff₀ hl).2
    apply Finset.sup_le
    intro j hj
    change ‖p.coeff j‖ ≤ B * ‖p.leadingCoeff‖
    exact (div_le_iff₀ (norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))).1
      (hcoeff j (Finset.mem_range.mp hj))
  have hcb : p.cauchyBound ≤ ((NNReal.mk B hB) : ℝ≥0) + 1 := by
    unfold Polynomial.cauchyBound
    simpa only [add_comm] using (add_le_add_right hs 1)
  have ht := (hw.norm_lt_cauchyBound hp).le.trans hcb
  change ‖w‖₊ ≤ ((NNReal.mk B hB) : ℝ≥0) + 1 at ht
  have hr : ‖w‖ ≤ B + 1 := ht
  simpa only [add_comm B 1] using hr

theorem root_norm_le_of_coeff_quotient_bound {p : Polynomial ℂ} {w : ℂ} {B : ℝ}
    (hp : p ≠ 0) (hw : p.IsRoot w) (hB : 0 ≤ B)
    (hcoeff : ∀ j < p.natDegree, ‖p.coeff j / p.leadingCoeff‖ ≤ B) :
    ‖w‖ ≤ 1 + B := by
  apply root_norm_le_of_coeff_bound hp hw hB
  simpa only [norm_div] using hcoeff

-- Specialized polynomial in the original bivariate polynomial's w-variable.
theorem fiber_root_norm_le {P : Polynomial (Polynomial ℂ)} {z w : ℂ} {B : ℝ}
    (hlead : P.leadingCoeff.eval z ≠ 0)
    (hw : (P.map (Polynomial.evalRingHom z)).IsRoot w) (hB : 0 ≤ B)
    (hcoeff : ∀ j < P.natDegree, ‖(P.coeff j).eval z / P.leadingCoeff.eval z‖ ≤ B) :
    ‖w‖ ≤ 1 + B := by
  have hl : (P.map (Polynomial.evalRingHom z)).leadingCoeff = P.leadingCoeff.eval z :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlead
  have hdeg : (P.map (Polynomial.evalRingHom z)).natDegree = P.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlead
  apply root_norm_le_of_coeff_quotient_bound
    (Polynomial.leadingCoeff_ne_zero.mp (hl ▸ hlead)) hw hB
  intro j hj
  simpa only [Polynomial.coeff_map, Polynomial.coe_evalRingHom, hl] using
    hcoeff j (hdeg ▸ hj)

theorem monic_root_norm_le {p : Polynomial ℂ} {w : ℂ} {B : ℝ}
    (hp : p.Monic) (hw : p.IsRoot w) (hB : 0 ≤ B)
    (hcoeff : ∀ j < p.natDegree, ‖p.coeff j‖ ≤ B) :
    ‖w‖ ≤ 1 + B := by
  apply root_norm_le_of_coeff_bound hp.ne_zero hw hB
  simpa only [hp.leadingCoeff, norm_one, div_one] using hcoeff

-- An explicit monic equation, matching the source's root estimate.
theorem monic_equation_root_norm_le {d : ℕ} {b : ℕ → ℂ} {w : ℂ} {B : ℝ}
    (heq : w ^ d + ∑ j ∈ range d, b j * w ^ j = 0)
    (hB : 0 ≤ B) (hb : ∀ j < d, ‖b j‖ ≤ B) : ‖w‖ ≤ 1 + B := by
  classical
  let p : Polynomial ℂ := Polynomial.X ^ d + ∑ j ∈ range d, Polynomial.monomial j (b j)
  have hc (j : ℕ) : p.coeff j = (if d = j then 1 else 0) + (if j < d then b j else 0) := by
    simp [p, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, eq_comm]
  have hcd : p.coeff d = 1 := by simp [hc]
  have hdegree : p.natDegree = d := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ (hcd ▸ one_ne_zero)
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro N hN
    simp [hc, ne_of_lt hN, not_lt_of_ge hN.le]
  have hmonic : p.Monic := by
    change p.coeff p.natDegree = 1
    rw [hdegree, hcd]
  apply monic_root_norm_le hmonic (by simpa [Polynomial.IsRoot, p, Polynomial.eval_finsetSum] using heq) hB
  intro j hj
  rw [hdegree] at hj
  simpa [hc, ne_of_gt hj, hj] using hb j hj

theorem monic_equation_root_norm_le_max {d : ℕ} {b : ℕ → ℂ} {w : ℂ}
    (heq : w ^ d + ∑ j ∈ range d, b j * w ^ j = 0) :
    ‖w‖ ≤ 1 + (↑((range d).sup (fun j => ‖b j‖₊)) : ℝ) := by
  apply monic_equation_root_norm_le heq (NNReal.coe_nonneg _)
  intro j hj
  have ht : ‖b j‖₊ ≤ (range d).sup (fun j => ‖b j‖₊) :=
    Finset.le_sup (f := fun j => ‖b j‖₊) (Finset.mem_range.mpr hj)
  exact ht

theorem monic_equation_root_nnnorm_le_max {d : ℕ} {b : ℕ → ℂ} {w : ℂ}
    (heq : w ^ d + ∑ j ∈ range d, b j * w ^ j = 0) :
    ‖w‖₊ ≤ 1 + (range d).sup (fun j => ‖b j‖₊) :=
  monic_equation_root_norm_le_max heq

open D12Complex.LocalZeroFactorization

lemma coefficient_ratios_of_finite_order
    (P : Polynomial (Polynomial ℂ)) (c : ℂ) (k : ℕ)
    (hk : HasFiniteOrder (fun z => P.leadingCoeff.eval z) c k) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝[≠] c,
      P.leadingCoeff.eval z ≠ 0 ∧
      ∀ j < P.natDegree,
        ‖(P.coeff j).eval z / P.leadingCoeff.eval z‖ ≤ C * ‖z-c‖ ^ (-(k : ℤ)) := by
  obtain ⟨g, hg, hg0, hfactor⟩ := hk
  let B : ℂ → ℝ := fun z => ∑ j ∈ Finset.range P.natDegree, ‖(P.coeff j).eval z / g z‖
  have hB : ContinuousAt B c := by
    apply tendsto_finsetSum
    intro j hj
    exact (((P.coeff j).continuous.continuousAt).div
      ((holomorphicNear_iff_analyticAt g c).mp hg).continuousAt hg0).norm
  have hBnonneg : 0 ≤ B c := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨B c + 1, by positivity, ?_⟩
  have hbound : ∀ᶠ z in 𝓝 c, B z < B c + 1 := hB.eventually_lt_const (by linarith)
  have hgne : ∀ᶠ z in 𝓝 c, g z ≠ 0 :=
    ((holomorphicNear_iff_analyticAt g c).mp hg).continuousAt.eventually_ne hg0
  filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
    hbound.filter_mono nhdsWithin_le_nhds,
    hgne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hBz hgz hzc
  have hz0 : z - c ≠ 0 := sub_ne_zero.mpr hzc
  have hlead : P.leadingCoeff.eval z ≠ 0 := by
    rw [hz]
    exact mul_ne_zero (pow_ne_zero k hz0) hgz
  refine ⟨hlead, fun j hj => ?_⟩
  have hterm : ‖(P.coeff j).eval z / g z‖ ≤ B z := by
    exact Finset.single_le_sum (f := fun i => ‖(P.coeff i).eval z / g z‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hj)
  calc
    ‖(P.coeff j).eval z / P.leadingCoeff.eval z‖ =
      ‖(P.coeff j).eval z / g z‖ * ‖z-c‖ ^ (-(k : ℤ)) := by
        rw [hz, norm_div, norm_mul, norm_pow, norm_div, zpow_neg, zpow_natCast]
        field_simp
    _ ≤ (B c + 1) * ‖z-c‖ ^ (-(k : ℤ)) :=
      mul_le_mul_of_nonneg_right (hterm.trans hBz.le) (zpow_nonneg (norm_nonneg _) _)

lemma polynomial_eval_has_finite_order (a : Polynomial ℂ) (ha : a ≠ 0) (c : ℂ) :
    ∃ k : ℕ, HasFiniteOrder a.eval c k := by
  have hh : HolomorphicNear a.eval c :=
    (holomorphicNear_iff_analyticAt a.eval c).mpr ((AnalyticOnNhd.eval_polynomial a) c (Set.mem_univ c))
  have hn : ¬ ZeroGerm a.eval c := by
    intro hzero
    have hne : ∀ᶠ z in 𝓝[≠] c, a.eval z ≠ 0 :=
      (eventually_codiscrete_iff_forall_eventually_nhdsNE.mp
        (a.eventually_eval_ne_zero_codiscrete ha)) c
    have hz : ∀ᶠ z in 𝓝[≠] c, a.eval z = 0 := hzero.filter_mono nhdsWithin_le_nhds
    exact (hz.and hne).exists.elim fun z hz => hz.2 hz.1
  obtain h | h := local_zero_factorization a.eval c hh
  · exact (hn h.1).elim
  · obtain ⟨k, hk, _⟩ := h.2
    exact ⟨k, hk⟩


lemma finite_parameter_growth
    (P : Polynomial (Polynomial ℂ)) (c : ℂ) (k h : ℕ) (hh : 0 < h)
    (hk : HasFiniteOrder (fun z => P.leadingCoeff.eval z) c k)
    (W : ℂ → ℂ)
    (hW : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (fiber P (c + t^h)).eval (W t) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      ‖W t‖ ≤ C * (‖t‖^(h*k))⁻¹ := by
  obtain ⟨C, hC, hratios⟩ := coefficient_ratios_of_finite_order P c k hk
  have hcomp : Tendsto (fun t : ℂ => c + t^h) (𝓝[≠] (0 : ℂ)) (𝓝[≠] c) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hct : ContinuousAt (fun t : ℂ => c + t^h) 0 := by fun_prop
      simpa [zero_pow (Nat.ne_of_gt hh)] using hct.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq, add_eq_left] using
        pow_ne_zero h ht
  have hnorm : ∀ᶠ t : ℂ in 𝓝 (0 : ℂ), ‖t‖ < (1 : ℝ) := by
    exact continuous_norm.continuousAt.eventually_lt_const (by norm_num)
  refine ⟨C+1, by positivity, ?_⟩
  filter_upwards [hcomp.eventually hratios, hW,
    hnorm.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hrat ht hsmall ht0
  have hflead : (fiber P (c+t^h)).leadingCoeff = P.leadingCoeff.eval (c+t^h) := by
    exact leadingCoeff_map_of_leadingCoeff_ne_zero (Polynomial.evalRingHom _) hrat.1
  have hfdeg : (fiber P (c+t^h)).natDegree = P.natDegree := by
    exact natDegree_map_of_leadingCoeff_ne_zero (Polynomial.evalRingHom _) hrat.1
  have hfnz : fiber P (c+t^h) ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [hflead]
    exact hrat.1
  have hpoweq : ‖c+t^h-c‖ ^ (-(k : ℤ)) = (‖t‖^(h*k))⁻¹ := by
    rw [add_sub_cancel_left, norm_pow, zpow_neg, zpow_natCast, ← pow_mul]
  have hroot : ‖W t‖ ≤ 1 + C * (‖t‖^(h*k))⁻¹ := by
    apply root_norm_le_of_coeff_bound hfnz ht (by positivity)
    intro j hj
    have hj' : j < P.natDegree := hfdeg ▸ hj
    rw [hflead, show (fiber P (c+t^h)).coeff j = (P.coeff j).eval (c+t^h) from coeff_map _ _]
    rw [← norm_div]
    exact hpoweq ▸ hrat.2 j hj'
  have hpos : 0 < ‖t‖^(h*k) := pow_pos (norm_pos_iff.mpr ht0) _
  have hle : ‖t‖^(h*k) ≤ 1 := pow_le_one₀ (norm_nonneg _) hsmall.le
  have hinv : 1 ≤ (‖t‖^(h*k))⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hpos).mpr (by simpa using hle)
  nlinarith

lemma finite_parameter_bounded
    (P : Polynomial (Polynomial ℂ)) (c : ℂ) (h : ℕ) (hh : 0 < h)
    (hc : P.leadingCoeff.eval c ≠ 0) (W : ℂ → ℂ)
    (hW : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (fiber P (c + t^h)).eval (W t) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖W t‖ ≤ C := by
  have hk : HasFiniteOrder (fun z => P.leadingCoeff.eval z) c 0 := by
    refine ⟨fun z => P.leadingCoeff.eval z, ?_, hc, ?_⟩
    · exact (holomorphicNear_iff_analyticAt _ _).mpr
        ((AnalyticOnNhd.eval_polynomial P.leadingCoeff) c (Set.mem_univ c))
    · filter_upwards [] with z
      simp
  simpa only [Nat.mul_zero, pow_zero, inv_one, mul_one] using
    finite_parameter_growth P c 0 h hh hk W hW


lemma degree_le_X_pow_mul {Q A : Polynomial ℂ} (hQ : Q ≠ 0) {L : ℕ}
    (hA : A.natDegree ≤ L) : A.degree ≤ ((X ^ L) * Q).degree := by
  rw [Polynomial.degree_mul, Polynomial.degree_X_pow]
  calc A.degree ≤ (A.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
       _ ≤ (L : WithBot ℕ) := by exact_mod_cast hA
       _ ≤ (L : WithBot ℕ) + Q.degree := by
         have hnonneg : (0 : WithBot ℕ) ≤ Q.degree := by rw [Polynomial.degree_eq_natDegree hQ]; exact_mod_cast Nat.zero_le Q.natDegree
         simpa using add_le_add_right hnonneg (L : WithBot ℕ)

lemma single_rational_growth {Q A : Polynomial ℂ} (hQ : Q ≠ 0) {L : ℕ}
    (hA : A.natDegree ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in cobounded ℂ,
      ‖A.eval z / Q.eval z‖ ≤ C * ‖z‖ ^ L := by
  obtain ⟨C, hC, hbound⟩ := Asymptotics.isBigO_iff'.mp
    (Polynomial.isBigO_cobounded_of_degree_le (degree_le_X_pow_mul hQ hA))
  refine ⟨C, hC, hbound.mono ?_⟩
  intro z hz
  by_cases hq : Q.eval z = 0
  · simp only [hq, div_zero, norm_zero]
    positivity
  · rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hq)).2
    simpa [Polynomial.eval_mul, Polynomial.eval_pow, norm_mul, norm_pow, mul_assoc] using hz

lemma rational_family_growth_at_infinity (a : ℕ → Polynomial ℂ) (d : ℕ)
    (hQ : a d ≠ 0) :
    ∃ (L : ℕ) (C R : ℝ), 0 < C ∧ 0 < R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ∀ j < d,
        ‖(a j).eval z / (a d).eval z‖ ≤ C * ‖z‖ ^ L := by
  let L := (Finset.range d).sup (fun j => (a j).natDegree)
  have h : ∀ j : Fin d, ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in cobounded ℂ,
      ‖(a j).eval z / (a d).eval z‖ ≤ C * ‖z‖ ^ L := by
    intro j
    exact single_rational_growth hQ (Finset.le_sup (f := fun j => (a j).natDegree)
      (Finset.mem_range.mpr j.isLt))
  choose C hCpos hC using h
  let D := (∑ j : Fin d, C j) + 1
  have hsum : 0 ≤ ∑ j : Fin d, C j := Finset.sum_nonneg (fun j _ => (hCpos j).le)
  have hD : 0 < D := by dsimp [D]; linarith
  have he : ∀ᶠ z in cobounded ℂ, ∀ j : Fin d,
      ‖(a j).eval z / (a d).eval z‖ ≤ D * ‖z‖ ^ L := by
    filter_upwards [Filter.eventually_all.mpr hC] with z hz j
    apply (hz j).trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg z) L)
    exact (Finset.single_le_sum (fun i _ => (hCpos i).le) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_right zero_le_one)
  obtain ⟨R, _, hR⟩ := (Filter.hasBasis_cobounded_norm.eventually_iff).mp he
  refine ⟨L, D, max R 1, hD, by positivity, ?_⟩
  intro z hz j hj
  exact hR (le_trans (le_max_left R 1) hz) ⟨j, hj⟩


lemma coefficient_growth_at_infinity (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0) :
    ∃ (L : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ z in cobounded ℂ, ∀ j < P.natDegree,
      ‖(P.coeff j).eval z‖ / ‖P.leadingCoeff.eval z‖ ≤ C * ‖z‖ ^ L := by
  obtain ⟨L, C, R, hC, _, hbound⟩ :=
    rational_family_growth_at_infinity P.coeff P.natDegree
      (by simpa using Polynomial.leadingCoeff_ne_zero.mpr hP)
  refine ⟨L, C, hC, ?_⟩
  filter_upwards [eventually_cobounded_le_norm R] with z hz j hj
  simpa only [Polynomial.coeff_natDegree, norm_div] using hbound z hz j hj

lemma branch_growth_at_infinity_of_coefficients
    (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0)
    (L : ℕ) (C : ℝ) (hC : 0 < C)
    (hcoeff : ∀ᶠ z in cobounded ℂ, ∀ j < P.natDegree,
      ‖(P.coeff j).eval z‖ / ‖P.leadingCoeff.eval z‖ ≤ C * ‖z‖ ^ L)
    (h : ℕ) (hh : 0 < h) (W : ℂ → ℂ)
    (hroot : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      (P.map (Polynomial.evalRingHom ((t ^ h)⁻¹))).eval (W t) = 0) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      ‖W t‖ ≤ D * (‖t‖ ^ (h * L))⁻¹ := by
  have hto : Tendsto (fun t : ℂ => (t ^ h)⁻¹) (𝓝[≠] 0) (cobounded ℂ) := by
    simpa only [zpow_neg, zpow_natCast] using
      (tendsto_zpow_nhdsNE_zero_cobounded (α := ℂ)
        (m := -(h : ℤ)) (by omega))
  have hlead : ∀ᶠ z in cobounded ℂ, P.leadingCoeff.eval z ≠ 0 :=
    (Polynomial.eventually_eval_ne_zero_cofinite
      (Polynomial.leadingCoeff_ne_zero.mpr hP)).filter_mono (Bornology.le_cofinite ℂ)
  have ht_norm : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖t‖ < 1 :=
    (continuous_norm.continuousAt.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1))).filter_mono
      nhdsWithin_le_nhds
  refine ⟨1 + C, by positivity, ?_⟩
  filter_upwards [hroot, hto.eventually hcoeff, hto.eventually hlead,
    self_mem_nhdsWithin, ht_norm] with t ht hct hlt ht0 ht1
  have hqdeg : (P.map (Polynomial.evalRingHom ((t ^ h)⁻¹))).natDegree = P.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlt
  have hqlead : (P.map (Polynomial.evalRingHom ((t ^ h)⁻¹))).leadingCoeff =
      P.leadingCoeff.eval ((t ^ h)⁻¹) :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlt
  have hq : P.map (Polynomial.evalRingHom ((t ^ h)⁻¹)) ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    rwa [hqlead]
  have hcb : ∀ j < (P.map (Polynomial.evalRingHom ((t ^ h)⁻¹))).natDegree,
      ‖(P.map (Polynomial.evalRingHom ((t ^ h)⁻¹))).coeff j‖ /
          ‖(P.map (Polynomial.evalRingHom ((t ^ h)⁻¹))).leadingCoeff‖ ≤
        C * (‖t‖ ^ (h * L))⁻¹ := by
    intro j hj
    rw [hqdeg] at hj
    simpa only [Polynomial.coeff_map, hqlead, Polynomial.coe_evalRingHom,
      norm_inv, norm_pow, inv_pow, ← pow_mul] using hct j hj
  have hb := root_norm_le_of_coeff_bound hq ht (by positivity : 0 ≤ C * (‖t‖ ^ (h * L))⁻¹) hcb
  have ht0' : t ≠ 0 := ht0
  have hp0 : 0 < ‖t‖ ^ (h * L) := pow_pos (norm_pos_iff.mpr ht0') _
  have hp1 : ‖t‖ ^ (h * L) ≤ 1 := pow_le_one₀ (norm_nonneg t) ht1.le
  have hpinv : 1 ≤ (‖t‖ ^ (h * L))⁻¹ := (one_le_inv₀ hp0).mpr hp1
  calc ‖W t‖ ≤ 1 + C * (‖t‖ ^ (h * L))⁻¹ := hb
    _ ≤ (1 + C) * (‖t‖ ^ (h * L))⁻¹ := by nlinarith


lemma branch_growth_at_infinity (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0)
    (h : ℕ) (hh : 0 < h) (W : ℂ → ℂ)
    (hroot : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      (P.map (Polynomial.evalRingHom ((t ^ h)⁻¹))).eval (W t) = 0) :
    ∃ (L : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      ‖W t‖ ≤ C * (‖t‖ ^ (h * L))⁻¹ := by
  obtain ⟨L, C, hC, hcoeff⟩ := coefficient_growth_at_infinity P hP
  obtain ⟨D, hD, hbound⟩ :=
    branch_growth_at_infinity_of_coefficients P hP L C hC hcoeff h hh W hroot
  exact ⟨L, D, hD, hbound⟩

/-- A power growth estimate excludes an essential singularity and cuts off
all Laurent coefficients below the same quantitative bound. -/
lemma finiteTail_of_bound (W : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hW : HolomorphicOn (puncturedDisk 0 r) W) (m : ℕ)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      ‖W t‖ ≤ C * (‖t‖ ^ m)⁻¹) :
    Specs.D12Complex.Ch21.AlgebraicGrowth.finiteTail W r m := by
  have hi : IsolatedSingularityAt W 0 := ⟨r, hr, hW⟩
  have hO : W =O[𝓝[≠] (0 : ℂ)] (fun t => ((t - 0)^m)⁻¹) := by
    obtain ⟨C, _, hC⟩ := hbound
    apply IsBigO.of_bound C
    simpa only [sub_zero, norm_inv, norm_pow] using hC
  have halt := (SingularityGrowth.bigO_iff W 0 hi m).mp hO
  have hm : MeromorphicAt W 0 := ((SingularityGrowth.atMost_iff_order hi m).mp halt).1
  have hann : Laurent.annulus 0 0 (ENNReal.ofReal r) = puncturedDisk 0 r := by
    exact SingularityCoefficients.annulus_ofReal 0 r
  have hWa : HolomorphicOn (Laurent.annulus 0 0 (ENNReal.ofReal r)) W := hann.symm ▸ hW
  have hR : (0 : ℝ≥0∞) < ENNReal.ofReal r := ENNReal.ofReal_pos.mpr hr
  obtain ⟨a, ha, _⟩ := Laurent.laurent_exists 0 0 (ENNReal.ofReal r) W
    le_rfl (by simpa using hR) hWa
  refine ⟨hm, halt, a, ha, ?_⟩
  rcases halt with hrem | ⟨k, hkm, hp⟩
  · intro n hn
    exact (SingularityCoefficients.removable_iff W 0 (ENNReal.ofReal r) a hR hWa ha).mp
      hrem n (by omega)
  · intro n hn
    exact (SingularityCoefficients.coefficients_of_pole hR ha hp).2 n (by omega)

/-- The source's finite maximum root estimate. -/
theorem root_bound : Specs.D12Complex.Ch21.AlgebraicGrowth.root_bound_type := by
  intro d b w _ heq
  exact monic_equation_root_nnnorm_le_max heq

/-- Finite leading-coefficient order gives exactly the exponent h*k. -/
theorem finite_growth : Specs.D12Complex.Ch21.AlgebraicGrowth.finite_growth_type := by
  intro P _ c k hk h hh r hr W hW hroot
  have he : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (fiber P (c+t^h)).eval (W t) = 0 :=
    by
      filter_upwards [SingularityGrowth.puncturedDisk_mem (a := 0) hr] with t ht
      exact hroot t ht
  have hb := finite_parameter_growth P c k h hh hk W he
  exact ⟨hb, finiteTail_of_bound W r hr hW (h*k) hb⟩

/-- No finite-order hypothesis needs to be furnished by the parameter. -/
theorem finite_parameter : Specs.D12Complex.Ch21.AlgebraicGrowth.finite_parameter_type := by
  intro P hP c h hh r hr W hW hroot
  obtain ⟨k, hk⟩ := polynomial_eval_has_finite_order P.leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hP) c
  exact ⟨k, hk, finite_growth P hP c k hk h hh r hr W hW hroot⟩

/-- Leading-coefficient nonvanishing gives an actual holomorphic extension. -/
theorem nonvanishing_parameter :
    Specs.D12Complex.Ch21.AlgebraicGrowth.nonvanishing_parameter_type := by
  intro P c hc h hh r hr W hW hroot
  have he : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (fiber P (c+t^h)).eval (W t) = 0 :=
    by
      filter_upwards [SingularityGrowth.puncturedDisk_mem (a := 0) hr] with t ht
      exact hroot t ht
  have hb := finite_parameter_bounded P c h hh hc W he
  have hb0 : ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      ‖W t‖ ≤ C * (‖t‖ ^ 0)⁻¹ := by
    simpa only [pow_zero, inv_one, mul_one] using hb
  refine ⟨hb, ?_, finiteTail_of_bound W r hr hW 0 hb0⟩
  apply SingularityGrowth.bounded_removable W 0 ⟨r, hr, hW⟩
  obtain ⟨C, _, hC⟩ := hb
  exact ⟨C, hC⟩

/-- The rational coefficients admit one common integer growth exponent. -/
theorem infinity_coefficients :
    Specs.D12Complex.Ch21.AlgebraicGrowth.infinity_coefficients_type := by
  intro P hP
  obtain ⟨L, C, hC, hcoeff⟩ := coefficient_growth_at_infinity P hP
  exact ⟨L, C, hC, by simpa only [norm_div] using hcoeff⟩

/-- The same exponent works for every cyclic parameter over infinity. -/
theorem infinity_parameter :
    Specs.D12Complex.Ch21.AlgebraicGrowth.infinity_parameter_type := by
  intro P hP
  obtain ⟨L, C, hC, hcoeff⟩ := coefficient_growth_at_infinity P hP
  refine ⟨L, ⟨C, hC, by simpa only [norm_div] using hcoeff⟩, ?_⟩
  intro h hh r hr W hW hroot
  have he : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      (P.map (Polynomial.evalRingHom ((t^h)⁻¹))).eval (W t) = 0 :=
    by
      filter_upwards [SingularityGrowth.puncturedDisk_mem (a := 0) hr] with t ht
      exact hroot t ht
  have hb := branch_growth_at_infinity_of_coefficients P hP L C hC hcoeff h hh W he
  exact ⟨hb, finiteTail_of_bound W r hr hW (h*L) hb⟩

end D12Complex.AlgebraicGrowth
