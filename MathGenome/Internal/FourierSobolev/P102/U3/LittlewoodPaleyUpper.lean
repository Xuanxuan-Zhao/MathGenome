import MathGenome.Internal.FourierSobolev.Specs.P102.U3.LittlewoodPaleyUpper
import MathGenome.Internal.FourierSobolev.P102.U3.Mihlin
import MathGenome.Internal.FourierSobolev.P102.U3.RandomSignMoments
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators ContDiff Topology FourierTransform

namespace P102.U3.LittlewoodPaley
open P102.Specs.U3 (Euclidean)
open P102.U3.Mihlin
open P102.U2.CZWeak (Operator)
open P102.U2.CZLpData (Exponent StrongOperator Agrees)

lemma Annular.hasCompactSupport {d : ℕ} {η : Euclidean d → ℝ} (hη : Annular η) :
    HasCompactSupport η := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean d) 4)
  intro x hx
  have hh : (4 : ℝ) < ‖x‖ := by simpa using hx
  exact hη.2.2 x hh.le

lemma annulus_annular {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ) :
    Annular (annulus χ) := by
  refine ⟨annulus_contDiff hχ, ?_, ?_⟩
  · intro ξ hξ
    exact annulus_eq_zero_of_small hχ (by linarith)
  · intro ξ hξ
    exact annulus_eq_zero_of_large hχ (by linarith)

lemma enlargedCutoff_annular {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ) :
    Annular (enlargedCutoff χ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (hχ.1.comp (contDiff_id.const_smul (1 / 2 : ℝ))).mul
      (contDiff_const.sub (hχ.1.comp (contDiff_id.const_smul (4 : ℝ))))
  · intro ξ hξ
    have hh : χ ((4 : ℝ) • ξ) = 1 := hχ.2.2.2.1 _ (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      linarith)
    simp only [enlargedCutoff, hh, sub_self, mul_zero]
  · intro ξ hξ
    have hh : χ ((1 / 2 : ℝ) • ξ) = 0 := hχ.2.2.2.2 _ (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith)
    simp only [enlargedCutoff, hh, zero_mul]

lemma annulus_tsupport {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ) :
    tsupport (annulus χ) ⊆ {ξ | (1 / 2 : ℝ) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2} := by
  apply closure_minimal
  · intro ξ hξ
    exact ⟨(annulus_support hχ ξ hξ).1.le, (annulus_support hχ ξ hξ).2.le⟩
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

lemma enlargedCutoff_eq_one {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    {ξ : Euclidean d} (hξ : ξ ∈ tsupport (annulus χ)) : enlargedCutoff χ ξ = 1 := by
  obtain ⟨hlo, hhi⟩ := annulus_tsupport hχ hξ
  have h1 : χ ((1 / 2 : ℝ) • ξ) = 1 := hχ.2.2.2.1 _ (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith)
  have h0 : χ ((4 : ℝ) • ξ) = 0 := hχ.2.2.2.2 _ (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith)
  simp only [enlargedCutoff, h1, h0, sub_zero, mul_one]

theorem cutoff_construction : P102.Specs.U3.LittlewoodPaleyUpper.cutoffType := by
  intro d χ hχ
  exact ⟨annulus_annular hχ, (annulus_annular hχ).hasCompactSupport,
    enlargedCutoff_annular hχ, (enlargedCutoff_annular hχ).hasCompactSupport,
    fun _ hξ => enlargedCutoff_eq_one hχ hξ⟩

lemma HasLpSymbol.unique {d : ℕ} {p : Exponent} {m : Euclidean d → ℂ}
    {R S : StrongOperator d p} (hR : HasLpSymbol p m R) (hS : HasLpSymbol p m S) :
    R = S := by
  obtain ⟨T, hT, hR⟩ := hR
  obtain ⟨U, hU, hS⟩ := hS
  have he : T = U := l2_unique d m T U hT hU
  subst U
  exact extension_unique T p R S hR hS

lemma multiplier_hasSymbol {d : ℕ} {p : Exponent} {m : Euclidean d → ℂ}
    (h : ∃ R : StrongOperator d p, HasLpSymbol p m R) :
    HasLpSymbol p m (multiplier p m) := by
  classical
  simpa only [multiplier, dite_eq_left h] using Classical.choose_spec h

lemma multiplier_eq {d : ℕ} {p : Exponent} {m : Euclidean d → ℂ}
    {R : StrongOperator d p} (hR : HasLpSymbol p m R) : multiplier p m = R :=
  (multiplier_hasSymbol ⟨R, hR⟩).unique hR

/-- Once a symbol bound is established, the total choice is the genuine
canonical extension and inherits the quantitative Mihlin bound. -/
lemma multiplier_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : Exponent → ℝ≥0, ∀ (m : Euclidean d → ℂ) (A : ℝ),
      0 ≤ A → SymbolBound m A → ∀ p : Exponent,
        HasLpSymbol p m (multiplier p m) ∧ ‖multiplier p m‖ ≤ (C p : ℝ) * A := by
  obtain ⟨C, hC⟩ := mihlin d hd
  refine ⟨C, ?_⟩
  intro m A hA hm p
  obtain ⟨T, hT, _, R, hnorm, hagree, _, _⟩ := hC m A hA hm
  have hR : HasLpSymbol p m (R p) := ⟨T, hT, hagree p⟩
  rw [multiplier_eq hR]
  exact ⟨hR, hnorm p⟩

lemma finiteSquare_measurable {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (J : Finset ℤ) (f : Lp (α := Euclidean d) ℂ p.val volume) :
    Measurable (finiteSquare p η J f) := by
  apply Real.continuous_sqrt.measurable.comp
  exact Finset.measurable_sum J fun j _ =>
    ((Lp.stronglyMeasurable (projection p η j f)).measurable.norm).pow_const 2

lemma infiniteSquare_measurable {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (f : Lp (α := Euclidean d) ℂ p.val volume) :
    Measurable (infiniteSquare p η f) := by
  exact (Measurable.tsum fun j =>
    ((Lp.stronglyMeasurable (projection p η j f)).measurable.enorm).pow_const 2).pow_const (1 / 2 : ℝ)

/-- A smooth symbol supported in a fixed ball satisfies the finite-order
Mihlin condition. No conclusion is inferred merely from its name or regularity. -/
lemma symbolBound_of_support_ball {d : ℕ} {g : Euclidean d → ℂ}
    (hg : ContDiff ℝ ∞ g) {R : ℝ} (hR : 0 < R)
    (hs : tsupport g ⊆ Metric.closedBall 0 R) :
    ∃ A : ℝ, 0 ≤ A ∧ SymbolBound g A := by
  classical
  have hc : HasCompactSupport g := (isCompact_closedBall (0 : Euclidean d) R).of_isClosed_subset
    isClosed_closure hs
  obtain ⟨D, hD0, hD⟩ := compactSmooth_derivative_bounds hg hc
  let A : ℝ := ∑ n ∈ Finset.range (order d + 1), D n * R ^ n
  have hA : 0 ≤ A := Finset.sum_nonneg fun n _ => mul_nonneg (hD0 n) (pow_nonneg hR.le n)
  refine ⟨A, hA, (hg.of_le (by simp)).contDiffOn, ?_⟩
  intro n hn β ξ hξ
  have heval := P102.U3.coordinate_eval_le_norm (iteratedFDeriv ℝ n g ξ) β
  by_cases hball : ξ ∈ Metric.closedBall 0 R
  · have hxR : ‖ξ‖ ≤ R := by simpa using hball
    have hx : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hDn : D n * R ^ n ≤ A := Finset.single_le_sum
      (fun i _ => mul_nonneg (hD0 i) (pow_nonneg hR.le i))
      (Finset.mem_range.mpr (by omega))
    apply heval.trans ((hD n ξ).trans ?_)
    rw [zpow_neg, zpow_natCast]
    apply (le_mul_inv_iff₀ (pow_pos hx n)).mpr
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le hxR n) (hD0 n)).trans hDn
  · have hz : iteratedFDeriv ℝ n g ξ = 0 := by
      by_contra hne
      exact hball (hs (support_iteratedFDeriv_subset (𝕜 := ℝ) n hne))
    simp only [hz, zero_apply, norm_zero]
    exact mul_nonneg hA (zpow_nonneg (norm_nonneg _) _)

lemma symbol_smooth {d : ℕ} {η : Euclidean d → ℝ} (hη : Annular η) (j : ℤ) :
    ContDiff ℝ ∞ (symbol η j) :=
  Complex.ofRealCLM.contDiff.comp (hη.1.comp (contDiff_id.const_smul (scale (-j))))

lemma symbol_tsupport {d : ℕ} {η : Euclidean d → ℝ} (hη : Annular η) (j : ℤ) :
    tsupport (symbol η j) ⊆ Metric.closedBall 0 (4 * scale j) := by
  apply closure_minimal
  · intro ξ hξ
    have hne : η (scale (-j) • ξ) ≠ 0 := by simpa [symbol] using hξ
    have hlt : ‖scale (-j) • ξ‖ < 4 := lt_of_not_ge fun h => hne (hη.2.2 _ h)
    rw [norm_scale_neg, div_lt_iff₀ (scale_pos j)] at hlt
    simpa using hlt.le
  · exact Metric.isClosed_closedBall

lemma symbol_bound {d : ℕ} {η : Euclidean d → ℝ} (hη : Annular η) (j : ℤ) :
    ∃ A : ℝ, 0 ≤ A ∧ SymbolBound (symbol η j) A :=
  symbolBound_of_support_ball (symbol_smooth hη j)
    (mul_pos (by norm_num : (0 : ℝ) < 4) (scale_pos j)) (symbol_tsupport hη j)

theorem projections : P102.Specs.U3.LittlewoodPaleyUpper.projectionsType := by
  intro d hd η hη p j
  obtain ⟨A, hA, hm⟩ := symbol_bound hη j
  obtain ⟨C, hC⟩ := multiplier_bound d hd
  exact (hC (symbol η j) A hA hm p).1

lemma finiteSquare_le_sum {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (J : Finset ℤ) (f : Lp (α := Euclidean d) ℂ p.val volume) (x : Euclidean d) :
    finiteSquare p η J f x ≤ ∑ j ∈ J, ‖projection p η j f x‖ := by
  apply (Real.sqrt_le_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _

/-- Finite square functions belong to Lᵖ before any uniform estimate is used. -/
lemma finiteSquare_memLp {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (J : Finset ℤ) (f : Lp (α := Euclidean d) ℂ p.val volume) :
    MemLp (finiteSquare p η J f) p.val volume := by
  have hs : MemLp (fun x => ∑ j ∈ J, ‖projection p η j f x‖) p.val volume :=
    memLp_finsetSum J fun j _ => (Lp.memLp (projection p η j f)).norm
  apply hs.of_le (finiteSquare_measurable p η J f).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ finiteSquare p η J f x from Real.sqrt_nonneg _),
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] using
    finiteSquare_le_sum p η J f x

lemma hasL2Symbol_add {d : ℕ} {T U : Operator d} {m n : Euclidean d → ℂ}
    (hT : HasL2Symbol T m) (hU : HasL2Symbol U n) :
    HasL2Symbol (T + U) (m + n) := by
  intro f
  change ((𝓕 (T f + U f) : P102.U2.CZWeak.L2 d) : Euclidean d → ℂ) =ᵐ[volume] _
  rw [show (𝓕 (T f + U f) : P102.U2.CZWeak.L2 d) = 𝓕 (T f) + 𝓕 (U f) from
    (Lp.fourierTransformₗᵢ (Euclidean d) ℂ).map_add _ _]
  filter_upwards [Lp.coeFn_add (𝓕 (T f) : P102.U2.CZWeak.L2 d) (𝓕 (U f)), hT f, hU f]
    with ξ ha hTξ hUξ
  simpa only [Pi.add_apply, hTξ, hUξ, add_mul] using ha

lemma HasLpSymbol.add {d : ℕ} {p : Exponent} {m n : Euclidean d → ℂ}
    {R S : StrongOperator d p} (hR : HasLpSymbol p m R) (hS : HasLpSymbol p n S) :
    HasLpSymbol p (m + n) (R + S) := by
  obtain ⟨T, hT, hR⟩ := hR
  obtain ⟨U, hU, hS⟩ := hS
  refine ⟨T + U, hasL2Symbol_add hT hU, ?_⟩
  intro f hp h2
  filter_upwards [Lp.coeFn_add (R (hp.toLp f)) (S (hp.toLp f)),
    Lp.coeFn_add (T (h2.toLp f)) (U (h2.toLp f)), hR f hp h2, hS f hp h2]
    with x ha hb hR hS
  change (R (hp.toLp f) + S (hp.toLp f) : P102.U2.CZLpData.Space d p.val) x =
    (T (h2.toLp f) + U (h2.toLp f) : P102.U2.CZWeak.L2 d) x
  simp only [ha, hb, Pi.add_apply, hR, hS]

lemma HasLpSymbol.smul {d : ℕ} {p : Exponent} {m : Euclidean d → ℂ}
    {R : StrongOperator d p} (hR : HasLpSymbol p m R) (c : ℂ) :
    HasLpSymbol p (c • m) (c • R) := by
  obtain ⟨T, hT, hR⟩ := hR
  exact ⟨c • T, hasL2Symbol_smul c hT, agrees_smul c hR⟩

lemma hasLpSymbol_zero {d : ℕ} (p : Exponent) :
    HasLpSymbol p (0 : Euclidean d → ℂ) (0 : StrongOperator d p) := by
  refine ⟨0, ?_, ?_⟩
  · intro f
    change ((𝓕 (0 : P102.U2.CZWeak.L2 d) : P102.U2.CZWeak.L2 d) : Euclidean d → ℂ)
      =ᵐ[volume] _
    rw [show (𝓕 (0 : P102.U2.CZWeak.L2 d) : P102.U2.CZWeak.L2 d) = 0 from
      (Lp.fourierTransformₗᵢ (Euclidean d) ℂ).map_zero]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (Euclidean d))] with ξ hξ
    simpa only [Pi.zero_apply, zero_mul] using hξ
  · intro f hp h2
    exact (Lp.coeFn_zero ℂ p.val volume).trans (Lp.coeFn_zero ℂ 2 volume).symm

lemma signed_hasSymbol {d : ℕ} (hd : 1 ≤ d) {η : Euclidean d → ℝ} (hη : Annular η)
    (p : Exponent) (J : Finset ℤ) (ε : ℤ → Bool) :
    HasLpSymbol p (signedSymbol η J ε) (signedOperator p η J ε) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    have hz : signedSymbol η ∅ ε = 0 := by funext ξ; simp [signedSymbol]
    rw [hz]
    simpa [signedOperator] using (hasLpSymbol_zero (d := d) p)
  | @insert j J hj hJ =>
    have hsum := ((projections d hd η hη p j).smul (P102.U3.RandomSigns.sign (ε j))).add hJ
    have he : signedSymbol η (insert j J) ε =
        (P102.U3.RandomSigns.sign (ε j) : ℂ) • symbol η j + signedSymbol η J ε := by
      funext ξ
      simp [signedSymbol, Finset.sum_insert hj]
    rw [he]
    simpa only [signedOperator, Finset.sum_insert hj] using hsum

/-- Transfer a uniform signed-symbol derivative bound to the actual canonical
multiplier extensions using the quantitative Mihlin theorem. -/
lemma signed_control_of_symbol_bound {d : ℕ} (hd : 1 ≤ d)
    {η : Euclidean d → ℝ} (hη : Annular η)
    (h : ∃ A : ℝ, 0 ≤ A ∧ ∀ (J : Finset ℤ) (ε : ℤ → Bool),
      SymbolBound (signedSymbol η J ε) A) : SignedControl η := by
  refine ⟨h, ?_⟩
  obtain ⟨A, hA, hb⟩ := h
  obtain ⟨C, hC⟩ := multiplier_bound d hd
  intro p
  refine ⟨C p * A.toNNReal, ?_⟩
  intro J ε
  have hS := signed_hasSymbol hd hη p J ε
  refine ⟨hS, ?_⟩
  have he := multiplier_eq hS
  have hh := (hC (signedSymbol η J ε) A hA (hb J ε) p).2
  rw [he] at hh
  simpa only [NNReal.coe_mul, Real.coe_toNNReal A hA] using hh

/-- Derivatives of an annular function vanish outside its closed annulus. -/
lemma Annular.complex_tsupport {d : ℕ} {η : Euclidean d → ℝ} (hη : Annular η) :
    tsupport (fun x => (η x : ℂ)) ⊆ {x | (1 / 4 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 4} := by
  apply closure_minimal
  · intro x hx
    have hx' : η x ≠ 0 := by simpa using hx
    exact ⟨(lt_of_not_ge fun h => hx' (hη.2.1 x h)).le,
      (lt_of_not_ge fun h => hx' (hη.2.2 x h)).le⟩
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

lemma symbol_derivative {d : ℕ} {η : Euclidean d → ℝ} (hη : Annular η)
    (n : ℕ) (j : ℤ) (ξ : Euclidean d) :
    iteratedFDeriv ℝ n (symbol η j) ξ =
      scale (-j) ^ n • iteratedFDeriv ℝ n (fun x => (η x : ℂ)) (scale (-j) • ξ) := by
  exact congrFun (iteratedFDeriv_comp_const_smul (scale (-j))
    ((Complex.ofRealCLM.contDiff.comp hη.1).of_le (by simp))) ξ

/-- At a fixed nonzero frequency, at most five dyadic derivatives can be nonzero. -/
lemma symbol_derivative_support {d : ℕ} {η : Euclidean d → ℝ} (hη : Annular η)
    (n : ℕ) {ξ : Euclidean d} (hξ : ξ ≠ 0) :
    ∃ k : ℤ, ∀ j : ℤ, iteratedFDeriv ℝ n (symbol η j) ξ ≠ 0 →
      j ∈ Finset.Icc (k - 2) (k + 2) ∧ ‖ξ‖ ≤ 4 * scale j := by
  obtain ⟨k, hk, hk'⟩ := exists_mem_Ico_zpow (norm_pos_iff.mpr hξ)
    (by norm_num : (1 : ℝ) < 2)
  change scale k ≤ ‖ξ‖ at hk
  change ‖ξ‖ < scale (k + 1) at hk'
  refine ⟨k, ?_⟩
  intro j hj
  have hbase : iteratedFDeriv ℝ n (fun x => (η x : ℂ)) (scale (-j) • ξ) ≠ 0 := by
    intro hz
    rw [symbol_derivative hη, hz, smul_zero] at hj
    exact hj rfl
  obtain ⟨hlo, hhi⟩ := hη.complex_tsupport
    (support_iteratedFDeriv_subset (𝕜 := ℝ) n hbase)
  rw [norm_scale_neg, le_div_iff₀ (scale_pos j)] at hlo
  rw [norm_scale_neg, div_le_iff₀ (scale_pos j)] at hhi
  refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hhi⟩
  · by_contra h
    have hle : j + 2 ≤ k - 1 := by omega
    have hs : 4 * scale j ≤ scale (k - 1) := by
      calc
        4 * scale j = scale (j + 2) := by rw [scale_add]; norm_num [scale]; ring
        _ ≤ scale (k - 1) := scale_mono hle
    have he : scale k = 2 * scale (k - 1) := by
      rw [show k = (k - 1) + 1 by omega, scale_add, scale_one]; ring
    have hp := scale_pos (k - 1)
    linarith
  · by_contra h
    have hle : k + 1 ≤ j - 2 := by omega
    have hs : scale (k + 1) ≤ (1 / 4 : ℝ) * scale j := by
      calc
        scale (k + 1) ≤ scale (j - 2) := scale_mono hle
        _ = (1 / 4 : ℝ) * scale j := by
          rw [show j - 2 = j + (-2) by omega, scale_add]; norm_num [scale]; ring
    linarith

/-- Bounded overlap and the dilation chain rule give one Mihlin constant for
all finite signed sums. The constant is independent of both the set and signs. -/
lemma signed_symbol_bound {d : ℕ} {η : Euclidean d → ℝ} (hη : Annular η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (J : Finset ℤ) (ε : ℤ → Bool),
      SymbolBound (signedSymbol η J ε) A := by
  classical
  let g : Euclidean d → ℂ := fun x => (η x : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hη.1
  have hgc : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean d) 4)
    intro x hx
    have hh : (4 : ℝ) < ‖x‖ := by simpa using hx
    simp [g, hη.2.2 x hh.le]
  obtain ⟨D, hD0, hD⟩ := compactSmooth_derivative_bounds hg hgc
  let A : ℝ := 5 * ∑ n ∈ Finset.range (order d + 1), D n * 4 ^ n
  have hA : 0 ≤ A := mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun n _ => mul_nonneg (hD0 n) (by positivity))
  refine ⟨A, hA, ?_⟩
  intro J ε
  have hsmooth : ContDiff ℝ ∞ (signedSymbol η J ε) :=
    ContDiff.sum fun j _ => (symbol_smooth hη j).const_smul (P102.U3.RandomSigns.sign (ε j) : ℂ)
  refine ⟨(hsmooth.of_le (by simp)).contDiffOn, ?_⟩
  intro n hn β ξ hξ
  obtain ⟨k, hk⟩ := symbol_derivative_support hη n hξ
  let F : Finset ℤ := J.filter fun j => iteratedFDeriv ℝ n (symbol η j) ξ ≠ 0
  have hcard : F.card ≤ 5 := by
    calc
      F.card ≤ (Finset.Icc (k - 2) (k + 2)).card :=
        Finset.card_le_card fun j hj => (hk j (Finset.mem_filter.mp hj).2).1
      _ = 5 := by simp only [Int.card_Icc]; omega
  have hterm (j : ℤ) (hj : j ∈ F) :
      ‖iteratedFDeriv ℝ n (symbol η j) ξ‖ ≤ D n * 4 ^ n * ‖ξ‖ ^ (-(n : ℤ)) := by
    have hxpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hx := (hk j (Finset.mem_filter.mp hj).2).2
    have hinv : scale (-j) ≤ 4 / ‖ξ‖ := by
      rw [scale_neg, le_div_iff₀ hxpos, inv_mul_eq_div, div_le_iff₀ (scale_pos j)]
      linarith
    rw [symbol_derivative hη, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (scale_pos _).le n)]
    calc
      scale (-j) ^ n * ‖iteratedFDeriv ℝ n g (scale (-j) • ξ)‖ ≤
          (4 / ‖ξ‖) ^ n * D n :=
        mul_le_mul (pow_le_pow_left₀ (scale_pos _).le hinv n)
          (hD n _) (norm_nonneg _) (by positivity)
      _ = D n * 4 ^ n * ‖ξ‖ ^ (-(n : ℤ)) := by
        rw [div_pow, zpow_neg, zpow_natCast]; ring
  have hsign (j : ℤ) : ‖(P102.U3.RandomSigns.sign (ε j) : ℂ)‖ = 1 := by
    cases ε j <;> norm_num [P102.U3.RandomSigns.sign]
  have he : iteratedFDeriv ℝ n (signedSymbol η J ε) ξ =
      ∑ j ∈ J, (P102.U3.RandomSigns.sign (ε j) : ℂ) •
        iteratedFDeriv ℝ n (symbol η j) ξ := by
    change iteratedFDeriv ℝ n (fun x => ∑ j ∈ J,
      (P102.U3.RandomSigns.sign (ε j) : ℂ) • symbol η j x) ξ = _
    rw [iteratedFDeriv_fun_sum_apply]
    · apply Finset.sum_congr rfl
      intro j _
      exact iteratedFDeriv_const_smul_apply' ((symbol_smooth hη j).of_le (by simp)).contDiffAt
    · intro j _
      exact (((symbol_smooth hη j).const_smul
        (P102.U3.RandomSigns.sign (ε j) : ℂ)).of_le (by simp)).contDiffAt
  have hsum : (∑ j ∈ J, ‖iteratedFDeriv ℝ n (symbol η j) ξ‖) =
      ∑ j ∈ F, ‖iteratedFDeriv ℝ n (symbol η j) ξ‖ := by
    apply (Finset.sum_filter_of_ne fun j _ hj => ?_).symm
    exact fun hz => hj (by rw [hz, norm_zero])
  have hDn : 5 * (D n * 4 ^ n) ≤ A := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Finset.single_le_sum (fun i _ => mul_nonneg (hD0 i) (by positivity))
      (Finset.mem_range.mpr (by omega))
  calc
    ‖iteratedFDeriv ℝ n (signedSymbol η J ε) ξ (P102.U3.coordinateVector ∘ β)‖ ≤
        ‖iteratedFDeriv ℝ n (signedSymbol η J ε) ξ‖ := P102.U3.coordinate_eval_le_norm _ β
    _ ≤ ∑ j ∈ J, ‖iteratedFDeriv ℝ n (symbol η j) ξ‖ := by
      rw [he]
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_smul, hsign, one_mul])
    _ ≤ (5 : ℝ) * (D n * 4 ^ n * ‖ξ‖ ^ (-(n : ℤ))) := by
      rw [hsum]
      calc
        _ ≤ ∑ j ∈ F, D n * 4 ^ n * ‖ξ‖ ^ (-(n : ℤ)) := Finset.sum_le_sum hterm
        _ = (F.card : ℝ) * (D n * 4 ^ n * ‖ξ‖ ^ (-(n : ℤ))) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
            (mul_nonneg (mul_nonneg (hD0 n) (by positivity)) (zpow_nonneg (norm_nonneg _) _))
    _ ≤ A * ‖ξ‖ ^ (-(n : ℤ)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hDn (zpow_nonneg (norm_nonneg _) _)

theorem signed_control : P102.Specs.U3.LittlewoodPaleyUpper.signedType := by
  intro d hd η hη
  exact signed_control_of_symbol_bound hd hη (signed_symbol_bound hη)

lemma finiteSquare_enorm {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (J : Finset ℤ) (f : Lp (α := Euclidean d) ℂ p.val volume) (x : Euclidean d) :
    ‖finiteSquare p η J f x‖ₑ =
      (∑ j ∈ J, ‖projection p η j f x‖ₑ ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  rw [finiteSquare, Real.enorm_eq_ofReal (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma infiniteSquare_rpow_eq_iSup {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (f : Lp (α := Euclidean d) ℂ p.val volume) (x : Euclidean d) {q : ℝ} (hq : 0 < q) :
    infiniteSquare p η f x ^ q = ⨆ J : Finset ℤ, ‖finiteSquare p η J f x‖ₑ ^ q := by
  simp_rw [finiteSquare_enorm, infiniteSquare, ← ENNReal.rpow_mul]
  change (∑' j : ℤ, ‖projection p η j f x‖ₑ ^ (2 : ℕ)) ^ ((1 / 2 : ℝ) * q) = _
  rw [ENNReal.tsum_eq_iSup_sum]
  exact (ENNReal.orderIsoRpow ((1 / 2 : ℝ) * q) (by positivity)).map_iSup _

/-- Monotone convergence over all finite subsets preserves the finite bound,
including the value infinity until a.e. finiteness has been established. -/
lemma upperBound_of_finite {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ) (C : ℝ≥0)
    (hfin : ∀ (f : Lp (α := Euclidean d) ℂ p.val volume) (J : Finset ℤ),
      eLpNorm (finiteSquare p η J f) p.val volume ≤ (C : ℝ≥0∞) * ‖f‖ₑ) :
    UpperBound p η C := by
  intro f
  have hp0 : p.val ≠ 0 := ne_of_gt (lt_trans (by simp) p.one_lt)
  have hpT : p.val ≠ (∞ : ℝ≥0∞) := p.lt_top.ne
  have hq : 0 < p.val.toReal := ENNReal.toReal_pos hp0 hpT
  have hmeas := infiniteSquare_measurable p η f
  have hI : (∫⁻ x, infiniteSquare p η f x ^ p.val.toReal ∂volume) ≤
      ((C : ℝ≥0∞) * ‖f‖ₑ) ^ p.val.toReal := by
    simp_rw [infiniteSquare_rpow_eq_iSup p η f _ hq]
    rw [lintegral_iSup_directed_of_measurable]
    · apply iSup_le
      intro J
      have hJ := ENNReal.rpow_le_rpow (hfin f J) hq.le
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT
        (finiteSquare_measurable p η J f).aestronglyMeasurable,
        ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one] at hJ
      exact hJ
    · intro J
      exact ((finiteSquare_measurable p η J f).enorm).pow_const _
    · intro J K
      refine ⟨J ∪ K, ?_, ?_⟩ <;> intro x <;> dsimp only <;>
        rw [finiteSquare_enorm, finiteSquare_enorm] <;>
        apply ENNReal.rpow_le_rpow _ hq.le <;>
        apply ENNReal.rpow_le_rpow _ (by norm_num) <;>
        exact Finset.sum_le_sum_of_subset (by simp)
  have hinf : eLpNorm (infiniteSquare p η f) p.val volume ≤ (C : ℝ≥0∞) * ‖f‖ₑ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT hmeas.aestronglyMeasurable]
    simp only [enorm_eq_self]
    simpa only [one_div] using (ENNReal.rpow_inv_le_iff hq).mpr hI
  have hItop : (∫⁻ x, infiniteSquare p η f x ^ p.val.toReal ∂volume) < (∞ : ℝ≥0∞) :=
    hI.trans_lt (ENNReal.rpow_lt_top_of_nonneg hq.le (by finiteness))
  have hae : ∀ᵐ x ∂volume, infiniteSquare p η f x < (∞ : ℝ≥0∞) := by
    filter_upwards [ae_lt_top (hmeas.pow_const p.val.toReal) hItop.ne] with x hx
    by_contra h
    have htop : infiniteSquare p η f x = (∞ : ℝ≥0∞) := top_unique (not_lt.mp h)
    simp [htop, hq] at hx
  have hmem : MemLp (fun x => (infiniteSquare p η f x).toReal) p.val volume := by
    apply lt_of_le_of_lt (eLpNorm_mono_enorm (hmeas.ennreal_toReal.aestronglyMeasurable) ?_)
      (hinf.trans_lt (by finiteness))
    intro x
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, enorm_eq_self]
    exact ENNReal.ofReal_toReal_le
  exact ⟨fun J => ⟨finiteSquare_memLp p η J f, hfin f J⟩, hmeas, hae, hmem, hinf⟩
open P102.U3.RandomSigns (Cube signedSum energy moment)

def extendSigns (J : Finset ℤ) (σ : Cube J) (j : ℤ) : Bool :=
  if h : j ∈ J then σ ⟨j, h⟩ else false

lemma signedOperator_coeFn {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (J : Finset ℤ) (ε : ℤ → Bool) (f : Lp (α := Euclidean d) ℂ p.val volume) :
    (signedOperator p η J ε f : Euclidean d → ℂ) =ᵐ[volume]
      fun x => ∑ j ∈ J, (P102.U3.RandomSigns.sign (ε j) : ℂ) * projection p η j f x := by
  have h := (Lp.coeFn_finsetSum J fun j =>
    (P102.U3.RandomSigns.sign (ε j) : ℂ) • projection p η j f).trans
      (eventuallyEq_sum fun j _ => Lp.coeFn_smul
        (P102.U3.RandomSigns.sign (ε j) : ℂ) (projection p η j f))
  have he : signedOperator p η J ε f = ∑ j ∈ J,
      (P102.U3.RandomSigns.sign (ε j) : ℂ) • projection p η j f := by
    simp only [signedOperator, sum_apply, smul_apply]
  rw [he]
  filter_upwards [h] with x hx
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hx

lemma cube_sum_eq {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (J : Finset ℤ) (σ : Cube J) (f : Lp (α := Euclidean d) ℂ p.val volume) (x : Euclidean d) :
    signedSum (fun j : J => projection p η j f x) σ =
      ∑ j ∈ J, (P102.U3.RandomSigns.sign (extendSigns J σ j) : ℂ) * projection p η j f x := by
  classical
  simp only [signedSum, ← Finset.sum_attach J]
  apply Finset.sum_congr rfl
  intro j _
  simp only [extendSigns, dite_eq_left j.property]

/-- Integrating Khintchine's lower estimate gives the finite-square bound for
any family with uniformly bounded finite signed sums. -/
lemma finite_square_bound_of_signed {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (B : ℝ≥0) (hB : ∀ (J : Finset ℤ) (ε : ℤ → Bool), ‖signedOperator p η J ε‖ ≤ B) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (f : Lp (α := Euclidean d) ℂ p.val volume) (J : Finset ℤ),
      eLpNorm (finiteSquare p η J f) p.val volume ≤ (C : ℝ≥0∞) * ‖f‖ₑ := by
  classical
  have hp0 : p.val ≠ 0 := ne_of_gt (lt_trans (by simp) p.one_lt)
  have hpT : p.val ≠ (∞ : ℝ≥0∞) := p.lt_top.ne
  have hq : 0 < p.val.toReal := ENNReal.toReal_pos hp0 hpT
  obtain ⟨c, _, hc, _, hl⟩ := P102.U3.RandomSigns.randomSignMoments p.val.toReal hq
  let K : ℝ≥0∞ := (ENNReal.ofReal c)⁻¹ ^ (1 / p.val.toReal)
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hKT : K ≠ (∞ : ℝ≥0∞) :=
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) (ENNReal.inv_ne_top.mpr hc0)).ne
  let C : ℝ≥0 := K.toNNReal * B + 1
  refine ⟨C, by positivity, ?_⟩
  intro f J
  let : DecidableEq J := fun _ _ => Classical.propDecidable _
  let F : Cube J → Euclidean d → ℂ := fun σ x =>
    signedSum (fun j : J => projection p η j f x) σ
  have hFmeas (σ : Cube J) : Measurable (F σ) := by
    exact Finset.measurable_sum _ fun j _ =>
      measurable_const.mul (Lp.stronglyMeasurable (projection p η j f)).measurable
  have hFnorm (σ : Cube J) : eLpNorm (F σ) p.val volume ≤ (B : ℝ≥0∞) * ‖f‖ₑ := by
    have he : (signedOperator p η J (extendSigns J σ) f : Euclidean d → ℂ) =ᵐ[volume] F σ := by
      simpa only [F, cube_sum_eq] using signedOperator_coeFn p η J (extendSigns J σ) f
    rw [← eLpNorm_congr_ae he, ← Lp.enorm_def]
    have hb := (signedOperator p η J (extendSigns J σ)).le_opNorm f
    have hn := hb.trans (mul_le_mul_of_nonneg_right (hB J (extendSigns J σ)) (norm_nonneg f))
    simpa only [ENNReal.ofReal_mul B.coe_nonneg, ENNReal.ofReal_coe_nnreal, ofReal_norm]
      using ENNReal.ofReal_le_ofReal hn
  have henergy (x : Euclidean d) : energy (fun j : J => projection p η j f x) =
      ∑ j ∈ J, ‖projection p η j f x‖ ^ 2 := by
    change (∑ j : J, ‖projection p η j f x‖ ^ 2) = _
    exact Finset.sum_coe_sort J (fun j : ℤ => ‖projection p η j f x‖ ^ 2)
  have hpow (x : Euclidean d) :
      ENNReal.ofReal ((energy (fun j : J => projection p η j f x)) ^ (p.val.toReal / 2)) =
        ‖finiteSquare p η J f x‖ₑ ^ p.val.toReal := by
    rw [finiteSquare, Real.enorm_eq_ofReal (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le,
      ← Real.rpow_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _), henergy]
    congr 2
    ring
  let N : ℝ≥0∞ := Fintype.card (Cube J)
  have hN0 : N ≠ 0 := by simp [N]
  have hNT : N ≠ (∞ : ℝ≥0∞) := by simp [N]
  have hpt (x : Euclidean d) :
      ENNReal.ofReal c * ‖finiteSquare p η J f x‖ₑ ^ p.val.toReal ≤
        N⁻¹ * ∑ σ : Cube J, ‖F σ x‖ₑ ^ p.val.toReal := by
    have hh := ENNReal.ofReal_le_ofReal (hl J (fun j : J => projection p η j f x)).1
    rw [ENNReal.ofReal_mul hc.le, hpow, moment, Fintype.expect_eq_sum_div_card,
      ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)] at hh
    simpa only [F, N, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le, ofReal_norm,
      ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm] using hh
  have hI : ENNReal.ofReal c * (∫⁻ x, ‖finiteSquare p η J f x‖ₑ ^ p.val.toReal ∂volume) ≤
      ((B : ℝ≥0∞) * ‖f‖ₑ) ^ p.val.toReal := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal c * ‖finiteSquare p η J f x‖ₑ ^ p.val.toReal ∂volume :=
        (lintegral_const_mul _ ((finiteSquare_measurable p η J f).enorm.pow_const _)).symm
      _ ≤ ∫⁻ x, N⁻¹ * ∑ σ : Cube J, ‖F σ x‖ₑ ^ p.val.toReal ∂volume := lintegral_mono hpt
      _ = N⁻¹ * ∑ σ : Cube J, ∫⁻ x, ‖F σ x‖ₑ ^ p.val.toReal ∂volume := by
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hN0), lintegral_finsetSum]
        intro σ _
        exact (hFmeas σ).enorm.pow_const _
      _ ≤ N⁻¹ * ∑ _σ : Cube J, ((B : ℝ≥0∞) * ‖f‖ₑ) ^ p.val.toReal := by
        apply mul_le_mul_of_nonneg_left _ zero_le
        apply Finset.sum_le_sum
        intro σ _
        have hh := ENNReal.rpow_le_rpow (hFnorm σ) hq.le
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT (hFmeas σ).aestronglyMeasurable,
          ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one] at hh
        exact hh
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← mul_assoc, ENNReal.inv_mul_cancel hN0 hNT, one_mul]
  have hI' : (∫⁻ x, ‖finiteSquare p η J f x‖ₑ ^ p.val.toReal ∂volume) ≤
      (ENNReal.ofReal c)⁻¹ * (((B : ℝ≥0∞) * ‖f‖ₑ) ^ p.val.toReal) := by
    calc
      _ = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c *
          (∫⁻ x, ‖finiteSquare p η J f x‖ₑ ^ p.val.toReal ∂volume)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hI zero_le
  calc
    eLpNorm (finiteSquare p η J f) p.val volume =
        (∫⁻ x, ‖finiteSquare p η J f x‖ₑ ^ p.val.toReal ∂volume) ^ (1 / p.val.toReal) :=
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT
        (finiteSquare_measurable p η J f).aestronglyMeasurable
    _ ≤ ((ENNReal.ofReal c)⁻¹ * (((B : ℝ≥0∞) * ‖f‖ₑ) ^ p.val.toReal)) ^ (1 / p.val.toReal) :=
      ENNReal.rpow_le_rpow hI' (by positivity)
    _ = K * (B : ℝ≥0∞) * ‖f‖ₑ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div,
        ENNReal.rpow_rpow_inv hq.ne', mul_assoc]
      simp only [K, one_div]
    _ ≤ (C : ℝ≥0∞) * ‖f‖ₑ := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      rw [← ENNReal.coe_toNNReal hKT, ← ENNReal.coe_mul]
      exact_mod_cast (le_add_of_nonneg_right (by positivity : (0 : ℝ≥0) ≤ 1) :
        K.toNNReal * B ≤ C)
theorem upper_bound : P102.Specs.U3.LittlewoodPaleyUpper.upperType := by
  intro d hd η hη p
  obtain ⟨B, hB⟩ := (signed_control d hd η hη).2 p
  obtain ⟨C, hC, hfin⟩ := finite_square_bound_of_signed p η B (fun J ε => (hB J ε).2)
  exact ⟨C, hC, upperBound_of_finite p η C hfin⟩

lemma UpperBound.mono {d : ℕ} {p : Exponent} {η : Euclidean d → ℝ}
    {C D : ℝ≥0} (hC : UpperBound p η C) (hCD : C ≤ D) : UpperBound p η D := by
  intro f
  obtain ⟨hfin, hmeas, hae, hmem, hinf⟩ := hC f
  have hCD' : (C : ℝ≥0∞) * ‖f‖ₑ ≤ (D : ℝ≥0∞) * ‖f‖ₑ :=
    mul_le_mul (show (C : ℝ≥0∞) ≤ (D : ℝ≥0∞) by exact_mod_cast hCD)
      le_rfl zero_le zero_le
  exact ⟨fun J => ⟨(hfin J).1, (hfin J).2.trans hCD'⟩,
    hmeas, hae, hmem, hinf.trans hCD'⟩

/-- Combine the cutoff construction and the two upper-bound ingredients. -/
lemma upper_assembly
    (hSigned : P102.Specs.U3.LittlewoodPaleyUpper.signedType)
    (hUpper : P102.Specs.U3.LittlewoodPaleyUpper.upperType) :
    P102.Specs.U3.LittlewoodPaleyUpper.theoremType := by
  intro d hd χ hχ _
  obtain ⟨hη, _, ht, htc, hte⟩ := cutoff_construction d χ hχ
  refine ⟨enlargedCutoff χ, ht, htc, hte,
    hSigned d hd (annulus χ) hη, hSigned d hd (enlargedCutoff χ) ht, ?_⟩
  intro p
  obtain ⟨C, hC, hCU⟩ := hUpper d hd (annulus χ) hη p
  obtain ⟨D, _, hDU⟩ := hUpper d hd (enlargedCutoff χ) ht p
  exact ⟨projections d hd (annulus χ) hη p, projections d hd (enlargedCutoff χ) ht p,
    max C D, lt_of_lt_of_le hC (le_max_left _ _),
    hCU.mono (le_max_left _ _), hDU.mono (le_max_right _ _)⟩

/-- The complete upper-square-function stage, for both the original partition
and an enlarged annular cutoff, on every Lᵖ with 1 < p < ∞. -/
theorem littlewood_paley_upper : P102.Specs.U3.LittlewoodPaleyUpper.theoremType :=
  upper_assembly signed_control upper_bound

end P102.U3.LittlewoodPaley
