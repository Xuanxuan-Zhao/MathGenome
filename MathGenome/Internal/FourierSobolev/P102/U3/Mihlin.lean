import MathGenome.Internal.FourierSobolev.Specs.P102.U3.Mihlin
import MathGenome.Internal.FourierSobolev.P102.U3.MihlinDyadicKernels
import MathGenome.Internal.FourierSobolev.P102.U2.CZLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter Set
open scoped FourierTransform Topology ENNReal NNReal

namespace P102.U3.Mihlin
open P102.Specs.U3 (Euclidean)
open P102.U2.CZWeak (Operator)
open P102.U2.CZLpData (Exponent StrongOperator Agrees PairwiseCompatible)

lemma ae_ne_zero (d : ℕ) (hd : 1 ≤ d) : ∀ᵐ ξ : Euclidean d ∂volume, ξ ≠ 0 := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact ae_iff.mpr (by simp)

/-- The symbol's arbitrary value at zero is removed only for constructing a
bounded representative; its multiplier is specified using the original symbol. -/
lemma symbol_measurable {d : ℕ} {m : Euclidean d → ℂ} {A : ℝ}
    (hm : SymbolBound m A) : Measurable m := by
  exact measurable_of_continuousOn_compl_singleton 0 hm.1.continuousOn

theorem l2_unique : P102.Specs.U3.Mihlin.l2UniquenessType := by
  intro d m T U hT hU
  apply ContinuousLinearMap.ext
  intro f
  apply (Lp.fourierTransformₗᵢ (Euclidean d) ℂ).injective
  apply Lp.ext
  exact (hT f).trans (hU f).symm

theorem origin_irrelevant : P102.Specs.U3.Mihlin.originIrrelevanceType := by
  intro d hd m n he T
  have hae : m =ᵐ[volume] n := (ae_ne_zero d hd).mono fun ξ hξ => he ξ hξ
  constructor <;> intro h f
  · exact (h f).trans (hae.mono fun ξ hξ => by simp only [hξ])
  · exact (h f).trans (hae.symm.mono fun ξ hξ => by simp only [hξ])

theorem l2_exists : P102.Specs.U3.Mihlin.l2ExistenceType := by
  classical
  intro d hd m A hm
  have hA := symbol_bound_nonneg hd hm
  let b : Euclidean d → ℂ := fun ξ => if ξ = 0 then 0 else m ξ
  have hb : AEStronglyMeasurable b volume :=
    (Measurable.ite (measurableSet_singleton 0) measurable_const (symbol_measurable hm)).aestronglyMeasurable
  have hB : ∀ ξ, ‖b ξ‖ ≤ A := by
    intro ξ
    by_cases hξ : ξ = 0
    · simp [b, hξ, hA]
    · simpa [b, hξ] using symbol_norm_le hm ξ hξ
  let F := Lp.fourierTransformₗᵢ (Euclidean d) ℂ
  let M := boundedMultiplication b A hb hB
  let T := F.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    M ∘L F.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨T, ?_, ?_⟩
  · intro f
    change (F (F.symm (M (F f))) : Euclidean d → ℂ) =ᵐ[volume] _
    rw [F.apply_symm_apply]
    filter_upwards [boundedMultiplication_apply b A hb hB (F f), ae_ne_zero d hd]
      with ξ hξ hne
    change (M (F f) : Euclidean d → ℂ) ξ = m ξ * (F f) ξ
    change (M (F f) : Euclidean d → ℂ) ξ = b ξ * (F f) ξ at hξ
    rw [show b ξ = m ξ by simp [b, hne]] at hξ
    exact hξ
  · apply ContinuousLinearMap.opNorm_le_bound _ hA
    intro f
    change ‖F.symm (M (F f))‖ ≤ A * ‖f‖
    rw [F.symm.norm_map]
    calc
      ‖M (F f)‖ ≤ ‖M‖ * ‖F f‖ := M.le_opNorm _
      _ ≤ A * ‖F f‖ := mul_le_mul_of_nonneg_right
        (boundedMultiplication_norm_le b A hA hb hB) (norm_nonneg _)
      _ = A * ‖f‖ := by rw [F.norm_map]

/-- Once the exhausting interval contains the finite frequency support, its
sum is exactly the partition sum. -/
lemma finiteSymbol_eventually_eq {d : ℕ} {χ : Euclidean d → ℝ}
    (hχ : IsPartition χ) (m : Euclidean d → ℂ) (ξ : Euclidean d) (hξ : ξ ≠ 0) :
    ∀ᶠ M : ℕ in atTop, finiteSymbol χ m (scales M) ξ = m ξ := by
  classical
  let S := (hχ.2.2.1 ξ).toFinset
  have hS : ∀ᶠ M : ℕ in atTop, S ⊆ scales M := by
    apply (Finset.eventually_all S).mpr
    intro j hj
    filter_upwards [eventually_ge_atTop j.natAbs] with M hM
    simp only [scales, Finset.mem_Icc]
    have hcast : (j.natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    constructor
    · have hneg := (Int.le_natAbs (a := -j)); simpa only [Int.natAbs_neg] using (show -(M : ℤ) ≤ j by omega)
    · have := Int.le_natAbs (a := j); omega
  filter_upwards [hS] with M hM
  have hsum : (∑ j ∈ scales M, block χ j ξ) = 1 := by
    apply HasSum.unique ?_ (hχ.2.1 ξ hξ)
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    by_contra hn
    exact hj (hM (by simpa [S] using hn))
  simp [finiteSymbol, hsum]

/-- A dominated convergence lemma for actual L² classes, with eventual
pointwise equality (which is enough for a locally finite dyadic partition). -/
lemma tendsto_L2_of_dominated_eventually_eq {d : ℕ}
    (u : ℕ → Lp (α := Euclidean d) ℂ 2 volume)
    (v : Lp (α := Euclidean d) ℂ 2 volume)
    (g : Euclidean d → ℂ) (hg : MemLp g 2 volume)
    (hbound : ∀ M, ∀ᵐ ξ ∂volume, ‖u M ξ - v ξ‖ ≤ ‖g ξ‖)
    (hpoint : ∀ᵐ ξ ∂volume, ∀ᶠ M in atTop, u M ξ = v ξ) :
    Tendsto u atTop (𝓝 v) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' u v).mpr
  have hmeas M : AEStronglyMeasurable (fun ξ => u M ξ - v ξ) volume :=
    (Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)
  change Tendsto (fun M => eLpNorm (fun ξ => u M ξ - v ξ) 2 volume) atTop (𝓝 0)
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hmeas _), ENNReal.toReal_ofNat]
  have hfin : (∫⁻ ξ, ‖g ξ‖ₑ ^ (2 : ℝ)) ≠ ∞ := by
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hg).ne
  have hlim : Tendsto (fun M => ∫⁻ ξ, ‖u M ξ - v ξ‖ₑ ^ (2 : ℝ))
      atTop (𝓝 0) := by
    have ht := tendsto_lintegral_of_dominated_convergence' (f := fun _ => 0)
      (fun ξ => ‖g ξ‖ₑ ^ (2 : ℝ))
      (fun M => (hmeas M).enorm.pow_const (2 : ℝ))
      (fun M => (hbound M).mono fun ξ hξ => ENNReal.rpow_le_rpow
        (by simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hξ) (by norm_num))
      hfin
      (hpoint.mono fun ξ hξ => tendsto_const_nhds.congr' (hξ.mono fun M hM => by simp [hM]))
    simpa using ht
  simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
    (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hlim

theorem dyadic_convergence : P102.Specs.U3.Mihlin.dyadicConvergenceType := by
  intro d hd χ hχ hpart m A hm T U hT hU f
  let F := Lp.fourierTransformₗᵢ (Euclidean d) ℂ
  have hA := symbol_bound_nonneg hd hm
  have hconv : Tendsto (fun M => F (U M f)) atTop (𝓝 (F (T f))) := by
    apply tendsto_L2_of_dominated_eventually_eq _ _
      (fun ξ => ((3 * A : ℝ) : ℂ) * (F f) ξ)
      ((Lp.memLp (F f)).const_mul ((3 * A : ℝ) : ℂ))
    · intro M
      filter_upwards [hU M f, hT f, ae_ne_zero d hd] with ξ huf htf hne
      change (F (U M f) : Euclidean d → ℂ) ξ = _ at huf
      change (F (T f) : Euclidean d → ℂ) ξ = _ at htf
      rw [huf, htf, ← sub_mul, norm_mul]
      have hdiff : ‖finiteSymbol χ m (scales M) ξ - m ξ‖ ≤ 3 * A :=
        (norm_sub_le _ _).trans (by
          linarith [finiteSymbol_norm_le hd hχ hm (scales M) ξ, symbol_norm_le hm ξ hne])
      change ‖finiteSymbol χ m (scales M) ξ - m ξ‖ * ‖(F f) ξ‖ ≤
        ‖((3 * A : ℝ) : ℂ) * (F f) ξ‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 3 * A)]
      exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg (F f ξ))
    · filter_upwards [ae_all_iff.mpr (fun M => hU M f), hT f, ae_ne_zero d hd]
        with ξ huf htf hne
      filter_upwards [finiteSymbol_eventually_eq hpart m ξ hne] with M hM
      have hufM := huf M
      change (F (U M f) : Euclidean d → ℂ) ξ = _ at hufM
      change (F (T f) : Euclidean d → ℂ) ξ = _ at htf
      rw [hufM, htf, hM]
  have hh := F.symm.continuous.tendsto (F (T f)) |>.comp hconv
  change Tendsto (fun M => F.symm (F (U M f))) atTop (𝓝 (F.symm (F (T f)))) at hh
  simpa only [F.symm_apply_apply] using hh

/-- Padding by a scalar identity makes the L² operator norm an exact fixed
number. This lets the general CZ theorem, whose bound is an arbitrary function
of the exact L² norm, provide a bound uniform over a norm-bounded family. -/
lemma exists_scalar_shift_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [Nontrivial E] (T : E →L[ℂ] E) (B : ℝ)
    (hB : 0 ≤ B) (hT : ‖T‖ ≤ B) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 2 * B ∧
      ‖T + (t : ℂ) • ContinuousLinearMap.id ℂ E‖ = B := by
  let I := ContinuousLinearMap.id ℂ E
  have hI (t : ℝ) : ‖(t : ℂ) • I‖ = |t| := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, ContinuousLinearMap.norm_id, mul_one]
  have hhigh : B ≤ ‖T + ((2 * B : ℝ) : ℂ) • I‖ := by
    have h := norm_sub_le (T + ((2 * B : ℝ) : ℂ) • I) T
    rw [add_sub_cancel_left, hI, abs_of_nonneg (by positivity : 0 ≤ 2 * B)] at h
    linarith
  have hc : ContinuousOn (fun t : ℝ => ‖T + (t : ℂ) • I‖) (Icc 0 (2 * B)) := by
    fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by positivity : 0 ≤ 2 * B) hc
    (show B ∈ Icc ‖T + (0 : ℂ) • I‖ ‖T + ((2 * B : ℝ) : ℂ) • I‖ from
      ⟨by simpa using hT, hhigh⟩)
  exact ⟨t, ht.1, ht.2, he⟩

lemma kernelHypotheses_add_scalar_id {d : ℕ}
    {T : Operator d} {K : Euclidean d → ℂ} {H : ℝ≥0}
    (hK : P102.U2.CZWeak.KernelHypotheses T K H) (t : ℂ) :
    P102.U2.CZWeak.KernelHypotheses
      (T + t • ContinuousLinearMap.id ℂ _) K H := by
  refine ⟨hK.locallyIntegrable, ?_, hK.difference⟩
  intro b h2 S hS hb
  filter_upwards [hK.offSupport b h2 S hS hb, hb, h2.coeFn_toLp,
    Lp.coeFn_add (T (h2.toLp b)) (t • h2.toLp b),
    Lp.coeFn_smul t (h2.toLp b)] with x hx hbx h2x hsum hsmul
  intro hxs
  change (T (h2.toLp b) + t • h2.toLp b : P102.U2.CZWeak.L2 d) x = _
  rw [hsum, Pi.add_apply, hsmul, Pi.smul_apply, h2x, hbx hxs, smul_zero, add_zero]
  exact hx hxs

/-- A uniform version of the supplied CZ theorem, using only its original
rough-kernel hypotheses. No monotonicity of its existential constant is assumed. -/
lemma uniform_cz_extension (d : ℕ) (hd : 1 ≤ d) (H B : ℝ≥0) :
    ∃ C : Exponent → ℝ≥0, ∀ (T : Operator d) (K : Euclidean d → ℂ),
      P102.U2.CZWeak.KernelHypotheses T K H → ‖T‖ ≤ (B : ℝ) →
      ∀ p : Exponent, ∃ R : StrongOperator d p,
        ‖R‖ ≤ (C p : ℝ) ∧ Agrees T p R := by
  obtain ⟨C₁, C, hC⟩ := P102.U2.CZLp.full_extension
  refine ⟨fun p => C d p H B + 2 * B, ?_⟩
  intro T K hK hT p
  rcases subsingleton_or_nontrivial (P102.U2.CZWeak.L2 d) with hsub | hn
  · have := hsub
    refine ⟨0, by simp only [norm_zero]; positivity, ?_⟩
    intro f hp h2
    have he : T (h2.toLp f) = 0 := Subsingleton.elim _ _
    rw [he]
    exact (Lp.coeFn_zero _ _ _).trans (Lp.coeFn_zero _ _ _).symm
  · have := hn
    obtain ⟨t, ht0, htB, ht⟩ := exists_scalar_shift_norm T B B.coe_nonneg hT
    let V : Operator d := T + (t : ℂ) • ContinuousLinearMap.id ℂ _
    have hnV : ‖V‖₊ = B := NNReal.eq ht
    obtain ⟨_, S, R, _, _, _, _, _, _, hnorm, hagree, _, _⟩ :=
      hC d hd V K H (kernelHypotheses_add_scalar_id hK t)
    refine ⟨R p - (t : ℂ) • ContinuousLinearMap.id ℂ _, ?_, ?_⟩
    · have hr := hnorm p
      rw [hnV] at hr
      have hi : ‖(t : ℂ) • ContinuousLinearMap.id ℂ (P102.U2.CZLpData.Space d p.val)‖ ≤ t := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
        exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le ht0).trans_eq (mul_one t)
      exact (norm_sub_le _ _).trans (by
        simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
        linarith)
    · intro f hp h2
      have h := hagree p f hp h2
      change (R p (hp.toLp f) - (t : ℂ) • hp.toLp f : P102.U2.CZLpData.Space d p.val)
        =ᵐ[volume] (T (h2.toLp f) : Euclidean d → ℂ)
      filter_upwards [h, Lp.coeFn_sub (R p (hp.toLp f)) ((t : ℂ) • hp.toLp f),
        Lp.coeFn_smul (t : ℂ) (hp.toLp f), hp.coeFn_toLp,
        Lp.coeFn_add (T (h2.toLp f)) ((t : ℂ) • h2.toLp f),
        Lp.coeFn_smul (t : ℂ) (h2.toLp f), h2.coeFn_toLp]
        with x hx hsub hsmul hpx hadd hsmul2 h2x
      change (R p (hp.toLp f) : Euclidean d → ℂ) x =
        (T (h2.toLp f) + (t : ℂ) • h2.toLp f : P102.U2.CZWeak.L2 d) x at hx
      rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hpx, hx, hadd, Pi.add_apply, hsmul2, Pi.smul_apply, h2x]
      simp

lemma finite_kernel_hypotheses {d : ℕ} {χ : Euclidean d → ℝ}
    {m : Euclidean d → ℂ} {J : Finset ℤ} {H : ℝ≥0} {T : Operator d}
    (hK : Integrable (finiteKernel χ m J))
    (hrep : ∀ f : P102.U2.CZWeak.L2 d,
      (T f : Euclidean d → ℂ) =ᵐ[volume]
        fun x => ∫ y, finiteKernel χ m J (x-y) * f y)
    (hdiff : ∀ h : Euclidean d, h ≠ 0 →
      IntegrableOn (fun x => ‖finiteKernel χ m J (x-h) - finiteKernel χ m J x‖)
        {x | 2*‖h‖ < ‖x‖} ∧
      (∫ x in {x | 2*‖h‖ < ‖x‖}, ‖finiteKernel χ m J (x-h) - finiteKernel χ m J x‖) ≤ H) :
    P102.U2.CZWeak.KernelHypotheses T (finiteKernel χ m J) H := by
  refine ⟨hK.locallyIntegrable.locallyIntegrableOn _, ?_, ?_⟩
  · intro b h2 S _ _
    have he (x : Euclidean d) :
        (∫ y, finiteKernel χ m J (x-y) * h2.toLp b y) =
        ∫ y, finiteKernel χ m J (x-y) * b y := by
      apply integral_congr_ae
      exact h2.coeFn_toLp.mono fun y hy => by simp only [hy]
    filter_upwards [hrep (h2.toLp b)] with x hx
    intro _
    exact hx.trans (he x)
  · intro h hh
    obtain ⟨hi, hb⟩ := hdiff h hh
    calc
      (∫⁻ x in {x | 2*‖h‖ < ‖x‖}, ‖finiteKernel χ m J (x-h) - finiteKernel χ m J x‖ₑ) =
          ENNReal.ofReal (∫ x in {x | 2*‖h‖ < ‖x‖},
            ‖finiteKernel χ m J (x-h) - finiteKernel χ m J x‖) := by
        rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
        simp only [ofReal_norm]
      _ ≤ (H : ℝ≥0∞) := by
        simpa using ENNReal.ofReal_le_ofReal hb

/-- Uniform finite-sum Lp bounds for the unit Mihlin ball. The cutoff and all
constants are chosen independently of the symbol and of the finite scale set. -/
lemma unit_finite_extensions (d : ℕ) (hd : 1 ≤ d) :
    ∃ (χ : Euclidean d → ℝ) (C : Exponent → ℝ≥0),
      IsCutoff χ ∧ IsPartition χ ∧
      ∀ m : Euclidean d → ℂ, SymbolBound m 1 → ∀ J : Finset ℤ,
        ∃ T : Operator d, HasL2Symbol T (finiteSymbol χ m J) ∧
          ∀ p : Exponent, ∃ R : StrongOperator d p,
            ‖R‖ ≤ (C p : ℝ) ∧ Agrees T p R := by
  obtain ⟨χ, D, hD, hχ, hpart, hdyadic⟩ := dyadic_kernels d hd
  let H : ℝ≥0 := ⟨D, hD.le⟩
  obtain ⟨C, hC⟩ := uniform_cz_extension d hd H H
  refine ⟨χ, C, hχ, hpart, ?_⟩
  intro m hm J
  obtain ⟨hK, _, ⟨T, hnorm, hT⟩, hdiff⟩ := (hdyadic m 1 hm).2 J
  have hKH : P102.U2.CZWeak.KernelHypotheses T (finiteKernel χ m J) H :=
    finite_kernel_hypotheses hK (fun f => (hT f).2.2) (by
      intro h hh
      obtain ⟨hi, hb⟩ := hdiff h hh
      refine ⟨hi, ?_⟩
      change _ ≤ D
      simpa only [mul_one] using hb)
  exact ⟨T, fun f => (hT f).1, hC T _ hKH (by change ‖T‖ ≤ D; simpa only [mul_one] using hnorm)⟩

/-- Fatou followed by extension from the dense intersection. The input
hypotheses are operator convergence on L² and actual uniformly bounded Lp
realizations of the approximants, rather than an assumed full multiplier bound. -/
lemma extension_of_l2_limits {d : ℕ} (p : Exponent) (B : ℝ≥0)
    (T : Operator d) (V : ℕ → Operator d)
    (hconv : ∀ f : P102.U2.CZWeak.L2 d, Tendsto (fun M => V M f) atTop (𝓝 (T f)))
    (hext : ∀ M, ∃ R : StrongOperator d p, ‖R‖ ≤ (B : ℝ) ∧ Agrees (V M) p R) :
    ∃ R : StrongOperator d p, ‖R‖ ≤ (B : ℝ) ∧ Agrees T p R := by
  open ExpandedFA.Interpolation ExpandedFA.Interpolation.MarcinkiewiczSpec in
    obtain ⟨L, hLm, hLae⟩ := ExpandedFA.SingularIntegrals.CZLp.exists_linear_representatives
      ℂ (volume : Measure (Euclidean d))
    let I := ExpandedFA.SingularIntegrals.CZLp.intersectionToL2 (𝕜 := ℂ) (d := d) p.val
    let W : intersectionCore (volume : Measure (Euclidean d)) 1 2 p.val →ₗ[ℂ]
        P102.U2.CZWeak.Classes d :=
      (P102.U2.CZWeak.lpEmbed 2).comp (T.toLinearMap.comp I)
    let U := L.comp W
    have hae (a : intersectionCore (volume : Measure (Euclidean d)) 1 2 p.val) : U a =ᵐ[volume] (T (I a) : Euclidean d → ℂ) := hLae (W a)
    choose R hRnorm hR using hext
    have hbound (a : intersectionCore (volume : Measure (Euclidean d)) 1 2 p.val) : eLpNorm (T (I a) : Euclidean d → ℂ) p.val volume ≤
        (B : ℝ≥0∞) * eLpNorm (a.val : Euclidean d → ℂ) p.val volume := by
      apply eLpNorm_le_of_tendstoInMeasure (Filter.Eventually.of_forall fun M => ?_)
        (tendstoInMeasure_of_tendsto_Lp (hconv (I a)))
        (fun M => Lp.aestronglyMeasurable _)
      have he := hR M (a.val : Euclidean d → ℂ) (Lp.memLp _) a.property.2
      have hi : I a = a.property.2.toLp a.val := rfl
      rw [← hi, Lp.toLp_coeFn] at he
      rw [← eLpNorm_congr_ae he, ← Lp.enorm_def, ← ofReal_norm]
      calc
        ENNReal.ofReal ‖R M a.val‖ ≤ ENNReal.ofReal ((B : ℝ) * ‖a.val‖) :=
          ENNReal.ofReal_le_ofReal ((R M).le_opNorm a.val |>.trans
            (mul_le_mul_of_nonneg_right (hRnorm M) (norm_nonneg _)))
        _ = (B : ℝ≥0∞) * eLpNorm (a.val : Euclidean d → ℂ) p.val volume := by
          rw [ENNReal.ofReal_mul B.coe_nonneg, ENNReal.ofReal_coe_nnreal, ofReal_norm, Lp.enorm_def]
    have hb (a : intersectionCore (volume : Measure (Euclidean d)) 1 2 p.val) : MemLp (U a) p.val volume ∧ eLpNorm (U a) p.val volume ≤
        (B : ℝ≥0∞) * eLpNorm (a.val : Euclidean d → ℂ) p.val volume := by
      have hh := (eLpNorm_congr_ae (hae a)).trans_le (hbound a)
      exact ⟨hh.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (Lp.memLp a.val)), hh⟩
    obtain ⟨S, hS, _⟩ := extend_from_intersection_of_bound volume volume 1 2 p.val p.lt_top.ne B U hb
    refine ⟨S, hS.1, ?_⟩
    have hcore : ∀ (f : Euclidean d → ℂ) (_h1 : MemLp f 1 volume)
        (h2 : MemLp f 2 volume) (hp : MemLp f p.val volume),
        (S (hp.toLp f) : Euclidean d → ℂ) =ᵐ[volume] (T (h2.toLp f) : Euclidean d → ℂ) := by
      intro f h1 h2 hp
      let a : intersectionCore (volume : Measure (Euclidean d)) 1 2 p.val :=
        ⟨hp.toLp f, (memLp_congr_ae hp.coeFn_toLp).mpr h1,
          (memLp_congr_ae hp.coeFn_toLp).mpr h2⟩
      have he : I a = h2.toLp f := a.property.2.toLp_congr h2 hp.coeFn_toLp
      exact (hS.2 a).trans ((hae a).trans (by rw [he]))
    intro f hp h2
    exact P102.U2.CZLp.bounded_extensions_agree T p.val 2 p.lt_top.ne (by simp) S T hcore
      (fun _ _ _ _ => Filter.EventuallyEq.rfl) f hp h2

lemma unit_multiplier_extension (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : Exponent → ℝ≥0, ∀ (m : Euclidean d → ℂ), SymbolBound m 1 →
      ∃ T : Operator d, HasL2Symbol T m ∧ ‖T‖ ≤ 1 ∧
        ∀ p : Exponent, ∃ R : StrongOperator d p,
          ‖R‖ ≤ (C p : ℝ) ∧ Agrees T p R := by
  obtain ⟨χ, C, hχ, hpart, hfinite⟩ := unit_finite_extensions d hd
  refine ⟨C, ?_⟩
  intro m hm
  obtain ⟨T, hT, hnorm⟩ := l2_exists d hd m 1 hm
  have hf M := hfinite m hm (scales M)
  choose V hV hext using hf
  refine ⟨T, hT, hnorm, ?_⟩
  intro p
  exact extension_of_l2_limits p (C p) T V
    (dyadic_convergence d hd χ hχ hpart m 1 hm T V hT hV) (fun M => hext M p)

lemma symbolBound_smul {d : ℕ} {m : Euclidean d → ℂ} {A : ℝ}
    (c : ℂ) (hm : SymbolBound m A) : SymbolBound (c • m) (‖c‖ * A) := by
  refine ⟨ContDiffOn.const_smul c hm.1, ?_⟩
  intro n hn β ξ hξ
  have hc : ContDiffAt ℝ n m ξ :=
    (hm.1.contDiffAt (isOpen_compl_singleton.mem_nhds hξ)).of_le (by exact_mod_cast hn)
  rw [iteratedFDeriv_const_smul_apply hc, smul_apply, norm_smul]
  exact (mul_le_mul_of_nonneg_left (hm.2 n hn β ξ hξ) (norm_nonneg c)).trans_eq (by ring)

lemma hasL2Symbol_smul {d : ℕ} {T : Operator d} {m : Euclidean d → ℂ}
    (c : ℂ) (h : HasL2Symbol T m) : HasL2Symbol (c • T) (c • m) := by
  intro f
  change ((𝓕 (c • T f) : P102.U2.CZWeak.L2 d) : Euclidean d → ℂ) =ᵐ[volume] _
  have hs : (𝓕 (c • T f) : P102.U2.CZWeak.L2 d) =
      c • (𝓕 (T f) : P102.U2.CZWeak.L2 d) :=
    (Lp.fourierTransformₗᵢ (Euclidean d) ℂ).map_smul c (T f)
  rw [hs]
  filter_upwards [Lp.coeFn_smul c (𝓕 (T f) : P102.U2.CZWeak.L2 d), h f] with ξ hsmul hξ
  rw [hsmul, Pi.smul_apply, hξ]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

lemma agrees_smul {d : ℕ} {T : Operator d} {p : Exponent} {R : StrongOperator d p}
    (c : ℂ) (h : Agrees T p R) : Agrees (c • T) p (c • R) := by
  intro f hp h2
  filter_upwards [Lp.coeFn_smul c (R (hp.toLp f)), Lp.coeFn_smul c (T (h2.toLp f)),
    h f hp h2] with x hpx h2x hx
  change (c • R (hp.toLp f) : P102.U2.CZLpData.Space d p.val) x =
    (c • T (h2.toLp f) : P102.U2.CZWeak.L2 d) x
  simp only [hpx, h2x, Pi.smul_apply, hx]

lemma extension_unique {d : ℕ} (T : Operator d) (p : Exponent)
    (R S : StrongOperator d p) (hR : Agrees T p R) (hS : Agrees T p S) : R = S := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have he := P102.U2.CZLp.bounded_extensions_agree T p.val p.val p.lt_top.ne p.lt_top.ne R S
    (fun f _ h2 hp => hR f hp h2) (fun f _ h2 hp => hS f hp h2)
    (f : Euclidean d → ℂ) (Lp.memLp _) (Lp.memLp _)
  simpa only [Lp.toLp_coeFn] using he

/-- Classical Mihlin, with the source's exact derivative count, a constant
independent of the symbol and its bound, whole-intersection agreement, and a
unique compatible family of extensions. -/
theorem mihlin : P102.Specs.U3.Mihlin.theoremType := by
  intro d hd
  obtain ⟨C, hC⟩ := unit_multiplier_extension d hd
  refine ⟨C, ?_⟩
  intro m A hA hm
  have hex : ∃ T : Operator d, HasL2Symbol T m ∧ ‖T‖ ≤ A ∧
      ∀ p : Exponent, ∃ R : StrongOperator d p,
        ‖R‖ ≤ (C p : ℝ) * A ∧ Agrees T p R := by
    rcases eq_or_lt_of_le hA with hz | hpos
    · have hAz : A = 0 := hz.symm
      subst A
      obtain ⟨T, hT, hn⟩ := l2_exists d hd m 0 hm
      have hzero : T = 0 := norm_le_zero_iff.mp hn
      refine ⟨T, hT, hn, ?_⟩
      intro p
      refine ⟨0, by simp, ?_⟩
      intro f hp h2
      rw [hzero]
      exact (Lp.coeFn_zero _ _ _).trans (Lp.coeFn_zero _ _ _).symm
    · let n : Euclidean d → ℂ := (A : ℂ)⁻¹ • m
      have hn : SymbolBound n 1 := by
        have h := symbolBound_smul (A : ℂ)⁻¹ hm
        simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
          inv_mul_cancel₀ hpos.ne'] using h
      obtain ⟨T₀, hT₀, hnorm₀, hR⟩ := hC n hn
      have he : (A : ℂ) • n = m := by
        funext ξ
        simp only [n, Pi.smul_apply, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hpos.ne' :
          (A : ℂ) ≠ 0), one_smul]
      have hT : HasL2Symbol ((A : ℂ) • T₀) m := by
        simpa only [he] using hasL2Symbol_smul (A : ℂ) hT₀
      refine ⟨(A : ℂ) • T₀, hT, ?_, ?_⟩
      · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
        exact (mul_le_mul_of_nonneg_left hnorm₀ hA).trans_eq (mul_one A)
      · intro p
        obtain ⟨R, hnormR, hagree⟩ := hR p
        refine ⟨(A : ℂ) • R, ?_, agrees_smul (A : ℂ) hagree⟩
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
        exact (mul_le_mul_of_nonneg_left hnormR hA).trans_eq (mul_comm A (C p : ℝ))
  obtain ⟨T, hT, hnorm, hR⟩ := hex
  choose R hRnorm hagree using hR
  refine ⟨T, hT, hnorm, R, hRnorm, hagree, ?_, ?_⟩
  · intro p q f hp hq
    exact P102.U2.CZLp.bounded_extensions_agree T p.val q.val p.lt_top.ne q.lt_top.ne (R p) (R q)
      (fun f _ h2 hp => hagree p f hp h2) (fun f _ h2 hq => hagree q f hq h2) f hp hq
  · intro p S hS
    exact extension_unique T p S (R p) hS (hagree p)

end P102.U3.Mihlin
