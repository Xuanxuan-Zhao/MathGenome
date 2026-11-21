import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.MeanZeroPoincare
import MathGenome.Internal.FourierSobolev.P102.Sobolev.Rellich
import MathGenome.Internal.FourierSobolev.P102.Sobolev.ZeroGradient
import Mathlib.Analysis.Normed.Module.RCLike.Basic

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace P102.Sobolev.MeanZeroPoincare
open P102.U4

/-- A compact component and a lower bound for their product give coercivity
of the other component when its kernel is zero. -/
lemma coercive_of_compact {𝕜 E F G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (A : E →L[𝕜] F) (B : E →L[𝕜] G)
    (hcompact : ∀ S : Set E, Bornology.IsBounded S → IsCompact (closure (A '' S)))
    (hbound : ∀ x, ‖x‖ ≤ ‖A x‖ + ‖B x‖)
    (hker : ∀ x, B x = 0 → x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖x‖ ≤ C * ‖B x‖ := by
  classical
  by_contra! h
  have hn (n : ℕ) : ∃ x : E, ‖x‖ = 1 ∧ ‖B x‖ < ((n : ℝ) + 1)⁻¹ := by
    obtain ⟨x, hx⟩ := h ((n : ℝ) + 1) (by positivity)
    have hx0 : x ≠ 0 := by intro he; simp [he] at hx
    refine ⟨(‖x‖⁻¹ : 𝕜) • x, norm_smul_inv_norm hx0, ?_⟩
    rw [map_smul, norm_smul, norm_inv, RCLike.norm_coe_norm, ← div_eq_inv_mul]
    apply (div_lt_iff₀ (norm_pos_iff.mpr hx0)).mpr
    rw [mul_comm, ← div_eq_mul_inv]
    exact (lt_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr (by simpa [mul_comm] using hx)
  choose x hxnorm hxB using hn
  have htB : Tendsto (fun n => B (x n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hxB n).le) (by
      exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))))
  have hb : Bornology.IsBounded (range x) := isBounded_iff_forall_norm_le.mpr
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hxnorm n).le⟩
  obtain ⟨y, _, σ, hσ, htA⟩ := (hcompact (range x) hb).tendsto_subseq
    (fun n => subset_closure (mem_image_of_mem A (mem_range_self n)))
  let L := A.prod B
  have hL : IsUniformEmbedding L := L.isUniformEmbedding_of_bound (K := 2) (fun u => by
    have ha : ‖A u‖ ≤ ‖L u‖ := norm_fst_le (L u)
    have hb : ‖B u‖ ≤ ‖L u‖ := norm_snd_le (L u)
    norm_num only [NNReal.coe_ofNat]
    linarith [hbound u])
  have htL : Tendsto (fun n => L (x (σ n))) atTop (𝓝 (y, 0)) :=
    htA.prodMk_nhds (htB.comp hσ.tendsto_atTop)
  have hc : CauchySeq (x ∘ σ) := hL.isUniformInducing.cauchy_map_iff.mp (by simpa only [CauchySeq, Filter.map_map, Function.comp_def] using htL.cauchySeq)
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
  have hzB : B z = 0 := tendsto_nhds_unique (B.continuous.tendsto z |>.comp hz)
    (htB.comp hσ.tendsto_atTop)
  have hzn : ‖z‖ = 1 := tendsto_nhds_unique hz.norm
    (by simpa only [Function.comp_apply, hxnorm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  rw [hker z hzB, norm_zero] at hzn
  norm_num at hzn

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The positive-order part of the Sobolev tuple, with zero in its zeroth slot. -/
def positiveDerivatives : Sobolev 𝕜 Ω 1 p →L[𝕜] SobolevTuple 𝕜 Ω 1 p :=
  (PiLp.continuousLinearEquiv 1 𝕜 _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun α => if α = zeroSobolevIndex d 1 then 0 else
      (PiLp.proj 1 _ α).comp (sobolevSubmodule 𝕜 Ω 1 p).subtypeL)

@[simp] lemma positiveDerivatives_apply (u : Sobolev 𝕜 Ω 1 p) (α : SobolevIndex d 1) :
    positiveDerivatives Ω p u α =
      if α = zeroSobolevIndex d 1 then 0 else sobolevDerivative u α := by
  change (if α = zeroSobolevIndex d 1 then
    (0 : Sobolev 𝕜 Ω 1 p →L[𝕜] DomainLp 𝕜 Ω p) else
      (PiLp.proj 1 _ α).comp (sobolevSubmodule 𝕜 Ω 1 p).subtypeL) u = _
  split_ifs <;> rfl

lemma norm_split (u : Sobolev 𝕜 Ω 1 p) :
    ‖u‖ = ‖sobolevUnderlying u‖ + ‖positiveDerivatives Ω p u‖ := by
  rw [sobolev_norm Ω 1 p, PiLp.norm_eq_of_L1]
  have heq (α : SobolevIndex d 1) : ‖sobolevDerivative u α‖ =
      (if α = zeroSobolevIndex d 1 then ‖sobolevUnderlying u‖ else 0) +
        ‖positiveDerivatives Ω p u α‖ := by
    by_cases h : α = zeroSobolevIndex d 1
    · subst α; simp [sobolev_derivative_zero]
    · simp [positiveDerivatives_apply, h]
  simp_rw [heq, Finset.sum_add_distrib]
  simp

variable [IsFiniteMeasure (volume.restrict (Ω : Set (Space d)))]
/-- Integration as a continuous linear functional on the actual Lp space. -/
def integralLp : DomainLp 𝕜 Ω p →L[𝕜] 𝕜 := by
  letI : Fact (1 ≤ ENNReal.conjExponent p) := ⟨by
    simp only [ENNReal.conjExponent]; exact le_self_add⟩
  exact ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
    (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p)).flip
      (Lp.const _ _ 1)

lemma integralLp_eq (u : DomainLp 𝕜 Ω p) :
    integralLp Ω p u = ∫ x in Ω, u x := by
  letI : Fact (1 ≤ ENNReal.conjExponent p) := ⟨by
    simp only [ENNReal.conjExponent]; exact le_self_add⟩
  change (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing _ _ _ u _ = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (ENNReal.conjExponent p)
    (volume.restrict (Ω : Set (Space d))) (1 : 𝕜)] with x hx
  change u x * (Lp.const (ENNReal.conjExponent p) (volume.restrict (Ω : Set (Space d))) (1 : 𝕜)) x = u x
  rw [hx]
  exact mul_one _

lemma regularLp_const (c : 𝕜) :
    regularDistribution Ω (Lp.const p (volume.restrict (Ω : Set (Space d))) c) =
      regularDistribution Ω (fun _ => c) := by
  apply (regular_injectivity d 𝕜 Ω _ _ (domainLp_locallyIntegrable Ω p _)
    (continuous_const.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)).mpr
  exact Lp.coeFn_const _ _ _

omit [IsFiniteMeasure (volume.restrict (Ω : Set (Space d)))] in
lemma regularLp_zero : regularDistribution Ω (0 : DomainLp 𝕜 Ω p) = 0 := by
  ext φ
  rw [regularLp_pairing Ω p, map_zero]
  rfl

/-- Constant functions belong to the canonical weak Sobolev space. -/
lemma exists_constant (c : 𝕜) : ∃ v : Sobolev 𝕜 Ω 1 p,
    sobolevUnderlying v = Lp.const p (volume.restrict (Ω : Set (Space d))) c ∧
    positiveDerivatives Ω p v = 0 := by
  let f : DomainLp 𝕜 Ω p := Lp.const p (volume.restrict (Ω : Set (Space d))) c
  have hmem : HasSobolevDerivatives Ω 1 p f := by
    intro α hα
    by_cases hzero : α = 0
    · subst α; exact ⟨f, derivative_zero d 𝕜 Ω _⟩
    · have hc : α.card = 1 := by have := Multiset.card_pos.mpr hzero; omega
      obtain ⟨i, rfl⟩ := Multiset.card_eq_one.mp hc
      refine ⟨0, ?_⟩
      rw [regularLp_const Ω p c,
        derivative_classicalCompatibility d 𝕜 Ω {i} (fun _ => c) contDiffOn_const]
      simp only [multiPartial, Multiset.sort_singleton, partialWord, fderiv_const_apply,
        zero_apply]
      exact (regularLp_const Ω p (0 : 𝕜)).symm
  obtain ⟨v, hv⟩ := (Set.ext_iff.mp (sobolev_range (𝕜 := 𝕜) Ω 1 p) f).mpr hmem
  refine ⟨v, hv, ?_⟩
  apply PiLp.ext
  intro α
  rw [positiveDerivatives_apply]
  split_ifs with h
  · rfl
  · have hc : α.val.card = 1 := by
      have hzero : α.val ≠ 0 := fun he => h (Subtype.ext he)
      have := Multiset.card_pos.mpr hzero
      have := α.property
      omega
    obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp hc
    have hidx : α = firstIndex i := Subtype.ext hi
    have hd := sobolev_derivative_distribution Ω 1 p v α
    rw [hv, regularLp_const Ω p c] at hd
    rw [hi, derivative_classicalCompatibility d 𝕜 Ω {i} (fun _ => c)
      contDiffOn_const] at hd
    simp only [multiPartial, Multiset.sort_singleton, partialWord, fderiv_const_apply,
      zero_apply] at hd
    apply regularLp_injective Ω p
    exact hd.symm.trans (regularLp_const Ω p (0 : 𝕜)).symm

/-- Each coordinate is dominated by the Euclidean gradient, so the tuple's
positive-order sum norm has a fixed finite-dimensional bound. -/
lemma positive_le_gradient (u : Sobolev 𝕜 Ω 1 p) :
    ‖positiveDerivatives Ω p u‖ ≤ (Fintype.card (SobolevIndex d 1) : ℝ) *
      (eLpNorm (weakGradientOn u) p (volume.restrict (Ω : Set (Space d)))).toReal := by
  let g := (weakGradientOn_memLp u).toLp (weakGradientOn u)
  have hgn : ‖g‖ = (eLpNorm (weakGradientOn u) p
      (volume.restrict (Ω : Set (Space d)))).toReal := Lp.norm_toLp _ _
  rw [← hgn, PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _α : SobolevIndex d 1, ‖g‖ := by
      apply Finset.sum_le_sum
      intro α _
      rw [positiveDerivatives_apply]
      split_ifs with h
      · simpa only [norm_zero] using norm_nonneg g
      · have hzero : α.val ≠ 0 := fun he => h (Subtype.ext he)
        have hc : α.val.card = 1 := by
          have := Multiset.card_pos.mpr hzero
          have := α.property
          omega
        obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp hc
        have he : α = firstIndex i := Subtype.ext hi
        rw [he]
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [(weakGradientOn_memLp u).coeFn_toLp] with x hx
        change g x = weakGradientOn u x at hx
        rw [hx]
        exact PiLp.norm_apply_le (weakGradientOn u x) i
    _ = _ := by simp

lemma zero_of_integral_zero_of_positive_zero
    (hconn : IsPreconnected (Ω : Set (Space d)))
    (hV : (volume (Ω : Set (Space d))).toReal ≠ 0)
    (u : Sobolev 𝕜 Ω 1 p) (hI : integralLp Ω p (sobolevUnderlying u) = 0)
    (hD : positiveDerivatives Ω p u = 0) : u = 0 := by
  have hd (i : Fin d) : distributionPartial {i}
      (regularDistribution Ω (sobolevUnderlying u)) = 0 := by
    have hi : firstIndex i ≠ zeroSobolevIndex d 1 := by
      intro h
      have := congrArg Subtype.val h
      simp [firstIndex, zeroSobolevIndex] at this
    have hz : sobolevDerivative u (firstIndex i) = 0 := by
      have := congrArg (fun v : SobolevTuple 𝕜 Ω 1 p => v (firstIndex i)) hD
      simpa only [positiveDerivatives_apply, ite_eq_right hi, WithLp.ofLp_zero, Pi.zero_apply] using this
    have he := sobolev_derivative_distribution Ω 1 p u (firstIndex i)
    change distributionPartial {i} _ = _ at he
    rw [he, hz, regularLp_zero Ω p]
  obtain ⟨c, hc⟩ := zero_gradient_constant d 𝕜 Ω (sobolevUnderlying u) hconn
    (domainLp_locallyIntegrable Ω p _) hd
  have hic : (volume (Ω : Set (Space d))).toReal • c = 0 := by
    rw [integralLp_eq Ω p] at hI
    have hh := integral_congr_ae hc
    rw [integral_const] at hh
    simpa only [Measure.real, Measure.restrict_apply_univ] using hh.symm.trans hI
  have hc0 : c = 0 := (smul_eq_zero.mp hic).resolve_left hV
  apply sobolevUnderlying_injective Ω 1 p
  apply Lp.ext
  exact (hc.trans (Eventually.of_forall fun _ => hc0)).trans (Lp.coeFn_zero _ _ _).symm

/-- Rellich and the independently proved zero-gradient theorem yield the
mean-zero estimate on the closed kernel of the integral functional. -/
lemma mean_zero_estimate
    (hcompact : Rellich.CompactLpInclusion 𝕜 Ω p p)
    (hconn : IsPreconnected (Ω : Set (Space d)))
    (hV : (volume (Ω : Set (Space d))).toReal ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Sobolev 𝕜 Ω 1 p,
      integralLp Ω p (sobolevUnderlying u) = 0 →
      ‖sobolevUnderlying u‖ ≤ C * ‖positiveDerivatives Ω p u‖ := by
  let J := (integralLp (𝕜 := 𝕜) Ω p).comp (sobolevUnderlyingCLM Ω 1 p)
  let Z : Submodule 𝕜 (Sobolev 𝕜 Ω 1 p) := J.ker
  letI : NormedSpace 𝕜 Z := inferInstance
  letI : CompleteSpace Z := J.isClosed_ker.completeSpace_coe
  let A : Z →L[𝕜] DomainLp 𝕜 Ω p := (sobolevUnderlyingCLM Ω 1 p).comp Z.subtypeL
  let B : Z →L[𝕜] SobolevTuple 𝕜 Ω 1 p := (positiveDerivatives Ω p).comp Z.subtypeL
  obtain ⟨I, _, hI, hIc⟩ := hcompact
  have heq : I = sobolevUnderlyingCLM (𝕜 := 𝕜) Ω 1 p := by
    apply ContinuousLinearMap.ext
    intro u
    exact Lp.ext (hI u)
  obtain ⟨C, hC, hb⟩ := @coercive_of_compact 𝕜 Z (DomainLp 𝕜 Ω p) (SobolevTuple 𝕜 Ω 1 p)
    _ _ (inferInstance : NormedSpace 𝕜 Z) _ _ _ _ _ A B (fun S hS => by
    have hs := hIc ((Z.subtypeL : Z →L[𝕜] Sobolev 𝕜 Ω 1 p) '' S) (isometry_subtype_coe.lipschitzWith.isBounded_image hS)
    rw [heq] at hs
    simpa only [A, ContinuousLinearMap.coe_comp, image_image, Function.comp_def] using hs)
    (fun u => by exact (norm_split Ω p u.val).le)
    (fun u hu => by
      apply Subtype.ext
      exact zero_of_integral_zero_of_positive_zero Ω p hconn hV u.val u.property hu)
  refine ⟨C, hC, fun u hu => ?_⟩
  have humem : u ∈ Z := hu
  exact (PiLp.norm_apply_le u.val (zeroSobolevIndex d 1)).trans (hb ⟨u, humem⟩)

end P102.Sobolev.MeanZeroPoincare

namespace P102.Sobolev.MeanZeroPoincare
open P102.U4

/-- Mean-zero Poincaré on every bounded connected Lipschitz open set,
including the empty set. The RHS uses the Euclidean weak gradient. -/
theorem inequality : Expected.Inequality := by
  intro m e Ω hΩ hconn 𝕜 _ p _ hp
  have hfinite : volume (Ω : Set (Space (m+1))) ≠ ⊤ :=
    (Rellich.bounded_domain e Ω hΩ).measure_lt_top.ne
  letI : IsFiniteMeasure (volume.restrict (Ω : Set (Space (m+1)))) :=
    isFiniteMeasure_restrict.mpr hfinite
  by_cases hne : (Ω : Set (Space (m+1))).Nonempty
  · have hV : (volume (Ω : Set (Space (m+1)))).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨(Ω.isOpen.measure_pos volume hne).ne', hfinite⟩
    obtain ⟨C, hC, hest⟩ := mean_zero_estimate Ω p
      (Rellich.same_exponent m e Ω hΩ 𝕜 p hp) hconn hV
    let N : ℝ := Fintype.card (SobolevIndex (m+1) 1)
    refine ⟨C * N, mul_nonneg hC (Nat.cast_nonneg _), fun u => ?_⟩
    let c := average Ω (sobolevUnderlying u)
    obtain ⟨v, hv, hDv⟩ := exists_constant Ω p c
    let w := u - v
    have hUw : sobolevUnderlying w = sobolevUnderlying u -
        Lp.const p (volume.restrict (Ω : Set (Space (m+1)))) c := by
      change (sobolevUnderlyingCLM Ω 1 p) (u - v) = _
      rw [map_sub]
      change sobolevUnderlying u - sobolevUnderlying v = _
      rw [hv]
    have hDc : positiveDerivatives Ω p w = positiveDerivatives Ω p u := by
      simp only [w, map_sub, hDv, sub_zero]
    have hIc : integralLp Ω p
        (Lp.const p (volume.restrict (Ω : Set (Space (m+1)))) c) =
        integralLp Ω p (sobolevUnderlying u) := by
      rw [integralLp_eq Ω p, integralLp_eq Ω p,
        integral_congr_ae (Lp.coeFn_const p _ c)]
      simp only [Function.const_apply, integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ]
      change (volume (Ω : Set (Space (m+1)))).toReal •
        ((volume (Ω : Set (Space (m+1)))).toReal⁻¹ • ∫ x in Ω, sobolevUnderlying u x) = _
      rw [smul_smul, mul_inv_cancel₀ hV, one_smul]
    have hIw : integralLp Ω p (sobolevUnderlying w) = 0 := by
      rw [hUw, map_sub, hIc, sub_self]
    have heq : (sobolevUnderlying w : Space (m+1) → 𝕜) =ᵐ[
        volume.restrict (Ω : Set (Space (m+1)))]
        fun x => sobolevUnderlying u x - average Ω (sobolevUnderlying u) := by
      rw [hUw]
      filter_upwards [Lp.coeFn_sub (sobolevUnderlying u)
        (Lp.const p (volume.restrict (Ω : Set (Space (m+1)))) c), Lp.coeFn_const p _ c]
        with x hx hc
      exact hx.trans (congrArg (fun z => sobolevUnderlying u x - z) hc)
    rw [← eLpNorm_congr_ae heq, ← Lp.norm_def]
    calc
      ‖sobolevUnderlying w‖ ≤ C * ‖positiveDerivatives Ω p w‖ := hest w hIw
      _ = C * ‖positiveDerivatives Ω p u‖ := by rw [hDc]
      _ ≤ C * (N * (eLpNorm (weakGradientOn u) p
          (volume.restrict (Ω : Set (Space (m+1))))).toReal) :=
        mul_le_mul_of_nonneg_left (positive_le_gradient Ω p u) hC
      _ = _ := by ring
  · have he : (Ω : Set (Space (m+1))) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, le_rfl, fun u => ?_⟩
    simp [he]

end P102.Sobolev.MeanZeroPoincare
