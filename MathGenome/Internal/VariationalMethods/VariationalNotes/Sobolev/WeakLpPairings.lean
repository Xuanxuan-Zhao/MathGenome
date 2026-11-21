import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.WeakLpPairings
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Basic.Real.ConjExponents

open MeasureTheory Filter
open scoped Topology ENNReal

namespace VariationalNotes

/-- Every continuous linear functional is a continuous test for weak convergence. -/
theorem weak_tendsto_test {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {vₙ : ℕ → E} {v : E}
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ E (vₙ n)) atTop
      (𝓝 (toWeakSpace ℝ E v))) (f : E →L[ℝ] ℝ) :
    Tendsto (fun n ↦ f (vₙ n)) atTop (𝓝 (f v)) := by
  exact (WeakBilin.eval_continuous (topDualPairing ℝ E).flip f).tendsto _ |>.comp hv

/-- Weakly convergent sequences are norm bounded, without assuming completeness
of the original space. Uniform boundedness is applied on its complete dual. -/
theorem weak_tendsto_norm_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {vₙ : ℕ → E} {v : E}
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ E (vₙ n)) atTop
      (𝓝 (toWeakSpace ℝ E v))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖vₙ n‖ ≤ C := by
  have hpoint : ∀ f : E →L[ℝ] ℝ, ∃ C : ℝ, ∀ n,
      ‖NormedSpace.inclusionInDoubleDual ℝ E (vₙ n) f‖ ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ (weak_tendsto_test hv f)).exists_norm_le
    exact ⟨C, fun n ↦ hC _ ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  have hnorm (n : ℕ) : ‖vₙ n‖ ≤ C := by
    calc
      ‖vₙ n‖ = ‖(NormedSpace.inclusionInDoubleDualLi ℝ) (vₙ n)‖ :=
        ((NormedSpace.inclusionInDoubleDualLi ℝ).norm_map _).symm
      _ = ‖NormedSpace.inclusionInDoubleDual ℝ E (vₙ n)‖ := rfl
      _ ≤ C := hC n
  exact ⟨C, (norm_nonneg (vₙ 0)).trans (hnorm 0), hnorm⟩

/-- Evaluation converges when the functionals converge in norm and their arguments
converge weakly. -/
theorem tendsto_dual_apply_of_strong_weak {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {fₙ : ℕ → E →L[ℝ] ℝ} {f : E →L[ℝ] ℝ} {vₙ : ℕ → E} {v : E}
    (hf : Tendsto fₙ atTop (𝓝 f))
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ E (vₙ n)) atTop
      (𝓝 (toWeakSpace ℝ E v))) :
    Tendsto (fun n ↦ fₙ n (vₙ n)) atTop (𝓝 (f v)) := by
  obtain ⟨C, hC, hvC⟩ := weak_tendsto_norm_bounded hv
  have herr : Tendsto (fun n ↦ (fₙ n - f) (vₙ n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦
      ((fₙ n - f).le_opNorm (vₙ n)).trans
        (mul_le_mul_of_nonneg_left (hvC n) (norm_nonneg _)))
    simpa using ((hf.sub (tendsto_const_nhds (x := f))).norm.mul_const C)
  have hsum := herr.add (weak_tendsto_test hv f)
  simpa only [sub_apply, sub_add_cancel, zero_add] using hsum

/-- A uniformly bounded, a.e. convergent sequence converges in every finite
`Lʳ`, `1 ≤ r`. The domination is by a constant integrable function; the base
measure needs no completeness or countable-generation hypothesis. -/
theorem tendsto_eLpNorm_of_ae_bounded {S E : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsFiniteMeasure μ] [NormedAddCommGroup E]
    {r : ℝ≥0∞} (hr : 1 ≤ r) (hrtop : r ≠ ∞)
    {bₙ : ℕ → S → E} {b : S → E}
    (hbₙ : ∀ n, AEStronglyMeasurable (bₙ n) μ) (hb : AEStronglyMeasurable b μ)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ bₙ n x) atTop (𝓝 (b x)))
    {M : ℝ} (hboundₙ : ∀ n, ∀ᵐ x ∂μ, ‖bₙ n x‖ ≤ M)
    (hbound : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) :
    Tendsto (fun n ↦ eLpNorm (bₙ n - b) r μ) atTop (𝓝 0) := by
  have hconst := unifIntegrable_const (ι := ℕ) hr hrtop
    (memLp_const M : MemLp (fun _ : S ↦ M) r μ)
  have hui : UnifIntegrable bₙ r μ := by
    apply unifIntegrable_iff.2
    intro ε hε
    obtain ⟨δ, hδ, hδbound⟩ := unifIntegrable_iff.1 hconst ε hε
    refine ⟨δ, hδ, fun n s hs ↦ ?_⟩
    apply le_trans (eLpNorm_mono_ae (g := fun _ : S ↦ M) (hbₙ n).restrict ?_)
      (hδbound n s hs)
    filter_upwards [(hboundₙ n).filter_mono ae_restrict_le] with x hx
    exact hx.trans (le_abs_self M)
  exact tendsto_Lp_finite_of_tendsto_ae hr hrtop hbₙ (MemLp.of_bound hb M hbound) hui hconv

/-- Bounded variable coefficients pair continuously with weakly convergent `Lᵖ`
sequences on every finite measure space, for `1 < p < ∞`. -/
theorem bounded_weakLp_pairing : Specs.BoundedWeakLpPairing := by
  intro S _ μ _ D p hp hptop
  let : Fact (1 ≤ p) := ⟨hp.le⟩
  intro vₙ v bₙ b hv hbₙ hb hconv hbound
  obtain ⟨M, hM, hbound⟩ := hbound
  let H := EuclideanSpace ℝ (Fin D)
  let r := ENNReal.conjExponent p
  have hr : 1 ≤ r := ENNReal.HolderConjugate.one_le r p
  have hrtop : r ≠ ∞ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt r p).2 hp).ne
  let : Fact (1 ≤ r) := ⟨hr⟩
  have hboundₙ (n : ℕ) : ∀ᵐ x ∂μ, ‖bₙ n x‖ ≤ M :=
    hbound.mono fun _ hx ↦ hx.1 n
  have hboundb : ∀ᵐ x ∂μ, ‖b x‖ ≤ M := hbound.mono fun _ hx ↦ hx.2
  have hbₙLp (n : ℕ) : MemLp (bₙ n) r μ :=
    MemLp.of_bound (hbₙ n).aestronglyMeasurable M (hboundₙ n)
  have hbLp : MemLp b r μ := MemLp.of_bound hb.aestronglyMeasurable M hboundb
  have hcoef : Tendsto (fun n ↦ (hbₙLp n).toLp (bₙ n)) atTop
      (𝓝 (hbLp.toLp b)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' bₙ hbₙLp b hbLp).2
    exact tendsto_eLpNorm_of_ae_bounded hr hrtop
      (fun n ↦ (hbₙ n).aestronglyMeasurable) hb.aestronglyMeasurable
      hconv hboundₙ hboundb
  let B : H →L[ℝ] H →L[ℝ] ℝ := innerSL ℝ
  let P : Lp H r μ →L[ℝ] Lp H p μ →L[ℝ] ℝ := B.lpPairing μ r p
  have hP (c : S → H) (hc : MemLp c r μ) (w : Lp H p μ) :
      P (hc.toLp c) w = ∫ x, inner ℝ (c x) (w x) ∂μ := by
    change B.lpPairing μ r p (hc.toLp c) w = _
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hc.coeFn_toLp] with x hx
    rw [hx]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact memLp_one_iff_integrable.1 (B.memLp_of_bilin 1 (hbₙLp n) (Lp.memLp (vₙ n)))
  · exact memLp_one_iff_integrable.1 (B.memLp_of_bilin 1 hbLp (Lp.memLp v))
  · have hdual := P.continuous.tendsto (hbLp.toLp b) |>.comp hcoef
    have hpair := tendsto_dual_apply_of_strong_weak hdual hv
    simpa only [Function.comp_apply, hP] using hpair

end VariationalNotes
