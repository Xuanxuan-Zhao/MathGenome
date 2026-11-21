import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.BirkhoffConvergence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.DenseCoboundaries
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.MaximalLemma
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace D13Unified.Ch19.BirkhoffConvergence
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  (T : X → X) (hT : MeasurePreserving T μ μ)

lemma dense_convergence (d : Lp ℝ 1 μ)
    (hd : d ∈ DenseCoboundaries.boundedCoboundaries 1 T μ hT) :
    (∃ v : Lp ℝ 1 μ, Tendsto (fun n => CompositionIsometry.average ℝ 1 T μ hT n d)
      atTop (𝓝 v)) ∧
    (∀ᵐ x ∂μ, CauchySeq (fun n => MeasureDefinitions.ergodicAverage T (d : X → ℝ) n x)) := by
  obtain ⟨v, g, hv, hg, hi, rfl⟩ := hd
  have hc := DenseCoboundaries.convergence T μ hT v g hv hg hi
  exact ⟨⟨v, hc.2⟩, hc.1.mono fun x hx => hx.2.2.cauchySeq⟩

/-- The contraction bound extends norm convergence from the dense class.
This uses Banach completeness of L¹, independently of pointwise convergence. -/
lemma l1_convergence (f : Lp ℝ 1 μ) :
    ∃ g : Lp ℝ 1 μ, Tendsto (fun n => CompositionIsometry.average ℝ 1 T μ hT n f)
      atTop (𝓝 g) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨d, hd, hfd⟩ := (DenseCoboundaries.dense_l1 T hT).exists_dist_lt f (by linarith : 0 < ε / 3)
  obtain ⟨v, hv⟩ := (dense_convergence T hT d hd).1
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hv.cauchySeq (ε / 3) (by linarith)
  refine ⟨N, fun m hm n hn => ?_⟩
  let A := CompositionIsometry.average ℝ 1 T μ hT
  have hb (j : ℕ) : dist (A j f) (A j d) ≤ dist f d := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact CompositionIsometry.average_norm_le ℝ 1 T μ hT j (f - d)
  calc
    dist (A m f) (A n f) ≤ dist (A m f) (A m d) +
        dist (A m d) (A n d) + dist (A n d) (A n f) := dist_triangle4 _ _ _ _
    _ < ε := by
      have := hb m
      have := hb n
      have := hN m hm n hn
      rw [dist_comm (A n d) (A n f)]
      linarith

omit [IsProbabilityMeasure μ] in
lemma integral_norm_sub (f d : Lp ℝ 1 μ) :
    (∫ x, ‖f x - d x‖ ∂μ) = ‖f - d‖ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f d] with x hx
  rw [hx]
  rfl

omit hT [MeasurableSpace X] in
lemma norm_average_le (f : X → ℝ) (n : ℕ) (x : X) :
    ‖MeasureDefinitions.ergodicAverage T f n x‖ ≤
      MeasureDefinitions.ergodicAverage T (fun y => ‖f y‖) n x := by
  change ‖(n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, f (T^[j] x)‖ ≤
    (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, ‖f (T^[j] x)‖
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

include hT in
/-- Summable maximal-error sets give uniform-in-time approximation at almost
every point. Convergence of the approximants then makes the averages Cauchy. -/
lemma pointwise_cauchy (f : Lp ℝ 1 μ) :
    ∀ᵐ x ∂μ, CauchySeq (fun n => MeasureDefinitions.ergodicAverage T (f : X → ℝ) n x) := by
  let r : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  have hr (k : ℕ) : 0 < r k := by dsimp [r]; positivity
  have hd (k : ℕ) : ∃ d ∈ DenseCoboundaries.boundedCoboundaries 1 T μ hT,
      dist f d < r k * r k :=
    (DenseCoboundaries.dense_l1 T hT).exists_dist_lt f (mul_pos (hr k) (hr k))
  choose d hd hdist using hd
  let E (k : ℕ) := MaximalLemma.maximalAverageSet T (fun x => f x - d k x) (r k)
  have hE (k : ℕ) : μ (E k) ≤ ENNReal.ofReal (r k) := by
    have hi : Integrable (fun x => f x - d k x) μ :=
      (Lp.memLp f).integrable (by rfl) |>.sub ((Lp.memLp (d k)).integrable (by rfl))
    have hb := (MaximalLemma.maximal_inequality ℝ T μ hT _ hi (r k) (hr k)).2
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    rw [integral_norm_sub]
    apply (div_le_iff₀ (hr k)).mpr
    simpa only [dist_eq_norm] using (hdist k).le
  have hsum : (∑' k, μ (E k)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hE)
    simp only [r, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num [ENNReal.ofReal_div_of_pos, ENNReal.tsum_geometric]
  have hbc := ae_eventually_notMem hsum
  have hdc : ∀ᵐ x ∂μ, ∀ k, CauchySeq
      (fun n => MeasureDefinitions.ergodicAverage T (d k : X → ℝ) n x) :=
    ae_all_iff.mpr fun k => (dense_convergence T hT (d k) (hd k)).2
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  filter_upwards [hbc, hdc] with x hx hcx
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨k, hk, hkr⟩ := (hx.and (hr0.eventually (gt_mem_nhds (by linarith : 0 < ε / 3)))).exists
  have hclose (n : ℕ) : dist (MeasureDefinitions.ergodicAverage T (f : X → ℝ) n x)
      (MeasureDefinitions.ergodicAverage T (d k : X → ℝ) n x) ≤ r k := by
    rw [dist_eq_norm]
    change ‖birkhoffAverage ℝ T (f : X → ℝ) n x -
      birkhoffAverage ℝ T (d k : X → ℝ) n x‖ ≤ r k
    rw [← birkhoffAverage_sub_apply]
    apply (norm_average_le T (fun y => f y - d k y) n x).trans
    by_cases hn : 0 < n
    · exact le_of_not_gt (fun h => hk ⟨n, hn, h⟩)
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simpa [MeasureDefinitions.ergodicAverage,
        Specs.D13Unified.Ch19.MeasureDefinitions.ergodicAverage] using (hr k).le
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hcx k) (ε / 3) (by linarith)
  refine ⟨N, fun m hm n hn => ?_⟩
  calc
    _ ≤ dist (MeasureDefinitions.ergodicAverage T (f : X → ℝ) m x)
        (MeasureDefinitions.ergodicAverage T (d k : X → ℝ) m x) +
        dist (MeasureDefinitions.ergodicAverage T (d k : X → ℝ) m x)
        (MeasureDefinitions.ergodicAverage T (d k : X → ℝ) n x) +
        dist (MeasureDefinitions.ergodicAverage T (d k : X → ℝ) n x)
        (MeasureDefinitions.ergodicAverage T (f : X → ℝ) n x) := dist_triangle4 _ _ _ _
    _ < ε := by
      have hm' := hclose m
      have hn' := hclose n
      have hmn := hN m hm n hn
      rw [dist_comm (MeasureDefinitions.ergodicAverage T (d k : X → ℝ) n x)]
      linarith

include hT in
/-- Both kinds of convergence have the same L¹ limit. A subsequence of the
norm-convergent sequence identifies the pointwise Cauchy limit. -/
lemma real_lp_convergence (f : Lp ℝ 1 μ) :
    ∃ g : Lp ℝ 1 μ,
      (∀ᵐ x ∂μ, Tendsto (fun n => MeasureDefinitions.ergodicAverage T (f : X → ℝ) n x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun n => ∫ x, ‖MeasureDefinitions.ergodicAverage T (f : X → ℝ) n x - g x‖ ∂μ)
        atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := l1_convergence T hT f
  obtain ⟨ns, hns, hs⟩ := (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  have hav : ∀ᵐ x ∂μ, ∀ n, CompositionIsometry.average ℝ 1 T μ hT n f x =
      MeasureDefinitions.ergodicAverage T (f : X → ℝ) n x :=
    ae_all_iff.mpr fun n => CompositionIsometry.average_ae ℝ 1 T μ hT n f
  refine ⟨g, ?_, ?_⟩
  · filter_upwards [pointwise_cauchy T hT f, hs, hav] with x hc hx ha
    exact tendsto_nhds_of_cauchySeq_of_subseq hc hns.tendsto_atTop
      (hx.congr fun n => ha (ns n))
  · have heq (n : ℕ) :
        (∫ x, ‖MeasureDefinitions.ergodicAverage T (f : X → ℝ) n x - g x‖ ∂μ) =
        ‖CompositionIsometry.average ℝ 1 T μ hT n f - g‖ := by
      rw [L1.norm_eq_integral_norm]
      apply integral_congr_ae
      filter_upwards [CompositionIsometry.average_ae ℝ 1 T μ hT n f,
        Lp.coeFn_sub (CompositionIsometry.average ℝ 1 T μ hT n f) g] with x ha hs
      rw [hs, Pi.sub_apply, ha]
    simpa only [heq] using (tendsto_iff_norm_sub_tendsto_zero.mp hg)

theorem real_convergence : Specs.D13Unified.Ch19.BirkhoffConvergence.real_convergenceStatement := by
  intro X _ T μ _ hT f hf
  let F := hf.toL1 f
  obtain ⟨g, hga, hgn⟩ := real_lp_convergence T hT F
  have hF : (F : X → ℝ) =ᵐ[μ] f := hf.coeFn_toL1
  have ha (n : ℕ) : MeasureDefinitions.ergodicAverage T (F : X → ℝ) n =ᵐ[μ]
      MeasureDefinitions.ergodicAverage T f n :=
    hT.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hF n
  refine ⟨g, (Lp.memLp g).integrable (by rfl), ?_, ?_⟩
  · filter_upwards [hga, ae_all_iff.mpr ha] with x hx hax
    exact hx.congr (fun n => hax n)
  · apply hgn.congr
    intro n
    apply integral_congr_ae
    filter_upwards [ha n] with x hx
    rw [hx]

omit hT [MeasurableSpace X] in
lemma average_re (f : X → ℂ) (n : ℕ) (x : X) :
    (MeasureDefinitions.ergodicAverage T f n x).re =
      MeasureDefinitions.ergodicAverage T (fun y => (f y).re) n x := by
  simp [MeasureDefinitions.ergodicAverage,
    Specs.D13Unified.Ch19.MeasureDefinitions.ergodicAverage, birkhoffAverage, birkhoffSum]

omit hT [MeasurableSpace X] in
lemma average_im (f : X → ℂ) (n : ℕ) (x : X) :
    (MeasureDefinitions.ergodicAverage T f n x).im =
      MeasureDefinitions.ergodicAverage T (fun y => (f y).im) n x := by
  simp [MeasureDefinitions.ergodicAverage,
    Specs.D13Unified.Ch19.MeasureDefinitions.ergodicAverage, birkhoffAverage, birkhoffSum]

omit [IsProbabilityMeasure μ] in
include hT in
lemma integrable_average {𝕜 : Type*} [RCLike 𝕜] (f : X → 𝕜) (hf : Integrable f μ) (n : ℕ) :
    Integrable (MeasureDefinitions.ergodicAverage T f n) μ := by
  change Integrable ((n : ℝ)⁻¹ • birkhoffSum T f n) μ
  apply Integrable.smul
  change Integrable (fun x => ∑ j ∈ Finset.range n, f (T^[j] x)) μ
  exact integrable_finsetSum _ fun j _ => (hT.iterate j).integrable_comp_of_integrable hf

theorem complex_convergence : Specs.D13Unified.Ch19.BirkhoffConvergence.complex_convergenceStatement := by
  intro X _ T μ _ hT f hf
  obtain ⟨g, hg, hga, hgn⟩ := real_convergence T μ hT (fun x => (f x).re) hf.re
  obtain ⟨h, hh, hha, hhn⟩ := real_convergence T μ hT (fun x => (f x).im) hf.im
  let l : X → ℂ := fun x => (g x : ℂ) + (h x : ℂ) * Complex.I
  have hl : Integrable l μ := hg.ofReal.add (hh.ofReal.mul_const Complex.I)
  refine ⟨l, hl, ?_, ?_⟩
  · filter_upwards [hga, hha] with x hx hy
    have hx' := Complex.continuous_ofReal.continuousAt.tendsto.comp hx
    have hy' := Complex.continuous_ofReal.continuousAt.tendsto.comp hy
    have ht := hx'.add (hy'.mul_const Complex.I)
    apply ht.congr
    intro n
    change Complex.ofReal (MeasureDefinitions.ergodicAverage T (fun y => (f y).re) n x) +
      Complex.ofReal (MeasureDefinitions.ergodicAverage T (fun y => (f y).im) n x) * Complex.I =
      MeasureDefinitions.ergodicAverage T f n x
    rw [← average_re, ← average_im, Complex.re_add_im]
  · have hb (n : ℕ) :
        (∫ x, ‖MeasureDefinitions.ergodicAverage T f n x - l x‖ ∂μ) ≤
          (∫ x, ‖MeasureDefinitions.ergodicAverage T (fun y => (f y).re) n x - g x‖ ∂μ) +
          (∫ x, ‖MeasureDefinitions.ergodicAverage T (fun y => (f y).im) n x - h x‖ ∂μ) := by
      have hR : Integrable (fun x =>
          ‖MeasureDefinitions.ergodicAverage T (fun y => (f y).re) n x - g x‖) μ :=
        ((integrable_average T hT _ hf.re n).sub hg).norm
      have hI : Integrable (fun x =>
          ‖MeasureDefinitions.ergodicAverage T (fun y => (f y).im) n x - h x‖) μ :=
        ((integrable_average T hT _ hf.im n).sub hh).norm
      rw [← integral_add hR hI]
      apply integral_mono ((integrable_average T hT f hf n).sub hl).norm
        (((integrable_average T hT _ hf.re n).sub hg).norm.add
          ((integrable_average T hT _ hf.im n).sub hh).norm)
      intro x
      simpa [Complex.sub_re, Complex.sub_im, average_re, average_im,
        l, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add,
        Real.norm_eq_abs, Pi.sub_apply, Pi.add_apply] using
        Complex.norm_le_abs_re_add_abs_im (MeasureDefinitions.ergodicAverage T f n x - l x)
    exact squeeze_zero (fun n => integral_nonneg fun x => norm_nonneg _) hb
      (by simpa only [add_zero] using hgn.add hhn)

end
end D13Unified.Ch19.BirkhoffConvergence
