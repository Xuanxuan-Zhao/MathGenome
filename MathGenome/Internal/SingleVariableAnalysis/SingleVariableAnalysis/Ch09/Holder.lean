import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Holder
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Products
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Young
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Hölder's finite proper-integral inequality (K03.09.holder, paper.tex:2614–2638).

The integral throughout is the existing Darboux integral, not a measure integral.
Continuous composition on bounded ranges proves all positive absolute-power
integrability assertions. For a tagged partition with cell lengths w_i, apply
Mathlib's finite Hölder inequality to w_i^(1/p)|f(ξ_i)| and
w_i^(1/q)|g(ξ_i)|. The weight powers multiply to w_i and their p-th/q-th
powers recover w_i. Pass to the three Darboux values along a common sequence
of meshes tending to zero. Continuity of the nonnegative root powers also
holds at zero. The zero-seminorm conclusion then follows from this inequality
and positivity of the integral; no pointwise zero assertion is used.

The finite library inequality is proved from Young's inequality, with separate
zero finite-sum cases (Mathlib.Analysis.MeanInequalities). The canonical real
powers at nonnegative bases agree with the source exp/log construction and
its extension at zero by the imported chapter-09 Young bridge. This proof
route replaces the manuscript's normalization of integral values by finite
normalization before taking tagged-sum limits.
-/

namespace SingleVariableAnalysis.Riemann
open scoped BigOperators Topology
open Filter

/-- Finite Hölder with nonnegative weights, including the empty sum. -/
theorem weighted_holder {ι : Type*} (s : Finset ι) (w u v : ι → ℝ)
    {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, 0 ≤ u i)
    (hv : ∀ i ∈ s, 0 ≤ v i) :
    (∑ i ∈ s, w i * (u i * v i)) ≤
      (∑ i ∈ s, w i * u i ^ p) ^ (1 / p) *
      (∑ i ∈ s, w i * v i ^ q) ^ (1 / q) := by
  have hconj : p.HolderConjugate q :=
    Real.holderConjugate_iff.mpr ⟨hp, by simpa only [one_div] using hpq⟩
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hconj
    (f := fun i => w i ^ (1 / p) * u i)
    (g := fun i => w i ^ (1 / q) * v i)
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hw i hi) _) (hu i hi))
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hw i hi) _) (hv i hi))
  have hleft : (∑ i ∈ s, (w i ^ (1 / p) * u i) * (w i ^ (1 / q) * v i)) =
      ∑ i ∈ s, w i * (u i * v i) := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (w i ^ (1 / p) * w i ^ (1 / q)) * (u i * v i) := by ring
      _ = _ := by
        rw [← Real.rpow_add_of_nonneg (hw i hi) (by positivity : 0 ≤ 1 / p)
          (by positivity : 0 ≤ 1 / q), hpq, Real.rpow_one]
  have hpower (r : ℝ) (hr : 1 < r) (z : ι → ℝ) (hz : ∀ i ∈ s, 0 ≤ z i) :
      (∑ i ∈ s, (w i ^ (1 / r) * z i) ^ r) = ∑ i ∈ s, w i * z i ^ r := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i hi) _) (hz i hi)]
    congr 1
    simpa only [one_div] using Real.rpow_inv_rpow (hw i hi) (ne_of_gt (lt_trans zero_lt_one hr))
  rwa [hleft, hpower p hp u hu, hpower q hq v hv] at h

/-- Continuous real composition on the actual bounded range of an integrable function. -/
theorem RealIntegrable.continuous_comp {f : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    RealIntegrable (fun x => Φ (f x)) a b := by
  obtain ⟨M, hM⟩ := hf.bounded.abs_bound
  exact real_composition hf hΦ.continuousOn (fun x hx => abs_le.mp (hM x hx))

/-- Every nonnegative real power is integrable; in particular all positive powers are. -/
theorem RealIntegrable.rpow {f : ℝ → ℝ} {a b r : ℝ}
    (hf : RealIntegrable f a b) (hr : 0 ≤ r) :
    RealIntegrable (fun x => f x ^ r) a b :=
  hf.continuous_comp (Real.continuous_rpow_const hr)

/-- Fine tagged convergence gives convergence along any sequence of meshes tending to zero. -/
theorem FineTaggedLimit.tendsto {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    {f : ℝ → E} {a b : ℝ} {I : E} (hf : FineTaggedLimit f a b I)
    (P : ℕ → Partition a b) (ξ : ∀ n, Tagging (P n))
    (hmesh : Tendsto (fun n => mesh (P n)) atTop (𝓝 0)) :
    Tendsto (fun n => taggedSum (P n) (ξ n) f) atTop (𝓝 I) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := hf ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmesh.eventually (gt_mem_nhds hδ))
  exact ⟨N, fun n hn => by simpa only [dist_eq_norm] using hc (P n) (ξ n) (hN n hn)⟩

/-- A common sequence of tagged partitions can test several integrands at once. -/
theorem exists_tagged_partition_sequence {a b : ℝ} (hab : a ≤ b) :
    ∃ (P : ℕ → Partition a b) (_ξ : ∀ n, Tagging (P n)),
      Tendsto (fun n => mesh (P n)) atTop (𝓝 0) := by
  have hP (n : ℕ) : ∃ P : Partition a b, mesh P < 1 / ((n : ℝ) + 1) :=
    exists_fine_partition hab _ (by positivity)
  choose P hP using hP
  let ξ : ∀ n, Tagging (P n) := fun n => Classical.choice (tags_exist (P n))
  refine ⟨P, ξ, ?_⟩
  exact squeeze_zero (fun n => (mesh_maximum (P n)).1) (fun n => (hP n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Hölder for nonnegative Riemann integrands, obtained from finite weighted
Hölder on a common tagged partition sequence. No positive-integral premise is used. -/
theorem holder_nonneg {f g : ℝ → ℝ} {a b p q : ℝ}
    (hf : RealIntegrable f a b) (_hg : RealIntegrable g a b)
    (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (hf0 : ∀ x ∈ Set.Icc a b, 0 ≤ f x) (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x)
    (hfg : RealIntegrable (fun x => f x * g x) a b)
    (hfp : RealIntegrable (fun x => f x ^ p) a b)
    (hgq : RealIntegrable (fun x => g x ^ q) a b) :
    realIntegral _ hfg ≤ realIntegral _ hfp ^ (1 / p) * realIntegral _ hgq ^ (1 / q) := by
  obtain ⟨P, ξ, hm⟩ := exists_tagged_partition_sequence hf.ordered
  have hlim {h : ℝ → ℝ} (hh : RealIntegrable h a b) :
      Tendsto (fun n => taggedSum (P n) (ξ n) h) atTop (𝓝 (realIntegral h hh)) :=
    ((real_tagged_equivalence h hh.ordered hh.bounded _).mp ⟨hh, rfl⟩).tendsto P ξ hm
  have hright := ((Real.continuous_rpow_const (show 0 ≤ 1 / p by positivity)).tendsto
    (realIntegral _ hfp)).comp (hlim hfp)
  have hright' := ((Real.continuous_rpow_const (show 0 ≤ 1 / q by positivity)).tendsto
    (realIntegral _ hgq)).comp (hlim hgq)
  apply le_of_tendsto_of_tendsto (hlim hfg) (hright.mul hright')
  exact Filter.Eventually.of_forall fun n => by
    have htag (i : Fin (P n).n) : (ξ n i : ℝ) ∈ Set.Icc a b :=
      cell_subset_interval (P n) i (ξ n i).property
    simpa only [taggedSum, S.sumValue, smul_eq_mul, Function.comp_apply] using
      weighted_holder Finset.univ (cellLength (P n)) (fun i => f (ξ n i))
        (fun i => g (ξ n i)) hp hq hpq
        (fun i _ => (cell_positive (P n) i).le)
        (fun i _ => hf0 _ (htag i)) (fun i _ => hg0 _ (htag i))

/-- Positivity for the existing proper real integral. -/
theorem realIntegral_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (h0 : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
    0 ≤ realIntegral f hf := by
  obtain ⟨hz, he⟩ := real_zero_value hf.ordered
  rw [← he]
  exact realIntegral_mono _ _ hz hf h0

/-- Scalar Hölder needs only integrability of the two norms. -/
theorem holder_of_norm_integrable {K : Type} [NormedField K]
    {f g : ℝ → K} {a b p q : ℝ}
    (hf : RealIntegrable (fun x => ‖f x‖) a b)
    (hg : RealIntegrable (fun x => ‖g x‖) a b)
    (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1) :
    Specs.SingleVariableAnalysis.Ch09.Holder.holderEstimate f g a b p q := by
  have hprod := real_product hf hg
  have hfg : RealIntegrable (fun x => ‖f x * g x‖) a b := by
    simpa only [norm_mul] using hprod
  have hfp := hf.rpow (le_trans zero_le_one hp.le)
  have hgq := hg.rpow (le_trans zero_le_one hq.le)
  have hi : realIntegral _ hfg ≤
      realIntegral _ hfp ^ (1 / p) * realIntegral _ hgq ^ (1 / q) := by
    simpa only [norm_mul] using holder_nonneg hf hg hp hq hpq
      (fun x _ => norm_nonneg _) (fun x _ => norm_nonneg _) hprod hfp hgq
  refine ⟨hfg, hfp, hgq, hi, ?_⟩
  intro hz
  apply le_antisymm _ (realIntegral_nonneg hfg (fun x _ => norm_nonneg _))
  rcases hz with hz | hz
  · simpa only [hz, zero_mul] using hi
  · simpa only [hz, mul_zero] using hi

theorem real_absolute_powers : Specs.SingleVariableAnalysis.Ch09.Holder.realAbsolutePowers := by
  intro f a b hf r hr
  exact (RealIntegrable.norm hf).rpow hr.le

theorem complex_absolute_powers : Specs.SingleVariableAnalysis.Ch09.Holder.complexAbsolutePowers := by
  intro f a b hf r hr
  exact (ComplexIntegrable.norm hf).rpow hr.le

theorem real_holder : Specs.SingleVariableAnalysis.Ch09.Holder.realHolder := by
  intro p q hp hq hpq f g a b hf hg
  exact holder_of_norm_integrable (RealIntegrable.norm hf) (RealIntegrable.norm hg) hp hq hpq

theorem complex_holder : Specs.SingleVariableAnalysis.Ch09.Holder.complexHolder := by
  intro p q hp hq hpq f g a b hf hg
  exact holder_of_norm_integrable (ComplexIntegrable.norm hf) (ComplexIntegrable.norm hg) hp hq hpq

/-- Convert the p=q=2 instance to the ordinary square-root form. -/
theorem cauchySchwarz_of_holder {K : Type} [NormedField K]
    {f g : ℝ → K} {a b : ℝ}
    (h : Specs.SingleVariableAnalysis.Ch09.Holder.holderEstimate f g a b 2 2) :
    Specs.SingleVariableAnalysis.Ch09.Holder.cauchySchwarzEstimate f g a b := by
  rcases h with ⟨hfg, hfp, hgq, hi, _⟩
  have hf2 : RealIntegrable (fun x => ‖f x‖ ^ (2 : ℕ)) a b := by
    simpa only [Real.rpow_two] using hfp
  have hg2 : RealIntegrable (fun x => ‖g x‖ ^ (2 : ℕ)) a b := by
    simpa only [Real.rpow_two] using hgq
  refine ⟨hfg, hf2, hg2, ?_⟩
  simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using hi

theorem real_cauchySchwarz : Specs.SingleVariableAnalysis.Ch09.Holder.realCauchySchwarz := by
  intro f g a b hf hg
  exact cauchySchwarz_of_holder (real_holder 2 2 (by norm_num) (by norm_num) (by norm_num) hf hg)

theorem complex_cauchySchwarz : Specs.SingleVariableAnalysis.Ch09.Holder.complexCauchySchwarz := by
  intro f g a b hf hg
  exact cauchySchwarz_of_holder (complex_holder 2 2 (by norm_num) (by norm_num) (by norm_num) hf hg)

end SingleVariableAnalysis.Riemann
