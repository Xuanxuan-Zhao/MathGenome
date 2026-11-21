import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsUniform
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsAlgebra
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.Variation
import Batteries.Tactic.OpenPrivate

namespace SingleVariableAnalysis.Stieltjes
open Riemann BV
open scoped BigOperators
open Filter
namespace U
export Specs.SingleVariableAnalysis.Ch15.RsUniform (supNormValue)
end U
noncomputable abbrev supNorm := @U.supNormValue

variable {K : Type} [RCLike K]

lemma supNorm_bddAbove {a b : ℝ} {h : ℝ → K} (hh : BoundedOn a b h) :
    BddAbove ((fun x => ‖h x‖) '' Set.Icc a b) := by
  obtain ⟨M, hM⟩ := hh
  exact ⟨M, by rintro y ⟨x, hx, rfl⟩; exact hM x hx⟩

lemma norm_le_supNorm {a b : ℝ} {h : ℝ → K} (hh : BoundedOn a b h)
    {x : ℝ} (hx : x ∈ Set.Icc a b) : ‖h x‖ ≤ supNorm a b h :=
  le_csSup (supNorm_bddAbove hh) ⟨x, hx, rfl⟩

lemma supNorm_nonneg {a b : ℝ} (hab : a ≤ b) {h : ℝ → K}
    (hh : BoundedOn a b h) : 0 ≤ supNorm a b h :=
  (norm_nonneg (h a)).trans (norm_le_supNorm hh ⟨le_rfl, hab⟩)

lemma supNorm_le {a b : ℝ} (hab : a ≤ b) {h : ℝ → K} {M : ℝ}
    (hM : ∀ x ∈ Set.Icc a b, ‖h x‖ ≤ M) : supNorm a b h ≤ M := by
  exact csSup_le ⟨_, ⟨a, ⟨le_rfl, hab⟩, rfl⟩⟩ (by
    rintro y ⟨x, hx, rfl⟩; exact hM x hx)

/-- A finite sum of absolute integrator increments is bounded by variation. -/
lemma sum_increments_le_variation {a b : ℝ} (P : Partition a b) (α : ℝ → ℝ)
    (hα : HasBoundedVariation α a b) :
    (∑ i : Fin P.n, ‖α (P.point i.succ) - α (P.point i.castSucc)‖) ≤
      (totalVariation α a b).toReal := by
  have hP : partitionSum P α ≤ totalVariation α a b :=
    le_iSup (fun Q : Partition a b => partitionSum Q α) P
  have hfin : totalVariation α a b ≠ ⊤ := ne_of_lt hα
  have := ENNReal.toReal_mono hfin hP
  simpa [Specs.SingleVariableAnalysis.Ch15.Variation.partitionSumValue,
    ENNReal.toReal_sum, ENNReal.toReal_ofReal, norm_nonneg] using this

lemma taggedSum_norm_le {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (h : ℝ → K) (α : ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hh : ∀ x ∈ Set.Icc a b, ‖h x‖ ≤ M) (hα : HasBoundedVariation α a b) :
    ‖taggedSum P t h α‖ ≤ M * (totalVariation α a b).toReal := by
  calc
    ‖taggedSum P t h α‖ ≤ ∑ i : Fin P.n,
        ‖(α (P.point i.succ) - α (P.point i.castSucc)) • h (t i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin P.n, M * ‖α (P.point i.succ) - α (P.point i.castSucc)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hh _ (tag_mem_interval P t i)) (norm_nonneg _)
    _ = M * ∑ i : Fin P.n, ‖α (P.point i.succ) - α (P.point i.castSucc)‖ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ M * (totalVariation α a b).toReal :=
      mul_le_mul_of_nonneg_left (sum_increments_le_variation P α hα) hM

lemma refinementLimit_norm_le {a b : ℝ} {h : ℝ → K} {α : ℝ → ℝ} {I : K}
    (hI : RefinementLimit a b h α I) {M : ℝ} (hM : 0 ≤ M)
    (hh : ∀ x ∈ Set.Icc a b, ‖h x‖ ≤ M) (hα : HasBoundedVariation α a b) :
    ‖I‖ ≤ M * (totalVariation α a b).toReal := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨P, hP⟩ := hI ε hε
  obtain ⟨t⟩ := tags_exist P
  have he := hP P (Finset.Subset.refl _) t
  have hb := taggedSum_norm_le P t h α hM hh hα
  have ht : ‖I‖ ≤ ‖taggedSum P t h α‖ + ‖taggedSum P t h α - I‖ := by
    have h := norm_add_le (I - taggedSum P t h α) (taggedSum P t h α)
    rw [sub_add_cancel, norm_sub_rev I, add_comm] at h
    exact h
  linarith

theorem integral_norm_bound : Specs.SingleVariableAnalysis.Ch15.RsUniform.integralBound := by
  intro K _ a b hab h α I hα hI
  have h := (integral_iff_of_le a b hab h α I).mp hI
  exact refinementLimit_norm_le h.2.2 (supNorm_nonneg hab h.1)
    (fun x hx => norm_le_supNorm h.1 hx) hα

lemma bounded_difference {a b : ℝ} {f g : ℝ → K}
    (hf : BoundedOn a b f) (hg : BoundedOn a b g) :
    BoundedOn a b (fun x => f x - g x) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  exact ⟨M + N, fun x hx => (norm_sub_le _ _).trans (add_le_add (hM x hx) (hN x hx))⟩

lemma uniform_limit_bounded {a b : ℝ} {F : ℕ → ℝ → K} {f : ℝ → K}
    (hF : ∀ n, BoundedOn a b (F n))
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc a b,
      ‖F n x - f x‖ < ε) : BoundedOn a b f := by
  obtain ⟨n, hn⟩ := hu 1 zero_lt_one
  obtain ⟨M, hM⟩ := hF n
  refine ⟨1 + M, fun x hx => ?_⟩
  have ht := norm_add_le (f x - F n x) (F n x)
  rw [sub_add_cancel, norm_sub_rev] at ht
  exact ht.trans (add_le_add (hn n le_rfl x hx).le (hM x hx))

lemma stieltjes_sum_sub {a b : ℝ} (P : Partition a b) (t : Tagging P)
    (f g : ℝ → K) (α : ℝ → ℝ) :
    taggedSum P t (fun x => f x - g x) α = taggedSum P t f α - taggedSum P t g α := by
  simp only [Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue,
    smul_sub, Finset.sum_sub_distrib]

/-- Uniform approximation transfers the directed Cauchy condition. No positive
lower bound on variation is used. -/
lemma refinementCauchy_of_uniform {a b : ℝ} {α : ℝ → ℝ}
    {F : ℕ → ℝ → K} {f : ℝ → K}
    (hα : HasBoundedVariation α a b)
    (hF : ∀ n, RefinementCauchy a b (F n) α)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc a b,
      ‖F n x - f x‖ < ε) : RefinementCauchy a b f α := by
  intro ε hε
  let V := (totalVariation α a b).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hd : 0 < 4 * (V + 1) := by positivity
  let δ := ε / (4 * (V + 1))
  have hδ : 0 < δ := div_pos hε hd
  have heq : δ * (4 * (V + 1)) = ε := div_mul_cancel₀ ε (ne_of_gt hd)
  have hsmall : δ * V < ε / 4 := by nlinarith
  obtain ⟨n, hn⟩ := hu δ hδ
  obtain ⟨P₀, hP₀⟩ := hF n (ε / 2) (half_pos hε)
  refine ⟨P₀, fun P hP t Q hQ v => ?_⟩
  have bound (R : Partition a b) (w : Tagging R) :
      ‖taggedSum R w f α - taggedSum R w (F n) α‖ ≤ δ * V := by
    rw [← stieltjes_sum_sub R w f (F n) α]
    exact taggedSum_norm_le R w _ α hδ.le (fun x hx => by
      rw [norm_sub_rev]; exact (hn n le_rfl x hx).le) hα
  have ht : ‖taggedSum P t f α - taggedSum Q v f α‖ ≤
      ‖taggedSum P t f α - taggedSum P t (F n) α‖ +
      ‖taggedSum P t (F n) α - taggedSum Q v (F n) α‖ +
      ‖taggedSum Q v f α - taggedSum Q v (F n) α‖ := by
    have h₁ := dist_triangle (taggedSum P t f α) (taggedSum P t (F n) α)
      (taggedSum Q v (F n) α)
    have h₂ := dist_triangle (taggedSum P t f α) (taggedSum Q v (F n) α)
      (taggedSum Q v f α)
    simp only [dist_eq_norm] at h₁ h₂
    rw [norm_sub_rev (taggedSum Q v (F n) α)] at h₂
    linarith
  have hp := bound P t
  have hq := bound Q v
  have hm := hP₀ P hP t Q hQ v
  linarith

lemma supNorm_error_tendsto {a b : ℝ} (hab : a ≤ b) {F : ℕ → ℝ → K} {f : ℝ → K}
    (hF : ∀ n, BoundedOn a b (F n)) (hf : BoundedOn a b f)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc a b,
      ‖F n x - f x‖ < ε) :
    Tendsto (fun n => supNorm a b (fun x => f x - F n x)) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hu (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hb := supNorm_nonneg hab (bounded_difference hf (hF n))
  have he : supNorm a b (fun x => f x - F n x) ≤ ε / 2 :=
    supNorm_le hab (fun x hx => by rw [norm_sub_rev]; exact (hN n hn x hx).le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hb]
  linarith

open private scalar_complete from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsAlgebra

theorem uniform_stability : Specs.SingleVariableAnalysis.Ch15.RsUniform.uniformStability := by
  intro K _ a b hab α F f J hα hF hu
  have hFn (n : ℕ) := (integral_iff_of_le a b hab (F n) α (J n)).mp (hF n)
  have hf := uniform_limit_bounded (fun n => (hFn n).1) hu
  have hc := refinementCauchy_of_uniform hα
    (fun n => refinementCauchy_of_limit (hFn n).2.2) hu
  obtain ⟨I, hI⟩ := exists_refinementLimit_of_cauchy scalar_complete hc
  have hi : HasIntegral a b f α I :=
    (integral_iff_of_le a b hab f α I).mpr ⟨hf, (hFn 0).2.1, hI⟩
  have hb (n : ℕ) : ‖I - J n‖ ≤ supNorm a b (fun x => f x - F n x) *
      (totalVariation α a b).toReal := by
    have hdiff : HasIntegral a b (fun x => f x - F n x) α (I - J n) := by
      simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using
        integrand_linearity a b f (F n) α I (J n) 1 (-1) hi (hF n)
    exact integral_norm_bound a b hab _ α _ hα hdiff
  have ht : Tendsto (fun n => supNorm a b (fun x => f x - F n x) *
      (totalVariation α a b).toReal) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (supNorm_error_tendsto hab (fun n => (hFn n).1) hf hu).mul_const
        (totalVariation α a b).toReal
  refine ⟨hf, I, hi, hb, ht, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) ht
  simpa only [dist_eq_norm, norm_sub_rev] using hb n

theorem uniform_stability_zero_variation :
    Specs.SingleVariableAnalysis.Ch15.RsUniform.zeroVariation := by
  intro K _ a b hab α F f J hα hzero hF hu
  change totalVariation α a b = 0 at hzero
  obtain ⟨hf, I, hi, _, _, _⟩ := uniform_stability a b hab α F f J hα hF hu
  have zero_value (g : ℝ → K) (L : K) (hg : HasIntegral a b g α L) : L = 0 := by
    have h := integral_norm_bound a b hab g α L hα hg
    change ‖L‖ ≤ supNorm a b g * (totalVariation α a b).toReal at h
    rw [hzero, ENNReal.toReal_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg L))
  have hI := zero_value f I hi
  exact ⟨hf, hI ▸ hi, fun n => zero_value (F n) (J n) (hF n)⟩

end SingleVariableAnalysis.Stieltjes
