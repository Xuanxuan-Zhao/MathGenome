import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Monotone
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.VariationRules

/-! Monotone real functions and finite linear combinations of BV functions. -/
namespace SingleVariableAnalysis.BV
open scoped BigOperators ENNReal
universe u v w

/-- The Mathlib monotone variation identity applies on the closed interval,
using the previously proved bridge from strict endpoint partitions. -/
theorem totalVariation_of_monotoneOn :
    Specs.SingleVariableAnalysis.Ch15.Monotone.nondecreasingVariation := by
  intro f a b hab hf
  rw [totalVariation_eq_eVariationOn f hab]
  have h := hf.eVariationOn_eq (a := a) (b := b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  simpa only [Set.inter_self, abs_of_nonneg (sub_nonneg.mpr
    (hf ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab))] using h

/-- Negation changes nonincreasing to nondecreasing and preserves variation. -/
theorem totalVariation_of_antitoneOn :
    Specs.SingleVariableAnalysis.Ch15.Monotone.nonincreasingVariation := by
  intro f a b hab hf
  have hneg : MonotoneOn (fun x => -f x) (Set.Icc a b) := by
    intro x hx y hy hxy
    exact neg_le_neg (hf hx hy hxy)
  have h := totalVariation_of_monotoneOn (fun x => -f x) hab hneg
  have hvar : totalVariation (fun x => -f x) a b = totalVariation f a b := by
    simpa only [neg_one_smul, norm_neg, norm_one, ENNReal.ofReal_one, one_mul] using
      totalVariation_smul (-1 : ℝ) f hab
  change totalVariation (fun x => -f x) a b = _ at h
  rw [hvar] at h
  simpa only [neg_sub_neg, abs_sub_comm] using h

theorem hasBoundedVariation_of_monotone :
    Specs.SingleVariableAnalysis.Ch15.Monotone.monotoneBoundedVariation := by
  intro f a b hab hf
  have heq : totalVariation f a b = ENNReal.ofReal |f b - f a| := by
    rcases hf with hf | hf
    · exact totalVariation_of_monotoneOn f hab hf
    · exact totalVariation_of_antitoneOn f hab hf
  constructor
  · change totalVariation f a b < ⊤
    rw [heq]
    exact ENNReal.ofReal_lt_top
  · change (totalVariation f a b).toReal = _
    rw [heq, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- Closure under two-term addition follows from the extended sum bound. -/
theorem hasBoundedVariation_add {E : Type u} [NormedAddCommGroup E]
    {f g : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : HasBoundedVariation f a b) (hg : HasBoundedVariation g a b) :
    HasBoundedVariation (fun x => f x + g x) a b :=
  (totalVariation_add_le f g hab).trans_lt (ENNReal.add_lt_top.mpr ⟨hf, hg⟩)

/-- Induct over the finite set, using homogeneity for each summand and the
sum inequality at each insertion. Zero coefficients and the empty set require
no exceptions. -/
theorem hasBoundedVariation_linearCombination {𝕜 : Type v} [NormedField 𝕜]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {ι : Type w} (s : Finset ι) (c : ι → 𝕜) (f : ι → ℝ → E) {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ i ∈ s, HasBoundedVariation (f i) a b) :
    HasBoundedVariation (fun x => ∑ i ∈ s, c i • f i x) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : totalVariation (fun _ : ℝ => (0 : E)) a b = 0 := by
        simpa only [zero_smul] using
          totalVariation_zero_smul (𝕜 := 𝕜) (fun _ : ℝ => (0 : E)) hab
      have hzero : HasBoundedVariation (fun _ : ℝ => (0 : E)) a b := by
        change totalVariation (fun _ : ℝ => (0 : E)) a b < ⊤
        rw [hz]
        exact ENNReal.zero_lt_top
      simpa only [Finset.sum_empty] using hzero
  | @insert i s hi ih =>
      have hfi := (totalVariation_smul_finite (c i) (f i) hab
        (hf i (Finset.mem_insert_self i s))).1
      have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using hasBoundedVariation_add hab hfi hs

end SingleVariableAnalysis.BV
