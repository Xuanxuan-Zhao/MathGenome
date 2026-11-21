import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.VariationRules
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.Variation

/-! Variation rules for the manuscript's strict-partition total variation. -/
namespace SingleVariableAnalysis.BV
open Riemann
open scoped BigOperators ENNReal
universe u v

/-- Splitting a closed interval counts the value at the common endpoint on
both sides. The equality holds in the extended nonnegative reals. -/
theorem totalVariation_additive :
    Specs.SingleVariableAnalysis.Ch15.VariationRules.additive := by
  intro E _ f a c b hac hcb
  rw [totalVariation_eq_eVariationOn f (hac.trans hcb),
    totalVariation_eq_eVariationOn f hac, totalVariation_eq_eVariationOn f hcb]
  simpa only [Set.univ_inter] using
    (eVariationOn.Icc_add_Icc f (s := Set.univ) hac hcb (Set.mem_univ c)).symm

theorem partitionSum_add_le {E : Type u} [NormedAddCommGroup E]
    {a b : ℝ} (P : Partition a b) (f g : ℝ → E) :
    partitionSum P (fun x => f x + g x) ≤ partitionSum P f + partitionSum P g := by
  unfold partitionSum Specs.SingleVariableAnalysis.Ch15.Variation.partitionSumValue
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [add_sub_add_comm]
  exact (ENNReal.ofReal_le_ofReal (norm_add_le _ _)).trans
    ENNReal.ofReal_add_le

theorem totalVariation_add_le :
    Specs.SingleVariableAnalysis.Ch15.VariationRules.subadditive := by
  intro E _ f g a b _hab
  apply iSup_le
  intro P
  exact (partitionSum_add_le P f g).trans
    (add_le_add (le_iSup (fun Q : Partition a b => partitionSum Q f) P)
      (le_iSup (fun Q : Partition a b => partitionSum Q g) P))

/-- Homogeneity is an identity on each finite partition, even for c = 0. -/
theorem partitionSum_smul {𝕜 : Type v} [NormedField 𝕜]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {a b : ℝ} (P : Partition a b) (c : 𝕜) (f : ℝ → E) :
    partitionSum P (fun x => c • f x) = ENNReal.ofReal ‖c‖ * partitionSum P f := by
  unfold partitionSum Specs.SingleVariableAnalysis.Ch15.Variation.partitionSumValue
  simp_rw [← smul_sub, norm_smul, ENNReal.ofReal_mul (norm_nonneg c)]
  exact (Finset.mul_sum ..).symm

theorem totalVariation_smul {𝕜 : Type v} [NormedField 𝕜]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (c : 𝕜) (f : ℝ → E) {a b : ℝ} (_hab : a ≤ b) :
    totalVariation (fun x => c • f x) a b =
      ENNReal.ofReal ‖c‖ * totalVariation f a b := by
  change (⨆ P : Partition a b, partitionSum P (fun x => c • f x)) =
    ENNReal.ofReal ‖c‖ * ⨆ P : Partition a b, partitionSum P f
  simp_rw [partitionSum_smul, ENNReal.mul_iSup]

/-- Zero scaling is direct and needs no finiteness assumption on f. -/
theorem totalVariation_zero_smul {𝕜 : Type v} [NormedField 𝕜]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    totalVariation (fun x => (0 : 𝕜) • f x) a b = 0 := by
  simpa only [norm_zero, ENNReal.ofReal_zero, zero_mul] using
    totalVariation_smul (0 : 𝕜) f hab

theorem totalVariation_smul_finite {𝕜 : Type v} [NormedField 𝕜]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (c : 𝕜) (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) (hf : HasBoundedVariation f a b) :
    HasBoundedVariation (fun x => c • f x) a b ∧
      (totalVariation (fun x => c • f x) a b).toReal =
        ‖c‖ * (totalVariation f a b).toReal := by
  constructor
  · change totalVariation (fun x => c • f x) a b < ⊤
    rw [totalVariation_smul c f hab]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf
  · rw [totalVariation_smul c f hab, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (norm_nonneg c)]

theorem norm_sub_le_totalVariation {E : Type u} [NormedAddCommGroup E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) (hf : HasBoundedVariation f a b)
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    ‖f x - f y‖ ≤ (totalVariation f a b).toReal := by
  change ‖f x - f y‖ ≤
    (Specs.SingleVariableAnalysis.Ch15.Variation.totalVariationValue f a b).toReal
  rw [totalVariation_eq_eVariationOn f hab, ← dist_eq_norm]
  exact ((boundedVariation_iff f hab).mp hf).dist_le hx hy

theorem norm_le_start_add_totalVariation :
    Specs.SingleVariableAnalysis.Ch15.VariationRules.boundedness := by
  intro E _ f a b hab hf x hx
  calc
    ‖f x‖ ≤ ‖f a‖ + ‖f x - f a‖ := by
      simpa only [norm_sub_rev, add_comm] using norm_le_insert' (f x) (f a)
    _ ≤ ‖f a‖ + (totalVariation f a b).toReal :=
      add_le_add le_rfl (norm_sub_le_totalVariation f hab hf hx ⟨le_rfl, hab⟩)

end SingleVariableAnalysis.BV
