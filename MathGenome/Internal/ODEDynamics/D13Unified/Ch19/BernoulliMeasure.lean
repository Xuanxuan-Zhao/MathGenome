import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.BernoulliMeasure
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.ShiftSpaces
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace D13Unified.Ch19.BernoulliMeasure
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
open D13Unified.Ch17.ShiftSpaces
noncomputable section

abbrev fair := Specs.D13Unified.Ch19.BernoulliMeasure.fair
abbrev bernoulliMeasure := Specs.D13Unified.Ch19.BernoulliMeasure.bernoulliMeasure
abbrev bernoulliPlus := Specs.D13Unified.Ch19.BernoulliMeasure.bernoulliPlus
abbrev bernoulliTwoSided := Specs.D13Unified.Ch19.BernoulliMeasure.bernoulliTwoSided
abbrev HasFairCylinderMasses := @Specs.D13Unified.Ch19.BernoulliMeasure.HasFairCylinderMasses

instance fair_probability : IsProbabilityMeasure fair := by
  constructor
  simpa [fair, Specs.D13Unified.Ch19.BernoulliMeasure.fair,
    Measure.smul_apply, Measure.add_apply, ← ENNReal.div_eq_inv_mul] using
    ENNReal.add_halves 1

lemma fair_singleton (b : Binary) : fair {b} = (2 : ℝ≥0∞)⁻¹ := by
  fin_cases b <;>
    norm_num [fair, Specs.D13Unified.Ch19.BernoulliMeasure.fair,
      Measure.smul_apply, Measure.add_apply, Measure.dirac_apply]

theorem probability : Specs.D13Unified.Ch19.BernoulliMeasure.probabilityStatement := by
  intro I
  change IsProbabilityMeasure (Measure.infinitePi (fun _ : I => fair))
  infer_instance

theorem cylinder_mass : Specs.D13Unified.Ch19.BernoulliMeasure.cylinder_massStatement := by
  intro I s F
  change (Measure.infinitePi (fun _ : I => fair))
    ((F : Set I).pi (fun j => {s j})) = _
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [fair_singleton, ENNReal.zpow_neg, zpow_natCast, ENNReal.inv_pow]

theorem borel_compatibility :
    Specs.D13Unified.Ch19.BernoulliMeasure.borel_compatibilityStatement := by
  intro I _
  exact BorelSpace.measurable_eq

/-- Equality of the point masses of each finite marginal determines the full
product measure; no shift invariance enters the argument. -/
theorem uniqueness : Specs.D13Unified.Ch19.BernoulliMeasure.uniquenessStatement := by
  intro I μ _ hm
  change μ = Measure.infinitePi (fun _ : I => fair)
  apply (Measure.isProjectiveLimit_infinitePi (fun _ : I => fair)).unique _ |>.symm
  intro F
  classical
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (show Measurable (F.restrict : (I → Binary) → (F → Binary)) from
      measurable_pi_iff.mpr (fun j => measurable_pi_apply (j : I)))
    (measurableSet_singleton a)]
  let s : I → Binary := fun i => if hi : i ∈ F then a ⟨i, hi⟩ else 0
  have hpre : (F.restrict : (I → Binary) → (F → Binary)) ⁻¹' {a} =
      cylinder s F := by
    ext x
    constructor
    · intro hx i hi
      have heq : F.restrict x = a := hx
      simpa [s, hi] using congrFun heq ⟨i, hi⟩
    · intro hx
      change F.restrict x = a
      funext j
      simpa [s, j.property] using hx j j.property
  rw [hpre, hm s F, Measure.pi_singleton]
  simp [fair_singleton, ENNReal.zpow_neg, zpow_natCast, ENNReal.inv_pow]

theorem exists_uniquePlus :
    Specs.D13Unified.Ch19.BernoulliMeasure.exists_uniquePlusStatement := by
  refine ⟨bernoulliPlus, ⟨probability ℕ, cylinder_mass ℕ⟩, ?_⟩
  intro μ hμ
  exact uniqueness ℕ μ hμ.1 hμ.2

theorem exists_uniqueTwoSided :
    Specs.D13Unified.Ch19.BernoulliMeasure.exists_uniqueTwoSidedStatement := by
  refine ⟨bernoulliTwoSided, ⟨probability ℤ, cylinder_mass ℤ⟩, ?_⟩
  intro μ hμ
  exact uniqueness ℤ μ hμ.1 hμ.2

theorem independent_blocks :
    Specs.D13Unified.Ch19.BernoulliMeasure.independent_blocksStatement := by
  intro I S T hST
  change IndepFun _ _ (Measure.infinitePi (fun _ : I => fair))
  exact (iIndepFun_infinitePi (P := fun _ : I => fair)
    (X := fun _ x => x) (fun _ => measurable_id)).indepFun_finset S T hST
      (fun i => measurable_pi_apply i)

theorem independent_events :
    Specs.D13Unified.Ch19.BernoulliMeasure.independent_eventsStatement := by
  intro I S T hST A B
  exact (independent_blocks I S T hST).measure_inter_preimage_eq_mul A B
    (.of_discrete) (.of_discrete)

end
end D13Unified.Ch19.BernoulliMeasure
