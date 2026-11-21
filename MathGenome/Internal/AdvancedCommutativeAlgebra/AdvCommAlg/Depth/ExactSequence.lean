import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtCharacterization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ExactSequence

/-! The depth lemma (DP-07). We transport the Ext long-exact-sequence
inequalities through DP-04, then deduce all strict cases in ℕ∞. -/

universe u
open CategoryTheory
namespace AdvCommAlg.Depth

private lemma middle_eq_left_of_lt {a b c : ℕ∞}
    (h₁ : min a c ≤ b) (h₂ : min b (c + 1) ≤ a) (h : a < c) : b = a := by
  apply le_antisymm
  · by_contra! hab
    exact (not_lt_of_ge h₂) (lt_min hab (h.trans_le le_self_add))
  · simpa only [min_eq_left h.le] using h₁

private lemma middle_eq_right_of_add_one_lt {a b c : ℕ∞}
    (h₁ : min a c ≤ b) (h₃ : min b (a - 1) ≤ c) (h : c + 1 < a) : b = c := by
  apply le_antisymm
  · by_contra! hcb
    exact (not_lt_of_ge h₃) (lt_min hcb (lt_tsub_iff_right.mpr h))
  · have hca : c ≤ a := (le_self_add : c ≤ c + 1).trans h.le
    simpa only [min_eq_right hca] using h₁

private lemma right_eq_sub_one_of_left_lt_middle {a b c : ℕ∞}
    (h₂ : min b (c + 1) ≤ a) (h₃ : min b (a - 1) ≤ c) (h : a < b) :
    1 ≤ a ∧ c = a - 1 := by
  have hca : c + 1 ≤ a := (min_le_iff.mp h₂).resolve_left (not_le.mpr h)
  refine ⟨le_trans le_add_self hca, le_antisymm ?_ ?_⟩
  · exact ENat.le_sub_of_add_le_right (by simp) hca
  · simpa only [min_eq_right ((tsub_le_self : a - 1 ≤ a).trans h.le)] using h₃

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The grade of the middle term is at least the minimum of the outer grades. -/
theorem grade_min_le_middle (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (hS : S.ShortExact) : min (grade I S.X₁) (grade I S.X₃) ≤ grade I S.X₂ := by
  simp only [grade_eq_idealDepth]
  exact ModuleCat.depth_min_fst_trd_le_snd_right _ S hS

/-- The left grade is at least the minimum of the middle grade and right grade plus one. -/
theorem grade_min_add_one_le_left (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (hS : S.ShortExact) : min (grade I S.X₂) (grade I S.X₃ + 1) ≤ grade I S.X₁ := by
  simp only [grade_eq_idealDepth]
  exact ModuleCat.depth_min_snd_trd_add_one_le_fst_right _ S hS

/-- The right grade is at least the minimum of the middle grade and left grade minus one. -/
theorem grade_min_sub_one_le_right (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (hS : S.ShortExact) : min (grade I S.X₂) (grade I S.X₁ - 1) ≤ grade I S.X₃ := by
  simp only [grade_eq_idealDepth]
  exact ModuleCat.depth_min_snd_fst_sub_one_le_trd_right _ S hS

theorem grade_middle_eq_left_of_left_lt_right (I : Ideal R)
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (hS : S.ShortExact) (h : grade I S.X₁ < grade I S.X₃) :
    grade I S.X₂ = grade I S.X₁ :=
  middle_eq_left_of_lt (grade_min_le_middle I S hS) (grade_min_add_one_le_left I S hS) h

theorem grade_middle_eq_right_of_right_add_one_lt_left (I : Ideal R)
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (hS : S.ShortExact) (h : grade I S.X₃ + 1 < grade I S.X₁) :
    grade I S.X₂ = grade I S.X₃ :=
  middle_eq_right_of_add_one_lt (grade_min_le_middle I S hS)
    (grade_min_sub_one_le_right I S hS) h

theorem grade_right_eq_sub_one_of_left_lt_middle (I : Ideal R)
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (hS : S.ShortExact) (h : grade I S.X₁ < grade I S.X₂) :
    1 ≤ grade I S.X₁ ∧ grade I S.X₃ = grade I S.X₁ - 1 :=
  right_eq_sub_one_of_left_lt_middle (grade_min_add_one_le_left I S hS)
    (grade_min_sub_one_le_right I S hS) h

variable [IsLocalRing R]

theorem depth_min_le_middle (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (hS : S.ShortExact) : min (depth R S.X₁) (depth R S.X₃) ≤ depth R S.X₂ :=
  grade_min_le_middle (IsLocalRing.maximalIdeal R) S hS

theorem depth_min_add_one_le_left (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (hS : S.ShortExact) : min (depth R S.X₂) (depth R S.X₃ + 1) ≤ depth R S.X₁ :=
  grade_min_add_one_le_left (IsLocalRing.maximalIdeal R) S hS

theorem depth_min_sub_one_le_right (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (hS : S.ShortExact) : min (depth R S.X₂) (depth R S.X₁ - 1) ≤ depth R S.X₃ :=
  grade_min_sub_one_le_right (IsLocalRing.maximalIdeal R) S hS

theorem depth_middle_eq_left_of_left_lt_right (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (hS : S.ShortExact) (h : depth R S.X₁ < depth R S.X₃) :
    depth R S.X₂ = depth R S.X₁ :=
  grade_middle_eq_left_of_left_lt_right (IsLocalRing.maximalIdeal R) S hS h

theorem depth_middle_eq_right_of_right_add_one_lt_left (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (hS : S.ShortExact) (h : depth R S.X₃ + 1 < depth R S.X₁) :
    depth R S.X₂ = depth R S.X₃ :=
  grade_middle_eq_right_of_right_add_one_lt_left (IsLocalRing.maximalIdeal R) S hS h

theorem depth_right_eq_sub_one_of_left_lt_middle (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (hS : S.ShortExact) (h : depth R S.X₁ < depth R S.X₂) :
    1 ≤ depth R S.X₁ ∧ depth R S.X₃ = depth R S.X₁ - 1 :=
  grade_right_eq_sub_one_of_left_lt_middle (IsLocalRing.maximalIdeal R) S hS h

end AdvCommAlg.Depth
