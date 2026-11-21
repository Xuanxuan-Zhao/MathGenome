import MathGenome.Internal.Specs.D07.Ch12.SplittingDefinition
import MathGenome.Internal.D07.Ch12.AdjoinDefinition

/-! Splitting fields of nonzero polynomials: splitting and field generation
are separate requirements. Constants generate the base, and an overfield in
which the polynomial splits can still be strictly larger. -/

universe u v

namespace D07.Ch12.SplittingDefinition

open Polynomial Specs.D07.Ch12.SplittingDefinition

/-- The source's predicate, with its nonzero-polynomial domain explicit. -/
abbrev IsSplittingField (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] (f : Polynomial K) : Prop :=
  f ≠ 0 ∧ (f.map (algebraMap K L)).Splits ∧
    D07.Ch12.AdjoinDefinition.generatedField K L (f.rootSet L) = ⊤

theorem source_characterization : SourceCharacterization.{u, v} := by
  intro K L _ _ _ f hf
  have hroots : f.rootSet L = {a : L | aeval a f = 0} := by
    ext a
    exact mem_rootSet_of_ne hf
  unfold splittingFieldValue
  rw [hroots, and_iff_right hf, splits_iff_exists_multiset]

theorem library_characterization : LibraryCharacterization.{u, v} := by
  intro K L _ _ _ f hf
  unfold splittingFieldValue
  rw [and_iff_right hf]
  exact isSplittingField_iff_intermediateField.symm

theorem roots_generate : RootsGenerate.{u, v} := by
  intro K L _ _ _ f h E hE
  apply top_unique
  rw [← h.2.2]
  apply (D07.Ch12.AdjoinDefinition.adjoin_least K L (f.rootSet L) E).mpr
  intro a ha
  exact hE a (aeval_eq_zero_of_mem_rootSet ha)

theorem constant_base : ConstantBase.{u} := by
  intro K _ c hc
  apply (library_characterization K K (C c) (C_ne_zero.mpr hc)).mpr
  exact Polynomial.isSplittingField_C c

theorem constant_characterization : ConstantCharacterization.{u, v} := by
  intro K L _ _ _ c hc
  unfold splittingFieldValue
  simp only [C_ne_zero, hc, ne_eq, not_false_eq_true, map_C, Splits.C,
    rootSet_C, IntermediateField.adjoin_empty, true_and]
  constructor
  · intro h x
    apply IntermediateField.mem_bot.mp
    rw [h]
    trivial
  · intro h
    apply le_antisymm bot_le
    intro x _
    exact IntermediateField.mem_bot.mpr (h x)

theorem constant_equivalence : ConstantEquivalence.{u, v} := by
  intro K L _ _ _ c h
  have hc : c ≠ 0 := fun hc => h.1 (by simp [hc])
  have hs := (constant_characterization K L c hc).mp h
  exact ⟨AlgEquiv.ofBijective (Algebra.ofId K L)
    ⟨(algebraMap K L).injective, hs⟩⟩

theorem containing_roots_insufficient : ContainingRootsInsufficient := by
  have hroots : (X : Polynomial ℝ).rootSet ℂ = {0} := by
    ext a
    simp [mem_rootSet_of_ne (X_ne_zero : (X : Polynomial ℝ) ≠ 0)]
  have hadj : IntermediateField.adjoin ℝ ((X : Polynomial ℝ).rootSet ℂ) = ⊥ := by
    rw [hroots]
    exact IntermediateField.adjoin_zero
  have hproper : (⊥ : IntermediateField ℝ ℂ) < ⊤ := by
    apply lt_of_le_of_ne bot_le
    intro h
    have hI : Complex.I ∈ (⊥ : IntermediateField ℝ ℂ) := by
      rw [h]
      trivial
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hI
    have hi := congrArg Complex.im hr
    simp at hi
  refine ⟨by simp, hadj, hproper, ?_⟩
  intro h
  exact (ne_of_lt hproper) (hadj.symm.trans h.2.2)

end D07.Ch12.SplittingDefinition
