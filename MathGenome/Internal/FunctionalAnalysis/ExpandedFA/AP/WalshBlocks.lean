import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.WalshBlocks
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

noncomputable section

namespace ExpandedFA.AP.WalshBlocks
open ExpandedFA.AP.Walsh
open scoped BigOperators

abbrev H := Cube
abbrev χ := character
abbrev W := level
abbrev F := levelSum
abbrev t := levelSize
abbrev h := difference
abbrev E := block
abbrev G := symmetryGroup

/-- All functions on the finite discrete cube are continuous; the supremum
norm agrees exactly with the norm on continuous functions used in the source. -/
def continuousModel (n : ℕ) :
    letI : TopologicalSpace (Cube n) := ⊥
    Functions n ≃ₗᵢ[ℝ] C(Cube n, ℝ) := by
  letI : TopologicalSpace (Cube n) := ⊥
  letI : DiscreteTopology (Cube n) := ⟨rfl⟩
  exact {
    toFun := fun f => ⟨f, continuous_of_discreteTopology⟩
    invFun := fun f => f
    left_inv := fun f => rfl
    right_inv := fun f => by ext a; rfl
    map_add' := fun f g => rfl
    map_smul' := fun c f => rfl
    norm_map' := fun f => ContinuousMap.norm_eq_norm_coeFn _ }

theorem continuous_function_model : Specs.ExpandedFA.AP.WalshBlocks.continuousFunctionModel := by
  intro n
  exact ⟨continuousModel n, fun f a => rfl⟩

/-- Each bit contributes its real sign. -/
def bitSign (b : Bool) : ℝ := if b then -1 else 1

lemma character_product (n : ℕ) (S : Finset (Fin (2 * n))) (a : Cube n) :
    character n S a = ∏ j ∈ S, bitSign (a j) := by
  rw [character, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j hj
  cases a j <;> simp [bitSign]

lemma character_product_univ (n : ℕ) (S : Finset (Fin (2 * n))) (a : Cube n) :
    character n S a = ∏ j, if j ∈ S then bitSign (a j) else 1 := by
  rw [Finset.prod_ite_mem_eq, character_product]

lemma character_pair_sum (n : ℕ) (S T : Finset (Fin (2 * n))) :
    (∑ a : Cube n, character n S a * character n T a) =
      if S = T then (Fintype.card (Cube n) : ℝ) else 0 := by
  simp_rw [character_product_univ, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j (b : Bool) =>
    (if j ∈ S then bitSign b else 1) * (if j ∈ T then bitSign b else 1))]
  by_cases hST : S = T
  · subst T
    simp only [ite_true]
    have hbit : ∀ j : Fin (2 * n),
        (∑ b : Bool, (if j ∈ S then bitSign b else 1) *
          (if j ∈ S then bitSign b else 1)) = (2 : ℝ) := by
      intro j
      by_cases hj : j ∈ S <;> norm_num [hj, Fintype.sum_bool, bitSign]
    simp_rw [hbit]
    simp [Cube]
  · simp only [hST, ↓reduceIte]
    obtain ⟨j, hj⟩ : ∃ j, ¬ (j ∈ S ↔ j ∈ T) := by
      by_contra! he
      exact hST (Finset.ext he)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;>
      simp_all [bitSign]

/-- Orthonormality for exactly the uniform probability on the entire cube. -/
theorem character_orthonormal : Specs.ExpandedFA.AP.WalshBlocks.characterOrthonormal := by
  intro n S T
  rw [character_pair_sum]
  split_ifs
  · exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := Cube n))
  · simp

lemma level_card (n r : ℕ) : (level n r).card = (2 * n).choose r := by
  simp [level, Finset.card_powersetCard]

/-- The lower and upper levels have the source's common cardinality. -/
theorem adjacent_level_sizes : Specs.ExpandedFA.AP.WalshBlocks.adjacentLevelSizes := by
  intro n hn
  constructor
  · exact level_card n (n - 1)
  · rw [level_card, levelSize]
    exact Nat.choose_symm_of_eq_add (by omega)

lemma character_xor (n : ℕ) (S : Finset (Fin (2 * n))) (a b : Cube n) :
    character n S (fun j => xor (a j) (b j)) = character n S a * character n S b := by
  simp_rw [character_product]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  cases a j <;> cases b j <;> norm_num [bitSign]

lemma character_permute (n : ℕ) (S : Finset (Fin (2 * n)))
    (σ : Equiv.Perm (Fin (2 * n))) (a : Cube n) :
    character n S (fun j => a (σ j)) = character n (S.map σ.toEmbedding) a := by
  simp [character_product, Finset.prod_map]

lemma character_mem_block (n : ℕ) (S : Finset (Fin (2 * n)))
    (hS : S ∈ level n (n - 1) ∨ S ∈ level n (n + 1)) : character n S ∈ block n :=
  Submodule.subset_span ⟨S, hS, rfl⟩

/-- Both level sums, and hence their normalized difference, lie in the block. -/
theorem difference_mem_block : Specs.ExpandedFA.AP.WalshBlocks.differenceMembership := by
  intro n
  apply (block n).smul_mem
  apply (block n).sub_mem
  · apply (block n).sum_mem
    intro S hS
    exact character_mem_block n S (Or.inl hS)
  · apply (block n).sum_mem
    intro S hS
    exact character_mem_block n S (Or.inr hS)

/-- The same difference viewed as a vector in the invariant block. -/
def blockDifference (n : ℕ) : block n := ⟨difference n, difference_mem_block n⟩

/-- Checking the generators of the span suffices for preservation. -/
lemma pullback_preserves_span (n : ℕ) (g : Equiv.Perm (Cube n))
    (hg : ∀ S, (S ∈ level n (n - 1) ∨ S ∈ level n (n + 1)) →
      pullback n g (character n S) ∈ block n) :
    ∀ f, f ∈ block n → pullback n g f ∈ block n := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨S, hS, rfl⟩ := hf
    exact hg S hS
  | zero => exact (block n).zero_mem
  | add f g hf hg ihf ihg => exact (block n).add_mem ihf ihg
  | smul c f hf ih => exact (block n).smul_mem c ih

lemma translation_preserves (n : ℕ) (b : Cube n) :
    ∀ f, f ∈ block n → pullback n (translation n b) f ∈ block n := by
  apply pullback_preserves_span
  intro S hS
  have he : pullback n (translation n b) (character n S) =
      character n S b • character n S := by
    ext a
    change character n S (fun j => xor (a j) (b j)) =
      character n S b * character n S a
    rw [character_xor, mul_comm]
  rw [he]
  exact (block n).smul_mem _ (character_mem_block n S hS)

lemma permutation_preserves (n : ℕ) (σ : Equiv.Perm (Fin (2 * n))) :
    ∀ f, f ∈ block n → pullback n (coordinatePermutation n σ) f ∈ block n := by
  apply pullback_preserves_span
  intro S hS
  have he : pullback n (coordinatePermutation n σ) (character n S) =
      character n (S.map σ.toEmbedding) := by
    ext a
    exact character_permute n S σ a
  rw [he]
  apply character_mem_block
  simpa [level, Finset.mem_powersetCard] using hS

@[simp] lemma pullback_one (n : ℕ) (f : Functions n) : pullback n 1 f = f := rfl

lemma pullback_mul (n : ℕ) (g k : Equiv.Perm (Cube n)) (f : Functions n) :
    pullback n (g * k) f = pullback n g (pullback n k f) := rfl

@[simp] lemma translation_symm (n : ℕ) (b : Cube n) :
    (translation n b).symm = translation n b := by ext a j; rfl

@[simp] lemma coordinatePermutation_symm (n : ℕ) (σ : Equiv.Perm (Fin (2 * n))) :
    (coordinatePermutation n σ).symm = coordinatePermutation n σ.symm := by ext a j; rfl

/-- Both a group element and its inverse preserve the two-level space. -/
lemma symmetry_preserves (n : ℕ) (g : Equiv.Perm (Cube n)) (hg : g ∈ symmetryGroup n) :
    (∀ f, f ∈ block n → pullback n g f ∈ block n) ∧
    (∀ f, f ∈ block n → pullback n g.symm f ∈ block n) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨b, rfl⟩ | ⟨σ, rfl⟩
    · simpa only [translation_symm] using
        And.intro (translation_preserves n b) (translation_preserves n b)
    · simpa only [coordinatePermutation_symm] using
        And.intro (permutation_preserves n σ) (permutation_preserves n σ.symm)
  | one => exact ⟨fun f hf => hf, fun f hf => hf⟩
  | mul g k hg hk ihg ihk =>
    constructor
    · intro f hf
      exact ihg.1 _ (ihk.1 f hf)
    · intro f hf
      exact ihk.2 _ (ihg.2 f hf)
  | inv g hg ih => exact ⟨ih.2, ih.1⟩

/-- Restriction of the permutation pullback to the invariant, sup-normed span. -/
def blockIsometry (n : ℕ) (g : symmetryGroup n) : (block n) ≃ₗᵢ[ℝ] (block n) where
  toFun f := ⟨pullback n g.val f.val, (symmetry_preserves n g.val g.property).1 _ f.property⟩
  invFun f := ⟨pullback n g.val.symm f.val,
    (symmetry_preserves n g.val g.property).2 _ f.property⟩
  left_inv f := by apply Subtype.ext; ext a; simp [pullback]
  right_inv f := by apply Subtype.ext; ext a; simp [pullback]
  map_add' f k := rfl
  map_smul' c f := rfl
  norm_map' f := g.val.symm.surjective.pi_norm_comp f.val

/-- The group law agrees with composition of the restricted isometries. -/
def blockAction (n : ℕ) : symmetryGroup n →* ((block n) ≃ₗᵢ[ℝ] (block n)) where
  toFun := blockIsometry n
  map_one' := by apply LinearIsometryEquiv.ext; intro f; rfl
  map_mul' g k := by apply LinearIsometryEquiv.ext; intro f; rfl

/-- Finiteness and the exact pointwise action, including all group laws. -/
theorem isometric_action : Specs.ExpandedFA.AP.WalshBlocks.isometricAction := by
  intro n hn
  refine ⟨inferInstance, blockAction n, ?_⟩
  intro g f a
  rfl

end ExpandedFA.AP.WalshBlocks
