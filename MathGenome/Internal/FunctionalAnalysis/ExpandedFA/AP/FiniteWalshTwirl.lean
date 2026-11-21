import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.FiniteWalshTwirl
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.WalshBlocks
import Mathlib.Tactic.Ring

noncomputable section
attribute [local instance] Classical.propDecidable
namespace ExpandedFA.AP.FiniteWalshTwirl
open ExpandedFA.AP.Walsh ExpandedFA.AP.WalshTwirl
open ExpandedFA.AP.WalshBlocks
open scoped BigOperators

abbrev diagonalCoefficient := coefficient
abbrev τ_minus := tauMinus
abbrev τ_plus := tauPlus

/-- These are the coordinates of the Walsh basis, by uniform orthonormality. -/
lemma coefficient_character (n : ℕ) (T R : Finset (Fin (2 * n))) :
    coefficient n T (character n R) = if T = R then 1 else 0 :=
  character_orthonormal n T R

@[simp] theorem differenceVector_coe (n : ℕ) :
    (differenceVector n : Functions n) = difference n := by
  classical
  simp [differenceVector, difference, levelSum, lowerVector, upperVector,
    characterVector, Finset.sum_attach]

lemma levelSum_permute (n r : ℕ) (σ : Equiv.Perm (Fin (2 * n))) (a : Cube n) :
    levelSum n r (fun j => a (σ j)) = levelSum n r a := by
  classical
  simp only [levelSum, Finset.sum_apply, character_permute]
  apply Finset.sum_bij (fun T _ => T.map σ.toEmbedding)
  · intro T hT
    simpa [level, Finset.mem_powersetCard] using hT
  · intro T hT R hR h
    exact Finset.map_injective σ.toEmbedding h
  · intro T hT
    refine ⟨T.map σ.symm.toEmbedding, ?_, ?_⟩
    · simpa [level, Finset.mem_powersetCard] using hT
    · simp [Finset.map_map]
  · intro T hT
    rfl

lemma difference_permute (n : ℕ) (σ : Equiv.Perm (Fin (2 * n))) (a : Cube n) :
    difference n (fun j => a (σ j)) = difference n a := by
  simp [difference, levelSum_permute]

/-- Translation kernel of the normalized difference. -/
def kernel (n : ℕ) (a : Cube n) : Functions n :=
  fun x => difference n (fun j => xor (x j) (a j))

lemma kernel_equivariant (n : ℕ) (g : Equiv.Perm (Cube n))
    (hg : g ∈ symmetryGroup n) :
    ∀ a, pullback n g (kernel n a) = kernel n (g a) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨b, rfl⟩ | ⟨σ, rfl⟩
    · intro a
      ext x
      change difference n (fun j => xor (xor (x j) (b j)) (a j)) =
        difference n (fun j => xor (x j) (xor (a j) (b j)))
      congr 1
      funext j
      cases x j <;> cases a j <;> cases b j <;> rfl
    · intro a
      ext x
      change difference n (fun j => xor (x (σ j)) (a j)) =
        difference n (fun j => xor (x j) (a (σ.symm j)))
      simpa using difference_permute n σ (fun j => xor (x j) (a (σ.symm j)))
  | one => intro a; rfl
  | mul g k hg hk ihg ihk =>
    intro a
    rw [pullback_mul, ihk, ihg]
    rfl
  | inv g hg ih =>
    intro a
    have he := congrArg (pullback n g.symm) (ih (g.symm a))
    have hc : pullback n g.symm (pullback n g (kernel n (g.symm a))) =
        kernel n (g.symm a) := by
      ext x
      exact congrArg (kernel n (g.symm a)) (g.symm_apply_apply x)
    rw [hc] at he
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using he.symm

@[simp] lemma kernel_origin (n : ℕ) : kernel n (fun _ => false) = difference n := by
  ext x
  simp [kernel]

lemma pullback_difference (n : ℕ) (g : symmetryGroup n) :
    pullback n g.val (difference n) = kernel n (g.val (fun _ => false)) := by
  simpa only [kernel_origin] using kernel_equivariant n g.val g.property (fun _ => false)

/-- The kernel written in the two Walsh levels of the block. -/
def kernelVector (n : ℕ) (a : Cube n) : block n :=
  (levelSize n : ℝ)⁻¹ •
    ((∑ T : LowerIndex n, character n T.val a • lowerVector n T) -
      ∑ T : UpperIndex n, character n T.val a • upperVector n T)

@[simp] lemma kernelVector_coe (n : ℕ) (a : Cube n) :
    (kernelVector n a : Functions n) = kernel n a := by
  classical
  ext x
  simp [kernelVector, kernel, difference, levelSum, lowerVector, upperVector,
    characterVector, Finset.sum_apply, character_xor, mul_comm]
  left
  exact congrArg₂ (· - ·)
    (Finset.sum_attach _ (fun T => character n T a * character n T x))
    (Finset.sum_attach _ (fun T => character n T a * character n T x))

def translationElement (n : ℕ) (a : Cube n) : symmetryGroup n :=
  ⟨translation n a, Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)⟩

/-- Uniform group averaging sends the origin to the uniform probability on the
cube. The proof counts by a double sum, avoiding any choice of coset representatives. -/
lemma average_origin (n : ℕ) (f : Cube n → ℝ) :
    (Fintype.card (symmetryGroup n) : ℝ)⁻¹ *
      ∑ g : symmetryGroup n, f (g.val (fun _ => false)) =
    (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ a : Cube n, f a := by
  classical
  have hr (a : Cube n) :
      (∑ g : symmetryGroup n, f (g.val a)) =
      ∑ g : symmetryGroup n, f (g.val (fun _ => false)) := by
    simpa [translationElement, translation] using
      Equiv.sum_comp (Equiv.mulRight (translationElement n a))
        (fun g : symmetryGroup n => f (g.val (fun _ => false)))
  have hd : (Fintype.card (Cube n) : ℝ) *
      (∑ g : symmetryGroup n, f (g.val (fun _ => false))) =
      (Fintype.card (symmetryGroup n) : ℝ) * ∑ a : Cube n, f a := by
    calc
      _ = ∑ a : Cube n, ∑ g : symmetryGroup n, f (g.val a) := by
        simp_rw [hr]
        simp
      _ = ∑ g : symmetryGroup n, ∑ a : Cube n, f (g.val a) := Finset.sum_comm
      _ = _ := by
        simp_rw [Equiv.sum_comp]
        simp
  have hG : (Fintype.card (symmetryGroup n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := symmetryGroup n)
  have hH : (Fintype.card (Cube n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Cube n)
  rw [inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff hG hH]
  simpa [mul_comm] using hd

/-- Applying any linear endomorphism to the translated difference and averaging
evaluations extracts exactly the difference of the normalized diagonals. -/
lemma average_kernel (n : ℕ) (hn : 2 ≤ n) (S : block n →ₗ[ℝ] block n) :
    (Fintype.card (Cube n) : ℝ)⁻¹ *
      ∑ a : Cube n, (S (kernelVector n a) : Functions n) a =
      tauMinus n S - tauPlus n S := by
  classical
  have hp (a : Cube n) : (S (kernelVector n a) : Functions n) a =
      (levelSize n : ℝ)⁻¹ *
        ((∑ T : LowerIndex n, character n T.val a * (S (lowerVector n T) : Functions n) a) -
          ∑ T : UpperIndex n, character n T.val a * (S (upperVector n T) : Functions n) a) := by
    simp [kernelVector, map_smul, map_sub, map_sum]
  have hs : (∑ a : Cube n, (S (kernelVector n a) : Functions n) a) =
      (levelSize n : ℝ)⁻¹ *
        ((∑ T : LowerIndex n, ∑ a : Cube n,
          character n T.val a * (S (lowerVector n T) : Functions n) a) -
        ∑ T : UpperIndex n, ∑ a : Cube n,
          character n T.val a * (S (upperVector n T) : Functions n) a) := by
    simp_rw [hp]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1
    exact congrArg₂ (· - ·) Finset.sum_comm Finset.sum_comm
  rw [hs, tauMinus, tauPlus, (adjacent_level_sizes n hn).1,
    (adjacent_level_sizes n hn).2]
  simp only [coefficient, ← Finset.mul_sum]
  ring

/-- Full conjugation average, as stated in the paper. No bound or regularity
hypothesis on the endomorphism is required in this finite dimensional space. -/
theorem finite_twirl : Specs.ExpandedFA.AP.FiniteWalshTwirl.finiteTwirl := by
  classical
  intro n hn S U hU
  have hdiff (g : symmetryGroup n) :
      U g (differenceVector n) = kernelVector n (g.val (fun _ => false)) := by
    apply Subtype.ext
    ext a
    rw [hU, differenceVector_coe, kernelVector_coe]
    exact congrFun (pullback_difference n g) a
  have hinv (g : symmetryGroup n) (f : block n) :
      ((U g).symm f : Functions n) (fun _ => false) =
        (f : Functions n) (g.val (fun _ => false)) := by
    have he := hU g ((U g).symm f) (g.val (fun _ => false))
    simpa only [LinearIsometryEquiv.apply_symm_apply, Equiv.symm_apply_apply] using he.symm
  simp_rw [hinv, hdiff]
  rw [average_origin n (fun a => (S (kernelVector n a) : Functions n) a),
    average_kernel n hn S]

/-- Specialization to the accepted concrete action and the accepted block
representative of the original function `h_n`. -/
theorem finite_twirl_canonical (n : ℕ) (hn : 2 ≤ n)
    (S : block n →ₗ[ℝ] block n) :
    τ_minus n S - τ_plus n S =
      (Fintype.card (symmetryGroup n) : ℝ)⁻¹ *
        ∑ g : symmetryGroup n,
          ((blockAction n g).symm
            (S (blockAction n g (blockDifference n))) : Functions n) (fun _ => false) := by
  have hh : differenceVector n = blockDifference n :=
    Subtype.ext (differenceVector_coe n)
  simpa only [hh] using
    finite_twirl n hn S (blockAction n) (fun g f a => rfl)

end ExpandedFA.AP.FiniteWalshTwirl



