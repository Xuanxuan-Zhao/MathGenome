import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.WalshBlocks
import Mathlib.Data.Fintype.Perm

/-! Independent statement of paper.tex, equation `fa2:ap:finite-twirl`.
The action is quantified together with its prescribed pointwise formula;
its existence is the accepted WalshBlocks.isometric_action theorem. -/
noncomputable section
attribute [local instance] Classical.propDecidable

namespace ExpandedFA.AP.WalshTwirl
open ExpandedFA.AP.Walsh
open scoped BigOperators

abbrev LowerIndex (n : ℕ) := {T // T ∈ level n (n - 1)}
abbrev UpperIndex (n : ℕ) := {T // T ∈ level n (n + 1)}

def characterVector (n : ℕ) (T : Finset (Fin (2 * n)))
    (hT : T ∈ level n (n - 1) ∨ T ∈ level n (n + 1)) : block n :=
  ⟨character n T, Submodule.subset_span ⟨T, hT, rfl⟩⟩

def lowerVector (n : ℕ) (T : LowerIndex n) : block n :=
  characterVector n T.val (Or.inl T.property)

def upperVector (n : ℕ) (T : UpperIndex n) : block n :=
  characterVector n T.val (Or.inr T.property)

/-- Walsh coefficient for the uniform probability measure on the full cube. -/
def coefficient (n : ℕ) (T : Finset (Fin (2 * n))) (f : Functions n) : ℝ :=
  (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ a : Cube n, character n T a * f a

/-- Average diagonal coefficient on the lower Walsh level. -/
def tauMinus (n : ℕ) (S : block n →ₗ[ℝ] block n) : ℝ :=
  ((level n (n - 1)).card : ℝ)⁻¹ *
    ∑ T : LowerIndex n, coefficient n T.val (S (lowerVector n T)).val

/-- Average diagonal coefficient on the upper Walsh level. -/
def tauPlus (n : ℕ) (S : block n →ₗ[ℝ] block n) : ℝ :=
  ((level n (n + 1)).card : ℝ)⁻¹ *
    ∑ T : UpperIndex n, coefficient n T.val (S (upperVector n T)).val

/-- The source's normalized difference, as a vector of the block. -/
def differenceVector (n : ℕ) : block n :=
  (levelSize n : ℝ)⁻¹ •
    ((∑ T : LowerIndex n, lowerVector n T) - ∑ T : UpperIndex n, upperVector n T)

end ExpandedFA.AP.WalshTwirl

namespace Specs.ExpandedFA.AP.FiniteWalshTwirl
open ExpandedFA.AP.Walsh ExpandedFA.AP.WalshTwirl
open scoped BigOperators

def coefficientType := ∀ n, Finset (Fin (2 * n)) → Functions n → ℝ
def coefficientValue : coefficientType := coefficient

def averageType := ∀ n, (block n →ₗ[ℝ] block n) → ℝ
def tauMinusValue : averageType := tauMinus
def tauPlusValue : averageType := tauPlus

def differenceVectorRealization : Prop := ∀ n,
  (differenceVector n : Functions n) = difference n

/-- Exact scalar matrix identity for every endomorphism, with the full finite
translation/permutation group and its prescribed isometric action. -/
def finiteTwirl : Prop := ∀ n, 2 ≤ n →
  ∀ (S : block n →ₗ[ℝ] block n)
    (U : symmetryGroup n →* ((block n) ≃ₗᵢ[ℝ] (block n))),
    (∀ g f a, ((U g f : block n) : Functions n) a =
      (f : Functions n) ((g : Equiv.Perm (Cube n)).symm a)) →
    tauMinus n S - tauPlus n S =
      (Fintype.card (symmetryGroup n) : ℝ)⁻¹ *
        ∑ g : symmetryGroup n,
          ((U g).symm (S (U g (differenceVector n))) : Functions n) (fun _ => false)

end Specs.ExpandedFA.AP.FiniteWalshTwirl
