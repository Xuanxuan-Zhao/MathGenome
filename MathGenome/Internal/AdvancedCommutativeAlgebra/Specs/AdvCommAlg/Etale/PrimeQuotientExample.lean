import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! ET-16, paper.tex:1973–1977. A prime integer is represented by its
positive natural prime p. All algebra and module structures use the
canonical integer map ℤ → ZMod p; ZMod p is the prime field 𝔽_p.
-/
namespace Specs.AdvCommAlg.Etale.PrimeQuotient

open scoped TensorProduct

/-- The integer endomorphism z ↦ pz, before tensoring. -/
def multiplication (p : ℕ) : ℤ →ₗ[ℤ] ℤ := (p : ℤ) • LinearMap.id

def properties : Prop := ∀ (p : ℕ) [Fact p.Prime],
  Algebra.FinitePresentation ℤ (ZMod p) ∧
  unramifiedValue ℤ (ZMod p) ∧
  ¬ Module.Flat ℤ (ZMod p) ∧ ¬ etaleValue ℤ (ZMod p)

def multiplicationInjective : Prop := ∀ (p : ℕ) [Fact p.Prime],
  Function.Injective (multiplication p)

/-- Tensoring on the left with 𝔽_p kills the multiplication map. -/
def tensorZero : Prop := ∀ (p : ℕ) [Fact p.Prime],
  (multiplication p).lTensor (ZMod p) = 0

/-- Its source and target are a nonzero 𝔽_p-module, canonically isomorphic to 𝔽_p. -/
def tensorNonzero : Prop := ∀ (p : ℕ) [Fact p.Prime],
  Nontrivial (ZMod p ⊗[ℤ] ℤ) ∧
  Nonempty ((ZMod p ⊗[ℤ] ℤ) ≃ₗ[ZMod p] ZMod p)

end Specs.AdvCommAlg.Etale.PrimeQuotient
