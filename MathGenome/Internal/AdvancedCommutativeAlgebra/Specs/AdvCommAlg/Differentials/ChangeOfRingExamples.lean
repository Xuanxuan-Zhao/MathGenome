import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Polynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.Basic

/-! Independent specifications for paper.tex, KD-25 (lines 471–475).
`RatFunc K` is the rational function field K(t), and `RatFunc.X` is t.
The localization statement allows arbitrary models and the zero ring.
The last two statements exhibit the tensor obstruction and its flatness consequence. -/
namespace Specs.AdvCommAlg.Differentials.ChangeOfRingExamples

universe u v
open scoped TensorProduct

/-- Ω_{A_f/A} = 0, for every element, including zero. -/
def awayDifferentials : Prop :=
  ∀ (A : Type u) (T : Type v) [CommRing A] [CommRing T] [Algebra A T]
    (f : A) [IsLocalization.Away f T], Subsingleton (KaehlerDifferential A T)

/-- The single differential dt is a basis over the rational function field. -/
def rationalFunctionBasis : Prop :=
  ∀ (K : Type u) [Field K],
    ∃ b : Module.Basis Unit (RatFunc K) (KaehlerDifferential K (RatFunc K)),
      b () = KaehlerDifferential.D K (RatFunc K) RatFunc.X

/-- Ω_{F_p/Z} = 0 for each prime p, with the canonical structural map. -/
def primeFieldDifferentials : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Subsingleton (KaehlerDifferential ℤ (ZMod p))

/-- Multiplication by p is injective on Z. Its tensor with F_p is zero on a
nonzero module, and hence is not injective. -/
def primeFieldTensorObstruction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    let μ : ℤ →ₗ[ℤ] ℤ := (p : ℤ) • LinearMap.id
    Function.Injective μ ∧
      μ.rTensor (ZMod p) = 0 ∧
      Nontrivial (ℤ ⊗[ℤ] ZMod p) ∧
      ¬ Function.Injective (μ.rTensor (ZMod p))

/-- The canonical map Z → F_p is not flat. -/
def primeFieldNotFlat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ¬ Module.Flat ℤ (ZMod p)

end Specs.AdvCommAlg.Differentials.ChangeOfRingExamples
