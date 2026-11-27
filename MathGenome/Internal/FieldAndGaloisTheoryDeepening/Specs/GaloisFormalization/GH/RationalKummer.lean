import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KummerCoefficients
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! The rational Kummer class in Example 3.13. -/

namespace Specs.GaloisFormalization.GH.RationalKummer

open KummerCoefficients

universe u v

/-- The unit defined by the rational-function indeterminate. -/
noncomputable def parameterUnit (F : Type u) [Field F] : (RatFunc F)ˣ :=
  Units.mk0 RatFunc.X RatFunc.X_ne_zero

/-- The class of the indeterminate has order exactly `m`. -/
def ParameterClassOrder : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (m : ℕ),
    1 < m → m ∣ Nat.card F - 1 →
      orderOf (powerClass (RatFunc F) m (parameterUnit F)) = m

/-- Roots exist in the chosen separable closure, and adjoining any one gives
a cyclic Galois extension of degree `m`. -/
def ParameterRadicalExtension : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (S : Type v) [Field S]
    [Algebra (RatFunc F) S] [IsSepClosure (RatFunc F) S] (m : ℕ),
    1 < m → m ∣ Nat.card F - 1 →
      (∃ α : Sˣ, α ^ m = Units.map (algebraMap (RatFunc F) S) (parameterUnit F)) ∧
      ∀ (α : Sˣ), α ^ m = Units.map (algebraMap (RatFunc F) S) (parameterUnit F) →
        ∃ L : FiniteGaloisIntermediateField (RatFunc F) S,
          L.toIntermediateField = IntermediateField.adjoin (RatFunc F) ({(α : S)} : Set S) ∧
          IsCyclic Gal(L/RatFunc F) ∧ Module.finrank (RatFunc F) L = m

end Specs.GaloisFormalization.GH.RationalKummer
