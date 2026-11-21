import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Profinite.Integers
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.ExponentCoordinates
import Mathlib.FieldTheory.KrullTopology

/-! The finite-field part of GR02-C05.05, using the arithmetic Frobenius
coordinates of Advanced Field Theory E06. -/

namespace Specs.ALG02GroupTheory.Profinite

universe u v

/-- The absolute Galois group with its Krull topology is isomorphic to the
profinite completion of the additive integers. Arithmetic Frobenius acts
as the image of the integer 1, and the completed integer's residue at each
positive modulus encodes restriction to the corresponding finite root field. -/
def FiniteFieldGaloisCompletion : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
    ∃ e : (Ω ≃ₐ[k] Ω) ≃ₜ* completionValue IntegerGroup,
      e (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) =
        etaValue IntegerGroup (Multiplicative.ofAdd (1 : ℤ)) ∧
      ∃ coords : ∀ n : ℕ+, Multiplicative (ZMod (n : ℕ)) ≃*
          (Specs.AdvancedFieldTheory.rootField k Ω n ≃ₐ[k]
            Specs.AdvancedFieldTheory.rootField k Ω n),
        (∀ (n : ℕ+) (a : ℤ), coords n (Multiplicative.ofAdd (a : ZMod (n : ℕ))) =
          Specs.AdvancedFieldTheory.layerFrobenius k Ω n ^ a) ∧
        ∀ (σ : Ω ≃ₐ[k] Ω) (n : ℕ+) (x : Specs.AdvancedFieldTheory.rootField k Ω n),
          (coords n (integerQuotientEquivValue n
            (projectionValue (integerIndexValue n) (e σ))) x : Ω) = σ (x : Ω)

end Specs.ALG02GroupTheory.Profinite
