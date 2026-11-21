import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.ExponentCoordinates
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.ProfiniteIntegers.ResidueModel
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.FieldTheory.KrullTopology

/-! FT-E06, advanced-field-theory.tex:1189–1222. The target is the literal
positive-divisibility residue model with its product subspace topology.
The coordinate isomorphisms are characterized on every integer residue by the
same arithmetic Frobenius, including negative exponents and modulus one.
The action equation λₙ(Θ(σ)ₙ)(x) = σ(x), for every x in kₙ, is the equation
λₙ(Θ(σ)ₙ) = σ|ₖₙ; since λₙ is an equivalence, this is exactly the source's
inverse-coordinate formula. This formulation uses no assumed normality proof. -/
universe u v
noncomputable section
namespace Specs.AdvancedFieldTheory

def absoluteGaloisGroup_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
  ∃ coords : ∀ n : ℕ+, Multiplicative (ZMod (n : ℕ)) ≃*
      (rootField k Ω n ≃ₐ[k] rootField k Ω n),
    (∀ (n : ℕ+) (a : ℤ),
      coords n (Multiplicative.ofAdd (a : ZMod (n : ℕ))) = layerFrobenius k Ω n ^ a) ∧
    ∃! e : (Ω ≃ₐ[k] Ω) ≃ₜ* Multiplicative
        AdvancedFieldTheory.ProfiniteIntegers.ResidueSystem.ResidueFamily,
      (∀ (σ : Ω ≃ₐ[k] Ω) (n : ℕ+) (x : rootField k Ω n),
        (coords n (Multiplicative.ofAdd
          (AdvancedFieldTheory.ProfiniteIntegers.ResidueSystem.coordinate n (e σ).toAdd)) x : Ω) =
          σ (x : Ω)) ∧
      e (globalFrobenius_value k Ω) = Multiplicative.ofAdd
        (AdvancedFieldTheory.ProfiniteIntegers.ResidueSystem.integerResidues 1)

end Specs.AdvancedFieldTheory
