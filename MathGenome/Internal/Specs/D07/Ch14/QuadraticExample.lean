import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Independent specification of K07.14.quadratic_example (paper.tex:4248–4254).
The chosen algebra map embeds K in an arbitrary ambient field L; K(u) is
exactly `IntermediateField.adjoin K {u}`, with its inherited field structure.
A unit encodes a ∈ Kˣ, and `¬ IsSquare` encodes nonsquareness.
For a field, `(2 : K) ≠ 0` is the characteristic-not-two condition.
No finiteness, normality or separability of the ambient L/K is assumed.
`Multiplicative (ZMod 2)` is the cyclic group C₂, with addition written
multiplicatively. Automorphism multiplication is function composition.
-/

universe u v

namespace Specs.D07.Ch14.QuadraticExample

/-- Degree, Galois property, cyclic group isomorphism, full intermediate-field
classification, and the nonidentity sign automorphism with its coordinate rule. -/
def QuadraticExtension : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (a : Kˣ), (2 : K) ≠ 0 → ¬ IsSquare (a : K) →
    ∀ (x : L), x ^ 2 = algebraMap K L (a : K) →
    let E := IntermediateField.adjoin K ({x} : Set L)
    let r : E := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
    FiniteDimensional K E ∧ Module.finrank K E = 2 ∧ IsGalois K E ∧
      Nonempty ((E ≃ₐ[K] E) ≃* Multiplicative (ZMod 2)) ∧
      (∀ M : IntermediateField K E, M = ⊥ ∨ M = ⊤) ∧
      ∃ σ : E ≃ₐ[K] E, σ ≠ 1 ∧ σ r = -r ∧ σ ^ 2 = 1 ∧
        (∀ b c : K, σ (algebraMap K E b + algebraMap K E c * r) =
          algebraMap K E b - algebraMap K E c * r) ∧
        (∀ τ : E ≃ₐ[K] E, τ = 1 ∨ τ = σ)

end Specs.D07.Ch14.QuadraticExample
