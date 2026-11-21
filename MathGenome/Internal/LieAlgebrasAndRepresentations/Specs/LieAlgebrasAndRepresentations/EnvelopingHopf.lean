import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Enveloping
import Mathlib.RingTheory.TensorProduct.Maps

/-! LA A06, Hopf part, source lines 414–459. Tensor and dual representations
are allocated separately. All tensor products are over the coefficient field.
The algebra is exactly the shared tensor quotient, without PBW assumptions. -/
namespace Specs.LieAlgebrasAndRepresentations.EnvelopingHopf
open _root_.Shared.Lie
open scoped TensorProduct
universe u v

/-- The full Hopf identities, including invertibility and anti-multiplicativity
of the linear antipode. The maps in this predicate are conclusions to construct. -/
def HopfLaws (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (Δ : U k g →ₐ[k] U k g ⊗[k] U k g) (ε : U k g →ₐ[k] k)
    (S : U k g ≃ₗ[k] U k g) : Prop :=
  (∀ x : g, Δ (inclusion k g x) =
    inclusion k g x ⊗ₜ[k] (1 : U k g) + (1 : U k g) ⊗ₜ[k] inclusion k g x) ∧
  (∀ x : g, ε (inclusion k g x) = 0) ∧
  (∀ x : g, S (inclusion k g x) = -inclusion k g x) ∧
  S 1 = 1 ∧
  (∀ a b : U k g, S (a*b) = S b * S a) ∧
  (∀ a : U k g,
    TensorProduct.assoc k (U k g) (U k g) (U k g)
      (TensorProduct.map Δ.toLinearMap (LinearMap.id) (Δ a)) =
    TensorProduct.map (LinearMap.id) Δ.toLinearMap (Δ a)) ∧
  (∀ a : U k g, TensorProduct.lid k (U k g)
    (TensorProduct.map ε.toLinearMap (LinearMap.id) (Δ a)) = a) ∧
  (∀ a : U k g, TensorProduct.rid k (U k g)
    (TensorProduct.map (LinearMap.id) ε.toLinearMap (Δ a)) = a) ∧
  (∀ a : U k g, LinearMap.mul' k (U k g)
    (TensorProduct.map S.toLinearMap (LinearMap.id) (Δ a)) =
      algebraMap k (U k g) (ε a)) ∧
  (∀ a : U k g, LinearMap.mul' k (U k g)
    (TensorProduct.map (LinearMap.id) S.toLinearMap (Δ a)) =
      algebraMap k (U k g) (ε a))

def hopfExpected : Prop := ∀ (k : Type u) (g : Type v)
  [Field k] [LieRing g] [LieAlgebra k g],
  ∃ (Δ : U k g →ₐ[k] U k g ⊗[k] U k g) (ε : U k g →ₐ[k] k)
    (S : U k g ≃ₗ[k] U k g), HopfLaws k g Δ ε S
end Specs.LieAlgebrasAndRepresentations.EnvelopingHopf
