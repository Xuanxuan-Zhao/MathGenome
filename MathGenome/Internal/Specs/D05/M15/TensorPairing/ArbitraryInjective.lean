import MathGenome.Internal.Specs.D05.M15.TensorUniversal
import MathGenome.Internal.Specs.D05.M07.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
Independent statements for the arbitrary-dimensional supplement to
K05.15.tensor_pairing (paper.tex:2846).

The map is Mathlib's canonical algebraic dual tensor map. Its evaluation formula
fixes the pairing as the product of the two functional values. All vector spaces
are arbitrary, over any field; no finite-dimensional, characteristic, topological,
or nonzero-space hypotheses are imposed. Unrestricted basis choice in the proof
uses the declared classical basis-extension principle.
-/

namespace Specs.D05.M15.TensorPairing.ArbitraryInjective

open scoped TensorProduct

/-- The canonical map has the evaluation rule from the paper. -/
def elementary_evaluation : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (φ : Module.Dual K V) (ψ : Module.Dual K W) (v : V) (w : W),
    TensorProduct.dualDistrib K V W (φ ⊗ₜ[K] ψ) (v ⊗ₜ[K] w) = φ v * ψ w

/-- Vanishing on all elementary inputs forces the dual tensor itself to vanish. -/
def eq_zero_of_evaluations_zero : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (z : Module.Dual K V ⊗[K] Module.Dual K W),
    (∀ v w, TensorProduct.dualDistrib K V W z (v ⊗ₜ[K] w) = 0) → z = 0

/-- Injectivity is valid even when either or both spaces have infinite dimension. -/
def canonical_map_injective : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    Function.Injective (TensorProduct.dualDistrib K V W)

end Specs.D05.M15.TensorPairing.ArbitraryInjective
