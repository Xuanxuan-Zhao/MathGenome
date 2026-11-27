import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers

/-! Pointwise inflation and descent of cochains with discrete coefficients. -/

namespace Specs.GaloisFormalization.GH.FiniteCochainDescent

open Specs.GaloisFormalization.GH.KrullLayers

universe u v w z

set_option linter.checkUnivs false in
def inflate_type :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    {X : Type w} {q : ℕ} [MulAction Gal(L/k) X] (E : FiniteGaloisIntermediateField k L),
    ((Fin q → LayerGroup E) → MulAction.fixedPoints (layerKernel E) X) →
    (Fin q → Gal(L/k)) → X

noncomputable def inflate : inflate_type :=
  fun E f g => (f (fun j => restrict E (g j)) : _)

def continuous_inflate_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    {X : Type w} {q : ℕ} [MulAction Gal(L/k) X] [TopologicalSpace X]
    (E : FiniteGaloisIntermediateField k L)
    (f : (Fin q → LayerGroup E) → MulAction.fixedPoints (layerKernel E) X),
    Continuous (inflate E f)

def inflate_injective_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    {X : Type w} {q : ℕ} [IsGalois k L] [MulAction Gal(L/k) X]
    (E : FiniteGaloisIntermediateField k L),
    Function.Injective (inflate (X := X) (q := q) E)

def finiteCochainFactorization_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    {X : Type w} {q : ℕ} [IsGalois k L] [TopologicalSpace X] [DiscreteTopology X]
    [MulAction Gal(L/k) X] [ContinuousSMul Gal(L/k) X] (f : (Fin q → Gal(L/k)) → X),
    Continuous f → ∀ E₀ : FiniteGaloisIntermediateField k L,
      ∃ E : FiniteGaloisIntermediateField k L, E₀ ≤ E ∧
        ∃ fE : (Fin q → LayerGroup E) → MulAction.fixedPoints (layerKernel E) X,
          ∀ g, (fE (fun j => restrict E (g j)) : X) = f g

def commonCochainFactorization_type : Prop :=
  ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    {X : Type w} [IsGalois k L] [TopologicalSpace X] [DiscreteTopology X]
    [MulAction Gal(L/k) X] [ContinuousSMul Gal(L/k) X] (ι : Type z) [Finite ι] (q : ι → ℕ)
    (f : ∀ i, (Fin (q i) → Gal(L/k)) → X), (∀ i, Continuous (f i)) →
    ∀ E₀ : FiniteGaloisIntermediateField k L,
      ∃ E : FiniteGaloisIntermediateField k L, E₀ ≤ E ∧
        ∃ fE : ∀ i, (Fin (q i) → LayerGroup E) → MulAction.fixedPoints (layerKernel E) X,
          ∀ i g, (fE i (fun j => restrict E (g j)) : X) = f i g

end Specs.GaloisFormalization.GH.FiniteCochainDescent
