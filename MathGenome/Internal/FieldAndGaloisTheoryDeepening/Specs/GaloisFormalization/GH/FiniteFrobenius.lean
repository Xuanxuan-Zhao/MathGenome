import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteFields.ExponentCoordinates
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.ProfiniteIntegers.ResidueModel

/-! Arithmetic Frobenius and its residue coordinates on a chosen separable closure. -/

namespace Specs.GaloisFormalization.GH.FiniteFrobenius

open _root_.AdvancedFieldTheory (finiteRootField finiteRootField_finite_galois
  frobeniusExponentCoordinates)
open _root_.AdvancedFieldTheory.ProfiniteIntegers (Zhat π ι)
open KrullLayers

universe u v

noncomputable section

variable (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
  [IsSepClosure k S]

/-- Arithmetic Frobenius in the Krull group of the specified closure. -/
def arithmeticFrobenius : AbsoluteGaloisGroup k S :=
  FiniteField.frobeniusAlgEquivOfAlgebraic k S

/-- The degree-`d` root field inside the same closure. -/
def rootLayer (d : ℕ+) : FiniteGaloisIntermediateField k S where
  toIntermediateField := finiteRootField k S d
  finiteDimensional := (finiteRootField_finite_galois k S d d.pos).1
  isGalois := (finiteRootField_finite_galois k S d d.pos).2

/-- The exponent isomorphism based at arithmetic Frobenius on the root field. -/
def exponentEquiv (d : ℕ+) : Multiplicative (ZMod (d : ℕ)) ≃* LayerGroup (rootLayer k S d) :=
  frobeniusExponentCoordinates k S d d.pos

/-- Restrict to the embedded root field and take the Frobenius exponent. -/
def reduction (d : ℕ+) : AbsoluteGaloisGroup k S →ₜ* Multiplicative (ZMod (d : ℕ)) :=
  { toMonoidHom := (exponentEquiv k S d).symm.toMonoidHom.comp
      (restrict (rootLayer k S d)).toMonoidHom
    continuous_toFun := (continuous_of_discreteTopology (f := (exponentEquiv k S d).symm)).comp
      (restrict (rootLayer k S d)).continuous }

section DefinitionTypes

set_option linter.checkUnivs false

def arithmeticFrobenius_type :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S], AbsoluteGaloisGroup k S

def rootLayer_type :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S], ℕ+ → FiniteGaloisIntermediateField k S

def exponentEquiv_type :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S] (d : ℕ+),
    Multiplicative (ZMod (d : ℕ)) ≃* LayerGroup (rootLayer k S d)

def reduction_type :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S] (d : ℕ+), AbsoluteGaloisGroup k S →ₜ* Multiplicative (ZMod (d : ℕ))

end DefinitionTypes

def arithmeticFrobenius_apply_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S] (x : S), arithmeticFrobenius k S x = x ^ Fintype.card k

def arithmeticFrobenius_orderOf_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S], orderOf (arithmeticFrobenius k S) = 0

def rootLayer_spec_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S] (d : ℕ+),
    Module.finrank k (rootLayer k S d) = (d : ℕ) ∧
    ∀ x : S, x ∈ (rootLayer k S d).toIntermediateField ↔
      x ^ (Fintype.card k ^ (d : ℕ)) = x

def restrict_frobenius_apply_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S] (E : FiniteGaloisIntermediateField k S) (x : E),
    restrict E (arithmeticFrobenius k S) x = x ^ Fintype.card k

def restrict_frobenius_orderOf_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S] (E : FiniteGaloisIntermediateField k S),
    orderOf (restrict E (arithmeticFrobenius k S)) = Module.finrank k E

def restrict_frobenius_generates_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S] (E : FiniteGaloisIntermediateField k S),
    Subgroup.zpowers (restrict E (arithmeticFrobenius k S)) = ⊤

def frobenius_cyclic_dense_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S],
    Dense (Subgroup.zpowers (arithmeticFrobenius k S) : Set (AbsoluteGaloisGroup k S))

def exponentEquiv_intCast_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S] (d : ℕ+) (a : ℤ),
    exponentEquiv k S d (Multiplicative.ofAdd (a : ZMod (d : ℕ))) =
      restrict (rootLayer k S d) (arithmeticFrobenius k S) ^ a

def reduction_restrict_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S] (d : ℕ+) (σ : AbsoluteGaloisGroup k S),
    exponentEquiv k S d (reduction k S d σ) = restrict (rootLayer k S d) σ

def reduction_surjective_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S] (d : ℕ+), Function.Surjective (reduction k S d)

def reduction_frobenius_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S] (d : ℕ+),
    reduction k S d (arithmeticFrobenius k S) = Multiplicative.ofAdd (1 : ZMod (d : ℕ))

def absoluteGaloisEquiv_type : Prop :=
  ∀ (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [IsSepClosure k S],
    ∃! e : AbsoluteGaloisGroup k S ≃ₜ* Multiplicative Zhat,
      e (arithmeticFrobenius k S) = Multiplicative.ofAdd (ι 1) ∧
      ∀ (d : ℕ+) (σ : AbsoluteGaloisGroup k S),
        Multiplicative.ofAdd (π d (e σ).toAdd) = reduction k S d σ

end

end Specs.GaloisFormalization.GH.FiniteFrobenius
