import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.UniversalEnveloping
import Mathlib.Algebra.Field.Defs

/-! Independent field specialization of LA A04 (source lines 305–331).
The objects are the shared tensor quotient and its canonical Lie map.
No dimension, characteristic, freeness, or injectivity hypothesis is imposed. -/
namespace Specs.LieAlgebrasAndRepresentations.Enveloping
open _root_.Shared.Lie
attribute [local instance 100] LieRing.ofAssociativeRing
universe u v w w'

def algebraExpectedType := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g], Type (max u v)
def algebraExpectedValue (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] : Type (max u v) := U k g

def inclusionExpectedType := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g], g →ₗ⁅k⁆ U k g
def inclusionExpectedValue (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] := inclusion k g

def projectionExpectedType := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g], TensorAlgebra k g →ₐ[k] U k g
def projectionExpectedValue (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] := tensorQuotient k g

def universalEquivExpectedType := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (A : Type w) [Ring A] [Algebra k A],
  (g →ₗ⁅k⁆ A) ≃ (U k g →ₐ[k] A)
def universalEquivExpectedValue (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (A : Type w) [Ring A] [Algebra k A] :=
  (UniversalEnvelopingAlgebra.lift k : (g →ₗ⁅k⁆ A) ≃ (U k g →ₐ[k] A))

def representationEquivExpectedType := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (M : Type w) [AddCommGroup M] [Module k M],
  Representation k g M ≃ ModuleAction k g M
def representationEquivExpectedValue (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (M : Type w) [AddCommGroup M] [Module k M] := representationEquiv k g M

def quotientExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g],
  Function.Surjective (tensorQuotient k g) ∧
  ∀ x y : g, inclusion k g x * inclusion k g y - inclusion k g y * inclusion k g x =
    inclusion k g ⁅x, y⁆

def universalExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (A : Type w) [Ring A] [Algebra k A]
  (f : g →ₗ⁅k⁆ A), ∃! F : U k g →ₐ[k] A, ∀ x, F (inclusion k g x) = f x

def universalLawsExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (A : Type w) [Ring A] [Algebra k A],
  (∀ (f : g →ₗ⁅k⁆ A) (x : g),
    universalEquivExpectedValue k g A f (inclusion k g x) = f x) ∧
  (∀ F : U k g →ₐ[k] A, (universalEquivExpectedValue k g A).symm F =
    (F : U k g →ₗ⁅k⁆ A).comp (inclusion k g))

def moduleStructuresExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (M : Type w) [AddCommGroup M] [Module k M],
  ∃ e : Representation k g M ≃ CompatibleModule k g M,
    ∀ (ρ : Representation k g M) (a : U k g) (v : M),
      letI := (e ρ).val
      a • v = representationEquiv k g M ρ a v

def underlyingTowerExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (M : Type w) [AddCommGroup M] [Module (U k g) M],
  letI := underlyingModule k g M
  IsScalarTower k (U k g) M

def moduleRestrictionExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
  [IsScalarTower k (U k g) M],
  ∀ a v, representationEquiv k g M
    (((Algebra.lsmul k k M : U k g →ₐ[k] Module.End k M) :
      U k g →ₗ⁅k⁆ Module.End k M).comp (inclusion k g)) a v = a • v

def lieExtensionExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (M : Type w) [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
  ∀ x v, representationEquiv k g M (LieModule.toEnd k g M)
    (inclusion k g x) v = ⁅x, v⁆

def lieRoundtripExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (M : Type w) [AddCommGroup M] [Module k M] (ρ : Representation k g M),
  letI := representationLieRingModule k g M ρ
  letI := representationLieModule k g M ρ
  LieModule.toEnd k g M = ρ

def moduleRoundtripExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (M : Type w) [AddCommGroup M] [Module k M] [Module (U k g) M]
  [IsScalarTower k (U k g) M],
  actionModule k g M (Algebra.lsmul k k M) = (inferInstance : Module (U k g) M)

def morphismExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (M : Type w) [AddCommGroup M] [Module k M]
  (N : Type w') [AddCommGroup N] [Module k N]
  (ρ : Representation k g M) (σ : Representation k g N) (f : M →ₗ[k] N),
  Intertwines (representationEquiv k g M ρ) (representationEquiv k g N σ) f ↔
    LieIntertwines ρ σ f

def morphismEquivExpected : Prop := ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (M : Type w) [AddCommGroup M] [Module k M]
  (N : Type w') [AddCommGroup N] [Module k N]
  (ρ : Representation k g M) (σ : Representation k g N),
  ∃ e : {f : M →ₗ[k] N // LieIntertwines ρ σ f} ≃
    {f : M →ₗ[k] N // Intertwines (representationEquiv k g M ρ)
      (representationEquiv k g N σ) f}, ∀ f, (e f).val = f.val

end Specs.LieAlgebrasAndRepresentations.Enveloping
