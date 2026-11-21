import MathGenome.Internal.Specs.D07.Ch01.AutomorphismGroups
import MathGenome.Internal.Specs.D07.Ch12.ExtensionDefinition
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
Independent specification of K07.14.automorphism_group, paper.tex:4086–4097.
The chosen Algebra structure records the specified embedding of K in L.
No algebraicity, normality, separability or finite-degree assumption is needed.
The full field automorphism group is RingAut L, not the automorphism group
of the multiplicative group of nonzero elements. The subgroup carrier and
identification below explicitly retain the underlying field maps.
-/

universe u v

namespace Specs.D07.Ch14.AutomorphismGroup

def AutType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], Type v

def autValue : AutType.{u, v} := fun K L _ _ _ => L ≃ₐ[K] L

def ForgetType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    (L ≃ₐ[K] L) →* RingAut L

def forgetValue : ForgetType.{u, v} := fun _ _ _ _ _ =>
  { toFun := AlgEquiv.toRingEquiv
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

def BaseFixingSubgroupType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Subgroup (RingAut L)

def baseFixingSubgroupValue : BaseFixingSubgroupType.{u, v} :=
  fun K L _ _ _ => (forgetValue K L).range

def GroupLaws : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Ch01.GroupDefinition.groupAxiomsValue (L ≃ₐ[K] L) (· * ·) 1 Inv.inv

/-- Product, identity and inverse are exactly the specified function operations. -/
def Operations : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    (∀ (σ τ : L ≃ₐ[K] L) (x : L), (σ * τ) x = σ (τ x)) ∧
    (1 : L ≃ₐ[K] L) = AlgEquiv.refl ∧
    (∀ σ : L ≃ₐ[K] L, σ⁻¹ = σ.symm)

def FixesBase : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (k : K), σ (algebraMap K L k) = algebraMap K L k

/-- Precisely the base-fixing field automorphisms can be bundled as K-automorphisms. -/
def AutomorphismIff : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : RingAut L),
    (∃ σ : L ≃ₐ[K] L, σ.toRingEquiv = f) ↔
      ∀ k : K, f (algebraMap K L k) = algebraMap K L k

def ForgetInjective : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Function.Injective (forgetValue K L)

def SubgroupCarrier : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    (baseFixingSubgroupValue K L : Set (RingAut L)) =
      {f | ∀ k : K, f (algebraMap K L k) = algebraMap K L k}

/-- The subgroup assertion identifies the same maps and respects composition. -/
def SubgroupIdentification : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    ∃ e : (L ≃ₐ[K] L) ≃* baseFixingSubgroupValue K L,
      ∀ σ : L ≃ₐ[K] L, (e σ : RingAut L) = σ.toRingEquiv

end Specs.D07.Ch14.AutomorphismGroup
