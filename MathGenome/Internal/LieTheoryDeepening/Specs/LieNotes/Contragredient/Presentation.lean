import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.CartanData
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! The universal contragredient Lie algebra before taking the Cartan-disjoint quotient. -/

namespace Specs.LieNotes.Contragredient.Presentation

open CartanData
open scoped Classical

noncomputable section

-- The packed type specifications retain all of the indicated universes.
set_option linter.checkUnivs false

universe u v w

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H]

/-- One copy of a basis of the entire Cartan space and two copies of the simple indices. -/
abbrev Generators (I : Type u) (H : Type v) [AddCommGroup H] [Module ℂ H] :=
  Module.Basis.ofVectorSpaceIndex ℂ H ⊕ (I ⊕ I)

abbrev Free (I : Type u) (H : Type v) [AddCommGroup H] [Module ℂ H] :=
  FreeLieAlgebra ℂ (Generators I H)

def freeCartan : H →ₗ[ℂ] Free I H :=
  (Module.Basis.ofVectorSpace ℂ H).constr ℂ (fun b => FreeLieAlgebra.of ℂ (.inl b))

def freeE (i : I) : Free I H := FreeLieAlgebra.of ℂ (.inr (.inl i))

def freeF (i : I) : Free I H := FreeLieAlgebra.of ℂ (.inr (.inr i))

variable [Finite I]

/-- The four defining relators, using arbitrary elements of the Cartan space. -/
inductive Relator (R : Realization A H) : Free I H → Prop
  | cartan_cartan (h k : H) : Relator R ⁅freeCartan (I := I) h, freeCartan (I := I) k⁆
  | cartan_e (h : H) (i : I) :
      Relator R (⁅freeCartan (I := I) h, freeE (H := H) i⁆ - R.α i h • freeE i)
  | cartan_f (h : H) (i : I) :
      Relator R (⁅freeCartan (I := I) h, freeF (H := H) i⁆ + R.α i h • freeF i)
  | e_f (i j : I) :
      Relator R (⁅freeE (H := H) i, freeF (H := H) j⁆ - if i = j then freeCartan (R.h i) else 0)

def relationIdeal (R : Realization A H) : LieIdeal ℂ (Free I H) :=
  LieSubmodule.lieSpan ℂ (Free I H) {x | Relator R x}

abbrev Algebra (R : Realization A H) := Free I H ⧸ relationIdeal R

def quotientMap (R : Realization A H) : Free I H →ₗ⁅ℂ⁆ Algebra R :=
  { (relationIdeal R).toSubmodule.mkQ with
    map_lie' := by intros; rfl }

def cartan (R : Realization A H) : H →ₗ[ℂ] Algebra R :=
  (quotientMap R).toLinearMap.comp freeCartan

def e (R : Realization A H) (i : I) : Algebra R := quotientMap R (freeE i)

def f (R : Realization A H) (i : I) : Algebra R := quotientMap R (freeF i)

def positive (R : Realization A H) : LieSubalgebra ℂ (Algebra R) :=
  LieSubalgebra.lieSpan ℂ (Algebra R) (Set.range (e R))

def negative (R : Realization A H) : LieSubalgebra ℂ (Algebra R) :=
  LieSubalgebra.lieSpan ℂ (Algebra R) (Set.range (f R))

/-- A linear Cartan assignment and simple generator assignments respect the presentation. -/
structure Relations {L : Type w} [LieRing L] [LieAlgebra ℂ L]
    (R : Realization A H) (C : H →ₗ[ℂ] L) (E F : I → L) : Prop where
  cartan_cartan : ∀ h k, ⁅C h, C k⁆ = 0
  cartan_e : ∀ h i, ⁅C h, E i⁆ = R.α i h • E i
  cartan_f : ∀ h i, ⁅C h, F i⁆ = -(R.α i h • F i)
  e_f : ∀ i j, ⁅E i, F j⁆ = if i = j then C (R.h i) else 0

def Extends {L : Type w} [LieRing L] [LieAlgebra ℂ L]
    (R : Realization A H) (C : H →ₗ[ℂ] L) (E F : I → L)
    (φ : Algebra R →ₗ⁅ℂ⁆ L) : Prop :=
  (∀ h, φ (cartan R h) = C h) ∧ (∀ i, φ (e R i) = E i) ∧ (∀ i, φ (f R i) = F i)

def IsInterchange (R : Realization A H) (σ : Algebra R ≃ₗ⁅ℂ⁆ Algebra R) : Prop :=
  Function.Involutive σ ∧
    (∀ h, σ (cartan R h) = -cartan R h) ∧
    (∀ i, σ (e R i) = f R i) ∧
    (∀ i, σ (f R i) = e R i)

-- Type and value bindings for the presented objects.
-- The full signatures below preserve the implicit scalar structure and index finiteness.
def PresentedAlgebraType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    Realization A H → Type (max u v)

def CartanType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), H →ₗ[ℂ] Algebra R

def SimpleGeneratorType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), I → Algebra R

def SideType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), LieSubalgebra ℂ (Algebra R)

def RelationsType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    {L : Type w} [LieRing L] [LieAlgebra ℂ L],
    Realization A H → (H →ₗ[ℂ] L) → (I → L) → (I → L) → Prop

abbrev RelationsValue {L : Type w} [LieRing L] [LieAlgebra ℂ L]
    (R : Realization A H) (C : H →ₗ[ℂ] L) (E F : I → L) := Relations R C E F

def DefiningRelations : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), Relations R (cartan R) (e R) (f R)

def Generated : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
    LieSubalgebra.lieSpan ℂ (Algebra R) (Set.range (cartan R) ∪ Set.range (e R) ∪ Set.range (f R)) = ⊤

def UniversalProperty : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    {L : Type w} [LieRing L] [LieAlgebra ℂ L]
    (R : Realization A H) (C : H →ₗ[ℂ] L) (E F : I → L), Relations R C E F → ∃! φ, Extends R C E F φ

def HasInterchange : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), ∃ σ, IsInterchange R σ

end

end Specs.LieNotes.Contragredient.Presentation
