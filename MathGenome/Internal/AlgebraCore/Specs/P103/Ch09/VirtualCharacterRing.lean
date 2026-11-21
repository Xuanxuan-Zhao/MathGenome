import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RegularMultiplicity
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InductionModels
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-! Independent objects and expected statements for the virtual-character part
of paper.tex 2178–2182 and 2198–2204. The ambient scalars are complex, never
rational-valued functions. Finite coordinate spaces avoid quantifying over a
proper class of representation spaces; `ordinary_of_repType` supplies the
bridge from every finite-dimensional representation in any universe. -/
noncomputable section
universe u v w
namespace P103.Ch09.VirtualCharacterSpecs
open P103.Ch08

variable (G : Type u) [Group G]

/-- Ordinary characters, using one small model for every finite-dimensional
complex vector space, including the zero vector space. -/
def Ordinary (f : G → ℂ) : Prop :=
  ∃ n : ℕ, ∃ ρ : Representation ℂ G (Fin n → ℂ),
    CharacterSpecs.characterValue ρ = f

/-- The concrete candidate ring; the implementation must prove that ring
closure adds exactly formal differences of ordinary characters. -/
def virtualSubring : Subring (G → ℂ) := Subring.closure {f | Ordinary G f}

abbrev Ring := virtualSubring G

/-- The direct-sum monoid of ordinary characters. Its closure presentation is
independent of the implementation's proofs of closure of ordinary characters. -/
def ordinaryMonoid : AddSubmonoid (G → ℂ) :=
  AddSubmonoid.closure {f | Ordinary G f}

/-- The canonical map from ordinary to virtual characters. -/
def ordinaryInclusion : ordinaryMonoid G →+ Ring G where
  toFun a := ⟨a.1, (AddSubmonoid.closure_le.mpr
    (show {f | Ordinary G f} ⊆ (virtualSubring G).toAddSubmonoid from
      fun _ h => Subring.subset_closure h)) a.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Complex class functions with pointwise operations. -/
def classFunctions : Subring (G → ℂ) where
  carrier := {f | ∀ g h, f (h * g * h⁻¹) = f g}
  zero_mem' := by exact fun _ _ => rfl
  one_mem' := by exact fun _ _ => rfl
  add_mem' := by intro a b ha hb g h; exact congrArg₂ (· + ·) (ha g h) (hb g h)
  neg_mem' := by intro a ha g h; exact congrArg Neg.neg (ha g h)
  mul_mem' := by intro a b ha hb g h; exact congrArg₂ (· * ·) (ha g h) (hb g h)

namespace Expected

def ringType := ∀ (G : Type u) [Group G], Subring (G → ℂ)

def ringValue : ringType.{u} := fun G _ => virtualSubring G

def ordinary_of_repType : Prop :=
  ∀ {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V),
    Ordinary G (CharacterSpecs.characterValue ρ)

def differenceType : Prop :=
  ∀ {G : Type u} [Group G] (f : G → ℂ),
    f ∈ virtualSubring G ↔
      ∃ a b : G → ℂ, Ordinary G a ∧ Ordinary G b ∧ f = a - b

def classFunctionsType : Prop :=
  ∀ {G : Type u} [Group G], virtualSubring G ≤ classFunctions G

def embeddingType : Prop :=
  ∀ {G : Type u} [Group G],
    ∃ j : Ring G →+* classFunctions G,
      Function.Injective j ∧ ∀ x, (j x).1 = x.1

def actualType :=
  ∀ {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V], Representation ℂ G V → Ring G

/-- A finite-coordinate witness used only to give the canonical ordinary
character inclusion its independent expected value. -/
private theorem ordinaryCoordinates {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) : Ordinary G (CharacterSpecs.characterValue ρ) := by
  let e := (Module.finBasis ℂ V).equivFun
  let σ : Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) :=
    e.conjRingEquiv.toMonoidHom.comp ρ
  refine ⟨Module.finrank ℂ V, σ, ?_⟩
  funext g
  exact LinearMap.trace_conj' (ρ g) e

def actualValue : actualType.{u,v} :=
  fun {_} _ {_} _ _ _ ρ =>
    ⟨CharacterSpecs.characterValue ρ, Subring.subset_closure (ordinaryCoordinates ρ)⟩

def actualAdditionType : Prop :=
  ∀ {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : Ordinary G (CharacterSpecs.characterValue ρ))
    (hσ : Ordinary G (CharacterSpecs.characterValue σ))
    (hs : Ordinary G (CharacterSpecs.characterValue (CharacterSpecs.sumValue ρ σ))),
    (⟨CharacterSpecs.characterValue (CharacterSpecs.sumValue ρ σ),
        Subring.subset_closure hs⟩ : Ring G) =
      ⟨CharacterSpecs.characterValue ρ, Subring.subset_closure hρ⟩ +
        ⟨CharacterSpecs.characterValue σ, Subring.subset_closure hσ⟩

def actualProductType : Prop :=
  ∀ {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : Ordinary G (CharacterSpecs.characterValue ρ))
    (hσ : Ordinary G (CharacterSpecs.characterValue σ))
    (ht : Ordinary G (CharacterSpecs.characterValue (CharacterSpecs.tensorValue ρ σ))),
    (⟨CharacterSpecs.characterValue (CharacterSpecs.tensorValue ρ σ),
        Subring.subset_closure ht⟩ : Ring G) =
      ⟨CharacterSpecs.characterValue ρ, Subring.subset_closure hρ⟩ *
        ⟨CharacterSpecs.characterValue σ, Subring.subset_closure hσ⟩

/-- Classification gives the precise identification by equivariant isomorphism
required to use ordinary characters as the direct-sum monoid. -/
def actualClassificationType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    CharacterSpecs.characterValue ρ = CharacterSpecs.characterValue σ ↔
      Nonempty (ρ.Equiv σ)

/-- The full universal property of group completion. For finite groups,
character classification identifies the input monoid with representations up
to equivariant isomorphism, under direct sum. -/
def completionType : Prop :=
  ∀ {G : Type u} [Group G] {A : Type v} [AddCommGroup A]
    (f : ordinaryMonoid G →+ A),
    ∃! F : Ring G →+ A, F.comp (ordinaryInclusion G) = f

/-- The irreducible-character basis statement includes its actual value as a
complex function and applies to any complete nonrepeating family. -/
def irreducibleBasisType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G]
    (C : RegularMultiplicitySpecs.Family G),
    RegularMultiplicitySpecs.Valid C → RegularMultiplicitySpecs.Exhaustive.{u,u} C →
    ∃ b : Module.Basis (Fin C.n) ℤ (Ring G), ∀ i,
      (b i).1 = CharacterSpecs.characterValue
        (RegularMultiplicitySpecs.idealRepresentation (C.space i))

/-- Unconditional existence, including existence of a complete irreducible
family. No classification or basis certificate is assumed. -/
def freeAbelianType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G],
    ∃ C : RegularMultiplicitySpecs.Family G,
      RegularMultiplicitySpecs.Valid C ∧ RegularMultiplicitySpecs.Exhaustive.{u,u} C ∧
      ∃ b : Module.Basis (Fin C.n) ℤ (Ring G), ∀ i,
        (b i).1 = CharacterSpecs.characterValue
          (RegularMultiplicitySpecs.idealRepresentation (C.space i))

/-- Restriction is an additive map on the same integral lattices; the stronger
ring-homomorphism interface also records the pointwise formula. -/
def restrictionType :=
  ∀ {G : Type u} [Group G] (H : Subgroup G), Ring G →+* Ring H

def restrictionFormulaType (res : restrictionType.{u}) : Prop :=
  ∀ {G : Type u} [Group G] (H : Subgroup G) (f : Ring G) (h : H),
    (res H f).1 h = f.1 h

def restrictionExistsType : Prop :=
  ∀ {G : Type u} [Group G] (H : Subgroup G),
    ∃ res : Ring G →+* Ring H,
      (∀ (x : Ring G) (h : H), (res x).1 h = x.1 h) ∧
      ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (ρ : Representation ℂ G V) (x : Ring G),
        x.1 = CharacterSpecs.characterValue ρ →
          (res x).1 = CharacterSpecs.characterValue (P103.Ch09.restrict H ρ)

/-- Induction uses the very tensor representation from the upstream interface,
not an arbitrary operation merely named induction. -/
def inductionType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (H : Subgroup G),
    ∃ ind : Ring H →+ Ring G,
      ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (ρ : Representation ℂ H V) (D : InductionData H ρ),
        letI := D.module
        ∃ hfin : FiniteDimensional ℂ (Induced H ρ),
          ∀ x : Ring H, x.1 = CharacterSpecs.characterValue ρ →
            (ind x).1 = CharacterSpecs.characterValue D.representation

end Expected
end P103.Ch09.VirtualCharacterSpecs
