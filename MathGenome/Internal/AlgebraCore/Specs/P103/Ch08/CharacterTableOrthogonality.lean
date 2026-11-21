import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.FourierTransform
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.RepresentationTheory.Character

/-! The class-function model is functions on the conjugacy quotient. Pullback
along `ConjClasses.mk` identifies these with all conjugacy-invariant functions
on the group. Pairings below use that pullback and are linear in the first slot. -/
noncomputable section
universe u v
namespace P103.Ch08.CharacterTableSpecs
open FourierSpecs
open scoped Classical

abbrev ClassFunction (G : Type u) [Group G] := ConjClasses G → ℂ

/-- The ordinary trace character, descended to conjugacy classes. -/
def classCharacter {G : Type u} [Group G] (C : Family.{u,v} G) (i : Fin C.n) :
    ClassFunction G :=
  Quotient.lift (CharacterSpecs.characterValue (C.representation i)) (by
    intro g h hgh
    obtain ⟨s, hs⟩ := isConj_iff.mp hgh
    rw [← hs]
    exact (C.representation i).char_conj g s |>.symm)

/-- The quotient model includes exactly all conjugacy-invariant functions. -/
def pullbackType : Prop :=
  ∀ {G : Type u} [Group G] (f : G → ℂ),
    (∀ g h : G, f (h * g * h⁻¹) = f g) ↔
      ∃! F : ClassFunction G, ∀ g, F (ConjClasses.mk g) = f g

/-- Row orthogonality, without a chosen norm. -/
def rowType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → ∀ i j,
      UnitaritySpecs.functionPairingValue
        (CharacterSpecs.characterValue (C.representation i))
        (CharacterSpecs.characterValue (C.representation j)) = if i = j then 1 else 0

def basisType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C →
    ∃ b : Module.Basis (Fin C.n) ℂ (ClassFunction G), ∀ i, b i = classCharacter C i

def classCountType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C → C.n = Nat.card (ConjClasses G)

def columnType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G),
    Valid C → Complete C → ∀ g h : G,
      ∑ i : Fin C.n, CharacterSpecs.characterValue (C.representation i) g *
        star (CharacterSpecs.characterValue (C.representation i) h) =
      if IsConj g h then (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) else 0

end P103.Ch08.CharacterTableSpecs
