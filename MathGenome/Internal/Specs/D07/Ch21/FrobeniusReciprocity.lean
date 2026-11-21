import MathGenome.Internal.Specs.D07.Ch21.FrobeniusReciprocityHomReciprocity
import MathGenome.Internal.Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity
import MathGenome.Internal.Specs.D07.Ch21.InducedCharacter
import MathGenome.Internal.Specs.D07.Ch21.HomPairing
import MathGenome.Internal.Specs.D07.Ch21.MultiplicityClassification

/-!
Frobenius reciprocity, paper.tex:6574–6627. The induction space is the
ordinary tensor quotient of the paper. The Hom equivalence and its naturality
are specified by the prerequisite interface, including both generator formulas.
The character and multiplicity statements below use the existing induced
class-function sum and the existing linear-first Hermitian pairing.
No dimension assumption is imposed on the Hom statements. Finite dimension of
the induced space and of irreducibles is a conclusion, never a certificate.
-/
namespace Specs.D07.Ch21.FrobeniusReciprocity

universe u v v' r w w'
noncomputable section
open scoped Classical

open Representation
open Specs.D07.Ch17.Characters (characterValue)
open Specs.D07.Ch21.HomPairing (pairingValue)
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
open Specs.D07.Ch21.FrobeniusReciprocityHomReciprocity (IsInducedAction)
open Specs.D07.Ch21.MultiplicityClassification (Decomposes)

/-- The same quotient action works for every W; the equivalence and its inverse
are T ↦ (v ↦ T[1,v]) and A ↦ ([g,v] ↦ gA(v)). -/
def HomReciprocity : Prop :=
  FrobeniusReciprocityHomReciprocity.HomReciprocity.{u,v,w}

/-- Independence from the choice of action satisfying the generator law. -/
def AnyInducedAction : Prop :=
  FrobeniusReciprocityHomReciprocity.AnyInducedAction.{u,v,w}

/-- Induction of maps is characterized by [g,v] ↦ [g,a(v)]. -/
def InducedMorphism : Prop :=
  FrobeniusReciprocityHomReciprocity.InducedMorphism.{u,v,v'}

/-- Naturality in both V (contravariant) and W (covariant). -/
def Naturality : Prop :=
  FrobeniusReciprocityHomReciprocity.Naturality.{u,v,v',w,w'}

/-- Arbitrary class functions, with precisely the previously constructed
induction sum and the character chapter's pairing. -/
def ClassFunctionReciprocity : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (f : H → ℂ) (k : G → ℂ),
    FrobeniusReciprocityClassFunctionReciprocity.IsClassFunction f →
    FrobeniusReciprocityClassFunctionReciprocity.IsClassFunction k →
    pairingValue G (InducedCharacter.induceClassFunction H f) k =
      pairingValue H f (fun h => k h)

/-- A direct consequence of the linear Hom equivalence, including zero and
infinite-dimensional spaces (finrank agrees even in its zero-default cases). -/
def HomDimensionReciprocity : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (σ : Representation ℂ G (NotesInd H ρ)), IsInducedAction σ →
    ∀ (W : Type w) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W),
      Module.finrank ℂ (IntertwiningMap σ τ) =
        Module.finrank ℂ (IntertwiningMap ρ (τ.comp H.subtype))

/-- Specialization to characters of arbitrary finite-dimensional V and W,
including zero. Restriction retains the original vector space. -/
def CharacterReciprocity : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G (NotesInd H ρ)),
    IsInducedAction σ →
    ∀ (W : Type w) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (τ : Representation ℂ G W),
    ∃ hfd : FiniteDimensional ℂ (NotesInd H ρ),
      letI := hfd
      pairingValue G (characterValue ℂ G (NotesInd H ρ) σ)
          (characterValue ℂ G W τ) =
        pairingValue H (characterValue ℂ H V ρ)
          (characterValue ℂ H W (τ.comp H.subtype))

/-- The multiplicity interpretation for every complete, nonrepeating finite
family of irreducibles. A genuine equivariant direct-sum decomposition exists,
its multiplicities are unique, and every coefficient is computed by both
character reciprocity and the natural Hom reciprocity. The spaces W_i are
not assumed finite dimensional; that fact must be proved. -/
def InducedMultiplicities : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G (NotesInd H ρ)),
    IsInducedAction σ →
    ∀ (I : Type r) [Fintype I] (W : I → Type w)
      [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
      (τ : ∀ i, Representation ℂ G (W i)),
    (∀ i, IsIrreducible (τ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((τ i).Equiv (τ j))) →
    RegularDecomposition.IsComplete τ →
    ∃ (hfd : ∀ i, FiniteDimensional ℂ (W i))
      (hind : FiniteDimensional ℂ (NotesInd H ρ)),
      letI := hfd
      letI := hind
      ∃ m : I → ℕ, Decomposes τ σ m ∧
        (∀ i,
          (m i : ℂ) = pairingValue G (characterValue ℂ G (NotesInd H ρ) σ)
            (characterValue ℂ G (W i) (τ i)) ∧
          (m i : ℂ) = pairingValue H (characterValue ℂ H V ρ)
            (characterValue ℂ H (W i) ((τ i).comp H.subtype)) ∧
          m i = Module.finrank ℂ (IntertwiningMap σ (τ i)) ∧
          m i = Module.finrank ℂ (IntertwiningMap ρ ((τ i).comp H.subtype))) ∧
        ∀ n : I → ℕ, Decomposes τ σ n → n = m

/-- The formula applies to any given irreducible G-representation, without
assuming finite dimension or providing a chosen complete family. The family
statement above identifies these numbers with direct-sum multiplicities. -/
def IrreducibleMultiplicity : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G (NotesInd H ρ)),
    IsInducedAction σ →
    ∀ (W : Type w) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W),
    IsIrreducible τ →
    ∃ (hfd : FiniteDimensional ℂ W) (hind : FiniteDimensional ℂ (NotesInd H ρ)),
      letI := hfd
      letI := hind
      ∃ n : ℕ,
        (n : ℂ) = pairingValue G (characterValue ℂ G (NotesInd H ρ) σ)
          (characterValue ℂ G W τ) ∧
        (n : ℂ) = pairingValue H (characterValue ℂ H V ρ)
          (characterValue ℂ H W (τ.comp H.subtype)) ∧
        n = Module.finrank ℂ (IntertwiningMap σ τ) ∧
        n = Module.finrank ℂ (IntertwiningMap ρ (τ.comp H.subtype))

end
end Specs.D07.Ch21.FrobeniusReciprocity
