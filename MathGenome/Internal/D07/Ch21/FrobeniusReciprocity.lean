import MathGenome.Internal.Specs.D07.Ch21.FrobeniusReciprocity
import MathGenome.Internal.D07.Ch21.FrobeniusReciprocityHomReciprocity
import MathGenome.Internal.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity
import MathGenome.Internal.D07.Ch21.HomPairing
import MathGenome.Internal.D07.Ch21.InductionCosetModel
import MathGenome.Internal.D07.Ch21.InducedCharacter
import MathGenome.Internal.D07.Ch21.MultiplicityClassification

/-! Assembly of Frobenius reciprocity on the source's tensor quotient, and
its character and multiplicity consequences. The normalized class-function
sum is explicitly identified with the existing induced-character definition.
-/
namespace D07.Ch21.FrobeniusReciprocity

universe u v v' r w w'
noncomputable section
open scoped Classical

open Representation
open Specs.D07.Ch21.FrobeniusReciprocity
open Specs.D07.Ch17.Characters (characterValue)
open Specs.D07.Ch21.HomPairing (pairingValue)
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
open Specs.D07.Ch21.FrobeniusReciprocityHomReciprocity (IsInducedAction)
open Specs.D07.Ch21.MultiplicityClassification (Decomposes)

/-- Evaluation and balanced extension on the paper's actual quotient. -/
theorem hom_reciprocity : HomReciprocity.{u,v,w} :=
  FrobeniusReciprocityHomReciprocity.hom_reciprocity

theorem any_induced_action : AnyInducedAction.{u,v,w} :=
  FrobeniusReciprocityHomReciprocity.any_induced_action

theorem induced_morphism : InducedMorphism.{u,v,v'} :=
  FrobeniusReciprocityHomReciprocity.induced_morphism

theorem naturality : Naturality.{u,v,v',w,w'} :=
  FrobeniusReciprocityHomReciprocity.naturality

/-- The two upstream interfaces have identical zero extensions and sums;
only the presentation of the finite subgroup cardinal differs. -/
lemma induction_sum_eq {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) (f : H → ℂ) :
    Specs.D07.Ch21.InducedCharacter.induceClassFunction H f =
      Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity.induce H f := by
  classical
  funext g
  simp only [Specs.D07.Ch21.InducedCharacter.induceClassFunction,
    Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity.induce,
    Nat.card_eq_fintype_card]
  rfl

/-- Finite-sum reciprocity expressed using the common character interfaces. -/
theorem class_function_reciprocity : ClassFunctionReciprocity.{u} := by
  intro G _ _ H f k hf hk
  rw [induction_sum_eq]
  exact FrobeniusReciprocityClassFunctionReciprocity.reciprocity G H f k hf hk

/-- Scalar linearity of the Hom equivalence gives equality of dimensions. -/
theorem hom_dimension_reciprocity : HomDimensionReciprocity.{u,v,w} := by
  intro G _ _ H V _ _ ρ σ hσ W _ _ τ
  exact (FrobeniusReciprocityHomReciprocity.homEquiv H ρ τ σ hσ).finrank_eq

/-- The induced trace is precisely induction of the input character. -/
lemma induced_character_eq {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ H V)
    (σ : Representation ℂ G (NotesInd H ρ)) (hσ : IsInducedAction σ)
    [FiniteDimensional ℂ (NotesInd H ρ)] :
    characterValue ℂ G (NotesInd H ρ) σ =
      Specs.D07.Ch21.InducedCharacter.induceClassFunction H (characterValue ℂ H V ρ) := by
  funext g
  exact (InducedCharacter.character_formulas G H V ρ σ hσ
    Quotient.out QuotientGroup.out_eq' g).2

/-- Arbitrary-dimensional Hom reciprocity specializes to the character
identity as soon as the two input character spaces are finite dimensional. -/
theorem character_reciprocity : CharacterReciprocity.{u,v,w} := by
  intro G _ _ H V _ _ _ ρ σ hσ W _ _ _ τ
  have hind := (InductionCosetModel.dimension G H V ρ).1
  let := hind
  refine ⟨hind, ?_⟩
  rw [induced_character_eq H ρ σ hσ]
  exact class_function_reciprocity G H _ _
    (fun a g => D07.Ch17.Characters.character_conjugate ℂ H V ρ g a)
    (fun a g => D07.Ch17.Characters.character_conjugate ℂ G W τ g a)

/-- For characters, the two orders of the pairing agree: the Hom formula
makes it a natural number, fixed by complex conjugation. -/
lemma character_pairing_comm {G : Type u} [Group G] [Fintype G]
    {A : Type v} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    {B : Type w} [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]
    (α : Representation ℂ G A) (β : Representation ℂ G B) :
    pairingValue G (characterValue ℂ G A α) (characterValue ℂ G B β) =
      pairingValue G (characterValue ℂ G B β) (characterValue ℂ G A α) := by
  have hh := (HomPairing.pairing_hermitian G).hermitian
    (characterValue ℂ G A α) (characterValue ℂ G B β)
  rw [HomPairing.character_hom_pairing G A B α β, map_natCast] at hh
  exact hh.symm.trans (HomPairing.character_hom_pairing G A B α β).symm

/-- A complete decomposition and the four compatible formulas for each
irreducible multiplicity. No finite-dimensionality of irreducibles is assumed. -/
theorem induced_multiplicities : InducedMultiplicities.{u,v,r,w} := by
  intro G _ _ H V _ _ _ ρ σ hσ I _ W _ _ τ hi hne hc
  have hfd : ∀ i, FiniteDimensional ℂ (W i) :=
    fun i => (RegularDecomposition.irreducible_finite G (W i) (τ i) (hi i)).1
  have hind := (InductionCosetModel.dimension G H V ρ).1
  let := hfd
  let := hind
  obtain ⟨m, hm⟩ := MultiplicityClassification.decomposition_exists τ hc σ
  refine ⟨hfd, hind, m, hm, ?_, ?_⟩
  · intro i
    have hmi := MultiplicityClassification.multiplicity_formula τ hi hne σ m hm i
    have hrec := (character_reciprocity G H V ρ σ hσ (W i) (τ i)).choose_spec
    have hhom : (m i : ℂ) =
        (Module.finrank ℂ (IntertwiningMap σ (τ i)) : ℂ) := by
      rw [hmi, character_pairing_comm σ (τ i)]
      exact HomPairing.character_hom_pairing G (NotesInd H ρ) (W i) σ (τ i)
    have hnat : m i = Module.finrank ℂ (IntertwiningMap σ (τ i)) :=
      Nat.cast_injective hhom
    exact ⟨hmi, hmi.trans hrec, hnat,
      hnat.trans (hom_dimension_reciprocity G H V ρ σ hσ (W i) (τ i))⟩
  · intro n hn
    exact MultiplicityClassification.multiplicities_unique τ hi hne σ n m hn hm

/-- For an arbitrary irreducible target the same formula holds, with its
finite dimension supplied by the finite-group theorem. -/
theorem irreducible_multiplicity : IrreducibleMultiplicity.{u,v,w} := by
  intro G _ _ H V _ _ _ ρ σ hσ W _ _ τ hi
  have hfd := (RegularDecomposition.irreducible_finite G W τ hi).1
  have hind := (InductionCosetModel.dimension G H V ρ).1
  let := hfd
  let := hind
  refine ⟨hfd, hind, Module.finrank ℂ (IntertwiningMap σ τ), ?_, ?_, rfl,
    hom_dimension_reciprocity G H V ρ σ hσ W τ⟩
  · rw [character_pairing_comm σ τ]
    exact (HomPairing.character_hom_pairing G (NotesInd H ρ) W σ τ).symm
  · rw [← (character_reciprocity G H V ρ σ hσ W τ).choose_spec,
      character_pairing_comm σ τ]
    exact (HomPairing.character_hom_pairing G (NotesInd H ρ) W σ τ).symm

end
end D07.Ch21.FrobeniusReciprocity
