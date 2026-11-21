import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InducedCharacter
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.UnitarityPairing
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RegularMultiplicity

/-! Frobenius reciprocity with the source's first-variable-linear pairing.
The last statement expresses multiplicities as counts in actual decompositions,
using complete lists of irreducibles and the original representations.
-/
noncomputable section
open scoped Classical
universe u v w
namespace P103.Ch09.FrobeniusCharactersSpecs
open Ch08 Ch08.RegularMultiplicitySpecs

def classFunctionReciprocityType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (ψ : InducedCharacterSpecs.classFunctions H)
    (θ : InducedCharacterSpecs.classFunctions G),
    UnitaritySpecs.functionPairingValue (InducedCharacterSpecs.inductionValue H ψ) θ =
      UnitaritySpecs.functionPairingValue ψ (fun h : H => θ.1 h)

def characterReciprocityType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G W)
    (D : InductionData H ρ) (E : FunctionModelData H ρ D),
    letI := D.module
    FiniteDimensional ℂ (Induced H ρ) ∧
    UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue D.representation)
      (CharacterSpecs.characterValue σ) =
    UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue ρ)
      (CharacterSpecs.characterValue (restrict H σ))

/-- For irreducible source and target these natural numbers are multiplicities;
`decompositionReciprocityType` below also identifies actual summand counts. -/
def multiplicityReciprocityType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G W)
    (D : InductionData H ρ) (E : FunctionModelData H ρ D),
    Irreducible ℂ H V ρ → Irreducible ℂ G W σ →
    letI := D.module
    Module.finrank ℂ (σ.IntertwiningMap D.representation) =
      Module.finrank ℂ (ρ.IntertwiningMap (restrict H σ))

/-- Complete families on H and G represent every irreducible, including V and W.
The induced and restricted modules have actual decompositions. In every such
pair of decompositions, the numbers of copies of W and V agree. -/
def decompositionReciprocityType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G W)
    (D : InductionData H ρ) (E : FunctionModelData H ρ D),
    Irreducible ℂ H V ρ → Irreducible ℂ G W σ →
    letI := D.module
    ∃ (A : Family H) (B : Family G),
      Valid A ∧ Exhaustive.{u,u} A ∧ Valid B ∧ Exhaustive.{u,u} B ∧
    ∃ (i : Fin A.n) (j : Fin B.n),
      Nonempty ((idealRepresentation (A.space i)).Equiv ρ) ∧
      Nonempty ((idealRepresentation (B.space j)).Equiv σ) ∧
      Decomposition B D.representation (multiplicity B D.representation) ∧
      Decomposition A (restrict H σ) (multiplicity A (restrict H σ)) ∧
      ∀ (m : Fin B.n → ℕ) (n : Fin A.n → ℕ),
        Decomposition B D.representation m → Decomposition A (restrict H σ) n →
        m j = n i

end P103.Ch09.FrobeniusCharactersSpecs
