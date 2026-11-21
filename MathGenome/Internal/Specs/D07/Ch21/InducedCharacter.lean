import MathGenome.Internal.Specs.D07.Ch17.Characters
import MathGenome.Internal.Specs.D07.Ch21.InductionCosetModelCosetCoordinateEquivalence

/-! The induced-character formula of paper.tex:6543–6576. Sums are written
using extension by zero from H, so the membership conditions are retained.
The action on the source quotient is characterized on its spanning generators.
The input space can be zero; only character-bearing spaces have finite dimension. -/
namespace Specs.D07.Ch21.InducedCharacter
universe u v
noncomputable section
open scoped BigOperators Classical
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
open Specs.D07.Ch21.InductionCosetModelCosetCoordinateEquivalence

variable {G : Type u} [Group G] (H : Subgroup G)

/-- A complex function constant on conjugacy classes in its own group. -/
def IsClassFunction (ψ : G → ℂ) : Prop :=
  ∀ a b, ψ (b * a * b⁻¹) = ψ a

/-- Extension by zero retains precisely the terms whose argument belongs to H. -/
def extendByZero (ψ : H → ℂ) (y : G) : ℂ :=
  if h : y ∈ H then ψ ⟨y, h⟩ else 0

/-- The second expression in the source, also for arbitrary class functions. -/
def induceClassFunction [Fintype G] (ψ : H → ℂ) (g : G) : ℂ :=
  (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendByZero H ψ (x⁻¹ * g * x)

/-- The first expression for any actual left-coset transversal. -/
def cosetSum [Finite G] (r : G ⧸ H → G) (ψ : H → ℂ) (g : G) : ℂ := by
  letI := Fintype.ofFinite (G ⧸ H)
  exact ∑ q : G ⧸ H, extendByZero H ψ ((r q)⁻¹ * g * r q)

/-- Character formulas for every action on the source quotient with the
constructed generator law; this characterizes the induced action uniquely. -/
def CharacterFormulas : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G (NotesInd H ρ)),
    (∀ k x v, σ k (notesMk H ρ x v) = notesMk H ρ (k * x) v) →
    ∀ (r : G ⧸ H → G), IsTransversal H r → ∀ g,
      LinearMap.trace ℂ (NotesInd H ρ) (σ g) =
        cosetSum H r (Specs.D07.Ch17.Characters.characterValue ℂ H V ρ) g ∧
      LinearMap.trace ℂ (NotesInd H ρ) (σ g) =
        induceClassFunction H (Specs.D07.Ch17.Characters.characterValue ℂ H V ρ) g

/-- The same equality of the two sums for all class functions, rather than
only characters. -/
def ClassFunctionCosetFormula : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (ψ : H → ℂ), IsClassFunction ψ →
    ∀ (r : G ⧸ H → G), IsTransversal H r → ∀ g,
      cosetSum H r ψ g = induceClassFunction H ψ g

def ClassFunctionInduction : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (ψ : H → ℂ), IsClassFunction ψ → IsClassFunction (induceClassFunction H ψ)

/-- No conjugate of g belongs to H. -/
def Vanishing : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G (NotesInd H ρ)),
    (∀ k x v, σ k (notesMk H ρ x v) = notesMk H ρ (k * x) v) →
    ∀ g, (∀ x : G, x⁻¹ * g * x ∉ H) →
      LinearMap.trace ℂ (NotesInd H ρ) (σ g) = 0

def ValueAtOne : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G (NotesInd H ρ)),
    (∀ k x v, σ k (notesMk H ρ x v) = notesMk H ρ (k * x) v) →
      LinearMap.trace ℂ (NotesInd H ρ) (σ 1) =
        (H.index : ℂ) * Specs.D07.Ch17.Characters.characterValue ℂ H V ρ 1


/-- Applicability to the quotient constructed in the preceding entry, with
finite dimension proved rather than imposed on the induced space. -/
def InducedActionExists : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V),
    FiniteDimensional ℂ (NotesInd H ρ) ∧
    ∃ σ : Representation ℂ G (NotesInd H ρ),
      ∀ k x v, σ k (notesMk H ρ x v) = notesMk H ρ (k * x) v

/-- The zero representation is included: its entire induced character is zero. -/
def ZeroSpace : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Subsingleton V] (ρ : Representation ℂ H V)
    (σ : Representation ℂ G (NotesInd H ρ)),
    (∀ k x v, σ k (notesMk H ρ x v) = notesMk H ρ (k * x) v) →
    ∀ g, LinearMap.trace ℂ (NotesInd H ρ) (σ g) = 0

/-- A function on H is the input, rather than an arbitrary function on G. -/
def InductionType : Type (u + 1) :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G), (H → ℂ) → G → ℂ

def inductionValue : InductionType.{u} :=
  fun _ _ _ H ψ g => induceClassFunction H ψ g

end
end Specs.D07.Ch21.InducedCharacter
