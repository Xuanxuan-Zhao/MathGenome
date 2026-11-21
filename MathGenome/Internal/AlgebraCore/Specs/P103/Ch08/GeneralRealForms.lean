import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.IrreducibleRealForms
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RegularMultiplicity

/-! Independent statements for the general assertions in paper.tex 1756–1762
and 1807–1838. Multiplicities are the upstream natural Hom multiplicities,
which count copies in the actual semisimple decomposition. No real-structure
certificate is an input to either realization criterion. -/
noncomputable section
universe u v
namespace P103.Ch08.GeneralRealFormSpecs
open RegularMultiplicitySpecs RealFormSpecs FrobeniusSchurSpecs

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- The two actual irreducible representations are contragredient types. -/
def DualPair (C : Family G) (i j : Fin C.n) : Prop :=
  Nonempty ((idealRepresentation (C.space i)).dual.Equiv
    (idealRepresentation (C.space j)))

/-- Only pairs of distinct (hence non-self-dual) types impose equalities. -/
def BalancedMultiplicity (C : Family G) (ρ : Representation ℂ G V) : Prop :=
  ∀ i j, i ≠ j → DualPair C i j → multiplicity C ρ i = multiplicity C ρ j

/-- Positive types impose no parity restriction. -/
def EvenQuaternionicMultiplicity [Fintype G] (C : Family G)
    (ρ : Representation ℂ G V) : Prop :=
  ∀ i, indicatorValue (idealRepresentation (C.space i)) = -1 →
    Even (multiplicity C ρ i)

/-- Nondegeneracy, rather than nonzeroness, includes the zero representation. -/
def HasPerfectSymmetricForm (ρ : Representation ℂ G V) : Prop :=
  ∃ B : LinearMap.BilinForm ℂ V, Invariant ρ B ∧ B.IsSymm ∧ B.Nondegenerate

/-- Completeness in the universe of the regular module suffices for all
representation universes, by the upstream `exhaustive_from_regular` bridge. -/
def realCharacterCriterionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family G),
    Valid C → Exhaustive.{u,u} C →
    ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V),
      RealCharacter ρ ↔ BalancedMultiplicity C ρ

def realFormCriterionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family G),
    Valid C → Exhaustive.{u,u} C →
    ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V),
      HasRealForm ρ ↔ BalancedMultiplicity C ρ ∧ EvenQuaternionicMultiplicity C ρ

def symmetricFormCriterionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V),
      HasRealForm ρ ↔ HasPerfectSymmetricForm ρ

/-- Construction of a conjugate-linear equivariant involution from the
numerical conditions; fixed-space descent produces the actual real form. -/
def realStructureConstructionType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family G),
    Valid C → Exhaustive.{u,u} C →
    ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V),
      BalancedMultiplicity C ρ → EvenQuaternionicMultiplicity C ρ →
        HasConjugateStructure ρ 1

def realFormSymmetricNecessityType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V),
      HasRealForm ρ → HasPerfectSymmetricForm ρ

def symmetricFormBalancedNecessityType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family G),
    Valid C → Exhaustive.{u,u} C →
    ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V),
      HasPerfectSymmetricForm ρ → BalancedMultiplicity C ρ

/-- The remaining parity obstruction, stated for the original bilinear form
rather than assuming a real form or a normalized real structure. -/
def symmetricFormParityNecessityType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (C : Family G),
    Valid C → Exhaustive.{u,u} C →
    ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V),
      HasPerfectSymmetricForm ρ → EvenQuaternionicMultiplicity C ρ

def realFormRealCharacterType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), HasRealForm ρ → RealCharacter ρ

def zeroRealFormType : Prop :=
  ∀ {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [Subsingleton V]
    (ρ : Representation ℂ G V), HasRealForm ρ

end P103.Ch08.GeneralRealFormSpecs
