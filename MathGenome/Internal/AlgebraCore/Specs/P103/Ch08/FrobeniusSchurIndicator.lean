import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.SquareCharacters
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! Independent statements for the indicator and invariant-form assertions of
paper.tex 1741–1754 and 1765–1782. Real realization is a separate obligation.
All forms are complex bilinear; the dual is the actual contragredient. -/
noncomputable section
universe u v
namespace P103.Ch08.FrobeniusSchurSpecs

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- Simultaneous invariance in the two arguments. -/
def Invariant (ρ : Representation ℂ G V) (B : LinearMap.BilinForm ℂ V) : Prop :=
  ∀ (g : G) (x y : V), B (ρ g x) (ρ g y) = B x y

/-- The full space of invariant complex bilinear forms. -/
def invariantForms (ρ : Representation ℂ G V) : Submodule ℂ (LinearMap.BilinForm ℂ V) where
  carrier := {B | Invariant ρ B}
  zero_mem' := by intro g x y; rfl
  add_mem' := by intro B C hB hC g x y; exact congrArg₂ (· + ·) (hB g x y) (hC g x y)
  smul_mem' := by intro c B hB g x y; exact congrArg (c * ·) (hB g x y)

/-- Invariant symmetric forms, including zero. -/
def symmetricForms (ρ : Representation ℂ G V) : Submodule ℂ (LinearMap.BilinForm ℂ V) where
  carrier := {B | Invariant ρ B ∧ B.IsSymm}
  zero_mem' := ⟨(invariantForms ρ).zero_mem, LinearMap.BilinForm.isSymm_zero⟩
  add_mem' := fun hB hC => ⟨(invariantForms ρ).add_mem hB.1 hC.1, hB.2.add hC.2⟩
  smul_mem' := fun c _ hB => ⟨(invariantForms ρ).smul_mem c hB.1, hB.2.smul c⟩

/-- Alternating means zero on the diagonal, over the original complex field. -/
def alternatingForms (ρ : Representation ℂ G V) : Submodule ℂ (LinearMap.BilinForm ℂ V) where
  carrier := {B | Invariant ρ B ∧ B.IsAlt}
  zero_mem' := ⟨(invariantForms ρ).zero_mem, LinearMap.BilinForm.isAlt_zero⟩
  add_mem' := fun hB hC => ⟨(invariantForms ρ).add_mem hB.1 hC.1, hB.2.add hC.2⟩
  smul_mem' := fun c _ hB => ⟨(invariantForms ρ).smul_mem c hB.1, hB.2.smul c⟩

def SelfDual (ρ : Representation ℂ G V) : Prop := Nonempty (ρ.Equiv ρ.dual)

def HasSymmetricForm (ρ : Representation ℂ G V) : Prop :=
  ∃ B : LinearMap.BilinForm ℂ V, B ≠ 0 ∧ Invariant ρ B ∧ B.IsSymm

def HasAlternatingForm (ρ : Representation ℂ G V) : Prop :=
  ∃ B : LinearMap.BilinForm ℂ V, B ≠ 0 ∧ Invariant ρ B ∧ B.IsAlt

/-- Definition for every finite-dimensional representation, not only irreducibles. -/
def indicatorValue [Fintype G] (ρ : Representation ℂ G V) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, CharacterSpecs.characterValue ρ (g ^ 2)

def indicatorType :=
  ∀ {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), ℂ

def indicatorExpected : indicatorType.{u,v} := fun ρ => indicatorValue ρ

/-- The full numerical trichotomy, with all three converses. Nonzeroness is
part of the shared definition of irreducibility, not an assumed form. -/
def classificationType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), Irreducible ℂ G V ρ →
    (indicatorValue ρ = 0 ∨ indicatorValue ρ = 1 ∨ indicatorValue ρ = -1) ∧
    (indicatorValue ρ = 0 ↔ ¬ SelfDual ρ) ∧
    (indicatorValue ρ = 1 ↔ HasSymmetricForm ρ) ∧
    (indicatorValue ρ = -1 ↔ HasAlternatingForm ρ)

/-- Every nonzero invariant form is nondegenerate on both sides; no symmetry
hypothesis is needed. This includes the forms in both nonzero indicator cases. -/
def nondegeneracyType : Prop :=
  ∀ {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), Irreducible ℂ G V ρ →
    ∀ B : LinearMap.BilinForm ℂ V, Invariant ρ B → B ≠ 0 → B.Nondegenerate

/-- An actual equivariant duality exists exactly when a nonzero invariant
bilinear form does. This is a useful interface for the real-form obligations. -/
def selfDualityType : Prop :=
  ∀ {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), Irreducible ℂ G V ρ →
      (SelfDual ρ ↔ ∃ B : LinearMap.BilinForm ℂ V, B ≠ 0 ∧ Invariant ρ B)

/-- Character averaging and the usual degree-two quotient constructions give
this formula for every finite-dimensional complex representation. -/
def dimensionFormulaType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V),
    indicatorValue ρ = (Module.finrank ℂ (symmetricForms ρ) : ℂ) -
      (Module.finrank ℂ (alternatingForms ρ) : ℂ)

end P103.Ch08.FrobeniusSchurSpecs
