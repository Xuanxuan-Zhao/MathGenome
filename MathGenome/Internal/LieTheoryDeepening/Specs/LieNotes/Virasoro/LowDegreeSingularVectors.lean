import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.VermaModules

/-! Low-degree singular vectors in the Virasoro Verma module (KM14). -/

noncomputable section

namespace LieNotes.Virasoro.SingularSpec

open VermaSpec

local notation "L" => VirasoroSpec.mode

section Models

variable [LieRing V] [LieAlgebra ℂ V]

/-- The vectors `L₋₁v`, `L₋₂v`, and `L₋₁²v`. -/
abbrev first (D : InducingData) (c h : ℂ) := D.applyWord c h [0]
abbrev second (D : InducingData) (c h : ℂ) := D.applyWord c h [1]
abbrev square (D : InducingData) (c h : ℂ) := D.applyWord c h [0, 0]

/-- The degree-`d` vectors annihilated by all strictly positive modes. -/
def singularSpace (D : InducingData) (c h : ℂ) (d : ℤ) : Submodule ℂ (D.Verma c h) where
  carrier := {x | x ∈ D.degree c h d ∧ ∀ j : ℤ, 0 < j → ⁅L j, x⁆ = 0}
  zero_mem' := ⟨(D.degree c h d).zero_mem, fun _ _ => lie_zero _⟩
  add_mem' := by
    rintro x y ⟨hx, px⟩ ⟨hy, py⟩
    exact ⟨(D.degree c h d).add_mem hx hy, fun j hj => by rw [lie_add, px j hj, py j hj, add_zero]⟩
  smul_mem' := by
    rintro a x ⟨hx, px⟩
    exact ⟨(D.degree c h d).smul_mem a hx, fun j hj => by rw [lie_smul, px j hj, smul_zero]⟩

def determinant (c h : ℂ) : ℂ := 18 * h - (4 * h + 2) * (4 * h + c / 2)

def degreeTwoGenerator (D : InducingData) (c h : ℂ) : D.Verma c h :=
  (3 : ℂ) • square D c h - (4 * h + 2) • second D c h

/-- The action entries on the PBW vectors of degrees one and two. -/
structure ActionRows (D : InducingData) (c h : ℂ) : Prop where
  first_one : ⁅L 1, first D c h⁆ = (2 * h) • D.top c h
  second_one : ⁅L 1, second D c h⁆ = (3 : ℂ) • first D c h
  square_one : ⁅L 1, square D c h⁆ = (4 * h + 2) • first D c h
  second_two : ⁅L 2, second D c h⁆ = (4 * h + c / 2) • D.top c h
  square_two : ⁅L 2, square D c h⁆ = (6 * h) • D.top c h

/-- The low-degree conclusions on the same induced modules and grading as KM13. -/
structure Results (D : InducingData) : Prop where
  degree_one_span : ∀ c h, D.degree c h 1 = Submodule.span ℂ {first D c h}
  first_ne_zero : ∀ c h, first D c h ≠ 0
  degree_two_span : ∀ c h, D.degree c h 2 = Submodule.span ℂ {second D c h, square D c h}
  degree_two_independent : ∀ c h (a b : ℂ),
    a • second D c h + b • square D c h = 0 → a = 0 ∧ b = 0
  action_rows : ∀ c h, ActionRows D c h
  higher_modes : ∀ c h (d j : ℤ) (x : D.Verma c h), x ∈ D.degree c h d → d < j → ⁅L j, x⁆ = 0
  degree_one_exists : ∀ c h, (∃ x ∈ singularSpace D c h 1, x ≠ 0) ↔ h = 0
  degree_one_line : ∀ c h, h = 0 → singularSpace D c h 1 = Submodule.span ℂ {first D c h}
  degree_two_exists : ∀ c h, (∃ x ∈ singularSpace D c h 2, x ≠ 0) ↔ determinant c h = 0
  degree_two_line : ∀ c h, determinant c h = 0 →
    singularSpace D c h 2 = Submodule.span ℂ {degreeTwoGenerator D c h}
  generated_degrees : ∀ c h (d : ℤ) (x : D.Verma c h), x ∈ singularSpace D c h d →
    (LieSubmodule.lieSpan ℂ V {x}).toSubmodule ≤ ⨆ n : ℕ, D.degree c h (d + n)
  generated_proper : ∀ c h (d : ℤ) (x : D.Verma c h), 0 < d → x ∈ singularSpace D c h d →
    D.top c h ∉ LieSubmodule.lieSpan ℂ V {x} ∧ LieSubmodule.lieSpan ℂ V {x} ≠ ⊤
  first_positive_example :
    IsLeast {d : ℤ | 0 < d ∧ ∃ x ∈ singularSpace D 1 (1 / 4) d, x ≠ 0} 2
  example_line : singularSpace D 1 (1 / 4) 2 =
    Submodule.span ℂ {square D 1 (1 / 4) - second D 1 (1 / 4)}

end Models

/-- The mode relation with addition and scalar multiplication from the Lie algebra. -/
def ModeBracket [r : LieRing V] [a : LieAlgebra ℂ V] : Prop :=
  letI : AddCommGroup V := r.toAddCommGroup
  letI : Module ℂ V := a.toModule
  ∀ m n : ℤ, ⁅L m, L n⁆ =
    ((m : ℂ) - (n : ℂ)) • L (m + n) +
      VirasoroSpec.centralCoefficient m n • VirasoroSpec.central

/-- The result applies to the induced Verma model for the Virasoro mode relations. -/
def ResultsOnModels : Prop :=
  ∀ [LieRing V] [LieAlgebra ℂ V], ModeBracket →
    ∀ D : InducingData, ModelProperties.{0} D → Results D

/-- The same canonical Verma construction satisfies KM13 and the singular-vector conclusions. -/
def CanonicalResult : Prop :=
  ∃ r : LieRing V, ∃ a : @LieAlgebra ℂ V _ r,
    r.toAddCommGroup = (inferInstance : AddCommGroup V) ∧
    HEq a.toModule (inferInstance : Module ℂ V) ∧
    letI : LieRing V := r
    letI : LieAlgebra ℂ V := a
    (∀ x y : V, ⁅x, y⁆ = VirasoroSpec.bracket x y) ∧
    ∃ D : InducingData, ModelProperties.{0} D ∧ Results D

end LieNotes.Virasoro.SingularSpec
