import MathGenome.Internal.Specs.D07.Ch17.Characters
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent specification of K07.21.unitary_averaging (paper.tex:6251–6276).
The pairing below uses the source's linear-first convention. There is no
preassigned topology or inner product on the representation space. -/
namespace Specs.D07.Ch21.UnitaryAveraging

universe u v
noncomputable section

/-- A positive definite Hermitian pairing, linear in the first variable. -/
structure IsPositiveHermitian {V : Type v} [AddCommGroup V] [Module ℂ V]
    (h : V → V → ℂ) : Prop where
  add_left : ∀ x y z, h (x + y) z = h x z + h y z
  smul_left : ∀ (a : ℂ) x y, h (a • x) y = a * h x y
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (a : ℂ) x y, h x (a • y) = starRingEnd ℂ a * h x y
  hermitian : ∀ x y, starRingEnd ℂ (h y x) = h x y
  positive : ∀ x, x ≠ 0 → 0 < (h x x).re

/-- Normalized finite-group average, retaining the actual initial pairing. -/
def averageForm {G : Type u} {V : Type v} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (h₀ : V → V → ℂ) (x y : V) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, h₀ (ρ g x) (ρ g y)

def PositiveFormExists : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    ∃ h₀ : V → V → ℂ, IsPositiveHermitian h₀

def AverageProperties : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (h₀ : V → V → ℂ),
    IsPositiveHermitian h₀ →
    IsPositiveHermitian (averageForm ρ h₀) ∧
      ∀ k x y, averageForm ρ h₀ (ρ k x) (ρ k y) = averageForm ρ h₀ x y

/-- The orthonormal basis belongs to the averaged form itself. Both unitary
matrix membership and the inverse/conjugate-transpose identity are asserted. -/
def AveragedUnitaryBasis : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (h₀ : V → V → ℂ),
    IsPositiveHermitian h₀ →
    ∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V,
      (∀ i j, averageForm ρ h₀ (b i) (b j) = if i = j then 1 else 0) ∧
      (∀ g, LinearMap.toMatrix b b (ρ g) ∈ Matrix.unitaryGroup _ ℂ) ∧
      (∀ g, LinearMap.toMatrix b b (ρ g⁻¹) =
        (LinearMap.toMatrix b b (ρ g)).conjTranspose)

/-- In the zero vector space the zero pairing is the unique such form;
the nonzero-vector positivity test is vacuous. -/
def ZeroSpaceUniqueForm : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [Subsingleton V],
    IsPositiveHermitian (fun (_ _ : V) => (0 : ℂ)) ∧
      ∀ h : V → V → ℂ, IsPositiveHermitian h → h = fun _ _ => 0

def CharacterInverse : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G),
    Specs.D07.Ch17.Characters.characterValue ℂ G V ρ g⁻¹ =
      starRingEnd ℂ (Specs.D07.Ch17.Characters.characterValue ℂ G V ρ g)

def CharacterDual : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G),
    Specs.D07.Ch17.Characters.characterValue ℂ G (Module.Dual ℂ V) ρ.dual g =
      starRingEnd ℂ (Specs.D07.Ch17.Characters.characterValue ℂ G V ρ g)

end
end Specs.D07.Ch21.UnitaryAveraging
