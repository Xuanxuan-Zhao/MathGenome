import MathGenome.Internal.Specs.D07.Ch21.UnitaryAveraging
import Mathlib.RepresentationTheory.Character

/-! Independent specification of K07.21.hom_pairing, paper.tex:6275–6316.
The scalar product is linear first. The Hom action and its normalized average
are specified explicitly. No nonzero-space hypothesis is imposed. -/
namespace Specs.D07.Ch21.HomPairing

universe u v w t s
noncomputable section

/-- Functions on the finite group, with the source's order of arguments. -/
def PairingType := ∀ (G : Type u) [Group G] [Fintype G], (G → ℂ) → (G → ℂ) → ℂ

def pairingValue : PairingType.{u} := fun G _ _ f k =>
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f g * starRingEnd ℂ (k g)

def PairingHermitian : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    UnitaryAveraging.IsPositiveHermitian (pairingValue G)

def PairingSquareNorm : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (f : G → ℂ),
    pairingValue G f f =
      (((Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖f g‖ ^ 2 : ℝ) : ℂ)

def PairingDefinite : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (f : G → ℂ),
    0 ≤ (pairingValue G f f).re ∧
      (pairingValue G f f = 0 ↔ ∀ g, f g = 0)

def HomActionType :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W],
    Representation ℂ G V → Representation ℂ G W →
      Representation ℂ G (V →ₗ[ℂ] W)

def homActionValue : HomActionType.{u,v,w} := fun _ _ _ _ _ _ _ _ ρ σ =>
  Representation.linHom ρ σ

def HomAverageType :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W],
    Representation ℂ G V → Representation ℂ G W →
      Module.End ℂ (V →ₗ[ℂ] W)

def homAverageValue : HomAverageType.{u,v,w} := fun G V W _ _ _ _ _ _ ρ σ =>
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, homActionValue G V W ρ σ g

def HomActionLaws : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
  (∀ g T, homActionValue G V W ρ σ g T = (σ g).comp (T.comp (ρ g⁻¹))) ∧
  homActionValue G V W ρ σ 1 = 1 ∧
  ∀ g h, homActionValue G V W ρ σ (g * h) =
    (homActionValue G V W ρ σ g).comp (homActionValue G V W ρ σ h)

def InvariantsIntertwiners : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
  ∀ T : V →ₗ[ℂ] W,
    T ∈ (homActionValue G V W ρ σ).invariants ↔ ρ.IsIntertwiningMap σ T


def AverageProjection : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype G]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
  (∀ T, homAverageValue G V W ρ σ T ∈ (homActionValue G V W ρ σ).invariants) ∧
  (∀ T, ρ.IsIntertwiningMap σ T → homAverageValue G V W ρ σ T = T) ∧
  (homAverageValue G V W ρ σ).comp (homAverageValue G V W ρ σ) =
    homAverageValue G V W ρ σ ∧
  LinearMap.range (homAverageValue G V W ρ σ) = (homActionValue G V W ρ σ).invariants ∧
  IsCompl (LinearMap.range (homAverageValue G V W ρ σ))
    (LinearMap.ker (homAverageValue G V W ρ σ))


def TraceAverage : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype G]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
  LinearMap.trace ℂ (V →ₗ[ℂ] W) (homAverageValue G V W ρ σ) =
    (Module.finrank ℂ (Representation.IntertwiningMap ρ σ) : ℂ)

def TraceHomAction : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype G]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
  ∀ g, LinearMap.trace ℂ (V →ₗ[ℂ] W) (homActionValue G V W ρ σ g) =
    LinearMap.trace ℂ W (σ g) * LinearMap.trace ℂ V (ρ g⁻¹)

def CharacterHomPairing : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype G]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
  pairingValue G (Specs.D07.Ch17.Characters.characterValue ℂ G W σ) (Specs.D07.Ch17.Characters.characterValue ℂ G V ρ) =
    (Module.finrank ℂ (Representation.IntertwiningMap ρ σ) : ℂ)

def PairingNonnegativeInteger : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype G]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
  ∃ n : ℕ, pairingValue G (Specs.D07.Ch17.Characters.characterValue ℂ G W σ)
      (Specs.D07.Ch17.Characters.characterValue ℂ G V ρ) = (n : ℂ) ∧
    0 ≤ (pairingValue G (Specs.D07.Ch17.Characters.characterValue ℂ G W σ)
      (Specs.D07.Ch17.Characters.characterValue ℂ G V ρ)).re

def ZeroSpace : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype G]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
  (Subsingleton V ∨ Subsingleton W) →
    pairingValue G (Specs.D07.Ch17.Characters.characterValue ℂ G W σ)
      (Specs.D07.Ch17.Characters.characterValue ℂ G V ρ) = 0 ∧
    Module.finrank ℂ (Representation.IntertwiningMap ρ σ) = 0

/-- The operator on the full rectangular matrix space; either index can be empty. -/
def matrixSandwich {m : Type t} {n : Type s} [Fintype m] [Fintype n]
    (B : Matrix m m ℂ) (A : Matrix n n ℂ) : Module.End ℂ (Matrix m n ℂ) where
  toFun T := B * T * A
  map_add' T U := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' a T := by simp

def MatrixSandwichTrace : Prop :=
  ∀ (m : Type t) (n : Type s) [Fintype m] [Fintype n]
    (B : Matrix m m ℂ) (A : Matrix n n ℂ),
    LinearMap.trace ℂ (Matrix m n ℂ) (matrixSandwich B A) = Matrix.trace B * Matrix.trace A

end
end Specs.D07.Ch21.HomPairing
