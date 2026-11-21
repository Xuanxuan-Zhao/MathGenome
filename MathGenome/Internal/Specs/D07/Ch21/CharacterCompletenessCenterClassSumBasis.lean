import MathGenome.Internal.Specs.D07.Ch21.GroupAlgebra
import MathGenome.Internal.Specs.D07.Ch05.ConjugationAction
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
The elementary center calculation in K07.21.character_completeness,
paper.tex:6404–6411. The algebra and its center are the canonical complex
group algebra and algebra center. No irreducible representations are used.
-/
namespace Specs.D07.Ch21.CharacterCompletenessCenterClassSumBasis

universe u
noncomputable section

/-- The unnormalized sum of the group basis elements in one conjugacy class. -/
def classSumValue (G : Type u) [Group G] [Fintype G]
    (c : ConjClasses G) : MonoidAlgebra ℂ G := by
  classical
  exact ∑ g : G, if ConjClasses.mk g = c then MonoidAlgebra.single g 1 else 0

def CentralIffClassConstant : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (a : MonoidAlgebra ℂ G),
    a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) ↔
      ∀ x y : G, IsConj x y → a.coeff x = a.coeff y

def CentralIffConjugationFixed : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (a : MonoidAlgebra ℂ G),
    a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) ↔
      ∀ h : G, MonoidAlgebra.single h 1 * a * MonoidAlgebra.single h⁻¹ 1 = a

def ClassSumCoefficients : Prop := by
  classical
  exact ∀ (G : Type u) [Group G] [Fintype G] (c : ConjClasses G) (g : G),
    (classSumValue G c).coeff g = if ConjClasses.mk g = c then 1 else 0

def ClassSumBasis : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∃ b : Module.Basis (ConjClasses G) ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)),
      ∀ c, (b c : MonoidAlgebra ℂ G) = classSumValue G c

def CenterDimension : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    Module.Finite ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) ∧
      Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) = Nat.card (ConjClasses G)

end
end Specs.D07.Ch21.CharacterCompletenessCenterClassSumBasis
