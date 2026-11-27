import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

open CategoryTheory CategoryTheory.Limits ZeroObject
open HomologicalComplex

universe u

namespace DerivedFormalization.Model.Complexes

/-- Unbounded cochain complexes of left modules over a unital ring. -/
abbrev Cochains (A : Type u) [Ring A] := CochainComplex (ModuleCat.{u} A) ℤ

end DerivedFormalization.Model.Complexes

namespace DerivedFormalization.Specs.ComplexGenerators

open Model.Complexes

def sphereType := ∀ (A : Type u) [Ring A], ℤ → Cochains A

/-- The regular left module in degree `n`. -/
noncomputable def sphereValue : sphereType.{u} :=
  fun A _ n ↦ (single (ModuleCat A) (ComplexShape.up ℤ) n).obj (ModuleCat.of A A)

def diskType := ∀ (A : Type u) [Ring A], ℤ → Cochains A

/-- The identity on the regular left module, in cochain degrees `n` and `n + 1`. -/
noncomputable def diskValue : diskType.{u} :=
  fun A _ n ↦ double (𝟙 (ModuleCat.of A A)) (ComplexShape.up_mk n (n + 1) rfl)

def iGeneratorType :=
  ∀ (A : Type u) [Ring A] (n : ℤ), sphereValue A (n + 1) ⟶ diskValue A n

/-- The inclusion of the upper degree of the disk. -/
noncomputable def iGeneratorValue : iGeneratorType.{u} := by
  intro A _ n
  change (single (ModuleCat A) (ComplexShape.up ℤ) (n + 1)).obj (ModuleCat.of A A) ⟶
    double (𝟙 (ModuleCat.of A A)) (ComplexShape.up_mk n (n + 1) rfl)
  refine mkHomFromSingle (doubleXIso₁ _ _ (by omega : n ≠ n + 1)).inv ?_
  intro k _
  rw [double_d_eq_zero₀ _ _ _ _ (by omega : n + 1 ≠ n), comp_zero]

def jGeneratorType := ∀ (A : Type u) [Ring A] (n : ℤ), 0 ⟶ diskValue A n

/-- The unique map from the zero complex to the disk. -/
noncomputable def jGeneratorValue : jGeneratorType.{u} := fun _ _ _ ↦ 0

def generatorClassType := ∀ (A : Type u) [Ring A], MorphismProperty (Cochains A)

noncomputable def iValue : generatorClassType.{u} :=
  fun A _ ↦ MorphismProperty.ofHoms (iGeneratorValue A)

noncomputable def jValue : generatorClassType.{u} :=
  fun A _ ↦ MorphismProperty.ofHoms (jGeneratorValue A)

def degreewiseSurjectiveValue : generatorClassType.{u} :=
  fun _ _ _ _ f ↦ ∀ n : ℤ, Function.Surjective (f.f n)

def degreewiseLimitsAndColimitsType : Prop :=
  ∀ (A : Type u) [Ring A],
    HasLimits (Cochains A) ∧ HasColimits (Cochains A) ∧
      ∀ n : ℤ,
        PreservesLimits (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n) ∧
          PreservesColimits (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n)

/-- An element lift along the degree-`n` sphere-to-disk generator. -/
def iGeneratorLiftingType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y : Cochains A} (p : X ⟶ Y) (n : ℤ),
    HasLiftingProperty (iGeneratorValue A n) p ↔
      ∀ (z : X.X (n + 1)) (y : Y.X n),
        X.d (n + 1) (n + 1 + 1) z = 0 →
        p.f (n + 1) z = Y.d n (n + 1) y →
        ∃ x : X.X n, p.f n x = y ∧ X.d n (n + 1) x = z

def jRightLiftingType : Prop :=
  ∀ (A : Type u) [Ring A], (jValue A).rlp = degreewiseSurjectiveValue A

def iRightLiftingType : Prop :=
  ∀ (A : Type u) [Ring A], (iValue A).rlp =
    degreewiseSurjectiveValue A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ)

end DerivedFormalization.Specs.ComplexGenerators
