import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.MappingCones
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.ZMod.Basic

/-! HA-K03, notes/002/advanced-homological-algebra.tex:1268–1298.
Cochain conventions are those of the source, with degrees -1 and 0 for the
integral two-term complex. Contractibility means that its identity is homotopic
to zero; acyclicity and quasi-isomorphism use ordinary cohomology in all degrees.
-/
set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
namespace Specs.AdvancedHomologicalAlgebra.ConeCriterion

/-- The identity cone is contractible in every additive category. -/
def identityConeContractibleType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X : CochainComplex A ℤ),
    Nonempty (Homotopy (𝟙 (MappingCones.coneComplex (𝟙 X))) 0)

/-- The cone criterion, without any boundedness restrictions. -/
def coneCriterionType : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (X Y : CochainComplex A ℤ) (f : X ⟶ Y),
    QuasiIso f ↔ (MappingCones.coneComplex f).Acyclic

abbrev integers : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ
abbrev modTwo : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 2)
def doubling : integers ⟶ integers := 2 • 𝟙 _
def reduction : integers ⟶ modTwo :=
  ModuleCat.ofHom (Int.castAddHom (ZMod 2)).toIntLinearMap

/-- Z --2--> Z, in cochain degrees -1 and 0, zero elsewhere. -/
noncomputable def twoTerm : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  HomologicalComplex.double doubling (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)
/-- The stalk (Z/2)[0]. -/
noncomputable def stalk : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  (HomologicalComplex.single (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) 0).obj modTwo

/-- The quotient map in degree zero. -/
noncomputable def augmentation : twoTerm ⟶ stalk :=
  HomologicalComplex.mkHomToSingle
    ((HomologicalComplex.doubleXIso₁ doubling (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)
      (by decide)).hom ≫ reduction)
    (by
      intro i hi
      have : i = -1 := by change i + 1 = 0 at hi; omega
      subst i
      dsimp only [twoTerm]
      rw [HomologicalComplex.double_d _ _ (by decide)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      suffices doubling ≫ reduction = 0 by rw [this, comp_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ((2 * x : ℤ) : ZMod 2) = 0
      rw [Int.cast_mul, show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul])

def twoTermType := CochainComplex (ModuleCat.{0} ℤ) ℤ
noncomputable def twoTermValue : twoTermType := twoTerm

def augmentationType := twoTerm ⟶ stalk
noncomputable def augmentationValue : augmentationType := augmentation

def augmentationQuasiIsoType : Prop := QuasiIso augmentation

/-- Even the equation on the stalk required of a homotopy inverse is impossible. -/
def augmentationNoHomotopyInverseType : Prop :=
  ∀ g : stalk ⟶ twoTerm, ¬ Nonempty (Homotopy (g ≫ augmentation) (𝟙 stalk))

/-- The existential assertion about module complexes in the proposition. -/
def moduleCounterexampleType : Prop :=
  ∃ (X Y : CochainComplex (ModuleCat.{0} ℤ) ℤ) (f : X ⟶ Y),
    QuasiIso f ∧ ¬ HomologicalComplex.homotopyEquivalences (ModuleCat.{0} ℤ)
      (ComplexShape.up ℤ) f

end Specs.AdvancedHomologicalAlgebra.ConeCriterion
