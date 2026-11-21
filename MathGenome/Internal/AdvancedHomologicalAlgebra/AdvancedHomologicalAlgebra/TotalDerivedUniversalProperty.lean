import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedFractions
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.BoundedDerivedModels

/-!
HA-R05. Universal comparison data and their consequences. No resolutions or
existence hypotheses are used here. The argument factors each comparison through
the other; injectivity of the universal map proves both inverse identities.
The same factorization gives maps of derived functors and their comparison square.
-/
set_option linter.checkUnivs false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty

namespace AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty

section Bounded
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B]

def termwisePlus : termwisePlusType (A := A) (B := B) := termwisePlusValue

def termwiseMinus : termwiseMinusType (A := A) (B := B) := termwiseMinusValue

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]

noncomputable def plusU : plusUType (A := A) (B := B) := plusUValue

noncomputable def minusU : minusUType (A := A) (B := B) := minusUValue

noncomputable def rightDerivedData : rightDerivedDataType.{u, v, u', v', w, w'}
    (A := A) (B := B) := rightDerivedDataValue.{u, v, u', v', w, w'}

noncomputable def leftDerivedData : leftDerivedDataType.{u, v, u', v', w, w'}
    (A := A) (B := B) := leftDerivedDataValue.{u, v, u', v', w, w'}

noncomputable def plusUMap : plusUMapType (A := A) (B := B) := plusUMapValue

noncomputable def minusUMap : minusUMapType (A := A) (B := B) := minusUMapValue
end Bounded

theorem rightUniversal : rightUniversalType := by
  intro C D E _ _ _ Q U R H
  exact ⟨Equiv.ofBijective _ (R.universal H), fun _ => rfl⟩

theorem leftUniversal : leftUniversalType := by
  intro C D E _ _ _ Q U R H
  exact ⟨Equiv.ofBijective _ (R.universal H), fun _ => rfl⟩

theorem rightMap : rightMapType := by
  intro C D E _ _ _ Q U V R S τ
  obtain ⟨α, hα⟩ := (R.universal S.functor).2 (τ ≫ S.unit)
  exact ⟨α, hα, fun β hβ => (R.universal S.functor).1 (hβ.trans hα.symm)⟩

theorem leftMap : leftMapType := by
  intro C D E _ _ _ Q U V R S τ
  obtain ⟨α, hα⟩ := (S.universal R.functor).2 (R.counit ≫ τ)
  exact ⟨α, hα, fun β hβ => (S.universal R.functor).1 (hβ.trans hα.symm)⟩

theorem rightUnique : rightUniqueType := by
  intro C D E _ _ _ Q U R S
  obtain ⟨f, hf⟩ := (R.universal S.functor).2 S.unit
  obtain ⟨g, hg⟩ := (S.universal R.functor).2 R.unit
  have hfg : f ≫ g = 𝟙 R.functor := (R.universal R.functor).1 (by
    simp only [whiskerLeft_comp, ← Category.assoc, hf, hg, whiskerLeft_id',
      Category.comp_id])
  have hgf : g ≫ f = 𝟙 S.functor := (S.universal S.functor).1 (by
    simp only [whiskerLeft_comp, ← Category.assoc, hf, hg, whiskerLeft_id',
      Category.comp_id])
  refine ⟨⟨f, g, hfg, hgf⟩, hf, ?_⟩
  intro e he
  apply Iso.ext
  exact (R.universal S.functor).1 (he.trans hf.symm)

theorem leftUnique : leftUniqueType := by
  intro C D E _ _ _ Q U R S
  obtain ⟨f, hf⟩ := (S.universal R.functor).2 R.counit
  obtain ⟨g, hg⟩ := (R.universal S.functor).2 S.counit
  have hfg : f ≫ g = 𝟙 R.functor := (R.universal R.functor).1 (by
    simp only [whiskerLeft_comp, Category.assoc, hf, hg, whiskerLeft_id',
      Category.id_comp])
  have hgf : g ≫ f = 𝟙 S.functor := (S.universal S.functor).1 (by
    simp only [whiskerLeft_comp, Category.assoc, hf, hg, whiskerLeft_id',
      Category.id_comp])
  refine ⟨⟨f, g, hfg, hgf⟩, hf, ?_⟩
  intro e he
  apply Iso.ext
  exact (S.universal R.functor).1 (he.trans hf.symm)

theorem rightOriginalMap : rightOriginalMapType := by
  intro A B _ _ _ _ _ _ F G _ _ R S τ
  exact rightMap _ _ _ _ _ _ R S (plusUMapValue F G τ)

theorem leftOriginalMap : leftOriginalMapType := by
  intro A B _ _ _ _ _ _ F G _ _ R S τ
  exact leftMap _ _ _ _ _ _ R S (minusUMapValue F G τ)

end AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
