import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TotalRightDerivedFunctor

/-! HA-R06. We use Mathlib's bounded-below injective derivability structure.
Its objects are genuine complexes of injectives, without any left exactness
assumption on F. The derived functor is its left Kan extension along Q_A.
The hom-equivalence below identifies this with the exact HA-R05 comparison.
The replacement formula uses naturality, invertibility of Q(f), and invertibility
of the comparison on I; thus it applies to every replacement, independently
of how the injective models were chosen. -/
noncomputable section
set_option linter.checkUnivs false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.TotalRightDerivedFunctor

namespace AdvancedHomologicalAlgebra.TotalRightDerivedFunctor

section
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} B] [EnoughInjectives A]

noncomputable def rightFunctor : rightFunctorType (A := A) (B := B) := rightFunctorValue
noncomputable def unit : unitType (A := A) (B := B) := unitValue
noncomputable def derivedMap : derivedMapType (A := A) (B := B) := derivedMapValue
end

theorem universal : universalType := by
  intro A B _ _ _ _ _ _ _ F _ H
  have := Functor.IsRightDerivedFunctor.isLeftKanExtension
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A)
  exact (F.rightDerivedFunctorPlus.homEquivOfIsLeftKanExtension
    F.rightDerivedFunctorPlusUnith H).bijective

theorem exact : exactType := by
  intro A B _ _ _ _ _ _ _ F _
  classical
  exact ⟨inferInstanceAs (F.rightDerivedFunctorPlus.CommShift ℤ),
    inferInstanceAs F.rightDerivedFunctorPlus.IsTriangulated,
    inferInstanceAs (NatTrans.CommShift F.rightDerivedFunctorPlusUnith ℤ)⟩

theorem modelComparison : modelComparisonType := by
  intro A B _ _ _ _ _ _ _ F _ I hI
  let := hI
  exact inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnith.app I))

/-- The formula for the complex comparison shows it is invertible on every
termwise injective complex, not just complexes packaged over InjectiveObject. -/
private lemma complex_model_comparison
    {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
    [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (I : CochainComplex.Plus A)
    (hI : ∀ n : ℤ, Injective (I.obj.X n)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app I) := by
  let := hI
  simp only [Functor.rightDerivedFunctorPlusUnit_app]
  infer_instance

theorem computesReplacement : computesReplacementType := by
  intro A B _ _ _ _ _ _ _ F _ X I f hf hI
  let := hf
  let _ : IsIso (F.rightDerivedFunctorPlusUnit.app I) := complex_model_comparison F I hI
  have : IsIso (_root_.DerivedCategory.Plus.Q.map f) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso A) f hf
  let e := (F.rightDerivedFunctorPlus.mapIso
    (asIso (_root_.DerivedCategory.Plus.Q.map f))) ≪≫
      (asIso (F.rightDerivedFunctorPlusUnit.app I)).symm
  refine ⟨e, ?_⟩
  change F.rightDerivedFunctorPlusUnit.app X ≫
    (F.rightDerivedFunctorPlus.map (_root_.DerivedCategory.Plus.Q.map f) ≫
      inv (F.rightDerivedFunctorPlusUnit.app I)) = _
  have h := F.rightDerivedFunctorPlusUnit.naturality f
  dsimp only [Functor.comp_map] at h
  rw [← Category.assoc, ← h]
  simp

theorem derivedMapComparison : derivedMapComparisonType := by
  intro A B _ _ _ _ _ _ _ F G _ _ τ
  exact τ.rightDerivedFunctorPlus_fach

theorem derivedMapModel : derivedMapModelType := by
  intro A B _ _ _ _ _ _ _ F G _ _ τ I hI
  dsimp only [rightFunctorValue, derivedMapValue]
  let _ : IsIso (F.rightDerivedFunctorPlusUnit.app I) := complex_model_comparison F I hI
  let _ : IsIso (G.rightDerivedFunctorPlusUnit.app I) := complex_model_comparison G I hI
  refine ⟨asIso (F.rightDerivedFunctorPlusUnit.app I),
    asIso (G.rightDerivedFunctorPlusUnit.app I), rfl, rfl, ?_⟩
  have h := τ.rightDerivedFunctorPlus_fac_app I
  dsimp [derivedMapValue, rightFunctorValue]
  rw [← h]
  simp

theorem shiftCompatibility : shiftCompatibilityType := by
  intro A B _ _ _ _ _ _ _ F _
  classical
  exact ⟨inferInstanceAs (F.rightDerivedFunctorPlus.CommShift ℤ),
    inferInstanceAs F.rightDerivedFunctorPlus.IsTriangulated,
    inferInstanceAs (NatTrans.CommShift F.rightDerivedFunctorPlusUnith ℤ),
    inferInstanceAs (NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ)⟩

end AdvancedHomologicalAlgebra.TotalRightDerivedFunctor
