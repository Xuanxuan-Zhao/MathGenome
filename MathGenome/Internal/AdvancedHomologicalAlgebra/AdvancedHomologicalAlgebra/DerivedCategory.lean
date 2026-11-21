import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedCategory
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedFractions
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TriangleExactSequences

/-!
HA-D03. We use the actual chosen library derived category and its localization
of the shared homotopy category. The standard choice works for every abelian
category in Hom universe max u v; smaller choices are permitted explicitly.
HA-D01 identifies the ordinary cohomology kernel with the library acyclic
subcategory, so localization at its cone class is precisely the Verdier
localization. The inherited triangles are exactly the localized source rows.
For exact descent, killing the cone makes its first arrow invertible. Conversely,
inverting quasi-isomorphisms inverts the zero endomorphism of each acyclic
object, forcing its image to be zero. Localization then gives the factorization,
its shift comparison, exactness, and uniqueness on functors and transformations.
-/

set_option linter.checkUnivs false
universe w v u v' u'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory
open Specs.AdvancedHomologicalAlgebra.DerivedFractions
open Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory
open Specs.AdvancedHomologicalAlgebra.DerivedCategory

namespace AdvancedHomologicalAlgebra.DerivedCategory

noncomputable def standardChoice :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.standardChoiceType := standardChoiceValue

def derivedCategory :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.derivedCategoryType :=
  fun A _ _ _ => D A

noncomputable def quotient :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.quotientType := quotientValue

noncomputable def cohomology :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.cohomologyType := cohomologyValue

noncomputable def cohomologyFactors :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.cohomologyFactorsType := cohomologyFactorsValue

theorem localization :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.localizationType := by
  intro A _ _ _
  infer_instance

theorem verdierLocalization :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.verdierLocalizationType := by
  intro A _ _ _
  rw [AcyclicThickSubcategory.acyclicObjects_eq]
  infer_instance

theorem triangulated :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.triangulatedType := by
  intro A _ _ _
  infer_instance

theorem preservesTriangles :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.preservesTrianglesType := by
  intro A _ _ _ T hT
  exact (localizationQ A).map_distinguished T
    ((TriangulatedHomotopyCategory.distinguished_iff A T).mpr hT)

theorem distinguished :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.distinguishedType := by
  intro A _ _ _ T
  rw [(localizationQ A).distTriang_iff T]
  constructor
  · rintro ⟨T₀, e, hT₀⟩
    exact ⟨T₀, (TriangulatedHomotopyCategory.distinguished_iff A T₀).mp hT₀, ⟨e⟩⟩
  · rintro ⟨T₀, hT₀, ⟨e⟩⟩
    exact ⟨T₀, e, (TriangulatedHomotopyCategory.distinguished_iff A T₀).mpr hT₀⟩

theorem isIso_iff :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.isIso_iffType := by
  intro A _ _ _ X Y f
  exact _root_.DerivedCategory.isIso_iff A f

theorem isZero_iff :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.isZero_iffType := by
  intro A _ _ _ X
  constructor
  · intro hX n
    exact (HD A n).map_isZero hX
  · intro hX
    have h : IsIso (0 : X ⟶ X) := (isIso_iff A X X 0).mpr (fun n => by
      rw [Functor.map_zero]
      exact (hX n).isIso (hX n) 0)
    exact ((isIsoZero_iff_source_target_isZero X X).mp h).1

theorem kernel :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.kernelType := by
  intro A _ _ _ X
  rw [isZero_iff A]
  exact forall_congr' (fun n => ((_root_.DerivedCategory.homologyFunctorFactorsh A n).app X).isZero_iff)

theorem cohomologyExact :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.cohomologyExactType := by
  intro A _ _ _ T hT n
  exact (HD A 0).homologySequenceComposableArrows₅_exact T hT n (n + 1) rfl

noncomputable def universal :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.universalType := fun A _ _ _ E _ =>
  Localization.functorEquivalence (localizationQ A) (W A) E

theorem inverts_iff_kills :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.inverts_iff_killsType := by
  intro A _ _ E _ _ _ _ _ _ F _ _
  constructor
  · intro hF X hX
    have hW : W A (0 : X ⟶ X) := by
      change HomotopyCategory.quasiIso A (ComplexShape.up ℤ) (0 : X ⟶ X)
      rw [HomotopyCategory.mem_quasiIso_iff]
      intro n
      rw [Functor.map_zero]
      exact (hX n).isIso (hX n) 0
    have h := hF (0 : X ⟶ X) hW
    rw [F.map_zero] at h
    exact ((isIsoZero_iff_source_target_isZero (F.obj X) (F.obj X)).mp h).1
  · intro hF X Y f hf
    change HomotopyCategory.quasiIso A (ComplexShape.up ℤ) f at hf
    rw [← AcyclicThickSubcategory.coneClass_eq_quasiIso A] at hf
    obtain ⟨Z, g, h, hT, hZ⟩ := hf
    exact (Triangle.isZero₃_iff_isIso₁ _
      (F.map_distinguished _ ((TriangulatedHomotopyCategory.distinguished_iff A _).mpr hT))).mp
        (hF Z hZ)

theorem exactDescent :
    Specs.AdvancedHomologicalAlgebra.DerivedCategory.exactDescentType := by
  intro A _ _ _ E _ _ _ _ _ _ F _ _ hF
  let hW := (inverts_iff_kills A E F).mpr hF
  let G := Localization.lift F hW (localizationQ A)
  let := Functor.commShiftOfLocalization (localizationQ A) (W A) ℤ F G
  let e : localizationQ A ⋙ G ≅ F := Localization.fac F hW (localizationQ A)
  have : NatTrans.CommShift e.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift
      (Localization.Lifting.iso (localizationQ A) (W A) F G).hom ℤ)
  refine ⟨⟨G, inferInstance, e, inferInstance, ?_⟩⟩
  exact Functor.isTriangulated_of_precomp_iso e

end AdvancedHomologicalAlgebra.DerivedCategory
