import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ConeCriterion
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory

/-! HA-D01. Vanishing of every ordinary cohomology object defines the library
homological kernel. Its triangulated and isomorphism closure therefore apply to
exactly the cohomology and cone conventions already established in HA-K01/K05.
For thickness, apply cohomology to a retraction: its split epimorphism has zero
source, so the retract's cohomology is zero. Finally the cone-class bridge is
made for arbitrary triangles of K(A), not just maps with chosen representatives.
-/

set_option linter.checkUnivs false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory
open Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory

namespace AdvancedHomologicalAlgebra.AcyclicThickSubcategory

/-- Identification of the predicates, using all integer cohomology functors. -/
lemma acyclicObjects_eq (A : Type u) [Category.{v} A] [Abelian A] :
    acyclicObjects A = HomotopyCategory.subcategoryAcyclic A := by
  ext X
  exact (HomotopyCategory.mem_subcategoryAcyclic_iff X).symm

def acyclicSubcategory :
    Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory.acyclicSubcategoryType :=
  acyclicSubcategoryValue

def coneClass :
    Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory.coneClassType :=
  coneClassValue

theorem acyclic_quotient_iff :
    Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory.acyclic_quotient_iffType := by
  intro A _ _ X
  rw [acyclicObjects_eq]
  exact HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic X

/-- Triangulated closure of the full subcategory of acyclic objects. -/
instance acyclicObjects_isTriangulated (A : Type u) [Category.{v} A] [Abelian A] :
    (acyclicObjects A).IsTriangulated := by
  rw [acyclicObjects_eq]
  infer_instance

instance acyclicObjects_isClosedUnderIsomorphisms
    (A : Type u) [Category.{v} A] [Abelian A] :
    (acyclicObjects A).IsClosedUnderIsomorphisms := by
  rw [acyclicObjects_eq]
  infer_instance

/-- No splitting of arbitrary idempotents is required: existing retracts suffice. -/
instance acyclicObjects_isStableUnderRetracts
    (A : Type u) [Category.{v} A] [Abelian A] :
    (acyclicObjects A).IsStableUnderRetracts where
  of_retract r hY n := by
    let hr := r.map (H A n)
    exact IsZero.of_epi hr.r (hY n)

theorem thick :
    Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory.thickType := by
  intro A _ _
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem shift_closed :
    Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory.shift_closedType := by
  intro A _ _ X m hX
  exact (acyclicObjects A).le_shift m X hX

theorem cone_closed :
    Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory.cone_closedType := by
  intro A _ _ D hD h₁ h₂
  exact (acyclicObjects A).ext_of_isTriangulatedClosed₃ D
    ((TriangulatedHomotopyCategory.distinguished_iff A D).mpr hD) h₁ h₂

theorem mappingCone_closed :
    Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory.mappingCone_closedType := by
  intro A _ _ X Y f hX hY
  apply (acyclic_quotient_iff A _).mp
  exact cone_closed A (coneTriangle f) ⟨X, Y, f, ⟨Iso.refl _⟩⟩
    ((acyclic_quotient_iff A X).mpr hX) ((acyclic_quotient_iff A Y).mpr hY)

theorem coneClass_eq_quasiIso :
    Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory.coneClass_eq_quasiIsoType := by
  intro A _ _
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, ← acyclicObjects_eq A]
  ext X Y f
  constructor
  · rintro ⟨Z, g, h, hD, hZ⟩
    exact ⟨Z, g, h, (TriangulatedHomotopyCategory.distinguished_iff A _).mpr hD, hZ⟩
  · rintro ⟨Z, g, h, hD, hZ⟩
    exact ⟨Z, g, h, (TriangulatedHomotopyCategory.distinguished_iff A _).mp hD, hZ⟩

theorem cone_criterion :
    Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory.cone_criterionType :=
  ConeCriterion.coneCriterion

/-- Two-out-of-three is checked degree by degree on the actual cohomology maps. -/
theorem two_out_of_three :
    Specs.AdvancedHomologicalAlgebra.AcyclicThickSubcategory.two_out_of_threeType := by
  intro A _ _
  refine { comp_mem := ?_, of_postcomp := ?_, of_precomp := ?_ }
  · intro X Y Z f g hf hg n
    have := hf n
    have := hg n
    change IsIso ((H A n).map (f ≫ g))
    rw [Functor.map_comp]
    infer_instance
  · intro X Y Z f g hg hfg n
    exact (MorphismProperty.isomorphisms A).of_postcomp
      ((H A n).map f) ((H A n).map g) (hg n) (by
        simpa only [Functor.map_comp] using hfg n)
  · intro X Y Z f g hf hfg n
    exact (MorphismProperty.isomorphisms A).of_precomp
      ((H A n).map f) ((H A n).map g) (hf n) (by
        simpa only [Functor.map_comp] using hfg n)

end AdvancedHomologicalAlgebra.AcyclicThickSubcategory
