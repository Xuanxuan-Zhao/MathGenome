import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TriangleExactSequences
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor

/-!
HA-K06. The upstream sign/class bridge lets us apply the long exact sequence
of a homological functor to exactly the source's distinguished triangles.
Representable functors are homological on every pretriangulated category;
ordinary cohomology on K(A) is homological when A is abelian. Every integer
indexes a six-term exact window, covering every position in the long sequence.
The opposite-triangle equivalence gives the reversed Hom sequence.
-/

set_option linter.checkUnivs false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Pretriangulated.Opposite
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.MappingCones
open Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory
open Specs.AdvancedHomologicalAlgebra.TriangleExactSequences

namespace AdvancedHomologicalAlgebra.TriangleExactSequences

/-- All squares are obtained by functoriality and the third triangle square. -/
lemma sequence_natural {C B : Type*} [Category* C] [HasShift C ℤ]
    [Category* B] [HasZeroMorphisms B] (F : C ⥤ B) [F.ShiftSequence ℤ]
    {D E : Triangle C} (φ : D ⟶ E) : Natural F φ := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁]
  · rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂]
  · exact F.homologySequenceδ_naturality φ n (n + 1) rfl

theorem covariantHom_exact :
    Specs.AdvancedHomologicalAlgebra.TriangleExactSequences.covariantHom_exactType := by
  intro A _ _ _ _ D hD U n
  exact (preadditiveCoyoneda.obj (Opposite.op U)).homologySequenceComposableArrows₅_exact D
    ((TriangulatedHomotopyCategory.distinguished_iff A D).mpr hD) n (n + 1) rfl

theorem contravariantHom_exact :
    Specs.AdvancedHomologicalAlgebra.TriangleExactSequences.contravariantHom_exactType := by
  intro A _ _ _ _ D hD U n
  exact (preadditiveYoneda.obj U).homologySequenceComposableArrows₅_exact _
    (op_distinguished D ((TriangulatedHomotopyCategory.distinguished_iff A D).mpr hD))
    n (n + 1) rfl

theorem cohomology_exact :
    Specs.AdvancedHomologicalAlgebra.TriangleExactSequences.cohomology_exactType := by
  intro A _ _ D hD n
  exact (H A 0).homologySequenceComposableArrows₅_exact D
    ((TriangulatedHomotopyCategory.distinguished_iff A D).mpr hD) n (n + 1) rfl

theorem covariantHom_natural :
    Specs.AdvancedHomologicalAlgebra.TriangleExactSequences.covariantHom_naturalType := by
  intro A _ _ _ _ D E φ U
  exact sequence_natural _ φ

theorem contravariantHom_natural :
    Specs.AdvancedHomologicalAlgebra.TriangleExactSequences.contravariantHom_naturalType := by
  intro A _ _ _ _ D E φ U
  exact sequence_natural _ _

theorem cohomology_natural :
    Specs.AdvancedHomologicalAlgebra.TriangleExactSequences.cohomology_naturalType := by
  intro A _ _ D E φ
  exact sequence_natural _ φ

theorem covariantHom_boundary :
    Specs.AdvancedHomologicalAlgebra.TriangleExactSequences.covariantHom_boundaryType := by
  intro A _ _ _ _ D U n x
  exact preadditiveCoyoneda_homologySequenceδ_apply D n (n + 1) rfl x

theorem contravariantHom_boundary :
    Specs.AdvancedHomologicalAlgebra.TriangleExactSequences.contravariantHom_boundaryType := by
  intro A _ _ _ _ D U n x
  exact preadditiveYoneda_homologySequenceδ_apply D n (n + 1) rfl x

theorem cohomology_boundary :
    Specs.AdvancedHomologicalAlgebra.TriangleExactSequences.cohomology_boundaryType := by
  intro A _ _ D n
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem cohomology_cone_sign :
    Specs.AdvancedHomologicalAlgebra.TriangleExactSequences.cohomology_cone_signType := by
  intro A _ _ X Y f n
  rw [cohomology_boundary A (coneTriangle f) n]
  change (H A n).map ((Q A).map (-projectionToShift f) ≫
      ((Q A).commShiftIso (1 : ℤ)).hom.app X) ≫
      (cohomologyShiftHomotopyValue A 1 n).hom.app ((Q A).obj X) = _
  rw [(Q A).map_neg, Preadditive.neg_comp, (H A n).map_neg, Preadditive.neg_comp]

end AdvancedHomologicalAlgebra.TriangleExactSequences
