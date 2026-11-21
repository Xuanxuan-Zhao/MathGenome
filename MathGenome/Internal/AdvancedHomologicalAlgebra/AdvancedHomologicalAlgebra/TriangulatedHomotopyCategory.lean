import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! HA-K05. The HA-K02 cone is Mathlib's cone in the source coordinates Y,X[1].
Its positive projection is the negative of Mathlib's third arrow, so the source
row with -p is exactly the library row. We first prove this equality and identify
the full isomorphism-closed class, then transfer TR1–TR4. The library octahedron
axiom applies to arbitrary prescribed triangles; no choice of cone representatives
is imposed on the inputs of our theorem.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.MappingCones
open Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory

namespace AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory

theorem coneTriangle_eq :
    Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory.coneTriangle_eqType := by
  intro A _ _ _ X Y f
  simp only [coneTriangle, projectionToShift, neg_neg]
  rfl

theorem distinguished_iff :
    Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory.distinguished_iffType := by
  intro A _ _ _ _ T
  change (∃ (X Y : CochainComplex A ℤ) (f : X ⟶ Y),
    Nonempty (T ≅ CochainComplex.mappingCone.triangleh f)) ↔ _
  constructor
  · rintro ⟨X, Y, f, h⟩
    refine ⟨X, Y, f, ?_⟩
    simpa only [coneTriangle_eq A X Y f] using h
  · rintro ⟨X, Y, f, h⟩
    refine ⟨X, Y, f, ?_⟩
    simpa only [coneTriangle_eq A X Y f] using h

/-- All triangulated axioms, including the octahedron on any three prescribed rows. -/
theorem triangulated :
    Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory.triangulatedType := by
  intro A _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T₁ T₂ h e
    exact (distinguished_iff A T₂).mp
      (isomorphic_distinguished T₁ ((distinguished_iff A T₁).mpr h) T₂ e)
  · intro X
    exact (distinguished_iff A _).mp (contractible_distinguished X)
  · intro X Y f
    obtain ⟨Z, g, h, H⟩ := distinguished_cocone_triangle f
    exact ⟨Z, g, h, (distinguished_iff A _).mp H⟩
  · intro T
    exact (distinguished_iff A T).symm.trans
      ((rotate_distinguished_triangle T).trans (distinguished_iff A T.rotate))
  · intro T₁ T₂ h₁ h₂ a b comm
    exact complete_distinguished_triangle_morphism T₁ T₂
      ((distinguished_iff A T₁).mpr h₁) ((distinguished_iff A T₂).mpr h₂) a b comm
  · intro X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ comm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃
    obtain ⟨O⟩ := IsTriangulated.octahedron_axiom comm
      ((distinguished_iff A _).mpr h₁₂) ((distinguished_iff A _).mpr h₂₃)
      ((distinguished_iff A _).mpr h₁₃)
    exact ⟨O.m₁, O.m₃, O.comm₁, O.comm₂, O.comm₃, O.comm₄,
      (distinguished_iff A _).mp O.mem⟩

end AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory
