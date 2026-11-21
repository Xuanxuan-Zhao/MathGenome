import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.MappingCones

/-!
HA-K05, notes/002/advanced-homological-algebra.tex:1331–1400.
The global cochain conventions are at lines 107–109; the cone and its positive
projection are the shared HA-K02 objects. An additive category is expressed by
Preadditive, a zero object, and binary biproducts. No abelian hypothesis is used.

The specification states all axioms for the source's class of triangles itself.
In particular the three input triangles in the octahedron axiom are arbitrary
prescribed distinguished triangles, not chosen cone triangles.
-/

set_option linter.checkUnivs false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.MappingCones

namespace Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]

/-- The source row, with the third arrow -p, transported by the quotient functor
and its canonical comparison with shift [1]. -/
noncomputable def coneTriangle {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    Triangle (K A) :=
  (Q A).mapTriangle.obj (Triangle.mk f (targetInclusion f) (-projectionToShift f))

/-- Exactly the class in the source: all triangles isomorphic to a cone row. -/
def Distinguished (T : Triangle (K A)) : Prop :=
  ∃ (X Y : CochainComplex A ℤ) (f : X ⟶ Y), Nonempty (T ≅ coneTriangle f)

/-- TR1–TR4 for the specified shift and the specified class of triangles.
`rotate` has closing arrow -f[1]; its iff includes inverse rotation. -/
structure TriangulatedAxioms (A : Type u) [Category.{v} A] [Preadditive A]
    [HasZeroObject A] [HasBinaryBiproducts A] : Prop where
  isomorphic : ∀ (T₁ T₂ : Triangle (K A)), Distinguished T₁ →
    (T₂ ≅ T₁) → Distinguished T₂
  contractible : ∀ X : K A, Distinguished (contractibleTriangle X)
  completion : ∀ {X Y : K A} (f : X ⟶ Y),
    ∃ (Z : K A) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Distinguished (Triangle.mk f g h)
  rotation : ∀ T : Triangle (K A), Distinguished T ↔ Distinguished T.rotate
  morphism : ∀ (T₁ T₂ : Triangle (K A)), Distinguished T₁ → Distinguished T₂ →
    ∀ (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂),
    T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃,
      T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃
  octahedron : ∀ {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : K A}
    {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃},
    u₁₂ ≫ u₂₃ = u₁₃ →
    ∀ {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧},
    Distinguished (Triangle.mk u₁₂ v₁₂ w₁₂) →
    ∀ {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧},
    Distinguished (Triangle.mk u₂₃ v₂₃ w₂₃) →
    ∀ {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧},
    Distinguished (Triangle.mk u₁₃ v₁₃ w₁₃) →
    ∃ (a : Z₁₂ ⟶ Z₁₃) (b : Z₁₃ ⟶ Z₂₃),
      v₁₂ ≫ a = u₂₃ ≫ v₁₃ ∧ a ≫ w₁₃ = w₁₂ ∧
      v₁₃ ≫ b = v₂₃ ∧ w₁₃ ≫ u₁₂⟦(1 : ℤ)⟧' = b ≫ w₂₃ ∧
      Distinguished (Triangle.mk a b (w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧'))

/-- Explicit cone/sign bridge, including the quotient's shift comparison. -/
def coneTriangle_eqType := ∀ (A : Type u) [Category.{v} A] [Preadditive A]
  [HasBinaryBiproducts A] (X Y : CochainComplex A ℤ) (f : X ⟶ Y),
  coneTriangle f = CochainComplex.mappingCone.triangleh f

/-- Identification of the entire class of distinguished triangles. -/
def distinguished_iffType := ∀ (A : Type u) [Category.{v} A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A] (T : Triangle (K A)),
  T ∈ distTriang (K A) ↔ Distinguished T

/-- The full conclusion of HA-K05, stated for the source class. -/
def triangulatedType := ∀ (A : Type u) [Category.{v} A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A], TriangulatedAxioms A

end Specs.AdvancedHomologicalAlgebra.TriangulatedHomotopyCategory
