import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.Relations
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.PathOperators
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Notation

/-! The path algebra, arrow ideal, and module action for the quiver with one arrow. -/

open scoped Matrix ModuleCat

namespace RM03.OneArrowSpec

universe w d

/-- The vertices `false` and `true` stand for 1 and 2, respectively. -/
abbrev Vertex := Bool

scoped instance : Quiver Vertex := quiverOfArrows (fun _ : Unit => false) (fun _ => true)

def edge : Quiver.Hom (false : Vertex) (true : Vertex) := ⟨(), rfl, rfl⟩

/-- The three claimed paths in order: the two trivial paths, then the arrow. -/
def pathAt : Fin 3 → Path Vertex :=
  ![Path.vertex false, Path.vertex true, Path.arrow edge]

/-- The lower triangular subalgebra of actual two-by-two matrices. -/
def lowerTriangular (k : Type w) [Field k] : Subalgebra k (Matrix (Fin 2) (Fin 2) k) where
  carrier := {m | m 0 1 = 0}
  mul_mem' {m n} hm hn := by
    change m 0 1 = 0 at hm
    change n 0 1 = 0 at hn
    change (m * n) 0 1 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, hm, hn]
  add_mem' {m n} hm hn := by
    change m 0 1 = 0 at hm
    change n 0 1 = 0 at hn
    change m 0 1 + n 0 1 = 0
    rw [hm, hn, add_zero]
  algebraMap_mem' c := by
    change algebraMap k (Matrix (Fin 2) (Fin 2) k) c 0 1 = 0
    simp [Matrix.algebraMap_matrix_apply]

def matrix {k : Type w} [Field k] (x u y : k) : lowerTriangular k :=
  ⟨!![x, 0; u, y], rfl⟩

section Spaces

variable {k : Type w} [Field k] {V₁ V₂ : Type d}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]

def spaces : Vertex → ModuleCat.{d} k
  | false => ModuleCat.of k V₁
  | true => ModuleCat.of k V₂

def representation (T : V₁ →ₗ[k] V₂) : QuiverRepresentationSpec.Carrier k Vertex :=
  QuiverRepresentationSpec.ofArrows (spaces (V₁ := V₁) (V₂ := V₂))
    (fun {i j} a => by
      rcases a with ⟨⟨⟩, rfl, rfl⟩
      exact T)

/-- The two direct sum coordinates in the order of the vertices. -/
def pair (T : V₁ →ₗ[k] V₂) : PathOperatorsSpec.Total (representation T) →ₗ[k] V₁ × V₂ :=
  (PathOperatorsSpec.projection (representation T) false).prod
    (PathOperatorsSpec.projection (representation T) true)

end Spaces

def OrderedPathBasis : Prop :=
  Function.Bijective pathAt ∧
    ∀ (k : Type w) [Field k], ∃ b : Module.Basis (Fin 3) k (PathAlgebraSpec.Carrier k Vertex),
      ∀ i, b i = PathAlgebraSpec.ofPath k Vertex (pathAt i)

section
attribute [local instance] QuiverRelationSpec.nonUnitalNonAssocRing

def SquareZeroAndAdmissible : Prop :=
  ∀ (k : Type w) [Field k],
    QuiverRelationSpec.idealPower (QuiverRelationSpec.arrowIdeal k Vertex) 2 = ⊥ ∧
    QuiverRelationSpec.admissible (⊥ : TwoSidedIdeal (PathAlgebraSpec.Carrier k Vertex))

end

/-- The matrix isomorphism and the action transported along its inverse.
The module coordinates realize the prescribed path operators on the direct sum. -/
def MatrixAndAction : Prop :=
  ∀ (k : Type w) [Field k],
    ∃ (r : Ring (PathAlgebraSpec.Carrier k Vertex))
      (a : @Algebra k (PathAlgebraSpec.Carrier k Vertex) _ r.toSemiring),
      PathOperatorsSpec.IsPathAlgebra r a ∧
      letI := r
      letI := a
      ∃ E : PathAlgebraSpec.Carrier k Vertex ≃ₐ[k] lowerTriangular k,
        (↑(E (PathAlgebraSpec.vertex k Vertex false)) : Matrix (Fin 2) (Fin 2) k) =
          Matrix.single 0 0 1 ∧
        (↑(E (PathAlgebraSpec.vertex k Vertex true)) : Matrix (Fin 2) (Fin 2) k) =
          Matrix.single 1 1 1 ∧
        (↑(E (PathAlgebraSpec.arrow k Vertex edge)) : Matrix (Fin 2) (Fin 2) k) =
          Matrix.single 1 0 1 ∧
        ∀ (V₁ V₂ : Type d) [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
          (T : V₁ →ₗ[k] V₂),
          Function.Bijective (pair T) ∧
          ∃ (M : ModuleCat.{d} (PathAlgebraSpec.Carrier k Vertex))
            (J : M ≃ₗ[k] PathOperatorsSpec.Total (representation T)),
            (∀ b v, J (b • v) = PathOperatorsSpec.linearExtension (representation T) b (J v)) ∧
            ∀ (x u y : k) (v : M),
              (pair T) (J (E.symm (matrix x u y) • v)) =
                (x • ((pair T) (J v)).1, u • T ((pair T) (J v)).1 + y • ((pair T) (J v)).2)

end RM03.OneArrowSpec
