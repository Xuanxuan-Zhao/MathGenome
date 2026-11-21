import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.Representations
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! The vertex-space construction and its canonical decomposition. -/

open CategoryTheory
open scoped BigOperators Classical DirectSum ModuleCat

namespace RM03.ModuleVerticesSpec

universe u v w d

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]

abbrev Coefficients (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] :=
  PathAlgebraSpec.Carrier k Q

section
variable [Ring (Coefficients k Q)] [Algebra k (Coefficients k Q)]

/-- The action of a path algebra element is linear over the coefficient field. -/
noncomputable def act (M : ModuleCat.{d} (Coefficients k Q)) (b : Coefficients k Q) :
    M →ₗ[k] M :=
  DistribSMul.toLinearMap k M b

noncomputable def vertexProjection (M : ModuleCat.{d} (Coefficients k Q)) (i : Q) :
    M →ₗ[k] M :=
  act M (PathAlgebraSpec.vertex k Q i)

/-- The vertex space is the image of the operator `m ↦ eᵢ • m`. -/
noncomputable def vertexSpace (M : ModuleCat.{d} (Coefficients k Q)) (i : Q) :
    Submodule k M :=
  LinearMap.range (vertexProjection M i)

noncomputable def project (M : ModuleCat.{d} (Coefficients k Q)) (i : Q) :
    M →ₗ[k] vertexSpace M i :=
  (vertexProjection M i).rangeRestrict

/-- Apply the arrow and project to its target space. The target projection fixes its image. -/
noncomputable def arrowMap (M : ModuleCat.{d} (Coefficients k Q))
    {i j : Q} (a : Quiver.Hom i j) : vertexSpace M i →ₗ[k] vertexSpace M j :=
  (project M j).comp ((act M (PathAlgebraSpec.arrow k Q a)).comp (vertexSpace M i).subtype)

/-- Apply a module homomorphism at a vertex, with codomain the corresponding vertex image. -/
noncomputable def restrictMap {M N : ModuleCat.{d} (Coefficients k Q)}
    (f : M ⟶ N) (i : Q) : vertexSpace M i →ₗ[k] vertexSpace N i :=
  (project N i).comp ((f.hom.restrictScalars k).comp (vertexSpace M i).subtype)

noncomputable def representation (M : ModuleCat.{d} (Coefficients k Q)) :
    QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q :=
  QuiverRepresentationSpec.ofArrows (fun i => ModuleCat.of k (vertexSpace M i))
    (fun a => arrowMap M a)

abbrev VertexSum (M : ModuleCat.{d} (Coefficients k Q)) :=
  ⨁ i : Q, ↥(vertexSpace M i)

/-- Sum the inclusions of the vertex subspaces into the ambient module. -/
noncomputable def sumMap (M : ModuleCat.{d} (Coefficients k Q)) :
    VertexSum M →ₗ[k] M :=
  DirectSum.coeLinearMap (vertexSpace M)

/-- Take all the vertex coordinates of a module element. -/
noncomputable def decomposeMap (M : ModuleCat.{d} (Coefficients k Q)) :
    M →ₗ[k] VertexSum M :=
  (DirectSum.linearEquivFunOnFintype k Q _).symm.toLinearMap.comp (LinearMap.pi (project M))

def FunctorFormula (F : ModuleCat.{d} (Coefficients k Q) ⥤
    QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q) : Prop :=
  F.Additive ∧ F.Linear k ∧
    ∃ h : ∀ M, F.obj M = representation M,
      ∀ {M N} (f : M ⟶ N) (i : Q),
        QuiverRepresentationSpec.component (eqToHom (h M).symm ≫ F.map f ≫ eqToHom (h N)) i =
          restrictMap f i

def SumEquivalenceFormula
    (E : ∀ M : ModuleCat.{d} (Coefficients k Q), VertexSum M ≃ₗ[k] M) : Prop :=
  (∀ M, (E M).toLinearMap = sumMap M) ∧
  (∀ (M : ModuleCat.{d} (Coefficients k Q)) (m : M) (i : Q),
    ((E M).symm m i : M) = PathAlgebraSpec.vertex k Q i • m) ∧
  (∀ (M : ModuleCat.{d} (Coefficients k Q)) (i : Q) (x : vertexSpace M i),
    E M (DirectSum.lof k Q (fun j => ↥(vertexSpace M j)) i x) = (x : M)) ∧
  (∀ {M N : ModuleCat.{d} (Coefficients k Q)} (f : M ⟶ N) (x : VertexSum M),
    E N (DirectSum.lmap (restrictMap f) x) = f.hom (E M x))

def ActionFormula
    (E : ∀ M : ModuleCat.{d} (Coefficients k Q), VertexSum M ≃ₗ[k] M) : Prop :=
  (∀ (M : ModuleCat.{d} (Coefficients k Q)) (i : Q) (x : VertexSum M),
    E M (DirectSum.lof k Q (fun j => ↥(vertexSpace M j)) i (x i)) =
      PathAlgebraSpec.vertex k Q i • E M x) ∧
  (∀ (M : ModuleCat.{d} (Coefficients k Q)) {i j : Q} (a : Quiver.Hom i j) (x : VertexSum M),
    E M (DirectSum.lof k Q (fun l => ↥(vertexSpace M l)) j
      (QuiverRepresentationSpec.arrow (representation M) a (x i))) =
      PathAlgebraSpec.arrow k Q a • E M x)

def MapFormula : Prop :=
  (∀ (M : ModuleCat.{d} (Coefficients k Q)) {i j : Q} (a : Quiver.Hom i j)
    (x : vertexSpace M i),
    (show vertexSpace M j from QuiverRepresentationSpec.arrow (representation M) a x).val =
      PathAlgebraSpec.arrow k Q a • (x : M)) ∧
  (∀ {M N : ModuleCat.{d} (Coefficients k Q)} (f : M ⟶ N) (i : Q) (x : vertexSpace M i),
    (restrictMap f i x : N) = f.hom x)

end

/-- Use the specified path algebra operations and scalar structure. For every unital module on
that algebra the forward functor and the direct-sum isomorphism have the indicated formulas. -/
def Construction : Prop :=
  ∀ (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Fintype Q],
    ∃ r : Ring (Coefficients k Q),
      r.toAddCommGroup = inferInstanceAs (AddCommGroup (Coefficients k Q)) ∧
      r.toSemiring.toMonoidWithZero.toMonoid.toMulOneClass.toMul =
        inferInstanceAs (Mul (Coefficients k Q)) ∧
      r.toSemiring.toMonoidWithZero.toMonoid.toMulOneClass.toOne =
        inferInstanceAs (One (Coefficients k Q)) ∧
      ∃ a : @Algebra k (Coefficients k Q) _ r.toSemiring,
        a.toSMul = inferInstanceAs (SMul k (Coefficients k Q)) ∧
        (∀ c, a.algebraMap c = PathAlgebraSpec.scalarMap k Q c) ∧
        letI := r
        letI := a
        MapFormula.{u, v, w, d} (k := k) (Q := Q) ∧
        ∃ (F : ModuleCat.{d} (Coefficients k Q) ⥤
            QuiverRepresentationSpec.Carrier.{u, v, w, d} k Q)
          (E : ∀ M : ModuleCat.{d} (Coefficients k Q), VertexSum M ≃ₗ[k] M),
          FunctorFormula F ∧ SumEquivalenceFormula E ∧ ActionFormula E

end RM03.ModuleVerticesSpec
