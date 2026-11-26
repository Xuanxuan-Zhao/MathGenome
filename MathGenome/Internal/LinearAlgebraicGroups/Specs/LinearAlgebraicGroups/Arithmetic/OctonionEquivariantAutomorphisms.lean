import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.OctonionAutomorphisms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeFormComparison

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u v

namespace LinearAlgebraicGroups.Specs.OctonionEquivariantAutomorphisms

open AutomorphismSequence (relativePoints innerAut)
open RelativeFormComparison (fieldTest transportedAut)
open LinearAlgebraicGroups.Composition
open Composition.Specification (OctonionNormConditions normBaseChange)
open PeirceSpecification (tensorMap)
open OctonionAutomorphismSpecification (AutomorphismGroup)
open LinearAlgebraicGroups.Descent (SemilinearAction)

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The relative affine test given by a scalar map from the extension field. -/
abbrev affineTest {S : TestAlgebra k} (f : CommAlgCat.of k K ⟶ S) : Over (fieldTest k K) :=
  Over.mk ((testSpec k).map f.op)

/-- Extend the linear comparison to the test algebra using its specified scalar map. -/
def extendComparison {C : Type v} {D : Type*} [AddCommGroup C] [AddCommGroup D]
    [Module k C] [Module k D] {S : TestAlgebra k} (f : CommAlgCat.of k K ⟶ S)
    (e : (K ⊗[k] C) →ₗ[K] (K ⊗[k] D)) : (S ⊗[k] C) →ₗ[S] (S ⊗[k] D) :=
  ((tensorMap f.hom).comp ((e.restrictScalars k).comp
    (TensorProduct.mk k K C 1))).liftBaseChange S

/-- Conjugation on all relative points has the indicated effect on affine tests and
the prescribed inner displacement. -/
def EquivariantAutomorphisms : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {C : Type v} [NonAssocRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]
    {n : QuadraticForm k C} (hn : OctonionNormConditions n)
    (A₀ : AutomorphismGroup k (Zorn k)) (A : AutomorphismGroup k C)
    (c : Gal(K/k) → (fieldTest k K ⟶ A₀.group.X))
    (e : (K ⊗[k] C) ≃ₗ[K] (K ⊗[k] Zorn k)),
    e 1 = 1 →
    (∀ x y, e (x * y) = e x * e y) →
    (letI := hn.projective
     ∀ x, normBaseChange K (ZornSpecification.norm k) (e x) = normBaseChange K n x) →
    (∀ σ x, (A₀.subgroupPoints (CommAlgCat.of k K) (c σ)).val.val
      ((SemilinearAction.scalarExtension (k := k) (K := K) (Zorn k)).act σ (e x)) =
      e ((SemilinearAction.scalarExtension (k := k) (K := K) C).act σ x)) →
    ∃ j : relativePoints A₀.group (fieldTest k K) ≅ relativePoints A.group (fieldTest k K),
      (∀ (S : TestAlgebra k) (f : CommAlgCat.of k K ⟶ S)
        (p : Points A₀.group.X S) (x : S ⊗[k] C),
        let q : Points A.group.X S := (j.hom.app (op (affineTest f))).hom p
        extendComparison f e.toLinearMap ((A.subgroupPoints S q).val.val x) =
          (A₀.subgroupPoints S p).val.val (extendComparison f e.toLinearMap x)) ∧
      ∀ σ : Gal(K/k), transportedAut k K j σ = innerAut (c σ)

end

end LinearAlgebraicGroups.Specs.OctonionEquivariantAutomorphisms
