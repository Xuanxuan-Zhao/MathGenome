import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldWeilAdelicPoints
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldWeilGroupStructure
import Mathlib.Topology.Algebra.Group.Quotient

open CategoryTheory
open scoped RatFunc RestrictedProduct TensorProduct

universe u v

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LinearAlgebraicGroups.Specs.FunctionFieldAnisotropicCompactness

open Arithmetic Arithmetic.AdelicGroups
open GeometricRadicals (IsSemisimple)
open IntegralModels (MatrixRealization RationalPoints)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- An anisotropic group has no closed split torus of positive rank over its ground field. -/
abbrev IsAnisotropic {K : Type u} [Field K] (G : AffineAlgebraicGroup K) : Prop :=
  FunctionFieldWeilGroupStructure.IsAnisotropic G

/-- The subgroup of rational points in the full adelic group. -/
def rationalDiagonal {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) :
    Subgroup (Adeles D i ∅) where
  carrier := DiscreteDiagonals.groupDiagonalImage D i
  one_mem' := ⟨1, fun w => (map_one (localPoint D i w.1)).symm⟩
  mul_mem' := by
    rintro a b ⟨g, hg⟩ ⟨h, hh⟩
    exact ⟨g * h, fun w => by
      change a w * b w = _
      rw [hg w, hh w, map_mul]⟩
  inv_mem' := by
    rintro a ⟨g, hg⟩
    exact ⟨g⁻¹, fun w => by
      change (a w)⁻¹ = _
      rw [hg w, map_inv]⟩

/-- The orbit space for right multiplication by the rational diagonal, with the quotient topology. -/
abbrev AdelicQuotient {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) :=
  Adeles D i ∅ ⧸ rationalDiagonal D i

-- Fix the existing restricted product and quotient topologies before
-- specializing the field data.
private abbrev adelesTopology {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) :
    TopologicalSpace (Adeles D i ∅) :=
  inferInstance

private abbrev quotientTopology {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) :
    TopologicalSpace (AdelicQuotient D i) :=
  inferInstance

/-- The rational function field with its usual separating parameter. -/
abbrev rationalParameter (F : Type u) [Field F] : SeparatingParameter F F⟮X⟯ :=
  FunctionFieldWeilAdelicPoints.rationalParameter F

/-- The map from the scalar-extended test algebra to a factor, induced by its
two compatible scalar embeddings. -/
abbrev tensorPointMap {k K R L : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] [CommRing L] [Algebra K L] (f : R →+* L)
    (hf : f.comp (algebraMap k R) = (algebraMap K L).comp (algebraMap k K)) :
    R ⊗[k] K →ₐ[K] L :=
  FunctionFieldWeilAdelicPoints.tensorSpecialization f hf

/-- The natural point map of a represented Weil restriction, followed by the
specified specialization of the extended test algebra. -/
abbrev restrictionPoint {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : AffineAlgebraicGroup K} {W : AffineAlgebraicGroup k}
    (e : (groupPointsFunctor k).obj W.val ≅
      LinearAlgebraicGroups.WeilRestriction.extendScalars k K ⋙
        (groupPointsFunctor K).obj G.val)
    {R L : Type u} [CommRing R] [Algebra k R] [CommRing L] [Algebra K L]
    (f : R ⊗[k] K →ₐ[K] L) :
    ((groupPointsFunctor k).obj W.val).obj (CommAlgCat.of k R) →*
      ((groupPointsFunctor K).obj G.val).obj (CommAlgCat.of K L) :=
  FunctionFieldWeilAdelicPoints.specializedPoint e f

/-- Weil restriction along a separating parameter preserves semisimplicity and
anisotropy, and identifies rational points, full adelic groups, and their
right quotients. Each adelic coordinate is obtained from the canonical
specialization into that extension completion, including every pole of the
parameter. -/
def WeilRestrictionComparison : Prop :=
  ∀ {F K : Type u} [Field F] [Finite F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G),
    letI := t.rationalAlgebra
    let D : GlobalFieldData.{u, u} K := GlobalFieldData.function F t
    let D₀ : GlobalFieldData.{u, u} F⟮X⟯ := GlobalFieldData.function F (rationalParameter F)
    letI := adelesTopology D i
    letI := quotientTopology D i
    ∃ (W : AffineAlgebraicGroup F⟮X⟯)
      (ρ : (groupPointsFunctor F⟮X⟯).obj W.val ≅
        LinearAlgebraicGroups.WeilRestriction.extendScalars F⟮X⟯ K ⋙
          (groupPointsFunctor K).obj G.val)
      (j : MatrixRealization W),
    letI := adelesTopology D₀ j
    letI := quotientTopology D₀ j
    ∃ (below : FunctionPlace K → FunctionPlace F⟮X⟯)
      (ext : ∀ w, (below w).Completion →+* w.Completion)
      (compatible : ∀ w,
        (ext w).comp (below w).embedding = w.embedding.comp t.rationalMap.toRingHom)
      (eK : RationalPoints W ≃* RationalPoints G)
      (eA : Adeles D₀ j ∅ ≃ₜ* Adeles D i ∅)
      (eQ : AdelicQuotient D₀ j ≃ₜ AdelicQuotient D i),
      (IsSemisimple G → IsSemisimple W) ∧
      (IsAnisotropic G → IsAnisotropic W) ∧
      (∀ w, (below w).val = w.val.comap t.rationalMap.toRingHom ∧ Continuous (ext w)) ∧
      (∀ g, eK g =
        restrictionPoint ρ (tensorPointMap (R := F⟮X⟯) (L := K)
          (algebraMap F⟮X⟯ K) (by ext; simp)) g) ∧
      (∀ (g : Adeles D₀ j ∅) (w : FunctionPlace K),
        let v : Outside D₀ ∅ := ⟨.inl (below w), Finset.notMem_empty _⟩
        let z : Outside D ∅ := ⟨.inl w, Finset.notMem_empty _⟩
        letI : Field (D₀.Completion v.1) := GlobalFieldData.instFieldCompletion D₀ v.1
        letI : Field (D.Completion z.1) := GlobalFieldData.instFieldCompletion D z.1
        letI : Algebra F⟮X⟯ (D₀.Completion v.1) := completionAlgebra D₀ v.1
        letI : Algebra K (D.Completion z.1) := completionAlgebra D z.1
        eA g z = restrictionPoint ρ
          (R := D₀.Completion v.1) (L := D.Completion z.1)
          (tensorPointMap (ext w) (compatible w)) (g v)) ∧
      (∀ g : Adeles D₀ j ∅, eQ (QuotientGroup.mk g) = QuotientGroup.mk (eA g))

/-- Compactness of the full adelic right quotient of a connected semisimple
anisotropic group over a global function field. -/
def FunctionFieldCompactness : Prop :=
  ∀ {F : Type v} {K : Type u} [Field F] [Finite F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K) (G : AffineAlgebraicGroup K) (i : MatrixRealization G),
    IsSemisimple G → IsAnisotropic G →
      let D := GlobalFieldData.function F t
      @CompactSpace (AdelicQuotient D i) (quotientTopology D i)

end LinearAlgebraicGroups.Specs.FunctionFieldAnisotropicCompactness
