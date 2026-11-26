import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.AdjointRepresentation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormsConjugations
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.GaloisDescent

open AlgebraicGeometry CategoryTheory
open LieAlgebrasAndRepresentations.RealForms
open scoped TensorProduct

namespace LinearAlgebraicGroups.Specs.RealF4AdjointPointComparison

open AdjointRepresentation (conjugate)
open Arithmetic.AdelicGroups (PointsIn)
open AbsoluteDynkinTypes (HasDynkinType)
open GeometricRadicals (GeometricGroup IsSemisimple)
open IntegralModels (MatrixRealization)
open Pinning (AttachedDatum SplitBorelPair)
open RootData (integralCartan)

noncomputable section

/-- The specified field extension of the given real algebraic group. -/
abbrev complexGroup (G : AffineAlgebraicGroup ℝ) : AffineAlgebraicGroup ℂ :=
  Unipotent.baseChangedAlgebraicGroup ℂ G

/-- The subgroup of complex Lie automorphisms descending to the real Lie algebra. -/
def fixedAutomorphisms {L : Type} [LieRing L] [LieAlgebra ℂ L] (σ : Conjugation L) :
    Subgroup (L ≃ₗ⁅ℂ⁆ L) where
  carrier := {a | Intertwines σ σ a}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb x
    change σ.map (a (b x)) = a (b (σ.map x))
    rw [ha, hb]
  inv_mem' := by
    intro a ha x
    change σ.map (a.symm x) = a.symm (σ.map x)
    change Intertwines σ σ a at ha
    apply a.injective
    change a (σ.map (a.symm x)) = a (a.symm (σ.map x))
    rw [a.apply_symm_apply, ← ha (a.symm x), a.apply_symm_apply]

/-- Topology of the complex automorphism group in its finite-dimensional matrix
coordinates. The subgroup topology below is induced by its inclusion. -/
@[instance_reducible] def coordinateTopology {L : Type} [LieRing L] [LieAlgebra ℂ L] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ L) : TopologicalSpace (L ≃ₗ⁅ℂ⁆ L) :=
  TopologicalSpace.induced
    (fun a => fun r d : Fin n => b.repr (a (b d)) r) inferInstance

/-- The complex identity tangent with its actual Lie structure and its canonical
identification with the scalar extension of the real identity tangent. -/
def ComplexTangentData (G : AffineAlgebraicGroup ℝ) (s : IdentityLieStructure G.val)
    (sC : IdentityLieStructure (complexGroup G).val) : Prop :=
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := sC.lieRing
  letI := sC.lieAlgebra
  ∃ e : (ℂ ⊗[ℝ] Lie ℝ G.val) ≃ₗ⁅ℂ⁆ Lie ℂ (complexGroup G).val,
    ∀ p : Lie ℝ G.val,
      baseChangePoint ℝ ℂ G.val.X (CommAlgCat.of ℂ (DualNumber ℂ))
          (e (1 ⊗ₜ[ℝ] p)).toMul.val =
        mapPoints (extendDualNumber ℂ) p.toMul.val

/-- The two comparisons for the original real group and its actual complex
base change. The complex equivalence is induced by conjugation on identity
tangents. Its restriction along coefficient extension gives the real comparison. -/
def AdjointPointComparison : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G), IsSemisimple G →
    ∀ (P : SplitBorelPair (AlgebraicClosure ℝ)) (_ : P.G = GeometricGroup G)
      (D : AttachedDatum P),
      (letI := D.comm
       HasDynkinType (integralCartan D.datum.rootDatum D.base) .F4) →
      let GC := complexGroup G
      IsSemisimple GC ∧
      (∃ (PC : SplitBorelPair ℂ) (_ : PC.G = GC) (DC : AttachedDatum PC),
        letI := DC.comm
        HasDynkinType (integralCartan DC.datum.rootDatum DC.base) .F4) ∧
      ∃ (j : MatrixRealization GC) (s : IdentityLieStructure G.val)
        (sC : IdentityLieStructure GC.val),
        let L := Lie ℂ GC.val
        letI := s.lieRing
        letI := s.lieAlgebra
        letI := sC.lieRing
        letI := sC.lieAlgebra
        FiniteDimensional ℂ L ∧
        _root_.Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ L ∧
        ∃ (e : (ℂ ⊗[ℝ] Lie ℝ G.val) ≃ₗ⁅ℂ⁆ L) (σ : Conjugation L)
          (n : ℕ) (b : Module.Basis (Fin n) ℂ L),
          (∀ p : Lie ℝ G.val,
            baseChangePoint ℝ ℂ G.val.X (CommAlgCat.of ℂ (DualNumber ℂ))
                (e (1 ⊗ₜ[ℝ] p)).toMul.val =
              mapPoints (extendDualNumber ℂ) p.toMul.val) ∧
          (∀ z, σ.map (e z) = e (coefficientConjugationMap (Lie ℝ G.val) z)) ∧
          letI := coordinateTopology b
          ∃ (aC : PointsIn j ℂ ≃* (L ≃ₗ⁅ℂ⁆ L))
            (aR : PointsIn i ℝ ≃ₜ fixedAutomorphisms σ),
            Continuous aC ∧ Continuous aC.symm ∧
            (∀ (g : PointsIn j ℂ) (v : L),
              (aC g v).toMul.val = conjugate (R := CommAlgCat.of ℂ ℂ) g v) ∧
            ∀ g : PointsIn i ℝ, ∀ gC : PointsIn j ℂ,
              baseChangePoint ℝ ℂ G.val.X (CommAlgCat.of ℂ ℂ) gC =
                mapPoints (CommAlgCat.ofHom
                  (Algebra.ofId ℝ ((restrictTestAlgebra ℝ ℂ).obj (CommAlgCat.of ℂ ℂ)))) g →
              (aR g).val = aC gC

end
end LinearAlgebraicGroups.Specs.RealF4AdjointPointComparison
