import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.Triality

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Albert.FrameTangentSpecification

open _root_.Specs.LinearAlgebraicGroups.Albert
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open TrialitySpecification (Model modelOp modelBaseChange mapModel)
open FrameSpecification (frameAxis)
open CubicSpecification (cubicUnit)

variable {k : Type u} [Field k]

/-- Quadratic derivations annihilating each axis of the ordered diagonal frame. -/
def frameDerivations (J : QuadraticJordan k (Model k)) : Submodule k (Module.End k (Model k)) where
  carrier := {D | IsQuadraticDerivation J D ∧ ∀ i : Fin 3, D (frameAxis i) = 0}
  zero_mem' := by
    simp [IsQuadraticDerivation, QuadraticJordan.polar]
  add_mem' := by
    rintro D E ⟨hD, hDf⟩ ⟨hE, hEf⟩
    refine ⟨⟨by simp [hD.1, hE.1], ?_⟩, fun i => by simp [hDf i, hEf i]⟩
    intro S _ _ x y
    simp only [LinearMap.baseChange_add, LinearMap.add_apply, hD.2 S x y, hE.2 S x y,
      map_add]
    abel
  smul_mem' := by
    rintro c D ⟨hD, hDf⟩
    refine ⟨⟨by simp [hD.1], ?_⟩, fun i => by simp [hDf i]⟩
    intro S _ _ x y
    simp only [LinearMap.baseChange_smul, LinearMap.smul_apply, hD.2 S x y,
      LinearMap.map_smul_of_tower, smul_add]

def FrameDerivationsType :=
  ∀ {k : Type u} [Field k], QuadraticJordan k (Model k) → Submodule k (Module.End k (Model k))

/-- The affine group representing the ordered-frame stabilizer over a field,
with its action in the split coordinates over every scalar algebra. -/
structure FrameRepresentation (k : Type u) [Field k] where
  group : LinearAlgebraicGroups.Specs.GroupScheme k
  affine : IsAffine group.X.left
  points : ∀ S : CommAlgCat k,
    ((groupPointsFunctor k).obj group).obj S ≃* TrialitySpecification.frameStabilizer (R := S)
  natural : ∀ {S T : CommAlgCat k} (f : S ⟶ T)
    (p : ((groupPointsFunctor k).obj group).obj S) (x : Model S),
    mapModel f.hom.toRingHom ((points S p).val x) =
      (points T (((groupPointsFunctor k).obj group).map f p)).val (mapModel f.hom.toRingHom x)

/-- The differential is the actual dual-number point of the represented
stabilizer, and its vector space of frame-fixing derivations has rank 28. -/
def FrameTangentRank : Prop :=
  ∀ (k : Type u) [Field k] (J : QuadraticJordan k (Model k)),
    J.unit = cubicUnit → (∀ x y, J.groundOp x y = modelOp x y) →
    ∃ (G : FrameRepresentation k) (m : LinearAlgebraicGroups.Specs.LieVectorStructure G.group),
      letI := m.addGroup
      letI := m.module
      ∃ e : frameDerivations J ≃ₗ[k] LinearAlgebraicGroups.Specs.Lie k G.group,
        (∀ D x, (G.points (CommAlgCat.of k (DualNumber k)) (e D).toMul.val).val
            (modelBaseChange k (DualNumber k) x) =
          modelBaseChange k (DualNumber k) (infinitesimal D.val x)) ∧
        Module.finrank k (frameDerivations J) = 28

end LinearAlgebraicGroups.Albert.FrameTangentSpecification
