import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteGaloisStages.DirectedUnion
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.RestrictionSystem
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.InverseLimit.CompatibleTuples

/-!
# The compatible-tuple inverse limit (FT-T04)

All stages are literal finite Galois intermediate fields of the specified L/K.
The canonical definitions in the independent Specs equip their automorphism
groups with discrete topologies. The subgroup inherits coordinatewise group
operations and the subspace topology of the dependent product. Its continuous
projections and the unique componentwise lift give the inverse limit in
(topological, not necessarily Hausdorff) groups.
-/

universe u v w
noncomputable section
namespace AdvancedFieldTheory

/-- The inclusion-ordered set of all finite Galois intermediate fields. -/
abbrev finiteGaloisStage : Specs.AdvancedFieldTheory.finiteGaloisStage_type.{u, v} :=
  Specs.AdvancedFieldTheory.finiteGaloisStage_value

/-- Gal(E/K), with its discrete topology. This is a synonym of the actual automorphism group. -/
abbrev finiteStageGroup : Specs.AdvancedFieldTheory.finiteStageGroup_type.{u, v} :=
  Specs.AdvancedFieldTheory.finiteStageGroup_value

/-- The continuous restriction homomorphism from a larger finite stage to a smaller one. -/
abbrev finiteStageTransition : Specs.AdvancedFieldTheory.finiteStageTransition_type.{u, v} :=
  Specs.AdvancedFieldTheory.finiteStageTransition_value

/-- The subgroup of tuples satisfying every restriction compatibility equation. -/
abbrev compatibleTuplesSubgroup : Specs.AdvancedFieldTheory.compatibleTuplesSubgroup_type.{u, v} :=
  Specs.AdvancedFieldTheory.compatibleTuplesSubgroup_value

/-- The compatible tuples, with coordinatewise operations and the product subspace topology. -/
abbrev compatibleTuples : Specs.AdvancedFieldTheory.compatibleTuples_type.{u, v} :=
  Specs.AdvancedFieldTheory.compatibleTuples_value

/-- Continuous evaluation at one finite stage. -/
abbrev compatibleTupleProjection : Specs.AdvancedFieldTheory.compatibleTupleProjection_type.{u, v} :=
  Specs.AdvancedFieldTheory.compatibleTupleProjection_value

/-- Componentwise pairing of a compatible family of continuous homomorphisms. -/
abbrev compatibleTupleLift : Specs.AdvancedFieldTheory.compatibleTupleLift_type.{u, v, w} :=
  Specs.AdvancedFieldTheory.compatibleTupleLift_value

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The source's indexing set is nonempty and directed by inclusion. -/
theorem finiteStageIndex (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Nonempty (finiteGaloisStage K L) ∧
      ∀ E F : finiteGaloisStage K L, ∃ H, E ≤ H ∧ F ≤ H := by
  refine ⟨⟨⟨⊥, finite_galois_bot K L⟩⟩, ?_⟩
  intro E F
  exact ⟨⟨E.val ⊔ F.val,
    finite_galois_compositum K L E.val F.val E.property F.property⟩,
    (show E.val ≤ E.val ⊔ F.val from le_sup_left),
    (show F.val ≤ E.val ⊔ F.val from le_sup_right)⟩

/-- These are onto restrictions, with the identity and composition laws of an inverse system. -/
theorem finiteStageTransition_laws :
    (∀ {E F : finiteGaloisStage K L} (h : E ≤ F),
      Function.Surjective (finiteStageTransition h)) ∧
    (∀ (E : finiteGaloisStage K L) (σ : finiteStageGroup E),
      finiteStageTransition (le_refl E) σ = σ) ∧
    (∀ {E F H : finiteGaloisStage K L} (hEF : E ≤ F) (hFH : F ≤ H)
      (σ : finiteStageGroup H),
      finiteStageTransition (hEF.trans hFH) σ =
        finiteStageTransition hEF (finiteStageTransition hFH σ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro E F h
    exact stageRestriction_surjective (show E.val ≤ F.val from h)
  · intro E σ
    exact DFunLike.congr_fun (stageRestriction_self E.val) σ
  · intro E F H hEF hFH σ
    exact DFunLike.congr_fun
      (stageRestriction_comp (show E.val ≤ F.val from hEF)
        (show F.val ≤ H.val from hFH)) σ

@[simp] theorem mem_compatibleTuplesSubgroup
    (σ : ∀ E : finiteGaloisStage K L, finiteStageGroup E) :
    σ ∈ compatibleTuplesSubgroup K L ↔
      ∀ (E F : finiteGaloisStage K L) (h : E ≤ F),
        finiteStageTransition h (σ F) = σ E := Iff.rfl

@[simp] theorem compatibleTupleProjection_apply
    (E : finiteGaloisStage K L) (σ : compatibleTuples K L) :
    compatibleTupleProjection E σ = σ.val E := rfl

/-- The projections form a cone over the restriction system. -/
theorem compatibleTupleProjection_compatible {E F : finiteGaloisStage K L} (h : E ≤ F) :
    (finiteStageTransition h).comp (compatibleTupleProjection F) =
      compatibleTupleProjection E := by
  apply ContinuousMonoidHom.ext
  intro σ
  exact σ.property E F h

/-- The topology is the literal subspace topology from the product of discrete groups. -/
theorem compatibleTuples_topology :
    (inferInstance : TopologicalSpace (compatibleTuples K L)) =
      TopologicalSpace.induced (fun σ : compatibleTuples K L => σ.val)
        (inferInstance : TopologicalSpace
          (∀ E : finiteGaloisStage K L, finiteStageGroup E)) := rfl

theorem compatibleTuples_topologicalGroup : IsTopologicalGroup (compatibleTuples K L) :=
  inferInstance

@[simp] theorem compatibleTupleLift_projection
    {X : Type w} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    (f : ∀ E : finiteGaloisStage K L, ContinuousMonoidHom X (finiteStageGroup E))
    (hf : ∀ (E F : finiteGaloisStage K L) (h : E ≤ F),
      (finiteStageTransition h).comp (f F) = f E)
    (E : finiteGaloisStage K L) :
    (compatibleTupleProjection E).comp (compatibleTupleLift f hf) = f E := by
  apply ContinuousMonoidHom.ext
  intro x
  rfl

/-- The universal property characterizing the inverse limit in topological groups. -/
theorem compatibleTuples_universal
    {X : Type w} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    (f : ∀ E : finiteGaloisStage K L, ContinuousMonoidHom X (finiteStageGroup E))
    (hf : ∀ (E F : finiteGaloisStage K L) (h : E ≤ F),
      (finiteStageTransition h).comp (f F) = f E) :
    ∃! g : ContinuousMonoidHom X (compatibleTuples K L),
      ∀ E, (compatibleTupleProjection E).comp g = f E := by
  refine ⟨compatibleTupleLift f hf, compatibleTupleLift_projection f hf, ?_⟩
  intro g hg
  apply ContinuousMonoidHom.ext
  intro x
  apply Subtype.ext
  funext E
  exact DFunLike.congr_fun (hg E) x

end AdvancedFieldTheory
