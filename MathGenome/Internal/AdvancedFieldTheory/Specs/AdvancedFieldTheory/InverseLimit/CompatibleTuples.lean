import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.RestrictionSystem
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
Independent specification of FT-T04, notes/003/advanced-field-theory.tex:474–507.
The index consists of all literal finite Galois intermediate fields. The groups
are the actual automorphism groups, given the discrete topology. The limit is
the subgroup of the dependent product cut out by every restriction equation.
The constructions make sense for any ambient extension, in particular for the
Galois extensions in the source. No categorical limit is used.
-/

universe u v w
noncomputable section
set_option linter.checkUnivs false
namespace Specs.AdvancedFieldTheory

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

def finiteGaloisStage_type :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], Type v

abbrev finiteGaloisStage_value : finiteGaloisStage_type.{u, v} :=
  fun K L [Field K] [Field L] [Algebra K L] =>
    {E : IntermediateField K L // FiniteDimensional K E ∧ IsGalois K E}

instance stageFiniteDimensional (E : finiteGaloisStage_value K L) :
    FiniteDimensional K E.val := E.property.1
instance stageIsGalois (E : finiteGaloisStage_value K L) : IsGalois K E.val :=
  E.property.2

def finiteStageGroup_type :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
    finiteGaloisStage_value K L → Type v

/-- A type synonym keeps the discrete stage topology local to finite stages. -/
def finiteStageGroup_value : finiteStageGroup_type.{u, v} :=
  fun {K} {L} [Field K] [Field L] [Algebra K L] E => E.val ≃ₐ[K] E.val

instance stageGroupStructure (E : finiteGaloisStage_value K L) :
    Group (finiteStageGroup_value E) := inferInstanceAs (Group (E.val ≃ₐ[K] E.val))
instance stageGroupFinite (E : finiteGaloisStage_value K L) :
    Finite (finiteStageGroup_value E) := inferInstanceAs (Finite (E.val ≃ₐ[K] E.val))
instance stageGroupTopology (E : finiteGaloisStage_value K L) :
    TopologicalSpace (finiteStageGroup_value E) := ⊥
instance stageGroupDiscrete (E : finiteGaloisStage_value K L) :
    DiscreteTopology (finiteStageGroup_value E) := ⟨rfl⟩
instance stageGroupTopological (E : finiteGaloisStage_value K L) :
    IsTopologicalGroup (finiteStageGroup_value E) := inferInstance

def finiteStageTransition_type :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {E F : finiteGaloisStage_value K L}, E ≤ F →
    ContinuousMonoidHom (finiteStageGroup_value F) (finiteStageGroup_value E)

def finiteStageTransition_value : finiteStageTransition_type.{u, v} :=
  fun {K} {L} [Field K] [Field L] [Algebra K L] {E F} h =>
  { stageRestriction_value (show E.val ≤ F.val from h) with
    continuous_toFun := continuous_of_discreteTopology }

def compatibleTuplesSubgroup_type :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Subgroup (∀ E : finiteGaloisStage_value K L, finiteStageGroup_value E)

def compatibleTuplesSubgroup_value : compatibleTuplesSubgroup_type.{u, v} := fun K L _ _ _ =>
  { carrier := {σ | ∀ (E F : finiteGaloisStage_value K L) (h : E ≤ F),
        finiteStageTransition_value h (σ F) = σ E}
    one_mem' := fun E F h => map_one (finiteStageTransition_value h)
    mul_mem' := by
      intro σ τ hσ hτ E F h
      exact (map_mul (finiteStageTransition_value h) (σ F) (τ F)).trans
        (congrArg₂ (· * ·) (hσ E F h) (hτ E F h))
    inv_mem' := by
      intro σ hσ E F h
      exact (map_inv (finiteStageTransition_value h) (σ F)).trans
        (congrArg Inv.inv (hσ E F h)) }

def compatibleTuples_type :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], Type v

abbrev compatibleTuples_value : compatibleTuples_type.{u, v} := fun K L _ _ _ =>
  ↥(compatibleTuplesSubgroup_value K L)

def compatibleTupleProjection_type :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (E : finiteGaloisStage_value K L),
    ContinuousMonoidHom (compatibleTuples_value K L) (finiteStageGroup_value E)

def compatibleTupleProjection_value : compatibleTupleProjection_type.{u, v} :=
  fun {K} {L} [Field K] [Field L] [Algebra K L] E =>
  { toFun := fun σ => σ.val E
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    continuous_toFun := (continuous_apply E).comp continuous_subtype_val }

def compatibleTupleLift_type :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {X : Type w} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    (f : ∀ E : finiteGaloisStage_value K L, ContinuousMonoidHom X (finiteStageGroup_value E)),
    (∀ (E F : finiteGaloisStage_value K L) (h : E ≤ F),
      (finiteStageTransition_value h).comp (f F) = f E) →
    ContinuousMonoidHom X (compatibleTuples_value K L)

def compatibleTupleLift_value : compatibleTupleLift_type.{u, v, w} :=
  fun {K} {L} [Field K] [Field L] [Algebra K L]
    {X} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] f hf =>
  { toFun := fun x => ⟨fun E => f E x, fun E F h =>
        DFunLike.congr_fun (hf E F h) x⟩
    map_one' := Subtype.ext (funext (fun E => map_one (f E)))
    map_mul' := fun x y => Subtype.ext (funext (fun E => map_mul (f E) x y))
    continuous_toFun :=
      (continuous_pi (fun E => (f E).continuous)).subtype_mk _ }

/-- The finite-stage index retains the source's nonempty directed ordering. -/
def finiteStageIndex_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L],
    Nonempty (finiteGaloisStage_value K L) ∧
    ∀ E F : finiteGaloisStage_value K L, ∃ H, E ≤ H ∧ F ≤ H

/-- The onto transition homomorphisms satisfy the inverse-system identities. -/
def finiteStageTransition_laws_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
    (∀ {E F : finiteGaloisStage_value K L} (h : E ≤ F),
      Function.Surjective (finiteStageTransition_value h)) ∧
    (∀ (E : finiteGaloisStage_value K L) (σ : finiteStageGroup_value E),
      finiteStageTransition_value (le_refl E) σ = σ) ∧
    (∀ {E F H : finiteGaloisStage_value K L} (hEF : E ≤ F) (hFH : F ≤ H)
      (σ : finiteStageGroup_value H),
      finiteStageTransition_value (hEF.trans hFH) σ =
        finiteStageTransition_value hEF (finiteStageTransition_value hFH σ))

def mem_compatibleTuplesSubgroup_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (σ : ∀ E : finiteGaloisStage_value K L, finiteStageGroup_value E),
    σ ∈ compatibleTuplesSubgroup_value K L ↔
      ∀ (E F : finiteGaloisStage_value K L) (h : E ≤ F),
        finiteStageTransition_value h (σ F) = σ E

/-- Projection really is evaluation of the underlying tuple. -/
def compatibleTupleProjection_apply_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (E : finiteGaloisStage_value K L) (σ : compatibleTuples_value K L),
    compatibleTupleProjection_value E σ = σ.val E

def compatibleTupleProjection_compatible_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {E F : finiteGaloisStage_value K L} (h : E ≤ F),
    (finiteStageTransition_value h).comp (compatibleTupleProjection_value F) =
      compatibleTupleProjection_value E

/-- The topology is exactly the topology induced from the product, not a completion. -/
def compatibleTuples_topology_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
    (inferInstance : TopologicalSpace (compatibleTuples_value K L)) =
      TopologicalSpace.induced
        (fun σ : compatibleTuples_value K L => σ.val)
        (inferInstance : TopologicalSpace
          (∀ E : finiteGaloisStage_value K L, finiteStageGroup_value E))

def compatibleTuples_topologicalGroup_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
    IsTopologicalGroup (compatibleTuples_value K L)

def compatibleTupleLift_projection_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {X : Type w} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    (f : ∀ E : finiteGaloisStage_value K L, ContinuousMonoidHom X (finiteStageGroup_value E))
    (hf : ∀ (E F : finiteGaloisStage_value K L) (h : E ≤ F),
      (finiteStageTransition_value h).comp (f F) = f E)
    (E : finiteGaloisStage_value K L),
    (compatibleTupleProjection_value E).comp (compatibleTupleLift_value f hf) = f E

/-- The full universal property in topological groups, with no separation restriction on X. -/
def compatibleTuples_universal_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {X : Type w} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    (f : ∀ E : finiteGaloisStage_value K L, ContinuousMonoidHom X (finiteStageGroup_value E)),
    (∀ (E F : finiteGaloisStage_value K L) (h : E ≤ F),
      (finiteStageTransition_value h).comp (f F) = f E) →
    ∃! g : ContinuousMonoidHom X (compatibleTuples_value K L),
      ∀ E, (compatibleTupleProjection_value E).comp g = f E

end Specs.AdvancedFieldTheory
