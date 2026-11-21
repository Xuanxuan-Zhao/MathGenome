import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.CategoryTheory.Filtered.Basic

/-! The finite-quotient system and tuple model of GR02-C05.01. -/

open CategoryTheory

namespace Specs.ALG02GroupTheory.Profinite

universe u v

variable {G : Type u} [Group G]

/-- A coordinate group `G ⧸ N.toSubgroup`, endowed with the discrete topology. -/
abbrev finiteQuotient (N : FiniteIndexNormalSubgroup G) : ProfiniteGrp.{u} :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (G ⧸ N.toSubgroup))

def FiniteQuotientType :=
  ∀ {G : Type u} [Group G], FiniteIndexNormalSubgroup G → ProfiniteGrp.{u}

def TopIndexType := ∀ (G : Type u) [Group G], FiniteIndexNormalSubgroup G

def topIndexValue : TopIndexType :=
  fun _ [_] => FiniteIndexNormalSubgroup.ofSubgroup ⊤

set_option linter.checkUnivs false in
def FiniteIntersectionType : Type (max u v + 1) :=
  ∀ {G : Type u} [Group G] {ι : Type v} [Finite ι],
    (ι → FiniteIndexNormalSubgroup G) → FiniteIndexNormalSubgroup G

def finiteIntersectionValue : FiniteIntersectionType.{u, v} :=
  fun {_} [_] {_} [_] N =>
    { toSubgroup := ⨅ i, (N i).toSubgroup
      isNormal' := Subgroup.normal_iInf_normal fun i => (N i).isNormal'
      isFiniteIndex' := Subgroup.finiteIndex_iInf fun i => (N i).isFiniteIndex' }

def FiniteIntersectionLe : Prop :=
  ∀ {G : Type u} [Group G] {ι : Type v} [Finite ι]
    (N : ι → FiniteIndexNormalSubgroup G) (i : ι), finiteIntersectionValue N ≤ N i

def FiniteIntersectionIsEmpty : Prop :=
  ∀ {G : Type u} [Group G] {ι : Type v} [IsEmpty ι] [Finite ι]
    (N : ι → FiniteIndexNormalSubgroup G), finiteIntersectionValue N = topIndexValue G

def TopQuotientSubsingleton : Prop :=
  ∀ (G : Type u) [Group G], Subsingleton (finiteQuotient (topIndexValue G))

def Cofiltered : Prop :=
  ∀ (G : Type u) [Group G], IsCofiltered (FiniteIndexNormalSubgroup G)

def TransitionType :=
  ∀ {G : Type u} [Group G] {M N : FiniteIndexNormalSubgroup G}, M ≤ N →
    (G ⧸ M.toSubgroup) →* (G ⧸ N.toSubgroup)

/-- The quotient map for an inclusion of the subgroups. -/
def transitionValue : TransitionType :=
  fun {_} [_] {_ _} h => QuotientGroup.map _ _ (MonoidHom.id _) h

def TransitionMk : Prop :=
  ∀ {G : Type u} [Group G] {M N : FiniteIndexNormalSubgroup G} (h : M ≤ N) (g : G),
    transitionValue h (QuotientGroup.mk g) = QuotientGroup.mk g

def QuotientDiagramType :=
  ∀ (G : Type u) [Group G], FiniteIndexNormalSubgroup G ⥤ FiniteGrp.{u}

def quotientDiagramValue : QuotientDiagramType.{u} :=
  fun G [_] =>
    { obj := fun N => FiniteGrp.of (G ⧸ N.toSubgroup)
      map := fun f => FiniteGrp.ofHom (transitionValue f.le)
      map_id := by
        intro N
        ext ⟨g⟩
        rfl
      map_comp := by
        intro M N L f g
        ext ⟨x⟩
        rfl }

variable (G)

/-- The subgroup of the entire product cut out by the quotient compatibilities. -/
def compatibleTuples : Subgroup (∀ N : FiniteIndexNormalSubgroup G, finiteQuotient N) where
  carrier := { x | ∀ ⦃M N : FiniteIndexNormalSubgroup G⦄ (h : M ≤ N),
    transitionValue h (x M) = x N }
  one_mem' := by
    intro M N h
    exact map_one (transitionValue h)
  mul_mem' := by
    intro x y hx hy M N h
    exact (map_mul (transitionValue h) (x M) (y M)).trans
      (congrArg₂ (· * ·) (hx h) (hy h))
  inv_mem' := by
    intro x hx M N h
    exact (map_inv (transitionValue h) (x M)).trans (congrArg Inv.inv (hx h))

/-- The subgroup inherits coordinatewise group operations and the product subspace topology. -/
abbrev TupleCompletion := ↥(compatibleTuples G)

def TupleCompletionType := ∀ (G : Type u) [Group G], Type u

def CompletionType := ∀ (G : Type u) [Group G], ProfiniteGrp.{u}

def completionValue : CompletionType :=
  fun G [_] => ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)

def TupleEquivType :=
  ∀ (G : Type u) [Group G], completionValue G ≃ₜ* TupleCompletion G

/-- The same coordinates satisfy both the order and the categorical compatibility equations. -/
def tupleEquivValue : TupleEquivType.{u} :=
  fun _ [_] =>
    { toFun := fun x => ⟨x.1, fun _ _ h => x.2 h.hom⟩
      invFun := fun x => ⟨x.1, fun _ _ f => x.2 f.le⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      continuous_toFun := continuous_induced_rng.mpr continuous_subtype_val
      continuous_invFun := continuous_induced_rng.mpr continuous_subtype_val }

def ProjectionType :=
  ∀ {G : Type u} [Group G] (N : FiniteIndexNormalSubgroup G),
    completionValue G →ₜ* finiteQuotient N

/-- Coordinate evaluation on the compatible tuples. -/
def projectionValue : ProjectionType :=
  fun {_} [_] N =>
    { toFun := fun x => x.1 N
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun := (continuous_apply N).comp continuous_subtype_val }

def EtaType := ∀ (G : Type u) [Group G], G →* completionValue G

/-- The tuple made up of all cosets of a given element. -/
def etaValue : EtaType :=
  fun _ [_] =>
    { toFun := fun g => ⟨fun _ => QuotientGroup.mk g, fun _ _ _ => rfl⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

def TupleEquivProjection : Prop :=
  ∀ {G : Type u} [Group G] (N : FiniteIndexNormalSubgroup G) (x : completionValue G),
    (tupleEquivValue G x).1 N = projectionValue N x

def TupleEquivEta : Prop :=
  ∀ (G : Type u) [Group G] (g : G) (N : FiniteIndexNormalSubgroup G),
    (tupleEquivValue G (etaValue G g)).1 N = QuotientGroup.mk g

def ProjectionEta : Prop :=
  ∀ {G : Type u} [Group G] (N : FiniteIndexNormalSubgroup G) (g : G),
    projectionValue N (etaValue G g) = QuotientGroup.mk g

def ProjectionCompatible : Prop :=
  ∀ {G : Type u} [Group G] {M N : FiniteIndexNormalSubgroup G} (h : M ≤ N)
    (x : completionValue G), transitionValue h (projectionValue M x) = projectionValue N x

end Specs.ALG02GroupTheory.Profinite
