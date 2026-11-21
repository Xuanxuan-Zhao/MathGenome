import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Profinite.Completion

/-! The profinite completion of an abstract group, with its finite-quotient coordinates. -/

open CategoryTheory

namespace ALG02GroupTheory.Profinite

universe u v

variable {G : Type u} [Group G]

/-- The quotient by `N` as a finite discrete profinite group. -/
abbrev finiteQuotient (N : FiniteIndexNormalSubgroup G) : ProfiniteGrp.{u} :=
  Specs.ALG02GroupTheory.Profinite.finiteQuotient N

/-- The index for the trivial quotient of `G`. -/
def topIndex (G : Type u) [Group G] : FiniteIndexNormalSubgroup G :=
  FiniteIndexNormalSubgroup.ofSubgroup ⊤

theorem topQuotient_subsingleton (G : Type u) [Group G] :
    Subsingleton (finiteQuotient (topIndex G)) :=
  QuotientGroup.subsingleton_quotient_top

/-- Intersect a finite family of finite-index normal subgroups of `G`. -/
def finiteIntersection {ι : Type v} [Finite ι] (N : ι → FiniteIndexNormalSubgroup G) :
    FiniteIndexNormalSubgroup G where
  toSubgroup := ⨅ i, (N i).toSubgroup
  isNormal' := Subgroup.normal_iInf_normal fun i => (N i).isNormal'
  isFiniteIndex' := Subgroup.finiteIndex_iInf fun i => (N i).isFiniteIndex'

theorem finiteIntersection_le {ι : Type v} [Finite ι] (N : ι → FiniteIndexNormalSubgroup G)
    (i : ι) : finiteIntersection N ≤ N i :=
  iInf_le (fun j => (N j).toSubgroup) i

theorem finiteIntersection_isEmpty {ι : Type v} [IsEmpty ι] [Finite ι]
    (N : ι → FiniteIndexNormalSubgroup G) : finiteIntersection N = topIndex G := by
  apply FiniteIndexNormalSubgroup.toSubgroup_injective
  change (⨅ i, (N i).toSubgroup) = ⊤
  exact top_unique (le_iInf fun i => isEmptyElim i)

instance indexIsCofiltered (G : Type u) [Group G] : IsCofiltered (FiniteIndexNormalSubgroup G) := by
  let _ : Nonempty (FiniteIndexNormalSubgroup G) := ⟨topIndex G⟩
  infer_instance

/-- The quotient homomorphism from `G/M` to `G/N` when `M ≤ N`. -/
def transition {M N : FiniteIndexNormalSubgroup G} (h : M ≤ N) :
    (G ⧸ M.toSubgroup) →* (G ⧸ N.toSubgroup) :=
  QuotientGroup.map _ _ (MonoidHom.id _) h

@[simp]
theorem transition_mk {M N : FiniteIndexNormalSubgroup G} (h : M ≤ N) (g : G) :
    transition h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

/-- The finite quotients ordered by inclusion of the indexing subgroups. -/
abbrev quotientDiagram (G : Type u) [Group G] :
    FiniteIndexNormalSubgroup G ⥤ FiniteGrp.{u} :=
  ProfiniteGrp.ProfiniteCompletion.finiteGrpDiagram (GrpCat.of G)

/-- Mathlib's limit of the finite discrete quotients. -/
abbrev Completion (G : Type u) [Group G] : ProfiniteGrp.{u} :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)

/-- The compatible-tuple description of the completion. -/
abbrev TupleCompletion (G : Type u) [Group G] :=
  Specs.ALG02GroupTheory.Profinite.TupleCompletion G

/-- Identify the categorical limit and the paper's tuple model by their coordinates. -/
def toCompatibleTuples (G : Type u) [Group G] : Completion G ≃ₜ* TupleCompletion G where
  toFun x := ⟨x.1, fun _ _ h => x.2 h.hom⟩
  invFun x := ⟨x.1, fun _ _ f => x.2 f.le⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  continuous_toFun := continuous_induced_rng.mpr continuous_subtype_val
  continuous_invFun := continuous_induced_rng.mpr continuous_subtype_val

/-- The continuous coordinate projection from the completion to `G/N`. -/
def projection (N : FiniteIndexNormalSubgroup G) : Completion G →ₜ* finiteQuotient N := by
  let F := ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of G)
  change (ProfiniteGrp.limitCone F).pt →ₜ* F.obj N
  exact ((ProfiniteGrp.limitCone F).π.app N).hom

/-- The canonical homomorphism from the abstract group to its completion. -/
def eta (G : Type u) [Group G] : G →* Completion G :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom

@[simp]
theorem projection_eta (N : FiniteIndexNormalSubgroup G) (g : G) :
    projection N (eta G g) = QuotientGroup.mk g :=
  rfl

theorem projection_compatible {M N : FiniteIndexNormalSubgroup G} (h : M ≤ N)
    (x : Completion G) : transition h (projection M x) = projection N x :=
  x.2 h.hom

@[simp]
theorem toCompatibleTuples_apply (N : FiniteIndexNormalSubgroup G) (x : Completion G) :
    (toCompatibleTuples G x).1 N = projection N x :=
  rfl

theorem toCompatibleTuples_eta (G : Type u) [Group G] (g : G)
    (N : FiniteIndexNormalSubgroup G) :
    (toCompatibleTuples G (eta G g)).1 N = QuotientGroup.mk g :=
  rfl

end ALG02GroupTheory.Profinite
