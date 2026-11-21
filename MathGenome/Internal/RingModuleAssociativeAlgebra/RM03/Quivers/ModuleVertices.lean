import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.PathAlgebra
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.Representations
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.ModuleVertices

/-! The forward functor from path algebra modules to quiver representations. -/

open CategoryTheory
open scoped BigOperators Classical DirectSum ModuleCat

namespace RM03.ModuleVertices

open ModuleVerticesSpec
  (vertexProjection vertexSpace project arrowMap restrictMap representation VertexSum sumMap
    decomposeMap)

universe u v w d

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]

private theorem vertex_mul_arrow {i j : Q} (a : Quiver.Hom i j) :
    PathAlgebra.vertex k j * PathAlgebra.arrow k a = PathAlgebra.arrow k a := by
  rw [PathAlgebra.arrow_eq_ofPath, PathAlgebra.vertex_mul_ofPath]
  simp

private theorem arrow_mul_vertex {i j : Q} (a : Quiver.Hom i j) :
    PathAlgebra.arrow k a * PathAlgebra.vertex k i = PathAlgebra.arrow k a := by
  rw [PathAlgebra.arrow_eq_ofPath, PathAlgebra.ofPath_mul_vertex]
  simp

variable [Fintype Q]
variable {M N : ModuleCat.{d} (PathAlgebra k Q)}

/-- A vertex idempotent acts as the identity on its image and as zero on the other images. -/
theorem vertex_smul_coe (i j : Q) (x : vertexSpace M j) :
    PathAlgebra.vertex k i • (x : M) = if i = j then (x : M) else 0 := by
  obtain ⟨m, hm⟩ := x.property
  change PathAlgebra.vertex k j • m = (x : M) at hm
  rw [← hm, ← mul_smul]
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl, PathAlgebra.vertex_idempotent]
  · rw [ite_eq_right h, PathAlgebra.vertex_orthogonal i j h, zero_smul]

@[simp]
theorem coe_arrowMap {i j : Q} (a : Quiver.Hom i j) (x : vertexSpace M i) :
    (arrowMap M a x : M) = PathAlgebra.arrow k a • (x : M) := by
  change PathAlgebra.vertex k j • (PathAlgebra.arrow k a • (x : M)) = _
  rw [← mul_smul, vertex_mul_arrow]

@[simp]
theorem coe_restrictMap (f : M ⟶ N) (i : Q) (x : vertexSpace M i) :
    (restrictMap f i x : N) = f.hom (x : M) := by
  change PathAlgebra.vertex k i • f.hom (x : M) = f.hom (x : M)
  rw [← f.hom.map_smul, vertex_smul_coe, ite_eq_left rfl]

@[simp]
theorem representation_arrow (M : ModuleCat.{d} (PathAlgebra k Q)) {i j : Q}
    (a : Quiver.Hom i j) : QuiverRepresentation.arrow (representation M) a = arrowMap M a :=
  QuiverRepresentation.arrow_ofArrows _ _ a

/-- The restrictions of a module map to the vertex images form a representation morphism. -/
noncomputable def map (f : M ⟶ N) : representation M ⟶ representation N :=
  QuiverRepresentation.homMk (restrictMap f) (by
    intro i j a
    change (restrictMap f j).comp (QuiverRepresentation.arrow (representation M) a) =
      (QuiverRepresentation.arrow (representation N) a).comp (restrictMap f i)
    rw [representation_arrow, representation_arrow]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change vertexSpace M i at x
    change (restrictMap f j (arrowMap M a x) : N) =
      (arrowMap N a (restrictMap f i x) : N)
    rw [coe_restrictMap, coe_arrowMap, coe_arrowMap, coe_restrictMap, f.hom.map_smul])

@[simp]
theorem component_map (f : M ⟶ N) (i : Q) :
    QuiverRepresentation.component (map f) i = restrictMap f i :=
  rfl

/-- Send a unital left module to its vertex spaces and arrow actions. -/
noncomputable def functor (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Fintype Q] :
    ModuleCat.{d} (PathAlgebra k Q) ⥤ QuiverRepresentation.{u, v, w, d} k Q where
  obj := representation
  map := map
  map_id M := by
    apply QuiverRepresentation.hom_ext
    intro i
    rw [component_map, QuiverRepresentation.component_id]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [coe_restrictMap]
    rfl
  map_comp {X Y Z} f g := by
    apply QuiverRepresentation.hom_ext
    intro i
    rw [component_map, QuiverRepresentation.component_comp, component_map, component_map]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (restrictMap (f ≫ g) i x : Z) = (restrictMap g i (restrictMap f i x) : Z)
    rw [coe_restrictMap, coe_restrictMap, coe_restrictMap]
    rfl

instance functorAdditive : (functor.{u, v, w, d} k Q).Additive where
  map_add {X Y} {f g} := by
    apply QuiverRepresentation.hom_ext
    intro i
    change QuiverRepresentation.component (map (f + g)) i =
      QuiverRepresentation.component (map f + map g) i
    rw [QuiverRepresentation.component_add, component_map, component_map, component_map]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (restrictMap (f + g) i x : Y) =
      (restrictMap f i x : Y) + (restrictMap g i x : Y)
    rw [coe_restrictMap, coe_restrictMap, coe_restrictMap]
    rfl

instance functorLinear : (functor.{u, v, w, d} k Q).Linear k where
  map_smul {X Y} f c := by
    apply QuiverRepresentation.hom_ext
    intro i
    change QuiverRepresentation.component (map (c • f)) i =
      QuiverRepresentation.component (c • map f) i
    rw [QuiverRepresentation.component_smul, component_map, component_map]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (restrictMap (c • f) i x : Y) = c • (restrictMap f i x : Y)
    rw [coe_restrictMap, coe_restrictMap]
    rfl

@[simp]
theorem sumMap_lof (i : Q) (x : vertexSpace M i) :
    sumMap M (DirectSum.lof k Q (fun j => ↥(vertexSpace M j)) i x) = (x : M) :=
  DirectSum.coeLinearMap_lof _ _ _

theorem sumMap_apply (x : VertexSum M) : sumMap M x = ∑ i : Q, (x i : M) := by
  calc
    sumMap M x = sumMap M (∑ i : Q, DirectSum.lof k Q (fun j => ↥(vertexSpace M j)) i (x i)) :=
      congrArg (sumMap M) (DirectSum.sum_univ_of x).symm
    _ = ∑ i : Q, (x i : M) := by simp only [map_sum, sumMap_lof]

@[simp]
theorem decomposeMap_apply (m : M) (i : Q) :
    decomposeMap M m i = project M i m := by
  let coordinates := DirectSum.linearEquivFunOnFintype k Q (fun j => ↥(vertexSpace M j))
  exact congrFun (coordinates.apply_symm_apply (fun j => project M j m)) i

@[simp]
theorem project_sumMap (x : VertexSum M) (i : Q) :
    project M i (sumMap M x) = x i := by
  apply Subtype.ext
  change PathAlgebra.vertex k i • sumMap M x = (x i : M)
  rw [sumMap_apply, Finset.smul_sum]
  simp [vertex_smul_coe]

/-- The canonical sum isomorphism with inverse given by the vertex projections. -/
noncomputable def sumEquiv (M : ModuleCat.{d} (PathAlgebra k Q)) : VertexSum M ≃ₗ[k] M :=
  { sumMap M with
    invFun := decomposeMap M
    left_inv := fun x => DFinsupp.ext fun i => by
      change decomposeMap M (sumMap M x) i = x i
      rw [decomposeMap_apply, project_sumMap]
    right_inv := fun m => by
      change sumMap M (decomposeMap M m) = m
      rw [sumMap_apply]
      simp only [decomposeMap_apply]
      change (∑ i : Q, PathAlgebra.vertex k i • m) = m
      rw [← Finset.sum_smul, PathAlgebra.sum_vertices, one_smul] }

@[simp]
theorem sumEquiv_symm_apply (m : M) (i : Q) :
    ((sumEquiv M).symm m i : M) = PathAlgebra.vertex k i • m := by
  change (decomposeMap M m i : M) = _
  rw [decomposeMap_apply]
  rfl

@[simp]
theorem sumEquiv_lof (i : Q) (x : vertexSpace M i) :
    sumEquiv M (DirectSum.lof k Q (fun j => ↥(vertexSpace M j)) i x) = (x : M) :=
  sumMap_lof i x

theorem sumEquiv_natural (f : M ⟶ N) (x : VertexSum M) :
    sumEquiv N (DirectSum.lmap (restrictMap f) x) = f.hom (sumEquiv M x) := by
  change sumMap N (DirectSum.lmap (restrictMap f) x) = f.hom (sumMap M x)
  rw [sumMap_apply, sumMap_apply, map_sum]
  simp only [DirectSum.lmap_apply, coe_restrictMap]

theorem sumEquiv_vertex (i : Q) (x : VertexSum M) :
    sumEquiv M (DirectSum.lof k Q (fun j => ↥(vertexSpace M j)) i (x i)) =
      PathAlgebra.vertex k i • sumEquiv M x := by
  rw [sumEquiv_lof]
  exact (congrArg Subtype.val (project_sumMap x i)).symm

theorem sumEquiv_arrow {i j : Q} (a : Quiver.Hom i j) (x : VertexSum M) :
    sumEquiv M (DirectSum.lof k Q (fun l => ↥(vertexSpace M l)) j
      (QuiverRepresentation.arrow (representation M) a (x i))) =
      PathAlgebra.arrow k a • sumEquiv M x := by
  have h : QuiverRepresentation.arrow (representation M) a (x i) = arrowMap M a (x i) :=
    DFunLike.congr_fun (representation_arrow M a) (x i)
  rw [h, sumEquiv_lof, coe_arrowMap]
  have hx : (x i : M) = PathAlgebra.vertex k i • sumEquiv M x :=
    (congrArg Subtype.val (project_sumMap x i)).symm
  rw [hx, ← mul_smul, arrow_mul_vertex]

/-- The functor and sum isomorphism use the specified path algebra and the indicated formulas. -/
theorem construction : ModuleVerticesSpec.Construction.{u, v, w, d} := by
  intro k Q _ _ _
  refine ⟨inferInstance, rfl, rfl, rfl, inferInstance, rfl, fun _ => rfl, ?_⟩
  refine ⟨⟨?_, fun f i x => coe_restrictMap f i x⟩,
    functor k Q, sumEquiv, ?_, ?_, fun _ i x => sumEquiv_vertex i x,
    fun M {i j} a x => sumEquiv_arrow (M := M) (i := i) (j := j) a x⟩
  · intro M i j a x
    change (QuiverRepresentation.arrow (representation M) a x : vertexSpace M j).val = _
    rw [representation_arrow]
    exact coe_arrowMap a x
  · refine ⟨inferInstance, inferInstance, fun _ => rfl, ?_⟩
    intro M N f i
    change QuiverRepresentation.component
      (𝟙 (representation M) ≫ map f ≫ 𝟙 (representation N)) i = restrictMap f i
    rw [Category.comp_id, Category.id_comp, component_map]
  · exact ⟨fun _ => rfl, fun _ m i => sumEquiv_symm_apply m i,
      fun _ i x => sumEquiv_lof i x, sumEquiv_natural⟩

end RM03.ModuleVertices
