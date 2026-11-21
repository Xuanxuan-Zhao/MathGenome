import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.PathOperators
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.AlgebraRepresentations
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.PathAlgebra
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.Representations

/-! The left path algebra action on the direct sum of a quiver representation. -/

open CategoryTheory
open scoped DirectSum BigOperators Classical

namespace RM03.PathOperators

open Quivers.AlgebraRepresentations
open QuiverRepresentation (component)

universe u v w d

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]
variable {F G : QuiverRepresentation.{u, v, w, d} k Q}

abbrev Total (F : QuiverRepresentation.{u, v, w, d} k Q) :=
  PathOperatorsSpec.Total F

noncomputable abbrev inclusion (F : QuiverRepresentation.{u, v, w, d} k Q) (i : Q) :=
  PathOperatorsSpec.inclusion F i

abbrev projection (F : QuiverRepresentation.{u, v, w, d} k Q) (i : Q) :=
  PathOperatorsSpec.projection F i

noncomputable abbrev operator (F : QuiverRepresentation.{u, v, w, d} k Q) (p : Path Q) :=
  PathOperatorsSpec.operator F p

noncomputable abbrev linearExtension (F : QuiverRepresentation.{u, v, w, d} k Q) :=
  PathOperatorsSpec.linearExtension F

abbrev sumMap (f : F ⟶ G) := PathOperatorsSpec.sumMap f

theorem operator_apply (F : QuiverRepresentation.{u, v, w, d} k Q) (p : Path Q) (x : Total F) :
    operator F p x = inclusion F p.2.1 (F.mapPath p.2.2 (projection F p.1 x)) := rfl

@[simp] theorem projection_inclusion (F : QuiverRepresentation.{u, v, w, d} k Q)
    (i : Q) (x : F.vertex i) : projection F i (inclusion F i x) = x :=
  DirectSum.component.lof_self (M := fun j => (F.vertex j : Type d)) k i x

theorem projection_inclusion_of_ne (F : QuiverRepresentation.{u, v, w, d} k Q)
    {i j : Q} (h : i ≠ j) (x : F.vertex j) : projection F i (inclusion F j x) = 0 := by
  exact (DirectSum.component.of (M := fun l => (F.vertex l : Type d)) k i j x).trans
    (dite_eq_right (Ne.symm h))

@[simp] theorem operator_vertex_apply (F : QuiverRepresentation.{u, v, w, d} k Q)
    (i : Q) (x : Total F) : operator F (Path.vertex i) x = inclusion F i (projection F i x) := by
  change inclusion F i (F.mapPath Quiver.Path.nil (projection F i x)) = _
  rw [QuiverRepresentation.mapPath_nil]
  rfl

theorem operator_mul (F : QuiverRepresentation.{u, v, w, d} k Q) (p q : Path Q) :
    operator F p * operator F q =
      if h : p.source = q.target then operator F (p.concat q h) else 0 := by
  rw [Module.End.mul_eq_comp]
  apply LinearMap.ext
  intro x
  by_cases h : p.source = q.target
  · rw [dite_eq_left h]
    rcases p with ⟨i, j, p⟩
    rcases q with ⟨l, m, q⟩
    change i = m at h
    subst m
    change inclusion F j (F.mapPath p (projection F i
      (inclusion F i (F.mapPath q (projection F l x))))) =
        inclusion F j (F.mapPath (q.comp p) (projection F l x))
    rw [projection_inclusion, QuiverRepresentation.mapPath_comp, LinearMap.comp_apply]
  · rw [dite_eq_right h, LinearMap.comp_apply, operator_apply, operator_apply,
      projection_inclusion_of_ne F (show p.1 ≠ q.2.1 from h), map_zero, map_zero,
      LinearMap.zero_apply]

theorem sum_vertex_operators [Fintype Q] (F : QuiverRepresentation.{u, v, w, d} k Q) :
    (∑ i : Q, operator F (Path.vertex i)) = 1 := by
  apply LinearMap.ext
  intro x
  apply DirectSum.ext_component k
  intro j
  rw [LinearMap.sum_apply, Module.End.one_apply, map_sum]
  simp only [operator_vertex_apply]
  rw [Finset.sum_eq_single j]
  · exact projection_inclusion F j (projection F j x)
  · intro i _ hij
    exact projection_inclusion_of_ne F (Ne.symm hij) (projection F i x)
  · simp

@[simp] theorem linearExtension_ofPath (F : QuiverRepresentation.{u, v, w, d} k Q) (p : Path Q) :
    linearExtension F (PathAlgebra.ofPath k p) = operator F p := by
  rw [← PathAlgebra.basis_apply]
  exact (PathAlgebra.basis k Q).constr_basis k (operator F) p

theorem linearExtension_apply (F : QuiverRepresentation.{u, v, w, d} k Q)
    (a : PathAlgebra k Q) (x : Total F) :
    linearExtension F a x =
      (show Path Q →₀ k from a).sum (fun p c => c • operator F p x) := by
  change ((PathAlgebra.basis k Q).constr k (operator F) a) x = _
  rw [Module.Basis.constr_apply]
  change ((show Path Q →₀ k from a).sum fun p c => c • operator F p) x = _
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem linearExtension_mul (F : QuiverRepresentation.{u, v, w, d} k Q)
    (a b : PathAlgebra k Q) :
    linearExtension F (a * b) = linearExtension F a * linearExtension F b := by
  let L := linearExtension F
  let D := Total F
  let left := (PathAlgebra.mulBilinear k Q).compr₂ₛₗ L
  let right := (LinearMap.llcomp k D D D).compl₁₂ L L
  have h : left = right := by
    apply (PathAlgebra.basis k Q).ext
    intro p
    apply (PathAlgebra.basis k Q).ext
    intro q
    change L (PathAlgebra.basis k Q p * PathAlgebra.basis k Q q) =
      L (PathAlgebra.basis k Q p) * L (PathAlgebra.basis k Q q)
    simp only [L, PathAlgebra.basis_apply, linearExtension_ofPath, operator_mul,
      PathAlgebra.ofPath_mul_ofPath]
    split <;> simp
  exact DFunLike.congr_fun (DFunLike.congr_fun h a) b

theorem sumMap_apply (f : F ⟶ G) (x : Total F) (i : Q) :
    projection G i (sumMap f x) = component f i (projection F i x) := rfl

@[simp] theorem sumMap_inclusion (f : F ⟶ G) (i : Q) (x : F.vertex i) :
    sumMap f (inclusion F i x) = inclusion G i (component f i x) :=
  DirectSum.lmap_lof (component f) i x

theorem sumMap_operator (f : F ⟶ G) (p : Path Q) (x : Total F) :
    sumMap f (operator F p x) = operator G p (sumMap f x) := by
  rw [operator_apply, operator_apply, sumMap_inclusion, sumMap_apply]
  exact congrArg (inclusion G p.2.1)
    (DFunLike.congr_fun (QuiverRepresentation.naturality f p.2.2) (projection F p.1 x))

theorem sumMap_linearExtension (f : F ⟶ G) (a : PathAlgebra k Q) (x : Total F) :
    sumMap f (linearExtension F a x) = linearExtension G a (sumMap f x) := by
  rw [linearExtension_apply, linearExtension_apply]
  simp only [Finsupp.sum, map_sum, map_smul, sumMap_operator]

section FiniteVertices

variable [Fintype Q]

/-- The path operators assembled into a unital algebra representation. -/
noncomputable def representation (F : QuiverRepresentation.{u, v, w, d} k Q) :
    PathAlgebra k Q →ₐ[k] Module.End k (Total F) :=
  AlgHom.ofLinearMap (linearExtension F) (by
    rw [← PathAlgebra.sum_vertices, map_sum]
    change (∑ i : Q, linearExtension F (PathAlgebra.ofPath k (Path.vertex i))) = _
    simpa only [linearExtension_ofPath] using sum_vertex_operators F)
    (linearExtension_mul F)

/-- The unital left path algebra module on the direct sum, with its original field action. -/
noncomputable def action (F : QuiverRepresentation.{u, v, w, d} k Q) :
    CompatibleModule k (PathAlgebra k Q) (Total F) :=
  moduleOfRepresentation (representation F)

theorem action_apply (F : QuiverRepresentation.{u, v, w, d} k Q)
    (a : PathAlgebra k Q) (x : Total F) : (action F).act a x = linearExtension F a x := rfl

@[simp] theorem action_ofPath (F : QuiverRepresentation.{u, v, w, d} k Q) (p : Path Q)
    (x : Total F) : (action F).act (PathAlgebra.ofPath k p) x = operator F p x := by
  rw [action_apply, linearExtension_ofPath]

@[simp] theorem action_vertex (F : QuiverRepresentation.{u, v, w, d} k Q) (i : Q) (x : Total F) :
    (action F).act (PathAlgebra.vertex k i) x = inclusion F i (projection F i x) := by
  rw [PathAlgebra.vertex_eq_ofPath, action_ofPath, operator_vertex_apply]

/-- The direct sum with its left path algebra action, as a bundled module. -/
noncomputable def toModule (F : QuiverRepresentation.{u, v, w, d} k Q) :
    ModuleCat.{max u d} (PathAlgebra k Q) :=
  PathOperatorsSpec.bundledModule F (action F)

theorem toModule_smul (F : QuiverRepresentation.{u, v, w, d} k Q)
    (a : PathAlgebra k Q) (x : toModule F) :
    a • x = (linearExtension F a x : toModule F) := rfl

/-- The direct sum map, as a morphism of left path algebra modules. -/
noncomputable def toModuleMap (f : F ⟶ G) : toModule F ⟶ toModule G :=
  letI := (action F).module
  letI := (action G).module
  ModuleCat.ofHom
    { toFun := sumMap f
      map_add' := (sumMap f).map_add
      map_smul' := sumMap_linearExtension f }

@[simp] theorem toModuleMap_apply (f : F ⟶ G) (x : Total F) :
    toModuleMap f x = sumMap f x := rfl

/-- The representation-to-module functor of the path algebra correspondence. -/
noncomputable def moduleFunctor (k : Type w) (Q : Type u)
    [Field k] [Quiver.{v} Q] [Fintype Q] :
    QuiverRepresentation.{u, v, w, d} k Q ⥤ ModuleCat.{max u d} (PathAlgebra k Q) where
  obj := toModule
  map := toModuleMap
  map_id F := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext_component k
    intro i
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext_component k
    intro i
    rfl

@[simp] theorem moduleFunctor_obj (F : QuiverRepresentation.{u, v, w, d} k Q) :
    (moduleFunctor k Q).obj F = toModule F := rfl

@[simp] theorem moduleFunctor_map_apply (f : F ⟶ G) (x : Total F) :
    (moduleFunctor k Q).map f x = sumMap f x := rfl

instance moduleFunctor_additive : (moduleFunctor.{u, v, w, d} k Q).Additive where
  map_add := by
    intro F G f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext_component k
    intro i
    rfl

instance moduleFunctor_linear : (moduleFunctor.{u, v, w, d} k Q).Linear k where
  map_smul := by
    intro F G f c
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sumMap (c • f) x = (action G).act (algebraMap k (PathAlgebra k Q) c) (sumMap f x)
    have h : (action G).act (algebraMap k (PathAlgebra k Q) c) (sumMap f x) =
        c • sumMap f x := (action G).scalar c (sumMap f x)
    rw [h]
    apply DirectSum.ext_component k
    intro i
    rfl

end FiniteVertices

theorem construction : PathOperatorsSpec.Construction.{u, v, w, d} := by
  intro k Q _ _ _
  exact ⟨inferInstance, inferInstance, ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩,
    representation, action, moduleFunctor k Q, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ => rfl, action_ofPath, (by intro F G f; rfl),
    inferInstance, inferInstance⟩

end RM03.PathOperators
