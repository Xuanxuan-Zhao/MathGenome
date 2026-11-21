import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.ModuleEquivalence
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.ModuleVertices
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.PathOperators
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.VertexwiseExactness
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-! The two natural identifications in the module–representation equivalence. -/

open CategoryTheory
open scoped Classical DirectSum ModuleCat

namespace RM03.QuiverModuleEquivalence

universe u v w d

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]

local notation "A" => PathAlgebra k Q
open ModuleVerticesSpec (representation vertexSpace project vertexProjection arrowMap)
open PathOperators (Total inclusion projection operator)
open QuiverRepresentation (component)

private theorem smallTotal (V : QuiverRepresentation.{u, v, w, d} k Q) : Small.{d} (Total V) := by
  let : Small.{d} Q := small_map (Fintype.equivFin Q)
  exact small_of_injective (f := fun x : Total V => (x : ∀ i, V.vertex i))
    (fun _ _ h => DFinsupp.ext (congrFun h))

/-- A copy of the direct sum in the same universe as the vertex spaces.
Only the finiteness of the index type is used to obtain this copy. -/
noncomputable def inverseObj (V : QuiverRepresentation.{u, v, w, d} k Q) : ModuleCat.{d} A :=
  letI : Small.{d} (↑(PathOperators.toModule V)) := smallTotal V
  ModuleCat.of A (Shrink.{d} (↑(PathOperators.toModule V)))

private noncomputable def moduleCoordinates (V : QuiverRepresentation.{u, v, w, d} k Q) :
    inverseObj V ≃ₗ[A] PathOperators.toModule V :=
  letI : Small.{d} (↑(PathOperators.toModule V)) := smallTotal V
  Shrink.linearEquiv A (↑(PathOperators.toModule V))

private noncomputable def unpack (V : QuiverRepresentation.{u, v, w, d} k Q) (x : inverseObj V) : Total V :=
  moduleCoordinates V x

private theorem unpack_smul (V : QuiverRepresentation.{u, v, w, d} k Q) (b : A) (x : inverseObj V) :
    unpack V (b • x) = PathOperators.linearExtension V b (unpack V x) :=
  (moduleCoordinates V).map_smul b x

/-- Coordinates of the inverse functor object in its original direct sum. -/
noncomputable def coordinates (V : QuiverRepresentation.{u, v, w, d} k Q) : inverseObj V ≃ₗ[k] Total V :=
  { (moduleCoordinates V).toAddEquiv with
    map_smul' := fun c x => by
      change unpack V ((algebraMap k A c) • x) = c • (unpack V x : Total V)
      rw [unpack_smul]
      exact (PathOperators.action V).scalar c (unpack V x) }

private noncomputable def inverseMap {V W : QuiverRepresentation.{u, v, w, d} k Q} (f : V ⟶ W) :
    inverseObj V ⟶ inverseObj W :=
  let map : inverseObj V →ₗ[A] inverseObj W :=
    (moduleCoordinates W).symm.toLinearMap.comp
      ((PathOperators.toModuleMap f).hom.comp (moduleCoordinates V).toLinearMap)
  ModuleCat.ofHom (X := inverseObj V) (Y := inverseObj W) map

private theorem unpack_map {V W : QuiverRepresentation.{u, v, w, d} k Q} (f : V ⟶ W) (x : inverseObj V) :
    unpack W (inverseMap f x) = PathOperators.sumMap f (unpack V x) :=
  (moduleCoordinates W).apply_symm_apply _

/-- Send a representation to its direct sum with the path action. -/
noncomputable def inverse (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Fintype Q] :
    QuiverRepresentation.{u, v, w, d} k Q ⥤ ModuleCat.{d} (PathAlgebra k Q) where
  obj := inverseObj
  map := inverseMap
  map_id V := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => (moduleCoordinates V).injective ?_
    change unpack V (inverseMap (𝟙 V) x) = unpack V x
    rw [unpack_map]
    apply DirectSum.ext_component k
    intro i
    rfl
  map_comp {V W X} f g := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => (moduleCoordinates X).injective ?_
    change unpack X (inverseMap (f ≫ g) x) = unpack X (inverseMap g (inverseMap f x))
    rw [unpack_map, unpack_map, unpack_map]
    apply DirectSum.ext_component k
    intro i
    rfl

instance inverseAdditive : (inverse.{u, v, w, d} k Q).Additive where
  map_add {V W} {f g} := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => (moduleCoordinates W).injective ?_
    change unpack W (inverseMap (f + g) x) = unpack W (inverseMap f x + inverseMap g x)
    change inverseObj V at x
    have hadd : unpack W (inverseMap f x + inverseMap g x) =
        unpack W (inverseMap f x) + unpack W (inverseMap g x) :=
      (moduleCoordinates W).map_add _ _
    rw [hadd, unpack_map, unpack_map, unpack_map]
    apply DirectSum.ext_component k
    intro i
    rfl

instance inverseLinear : (inverse.{u, v, w, d} k Q).Linear k where
  map_smul {V W} f c := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => (coordinates W).injective ?_
    change coordinates W (inverseMap (c • f) x) = coordinates W (c • inverseMap f x)
    rw [map_smul]
    change unpack W (inverseMap (c • f) x) = (c • (unpack W (inverseMap f x) : Total W))
    change inverseObj V at x
    rw [unpack_map, unpack_map]
    apply DirectSum.ext_component k
    intro i
    rfl

/-- The algebra action in direct sum coordinates. -/
theorem coordinates_smul (V : QuiverRepresentation.{u, v, w, d} k Q)
    (b : A) (x : inverseObj V) :
    coordinates V (b • x) = PathOperators.linearExtension V b (coordinates V x) :=
  unpack_smul V b x

/-- Each path acts by projection, the path map, and inclusion. -/
theorem coordinates_smul_ofPath (V : QuiverRepresentation.{u, v, w, d} k Q)
    (p : Path Q) (x : inverseObj V) :
    coordinates V (PathAlgebra.ofPath k p • x) = operator V p (coordinates V x) := by
  rw [coordinates_smul, PathOperators.linearExtension_ofPath]

/-- The morphism on direct sums is the direct sum of the vertex maps. -/
theorem coordinates_map {V W : QuiverRepresentation.{u, v, w, d} k Q}
    (f : V ⟶ W) (x : inverseObj V) :
    coordinates W ((inverse k Q).map f x) = PathOperators.sumMap f (coordinates V x) :=
  unpack_map f x

private theorem sum_path (M : ModuleCat.{d} A) {i j : Q} (p : Quiver.Path i j)
    (x : Total (representation M)) :
    ModuleVertices.sumEquiv M (operator (representation M) (Path.ofPath p) x) =
      PathAlgebra.ofPath k (Path.ofPath p) • ModuleVertices.sumEquiv M x := by
  induction p with
  | nil =>
    rw [show Path.ofPath (Quiver.Path.nil : Quiver.Path i i) = Path.vertex i from rfl,
      PathOperators.operator_vertex_apply]
    exact ModuleVertices.sumEquiv_vertex i x
  | @cons j l p a ih =>
    have ha (y : Total (representation M)) :
        ModuleVertices.sumEquiv M (operator (representation M) (Path.arrow a) y) =
          PathAlgebra.arrow k a • ModuleVertices.sumEquiv M y :=
      ModuleVertices.sumEquiv_arrow a y
    have hop : operator (representation M) (Path.arrow a) *
        operator (representation M) (Path.ofPath p) =
          operator (representation M) (Path.ofPath (p.cons a)) := by
      rw [PathOperators.operator_mul, dite_eq_left (show (Path.arrow a).source =
        (Path.ofPath p).target from rfl)]
      exact congrArg (operator (representation M)) (Path.concat_ofPath a.toPath p)
    rw [← hop, Module.End.mul_apply, ha, ih, ← mul_smul, PathAlgebra.ofPath_cons]

private theorem sum_smul (M : ModuleCat.{d} A) (b : A) (x : Total (representation M)) :
    ModuleVertices.sumEquiv M (PathOperators.linearExtension (representation M) b x) =
      b • ModuleVertices.sumEquiv M x := by
  let S := (ModuleVertices.sumEquiv M).toLinearMap
  let L := PathOperators.linearExtension (representation M)
  let R := (Algebra.lsmul k k M : A →ₐ[k] Module.End k M).toLinearMap
  let D := Total (representation M)
  let c : (M →ₗ[k] M) →ₗ[k] (D →ₗ[k] M) →ₗ[k] D →ₗ[k] M := LinearMap.llcomp k D M M
  let c' : (D →ₗ[k] M) →ₗ[k] (D →ₗ[k] D) →ₗ[k] D →ₗ[k] M := LinearMap.llcomp k D D M
  have h : (c' S).comp L = (c.flip S).comp R := by
    apply (PathAlgebra.basis k Q).ext
    rintro ⟨i, j, p⟩
    rw [PathAlgebra.basis_apply]
    change S.comp (PathOperators.linearExtension (representation M)
        (PathAlgebra.ofPath k (Path.ofPath p))) =
      (R (PathAlgebra.ofPath k (Path.ofPath p))).comp S
    rw [PathOperators.linearExtension_ofPath]
    exact LinearMap.ext fun x => sum_path M p x
  exact DFunLike.congr_fun (DFunLike.congr_fun h b) x

private noncomputable def sumIso (M : ModuleCat.{d} A) :
    inverseObj (representation M) ≅ M :=
  (LinearEquiv.ofBijective
    ({ toFun := fun x => ModuleVertices.sumEquiv M (unpack (representation M) x)
       map_add' := fun x y => by
         change ModuleVertices.sumEquiv M (moduleCoordinates (representation M) (x + y)) =
           ModuleVertices.sumEquiv M (moduleCoordinates (representation M) x) +
             ModuleVertices.sumEquiv M (moduleCoordinates (representation M) y)
         rw [(moduleCoordinates (representation M)).map_add]
         exact (ModuleVertices.sumEquiv M).map_add _ _
       map_smul' := fun b x => (congrArg _ (unpack_smul _ b x)).trans (sum_smul M b _) } :
      inverseObj (representation M) →ₗ[A] M)
    ((ModuleVertices.sumEquiv M).bijective.comp
      (moduleCoordinates (representation M)).bijective)).toModuleIso

private theorem sumIso_hom (M : ModuleCat.{d} A) (x : inverseObj (representation M)) :
    (sumIso M).hom x = ModuleVertices.sumEquiv M (unpack (representation M) x) :=
  rfl

private theorem sumIso_inv (M : ModuleCat.{d} A) (m : M) :
    unpack (representation M) ((sumIso M).inv m) = (ModuleVertices.sumEquiv M).symm m := by
  apply (ModuleVertices.sumEquiv M).injective
  change ((sumIso M).inv ≫ (sumIso M).hom) m = _
  rw [Iso.inv_hom_id]
  exact ((ModuleVertices.sumEquiv M).apply_symm_apply m).symm

private noncomputable def sumNatIso :
    ModuleVertices.functor.{u, v, w, d} k Q ⋙ inverse k Q ≅ 𝟭 (ModuleCat.{d} A) :=
  NatIso.ofComponents sumIso (by
    intro M N f
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => ?_
    change inverseObj (representation M) at x
    change (sumIso N).hom (inverseMap (ModuleVertices.map f) x) = f ((sumIso M).hom x)
    rw [sumIso_hom, sumIso_hom, unpack_map]
    exact ModuleVertices.sumEquiv_natural f _)

private theorem vertex_action (V : QuiverRepresentation.{u, v, w, d} k Q) (i : Q) (x : inverseObj V) :
    unpack V (PathAlgebra.vertex k i • x) = inclusion V i (projection V i (unpack V x)) :=
  (unpack_smul V _ x).trans (PathOperators.action_vertex V i (unpack V x))

/-- Recover the original vertex space inside the direct sum module. -/
private noncomputable def recoverMap (V : QuiverRepresentation.{u, v, w, d} k Q) (i : Q) :
    V.vertex i →ₗ[k] vertexSpace (inverseObj V) i :=
  ((coordinates V).symm.toLinearMap.comp (inclusion V i)).codRestrict _ (by
    intro x
    refine ⟨(coordinates V).symm (inclusion V i x), ?_⟩
    change PathAlgebra.vertex k i • (coordinates V).symm (inclusion V i x) =
      (coordinates V).symm (inclusion V i x)
    apply (coordinates V).injective
    change unpack V (PathAlgebra.vertex k i • (coordinates V).symm (inclusion V i x)) =
      coordinates V ((coordinates V).symm (inclusion V i x))
    rw [vertex_action]
    change inclusion V i (projection V i (coordinates V ((coordinates V).symm
      (inclusion V i x)))) = _
    rw [LinearEquiv.apply_symm_apply, PathOperators.projection_inclusion])

private theorem recover_apply (V : QuiverRepresentation.{u, v, w, d} k Q) (i : Q) (x : V.vertex i) :
    coordinates V (recoverMap V i x : inverseObj V) = inclusion V i x :=
  (coordinates V).apply_symm_apply _

private noncomputable def recover (V : QuiverRepresentation.{u, v, w, d} k Q) (i : Q) :
    V.vertex i ≃ₗ[k] vertexSpace (inverseObj V) i :=
  LinearEquiv.ofLinearMap (recoverMap V i)
    (((projection V i).comp (coordinates V).toLinearMap).comp (vertexSpace (inverseObj V) i).subtype)
    (by
      refine LinearMap.ext fun x => Subtype.ext ((coordinates V).injective ?_)
      change coordinates V (recoverMap V i (projection V i (coordinates V (x : inverseObj V))) :
        inverseObj V) = coordinates V (x : inverseObj V)
      rw [recover_apply]
      exact (vertex_action V i x).symm.trans
        (congrArg (unpack V) (by rw [ModuleVertices.vertex_smul_coe i i x, ite_eq_left rfl])))
    (by
      refine LinearMap.ext fun x => ?_
      change projection V i (coordinates V (recoverMap V i x : inverseObj V)) = x
      rw [recover_apply, PathOperators.projection_inclusion])

private theorem arrow_action (V : QuiverRepresentation.{u, v, w, d} k Q)
    {i j : Q} (a : Quiver.Hom i j) (x : inverseObj V) :
    unpack V (PathAlgebra.arrow k a • x) = inclusion V j (V.arrow a (projection V i (unpack V x))) := by
  rw [unpack_smul, PathAlgebra.arrow_eq_ofPath, PathOperators.linearExtension_ofPath]
  rfl

private noncomputable def recoverHom (V : QuiverRepresentation.{u, v, w, d} k Q) :
    V ⟶ representation (inverseObj V) :=
  QuiverRepresentation.homMk (fun i => (recover V i).toLinearMap) (by
    intro i j a
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply (coordinates V).injective
    change coordinates V (recoverMap V j (V.arrow a x) : inverseObj V) =
      coordinates V (show vertexSpace (inverseObj V) j from
        QuiverRepresentation.arrow (representation (inverseObj V)) a (recoverMap V i x)).val
    rw [recover_apply]
    have harrow :
        (show vertexSpace (inverseObj V) j from
          QuiverRepresentation.arrow (representation (inverseObj V)) a (recoverMap V i x)) =
        arrowMap (inverseObj V) a (recoverMap V i x) :=
      DFunLike.congr_fun (ModuleVertices.representation_arrow (inverseObj V) a) (recoverMap V i x)
    rw [show (show vertexSpace (inverseObj V) j from
      QuiverRepresentation.arrow (representation (inverseObj V)) a (recoverMap V i x)).val =
        PathAlgebra.arrow k a • (recoverMap V i x : inverseObj V) from
      (congrArg Subtype.val harrow).trans (ModuleVertices.coe_arrowMap a (recoverMap V i x))]
    change inclusion V j (V.arrow a x) = unpack V (PathAlgebra.arrow k a •
      (recoverMap V i x : inverseObj V))
    rw [arrow_action]
    change inclusion V j (V.arrow a x) =
      inclusion V j (V.arrow a (projection V i (coordinates V (recoverMap V i x : inverseObj V))))
    rw [recover_apply, PathOperators.projection_inclusion])

private theorem recoverHom_component (V : QuiverRepresentation.{u, v, w, d} k Q) (i : Q) :
    component (recoverHom V) i = recoverMap V i := rfl

private theorem recoverHom_isIso (V : QuiverRepresentation.{u, v, w, d} k Q) : IsIso (recoverHom V) := by
  let (i : Paths Q) : IsIso ((recoverHom V).app i) := by
    change IsIso (recover V i).toModuleIso.hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

private noncomputable def recoverNatIso :
    𝟭 (QuiverRepresentation.{u, v, w, d} k Q) ≅
      inverse k Q ⋙ ModuleVertices.functor.{u, v, w, d} k Q :=
  NatIso.ofComponents (fun V =>
      @CategoryTheory.asIso _ _ V (representation (inverseObj V)) (recoverHom V) (recoverHom_isIso V)) (by
    intro V W f
    apply QuiverRepresentation.hom_ext
    intro i
    change (recoverMap W i).comp (component f i) =
      (ModuleVerticesSpec.restrictMap (inverseMap f) i).comp (recoverMap V i)
    refine LinearMap.ext fun x => Subtype.ext ((coordinates W).injective ?_)
    change coordinates W (recoverMap W i (component f i x) : inverseObj W) =
      coordinates W (ModuleVerticesSpec.restrictMap (inverseMap f) i
        (recoverMap V i x) : inverseObj W)
    rw [recover_apply, ModuleVertices.coe_restrictMap]
    change inclusion W i (component f i x) =
      unpack W (inverseMap f (recoverMap V i x : inverseObj V))
    rw [unpack_map]
    change inclusion W i (component f i x) =
      PathOperators.sumMap f (coordinates V (recoverMap V i x : inverseObj V))
    rw [recover_apply, PathOperators.sumMap_inclusion])

/-- The linear equivalence between left path algebra modules and representations. -/
noncomputable def equivalence (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Fintype Q] :
    ModuleCat.{d} (PathAlgebra k Q) ≌ QuiverRepresentation.{u, v, w, d} k Q where
  functor := ModuleVertices.functor.{u, v, w, d} k Q
  inverse := inverse k Q
  unitIso := sumNatIso.symm
  counitIso := recoverNatIso.symm
  functor_unitIso_comp M := by
    change ModuleVertices.map (sumIso M).inv ≫ (recoverNatIso.app (representation M)).inv =
      𝟙 (representation M)
    apply (Iso.comp_inv_eq (recoverNatIso.app (representation M))).mpr
    rw [Category.id_comp]
    apply QuiverRepresentation.hom_ext
    intro i
    change ModuleVerticesSpec.restrictMap (sumIso M).inv i = recoverMap (representation M) i
    refine LinearMap.ext fun x => Subtype.ext ((coordinates (representation M)).injective ?_)
    rw [ModuleVertices.coe_restrictMap]
    refine Eq.trans ?_ (recover_apply (representation M) i x).symm
    change unpack (representation M) ((sumIso M).inv (x : M)) = _
    rw [sumIso_inv]
    apply DirectSum.ext_component k
    intro j
    change (ModuleVertices.sumEquiv M).symm (x : M) j =
      projection (representation M) j (inclusion (representation M) i x)
    by_cases h : j = i
    · subst j
      refine Eq.trans ?_ (PathOperators.projection_inclusion (representation M) i x).symm
      apply Subtype.ext
      rw [ModuleVertices.sumEquiv_symm_apply, ModuleVertices.vertex_smul_coe,
        ite_eq_left rfl]
    · refine Eq.trans ?_ (PathOperators.projection_inclusion_of_ne (representation M) h x).symm
      apply Subtype.ext
      rw [ModuleVertices.sumEquiv_symm_apply, ModuleVertices.vertex_smul_coe,
        ite_eq_right h]
      rfl

open QuiverModuleEquivalenceSpec (finiteModules finiteRepresentations)

private theorem finite_total_iff (V : QuiverRepresentation.{u, v, w, d} k Q) :
    FiniteDimensional k (Total V) ↔ finiteRepresentations V := by
  constructor
  · intro h i
    exact Module.Finite.of_surjective (projection V i)
      (fun x => ⟨inclusion V i x, PathOperators.projection_inclusion V i x⟩)
  · intro h
    let (i : Q) : Module.Finite k (V.vertex i) := h i
    exact Module.Finite.equiv
      (DirectSum.linearEquivFunOnFintype k Q (fun i => V.vertex i)).symm

/-- A module is finite-dimensional precisely when all its vertex spaces are. -/
theorem finite_forward (M : ModuleCat.{d} A) :
    FiniteDimensional k M ↔ finiteRepresentations ((ModuleVertices.functor.{u, v, w, d} k Q).obj M) :=
  (Module.Finite.equiv_iff (ModuleVertices.sumEquiv M).symm).trans (finite_total_iff (representation M))

/-- The direct sum is finite-dimensional precisely when all its vertex spaces are. -/
theorem finite_inverse (V : QuiverRepresentation.{u, v, w, d} k Q) :
    FiniteDimensional k (inverseObj V) ↔ finiteRepresentations V :=
  (Module.Finite.equiv_iff (coordinates V)).trans (finite_total_iff V)

private instance finiteRepresentationsClosed :
    (finiteRepresentations.{u, v, w, d} (k := k) (Q := Q)).IsClosedUnderIsomorphisms where
  of_iso {V W} e h i := by
    let e' : QuiverRepresentation.vertex V i ≅ QuiverRepresentation.vertex W i :=
      ((evaluation (Paths Q) (ModuleCat.{d} k)).obj (i : Paths Q)).mapIso e
    let : FiniteDimensional k (QuiverRepresentation.vertex V i) := h i
    exact Module.Finite.equiv e'.toLinearEquiv

/-- Restrict the equivalence to the full subcategories of finite-dimensional objects. -/
noncomputable def finiteEquivalence (k : Type w) (Q : Type u)
    [Field k] [Quiver.{v} Q] [Fintype Q] :
    (finiteModules.{u, v, w, d} (k := k) (Q := Q)).FullSubcategory ≌
      (finiteRepresentations.{u, v, w, d} (k := k) (Q := Q)).FullSubcategory :=
  (equivalence k Q).congrFullSubcategory (funext fun M => propext (finite_forward M).symm)

instance finiteForwardAdditive : (finiteEquivalence.{u, v, w, d} k Q).functor.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact (ModuleVertices.functor k Q).map_add

instance finiteForwardLinear : (finiteEquivalence.{u, v, w, d} k Q).functor.Linear k where
  map_smul := by
    intro M N f c
    apply ObjectProperty.hom_ext
    exact (ModuleVertices.functor k Q).map_smul c f.hom

instance finiteInverseAdditive : (finiteEquivalence.{u, v, w, d} k Q).inverse.Additive where
  map_add := by
    intro V W f g
    apply ObjectProperty.hom_ext
    exact (inverse k Q).map_add

instance finiteInverseLinear : (finiteEquivalence.{u, v, w, d} k Q).inverse.Linear k where
  map_smul := by
    intro V W f c
    apply ObjectProperty.hom_ext
    exact (inverse k Q).map_smul c f.hom

/-- Exactness at the middle module is equivalent to exactness at every vertex. -/
theorem exact_iff_vertexwise {M N P : ModuleCat.{d} A} (f : M ⟶ N) (g : N ⟶ P) :
    (∃ hz : f ≫ g = 0, (ShortComplex.mk f g hz).Exact) ↔
      ∀ i : Q, (ModuleVerticesSpec.restrictMap f i).range =
        (ModuleVerticesSpec.restrictMap g i).ker := by
  let F := ModuleVertices.functor.{u, v, w, d} k Q
  let : F.IsEquivalence := (equivalence k Q).isEquivalence_functor
  refine Iff.trans ?_ (QuiverRepresentation.exact_pair_iff_vertexwise (F.map f) (F.map g))
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨((ShortComplex.mk f g hz).map F).zero, h.map F⟩
  · rintro ⟨hz, h⟩
    have hz' : f ≫ g = 0 := F.map_injective (by rw [Functor.map_comp, hz, Functor.map_zero])
    exact ⟨hz', ((ShortComplex.mk f g hz').exact_map_iff_of_faithful F).1 h⟩

theorem construction : QuiverModuleEquivalenceSpec.Conclusion.{u, v, w, d} := by
  intro k Q _ _ _
  refine ⟨inferInstance, inferInstance, ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩,
    equivalence k Q, fun _ => rfl, coordinates,
    ModuleVertices.functorAdditive, ModuleVertices.functorLinear, inverseAdditive, inverseLinear,
    ⟨coordinates_smul, coordinates_smul_ofPath, coordinates_map⟩,
    ?_, finite_forward, finite_inverse,
    ⟨finiteEquivalence k Q, finiteForwardAdditive, finiteForwardLinear,
      finiteInverseAdditive, finiteInverseLinear, rfl, rfl⟩,
    exact_iff_vertexwise⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M N f i
    change component (𝟙 _ ≫ ModuleVertices.map f ≫ 𝟙 _) i = _
    rw [Category.id_comp, Category.comp_id, ModuleVertices.component_map]
  · intro M x
    change inverseObj (representation M) at x
    change (sumIso M).hom x = ModuleVerticesSpec.sumMap M
      (coordinates (representation M) ((inverse k Q).map (𝟙 (representation M)) x))
    rw [CategoryTheory.Functor.map_id (inverse k Q) (representation M)]
    rfl
  · intro M m i
    change ((show vertexSpace M i from coordinates (representation M)
      ((inverse k Q).map (𝟙 (representation M)) ((sumIso M).inv m)) i) : M) = _
    rw [CategoryTheory.Functor.map_id (inverse k Q) (representation M)]
    change ((show vertexSpace M i from unpack (representation M) ((sumIso M).inv m) i) : M) = _
    rw [sumIso_inv]
    exact ModuleVertices.sumEquiv_symm_apply m i
  · intro V i x
    change coordinates V (show vertexSpace (inverseObj V) i from
      component (recoverHom V ≫ 𝟙 _) i x) = inclusion V i x
    rw [Category.comp_id, recoverHom_component]
    exact recover_apply V i x

end RM03.QuiverModuleEquivalence
