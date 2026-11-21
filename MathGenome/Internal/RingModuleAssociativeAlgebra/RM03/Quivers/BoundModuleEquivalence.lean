import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.BoundModuleEquivalence
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.ModuleEquivalence
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.QuotientModules
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.Relations
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-! The canonical equivalence for left modules over a path algebra modulo relations. -/

open CategoryTheory
open scoped ModuleCat

namespace RM03.QuiverBoundModuleEquivalence

universe u v w d

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q]

open QuiverBoundModuleEquivalenceSpec (satisfying quotientIdeal vertexExact)
open QuiverModuleEquivalence (coordinates coordinates_smul)
open Quivers.QuotientModules (annihilated)

local notation "A" => PathAlgebra k Q

/-- A relation acts on the direct sum by its map between its two vertex spaces. -/
theorem relation_operator (V : QuiverRepresentation.{u, v, w, d} k Q)
    {i j : Q} (r : QuiverRelation k i j) :
    PathOperators.linearExtension V (QuiverRelation.toPathAlgebra i j r) =
      (PathOperators.inclusion V j).comp
        ((QuiverRelation.evaluate V i j r).comp (PathOperators.projection V i)) := by
  let compose : (V.vertex i →ₗ[k] V.vertex j) →ₗ[k] Module.End k (PathOperators.Total V) :=
    { toFun := fun f => (PathOperators.inclusion V j).comp
        (f.comp (PathOperators.projection V i))
      map_add' := by
        intro f g
        ext x
        simp
      map_smul' := by
        intro c f
        ext x
        simp }
  change ((PathOperators.linearExtension V).comp (QuiverRelation.toPathAlgebra i j)) r =
    (compose.comp (QuiverRelation.evaluate V i j)) r
  apply LinearMap.congr_fun
  apply Finsupp.lhom_ext
  intro p c
  simp only [LinearMap.comp_apply, QuiverRelation.toPathAlgebra, QuiverRelation.evaluate,
    Finsupp.linearCombination_single, map_smul, PathOperators.linearExtension_ofPath]
  rfl

private theorem relation_mem_kernel [Fintype Q] (V : QuiverRepresentation.{u, v, w, d} k Q)
    (r : QuiverRelation.Bundled k Q) :
    QuiverRelation.toElement r ∈ TwoSidedIdeal.ker (PathOperators.representation V) ↔
      QuiverRelation.Satisfies V r.2.2 := by
  rw [TwoSidedIdeal.mem_ker]
  change PathOperators.linearExtension V (QuiverRelation.toPathAlgebra _ _ _) = 0 ↔ _
  rw [relation_operator]
  change _ ↔ QuiverRelation.evaluate V _ _ r.2.2 = 0
  constructor
  · intro h
    ext x
    have hx := LinearMap.congr_fun h (PathOperators.inclusion V r.1 x)
    change PathOperators.inclusion V r.2.1
      (QuiverRelation.evaluate V r.1 r.2.1 r.2.2
        (PathOperators.projection V r.1 (PathOperators.inclusion V r.1 x))) = 0 at hx
    simpa only [PathOperators.projection_inclusion, map_zero, LinearMap.zero_apply] using
      congrArg (PathOperators.projection V r.2.1) hx
  · intro h
    simp [h]

variable [Fintype Q] (S : Set (QuiverRelation.Bundled k Q))

/-- The chosen relations vanish precisely when the ideal they generate annihilates the
associated path algebra module. -/
theorem satisfies_iff_annihilated (V : QuiverRepresentation.{u, v, w, d} k Q) :
    satisfying S V ↔ annihilated (quotientIdeal S) ((QuiverModuleEquivalence.inverse k Q).obj V) := by
  change satisfying S V ↔ annihilated (quotientIdeal S) (QuiverModuleEquivalence.inverseObj V)
  have hkernel :
      satisfying S V ↔ QuiverRelation.generatedIdeal S ≤
        TwoSidedIdeal.ker (PathOperators.representation V) := by
    rw [QuiverRelation.generatedIdeal_le_iff]
    exact ⟨fun h r hr => (relation_mem_kernel V r).2 (h r hr),
      fun h r hr => (relation_mem_kernel V r).1 (h r hr)⟩
  rw [hkernel]
  constructor
  · intro h x b
    have hb := (TwoSidedIdeal.mem_ker (PathOperators.representation V)).mp (h b.property)
    apply (coordinates V).injective
    rw [coordinates_smul, map_zero]
    exact LinearMap.congr_fun hb _
  · intro h b hb
    apply (TwoSidedIdeal.mem_ker (PathOperators.representation V)).2
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := (coordinates V).surjective y
    change PathOperators.linearExtension V b (coordinates V x) = 0
    have hbx : b • x = 0 := h (x := x) (a := ⟨b, hb⟩)
    rw [← coordinates_smul, hbx, map_zero]

private theorem annihilated_of_iso {I : Ideal A} {M N : ModuleCat.{d} A}
    (e : M ≅ N) (h : annihilated I M) : annihilated I N := by
  intro y b
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
  change (b : A) • e.hom.hom x = 0
  rw [← e.hom.hom.map_smul, h (x := x) (a := b), map_zero]

private instance satisfyingClosed : (satisfying.{u, v, w, d} S).IsClosedUnderIsomorphisms where
  of_iso e h := (satisfies_iff_annihilated S _).2
    (annihilated_of_iso ((QuiverModuleEquivalence.inverse k Q).mapIso e)
      ((satisfies_iff_annihilated S _).1 h))

/-- The module-to-representation functor restricts to the two full subcategories. -/
noncomputable def restrictedEquivalence :
    (annihilated.{max u v w, d} (quotientIdeal S)).FullSubcategory ≌
      (satisfying S).FullSubcategory :=
  (QuiverModuleEquivalence.equivalence k Q).congrFullSubcategory (funext fun M => propext (by
    rw [ObjectProperty.prop_inverseImage_iff, satisfies_iff_annihilated]
    let e := (QuiverModuleEquivalence.equivalence.{u, v, w, d} k Q).unitIso.app M
    exact ⟨annihilated_of_iso e.symm, annihilated_of_iso e⟩))

/-- Restrict quotient scalars, then apply the path algebra equivalence to the
annihilated modules. The target is full, so it retains all representation maps. -/
noncomputable def equivalence :
    ModuleCat.{d} (A ⧸ quotientIdeal S) ≌ (satisfying S).FullSubcategory :=
  (Quivers.QuotientModules.equivalence (quotientIdeal S)).trans (restrictedEquivalence S)

/-- Forgetting the relation condition gives the original functor after scalar restriction. -/
theorem functor_comp_inclusion :
    (equivalence.{u, v, w, d} S).functor ⋙ (satisfying S).ι =
      ModuleCat.restrictScalars (Ideal.Quotient.mk (quotientIdeal S)) ⋙
        (QuiverModuleEquivalence.equivalence k Q).functor :=
  rfl

/-- The inverse recovers the original path algebra action after scalar restriction. -/
theorem inverse_comp_restriction :
    (equivalence.{u, v, w, d} S).inverse ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk (quotientIdeal S)) =
      (satisfying S).ι ⋙ (QuiverModuleEquivalence.equivalence k Q).inverse :=
  rfl

instance forwardAdditive : (equivalence.{u, v, w, d} S).functor.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    let F := ModuleCat.restrictScalars.{d} (Ideal.Quotient.mk (quotientIdeal S)) ⋙
      ModuleVertices.functor.{u, v, w, d} k Q
    change F.map (f + g) = F.map f + F.map g
    exact F.map_add

instance forwardLinear : (equivalence.{u, v, w, d} S).functor.Linear k where
  map_smul := by
    intro M N f c
    apply ObjectProperty.hom_ext
    let F := ModuleCat.restrictScalars.{d} (Ideal.Quotient.mkₐ k (quotientIdeal S)).toRingHom ⋙
      ModuleVertices.functor.{u, v, w, d} k Q
    change F.map (c • f) = c • F.map f
    exact F.map_smul c f

instance inverseAdditive : (equivalence.{u, v, w, d} S).inverse.Additive where
  map_add := by
    intro V W f g
    apply ModuleCat.hom_ext
    ext x
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      ((QuiverModuleEquivalence.inverse k Q).map_add (f := f.hom) (g := g.hom))) x

instance inverseLinear : (equivalence.{u, v, w, d} S).inverse.Linear k where
  map_smul := by
    intro V W f c
    apply ModuleCat.hom_ext
    ext x
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      ((QuiverModuleEquivalence.inverse k Q).map_smul c f.hom)) x

/-- Exactness is unchanged under scalar restriction and the path algebra equivalence. -/
private theorem exact_iff_representation_exact (T : ShortComplex (ModuleCat.{d} (A ⧸ quotientIdeal S))) :
    T.Exact ↔ (T.map ((equivalence S).functor ⋙ (satisfying S).ι)).Exact := by
  let R := ModuleCat.restrictScalars.{d} (Ideal.Quotient.mk (quotientIdeal S))
  let F := (QuiverModuleEquivalence.equivalence.{u, v, w, d} k Q).functor
  let : F.IsEquivalence := (QuiverModuleEquivalence.equivalence k Q).isEquivalence_functor
  change T.Exact ↔ ((T.map R).map F).Exact
  refine Iff.trans ?_ (((T.map R).exact_map_iff_of_faithful F).symm)
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

theorem exact_iff_vertexwise (T : ShortComplex (ModuleCat.{d} (A ⧸ quotientIdeal S))) :
    T.Exact ↔ vertexExact ((equivalence S).functor.map T.f).hom
      ((equivalence S).functor.map T.g).hom :=
  (exact_iff_representation_exact S T).trans
    (QuiverRepresentation.exact_iff_vertexwise (T.map ((equivalence S).functor ⋙ (satisfying S).ι)))

theorem full_exact_iff_vertexwise (T : ShortComplex (satisfying.{u, v, w, d} S).FullSubcategory) :
    T.Exact ↔ vertexExact T.f.hom T.g.hom := by
  let E := equivalence.{u, v, w, d} S
  let : E.functor.IsEquivalence := E.isEquivalence_functor
  let : E.inverse.IsEquivalence := E.isEquivalence_inverse
  have h₁ : T.Exact ↔ (T.map E.inverse).Exact := by
    constructor
    · exact fun h => h.map E.inverse
    · intro h
      exact (ShortComplex.exact_iff_of_iso (T.mapNatIso E.counitIso)).1 (h.map E.functor)
  have h₂ := ShortComplex.exact_iff_of_iso
    (T.mapNatIso (Functor.isoWhiskerRight E.counitIso (satisfying S).ι))
  exact h₁.trans ((exact_iff_representation_exact S (T.map E.inverse)).trans
    (h₂.trans (QuiverRepresentation.exact_iff_vertexwise (T.map (satisfying S).ι))))

/-- A pair of maps of quotient modules is exact precisely when each vertex pair is exact.
The vertex equalities also force the composite to vanish. -/
theorem exact_pair_iff_vertexwise {L M N : ModuleCat.{d} (A ⧸ quotientIdeal S)}
    (f : L ⟶ M) (g : M ⟶ N) :
    (∃ h : f ≫ g = 0, (ShortComplex.mk f g h).Exact) ↔
      vertexExact ((equivalence S).functor.map f).hom ((equivalence S).functor.map g).hom := by
  let B := equivalence.{u, v, w, d} S
  let F := B.functor ⋙ (satisfying S).ι
  let : B.functor.IsEquivalence := B.isEquivalence_functor
  constructor
  · rintro ⟨hz, h⟩
    exact (exact_iff_vertexwise S (ShortComplex.mk f g hz)).mp h
  · intro h
    obtain ⟨hz, _⟩ := (QuiverRepresentation.exact_pair_iff_vertexwise (F.map f) (F.map g)).mpr h
    have hz' : f ≫ g = 0 := F.map_injective (by rw [Functor.map_comp, hz, Functor.map_zero])
    exact ⟨hz', (exact_iff_vertexwise S (ShortComplex.mk f g hz')).mpr h⟩

/-- Exactness of a pair in the full category of representations satisfying the relations. -/
theorem full_exact_pair_iff_vertexwise {V W X : (satisfying.{u, v, w, d} S).FullSubcategory}
    (f : V ⟶ W) (g : W ⟶ X) :
    (∃ h : f ≫ g = 0, (ShortComplex.mk f g h).Exact) ↔ vertexExact f.hom g.hom := by
  constructor
  · rintro ⟨hz, h⟩
    exact (full_exact_iff_vertexwise S (ShortComplex.mk f g hz)).mp h
  · intro h
    obtain ⟨hz, _⟩ := (QuiverRepresentation.exact_pair_iff_vertexwise f.hom g.hom).mpr h
    have hz' : f ≫ g = 0 := (satisfying S).ι.map_injective hz
    exact ⟨hz', (full_exact_iff_vertexwise S (ShortComplex.mk f g hz')).mpr h⟩

theorem construction : QuiverBoundModuleEquivalenceSpec.Construction.{u, v, w, d} := by
  intro k Q _ _ _ S
  refine ⟨inferInstance, inferInstance, ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩,
    QuiverModuleEquivalence.equivalence k Q, fun _ => rfl, coordinates, equivalence S,
    ⟨coordinates_smul, QuiverModuleEquivalence.coordinates_smul_ofPath,
      QuiverModuleEquivalence.coordinates_map⟩, ?_, satisfies_iff_annihilated S,
    forwardAdditive S, forwardLinear S, inverseAdditive S, inverseLinear S,
    functor_comp_inclusion S, inverse_comp_restriction S,
    exact_pair_iff_vertexwise S, full_exact_pair_iff_vertexwise S⟩
  intro M N f i
  change QuiverRepresentation.component (𝟙 _ ≫ ModuleVertices.map f ≫ 𝟙 _) i = _
  rw [Category.id_comp, Category.comp_id, ModuleVertices.component_map]

end RM03.QuiverBoundModuleEquivalence
