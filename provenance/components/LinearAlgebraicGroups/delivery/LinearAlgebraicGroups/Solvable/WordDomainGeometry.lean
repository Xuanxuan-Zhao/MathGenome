import LinearAlgebraicGroups.Affine.Components
import LinearAlgebraicGroups.Affine.SmoothnessCriteria
import Specs.LinearAlgebraicGroups.Solvable.WordDomainGeometry
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Data.Fintype.Option
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

namespace LinearAlgebraicGroups.WordDomainGeometry

universe u

noncomputable section

open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

variable {k : Type u} [Field k]

private abbrev sectionOfClosedPoint [IsAlgClosed k] (X : SchemeOver k)
    [LocallyOfFiniteType X.hom] (x : X.left) (hx : IsClosed {x}) :
    (𝟙_ (SchemeOver k)) ⟶ X :=
  Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)

private theorem sectionOfClosedPoint_apply [IsAlgClosed k] (X : SchemeOver k)
    [LocallyOfFiniteType X.hom] (x : X.left) (hx : IsClosed {x}) :
    (sectionOfClosedPoint X x hx).left (IsLocalRing.closedPoint k) = x :=
  pointOfClosedPoint_apply X.hom x hx _

private theorem section_comp_mulRight {G : Specs.GroupScheme k}
    (p q : (𝟙_ (SchemeOver k)) ⟶ G.X) :
    p ≫ (GrpObj.mulRight q).hom = p * q := by
  simp [GrpObj.mulRight, CategoryTheory.Hom.mul_def, comp_lift_assoc, comp_toUnit_assoc]

private theorem geometricallyConnected_of_connected (G : AffineAlgebraicGroup k)
    [ConnectedSpace G.val.X.left] : GeometricallyConnected G.val.X.hom := by
  obtain ⟨Q, H, q, i, hi, -⟩ := identityComponentAndQuotient k G
  let j := i.hom.hom.left
  have : IsOpenImmersion j := hi.openImmersion
  have hj : j.opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext_iff.mpr
    change Set.range i.hom.hom.left = Set.univ
    rw [hi.identityComponent, PreconnectedSpace.connectedComponent_eq_univ]
  have : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j hj
  let P : MorphismProperty Scheme.{u} := geometrically (fun X ↦ ConnectedSpace X)
  have : P.IsStableUnderBaseChange := inferInstanceAs
    ((geometrically (fun X : Scheme.{u} ↦ ConnectedSpace X)).IsStableUnderBaseChange)
  exact ⟨(MorphismProperty.cancel_left_of_respectsIso P j G.val.X.hom).mp
    (show P (j ≫ G.val.X.hom) from
      (Over.w i.hom.hom).symm ▸ hi.geometricallyConnected.geometrically_connectedSpace)⟩

-- An intersection of distinct components would contain a closed point.
-- Translation sends it to a point lying on only one component.
private theorem irreducible_of_connected_over_algClosed [IsAlgClosed k]
    (G : Specs.GroupScheme k) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [ConnectedSpace G.X.left] : IrreducibleSpace G.X.left := by
  classical
  let X := G.X.left
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have : IsNoetherian X := ⟨⟩
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace G.X.hom
  let Z := irreducibleComponent (Classical.choice (inferInstance : Nonempty X))
  have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents _
  let V (C : Set X) := (⋃₀ (irreducibleComponents X \ {C}))ᶜ
  have hV (C : Set X) : IsOpen (V C) := by
    rw [show V C = (⋃₀ (irreducibleComponents X \ {C}))ᶜ from rfl,
      Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have hcl (C : Set X) (hC : C ∈ irreducibleComponents X) : closure (V C) = C :=
    closure_sUnion_irreducibleComponents_sdiff_singleton
      NoetherianSpace.finite_irreducibleComponents C hC
  have hne : (V Z).Nonempty := by
    rw [← closure_nonempty_iff, hcl Z hZ]
    exact hZ.1.nonempty
  obtain ⟨z, hzV, hzc⟩ := nonempty_inter_closedPoints hne (hV Z).isLocallyClosed
  have hz_only (C : Set X) (hC : C ∈ irreducibleComponents X) (hzC : z ∈ C) : C = Z := by
    by_contra h
    exact hzV (Set.mem_sUnion_of_mem hzC ⟨hC, by simpa using h⟩)
  have only_one (A B : Set X) (hA : A ∈ irreducibleComponents X)
      (hB : B ∈ irreducibleComponents X) (hAB : (A ∩ B).Nonempty) : A = B := by
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hAB
      ((isClosed_of_mem_irreducibleComponents _ hA).inter
        (isClosed_of_mem_irreducibleComponents _ hB)).isLocallyClosed
    let p := sectionOfClosedPoint G.X x hxc
    let r := sectionOfClosedPoint G.X z hzc
    let t := GrpObj.mulRight (p⁻¹ * r)
    let e : X ≃ₜ X := ((Over.forget _).mapIso t).hom.homeomorph
    have he : e x = z := by
      have hp : p ≫ t.hom = r := by
        dsimp only [t]
        rw [section_comp_mulRight, mul_inv_cancel_left]
      have h := congrArg (fun a : (𝟙_ (SchemeOver k)) ⟶ G.X ↦ a.left (IsLocalRing.closedPoint k)) hp
      change e (p.left (IsLocalRing.closedPoint k)) = r.left (IsLocalRing.closedPoint k) at h
      have hpx : p.left (IsLocalRing.closedPoint k) = x := sectionOfClosedPoint_apply _ _ _
      have hrz : r.left (IsLocalRing.closedPoint k) = z := sectionOfClosedPoint_apply _ _ _
      exact (congrArg e hpx).symm.trans (h.trans hrz)
    have hcomponent (C : Set X) (hC : C ∈ irreducibleComponents X) :
        e.symm ⁻¹' C ∈ irreducibleComponents X :=
      preimage_mem_irreducibleComponents hC e.symm.isOpenEmbedding (by simpa using hC.1.nonempty)
    have ha := hz_only _ (hcomponent A hA) (by simpa [← he] using hx.1)
    have hb := hz_only _ (hcomponent B hB) (by simpa [← he] using hx.2)
    exact Set.preimage_injective.mpr e.symm.surjective (ha.trans hb.symm)
  have hVZ : V Z = Z := by
    apply le_antisymm
    · exact subset_closure.trans (hcl Z hZ).le
    · intro x hx
      change x ∉ ⋃₀ (irreducibleComponents X \ {Z})
      intro h
      obtain ⟨C, ⟨hC, hCZ⟩, hxC⟩ := Set.mem_sUnion.mp h
      exact hCZ (only_one C Z hC hZ ⟨x, hxC, hx⟩)
  have hclopen : IsClopen Z :=
    ⟨isClosed_of_mem_irreducibleComponents Z hZ, hVZ ▸ hV Z⟩
  have heq : Z = Set.univ := (isClopen_iff.mp hclopen).resolve_left hZ.1.nonempty.ne_empty
  apply (irreducibleSpace_def X).mpr
  change IsIrreducible (Set.univ : Set X)
  rw [← heq]
  exact hZ.1

private theorem irreducible_of_geometricallyConnected (G : Specs.GroupScheme k)
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [GeometricallyConnected G.X.hom] : IrreducibleSpace G.X.left := by
  let K := AlgebraicClosure k
  let G' := (groupBaseChange k K).obj G
  let a := fieldSpecMap k K
  have : LocallyOfFiniteType G'.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom a))
  have : QuasiCompact G'.X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom a))
  have : ConnectedSpace G'.X.left :=
    pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace K a
  have : IrreducibleSpace ↥(pullback G.X.hom a) := irreducible_of_connected_over_algClosed G'
  have : Surjective a := ⟨fun x ↦ ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  let p := pullback.fst G.X.hom a
  have hp : Surjective p := inferInstanceAs (Surjective (pullback.fst G.X.hom a))
  exact p.surjective.irreducibleSpace p.continuous

private theorem geometricallyIrreducible_of_connected (G : AffineAlgebraicGroup k)
    [ConnectedSpace G.val.X.left] : GeometricallyIrreducible G.val.X.hom := by
  have := G.property.2.1
  have := G.property.2.2
  have := geometricallyConnected_of_connected G
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} ↦ IrreducibleSpace X) (f := G.val.X.hom)).mpr
  intro K _ _
  let G' := (groupBaseChange k K).obj G.val
  let a := fieldSpecMap k K
  have : LocallyOfFiniteType G'.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.val.X.hom a))
  have : QuasiCompact G'.X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.val.X.hom a))
  have : GeometricallyConnected G'.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.val.X.hom a))
  exact irreducible_of_geometricallyConnected G'

private theorem smooth_geometricallyIrreducible_tensor (X Y : SchemeOver k)
    [Smooth X.hom] [Smooth Y.hom]
    [GeometricallyIrreducible X.hom] [GeometricallyIrreducible Y.hom] :
    Smooth (X ⊗ Y).hom ∧ GeometricallyIrreducible (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  let f := pullback.fst X.hom Y.hom
  have : Smooth f := inferInstanceAs (Smooth (pullback.fst X.hom Y.hom))
  exact ⟨inferInstanceAs (Smooth (f ≫ X.hom)), GeometricallyIrreducible.comp f X.hom⟩

private theorem geometry_of_smooth_geometricallyIrreducible (X : SchemeOver k)
    [Smooth X.hom] [GeometricallyIrreducible X.hom] :
    Smooth X.hom ∧ ConnectedSpace X.left ∧ IsIntegral X.left := by
  have : IrreducibleSpace X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton X.hom
  have : IsReduced X.left := isReduced_of_smooth_over_field X.hom
  exact ⟨inferInstance, inferInstance, isIntegral_of_irreducibleSpace_of_isReduced _⟩

theorem smoothConnectedGroupIntegral : Specs.WordDomainGeometry.SmoothConnectedGroupIntegral.{u} := by
  intro k _ _ G hsm hc
  have := geometricallyIrreducible_of_connected G
  exact (geometry_of_smooth_geometricallyIrreducible G.val.X).2.2

theorem smoothConnectedGroupProduct : Specs.WordDomainGeometry.SmoothConnectedGroupProduct.{u} := by
  intro k _ _ G H hg hgc hh hhc
  have := geometricallyIrreducible_of_connected G
  have := geometricallyIrreducible_of_connected H
  obtain ⟨hs, hi⟩ := smooth_geometricallyIrreducible_tensor G.val.X H.val.X
  exact geometry_of_smooth_geometricallyIrreducible (G.val.X ⊗ H.val.X)

private theorem smooth_geometricallyIrreducible_of_iso {X Y : SchemeOver k} (e : X ≅ Y)
    [Smooth Y.hom] [GeometricallyIrreducible Y.hom] :
    Smooth X.hom ∧ GeometricallyIrreducible X.hom := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  rw [← Over.w e.hom]
  refine ⟨inferInstance, ?_⟩
  rw [GeometricallyIrreducible.eq_geometrically]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (geometrically (fun Z : Scheme.{u} ↦ IrreducibleSpace Z)) e.hom.left Y.hom).mpr
    GeometricallyIrreducible.geometrically_irreducibleSpace

private def productOptionIso {I : Type u} [Finite I] (X : Option I → SchemeOver k) :
    (∏ᶜ X) ≅ X none ⊗ (∏ᶜ fun i ↦ X (some i)) := by
  let Y := ∏ᶜ fun i ↦ X (some i)
  let p (i : Option I) : X none ⊗ Y ⟶ X i :=
    match i with
    | none => fst _ _
    | some j => snd _ _ ≫ Pi.π (fun i ↦ X (some i)) j
  refine ⟨lift (Pi.π X none) (Pi.lift fun i ↦ Pi.π X (some i)), Pi.lift p, ?_, ?_⟩
  · apply Pi.hom_ext
    intro i
    cases i <;> simp [p, Y, Category.assoc]
  · apply CartesianMonoidalCategory.hom_ext
    · simp [p, Y]
    · apply Pi.hom_ext
      intro i
      simp [p, Y]

private theorem smooth_geometricallyIrreducible_product (I : Type u) [Finite I]
    (X : I → SchemeOver k) (hX : ∀ i, Smooth (X i).hom ∧ GeometricallyIrreducible (X i).hom) :
    Smooth (∏ᶜ X).hom ∧ GeometricallyIrreducible (∏ᶜ X).hom := by
  classical
  cases nonempty_fintype I
  revert X
  refine Fintype.induction_empty_option
    (P := fun I [Fintype I] ↦ ∀ (X : I → SchemeOver k),
      (∀ i, Smooth (X i).hom ∧ GeometricallyIrreducible (X i).hom) →
      Smooth (∏ᶜ X).hom ∧ GeometricallyIrreducible (∏ᶜ X).hom)
    ?_ ?_ ?_ I
  · intro α β _ e ih X hX
    have : Finite α := Finite.of_equiv β e.symm
    obtain ⟨hs, hi⟩ := ih (X ∘ e) (fun i ↦ hX (e i))
    exact smooth_geometricallyIrreducible_of_iso (Pi.reindex e X).symm
  · intro X _
    let e : (∏ᶜ X) ≅ 𝟙_ (SchemeOver k) :=
      ⟨toUnit _, Pi.lift (fun i ↦ PEmpty.elim i),
        Pi.hom_ext _ _ (fun i ↦ PEmpty.elim i), toUnit_unique _ _⟩
    have : Smooth (𝟙_ (SchemeOver k)).hom :=
      inferInstanceAs (Smooth (𝟙 (Spec (CommRingCat.of k))))
    have : GeometricallyIrreducible (𝟙_ (SchemeOver k)).hom := by
      change GeometricallyIrreducible (𝟙 (Spec (CommRingCat.of k)))
      constructor
      intro K _ a Y fst snd h
      have : IsIso snd := h.isIso_snd_of_isIso
      exact snd.homeomorph.irreducibleSpace_iff.mpr inferInstance
    exact smooth_geometricallyIrreducible_of_iso e
  · intro α _ ih X hX
    obtain ⟨hs, hi⟩ := hX none
    obtain ⟨ht, hj⟩ := ih (fun i ↦ X (some i)) (fun i ↦ hX (some i))
    obtain ⟨hsm, hir⟩ := smooth_geometricallyIrreducible_tensor
      (X none) (∏ᶜ fun i ↦ X (some i))
    exact smooth_geometricallyIrreducible_of_iso (productOptionIso X)

/-- Finite products of smooth connected affine algebraic groups are smooth,
connected and integral, including the empty product over the field. -/
theorem smoothConnectedGroupFiniteProduct :
    Specs.WordDomainGeometry.SmoothConnectedGroupFiniteProduct.{u} := by
  intro k _ _ I _ G hG
  let X (i : I) := (G i).val.X
  have hi (i : I) : Smooth (X i).hom ∧ GeometricallyIrreducible (X i).hom := by
    obtain ⟨hs, hc⟩ := hG i
    exact ⟨hs, geometricallyIrreducible_of_connected (G i)⟩
  obtain ⟨hs, hir⟩ := smooth_geometricallyIrreducible_product I X hi
  exact geometry_of_smooth_geometricallyIrreducible (∏ᶜ X)

private theorem exists_open_subset_of_dense_constructible {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] {s : Set T} (hc : IsConstructible s) (hd : Dense s) :
    ∃ U : Set T, IsOpen U ∧ U.Nonempty ∧ U ⊆ s := by
  classical
  have dichotomy : ∃ U : Set T, IsOpen U ∧ U.Nonempty ∧ (U ⊆ s ∨ U ⊆ sᶜ) := by
    clear hd
    induction hc using IsConstructible.empty_union_induction with
    | open_retrocompact U ho _ =>
      by_cases hn : U.Nonempty
      · exact ⟨U, ho, hn, Or.inl Set.Subset.rfl⟩
      · exact ⟨Set.univ, isOpen_univ, Set.univ_nonempty,
          Or.inr (by rw [Set.not_nonempty_iff_eq_empty.mp hn, Set.compl_empty])⟩
    | union s hs t ht h₁ h₂ =>
      obtain ⟨U, hU, hnU, hsubU⟩ := h₁
      obtain ⟨V, hV, hnV, hsubV⟩ := h₂
      rcases hsubU with hUs | hUs
      · exact ⟨U, hU, hnU, Or.inl (hUs.trans Set.subset_union_left)⟩
      rcases hsubV with hVt | hVt
      · exact ⟨V, hV, hnV, Or.inl (hVt.trans Set.subset_union_right)⟩
      exact ⟨U ∩ V, hU.inter hV, nonempty_preirreducible_inter hU hV hnU hnV,
        Or.inr (fun x hx h ↦ h.elim (hUs hx.1) (hVt hx.2))⟩
    | compl s hs ih =>
      obtain ⟨U, ho, hn, h⟩ := ih
      exact ⟨U, ho, hn, by simpa only [compl_compl] using h.symm⟩
  obtain ⟨U, ho, hn, hsub | hsub⟩ := dichotomy
  · exact ⟨U, ho, hn, hsub⟩
  · obtain ⟨x, hxU, hxs⟩ := hd.inter_open_nonempty U ho hn
    exact (hsub hxU hxs).elim

private theorem section_apply_isClosed [IsAlgClosed k] (X : SchemeOver k)
    [LocallyOfFiniteType X.hom] (p : (𝟙_ (SchemeOver k)) ⟶ X) :
    IsClosed {p.left (IsLocalRing.closedPoint k)} :=
  (pointEquivClosedPoint X.hom ⟨p.left, Over.w p⟩).2

private theorem exists_section_lift [IsAlgClosed k] {X Y : SchemeOver k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (q : (𝟙_ (SchemeOver k)) ⟶ Y)
    (hq : q.left (IsLocalRing.closedPoint k) ∈ Set.range f.left) :
    ∃ p : (𝟙_ (SchemeOver k)) ⟶ X, p ≫ f = q := by
  let z := q.left (IsLocalRing.closedPoint k)
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hclosed := (section_apply_isClosed Y q).preimage f.left.continuous
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints
    (show (f.left ⁻¹' {z}).Nonempty from hq) hclosed.isLocallyClosed
  let p := sectionOfClosedPoint X x hxc
  refine ⟨p, Over.OverMorphism.ext (ext_of_apply_closedPoint_eq Y.hom (Over.w (p ≫ f))
    (Over.w q) ?_)⟩
  change f.left (p.left (IsLocalRing.closedPoint k)) = z
  exact (congrArg (fun y ↦ f.left y) (sectionOfClosedPoint_apply X x hxc)).trans hx

theorem dominantImageGenerates : Specs.WordDomainGeometry.DominantImageGenerates.{u} := by
  intro k _ _ X _ _ _ Q _ _ f _ S hS
  have := Q.property.1
  have := Q.property.2.1
  have : LocallyOfFiniteType (f.left ≫ Q.val.X.hom) := (Over.w f).symm ▸ inferInstance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Q.val.X.hom
  have : IsLocallyNoetherian Q.val.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian Q.val.X.hom
  have : JacobsonSpace Q.val.X.left := LocallyOfFiniteType.jacobsonSpace Q.val.X.hom
  have hc : IsConstructible (Set.range f.left) := by
    rw [← Set.image_univ]
    exact f.left.isConstructible_image IsConstructible.univ
  obtain ⟨U, hU, hne, hsub⟩ := exists_open_subset_of_dense_constructible hc f.left.denseRange
  apply top_unique
  intro q _
  let t := GrpObj.mulRight q
  let a := t.hom.left
  have ha : Function.Surjective a := ((Over.forget _).mapIso t).hom.surjective
  have hopen : IsOpen (U ∩ a ⁻¹' U) := hU.inter (hU.preimage a.continuous)
  have hinter : (U ∩ a ⁻¹' U).Nonempty :=
    nonempty_preirreducible_inter hU (hU.preimage a.continuous) hne (hne.preimage ha)
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hinter hopen.isLocallyClosed
  let p := sectionOfClosedPoint Q.val.X z hzc
  have hp : p.left (IsLocalRing.closedPoint k) = z := sectionOfClosedPoint_apply _ _ _
  have hpa : (p ≫ t.hom).left (IsLocalRing.closedPoint k) = a z := by
    change a (p.left (IsLocalRing.closedPoint k)) = a z
    rw [hp]
  obtain ⟨x, hx⟩ := exists_section_lift f p (by rw [hp]; exact hsub hz.1)
  obtain ⟨y, hy⟩ := exists_section_lift f (p ≫ t.hom) (by rw [hpa]; exact hsub hz.2)
  have hpS : p ∈ S := hx ▸ hS x
  have hpqS : p * q ∈ S := section_comp_mulRight p q ▸ hy ▸ hS y
  simpa only [inv_mul_cancel_left] using S.mul_mem (S.inv_mem hpS) hpqS

end

end LinearAlgebraicGroups.WordDomainGeometry
