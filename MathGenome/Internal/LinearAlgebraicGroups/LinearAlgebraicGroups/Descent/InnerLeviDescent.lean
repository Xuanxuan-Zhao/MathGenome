import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.InnerLeviDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DerivedSubgroup
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Descent.InnerLeviDescent

open _root_.LinearAlgebraicGroups.Specs
open Specs.AutomorphismSequence
open Specs.RelativeFormComparison
open Specs.QuasiSplitInnerForms (AreInnerForms)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsReductive IsSplitReductive IsSplitTorus baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup IsSubgroupOf)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.InnerLeviDescent (MultiplicativeGroup)
open CocharacterDynamics (LimitDecomposition)

open private relativeYoneda relativeYonedaIso relativeSectionEquiv relativeSection_natural relativeInclusion
  relativeEvaluate restrict_innerAut innerAut_intertwines
  innerAut_mul groupSectionsMap_locallySurjective
  groupSections_isSheaf groupSectionsMap range_of_local_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

open private schemeIsoEquiv schemeIsoEquiv_trans schemeIsoEquiv_apply schemeIsoEquiv_ground
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison

open private centralizes_iff mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private productAlgebraicGroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 550000
set_option linter.style.haveILetI false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local notation "V" => fieldTest k K
local notation "E" => groupBaseChange k K

private theorem relativeYoneda_ground {G H : GroupScheme k} (i : G ⟶ H) :
    (relativeYoneda V).map ((E).map i) ≫ (relativeYonedaIso V H).hom =
      (relativeYonedaIso V G).hom ≫ relativeInclusion i V := by
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  exact relativeSection_natural U.unop i.hom.hom x

private theorem relativeIso_refl (G : GroupScheme k) :
    schemeIsoEquiv K G G (Iso.refl ((E).obj G)) = Iso.refl (relativePoints G V) := by
  let F := yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget V).op
  have h := schemeIsoEquiv_ground (S := K) (Iso.refl G)
  change schemeIsoEquiv K G G ((E).mapIso (Iso.refl G)) = F.mapIso (Iso.refl G) at h
  rw [Functor.mapIso_refl, Functor.mapIso_refl] at h
  exact h

private theorem conjugated_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A₁ B₁ A₂ B₂ : C} {P₁ Q₁ P₂ Q₂ : D}
    (yA₁ : F.obj A₁ ≅ P₁) (yB₁ : F.obj B₁ ≅ Q₁)
    (yA₂ : F.obj A₂ ≅ P₂) (yB₂ : F.obj B₂ ≅ Q₂)
    (i : A₁ ⟶ B₁) (j : A₂ ⟶ B₂) (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂)
    (i' : P₁ ⟶ Q₁) (j' : P₂ ⟶ Q₂)
    (hi : F.map i ≫ yB₁.hom = yA₁.hom ≫ i')
    (hj : F.map j ≫ yB₂.hom = yA₂.hom ≫ j')
    (h : i ≫ b = a ≫ j) :
    i' ≫ (yB₁.inv ≫ F.map b ≫ yB₂.hom) =
      (yA₁.inv ≫ F.map a ≫ yA₂.hom) ≫ j' := by
  have hi' : i' = yA₁.inv ≫ F.map i ≫ yB₁.hom := by
    rw [hi, Iso.inv_hom_id_assoc]
  rw [hi']
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← hj, ← F.map_comp_assoc, h]

private theorem relative_square {A B C D : GroupScheme k} (i : A ⟶ B) (j : C ⟶ D)
    (a : (E).obj A ≅ (E).obj C) (b : (E).obj B ≅ (E).obj D)
    (h : (E).map i ≫ b.hom = a.hom ≫ (E).map j) :
    relativeInclusion i V ≫ (schemeIsoEquiv K B D b).hom =
      (schemeIsoEquiv K A C a).hom ≫ relativeInclusion j V :=
  conjugated_square (relativeYoneda V) (relativeYonedaIso V A) (relativeYonedaIso V B)
    (relativeYonedaIso V C) (relativeYonedaIso V D) ((E).map i) ((E).map j) a.hom b.hom
    (relativeInclusion i V) (relativeInclusion j V) (relativeYoneda_ground i)
    (relativeYoneda_ground j) h

private theorem restrict_square {A B C D : GroupScheme k} {X Y : SchemeOver k}
    (i : A ⟶ B) (j : C ⟶ D)
    (a : relativePoints A X ≅ relativePoints C X)
    (b : relativePoints B X ≅ relativePoints D X)
    (h : relativeInclusion i X ≫ b.hom = a.hom ≫ relativeInclusion j X)
    (p : Y ⟶ X) :
    relativeInclusion i Y ≫ (restrictIso p b).hom =
      (restrictIso p a).hom ≫ relativeInclusion j Y := by
  apply NatTrans.ext
  funext U
  exact NatTrans.congr_app h (op ((Over.map p).obj U.unop))

private theorem displacement_square {A B C D : GroupScheme k} (i : A ⟶ B) (j : C ⟶ D)
    (a : relativePoints A V ≅ relativePoints C V)
    (b : relativePoints B V ≅ relativePoints D V)
    (h : relativeInclusion i V ≫ b.hom = a.hom ≫ relativeInclusion j V)
    (σ : Gal(K/k)) :
    relativeInclusion i V ≫ (transportedAut k K b σ).asIso.hom =
      (transportedAut k K a σ).asIso.hom ≫ relativeInclusion i V := by
  have hi : relativeInclusion j V ≫ b.inv = a.inv ≫ relativeInclusion i V := by
    have hh := congrArg (fun f => a.inv ≫ f ≫ b.inv) h
    simpa only [Category.assoc, b.hom_inv_id, Category.comp_id, a.inv_hom_id_assoc] using hh.symm
  change relativeInclusion i V ≫ (restrictIso (fieldMap k K σ) b).hom ≫ b.inv =
    ((restrictIso (fieldMap k K σ) a).hom ≫ a.inv) ≫ relativeInclusion i V
  rw [← Category.assoc, restrict_square i j a b h, Category.assoc, hi, Category.assoc]

private theorem displacement_fixes {G H : GroupScheme k} (c : Cocharacter G)
    (d : Cocharacter H) (b : relativePoints G V ≅ relativePoints H V)
    (h : relativeInclusion c V ≫ b.hom = relativeInclusion d V) (σ : Gal(K/k)) :
    relativeInclusion c V ≫ (transportedAut k K b σ).asIso.hom = relativeInclusion c V := by
  have hs := restrict_square c d (Iso.refl (relativePoints (MultiplicativeGroup k) V)) b
    (h.trans (Category.id_comp _).symm) (fieldMap k K σ)
  change relativeInclusion c V ≫ (restrictIso (fieldMap k K σ) b).hom ≫ b.inv =
    relativeInclusion c V
  rw [← Category.assoc, hs, ← h]
  change ((𝟙 _) ≫ (relativeInclusion c V ≫ b.hom)) ≫ b.inv = relativeInclusion c V
  rw [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem centralizes_of_local_conjugation_fixes {G J : GroupScheme k}
    {X : SchemeOver k} (c : J ⟶ G) (g : X ⟶ G.X)
    (h : relativeInclusion c X ≫ (innerAut g).asIso.hom = relativeInclusion c X) :
    Centralizes c g := by
  apply (centralizes_iff c g).mpr
  intro Y y t
  have he := congrArg (fun f => relativeEvaluate f (Over.mk y) t) h
  change (y ≫ g) * (t ≫ c.hom.hom) * (y ≫ g)⁻¹ = t ≫ c.hom.hom at he
  exact (commute_iff_eq _ _).2 (mul_inv_eq_iff_eq_mul.mp he)

private theorem relativeInclusion_mono {G H : GroupScheme k} (i : H ⟶ G) [Mono i.hom.hom]
    (X : SchemeOver k) : Mono (relativeInclusion i X) := by
  have hm (U : (Over X)ᵒᵖ) : Mono ((relativeInclusion i X).app U) := by
    apply (GrpCat.mono_iff_injective _).mpr
    intro x y h
    exact (cancel_mono i.hom.hom).mp h
  exact NatTrans.mono_of_mono_app _

private theorem inner_on_derived_of_centralizer_point {G : AffineAlgebraicGroup k}
    (H : ClosedSubgroup G.val) (Q : AdjointQuotient (closedSubgroupAlgebraicGroup H))
    (inn : groupSections Q.quotient.val ⟶ automorphisms H.group)
    (hlift : ∀ (U : SchemeOver k) (g : U ⟶ H.group.X),
      inn.app (op U) ⟨g ≫ Q.projection.hom.hom⟩ = innerAut g)
    (hinj : ∀ U, Function.Injective (inn.app U))
    (Z : ClosedSubgroup G.val) (hZ : Specs.CentralTorus.IsSchemeCentre Z)
    (T : ClosedSubgroup Z.group)
    (m : (T.group ⊗ H.group) ⟶ G.val) (hm : Specs.CentralDerived.IsCentralProduct T H m)
    (hmf : Specs.Fppf.IsFppf m.hom.hom.left)
    {X : SchemeOver k} (g : X ⟶ G.val.X) (b : RelativeAut H.group X)
    (hb : relativeInclusion H.inclusion X ≫ (innerAut g).asIso.hom =
      b.asIso.hom ≫ relativeInclusion H.inclusion X) :
    b ∈ (inn.app (op X)).hom.range := by
  let p := groupSectionsMap m
  letI := groupSectionsMap_locallySurjective m hmf
  let gx : (groupSections G.val).obj (op X) := ⟨g⟩
  refine range_of_local_sections (i := inn) (U := X) (groupSections_isSheaf Q.quotient.val)
    hinj b (AutomorphismSequence.automorphisms_isSheaf H.group)
      (Presheaf.imageSieve_mem (Specs.Fppf.schemeTopology k) p gx) ?_
  rintro Y a ⟨x, hx⟩
  let z := x.down ≫ (fst T.group H.group).hom.hom ≫ T.inclusion.hom.hom
  let t := x.down ≫ (snd T.group H.group).hom.hom
  have hx' : x.down ≫ m.hom.hom = a ≫ g := ULift.up_inj.mp hx
  have hprod : a ≫ g = (z ≫ Z.inclusion.hom.hom) * (t ≫ H.inclusion.hom.hom) := by
    rw [← hx', hm, MonObj.comp_mul]
    rfl
  have hz : innerAut (z ≫ Z.inclusion.hom.hom) = 1 :=
    (AutomorphismSequence.innerAut_eq_one_iff _).mpr ((hZ _ _).2 ⟨z, rfl⟩)
  have ha : restrictAut a (innerAut g) = innerAut (t ≫ H.inclusion.hom.hom) := by
    rw [restrict_innerAut, hprod, innerAut_mul, hz, one_mul]
  have he := restrict_square H.inclusion H.inclusion b.asIso (innerAut g).asIso hb a
  change relativeInclusion H.inclusion Y ≫ (restrictAut a (innerAut g)).asIso.hom =
    (restrictAut a b).asIso.hom ≫ relativeInclusion H.inclusion Y at he
  rw [ha, innerAut_intertwines] at he
  haveI : Mono H.inclusion.hom.hom := mono_over _ H.isClosedImmersion
  letI := relativeInclusion_mono H.inclusion Y
  have he' : innerAut t = restrictAut a b :=
    Aut.ext (Iso.ext ((cancel_mono (relativeInclusion H.inclusion Y)).mp he))
  exact ⟨⟨t ≫ Q.projection.hom.hom⟩, (hlift Y t).trans he'⟩

private theorem inner_on_derived {G : AffineAlgebraicGroup k} {c : Cocharacter G.val}
    (L : LimitDecomposition c) (hL : IsReductive (closedSubgroupAlgebraicGroup L.centralizer))
    (H : ClosedSubgroup L.centralizer.group) (hH : IsDerivedSubgroup H)
    (QG : AdjointQuotient G) (innG : groupSections QG.quotient.val ⟶ automorphisms G.val)
    (hliftG : ∀ (U : SchemeOver k) (g : U ⟶ G.val.X),
      innG.app (op U) ⟨g ≫ QG.projection.hom.hom⟩ = innerAut g)
    (QH : AdjointQuotient
      (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L.centralizer) H))
    (innH : groupSections QH.quotient.val ⟶ automorphisms H.group)
    (hliftH : ∀ (U : SchemeOver k) (g : U ⟶ H.group.X),
      innH.app (op U) ⟨g ≫ QH.projection.hom.hom⟩ = innerAut g)
    (hinjH : ∀ U, Function.Injective (innH.app U))
    {X : SchemeOver k} (a : RelativeAut G.val X) (b : RelativeAut H.group X)
    (ha : a ∈ (innG.app (op X)).hom.range)
    (hc : relativeInclusion c X ≫ a.asIso.hom = relativeInclusion c X)
    (hb : relativeInclusion (H.inclusion ≫ L.centralizer.inclusion) X ≫ a.asIso.hom =
      b.asIso.hom ≫ relativeInclusion (H.inclusion ≫ L.centralizer.inclusion) X) :
    b ∈ (innH.app (op X)).hom.range := by
  obtain ⟨q, hq⟩ := ha
  let G' := closedSubgroupAlgebraicGroup L.centralizer
  obtain ⟨Z, hZ, T, hT, _⟩ := Reductive.CentralDerived.centralTorusExists G' hL
  obtain ⟨m, hm, _⟩ := Reductive.CentralDerived.centralProductKernel G' hL Z hZ T hT H hH
  obtain ⟨hmf, hms⟩ :=
    Reductive.CentralDerived.centralProductFaithfullyFlat G' hL Z hZ T hT H hH m hm
  have hmfp : Specs.Fppf.IsFppf m.hom.hom.left := by
    refine ⟨hmf, hms, ?_⟩
    have : LocallyOfFiniteType G'.val.X.hom := G'.property.2.1
    have : IsLocallyNoetherian G'.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G'.val.X.hom
    haveI : LocallyOfFiniteType (T.group ⊗ H.group).X.hom :=
      (productAlgebraicGroup
        (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup (G := G') Z) T)
        (closedSubgroupAlgebraicGroup (G := G') H)).property.2.1
    have : LocallyOfFiniteType (m.hom.hom.left ≫ G'.val.X.hom) := by
      rwa [Over.w]
    exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
      (locallyOfFiniteType_of_comp m.hom.hom.left G'.val.X.hom)
  let p := groupSectionsMap QG.projection
  letI := groupSectionsMap_locallySurjective QG.projection QG.fppf
  refine range_of_local_sections (i := innH) (U := X) (groupSections_isSheaf QH.quotient.val)
    hinjH b (AutomorphismSequence.automorphisms_isSheaf H.group)
      (Presheaf.imageSieve_mem (Specs.Fppf.schemeTopology k) p q) ?_
  rintro Y y ⟨g, hg⟩
  have hg' : g.down ≫ QG.projection.hom.hom = y ≫ q.down := ULift.up_inj.mp hg
  have hal : restrictAut y a = innerAut g.down := by
    rw [← hq]
    change (automorphisms G.val).map y.op (innG.app (op X) q) = _
    rw [← NatTrans.naturality_apply innG]
    change innG.app (op Y) ⟨y ≫ q.down⟩ = _
    rw [← hg', hliftG]
  have hcy := restrict_square c c (Iso.refl (relativePoints (MultiplicativeGroup k) X))
    a.asIso (hc.trans (Category.id_comp _).symm) y
  change relativeInclusion c Y ≫ (restrictAut y a).asIso.hom =
    𝟙 _ ≫ relativeInclusion c Y at hcy
  rw [hal, Category.id_comp] at hcy
  obtain ⟨s, hs⟩ := (L.centralizer_points Y g.down).mp
    (centralizes_of_local_conjugation_fixes c g.down hcy)
  have hby := restrict_square (H.inclusion ≫ L.centralizer.inclusion)
    (H.inclusion ≫ L.centralizer.inclusion) b.asIso a.asIso hb y
  change _ ≫ (restrictAut y a).asIso.hom = (restrictAut y b).asIso.hom ≫ _ at hby
  rw [hal, ← hs] at hby
  let j := relativeInclusion L.centralizer.inclusion Y
  let d := relativeInclusion H.inclusion Y
  have hcomp : relativeInclusion (H.inclusion ≫ L.centralizer.inclusion) Y = d ≫ j :=
    (yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget Y).op).map_comp
      H.inclusion L.centralizer.inclusion
  haveI : Mono L.centralizer.inclusion.hom.hom := mono_over _ L.centralizer.isClosedImmersion
  letI : Mono j := relativeInclusion_mono L.centralizer.inclusion Y
  have hrestrict : d ≫ (innerAut s).asIso.hom = (restrictAut y b).asIso.hom ≫ d := by
    apply (cancel_mono j).mp
    rw [Category.assoc d, ← innerAut_intertwines L.centralizer.inclusion s, ← Category.assoc d,
      ← hcomp, Category.assoc, ← hcomp]
    exact hby
  change restrictAut y b ∈ (innH.app (op Y)).hom.range
  exact inner_on_derived_of_centralizer_point (G := G') H QH innH hliftH hinjH Z hZ T m hm hmfp
    (X := Y) s (restrictAut y b) hrestrict

open private isTorus_of_split splitPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private splitTorus_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SplitToriConjugacy
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private subgroupOf_of_extend extend_subgroupOf extendSubgroup subgroupIso_of_same
  same_subgroup_of_same_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private maximalTransport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private liftSplitCocharacter from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open private innerIso innerMap comp_innerMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private relativeSectionGroupEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open private gm_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private splitOfClosedTorus derivedSubgroupOfIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies

open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups)
open Specs.GeometricRadicals (IsTorus)

private theorem maximalSplit_of_geometric {G : GroupScheme k} (T : ClosedSubgroup G)
    (hs : IsSplitTorus T.group) (hT : IsGeometricallyMaximal T) :
    IsMaximalSplitTorus T := by
  refine ⟨hs, fun U hu htu => ?_⟩
  obtain ⟨ht, hmax⟩ := hT
  exact subgroupOf_of_extend (K := AlgebraicClosure k)
    (hmax.2 (extendSubgroup (AlgebraicClosure k) U)
      (isTorus_of_split (splitTorus_baseChange hu)) (extend_subgroupOf htu))

private theorem maximalSplit_baseChange (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) (hT : IsGeometricallyMaximal T) :
    IsMaximalSplitTorus (extendSubgroup K T) := by
  have hcent := Reductive.TorusCentralizer.maximalTorusCentralizer G hG T (isTorus_of_split hs) hT
  obtain ⟨hc, hC⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange k K T.inclusion T hcent
  refine ⟨splitTorus_baseChange hs, ?_⟩
  intro U hU hTU
  obtain ⟨j, hj⟩ := hTU
  have hcomm : Centralizes ((E).map T.inclusion) U.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro X p s
    have hcomm : IsCommMonObj U.group.X :=
      torus_commutative (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup K G) U)
        (isTorus_of_split hU)
    change j ≫ U.inclusion = (E).map T.inclusion at hj
    rw [← hj]
    letI := (isCommMonObj_iff_isMulCommutative _).mp hcomm X
    exact (Commute.all p (s ≫ j.hom.hom)).map (IsMonHom.monoidHom U.inclusion.hom.hom X)
  obtain ⟨p, hp⟩ := (hC _ _).mp hcomm
  exact factor_group_through_subgroup (extendSubgroup K T) U.inclusion p hp

private theorem relativeInnerIso {G : GroupScheme k}
    (g : 𝟙_ (SchemeOver K) ⟶ ((E).obj G).X) :
    ∃ q : V ⟶ G.X, (schemeIsoEquiv K G G (innerIso g)) = (innerAut q).asIso := by
  let U₀ : Over V := Over.mk (𝟙 V)
  let q := relativeSectionEquiv U₀ G.X (toUnit _ ≫ g)
  refine ⟨q, ?_⟩
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  change U.unop.left ⟶ G.X at x
  let b := relativeSectionGroupEquiv U.unop G
  let p := b.symm x
  have hpoint : b (toUnit _ ≫ g) = U.unop.hom ≫ q := by
    let f : U.unop ⟶ U₀ := Over.homMk U.unop.hom (Category.comp_id _)
    let p₀ : (Over.iteratedSliceForward V).obj U₀ ⟶ ((E).obj G).X := toUnit _ ≫ g
    have he := ConcreteCategory.congr_hom ((relativeYonedaIso V G).hom.naturality f.op) p₀
    change b (((Over.iteratedSliceForward V).map f) ≫ (toUnit _ ≫ g)) =
      U.unop.hom ≫ q at he
    simpa only [← Category.assoc, comp_toUnit] using he
  change b (p ≫ (innerMap g).hom.hom) =
    (U.unop.hom ≫ q) * x * (U.unop.hom ≫ q)⁻¹
  rw [comp_innerMap, map_mul, map_mul, map_inv, hpoint, MulEquiv.apply_symm_apply]

private theorem inner_after_adjustment {G H : AffineAlgebraicGroup k}
    (Q : AdjointQuotient G) (inn : groupSections Q.quotient.val ⟶ automorphisms G.val)
    (hlift : ∀ (U : SchemeOver k) (g : U ⟶ G.val.X),
      inn.app (op U) ⟨g ≫ Q.projection.hom.hom⟩ = innerAut g)
    (i : relativePoints G.val V ≅ relativePoints H.val V)
    (hi : ∀ σ, transportedAut k K i σ ∈ (inn.app (op V)).hom.range)
    (g : 𝟙_ (SchemeOver K) ⟶ ((E).obj G.val).X)
    (σ : Gal(K/k)) :
    transportedAut k K (schemeIsoEquiv K G.val G.val (innerIso g) ≪≫ i) σ ∈
      (inn.app (op V)).hom.range := by
  obtain ⟨q, hq⟩ := relativeInnerIso g
  rw [hq, QuasiSplitInnerForms.changeOfTrivialization i (innerAut q) σ]
  let B := (inn.app (op V)).hom.range
  have hb : innerAut q ∈ B := ⟨⟨q ≫ Q.projection.hom.hom⟩, hlift V q⟩
  have hs : automorphismAction k K G.val σ (innerAut q) ∈ B := by
    change restrictAut (fieldMap k K σ) (innerAut q) ∈ B
    rw [restrict_innerAut]
    exact ⟨_, hlift V _⟩
  exact B.mul_mem (B.mul_mem (B.inv_mem hb) (hi σ)) hs

private theorem centralizes_transport {G J A : GroupScheme k} (e : G ≅ J) (c : A ⟶ G)
    {X : SchemeOver k} (x : X ⟶ G.X) :
    Centralizes (c ≫ e.hom) (x ≫ e.hom.hom.hom) ↔ Centralizes c x := by
  rw [centralizes_iff, centralizes_iff]
  constructor
  · intro h Y y t
    apply (commute_iff_eq _ _).mpr
    apply (cancel_mono e.hom.hom.hom).mp
    simp only [MonObj.mul_comp, Category.assoc]
    exact (h Y y t).eq
  · intro h Y y t
    have hm := (h Y y t).map (IsMonHom.monoidHom e.hom.hom.hom Y)
    change Commute ((y ≫ x) ≫ e.hom.hom.hom) ((t ≫ c.hom.hom) ≫ e.hom.hom.hom) at hm
    change Commute (y ≫ x ≫ e.hom.hom.hom) (t ≫ c.hom.hom ≫ e.hom.hom.hom)
    simpa only [Category.assoc] using hm

private theorem transported_centralizer {G J A : GroupScheme k}
    (e : G ≅ J) (c : A ⟶ G) (C : ClosedSubgroup G)
    (hC : RepresentsSubgroup C (fun _ x => Centralizes c x)) :
    RepresentsSubgroup (transportSubgroup e C) (fun _ x => Centralizes (c ≫ e.hom) x) := by
  intro X x
  have hx : (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x := by
    let F := Grp.forget (SchemeOver k)
    change (x ≫ F.map e.inv) ≫ F.map e.hom = x
    rw [Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id]
    exact Category.comp_id (Y := J.X) x
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (hC X _).mp
      ((centralizes_transport e c (x ≫ e.inv.hom.hom)).mp (hx.symm ▸ h))
    refine ⟨z, ?_⟩
    change z ≫ C.inclusion.hom.hom ≫ e.hom.hom.hom = x
    rw [← Category.assoc, hz, hx]
  · rintro ⟨z, rfl⟩
    exact (centralizes_transport e c (z ≫ C.inclusion.hom.hom)).mpr
      ((hC X _).mpr ⟨z, rfl⟩)

private theorem aligned_cocharacter (G₀ : AffineAlgebraicGroup k) (hG₀ : IsReductive G₀)
    (T₀ : ClosedSubgroup G₀.val) (hs₀ : IsSplitTorus T₀.group) (hm₀ : IsGeometricallyMaximal T₀)
    {G : GroupScheme k} (a : (E).obj G₀.val ≅ (E).obj G) (c : Cocharacter G)
    (T : ClosedSubgroup ((E).obj G)) (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (t : (E).obj (MultiplicativeGroup k) ⟶ T.group) (ht : t ≫ T.inclusion = (E).map c) :
    ∃ (g : 𝟙_ (SchemeOver K) ⟶ ((E).obj G₀.val).X) (c₀ : Cocharacter T₀.group),
      (E).map (c₀ ≫ T₀.inclusion) ≫ (innerIso g ≪≫ a).hom = (E).map c := by
  let G₀K := baseChangedAlgebraicGroup K G₀
  let U₀ := extendSubgroup K T₀
  let U := transportSubgroup a.symm T
  have hG₀K : IsReductive G₀K := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) G₀ hG₀.1 hG₀.2.1).mpr hG₀
  have hU : IsMaximalSplitTorus U := maximalSplit_of_geometric U hs (maximalTransport a.symm T hm)
  obtain ⟨g, f, hf⟩ := Relative.MaximalSplitTori.maximalSplitToriConjugate
    G₀K hG₀K U₀ U (maximalSplit_baseChange G₀ hG₀ T₀ hs₀ hm₀) hU
  obtain ⟨m, _⟩ := gm_baseChange k K
  obtain ⟨n, ⟨j⟩⟩ := splitPresentation hs₀
  obtain ⟨c₀, hc₀⟩ := liftSplitCocharacter K j m (m.hom ≫ t ≫ f.inv)
  have hc₀' : (E).map c₀ = t ≫ f.inv := (cancel_epi m.hom).mp hc₀
  have hsquare : (E).map T₀.inclusion ≫ (innerIso g).hom = f.hom ≫ U.inclusion := by
    apply Grp.hom_ext
    exact (comp_innerMap g U₀.inclusion.hom.hom).trans hf.symm
  refine ⟨g, c₀, ?_⟩
  change (E).map (c₀ ≫ T₀.inclusion) ≫ (innerIso g).hom ≫ a.hom = _
  rw [(E).map_comp, Category.assoc, ← Category.assoc ((E).map T₀.inclusion), hsquare, hc₀']
  change (t ≫ f.inv) ≫ (f.hom ≫ T.inclusion ≫ a.inv) ≫ a.hom = _
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, a.inv_hom_id, Category.comp_id] using ht

private theorem compare_centralizers (G₀ G : AffineAlgebraicGroup k)
    (c₀ : Cocharacter G₀.val) (c : Cocharacter G.val)
    (L₀ : LimitDecomposition c₀) (L : LimitDecomposition c)
    (a : (E).obj G₀.val ≅ (E).obj G.val) (ha : (E).map c₀ ≫ a.hom = (E).map c) :
    ∃ b : (E).obj L₀.centralizer.group ≅ (E).obj L.centralizer.group,
      (E).map L₀.centralizer.inclusion ≫ a.hom = b.hom ≫ (E).map L.centralizer.inclusion := by
  obtain ⟨h₀, hC₀⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange k K c₀
    L₀.centralizer L₀.centralizer_points
  obtain ⟨h, hC⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange k K c
    L.centralizer L.centralizer_points
  have hC₀' := transported_centralizer a ((E).map c₀)
    (baseChangedSubgroup K L₀.centralizer h₀) hC₀
  rw [ha] at hC₀'
  obtain ⟨b, hb⟩ := subgroupIso_of_same
    (same_subgroup_of_same_sections (H := baseChangedAlgebraicGroup K G) hC₀' hC)
  exact ⟨b, hb.symm⟩

private theorem compare_derived (L₀ L : AffineAlgebraicGroup k)
    (hL₀ : IsReductive L₀) (hL : IsReductive L)
    (H₀ : ClosedSubgroup L₀.val) (hH₀ : IsDerivedSubgroup H₀)
    (H : ClosedSubgroup L.val) (hH : IsDerivedSubgroup H)
    (b : (E).obj L₀.val ≅ (E).obj L.val) :
    ∃ d : (E).obj H₀.group ≅ (E).obj H.group,
      (E).map H₀.inclusion ≫ b.hom = d.hom ≫ (E).map H.inclusion := by
  obtain ⟨hc, hd, _⟩ := Reductive.DerivedSubgroup.derivedSubgroupBaseChange K L₀ H₀ hH₀
    hL₀.1 hL₀.2.1
  obtain ⟨_, _, hu⟩ := Reductive.DerivedSubgroup.derivedSubgroupBaseChange K L H hH
    hL.1 hL.2.1
  let P := transportSubgroup b (baseChangedSubgroup K H₀ hc)
  obtain ⟨e, he⟩ := hu P (derivedSubgroupOfIso b (baseChangedSubgroup K H₀ hc) hd)
  refine ⟨e.symm, ?_⟩
  change P.inclusion = e.inv ≫ (E).map H.inclusion
  rw [← he, Iso.inv_hom_id_assoc]

/-- A derived cocharacter centralizer in an inner form is inner to the
derived centralizer of a matching cocharacter in the split reference. -/
theorem innerLeviDescent : Specs.InnerLeviDescent.Statement.{u} := by
  intro F _ B G₀ G hG₀ hG hinner c L hL H hH T hs hm ht
  obtain ⟨T₀, hs₀, hm₀⟩ := hG₀.2
  obtain ⟨QG, innG, hliftG, _, j, hj⟩ := hinner
  let K := SeparableClosure F
  obtain ⟨a, ha⟩ := (schemeIsoEquiv K G₀.val G.val).surjective j
  obtain ⟨t, ht⟩ := ht
  obtain ⟨g, c₀, hc₀⟩ := aligned_cocharacter G₀ hG₀.1 T₀ hs₀ hm₀ a c T hs hm t ht
  let a' := innerIso g ≪≫ a
  let j' := schemeIsoEquiv K G₀.val G.val a'
  have hinner' (σ : Gal(K/F)) :
      transportedAut F K j' σ ∈ (innG.app (op (fieldTest F K))).hom.range := by
    change transportedAut F K (schemeIsoEquiv K G₀.val G.val (innerIso g ≪≫ a)) σ ∈ _
    rw [schemeIsoEquiv_trans, ha]
    exact inner_after_adjustment QG innG hliftG j hj g σ
  obtain ⟨L₀, H₀, hL₀, hH₀, hss₀⟩ :=
    Arithmetic.QuasiSplitOrbitLevis.derivedLeviFromRationalCocharacter G₀ T₀ hG₀.1
      (isTorus_of_split hs₀) hm₀ c₀
  obtain ⟨U, iU, _, hiU, hU, hUm, _⟩ :=
    Arithmetic.QuasiSplitOrbitLevis.rationalDerivedLeviTorus G₀ T₀ (isTorus_of_split hs₀) hm₀
      c₀ L₀ hL₀ H₀ hH₀
  let D₀ := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L₀.centralizer) H₀
  have hsplit : IsSplitReductive D₀ :=
    ⟨reductive_of_semisimple D₀ hss₀, U,
      splitOfClosedTorus (closedSubgroupAlgebraicGroup (G := D₀) U) hU hs₀ iU hiU, hUm⟩
  obtain ⟨b, hb⟩ := compare_centralizers G₀ G (c₀ ≫ T₀.inclusion) c L₀ L a' hc₀
  obtain ⟨d, hd⟩ := compare_derived (K := K)
    (closedSubgroupAlgebraicGroup L₀.centralizer) (closedSubgroupAlgebraicGroup L.centralizer)
      hL₀ hL H₀ hH₀ H hH b
  obtain ⟨QH⟩ := AutomorphismSequence.adjointQuotient_exists D₀
  obtain ⟨innH, hliftH, hinjH⟩ := AutomorphismSequence.adjointInner D₀ QH
  let jH := schemeIsoEquiv K H₀.group H.group d
  refine ⟨c₀ ≫ T₀.inclusion, L₀, H₀, hL₀, hH₀, hsplit, a', b, d, hc₀, hb, hd,
    QH, innH, hliftH, hinjH, jH, schemeIsoEquiv_apply d, ?_⟩
  intro σ
  apply inner_on_derived L₀ hL₀ H₀ hH₀ QG innG hliftG QH innH hliftH hinjH
    (transportedAut F K j' σ) (transportedAut F K jH σ) (hinner' σ)
  · apply displacement_fixes (c₀ ≫ T₀.inclusion) c j' ?_ σ
    have h := relative_square (c₀ ≫ T₀.inclusion) c (Iso.refl _) a'
      (hc₀.trans (Category.id_comp _).symm)
    rw [relativeIso_refl] at h
    exact h.trans (Category.id_comp _)
  · apply displacement_square (H₀.inclusion ≫ L₀.centralizer.inclusion)
      (H.inclusion ≫ L.centralizer.inclusion) jH j' ?_ σ
    apply relative_square _ _ d a'
    rw [B.map_comp, B.map_comp, Category.assoc, hb, ← Category.assoc, hd, Category.assoc]

end

end LinearAlgebraicGroups.Descent.InnerLeviDescent
