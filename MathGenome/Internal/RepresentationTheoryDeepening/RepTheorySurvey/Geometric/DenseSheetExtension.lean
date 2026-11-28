import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DenseSheetExtension
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Limits.Connected

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

namespace RepTheorySurvey.Geometric.DenseSheetExtension

open Analytic DenseSheetExtensionSpecs

open private stalkPushforward_naturality inverseDirectUnit_stalk_isIso
  from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

set_option backward.isDefEq.respectTransparency false

private theorem dense_distinctMarks : Dense {p : MarkedPlane | p.1 ≠ p.2} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨p, hp⟩
  have hV : IsOpen ((fun z : ℂ ↦ (p.1, z)) ⁻¹' U) :=
    hU.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨z, hzU, hz⟩ := (dense_compl_singleton p.1).inter_open_nonempty _ hV ⟨p.2, hp⟩
  exact ⟨(p.1, z), hzU, fun e ↦ hz e.symm⟩

private def constantSection {X : TopCat.{0}} (M : Coeff.{0}) :
    M ⟶ (constant X M).obj.obj (op ⊤) :=
  (toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj M)).app (op ⊤)

private theorem constantSection_germ_isIso {X : TopCat.{0}} (M : Coeff.{0}) (x : X) :
    IsIso (constantSection M ≫ (constant X M).presheaf.Γgerm x) := by
  let P : X.Presheaf Coeff.{0} := (Functor.const (Opens X)ᵒᵖ).obj M
  let η := toSheafify (Opens.grothendieckTopology X) P
  have htop : x ∈ (⊤ : Opens X) := trivial
  have hη := TopCat.Presheaf.stalkFunctor_map_germ (⊤ : Opens X) x htop η
  erw [← hη]
  let D := (OpenNhds.inclusion x).op ⋙ P
  let c : Cocone D := constCocone (OpenNhds x)ᵒᵖ M
  let hc : IsColimit c := isColimitConstCocone _ _
  let e := hc.coconePointUniqueUpToIso (colimit.isColimit D)
  have he : e.hom = P.germ ⊤ x trivial := by
    have hi := hc.comp_coconePointUniqueUpToIso_hom (colimit.isColimit D) (op ⟨⊤, htop⟩)
    change 𝟙 M ≫ e.hom = P.germ ⊤ x htop at hi
    simpa only [Category.id_comp] using hi
  rw [← he]
  have : IsIso ((TopCat.Presheaf.stalkFunctor Coeff.{0} x).map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ P
  infer_instance

/-- A germ of a section of a constant sheaf is represented on a neighbourhood
by a constant global section. -/
private theorem constantSection_locally {X : TopCat.{0}} (M : Coeff.{0}) (U : Opens X)
    (s : (constant X M).obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : x ∈ V) (i : V ⟶ U) (m : M),
      ∀ (y : X) (hy : y ∈ V), (constant X M).presheaf.germ U y (i.le hy) s =
        (constant X M).presheaf.Γgerm y (constantSection M m) := by
  let P := (constant X M).presheaf
  let g := constantSection M ≫ P.Γgerm x
  have : IsIso g := constantSection_germ_isIso M x
  let m := inv g (P.germ U x hx s)
  have hm : P.germ U x hx s = P.Γgerm x (constantSection M m) := by
    change P.germ U x hx s = g (inv g (P.germ U x hx s))
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
  obtain ⟨V, hxV, i, j, h⟩ := P.germ_eq x hx (show x ∈ (⊤ : Opens X) from trivial)
    s (constantSection M m) hm
  refine ⟨V, hxV, i, m, fun y hy ↦ ?_⟩
  rw [← P.germ_res_apply i y hy s, h, P.Γgerm_res_apply]

private theorem constant_hom_ext_of_dense {X : TopCat.{0}} {D : Set X} (hD : Dense D)
    (M : Coeff.{0}) {G : Sheaves X} {u v : G ⟶ constant X M}
    (h : ∀ x ∈ D, (stalk x).map u = (stalk x).map v) : u = v := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply TopCat.Presheaf.section_ext (constant X M) (unop U)
  intro x hx
  obtain ⟨V, hxV, i, m, hm⟩ := constantSection_locally M (unop U) (u.hom.app U s) x hx
  obtain ⟨W, hxW, j, n, hn⟩ := constantSection_locally M (unop U) (v.hom.app U s) x hx
  obtain ⟨y, ⟨hyV, hyW⟩, hyD⟩ :=
    hD.inter_open_nonempty _ (V.isOpen.inter W.isOpen) ⟨x, hxV, hxW⟩
  have hval := congrArg (fun k : (stalk y).obj G ⟶ (stalk y).obj (constant X M) ↦
    k (G.presheaf.germ (unop U) y (i.le hyV) s)) (h y hyD)
  change (TopCat.Presheaf.stalkFunctor Coeff.{0} y).map u.hom
      (G.presheaf.germ (unop U) y (i.le hyV) s) =
    (TopCat.Presheaf.stalkFunctor Coeff.{0} y).map v.hom
      (G.presheaf.germ (unop U) y (j.le hyW) s) at hval
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply,
    hm y hyV, hn y hyW] at hval
  let g := constantSection M ≫ (constant X M).presheaf.Γgerm y
  have : IsIso g := constantSection_germ_isIso M y
  have hg : g m = g n := hval
  have hmn : m = n := (ConcreteCategory.bijective_of_isIso g).injective hg
  rw [hm x hxV, hn x hxW, hmn]

private theorem hom_ext_of_stalks {X : TopCat.{0}} {F G : Sheaves X} {u v : G ⟶ F}
    (h : ∀ x, (stalk x).map u = (stalk x).map v) : u = v := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply TopCat.Presheaf.section_ext F (unop U)
  intro x hx
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply (unop U) x hx u.hom,
    ← TopCat.Presheaf.stalkFunctor_map_germ_apply (unop U) x hx v.hom]
  exact congrArg (fun k : (stalk x).obj G ⟶ (stalk x).obj F ↦
    k (G.presheaf.germ (unop U) x hx s)) (h x)

/-- The ordinary pushforward stalk map is natural in the sheaf. -/
private theorem pushforwardGerm_natural {X Y : TopCat.{0}} (f : X ⟶ Y)
    {F G : Sheaves X} (w : F ⟶ G) (x : X) :
    (stalk (f x)).map ((directImage f).map w) ≫ TopCat.Presheaf.stalkPushforward _ f G.obj x =
      TopCat.Presheaf.stalkPushforward _ f F.obj x ≫ (stalk x).map w :=
  stalkPushforward_naturality f w.hom x

private theorem inverseImageStalkMap_natural {X Y : TopCat.{0}} (f : X ⟶ Y)
    {G H : Sheaves Y} (w : G ⟶ H) (x : X) :
    (stalk (f x)).map w ≫ inverseImageStalkMap f H x =
      inverseImageStalkMap f G x ≫ (stalk x).map ((inverseImage f).map w) := by
  let a := inverseDirectAdjunction f
  have h := a.unit.naturality w
  change w ≫ a.unit.app H = a.unit.app G ≫ (directImage f).map ((inverseImage f).map w) at h
  unfold inverseImageStalkMap
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc, pushforwardGerm_natural]

private theorem adjointTranspose_stalk {X Y : TopCat.{0}} (f : X ⟶ Y) {G : Sheaves Y}
    {F : Sheaves X} (w : G ⟶ (directImage f).obj F) (x : X) :
    inverseImageStalkMap f G x ≫
      (stalk x).map (((inverseDirectAdjunction f).homEquiv G F).symm w) =
    (stalk (f x)).map w ≫ TopCat.Presheaf.stalkPushforward _ f F.obj x := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, ← Category.assoc,
    ← inverseImageStalkMap_natural, Category.assoc, inducedCounit_stalk]

private theorem hom_ext_of_distinct_sheet_stalks {J : Type} [TopologicalSpace J]
    {F G : Sheaves (TopCat.of (MarkedPlane × J))} {M : J → Coeff.{0}}
    (e : ∀ l : J, (inverseImage (sheetInclusion l)).obj F ≅ constant (TopCat.of MarkedPlane) (M l))
    {u v : G ⟶ F}
    (h : ∀ (p : MarkedPlane), p.1 ≠ p.2 → ∀ l : J,
      (stalk (X := TopCat.of (MarkedPlane × J)) (p, l)).map u =
        (stalk (X := TopCat.of (MarkedPlane × J)) (p, l)).map v) : u = v := by
  have hs (l : J) : (inverseImage (sheetInclusion l)).map u =
      (inverseImage (sheetInclusion l)).map v := by
    apply (cancel_mono (e l).hom).mp
    apply constant_hom_ext_of_dense dense_distinctMarks
    intro p hp
    simp only [Functor.map_comp]
    congr 1
    apply (cancel_epi (inverseImageStalkMap (sheetInclusion l) G p)).mp
    rw [← inverseImageStalkMap_natural, ← inverseImageStalkMap_natural]
    exact congrArg (· ≫ inverseImageStalkMap (sheetInclusion l) F p) (h p hp l)
  apply hom_ext_of_stalks
  rintro ⟨p, l⟩
  apply (cancel_mono (inverseImageStalkMap (sheetInclusion l) F p)).mp
  change (stalk ((sheetInclusion l) p)).map u ≫ _ =
    (stalk ((sheetInclusion l) p)).map v ≫ _
  rw [inverseImageStalkMap_natural, inverseImageStalkMap_natural, hs l]

private theorem homeomorphism_unit_isIso {Y Y' : TopCat.{0}} (k : Y' ≅ Y) (H : Sheaves Y) :
    IsIso ((inverseDirectAdjunction k.hom).unit.app H) := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro y
  obtain ⟨y', rfl⟩ := (TopCat.homeoOfIso k).surjective y
  exact inverseDirectUnit_stalk_isIso (TopCat.homeoOfIso k).isInducing H y'

theorem denseSheetExtension : DenseSheetExtensionSpecs.DenseSheetExtension := by
  intro J _ _ Y Y' f k F G M e u v h
  let H := (directImage f).obj F
  let a := inverseDirectAdjunction k.hom
  let η := a.unit.app H
  have : IsIso η := homeomorphism_unit_isIso k H
  let w (t : G ⟶ (inverseImage k.hom).obj H) : (directImage k.hom).obj G ⟶ H :=
    (directImage k.hom).map t ≫ inv η
  have hw {t : G ⟶ (inverseImage k.hom).obj H} (y' : Y') :
      (stalk (k.hom y')).map (w t) =
        TopCat.Presheaf.stalkPushforward _ k.hom G.obj y' ≫
          (stalk y').map t ≫ (inverseImageStalkIso k.hom H y').inv := by
    apply (cancel_mono (inverseImageStalkIso k.hom H y').hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [w]
    rw [Functor.map_comp, Category.assoc]
    change _ ≫ (stalk (k.hom y')).map (inv η) ≫
      (stalk (k.hom y')).map η ≫
        TopCat.Presheaf.stalkPushforward _ k.hom ((inverseImage k.hom).obj H).obj y' = _
    rw [← Functor.map_comp_assoc _ (inv η) η, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp, pushforwardGerm_natural]
  have compare {y : Y} {y' : Y'} (hy : k.hom y' = y) {A : Coeff.{0}}
      (g : (stalk y).obj H ⟶ A)
      (hh : (stalk y').map u ≫ (inverseImageStalkIso k.hom H y').inv ≫
          eqToHom (congrArg (fun z ↦ (stalk z).obj H) hy) ≫ g =
        (stalk y').map v ≫ (inverseImageStalkIso k.hom H y').inv ≫
          eqToHom (congrArg (fun z ↦ (stalk z).obj H) hy) ≫ g) :
      (stalk y).map (w u) ≫ g = (stalk y).map (w v) ≫ g := by
    subst y
    simp only [eqToHom_refl, Category.id_comp] at hh
    rw [hw y', hw y']
    simpa only [Category.assoc] using
      congrArg (TopCat.Presheaf.stalkPushforward _ k.hom G.obj y' ≫ ·) hh
  let b := (inverseDirectAdjunction f).homEquiv ((directImage k.hom).obj G) F
  have heq : b.symm (w u) = b.symm (w v) := by
    apply hom_ext_of_distinct_sheet_stalks e
    intro p hp l
    apply (cancel_epi (inverseImageStalkMap f ((directImage k.hom).obj G) (p, l))).mp
    change _ ≫ (stalk (X := TopCat.of (MarkedPlane × J)) (p, l)).map
        (((inverseDirectAdjunction f).homEquiv _ _).symm (w u)) =
      _ ≫ (stalk (X := TopCat.of (MarkedPlane × J)) (p, l)).map
        (((inverseDirectAdjunction f).homEquiv _ _).symm (w v))
    rw [adjointTranspose_stalk, adjointTranspose_stalk]
    obtain ⟨y', hy⟩ := (TopCat.homeoOfIso k).surjective (f (p, l))
    change k.hom y' = f (p, l) at hy
    exact compare hy (TopCat.Presheaf.stalkPushforward _ f F.obj (p, l))
      (by simpa only [pullbackSheetGerm] using h p hp l y' hy)
  have hmap : (directImage k.hom).map u = (directImage k.hom).map v := by
    simpa only [w, Category.assoc, IsIso.inv_hom_id, Category.comp_id] using
      congrArg (· ≫ η) (b.symm.injective heq)
  have hc (K : Sheaves Y') : IsIso (a.counit.app K) :=
    inducedCounit_isIso (TopCat.homeoOfIso k).isInducing K
  have : IsIso a.counit := NatIso.isIso_of_isIso_app a.counit
  exact (a.fullyFaithfulROfIsIsoCounit).map_injective hmap

end RepTheorySurvey.Geometric.DenseSheetExtension
