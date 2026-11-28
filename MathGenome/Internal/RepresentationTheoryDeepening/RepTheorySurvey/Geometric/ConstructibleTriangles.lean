import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConstructibleTriangles
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sheaves.LocallySurjective
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace Topology Opposite
open scoped ZeroObject

universe u v

namespace RepTheorySurvey.Geometric.ConstructibleTriangles

open Analytic

open private constantPullbackIso locallyConstantFiniteRank_of_iso
  zero_locallyConstantFiniteRank plusIsLE_iff plusIsGE_iff from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

abbrev IsConstructibleAlong : Expected.IsConstructibleAlongType.{u, v} :=
  Expected.IsConstructibleAlong.{u, v}

private abbrev H {X : TopCat.{u}} (q : ℤ) : BoundedBelow X ⥤ Sheaves X :=
  DerivedCategory.Plus.homologyFunctor (Sheaves X) q

private abbrev constantFunctor (X : TopCat.{u}) : Coeff.{u} ⥤ Sheaves X :=
  constantSheaf (Opens.grothendieckTopology X) Coeff.{u}

private abbrev constantAdjunction (X : TopCat.{u}) :=
  constantSheafAdj (Opens.grothendieckTopology X) Coeff.{u} (isTerminalTop (α := Opens X))

private abbrev constantPresheaf (X : TopCat.{u}) (V : Coeff.{u}) :
    X.Presheaf Coeff.{u} := (Functor.const _).obj V

private abbrev constantSection (X : TopCat.{u}) (V : Coeff.{u}) (U : Opens X) :
    V ⟶ (constant X V).obj.obj (op U) :=
  (toSheafify (Opens.grothendieckTopology X) (constantPresheaf X V)).app (op U)

private def constantStalkIso (X : TopCat.{u}) (V : Coeff.{u}) (x : X) :
    (stalk x).obj (constant X V) ≅ V := by
  let P := constantPresheaf X V
  let C := TopCat.Presheaf.stalkFunctor Coeff.{u} x
  let η := toSheafify (Opens.grothendieckTopology X) P
  have : IsIso (C.map η) := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ P
  let J := (OpenNhds x)ᵒᵖ
  exact (asIso (C.map η)).symm ≪≫
    (colimit.isColimit ((Functor.const J).obj V)).coconePointUniqueUpToIso
      (isColimitConstCocone J V)

private theorem constantSection_germ (X : TopCat.{u}) (V : Coeff.{u}) (U : Opens X)
    (x : X) (hx : x ∈ U) :
    constantSection X V U ≫ TopCat.Presheaf.germ (constant X V).obj U x hx ≫
      (constantStalkIso X V x).hom = 𝟙 V := by
  let P := constantPresheaf X V
  let η := toSheafify (Opens.grothendieckTopology X) P
  change η.app (op U) ≫ TopCat.Presheaf.germ (sheafify (Opens.grothendieckTopology X) P)
    U x hx ≫ _ = _
  erw [← TopCat.Presheaf.stalkFunctor_map_germ_assoc U x hx η]
  rw [constantStalkIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]
  exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (isColimitConstCocone (OpenNhds x)ᵒᵖ V) (op ⟨U, hx⟩)

private theorem constantSection_germ_apply (X : TopCat.{u}) (V : Coeff.{u})
    (U : Opens X) (x : X) (hx : x ∈ U) (v : V) :
    (constantStalkIso X V x).hom
      (TopCat.Presheaf.germ (constant X V).obj U x hx (constantSection X V U v)) = v :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (constantSection_germ X V U x hx)) v

open TopCat.Presheaf in
private theorem constantSection_bijective {X : TopCat.{u}} (V : Coeff.{u}) (U : Opens X)
    (hU : IsConnected (U : Set X)) : Function.Bijective (constantSection X V U) := by
  obtain ⟨x, hx⟩ := hU.nonempty
  refine ⟨fun v w e => ?_, ?_⟩
  · rw [← constantSection_germ_apply X V U x hx v, ← constantSection_germ_apply X V U x hx w, e]
  intro s
  let F := constant X V
  let f : U → V := fun y => (constantStalkIso X V y.val).hom (germ F.obj U y.val y.property s)
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    obtain ⟨W, hy, j, j', e⟩ := germ_eq F.obj y.val y.property y.property s
      (constantSection X V U (f y)) (by
        apply (ModuleCat.mono_iff_injective (constantStalkIso X V y.val).hom).mp inferInstance
        exact (constantSection_germ_apply X V U y.val y.property (f y)).symm)
    filter_upwards [(W.isOpen.preimage continuous_subtype_val).mem_nhds hy] with z hz
    have ez := germ_ext F.obj (hxU := z.property) (hxV := z.property) W hz j j' e
    change (constantStalkIso X V z.val).hom (germ F.obj U z.val z.property s) = f y
    rw [ez, constantSection_germ_apply]
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU.isPreconnected
  refine ⟨f ⟨x, hx⟩, ?_⟩
  apply TopCat.Presheaf.section_ext F U
  intro y hy
  apply (ModuleCat.mono_iff_injective (constantStalkIso X V y).hom).mp inferInstance
  rw [constantSection_germ_apply]
  exact hf.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

private def constantFullyFaithful (X : TopCat.{u}) [ConnectedSpace X] :
    (constantFunctor X).FullyFaithful := by
  let a := constantAdjunction X
  have (V : Coeff.{u}) : IsIso (a.unit.app V) := by
    change IsIso (constantSection X V ⊤)
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (constantSection_bijective V ⊤
      (show IsConnected (Set.univ : Set X) from isConnected_univ))
  have : IsIso a.unit := NatIso.isIso_of_isIso_app a.unit
  exact a.fullyFaithfulLOfIsIsoUnit

private instance constantPreservesFiniteLimits (X : TopCat.{u}) :
    PreservesFiniteLimits (constantFunctor X) := by
  let T := presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}
  let E := (Functor.const (Opens X)ᵒᵖ : Coeff.{u} ⥤ X.Presheaf Coeff.{u})
  have : PreservesLimits E := preservesLimits_const
  have : T.PreservesHomology := by dsimp only [T]; infer_instance
  have : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  exact comp_preservesFiniteLimits E T

private instance constantIsLeftAdjoint (X : TopCat.{u}) :
    (constantFunctor X).IsLeftAdjoint := (constantAdjunction X).isLeftAdjoint

private instance constantAdditive (X : TopCat.{u}) : (constantFunctor X).Additive :=
  Functor.additive_of_preserves_binary_products _

private def inclusionOfOpenLE {X : TopCat.{u}} {U W : Opens X} (h : U ≤ W) :
    TopCat.of U ⟶ TopCat.of W :=
  TopCat.ofHom ⟨fun x => ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩

private def restrictionIso {X : TopCat.{u}} {U W : Opens X} (h : U ≤ W)
    (F : Sheaves X) :
    (inverseImage (openInclusion U)).obj F ≅
      (inverseImage (inclusionOfOpenLE h)).obj ((inverseImage (openInclusion W)).obj F) :=
  (inverseImageComposition (inclusionOfOpenLE h) (openInclusion W)).app F

private theorem commonConnectedTrivialization {X : TopCat.{u}} [LocallyConnectedSpace X]
    {A B : Sheaves X} (hA : LocallyConstantFiniteRank A) (hB : LocallyConstantFiniteRank B)
    (x : X) :
    ∃ U : Opens X, x ∈ U ∧ IsConnected (U : Set X) ∧
      ∃ V W : Coeff.{u}, Module.Finite ℚ V ∧ Module.Finite ℚ W ∧
        Nonempty ((inverseImage (openInclusion U)).obj A ≅ constant (TopCat.of U) V) ∧
        Nonempty ((inverseImage (openInclusion U)).obj B ≅ constant (TopCat.of U) W) := by
  obtain ⟨U, hxU, V, hV, ⟨i⟩⟩ := hA x
  obtain ⟨W, hxW, V', hV', ⟨j⟩⟩ := hB x
  obtain ⟨T, ⟨hTo, hxT, hTc⟩, hT⟩ := (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp
    ((U ⊓ W).isOpen.mem_nhds (show x ∈ U ⊓ W from ⟨hxU, hxW⟩))
  let O : Opens X := ⟨T, hTo⟩
  have hOU : O ≤ U := fun _ hy => (hT hy).1
  have hOW : O ≤ W := fun _ hy => (hT hy).2
  refine ⟨O, hxT, hTc, V, V', hV, hV', ⟨?_⟩, ⟨?_⟩⟩
  · exact restrictionIso hOU A ≪≫ (inverseImage (inclusionOfOpenLE hOU)).mapIso i ≪≫
      constantPullbackIso _ _
  · exact restrictionIso hOW B ≪≫ (inverseImage (inclusionOfOpenLE hOW)).mapIso j ≪≫
      constantPullbackIso _ _

theorem locallyConstantFiniteRank_kernel : Expected.LocallyConstantFiniteRankKernel.{u} := by
  intro X _ A B f hA hB x
  obtain ⟨U, hx, hc, V, W, hV, _, ⟨i⟩, ⟨j⟩⟩ := commonConnectedTrivialization hA hB x
  let Y := TopCat.of U
  have : ConnectedSpace Y := isConnected_iff_connectedSpace.mp hc
  let L := inverseImage (openInclusion U)
  let C := constantFunctor Y
  have : C.Additive := constantAdditive Y
  have : PreservesFiniteLimits C := constantPreservesFiniteLimits Y
  let ff := constantFullyFaithful Y
  let g : V ⟶ W := ff.preimage (i.inv ≫ L.map f ≫ j.hom)
  have eq : L.map f ≫ j.hom = i.hom ≫ C.map g := by
    rw [ff.map_preimage, Iso.hom_inv_id_assoc]
  exact ⟨U, hx, ModuleCat.of ℚ g.hom.ker, inferInstance, ⟨
    PreservesKernel.iso L f ≪≫ kernel.mapIso _ _ i j eq ≪≫
      (PreservesKernel.iso C g).symm ≪≫ C.mapIso (ModuleCat.kernelIsoKer g)⟩⟩

theorem locallyConstantFiniteRank_cokernel : Expected.LocallyConstantFiniteRankCokernel.{u} := by
  intro X _ A B f hA hB x
  obtain ⟨U, hx, hc, V, W, _, hW, ⟨i⟩, ⟨j⟩⟩ := commonConnectedTrivialization hA hB x
  let Y := TopCat.of U
  have : ConnectedSpace Y := isConnected_iff_connectedSpace.mp hc
  let L := inverseImage (openInclusion U)
  let C := constantFunctor Y
  have : C.Additive := constantAdditive Y
  have : C.IsLeftAdjoint := constantIsLeftAdjoint Y
  let ff := constantFullyFaithful Y
  let g : V ⟶ W := ff.preimage (i.inv ≫ L.map f ≫ j.hom)
  have eq : L.map f ≫ j.hom = i.hom ≫ C.map g := by
    rw [ff.map_preimage, Iso.hom_inv_id_assoc]
  exact ⟨U, hx, ModuleCat.of ℚ (W ⧸ g.hom.range), inferInstance, ⟨
    PreservesCokernel.iso L f ≪≫ cokernel.mapIso _ _ i j eq ≪≫
      (PreservesCokernel.iso C g).symm ≪≫ C.mapIso (ModuleCat.cokernelIsoRangeQuotient g)⟩⟩

private theorem constantSection_restrict {X : TopCat.{u}} (V : Coeff.{u})
    {U W : Opens X} (r : U ⟶ W) :
    constantSection X V W ≫ (constant X V).obj.map r.op = constantSection X V U := by
  have h := (toSheafify (Opens.grothendieckTopology X) (constantPresheaf X V)).naturality r.op
  change 𝟙 V ≫ constantSection X V U =
    constantSection X V W ≫ (constant X V).obj.map r.op at h
  simpa only [Category.id_comp] using h.symm

private theorem exists_lift_constant_sections {X : TopCat.{u}} {B : Sheaves X}
    {V : Coeff.{u}} [Module.Finite ℚ V] (f : B ⟶ constant X V) [Epi f] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (s : V ⟶ B.obj.obj (op U)),
      s ≫ f.hom.app (op U) = constantSection X V U := by
  classical
  let b := Module.Basis.ofVectorSpace ℚ V
  letI := b.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 ℚ V)
  have h := (TopCat.Sheaf.isLocallySurjective_iff_epi f).mpr inferInstance
  have lift (i : Module.Basis.ofVectorSpaceIndex ℚ V) :
      ∃ (U : Opens X) (_ : x ∈ U) (s : B.obj.obj (op U)),
        f.hom.app (op U) s = constantSection X V U (b i) := by
    obtain ⟨U, hU, ⟨s, hs⟩, hx⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff f.hom).mp h ⊤
        (constantSection X V ⊤ (b i)) x (by trivial)
    exact ⟨U, hx, s, hs.trans (DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom (constantSection_restrict V (homOfLE hU))) (b i))⟩
  choose U hx s hs using lift
  let O := ⨅ i, U i
  let r (i : Module.Basis.ofVectorSpaceIndex ℚ V) : O ⟶ U i := homOfLE (iInf_le U i)
  let s' := ModuleCat.ofHom (b.constr ℚ (fun i => B.obj.map (r i).op (s i)))
  refine ⟨O, ?_, s', ?_⟩
  · change x ∈ ((⨅ i, U i : Opens X) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hx
  · apply ModuleCat.hom_ext
    apply b.ext
    intro i
    change f.hom.app (op O) ((b.constr ℚ _) (b i)) = constantSection X V O (b i)
    rw [Module.Basis.constr_basis]
    rw [← ConcreteCategory.comp_apply, f.hom.naturality, ConcreteCategory.comp_apply, hs]
    exact DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom (constantSection_restrict V (r i))) (b i)

private theorem inverseImage_split_of_section_lift {X : TopCat.{u}} {B : Sheaves X}
    {V : Coeff.{u}} (f : B ⟶ constant X V) (U : Opens X)
    (s : V ⟶ B.obj.obj (op U)) (hs : s ≫ f.hom.app (op U) = constantSection X V U) :
    ∃ l : (inverseImage (openInclusion U)).obj (constant X V) ⟶
        (inverseImage (openInclusion U)).obj B,
      l ≫ (inverseImage (openInclusion U)).map f = 𝟙 _ := by
  let j := openInclusion U
  let L := inverseImage j
  let R := directImage j
  let adj := inverseDirectAdjunction j
  let adjC := constantAdjunction X
  let d := adjC.comp adj
  let F := constant X V
  let r₀ : U ⟶ ⊤ := homOfLE le_top
  let r := r₀.op
  let ρ (G : Sheaves (TopCat.of U)) := (R.obj G).obj.map r
  have hρ (G : Sheaves (TopCat.of U)) : IsIso (ρ G) := by
    change IsIso (G.obj.map ((Opens.map j).op.map r))
    have eq : (Opens.map j).obj U = ⊤ := by
      ext z
      exact ⟨fun _ => trivial, fun _ => z.property⟩
    have : IsIso ((Opens.map j).op.map r) := by
      let e : (Opens.map j).op.obj (op ⊤) = (Opens.map j).op.obj (op U) :=
        congrArg op ((Opens.map_top j).trans eq.symm)
      have he : (Opens.map j).op.map r = eqToHom e := Subsingleton.elim _ _
      rw [he]
      infer_instance
    infer_instance
  let s' : V ⟶ (R.obj (L.obj B)).obj.obj (op (⊤ : Opens X)) :=
    s ≫ (adj.unit.app B).hom.app (op U) ≫ inv (ρ (L.obj B))
  let l := (d.homEquiv V (L.obj B)).symm s'
  refine ⟨l, ?_⟩
  apply (d.homEquiv V (L.obj F)).injective
  rw [d.homEquiv_naturality_right, Equiv.apply_symm_apply]
  refine Eq.trans ?_ (d.homEquiv_id V).symm
  apply (cancel_mono (ρ (L.obj F))).mp
  change (s ≫ (adj.unit.app B).hom.app (op U) ≫ inv (ρ (L.obj B))) ≫
    (R.map (L.map f)).hom.app (op ⊤) ≫ ρ (L.obj F) =
    d.unit.app V ≫ ρ (L.obj F)
  rw [← (R.map (L.map f)).hom.naturality r]
  dsimp only [ρ]
  rw [Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc]
  have hu := congrArg (fun g : B ⟶ R.obj (L.obj F) => g.hom.app (op U))
    (adj.unit.naturality f)
  change f.hom.app (op U) ≫ (adj.unit.app F).hom.app (op U) =
    (adj.unit.app B).hom.app (op U) ≫ (R.map (L.map f)).hom.app (op U) at hu
  rw [← hu, ← Category.assoc, hs, Adjunction.comp_unit_app]
  change constantSection X V U ≫ (adj.unit.app F).hom.app (op U) =
    (constantSection X V ⊤ ≫ (adj.unit.app F).hom.app (op ⊤)) ≫ (R.obj (L.obj F)).obj.map r
  have hnat := (adj.unit.app F).hom.naturality r
  change F.obj.map r ≫ (adj.unit.app F).hom.app (op U) =
    (adj.unit.app F).hom.app (op ⊤) ≫ (R.obj (L.obj F)).obj.map r at hnat
  rw [Category.assoc, ← hnat, ← Category.assoc,
    constantSection_restrict V r₀]

theorem locallyConstantFiniteRank_extension : Expected.LocallyConstantFiniteRankExtension.{u} := by
  intro X _ S hS h₁ h₃ x
  obtain ⟨U, hx, _, V, W, hV, hW, ⟨e₁⟩, ⟨e₃⟩⟩ := commonConnectedTrivialization h₁ h₃ x
  let Y := TopCat.of U
  let L := inverseImage (openInclusion U)
  let f : L.obj S.X₂ ⟶ constant Y W := L.map S.g ≫ e₃.hom
  have hSu := DerivedLocalSheaves.inverseImageExact (openInclusion U) S hS
  have : Epi (L.map S.g) := hSu.epi_g
  have : Epi f := epi_comp _ _
  obtain ⟨O, ho, s, hs⟩ := exists_lift_constant_sections f ⟨x, hx⟩
  obtain ⟨l, hl⟩ := inverseImage_split_of_section_lift f O s hs
  let K := inverseImage (openInclusion O)
  let S' := (S.map L).map K
  have hS' : S'.ShortExact := DerivedLocalSheaves.inverseImageExact (openInclusion O) _ hSu
  have hh : (K.map e₃.hom ≫ l) ≫ S'.g = 𝟙 _ := by
    have h : l ≫ K.map (L.map S.g) ≫ K.map e₃.hom = 𝟙 _ := by
      simpa only [f, Functor.map_comp] using hl
    change (K.map e₃.hom ≫ l) ≫ K.map (L.map S.g) = 𝟙 _
    apply (cancel_mono (K.map e₃.hom)).mp
    rw [Category.assoc, Category.assoc, h, Category.comp_id, Category.id_comp]
  let split := ShortComplex.Splitting.ofExactOfSection S' hS'.exact (K.map e₃.hom ≫ l)
    hh hS'.mono_f
  let C := constantFunctor (TopCat.of O)
  have : C.Additive := constantAdditive _
  have : PreservesBinaryBiproducts C := preservesBinaryBiproducts_of_preservesBiproducts C
  let P := ModuleCat.of ℚ (V × W)
  let i₁ := K.mapIso e₁ ≪≫ constantPullbackIso (openInclusion O) V
  let i₃ := K.mapIso e₃ ≪≫ constantPullbackIso (openInclusion O) W
  let d : S'.X₂ ≅ constant (TopCat.of O) P :=
    split.isoBinaryBiproduct ≪≫ biprod.mapIso i₁ i₃ ≪≫
      (C.mapBiprod V W).symm ≪≫ C.mapIso (ModuleCat.biprodIsoProd V W)
  let T := U.isOpenEmbedding.functor.obj O
  have ht : ∀ z : T, ∃ (y : Y), y ∈ O ∧ y.val = z.val := fun z => z.property
  have hu (z : T) : z.val ∈ U := by
    obtain ⟨y, _, he⟩ := ht z
    exact he ▸ y.property
  have huo (z : T) : (⟨z.val, hu z⟩ : Y) ∈ O := by
    obtain ⟨y, hy, he⟩ := ht z
    exact (Subtype.ext he : y = ⟨z.val, hu z⟩) ▸ hy
  have hk : Continuous (fun z : T => (⟨z.val, hu z⟩ : Y)) :=
    continuous_subtype_val.subtype_mk hu
  let k : TopCat.of T ⟶ TopCat.of O := TopCat.ofHom
    ⟨fun z => ⟨⟨z.val, hu z⟩, huo z⟩, hk.subtype_mk huo⟩
  have ke : openInclusion T = k ≫ openInclusion O ≫ openInclusion U := by rfl
  refine ⟨T, ⟨⟨x, hx⟩, ho, rfl⟩, P, inferInstance, ⟨?_⟩⟩
  exact eqToIso (congrArg (fun g => (inverseImage g).obj S.X₂) ke) ≪≫
    (inverseImageComposition k (openInclusion O ≫ openInclusion U)).app S.X₂ ≪≫
    (inverseImage k).mapIso ((inverseImageComposition (openInclusion O) (openInclusion U)).app S.X₂
      ≪≫ d) ≪≫ constantPullbackIso k P

theorem constructible_zero : Expected.ConstructibleZero.{u, v} := by
  intro X I Z e
  have hz (q : ℤ) : IsZero ((H q).obj (0 : BoundedBelow X)) :=
    (H (X := X) q).map_isZero (isZero_zero (BoundedBelow X))
  refine ⟨Set.finite_empty.subset ?_, fun i q =>
    zero_locallyConstantFiniteRank ((inverseImage (e i)).map_isZero (hz q))⟩
  intro q hq
  exact False.elim (hq (hz q))

theorem constructible_of_iso : Expected.ConstructibleOfIso.{u, v} := by
  intro X I Z e F G i h
  refine ⟨h.1.subset ?_, fun j q => locallyConstantFiniteRank_of_iso
    ((inverseImage (e j)).mapIso ((H q).mapIso i)) (h.2 j q)⟩
  intro q hq hz
  exact hq (hz.of_iso ((H q).mapIso i).symm)

theorem constructible_shift : Expected.ConstructibleShift.{u, v} := by
  intro X I Z e F n h
  let c (q : ℤ) : (H q).obj (F⟦n⟧) ≅ (H (q + n)).obj F :=
    ((H 0).shiftIso n q (q + n) (add_comm _ _)).app F
  have hf : (Set.preimage (fun q : ℤ => q + n)
      {q : ℤ | ¬ IsZero ((H q).obj F)}).Finite :=
    h.1.preimage (fun _ _ _ _ h => add_right_cancel h)
  refine ⟨hf.subset ?_, fun i q => locallyConstantFiniteRank_of_iso
    ((inverseImage (e i)).mapIso (c q).symm) (h.2 i (q + n))⟩
  intro q hq hz
  exact hq (hz.of_iso (c q))

/-- Three consecutive exact pairs give a short exact sequence at their common middle term. -/
private theorem shortExact_of_exact_pairs {C : Type*} [Category* C] [Abelian C]
    {A₀ A B D D₁ : C} {l : A₀ ⟶ A} {f : A ⟶ B} {g : B ⟶ D} {r : D ⟶ D₁}
    {hl : l ≫ f = 0} {hm : f ≫ g = 0} {hr : g ≫ r = 0}
    (el : (ShortComplex.mk l f hl).Exact) (em : (ShortComplex.mk f g hm).Exact)
    (er : (ShortComplex.mk g r hr).Exact) :
    ∃ S : ShortComplex C, S.X₁ = cokernel l ∧ S.X₂ = B ∧ S.X₃ = kernel r ∧ S.ShortExact := by
  let i := cokernel.desc l f hl
  let p := kernel.lift r g hr
  have hi : Mono i := el.mono_cokernelDesc
  have hp : Epi p := er.epi_kernelLift
  have hig : i ≫ g = 0 := by
    apply (cancel_epi (cokernel.π l)).mp
    rw [← Category.assoc, cokernel.π_desc, hm, comp_zero]
  have hip : i ≫ p = 0 := by
    apply (cancel_mono (kernel.ι r)).mp
    rw [Category.assoc, kernel.lift_ι, hig, zero_comp]
  let M := ShortComplex.mk f g hm
  let L := ShortComplex.mk i g hig
  let S := ShortComplex.mk i p hip
  let a : M ⟶ L := { τ₁ := cokernel.π l, τ₂ := 𝟙 B, τ₃ := 𝟙 D
                     comm₁₂ := by dsimp [M, L, i]; simp }
  let b : S ⟶ L := { τ₁ := 𝟙 _, τ₂ := 𝟙 B, τ₃ := kernel.ι r
                     comm₂₃ := by dsimp [S, L, p]; simp }
  have : Epi a.τ₁ := inferInstanceAs (Epi (cokernel.π l))
  have : IsIso a.τ₂ := inferInstanceAs (IsIso (𝟙 B))
  have : Mono a.τ₃ := inferInstanceAs (Mono (𝟙 D))
  have : Epi b.τ₁ := inferInstanceAs (Epi (𝟙 (cokernel l)))
  have : IsIso b.τ₂ := inferInstanceAs (IsIso (𝟙 B))
  have : Mono b.τ₃ := inferInstanceAs (Mono (kernel.ι r))
  have he := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono b).mpr
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono a).mp em)
  exact ⟨S, rfl, rfl, rfl, ShortComplex.ShortExact.mk' he hi hp⟩

private theorem constructible_middle {X : TopCat.{u}} {I : Type v} {Z : I → TopCat.{u}}
    [∀ i, LocallyConnectedSpace (Z i)] (e : ∀ i, Z i ⟶ X) (T : Triangle (BoundedBelow X))
    (hT : T ∈ distTriang (BoundedBelow X))
    (h₁ : IsConstructibleAlong e T.obj₁) (h₃ : IsConstructibleAlong e T.obj₃) :
    IsConstructibleAlong e T.obj₂ := by
  let F := H (X := X) 0
  refine ⟨(h₁.1.union h₃.1).subset ?_, ?_⟩
  · intro q hq
    by_contra hn
    change ¬ (¬ IsZero ((H q).obj T.obj₁) ∨ ¬ IsZero ((H q).obj T.obj₃)) at hn
    push Not at hn
    exact hq ((F.homologySequence_exact₂ T hT q).isZero_X₂
      (hn.1.eq_of_src _ _) (hn.2.eq_of_tgt _ _))
  · intro j q
    let L := inverseImage (e j)
    let l := F.homologySequenceδ T (q - 1) q (by omega)
    let f := (F.shift q).map T.mor₁
    let g := (F.shift q).map T.mor₂
    let r := F.homologySequenceδ T q (q + 1) rfl
    obtain ⟨S, e₁, e₂, e₃, he⟩ := shortExact_of_exact_pairs
      ((F.homologySequence_exact₁ T hT (q - 1) q (by omega)).map L)
      ((F.homologySequence_exact₂ T hT q).map L)
      ((F.homologySequence_exact₃ T hT q (q + 1) rfl).map L)
    have hc : LocallyConstantFiniteRank (cokernel (L.map l)) :=
      locallyConstantFiniteRank_cokernel _ (h₃.2 j (q - 1)) (h₁.2 j q)
    have hk : LocallyConstantFiniteRank (kernel (L.map r)) :=
      locallyConstantFiniteRank_kernel _ (h₃.2 j q) (h₁.2 j (q + 1))
    exact e₂ ▸ locallyConstantFiniteRank_extension S he (e₁.symm ▸ hc) (e₃.symm ▸ hk)

theorem constructible_triangle : Expected.ConstructibleTriangle.{u, v} := by
  intro X I Z inst e T hT
  refine ⟨constructible_middle e T hT, ?_, ?_⟩
  · intro h₁ h₂
    exact constructible_middle e T.rotate (rot_of_distTriang T hT) h₂
      (constructible_shift e 1 h₁)
  · intro h₂ h₃
    exact constructible_middle e T.invRotate (inv_rot_of_distTriang T hT)
      (constructible_shift e (-1) h₃) h₂

private theorem truncation_low {X : TopCat.{u}} (a : ℤ) (F : BoundedBelow X)
    (q : ℤ) (hq : q ≤ a) :
    let t := DerivedCategory.Plus.TStructure.t (C := Sheaves X)
    IsIso ((H q).map ((t.triangleLEGT a).obj F).mor₁) := by
  let t := DerivedCategory.Plus.TStructure.t (C := Sheaves X)
  let T := (t.triangleLEGT a).obj F
  have hT := t.triangleLEGT_distinguished a F
  have hb : T.obj₃.IsGE (a + 1) := t.isGE_truncGT_obj F a (a + 1)
  have z₁ := (plusIsGE_iff _ _).mp hb (q - 1) (by omega)
  have z₂ := (plusIsGE_iff _ _).mp hb q (by omega)
  have he : Epi ((H 0).shift q |>.map T.mor₁) :=
    ((H 0).homologySequence_epi_shift_map_mor₁_iff T hT q).mpr (z₂.eq_of_tgt _ _)
  have hm : Mono ((H 0).shift q |>.map T.mor₁) :=
    ((H 0).homologySequence_mono_shift_map_mor₁_iff T hT (q - 1) q (by omega)).mpr
      (z₁.eq_of_src _ _)
  change IsIso ((H 0).shift q |>.map T.mor₁)
  exact isIso_of_mono_of_epi _

private theorem truncation_high {X : TopCat.{u}} (a : ℤ) (F : BoundedBelow X)
    (q : ℤ) (hq : a < q) :
    let t := DerivedCategory.Plus.TStructure.t (C := Sheaves X)
    IsIso ((H q).map ((t.triangleLEGT a).obj F).mor₂) := by
  let t := DerivedCategory.Plus.TStructure.t (C := Sheaves X)
  let T := (t.triangleLEGT a).obj F
  have hT := t.triangleLEGT_distinguished a F
  have hb : T.obj₁.IsLE a := t.isLE_truncLE_obj F a a
  have z₁ := (plusIsLE_iff _ _).mp hb q hq
  have z₂ := (plusIsLE_iff _ _).mp hb (q + 1) (by omega)
  have he : Epi ((H 0).shift q |>.map T.mor₂) :=
    ((H 0).homologySequence_epi_shift_map_mor₂_iff T hT q (q + 1) rfl).mpr
      (z₂.eq_of_tgt _ _)
  have hm : Mono ((H 0).shift q |>.map T.mor₂) :=
    ((H 0).homologySequence_mono_shift_map_mor₂_iff T hT q).mpr (z₁.eq_of_src _ _)
  change IsIso ((H 0).shift q |>.map T.mor₂)
  exact isIso_of_mono_of_epi _

theorem constructible_truncation_induction : Expected.ConstructibleTruncationInduction.{u, v} := by
  intro X I Z e P _hzero hiso hshift htriangle hsingle
  let t := DerivedCategory.Plus.TStructure.t (C := Sheaves X)
  have single (F : BoundedBelow X) (n : ℤ) (hge : F.IsGE n) (hle : F.IsLE n)
      (h : ∀ i, LocallyConstantFiniteRank ((inverseImage (e i)).obj ((H n).obj F))) :
      P F := by
    haveI : F.IsGE n := hge
    haveI : F.IsLE n := hle
    obtain ⟨M, ⟨j⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
      (DerivedCategory.Plus.ι.obj F) n
    let d : F ≅ (DerivedCategory.Plus.singleFunctor (Sheaves X) n).obj M :=
      DerivedCategory.Plus.ι.preimageIso j
    let c : (H n).obj F ≅ M :=
      (cohomology X n).mapIso j ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (Sheaves X) n).app M
    have hc := hsingle M (fun i => locallyConstantFiniteRank_of_iso
      ((inverseImage (e i)).mapIso c) (h i))
    let s := ((DerivedCategory.Plus.singleFunctors (Sheaves X)).shiftIso
      (-n) n 0 (neg_add_cancel n)).app M
    exact hiso (d ≪≫ s.symm).symm
      (hshift (LocalSheaf.sheafInDegreeZero M) (-n) hc)
  have bounded (b : ℤ) (k : ℕ) (F : BoundedBelow X) (hge : F.IsGE b)
      (hle : F.IsLE (b + k))
      (h : ∀ i q, LocallyConstantFiniteRank ((inverseImage (e i)).obj ((H q).obj F))) :
      P F := by
    induction k generalizing F with
    | zero =>
      exact single F b hge (by simpa using hle) (fun i => h i b)
    | succ k ih =>
      let a := b + (k : ℤ)
      let T := (t.triangleLEGT a).obj F
      have hT : T ∈ distTriang (BoundedBelow X) := t.triangleLEGT_distinguished a F
      have h₁ : T.obj₁.IsLE a := t.isLE_truncLE_obj F a a
      have h₃ : T.obj₃.IsGE (a + 1) := t.isGE_truncGT_obj F a (a + 1)
      have lge : T.obj₁.IsGE b := (plusIsGE_iff _ _).mpr (fun q hq => by
        haveI : IsIso ((H q).map T.mor₁) := truncation_low a F q (by dsimp [a]; omega)
        exact ((plusIsGE_iff _ _).mp hge q hq).of_iso (asIso ((H q).map T.mor₁)))
      have rle : T.obj₃.IsLE (a + 1) := (plusIsLE_iff _ _).mpr (fun q hq => by
        haveI : IsIso ((H q).map T.mor₂) := truncation_high a F q (by omega)
        exact ((plusIsLE_iff _ _).mp hle q (by dsimp [a] at hq; omega)).of_iso
          (asIso ((H q).map T.mor₂)).symm)
      apply htriangle T hT
      · apply ih T.obj₁ lge h₁
        intro i q
        by_cases hq : q ≤ a
        · haveI : IsIso ((H q).map T.mor₁) := truncation_low a F q hq
          exact locallyConstantFiniteRank_of_iso
            ((inverseImage (e i)).mapIso (asIso ((H q).map T.mor₁)).symm) (h i q)
        · exact zero_locallyConstantFiniteRank ((inverseImage (e i)).map_isZero
            ((plusIsLE_iff _ _).mp h₁ q (lt_of_not_ge hq)))
      · apply single T.obj₃ (a + 1) h₃ rle
        intro i
        haveI : IsIso ((H (a + 1)).map T.mor₂) := truncation_high a F (a + 1) (by omega)
        exact locallyConstantFiniteRank_of_iso
          ((inverseImage (e i)).mapIso (asIso ((H (a + 1)).map T.mor₂))) (h i (a + 1))
  intro F hF
  obtain ⟨b, hb⟩ := F.property
  have hge : F.IsGE b := (DerivedCategory.Plus.isGE_ι_obj_iff F b).mp hb
  obtain ⟨a, ha⟩ := hF.1.bddAbove
  let k := (a - b).toNat
  refine bounded b k F hge ((plusIsLE_iff _ _).mpr ?_) hF.2
  intro q hq
  by_contra hn
  have hq' : q ≤ a := ha hn
  dsimp [k] at hq
  omega

end RepTheorySurvey.Geometric.ConstructibleTriangles
