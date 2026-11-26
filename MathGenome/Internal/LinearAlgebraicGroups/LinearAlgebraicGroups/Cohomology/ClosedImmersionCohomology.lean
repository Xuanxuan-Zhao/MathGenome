import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ClosedImmersionCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechInjectiveRows
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Topology.Sheaves.Flasque
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open HomologicalComplex

universe u
noncomputable section

namespace LinearAlgebraicGroups.ClosedImmersionCohomology

open Specs.ClosedImmersionCohomology Specs.OrderedCechComparison

private abbrev underlying (X : Scheme.{u}) :
    X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf X.ringCatSheaf

private instance (X : Scheme.{u}) : PreservesFiniteColimits (underlying X) where
  preservesFiniteColimits K := by
    intro _ _
    constructor
    intro D
    let R := X.ringCatSheaf
    let F := SheafOfModules.forget R
    let L := PresheafOfModules.sheafification.{u} (𝟙 R.obj)
    let D' := D ⋙ F
    have hL : PreservesColimits L := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).leftAdjoint_preservesColimits
    have hP : PreservesFiniteColimits (L ⋙ underlying X) := by
      apply preservesFiniteColimits_of_natIso (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
    let adj : L ⊣ F := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
    have hcounit : IsIso adj.counit := by
      change IsIso (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).counit
      apply NatIso.isIso_of_isIso_app
    let e : D' ⋙ L ≅ D :=
      (Functor.associator D F L) ≪≫ Functor.isoWhiskerLeft D
        (@asIso _ _ _ _ adj.counit hcounit) ≪≫
        D.rightUnitor
    have h : PreservesColimit (D' ⋙ L) (underlying X) := preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit D'))
      (show IsColimit ((underlying X).mapCocone (L.mapCocone (colimit.cocone D'))) from
        isColimitOfPreserves (L ⋙ underlying X) (colimit.isColimit D'))
    exact @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ (underlying X) e h

set_option backward.isDefEq.respectTransparency false in
private lemma epi_pushforward {X Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j]
    {F G : Z.Modules} (f : F ⟶ G) [Epi f] :
    Epi ((Scheme.Modules.pushforward j).map f) := by
  let P := Scheme.Modules.pushforward j
  have hf : Epi ((underlying Z).map f) := inferInstance
  have h := (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi ((underlying Z).map f)).2 hf)
  have hp : Epi ((underlying X).map (P.map f)) := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).1
    apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).2
    intro x
    by_cases hx : x ∈ Set.range j
    · obtain ⟨z, rfl⟩ := hx
      let a := TopCat.Presheaf.stalkPushforward AddCommGrpCat j.base ((underlying Z).obj F).obj z
      let b := TopCat.Presheaf.stalkPushforward AddCommGrpCat j.base ((underlying Z).obj G).obj z
      have ha : IsIso a := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        _ j.isClosedEmbedding.isInducing _ z
      have hb : IsIso b := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        _ j.isClosedEmbedding.isInducing _ z
      let m := (TopCat.Presheaf.stalkFunctor AddCommGrpCat (j z)).map
        ((underlying X).map (P.map f)).hom
      have hc : m ≫ b = a ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map
          ((underlying Z).map f).hom := by
        apply TopCat.Presheaf.stalk_hom_ext
        intro U hU
        let H : TopCat.Presheaf AddCommGrpCat Z := ((underlying Z).obj F).obj
        let H' : TopCat.Presheaf AddCommGrpCat Z := ((underlying Z).obj G).obj
        let f' : H ⟶ H' := ((underlying Z).map f).hom
        let p := (TopCat.Presheaf.pushforward AddCommGrpCat j.base).map f'
        change ((TopCat.Presheaf.pushforward AddCommGrpCat j.base).obj H).germ U (j z) hU ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat (j z)).map p ≫
            TopCat.Presheaf.stalkPushforward AddCommGrpCat j.base H' z =
          ((TopCat.Presheaf.pushforward AddCommGrpCat j.base).obj H).germ U (j z) hU ≫
            TopCat.Presheaf.stalkPushforward AddCommGrpCat j.base H z ≫
              (TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map f'
        rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
          TopCat.Presheaf.stalkPushforward_germ, TopCat.Presheaf.stalkPushforward_germ_assoc,
          TopCat.Presheaf.stalkFunctor_map_germ]
        rfl
      intro t
      obtain ⟨s, hs⟩ := h z (b t)
      refine ⟨inv a s, ((AddCommGrpCat.mono_iff_injective b).1 inferInstance) ?_⟩
      change (m ≫ b) (inv a s) = b t
      rw [hc]
      change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map ((underlying Z).map f).hom)
        (a (inv a s)) = b t
      rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
      exact hs
    · let W : X.Opens := ⟨(Set.range j)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      intro t
      refine ⟨0, ?_⟩
      obtain ⟨U, hxU, s, rfl⟩ :=
        TopCat.Presheaf.exists_germ_eq ((underlying X).obj ((P).obj G)).obj t
      let V := U ⊓ W
      have hxV : x ∈ V := ⟨hxU, hx⟩
      have hv : j ⁻¹ᵁ V = ⊥ := by
        ext z
        exact ⟨fun hz => (show j z ∈ W from hz.2) ⟨z, rfl⟩, False.elim⟩
      have hz : Subsingleton (((underlying X).obj ((P).obj G)).obj.obj (op V)) := by
        change Subsingleton (((underlying Z).obj G).obj.obj (op (j ⁻¹ᵁ V)))
        rw [hv]
        exact AddCommGrpCat.isZero_iff_subsingleton.1 (IsZero.of_iso
          (isZero_zero AddCommGrpCat) (((underlying Z).obj G).isTerminalOfEmpty.uniqueUpToIso
            (HasZeroObject.zeroIsTerminal (C := AddCommGrpCat))))
      rw [map_zero, ← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_left : V ⟶ U) x hxV]
      let pres : TopCat.Presheaf AddCommGrpCat X := ((underlying X).obj ((P).obj G)).obj
      change 0 = pres.germ V x hxV (pres.map (homOfLE inf_le_left : V ⟶ U).op s)
      have hz' : pres.map (homOfLE inf_le_left : V ⟶ U).op s = 0 := Subsingleton.elim _ _
      rw [hz', map_zero]
  constructor
  intro H a b hab
  have : (underlying X).Faithful := inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Faithful
  apply (underlying X).map_injective
  apply (cancel_epi ((underlying X).map (P.map f))).1
  simpa only [← Functor.map_comp] using (underlying X).congr_map hab

theorem pushforwardExact : PushforwardExact.{u} := by
  intro X Z j hj
  let P := Scheme.Modules.pushforward j
  apply ((Functor.preservesFiniteColimits_tfae P).out 1 4).mp
  intro S hS
  have := hS.epi_g
  exact ⟨(Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono P).1 inferInstance S hS |>.1,
    epi_pushforward j S.g⟩


section Lifts

variable {C : Type*} [Category* C] [Abelian C]

/-- Into a termwise injective, nonnegative complex, a quasi-isomorphism
induces a bijection on maps in the homotopy category. -/
private theorem precomp_bijective {K L T : CochainComplex C ℕ} (a : K ⟶ L)
    [QuasiIso a] [∀ n, Injective (T.X n)] :
    Function.Bijective (fun b : (HomotopyCategory.quotient C (.up ℕ)).obj L ⟶
        (HomotopyCategory.quotient C (.up ℕ)).obj T =>
      (HomotopyCategory.quotient C (.up ℕ)).map a ≫ b) := by
  let E := ComplexShape.embeddingUpNat.extendHomotopyFunctor C
  let Q := HomotopyCategory.quotient C (.up ℤ)
  let a' := extendMap a ComplexShape.embeddingUpNat
  have ha : QuasiIso a' := (quasiIso_extendMap_iff a ComplexShape.embeddingUpNat).2 inferInstance
  have ht := CochainComplex.IsKInjective.rightOrthogonal (T.extend ComplexShape.embeddingUpNat)
  rw [← CategoryTheory.ObjectProperty.isLocal_trW,
    ← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at ht
  have h := ht (Q.map a') ((HomotopyCategory.quotient_map_mem_quasiIso_iff a').2 ha)
  let Q₀ := HomotopyCategory.quotient C (.up ℕ)
  change Function.Bijective (fun b : E.obj (Q₀.obj L) ⟶ E.obj (Q₀.obj T) =>
    E.map (Q₀.map a) ≫ b) at h
  constructor
  · intro b c eq
    apply E.map_injective
    apply h.1
    simpa only [← Functor.map_comp] using E.congr_map eq
  · intro b
    obtain ⟨c, hc⟩ := h.2 (E.map b)
    obtain ⟨d, rfl⟩ := E.map_surjective c
    exact ⟨d, E.map_injective (by simpa only [Functor.map_comp] using hc)⟩

private theorem fromSingle_eq {M : C} {K : CochainComplex C ℕ}
    {f g : (CochainComplex.single₀ C).obj M ⟶ K} (h : f.f 0 = g.f 0) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    exact h
  · exact (isZero_single_obj_X (.up ℕ) 0 M i hi).eq_of_src _ _

private theorem fromSingle_eq_of_homotopy {M : C} {K : CochainComplex C ℕ}
    {f g : (CochainComplex.single₀ C).obj M ⟶ K} (h : Homotopy f g) : f = g := by
  apply fromSingle_eq
  have h₁ : h.hom 1 0 = 0 :=
    (isZero_single_obj_X (.up ℕ) 0 M 1 (by decide)).eq_of_src _ _
  have hh := h.comm 0
  rw [dNext_eq h.hom (show (ComplexShape.up ℕ).Rel 0 1 by rfl), h₁, comp_zero,
    prevD_eq_zero h.hom 0 (by decide), add_zero, zero_add] at hh
  exact hh

private theorem lift_from_resolution {M : C} {K T : CochainComplex C ℕ}
    (a : (CochainComplex.single₀ C).obj M ⟶ K) [QuasiIso a]
    (b : (CochainComplex.single₀ C).obj M ⟶ T) [∀ n, Injective (T.X n)] :
    ∃ c : K ⟶ T, a ≫ c = b := by
  let Q := HomotopyCategory.quotient C (.up ℕ)
  obtain ⟨c, hc⟩ := (precomp_bijective (T := T) a).2 (Q.map b)
  obtain ⟨l, rfl⟩ := Q.map_surjective c
  refine ⟨l, fromSingle_eq_of_homotopy (HomotopyCategory.homotopyOfEq _ _ ?_)⟩
  simpa only [Functor.map_comp] using hc

private def homotopy_of_lift {K₀ K T : CochainComplex C ℕ} (a : K₀ ⟶ K) [QuasiIso a]
    [∀ n, Injective (T.X n)] (f g : K ⟶ T) (h : a ≫ f = a ≫ g) : Homotopy f g :=
  HomotopyCategory.homotopyOfEq f g ((precomp_bijective (T := T) a).1
    (by simpa only [← Functor.map_comp] using (HomotopyCategory.quotient C (.up ℕ)).congr_map h))

end Lifts

section Resolution

variable {X Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j]
  {G : Z.Modules} (J : InjectiveResolution G)

local notation "P" => Scheme.Modules.pushforward j
local notation "P₊" => Functor.mapHomologicalComplex (Scheme.Modules.pushforward j) (ComplexShape.up ℕ)

private local instance : PreservesFiniteColimits P := pushforwardExact j

private def pushedAugmentation :
    (CochainComplex.single₀ X.Modules).obj ((P).obj G) ⟶ (P₊).obj J.cocomplex :=
  ((HomologicalComplex.singleMapHomologicalComplex P (.up ℕ) 0).inv.app G) ≫ (P₊).map J.ι

omit [IsClosedImmersion j] in
@[simp]
private lemma pushedAugmentation_f :
    (pushedAugmentation j J).f 0 = (P).map (J.ι.f 0) := by
  simp only [pushedAugmentation, comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToIso]
  change (𝟙 _) ≫ (P).map (𝟙 _) ≫ (P).map (J.ι.f 0) = _
  rw [(P).map_id, Category.id_comp, Category.id_comp]

private instance : QuasiIso (pushedAugmentation j J) := by
  unfold pushedAugmentation
  infer_instance

theorem exists_lift (I : InjectiveResolution ((P).obj G)) :
    ∃ l, LiftsIdentity (j := j) J I l := by
  obtain ⟨l, hl⟩ := lift_from_resolution (pushedAugmentation j J) I.ι
  exact ⟨l, by simpa [LiftsIdentity] using congr_hom hl 0⟩

private theorem lift_quasiIso (I : InjectiveResolution ((P).obj G))
    (l : (P₊).obj J.cocomplex ⟶ I.cocomplex) (hl : LiftsIdentity (j := j) J I l) : QuasiIso l := by
  have h : pushedAugmentation j J ≫ l = I.ι :=
    fromSingle_eq (by simpa [LiftsIdentity] using hl)
  exact (quasiIso_iff_comp_left (pushedAugmentation j J) l).1 (h ▸ inferInstance)

end Resolution


private instance (X : Scheme.{u}) : PreservesFiniteLimits (underlying X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))

private instance (X : Scheme.{u}) : (underlying X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Additive

private lemma underlying_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (h : S.ShortExact) : (S.map (underlying X)).ShortExact := by
  let F := underlying X
  have hF : PreservesFiniteLimits F ∧ PreservesFiniteColimits F := ⟨inferInstance, inferInstance⟩
  have hh : ∀ T : ShortComplex X.Modules, T.ShortExact → (T.map F).ShortExact :=
    ((Functor.exact_tfae F).out 4 1).1 hF
  exact hh S h

section Flasque

open private germFamilies germFamiliesEmbedding from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechInjectiveRows

variable {X : Scheme.{u}}

private abbrev Flasque (M : X.Modules) :=
  TopCat.Sheaf.IsFlasque ((underlying X).obj M)

private lemma flasque_of_split {M N : X.Modules} (i : M ⟶ N) (r : N ⟶ M)
    (h : i ≫ r = 𝟙 M) [Flasque N] : Flasque M where
  epi {U V} f := by
    let e := (underlying X).map i
    let t := (underlying X).map r
    apply (AddCommGrpCat.epi_iff_surjective _).2
    intro s
    obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective _).1
      (TopCat.Presheaf.IsFlasque.epi (F := ((underlying X).obj N).obj) f) (e.hom.app V s)
    refine ⟨t.hom.app U y, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← t.hom.naturality, ConcreteCategory.comp_apply, hy,
      ← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
    change ((underlying X).map (i ≫ r)).hom.app V s = s
    rw [h, (underlying X).map_id]
    rfl

private lemma flasque_of_iso {M N : X.Modules} (e : M ≅ N) [Flasque N] : Flasque M :=
  flasque_of_split e.hom e.inv e.hom_inv_id

private lemma flasque_zero {M : X.Modules} (h : IsZero M) : Flasque M where
  epi {U V} f := by
    let E := (CategoryTheory.evaluation (X.Opensᵒᵖ) AddCommGrpCat.{u}).obj V
    let F := TopCat.Sheaf.forget AddCommGrpCat.{u} X
    have h' := E.map_isZero (F.map_isZero ((underlying X).map_isZero h))
    have hs : Subsingleton (((underlying X).obj M).obj.obj V) :=
      AddCommGrpCat.isZero_iff_subsingleton.1 h'
    exact (AddCommGrpCat.epi_iff_surjective _).2 fun s => ⟨0, @Subsingleton.elim _ hs _ _⟩

set_option backward.isDefEq.respectTransparency false in
private lemma flasque_injective (M : X.Modules) [Injective M] : Flasque M := by
  let N : X.Modules := germFamilies M
  have h : Flasque N := by
    constructor
    intro U V f
    apply (AddCommGrpCat.epi_iff_surjective _).2
    intro s
    classical
    refine ⟨fun x => if hx : x.val ∈ V.unop then s ⟨x.val, hx⟩ else 0, ?_⟩
    funext x
    change (if hx : (f.unop x).val ∈ V.unop then s ⟨(f.unop x).val, hx⟩ else 0) = s x
    exact dite_eq_left (show (f.unop x).val ∈ V.unop from x.property)
  let i : M ⟶ N := germFamiliesEmbedding M
  have hi : Mono i := by
    change Mono (germFamiliesEmbedding M)
    infer_instance
  exact flasque_of_split i (Injective.factorThru (𝟙 M) i) (Injective.comp_factorThru (𝟙 M) i)

private lemma flasque_pushforward {Z : Scheme.{u}} (j : Z ⟶ X) (M : Z.Modules)
    [Flasque M] : Flasque ((Scheme.Modules.pushforward j).obj M) :=
  TopCat.Presheaf.IsFlasque.pushforward_isFlasque ((underlying Z).obj M).obj j.base

private lemma flasque_biprod (M N : X.Modules) [Flasque M] [Flasque N] :
    Flasque (M ⊞ N) where
  epi {U V} f := by
    let P := underlying X
    let a := (P.map (biprod.fst : M ⊞ N ⟶ M)).hom
    let b := (P.map (biprod.snd : M ⊞ N ⟶ N)).hom
    let c := (P.map (biprod.inl : M ⟶ M ⊞ N)).hom
    let d := (P.map (biprod.inr : N ⟶ M ⊞ N)).hom
    apply (AddCommGrpCat.epi_iff_surjective _).2
    intro s
    obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective _).1
      (TopCat.Presheaf.IsFlasque.epi (F := (P.obj M).obj) f) (a.app V s)
    obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective _).1
      (TopCat.Presheaf.IsFlasque.epi (F := (P.obj N).obj) f) (b.app V s)
    refine ⟨c.app U x + d.app U y, ?_⟩
    rw [map_add]
    have hc := congrArg (fun g => g x) (c.naturality f).symm
    have hd := congrArg (fun g => g y) (d.naturality f).symm
    simp only [ConcreteCategory.comp_apply] at hc hd
    rw [hc, hd, hx, hy]
    change ((P.map ((biprod.fst : M ⊞ N ⟶ M) ≫ biprod.inl +
      (biprod.snd : M ⊞ N ⟶ N) ≫ biprod.inr)).hom.app V) s = s
    rw [biprod.total, P.map_id]
    rfl

private abbrev cycleSequence (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ShortComplex X.Modules :=
  ShortComplex.mk (K.iCycles (n - 1)) (K.toCycles (n - 1) n) (by
    rw [← cancel_mono (K.iCycles n), Category.assoc, toCycles_i, iCycles_d, zero_comp])

private lemma cycleSequence_shortExact (K : CochainComplex X.Modules ℤ) (hK : K.Acyclic)
    (n : ℤ) : (cycleSequence K n).ShortExact := by
  let S := cycleSequence K n
  have he : (K.sc n).Exact := hK n
  have hep : Epi S.g := by
    have hs := he.epi_toCycles
    change Epi (K.toCycles ((ComplexShape.up ℤ).prev n) n) at hs
    rwa [show (ComplexShape.up ℤ).prev n = n - 1 by simp] at hs
  have hm : Mono S.f := inferInstanceAs (Mono (K.iCycles (n - 1)))
  apply ShortComplex.ShortExact.mk
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofι _ _ (fun x hx => K.liftCycles x n (by simp) (by
    change x ≫ K.toCycles (n - 1) n = 0 at hx
    have heq := congrArg (fun f => f ≫ K.iCycles n) hx
    change (x ≫ K.toCycles (n - 1) n) ≫ K.iCycles n = 0 ≫ K.iCycles n at heq
    rwa [Category.assoc, toCycles_i, zero_comp] at heq))
    (by intro _ x hx; exact K.liftCycles_i _ _ _ _)
    (by intro _ x hx y hy
        apply (cancel_mono (K.iCycles (n - 1))).1
        rw [K.liftCycles_i]
        exact hy)

private lemma cycle_flasque (K : CochainComplex X.Modules ℤ) (hK : K.Acyclic)
    (hF : ∀ n, Flasque (K.X n)) (d : ℤ) (h₀ : ∀ n < d, IsZero (K.X n)) :
    ∀ n, Flasque (K.cycles n) := by
  have hz (n : ℤ) (hn : n ≤ d) : IsZero (K.cycles n) := by
    have h : Epi (K.toCycles (n - 1) n) := (cycleSequence_shortExact K hK n).epi_g
    have hf := h₀ (n - 1) (by omega)
    rw [IsZero.iff_id_eq_zero, ← cancel_epi (K.toCycles (n - 1) n), Category.comp_id, comp_zero]
    exact hf.eq_of_src _ _
  intro n
  by_cases hn : n ≤ d
  · exact flasque_zero (hz n hn)
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = d + (k : ℤ) := ⟨(n - d).toNat, by omega⟩
  clear hn
  induction k with
  | zero => exact flasque_zero (hz _ (by simp))
  | succ k ih =>
    let m := d + ((k + 1 : ℕ) : ℤ)
    have hh : m - 1 = d + (k : ℤ) := by dsimp [m]; omega
    have hfc : Flasque (K.cycles (m - 1)) := hh ▸ ih
    have hfm : Flasque (K.X (m - 1)) := hF _
    have hS : ((cycleSequence K m).map (underlying X)).ShortExact :=
      underlying_shortExact (cycleSequence_shortExact K hK m)
    exact @TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ _ _ hS hfc hfm

private lemma acyclic_sections_of_flasque {A : Type u} [CommRing A] (X₀ : SchemeOverRing A)
    (K : CochainComplex X₀.left.Modules ℤ) (hK : K.Acyclic)
    (hF : ∀ n, Flasque (K.X n)) (d : ℤ) (h₀ : ∀ n < d, IsZero (K.X n)) :
    (((sectionsFunctor X₀).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  intro n
  let S := sectionsFunctor X₀
  let L := (S.mapHomologicalComplex (.up ℤ)).obj K
  have hfc := cycle_flasque K hK hF d h₀ (n - 1)
  let E := cycleSequence K n
  have hE : (E.map (underlying X₀.left)).ShortExact :=
    underlying_shortExact (cycleSequence_shortExact K hK n)
  have he := @TopCat.Sheaf.IsFlasque.epi_of_shortExact _ ⊤ _ hE hfc
  have hepi : Epi (S.map (K.toCycles (n - 1) n)) :=
    (ModuleCat.epi_iff_surjective _).2 ((AddCommGrpCat.epi_iff_surjective _).1 he)
  apply (exactAt_iff' L (n - 1) n (n + 1) (by simp) (by simp)).2
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro x hx
  let T := ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (K.iCycles_d _ _)
  have hT : (T.map S).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ (K.cyclesIsKernel n (n + 1) (by simp)) S)
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 hT x hx
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).1 hepi z
  refine ⟨y, ?_⟩
  change S.map (K.d (n - 1) n) y = x
  rw [← toCycles_i, Functor.map_comp]
  exact (congrArg (S.map (K.iCycles n)) hy).trans hz

end Flasque


section Sections

open private mapExtendIso extendMapTo extendMapTo_comm from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechComparison

private lemma quasiIso_iff_acyclic_cone {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  change HomologicalComplex.quasiIso C (ComplexShape.up ℤ) f ↔ _
  rw [← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

private lemma extend_flasque {X : Scheme.{u}} (K : CochainComplex X.Modules ℕ)
    (h : ∀ n, Flasque (K.X n)) (i : ℤ) : Flasque ((K.extend intEmbedding).X i) := by
  by_cases hi : i < 0
  · exact flasque_zero (K.isZero_extend_X intEmbedding i (by
      intro n hn
      simp only [intEmbedding, ComplexShape.embeddingUpIntGE_f, zero_add] at hn
      omega))
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
    have h' := h n
    exact flasque_of_iso (K.extendXIso intEmbedding (i := n) (by simp [intEmbedding]))

variable {A : Type u} [CommRing A] {X : SchemeOverRing A} {Z : Scheme.{u}}
    (j : Z ⟶ X.left) [IsClosedImmersion j]
    {G : Z.Modules} (J : InjectiveResolution G)
    (I : InjectiveResolution ((Scheme.Modules.pushforward j).obj G))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Applying global sections to any comparison lift gives a quasi-isomorphism.
Its cone is acyclic, bounded below, and flasque termwise. -/
theorem sections_quasiIso
    (l : ((Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℕ)).obj
      J.cocomplex ⟶ I.cocomplex) (hl : LiftsIdentity (j := j) J I l) :
    QuasiIso (((sectionsFunctor X).mapHomologicalComplex (.up ℕ)).map l) := by
  let P := (Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℕ)
  let S := sectionsFunctor X
  let K := P.obj J.cocomplex
  let L := I.cocomplex
  let f := extendMap l intEmbedding
  let T := CochainComplex.mappingCone f
  have q : QuasiIso f := (quasiIso_extendMap_iff l intEmbedding).2 (lift_quasiIso j J I l hl)
  have hT : T.Acyclic := (quasiIso_iff_acyclic_cone f).1 q
  have hK (n : ℕ) : Flasque (K.X n) := by
    have hf := flasque_injective (J.cocomplex.X n)
    exact flasque_pushforward j _
  have hL (n : ℕ) : Flasque (L.X n) := flasque_injective _
  have hF (n : ℤ) : Flasque (T.X n) := by
    have h₁ := extend_flasque K hK (n + 1)
    have h₂ := extend_flasque L hL n
    have h₃ := flasque_biprod ((K.extend intEmbedding).X (n + 1)) ((L.extend intEmbedding).X n)
    exact flasque_of_iso (homotopyCofiber.XIsoBiprod f n (n + 1) rfl)
  have hb (n : ℤ) (hn : n < -1) : IsZero (T.X n) := by
    apply (CochainComplex.mappingCone.isZero_X_iff f n).2
    constructor
    · apply K.isZero_extend_X
      intro m hm
      simp [intEmbedding] at hm
      omega
    · apply L.isZero_extend_X
      intro m hm
      simp [intEmbedding] at hm
      omega
  let e := CochainComplex.mappingCone.mapHomologicalComplexIso f S
  have hac := acyclic_sections_of_flasque X T hT hF (-1) hb
  have hac' : (CochainComplex.mappingCone ((S.mapHomologicalComplex (.up ℤ)).map f)).Acyclic := by
    intro n
    exact (exactAt_iff_of_quasiIsoAt e.hom n).1 (hac n)
  have hq := (quasiIso_iff_acyclic_cone _).2 hac'
  have hcomm := extendMapTo_comm S (K := (S.mapHomologicalComplex (.up ℕ)).obj K)
    (K' := (S.mapHomologicalComplex (.up ℕ)).obj L) (𝟙 _) (𝟙 _)
    ((S.mapHomologicalComplex (.up ℕ)).map l) l (by simp)
  have heq : extendMap ((S.mapHomologicalComplex (.up ℕ)).map l) intEmbedding ≫
      (mapExtendIso S L).inv =
      (mapExtendIso S K).inv ≫ (S.mapHomologicalComplex (.up ℤ)).map f := by
    simpa [extendMapTo] using hcomm
  apply (quasiIso_extendMap_iff _ intEmbedding).1
  apply (quasiIso_iff_comp_right _ (mapExtendIso S L).inv).1
  rw [heq]
  infer_instance

end Sections


section Comparison

variable {A B : Type u} [CommRing A] [CommRing B]
  {X : SchemeOverRing A} {Z : SchemeOverRing B}
  (φ : A →+* B) (j : Z.left ⟶ X.left) [IsClosedImmersion j]
  (hj : j ≫ X.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom φ))

local notation "P" => Scheme.Modules.pushforward j
local notation "P₊" => Functor.mapHomologicalComplex (Scheme.Modules.pushforward j) (ComplexShape.up ℕ)
private abbrev restriction : ModuleCat.{u} B ⥤ ModuleCat.{u} A :=
  ModuleCat.restrictScalars φ

local notation "R" => restriction φ
local notation "R₊" => Functor.mapHomologicalComplex (restriction φ) (ComplexShape.up ℕ)
local notation "SX" => sectionsFunctor X
local notation "SZ" => sectionsFunctor Z
local notation "SX₊" => Functor.mapHomologicalComplex (sectionsFunctor X) (ComplexShape.up ℕ)
local notation "SZ₊" => Functor.mapHomologicalComplex (sectionsFunctor Z) (ComplexShape.up ℕ)

omit [IsClosedImmersion j] in
private lemma sectionComplexIso_inv_naturality {K L : CochainComplex Z.left.Modules ℕ}
    (a : K ⟶ L) :
    (R₊).map ((SZ₊).map a) ≫ (pushforwardSectionsComplexIso φ j hj L).inv =
      (pushforwardSectionsComplexIso φ j hj K).inv ≫ (SX₊).map ((P₊).map a) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact (pushforwardSectionsIso φ j hj).inv.naturality (a.f n)

set_option backward.isDefEq.respectTransparency false in
theorem inverseComparison_naturality {G G' : Z.left.Modules} (α : G ⟶ G')
    (J : InjectiveResolution G) (J' : InjectiveResolution G')
    (I : InjectiveResolution ((P).obj G)) (I' : InjectiveResolution ((P).obj G'))
    (l : (P₊).obj J.cocomplex ⟶ I.cocomplex)
    (l' : (P₊).obj J'.cocomplex ⟶ I'.cocomplex)
    (hl : LiftsIdentity (j := j) J I l) (hl' : LiftsIdentity (j := j) J' I' l')
    (n : ℕ) :
    (R).map ((cohomology Z n).map α) ≫ inverseComparisonOfLift φ hj J' I' l' n =
      inverseComparisonOfLift φ hj J I l n ≫ (cohomology X n).map ((P).map α) := by
  let a := InjectiveResolution.desc α J' J
  let b := InjectiveResolution.desc ((P).map α) I' I
  have ha : J.ι.f 0 ≫ a.f 0 = α ≫ J'.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero α J' J
  have hb : I.ι.f 0 ≫ b.f 0 = (P).map α ≫ I'.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero ((P).map α) I' I
  have hcomm : pushedAugmentation j J ≫ ((P₊).map a ≫ l') =
      pushedAugmentation j J ≫ (l ≫ b) := by
    apply fromSingle_eq
    simp only [comp_f, pushedAugmentation_f, Functor.mapHomologicalComplex_map_f]
    unfold LiftsIdentity at hl hl'
    rw [← Category.assoc, ← (P).map_comp, ha, (P).map_comp, Category.assoc,
      hl', ← Category.assoc, hl, hb]
  have q : PreservesFiniteColimits (P) := pushforwardExact j
  have hh := ((SX).mapHomotopy
    (homotopy_of_lift (pushedAugmentation j J) _ _ hcomm)).homologyMap_eq n
  change homologyMap ((SX₊).map ((P₊).map a ≫ l')) n =
    homologyMap ((SX₊).map (l ≫ b)) n at hh
  have hZ : (cohomology Z n).map α ≫ (J'.isoRightDerivedObj (SZ) n).hom =
      (J.isoRightDerivedObj (SZ) n).hom ≫ homologyMap ((SZ₊).map a) n :=
    InjectiveResolution.isoRightDerivedObj_hom_naturality α J J' a ha (SZ) n
  have hX : (I.isoRightDerivedObj (SX) n).inv ≫ (cohomology X n).map ((P).map α) =
      homologyMap ((SX₊).map b) n ≫ (I'.isoRightDerivedObj (SX) n).inv :=
    InjectiveResolution.isoRightDerivedObj_inv_naturality ((P).map α) I I' b hb (SX) n
  have hR :
      (R).map (homologyMap ((SZ₊).map a) n) ≫
        (restrictCohomologyIso φ ((SZ₊).obj J'.cocomplex) n).hom =
      (restrictCohomologyIso φ ((SZ₊).obj J.cocomplex) n).hom ≫
        homologyMap ((R₊).map ((SZ₊).map a)) n :=
    ShortComplex.mapHomologyIso_inv_naturality ((shortComplexFunctor _ _ n).map ((SZ₊).map a)) (R)
  have hH := congrArg (fun t => homologyMap t n) (sectionComplexIso_inv_naturality φ j hj a)
  simp only [homologyMap_comp] at hH
  unfold inverseComparisonOfLift
  simp only [homologyMap_comp, Category.assoc]
  rw [← (R).map_comp_assoc, hZ, (R).map_comp, Category.assoc,
    reassoc_of% hR, reassoc_of% hH, hX]
  simp only [← homologyMap_comp_assoc, ← Functor.map_comp, hh]

private def chosenLift (G : Z.left.Modules) :
    (P₊).obj (injectiveResolution G).cocomplex ⟶
      (injectiveResolution ((P).obj G)).cocomplex :=
  (exists_lift j _ _).choose

private lemma chosenLift_spec (G : Z.left.Modules) :
    LiftsIdentity (j := j) (injectiveResolution G) (injectiveResolution ((P).obj G))
      (chosenLift j G) :=
  (exists_lift j _ _).choose_spec

/-- The closed-immersion comparison, natural in the coefficient module sheaf. -/
def closedImmersionCohomologyIso (n : ℕ) :
    (P) ⋙ cohomology X n ≅ cohomology Z n ⋙ (R) := by
  symm
  refine NatIso.ofComponents (fun G => ?_) (fun {G G'} α => ?_)
  · let J := injectiveResolution G
    let I := injectiveResolution ((P).obj G)
    let l := chosenLift j G
    have hq := sections_quasiIso j J I l (chosenLift_spec j G)
    exact (R).mapIso (J.isoRightDerivedObj (SZ) n) ≪≫
      restrictCohomologyIso φ ((SZ₊).obj J.cocomplex) n ≪≫
      asIso (homologyMap ((pushforwardSectionsComplexIso φ j hj J.cocomplex).inv ≫
        (SX₊).map l) n) ≪≫ (I.isoRightDerivedObj (SX) n).symm
  · exact inverseComparison_naturality φ j hj α _ _ _ _
      (chosenLift j G) (chosenLift j G') (chosenLift_spec j G) (chosenLift_spec j G') n

theorem closedImmersionCohomologyIso_inv_app (n : ℕ) {G : Z.left.Modules}
    (J : InjectiveResolution G) (I : InjectiveResolution ((P).obj G))
    (l : (P₊).obj J.cocomplex ⟶ I.cocomplex) (hl : LiftsIdentity (j := j) J I l) :
    inverseComparisonOfLift φ hj J I l n = (closedImmersionCohomologyIso φ j hj n).inv.app G := by
  have h := inverseComparison_naturality φ j hj (𝟙 G) J _ I _
    l (chosenLift j G) hl (chosenLift_spec j G) n
  have he : inverseComparisonOfLift φ hj J I l n =
      inverseComparisonOfLift φ hj (injectiveResolution G) (injectiveResolution ((P).obj G))
        (chosenLift j G) n := by
    simpa only [(cohomology Z n).map_id, (cohomology X n).map_id, (P).map_id, (R).map_id,
      Category.id_comp, Category.comp_id] using h.symm
  rw [he]
  rfl

end Comparison

theorem comparison : Specs.ClosedImmersionCohomology.Comparison.{u} := by
  intro A B _ _ X Z φ j _ hj n
  refine ⟨closedImmersionCohomologyIso φ j hj n, fun G J I => ⟨exists_lift j J I, ?_⟩⟩
  intro l hl
  exact ⟨sections_quasiIso j J I l hl, closedImmersionCohomologyIso_inv_app φ j hj n J I l hl⟩

end LinearAlgebraicGroups.ClosedImmersionCohomology
