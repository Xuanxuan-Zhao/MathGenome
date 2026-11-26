import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.DerivedFlagCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.DerivedFlagCohomology

open _root_.LinearAlgebraicGroups.Specs
open Specs.DerivedFlagCohomology
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection AssociatedBundle)
open Specs.FlagCohomology (FlagKernelPair flagLineData flagLineSheaf flagCohomology CovarianceData)
open Specs.QuotientEmbedding (Presentation)
open Specs.CharacterDescent (Character)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.CentralDerived (IsCentralProduct)
open Specs.AssociatedFlagLineSheaves (QuotientMap)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

open private projection_eq_iff locallySurjective_of_fppf
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding
open private compareRepresentatives compareRepresentatives_projection
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient

private theorem quotientIsoOfLocalLifts {A : GroupScheme k} (B : ClosedSubgroup A)
    {Y : SchemeOver k} (q : A.X ⟶ Y)
    [Presheaf.IsLocallySurjective (fppfOver k) ((fppfOver k).uliftYoneda.{u + 1}.map q).hom]
    (hq : ∀ (T : SchemeOver k) (g h : T ⟶ A.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ SubgroupSections B T) :
    ∃ e : rightQuotientSheaf B ≅ schemeFppfSheaf Y,
      rightQuotientProjection B ≫ e.hom = (fppfOver k).uliftYoneda.map q := by
  let p : rightCosetPresheaf B ⟶ (schemeFppfSheaf Y).obj :=
    { app T := ↾fun z ↦ Quotient.lift (fun g ↦ ULift.up (g ≫ q))
        (fun g h he ↦ congrArg ULift.up ((hq T.unop g h).2 (QuotientGroup.leftRel_apply.mp he)))
        z.down
      naturality := by
        intro T U f
        ext ⟨z⟩
        induction z using QuotientGroup.induction_on with
        | H g => exact congrArg ULift.up (Category.assoc f.unop g q) }
  have hp : rightCosetProjection B ≫ p = ((fppfOver k).uliftYoneda.map q).hom := by
    ext T ⟨g⟩
    rfl
  letI : Presheaf.IsLocallySurjective (fppfOver k) p :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (fppfOver k) hp
  letI : Presheaf.IsLocallyInjective (fppfOver k) p := by
    apply Presheaf.isLocallyInjective_of_injective
    rintro T ⟨a⟩ ⟨b⟩
    induction a using QuotientGroup.induction_on with
    | H g =>
      induction b using QuotientGroup.induction_on with
      | H h =>
        intro he
        exact congrArg ULift.up (QuotientGroup.eq.mpr ((hq T.unop g h).1 (ULift.up.inj he)))
  let φ : rightQuotientSheaf B ⟶ schemeFppfSheaf Y :=
    ⟨sheafifyLift (fppfOver k) p (schemeFppfSheaf Y).property⟩
  have hφ : toSheafify (fppfOver k) (rightCosetPresheaf B) ≫ φ.hom = p :=
    toSheafify_sheafifyLift _ _ _
  haveI : Sheaf.IsLocallySurjective φ :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (fppfOver k) hφ
  haveI : Sheaf.IsLocallyInjective φ :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac (fppfOver k) p hφ
  haveI : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso φ).mp ⟨inferInstance, inferInstance⟩
  refine ⟨asIso φ, ?_⟩
  apply (sheafToPresheaf _ _).map_injective
  change (rightCosetProjection B ≫ toSheafify (fppfOver k) _) ≫ φ.hom = _
  rw [Category.assoc, hφ, hp]
  rfl

open private affineProduct from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private commute_from_centre from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralTorus

variable {D Z : ClosedSubgroup G.val} {C : ClosedSubgroup Z.group}

/-- Under the central product, a right coset represented by `(z,d)` is
represented by `d` whenever the Borel contains the central factor. -/
private theorem centralProduct_quotient
    {B : ClosedSubgroup G.val} (Q : Presentation B)
    (m : (C.group ⊗ D.group) ⟶ G.val) (hm : IsCentralProduct C D m)
    (hC : Centralizes (𝟙 G.val) (C.inclusion ≫ Z.inclusion).hom.hom)
    (b : C.group ⟶ B.group) (hb : b ≫ B.inclusion = C.inclusion ≫ Z.inclusion) :
    m.hom.hom ≫ Q.projection = snd C.group.X D.group.X ≫ D.inclusion.hom.hom ≫ Q.projection := by
  let x := snd C.group.X D.group.X ≫ D.inclusion.hom.hom
  let z := fst C.group.X D.group.X ≫ (C.inclusion ≫ Z.inclusion).hom.hom
  have hz : z = (fst C.group.X D.group.X ≫ b.hom.hom) ≫ B.inclusion.hom.hom := by
    change z = fst C.group.X D.group.X ≫ (b ≫ B.inclusion).hom.hom
    rw [hb]
  have hc : Commute z x := commute_from_centre hC _ _
  change m.hom.hom ≫ Q.projection = x ≫ Q.projection
  rw [show m.hom.hom = z * x from hm, hc.eq]
  apply ((projection_eq_iff Q x (x * z)).2 ?_).symm
  rw [inv_mul_cancel_left]
  exact ⟨_, hz.symm⟩

private theorem derivedFlagIso {B : ClosedSubgroup G.val} {B' : ClosedSubgroup D.group}
    (r : B'.group ⟶ B.group)
    (hr : IsPullback B'.inclusion.hom.hom r.hom.hom D.inclusion.hom.hom B.inclusion.hom.hom)
    (Q : Presentation B) (Q' : Presentation B')
    (m : (C.group ⊗ D.group) ⟶ G.val) (hm : IsCentralProduct C D m)
    (hC : Centralizes (𝟙 G.val) (C.inclusion ≫ Z.inclusion).hom.hom)
    (b : C.group ⟶ B.group) (hb : b ≫ B.inclusion = C.inclusion ≫ Z.inclusion)
    (hf : Flat m.hom.hom.left) (hs : Surjective m.hom.hom.left) :
    ∃ (e : Q'.scheme ≅ Q.scheme),
      Q'.projection ≫ e.hom = D.inclusion.hom.hom ≫ Q.projection ∧
      Q'.quotientIso.inv ≫ rightQuotientMap D.inclusion r
          (Grp.hom_ext _ _ hr.w) ≫ Q.quotientIso.hom =
        (fppfOver k).uliftYoneda.map e.hom := by
  let q := D.inclusion.hom.hom ≫ Q.projection
  let J := fppfOver k
  let Y := J.uliftYoneda.{u + 1}
  let F := affineProduct (closedSubgroupAlgebraicGroup
    (Specs.GeometricBorelConjugacy.subgroupOfSubgroup Z C)) (closedSubgroupAlgebraicGroup D)
  haveI : LocallyOfFiniteType F.val.X.hom := F.property.2.1
  haveI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  haveI : IsLocallyNoetherian G.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
  haveI : LocallyOfFiniteType (m.hom.hom.left ≫ G.val.X.hom) := by
    rw [Over.w]; exact F.property.2.1
  haveI := locallyOfFiniteType_of_comp m.hom.hom.left G.val.X.hom
  haveI : LocallyOfFinitePresentation m.hom.hom.left := inferInstance
  letI := Q.flat
  letI := Q.surjective
  letI := Q.finitePresentation
  letI := hf
  letI := hs
  letI : Flat (m.hom.hom ≫ Q.projection).left := by
    change Flat (m.hom.hom.left ≫ Q.projection.left)
    infer_instance
  letI : Surjective (m.hom.hom ≫ Q.projection).left := by
    change Surjective (m.hom.hom.left ≫ Q.projection.left)
    infer_instance
  letI : LocallyOfFinitePresentation (m.hom.hom ≫ Q.projection).left := by
    change LocallyOfFinitePresentation (m.hom.hom.left ≫ Q.projection.left)
    infer_instance
  haveI := locallySurjective_of_fppf (m.hom.hom ≫ Q.projection)
  haveI : Presheaf.IsLocallySurjective J (Y.map q).hom := by
    apply Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (f₁ := (Y.map (snd C.group.X D.group.X)).hom)
      (f₃ := (Y.map (m.hom.hom ≫ Q.projection)).hom)
    change (Y.map (snd C.group.X D.group.X) ≫ Y.map q).hom = _
    rw [← Functor.map_comp, ← centralProduct_quotient Q m hm hC b hb]
  have hq (T : SchemeOver k) (g h : T ⟶ D.group.X) :
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ SubgroupSections B' T := by
    simp only [q, ← Category.assoc]
    rw [projection_eq_iff]
    change (∃ t : T ⟶ B.group.X,
        t ≫ B.inclusion.hom.hom = (g ≫ D.inclusion.hom.hom)⁻¹ *
          (h ≫ D.inclusion.hom.hom)) ↔
      ∃ t' : T ⟶ B'.group.X, t' ≫ B'.inclusion.hom.hom = g⁻¹ * h
    rw [← GrpObj.inv_comp, ← MonObj.mul_comp]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨hr.lift (g⁻¹ * h) t ht.symm,
        hr.lift_fst _ _ _⟩
    · rintro ⟨t, ht⟩
      exact ⟨t ≫ r.hom.hom, by
        rw [Category.assoc, ← hr.w, ← Category.assoc, ht]⟩
  obtain ⟨v, hv⟩ := quotientIsoOfLocalLifts B' q hq
  let e := compareRepresentatives Q' v
  refine ⟨e, compareRepresentatives_projection Q' q v hv, ?_⟩
  have hv' : v.hom = rightQuotientMap D.inclusion r
      (Grp.hom_ext _ _ hr.w) ≫ Q.quotientIso.hom := by
    letI : Sheaf.IsLocallySurjective (rightQuotientProjection B') :=
      LinearAlgebraicGroups.rightQuotientLocalLifts B'
    apply (cancel_epi (rightQuotientProjection B')).mp
    rw [hv, ← Category.assoc]
    have hmap : rightQuotientProjection B' ≫
        rightQuotientMap D.inclusion r (Grp.hom_ext _ _ hr.w) =
        Y.map D.inclusion.hom.hom ≫ rightQuotientProjection B := by
      apply (sheafToPresheaf _ _).map_injective
      ext T ⟨g⟩
      exact rightQuotientMapOnLifts D.inclusion r
        (Grp.hom_ext _ _ hr.w) (T := T.unop) g
    rw [hmap, Category.assoc, Q.quotientProjection, ← Functor.map_comp]
  change _ = Y.map (compareRepresentatives Q' v).hom
  rw [compareRepresentatives, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  exact congrArg (Q'.quotientIso.inv ≫ ·) hv'.symm

section Coefficients

open LinearAlgebraicGroups.AssociatedFlagLineSheaves (realizeSections associatedSheafPullback)
open Specs.AssociatedFlagLineSheaves (CompatibleCharacters pullFunction)
open LinearAlgebraicGroups.Representation.FlagCohomology
  (covarianceMap_app covariancePullback_exists isCohomologyMap_of_isIso)
open private covarianceDifference from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves
open private covariancePullback_app pushforwardEquivalenceOfIso exists_associatedBundle
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

variable {P : OppositeBorelPair G} {Q : Presentation P.negative}
    {a : ModObj G.val.X Q.scheme} {p : BorelProjection P} {χ : Character P.torus.group}

private theorem covarianceDifference_eq (h : FlagKernelPair Q) :
    covarianceDifference Q p χ = (flagLineData Q p χ h).covariance := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext f : 1
  change (covarianceDifference Q p χ).app U.unop f =
    (flagLineData Q p χ h).covariance.app U.unop f
  unfold CovarianceData.covariance
  rw [covarianceMap_app]
  let X := (G.val.X ⨯ P.negative.group.X).left
  let V := ((prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X) ≫ Q.projection).left ⁻¹ᵁ U.unop
  let R := Γ(X, V)
  exact congrArg (fun t : R => _ - t) (mul_comm _ _)

private theorem realizationIso (L : AssociatedBundle Q a p χ) (h : FlagKernelPair Q) :
    ∃ e : (realizeSections L).sheaf ≅ flagLineSheaf Q p χ h,
      ∀ U x, (flagLineData Q p χ h).inclusion.app U (e.hom.app U x) =
        (realizeSections L).functions.app U x := by
  let M := realizeSections L
  let F := flagLineData Q p χ h
  have hz : M.functions ≫ F.covariance = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x : 1
    change F.covariance.app U.unop (M.functions.app U.unop x) = 0
    rw [← covarianceDifference_eq h]
    exact x.property
  let f : M.sheaf ⟶ F.sheaf := kernel.lift F.covariance M.functions hz
  have hcomp (U : Q.scheme.left.Opens) (x : Γ(M.sheaf, U)) :
      F.inclusion.app U (f.app U x) = M.functions.app U x :=
    ConcreteCategory.congr_hom (congrArg (fun a => a.app U)
      (kernel.lift_ι F.covariance M.functions hz)) x
  have hf : IsIso f := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · intro x y hxy
      apply M.functions_injective U
      rw [← hcomp, ← hcomp, hxy]
    · intro y
      let x : Γ(M.sheaf, U) := ⟨F.inclusion.app U y, by
        change (covarianceDifference Q p χ).app U (F.inclusion.app U y) = 0
        rw [covarianceDifference_eq h]
        exact ConcreteCategory.congr_hom
          (congrArg (fun a => a.app U) (kernel.condition F.covariance)) y⟩
      refine ⟨x, ?_⟩
      let E := SheafOfModules.evaluation Q.scheme.left.ringCatSheaf (op U)
      letI : Mono (E.map F.inclusion) := E.map_mono F.inclusion
      apply (ModuleCat.mono_iff_injective (E.map F.inclusion)).mp inferInstance
      exact hcomp U x
  exact ⟨asIso f, hcomp⟩

variable {G' : AffineAlgebraicGroup k} {P' : OppositeBorelPair G'}
    {Q' : Presentation P'.negative} {p' : BorelProjection P'} {χ' : Character P'.torus.group}

private theorem flagCoefficientIso (f : QuotientMap Q' Q) [IsIso f.flag.left]
    (hχ : CompatibleCharacters f p' p χ' χ) (h : FlagKernelPair Q) (h' : FlagKernelPair Q') :
    let F := flagLineData Q p χ h
    let F' := flagLineData Q' p' χ' h'
    ∃ α : F.sheaf ⟶ (Scheme.Modules.pushforward f.flag.left).obj F'.sheaf,
      F.IsPullbackMap F' f.flag.left f.group.hom.hom.left
        (congrArg Over.Hom.left f.commutesFlag.symm) α ∧ IsIso α := by
  let F := flagLineData Q p χ h
  let F' := flagLineData Q' p' χ' h'
  let j := prod.map f.group.hom.hom f.borel.hom.hom
  have hb := congrArg (fun g : P'.negative.group ⟶ G.val ↦ g.hom.hom) f.commutesBorel
  have h₁ : j ≫ F.second = F'.second ≫ f.group.hom.hom := by
    change j ≫ Specs.HomogeneousQuotient.rightMultiplication P.negative =
      Specs.HomogeneousQuotient.rightMultiplication P'.negative ≫ f.group.hom.hom
    simp only [Specs.HomogeneousQuotient.rightMultiplication, MonObj.comp_mul, MonObj.mul_comp,
      j, prod.map_fst, Category.assoc, prod.map_snd_assoc]
    exact congrArg (_ * ·) (congrArg (prod.snd ≫ ·) hb.symm)
  have hc : j.left.appTop F.multiplier = F'.multiplier := by
    let t : (G.val.X ⨯ P.negative.group.X) ⟶ _ :=
      prod.snd⁻¹ ≫ (p.projection ≫ χ).hom.hom
    let t' : (G'.val.X ⨯ P'.negative.group.X) ⟶ _ :=
      prod.snd⁻¹ ≫ (p'.projection ≫ χ').hom.hom
    have ht : j ≫ t = t' := by
      have he := congrArg (fun g : Character P'.negative.group ↦ g.hom.hom) hχ
      change (p'.projection ≫ χ').hom.hom =
        f.borel.hom.hom ≫ (p.projection ≫ χ).hom.hom at he
      change j ≫ (prod.snd⁻¹ ≫ (p.projection ≫ χ).hom.hom) = _
      rw [← Category.assoc, GrpObj.comp_inv,
        show j ≫ prod.snd = prod.snd ≫ f.borel.hom.hom from prod.map_snd _ _,
        ← GrpObj.inv_comp, Category.assoc, ← he]
    change (t.left.appTop ≫ j.left.appTop) _ = t'.left.appTop _
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, ht]
  obtain ⟨α, hα⟩ := covariancePullback_exists F F' f.flag.left f.group.hom.hom.left
    (congrArg Over.Hom.left f.commutesFlag.symm) j.left
    (congrArg Over.Hom.left (prod.map_fst f.group.hom.hom f.borel.hom.hom))
    (congrArg Over.Hom.left h₁) hc
  refine ⟨α, hα, ?_⟩
  obtain ⟨_, _, _, V, hv, hm, hf, a, _, _, ha⟩ :=
    (LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q
  obtain ⟨_, _, _, V', hv', hm', hf', a', _, _, ha'⟩ :=
    (LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G' P').2.2 Q'
  obtain ⟨L⟩ := exists_associatedBundle Q p χ a ha
  obtain ⟨L'⟩ := exists_associatedBundle Q' p' χ' a' ha'
  let M := realizeSections L
  let M' := realizeSections L'
  obtain ⟨i, hi⟩ := realizationIso L h
  obtain ⟨i', hi'⟩ := realizationIso L' h'
  obtain ⟨b, hb⟩ := associatedSheafPullback M' M f hχ
  let R := Scheme.Modules.pushforward f.flag.left
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f.flag.left
  letI : R.IsEquivalence := (pushforwardEquivalenceOfIso f.flag.left).isEquivalence_functor
  let β := adj.homEquiv M.sheaf M'.sheaf b.hom
  haveI : IsIso β := by
    change IsIso (adj.homEquiv M.sheaf M'.sheaf b.hom)
    rw [Adjunction.homEquiv_unit]
    infer_instance
  have he : i.hom ≫ α = β ≫ R.map i'.hom := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro x
    let W := f.flag.left ⁻¹ᵁ U
    let E := SheafOfModules.evaluation Q'.scheme.left.ringCatSheaf (op W)
    letI : Mono (E.map F'.inclusion) := E.map_mono F'.inclusion
    apply (ModuleCat.mono_iff_injective (E.map F'.inclusion)).mp inferInstance
    change F'.inclusion.app W (α.app U (i.hom.app U x)) =
      F'.inclusion.app W (i'.hom.app W (β.app U x))
    rw [hi']
    exact (covariancePullback_app hα U (i.hom.app U x)).trans
      (by
        change pullFunction f U (F.inclusion.app U (i.hom.app U x)) =
          M'.functionVal W (β.app U x)
        rw [hi]
        exact (hb U x).symm)
  have hh : α = i.inv ≫ β ≫ R.map i'.hom := by
    rw [← he, Iso.inv_hom_id_assoc]
  rw [hh]
  infer_instance

end Coefficients

section TorusRestriction

open Specs.GeometricRadicals (IsReductive IsSemisimple IsTorus IsSplitTorus IsMaximalTorus)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.CharacterDescent (StandardLattice)
open Specs.IntegralCentralQuotient (fibreGroup IntegralRing)
open private mulMap surjectiveOnSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private image_of_geometric_torus
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
open private reductive_of_semisimple diagonalIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private isTorus_iff_coordinates torus_of_iso conjugate conjugationIso comp_conjugate conjugate_comp
  conjugate_mul transportSubgroup maximal_of_square
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private lattice_torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private geometricallyMaximal_of_maximal_split maximalTorus_of_geometricallyMaximal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private torus_smooth_connected_solvable
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private factors_through_closed_of_rational_points subgroup_of_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private splitPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private integralTorus productTorusIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
open private fibreHopfSpectrumIso monoidAlgebra_scalarExtension
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralCentralQuotient

open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent

variable [IsAlgClosed k]

private theorem splitOverAlgClosed (A : AffineAlgebraicGroup k) (h : IsTorus A.val) :
    IsSplitTorus A.val :=
  split_of_torus ((isTorus_iff_coordinates A).mp h)

omit [IsAlgClosed k] in
private theorem groupConnected (A : AffineAlgebraicGroup k) (h : IsReductive A) :
    ConnectedSpace A.val.X.left := by
  letI := h.2.1
  exact GeometricallyConnected.connectedSpace_of_subsingleton A.val.X.hom

omit [IsAlgClosed k] in
private theorem productTorus {A B : GroupScheme k} (ha : IsSplitTorus A) (hb : IsSplitTorus B) :
    IsTorus (A ⊗ B) := by
  obtain ⟨r, ⟨a⟩⟩ := splitPresentation ha
  obtain ⟨s, ⟨b⟩⟩ := splitPresentation hb
  let X := StandardLattice.{u} r
  let Y := StandardLattice.{u} s
  letI : Algebra IntegralRing.{u} k := (Int.castRingHom k).comp ULift.ringEquiv.toRingHom |>.toAlgebra
  let F := fibreGroup k (R := IntegralRing.{u})
  let e (L : Type u) [CommGroup L] :
      F.obj (integralTorus L) ≅ specGroup (Specs.DiagonalizableGroups.groupAlgebra k L) :=
    fibreHopfSpectrumIso k (MonoidAlgebra IntegralRing.{u} L) ≪≫
      ((hopfSpec (CommRingCat.of k)).mapIso
        (CommHopfAlgCat.isoMk (monoidAlgebra_scalarExtension (R := IntegralRing.{u}) k L)).op).symm
  let eA : F.obj (integralTorus X) ≅ A := e X ≪≫ a
  let eB : F.obj (integralTorus Y) ≅ B := e Y ≪≫ b
  let eXY : StandardLattice.{u} (r + s) ≃* (X × Y) :=
    { toFun := fun v => (v ∘ Fin.castAdd s, v ∘ Fin.natAdd r)
      invFun := fun w i => Fin.addCases w.1 w.2 i
      left_inv := by
        intro v
        funext i
        refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp [Function.comp_def]
      right_inv := by
        intro w
        apply Prod.ext <;> funext i <;> simp
      map_mul' := fun _ _ => rfl }
  let iso := F.mapIso (productTorusIso X Y) ≪≫
    (Functor.Monoidal.μIso F _ _).symm ≪≫ MonoidalCategory.tensorIso eA eB
  obtain ⟨eStd⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) (r + s)
  exact lattice_torus_of_split
    ⟨r + s, ⟨iso.symm ≪≫ e (X × Y) ≪≫ diagonalIso eXY ≪≫ eStd⟩⟩

private theorem centralProductPoint
    (m : (C.group ⊗ D.group) ⟶ G.val) (hm : IsCentralProduct C D m)
    (hs : Surjective m.hom.hom.left) (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    ∃ (z : 𝟙_ (SchemeOver k) ⟶ C.group.X) (d : 𝟙_ (SchemeOver k) ⟶ D.group.X),
      (z ≫ (C.inclusion ≫ Z.inclusion).hom.hom) * (d ≫ D.inclusion.hom.hom) = g := by
  let F := affineProduct (closedSubgroupAlgebraicGroup (subgroupOfSubgroup Z C))
    (closedSubgroupAlgebraicGroup D)
  obtain ⟨x, hx⟩ := surjectiveOnSections (G := F) (Q := G) m hs g
  refine ⟨x ≫ fst _ _, x ≫ snd _ _, ?_⟩
  rw [← hx, hm, MonObj.comp_mul]
  rfl

omit [IsAlgClosed k] in
private theorem commutesWithDerivedFactor {S : ClosedSubgroup D.group}
    (hC : Centralizes (𝟙 G.val) (C.inclusion ≫ Z.inclusion).hom.hom)
    (z : 𝟙_ (SchemeOver k) ⟶ C.group.X) (d : 𝟙_ (SchemeOver k) ⟶ D.group.X)
    (h : Centralizes (S.inclusion ≫ D.inclusion)
      ((z ≫ (C.inclusion ≫ Z.inclusion).hom.hom) * (d ≫ D.inclusion.hom.hom))) :
    Centralizes S.inclusion d := by
  letI := D.isClosedImmersion
  letI : Mono D.inclusion.hom.hom := Over.mono_of_mono_left _
  apply (centralizes_iff _ _).mpr
  intro U x y
  have hh := (centralizes_iff _ _).mp h U x y
  let a := x ≫ z ≫ (C.inclusion ≫ Z.inclusion).hom.hom
  let b := x ≫ d ≫ D.inclusion.hom.hom
  let c := y ≫ S.inclusion.hom.hom ≫ D.inclusion.hom.hom
  have hz : Commute a c := commute_from_centre hC (x ≫ z) c
  have hd : (a * b) * c = c * (a * b) := by
    have hS : (S.inclusion ≫ D.inclusion).hom.hom =
        S.inclusion.hom.hom ≫ D.inclusion.hom.hom := rfl
    simpa only [MonObj.comp_mul, Category.assoc, hS, a, b, c] using hh.eq
  apply (cancel_mono D.inclusion.hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp]
  change b * c = c * b
  apply mul_left_cancel (a := a)
  calc
    a * (b * c) = (a * b) * c := (mul_assoc _ _ _).symm
    _ = c * (a * b) := hd
    _ = a * (c * b) := by rw [← mul_assoc, ← hz.eq, mul_assoc]

private theorem markedDerivedTorus (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (hD : IsReductive (closedSubgroupAlgebraicGroup D))
    (hC : IsTorus C.group) (hc : Centralizes (𝟙 G.val) (C.inclusion ≫ Z.inclusion).hom.hom)
    (m : (C.group ⊗ D.group) ⟶ G.val) (hm : IsCentralProduct C D m)
    (hs : Surjective m.hom.hom.left) :
    ∃ (S : ClosedSubgroup D.group) (s : S.group ⟶ T.group),
      IsSplitTorus S.group ∧ IsGeometricallyMaximal S ∧
      IsPullback S.inclusion.hom.hom s.hom.hom D.inclusion.hom.hom T.inclusion.hom.hom := by
  let H := closedSubgroupAlgebraicGroup D
  let C₀ := closedSubgroupAlgebraicGroup (subgroupOfSubgroup Z C)
  obtain ⟨S, hS, hSm⟩ := MaximalToriExist.geometricallyMaximalTorusExists H hD.1 (groupConnected H hD)
  let S₀ := closedSubgroupAlgebraicGroup (G := H) S
  have hSs := splitOverAlgClosed S₀ hS
  have hcent := Reductive.TorusCentralizer.maximalTorusCentralizer H hD S hS hSm
  obtain ⟨v, hv⟩ := mulMap (C.inclusion ≫ Z.inclusion) (S.inclusion ≫ D.inclusion) hc
  obtain ⟨A, a, hA, ha⟩ := image_of_geometric_torus (G := affineProduct C₀ S₀) (Q := G)
    v (productTorus (splitOverAlgClosed C₀ hC) hSs)
  let l : S.group ⟶ A.group := lift (0 : S.group ⟶ C.group) (𝟙 S.group) ≫ a
  have hl : l ≫ A.inclusion = S.inclusion ≫ D.inclusion := by
    apply Grp.hom_ext
    change ((lift (0 : S.group ⟶ C.group) (𝟙 S.group) ≫ a) ≫ A.inclusion).hom.hom = _
    rw [Category.assoc, ha]
    change (lift (0 : S.group ⟶ C.group) (𝟙 S.group)).hom.hom ≫ v.hom.hom = _
    rw [hv]
    change (lift (0 : S.group ⟶ C.group).hom.hom (𝟙 S.group.X)) ≫
      ((fst C.group.X S.group.X ≫ (C.inclusion ≫ Z.inclusion).hom.hom) *
        (snd C.group.X S.group.X ≫ (S.inclusion ≫ D.inclusion).hom.hom)) = _
    simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, Category.id_comp]
    change (1 : S.group.X ⟶ C.group.X) ≫ (C.inclusion ≫ Z.inclusion).hom.hom *
      (S.inclusion ≫ D.inclusion).hom.hom = _
    rw [MonObj.one_comp, one_mul]
  have hAm : IsMaximalTorus A := by
    refine ⟨hA, ?_⟩
    intro V hV hAV
    obtain ⟨aV, haV⟩ := hAV
    have hvS : (l ≫ aV) ≫ V.inclusion = S.inclusion ≫ D.inclusion := by
      rw [Category.assoc, haV, hl]
    let V₀ := closedSubgroupAlgebraicGroup V
    haveI : Smooth V.group.X.hom := (torus_smooth_connected_solvable V₀ hV).1
    letI : IsReduced V.group.X.left := isReduced_of_smooth_over_field V.group.X.hom
    letI : LocallyOfFiniteType V.group.X.hom := V₀.property.2.1
    letI : IsCommMonObj V.group.X := torus_commutative V₀ hV
    apply subgroup_of_sections
    apply factors_through_closed_of_rational_points A.inclusion.hom.hom A.isClosedImmersion
    intro x
    obtain ⟨z, d, hd⟩ := centralProductPoint m hm hs (x ≫ V.inclusion.hom.hom)
    have hcd : Centralizes S.inclusion d := by
      apply commutesWithDerivedFactor hc z d
      rw [hd]
      apply (centralizes_iff _ _).mpr
      intro U w y
      have hh := (Commute.all (w ≫ x) (y ≫ (l ≫ aV).hom.hom)).map
        (IsMonHom.monoidHom V.inclusion.hom.hom U)
      change Commute ((w ≫ x) ≫ V.inclusion.hom.hom)
        ((y ≫ (l ≫ aV).hom.hom) ≫ V.inclusion.hom.hom) at hh
      have hvS' : (l ≫ aV).hom.hom ≫ V.inclusion.hom.hom =
          (S.inclusion ≫ D.inclusion).hom.hom :=
        congrArg (fun f : S.group ⟶ G.val ↦ f.hom.hom) hvS
      simpa only [Category.assoc, hvS'] using hh
    obtain ⟨y, hy⟩ := (hcent _ _).mp hcd
    refine ⟨lift z y ≫ a.hom.hom, ?_⟩
    rw [Category.assoc]
    change lift z y ≫ (a ≫ A.inclusion).hom.hom = _
    rw [ha, hv]
    simp only [MonObj.comp_mul, Grp.comp_hom_hom, Grp.fst_hom_hom, Grp.snd_hom_hom,
      lift_fst_assoc, lift_snd_assoc]
    change (z ≫ (C.inclusion ≫ Z.inclusion).hom.hom) *
      (y ≫ S.inclusion.hom.hom ≫ D.inclusion.hom.hom) = _
    rw [← Category.assoc y, hy]
    exact hd
  obtain ⟨g, e, he⟩ := MaximalToriConjugate.maximalToriConjugate G hG.1 (groupConnected G hG)
    A T hAm (maximalTorus_of_geometricallyMaximal G T (lattice_torus_of_split hT) hTm)
  obtain ⟨z, d, hzd⟩ := centralProductPoint m hm hs g
  let j := conjugationIso d
  let S' := transportSubgroup j S
  let s := l ≫ e.hom
  have hS'm := maximal_of_square j S S' (Iso.refl _) (Category.id_comp _)
    (maximalTorus_of_geometricallyMaximal H S hS hSm)
  have hS'mg := geometricallyMaximal_of_maximal_split H S' hS'm hSs
  have hcomm : S'.inclusion ≫ D.inclusion = s ≫ T.inclusion := by
    apply Grp.hom_ext
    change (S.inclusion.hom.hom ≫ conjugate d (𝟙 D.group.X)) ≫ D.inclusion.hom.hom =
      l.hom.hom ≫ (e.hom ≫ T.inclusion).hom.hom
    have hconj : (S.inclusion.hom.hom ≫ conjugate d (𝟙 D.group.X)) =
        conjugate d S.inclusion.hom.hom :=
      (comp_conjugate S.inclusion.hom.hom d (𝟙 D.group.X)).trans
        (congrArg (conjugate d) (Category.comp_id S.inclusion.hom.hom))
    rw [hconj, conjugate_comp, he]
    change conjugate (d ≫ D.inclusion.hom.hom) (S.inclusion.hom.hom ≫ D.inclusion.hom.hom) =
      l.hom.hom ≫ conjugate g A.inclusion.hom.hom
    rw [comp_conjugate]
    have hl' := congrArg (fun a : S.group ⟶ G.val ↦ a.hom.hom) hl
    change l.hom.hom ≫ A.inclusion.hom.hom = _ at hl'
    rw [hl', ← hzd, conjugate_mul]
    let a₀ := (toUnit S.group.X ≫ z) ≫ (C.inclusion ≫ Z.inclusion).hom.hom
    let x₀ := conjugate (d ≫ D.inclusion.hom.hom) ((S.inclusion ≫ D.inclusion).hom.hom)
    have hc' : Commute a₀ x₀ := commute_from_centre hc (toUnit S.group.X ≫ z) x₀
    change x₀ = a₀ * x₀ * a₀⁻¹
    rw [hc'.eq, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨S', s, hSs, hS'mg, ?_⟩
  haveI := S'.isClosedImmersion
  haveI : Mono S'.inclusion.hom.hom := Over.mono_of_mono_left _
  haveI := T.isClosedImmersion
  haveI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  haveI := D.isClosedImmersion
  haveI : Mono D.inclusion.hom.hom := Over.mono_of_mono_left _
  haveI : IsCommMonObj T.group.X :=
    torus_commutative (closedSubgroupAlgebraicGroup T) (lattice_torus_of_split hT)
  refine IsPullback.mk' (congrArg (fun a : S'.group ⟶ G.val ↦ a.hom.hom) hcomm) ?_ ?_
  · intro U v w h₁ h₂
    exact (cancel_mono S'.inclusion.hom.hom).mp h₁
  · intro U d t hdt
    have hd : Centralizes S'.inclusion d := by
      apply (centralizes_iff _ _).mpr
      intro W x y
      have hh := (Commute.all (x ≫ t) (y ≫ s.hom.hom)).map
        (IsMonHom.monoidHom T.inclusion.hom.hom W)
      have hh' := congrArg (fun a : S'.group ⟶ G.val ↦ a.hom.hom) hcomm
      change S'.inclusion.hom.hom ≫ D.inclusion.hom.hom =
        s.hom.hom ≫ T.inclusion.hom.hom at hh'
      apply (cancel_mono D.inclusion.hom.hom).mp
      simp only [MonObj.mul_comp, Category.assoc, hdt, hh']
      exact hh.eq
    obtain ⟨w, hw⟩ := (Reductive.TorusCentralizer.maximalTorusCentralizer H hD S'
      hS'm.1 hS'mg U d).mp hd
    refine ⟨w, hw, (cancel_mono T.inclusion.hom.hom).mp ?_⟩
    rw [Category.assoc, ← show S'.inclusion.hom.hom ≫ D.inclusion.hom.hom =
      s.hom.hom ≫ T.inclusion.hom.hom from congrArg (fun a : S'.group ⟶ G.val ↦ a.hom.hom) hcomm,
      ← Category.assoc, hw, hdt]

end TorusRestriction

section BorelRestriction

open Specs.GeometricRadicals (IsReductive IsTorus IsSplitTorus IsUnipotentRadical)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel IsSmoothConnectedSolvable subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open CocharacterDynamics (multiplyFactors)
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private lattice_torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private torus_smooth_connected_solvable from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private solvable_iff_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private splitKernel_product from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private torus_multiplicativeType from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private borel_of_proper_quotient from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private isKBorel_iff_of_isAlgClosed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private geometricallyConnected_of_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry

private theorem eqOnSplitKernel {B T K L : GroupScheme k}
    (p : B ⟶ T) (j : T ⟶ B) (i : K ⟶ B)
    (hj : j ≫ p = 𝟙 _) (hk : IsPullback i.hom.hom (toUnit _) p.hom.hom η[T.X])
    [Mono i.hom.hom] (f g : B ⟶ L)
    (ht : j ≫ f = j ≫ g) (hu : i ≫ f = i ≫ g) : f = g := by
  letI := splitKernel_product j p i hj hk (inferInstance : Mono i.hom.hom)
  apply Grp.hom_ext
  apply (cancel_epi (multiplyFactors j i)).mp
  have ht' : j.hom.hom ≫ f.hom.hom = j.hom.hom ≫ g.hom.hom :=
    congrArg (fun h : T ⟶ L ↦ h.hom.hom) ht
  have hu' : i.hom.hom ≫ f.hom.hom = i.hom.hom ≫ g.hom.hom :=
    congrArg (fun h : K ⟶ L ↦ h.hom.hom) hu
  simp only [multiplyFactors, MonObj.mul_comp, Category.assoc, ht', hu']

private theorem splitProjectionProperties [IsAlgClosed k] {B T : GroupScheme k}
    (p : B ⟶ T) (j : T ⟶ B) (U : AffineAlgebraicGroup k) (i : U.val ⟶ B)
    (hj : j ≫ p = 𝟙 _) (hk : IsPullback i.hom.hom (toUnit _) p.hom.hom η[T.X])
    [Mono i.hom.hom] (hu : Smooth U.val.X.hom) (hc : ConnectedSpace U.val.X.left) :
    Smooth p.hom.hom.left ∧ GeometricallyConnected p.hom.hom.left := by
  let m := multiplyFactors j i
  letI : IsIso m := splitKernel_product j p i hj hk inferInstance
  letI : IsIso m.left := (Over.forget _).map_isIso m
  have hmp : m ≫ p.hom.hom = fst T.X U.val.X := by
    have hp : j.hom.hom ≫ p.hom.hom = 𝟙 T.X :=
      congrArg (fun f : T ⟶ T ↦ f.hom.hom) hj
    change ((fst T.X U.val.X ≫ j.hom.hom) * (snd T.X U.val.X ≫ i.hom.hom)) ≫ p.hom.hom = _
    simp only [MonObj.mul_comp, Category.assoc, hp, Category.comp_id, hk.w]
    rw [← Category.assoc (snd T.X U.val.X), comp_toUnit]
    exact mul_one _
  have hl := congrArg Over.Hom.left hmp
  change m.left ≫ p.hom.hom.left = pullback.fst T.X.hom U.val.X.hom at hl
  let b := IsPullback.of_hasPullback T.X.hom U.val.X.hom
  letI := hc
  have hgc := geometricallyConnected_of_connected U
  constructor
  · apply (MorphismProperty.cancel_left_of_respectsIso @Smooth m.left _).mp
    rw [hl]
    exact MorphismProperty.of_isPullback b.flip hu
  · apply (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected m.left _).mp
    rw [hl]
    exact MorphismProperty.of_isPullback b.flip hgc

variable [IsAlgClosed k]

/-- The scheme intersection of a marked Borel with the derived group is
a Borel. Its projection to the marked derived torus is the base change
of the original Borel projection. -/
private theorem restrictBorel {T B : ClosedSubgroup G.val} {S : ClosedSubgroup D.group}
    (s : S.group ⟶ T.group)
    (hS : IsPullback S.inclusion.hom.hom s.hom.hom D.inclusion.hom.hom T.inclusion.hom.hom)
    (hSt : IsSplitTorus S.group) (hD : IsReductive (closedSubgroupAlgebraicGroup D))
    (hB : IsBorel B)
    (R : ClosedSubgroup B.group) (j : T.group ⟶ B.group) (p : B.group ⟶ T.group)
    (hR : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) R)
    (hj : j ≫ B.inclusion = T.inclusion) (hp : j ≫ p = 𝟙 _) (hk : IsSchemeKernel p R)
    {A : AffineAlgebraicGroup k} (q : G.val ⟶ A.val) (hq : IsSchemeKernel q D) (hA : IsTorus A.val)
    (Q : Presentation B) (hQ : IsProper Q.scheme.hom)
    (m : (C.group ⊗ D.group) ⟶ G.val) (hm : IsCentralProduct C D m)
    (hC : Centralizes (𝟙 G.val) (C.inclusion ≫ Z.inclusion).hom.hom)
    (c : C.group ⟶ T.group) (hc : c ≫ T.inclusion = C.inclusion ≫ Z.inclusion)
    (hf : Flat m.hom.hom.left) (hs : Surjective m.hom.hom.left) :
    ∃ (B' : ClosedSubgroup D.group) (r : B'.group ⟶ B.group),
      IsPullback B'.inclusion.hom.hom r.hom.hom D.inclusion.hom.hom B.inclusion.hom.hom ∧
      IsKBorel B' ∧ IsSubgroupOf S B' := by
  let H := closedSubgroupAlgebraicGroup D
  let U := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup B) R
  letI := R.isClosedImmersion
  letI : Mono R.inclusion.hom.hom := Over.mono_of_mono_left _
  have hz : R.inclusion ≫ (B.inclusion ≫ q) = 0 :=
    LinearAlgebraicGroups.Unipotent.homFromUnipotentToMultiplicativeType U A _
      hR.2.1 (torus_multiplicativeType ((isTorus_iff_coordinates A).mp hA))
  have hqB : B.inclusion ≫ q = p ≫ (T.inclusion ≫ q) := by
    apply eqOnSplitKernel p j R.inclusion hp hk
    · rw [← Category.assoc j B.inclusion, hj, ← Category.assoc j p, hp, Category.id_comp]
    · rw [hz, ← Category.assoc, show R.inclusion ≫ p = 0 from Grp.hom_ext _ _ hk.w, zero_comp]
  let b₀ : pullback D.inclusion B.inclusion ⟶ D.group := pullback.fst _ _
  let r₀ : pullback D.inclusion B.inclusion ⟶ B.group := pullback.snd _ _
  have hpb : IsPullback b₀.hom.hom r₀.hom.hom D.inclusion.hom.hom B.inclusion.hom.hom :=
    (IsPullback.of_hasPullback D.inclusion B.inclusion).map (Grp.forget (SchemeOver k))
  have hib : IsClosedImmersion b₀.hom.hom.left :=
    MorphismProperty.of_isPullback (hpb.flip.map (Over.forget _)) B.isClosedImmersion
  let B' : ClosedSubgroup D.group := ⟨_, b₀, hib⟩
  have hbr : IsClosedImmersion r₀.hom.hom.left :=
    MorphismProperty.of_isPullback (hpb.map (Over.forget _)) D.isClosedImmersion
  have hSk : IsPullback s.hom.hom (toUnit S.group.X)
      (T.inclusion.hom.hom ≫ q.hom.hom) η[A.val.X] := by
    simpa only [comp_toUnit] using hS.flip.paste_vert hq
  have hBk : IsPullback r₀.hom.hom (toUnit B'.group.X)
      (p.hom.hom ≫ T.inclusion.hom.hom ≫ q.hom.hom) η[A.val.X] := by
    have w : B.inclusion.hom.hom ≫ q.hom.hom =
        p.hom.hom ≫ T.inclusion.hom.hom ≫ q.hom.hom :=
      congrArg (fun f : B.group ⟶ A.val ↦ f.hom.hom) hqB
    rw [← w]
    simpa only [comp_toUnit] using hpb.flip.paste_vert hq
  let t := hSk.lift (r₀.hom.hom ≫ p.hom.hom) (toUnit _) (by
    rw [Category.assoc, hBk.w])
  have ht : t ≫ s.hom.hom = r₀.hom.hom ≫ p.hom.hom := hSk.lift_fst _ _ _
  have hBk' : IsPullback r₀.hom.hom (t ≫ toUnit S.group.X)
      (p.hom.hom ≫ (T.inclusion.hom.hom ≫ q.hom.hom)) η[A.val.X] := by
    simpa only [comp_toUnit] using hBk
  have htpb : IsPullback t r₀.hom.hom s.hom.hom p.hom.hom := (hBk'.of_bot ht.symm hSk).flip
  obtain ⟨hps, hpc⟩ := splitProjectionProperties p j U R.inclusion hp hk hR.1.1 hR.1.2.1
  obtain ⟨hSs, hSc, _⟩ :=
    torus_smooth_connected_solvable (closedSubgroupAlgebraicGroup (G := H) S)
      (lattice_torus_of_split hSt)
  letI : ConnectedSpace S.group.X.left := hSc
  letI : Smooth S.group.X.hom := hSs
  haveI : Smooth t.left := MorphismProperty.of_isPullback (htpb.flip.map (Over.forget _)) hps
  haveI : GeometricallyConnected t.left :=
    MorphismProperty.of_isPullback (htpb.flip.map (Over.forget _)) hpc
  have hBs : Smooth B'.group.X.hom := by
    rw [← Over.w t]
    infer_instance
  have hBc : ConnectedSpace B'.group.X.left :=
    GeometricallyConnected.connectedSpace t.left t.left.isOpenMap
  have hBS : IsSmoothConnectedSolvable B' := by
    letI := hbr
    letI : Mono r₀.hom.hom := Over.mono_of_mono_left _
    letI : Group.IsSolvable (𝟙_ (SchemeOver k) ⟶ B.group.X) :=
      (solvable_iff_sections (closedSubgroupAlgebraicGroup B) hB.1.1 hB.1.2.1).mp hB.1.2.2
    refine ⟨hBs, hBc, (solvable_iff_sections
      (closedSubgroupAlgebraicGroup (G := H) B') hBs hBc).mpr ?_⟩
    exact Group.isSolvable_of_isSolvable_injective (f := IsMonHom.monoidHom r₀.hom.hom _)
      (fun _ _ h ↦ (cancel_mono r₀.hom.hom).mp h)
  obtain ⟨Q'⟩ := (LinearAlgebraicGroups.HomogeneousQuotient.homogeneousQuotient k H B').1
  obtain ⟨e, _, _⟩ := derivedFlagIso r₀ hpb Q Q' m hm hC (c ≫ j)
    (by rw [Category.assoc, hj, hc]) hf hs
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  haveI : IsProper Q.scheme.hom := hQ
  have hQ' : IsProper Q'.scheme.hom := by rw [← Over.w e.hom]; infer_instance
  have hB' : IsKBorel B' := (isKBorel_iff_of_isAlgClosed H B').mpr
    (borel_of_proper_quotient H hD.1 (groupConnected H hD) B' hBS Q' hQ')
  have hcomm : S.inclusion ≫ D.inclusion = (s ≫ j) ≫ B.inclusion := by
    rw [Category.assoc, hj]
    exact Grp.hom_ext _ _ hS.w
  exact ⟨B', r₀, hpb, hB', pullback.lift S.inclusion (s ≫ j) hcomm, pullback.lift_fst _ _ _⟩

end BorelRestriction

section Opposition

open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors pairing)
open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics (LimitDecomposition oppositeCocharacter existsLimitDecomposition
  multiplyFactors oppositeLimitIntersection lieImage)
open private oppositeCocharacter_eq_inv oppositePositiveRoots from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
open private pairing_inv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private root_weight_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private subgroupOf_trans from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

private theorem sectionOfSubgroup {M : GroupScheme k} {A B : ClosedSubgroup M}
    (h : IsSubgroupOf A B) {X : SchemeOver k} {x : X ⟶ M.X}
    (hx : x ∈ SubgroupSections A X) : x ∈ SubgroupSections B X := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨a, ha⟩ := hx
  refine ⟨a ≫ i.hom.hom, ?_⟩
  have w : i.hom.hom ≫ B.inclusion.hom.hom = A.inclusion.hom.hom :=
    congrArg (fun f : A.group ⟶ M ↦ f.hom.hom) hi
  change a ≫ A.inclusion.hom.hom = x at ha
  change (a ≫ i.hom.hom) ≫ B.inclusion.hom.hom = x
  simpa only [Category.assoc, w] using ha

private theorem oppositeBorelsIntersection (P : OppositeBorelPair G) {X : SchemeOver k}
    {x : X ⟶ G.val.X} (hx : x ∈ SubgroupSections P.positive X)
    (hy : x ∈ SubgroupSections P.negative X) : x ∈ SubgroupSections P.torus X := by
  let T := P.torus
  let B := P.positive
  let B' := P.negative
  obtain ⟨commT, ⟨datum⟩⟩ :=
    RootData.AbstractPairing.abstractPairing G P.reductive T P.split P.maximal
  letI := commT
  let BC := RootData.BorelsAndChambers.borelsThroughT G P.reductive T P.split P.maximal
  obtain ⟨c, L, hc, hB, hpos⟩ := BC.1 B P.positiveBorel P.inPositive
  have hcopp (α : ↥(absoluteRoots T)) :
      pairing T.group α.val (oppositeCocharacter c) = -pairing T.group α.val c := by
    rw [oppositeCocharacter_eq_inv, ← datum.pairing_eq, ← datum.pairing_eq]
    exact map_neg _ _
  have hreg : IsRegular T (oppositeCocharacter c) := by
    intro α
    rw [hcopp]
    exact neg_ne_zero.mpr (hc α)
  have hop : oppositeCocharacter c ≫ T.inclusion = oppositeCocharacter (c ≫ T.inclusion) := by
    change (_ ≫ c) ≫ T.inclusion = _ ≫ c ≫ T.inclusion
    exact Category.assoc _ _ _
  have hMprops (d : Cocharacter G.val) (M : LimitDecomposition d)
      (hd : oppositeCocharacter c ≫ T.inclusion = d) :
      SameSubgroup M.centralizer T ∧ IsKBorel M.parabolic ∧
        IsSubgroupOf T M.parabolic ∧ subgroupRoots T M.parabolic = positiveRoots T (oppositeCocharacter c) := by
    subst d
    obtain ⟨h₁, h₂, h₃, h₄, _⟩ :=
      RootData.BorelsAndChambers.regularCocharacterBorel G P.reductive T P.split P.maximal _ hreg M
    exact ⟨h₁, h₂, h₃, h₄⟩
  obtain ⟨M⟩ := existsLimitDecomposition G (oppositeCocharacter (c ≫ T.inclusion))
  obtain ⟨hMT, hMB, hMsub, hMroots⟩ := hMprops _ M hop
  have hM : IsSubgroupOf B' M.parabolic := by
    let A := subgroupRoots T M.parabolic
    have hb : subgroupRoots T B' = A := by
      change subgroupRoots T B' = subgroupRoots T M.parabolic
      rw [hMroots, oppositePositiveRoots datum hc, ← hpos]
      exact P.opposite
    have hA := (RootData.BorelsAndChambers.positiveSystemsFromCocharacters G P.reductive T
      P.split P.maximal A).mpr ⟨oppositeCocharacter c, hreg, hMroots.symm⟩
    obtain ⟨Z, hZ, hTZ, hZR, hu⟩ := (BC.2 A).mp hA
    exact subgroupOf_trans (hu B' P.negativeBorel P.inNegative hb).2
      (hu M.parabolic hMB hMsub rfl).1
  have hxL := sectionOfSubgroup hB.1 hx
  obtain ⟨y, hy'⟩ := sectionOfSubgroup hM hy
  let m := multiplyFactors M.sectionMap M.contractingToParabolic
  letI : IsIso m := M.product_iso
  let v := y ≫ inv m
  let z := v ≫ fst _ _ ≫ M.centralizer.inclusion.hom.hom
  let w := v ≫ snd _ _ ≫ M.contracting.inclusion.hom.hom
  have he : z * w = x := by
    have eq : v ≫ m ≫ M.parabolic.inclusion.hom.hom = x := by
      simpa [v, Iso.inv_hom_id_assoc] using hy'
    have h₁ : M.sectionMap.hom.hom ≫ M.parabolic.inclusion.hom.hom =
        M.centralizer.inclusion.hom.hom :=
      congrArg (fun f : M.centralizer.group ⟶ G.val ↦ f.hom.hom) M.section_in_G
    have h₂ : M.contractingToParabolic.hom.hom ≫ M.parabolic.inclusion.hom.hom =
        M.contracting.inclusion.hom.hom :=
      congrArg (fun f : M.contracting.group ⟶ G.val ↦ f.hom.hom) M.contracting_in_G
    simpa only [z, w, m, multiplyFactors, MonObj.mul_comp, MonObj.comp_mul, Category.assoc,
      h₁, h₂] using eq
  have hzT : z ∈ SubgroupSections T X :=
    sectionOfSubgroup hMT.1 ⟨v ≫ fst _ _, rfl⟩
  have hzL : z ∈ SubgroupSections L.parabolic X :=
    sectionOfSubgroup hB.1 (sectionOfSubgroup P.inPositive hzT)
  have hwL : w ∈ SubgroupSections L.parabolic X := by
    have hh := (SubgroupSections L.parabolic X).mul_mem
      ((SubgroupSections L.parabolic X).inv_mem hzL) hxL
    rwa [← he, inv_mul_cancel_left] at hh
  obtain ⟨l, hl⟩ := hwL
  have hid : w = 1 := by
    have hPB : IsPullback (η[M.contracting.group.X]) (η[L.parabolic.group.X])
        M.contracting.inclusion.hom.hom L.parabolic.inclusion.hom.hom := by
      exact oppositeLimitIntersection G _ L M
    have h : v ≫ snd _ _ ≫ M.contracting.inclusion.hom.hom =
        l ≫ L.parabolic.inclusion.hom.hom := hl.symm
    have hh := hPB.lift_fst (v ≫ snd _ _) l (by simpa only [Category.assoc] using h)
    change ((v ≫ snd _ _) ≫ M.contracting.inclusion.hom.hom) = 1
    rw [← hh, Category.assoc, IsMonHom.one_hom]
    exact congrArg (· ≫ η[G.val.X]) (toUnit_unique _ _)
  rw [hid, mul_one] at he
  exact he ▸ hzT


/-- The restricted Borels have disjoint root sets because a tangent point
belonging to both belongs to the scheme intersection with the marked torus. -/
private theorem derivedRootSetsDisjoint (P : OppositeBorelPair G)
    {S A B : ClosedSubgroup D.group}
    (hs : IsSplitTorus S.group) (hm : IsGeometricallyMaximal S)
    (hD : IsReductive (closedSubgroupAlgebraicGroup D))
    (s : S.group ⟶ P.torus.group) (a : A.group ⟶ P.positive.group)
    (b : B.group ⟶ P.negative.group)
    (hsq : IsPullback S.inclusion.hom.hom s.hom.hom D.inclusion.hom.hom P.torus.inclusion.hom.hom)
    (haq : IsPullback A.inclusion.hom.hom a.hom.hom D.inclusion.hom.hom P.positive.inclusion.hom.hom)
    (hbq : IsPullback B.inclusion.hom.hom b.hom.hom D.inclusion.hom.hom P.negative.inclusion.hom.hom) :
    Disjoint (subgroupRoots S A) (subgroupRoots S B) := by
  let H := closedSubgroupAlgebraicGroup D
  apply Set.disjoint_left.mpr
  intro α hαA hαB
  obtain ⟨hα, v, hv, hv0⟩ := α.property
  obtain ⟨x, hx⟩ := hαA hv
  obtain ⟨y, hy⟩ := hαB hv
  let R := CommAlgCat.of k (DualNumber k)
  let W := (testSpec k).obj (op R)
  let v₀ : W ⟶ D.group.X := v.toMul.val
  let g := v₀ ≫ D.inclusion.hom.hom
  have hx' : x.toMul.val ≫ A.inclusion.hom.hom = v₀ :=
    congrArg (fun w : Lie k D.group ↦ w.toMul.val) hx
  have hy' : y.toMul.val ≫ B.inclusion.hom.hom = v₀ :=
    congrArg (fun w : Lie k D.group ↦ w.toMul.val) hy
  have hgA : g ∈ SubgroupSections P.positive W := by
    refine ⟨x.toMul.val ≫ a.hom.hom, ?_⟩
    change (x.toMul.val ≫ a.hom.hom) ≫ P.positive.inclusion.hom.hom = g
    rw [Category.assoc, ← haq.w, ← Category.assoc, hx']
  have hgB : g ∈ SubgroupSections P.negative W := by
    refine ⟨y.toMul.val ≫ b.hom.hom, ?_⟩
    change (y.toMul.val ≫ b.hom.hom) ≫ P.negative.inclusion.hom.hom = g
    rw [Category.assoc, ← hbq.w, ← Category.assoc, hy']
  obtain ⟨z, hz⟩ := oppositeBorelsIntersection P hgA hgB
  have hz' : z ≫ P.torus.inclusion.hom.hom = v₀ ≫ D.inclusion.hom.hom := hz
  let u := hsq.lift v₀ z hz'.symm
  have hu : u ≫ S.inclusion.hom.hom = v₀ := hsq.lift_fst _ _ _
  letI := S.isClosedImmersion
  letI : Mono S.inclusion.hom.hom := Over.mono_of_mono_left _
  have hu₀ : reduceTangentPoints S.group u = 1 := by
    apply (cancel_mono S.inclusion.hom.hom).mp
    change (((testSpec k).map (dualReduction k).op ≫ u) ≫ S.inclusion.hom.hom) =
      (1 : Points S.group.X (CommAlgCat.of k k)) ≫ S.inclusion.hom.hom
    rw [Category.assoc, hu, MonObj.one_comp]
    exact v.toMul.property
  let t : Lie k S.group := ⟨u, hu₀⟩
  have h₁ : v ∈ adjointWeightVectors S 1 :=
    (RootData.RootGroups.rootSubgroups H hD S hs hm).1.2 ▸
      (show v ∈ Set.range (mapPointKernel S.inclusion) from ⟨t, Subtype.ext hu⟩)
  exact hα (root_weight_unique H S hs hv0 hv h₁)

private theorem oppositeFromDisjoint (H : AffineAlgebraicGroup k) (hH : IsReductive H)
    {S A B : ClosedSubgroup H.val} (hs : IsSplitTorus S.group)
    (hm : IsGeometricallyMaximal S) (hA : IsKBorel A) (hB : IsKBorel B)
    (ha : IsSubgroupOf S A) (hb : IsSubgroupOf S B)
    (hdis : Disjoint (subgroupRoots S A) (subgroupRoots S B)) :
    Specs.OpenCell.AreOpposite S A B := by
  let BC := RootData.BorelsAndChambers.borelsThroughT H hH S hs hm
  obtain ⟨a, _, ha₀, _, haR⟩ := BC.1 A hA ha
  obtain ⟨b, _, hb₀, _, hbR⟩ := BC.1 B hB hb
  unfold Specs.OpenCell.AreOpposite
  ext α
  change α ∈ subgroupRoots S B ↔ α ∉ subgroupRoots S A
  constructor
  · exact fun h h' ↦ Set.disjoint_left.mp hdis h' h
  · intro hα
    by_contra hβ
    have hinv : α.val⁻¹ ∈ absoluteRoots S :=
      ((RootData.RootGroups.rootSubgroups H hH S hs hm).2 α.val α.property).2.1
        _ |>.mpr (Or.inr rfl) |>.1
    let α' : ↥(absoluteRoots S) := ⟨α.val⁻¹, hinv⟩
    have hpair (c : Cocharacter S.group) :
        pairing S.group α'.val c = -pairing S.group α.val c :=
      pairing_inv S.group hs _ _
    rw [haR] at hα
    rw [hbR] at hβ
    change ¬ 0 < pairing S.group α.val a at hα
    change ¬ 0 < pairing S.group α.val b at hβ
    have hhA : α' ∈ subgroupRoots S A := by
      rw [haR]
      change 0 < pairing S.group α'.val a
      rw [hpair]
      have := ha₀ α
      omega
    have hhB : α' ∈ subgroupRoots S B := by
      rw [hbR]
      change 0 < pairing S.group α'.val b
      rw [hpair]
      have := hb₀ α
      omega
    exact Set.disjoint_left.mp hdis hhA hhB

end Opposition

section Comparison

open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.AssociatedFlagLineSheaves (CompatibleCharacters)
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private lattice_torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private torus_multiplicativeType from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting

private theorem restrictedBorelProjection {P : OppositeBorelPair G}
    {P' : OppositeBorelPair (closedSubgroupAlgebraicGroup D)} (r : Restriction D P P')
    (p : BorelProjection P) (p' : BorelProjection P') :
    r.negative ≫ p.projection = p'.projection ≫ r.torus := by
  have hB : P'.negative.inclusion ≫ D.inclusion = r.negative ≫ P.negative.inclusion :=
    Grp.hom_ext _ _ r.negativePullback.w
  have hT : P'.torus.inclusion ≫ D.inclusion = r.torus ≫ P.torus.inclusion :=
    Grp.hom_ext _ _ r.torusPullback.w
  letI := P.negative.isClosedImmersion
  letI : Mono P.negative.inclusion.hom.hom := Over.mono_of_mono_left _
  have hk : p'.inclusion ≫ r.negative = r.torus ≫ p.inclusion := by
    apply Grp.hom_ext
    apply (cancel_mono P.negative.inclusion.hom.hom).mp
    have hh : (p'.inclusion ≫ r.negative) ≫ P.negative.inclusion =
        (r.torus ≫ p.inclusion) ≫ P.negative.inclusion := by
      rw [Category.assoc, ← hB, ← Category.assoc, p'.inclusion_comp,
        Category.assoc, p.inclusion_comp, hT]
    exact congrArg (fun f : P'.torus.group ⟶ G.val ↦ f.hom.hom) hh
  letI := p'.radical.isClosedImmersion
  letI : Mono p'.radical.inclusion.hom.hom := Over.mono_of_mono_left _
  apply eqOnSplitKernel p'.projection p'.inclusion p'.radical.inclusion
    p'.section_projection p'.isKernel
  · rw [← Category.assoc p'.inclusion, hk, Category.assoc, p.section_projection,
      Category.comp_id, ← Category.assoc p'.inclusion, p'.section_projection, Category.id_comp]
  · have h := LinearAlgebraicGroups.Unipotent.homFromUnipotentToMultiplicativeType
      (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup
        (G := closedSubgroupAlgebraicGroup D) P'.negative) p'.radical)
      (closedSubgroupAlgebraicGroup P.torus) (p'.radical.inclusion ≫ (r.negative ≫ p.projection))
      p'.isRadical.2.1 (torus_multiplicativeType
        ((isTorus_iff_coordinates (closedSubgroupAlgebraicGroup P.torus)).mp
          (lattice_torus_of_split P.split)))
    rw [h, ← Category.assoc, show p'.radical.inclusion ≫ p'.projection = 0 from
      Grp.hom_ext _ _ p'.isKernel.w, zero_comp]

private theorem comparesOfCentralProduct {P : OppositeBorelPair G}
    {P' : OppositeBorelPair (closedSubgroupAlgebraicGroup D)} (r : Restriction D P P')
    (m : (C.group ⊗ D.group) ⟶ G.val) (hm : IsCentralProduct C D m)
    (hC : Centralizes (𝟙 G.val) (C.inclusion ≫ Z.inclusion).hom.hom)
    (b : C.group ⟶ P.negative.group) (hb : b ≫ P.negative.inclusion = C.inclusion ≫ Z.inclusion)
    (hf : Flat m.hom.hom.left) (hs : Surjective m.hom.hom.left)
    (Q : Presentation P.negative) (p : BorelProjection P)
    (χ : Character P.torus.group) (h : FlagKernelPair Q)
    (Q' : Presentation P'.negative) (p' : BorelProjection P') (h' : FlagKernelPair Q') :
    Compares r Q p χ h Q' p' h' := by
  obtain ⟨e, w, he⟩ := derivedFlagIso r.negative r.negativePullback Q Q' m hm hC b hb hf hs
  let f : QuotientMap Q' Q :=
    ⟨D.inclusion, r.negative, e.hom, Grp.hom_ext _ _ r.negativePullback.w, w⟩
  letI : IsIso f.flag.left := (Over.forget _).map_isIso e.hom
  let χ' : Character P'.torus.group := r.torus ≫ χ
  have hχ : CompatibleCharacters f p' p χ' χ := by
    change p'.projection ≫ r.torus ≫ χ = (r.negative ≫ p.projection) ≫ χ
    rw [restrictedBorelProjection r p p', Category.assoc]
  obtain ⟨α, hα, hIso⟩ := flagCoefficientIso f hχ h h'
  letI := hIso
  refine ⟨e, w, α, he, hα, hIso, fun n ↦ ?_⟩
  exact LinearAlgebraicGroups.Representation.FlagCohomology.isCohomologyMap_of_isIso
    f.flag.left (by simp [f]) α n

end Comparison

open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive)
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private centralInclusion from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
open private isKBorel_iff_of_isAlgClosed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer

/-- Inclusion of the derived group identifies the marked flags and the
cohomology of every associated line bundle with that of its restricted character. -/
theorem derivedFlagComparison : DerivedFlagComparison.{u} := by
  intro k _ _ G P
  obtain ⟨D, hD⟩ := LinearAlgebraicGroups.SchemeDerivedGroup.derivedSubgroupExists G
  let H := closedSubgroupAlgebraicGroup D
  let hss := Reductive.CentralDerived.derivedSemisimple G P.reductive D hD
  have hHr : IsReductive H := reductive_of_semisimple H hss
  obtain ⟨Z, hZ, C, hC, _⟩ := Reductive.CentralDerived.centralTorusExists G P.reductive
  obtain ⟨m, hm, _⟩ := Reductive.CentralDerived.centralProductKernel G P.reductive Z hZ C hC D hD
  obtain ⟨hf, hs⟩ := Reductive.CentralDerived.centralProductFaithfullyFlat G P.reductive Z hZ C hC D hD m hm
  have hcen := centralInclusion hZ C
  obtain ⟨c, hc⟩ := Classification.CentralIsogenies.kernel_le_maximalTorus
    RootData.SchemeCentre.schemeCentre G P.reductive P.torus P.split P.maximal
    (subgroupOfSubgroup Z C) hcen
  obtain ⟨S, s, hSt, hSm, hS⟩ := markedDerivedTorus P.reductive P.torus P.split P.maximal
    hHr hC.1 hcen m hm hs
  obtain ⟨A, q, hq, _, hAt⟩ := Reductive.CentralDerived.derivedTorusQuotient G P.reductive D hD
  let rev : OppositeBorelPair G :=
    { P with
      positive := P.negative
      negative := P.positive
      positiveBorel := P.negativeBorel
      negativeBorel := P.positiveBorel
      inPositive := P.inNegative
      inNegative := P.inPositive
      opposite := by
        change Specs.BorelsAndChambers.subgroupRoots P.torus P.positive =
          (Specs.BorelsAndChambers.subgroupRoots P.torus P.negative)ᶜ
        rw [P.opposite, compl_compl] }
  let neg := LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P
  let pos := LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G rev
  obtain ⟨p₁⟩ := pos.1
  obtain ⟨Q₁⟩ := pos.2.1
  obtain ⟨p₂⟩ := neg.1
  obtain ⟨Q₂⟩ := neg.2.1
  obtain ⟨B₁, r₁, h₁, hB₁, hSB₁⟩ := restrictBorel s hS hSt hHr
    ((isKBorel_iff_of_isAlgClosed G P.positive).mp P.positiveBorel)
    p₁.radical p₁.inclusion p₁.projection p₁.isRadical p₁.inclusion_comp p₁.section_projection
    p₁.isKernel q hq hAt Q₁ ((pos.2.2 Q₁).2.1) m hm hcen c hc hf hs
  obtain ⟨B₂, r₂, h₂, hB₂, hSB₂⟩ := restrictBorel s hS hSt hHr
    ((isKBorel_iff_of_isAlgClosed G P.negative).mp P.negativeBorel)
    p₂.radical p₂.inclusion p₂.projection p₂.isRadical p₂.inclusion_comp p₂.section_projection
    p₂.isKernel q hq hAt Q₂ ((neg.2.2 Q₂).2.1) m hm hcen c hc hf hs
  let P' : OppositeBorelPair H :=
    ⟨S, B₁, B₂, hHr, hSt, hSm, hB₁, hB₂, hSB₁, hSB₂,
      oppositeFromDisjoint H hHr hSt hSm hB₁ hB₂ hSB₁ hSB₂
        (derivedRootSetsDisjoint P hSt hSm hHr s r₁ r₂ hS h₁ h₂)⟩
  let r : Restriction D P P' := ⟨s, r₁, r₂, hS, h₁, h₂⟩
  let geo := LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k H P'
  refine ⟨D, P', r, hD, hss, geo.1, geo.2.1, fun Q p χ h Q' p' h' ↦ ?_⟩
  exact comparesOfCentralProduct r m hm hcen (c ≫ p.inclusion) (by
    rw [Category.assoc, p.inclusion_comp]
    exact hc) hf hs Q p χ h Q' p' h'

end

end LinearAlgebraicGroups.Representation.DerivedFlagCohomology
