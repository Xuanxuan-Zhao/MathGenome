import Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import LinearAlgebraicGroups.Descent.AutomorphismSequence
import LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import LinearAlgebraicGroups.Descent.RelativeFormComparison
import LinearAlgebraicGroups.Descent.PinnedPairDescent
import LinearAlgebraicGroups.Descent.BorelInnerAlignment
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Group

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

universe u v w

namespace LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

open NonabelianCohomology
open Specs.QuasiSplitInnerForms

theorem outerFiberCriterion : OuterFiberCriterion.{u,v,w} := by
  intro Γ M D _ _ _ _ _ _ _ ρ ρD p hp he hsurj hact a y
  refine Quotient.inductionOn y (fun c => ?_)
  change classOf (mapCocycle p hp he c) = classOf (mapCocycle p hp he a) ↔
    IsInnerTwist p a (classOf c)
  constructor
  · intro hc
    obtain ⟨t, ht⟩ := Quotient.exact hc
    obtain ⟨q, rfl⟩ := hsurj t
    have hq : Continuous (fun σ : Γ => ρ σ q) :=
      hact.comp (continuous_id.prodMk continuous_const)
    let b : Cocycle ρ :=
      ⟨fun σ => q⁻¹ * c σ * ρ σ q, (continuous_const.mul c.property.1).mul hq, by
        intro σ τ
        change q⁻¹ * c (σ * τ) * ρ (σ * τ) q =
          q⁻¹ * c σ * ρ σ q * ρ σ (q⁻¹ * c τ * ρ τ q)
        rw [c.property.2, map_mul ρ]
        simp only [MulAut.mul_apply, map_mul, map_inv]
        group⟩
    have hb (σ : Γ) : p (b σ) = p (a σ) := by
      change p (q⁻¹ * c σ * ρ σ q) = p (a σ)
      have h := ht σ
      change p (a σ) = (p q)⁻¹ * p (c σ) * ρD σ (p q) at h
      simpa only [map_mul, map_inv, he σ q] using h.symm
    let d : Cocycle (twistedAction a) :=
      ⟨fun σ => b σ * (a σ)⁻¹, b.property.1.mul a.property.1.inv, by
        intro σ τ
        change b (σ * τ) * (a (σ * τ))⁻¹ =
          b σ * (a σ)⁻¹ * (a σ * ρ σ (b τ * (a τ)⁻¹) * (a σ)⁻¹)
        rw [b.property.2, a.property.2, mul_inv_rev]
        simp only [map_mul, map_inv]
        group⟩
    have hcb : classOf c = classOf b := Quotient.sound ⟨q, fun _ => rfl⟩
    refine ⟨b, d, hcb.symm, fun σ => ⟨?_, ?_⟩⟩
    · change p (b σ * (a σ)⁻¹) = 1
      rw [map_mul, map_inv, hb, mul_inv_cancel]
    · change b σ = b σ * (a σ)⁻¹ * a σ
      group
  · rintro ⟨b, d, hb, hd⟩
    have hmap : mapCocycle p hp he b = mapCocycle p hp he a := by
      apply Subtype.ext
      funext σ
      change p (b σ) = p (a σ)
      rw [(hd σ).2, map_mul, (hd σ).1, one_mul]
    change mapH1 p hp he (classOf c) = mapH1 p hp he (classOf a)
    rw [← hb]
    exact congrArg classOf hmap

theorem outerFiberSection : OuterFiberSection.{u,v,w} := by
  intro Γ M D _ _ _ _ _ _ ρ ρD p hp he s hs se h x
  refine Quotient.inductionOn x (fun a => ?_)
  have ha : mapCocycle p hp he (mapCocycle s hs se a) = a := by
    apply Subtype.ext
    funext σ
    exact h (a σ)
  exact congrArg classOf ha

open Specs.AutomorphismSequence
open Specs.RelativeFormComparison
  (fieldTest fieldMap relativeAction automorphismAction transportedAut RelativeClassification
    Classification HopfConjugates)

theorem automorphismSequences : Specs.AutomorphismSequence.Statement.{u} :=
  AutomorphismSequence.automorphismSequence

theorem splitCoefficientMaps : SplitCoefficientMaps.{u} := by
  intro k S _ _ _ A P D l Q E
  let T := fieldTest k S
  let : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum S))
  have hfix (σ : Gal(S/k))
      (x : (constantGroup (k := k) (Aut D.toBased)).obj (op T)) :
      ((constantGroup (k := k) (Aut D.toBased)).map (fieldMap k S σ).op).hom x = x := by
    apply (constantEvaluation k S (Aut D.toBased)).injective
    change x.down _ = x.down _
    exact congrArg x.down (Subsingleton.elim _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro σ f
    change constantEvaluation k S _ ((E.outer.app (op T)).hom
      (((automorphisms P.pair.G.val).map (fieldMap k S σ).op).hom f)) =
      (1 : MulAut (Aut D.toBased)) (outerHom E f)
    have h := ConcreteCategory.congr_hom (E.outer.naturality (fieldMap k S σ).op) f
    change (E.outer.app (op T)).hom
      (((automorphisms P.pair.G.val).map (fieldMap k S σ).op).hom f) =
      ((constantGroup (k := k) (Aut D.toBased)).map (fieldMap k S σ).op).hom
        ((E.outer.app (op T)).hom f) at h
    rw [h, hfix]
    rfl
  · intro σ d
    change pinnedSection E ((1 : MulAut (Aut D.toBased)) d) =
      ((automorphisms P.pair.G.val).map (fieldMap k S σ).op).hom (pinnedSection E d)
    have h := ConcreteCategory.congr_hom (E.sectionMap.naturality (fieldMap k S σ).op)
      ((constantEvaluation k S (Aut D.toBased)).symm d)
    change (E.sectionMap.app (op T)).hom
      (((constantGroup (k := k) (Aut D.toBased)).map (fieldMap k S σ).op).hom _) = _ at h
    rw [hfix] at h
    exact h
  · intro d
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app E.rightInverse (op T)) ((constantEvaluation k S (Aut D.toBased)).symm d)
    change (E.outer.app (op T)).hom (pinnedSection E d) =
      (constantEvaluation k S (Aut D.toBased)).symm d at h
    change constantEvaluation k S _ ((E.outer.app (op T)).hom (pinnedSection E d)) = d
    rw [h, MulEquiv.apply_symm_apply]

theorem splitKernel : SplitKernel.{u} := by
  intro k S _ _ _ A P D l Q E f
  let e := constantEvaluation k S (Aut D.toBased)
  change e (E.outer.app (op (fieldTest k S)) f) = 1 ↔ _
  rw [← map_one e, e.injective.eq_iff]
  exact E.exact _ f

theorem differenceOfTrivializations : DifferenceOfTrivializations.{u} := by
  intro k S _ _ _ G H J i j σ
  apply Aut.ext
  apply Iso.ext
  change ((restrictIso (fieldMap k S σ) i).inv ≫ (restrictIso (fieldMap k S σ) j).hom) ≫
    j.inv ≫ i.hom =
    i.inv ≫ (((i.hom ≫ (restrictIso (fieldMap k S σ) i).inv) ≫
      (restrictIso (fieldMap k S σ) j).hom ≫ j.inv) ≫ i.hom)
  simp [Category.assoc]

theorem changeOfTrivialization : ChangeOfTrivialization.{u} := by
  intro k S _ _ _ G H i b σ
  apply Aut.ext
  apply Iso.ext
  change ((restrictIso (fieldMap k S σ) b.asIso).hom ≫
      (restrictIso (fieldMap k S σ) i).hom) ≫ i.inv ≫ b.asIso.inv =
    (restrictIso (fieldMap k S σ) b.asIso).hom ≫
      ((restrictIso (fieldMap k S σ) i).hom ≫ i.inv) ≫ b.asIso.inv
  simp [Category.assoc]

section Assembly

open _root_.LinearAlgebraicGroups.Specs
open Specs.Pinning (AttachedDatum PinnedGroup)
open Specs.RootGroups (AdditiveLine)
open Specs.GeometricBorelConjugacy (IsQuasiSplit)
open Forms (SchemeModels SchemeFormClasses)

open private relativeYonedaIso relativeSchemeIso adjointComparison
  from LinearAlgebraicGroups.Descent.AutomorphismSequence

attribute [local instance] relativeAutTopology basedAutTopology relativeAutDiscrete
  basedAutDiscrete fieldGalTopology

noncomputable section

set_option maxHeartbeats 1500000 in
theorem liftInnerCocycle : LiftInnerCocycle.{u} := by
  intro k S _ _ _ G Q inn hinj a ha
  let T := fieldTest k S
  let M := NonabelianCohomology.Points k S Q.X
  let : TopologicalSpace M := ⊥
  let p : M →* RelativeAut G T :=
    (inn.app (op T)).hom.comp
      { toFun := ULift.up, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hp : Function.Injective p := fun _ _ e => ULift.up_inj.mp (hinj e)
  have hp_action (σ : Gal(S/k)) (x : M) :
      p (pointAction k S Q.X σ x) = automorphismAction k S G σ (p x) :=
    ConcreteCategory.congr_hom (inn.naturality (fieldMap k S σ).op)
      (ULift.up x : (groupSections Q).obj (op T))
  obtain ⟨f, hf⟩ := hp.hasLeftInverse
  have hpfa (σ : Gal(S/k)) : p (f (a σ)) = a σ := by
    obtain ⟨x, hx⟩ := ha σ
    change p x.down = a σ at hx
    rw [← hx, hf x.down]
  let d : Cocycle (pointAction k S Q.X) :=
    ⟨fun σ => f (a σ), continuous_of_discreteTopology.comp a.property.1, by
      intro σ τ
      apply hp
      rw [map_mul, hp_action, hpfa, hpfa, hpfa]
      exact a.property.2 σ τ⟩
  refine ⟨d, hpfa, ?_⟩
  intro z hz
  apply Subtype.ext
  funext σ
  apply hp
  exact (hz σ).trans (hpfa σ).symm

variable {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]

theorem finiteOuterLevel : FiniteOuterLevel.{u} := by
  intro k S _ _ _ _ D ω
  obtain ⟨L, c, _, hc⟩ := finiteLevel ⊥ ω
  have hsurj : Function.Surjective (restriction L) := AlgEquiv.restrictNormalHom_surjective S
  let ωL : Gal(L/k) →* Aut D :=
    { toFun := fun σ => (c σ).val
      map_one' := by
        change (c 1).val = 1
        rw [c.map_one]
        rfl
      map_mul' := by
        intro σ τ
        obtain ⟨s, rfl⟩ := hsurj σ
        obtain ⟨t, rfl⟩ := hsurj τ
        change (c (restriction L s * restriction L t)).val =
          (c (restriction L s)).val * (c (restriction L t)).val
        rw [← map_mul (restriction L), hc, hc, hc]
        simpa using ω.property.2 s t }
  exact ⟨L, ωL, hc⟩

private abbrev S₀ := fieldTest k S

private def modelOfRelativeIso (G H : AffineAlgebraicGroup k)
    (i : relativePoints G.val (S₀ (k := k) (S := S)) ≅
      relativePoints H.val (S₀ (k := k) (S := S))) : SchemeModels S G :=
  ⟨H, ⟨relativeSchemeIso i⟩⟩

private def relativeTrivialization {G : AffineAlgebraicGroup k} (H : SchemeModels S G) :
    relativePoints G.val (S₀ (k := k) (S := S)) ≅
      relativePoints H.val.val (S₀ (k := k) (S := S)) :=
  let T := S₀ (k := k) (S := S)
  (relativeYonedaIso T G.val).symm ≪≫
    Functor.isoWhiskerLeft (Over.iteratedSliceForward T).op
      (yonedaGrp.mapIso (Classical.choice H.property)) ≪≫ relativeYonedaIso T H.val.val

set_option maxHeartbeats 1200000 in
omit [IsSepClosure k S] in
private theorem isoOfInvariant {G H : AffineAlgebraicGroup k}
    (C : RelativeClassification k S G)
    (i : relativePoints G.val (S₀ (k := k) (S := S)) ≅
      relativePoints H.val (S₀ (k := k) (S := S)))
    (hi : ∀ σ, restrictIso (fieldMap k S σ) i = i) : Nonempty (G.val ≅ H.val) := by
  let T := S₀ (k := k) (S := S)
  let H' := modelOfRelativeIso G H i
  let G' : SchemeModels S G := ⟨G, ⟨Iso.refl _⟩⟩
  have neutral (X : SchemeModels S G)
      (j : relativePoints G.val T ≅ relativePoints X.val.val T)
      (hj : ∀ σ, restrictIso (fieldMap k S σ) j = j) :
      C.equiv (Quotient.mk _ X) = basepoint (automorphismAction k S G.val) := by
    obtain ⟨a, ha, he⟩ := C.computes X j
    have e : a = trivial (automorphismAction k S G.val) := by
      apply Subtype.ext
      funext σ
      change a σ = 1
      rw [ha, transportedAut, hj]
      apply Aut.ext
      apply Iso.ext
      exact j.hom_inv_id
    rw [he, e]
    rfl
  have h₁ := neutral H' i hi
  have h₂ := neutral G' (Iso.refl _) (fun _ => rfl)
  exact Quotient.exact (C.equiv.injective (h₂.trans h₁.symm))

open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AdjointCocharacters (IsAdjointQuotient)

variable {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
  {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}

open Specs.AdjointCocharacters (coordinateHopfIso coordinateHopfMap)

open private extendedGroupIso extendedSpecIso_hom_fst
  from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private extendedCoordinateIso_natural
  from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private inversePullback from LinearAlgebraicGroups.Descent.PinnedPairDescent
open private hopfIsoEquiv hopfIsoEquiv_apply hopfIsoEquiv_trans restrict_hopfIso
  schemeIsoEquiv_ground from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private aut_ext standard standardAct transported transported_apply transportedDifference
  act_apply_inv difference_apply raiseAut raiseAut_inLevel raiseIso_ext inLevel inLevel_tmul
  transportedDifference_raise evalAut applyIso applyIso_right
  from LinearAlgebraicGroups.Descent.Forms

set_option maxHeartbeats 1600000 in
private theorem pinnedHopfDifference {K : Type u} [Field K] [Algebra k K]
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (W : PinnedTwist (P := P) K D l B T) (δ : Gal(K/k)) :
    transportedDifference W.groupIso δ =
      inversePullback (K := K) (G := P.pair.G)
        (Functor.mapAut P (forgetPinning (A := A)) (l (W.outer δ))) := by
  apply aut_ext
  intro x
  let C := Specs.AdjointCocharacters.coordinateHopf P.pair.G
  let f := Functor.mapAut P (forgetPinning (A := A)) (l (W.outer δ))
  let y := (standardAct K C).act δ⁻¹ x
  have hy : (standardAct K C).act δ y = x := act_apply_inv (standardAct K C) δ x
  have h := difference_apply (transported W.groupIso) (standard K C) δ y
  rw [transported_apply] at h
  change evalAut (transportedDifference W.groupIso δ) ((standardAct K C).act δ y) =
    W.groupIso.inv.hom ((standardAct K (Specs.AdjointCocharacters.coordinateHopf G)).act δ (W.groupIso.hom.hom y)) at h
  rw [hy, W.twistedAction] at h
  have hh := ConcreteCategory.congr_hom W.groupIso.hom_inv_id
    ((extendedHopfMap K (coordinateHopfMap (G := P.pair.G) (H := P.pair.G) f.asIso.inv)).hom
      ((standardAct K C).act δ y))
  change W.groupIso.inv.hom (W.groupIso.hom.hom _) = _ at hh
  rw [h, hh, hy]
  rfl

set_option maxHeartbeats 1200000 in
private theorem raiseInversePullback {G : AffineAlgebraicGroup k}
    (L : FiniteGaloisIntermediateField k S) (f : Aut G.val) :
    raiseAut L (inversePullback (K := L) (G := G) f) =
      inversePullback (K := S) (G := G) f := by
  apply Aut.ext
  apply raiseIso_ext L
  intro x
  change evalAut (raiseAut L (inversePullback (K := L) (G := G) f))
    (inLevel L _ (1 ⊗ₜ[k] x)) = _
  rw [raiseAut_inLevel]
  change inLevel L _ (1 ⊗ₜ[k] (coordinateHopfMap (G := G) (H := G) f.asIso.inv).hom x) =
    (extendedHopfMap S (coordinateHopfMap (G := G) (H := G) f.asIso.inv)).hom
      (inLevel L _ (1 ⊗ₜ[k] x))
  rw [inLevel_tmul, inLevel_tmul, map_one]
  rfl

set_option maxHeartbeats 1600000 in
omit [IsSepClosure k S] in
private theorem relativeInversePullback (G : AffineAlgebraicGroup k) (f : Aut G.val) :
    hopfIsoEquiv (extendedGroupIso (k := k) S) (coordinateHopfIso G) (coordinateHopfIso G)
      (inversePullback (K := S) (G := G) f).asIso = (scalarAut f (fieldTest k S)).asIso := by
  have hg := schemeIsoEquiv_ground (S := S) f.asIso
  change _ = (scalarAut f (fieldTest k S)).asIso at hg
  rw [hopfIsoEquiv_apply, ← hg]
  congr 1
  apply Iso.ext
  let e := extendedGroupIso S (Specs.AdjointCocharacters.coordinateHopf G) ≪≫
    (groupBaseChange k S).mapIso (coordinateHopfIso G)
  apply (cancel_epi e.hom).mp
  change e.hom ≫ (e.inv ≫
      specGroupMap (extendedHopfMap S (coordinateHopfMap (G := G) (H := G) f.asIso.hom)) ≫
      e.hom) = e.hom ≫ (groupBaseChange k S).map f.asIso.hom
  rw [Iso.hom_inv_id_assoc]
  exact extendedCoordinateIso_natural (K := S) (G := G) (H := G) f.asIso.hom

omit [IsSepClosure k S] in
private theorem conjugatesByTransportedDifference {C C' : HopfAlgebraCategory k}
    (i : extendedHopf S C ≅ extendedHopf S C') (σ : Gal(S/k)) :
    HopfConjugates σ i ((transportedDifference i σ).asIso ≪≫ i) := by
  intro x
  change applyIso i (evalAut (transportedDifference i σ) ((standardAct S C).act σ x)) =
    (standardAct S C').act σ (applyIso i x)
  have h := difference_apply (transported i) (standard S C) σ x
  change evalAut (transportedDifference i σ) ((standardAct S C).act σ x) = _ at h
  rw [h, transported_apply, applyIso_right]

set_option maxHeartbeats 2500000 in
private theorem pinnedRepresentatives : PinnedRepresentatives.{u} := by
  intro k S _ _ _ _ A P D l Q E ω
  obtain ⟨L, ωL, hω⟩ := finiteOuterLevel D.toBased ω
  obtain ⟨W⟩ := PinnedPairDescent.pinnedPairDescent (K := L) E ωL
  let i := Forms.raiseIso (S := S) W.data.groupIso
  let t := extendedGroupIso (k := k) S
  let g := coordinateHopfIso P.pair.G
  let h := coordinateHopfIso W.group
  let j := hopfIsoEquiv t g h i
  refine ⟨⟨modelOfRelativeIso P.pair.G W.group j, W.reductive, W.borel, W.torus,
    W.isKBorel, W.isTorus, W.isMaximal, W.inclusion, W.inclusion_comm, L, W.data,
    fun σ => (congrFun (congrArg DFunLike.coe W.outer_eq) (restriction L σ)).trans (hω σ),
    j, ?_⟩⟩
  intro σ
  let f := Functor.mapAut P (forgetPinning (A := A)) (l (ω σ))
  let b := inversePullback (K := S) (G := P.pair.G) f
  have hb : transportedDifference i σ = b := by
    change transportedDifference (Forms.raiseIso W.data.groupIso) σ = b
    rw [transportedDifference_raise L, pinnedHopfDifference, W.outer_eq, hω]
    exact raiseInversePullback L f
  have hc : HopfConjugates σ i (b.asIso ≪≫ i) := by
    rw [← hb]
    exact conjugatesByTransportedDifference i σ
  have hj := restrict_hopfIso t (extendedSpecIso_hom_fst S) g h σ hc
  have hs : pinnedSection E (ω σ) = scalarAut f (fieldTest k S) :=
    E.sectionOnConstants _ _
  apply Aut.ext
  change restrictIso (fieldMap k S σ) j ≪≫ j.symm = (pinnedSection E (ω σ)).asIso
  rw [hj, hopfIsoEquiv_trans t g g h]
  rw [Iso.trans_assoc]
  change hopfIsoEquiv t g g b.asIso ≪≫ (j ≪≫ j.symm) = _
  rw [Iso.self_symm_id, Iso.trans_refl, hs]
  exact relativeInversePullback (S := S) P.pair.G f

set_option maxHeartbeats 1600000 in
omit [IsSepClosure k S] in
private theorem pinnedClass (E : SplitSequence P D l Q)
    (C : RelativeClassification k S P.pair.G) (h : CoefficientMaps (S := S) E)
    (ω : Cocycle (trivialOuterAction (k := k) (S := S) D.toBased))
    (W : PinnedRepresentative (S := S) E ω) :
    C.equiv (Quotient.mk _ W.model) =
      mapH1 (pinnedSection E) continuous_of_discreteTopology h.2.1 (classOf ω) := by
  obtain ⟨a, ha, he⟩ := C.computes W.model W.trivialization
  have e : a = mapCocycle (pinnedSection E) continuous_of_discreteTopology h.2.1 ω := by
    apply Subtype.ext
    funext σ
    exact (ha σ).trans (W.transport_eq σ)
  rw [he, e]
  rfl

set_option maxHeartbeats 2200000 in
omit [IsSepClosure k S] in
private theorem innerRangeComparison
    (E : SplitSequence P D l Q) {G : AffineAlgebraicGroup k}
    (V : AdjointQuotient G) (inn : groupSections V.quotient.val ⟶ automorphisms G.val)
    (hinn : ∀ (U : SchemeOver k) (g : U ⟶ G.val.X),
      inn.app (op U) ⟨g ≫ V.projection.hom.hom⟩ = innerAut g)
    (hinj : ∀ U, Function.Injective (inn.app U))
    (i : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    (f : RelativeAut P.pair.G.val (fieldTest k S)) :
    Aut.autMulEquivOfIso i f ∈ (inn.app (op (fieldTest k S))).hom.range ↔
      outerHom E f = 1 := by
  obtain ⟨a, _, ha⟩ := adjointComparison i E.inner inn E.onLift hinn E.innerInjective hinj
  let T := Over.mk (𝟙 (fieldTest k S))
  have hid : restrictIso (𝟙 (fieldTest k S)) i = i := by
    apply Iso.ext
    apply NatTrans.ext
    funext U
    rfl
  have hcomm (x : (groupSections Q.quotient.val).obj (op (fieldTest k S))) :
      Aut.autMulEquivOfIso i ((E.inner.app (op (fieldTest k S))).hom x) =
        inn.app (op (fieldTest k S)) (a.hom.app (op T) x) := by
    have h := ha T x
    change Aut.autMulEquivOfIso (restrictIso (𝟙 (fieldTest k S)) i)
      ((E.inner.app (op (fieldTest k S))).hom x) = _ at h
    rw [hid] at h
    exact h
  rw [splitKernel]
  constructor
  · rintro ⟨x, hx⟩
    let y := a.inv.app (op T) x
    have hy : a.hom.app (op T) y = x :=
      ConcreteCategory.congr_hom (NatTrans.congr_app a.inv_hom_id (op T)) x
    refine ⟨y, (Aut.autMulEquivOfIso i).injective ?_⟩
    rw [hcomm, hy]
    exact hx
  · rintro ⟨x, hx⟩
    exact ⟨a.hom.app (op T) x, (hcomm x).symm.trans (congrArg (Aut.autMulEquivOfIso i) hx)⟩

set_option maxHeartbeats 2000000 in
omit [IsSepClosure k S] in
private theorem innerComparison
    (E : SplitSequence P D l Q) {G H : AffineAlgebraicGroup k}
    (V : AdjointQuotient G) (inn : groupSections V.quotient.val ⟶ automorphisms G.val)
    (hinn : ∀ (U : SchemeOver k) (g : U ⟶ G.val.X),
      inn.app (op U) ⟨g ≫ V.projection.hom.hom⟩ = innerAut g)
    (hinj : ∀ U, Function.Injective (inn.app U))
    (i : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    (j : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints H.val (fieldTest k S)) :
    (∀ σ, transportedAut k S (i.symm ≪≫ j) σ ∈
      (inn.app (op (fieldTest k S))).hom.range) ↔
    (∀ σ, outerHom E (transportedAut k S j σ) = outerHom E (transportedAut k S i σ)) := by
  have h (σ : Gal(S/k)) :
      transportedAut k S (i.symm ≪≫ j) σ ∈ (inn.app (op (fieldTest k S))).hom.range ↔
        outerHom E (transportedAut k S j σ) = outerHom E (transportedAut k S i σ) := by
    rw [differenceOfTrivializations, innerRangeComparison E V inn hinn hinj,
      map_mul, map_inv, mul_inv_eq_one]
  exact forall_congr' h

set_option maxHeartbeats 2400000 in
omit [IsSepClosure k S] in
private theorem alignOuterCocycles (E : SplitSequence P D l Q)
    (C : RelativeClassification k S P.pair.G) (h : CoefficientMaps (S := S) E)
    (H J : SchemeModels S P.pair.G)
    (i : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints H.val.val (fieldTest k S))
    (hout : mapH1 (outerHom (S := S) E) continuous_of_discreteTopology h.1
        (C.equiv (Quotient.mk _ J)) =
      mapH1 (outerHom (S := S) E) continuous_of_discreteTopology h.1
        (C.equiv (Quotient.mk _ H))) :
    ∃ j : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints J.val.val (fieldTest k S),
      ∀ σ, outerHom E (transportedAut k S j σ) = outerHom E (transportedAut k S i σ) := by
  let j := relativeTrivialization J
  obtain ⟨a, ha, hca⟩ := C.computes H i
  obtain ⟨b, hb, hcb⟩ := C.computes J j
  rw [hca, hcb] at hout
  obtain ⟨b', d, hb', hd⟩ :=
    (outerFiberCriterion _ _ _ h.2.2.surjective C.continuousAction a (classOf b)).mp hout
  obtain ⟨g, hg⟩ := Quotient.exact hb'.symm
  refine ⟨g.asIso ≪≫ j, fun σ => ?_⟩
  rw [changeOfTrivialization, ← hb, ← hg, (hd σ).2, map_mul, (hd σ).1, one_mul, ha]

set_option maxHeartbeats 3500000 in
private theorem geometricOuterCriterion (E : SplitSequence P D l Q)
    (hTwist : Twists E.toExactSequence)
    (C : RelativeClassification k S P.pair.G) (h : CoefficientMaps (S := S) E)
    (H J : SchemeModels S P.pair.G) :
    mapH1 (outerHom (S := S) E) continuous_of_discreteTopology h.1 (C.equiv (Quotient.mk _ J)) =
      mapH1 (outerHom (S := S) E) continuous_of_discreteTopology h.1 (C.equiv (Quotient.mk _ H)) ↔
      AreInnerForms (S := S) H.val J.val := by
  let i := relativeTrivialization H
  constructor
  · intro hout
    obtain ⟨j, hj⟩ := alignOuterCocycles E C h H J i hout
    obtain ⟨V, O, F, _, _⟩ := hTwist H.val ⟨S, ‹Field S›, ‹Algebra k S›, ‹IsSepClosure k S›, H.property⟩
    exact ⟨V, F.inner, F.onLift, F.innerInjective, i.symm ≪≫ j,
      (innerComparison E V F.inner F.onLift F.innerInjective i j).mpr hj⟩
  · rintro ⟨V, inn, hinn, hinj, r, hr⟩
    let j := i ≪≫ r
    have hcomp : i.symm ≪≫ j = r := by simp [j]
    have hp := (innerComparison E V inn hinn hinj i j).mp (hcomp.symm ▸ hr)
    obtain ⟨a, ha, hca⟩ := C.computes H i
    obtain ⟨b, hb, hcb⟩ := C.computes J j
    rw [hca, hcb]
    apply congrArg classOf
    apply Subtype.ext
    funext σ
    change outerHom E (b σ) = outerHom E (a σ)
    rw [ha, hb]
    exact hp σ

set_option maxHeartbeats 5000000 in
private theorem quasiSplitUniqueness
    (classify : Classification.{u})
    (remove : Specs.BorelInnerAlignment.Statement.{u})
    (E : SplitSequence P D l Q)
    (C : RelativeClassification k S P.pair.G) (h : CoefficientMaps (S := S) E)
    (ω : Cocycle (trivialOuterAction (k := k) (S := S) D.toBased))
    (W : PinnedRepresentative (S := S) E ω)
    (H : SchemeModels S P.pair.G) (hq : IsQuasiSplit H.val)
    (hout : mapH1 (outerHom (S := S) E) continuous_of_discreteTopology h.1
      (C.equiv (Quotient.mk _ H)) = classOf ω) :
    C.equiv (Quotient.mk _ H) =
      mapH1 (pinnedSection (S := S) E) continuous_of_discreteTopology h.2.1 (classOf ω) := by
  have hW := pinnedClass E C h ω W
  have houterW : mapH1 (outerHom (S := S) E) continuous_of_discreteTopology h.1
      (C.equiv (Quotient.mk _ W.model)) = classOf ω := by
    rw [hW]
    exact outerFiberSection _ _ _ _ _ _ h.2.2 (classOf ω)
  obtain ⟨j', htransport⟩ :=
    alignOuterCocycles E C h W.model H W.trivialization (hout.trans houterW.symm)
  obtain ⟨Z, V, q, hqV, _, Bq, rest⟩ :=
    AdjointBorelCohomology.adjointBorelCohomology D l Q E W.model.val W.B W.T W.data
      W.reductive W.borel W.torus W.maximal W.j W.j_comm
  obtain ⟨z, hz, hzc, Td, p, U, π, _, _, _, _, _, _, _, _, _, hv⟩ := rest
  let V' : AdjointQuotient W.model.val :=
    ⟨Z, hqV.1, V, q, ⟨hqV.2.2.2.1, hqV.2.2.2.2.1, hqV.2.2.2.2.2⟩, hqV.2.1⟩
  obtain ⟨inn, hinn, hinj⟩ := AutomorphismSequence.adjointInner W.model.val V'
  have hrange := (innerComparison E V' inn hinn hinj W.trivialization j').mpr htransport
  obtain ⟨C'⟩ := classify (S := S) W.model.val
  let j'' := W.trivialization.symm ≪≫ j'
  let H' := modelOfRelativeIso W.model.val H.val j''
  obtain ⟨a', ha', _⟩ := C'.computes H' j''
  have hra (σ : Gal(S/k)) : a' σ ∈ (inn.app (op (fieldTest k S))).hom.range := by
    rw [ha' σ]
    exact hrange σ
  obtain ⟨BH, hBH⟩ := hq.2
  obtain ⟨i, hi⟩ := remove W.model.val H.val V W.reductive hq.1 W.B BH
    W.borel hBH Z q hqV Bq inn hinn hinj (hv S) C'.continuousAction j'' a' ha' hra
  have hm : (Quotient.mk _ H : SchemeFormClasses S P.pair.G) = Quotient.mk _ W.model :=
    Quotient.sound ((isoOfInvariant C' i hi).map Iso.symm)
  rw [hm]
  exact hW

set_option maxHeartbeats 5000000 in
theorem assemble (classify : Classification.{u})
    (descend : PinnedRepresentatives.{u}) (remove : Specs.BorelInnerAlignment.Statement.{u}) :
    Specs.QuasiSplitInnerForms.Statement.{u} := by
  intro k S _ _ _ _ A P
  obtain ⟨D, l, Q, E, _, hTwist⟩ := automorphismSequences P
  obtain ⟨C⟩ := classify (S := S) P.pair.G
  refine ⟨D, l, Q, E, hTwist, C, ?_⟩
  have h := splitCoefficientMaps (S := S) E
  refine ⟨h, ?_, geometricOuterCriterion E hTwist C h, descend E, ?_⟩
  · exact outerFiberCriterion _ _ _ h.2.2.surjective C.continuousAction
  let po := mapH1 (outerHom (S := S) E) continuous_of_discreteTopology h.1
  let so := mapH1 (pinnedSection (S := S) E) continuous_of_discreteTopology h.2.1
  have hright : Function.RightInverse so po :=
    outerFiberSection _ _ _ _ _ _ h.2.2
  intro x
  refine Quotient.inductionOn x (fun ω y => ?_)
  obtain ⟨W⟩ := descend E ω
  have hW := pinnedClass E C h ω W
  constructor
  · rintro ⟨he, H, rfl, hq⟩
    exact quasiSplitUniqueness classify remove E C h ω W H hq he
  · intro he
    have eq : y = Quotient.mk _ W.model := C.equiv.injective (he.trans hW.symm)
    refine ⟨?_, W.model, eq.symm, W.reductive, W.B, W.borel⟩
    exact (congrArg po he).trans (hright (classOf ω))

/-- The split automorphism sequence, its twists, and the unique quasi-split
representative of each outer fiber. -/
theorem quasiSplitInnerForms : Specs.QuasiSplitInnerForms.Statement.{u} :=
  assemble RelativeFormComparison.relativeFormClassification pinnedRepresentatives
    BorelInnerAlignment.borelInnerAlignment

end
end Assembly

end LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
