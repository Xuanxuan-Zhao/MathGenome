import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.PositiveKempfVanishing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AmpleFlagWeights
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SteinbergFrobeniusPushforward
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AmpleFlagTwistVanishing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomologyOverAlgClosure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.DerivedFlagCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimplyConnectedFlagCover
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

noncomputable section

namespace LinearAlgebraicGroups.PositiveKempfVanishing

open LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Datum)
open Specs.CharacterDescent (Character)
open Specs.InducedNonvanishing (Dominant)
open Specs.FlagCohomology (FlagKernelPair flagCohomology flagLineSheaf cohomology
  coefficientPresheaf)
open Specs.FlagLineBundle (BorelProjection OppositeBorelPair AssociatedBundle)
open Specs.QuotientEmbedding (Presentation)
open Specs.RootWeightAction (IsDominant)

section Flag

open Specs.AmpleFlagWeights (IsStrictlyDominant)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.RootWeightAction (SimpleRoot)
open Specs.SteinbergDimension (IsHalfPositiveRootSum)
open Representation.SteinbergDimension (halfSum_simpleCoroot)
open private exists_associatedBundle from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

theorem strictlyDominant_mul_halfSum (P : OppositeBorelPair G)
    [IsCommMonObj P.torus.group.X] (D : Datum P.torus)
    (χ ρ : Character P.torus.group) (hχ : IsDominant D P.positive χ)
    (hρ : IsHalfPositiveRootSum P ρ) :
    IsStrictlyDominant (B := P.positive) D (χ * ρ) := by
  intro α
  have hpair := halfSum_simpleCoroot P ρ hρ α
    (Additive.toMul (D.rootDatum.coroot α.val)) (D.attached α.val)
  rw [← D.pairing_eq] at hpair
  change D.rootDatum.coroot' α.val (Additive.ofMul ρ) = 1 at hpair
  change 0 < D.rootDatum.coroot' α.val (Additive.ofMul χ + Additive.ofMul ρ)
  have hnonneg : 0 ≤ D.rootDatum.coroot' α.val (Additive.ofMul χ) := hχ α
  rw [map_add, hpair]
  omega

/-- The Steinberg shift is the high power of the strictly dominant
character, translated by the fixed inverse half-sum. -/
theorem steinbergWeight_mul_pow {T : GroupScheme k} (ρ χ : Character T) (q : ℕ)
    (hq : 0 < q) :
    Additive.toMul ((q - 1) • Additive.ofMul ρ) * χ ^ q =
      ρ⁻¹ * (χ * ρ) ^ q := by
  change ρ ^ (q - 1) * χ ^ q = ρ⁻¹ * (χ * ρ) ^ q
  have hρ : ρ ^ q = ρ ^ (q - 1) * ρ := by
    calc
      ρ ^ q = ρ ^ (q - 1 + 1) := congrArg (ρ ^ ·) (Nat.sub_add_cancel hq).symm
      _ = ρ ^ (q - 1) * ρ := pow_succ _ _
  calc
    _ = ρ⁻¹ * (ρ * (ρ ^ (q - 1) * χ ^ q)) := by simp
    _ = _ := by
      rw [mul_pow, hρ]
      apply congrArg (ρ⁻¹ * ·)
      rw [← mul_assoc, mul_comm _ (χ ^ q), mul_comm ρ (ρ ^ (q - 1))]

/-- A split torus has point flag, and its character sheaf has no
positive cohomology. -/
theorem splitTorusFlagVanishing (P : OppositeBorelPair G) (hG : IsSplitTorus G.val)
    (Q : Presentation P.negative) (b : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) (i : ℕ) (hi : 0 < i) : IsZero (flagCohomology Q b χ h i) := by
  obtain ⟨hs, _⟩ := Representation.AmpleFlagWeights.splitTorusPointCase k G P hG Q b χ
  let := hs
  let : IsAffine Q.scheme.left := IsAffine.of_isIso Q.scheme.hom
  obtain ⟨_, _, _, _, _, _, _, a, _, _, ha⟩ :=
    (LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q
  obtain ⟨L⟩ := exists_associatedBundle Q b χ a ha
  have hqc := (Representation.FlagCohomology.flagLineSheafIdentification Q b χ h L).1
  let I := ULift.{u} (Fin 1)
  let U : I → Q.scheme.left.Opens := fun _ => ⊤
  have hcov : (⨆ j, U j) = ⊤ := by simp [U, I]
  have haff (s : Finset I) (_ : s.Nonempty) :
      IsAffineOpen (⨅ j ∈ (s : Set I), U j) := by
    simpa [U] using isAffineOpen_top Q.scheme.left
  obtain ⟨e, _⟩ := Representation.FlagCohomology.affineCechComparison Q.scheme U hcov haff i
  exact (Representation.FlagCohomology.cechBounded U
    (coefficientPresheaf (flagLineSheaf Q b χ h)) i (by simpa [I] using Nat.succ_le_of_lt hi)).of_iso
    (e _ hqc)

open Specs.IsogenyFlagComparison (Restrictions)
open private projection_commutes from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.IsogenyFlagComparison

private def identityRestrictions (P : OppositeBorelPair G) : Restrictions (𝟙 G.val) P P where
  torus := 𝟙 _
  borel := 𝟙 _
  torus_comm := by simp
  borel_comm := by simp
  torus_surjective := by
    change Surjective (𝟙 P.torus.group.X.left)
    infer_instance
  borel_surjective := by
    change Surjective (𝟙 P.negative.group.X.left)
    infer_instance

/-- The Borel projection is determined by the unipotent radical and the
section of the marked torus. -/
private theorem borelProjection_eq {P : OppositeBorelPair G}
    (b c : BorelProjection P) : b.projection = c.projection := by
  simpa [identityRestrictions] using (projection_commutes (identityRestrictions P) b c).symm

private theorem flagLineSheaf_borelProjection_eq {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (b c : BorelProjection P)
    (χ : Character P.torus.group) (h : FlagKernelPair Q) :
    flagLineSheaf Q b χ h = flagLineSheaf Q c χ h := by
  simp only [flagLineSheaf, Specs.FlagCohomology.flagLineData, Specs.FlagCohomology.flagTransition,
    borelProjection_eq b c]

end Flag

section AssociatedCoefficients

open LinearAlgebraicGroups.AssociatedFlagLineSheaves (realizeSections)
open private exists_associatedFlagSheafIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AmpleFlagTwistVanishing

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
variable {b : BorelProjection P} {χ : Character P.torus.group}

/-- The section realization used by the pushforward formula is isomorphic to
the covariance kernel used to define flag cohomology. -/
private def associatedFlagSheafIso (L : AssociatedBundle Q a b χ) (h : FlagKernelPair Q) :
    (realizeSections L).sheaf ≅ flagLineSheaf Q b χ h :=
  (exists_associatedFlagSheafIso L h).choose

end AssociatedCoefficients

section FrobeniusCohomology

open CategoryTheory.MonoidalCategory
open Specs.LinePushforwardProjection (tensorModule)
open Specs.SteinbergFrobeniusPushforward (freeModule)
open Specs.FlagRelativeFrobeniusAtlas (twist IsRelativeFrobenius)
open Specs.FlagCohomology (pushforwardSectionsIso)
open FlagRelativeFrobeniusAtlas (relativeFrobenius absoluteFrobenius relativeFrobenius_unique)
open private exactPushforwardCohomologyIso pushforwardEquivalenceOfIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

variable {k : Type u} [Field k]

private def tensorLeftMap {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B)
    (M : X.Modules) : tensorModule A M ⟶ tensorModule B M :=
  let g := (SheafOfModules.forget X.ringCatSheaf).map f
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (MonoidalCategoryStruct.whiskerRight (C := PresheafOfModulesOfCommRing X.presheaf) g M.val)

set_option backward.isDefEq.respectTransparency false in
private def tensorLeftRetract {X : Scheme.{u}} (M : X.Modules)
    {J : Type u} (j : J) :
    SplitMono (tensorLeftMap (SheafOfModules.ιFree (R := X.ringCatSheaf) j) M) := by
  let p : freeModule X J ⟶ SheafOfModules.unit X.ringCatSheaf := Sigma.desc (fun _ ↦ 𝟙 _)
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let i : SheafOfModules.unit X.ringCatSheaf ⟶ freeModule X J := SheafOfModules.ιFree j
  let N : PresheafOfModulesOfCommRing X.presheaf := M.val
  refine ⟨tensorLeftMap p M, ?_⟩
  let A : PresheafOfModulesOfCommRing X.presheaf := (SheafOfModules.unit X.ringCatSheaf).val
  let B : PresheafOfModulesOfCommRing X.presheaf := (freeModule X J).val
  let i' : A ⟶ B := i.val
  let p' : B ⟶ A := p.val
  change F.map (i' ▷ N) ≫ F.map (p' ▷ N) = _
  rw [← F.map_comp]
  have hip : i ≫ p = 𝟙 _ := Sigma.ι_comp_desc _ j
  have h : i' ≫ p' = 𝟙 _ := congrArg
    (fun f : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf => f.val) hip
  have hw : i' ▷ N ≫ p' ▷ N = 𝟙 (A ⊗ N) :=
    (comp_whiskerRight i' p' N).symm.trans (by simp only [h, id_whiskerRight])
  let AN : PresheafOfModulesOfCommRing X.presheaf := A ⊗ N
  change F.map (i' ▷ N ≫ p' ▷ N) = 𝟙 (F.obj AN)
  exact (congrArg (fun f : AN ⟶ AN => F.map f) hw).trans (F.map_id _)

set_option backward.isDefEq.respectTransparency false in
private def tensorUnitLeftIso {X : Scheme.{u}} (M : X.Modules) :
    tensorModule (SheafOfModules.unit X.ringCatSheaf) M ≅ M := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let N : PresheafOfModulesOfCommRing X.presheaf := M.val
  exact F.mapIso (λ_ N) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app M

/-- A line sheaf is a retract of its tensor product with a nonempty free
sheaf, and this retraction remains a retraction on derived cohomology. -/
private theorem isZero_cohomology_of_tensorFree {X : SchemeOver k}
    (M : X.left.Modules) {J : Type u} (j : J) (n : ℕ)
    (h : IsZero ((cohomology X n).obj (tensorModule (freeModule X.left J) M))) :
    IsZero ((cohomology X n).obj M) := by
  let H := cohomology X n
  let t := tensorLeftRetract M j
  let f := H.map (tensorLeftMap (SheafOfModules.ιFree j) M)
  let g := H.map t.retraction
  have e : f ≫ g = 𝟙 _ := by dsimp only [f, g]; rw [← H.map_comp, t.id, H.map_id]
  have e' : 𝟙 (H.obj (tensorModule (SheafOfModules.unit X.left.ringCatSheaf) M)) = 0 := by
    rw [← e, h.eq_of_tgt f 0, zero_comp]
  apply IsZero.of_iso _ (H.mapIso (tensorUnitLeftIso M)).symm
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y => ?_⟩
  have hx (z : H.obj (tensorModule (SheafOfModules.unit X.left.ringCatSheaf) M)) : z = 0 := by
    change (𝟙 _ : H.obj _ ⟶ H.obj _).hom z = (0 : H.obj _ ⟶ H.obj _).hom z
    rw [e']
  exact (hx x).trans (hx y).symm

variable [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem relativeFrobenius_pushforward_colimits (X : SchemeOver k) :
    PreservesFiniteColimits
      (Scheme.Modules.pushforward ((relativeFrobenius p r).app X).left) := by
  let F := Scheme.Modules.pushforward ((relativeFrobenius p r).app X).left
  let A := SheafOfModules.toSheaf.{u} X.left.ringCatSheaf
  let e : A ≅ F ⋙ A := NatIso.ofComponents (fun M => by
    apply (sheafToPresheaf _ _).preimageIso
    refine NatIso.ofComponents (fun U => Iso.refl _) ?_
    intro U V i
    simp
    rfl) (by
      intro M N f
      apply (sheafToPresheaf _ _).map_injective
      simp only [Functor.map_comp, Functor.comp_map, Functor.preimageIso_hom, Functor.map_preimage]
      ext U : 2
      rfl)
  let _ : PreservesFiniteColimits A := inferInstanceAs
    (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.left.ringCatSheaf))
  let _ : A.ReflectsIsomorphisms := inferInstanceAs
    (SheafOfModules.toSheaf.{u} X.left.ringCatSheaf).ReflectsIsomorphisms
  let _ : PreservesFiniteColimits (F ⋙ A) := preservesFiniteColimits_of_natIso e
  exact preservesFiniteColimits_of_reflects_of_preserves F A

/-- For a flat relative Frobenius on the split flag, cohomology of its
direct image agrees with cohomology on the source. -/
private def frobeniusCohomologyIso {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative)
    (F : Q.scheme ⟶ (twist p r).obj Q.scheme) (hF : IsRelativeFrobenius p r Q.scheme F)
    (hr : 1 ≤ r) (M : Q.scheme.left.Modules) (n : ℕ) :
    (cohomology ((twist p r).obj Q.scheme) n).obj ((Scheme.Modules.pushforward F.left).obj M) ≅
      (cohomology Q.scheme n).obj M := by
  have hf := (LinearAlgebraicGroups.SteinbergFrobeniusPushforward.flagFrobeniusDegree p r hr Q F hF).2.2.1
  let _ : Flat F.left := hf
  let _ : (Scheme.Modules.pushforward F.left).PreservesInjectiveObjects :=
    FlatCohomology.flatPushforwardPreservesInjectives F.left
  let _ : PreservesFiniteColimits (Scheme.Modules.pushforward F.left) :=
    (relativeFrobenius_unique p r Q.scheme F hF).symm ▸
      relativeFrobenius_pushforward_colimits p r Q.scheme
  let w : F.left ≫ ((twist p r).obj Q.scheme).hom =
      Q.scheme.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by simp
  exact exactPushforwardCohomologyIso (RingHom.id k) F.left w (injectiveResolution M) n ≪≫
    (ModuleCat.restrictScalarsId k).app _

open FlagRelativeFrobeniusAtlas (twistIsBaseChange)

set_option backward.isDefEq.respectTransparency false in
private theorem isZero_twist_cohomology_iff (X : SchemeOver k) (M : X.left.Modules)
    (n : ℕ) :
    IsZero ((cohomology ((twist p r).obj X) n).obj M) ↔ IsZero ((cohomology X n).obj M) := by
  let Y := (twist p r).obj X
  let g : Y.left ⟶ X.left := 𝟙 _
  let φ : k →+* k := iterateFrobenius k p r
  let w : g ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ) := (twistIsBaseChange p r X).w
  let e := pushforwardEquivalenceOfIso (X := X) (Y := Y) g
  let _ : (Scheme.Modules.pushforward g).IsEquivalence := e.isEquivalence_functor
  let c := exactPushforwardCohomologyIso φ g w (injectiveResolution M) n
  let d : (cohomology X n).obj M ≅
      (ModuleCat.restrictScalars φ).obj ((cohomology Y n).obj M) :=
    (cohomology X n).mapIso ((Scheme.Modules.pushforwardId X.left).app M).symm ≪≫ c
  rw [d.isZero_iff, ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  rfl

end FrobeniusCohomology

section FieldExtension

open Specs.FlagCohomology (CovarianceData extendScheme extendToAlgebra flagLineData)
open scoped ZeroObject

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A field extension reflects zero vector spaces. -/
theorem extendScalars_isZero_iff (V : ModuleCat.{u} k) :
    IsZero ((extendToAlgebra (k := k) (K := K)).obj V) ↔ IsZero V := by
  let F := extendToAlgebra (k := k) (K := K)
  have hflat : (algebraMap k K).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  let : F.ReflectsIsomorphisms := ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat hflat
  refine ⟨fun hFV => ?_, F.map_isZero⟩
  let f : V ⟶ 0 := 0
  let : IsIso (F.map f) := hFV.isIso (F.map_isZero (isZero_zero _)) _
  let : IsIso f := isIso_of_reflects_iso f F
  exact (isZero_zero _).of_iso (asIso f)

/-- For a field extension, vanishing of the cohomology of the extended
covariance data descends to the original flag. -/
theorem flagCohomology_isZero_of_scalarExtension
    {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (b : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) (i : ℕ)
    (hz : IsZero ((cohomology ((extendScheme (CommAlgCat.of k K)).obj Q.scheme) i).obj
      ((flagLineData Q b χ h).extend (CommAlgCat.of k K)).sheaf)) :
    IsZero (flagCohomology Q b χ h i) := by
  let E := (Representation.FlagCohomology.flagCohomologyBaseChange
    Q b χ h (CommAlgCat.of k K)).some
  exact (extendScalars_isZero_iff (K := K) _).mp (hz.of_iso (E.iso i))

end FieldExtension

section CentralIsogeny

open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CentralIsogenies (IsCentralIsogeny characterPullback)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.IsogenyFlagComparison (Restrictions)
open Specs.RootWeightAction (SimpleRoot)
open private exists_associatedBundle from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private pairing_pushforward from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies

variable {k : Type u} [Field k] {G' G : AffineAlgebraicGroup k}
variable {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}

/-- The central-isogeny comparison of associated line bundles carries
vanishing from the pulled-back weight to the original weight. -/
theorem flagCohomology_isZero_of_centralIsogeny (f : G'.val ⟶ G.val)
    (hf : IsCentralIsogeny f) (r : Restrictions f P' P)
    (Q' : Presentation P'.negative) (Q : Presentation P.negative)
    (b' : BorelProjection P') (b : BorelProjection P)
    (h' : FlagKernelPair Q') (h : FlagKernelPair Q)
    (χ : Character P.torus.group) (i : ℕ)
    (hz : IsZero (flagCohomology Q' b' (characterPullback r.torus χ) h' i)) :
    IsZero (flagCohomology Q b χ h i) := by
  obtain ⟨_, _, _, _, _, _, _, a', _, _, ha'⟩ :=
    (LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G' P').2.2 Q'
  obtain ⟨_, _, _, _, _, _, _, a, _, _, ha⟩ :=
    (LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q
  obtain ⟨L'⟩ := exists_associatedBundle Q' b' (characterPullback r.torus χ) a' ha'
  obtain ⟨L⟩ := exists_associatedBundle Q b χ a ha
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hc⟩ :=
    Representation.FlagCohomology.centralCohomologyIsomorphism
      f hf r b' b χ Q' Q h' h a' a ha' ha L' L
  obtain ⟨e, _⟩ := hc i
  exact hz.of_iso e

/-- When the positive systems correspond under a central isogeny, dominance
of characters is preserved by pullback on the marked maximal tori. -/
theorem isDominant_centralIsogeny_pullback (f : G'.val ⟶ G.val)
    (hf : IsCentralIsogeny f) (r : Restrictions f P' P)
    [IsCommMonObj P'.torus.group.X] [IsCommMonObj P.torus.group.X]
    (D' : Datum P'.torus) (D : Datum P.torus)
    (hpos : ∀ (β : AbstractPairing.Root P.torus)
        (hβ : characterPullback r.torus β.val ∈ absoluteRoots P'.torus),
      (⟨characterPullback r.torus β.val, hβ⟩ : AbstractPairing.Root P'.torus) ∈
        subgroupRoots P'.torus P'.positive ↔ β ∈ subgroupRoots P.torus P.positive)
    (χ : Character P.torus.group) (hχ : IsDominant D P.positive χ) :
    IsDominant D' P'.positive (characterPullback r.torus χ) := by
  obtain ⟨_, _, hroots, hcoroot⟩ :=
    Classification.CentralIsogenies.centralIsogenyComparison
      G' G P'.reductive P.reductive P'.torus P.torus P'.split P'.maximal
      P.split P.maximal f r.torus hf r.torus_comm r.torus_surjective
  intro α
  obtain ⟨β, hβ, he⟩ := hroots.surjOn α.val.property
  let β' : AbstractPairing.Root P.torus := ⟨β, hβ⟩
  have hroot_eq : (⟨_, hroots.mapsTo hβ⟩ : AbstractPairing.Root P'.torus) = α.val :=
    Subtype.ext he
  have hsimple : β' ∈ subgroupRoots P.torus P.positive ∧
      ∀ delta ∈ subgroupRoots P.torus P.positive, ∀ gamma ∈ subgroupRoots P.torus P.positive,
        β ≠ delta.val * gamma.val := by
    refine ⟨?_, ?_⟩
    · exact (hpos β' (hroots.mapsTo hβ)).mp (hroot_eq ▸ α.property.1)
    · intro delta hdelta gamma hgamma heq
      let delta' : AbstractPairing.Root P'.torus := ⟨_, hroots.mapsTo delta.property⟩
      let gamma' : AbstractPairing.Root P'.torus := ⟨_, hroots.mapsTo gamma.property⟩
      apply α.property.2 delta' ((hpos delta (hroots.mapsTo delta.property)).mpr hdelta)
        gamma' ((hpos gamma (hroots.mapsTo gamma.property)).mpr hgamma)
      exact he.symm.trans ((congrArg (characterPullback r.torus) heq).trans (map_mul _ _ _))
  have hc := (hcoroot β hβ (hroots.mapsTo hβ)).2
    (Additive.toMul (D'.rootDatum.coroot α.val))
    (Additive.toMul (D.rootDatum.coroot β'))
    (hroot_eq ▸ D'.attached α.val) (D.attached β')
  calc
    0 ≤ D.rootDatum.toLinearMap (Additive.ofMul χ) (D.rootDatum.coroot β') :=
      hχ (⟨β', hsimple⟩ : SimpleRoot P.torus P.positive)
    _ = pairing P.torus.group χ (Additive.toMul (D.rootDatum.coroot β')) := D.pairing_eq _ _
    _ = pairing P'.torus.group (characterPullback r.torus χ)
        (Additive.toMul (D'.rootDatum.coroot α.val)) := by rw [← hc, pairing_pushforward]
    _ = _ := (D'.pairing_eq _ _).symm

end CentralIsogeny

section Dominance

open Specs.FlagCohomology (cohomologyZero sectionsFunctor)
open Specs.IsogenyFlagComparison (Restrictions)
open Specs.CentralIsogenies (characterPullback)
open Specs.FlagLineBundle (covariantFunctions)
open LinearAlgebraicGroups.AssociatedFlagLineSheaves (globalCovariantSections realizeSections)
open private identity_isogeny from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedNonvanishing

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- The degree-zero cohomology criterion detects dominance on any
presentation of the actual flag. -/
theorem dominant_iff_not_isZero_flagCohomologyZero (P : OppositeBorelPair G)
    (χ : Character P.torus.group)
    (Q : Presentation P.negative) (b : BorelProjection P) (h : FlagKernelPair Q) :
    Dominant P χ ↔ ¬ IsZero (flagCohomology Q b χ h 0) := by
  obtain ⟨b₀, Q₀, _, A, B, e, d, q, φ, c, L, _, _, _, hq, hφ, hc, _, _, _, _, hdom⟩ :=
    Representation.InducedNonvanishing.nonvanishing k G P χ
  let h₀ : FlagKernelPair Q₀ := HomogeneousQuotient.quotientPullback Q₀
  obtain ⟨E, _⟩ := globalCovariantSections (realizeSections L) e d q φ hq hφ c hc
  let V := flagCohomology Q₀ b₀ χ h₀ 0
  let comp : V ≅ (sectionsFunctor Q₀.scheme).obj (realizeSections L).sheaf :=
    (cohomologyZero Q₀.scheme).app (flagLineSheaf Q₀ b₀ χ h₀) ≪≫
      (sectionsFunctor Q₀.scheme).mapIso (associatedFlagSheafIso L h₀).symm
  let equivalence : V ≃ covariantFunctions q c :=
    comp.toLinearEquiv.toEquiv.trans E.toEquiv
  have hv : Nontrivial (covariantFunctions q c) ↔ ¬ IsZero V := by
    rw [ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]
    constructor
    · intro H
      let := H
      exact equivalence.symm.injective.nontrivial
    · intro H
      let := H
      exact equivalence.injective.nontrivial
  let r := identityRestrictions P
  have hcχ : characterPullback r.torus χ = χ := by
    change (𝟙 P.torus.group) ≫ χ = χ
    exact Category.id_comp χ
  have hV : IsZero V ↔ IsZero (flagCohomology Q b χ h 0) := by
    constructor
    · intro hz
      exact flagCohomology_isZero_of_centralIsogeny (𝟙 _) (identity_isogeny G)
        r Q₀ Q b₀ b h₀ h χ 0 (by rw [hcχ]; exact hz)
    · intro hz
      exact flagCohomology_isZero_of_centralIsogeny (𝟙 _) (identity_isogeny G)
        r Q Q₀ b b₀ h h₀ χ 0 (by rw [hcχ]; exact hz)
  exact hdom.symm.trans (hv.trans (not_congr hV))

end Dominance

section SteinbergWeights

open Specs.SteinbergDimension (IsHalfPositiveRootSum)
open Representation.SteinbergDimension (steinbergWeight_pairing)
open Specs.SimpleClassification (SocleModel)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem steinbergWeight_dominant (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (ρ : Character P.torus.group) (hρ : IsHalfPositiveRootSum P ρ) (q : ℕ) :
    Dominant P (Additive.toMul ((q - 1) • Additive.ofMul ρ)) := by
  intro α c hc
  rw [steinbergWeight_pairing P ρ hρ q α c hc]
  exact Int.natCast_nonneg _

private theorem socleBasis_nonempty {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
    {χ : Character P.torus.group} (S : SocleModel P U χ) : Nonempty S.J := by
  by_contra! h
  let : IsEmpty S.J := h
  apply S.socle_simple.2.1
  rw [← Submodule.subsingleton_iff_eq_bot]
  exact S.socleBasis.equivFun.injective.subsingleton

end SteinbergWeights

section SemisimpleVanishing

open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open LinearAlgebraicGroups.AssociatedFlagLineSheaves (realizeSections)
open FlagRelativeFrobeniusAtlas (relativeFrobenius relativeFrobenius_formula)
open Specs.FlagRelativeFrobeniusAtlas (twist)
open private exists_associatedBundle from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {G : AffineAlgebraicGroup k}

/-- Kempf vanishing on a simply connected semisimple flag by the Steinberg
Frobenius pushforward and vanishing of high ample twists. -/
private theorem simplyConnectedVanishing
    (p : ℕ) [Fact p.Prime] [CharP k p] (hG : IsSemisimple G)
    (hsc : GeometricallySimplyConnected G) (P : OppositeBorelPair G)
    [IsCommMonObj P.torus.group.X] (D : Datum P.torus)
    (χ : Character P.torus.group) (hχ : IsDominant D P.positive χ)
    (Q : Presentation P.negative) (b : BorelProjection P) (h : FlagKernelPair Q)
    (i : ℕ) (hi : 0 < i) : IsZero (flagCohomology Q b χ h i) := by
  obtain ⟨ρ, hρ⟩ := Representation.SteinbergDimension.halfSumExists hG hsc P
  have ha := Representation.AmpleFlagWeights.strictDominanceImpliesAmple
    k G P hG D (χ * ρ) (strictlyDominant_mul_halfSum P D χ ρ hχ hρ) Q b
  obtain ⟨N, hN⟩ := AmpleFlagTwistVanishing.ampleFlagTwistVanishing P Q b h (χ * ρ) ρ⁻¹ ha
  let r := N + 1
  let q := p ^ r
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hq : 0 < q := Nat.pow_pos (Fact.out : p.Prime).pos
  have hlarge : N ≤ q := by
    exact (Nat.le_succ N).trans (Nat.lt_pow_self (n := r) (Fact.out : p.Prime).one_lt).le
  let σ := Additive.toMul ((q - 1) • Additive.ofMul ρ)
  obtain ⟨U, hU⟩ := LinearAlgebraicGroups.GeometricRadicals.unipotentRadicalExists
    (Unipotent.closedSubgroupAlgebraicGroup P.positive)
  obtain ⟨S, _⟩ := (Representation.SimpleClassification.classification G P U hU).2.2
    σ (steinbergWeight_dominant P ρ hρ q)
  let j := (socleBasis_nonempty S).some
  obtain ⟨_, _, _, _, _, _, _, a, _, _, ha⟩ :=
    (LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q
  obtain ⟨Lσ⟩ := exists_associatedBundle Q S.projection σ a ha
  obtain ⟨Lν⟩ := exists_associatedBundle Q S.projection χ a ha
  obtain ⟨Lsum⟩ := exists_associatedBundle Q S.projection (σ * χ ^ q) a ha
  let F := (relativeFrobenius p r).app Q.scheme
  have hF := relativeFrobenius_formula p r Q.scheme
  obtain ⟨e⟩ := LinearAlgebraicGroups.SteinbergFrobeniusPushforward.steinbergFrobeniusFormula
    p r hr hG hsc P U hU ρ hρ S χ (realizeSections Lσ) (realizeSections Lν)
    (realizeSections Lsum) ha F hF
  have hsum : IsZero ((cohomology Q.scheme i).obj (realizeSections Lsum).sheaf) := by
    apply IsZero.of_iso _ ((cohomology Q.scheme i).mapIso (associatedFlagSheafIso Lsum h))
    rw [flagLineSheaf_borelProjection_eq Q S.projection b]
    change IsZero (flagCohomology Q b (σ * χ ^ q) h i)
    rw [show σ * χ ^ q = ρ⁻¹ * (χ * ρ) ^ q from steinbergWeight_mul_pow ρ χ q hq]
    exact hN q hlarge i hi
  let H := cohomology ((twist p r).obj Q.scheme) i
  have ht := hsum.of_iso ((H.mapIso e).symm ≪≫
    frobeniusCohomologyIso p r Q F hF hr (realizeSections Lsum).sheaf i)
  have hν := isZero_cohomology_of_tensorFree (X := (twist p r).obj Q.scheme)
    (realizeSections Lν).sheaf j i ht
  have hz := (isZero_twist_cohomology_iff p r Q.scheme (realizeSections Lν).sheaf i).mp hν
  change IsZero ((cohomology Q.scheme i).obj (flagLineSheaf Q b χ h))
  rw [flagLineSheaf_borelProjection_eq Q b S.projection]
  exact hz.of_iso ((cohomology Q.scheme i).mapIso (associatedFlagSheafIso Lν h)).symm

end SemisimpleVanishing

section ReductiveVanishing

open Specs.CentralIsogenies (characterPullback)
open Specs.GeometricRadicals (IsSemisimple)

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : AffineAlgebraicGroup k}

/-- Pull the character to the marked simply connected cover. Its positive
roots correspond, so dominance transfers to the pulled-back character. -/
private theorem semisimpleVanishing
    (p : ℕ) [Fact p.Prime] [CharP k p] (hG : IsSemisimple G)
    (P : OppositeBorelPair G) (χ : Character P.torus.group)
    (hχ : Dominant P χ) (Q : Presentation P.negative) (b : BorelProjection P)
    (h : FlagKernelPair Q) (i : ℕ) (hi : 0 < i) : IsZero (flagCohomology Q b χ h i) := by
  obtain ⟨G', P', f, hG', hsc, hf, r, _, hpos⟩ :=
    Representation.SimplyConnectedFlagCover.simplyConnectedFlagCover G hG P
  obtain ⟨comm, ⟨D⟩⟩ := RootData.AbstractPairing.abstractPairing
    G P.reductive P.torus P.split P.maximal
  let := comm
  obtain ⟨comm', ⟨D'⟩⟩ := RootData.AbstractPairing.abstractPairing
    G' P'.reductive P'.torus P'.split P'.maximal
  let := comm'
  have hχD := (Representation.InducedNonvanishing.dominant_iff_datum
    Classification.CentralIsogenies.centralIsogenyComparison P D χ).mp hχ
  have hχ' := isDominant_centralIsogeny_pullback f hf r D' D hpos χ hχD
  let geo := LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G' P'
  obtain ⟨b'⟩ := geo.1
  obtain ⟨Q'⟩ := geo.2.1
  let h' : FlagKernelPair Q' := HomogeneousQuotient.quotientPullback Q'
  exact flagCohomology_isZero_of_centralIsogeny f hf r Q' Q b' b h' h χ i
    (simplyConnectedVanishing p hG' hsc P' D' (characterPullback r.torus χ) hχ' Q' b' h' i hi)

/-- The identification with the derived flag preserves every cohomology
group, including degree zero, which detects dominance of the restriction. -/
private theorem vanishing_overAlgClosed
    (p : ℕ) [Fact p.Prime] [CharP k p] (P : OppositeBorelPair G)
    (χ : Character P.torus.group) (Q : Presentation P.negative)
    (b : BorelProjection P) (h : FlagKernelPair Q)
    (h₀ : ¬ IsZero (flagCohomology Q b χ h 0)) (i : ℕ) (hi : 0 < i) :
    IsZero (flagCohomology Q b χ h i) := by
  obtain ⟨_, P', r, _, hD, ⟨b'⟩, ⟨Q'⟩, comparison⟩ :=
    Representation.DerivedFlagCohomology.derivedFlagComparison G P
  let h' : FlagKernelPair Q' := HomogeneousQuotient.quotientPullback Q'
  obtain ⟨_, _, _, _, _, _, cohomologyIso⟩ := comparison Q b χ h Q' b' h'
  obtain ⟨e₀, _⟩ := cohomologyIso 0
  obtain ⟨eᵢ, _⟩ := cohomologyIso i
  let χ' : Character P'.torus.group := r.torus ≫ χ
  have hχ' := (dominant_iff_not_isZero_flagCohomologyZero P' χ' Q' b' h').mpr
    (fun hz => h₀ (hz.of_iso e₀))
  exact (semisimpleVanishing p hD P' χ' hχ' Q' b' h' i hi).of_iso eᵢ

end ReductiveVanishing

/-- The associated line of a dominant character on the opposite flag has
zero cohomology in all positive degrees over a field of positive characteristic. -/
theorem positiveKempfVanishing : Specs.PositiveKempfVanishing.Statement.{u} := by
  classical
  intro k _ p _ _ G P χ hχ Q b h i hi
  by_cases hG : Specs.GeometricRadicals.IsSplitTorus G.val
  · exact splitTorusFlagVanishing P hG Q b χ h i hi
  let : CharP (AlgebraicClosure k) p :=
    (Algebra.charP_iff k (AlgebraicClosure k) p).mp inferInstance
  obtain ⟨E⟩ := Representation.FlagCohomologyOverAlgClosure.flagCohomologyOverAlgClosure Q b χ h
  have h₀ := (dominant_iff_not_isZero_flagCohomologyZero P χ Q b h).mp hχ
  have h₀K : ¬ IsZero (flagCohomology E.quotient.presentation E.projection
      (E.multiplicative.character χ) E.kernelPair 0) := by
    intro hz
    exact h₀ ((extendScalars_isZero_iff (K := AlgebraicClosure k) _).mp
      (hz.of_iso (E.cohomologyIso 0)))
  exact (extendScalars_isZero_iff (K := AlgebraicClosure k) _).mp
    ((vanishing_overAlgClosed p E.borels.pair (E.multiplicative.character χ)
      E.quotient.presentation E.projection E.kernelPair h₀K i hi).of_iso (E.cohomologyIso i))

end LinearAlgebraicGroups.PositiveKempfVanishing
