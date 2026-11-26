import Specs.LinearAlgebraicGroups.Arithmetic.ReductiveModelSpreading
import LinearAlgebraicGroups.Arithmetic.CentralCover
import LinearAlgebraicGroups.Arithmetic.CentralCoverSpreading
import LinearAlgebraicGroups.Classification.IntegralRealization
import LinearAlgebraicGroups.Reductive.RadicalBaseChange
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Module (finrank)
open scoped TensorProduct
open Algebra.TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.ReductiveModelSpreading

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals (IsReductive IsSemisimple)
open Specs.IntegralSemisimpleModel (Integers fibre)
open Specs.Pinning (BasedRootDatum AttachedDatum PinnedGroup)
open Specs.ReductiveModelSpreading (GenericSplitting SplitModel)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private exists_split_maximalTorus_finiteGalois from LinearAlgebraicGroups.Arithmetic.CentralCover
open private semisimple_iff_corootFullRank splitBorelPair
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private pinnedLift from LinearAlgebraicGroups.Classification.PinnedEquivalence

noncomputable section

set_option linter.style.haveILetI false

private def FullCorootRank (D : BasedRootDatum.{u}) : Prop :=
  finrank ℤ (Submodule.span ℤ (Set.range D.datum.coroot)) = finrank ℤ D.Y

private theorem fullCorootRank_iff {D D' : BasedRootDatum.{u}} (e : Specs.Pinning.BasedIso D D') :
    FullCorootRank D ↔ FullCorootRank D' := by
  let v := e.val
  have hv (i : D'.I) :
      v.coweightEquiv (D'.datum.coroot i) = D.datum.coroot (v.indexEquiv.symm i) :=
    RootPairing.Hom.coroot_coweightMap_apply D.datum D'.datum i v.toHom
  have hr : v.coweightEquiv '' Set.range D'.datum.coroot = Set.range D.datum.coroot := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨v.indexEquiv.symm i, (hv i).symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨_, ⟨v.indexEquiv i, rfl⟩, ?_⟩
      rw [hv, Equiv.symm_apply_apply]
  change finrank ℤ (Submodule.span ℤ (Set.range D.datum.coroot)) = finrank ℤ D.Y ↔
    finrank ℤ (Submodule.span ℤ (Set.range D'.datum.coroot)) = finrank ℤ D'.Y
  have hm :
      (Submodule.span ℤ (Set.range D'.datum.coroot)).map v.coweightEquiv.toLinearMap =
        Submodule.span ℤ (Set.range D.datum.coroot) := by
    rw [Submodule.map_span]
    exact congrArg (Submodule.span ℤ) hr
  rw [← hm, LinearEquiv.finrank_map_eq, ← v.coweightEquiv.finrank_eq]

private theorem semisimple_iff_fullCorootRank {k : Type u} [Field k]
    {P : Specs.Pinning.SplitBorelPair k} (D : AttachedDatum P) :
    IsSemisimple P.G ↔ FullCorootRank D.toBased :=
  semisimple_iff_corootFullRank P D

/-- Over a finite Galois extension the group has an actual identification with
the field fibre of a split integral model. The root rank comparison also
shows that the split model has semisimple fibres in every characteristic. -/
theorem genericSplitting : GenericSplitting.{u} := by
  intro K _ G hG
  obtain ⟨E, hE, hKE, hfin, hgal, T, hGE, hT, hmax⟩ :=
    exists_split_maximalTorus_finiteGalois G hG
  let P := splitBorelPair (baseChangedAlgebraicGroup E G)
    (reductive_of_semisimple _ hGE) T hT hmax
  let D := Classification.Pinning.attachedDatum P
  have hD : FullCorootRank D.toBased := (semisimple_iff_fullCorootRank D).mp hGE
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D.toBased
  have hM (F : Type u) [Field F] :
      ∃ H : AffineAlgebraicGroup F, IsSemisimple H ∧ Nonempty ((fibre F).obj M.group ≅ H.val) := by
    obtain ⟨A, V, e, _, _, _, _, _, _⟩ := M.fieldFibre F
    have hV := (fullCorootRank_iff V.datumIso).mp hD
    exact ⟨V.pinned.pair.G, (semisimple_iff_fullCorootRank V.attached).mpr hV, ⟨e⟩⟩
  obtain ⟨A, V, e, _, _, _, _, _, _⟩ := M.fieldFibre E
  obtain ⟨W, ⟨pin⟩⟩ := Classification.Pinning.pinningsExist A P
  let Q : PinnedGroup A := ⟨P, W, pin⟩
  obtain ⟨w, _⟩ := pinnedLift V.pinned Q V.attached D
    (Groupoid.inv (show D.toBased ⟶ V.attached.toBased from V.datumIso))
  exact ⟨E, hE, hKE, hfin, hgal, ⟨D.toBased, M, hM⟩, ⟨(e ≪≫ w.group).symm⟩⟩

section EtaleCover

open private exists_common_multiple from LinearAlgebraicGroups.Arithmetic.CentralCoverSpreading

variable {A E : Type u} [CommRing A] [IsDedekindDomain A] [Field E] [Algebra A E]

/-- Over a principal open the integral closure in a finite separable extension
is finite étale. The same denominator works after any further base change. -/
private theorem integralClosure_etale_after_inverting (K : Type u) [Field K]
    [Algebra A K] [IsFractionRing A K] [Algebra K E] [IsScalarTower A K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    ∃ d : A, d ≠ 0 ∧ ∀ (R : Type u) [CommRing R] [Algebra A R],
      IsUnit (algebraMap A R d) → Algebra.Etale R (R ⊗[A] integralClosure A E) := by
  classical
  let B := integralClosure A E
  letI : Module.Finite A B := IsIntegralClosure.finite A K E B
  letI : Module.IsTorsionFree A E := .trans_faithfulSMul A K E
  letI : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A E
  letI : Module.Flat A B := inferInstance
  letI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) E :=
    IsIntegralClosure.isLocalization_of_isSeparable A K E B
  letI : Algebra.FormallyUnramified K E := Algebra.FormallyUnramified.of_isSeparable K E
  let f := (KaehlerDifferential.map A K B E).restrictScalars A
  letI : IsLocalizedModule (nonZeroDivisors A) f :=
    KaehlerDifferential.isLocalizedModule A K B E (nonZeroDivisors A)
  letI : Module.Finite A (KaehlerDifferential A B) := Module.Finite.trans B _
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := KaehlerDifferential A B)
  choose a ha hkill using fun x : s =>
    (IsLocalizedModule.subsingleton_iff (nonZeroDivisors A) f).mp
      (inferInstance : Subsingleton (KaehlerDifferential K E)) x.val
  obtain ⟨d, hd, hdiv⟩ :=
    exists_common_multiple (fun x => (a x : A))
      (fun x => mem_nonZeroDivisors_iff_ne_zero.mp (ha x))
  have hdall (m : KaehlerDifferential A B) : d • m = 0 := by
    have hm : m ∈ Submodule.span A (s : Set (KaehlerDifferential A B)) := by
      rw [hs]
      trivial
    refine Submodule.span_induction ?_ (by simp) ?_ ?_ hm
    · intro x hx
      obtain ⟨r, hr⟩ := hdiv ⟨x, hx⟩
      rw [hr, mul_comm, mul_smul, hkill ⟨x, hx⟩, smul_zero]
    · intro x y _ _ hx hy
      rw [smul_add, hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_comm, hx, smul_zero]
  refine ⟨d, hd, fun R _ _ hu => ?_⟩
  letI : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hz : Subsingleton (R ⊗[A] KaehlerDifferential A B) := by
    refine (subsingleton_iff_forall_eq 0).mpr fun z => ?_
    refine TensorProduct.inductionOn (motive := fun x => x = 0) z ?_
      (fun x y hx hy => by rw [hx, hy, add_zero])
    intro r m
    obtain ⟨v, hv⟩ := hu
    have he : ((↑v⁻¹ : R) * r) ⊗ₜ[A] (d • m) = (r ⊗ₜ[A] m) := by
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, ← hv, ← mul_assoc, Units.mul_inv, one_mul]
    rw [← he, hdall, TensorProduct.tmul_zero]
  letI : Algebra B (R ⊗[A] B) := rightAlgebra
  letI : Algebra.FormallyUnramified R (R ⊗[A] B) :=
    ⟨(KaehlerDifferential.tensorKaehlerEquivBase A R B (R ⊗[A] B)).surjective.subsingleton⟩
  exact Algebra.Etale.of_formallyUnramified_of_flat

end EtaleCover

section ScalarExtension

set_option backward.isDefEq.respectTransparency false

open Specs.ReductiveModelSpreading (scalarExtension)
open Specs.IntegralCentralQuotient (OverBase HopfSpectrum)
open private radical_transport unipotent_of_iso connected_baseChange_iff
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected from LinearAlgebraicGroups.Solvable.WordDomainGeometry

local instance (priority := 2000) integerAlgebra (R : Type u) [CommRing R] :
    Algebra Integers.{u} R := Specs.IntegralSemisimpleModel.integerAlgebra R

local instance : MorphismProperty.RespectsIso @GeometricallyConnected := by
  rw [GeometricallyConnected.eq_geometrically]
  infer_instance

private theorem integerScalarTower (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    @IsScalarTower Integers.{u} R S (integerAlgebra R).toSMul
      (inferInstance : Algebra R S).toSMul (integerAlgebra S).toSMul := by
  apply IsScalarTower.of_algebraMap_eq (R := Integers.{u}) (S := R) (A := S)
  intro x
  exact (map_intCast (algebraMap R S) x.down).symm

private def scalarExtensionTower (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] :
    scalarExtension R T ≅ scalarExtension R S ⋙ scalarExtension S T := by
  have h : CentralCover.scalarSpec S T ≫ CentralCover.scalarSpec R S =
      CentralCover.scalarSpec R T := by
    rw [CentralCover.scalarSpec, CentralCover.scalarSpec, CentralCover.scalarSpec, ← Spec.map_comp]
    exact congrArg Spec.map
      (congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq R S T).symm)
  let e : Over.pullback (CentralCover.scalarSpec R T) ≅
      Over.pullback (CentralCover.scalarSpec R S) ⋙ Over.pullback (CentralCover.scalarSpec S T) :=
    eqToIso (congrArg (fun f : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R) =>
      Over.pullback f) h.symm) ≪≫ Over.pullbackComp _ _
  exact Functor.mapGrpNatIso e ≪≫ Functor.mapGrpCompIso

private abbrev underlying (R : Type u) [CommRing R] : Grp (OverBase R) ⥤ Scheme.{u} :=
  Grp.forget _ ⋙ Over.forget _

private theorem smooth_of_groupIso {R : Type u} [CommRing R] {G H : Grp (OverBase R)}
    (e : G ≅ H) (hs : Smooth H.X.hom) : Smooth G.X.hom := by
  let i := (underlying R).mapIso e
  have hw : i.hom ≫ H.X.hom = G.X.hom := e.hom.hom.hom.w
  rw [← hw]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) i.hom _).mpr hs

private theorem smooth_of_split {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {G : Grp (OverBase R)} (M : SplitModel.{u})
    (e : (scalarExtension R S).obj G ≅ (scalarExtension Integers.{u} S).obj M.model.group) :
    Smooth G.X.hom := by
  letI := M.model.smooth
  have hs := smooth_of_groupIso e (show Smooth
    (pullback.snd M.model.group.X.hom (CentralCover.scalarSpec Integers.{u} S)) from inferInstance)
  have fpqc : ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme.{u})
      (CentralCover.scalarSpec R S) := by
    have h := (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap R S))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
    exact ⟨⟨h.2, h.1⟩, inferInstanceAs (QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))⟩
  exact (MorphismProperty.pullback_snd_iff (P := @Smooth) fpqc).mp hs

private theorem reductive_of_groupIso {F : Type u} [Field F] {G H : AffineAlgebraicGroup F}
    (e : G.val ≅ H.val) (hH : IsReductive H) : IsReductive G := by
  let i := (underlying F).mapIso e
  have hw : i.hom ≫ H.val.X.hom = G.val.X.hom := e.hom.hom.hom.w
  have hc : GeometricallyConnected G.val.X.hom := by
    rw [← hw]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected)
      i.hom _).mpr hH.2.1
  refine ⟨smooth_of_groupIso e hH.1, hc, ?_⟩
  let j := (groupBaseChange F (AlgebraicClosure F)).mapIso e.symm
  let N := GeometricRadicals.geometricUnipotentRadical H
  have ht := radical_transport (G := GeometricRadicals.GeometricGroup H)
    (G' := GeometricRadicals.GeometricGroup G) j Specs.Unipotent.IsUnipotent
    (fun m _ _ => unipotent_of_iso m) N
    (LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest H)
  obtain ⟨c, _, _⟩ := LinearAlgebraicGroups.GeometricRadicals.radicalUnique
    (GeometricRadicals.GeometricGroup G) Specs.Unipotent.IsUnipotent
    (LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G) ht
  obtain ⟨t⟩ := hH.2.2
  exact ⟨c ≪≫ t⟩

private theorem fieldFibres_of_split {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {G : Grp (OverBase R)} (M : SplitModel.{u})
    (e : (scalarExtension R S).obj G ≅ (scalarExtension Integers.{u} S).obj M.model.group)
    (F : Type u) [Field F] [Algebra R F] (H : AffineAlgebraicGroup F)
    (i : (scalarExtension R F).obj G ≅ H.val) : IsReductive H := by
  let B := F ⊗[R] S
  letI : Module.FaithfullyFlat F B := inferInstance
  letI : Nontrivial B := (FaithfulSMul.algebraMap_injective F B).nontrivial
  letI : Algebra S B := rightAlgebra
  obtain ⟨p, hp⟩ := Ideal.exists_maximal B
  letI := hp
  let L := B ⧸ p
  letI : Field L := Ideal.Quotient.field p
  have tF := (scalarExtensionTower R F L).app G
  have tS := (scalarExtensionTower R S L).app G
  letI := integerScalarTower S L
  have tZ := (scalarExtensionTower Integers.{u} S L).app M.model.group
  obtain ⟨J, hJ, ⟨j⟩⟩ := M.semisimple L
  let c : (groupBaseChange F L).obj H.val ≅ J.val :=
    (scalarExtension F L).mapIso i.symm ≪≫ tF.symm ≪≫ tS ≪≫
      (scalarExtension S L).mapIso e ≪≫ tZ.symm ≪≫ j
  have hL := reductive_of_groupIso (G := baseChangedAlgebraicGroup L H) c
    (reductive_of_semisimple J hJ)
  letI := hL.2.1
  have conn : ConnectedSpace (baseChangedAlgebraicGroup L H).val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      (f := (baseChangedAlgebraicGroup L H).val.X.hom)
  letI := (connected_baseChange_iff (K := L) H).mp conn
  letI := smooth_of_split M e
  have hs := smooth_of_groupIso i.symm (show Smooth
    (pullback.snd G.X.hom (CentralCover.scalarSpec R F)) from inferInstance)
  exact (Reductive.RadicalBaseChange.reductiveFieldExtension H hs
    (geometricallyConnected_of_connected H)).mp hL

private theorem locallyOfFinitePresentation_hopfSpectrum (R U : Type u)
    [CommRing R] [CommRing U] [HopfAlgebra R U] [Algebra.FinitePresentation R U] :
    LocallyOfFinitePresentation (HopfSpectrum R U).X.hom := by
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R U)))
  exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

private def hopfAlgebraicGroup (F U : Type u) [Field F] [CommRing U] [HopfAlgebra F U]
    [Algebra.FinitePresentation F U] : AffineAlgebraicGroup F := by
  let h := locallyOfFinitePresentation_hopfSpectrum F U
  letI := h
  exact ⟨HopfSpectrum F U, inferInstanceAs (IsAffine (Spec (CommRingCat.of U))),
    inferInstance, inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap F U))))⟩

private def modelOfSplitting {R K S U : Type u} [CommRing R] [Field K] [CommRing S]
    [CommRing U] [Algebra R K] [Algebra R S] [HopfAlgebra R U]
    [Algebra.FinitePresentation R U] [Module.Finite R S] [Module.FaithfullyFlat R S]
    [Algebra.Etale R S] (G : AffineAlgebraicGroup K) (M : SplitModel.{u})
    (g : (scalarExtension R K).obj (HopfSpectrum R U) ≅ G.val)
    (e : (scalarExtension R S).obj (HopfSpectrum R U) ≅
      (scalarExtension Integers.{u} S).obj M.model.group) :
    Specs.ReductiveModelSpreading.ReductiveModel G (R := R) := by
  refine {
    group := HopfSpectrum R U
    affine := inferInstanceAs (IsAffine (Spec (CommRingCat.of U)))
    finitePresentation := locallyOfFinitePresentation_hopfSpectrum R U
    quasiCompact := inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R U))))
    smooth := smooth_of_split M e
    generic := g
    reductive := ?_
    split := M
    cover := S
    coverRing := inferInstance
    coverAlgebra := inferInstance
    coverFinite := inferInstance
    coverFaithfullyFlat := inferInstance
    coverEtale := inferInstance
    splitting := e }
  intro F _ _
  let H := hopfAlgebraicGroup F (F ⊗[R] U)
  let i : (scalarExtension R F).obj (HopfSpectrum R U) ≅ H.val :=
    CentralCover.hopfSpectrumBaseChangeIso
  exact ⟨H, fieldFibres_of_split M e F H i, ⟨i⟩⟩

end ScalarExtension

section CoordinateComparison

open Specs.CentralCoverSpreading (tensorComparison)
open private tensorComparison_natural tensorComparison_injective
  from LinearAlgebraicGroups.Arithmetic.CentralCoverSpreading

variable {R E : Type u} [CommRing R] [CommRing E] [Algebra R E]

private def tensorBialgEquiv {B C : Type u} [CommRing B] [CommRing C]
    [HopfAlgebra R B] [HopfAlgebra R C] (e : B ≃ₐc[R] C) :
    E ⊗[R] B ≃ₐc[E] E ⊗[R] C := by
  refine BialgEquiv.ofBialgHom (Bialgebra.TensorProduct.map (.id E E) e.toBialgHom)
    (Bialgebra.TensorProduct.map (.id E E) e.symm.toBialgHom) ?_ ?_
  all_goals
    apply BialgHom.coe_toAlgHom_injective
    apply Algebra.TensorProduct.ext'
    intro a b
    simp

private def tensorBialgTower (R S E B : Type u) [CommRing R] [CommRing S] [CommRing E]
    [CommRing B] [HopfAlgebra R B] [Algebra R S] [Algebra S E] [Algebra R E]
    [IsScalarTower R S E] : E ⊗[S] (S ⊗[R] B) ≃ₐc[E] E ⊗[R] B :=
  by
    let a := Algebra.TensorProduct.cancelBaseChange R S E E B
    refine BialgEquiv.ofAlgEquiv a ?_ ?_
    · apply Algebra.TensorProduct.ext_ring
      apply Algebra.TensorProduct.ext'
      intro s b
      simp [a, Bialgebra.counitAlgHom_apply, Algebra.smul_def, IsScalarTower.algebraMap_apply R S E]
    · apply Algebra.TensorProduct.ext_ring
      apply Algebra.TensorProduct.ext'
      intro s b
      simp [a, Bialgebra.comulAlgHom_apply, ← (Coalgebra.Repr.arbitrary R b).eq,
        TensorProduct.tmul_sum, Algebra.smul_def]

private def fibreInclusion {U Y : Type u} [CommRing U] [CommRing Y]
    [HopfAlgebra R U] [HopfAlgebra E Y] [Algebra R Y] [IsScalarTower R E Y]
    (e : E ⊗[R] U ≃ₐc[E] Y) : U →ₐ[R] Y :=
  (e.toAlgEquiv.toAlgHom.restrictScalars R).comp includeRight

@[simp] private theorem fibreInclusion_apply {U Y : Type u} [CommRing U] [CommRing Y]
    [HopfAlgebra R U] [HopfAlgebra E Y] [Algebra R Y] [IsScalarTower R E Y]
    (e : E ⊗[R] U ≃ₐc[E] Y) (x : U) :
    fibreInclusion e x = e (1 ⊗ₜ[R] x) := rfl

private theorem fibreInclusion_comul {U Y : Type u} [CommRing U] [CommRing Y]
    [HopfAlgebra R U] [HopfAlgebra E Y] [Algebra R Y] [IsScalarTower R E Y]
    (e : E ⊗[R] U ≃ₐc[E] Y) (x : U) :
    tensorComparison R E (fibreInclusion e) (fibreInclusion e) (Bialgebra.comulAlgHom R U x) =
      Bialgebra.comulAlgHom E Y (fibreInclusion e x) := by
  let i : U →ₐ[R] E ⊗[R] U := includeRight
  have h : tensorComparison R E i i (Bialgebra.comulAlgHom R U x) =
      Bialgebra.comulAlgHom E (E ⊗[R] U) (1 ⊗ₜ[R] x) := by
    simp [Bialgebra.comulAlgHom_apply, ← (Coalgebra.Repr.arbitrary R x).eq,
      TensorProduct.tmul_sum, tensorComparison, i]
  have hn : tensorComparison R E (fibreInclusion e) (fibreInclusion e) =
      ((map e.toAlgEquiv.toAlgHom e.toAlgEquiv.toAlgHom).restrictScalars R).comp
        (tensorComparison R E i i) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [tensorComparison, i]
  rw [hn]
  change map e.toAlgEquiv.toAlgHom e.toAlgEquiv.toAlgHom
      (tensorComparison R E i i (Bialgebra.comulAlgHom R U x)) = _
  rw [h]
  exact DFunLike.congr_fun e.toBialgHom.map_comp_comulAlgHom (1 ⊗ₜ[R] x)

private theorem fibreInclusion_counit {U Y : Type u} [CommRing U] [CommRing Y]
    [HopfAlgebra R U] [HopfAlgebra E Y] [Algebra R Y] [IsScalarTower R E Y]
    (e : E ⊗[R] U ≃ₐc[E] Y) (x : U) :
    Bialgebra.counitAlgHom E Y (fibreInclusion e x) =
      algebraMap R E (Bialgebra.counitAlgHom R U x) := by
  rw [fibreInclusion_apply]
  simp [Bialgebra.counitAlgHom_apply, Algebra.smul_def]

private theorem spreadBialgEquiv {S E U V Y : Type u} [CommRing S] [IsDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E] [CommRing U] [CommRing V] [CommRing Y]
    [HopfAlgebra S U] [HopfAlgebra S V] [HopfAlgebra E Y] [Algebra S Y] [IsScalarTower S E Y]
    [Module.Flat S U] [Module.Flat S V]
    (e : E ⊗[S] U ≃ₐc[E] Y) (f : E ⊗[S] V ≃ₐc[E] Y)
    (heq : (fibreInclusion e).range = (fibreInclusion f).range) :
    Nonempty (U ≃ₐc[S] V) := by
  let i := fibreInclusion e
  let j := fibreInclusion f
  have hi : Function.Injective i :=
    e.injective.comp (Module.Flat.tensorProduct_mk_injective S U E)
  have hj : Function.Injective j :=
    f.injective.comp (Module.Flat.tensorProduct_mk_injective S V E)
  let g := (AlgEquiv.ofInjective i hi).trans
    ((Subalgebra.equivOfEq _ _ heq).trans (AlgEquiv.ofInjective j hj).symm)
  have hg (x : U) : j (g x) = i x := by
    exact congrArg Subtype.val ((AlgEquiv.ofInjective j hj).apply_symm_apply
      (Subalgebra.equivOfEq _ _ heq ((AlgEquiv.ofInjective i hi) x)))
  letI : Module.Flat S E := IsLocalization.flat E (nonZeroDivisors S)
  letI : Module.Flat S Y := Module.Flat.trans S E Y
  refine ⟨BialgEquiv.ofAlgEquiv g ?_ ?_⟩
  · ext x
    apply IsFractionRing.injective S E
    change algebraMap S E (Bialgebra.counitAlgHom S V (g x)) =
      algebraMap S E (Bialgebra.counitAlgHom S U x)
    rw [← fibreInclusion_counit f, ← fibreInclusion_counit e]
    exact congrArg (Bialgebra.counitAlgHom E Y) (hg x)
  · ext x
    apply tensorComparison_injective (E := E) j j hj hj
    change tensorComparison S E j j (map g.toAlgHom g.toAlgHom (Bialgebra.comulAlgHom S U x)) =
      tensorComparison S E j j (Bialgebra.comulAlgHom S V (g x))
    rw [tensorComparison_natural (g' := AlgHom.id E Y) (h' := AlgHom.id E Y)
      (b := i) (c := i) hg hg, map_id, AlgHom.id_apply]
    rw [show j = fibreInclusion f by rfl, show i = fibreInclusion e by rfl,
      fibreInclusion_comul, fibreInclusion_comul]
    exact congrArg (Bialgebra.comulAlgHom E Y) (hg x).symm

end CoordinateComparison

section Denominators

open private finite_mem_adjoin_after_localization
  from LinearAlgebraicGroups.Arithmetic.CentralCoverSpreading

private theorem adjoin_eq_after_inverting {B E Y : Type u} [CommRing B] [IsDomain B]
    [Field E] [Algebra B E] [IsFractionRing B E] [CommRing Y]
    [Algebra B Y] [Algebra E Y] [IsScalarTower B E Y]
    (s t : Finset Y) (hs : Algebra.adjoin E (s : Set Y) = ⊤)
    (ht : Algebra.adjoin E (t : Set Y) = ⊤) :
    ∃ b : B, b ≠ 0 ∧ ∀ (S : Type u) [CommRing S] [Algebra B S]
      [Algebra S Y] [IsScalarTower B S Y],
      IsUnit (algebraMap B S b) → Algebra.adjoin S (s : Set Y) = Algebra.adjoin S (t : Set Y) := by
  obtain ⟨b₁, hb₁, h₁⟩ := finite_mem_adjoin_after_localization (A := B) _ hs (fun x : t => x.val)
  obtain ⟨b₂, hb₂, h₂⟩ := finite_mem_adjoin_after_localization (A := B) _ ht (fun x : s => x.val)
  refine ⟨b₁ * b₂, mul_ne_zero hb₁ hb₂, fun S _ _ _ _ hu => le_antisymm ?_ ?_⟩
  · exact Algebra.adjoin_le fun x hx => h₂ S
      (isUnit_of_dvd_unit (map_dvd (algebraMap B S) (dvd_mul_left b₂ b₁)) hu) ⟨x, hx⟩
  · exact Algebra.adjoin_le fun x hx => h₁ S
      (isUnit_of_dvd_unit (map_dvd (algebraMap B S) (dvd_mul_right b₁ b₂)) hu) ⟨x, hx⟩

private theorem exists_base_multiple {A B E : Type u} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field E] [Algebra A B] [Algebra B E] [Algebra A E]
    [IsScalarTower A B E] [IsFractionRing B E]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) E]
    (b : B) (hb : b ≠ 0) : ∃ a : A, a ≠ 0 ∧ b ∣ algebraMap A B a := by
  obtain ⟨⟨x, ⟨_, a, ha, rfl⟩⟩, h⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      ((algebraMap B E b)⁻¹)
  refine ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp ha, x, ?_⟩
  apply IsFractionRing.injective B E
  have hn : algebraMap B E b ≠ 0 := fun h => hb ((IsFractionRing.injective B E) (h.trans (map_zero _).symm))
  change (algebraMap B E b)⁻¹ * algebraMap B E (algebraMap A B a) = algebraMap B E x at h
  rw [map_mul, ← h, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

end Denominators

section Construction

set_option backward.isDefEq.respectTransparency false

open Specs.IntegralCentralQuotient (HopfSpectrum)
open Specs.CentralCoverSpreading (GenericFibre)
open Specs.ReductiveModelSpreading (scalarExtension Statement)
open private exists_coordinate_model from LinearAlgebraicGroups.Descent.Forms
open private affineSpectrum from LinearAlgebraicGroups.Classification.IntegralRealization
open private exists_hopf_denominator localizationMap localization_tower localization_dedekind
  localization_fractionRing adjoin_isBaseChange flat_of_injective_into_field_module
  extendAmbientMap extendAmbientMap_range extendAmbientMap_tmul
  RestrictedOperations.hopfAlgebra RestrictedOperations.comul_agrees
  RestrictedOperations.counit_agrees RestrictedOperations.antipode_agrees
  from LinearAlgebraicGroups.Arithmetic.CentralCoverSpreading

private def bialgEquivOfSpectrumIso {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    [HopfAlgebra R B] [HopfAlgebra R C] (e : HopfSpectrum R C ≅ HopfSpectrum R B) :
    B ≃ₐc[R] C :=
  CommHopfAlgCat.ofIso (((hopfSpec.fullyFaithful (R := CommRingCat.of R)).isoEquiv.symm e).unop)

private theorem smooth_hopfCoordinates {R C : Type u} [CommRing R] [CommRing C]
    [HopfAlgebra R C] (h : Smooth (HopfSpectrum R C).X.hom) : Algebra.Smooth R C :=
  RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)
    (φ := CommRingCat.ofHom (algebraMap R C))).mp h)

private theorem tensor_range {A R D Y : Type u} [CommRing A] [CommRing R] [CommRing D]
    [CommRing Y] [Algebra A R] [Algebra A D] [Algebra A Y] [Algebra R Y] [IsScalarTower A R Y]
    (f : D →ₐ[A] Y) (s : Set D) (hs : Algebra.adjoin A s = ⊤) :
    (AlgHom.liftEquiv A R D Y f).range = Algebra.adjoin R (f '' s) := by
  have h : AlgHom.liftEquiv A R D Y f = extendAmbientMap f := by
    apply Algebra.TensorProduct.ext'
    intro r x
    rw [extendAmbientMap_tmul, AlgHom.liftEquiv_tmul, Algebra.smul_def]
  rw [h, extendAmbientMap_range f s hs]

private theorem tensor_fibre_range {A S E D Y : Type u} [CommRing A] [CommRing S]
    [CommRing E] [CommRing D] [CommRing Y] [Algebra A S] [Algebra S E] [Algebra A E]
    [IsScalarTower A S E] [HopfAlgebra A D] [HopfAlgebra E Y]
    [Algebra A Y] [Algebra S Y] [IsScalarTower A E Y] [IsScalarTower S E Y]
    [IsScalarTower A S Y] (e : E ⊗[A] D ≃ₐc[E] Y)
    (s : Set D) (hs : Algebra.adjoin A s = ⊤) :
    (fibreInclusion ((tensorBialgTower A S E D).trans e)).range =
      Algebra.adjoin S (fibreInclusion e '' s) := by
  have h : fibreInclusion ((tensorBialgTower A S E D).trans e) =
      AlgHom.liftEquiv A S D Y (fibreInclusion e) := by
    apply Algebra.TensorProduct.ext'
    intro a x
    change e (Algebra.TensorProduct.cancelBaseChange A S E E D
        (1 ⊗ₜ[S] (a ⊗ₜ[A] x))) = a • e (1 ⊗ₜ[A] x)
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    rw [← TensorProduct.smul_tmul' a (1 : E) x]
    exact (e.toAlgEquiv.restrictScalars S).toLinearEquiv.map_smul a (1 ⊗ₜ[A] x)
  rw [h, tensor_range _ _ hs]

private theorem fibre_generators {A E D Y : Type u} [CommRing A] [CommRing E]
    [CommRing D] [CommRing Y] [Algebra A E] [HopfAlgebra A D] [HopfAlgebra E Y]
    [Algebra A Y] [IsScalarTower A E Y] (e : E ⊗[A] D ≃ₐc[E] Y)
    (s : Set D) (hs : Algebra.adjoin A s = ⊤) :
    Algebra.adjoin E (fibreInclusion e '' s) = ⊤ := by
  have h : AlgHom.liftEquiv A E D Y (fibreInclusion e) = e.toAlgEquiv.toAlgHom :=
    (AlgHom.liftEquiv A E D Y).apply_symm_apply _
  rw [← tensor_range _ _ hs, h, AlgHom.range_eq_top]
  exact e.surjective

private theorem towerFromLocalization {A R S E : Type u} [CommRing A] [CommRing R]
    [CommRing S] [CommRing E] [Algebra A R] [Algebra R S] [Algebra A S]
    [Algebra R E] [Algebra A E] [Algebra S E] [IsScalarTower A R S]
    [IsScalarTower A R E] [IsScalarTower A S E] (d : A) [IsLocalization.Away d R] :
    IsScalarTower R S E := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext (Submonoid.powers d)
  ext x
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A R E,
    ← IsScalarTower.algebraMap_apply A R S, ← IsScalarTower.algebraMap_apply A S E]

private theorem algebraTowerAbove (A B S E : Type u) [CommRing A] [CommRing B] [CommRing S]
    [CommRing E] [Algebra A B] [Algebra A S] [Algebra A E] [Algebra B S]
    [Algebra B E] [Algebra S E] [IsScalarTower A B S] [IsScalarTower A B E]
    [IsScalarTower B S E] : IsScalarTower A S E :=
  IsScalarTower.to₁₃₄ A B S E

private theorem algebraTowerBelow (A B S E : Type u) [CommRing A] [CommRing B] [CommRing S]
    [CommRing E] [Algebra A B] [Algebra A S] [Algebra A E] [Algebra B S]
    [Algebra B E] [Algebra S E] [IsScalarTower A B S] [IsScalarTower A S E]
    [IsScalarTower B S E] : IsScalarTower A B E :=
  IsScalarTower.to₁₂₄ A B S E

set_option maxHeartbeats 1000000 in
/-- A connected semisimple group over a number field spreads to a smooth
affine model with reductive fibres and a finite étale splitting cover. -/
theorem reductiveModelSpreading : Statement.{u} := by
  classical
  intro K _ _ G hG
  obtain ⟨E, hE, hKE, hfin, hgal, M, ⟨gE⟩⟩ := genericSplitting K G hG
  obtain ⟨X, hX, ⟨gX⟩⟩ := exists_coordinate_model G
  obtain ⟨C, ⟨gC⟩⟩ := affineSpectrum M.model.group M.model.affine
  letI : Algebra Integers.{u} E := Specs.IntegralSemisimpleModel.integerAlgebra E
  letI : Module Integers.{u} E := (inferInstance : Algebra Integers.{u} E).toModule
  letI : Module Integers.{u} C := (inferInstance : Algebra Integers.{u} C).toModule
  let Y := E ⊗[K] X
  have hg : HopfSpectrum E Y ≅ HopfSpectrum E (E ⊗[Integers.{u}] C) :=
    CentralCover.hopfSpectrumBaseChangeIso.symm ≪≫ (scalarExtension K E).mapIso gX ≪≫ gE ≪≫
      (scalarExtension Integers.{u} E).mapIso gC.symm ≪≫ CentralCover.hopfSpectrumBaseChangeIso
  let e : E ⊗[Integers.{u}] C ≃ₐc[E] Y := bialgEquivOfSpectrumIso hg
  letI : Algebra.Smooth Integers.{u} C := smooth_hopfCoordinates (smooth_of_groupIso gC M.model.smooth)
  letI : Module.Flat Integers.{u} C := inferInstance
  let A := NumberField.RingOfIntegers K
  letI : Algebra A E := ((algebraMap K E).comp (algebraMap A K)).toAlgebra
  letI : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' rfl
  let B := integralClosure A E
  letI : Module.Finite A B := IsIntegralClosure.finite A K E B
  letI : Module.IsTorsionFree A E := .trans_faithfulSMul A K E
  letI : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A E
  letI : Module.Flat A B := inferInstance
  letI : Module.FaithfullyFlat A B := inferInstance
  letI : IsFractionRing B E := IsIntegralClosure.isFractionRing_of_finite_extension A K E B
  letI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K E B
  letI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) E :=
    IsIntegralClosure.isLocalization_of_isSeparable A K E B
  letI : Algebra B Y := ((algebraMap E Y).comp (algebraMap B E)).toAlgebra
  letI := IsScalarTower.of_algebraMap_eq' (R := B) (S := E) (A := Y) rfl
  letI : Algebra Integers.{u} Y := ((algebraMap E Y).comp (algebraMap Integers.{u} E)).toAlgebra
  letI := IsScalarTower.of_algebraMap_eq' (R := Integers.{u}) (S := E) (A := Y) rfl
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := K) (A := X)
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := Integers.{u}) (A := C)
  let i : X →ₐ[K] Y := includeRight
  let j : C →ₐ[Integers.{u}] Y := fibreInclusion e
  let s' := s.image i
  let t' := t.image j
  have hs' : Algebra.adjoin E (s' : Set Y) = ⊤ := by
    rw [Finset.coe_image]
    exact fibre_generators (BialgEquiv.refl E Y) _ hs
  have ht' : Algebra.adjoin E (t' : Set Y) = ⊤ := by
    rw [Finset.coe_image]
    exact fibre_generators e _ ht
  obtain ⟨b, hb, hcomparison⟩ := adjoin_eq_after_inverting (B := B) s' t' hs' ht'
  obtain ⟨a, ha, hab⟩ := exists_base_multiple (A := A) (E := E) b hb
  obtain ⟨q, hq, hetale⟩ := integralClosure_etale_after_inverting (A := A) (E := E) K
  letI : Algebra A X := ((algebraMap K X).comp (algebraMap A K)).toAlgebra
  letI : IsScalarTower A K X := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨p, hp, hmodel⟩ := exists_hopf_denominator (A := A) s hs
  let d := p * (q * a)
  have hd : d ≠ 0 := mul_ne_zero hp (mul_ne_zero hq ha)
  let R := Localization.Away d
  let rK := (localizationMap (E := K) d hd).toAlgebra
  letI : Algebra R K := rK
  letI : IsScalarTower A R K := localization_tower (E := K) d hd
  refine ⟨d, hd, rK, inferInstance, ?_⟩
  letI : IsDedekindDomain R := localization_dedekind d hd
  letI : IsFractionRing R K := localization_fractionRing d hd
  letI : Algebra R X := ((algebraMap K X).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K X := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A R X := IsScalarTower.to₁₂₄ A R K X
  have hu : IsUnit (algebraMap A R d) := IsLocalization.Away.algebraMap_isUnit d
  obtain ⟨o⟩ := hmodel R (isUnit_of_dvd_unit (map_dvd (algebraMap A R) (dvd_mul_right _ _)) hu)
  let U := Algebra.adjoin R (s : Set X)
  letI : HopfAlgebra R U := RestrictedOperations.hopfAlgebra o Subtype.val_injective
  letI : Module.Flat R U := flat_of_injective_into_field_module (E := K) U.val Subtype.val_injective
  letI : Algebra.FinitePresentation R U :=
    Algebra.FinitePresentation.of_finiteType.mp (.adjoin_of_finite s.finite_toSet)
  let f : GenericFibre R K U X :=
    ⟨U.val, adjoin_isBaseChange (A := R) _ hs, RestrictedOperations.comul_agrees o,
      RestrictedOperations.counit_agrees o, RestrictedOperations.antipode_agrees o⟩
  let b₀ := algebraMap A B d
  have hb₀ : b₀ ≠ 0 := fun h => hd ((FaithfulSMul.algebraMap_injective A B) (h.trans (map_zero _).symm))
  let S := Localization.Away b₀
  letI : IsDedekindDomain S := localization_dedekind b₀ hb₀
  letI : Algebra A S := ((algebraMap B S).comp (algebraMap A B)).toAlgebra
  letI := IsScalarTower.of_algebraMap_eq' (R := A) (S := B) (A := S) rfl
  let iRS : R →ₐ[A] S := IsLocalization.Away.liftAlgHom d (f := Algebra.ofId A S)
    (IsLocalization.Away.algebraMap_isUnit b₀)
  letI : Algebra R S := iRS.toAlgebra
  letI := IsScalarTower.of_algebraMap_eq' (R := A) (S := R) (A := S) iRS.comp_algebraMap.symm
  letI : Algebra S E := (localizationMap (E := E) b₀ hb₀).toAlgebra
  letI := localization_tower (E := E) b₀ hb₀
  letI : IsFractionRing S E := localization_fractionRing b₀ hb₀
  letI := algebraTowerAbove A B S E
  letI : Algebra R E := ((algebraMap K E).comp (algebraMap R K)).toAlgebra
  letI := IsScalarTower.of_algebraMap_eq' (R := R) (S := K) (A := E) rfl
  letI := algebraTowerBelow A R K E
  letI := towerFromLocalization (R := R) (S := S) (E := E) d
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers d)) S := by
    change IsLocalization ((Submonoid.powers d).map (algebraMap A B)) S
    rw [Submonoid.map_powers]
    infer_instance
  letI : Algebra.IsPushout A R B S :=
    (Algebra.isPushout_of_isLocalization (Submonoid.powers d) R B S).symm
  let qS := Algebra.IsPushout.equiv A R B S
  letI : Module.Finite R S := Module.Finite.of_surjective qS.toLinearMap qS.surjective
  letI : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_linearEquiv R (R ⊗[A] B) qS.toLinearEquiv.symm
  letI : Algebra.Etale R (R ⊗[A] B) := hetale R
    (isUnit_of_dvd_unit (map_dvd (algebraMap A R) ((dvd_mul_right q a).trans (dvd_mul_left _ _))) hu)
  letI : Algebra.Etale R S := Algebra.Etale.of_equiv qS
  letI : Algebra S Y := ((algebraMap E Y).comp (algebraMap S E)).toAlgebra
  letI := IsScalarTower.of_algebraMap_eq' (R := S) (S := E) (A := Y) rfl
  letI := algebraTowerBelow B S E Y
  letI : Algebra R Y := ((algebraMap E Y).comp (algebraMap R E)).toAlgebra
  letI := IsScalarTower.of_algebraMap_eq' (R := R) (S := E) (A := Y) rfl
  letI := algebraTowerBelow R S E Y
  letI : Algebra Integers.{u} S := Specs.IntegralSemisimpleModel.integerAlgebra S
  letI : Module Integers.{u} S := (inferInstance : Algebra Integers.{u} S).toModule
  letI := integerScalarTower S E
  letI := algebraTowerBelow Integers.{u} S E Y
  let k := (tensorBialgTower R K E U).symm.trans
    (tensorBialgEquiv (E := E) (CentralCover.genericBialgEquiv f))
  let eU := (tensorBialgTower R S E U).trans k
  let eC := (tensorBialgTower Integers.{u} S E C).trans e
  let sU : Set U := U.val ⁻¹' (s : Set X)
  have hsU : Algebra.adjoin R sU = ⊤ := by
    apply Subalgebra.map_injective (f := U.val) Subtype.val_injective
    have hsub : (s : Set X) ⊆ Set.range U.val :=
      fun x hx => ⟨⟨x, Algebra.subset_adjoin hx⟩, rfl⟩
    rw [← Algebra.adjoin_image, Algebra.map_top, Subalgebra.range_val]
    change Algebra.adjoin R (U.val '' (U.val ⁻¹' (s : Set X))) = U
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr hsub]
  have hk (x : U) : fibreInclusion k x = i x.val := by
    change (tensorBialgEquiv (E := E) (CentralCover.genericBialgEquiv f))
      ((Algebra.TensorProduct.cancelBaseChange R K E E U).symm (1 ⊗ₜ[R] x)) = _
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    change (1 : E) ⊗ₜ[K] CentralCover.genericBialgEquiv f (1 ⊗ₜ[R] x) = _
    rw [CentralCover.genericBialgEquiv_tmul, one_smul]
    rfl
  have hrs : (fibreInclusion k '' sU) = (s' : Set Y) := by
    rw [Finset.coe_image]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, (hk x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Algebra.subset_adjoin hx⟩, hx, hk _⟩
  have hrU := tensor_fibre_range (S := S) k sU hsU
  have hrC := tensor_fibre_range (S := S) e (t : Set C) ht
  have hbd : b ∣ b₀ := hab.trans (map_dvd (algebraMap A B)
    ((dvd_mul_left a q).trans (dvd_mul_left _ p)))
  have heq : (fibreInclusion eU).range = (fibreInclusion eC).range := by
    rw [show (fibreInclusion eU).range = _ from hrU, hrs,
      show (fibreInclusion eC).range = _ from hrC, ← Finset.coe_image]
    exact hcomparison S (isUnit_of_dvd_unit (map_dvd (algebraMap B S) hbd)
      (IsLocalization.Away.algebraMap_isUnit b₀))
  obtain ⟨l⟩ := spreadBialgEquiv eU eC heq
  let g : (scalarExtension R K).obj (HopfSpectrum R U) ≅ G.val :=
    CentralCover.genericFibreIso f ≪≫ gX
  let eS : (scalarExtension R S).obj (HopfSpectrum R U) ≅ (scalarExtension Integers.{u} S).obj M.model.group :=
    CentralCover.hopfSpectrumBaseChangeIso ≪≫ CentralCover.hopfSpectrumIsoOfBialgEquiv l.symm ≪≫
      CentralCover.hopfSpectrumBaseChangeIso.symm ≪≫ (scalarExtension Integers.{u} S).mapIso gC
  exact ⟨modelOfSplitting G M g eS⟩

end Construction

section Completions

set_option backward.isDefEq.respectTransparency false

open Specs.ReductiveModelSpreading (CompletedBaseChange scalarExtension)

/-- Pulling back the model and its splitting to a completed valuation ring
uses the unique map out of the prescribed principal localization. -/
theorem completedBaseChange : CompletedBaseChange.{u} := by
  intro K _ _ G d _ _ M v
  dsimp only
  intro hd
  let A := NumberField.RingOfIntegers K
  let R := Localization.Away d
  let O := v.adicCompletionIntegers K
  let L := v.adicCompletion K
  let i : R →ₐ[A] O := IsLocalization.Away.liftAlgHom d (f := Algebra.ofId A O) hd
  letI : Algebra R O := i.toAlgebra
  letI : IsScalarTower A R O := IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A R L := IsScalarTower.to₁₂₄ A R K L
  letI : IsScalarTower R O L := towerFromLocalization d
  letI := M.coverRing
  letI := M.coverAlgebra
  letI := M.coverFinite
  letI := M.coverFaithfullyFlat
  letI := M.coverEtale
  let T := O ⊗[R] M.cover
  letI : Algebra M.cover T := rightAlgebra
  letI : Algebra Integers.{u} M.cover := Specs.IntegralSemisimpleModel.integerAlgebra M.cover
  letI : Algebra Integers.{u} T := Specs.IntegralSemisimpleModel.integerAlgebra T
  letI := integerScalarTower M.cover T
  refine ⟨i.toAlgebra, inferInstance, ⟨?_⟩, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  · exact (scalarExtensionTower R O L).app M.group |>.symm.trans
      (((scalarExtensionTower R K L).app M.group).trans ((scalarExtension K L).mapIso M.generic))
  · exact ((scalarExtensionTower R O T).app M.group).symm ≪≫
      (scalarExtensionTower R M.cover T).app M.group ≪≫
      (scalarExtension M.cover T).mapIso M.splitting ≪≫
      ((scalarExtensionTower Integers.{u} M.cover T).app M.split.model.group).symm

end Completions

end

end LinearAlgebraicGroups.Arithmetic.ReductiveModelSpreading
