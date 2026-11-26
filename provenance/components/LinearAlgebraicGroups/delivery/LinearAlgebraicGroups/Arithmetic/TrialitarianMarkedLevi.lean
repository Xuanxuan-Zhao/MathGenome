import Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianMarkedLevi
import LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import LinearAlgebraicGroups.Flag.StandardParabolicLevi
import LinearAlgebraicGroups.Relative.MaximalSplitTori
import LinearAlgebraicGroups.Reductive.SplitToriConjugacy
import LinearAlgebraicGroups.Reductive.RadicalBaseChange
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianMarkedLevi

open LinearAlgebraicGroups.Specs
open Specs.AutomorphismSequence
open Specs.GeometricRadicals (IsReductive)
open Specs.Pinning (AttachedDatum PinnedGroup)
open Specs.QuasiSplitInnerForms (outerHom pinnedSection)
open Specs.RelativeFormComparison
open Specs.RootGroups (AdditiveLine)
open Specs.CharacterDescent (Cocharacter)
open Specs.StandardParabolicLevi (HasFace)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

variable {F K S : Type u} [Field F] [Field K] [Field S]
  [Algebra F K] [Algebra F S] [Algebra K S] [IsScalarTower F K S]

private abbrev fieldRestriction : fieldTest F S ⟶ fieldTest F K :=
  (testSpec F).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom F K S)).op

private theorem restrict_fieldMap (σ : Gal(S/F)) (τ : Gal(K/F))
    (h : σ.toAlgHom.comp (IsScalarTower.toAlgHom F K S) =
      (IsScalarTower.toAlgHom F K S).comp τ.toAlgHom) :
    fieldMap F S σ ≫ fieldRestriction (F := F) (K := K) (S := S) =
      fieldRestriction ≫ fieldMap F K τ := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  congr 1
  apply congrArg Quiver.Hom.op
  exact CommAlgCat.hom_ext h

private theorem outer_restrict {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {Q : AdjointQuotient P.pair.G} (seq : SplitSequence P D l Q)
    (v : fieldTest F S ⟶ fieldTest F K)
    (f : RelativeAut P.pair.G.val (fieldTest F K)) :
    outerHom seq (restrictAut v f) = outerHom seq f := by
  have h := ConcreteCategory.congr_hom (seq.outer.naturality v.op) f
  change (seq.outer.app (op (fieldTest F S))).hom (restrictAut v f) =
    ((constantGroup (k := F) (Aut D.toBased)).map v.op).hom
      ((seq.outer.app (op (fieldTest F K))).hom f) at h
  change Specs.QuasiSplitInnerForms.constantEvaluation F S _
      ((seq.outer.app (op (fieldTest F S))).hom (restrictAut v f)) =
    Specs.QuasiSplitInnerForms.constantEvaluation F K _
      ((seq.outer.app (op (fieldTest F K))).hom f)
  rw [h]
  letI : Subsingleton (fieldTest F K).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact congrArg ((seq.outer.app (op (fieldTest F K))).hom f).down (Subsingleton.elim _ _)

private theorem restrict_transport_generic {G H : GroupScheme F} {X Y : SchemeOver F}
    (v : X ⟶ Y) (s : X ⟶ X) (t : Y ⟶ Y) (h : s ≫ v = v ≫ t)
    (i : relativePoints G Y ≅ relativePoints H Y) :
    restrictIso s (restrictIso v i) ≪≫ (restrictIso v i).symm =
      restrictIso v (restrictIso t i ≪≫ i.symm) := by
  have h' : restrictIso s (restrictIso v i) = restrictIso v (restrictIso t i) := by
    change restrictIso (s ≫ v) i = restrictIso (v ≫ t) i
    rw [h]
  rw [h']
  apply Iso.ext
  apply NatTrans.ext
  rfl

private theorem transportedAut_restrict {G H : GroupScheme F}
    (i : relativePoints G (fieldTest F K) ≅ relativePoints H (fieldTest F K))
    (σ : Gal(S/F)) (τ : Gal(K/F))
    (h : fieldMap F S σ ≫ fieldRestriction (F := F) (K := K) (S := S) =
      fieldRestriction ≫ fieldMap F K τ) :
    transportedAut F S (restrictIso fieldRestriction i) σ =
      restrictAut fieldRestriction (transportedAut F K i τ) :=
  congrArg Aut.of (restrict_transport_generic fieldRestriction (fieldMap F S σ)
    (fieldMap F K τ) h i)

/-- Conjugation by a point of the reference group has trivial outer image. -/
private theorem outer_inner {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {Q : AdjointQuotient P.pair.G} (seq : SplitSequence P D l Q)
    (g : fieldTest F S ⟶ P.pair.G.val.X) :
    outerHom seq (innerAut g) = 1 := by
  apply (LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.splitKernel seq _).mpr
  exact ⟨⟨g ≫ Q.projection.hom.hom⟩, seq.onLift _ _⟩

/-- The outer coefficients of the descent cocycle are unchanged by
precomposing the comparison with an inner automorphism. -/
private theorem outer_transport_inner {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {Q : AdjointQuotient P.pair.G} (seq : SplitSequence P D l Q)
    {G : GroupScheme F}
    (i : relativePoints P.pair.G.val (fieldTest F S) ≅ relativePoints G (fieldTest F S))
    (g : fieldTest F S ⟶ P.pair.G.val.X) (σ : Gal(S/F)) :
    outerHom seq (transportedAut F S ((innerAut g).asIso ≪≫ i) σ) =
      outerHom seq (transportedAut F S i σ) := by
  have h := (LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.splitCoefficientMaps
    (S := S) seq).1 σ (innerAut g)
  rw [LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.changeOfTrivialization,
    map_mul, map_mul, map_inv, h, outer_inner]
  simp

/-- Pulling the corrected comparison to the separable closure gives the same
outer action as the original comparison. -/
private theorem outer_transport_of_restriction {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {Q : AdjointQuotient P.pair.G} (seq : SplitSequence P D l Q)
    {G : GroupScheme F}
    (i : relativePoints P.pair.G.val (fieldTest F S) ≅ relativePoints G (fieldTest F S))
    (iK : relativePoints P.pair.G.val (fieldTest F K) ≅ relativePoints G (fieldTest F K))
    (g : fieldTest F S ⟶ P.pair.G.val.X)
    (hi : restrictIso fieldRestriction iK = (innerAut g).asIso ≪≫ i)
    (σ : Gal(S/F)) (τ : Gal(K/F))
    (h : σ.toAlgHom.comp (IsScalarTower.toAlgHom F K S) =
      (IsScalarTower.toAlgHom F K S).comp τ.toAlgHom) :
    outerHom seq (transportedAut F K iK τ) =
      outerHom seq (transportedAut F S i σ) := by
  let v : fieldTest F S ⟶ fieldTest F K := fieldRestriction
  calc
    _ = outerHom seq (restrictAut v (transportedAut F K iK τ)) :=
      (outer_restrict seq v (transportedAut F K iK τ)).symm
    _ = outerHom seq (transportedAut F S (restrictIso v iK) σ) :=
      congrArg (outerHom seq) (transportedAut_restrict iK σ τ (restrict_fieldMap σ τ h)).symm
    _ = outerHom seq (transportedAut F S ((innerAut g).asIso ≪≫ i) σ) :=
      congrArg (fun j => outerHom seq (transportedAut F S j σ)) hi
    _ = _ := outer_transport_inner seq i g σ

section FiniteLevel

open LinearAlgebraicGroups.Descent.Forms
open scoped TensorProduct

open private exists_coordinate_model applyIso inLevel inLevel_tmul raiseIso_inLevel raiseIso_symm
  from LinearAlgebraicGroups.Descent.Forms
open private schemeIsoEquiv hopfIsoEquiv hopfIsoEquiv_ground hopfIsoEquiv_evaluate
  coordinatePoint coordinatePoint_projection coordinatePoint_field coordinatePoint_ext projection groundIso
  from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private extendedGroupIso extendedSpecIso_hom_fst
  from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem scalar_comparison (E : Type u) [Field E] [Algebra F E] :
    IsScalarExtensionComparison (extendedGroupIso (k := F) E) :=
  fun B => extendedSpecIso_hom_fst E B

private abbrev coordinateChange (B : HopfAlgebraCategory F) :
    extendedHopf K B →ₐ[F] extendedHopf S B :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom F K S) (AlgHom.id F B)

private abbrev spectrumChange (B : HopfAlgebraCategory F) :
    Spec (CommRingCat.of (extendedHopf S B)) ⟶ Spec (CommRingCat.of (extendedHopf K B)) :=
  Spec.map (CommRingCat.ofHom (coordinateChange B).toRingHom)

private theorem spectrumChange_projection (B : HopfAlgebraCategory F) :
    spectrumChange B ≫ projection (S := K) B = projection (S := S) B := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  change B at b
  change (algebraMap K S 1) ⊗ₜ[F] b = (1 : S) ⊗ₜ[F] b
  rw [map_one]

private theorem spectrumChange_field (B : HopfAlgebraCategory F) :
    spectrumChange B ≫ (specGroup (extendedHopf K B)).X.hom =
      (specGroup (extendedHopf S B)).X.hom ≫ (fieldRestriction (F := F) (K := K) (S := S)).left := by
  change Spec.map (CommRingCat.ofHom (coordinateChange B).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (extendedHopf K B))) =
    Spec.map (CommRingCat.ofHom (algebraMap S (extendedHopf S B))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K S))
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

private theorem coordinatePoint_fieldRestriction {B : HopfAlgebraCategory F}
    (U : Over (fieldTest F S)) (x : U.left ⟶ (specGroup B).X) :
    coordinatePoint (extendedGroupIso K)
      (Over.mk (U.hom ≫ fieldRestriction (F := F) (K := K) (S := S))) x =
      coordinatePoint (extendedGroupIso S) U x ≫ spectrumChange B := by
  let V : Over (fieldTest F K) :=
    Over.mk (U.hom ≫ fieldRestriction (F := F) (K := K) (S := S))
  apply coordinatePoint_ext (A := B) (extendedGroupIso K) (scalar_comparison K)
  · calc
      _ = x.left := coordinatePoint_projection (extendedGroupIso K) (scalar_comparison K) V x
      _ = coordinatePoint (extendedGroupIso S) U x ≫ projection (S := S) B :=
        (coordinatePoint_projection (extendedGroupIso S) (scalar_comparison S) U x).symm
      _ = _ := (congrArg (coordinatePoint (extendedGroupIso S) U x ≫ ·)
        (spectrumChange_projection (K := K) (S := S) B).symm).trans
          (Category.assoc _ _ _).symm
  · calc
      _ = V.hom.left := coordinatePoint_field (extendedGroupIso K) V x
      _ = (coordinatePoint (extendedGroupIso S) U x ≫ (specGroup (extendedHopf S B)).X.hom) ≫
          (fieldRestriction (F := F) (K := K) (S := S)).left :=
        congrArg (· ≫ (fieldRestriction (F := F) (K := K) (S := S)).left)
          (coordinatePoint_field (extendedGroupIso S) U x).symm
      _ = _ := (Category.assoc _ _ _).trans
        ((congrArg (coordinatePoint (extendedGroupIso S) U x ≫ ·)
          (spectrumChange_field (K := K) (S := S) B).symm).trans
            (Category.assoc _ _ _).symm)

variable (L : FiniteGaloisIntermediateField F S)

private theorem coordinateChange_eq_inLevel (B : HopfAlgebraCategory F)
    (x : extendedHopf L B) : coordinateChange (S := S) B x = inLevel L B x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact (inLevel_tmul L a b).symm
  | add x y hx hy =>
    rw [map_add, hx, hy]
    change _ = (scalarTowerIso B).hom.hom ((1 : S) ⊗ₜ[L] (x + y))
    rw [TensorProduct.tmul_add, map_add]

private theorem spectrumChange_inv_naturality {B C : HopfAlgebraCategory F}
    (j : extendedHopf L B ≅ extendedHopf L C) :
    spectrumChange B ≫ Spec.map (CommRingCat.ofHom j.inv.hom.toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom
        (raiseIso (S := S) j).inv.hom.toAlgHom.toRingHom) ≫ spectrumChange C := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  have h := raiseIso_inLevel (k := F) (S := S) L j.symm x
  rw [raiseIso_symm] at h
  change coordinateChange B (j.inv.hom x) =
    (raiseIso (S := S) j).inv.hom (coordinateChange C x)
  rw [coordinateChange_eq_inLevel L, coordinateChange_eq_inLevel L]
  exact h.symm

private abbrev groundRelIso {G H : GroupScheme F} (V : SchemeOver F) (e : G ≅ H) :
    relativePoints G V ≅ relativePoints H V :=
  (yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget V).op).mapIso e

private theorem restrict_ground_trans {G H B C : GroupScheme F} {V W : SchemeOver F}
    (v : W ⟶ V) (b : G ≅ B) (c : C ≅ H)
    (j : relativePoints B V ≅ relativePoints C V) :
    restrictIso v (groundRelIso V b ≪≫ j ≪≫ groundRelIso V c) =
      groundRelIso W b ≪≫ restrictIso v j ≪≫ groundRelIso W c := by
  apply Iso.ext
  apply NatTrans.ext
  rfl

private theorem restrict_hopf_level {B C : HopfAlgebraCategory F} {G H : GroupScheme F}
    (b : specGroup B ≅ G) (c : specGroup C ≅ H)
    (j : extendedHopf L B ≅ extendedHopf L C) :
    restrictIso fieldRestriction (hopfIsoEquiv (extendedGroupIso L) b c j) =
      hopfIsoEquiv (extendedGroupIso S) b c (raiseIso j) := by
  have h₀ : restrictIso fieldRestriction
      (hopfIsoEquiv (extendedGroupIso L) (Iso.refl (specGroup B)) (Iso.refl (specGroup C)) j) =
        hopfIsoEquiv (extendedGroupIso S) (Iso.refl (specGroup B)) (Iso.refl (specGroup C))
          (raiseIso j) := by
    apply Iso.ext
    apply NatTrans.ext
    funext U
    apply GrpCat.ext
    intro x
    apply Over.OverMorphism.ext
    let V : Over (fieldTest F L) :=
      Over.mk (U.unop.hom ≫ fieldRestriction (F := F) (K := L) (S := S))
    let xL : V.left ⟶ (specGroup B).X := x
    have hL := hopfIsoEquiv_evaluate (A := B) (B := C) (extendedGroupIso L)
      (scalar_comparison L) j V xL
    have hS := hopfIsoEquiv_evaluate (A := B) (B := C) (extendedGroupIso S)
      (scalar_comparison S) (raiseIso j) U.unop x
    refine hL.trans (Eq.trans ?_ hS.symm)
    dsimp only [V, xL]
    rw [coordinatePoint_fieldRestriction, Category.assoc, ← Category.assoc (spectrumChange B),
      spectrumChange_inv_naturality L j]
    simp only [Category.assoc, spectrumChange_projection (K := L) (S := S) C]
  calc
    _ = restrictIso fieldRestriction
          (groundIso (S := L) b.symm ≪≫
            hopfIsoEquiv (extendedGroupIso L) (Iso.refl (specGroup B)) (Iso.refl (specGroup C)) j ≪≫
            groundIso (S := L) c) :=
      congrArg (restrictIso fieldRestriction) (hopfIsoEquiv_ground _ b c j)
    _ = groundIso (S := S) b.symm ≪≫ restrictIso
          (fieldRestriction (F := F) (K := L) (S := S))
          (hopfIsoEquiv (extendedGroupIso L) (Iso.refl (specGroup B)) (Iso.refl (specGroup C)) j) ≪≫
          groundIso (S := S) c :=
      restrict_ground_trans fieldRestriction b.symm c _
    _ = groundIso (S := S) b.symm ≪≫
          hopfIsoEquiv (extendedGroupIso S) (Iso.refl (specGroup B)) (Iso.refl (specGroup C))
            (raiseIso j) ≪≫ groundIso (S := S) c :=
      congrArg (fun t : relativePoints (specGroup B) (fieldTest F S) ≅
        relativePoints (specGroup C) (fieldTest F S) =>
        groundIso (S := S) b.symm ≪≫ t ≪≫ groundIso (S := S) c) h₀
    _ = _ := (hopfIsoEquiv_ground _ b c (raiseIso j)).symm


/-- A relative isomorphism between finite-type affine groups is defined on
a finite Galois layer containing a prescribed layer. -/
private theorem exists_finite_level [IsGalois F S] (G H : AffineAlgebraicGroup F)
    (i : relativePoints G.val (fieldTest F S) ≅ relativePoints H.val (fieldTest F S))
    (L₀ : FiniteGaloisIntermediateField F S) :
    ∃ (L : FiniteGaloisIntermediateField F S)
      (j : relativePoints G.val (fieldTest F L) ≅ relativePoints H.val (fieldTest F L)),
      L₀ ≤ L ∧ restrictIso fieldRestriction j = i := by
  obtain ⟨B, hB, ⟨b⟩⟩ := exists_coordinate_model G
  obtain ⟨C, hC, ⟨c⟩⟩ := exists_coordinate_model H
  obtain ⟨j, rfl⟩ := (hopfIsoEquiv (extendedGroupIso S) b c).surjective i
  obtain ⟨L, jL, hL, rfl⟩ := (finiteLevelIsomorphisms B C hB hC L₀ j)
  exact ⟨L, hopfIsoEquiv (extendedGroupIso L) b c jL, hL, restrict_hopf_level L b c jL⟩

end FiniteLevel

section Dominance

open Specs.BorelsAndChambers (positiveRoots subgroupRoots)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Pinning (SplitBorelPair)
open Specs.AbstractPairing (Root)

open private regularPerturbation from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private evaluate_root from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private precomp_pairing conjugatesSubgroups_square subgroupOf_limit_of_rootSigns
  connected_of_geometricallyConnected from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private conjugationIso inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
/-- The split-torus cocharacter has a dominant conjugate given by a ground-field
point of the torus normalizer. -/
private theorem dominant_conjugate (P : SplitBorelPair F) (D : AttachedDatum P)
    (c : Cocharacter P.T.group) :
    ∃ (g : 𝟙_ (SchemeOver F) ⟶ P.G.val.X) (d : Cocharacter P.T.group)
      (J : Set D.toBased.I),
      (c ≫ P.T.inclusion) ≫ (conjugationIso g).hom = d ≫ P.T.inclusion ∧
      J ⊆ D.toBased.base.support ∧ (letI := D.comm; HasFace D.base J d) := by
  letI := D.comm
  obtain ⟨r, hr, hsign⟩ := regularPerturbation P.G P.T P.split c
  obtain ⟨b, _, hb, _, hB⟩ :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT
      P.G P.reductive P.T P.split P.maximal).1 P.B P.borel P.containsTorus
  let sys := LinearAlgebraicGroups.RootData.BorelsAndChambers.positiveSystemsFromCocharacters
    P.G P.reductive P.T P.split P.maximal
  have h₁ := (sys (positiveRoots P.T r)).mpr ⟨r, hr, rfl⟩
  have h₂ := (sys (subgroupRoots P.T P.B)).mpr ⟨b, hb, hB.symm⟩
  obtain ⟨g, e, _, he, hpos, _⟩ :=
    (LinearAlgebraicGroups.RootData.BorelNormalizer.weylSimplyTransitiveOnPositiveSystems
      P.G P.reductive P.T P.split P.maximal).2.2 _ _ h₁ h₂
  let d : Cocharacter P.T.group := c ≫ e.hom
  have ht := conjugatesSubgroups_square g e he
  have hd (α : Root P.T) (hα : α ∈ D.base.support) :
      0 ≤ pairing P.T.group α.val d := by
    have hα' := ((D.simple_iff α).mp hα).1
    have hm : α.val ∈ Subtype.val '' subgroupRoots P.T P.B := ⟨α, hα', rfl⟩
    rw [← hpos] at hm
    obtain ⟨_, ⟨β, hβ, rfl⟩, hβα⟩ := hm
    change e.inv ≫ β.val = α.val at hβα
    rw [show d = c ≫ e.hom from rfl, precomp_pairing, ← hβα, Iso.hom_inv_id_assoc]
    exact hsign β hβ
  let J : Set D.toBased.I := {α | α ∈ D.base.support ∧ pairing P.T.group α.val d = 0}
  refine ⟨g, d, J, ?_, fun α hα => hα.1, fun α hα => hα.2, fun α hα => ?_⟩
  · rw [Category.assoc, ht, ← Category.assoc]
  · exact lt_of_le_of_ne (hd α hα.1) (fun h => hα.2 ⟨hα.1, h.symm⟩)

/-- The full simple face gives the whole group as its limit parabolic. -/
private theorem full_face_isIso (P : SplitBorelPair F) (D : AttachedDatum P)
    (d : Cocharacter P.T.group) (M : LimitDecomposition (d ≫ P.T.inclusion))
    (h : ∀ α ∈ D.toBased.base.support, pairing P.T.group α.val d = 0) :
    IsIso M.parabolic.inclusion := by
  classical
  letI := D.comm
  have hz (i : Root P.T) : pairing P.T.group i.val d = 0 := by
    rw [← evaluate_root D.datum d]
    obtain ⟨a, _, _, he⟩ := D.base.exists_root_eq_sum_int i
    rw [he, map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [map_zsmul, evaluate_root, h j hj, smul_zero]
  let whole : ClosedSubgroup P.G.val := ⟨P.G.val, 𝟙 _, by
    change IsClosedImmersion (𝟙 P.G.val.X.left)
    infer_instance⟩
  have ht : IsSubgroupOf P.T whole := ⟨P.T.inclusion, Category.comp_id _⟩
  have hG := P.reductive
  obtain ⟨j, hj⟩ := subgroupOf_limit_of_rootSigns P.G hG P.T whole P.split P.maximal
    hG.1 (connected_of_geometricallyConnected hG.2.1) ht d M
    (fun α _ => (hz α).ge)
  letI := inclusion_mono M.parabolic
  change j ≫ M.parabolic.inclusion = 𝟙 _ at hj
  refine ⟨⟨j, (cancel_mono M.parabolic.inclusion).1 ?_, hj⟩⟩
  rw [Category.assoc, hj, Category.comp_id, Category.id_comp]

end Dominance

section LimitComparisons

open Specs.RankOneFlag (SameSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (existsLimitDecomposition)
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private pushSubgroup from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private subgroupIso_of_same limits_subgroups_extend same_subgroup_of_same_sections
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private pushLimitParabolic from LinearAlgebraicGroups.Relative.RationalCocharacter
open private gm_baseChange from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private theorem centralizes_postcomp {G H C : GroupScheme F} (e : G ≅ H)
    (c : C ⟶ G) {U : SchemeOver F} (x : U ⟶ G.X) :
    Centralizes (c ≫ e.hom) (x ≫ e.hom.hom.hom) ↔ Centralizes c x := by
  rw [centralizes_iff, centralizes_iff]
  haveI : IsIso e.hom.hom.hom := (Grp.forget (SchemeOver F)).map_isIso e.hom
  have h (Y : SchemeOver F) (t : Y ⟶ U) (a : Y ⟶ C.X) :
      Commute (t ≫ x ≫ e.hom.hom.hom) (a ≫ c.hom.hom ≫ e.hom.hom.hom) ↔
        Commute (t ≫ x) (a ≫ c.hom.hom) := by
    let m := IsMonHom.monoidHom e.hom.hom.hom Y
    have hm : Function.Injective m := fun p q hpq => (cancel_mono e.hom.hom.hom).mp hpq
    change Commute (t ≫ x ≫ e.hom.hom.hom) (a ≫ c.hom.hom ≫ e.hom.hom.hom) ↔ _
    rw [← Category.assoc, ← Category.assoc a]
    exact ⟨fun h => Commute.of_map hm h, fun h => h.map m⟩
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    (forall_congr' fun Y => forall_congr' fun t => forall_congr' fun a => h Y t a)

/-- Limit parabolics and centralizers are transported by the same ambient
isomorphism when it transports the defining cocharacter. -/
private theorem compare_limits (G H : AffineAlgebraicGroup F) (e : G.val ≅ H.val)
    {c : Cocharacter G.val} {d : Cocharacter H.val} (he : c ≫ e.hom = d)
    (C : LimitDecomposition c) (D : LimitDecomposition d) :
    ∃ (p : C.parabolic.group ≅ D.parabolic.group) (l : C.centralizer.group ≅ D.centralizer.group),
      C.parabolic.inclusion ≫ e.hom = p.hom ≫ D.parabolic.inclusion ∧
      C.centralizer.inclusion ≫ e.hom = l.hom ≫ D.centralizer.inclusion := by
  subst d
  obtain ⟨p, hp⟩ := subgroupIso_of_same (pushLimitParabolic G H e C D)
  have h : RepresentsSubgroup (pushSubgroup e C.centralizer)
      (fun _ x => Centralizes (c ≫ e.hom) x) := by
    intro U x
    let y := x ≫ e.inv.hom.hom
    have hx : y ≫ e.hom.hom.hom = x := by
      change (x ≫ ((Grp.forget _).mapIso e).inv) ≫ ((Grp.forget _).mapIso e).hom = x
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hx]
    change Centralizes (c ≫ e.hom) (y ≫ e.hom.hom.hom) ↔ _
    rw [centralizes_postcomp e c y]
    apply (C.centralizer_points U y).trans
    have hι : (pushSubgroup e C.centralizer).inclusion.hom.hom =
      C.centralizer.inclusion.hom.hom ≫ e.hom.hom.hom := rfl
    change (∃ z : U ⟶ C.centralizer.group.X, z ≫ C.centralizer.inclusion.hom.hom = y) ↔
      (∃ z : U ⟶ C.centralizer.group.X, z ≫ (pushSubgroup e C.centralizer).inclusion.hom.hom =
        y ≫ e.hom.hom.hom)
    haveI : Mono e.hom.hom.hom := by
      letI : IsIso e.hom.hom.hom := (Grp.forget (SchemeOver F)).map_isIso e.hom
      infer_instance
    simp only [hι, ← Category.assoc, cancel_mono]
  obtain ⟨l, hl⟩ := subgroupIso_of_same (same_subgroup_of_same_sections (H := H) h D.centralizer_points)
  exact ⟨p, l, hp.symm, hl.symm⟩

end LimitComparisons

section SplitAlignment

open Specs.GeometricRadicals (IsMaximalTorus IsSplitTorus IsTorus IsSplitReductive)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Pinning (SplitBorelPair)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)

open private inverseBaseChangeIso splitTorus_baseChange connected_of_geometricallyConnected
  conjugatesSubgroups_square smooth_baseChangedGroup geomConnected_baseChangedGroup
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private multiplicative_group_iso from LinearAlgebraicGroups.Relative.LeviConjugacy
open private cocharacterImageIsTorus geometricMaximal_of_rationalMaximal
  multiplicativeBaseChange extendCocharacter multiplicativeGroup
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private centralizer_of_split_maximal splitTorus_hom_descends splitTorus_isTorus
  from LinearAlgebraicGroups.Reductive.SplitToriConjugacy
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private extendSubgroup from LinearAlgebraicGroups.RootData.RankOneFlag
open private conjugationIso exists_maximal_torus_over
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem split_of_separably_closed [IsSepClosed F]
    {T : GroupScheme F} (hT : IsTorus T) : IsSplitTorus T := by
  obtain ⟨E, _, _, _, h⟩ := hT
  let e : F ≃ₐ[F] E := AlgEquiv.ofBijective (Algebra.ofId F E) (IsSepClosed.algebraMap_bijective F E)
  letI : Algebra E F := e.symm.toRingHom.toAlgebra
  let n : groupBaseChange F E ⋙ groupBaseChange E F ≅ 𝟭 (GroupScheme F) :=
    inverseBaseChangeIso (fun x => e.symm_apply_apply x)
  obtain ⟨r, ⟨j⟩⟩ := splitTorus_baseChange (K := F) h
  exact ⟨r, ⟨(n.app T).symm ≪≫ j⟩⟩

private theorem selfCentralizing_extend (E : Type u) [Field E] [Algebra F E]
    {G : GroupScheme F} (T : ClosedSubgroup G)
    (hT : RepresentsSubgroup T (fun _ x => Centralizes T.inclusion x)) :
    RepresentsSubgroup (extendSubgroup E T)
      (fun _ x => Centralizes (extendSubgroup E T).inclusion x) :=
  (LinearAlgebraicGroups.centralizerSchemeBaseChange F E T.inclusion T hT).choose_spec

private theorem maximal_of_selfCentralizing (G : AffineAlgebraicGroup F) (T : ClosedSubgroup G.val)
    (hT : IsTorus T.group)
    (hC : RepresentsSubgroup T (fun _ x => Centralizes T.inclusion x)) : IsMaximalTorus T := by
  refine ⟨hT, ?_⟩
  rintro U hU ⟨j, hj⟩
  letI : IsCommMonObj U.group.X := torus_commutative (closedSubgroupAlgebraicGroup U) hU
  have hc : Centralizes T.inclusion U.inclusion.hom.hom := by
    rw [← hj, centralizes_iff]
    intro Y y t
    letI : CommMonoid (Y ⟶ U.group.X) := CategoryTheory.Hom.commMonoid
    let m := IsMonHom.monoidHom U.inclusion.hom.hom Y
    change Commute (m y) (t ≫ (j ≫ U.inclusion).hom.hom)
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact (Commute.all y (t ≫ j.hom.hom)).map m
  obtain ⟨f, hf⟩ := (hC _ _).mp hc
  exact factor_group_through_subgroup T U.inclusion f hf

/-- A cocharacter of the split group over the separable closure can be
aligned with the original split torus using an actual rational point. -/
private theorem align_cocharacter_with_torus [IsSepClosed S] (P : SplitBorelPair F)
    (c : Cocharacter ((groupBaseChange F S).obj P.G.val)) :
    ∃ (g : 𝟙_ (SchemeOver S) ⟶ ((groupBaseChange F S).obj P.G.val).X)
      (d : Cocharacter P.T.group),
      (extendCocharacter S (d ≫ P.T.inclusion)) ≫ (conjugationIso g).hom = c := by
  let G := baseChangedAlgebraicGroup S P.G
  let T := extendSubgroup S P.T
  have hG : IsReductive G :=
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension
      (K := S) P.G P.reductive.1 P.reductive.2.1).mpr P.reductive
  have hT : IsSplitTorus T.group := splitTorus_baseChange P.split
  obtain ⟨_, hC⟩ := centralizer_of_split_maximal
    LinearAlgebraicGroups.Reductive.WeylScheme.weylScheme P.G P.reductive P.T P.split P.maximal
  have hTS := selfCentralizing_extend S P.T hC
  have hTm : IsGeometricallyMaximal T := by
    let E := AlgebraicClosure S
    let T' := extendSubgroup E T
    have hs : IsSplitTorus T'.group := splitTorus_baseChange hT
    exact ⟨T'.isClosedImmersion, maximal_of_selfCentralizing (baseChangedAlgebraicGroup E G) T'
      (splitTorus_isTorus hs) (selfCentralizing_extend E T hTS)⟩
  obtain ⟨C, p, hC', hp, _, _⟩ := cocharacterImageIsTorus G c
  obtain ⟨V, hV, j, hj⟩ := exists_maximal_torus_over G C hC'
  have hVs : IsSplitTorus V.group := split_of_separably_closed hV.1
  have hVm := geometricMaximal_of_rationalMaximal G hG.1
    (connected_of_geometricallyConnected hG.2.1) V hV
  have hSplit : IsSplitReductive G := ⟨hG, T, hT, hTm⟩
  obtain ⟨g, e, he⟩ :=
    LinearAlgebraicGroups.Reductive.SplitToriConjugacy.splitToriConjugacy G hSplit T V hT hVs hTm hVm
  let m : Cocharacter T.group := p ≫ j ≫ e.inv
  have hm : m ≫ T.inclusion ≫ (conjugationIso g).hom = c := by
    rw [conjugatesSubgroups_square g e he]
    dsimp only [m]
    simp only [Category.assoc, e.inv_hom_id_assoc, hj, hp]
  let n := multiplicativeBaseChange F S
  have hM : IsSplitTorus (multiplicativeGroup F) := ⟨1, multiplicative_group_iso⟩
  obtain ⟨d, hd⟩ := splitTorus_hom_descends (K := S) hM P.split (n.inv ≫ m)
  change (groupBaseChange F S).map d = n.inv ≫ m at hd
  refine ⟨g, d, ?_⟩
  change (n.hom ≫ (groupBaseChange F S).map (d ≫ P.T.inclusion)) ≫
      (conjugationIso g).hom = c
  rw [(groupBaseChange F S).map_comp, ← Category.assoc n.hom, hd, n.hom_inv_id_assoc,
    Category.assoc]
  exact hm

end SplitAlignment

section StandardParabolicType

open Specs.GeometricBorelConjugacy (ConjugatesSubgroups IsBorel subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.RankOneFlag (SameSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private restrictSubgroup compose_restrict transportSubgroup conjugationIso
  conjugates_preserves_borel conjugates_in_ambient conjugates_trans normalizes_of_conjugates_self
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private transportSubgroupOf
  from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private conjugates_transport_ambient conjugates_same_target isBorel_of_same
  isKBorel_iff_of_isAlgClosed conjugates_inverse
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private borel_transport from LinearAlgebraicGroups.Reductive.BorelProper
open private borel_in_subgroup from LinearAlgebraicGroups.Flag.StandardParabolics
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

/-- If an inner conjugacy takes one subgroup through the fixed Borel to
another, conjugacy of Borels within the target shows that the conjugating
element already belongs to the target. -/
private theorem same_standard_parabolic [IsAlgClosed F]
    (G : AffineAlgebraicGroup F) (hG : IsReductive G)
    (B P Q : ClosedSubgroup G.val) (hB : IsBorel B)
    (hBP : IsSubgroupOf B P) (hBQ : IsSubgroupOf B Q)
    (hPs : Smooth P.group.X.hom) (hPc : ConnectedSpace P.group.X.left)
    (g : 𝟙_ (SchemeOver F) ⟶ G.val.X) (hg : ConjugatesSubgroups g Q P) :
    SameSubgroup Q P := by
  let e := conjugationIso g
  let Bg := transportSubgroup e B
  have hBg : IsBorel Bg := borel_transport hB e
  have hBgP : IsSubgroupOf Bg P :=
    subgroupOf_trans
      (transportSubgroupOf hBQ e)
      (conjugates_same_target (conjugates_transport_ambient Q g) hg).1
  obtain ⟨b, hb⟩ := hBP
  obtain ⟨c, hc⟩ := hBgP
  let B₁ := restrictSubgroup B P b hb
  let B₂ := restrictSubgroup Bg P c hc
  have hB₁ : subgroupOfSubgroup P B₁ = B := compose_restrict B P b hb
  have hB₂ : subgroupOfSubgroup P B₂ = Bg := compose_restrict Bg P c hc
  obtain ⟨u, hu⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.borelsConjugate
    (closedSubgroupAlgebraicGroup P) hPs hPc B₂ B₁
    (borel_in_subgroup B₂ (hB₂.symm ▸ hBg)) (borel_in_subgroup B₁ (hB₁.symm ▸ hB))
  have hu' := conjugates_in_ambient P hu
  rw [hB₂, hB₁] at hu'
  let x := u ≫ P.inclusion.hom.hom
  have hnorm : Normalizes B.inclusion (x * g) :=
    normalizes_of_conjugates_self B (conjugates_trans (conjugates_transport_ambient B g) hu')
  have hxg : x * g ∈ SubgroupSections P (𝟙_ (SchemeOver F)) := by
    obtain ⟨y, hy⟩ :=
      (LinearAlgebraicGroups.RootData.BorelNormalizer.groundFieldBorelNormalizer G hG B
        ((isKBorel_iff_of_isAlgClosed G B).mpr hB) _ _).mp hnorm
    refine ⟨y ≫ b.hom.hom, ?_⟩
    change (y ≫ b.hom.hom) ≫ P.inclusion.hom.hom = x * g
    rw [Category.assoc, ← Grp.comp_hom_hom, hb, hy]
  have hx : x ∈ SubgroupSections P (𝟙_ (SchemeOver F)) := ⟨u, rfl⟩
  have hgP : g ∈ SubgroupSections P (𝟙_ (SchemeOver F)) := by
    simpa only [inv_mul_cancel_left] using
      (SubgroupSections P _).mul_mem ((SubgroupSections P _).inv_mem hx) hxg
  obtain ⟨v, hv⟩ := hgP
  have hgg : ConjugatesSubgroups g P P := hv ▸ conjugates_preserves_borel P v
  exact (conjugates_same_target
    (conjugates_inverse hg)
    (conjugates_inverse hgg))

end StandardParabolicType

section RelativeSquares

open private relativeInclusion relativeSchemeIso relativeSchemeIso_natural
  relativeYoneda relativeYonedaIso relativeYonedaFullyFaithful relativeSectionEquiv relativeSection_natural
  from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private schemeIsoEquiv induced_iff from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private baseChangeProjection_effectiveEpi
  from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem relativeYoneda_naturality {G H : GroupScheme F}
    (f : G ⟶ H) (V : SchemeOver F) :
    (relativeYoneda V).map ((Over.pullback V.hom).mapGrp.map f) ≫
      (relativeYonedaIso V H).hom =
      (relativeYonedaIso V G).hom ≫ relativeInclusion f V := by
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  exact relativeSection_natural U.unop f.hom.hom x

private theorem relative_inclusion_square {G H C D : GroupScheme F}
    (V : SchemeOver F) (f : C ⟶ G) (g : D ⟶ H)
    (i : relativePoints G V ≅ relativePoints H V)
    (j : relativePoints C V ≅ relativePoints D V) :
    relativeInclusion f V ≫ i.hom = j.hom ≫ relativeInclusion g V ↔
      (Over.pullback V.hom).mapGrp.map f ≫ (relativeSchemeIso i).hom =
        (relativeSchemeIso j).hom ≫ (Over.pullback V.hom).mapGrp.map g := by
  let E := relativeYonedaFullyFaithful V
  have hi := E.map_preimage
    ((relativeYonedaIso V G) ≪≫ i ≪≫ (relativeYonedaIso V H).symm).hom
  have hj := E.map_preimage
    ((relativeYonedaIso V C) ≪≫ j ≪≫ (relativeYonedaIso V D).symm).hom
  change (relativeYoneda V).map (relativeSchemeIso i).hom = _ at hi
  change (relativeYoneda V).map (relativeSchemeIso j).hom = _ at hj
  have hg : (relativeYonedaIso V D).inv ≫
      (relativeYoneda V).map ((Over.pullback V.hom).mapGrp.map g) =
      relativeInclusion g V ≫ (relativeYonedaIso V H).inv := by
    apply (cancel_epi (relativeYonedaIso V D).hom).mp
    apply (cancel_mono (relativeYonedaIso V H).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using
      relativeYoneda_naturality g V
  have hleft : (relativeYoneda V).map
      ((Over.pullback V.hom).mapGrp.map f ≫ (relativeSchemeIso i).hom) =
      (relativeYonedaIso V C).hom ≫ (relativeInclusion f V ≫ i.hom) ≫
        (relativeYonedaIso V H).inv := by
    rw [Functor.map_comp, hi]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← Category.assoc ((relativeYoneda V).map _), relativeYoneda_naturality, Category.assoc]
  have hright : (relativeYoneda V).map
      ((relativeSchemeIso j).hom ≫ (Over.pullback V.hom).mapGrp.map g) =
      (relativeYonedaIso V C).hom ≫ (j.hom ≫ relativeInclusion g V) ≫
        (relativeYonedaIso V H).inv := by
    rw [Functor.map_comp, hj]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hg]
  constructor
  · intro h
    apply E.map_injective
    rw [hleft, hright, h]
  · intro h
    have h' := congrArg ((relativeYoneda V).map) h
    rw [hleft, hright] at h'
    exact (cancel_mono (relativeYonedaIso V H).inv).mp
      ((cancel_epi (relativeYonedaIso V C).hom).mp h')

/-- Equality of morphisms of relative point functors can be checked after
restriction to the slice over a field extension. -/
private theorem restriction_injective {G H : GroupScheme F}
    (f g : relativePoints G (fieldTest F K) ⟶ relativePoints H (fieldTest F K))
    (h : Functor.whiskerLeft (Over.map (fieldRestriction (F := F) (K := K) (S := S))).op f =
      Functor.whiskerLeft (Over.map (fieldRestriction (F := F) (K := K) (S := S))).op g) :
    f = g := by
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  let W : SchemeOver K := Over.mk U.unop.hom.left
  let X : SchemeOver F :=
    Over.mk (pullback.snd W.hom (fieldSpecMap K S) ≫ (fieldTest F S).hom)
  let s : X ⟶ fieldTest F S := Over.homMk (pullback.snd _ _) rfl
  let v : fieldTest F S ⟶ fieldTest F K := fieldRestriction
  let Y : Over (fieldTest F S) := Over.mk s
  have hv : v.left = fieldSpecMap K S := rfl
  have hq : (pullback.fst W.hom (fieldSpecMap K S)) ≫ U.unop.hom.left =
      (s ≫ v).left := (pullback.condition (f := W.hom) (g := fieldSpecMap K S)).trans
        (congrArg (pullback.snd W.hom (fieldSpecMap K S) ≫ ·) hv.symm)
  let q : X ⟶ U.unop.left := Over.homMk (pullback.fst _ _) (by
    rw [← Over.w U.unop.hom, ← Category.assoc, hq, Over.w (s ≫ v)])
  let a : (Over.map v).obj Y ⟶ U.unop := Over.homMk q (Over.OverMorphism.ext hq)
  have hxy : f.app (op ((Over.map v).obj Y)) = g.app (op ((Over.map v).obj Y)) :=
    congrArg (fun n => n.app (op Y)) h
  change U.unop.left ⟶ G.X at x
  let x' : ((relativePoints G (fieldTest F K)).obj (op ((Over.map v).obj Y))) := q ≫ x
  have hxy' := ConcreteCategory.congr_hom hxy x'
  have hf := ConcreteCategory.congr_hom (f.naturality a.op) x
  have hg := ConcreteCategory.congr_hom (g.naturality a.op) x
  change (f.app (op ((Over.map v).obj Y))).hom (q ≫ x) =
    q ≫ (f.app U).hom x at hf
  change (g.app (op ((Over.map v).obj Y))).hom (q ≫ x) =
    q ≫ (g.app U).hom x at hg
  have he : q ≫ (f.app U).hom x = q ≫ (g.app U).hom x :=
    hf.symm.trans (hxy'.trans hg)
  letI : EffectiveEpi q.left := baseChangeProjection_effectiveEpi S W
  apply Over.OverMorphism.ext
  exact (cancel_epi q.left).mp (congrArg Over.Hom.left he)

end RelativeSquares

section FaceRecognition

open Specs.Pinning (SplitBorelPair)
open Specs.AbstractPairing (Root)
open Specs.CharacterPairing (pairing)
open Specs.RankOneFlag (SameSubgroup)
open private evaluate_root from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private limitParabolic_signs_of_same from LinearAlgebraicGroups.Relative.RationalCocharacter

/-- For two dominant cocharacters of the pinned torus, equality of the
scheme-theoretic limit parabolics identifies the vanishing simple roots. -/
private theorem face_eq_of_same_parabolic (P : SplitBorelPair F) (D : AttachedDatum P)
    (c d : Cocharacter P.T.group) (C : LimitDecomposition (c ≫ P.T.inclusion))
    (E : LimitDecomposition (d ≫ P.T.inclusion)) (hCE : SameSubgroup C.parabolic E.parabolic)
    (I J : Set D.toBased.I) (hI : I ⊆ D.toBased.base.support) (hJ : J ⊆ D.toBased.base.support)
    (hc : letI := D.comm; HasFace D.base I c) (hd : letI := D.comm; HasFace D.base J d) :
    I = J := by
  letI := D.comm
  have hsign (α : Root P.T) :=
    limitParabolic_signs_of_same P.G P.T c d C E hCE α
  have hzero (α : Root P.T) :
      pairing P.T.group α.val c = 0 ↔ pairing P.T.group α.val d = 0 := by
    let β := D.datum.rootDatum.reflectionPerm α α
    have hroot : D.datum.rootDatum.root β = -D.datum.rootDatum.root α := by
      change D.datum.rootDatum.root (D.datum.rootDatum.reflectionPerm α α) = _
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    have hneg (x : Cocharacter P.T.group) :
        pairing P.T.group β.val x = -pairing P.T.group α.val x := by
      rw [← evaluate_root D.datum x β, hroot, map_neg, evaluate_root]
    have ha := hsign α
    have hb := hsign β
    rw [hneg c, hneg d, neg_nonneg, neg_nonneg] at hb
    exact ⟨fun h => le_antisymm (hb.mp h.le) (ha.mp h.ge),
      fun h => le_antisymm (hb.mpr h.le) (ha.mpr h.ge)⟩
  ext α
  constructor
  · intro h
    by_contra hn
    exact (hd.2 α ⟨hI h, hn⟩).ne' ((hzero α).mp (hc.1 α h))
  · intro h
    by_contra hn
    exact (hc.2 α ⟨hJ h, hn⟩).ne' ((hzero α).mpr (hd.1 α h))

end FaceRecognition

section ExtendedLimits

open Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (existsLimitDecomposition)
open private extendCocharacter multiplicativeBaseChange multiplicativeBaseChange_unit
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private subgroupIso_of_same limits_subgroups_extend
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private factor_of_baseChange from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

private theorem extended_limit_squares (G H : AffineAlgebraicGroup F)
    {c : Cocharacter G.val} {d : Cocharacter H.val}
    (C : LimitDecomposition c) (D : LimitDecomposition d)
    (a : (groupBaseChange F S).obj G.val ≅ (groupBaseChange F S).obj H.val)
    (ha : extendCocharacter S c ≫ a.hom = extendCocharacter S d) :
    ∃ (p : (groupBaseChange F S).obj C.parabolic.group ≅
        (groupBaseChange F S).obj D.parabolic.group)
      (l : (groupBaseChange F S).obj C.centralizer.group ≅
        (groupBaseChange F S).obj D.centralizer.group),
      (groupBaseChange F S).map C.parabolic.inclusion ≫ a.hom =
        p.hom ≫ (groupBaseChange F S).map D.parabolic.inclusion ∧
      (groupBaseChange F S).map C.centralizer.inclusion ≫ a.hom =
        l.hom ≫ (groupBaseChange F S).map D.centralizer.inclusion := by
  let m := multiplicativeBaseChange F S
  obtain ⟨C'⟩ := existsLimitDecomposition (baseChangedAlgebraicGroup S G) (extendCocharacter S c)
  obtain ⟨D'⟩ := existsLimitDecomposition (baseChangedAlgebraicGroup S H) (extendCocharacter S d)
  obtain ⟨hp₁, _, hl₁⟩ := limits_subgroups_extend G C m (multiplicativeBaseChange_unit S) C'
  obtain ⟨hp₂, _, hl₂⟩ := limits_subgroups_extend H D m (multiplicativeBaseChange_unit S) D'
  obtain ⟨p₁, hp₁⟩ := subgroupIso_of_same hp₁
  obtain ⟨p₂, hp₂⟩ := subgroupIso_of_same hp₂
  obtain ⟨l₁, hl₁⟩ := subgroupIso_of_same hl₁
  obtain ⟨l₂, hl₂⟩ := subgroupIso_of_same hl₂
  obtain ⟨p, l, hp, hl⟩ := compare_limits (baseChangedAlgebraicGroup S G)
    (baseChangedAlgebraicGroup S H) a ha C' D'
  let F' := groupBaseChange F S
  change p₁.hom ≫ F'.map C.parabolic.inclusion = C'.parabolic.inclusion at hp₁
  change p₂.hom ≫ F'.map D.parabolic.inclusion = D'.parabolic.inclusion at hp₂
  change l₁.hom ≫ F'.map C.centralizer.inclusion = C'.centralizer.inclusion at hl₁
  change l₂.hom ≫ F'.map D.centralizer.inclusion = D'.centralizer.inclusion at hl₂
  refine ⟨p₁.symm ≪≫ p ≪≫ p₂, l₁.symm ≪≫ l ≪≫ l₂, ?_, ?_⟩
  · change F'.map C.parabolic.inclusion ≫ a.hom =
      (p₁.inv ≫ p.hom ≫ p₂.hom) ≫ F'.map D.parabolic.inclusion
    have he : p₁.inv ≫ C'.parabolic.inclusion = F'.map C.parabolic.inclusion := by
      rw [← hp₁, Iso.inv_hom_id_assoc]
    calc
      _ = p₁.inv ≫ C'.parabolic.inclusion ≫ a.hom :=
        (congrArg (· ≫ a.hom) he.symm).trans (Category.assoc _ _ _)
      _ = p₁.inv ≫ p.hom ≫ D'.parabolic.inclusion := congrArg (p₁.inv ≫ ·) hp
      _ = _ := by rw [← hp₂, Category.assoc, Category.assoc]
  · change F'.map C.centralizer.inclusion ≫ a.hom =
      (l₁.inv ≫ l.hom ≫ l₂.hom) ≫ F'.map D.centralizer.inclusion
    have he : l₁.inv ≫ C'.centralizer.inclusion = F'.map C.centralizer.inclusion := by
      rw [← hl₁, Iso.inv_hom_id_assoc]
    calc
      _ = l₁.inv ≫ C'.centralizer.inclusion ≫ a.hom :=
        (congrArg (· ≫ a.hom) he.symm).trans (Category.assoc _ _ _)
      _ = l₁.inv ≫ l.hom ≫ D'.centralizer.inclusion := congrArg (l₁.inv ≫ ·) hl
      _ = _ := by rw [← hl₂, Category.assoc, Category.assoc]

private theorem inclusion_iso_of_extended {G : GroupScheme F} (B : ClosedSubgroup G)
    [IsIso ((groupBaseChange F S).map B.inclusion)] : IsIso B.inclusion := by
  letI := mono_over B.inclusion.hom.hom B.isClosedImmersion
  let a := (groupBaseChange F S).map B.inclusion
  obtain ⟨j, hj⟩ := factor_of_baseChange S (𝟙 G.X) B.inclusion.hom.hom
    (inv a).hom.hom (by
      have h := congrArg (fun f : (groupBaseChange F S).obj G ⟶
        (groupBaseChange F S).obj G => f.hom.hom) (IsIso.inv_hom_id a)
      exact h.trans ((baseChange F S).map_id G.X).symm)
  obtain ⟨i, hi⟩ := factor_group_through_subgroup B (𝟙 G) j hj
  letI := inclusion_mono B
  refine ⟨⟨i, (cancel_mono B.inclusion).mp ?_, hi⟩⟩
  rw [Category.assoc, hi, Category.comp_id, Category.id_comp]

end ExtendedLimits

section InnerComparison

open CategoryTheory.CartesianMonoidalCategory
open private relativeSectionGroupEquiv relativeSectionEquiv relativeSchemeIso
  relativeSchemeIso_natural innerAut_mul
  from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private relativeSection_precomp from LinearAlgebraicGroups.Descent.BorelInnerAlignment
open private schemeIsoEquiv schemeIsoEquiv_trans schemeIsoEquiv_ground induced_iff
  from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private conjugationIso comp_conjugate conjugate
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private extendCocharacter from LinearAlgebraicGroups.Relative.RationalCocharacter
open private extendSubgroup from LinearAlgebraicGroups.RootData.RankOneFlag
open Specs.Pinning (SplitBorelPair)

private abbrev fieldPointEquiv (S : Type u) [Field S] [Algebra F S] (G : GroupScheme F) :
    (𝟙_ (SchemeOver S) ⟶ ((groupBaseChange F S).obj G).X) ≃* (fieldTest F S ⟶ G.X) :=
  relativeSectionGroupEquiv (Over.mk (𝟙 (fieldTest F S))) G

private theorem relative_inner_eq {G : GroupScheme F}
    (g : 𝟙_ (SchemeOver S) ⟶ ((groupBaseChange F S).obj G).X) :
    schemeIsoEquiv S G G (conjugationIso g) = (innerAut (fieldPointEquiv S G g)).asIso := by
  let V := fieldTest F S
  let O : Over V := Over.mk (𝟙 V)
  let z := fieldPointEquiv S G g
  let i := schemeIsoEquiv S G G (conjugationIso g)
  have hi : relativeSchemeIso i = conjugationIso g :=
    (schemeIsoEquiv S G G).symm_apply_apply (conjugationIso g)
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  let W := U.unop
  change W.left ⟶ G.X at x
  let r : W ⟶ O := Over.homMk W.hom (Category.comp_id _)
  have hq : (Over.iteratedSliceForward V).map r =
      toUnit ((Over.iteratedSliceForward V).obj W) := toUnit_unique _ _
  have hz : relativeSectionGroupEquiv W G
      (toUnit ((Over.iteratedSliceForward V).obj W) ≫ g) = W.hom ≫ z := by
    change relativeSectionEquiv W G.X
      (toUnit ((Over.iteratedSliceForward V).obj W) ≫ g) =
      r.left ≫ relativeSectionEquiv O G.X g
    rw [← relativeSection_precomp, hq]
  let x' := (relativeSectionGroupEquiv W G).symm x
  have hxx : relativeSectionGroupEquiv W G x' = x :=
    (relativeSectionGroupEquiv W G).apply_symm_apply x
  have hx := relativeSchemeIso_natural i W x'
  rw [hi] at hx
  change (relativeSectionGroupEquiv W G) (x' ≫ (conjugationIso g).hom.hom.hom) =
    (i.hom.app U).hom (relativeSectionGroupEquiv W G x') at hx
  change (i.hom.app U).hom x =
    (W.hom ≫ z) * x * (W.hom ≫ z)⁻¹
  rw [← hxx, ← hx]
  change (relativeSectionGroupEquiv W G) (x' ≫
    conjugate g (𝟙 _)) = _
  rw [comp_conjugate, Category.comp_id]
  let t : (Over.iteratedSliceForward V).obj W ⟶ ((Over.pullback V.hom).mapGrp.obj G).X :=
    toUnit _ ≫ g
  have ht : relativeSectionGroupEquiv W G t = W.hom ≫ z := hz
  change (relativeSectionGroupEquiv W G) (t * x' * t⁻¹) = _
  rw [map_mul, map_mul, map_inv, ht]

private theorem ground_conjugation_inverse {G : GroupScheme F}
    (g : 𝟙_ (SchemeOver F) ⟶ G.X) :
    schemeIsoEquiv S G G ((groupBaseChange F S).mapIso (conjugationIso g).symm) =
      (innerAut (toUnit (fieldTest F S) ≫ g⁻¹)).asIso := by
  rw [schemeIsoEquiv_ground]
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  change U.unop.left ⟶ G.X at x
  change x ≫ conjugate g⁻¹ (𝟙 G.X) =
    (U.unop.hom ≫ toUnit (fieldTest F S) ≫ g⁻¹) * x *
      (U.unop.hom ≫ toUnit (fieldTest F S) ≫ g⁻¹)⁻¹
  rw [comp_conjugate, Category.comp_id, ← Category.assoc U.unop.hom,
    show U.unop.hom ≫ toUnit (fieldTest F S) = toUnit U.unop.left from toUnit_unique _ _]
  rfl

private theorem align_dominant_comparison [IsSepClosure F S]
    {A : AdditiveLine F} (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (G : AffineAlgebraicGroup F) (c : Cocharacter G.val)
    (a : (groupBaseChange F S).obj P.pair.G.val ≅ (groupBaseChange F S).obj G.val)
    (i : relativePoints P.pair.G.val (fieldTest F S) ≅ relativePoints G.val (fieldTest F S))
    (hi : IsInduced F S a i) :
    ∃ (a' : (groupBaseChange F S).obj P.pair.G.val ≅ (groupBaseChange F S).obj G.val)
      (g : fieldTest F S ⟶ P.pair.G.val.X)
      (d : Cocharacter P.pair.T.group) (J : Set D.toBased.I),
      extendCocharacter S (d ≫ P.pair.T.inclusion) ≫ a'.hom = extendCocharacter S c ∧
      schemeIsoEquiv S P.pair.G.val G.val a' = (innerAut g).asIso ≪≫ i ∧
      J ⊆ D.toBased.base.support ∧ (letI := D.comm; HasFace D.base J d) := by
  letI : IsSepClosed S := IsSepClosure.sep_closed F
  let F' := groupBaseChange F S
  obtain ⟨h, d₁, hh⟩ := align_cocharacter_with_torus P.pair (extendCocharacter S c ≫ a.inv)
  obtain ⟨n, d, J, hn, hJ, hd⟩ := dominant_conjugate P.pair D d₁
  let e := F'.mapIso (conjugationIso n).symm
  let a' := e ≪≫ conjugationIso h ≪≫ a
  let z := fieldPointEquiv S P.pair.G.val h
  have hz := relative_inner_eq (F := F) (S := S) h
  let y := toUnit (fieldTest F S) ≫ n⁻¹
  refine ⟨a', z * y, d, J, ?_, ?_, hJ, hd⟩
  · have hn' : (d ≫ P.pair.T.inclusion) ≫ (conjugationIso n).inv =
        d₁ ≫ P.pair.T.inclusion := by
      rw [← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hmap := congrArg F'.map hn'
    rw [F'.map_comp] at hmap
    change extendCocharacter S (d ≫ P.pair.T.inclusion) ≫ (e.hom ≫ (conjugationIso h).hom ≫ a.hom) = _
    change _ ≫ F'.map (d ≫ P.pair.T.inclusion) ≫
      F'.map (conjugationIso n).inv ≫ (conjugationIso h).hom ≫ a.hom = _
    rw [← Category.assoc (F'.map (d ≫ P.pair.T.inclusion)), hmap,
      ← Category.assoc, ← Category.assoc, hh, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [show a' = e ≪≫ conjugationIso h ≪≫ a from rfl, schemeIsoEquiv_trans,
      schemeIsoEquiv_trans, hz, (induced_iff a i).mp hi, innerAut_mul]
    have hy := ground_conjugation_inverse (S := S) n
    change schemeIsoEquiv S _ _ e = (innerAut y).asIso at hy
    rw [hy]
    exact Iso.trans_assoc _ _ _ |>.symm

end InnerComparison

section SimultaneousDescent

open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private relativeInclusion relativeSchemeIso from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private schemeIsoEquiv induced_iff
  from LinearAlgebraicGroups.Descent.RelativeFormComparison

private abbrev layerMap {L M : FiniteGaloisIntermediateField F S} (h : L ≤ M) :
    fieldTest F M ⟶ fieldTest F L :=
  (testSpec F).map (CommAlgCat.ofHom
    (IntermediateField.inclusion (show L.toIntermediateField ≤ M.toIntermediateField from h))).op

private theorem layerMap_comp {L M : FiniteGaloisIntermediateField F S} (h : L ≤ M) :
    fieldRestriction (F := F) (K := M) (S := S) ≫ layerMap h =
      fieldRestriction (F := F) (K := L) (S := S) := by
  rw [← Functor.map_comp, ← op_comp]
  congr 1

private theorem restrictIso_comp {G H : GroupScheme F} {X Y Z : SchemeOver F}
    (a : X ⟶ Y) (b : Y ⟶ Z) (i : relativePoints G Z ≅ relativePoints H Z) :
    restrictIso a (restrictIso b i) = restrictIso (a ≫ b) i := by
  apply Iso.ext
  apply NatTrans.ext
  rfl

private theorem restrict_of_layer {L M : FiniteGaloisIntermediateField F S} (h : L ≤ M)
    {G H : GroupScheme F}
    (i : relativePoints G (fieldTest F L) ≅ relativePoints H (fieldTest F L)) :
    restrictIso (fieldRestriction (F := F) (K := M) (S := S)) (restrictIso (layerMap h) i) =
      restrictIso (fieldRestriction (F := F) (K := L) (S := S)) i :=
  (restrictIso_comp _ _ _).trans (congrArg (fun v => restrictIso v i) (layerMap_comp h))

private theorem descend_inclusion_square {G H C D : GroupScheme F}
    (f : C ⟶ G) (g : D ⟶ H)
    (i : relativePoints G (fieldTest F K) ≅ relativePoints H (fieldTest F K))
    (j : relativePoints C (fieldTest F K) ≅ relativePoints D (fieldTest F K))
    (h : relativeInclusion f (fieldTest F S) ≫ (restrictIso fieldRestriction i).hom =
      (restrictIso fieldRestriction j).hom ≫ relativeInclusion g (fieldTest F S)) :
    (groupBaseChange F K).map f ≫ (relativeSchemeIso i).hom =
      (relativeSchemeIso j).hom ≫ (groupBaseChange F K).map g := by
  apply (relative_inclusion_square (fieldTest F K) f g i j).mp
  exact restriction_injective (S := S) _ _ h

/-- A comparison of the two limit subgroups and the ambient groups over the
separable closure defines both inclusion squares on one finite Galois layer. -/
private theorem descend_limit_squares [IsGalois F S] (G H : AffineAlgebraicGroup F)
    {c : Cocharacter G.val} {d : Cocharacter H.val}
    (C : LimitDecomposition c) (D : LimitDecomposition d)
    (a : (groupBaseChange F S).obj G.val ≅ (groupBaseChange F S).obj H.val)
    (p : (groupBaseChange F S).obj C.parabolic.group ≅ (groupBaseChange F S).obj D.parabolic.group)
    (l : (groupBaseChange F S).obj C.centralizer.group ≅ (groupBaseChange F S).obj D.centralizer.group)
    (hp : (groupBaseChange F S).map C.parabolic.inclusion ≫ a.hom =
      p.hom ≫ (groupBaseChange F S).map D.parabolic.inclusion)
    (hl : (groupBaseChange F S).map C.centralizer.inclusion ≫ a.hom =
      l.hom ≫ (groupBaseChange F S).map D.centralizer.inclusion)
    (K₀ : FiniteGaloisIntermediateField F S) :
    ∃ (K : FiniteGaloisIntermediateField F S)
      (aK : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val)
      (pK : (groupBaseChange F K).obj C.parabolic.group ≅
        (groupBaseChange F K).obj D.parabolic.group)
      (lK : (groupBaseChange F K).obj C.centralizer.group ≅
        (groupBaseChange F K).obj D.centralizer.group)
      (iK : relativePoints G.val (fieldTest F K) ≅ relativePoints H.val (fieldTest F K)),
      K₀ ≤ K ∧ IsInduced F K aK iK ∧
      (groupBaseChange F K).map C.parabolic.inclusion ≫ aK.hom =
        pK.hom ≫ (groupBaseChange F K).map D.parabolic.inclusion ∧
      (groupBaseChange F K).map C.centralizer.inclusion ≫ aK.hom =
        lK.hom ≫ (groupBaseChange F K).map D.centralizer.inclusion ∧
      restrictIso fieldRestriction iK = schemeIsoEquiv S G.val H.val a := by
  let V := fieldTest F S
  let aS := schemeIsoEquiv S G.val H.val a
  let pS := schemeIsoEquiv S C.parabolic.group D.parabolic.group p
  let lS := schemeIsoEquiv S C.centralizer.group D.centralizer.group l
  have haS : relativeSchemeIso aS = a := (schemeIsoEquiv S G.val H.val).symm_apply_apply a
  have hpS : relativeSchemeIso pS = p :=
    (schemeIsoEquiv S C.parabolic.group D.parabolic.group).symm_apply_apply p
  have hlS : relativeSchemeIso lS = l :=
    (schemeIsoEquiv S C.centralizer.group D.centralizer.group).symm_apply_apply l
  obtain ⟨K₁, a₁, h₁, ha₁⟩ := exists_finite_level G H aS K₀
  obtain ⟨K₂, p₂, h₂, hp₂⟩ := exists_finite_level
    (closedSubgroupAlgebraicGroup C.parabolic) (closedSubgroupAlgebraicGroup D.parabolic) pS K₁
  obtain ⟨K, lK, h₃, hlK⟩ := exists_finite_level
    (closedSubgroupAlgebraicGroup C.centralizer) (closedSubgroupAlgebraicGroup D.centralizer) lS K₂
  let iK := restrictIso (layerMap (h₂.trans h₃)) a₁
  let jK := restrictIso (layerMap h₃) p₂
  have hiK : restrictIso fieldRestriction iK = aS :=
    (restrict_of_layer (h₂.trans h₃) a₁).trans ha₁
  have hjK : restrictIso fieldRestriction jK = pS := (restrict_of_layer h₃ p₂).trans hp₂
  refine ⟨K, relativeSchemeIso iK, relativeSchemeIso jK, relativeSchemeIso lK, iK,
    h₁.trans (h₂.trans h₃), ?_, ?_, ?_, hiK⟩
  · exact (induced_iff (relativeSchemeIso iK) iK).mpr ((schemeIsoEquiv K G.val H.val).apply_symm_apply iK)
  · apply descend_inclusion_square (S := S)
    rw [hiK, hjK]
    apply (relative_inclusion_square V _ _ aS pS).mpr
    rw [haS, hpS]
    exact hp
  · apply descend_inclusion_square (S := S)
    rw [hiK, hlK]
    apply (relative_inclusion_square V _ _ aS lS).mpr
    rw [haS, hlS]
    exact hl

end SimultaneousDescent

section PinnedFace

open CategoryTheory.CartesianMonoidalCategory
open Specs.AbstractPairing (Root)
open Specs.CharacterPairing (pairing)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Pinning (SplitBorelPair IsSimple)
open Specs.BorelsAndChambers (positiveRoots subgroupRoots)
open Specs.SimpleRoots (IsBaseFor evaluate positive)
open private pinnedScalarAligned from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private precomp_pairing from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private evaluate_root face_parabolic from LinearAlgebraicGroups.Flag.StandardParabolicLevi

private theorem pinned_has_face {A : AdditiveLine F} (P : PinnedGroup A) (D : AttachedDatum P.pair)
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G} (seq : SplitSequence P D l Q)
    (b : Aut D.toBased) (d : Cocharacter P.pair.T.group) (J : Set D.toBased.I)
    (hJ : J ⊆ D.toBased.base.support) (hd : letI := D.comm; HasFace D.base J d) :
    let f := (l b).asIso.hom
    let w := b.asIso.hom.val.indexEquiv
    w '' J ⊆ D.toBased.base.support ∧
      (letI := D.comm; HasFace D.base (w '' J) (d ≫ f.torus.hom)) := by
  letI := D.comm
  let w := b.asIso.hom.val.indexEquiv
  let f := (l b).asIso.hom
  let V : SchemeOver F := 𝟙_ (SchemeOver F)
  let e := scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l b)) V
  let al := pinnedScalarAligned (l b) V
  let x : (constantGroup (k := F) (Aut D.toBased)).obj (op V) :=
    ⟨LocallyConstant.const _ b⟩
  have hout : seq.outer.app (op V) e = x := by
    change seq.outer.app (op V) (scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l b)) V) = _
    rw [← seq.sectionOnConstants V b]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app seq.rightInverse (op V)) x
  have hchar (α : Root P.pair.T) :
      f.torus.inv ≫ α.val = (w α).val := by
    let U : Over V := Over.mk (toUnit P.pair.T.group.X)
    have h := (seq.latticeAction V e al b hout).1 α.val U (𝟙 _)
    have hr := b.asIso.hom.val.toHom.root_weightMap_apply D.toBased.datum D.toBased.datum α
    change b.asIso.hom.val.weightEquiv (D.datum.rootDatum.root α) = D.datum.rootDatum.root (w α) at hr
    rw [D.datum.root_eq, D.datum.root_eq] at hr
    change (𝟙 _ ≫ f.torus.inv.hom.hom) ≫ α.val.hom.hom =
      𝟙 _ ≫ (Additive.toMul (b.asIso.hom.val.weightEquiv (Additive.ofMul α.val))).hom.hom at h
    simp only [Category.id_comp] at h
    have he := congrArg (fun χ : D.toBased.X =>
      (show CharacterDescent.Character P.pair.T.group from Additive.toMul χ).hom.hom) hr
    exact Grp.hom_ext _ _ (h.trans he)
  have hpair (α : Root P.pair.T) :
      pairing P.pair.T.group (w α).val (d ≫ f.torus.hom) =
        pairing P.pair.T.group α.val d := by
    rw [precomp_pairing, ← hchar, Iso.hom_inv_id_assoc]
  have hs : w '' (D.toBased.base.support : Set D.toBased.I) = D.toBased.base.support :=
    b.asIso.hom.property
  refine ⟨?_, ?_, ?_⟩
  · calc
      w '' J ⊆ w '' (D.toBased.base.support : Set D.toBased.I) := Set.image_mono hJ
      _ = _ := hs
  · rintro _ ⟨α, hα, rfl⟩
    exact (hpair α).trans (hd.1 α hα)
  · rintro β ⟨hβ, hnot⟩
    have hmem : β ∈ w '' (D.toBased.base.support : Set D.toBased.I) := by
      rw [hs]
      exact hβ
    obtain ⟨α, hα, rfl⟩ := hmem
    exact (hpair α).symm ▸ hd.2 α ⟨hα, fun h => hnot ⟨α, h, rfl⟩⟩

private theorem standard_contains_borel (P : SplitBorelPair F) (D : AttachedDatum P)
    (d : Cocharacter P.T.group) (J : Set D.toBased.I)
    (hd : letI := D.comm; HasFace D.base J d)
    (L : LimitDecomposition (d ≫ P.T.inclusion)) :
    IsSubgroupOf P.B L.parabolic := by
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.reduced
  obtain ⟨c, _, hr, _, hc⟩ :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT
      P.G P.reductive P.T P.split P.maximal).1 P.B P.borel P.containsTorus
  obtain ⟨b, hb⟩ := LinearAlgebraicGroups.RootData.SimpleRoots.baseFor D.datum.rootDatum
    (evaluate D.datum c) (fun i => evaluate_root D.datum c i ▸ hr i)
  have hpos : positive D.datum.rootDatum (evaluate D.datum c) = subgroupRoots P.T P.B := by
    rw [hc]
    ext i
    change 0 < evaluate D.datum c (D.datum.rootDatum.root i) ↔ 0 < pairing P.T.group i.val c
    rw [evaluate_root]
  have hs (α : Root P.T) : α ∈ b.support ↔ IsSimple P α := by
    rw [hb.simple_iff, hpos]
    unfold IsSimple
    simp only [D.datum.root_eq]
    rfl
  have hsup : b.support = D.base.support := by
    ext α
    rw [hs α, D.simple_iff]
  have he : b = D.base := by
    rcases D with ⟨a, e, b', h'⟩
    cases b
    cases b'
    cases hsup
    rfl
  rw [he] at hb
  exact (face_parabolic P.reductive P.split P.maximal P.borel P.containsTorus hc.symm hb hd L).2

end PinnedFace

section StableFace

open Specs.Pinning (SplitBorelPair)
open Specs.RankOneFlag (SameSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics
  (existsLimitDecomposition limitSubgroupsSmooth geometricallyConnectedLimitSubgroups)
open private relativeSectionEquiv relativeSection_natural relativeInclusion relativeSchemeIso
  from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private schemeIsoEquiv schemeIsoEquiv_trans schemeIsoEquiv_ground
  from LinearAlgebraicGroups.Descent.RelativeFormComparison
open private pullback_map_square extended_borel
  from LinearAlgebraicGroups.Descent.RelativeBorelAlignment
open private exists_section_lift from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private extendSubgroup extend_subgroupOf subgroupOf_of_extend
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private conjugates_of_comp_ambient from LinearAlgebraicGroups.RootData.BorelNormalizer
open private conjugationIso from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private connected_of_geometricallyConnected smooth_baseChangedGroup
  geomConnected_baseChangedGroup from LinearAlgebraicGroups.RootData.BorelsAndChambers

private theorem relative_square_restrict {C G D H : GroupScheme F} {V W : SchemeOver F}
    (v : W ⟶ V) (f : C ⟶ G) (g : D ⟶ H)
    (i : relativePoints G V ≅ relativePoints H V)
    (j : relativePoints C V ≅ relativePoints D V)
    (h : relativeInclusion f V ≫ i.hom = j.hom ≫ relativeInclusion g V) :
    relativeInclusion f W ≫ (restrictIso v i).hom =
      (restrictIso v j).hom ≫ relativeInclusion g W := by
  exact congrArg (Functor.whiskerLeft (Over.map v).op) h

private theorem transported_preserves_subgroup {C G D H : GroupScheme F}
    (f : C ⟶ G) (g : D ⟶ H)
    (i : relativePoints G (fieldTest F K) ≅ relativePoints H (fieldTest F K))
    (j : relativePoints C (fieldTest F K) ≅ relativePoints D (fieldTest F K))
    (h : relativeInclusion f (fieldTest F K) ≫ i.hom =
      j.hom ≫ relativeInclusion g (fieldTest F K))
    (τ : Gal(K/F)) :
    relativeInclusion f (fieldTest F K) ≫ (transportedAut F K i τ).asIso.hom =
      (transportedAut F K j τ).asIso.hom ≫ relativeInclusion f (fieldTest F K) := by
  let V := fieldTest F K
  have hInv : relativeInclusion g V ≫ i.inv = j.inv ≫ relativeInclusion f V := by
    apply (cancel_mono i.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, Iso.inv_hom_id_assoc]
  have hτ := relative_square_restrict (fieldMap F K τ) f g i j h
  change relativeInclusion f V ≫ (restrictIso (fieldMap F K τ) i).hom ≫ i.inv =
    ((restrictIso (fieldMap F K τ) j).hom ≫ j.inv) ≫ relativeInclusion f V
  rw [← Category.assoc, hτ, Category.assoc, hInv, Category.assoc]

/-- The fppf central projection lifts points over an algebraically closed field. -/
private theorem geometric_inner [IsAlgClosed S] {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {Q : AdjointQuotient P.pair.G} (seq : SplitSequence P D l Q)
    (f : RelativeAut P.pair.G.val (fieldTest F S)) (hf : outerHom seq f = 1) :
    ∃ g : 𝟙_ (SchemeOver S) ⟶ ((groupBaseChange F S).obj P.pair.G.val).X,
      relativeSchemeIso f.asIso = conjugationIso g := by
  obtain ⟨⟨x⟩, hx⟩ :=
    (LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.splitKernel seq f).mp hf
  let q := (groupBaseChange F S).map Q.projection
  have hs : Surjective q.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (pullback_map_square (S := fieldTest F S) Q.projection.hom.hom).flip Q.fppf.2.1
  have hX : LocallyOfFiniteType ((groupBaseChange F S).obj P.pair.G.val).X.hom :=
    (baseChangedAlgebraicGroup S P.pair.G).property.2.1
  have hY : LocallyOfFiniteType ((groupBaseChange F S).obj Q.quotient.val).X.hom :=
    (baseChangedAlgebraicGroup S Q.quotient).property.2.1
  let y := (fieldPointEquiv S Q.quotient.val).symm x
  obtain ⟨g, hg⟩ := @exists_section_lift S _ _ _ _ hX hY q.hom.hom y (hs.1 _)
  have hg' : fieldPointEquiv S P.pair.G.val g ≫ Q.projection.hom.hom = x := by
    let U : Over (fieldTest F S) := Over.mk (𝟙 _)
    change relativeSectionEquiv U _ g ≫ Q.projection.hom.hom = x
    rw [← relativeSection_natural U Q.projection.hom.hom g]
    change fieldPointEquiv S Q.quotient.val (g ≫ q.hom.hom) = x
    rw [hg]
    exact (fieldPointEquiv S Q.quotient.val).apply_symm_apply x
  refine ⟨g, (schemeIsoEquiv S _ _).injective ?_⟩
  change (schemeIsoEquiv S P.pair.G.val P.pair.G.val)
      ((schemeIsoEquiv S P.pair.G.val P.pair.G.val).symm f.asIso) = _
  rw [Equiv.apply_symm_apply, relative_inner_eq, ← hx, ← hg', seq.onLift]

/-- An automorphism preserving the standard parabolic has outer part fixing its face. -/
private theorem outer_preserves_face [IsAlgClosed S]
    {A : AdditiveLine F} (P : PinnedGroup A) (D : AttachedDatum P.pair)
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (seq : SplitSequence P D l Q)
    (d : Cocharacter P.pair.T.group) (M : LimitDecomposition (d ≫ P.pair.T.inclusion))
    (J : Set D.toBased.I) (hJ : J ⊆ D.toBased.base.support)
    (hd : letI := D.comm; HasFace D.base J d)
    (f : RelativeAut P.pair.G.val (fieldTest F S))
    (r : RelativeAut M.parabolic.group (fieldTest F S))
    (hr : relativeInclusion M.parabolic.inclusion (fieldTest F S) ≫ f.asIso.hom =
      r.asIso.hom ≫ relativeInclusion M.parabolic.inclusion (fieldTest F S)) :
    (outerHom seq f).asIso.hom.val.indexEquiv '' J = J := by
  let b := outerHom seq f
  let w := b.asIso.hom.val.indexEquiv
  let p := (l b).asIso.hom
  let d' : Cocharacter P.pair.T.group := d ≫ p.torus.hom
  obtain ⟨hJ', hd'⟩ := pinned_has_face P D seq b d J hJ hd
  obtain ⟨N⟩ := existsLimitDecomposition P.pair.G (d' ≫ P.pair.T.inclusion)
  have hcoch : (d ≫ P.pair.T.inclusion) ≫ p.group.hom = d' ≫ P.pair.T.inclusion := by
    change _ = (d ≫ p.torus.hom) ≫ _
    rw [Category.assoc, p.torus_comm, Category.assoc]
  obtain ⟨j, _, hj, _⟩ := compare_limits P.pair.G P.pair.G p.group hcoch M N
  let G := baseChangedAlgebraicGroup S P.pair.G
  let M' := extendSubgroup S M.parabolic
  let N' := extendSubgroup S N.parabolic
  let B' := extendSubgroup S P.pair.B
  let F' := groupBaseChange F S
  let a := F'.mapIso p.group
  let e := relativeSchemeIso f.asIso
  let z := relativeSchemeIso r.asIso
  let j' := F'.mapIso j
  have he : M'.inclusion ≫ e.hom = z.hom ≫ M'.inclusion :=
    (relative_inclusion_square (fieldTest F S) _ _ f.asIso r.asIso).mp hr
  have ha : M'.inclusion ≫ a.hom = j'.hom ≫ N'.inclusion := by
    change F'.map M.parabolic.inclusion ≫ F'.map p.group.hom =
      F'.map j.hom ≫ F'.map N.parabolic.inclusion
    rw [← F'.map_comp, hj, F'.map_comp]
  let s := pinnedSection (S := S) seq b
  have hs : schemeIsoEquiv S P.pair.G.val P.pair.G.val a = s.asIso := by
    rw [schemeIsoEquiv_ground]
    have h := seq.sectionOnConstants (fieldTest F S) b
    change s = scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l b)) _ at h
    rw [h]
    apply Iso.ext
    apply NatTrans.ext
    funext U
    apply GrpCat.ext
    intro x
    rfl
  let f₀ := f * s⁻¹
  have hf₀ : outerHom seq f₀ = 1 := by
    change outerHom seq (f * s⁻¹) = 1
    rw [map_mul, map_inv,
      (LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.splitCoefficientMaps seq).2.2 b]
    exact mul_inv_cancel b
  obtain ⟨g, hg⟩ := geometric_inner seq f₀ hf₀
  have hc : a ≪≫ conjugationIso g = e := by
    apply (schemeIsoEquiv S P.pair.G.val P.pair.G.val).injective
    rw [schemeIsoEquiv_trans, hs, ← hg]
    change s.asIso ≪≫ (schemeIsoEquiv S P.pair.G.val P.pair.G.val)
        ((schemeIsoEquiv S P.pair.G.val P.pair.G.val).symm f₀.asIso) =
      (schemeIsoEquiv S P.pair.G.val P.pair.G.val)
        ((schemeIsoEquiv S P.pair.G.val P.pair.G.val).symm f.asIso)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change (f * s⁻¹ * s).asIso = f.asIso
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hg' : N'.inclusion ≫ (conjugationIso g).hom =
      (j'.symm ≪≫ z).hom ≫ M'.inclusion := by
    apply (cancel_epi j'.hom).mp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc j'.hom, ← ha, Category.assoc]
    change M'.inclusion ≫ (a ≪≫ conjugationIso g).hom = _
    rw [hc, he]
  have hG : IsReductive G :=
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension
      (K := S) P.pair.G P.pair.reductive.1 P.pair.reductive.2.1).mpr P.pair.reductive
  letI : Smooth P.pair.G.val.X.hom := P.pair.reductive.1
  letI : ConnectedSpace P.pair.G.val.X.left :=
    connected_of_geometricallyConnected P.pair.reductive.2.1
  have hMs : Smooth M'.group.X.hom :=
    smooth_baseChangedGroup (limitSubgroupsSmooth P.pair.G _ M).1
  have hMc : ConnectedSpace M'.group.X.left := connected_of_geometricallyConnected
    (geomConnected_baseChangedGroup (geometricallyConnectedLimitSubgroups P.pair.G _ M).1)
  have hsame := same_standard_parabolic G hG B' M' N' (extended_borel P.pair S)
    (extend_subgroupOf (standard_contains_borel P.pair D d J hd M))
    (extend_subgroupOf (standard_contains_borel P.pair D d' (w '' J) hd' N))
    hMs hMc g (conjugates_of_comp_ambient hg'.symm)
  have hNM : SameSubgroup N.parabolic M.parabolic :=
    ⟨subgroupOf_of_extend hsame.1, subgroupOf_of_extend hsame.2⟩
  exact face_eq_of_same_parabolic P.pair D d' d N M hNM (w '' J) J hJ' hJ hd' hd

end StableFace

open Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (existsLimitDecomposition)
open private extendCocharacter from LinearAlgebraicGroups.Relative.RationalCocharacter
open private relativeInclusion relativeSchemeIso from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private schemeIsoEquiv induced_iff from LinearAlgebraicGroups.Descent.RelativeFormComparison

/-- Simultaneously align the original limit parabolic and its Levi at a finite
Galois layer, and identify the action on the resulting proper face. -/
theorem markedFace : Specs.Arithmetic.TrialitarianMarkedLevi.MarkedFace.{u} := by
  intro F S _ _ _ _ A P D l Q seq G _ a i hi c M K₀ hproper
  obtain ⟨a', g, d, J, ha', hi', hJ, hd⟩ := align_dominant_comparison P D G c a i hi
  obtain ⟨M₀⟩ := existsLimitDecomposition P.pair.G (d ≫ P.pair.T.inclusion)
  obtain ⟨p, m, hp, hm⟩ := extended_limit_squares P.pair.G G M₀ M a' ha'
  have hJproper : J ⊂ D.toBased.base.support := by
    refine lt_of_le_of_ne hJ ?_
    intro hfull
    letI : IsIso M₀.parabolic.inclusion := full_face_isIso P.pair D d M₀ (by
      intro α hα
      exact hd.1 α (hfull ▸ hα))
    let F' := groupBaseChange F S
    haveI : IsIso (F'.map M₀.parabolic.inclusion ≫ a'.hom) :=
      inferInstanceAs (IsIso (F'.map M₀.parabolic.inclusion ≫ a'.hom))
    haveI : IsIso (p.hom ≫ F'.map M.parabolic.inclusion) := hp ▸ inferInstance
    haveI : IsIso (F'.map M.parabolic.inclusion) :=
      IsIso.of_isIso_comp_left p.hom _
    exact hproper (inclusion_iso_of_extended (S := S) M.parabolic)
  obtain ⟨K, aK, pK, lK, iK, hK, hiK, hpK, hlK, hrK⟩ :=
    descend_limit_squares P.pair.G G M₀ M a' p m hp hm K₀
  refine ⟨K, d, M₀, aK, pK, lK, iK, J, hK, hiK, hpK, hlK, hJproper, hd, ?_, ?_⟩
  · intro τ
    let V := fieldTest F K
    let jK := schemeIsoEquiv K M₀.parabolic.group M.parabolic.group pK
    have h : relativeInclusion M₀.parabolic.inclusion V ≫ iK.hom =
        jK.hom ≫ relativeInclusion M.parabolic.inclusion V := by
      apply (relative_inclusion_square V _ _ iK jK).mpr
      change _ ≫ ((schemeIsoEquiv K P.pair.G.val G.val).symm iK).hom =
        ((schemeIsoEquiv K M₀.parabolic.group M.parabolic.group).symm jK).hom ≫ _
      rw [← (induced_iff aK iK).mp hiK, Equiv.symm_apply_apply]
      change _ ≫ aK.hom =
        ((schemeIsoEquiv K M₀.parabolic.group M.parabolic.group).symm
          ((schemeIsoEquiv K M₀.parabolic.group M.parabolic.group) pK)).hom ≫ _
      rw [Equiv.symm_apply_apply]
      exact hpK
    let f := transportedAut F K iK τ
    let r := transportedAut F K jK τ
    have hf := transported_preserves_subgroup M₀.parabolic.inclusion M.parabolic.inclusion
      iK jK h τ
    let Ω := AlgebraicClosure K
    let v : fieldTest F Ω ⟶ V := fieldRestriction (F := F) (K := K) (S := Ω)
    have hΩ := relative_square_restrict v M₀.parabolic.inclusion M₀.parabolic.inclusion
      f.asIso r.asIso hf
    have hs := outer_preserves_face P D seq d M₀ J hJ hd (restrictAut v f) (restrictAut v r) hΩ
    rwa [outer_restrict seq v f] at hs
  · intro σ
    apply outer_transport_of_restriction seq i iK g (hrK.trans hi') σ (σ.restrictNormal K)
    ext x
    exact (AlgEquiv.restrictNormal_commutes σ K x).symm

end

end LinearAlgebraicGroups.Arithmetic.TrialitarianMarkedLevi
