import Specs.LinearAlgebraicGroups.Representation.FlagEquivariantEulerMap
import LinearAlgebraicGroups.Representation.FlagCohomology
import LinearAlgebraicGroups.Representation.EquivariantAffineModules
import LinearAlgebraicGroups.Representation.CoherentCohomologyAlgebraBaseChange
import LinearAlgebraicGroups.Representation.EquivariantPointGlobalSections
import LinearAlgebraicGroups.Representation.FlagCovarianceLinearization
import LinearAlgebraicGroups.Representation.FormalCharacters
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.FlagEquivariantEulerMap

open _root_.LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open Specs.FlagEquivariantEulerMap
open Specs.EquivariantAffineModules
open Specs.AbstractPairing (Datum)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character)
open Specs.DatumAndWeyl (Identification)
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection AssociatedBundle affineLine linePoint)
open Specs.FlagCohomology (cohomology AffineCechComparison CechBounded)
open Specs.CharacterPairing (characterValue)
open Specs.QuotientEmbedding (Presentation)
open private flatCohomologyMap_bridge exists_associatedBundle
  from LinearAlgebraicGroups.Representation.FlagCohomology
open private affinePullback_hasFiniteAffineCover
  from LinearAlgebraicGroups.Representation.CoherentCohomologyAlgebraBaseChange

noncomputable section

set_option linter.style.haveILetI false
set_option Elab.async false

variable {k : Type u} [Field k]
variable {T : GroupScheme k} {X : SchemeOver k} {a : ModObj T.X X}

section Cohomology

/-- A finite affine cover gives a common cohomology bound for all coherent
sheaves on the proper scheme. -/
theorem coherentCohomologyBound
    (hX : IsProper X.hom) :
    ∃ N : ℕ, ∀ (F : EquivariantCoherent a) (n : ℕ), N ≤ n →
      Limits.IsZero ((cohomology X n).obj F.sheaf) := by
  obtain ⟨I, inst, U, hcover, hinter⟩ := FlagCohomology.finiteAffineCover X hX
  let : Fintype I := inst
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  refine ⟨Fintype.card I, fun F n hn => ?_⟩
  obtain ⟨presentation, _⟩ := F.coherent.exists_quasicoherentData
  obtain ⟨e, -⟩ := FlagCohomology.affineCechComparison X U hcover hinter n
  exact (FlagCohomology.cechBounded U _ n hn).of_iso (e F.sheaf presentation.isQuasicoherent)

/-- Every equivariant coherent sheaf on the flag has finite-dimensional
cohomology, with a degree bound common to all such sheaves. -/
theorem flagCoherentCohomologyFinite {G : AffineAlgebraicGroup k}
    (P : OppositeBorelPair G) (Q : Presentation P.negative)
    (a : ModObj P.torus.group.X Q.scheme) :
    (∀ (F : EquivariantCoherent a) (n : ℕ),
      Module.Finite k ((cohomology Q.scheme n).obj F.sheaf)) ∧
    ∃ N : ℕ, ∀ (F : EquivariantCoherent a) (n : ℕ), N ≤ n →
      Limits.IsZero ((cohomology Q.scheme n).obj F.sheaf) := by
  obtain ⟨_, hproper, _, V, hAdd, hModule, hFinite, _, j, hj, _⟩ :=
    (_root_.LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q
  refine ⟨fun F n => ?_, coherentCohomologyBound hproper⟩
  let : AddCommGroup V := hAdd
  let : Module k V := hModule
  let : Module.Finite k V := hFinite
  let : IsClosedImmersion j.left := hj
  let : F.sheaf.IsFinitePresentation := F.coherent
  exact _root_.LinearAlgebraicGroups.ProjectiveFiniteness.projectiveCohomologyFiniteness
    k V Q.scheme j F.sheaf n

private def actionShear {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    (H : Grp C) {X : C} (a : ModObj H.X X) : H.X ⊗ X ≅ H.X ⊗ X := by
  let := a
  let p := fst H.X X
  let q := snd H.X X
  let forward := lift p (p • q)
  let backward := lift p (p⁻¹ • q)
  have hfp : forward ≫ p = p := lift_fst _ _
  have hfq : forward ≫ q = p • q := lift_snd _ _
  have hbp : backward ≫ p = p := lift_fst _ _
  have hbq : backward ≫ q = p⁻¹ • q := lift_snd _ _
  refine ⟨forward, backward, ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · change (forward ≫ backward) ≫ p = 𝟙 _ ≫ p
      rw [Category.assoc, hbp, hfp, Category.id_comp]
    · change (forward ≫ backward) ≫ q = 𝟙 _ ≫ q
      rw [Category.assoc, hbq, ModObj.comp_smul, GrpObj.comp_inv, hfp, hfq,
        inv_smul_smul, Category.id_comp]
  · apply CartesianMonoidalCategory.hom_ext
    · change (backward ≫ forward) ≫ p = 𝟙 _ ≫ p
      rw [Category.assoc, hfp, hbp, Category.id_comp]
    · change (backward ≫ forward) ≫ q = 𝟙 _ ≫ q
      rw [Category.assoc, hfq, ModObj.comp_smul, hbp, hbq, smul_inv_smul, Category.id_comp]

private theorem actionShear_snd {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    (H : Grp C) {X : C} (a : ModObj H.X X) :
    (actionShear H a).hom ≫ snd H.X X = a.smul := by
  let := a
  change lift (fst H.X X) (fst H.X X • snd H.X X) ≫ snd H.X X = a.smul
  rw [lift_snd, Hom.smul_def, lift_fst_snd, Category.id_comp]

private theorem isFlat_projection (T : GroupScheme k) (X : SchemeOver k) :
    Flat (snd T.X X).left := by
  have h := Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (fst T.X X) (snd T.X X)) (tensorProductIsBinaryProduct T.X X)
  exact MorphismProperty.of_isPullback h (show Flat T.X.hom from inferInstance)

private theorem isFlat_action {T : GroupScheme k} {X : SchemeOver k}
    (a : ModObj T.X X) : Flat a.smul.left := by
  let e := actionShear T a
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let : Flat (snd T.X X).left := isFlat_projection T X
  have h := congrArg Over.Hom.left (actionShear_snd T a)
  rw [Over.comp_left] at h
  rw [← h]
  infer_instance

private theorem exists_inducesOnCohomology {X Y : SchemeOver k}
    (f : Y ⟶ X) [Flat f.left] {F : X.left.Modules} {H : Y.left.Modules}
    (c : Pull f F ⟶ H) (n : ℕ) :
    ∃ m, InducesOnCohomology f c n m := by
  let α := (Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv F H c
  have hw : f.left ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    rw [show Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _ from Spec.map_id _,
      Category.comp_id]
    exact Over.w f
  obtain ⟨m, hm⟩ := flatCohomologyMap_bridge (X := X) (Y := Y) (RingHom.id k) f.left hw α n
  let e := ModuleCat.restrictScalarsId'App (RingHom.id k) rfl ((cohomology Y n).obj H)
  refine ⟨m ≫ e.hom, ?_⟩
  change LinearAlgebraicGroups.Specs.FlagCohomology.IsCohomologyMap
    (RingHom.id k) f.left hw α n ((m ≫ e.hom) ≫ e.inv)
  simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using hm

/-- The action and projection induce the two maps on actual cohomology. -/
theorem cohomologyPullbacks_nonempty {T : GroupScheme k} {X : SchemeOver k}
    {a : ModObj T.X X} (F : EquivariantCoherent a) (n : ℕ) :
    Nonempty (CohomologyPullbacks F n) := by
  let : Flat (snd T.X X).left := isFlat_projection T X
  let : Flat a.smul.left := isFlat_action a
  obtain ⟨p, hp⟩ := exists_inducesOnCohomology (snd T.X X) F.lin.iso.hom n
  obtain ⟨q, hq⟩ := exists_inducesOnCohomology a.smul (𝟙 (Pull a.smul F.sheaf)) n
  exact ⟨⟨p, q, hp, hq⟩⟩

/-- The one-open affine cover gives vanishing in every positive degree. -/
theorem affineCohomology_isZero
    (affineCechComparison : AffineCechComparison.{u}) (cechBounded : CechBounded.{u, u})
    [IsAffine X.left] (F : X.left.Modules) (hF : F.IsQuasicoherent)
    (n : ℕ) (hn : 0 < n) : Limits.IsZero ((cohomology X n).obj F) := by
  let U : PUnit.{u+1} → X.left.Opens := fun _ => ⊤
  have hU : (⨆ i, U i) = ⊤ := by simp [U]
  have hi (s : Finset PUnit.{u+1}) (hs : s.Nonempty) :
      IsAffineOpen (⨅ i ∈ (s : Set PUnit.{u+1}), U i) := by
    simpa only [U, iInf_top] using isAffineOpen_top X.left
  obtain ⟨e, -⟩ := affineCechComparison X U hU hi n
  apply (cechBounded U (Specs.FlagCohomology.coefficientPresheaf F) n ?_).of_iso (e F hF)
  simpa only [Fintype.card_punit] using Nat.succ_le_of_lt hn

private theorem inducedCohomologyMap_unique {Y : SchemeOver k}
    (f : Y ⟶ X) {F : X.left.Modules} {H : Y.left.Modules} (c : Pull f F ⟶ H) (n : ℕ)
    {m m' : (cohomology X n).obj F ⟶ (cohomology Y n).obj H}
    (hm : InducesOnCohomology f c n m) (hm' : InducesOnCohomology f c n m') : m = m' := by
  unfold InducesOnCohomology at hm hm'
  exact (cancel_mono _).mp
    (FlagCohomology.inducedCohomologyMap_unique (RingHom.id k) f.left _ _ n hm hm')

private theorem cohomologyPullbacks_unique {F : EquivariantCoherent a} {n : ℕ}
    (m m' : CohomologyPullbacks F n) : m = m' := by
  have hp := inducedCohomologyMap_unique _ _ n m.projection_induced m'.projection_induced
  have ha := inducedCohomologyMap_unique _ _ n m.action_induced m'.action_induced
  cases m
  cases m'
  congr

/-- The character is determined by the cohomology of the given
linearization. -/
theorem cohomologyCharacter_unique (F : EquivariantCoherent a) (n : ℕ)
    {c c' : CharacterRing T} (hc : IsCohomologyCharacter F n c)
    (hc' : IsCohomologyCharacter F n c') : c = c' := by
  obtain ⟨_, m, h⟩ := hc
  obtain ⟨_, m', h'⟩ := hc'
  have hm := cohomologyPullbacks_unique m m'
  subst m'
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro χ
  exact (h χ).trans (h' χ).symm

theorem cohomologyCharacter_eq_zero_of_isZero (F : EquivariantCoherent a) (n : ℕ)
    {c : CharacterRing T} (hc : IsCohomologyCharacter F n c)
    (hz : IsZero ((cohomology X n).obj F.sheaf)) : c = 0 := by
  obtain ⟨_, m, h⟩ := hc
  let : Subsingleton ((cohomology X n).obj F.sheaf) := ModuleCat.isZero_iff_subsingleton.mp hz
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro χ
  rw [h, Module.finrank_zero_of_subsingleton]
  rfl

/-- Vanishing of the underlying cohomology gives the zero character, with
the two maps induced by the given linearization. -/
theorem isCohomologyCharacter_zero_of_isZero (F : EquivariantCoherent a) (n : ℕ)
    (hz : IsZero ((cohomology X n).obj F.sheaf)) :
    IsCohomologyCharacter F n 0 := by
  let : Subsingleton ((cohomology X n).obj F.sheaf) := ModuleCat.isZero_iff_subsingleton.mp hz
  obtain ⟨m⟩ := cohomologyPullbacks_nonempty F n
  refine ⟨inferInstance, m, fun χ => ?_⟩
  rw [Module.finrank_zero_of_subsingleton]
  rfl

/-- Characters in the degrees below a cohomology cutoff determine the full
virtual character. -/
theorem exists_eulerCharacter_of_bounded (F : EquivariantCoherent a) (N : ℕ)
    (hN : ∀ n ≥ N, IsZero ((cohomology X n).obj F.sheaf))
    (hch : ∀ n < N, ∃ c, IsCohomologyCharacter F n c) :
    ∃ c, IsEulerCharacter F c := by
  have h (n : ℕ) : ∃ c, IsCohomologyCharacter F n c := by
    by_cases hn : n < N
    · exact hch n hn
    · exact ⟨0, isCohomologyCharacter_zero_of_isZero F n (hN n (Nat.le_of_not_gt hn))⟩
  choose ch hch' using h
  exact ⟨_, N, ch, hch', hN, rfl⟩

/-- The virtual cohomology character is independent of the cutoff. -/
theorem eulerCharacter_unique (F : EquivariantCoherent a)
    {c c' : CharacterRing T} (hc : IsEulerCharacter F c) (hc' : IsEulerCharacter F c') :
    c = c' := by
  obtain ⟨N, ch, hch, hN, rfl⟩ := hc
  obtain ⟨N', ch', hch', hN', rfl⟩ := hc'
  have extend (d : ℕ → CharacterRing T) (hd : ∀ n, IsCohomologyCharacter F n (d n))
      {L M : ℕ} (hle : L ≤ M) (hL : ∀ n ≥ L, IsZero ((cohomology X n).obj F.sheaf)) :
      (∑ n ∈ Finset.range L, (-1 : ℤ) ^ n • d n) =
        ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n • d n := by
    apply Finset.sum_subset (Finset.range_mono hle)
    intro n _ hn
    have hn' : L ≤ n := Nat.le_of_not_gt (fun hlt => hn (Finset.mem_range.mpr hlt))
    rw [cohomologyCharacter_eq_zero_of_isZero F n (hd n) (hL n hn'), smul_zero]
  calc
    _ = ∑ n ∈ Finset.range (max N N'), (-1 : ℤ) ^ n • ch n :=
      extend ch hch (le_max_left _ _) hN
    _ = ∑ n ∈ Finset.range (max N N'), (-1 : ℤ) ^ n • ch' n := by
      apply Finset.sum_congr rfl
      intro n _
      rw [cohomologyCharacter_unique F n (hch n) (hch' n)]
    _ = _ := (extend ch' hch' (le_max_right _ _) hN').symm


/-- The covariance sheaf is finitely presented for every character by its
local identification with the associated line bundle. -/
theorem flagLineSheaf_finitePresentation {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme)
    (p : BorelProjection P) (χ : Character P.torus.group) (h : Specs.FlagCohomology.FlagKernelPair Q)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul) :
    (Specs.FlagCohomology.flagLineSheaf Q p χ h).IsFinitePresentation := by
  obtain ⟨L⟩ := exists_associatedBundle Q p χ a ha
  obtain ⟨_, hl, _⟩ := FlagCohomology.flagLineSheafIdentification Q p χ h L
  choose U hU e using hl
  have hcover : TopologicalSpace.IsOpenCover U := by
    apply top_unique
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hU y⟩
  exact ProjectiveFiniteness.isFinitePresentation_of_local_rank_one_restrict _ U hcover
    (fun y => (e y).some.symm)

end Cohomology

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a torus point at a Weyl lift differs from the
original lift by right multiplication in the opposite Borel. -/
private theorem weylBorelFactor {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    [IsCommMonObj P.torus.group.X] {D : Datum P.torus}
    (J : Identification D) (w : D.rootDatum.weylGroup)
    (n : 𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X) (hn : RepresentsWeylElement J w n)
    (p : BorelProjection P) (χ : Character P.torus.group)
    {S : SchemeOver k} (t : S ⟶ P.torus.group.X) :
    let g := toUnit S ≫ n ≫ J.normalizer.inclusion.hom.hom
    ∃ b : S ⟶ P.negative.group.X,
      (t ≫ P.torus.inclusion.hom.hom) * g = g * (b ≫ P.negative.inclusion.hom.hom) ∧
      b ≫ (p.projection ≫ χ).hom.hom = t ≫ ((J.labelEquiv w).val χ).hom.hom := by
  let g := toUnit S ≫ n ≫ J.normalizer.inclusion.hom.hom
  let e := J.image.conjugation (J.labelEquiv w)
  let t' := t ≫ e.inv.hom.hom
  let b : S ⟶ P.negative.group.X := t' ≫ p.inclusion.hom.hom
  have hunit : toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ := Subsingleton.elim _ _
  have hn' : n ≫ J.quotient.hom.hom =
      toUnit _ ≫ J.image.constantGroup.sectionPoint (J.labelEquiv w) := by
    rw [hunit, Category.id_comp]
    exact hn
  have hc := J.image.conjugates _ n (J.labelEquiv w) hn'
  have hg := congrArg (fun f => lift t' (toUnit S) ≫ f) hc
  have hright : t' ≫ (e.hom ≫ P.torus.inclusion).hom.hom = t ≫ P.torus.inclusion.hom.hom := by
    change (t ≫ e.inv.hom.hom) ≫ e.hom.hom.hom ≫ P.torus.inclusion.hom.hom =
      t ≫ P.torus.inclusion.hom.hom
    have hinv := congrArg (fun h : P.torus.group ⟶ P.torus.group => h.hom.hom) e.inv_hom_id
    change e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ at hinv
    rw [Category.assoc, reassoc_of% hinv]
  simp only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc] at hg
  change g * (t' ≫ P.torus.inclusion.hom.hom) * g⁻¹ =
    t' ≫ (e.hom ≫ P.torus.inclusion).hom.hom at hg
  rw [hright] at hg
  have ht : (t ≫ P.torus.inclusion.hom.hom) * g = g * (t' ≫ P.torus.inclusion.hom.hom) := by
    rw [← hg, inv_mul_cancel_right]
  have hb : b ≫ P.negative.inclusion.hom.hom = t' ≫ P.torus.inclusion.hom.hom := by
    exact congrArg (fun f => t' ≫ f.hom.hom) p.inclusion_comp
  refine ⟨b, ht.trans (congrArg (g * ·) hb).symm, ?_⟩
  rw [J.image.characterAction]
  have hp := congrArg (Grp.forget (SchemeOver k)).map p.section_projection
  change p.inclusion.hom.hom ≫ p.projection.hom.hom = 𝟙 _ at hp
  change (t' ≫ p.inclusion.hom.hom) ≫ p.projection.hom.hom ≫ χ.hom.hom = t' ≫ χ.hom.hom
  rw [Category.assoc, reassoc_of% hp]

set_option backward.isDefEq.respectTransparency false in
/-- Torus transport in the torsor coordinate of the line-bundle fiber at a
Weyl point, over every test algebra. -/
theorem weylFiberTransport : WeylFiberTransport.{u} := by
  intro k _ G P _ D J w n hn Q a p χ L
  constructor
  · exact ((IsPullback.of_prod_fst_with_id (n ≫ J.normalizer.inclusion.hom.hom)
      (affineLine k)).flip.paste_horiz L.trivializes.flip).flip
  intro R t z
  dsimp only
  let S := (testSpec k).obj (.op R)
  let g := toUnit S ≫ n ≫ J.normalizer.inclusion.hom.hom
  obtain ⟨b, ht, hχ⟩ := weylBorelFactor J w n hn p χ t
  have hv : characterValue (p.projection ≫ χ) R b =
      characterValue ((J.labelEquiv w).val χ) R t := by
    unfold characterValue
    dsimp only
    rw [hχ]
  change lift (t ≫ P.torus.inclusion.hom.hom) (prod.lift g (linePoint R z) ≫ L.trivialization) ≫
    L.action.smul =
      prod.lift g (linePoint R (characterValue ((J.labelEquiv w).val χ) R t * z)) ≫ L.trivialization
  rw [L.leftTranslation, ht, ← hv]
  let bg : S ⟶ G.val.X := b ≫ P.negative.inclusion.hom.hom
  have hL := L.transition R (g * bg) b⁻¹ z
  have hbb : ((b⁻¹ : GroupPoints P.negative.group R)⁻¹) = b := inv_inv b
  have hbInv : (b⁻¹ : GroupPoints P.negative.group R) ≫ P.negative.inclusion.hom.hom =
      bg⁻¹ :=
    GrpObj.inv_comp (show S ⟶ P.negative.group.X from b) P.negative.inclusion.hom.hom
  simpa only [hbb, hbInv, mul_inv_cancel_right] using hL.symm


section DegreeZero

open Specs.FlagCohomology (sectionsFunctor cohomologyZero pushforwardSectionsIso)
open private cohomologyMap_over_eq sectionsLiftOver sectionsPushforwardOverIso
  from LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false in
/-- The derived comparison in degree zero is the map of ordinary
sections of the adjoint coefficient morphism. -/
theorem inducesOnCohomology_zero {Y : SchemeOver k}
    (f : Y ⟶ X) {F : X.left.Modules} {H : Y.left.Modules} (c : Pull f F ⟶ H)
    {m : (cohomology X 0).obj F ⟶ (cohomology Y 0).obj H}
    (hm : InducesOnCohomology f c 0 m) :
    (cohomologyZero X).inv.app F ≫ m =
      (sectionsFunctor X).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv F H c) ≫
      (pushforwardSectionsIso (RingHom.id k) f.left (by simp)).hom.app H ≫
      (ModuleCat.restrictScalarsId'App (RingHom.id k) rfl _).hom ≫
      (cohomologyZero Y).inv.app H := by
  let α := (Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv F H c
  let β (M : Y.left.Modules) := (pushforwardSectionsIso (RingHom.id k) f.left (by simp)).hom.app M ≫
    (ModuleCat.restrictScalarsId'App (RingHom.id k) rfl ((sectionsFunctor Y).obj M)).hom
  let I := injectiveResolution F
  let J := injectiveResolution H
  obtain ⟨l, hl⟩ := (hm I J).1
  let g := sectionsLiftOver f l
  let ΓX := sectionsFunctor X
  let ΓY := sectionsFunctor Y
  have he := cohomologyMap_over_eq f α 0 hm I J l hl
  change m = (I.isoRightDerivedObj ΓX 0).hom ≫ HomologicalComplex.homologyMap g 0 ≫
    (J.isoRightDerivedObj ΓY 0).inv at he
  let CX := (ΓX.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let CY := (ΓY.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  have hc :
      ΓX.map α ≫ β H ≫ ΓY.map (J.ι.f 0) =
        ΓX.map (I.ι.f 0) ≫ g.f 0 := by
    have hn : β H ≫ ΓY.map (J.ι.f 0) =
        ΓX.map ((Scheme.Modules.pushforward f.left).map (J.ι.f 0)) ≫ β (J.cocomplex.X 0) := by
      apply ModuleCat.hom_ext
      ext x : 1
      rfl
    change I.ι.f 0 ≫ l.f 0 = α ≫ (Scheme.Modules.pushforward f.left).map (J.ι.f 0) at hl
    calc
      _ = ΓX.map α ≫
          (ΓX.map ((Scheme.Modules.pushforward f.left).map (J.ι.f 0)) ≫
            β (J.cocomplex.X 0)) := congrArg (ΓX.map α ≫ ·) hn
      _ = ΓX.map (α ≫ (Scheme.Modules.pushforward f.left).map (J.ι.f 0)) ≫
          β (J.cocomplex.X 0) := by rw [ΓX.map_comp, Category.assoc]
      _ = _ := by rw [← hl, ΓX.map_comp, Category.assoc]; rfl
  change ΓX.toRightDerivedZero.app F ≫ m = (ΓX.map α ≫ β H) ≫ ΓY.toRightDerivedZero.app H
  apply (cancel_mono ((J.isoRightDerivedObj ΓY 0).hom ≫
    (CochainComplex.isoHomologyπ₀ CY).inv ≫ HomologicalComplex.iCycles CY 0)).mp
  rw [he, I.toRightDerivedZero_eq ΓX, J.toRightDerivedZero_eq ΓY]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change I.toRightDerivedZero' ΓX ≫ (CochainComplex.isoHomologyπ₀ CX).hom ≫
      HomologicalComplex.homologyMap g 0 ≫ (CochainComplex.isoHomologyπ₀ CY).inv ≫ CY.iCycles 0 =
    ΓX.map α ≫ β H ≫ J.toRightDerivedZero' ΓY ≫
      (CochainComplex.isoHomologyπ₀ CY).hom ≫ (CochainComplex.isoHomologyπ₀ CY).inv ≫ CY.iCycles 0
  have hπ : HomologicalComplex.homologyMap g 0 ≫ (CochainComplex.isoHomologyπ₀ CY).inv =
      (CochainComplex.isoHomologyπ₀ CX).inv ≫ HomologicalComplex.cyclesMap g 0 :=
    CochainComplex.isoHomologyπ₀_inv_naturality g
  have hi : HomologicalComplex.cyclesMap g 0 ≫ CY.iCycles 0 = CX.iCycles 0 ≫ g.f 0 :=
    HomologicalComplex.cyclesMap_i g 0
  rw [reassoc_of% hπ, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, hi,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  exact hc.symm

end DegreeZero

section CohomologyNaturality

open Specs.FlagCohomology (sectionsFunctor IsCohomologyMap)
open private cohomologyMap_over_eq sectionsLiftOver
  from LinearAlgebraicGroups.Representation.FlagCohomology

set_option backward.isDefEq.respectTransparency false in
/-- A commutative square of coefficient maps induces a commutative square
on cohomology over the given flat map of schemes. -/
private theorem cohomologyMap_naturality {Y : SchemeOver k} (p : Y ⟶ X) [Flat p.left]
    {F F' : X.left.Modules} {H H' : Y.left.Modules}
    (f : F ⟶ F') (g : H ⟶ H')
    (α : F ⟶ (Scheme.Modules.pushforward p.left).obj H)
    (α' : F' ⟶ (Scheme.Modules.pushforward p.left).obj H')
    (w : f ≫ α' = α ≫ (Scheme.Modules.pushforward p.left).map g)
    (n : ℕ)
    {m : (cohomology X n).obj F ⟶ (cohomology Y n).obj H}
    {m' : (cohomology X n).obj F' ⟶ (cohomology Y n).obj H'}
    (hm : IsCohomologyMap (RingHom.id k) p.left (by simp) α n
      (m ≫ (ModuleCat.restrictScalarsId'App (RingHom.id k) rfl _).inv))
    (hm' : IsCohomologyMap (RingHom.id k) p.left (by simp) α' n
      (m' ≫ (ModuleCat.restrictScalarsId'App (RingHom.id k) rfl _).inv)) :
    (cohomology X n).map f ≫ m' = m ≫ (cohomology Y n).map g := by
  let P := Scheme.Modules.pushforward p.left
  let I := injectiveResolution F
  let I' := injectiveResolution F'
  let J := injectiveResolution H
  let J' := injectiveResolution H'
  let r := InjectiveResolution.desc f I' I
  let s := InjectiveResolution.desc g J' J
  obtain ⟨⟨l, hl⟩, _⟩ := hm I J
  obtain ⟨⟨l', hl'⟩, _⟩ := hm' I' J'
  let t₁ := r ≫ l'
  let t₂ := l ≫ (P.mapHomologicalComplex (.up ℕ)).map s
  change I.ι.f 0 ≫ l.f 0 = α ≫ P.map (J.ι.f 0) at hl
  change I'.ι.f 0 ≫ l'.f 0 = α' ≫ P.map (J'.ι.f 0) at hl'
  have ht₁ : I.ι.f 0 ≫ t₁.f 0 = (f ≫ α') ≫ P.map (J'.ι.f 0) := by
    change I.ι.f 0 ≫ r.f 0 ≫ l'.f 0 = _
    rw [← Category.assoc, InjectiveResolution.desc_commutes_zero, Category.assoc, hl', Category.assoc]
  have ht₂ : I.ι.f 0 ≫ t₂.f 0 = (f ≫ α') ≫ P.map (J'.ι.f 0) := by
    change I.ι.f 0 ≫ l.f 0 ≫ P.map (s.f 0) = _
    rw [← Category.assoc, hl, Category.assoc, ← P.map_comp, InjectiveResolution.desc_commutes_zero,
      P.map_comp, ← Category.assoc, ← w]
  obtain ⟨q, hq⟩ := flatCohomologyMap_bridge (X := X) (Y := Y)
    (RingHom.id k) p.left (by simp) (f ≫ α') n
  let e := ModuleCat.restrictScalarsId'App (RingHom.id k) rfl ((cohomology Y n).obj H')
  let q' := q ≫ e.hom
  have hq' : IsCohomologyMap (RingHom.id k) p.left (by simp) (f ≫ α') n (q' ≫ e.inv) := by
    simpa only [q', Category.assoc, Iso.hom_inv_id, Category.comp_id] using hq
  have he₁ := cohomologyMap_over_eq p (f ≫ α') n hq' I J' t₁ ht₁
  have he₂ := cohomologyMap_over_eq p (f ≫ α') n hq' I J' t₂ ht₂
  have h₁ := cohomologyMap_over_eq p α n hm I J l hl
  have h₂ := cohomologyMap_over_eq p α' n hm' I' J' l' hl'
  let ΓX := sectionsFunctor X
  let ΓY := sectionsFunctor Y
  let RX := ΓX.mapHomologicalComplex (.up ℕ)
  let RY := ΓY.mapHomologicalComplex (.up ℕ)
  have hr : (cohomology X n).map f ≫ (I'.isoRightDerivedObj ΓX n).hom =
      (I.isoRightDerivedObj ΓX n).hom ≫ HomologicalComplex.homologyMap (RX.map r) n :=
    InjectiveResolution.isoRightDerivedObj_hom_naturality _ _ _ _
      (InjectiveResolution.desc_commutes_zero f I' I) ΓX n
  have hs :
      (J.isoRightDerivedObj ΓY n).inv ≫ (cohomology Y n).map g =
        HomologicalComplex.homologyMap (RY.map s) n ≫
          (J'.isoRightDerivedObj ΓY n).inv := by
    have h := InjectiveResolution.isoRightDerivedObj_hom_naturality _ _ _ _
      (InjectiveResolution.desc_commutes_zero g J' J) ΓY n
    change (cohomology Y n).map g ≫ (J'.isoRightDerivedObj ΓY n).hom =
      (J.isoRightDerivedObj ΓY n).hom ≫ HomologicalComplex.homologyMap (RY.map s) n at h
    apply (cancel_mono (J'.isoRightDerivedObj ΓY n).hom).mp
    rw [Category.assoc, h, Iso.inv_hom_id_assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hleft : sectionsLiftOver p t₁ = RX.map r ≫ sectionsLiftOver p l' := by
    unfold sectionsLiftOver
    change RX.map (r ≫ l') ≫ _ = RX.map r ≫ RX.map l' ≫ _
    rw [RX.map_comp, Category.assoc]
  have hright : sectionsLiftOver p t₂ = sectionsLiftOver p l ≫ RY.map s := by
    ext i : 1
    apply ModuleCat.hom_ext
    ext x : 1
    rfl
  calc
    (cohomology X n).map f ≫ m' = q' := by
      rw [h₂, reassoc_of% hr, he₁, hleft, HomologicalComplex.homologyMap_comp]
      simp only [Category.assoc, ΓX]
    _ = m ≫ (cohomology Y n).map g := by
      rw [h₁, he₂, hright, HomologicalComplex.homologyMap_comp]
      dsimp only [ΓY] at hs
      simp only [Category.assoc, hs]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of a derived pullback with respect to the coefficient map. -/
theorem inducesOnCohomology_naturality {Y : SchemeOver k} (p : Y ⟶ X) [Flat p.left]
    {F F' : X.left.Modules} {H H' : Y.left.Modules}
    (f : F ⟶ F') (g : H ⟶ H') (c : Pull p F ⟶ H) (c' : Pull p F' ⟶ H')
    (w : (Scheme.Modules.pullback p.left).map f ≫ c' = c ≫ g)
    (n : ℕ)
    {m : (cohomology X n).obj F ⟶ (cohomology Y n).obj H}
    {m' : (cohomology X n).obj F' ⟶ (cohomology Y n).obj H'}
    (hm : InducesOnCohomology p c n m) (hm' : InducesOnCohomology p c' n m') :
    (cohomology X n).map f ≫ m' = m ≫ (cohomology Y n).map g := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction p.left
  apply cohomologyMap_naturality p f g _ _ _ n hm hm'
  rw [← A.homEquiv_naturality_left, ← A.homEquiv_naturality_right]
  exact congrArg (A.homEquiv _ _) w

end CohomologyNaturality

section UniversalWeights

open EquivariantAffineModules (multiply_natural multiply_comp isUnit_characterFunction
  characterFunction_mul multiplyUnit)

variable {F H : EquivariantCoherent a} {n : ℕ}

private abbrev onWeights (F : EquivariantCoherent a) (n : ℕ) (χ : Character T) :=
  (cohomology (T.X ⊗ X) n).map (multiply (Pull a.smul F.sheaf)
    ((fst T.X X).left.appTop (characterFunction χ)))

private theorem mem_cohomologyWeightSpace (m : CohomologyPullbacks F n) (χ : Character T)
    (v : (cohomology X n).obj F.sheaf) :
    v ∈ cohomologyWeightSpace m χ ↔ m.viaProjection v = onWeights F n χ (m.viaAction v) := by
  simp only [cohomologyWeightSpace, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.comp_apply, sub_eq_zero]

private theorem actionMap_naturality (m : CohomologyPullbacks F n) (m' : CohomologyPullbacks H n)
    (f : F.sheaf ⟶ H.sheaf) :
    (cohomology X n).map f ≫ m'.viaAction = m.viaAction ≫
      (cohomology (T.X ⊗ X) n).map ((Scheme.Modules.pullback a.smul.left).map f) := by
  let : Flat a.smul.left := isFlat_action a
  apply inducesOnCohomology_naturality a.smul f _ _ _ (by simp) n
    m.action_induced m'.action_induced

private theorem onWeights_naturality (f : Pull a.smul F.sheaf ⟶ Pull a.smul H.sheaf)
    (χ : Character T) :
    onWeights F n χ ≫ (cohomology (T.X ⊗ X) n).map f =
      (cohomology (T.X ⊗ X) n).map f ≫ onWeights H n χ := by
  exact ((cohomology (T.X ⊗ X) n).map_comp _ _).symm.trans
    (congrArg ((cohomology (T.X ⊗ X) n).map) (multiply_natural f _)) |>.trans
    ((cohomology (T.X ⊗ X) n).map_comp _ _)

/-- The ordinary maps in the cohomology long exact sequence preserve the
universal torus weight spaces. -/
theorem equivariantHom_preserves_cohomologyWeights
    (m : CohomologyPullbacks F n) (m' : CohomologyPullbacks H n)
    (f : F.sheaf ⟶ H.sheaf) (hf : EquivariantHom f) (χ : Character T)
    {v : (cohomology X n).obj F.sheaf} (hv : v ∈ cohomologyWeightSpace m χ) :
    (cohomology X n).map f v ∈ cohomologyWeightSpace m' χ := by
  let : Flat (snd T.X X).left := isFlat_projection T X
  let f' := (Scheme.Modules.pullback a.smul.left).map f
  have hp := inducesOnCohomology_naturality (snd T.X X) f f' _ _ hf.symm n
    m.projection_induced m'.projection_induced
  have hact := actionMap_naturality m m' f
  rw [mem_cohomologyWeightSpace] at hv ⊢
  calc
    _ = (cohomology (T.X ⊗ X) n).map f' (m.viaProjection v) :=
      ConcreteCategory.congr_hom hp v
    _ = (cohomology (T.X ⊗ X) n).map f' (onWeights F n χ (m.viaAction v)) :=
      congrArg ((cohomology (T.X ⊗ X) n).map f') hv
    _ = _ := by
      have hw := ConcreteCategory.congr_hom (onWeights_naturality (n := n) f' χ) (m.viaAction v)
      change (cohomology (T.X ⊗ X) n).map f' (onWeights F n χ (m.viaAction v)) =
        onWeights H n χ ((cohomology (T.X ⊗ X) n).map f' (m.viaAction v)) at hw
      rw [hw]
      exact congrArg (onWeights H n χ) (ConcreteCategory.congr_hom hact v).symm

private theorem onWeights_mul (split : IsSplitTorus T) (χ ψ : Character T) :
    onWeights F n ψ ≫ onWeights F n χ = onWeights F n (χ * ψ) := by
  unfold onWeights
  rw [← (cohomology (T.X ⊗ X) n).map_comp, multiply_comp,
    characterFunction_mul split, map_mul]

private theorem onWeights_injective (χ : Character T) :
    Function.Injective (onWeights F n χ) := by
  let r := (fst T.X X).left.appTop (characterFunction χ)
  have hr : IsUnit r := (isUnit_characterFunction χ).map ((fst T.X X).left.appTop.hom)
  let e := multiplyUnit (Pull a.smul F.sheaf) hr.unit
  have he : e.hom = multiply (Pull a.smul F.sheaf) r :=
    congrArg (multiply (Pull a.smul F.sheaf)) hr.unit_spec
  have h : onWeights F n χ = ((cohomology (T.X ⊗ X) n).mapIso e).hom :=
    congrArg ((cohomology (T.X ⊗ X) n).map) he.symm
  rw [h]
  exact (ConcreteCategory.bijective_of_isIso _).1

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring by a character shifts the universal weights by multiplication
by that character. -/
theorem cohomologyWeights_twist (split : IsSplitTorus T) (χ ψ : Character T)
    (m : CohomologyPullbacks F n) (m' : CohomologyPullbacks H n)
    (h : IsTwist χ F H) :
    Nonempty (cohomologyWeightSpace m ψ ≃ₗ[k] cohomologyWeightSpace m' (χ * ψ)) := by
  obtain ⟨e, he⟩ := h
  let : Flat (snd T.X X).left := isFlat_projection T X
  let P := Scheme.Modules.pullback (snd T.X X).left
  let Q := Scheme.Modules.pullback a.smul.left
  let C := cohomology (T.X ⊗ X) n
  let r := (fst T.X X).left.appTop (characterFunction χ)
  let M := multiply (Pull a.smul F.sheaf) r
  let t := C.map (Q.map e.hom)
  let E := (cohomology X n).mapIso e
  have hproj : E.hom ≫ m'.viaProjection = m.viaProjection ≫ onWeights F n χ ≫ t := by
    rw [← C.map_comp]
    apply inducesOnCohomology_naturality (snd T.X X) e.hom (M ≫ Q.map e.hom) _ _ _ n
      m.projection_induced m'.projection_induced
    rw [he, ← P.map_comp_assoc, e.hom_inv_id, P.map_id, Category.id_comp]
  have hact := actionMap_naturality m m' e.hom
  have hcomm := onWeights_naturality (n := n) (Q.map e.hom) (χ * ψ)
  have hmul := onWeights_mul (F := F) (n := n) split χ ψ
  have ht : Function.Injective t :=
    (ConcreteCategory.bijective_of_isIso ((C.mapIso (Q.mapIso e)).hom)).1
  have hiff (v : (cohomology X n).obj F.sheaf) :
      E.hom v ∈ cohomologyWeightSpace m' (χ * ψ) ↔ v ∈ cohomologyWeightSpace m ψ := by
    rw [mem_cohomologyWeightSpace, mem_cohomologyWeightSpace]
    have hpv := ConcreteCategory.congr_hom hproj v
    have hav := ConcreteCategory.congr_hom hact v
    change m'.viaProjection (E.hom v) = t (onWeights F n χ (m.viaProjection v)) at hpv
    change m'.viaAction (E.hom v) = t (m.viaAction v) at hav
    rw [hpv, hav]
    have hcv := ConcreteCategory.congr_hom hcomm (m.viaAction v)
    change t (onWeights F n (χ * ψ) (m.viaAction v)) =
      onWeights H n (χ * ψ) (t (m.viaAction v)) at hcv
    rw [← hcv, ht.eq_iff]
    rw [← ConcreteCategory.congr_hom hmul (m.viaAction v)]
    exact (onWeights_injective (F := F) (n := n) χ).eq_iff
  let E' := E.toLinearEquiv
  refine ⟨E'.ofSubmodules _ _ ?_⟩
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (hiff u).mpr hu
  · intro hv
    have hmem : E' (E'.symm v) ∈ cohomologyWeightSpace m' (χ * ψ) :=
      (E'.apply_symm_apply v).symm ▸ hv
    exact ⟨E'.symm v, (hiff (E'.symm v)).mp hmem, E'.apply_symm_apply v⟩


/-- Twisting multiplies the actual cohomology character by the twisting
character in the integral character ring. -/
theorem isCohomologyCharacter_twist (split : IsSplitTorus T) (χ : Character T)
    (h : IsTwist χ F H) {c : CharacterRing T} (hc : IsCohomologyCharacter F n c) :
    IsCohomologyCharacter H n (eChar χ * c) := by
  let e := h.choose
  obtain ⟨hFin, m, hm⟩ := hc
  let E := (cohomology X n).mapIso e
  let : Module.Finite k ((cohomology X n).obj F.sheaf) := hFin
  obtain ⟨m'⟩ := cohomologyPullbacks_nonempty H n
  refine ⟨Module.Finite.of_surjective E.hom.hom E.toLinearEquiv.surjective, m', fun ψ => ?_⟩
  change (MonoidAlgebra.single χ 1 * c).coeff ψ = _
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul, hm]
  obtain ⟨e'⟩ := cohomologyWeights_twist split χ (χ⁻¹ * ψ) m m' h
  have he' := e'.finrank_eq
  rw [mul_inv_cancel_left] at he'
  exact_mod_cast he'

/-- Twisting by a character multiplies the finite signed cohomology
character by that character. -/
theorem isEulerCharacter_twist (split : IsSplitTorus T) (χ : Character T)
    (h : IsTwist χ F H) {c : CharacterRing T} (hc : IsEulerCharacter F c) :
    IsEulerCharacter H (eChar χ • c) := by
  let e := h.choose
  obtain ⟨N, ch, hch, hN, rfl⟩ := hc
  refine ⟨N, fun i => eChar χ * ch i, fun i => isCohomologyCharacter_twist split χ h (hch i),
    fun i hi => (hN i hi).of_iso ((cohomology X i).mapIso e).symm, ?_⟩
  rw [smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_smul_comm ((-1 : ℤ) ^ i) (eChar χ) (ch i)

end UniversalWeights

section GlobalSectionWeights

open Specs.FlagCohomology (cohomologyZero sectionsFunctor)

set_option backward.isDefEq.respectTransparency false in
private theorem induced_zero_apply {Y : SchemeOver k} (f : Y ⟶ X)
    {F : X.left.Modules} {H : Y.left.Modules} (c : Pull f F ⟶ H)
    {m : (cohomology X 0).obj F ⟶ (cohomology Y 0).obj H}
    (hm : InducesOnCohomology f c 0 m) (v : (cohomology X 0).obj F) :
    ((cohomologyZero Y).hom.app H) (m v) =
      c.app ⊤ (pullSection f.left F (((cohomologyZero X).hom.app F) v)) := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f.left
  let α := A.homEquiv F H c
  let e := (cohomologyZero X).app F
  let e' := (cohomologyZero Y).app H
  let s := e.hom v
  have hc := ConcreteCategory.congr_hom (inducesOnCohomology_zero f c hm) s
  change m (e.inv s) = e'.inv (α.app ⊤ s) at hc
  have hs : e.inv s = v := ConcreteCategory.congr_hom e.hom_inv_id v
  have hs' : e'.hom (e'.inv (α.app ⊤ s)) = α.app ⊤ s :=
    ConcreteCategory.congr_hom e'.inv_hom_id (α.app ⊤ s)
  have hα : α.app ⊤ s = c.app ⊤ (pullSection f.left F s) := by
    dsimp only [α]
    rw [Adjunction.homEquiv_unit]
    rfl
  change e'.hom (m v) = c.app ⊤ (pullSection f.left F s)
  calc
    _ = e'.hom (m (e.inv s)) := congrArg (fun v => e'.hom (m v)) hs.symm
    _ = e'.hom (e'.inv (α.app ⊤ s)) := congrArg (fun v => e'.hom v) hc
    _ = α.app ⊤ s := hs'
    _ = _ := hα

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero universal weights are the weights of the actual global
sections of the linearized sheaf. -/
theorem cohomologyWeights_zero {F : EquivariantCoherent a}
    (m : CohomologyPullbacks F 0) (χ : Character T) (v : (cohomology X 0).obj F.sheaf) :
    v ∈ cohomologyWeightSpace m χ ↔
      HasSectionWeight F.lin (((cohomologyZero X).hom.app F.sheaf) v) χ := by
  rw [mem_cohomologyWeightSpace]
  let Y := T.X ⊗ X
  let H := Pull a.smul F.sheaf
  let e := (cohomologyZero Y).app H
  let r := (fst T.X X).left.appTop (characterFunction χ)
  let M := multiply H r
  let s := ((cohomologyZero X).hom.app F.sheaf) v
  have hp := induced_zero_apply (snd T.X X) F.lin.iso.hom m.projection_induced v
  have ha := induced_zero_apply a.smul (𝟙 H) m.action_induced v
  change e.hom (m.viaProjection v) = F.lin.iso.hom.app ⊤ (pullSection (snd T.X X).left F.sheaf s) at hp
  change e.hom (m.viaAction v) = pullSection a.smul.left F.sheaf s at ha
  change _ ↔ F.lin.iso.hom.app ⊤ (pullSection (snd T.X X).left F.sheaf s) =
    r • pullSection a.smul.left F.sheaf s
  rw [← EquivariantAffineModules.multiply_app_top H r]
  have hscalar := ConcreteCategory.congr_hom ((cohomologyZero Y).hom.naturality M) (m.viaAction v)
  change e.hom (onWeights F 0 χ (m.viaAction v)) = M.app ⊤ (e.hom (m.viaAction v)) at hscalar
  constructor
  · intro h
    have he := congrArg (fun v => e.hom v) h
    rw [hp, hscalar, ha] at he
    exact he
  · intro h
    apply e.toLinearEquiv.injective
    change e.hom (m.viaProjection v) = e.hom (onWeights F 0 χ (m.viaAction v))
    rw [hp, hscalar, ha]
    exact h

end GlobalSectionWeights

section AffineOpenExactness

open AlgebraicGeometry.Scheme.Modules
open EquivariantAffineModules (affineSectionsExact)

set_option backward.isDefEq.respectTransparency false in
/-- For a quasi-coherent short exact sequence, evaluation on an affine
open gives an exact sequence of modules. -/
theorem affineOpenSections_exact {Z : Scheme.{u}} (U : Z.Opens) (hU : IsAffineOpen U)
    (S : ShortComplex Z.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hS : S.ShortExact) :
    Function.Injective (S.f.app U) ∧ Function.Exact (S.f.app U) (S.g.app U) ∧
      Function.Surjective (S.g.app U) := by
  let i := hU.fromSpec
  let R := restrictFunctor i
  let e := restrictFunctorIsoPullback i
  let : (Scheme.Modules.pullback i).PreservesHomology := FlatCohomology.flatPullbackExact i
  let : PreservesFiniteLimits (Scheme.Modules.pullback i) :=
    Functor.preservesFiniteLimits_of_preservesHomology (Scheme.Modules.pullback i)
  let K := S.map R
  have hK : K.ShortExact := ShortComplex.shortExact_of_iso
    (S.mapNatIso e.symm) (hS.map_of_exact (Scheme.Modules.pullback i))
  let : K.X₁.IsQuasicoherent := isQuasicoherent_restrictFunctor i S.X₁
  let : K.X₂.IsQuasicoherent := isQuasicoherent_restrictFunctor i S.X₂
  let : K.X₃.IsQuasicoherent := isQuasicoherent_restrictFunctor i S.X₃
  have he := affineSectionsExact K hK
  have htop : i ''ᵁ (⊤ : (Spec Γ(Z, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let P (W : Z.Opens) := Function.Injective (S.f.app W) ∧
    Function.Exact (S.f.app W) (S.g.app W) ∧ Function.Surjective (S.g.app W)
  exact (congrArg P htop).mp (show P (i ''ᵁ ⊤) from he)

end AffineOpenExactness

section CohomologyExactSequence

open Specs.FlagCohomology (coefficientPresheaf coefficientPresheafMap tupleOpen cechMap)
open private cechFunctor shortExact_cechFunctor from LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness
open private tupleOpen_isAffine_of_finite_intersections
  from LinearAlgebraicGroups.Representation.FlagCohomology

private theorem exact_of_moduleIso {A B C A' B' C' : ModuleCat.{u} k}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (eA : A ≅ A') (eB : B ≅ B') (eC : C ≅ C')
    (hf : f ≫ eB.hom = eA.hom ≫ f') (hg : g ≫ eC.hom = eB.hom ≫ g')
    (h : Function.Exact f' g') : Function.Exact f g := by
  intro y
  have e (x : A) : eB.hom (f x) = f' (eA.hom x) := ConcreteCategory.congr_hom hf x
  have e' : eC.hom (g y) = g' (eB.hom y) := ConcreteCategory.congr_hom hg y
  constructor
  · intro hy
    obtain ⟨x', hx'⟩ := (h (eB.hom y)).mp (by rw [← e', hy, map_zero])
    let x := eA.inv x'
    have hxx' : eA.hom x = x' := ConcreteCategory.congr_hom eA.inv_hom_id x'
    exact ⟨x, eB.toLinearEquiv.injective ((e x).trans (hxx' ▸ hx'))⟩
  · rintro ⟨x, rfl⟩
    apply eC.toLinearEquiv.injective
    change eC.hom (g (f x)) = eC.hom 0
    rw [e', e, (h (f' (eA.hom x))).mpr ⟨_, rfl⟩, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The Čech connecting maps for quasi-coherent coefficients give the
long exact sequence of the actual derived global-section functors. -/
theorem coherentCohomology_longExact
    (hX : Specs.FlagCohomology.HasFiniteAffineCover X)
    (S : ShortComplex X.left.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] (hS : S.ShortExact) :
    ∃ δ : ∀ n, (cohomology X n).obj S.X₃ ⟶ (cohomology X (n + 1)).obj S.X₁,
      Function.Injective ((cohomology X 0).map S.f) ∧
      (∀ n, Function.Exact ((cohomology X n).map S.f) ((cohomology X n).map S.g)) ∧
      (∀ n, Function.Exact ((cohomology X n).map S.g) (δ n)) ∧
      (∀ n, Function.Exact (δ n) ((cohomology X (n + 1)).map S.f)) := by
  classical
  obtain ⟨I, hI, U, hcover, hinter⟩ := hX
  let : Fintype I := hI
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  let f := coefficientPresheafMap (X := X) S.f
  let g := coefficientPresheafMap (X := X) S.g
  have w : f ≫ g = 0 := by
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    ext x : 1
    change S.g.app V.unop (S.f.app V.unop x) = 0
    have hz := congrArg (fun t : S.X₁ ⟶ S.X₃ => t.app V.unop) S.zero
    exact ConcreteCategory.congr_hom hz x
  let D := ShortComplex.mk f g w
  have hD (n : ℕ) (e : Fin (n + 1) ↪o I) :
      (D.map ((CategoryTheory.evaluation _ _).obj (op (tupleOpen U e)))).ShortExact := by
    let A := D.map ((CategoryTheory.evaluation _ _).obj (op (tupleOpen U e)))
    obtain ⟨hi, he, hs⟩ := affineOpenSections_exact _ (tupleOpen_isAffine_of_finite_intersections U hinter e)
      S hS
    exact ShortComplex.ShortExact.mk' ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact A).mpr he)
      ((ModuleCat.mono_iff_injective A.f).mpr hi) ((ModuleCat.epi_iff_surjective A.g).mpr hs)
  let K := D.map (cechFunctor U)
  have hK : K.ShortExact := shortExact_cechFunctor U D hD
  choose E hE using FlagCohomology.affineCechComparison X U hcover hinter
  let e₁ n := E n S.X₁ inferInstance
  let e₂ n := E n S.X₂ inferInstance
  let e₃ n := E n S.X₃ inferInstance
  let d n := hK.δ n (n + 1) rfl
  let δ n := (e₃ n).hom ≫ d n ≫ (e₁ (n + 1)).inv
  have hf (n : ℕ) : (cohomology X n).map S.f ≫ (e₂ n).hom =
      (e₁ n).hom ≫ HomologicalComplex.homologyMap K.f n := hE n _ _ S.f
  have hg (n : ℕ) : (cohomology X n).map S.g ≫ (e₃ n).hom =
      (e₂ n).hom ≫ HomologicalComplex.homologyMap K.g n := hE n _ _ S.g
  have hd (n : ℕ) : δ n ≫ (e₁ (n + 1)).hom = (e₃ n).hom ≫ d n := by
    change ((e₃ n).hom ≫ d n ≫ (e₁ (n + 1)).inv) ≫ (e₁ (n + 1)).hom = _
    simp only [Category.assoc]
    have hiv : (e₁ (n + 1)).inv ≫ (e₁ (n + 1)).hom = 𝟙 (K.X₁.homology (n + 1)) :=
      (e₁ (n + 1)).inv_hom_id
    exact congrArg ((e₃ n).hom ≫ ·) <| calc
      (d n ≫ (e₁ (n + 1)).inv) ≫ (e₁ (n + 1)).hom =
          d n ≫ ((e₁ (n + 1)).inv ≫ (e₁ (n + 1)).hom) := Category.assoc _ _ _
      _ = d n := (congrArg (d n ≫ ·) hiv).trans (Category.comp_id _)
  refine ⟨δ, ?_, ?_, ?_, ?_⟩
  · let : Mono K.f := hK.mono_f
    let : Mono (K.f.f 0) := inferInstanceAs (Mono ((HomologicalComplex.eval _ _ 0).map K.f))
    have : Mono (HomologicalComplex.homologyMap K.f 0) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel K.f 0 (by simp)
    have hmono : Mono ((cohomology X 0).map S.f ≫ (e₂ 0).hom) := by
      rw [hf]
      infer_instance
    have : Mono ((cohomology X 0).map S.f) := mono_of_mono _ (e₂ 0).hom
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  · intro n
    exact exact_of_moduleIso _ _ _ _ (e₁ n) (e₂ n) (e₃ n) (hf n) (hg n)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hK.homology_exact₂ n))
  · intro n
    exact exact_of_moduleIso _ _ _ _ (e₂ n) (e₃ n) (e₁ (n + 1)) (hg n) (hd n)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hK.homology_exact₃ n (n + 1) rfl))
  · intro n
    exact exact_of_moduleIso _ _ _ _ (e₃ n) (e₁ (n + 1)) (e₂ (n + 1)) (hd n) (hf (n + 1))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hK.homology_exact₁ n (n + 1) rfl))

end CohomologyExactSequence

section RationalPoint

open Specs.FlagCohomology (sectionsFunctor cohomologyZero structureModule pushforwardSectionsIso)
open private sectionsSubsingleton_bot from LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

private abbrev basePoint (k : Type u) [Field k] := (𝟙_ (SchemeOver k) : SchemeOver k)

private theorem basePoint_subsingleton : Subsingleton (basePoint k).left := by
  change Subsingleton (PrimeSpectrum k)
  exact (PrimeSpectrum.subsingleton_iff_isField_of_isReduced (R := k)).mpr (Field.toIsField k)

private theorem basePoint_flasque (H : (basePoint k).left.Modules) :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (basePoint k).left.ringCatSheaf).obj H) := by
  let : Subsingleton (basePoint k).left := basePoint_subsingleton
  constructor
  intro U V i
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  rcases TopologicalSpace.Opens.eq_bot_or_top V.unop with hV | hV
  · have hsub : Subsingleton (H.val.obj V) := by
      rw [← V.op_unop, hV]
      exact sectionsSubsingleton_bot H
    exact fun s => ⟨0, hsub.elim _ _⟩
  · have hU : U.unop = ⊤ :=
      top_unique (hV ▸ CategoryTheory.leOfHom i.unop)
    have hUV : U = V := Opposite.unop_injective (hU.trans hV.symm)
    subst V
    rw [show i = 𝟙 U from Subsingleton.elim _ _]
    intro s
    refine ⟨s, ?_⟩
    let F := ((SheafOfModules.toSheaf (basePoint k).left.ringCatSheaf).obj H).obj
    exact ConcreteCategory.congr_hom (F.map_id U) s

set_option backward.isDefEq.respectTransparency false in
/-- A direct image of a sheaf on the rational point is acyclic,
regardless of the equivariant structure. -/
theorem pointPushforward_cohomology_isZero (x : basePoint k ⟶ X)
    (H : (basePoint k).left.Modules) (n : ℕ) :
    IsZero ((cohomology X (n + 1)).obj ((Scheme.Modules.pushforward x.left).obj H)) := by
  let : TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (basePoint k).left.ringCatSheaf).obj H) := basePoint_flasque H
  let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.left.ringCatSheaf).obj
      ((Scheme.Modules.pushforward x.left).obj H)) :=
    TopCat.Sheaf.IsFlasque.pushforward_isFlasque
      ((SheafOfModules.toSheaf (basePoint k).left.ringCatSheaf).obj H) x.left.base
  exact ProjectiveFiniteness.isZero_cohomology_of_isFlasque X _ n

private def basePointSectionsIso :
    (sectionsFunctor (basePoint k)).obj (structureModule (basePoint k).left) ≅ ModuleCat.of k k := by
  let R := CommRingCat.of k
  let e := Scheme.ΓSpecIso R
  let N := (sectionsFunctor (basePoint k)).obj (structureModule (basePoint k).left)
  let f : N →ₗ[k] k :=
    { toFun := e.hom
      map_add' := e.hom.hom.map_add
      map_smul' := by
        intro r s
        let z : Γ(Spec R, ⊤) := s
        change e.hom (e.inv r * z) = r * e.hom z
        rw [map_mul]
        congr 1
        exact ConcreteCategory.congr_hom e.inv_hom_id r }
  exact (LinearEquiv.ofBijective f (ConcreteCategory.bijective_of_isIso e.hom)).toModuleIso

/-- The degree-zero cohomology of the direct image of the structure line
at a rational point is the ground field. -/
def pointPushforward_cohomologyZeroIso (x : basePoint k ⟶ X)
    {H : (basePoint k).left.Modules} (e : H ≅ structureModule (basePoint k).left) :
    (cohomology X 0).obj ((Scheme.Modules.pushforward x.left).obj H) ≅ ModuleCat.of k k := by
  have hx : x.left ≫ X.hom = (basePoint k).hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    simp
  exact (cohomologyZero X).app _ ≪≫
    (pushforwardSectionsIso (RingHom.id k) x.left hx).app H ≪≫
    ModuleCat.restrictScalarsId'App (RingHom.id k) rfl _ ≪≫
    (sectionsFunctor (basePoint k)).mapIso e ≪≫ basePointSectionsIso

/-- For the direct image from a rational point the signed character is
its degree-zero cohomology character. -/
theorem isEulerCharacter_point_of_degreeZero
    (x : basePoint k ⟶ X) (F : EquivariantCoherent a) (hF : IsPointClass x F)
    {c : CharacterRing T} (hc : IsCohomologyCharacter F 0 c) : IsEulerCharacter F c := by
  obtain ⟨H, _, e, _, _⟩ := hF
  let ch (n : ℕ) := if n = 0 then c else 0
  have hz (n : ℕ) : IsZero ((cohomology X (n + 1)).obj F.sheaf) :=
    (pointPushforward_cohomology_isZero x H.sheaf n).of_iso ((cohomology X (n + 1)).mapIso e)
  refine ⟨1, ch, ?_, ?_, by simp [ch]⟩
  · intro n
    cases n with
    | zero => simpa only [ch, ite_eq_left rfl] using hc
    | succ n => simpa only [ch, Nat.succ_ne_zero, ite_false] using
        isCohomologyCharacter_zero_of_isZero F (n + 1) (hz n)
  · intro n hn
    cases n with
    | zero => omega
    | succ n => exact hz n

/-- A one-dimensional space with a single universal weight has the
character of that weight. -/
private theorem cohomologyCharacter_of_line
    (F : EquivariantCoherent a) (n : ℕ) (m : CohomologyPullbacks F n)
    (e : (cohomology X n).obj F.sheaf ≅ ModuleCat.of k k) (χ : Character T)
    (hw : ∀ ψ v, v ∈ cohomologyWeightSpace m ψ ↔ ψ = χ ∨ v = 0) :
    IsCohomologyCharacter F n (eChar χ) := by
  classical
  let : Module.Finite k ((cohomology X n).obj F.sheaf) :=
    Module.Finite.of_surjective e.inv.hom e.toLinearEquiv.symm.surjective
  refine ⟨inferInstance, m, fun ψ => ?_⟩
  change (MonoidAlgebra.single χ (1 : ℤ)).coeff ψ = _
  rcases eq_or_ne ψ χ with rfl | h
  · have he : cohomologyWeightSpace m ψ = ⊤ :=
      Submodule.eq_top_iff'.mpr fun v => (hw ψ v).mpr (Or.inl rfl)
    rw [he, finrank_top, e.toLinearEquiv.finrank_eq, Module.finrank_self]
    simp
  · have he : cohomologyWeightSpace m ψ = ⊥ := by
      ext v
      simp only [hw, h, false_or, Submodule.mem_bot]
    rw [he, finrank_bot]
    simp [Ne.symm h]

/-- The direct image of the trivial structure line at a rational fixed
closed point has signed character one. -/
theorem pointEulerCharacter (split : IsSplitTorus T) (x : basePoint k ⟶ X)
    [IsClosedImmersion x.left] (F : EquivariantCoherent a) (hF : IsPointClass x F) :
    IsEulerCharacter F 1 := by
  obtain ⟨H, e₀, e, htriv, he⟩ := hF
  obtain ⟨_, hw⟩ := EquivariantPointGlobalSections.pointGlobalSections
    split x H e₀ F e htriv he
  obtain ⟨m⟩ := cohomologyPullbacks_nonempty F 0
  have hc := cohomologyCharacter_of_line F 0 m
    ((cohomology X 0).mapIso e ≪≫ pointPushforward_cohomologyZeroIso x e₀) (1 : Character T)
    (fun ψ v => (cohomologyWeights_zero m ψ v).trans <| (hw _ ψ).trans <| by
      let f := ((cohomologyZero X).app F.sheaf).toLinearEquiv
      change ψ = 1 ∨ f v = 0 ↔ ψ = 1 ∨ v = 0
      rw [map_eq_zero_iff f f.injective])
  exact isEulerCharacter_point_of_degreeZero x F ⟨H, e₀, e, htriv, he⟩ hc

end RationalPoint

section EquivariantConnecting

open Specs.CoherentCohomologyAlgebraBaseChange
open Specs.FlagCohomology (HasFiniteAffineCover IsCohomologyMap)
open Specs.OrderedCechComparison (ComparisonFamily)
open Scheme.Modules

private theorem connecting_multiply (c : ComparisonFamily.{u})
    (hc : ConnectingNaturality c) (hX : HasFiniteAffineCover X)
    {S : ShortComplex X.left.Modules} {d : ConnectingMaps X S}
    (hd : ComputesConnectingUsingCech c X S d) (r : Γ(X.left, ⊤)) (n : ℕ) :
    d n ≫ (cohomology X (n + 1)).map (multiply S.X₁ r) =
      (cohomology X n).map (multiply S.X₃ r) ≫ d n := by
  let f := 𝟙 X.left
  let i := pushforwardId X.left
  let α : S ⟶ S.map (pushforward f) :=
    { τ₁ := multiply S.X₁ r ≫ i.inv.app S.X₁
      τ₂ := multiply S.X₂ r ≫ i.inv.app S.X₂
      τ₃ := multiply S.X₃ r ≫ i.inv.app S.X₃
      comm₁₂ := by
        dsimp only [ShortComplex.map_f]
        rw [Category.assoc, ← i.inv.naturality, ← Category.assoc,
          EquivariantAffineModules.multiply_natural]
        rfl
      comm₂₃ := by
        dsimp only [ShortComplex.map_g]
        rw [Category.assoc, ← i.inv.naturality, ← Category.assoc,
          EquivariantAffineModules.multiply_natural]
        rfl }
  have hw : f ≫ X.hom = X.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    simp [f]
  let j₁ := ModuleCat.restrictScalarsId'App (RingHom.id k) rfl
    ((cohomology X (n + 1)).obj S.X₁)
  let j₃ := ModuleCat.restrictScalarsId'App (RingHom.id k) rfl
    ((cohomology X n).obj S.X₃)
  have h₁ : IsCohomologyMap (RingHom.id k) f hw α.τ₁ (n + 1)
      ((cohomology X (n + 1)).map (multiply S.X₁ r) ≫ j₁.inv) :=
    FlatCohomology.cohomologyMapId X (multiply S.X₁ r) (n + 1)
  have h₃ : IsCohomologyMap (RingHom.id k) f hw α.τ₃ n
      ((cohomology X n).map (multiply S.X₃ r) ≫ j₃.inv) :=
    FlatCohomology.cohomologyMapId X (multiply S.X₃ r) n
  have h := hc (RingHom.id k) f hw hX α hd hd n h₁ h₃
  apply (cancel_mono j₁.inv).mp
  simpa only [Category.assoc, j₁, j₃, ← ModuleCat.restrictScalarsId'App_inv_naturality]
    using h

/-- The connecting maps of a short exact sequence of linearized
coefficients preserve the universal cohomology weights. -/
theorem equivariantCohomology_longExact [IsAffine T.X.left]
    (hX : HasFiniteAffineCover X) {F H K : EquivariantCoherent a}
    (f : F.sheaf ⟶ H.sheaf) (g : H.sheaf ⟶ K.sheaf) (w : f ≫ g = 0)
    (hf : EquivariantHom f) (hg : EquivariantHom g) (he : (ShortComplex.mk f g w).ShortExact)
    (m : ∀ (F : EquivariantCoherent a) (n : ℕ), CohomologyPullbacks F n) :
    ∃ δ : ConnectingMaps X (ShortComplex.mk f g w),
      IsLongExactSequence X (ShortComplex.mk f g w) δ ∧
      ∀ (n : ℕ) (χ : Character T) (v : (cohomology X n).obj K.sheaf),
        v ∈ cohomologyWeightSpace (m K n) χ →
          δ n v ∈ cohomologyWeightSpace (m F (n + 1)) χ := by
  let S := ShortComplex.mk f g w
  let : S.X₁.IsQuasicoherent := F.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let : S.X₂.IsQuasicoherent := H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let : S.X₃.IsQuasicoherent := K.coherent.exists_quasicoherentData.choose.isQuasicoherent
  obtain ⟨c, _, _, hc, _, hl⟩ := CoherentCohomologyAlgebraBaseChange.cohomologyConnecting
  obtain ⟨d, e, hd, _, _, ce, hp, ha⟩ := hl T X hX a S he F.lin H.lin K.lin hf hg
  let Y := T.X ⊗ X
  let T' := S.map (pullback a.smul.left)
  have pb := Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (fst T.X X) (snd T.X X)) (tensorProductIsBinaryProduct T.X X)
  let : IsAffineHom (snd T.X X).left :=
    MorphismProperty.of_isPullback pb (show IsAffineHom T.X.hom from inferInstance)
  have hY : HasFiniteAffineCover Y :=
    affinePullback_hasFiniteAffineCover (snd T.X X).left hX
  refine ⟨d, hd, fun n χ v hv => ?_⟩
  have hp' := ConcreteCategory.congr_hom
    (hp.2 n (m F (n + 1)).projection_induced (m K n).projection_induced) v
  have ha' := ConcreteCategory.congr_hom
    (ha.2 n (m F (n + 1)).action_induced (m K n).action_induced) v
  have hmul := connecting_multiply c hc hY (S := T') ce
    ((fst T.X X).left.appTop (characterFunction χ)) n
  rw [mem_cohomologyWeightSpace] at hv ⊢
  change (m F (n + 1)).viaProjection (d n v) = e n ((m K n).viaProjection v) at hp'
  change (m F (n + 1)).viaAction (d n v) = e n ((m K n).viaAction v) at ha'
  rw [hp', ha', hv]
  exact (ConcreteCategory.congr_hom hmul ((m K n).viaAction v)).symm

end EquivariantConnecting

section DerivedPullback

open Scheme.Modules
open Specs.FlagCohomology (SchemeOverRing IsCohomologyMap)
open private cohomologyMap_comp_apply cohomologyMap_natural pushforwardCongr_refl
  from LinearAlgebraicGroups.Representation.CoherentCohomologyAlgebraBaseChange
open private transpose_comp
  from LinearAlgebraicGroups.Representation.FlagCovarianceLinearization
open private comparePull pullCongr_refl
  from LinearAlgebraicGroups.Representation.EquivariantAffineModules

open private pushforwardEquivalenceOfIso
  from LinearAlgebraicGroups.Representation.FlagCohomology

private abbrev cohomologyAdjoint {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F : X.Modules} {H : Y.Modules} (c : (Scheme.Modules.pullback f).obj F ⟶ H) :=
  (pullbackPushforwardAdjunction f).homEquiv F H c

private theorem cohomologyAdjoint_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {p : Z ⟶ X} (w : g ≫ f = p) {F : X.Modules} {H : Y.Modules} {K : Z.Modules}
    (c : (Scheme.Modules.pullback f).obj F ⟶ H) (d : (Scheme.Modules.pullback g).obj H ⟶ K) :
    cohomologyAdjoint f c ≫ (pushforward f).map (cohomologyAdjoint g d) ≫
      (pushforwardComp g f).hom.app K ≫ (pushforwardCongr w).hom.app K =
    cohomologyAdjoint p
      ((pullbackCongr w).inv.app F ≫ (pullbackComp g f).inv.app F ≫ (Scheme.Modules.pullback g).map c ≫ d) := by
  subst p
  have hi : (pullbackCongr (rfl : g ≫ f = g ≫ f)).inv.app F = 𝟙 _ := rfl
  rw [pushforwardCongr_refl, Category.comp_id, hi, Category.id_comp]
  apply ((pullbackPushforwardAdjunction (g ≫ f)).homEquiv F K).symm.injective
  rw [Equiv.symm_apply_apply, transpose_comp, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

private theorem induced_comp_apply {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    {X : SchemeOverRing A} {Y : SchemeOverRing B} {Z : SchemeOverRing C}
    (φ : A →+* B) (ψ : B →+* C) (ξ : A →+* C) (e : ψ.comp φ = ξ)
    (f : Y.left ⟶ X.left) (g : Z.left ⟶ Y.left) (p : Z.left ⟶ X.left)
    [Flat f] [Flat g] (w : g ≫ f = p)
    (wf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (wg : g ≫ Y.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom ψ))
    (wp : p ≫ X.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom ξ))
    {F : X.left.Modules} {H : Y.left.Modules} {K : Z.left.Modules}
    (c : (Scheme.Modules.pullback f).obj F ⟶ H) (d : (Scheme.Modules.pullback g).obj H ⟶ K)
    (b : (Scheme.Modules.pullback p).obj F ⟶ K)
    (hb : (pullbackComp g f).hom.app F ≫ (pullbackCongr w).hom.app F ≫ b =
      (Scheme.Modules.pullback g).map c ≫ d)
    (n : ℕ) {l m r}
    (hl : IsCohomologyMap φ f wf (cohomologyAdjoint f c) n l)
    (hm : IsCohomologyMap ψ g wg (cohomologyAdjoint g d) n m)
    (hr : IsCohomologyMap ξ p wp (cohomologyAdjoint p b) n r)
    (v : (cohomology X n).obj F) : m (l v) = r v := by
  apply cohomologyMap_comp_apply φ ψ ξ e f g p w wf wg wp _ _ _ _ n hl hm hr
  rw [cohomologyAdjoint_comp f g w, ← hb]
  simp only [Iso.inv_hom_id_app_assoc]

private def cohomologyPull {Y : SchemeOver k} (f : Y ⟶ X) [Flat f.left]
    {F : X.left.Modules} {H : Y.left.Modules} (c : Pull f F ⟶ H) (n : ℕ) :
    (cohomology X n).obj F ⟶ (cohomology Y n).obj H :=
  (exists_inducesOnCohomology f c n).choose

private theorem cohomologyPull_induced {Y : SchemeOver k} (f : Y ⟶ X) [Flat f.left]
    {F : X.left.Modules} {H : Y.left.Modules} (c : Pull f F ⟶ H) (n : ℕ) :
    InducesOnCohomology f c n (cohomologyPull f c n) :=
  (exists_inducesOnCohomology f c n).choose_spec

set_option backward.isDefEq.respectTransparency false in
private theorem cohomologyPull_comp_apply {Y Z : SchemeOver k}
    (f : Y ⟶ X) (g : Z ⟶ Y) (p : Z ⟶ X) [Flat f.left] [Flat g.left] [Flat p.left]
    (w : g ≫ f = p) {F : X.left.Modules} {H : Y.left.Modules} {K : Z.left.Modules}
    (c : Pull f F ⟶ H) (d : Pull g H ⟶ K) (b : Pull p F ⟶ K)
    (hb : (comparePull F g f w).hom ≫ b = (Scheme.Modules.pullback g.left).map c ≫ d)
    (n : ℕ) (v : (cohomology X n).obj F) :
    cohomologyPull g d n (cohomologyPull f c n v) = cohomologyPull p b n v := by
  have hl := cohomologyPull_induced f c n
  have hm := cohomologyPull_induced g d n
  have hr := cohomologyPull_induced p b n
  unfold InducesOnCohomology at hl hm hr
  exact induced_comp_apply _ _ _ rfl f.left g.left p.left (congrArg Over.Hom.left w)
    _ _ _ c d b (by exact hb) n hl hm hr v

private theorem cohomologyPull_natural {Y : SchemeOver k} (f : Y ⟶ X) [Flat f.left]
    {F F' : X.left.Modules} {H H' : Y.left.Modules}
    (b : F ⟶ F') (d : H ⟶ H') (c : Pull f F ⟶ H) (c' : Pull f F' ⟶ H')
    (h : (Scheme.Modules.pullback f.left).map b ≫ c' = c ≫ d) (n : ℕ) :
    (cohomology X n).map b ≫ cohomologyPull f c' n =
      cohomologyPull f c n ≫ (cohomology Y n).map d :=
  inducesOnCohomology_naturality f b d c c' h n
    (cohomologyPull_induced f c n) (cohomologyPull_induced f c' n)

private theorem cohomologyPull_postcomp {Y : SchemeOver k} (f : Y ⟶ X) [Flat f.left]
    {F : X.left.Modules} {H H' : Y.left.Modules} (c : Pull f F ⟶ H)
    (d : H ⟶ H') (n : ℕ) :
    cohomologyPull f (c ≫ d) n = cohomologyPull f c n ≫ (cohomology Y n).map d := by
  have h := cohomologyPull_natural f (𝟙 F) d c (c ≫ d) (by simp) n
  rw [(cohomology X n).map_id, Category.id_comp] at h
  exact h

private theorem cohomologyPull_congr {Y : SchemeOver k} {f g : Y ⟶ X}
    [Flat f.left] [Flat g.left] (w : f = g)
    {F : X.left.Modules} {H : Y.left.Modules} (c : Pull g F ⟶ H) (n : ℕ) :
    cohomologyPull f ((pullCongr F w).hom ≫ c) n = cohomologyPull g c n := by
  subst g
  rw [pullCongr_refl, Category.id_comp]

private theorem cohomologyPull_multiply {Y : SchemeOver k} (f : Y ⟶ X) [Flat f.left]
    {F : X.left.Modules} {H : Y.left.Modules} (c : Pull f F ⟶ H)
    (r : Γ(X.left, ⊤)) (n : ℕ) :
    (cohomology X n).map (multiply F r) ≫ cohomologyPull f c n =
      cohomologyPull f c n ≫ (cohomology Y n).map (multiply H (f.left.appTop r)) := by
  apply cohomologyPull_natural
  rw [EquivariantAffineModules.pullback_multiply, EquivariantAffineModules.multiply_natural]

private theorem exists_inducedIso {A B : Type u} [CommRing A] [CommRing B]
    {Z : SchemeOverRing A} {Y : SchemeOverRing B} (φ : A →+* B)
    (f : Y.left ⟶ Z.left) [IsIso f]
    (w : f ≫ Z.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {F : Z.left.Modules} {H : Y.left.Modules} (c : (Scheme.Modules.pullback f).obj F ≅ H) (n : ℕ) :
    ∃ e : (cohomology Z n).obj F ≅
        (ModuleCat.restrictScalars φ).obj ((cohomology Y n).obj H),
      IsCohomologyMap φ f w (cohomologyAdjoint f c.hom) n e.hom := by
  let e := pushforwardEquivalenceOfIso (X := Z)
    (Y := (Over.map (Spec.map (CommRingCat.ofHom φ))).obj Y) f
  let : (pushforward f).IsEquivalence := e.isEquivalence_functor
  let α := cohomologyAdjoint f c.hom
  let : IsIso α := by
    dsimp only [α, cohomologyAdjoint]
    rw [Adjunction.homEquiv_unit]
    infer_instance
  obtain ⟨b, hb⟩ := FlagCohomology.exactPushforward_isCohomologyMap φ f w α n
  exact ⟨(cohomology Z n).mapIso (asIso α) ≪≫ b, hb⟩

end DerivedPullback

section ProductCohomology

open scoped TensorProduct ChangeOfRings
open Specs.FlagCohomology (HasFiniteAffineCover extendToAlgebra extendScheme extensionProjection
  extensionProjection_over groundRingHom)
open Specs.CoherentCohomologyAlgebraBaseChange (IsBaseChange)
open Scheme.Modules
open private projectionToOriginal projectionToTestScheme extensionAsSchemeOverField
  from Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private extensionProductIso extensionProductIso_snd extensionProductIso_fst
  from LinearAlgebraicGroups.Representation.FlagCovarianceLinearization
open private torusProductChart groupRingAlgebra comparePull appTop_comp_apply
  from LinearAlgebraicGroups.Representation.EquivariantAffineModules
open private cohomologyMap_natural
  from LinearAlgebraicGroups.Representation.CoherentCohomologyAlgebraBaseChange

/-- A split torus has an affine coordinate system with the characters as
its monomial basis. -/
private theorem torusCharacterChart (T : GroupScheme k) (split : IsSplitTorus T) :
    let R := groupRingAlgebra (CommAlgCat.of k k) (Character T)
    ∃ j : affineScheme R ≅ T.X,
      ∀ χ, j.hom.left.appTop (characterFunction χ) =
        (Scheme.ΓSpecIso (affineRing R)).inv (MonoidAlgebra.of k _ χ) := by
  obtain ⟨e, _, hχ⟩ := torusProductChart T split (CommAlgCat.of k k)
  let o : affineScheme (CommAlgCat.of k k) ≅ (𝟙_ (SchemeOver k)) :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 (Spec (CommRingCat.of k)) ≫ 𝟙 _ = Spec.map (CommRingCat.ofHom (RingHom.id k))
      simp)
  let q : T.X ⊗ affineScheme (CommAlgCat.of k k) ≅ T.X :=
    (Iso.refl T.X ⊗ᵢ o) ≪≫ (ρ_ T.X)
  have hq : q.hom = fst T.X (affineScheme (CommAlgCat.of k k)) := by
    simp [q, rightUnitor_hom]
  refine ⟨e ≪≫ q, ?_⟩
  intro χ
  simpa only [Iso.trans_hom, hq] using hχ χ

private theorem torus_isAffine (T : GroupScheme k) (split : IsSplitTorus T) :
    IsAffine T.X.left := by
  obtain ⟨j, _⟩ := torusCharacterChart T split
  exact AlgebraicGeometry.essImage_algSpec.mp ⟨_, ⟨j⟩⟩

private abbrev geometricScalar {Y : SchemeOver k} {H : Y.left.Modules}
    (n : ℕ) (r : Γ(Y.left, ⊤)) :=
  (cohomology Y n).map (multiply H r)

private def ProjectionCohomologyExpansion (T : GroupScheme k) (X : SchemeOver k)
    (F : X.left.Modules) (n : ℕ)
    (E : (cohomology (T.X ⊗ X) n).obj (Pull (snd T.X X) F) ≃+
      (Character T →₀ (cohomology X n).obj F)) : Prop :=
  letI : Flat (snd T.X X).left := isFlat_projection T X
  ∀ χ v, E (geometricScalar n ((fst T.X X).left.appTop (characterFunction χ))
      (cohomologyPull (snd T.X X) (𝟙 (Pull (snd T.X X) F)) n v)) = Finsupp.single χ v

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
private theorem projectionCohomology_baseChange {R : TestAlgebra k}
    (j : affineScheme R ≅ T.X) (X : SchemeOver k) (hX : HasFiniteAffineCover X)
    (F : X.left.Modules) [F.IsQuasicoherent] (n : ℕ) :
    letI : Flat (snd T.X X).left := isFlat_projection T X
    let V := (cohomology X n).obj F
    let VR := (extendToAlgebra (k := k) (K := R)).obj V
    ∃ e : (cohomology (T.X ⊗ X) n).obj (Pull (snd T.X X) F) ≅
        (ModuleCat.restrictScalars (algebraMap k R)).obj VR,
      ∀ (c : Γ(T.X.left, ⊤)) (v : V),
        e.hom (geometricScalar n ((fst T.X X).left.appTop c)
          (cohomologyPull (snd T.X X) (𝟙 (Pull (snd T.X X) F)) n v)) =
        ((Scheme.ΓSpecIso (affineRing R)).hom (j.hom.left.appTop c) •
          (show VR from (ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).unit.app V v) : VR) := by
  let Y : SchemeOver k := T.X ⊗ X
  let p : Y ⟶ X := snd T.X X
  let Y' : Specs.FlagCohomology.SchemeOverRing R := (extendScheme R).obj X
  let Yk : SchemeOver k := extensionAsSchemeOverField R X
  let q : Yk ⟶ Y := (extensionProductIso (R := R) j X).hom
  let H : Y.left.Modules := Pull p F
  let K : Y'.left.Modules := (Scheme.Modules.pullback (extensionProjection R X)).obj F
  have w : q.left ≫ p.left = extensionProjection R X :=
    congrArg Over.Hom.left (extensionProductIso_snd (R := R) j X)
  let c : (Scheme.Modules.pullback q.left).obj H ≅ K :=
    (pullbackComp q.left p.left).app F ≪≫ (pullbackCongr w).app F
  have wq : q.left ≫ Y.hom = Y'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) :=
    Over.w q
  let : Flat p.left := isFlat_projection T X
  let : IsIso q.left := inferInstanceAs (IsIso ((Over.forget _).map q))
  obtain ⟨e, he⟩ := exists_inducedIso (Z := Y) (Y := Y') (algebraMap k R) q.left wq c n
  obtain ⟨b, hb⟩ := CoherentCohomologyAlgebraBaseChange.baseChange X hX R F n
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap k R)
  let B := ModuleCat.restrictScalars (algebraMap k R)
  let V := (cohomology X n).obj F
  let VR := (extendToAlgebra (k := k) (K := R)).obj V
  refine ⟨e ≪≫ B.mapIso b.symm, fun d₀ v => ?_⟩
  let r : R := (Scheme.ΓSpecIso (affineRing R)).hom (j.hom.left.appTop d₀)
  let d := (fst T.X X).left.appTop d₀
  have hcomp : e.hom (cohomologyPull p (𝟙 H) n v) = adj.homEquiv _ _ b.hom v := by
    have hp := cohomologyPull_induced p (𝟙 H) n
    unfold InducesOnCohomology at hp
    have hb' : Specs.FlagCohomology.IsCohomologyMap (algebraMap k R)
        (extensionProjection R X) (extensionProjection_over R X)
        (cohomologyAdjoint (extensionProjection R X) (𝟙 K)) n (adj.homEquiv _ _ b.hom) := by
      have hc : cohomologyAdjoint (extensionProjection R X) (𝟙 K) =
          (pullbackPushforwardAdjunction (extensionProjection R X)).unit.app F := by
        change (pullbackPushforwardAdjunction (extensionProjection R X)).homEquiv F K (𝟙 K) = _
        rw [Adjunction.homEquiv_unit, (pushforward (extensionProjection R X)).map_id]
        exact Category.comp_id _
      exact hc.symm ▸ hb
    refine induced_comp_apply (X := X) (Y := Y) (Z := Y') (RingHom.id k)
      (algebraMap k R) (algebraMap k R) (RingHom.comp_id _)
      p.left q.left (extensionProjection R X) w
      _ _ _ (𝟙 H) c.hom (𝟙 K) ?_ n hp he hb' v
    rw [(Scheme.Modules.pullback q.left).map_id, Category.id_comp, Category.comp_id]
    rfl
  have hd : q.left.appTop d = groundRingHom Y' r := by
    change q.left.appTop ((fst T.X X).left.appTop d₀) = _
    rw [← appTop_comp_apply, ← Over.comp_left,
      extensionProductIso_fst j X, Over.comp_left, appTop_comp_apply]
    unfold groundRingHom
    change _ = Y'.hom.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r)
    rw [show (Scheme.ΓSpecIso (affineRing R)).inv r = j.hom.left.appTop d₀ from
      ConcreteCategory.congr_hom (Scheme.ΓSpecIso (affineRing R)).hom_inv_id _]
    rfl
  have hmul : (cohomology Y n).map (multiply H d) ≫ e.hom =
      e.hom ≫ B.map ((cohomology Y' n).map (FlagCohomology.sheafScalarMap Y' r K)) := by
    refine cohomologyMap_natural (X := Y) (Y := Y') (algebraMap k R) q.left wq (multiply H d)
      (FlagCohomology.sheafScalarMap Y' r K) (α := cohomologyAdjoint q.left c.hom)
      (α' := cohomologyAdjoint q.left c.hom) ?_ n he he
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
    congr 1
    have hscalar : FlagCohomology.sheafScalarMap Y' r K =
        multiply (X := extensionAsSchemeOverField R X) K (groundRingHom Y' r) := rfl
    rw [EquivariantAffineModules.pullback_multiply, hd, hscalar,
      EquivariantAffineModules.multiply_natural]
  rw [FlagCohomology.cohomology_map_scalar] at hmul
  have h := ConcreteCategory.congr_hom hmul (cohomologyPull p (𝟙 H) n v)
  change e.hom (geometricScalar n d (cohomologyPull p (𝟙 H) n v)) =
    r • e.hom (cohomologyPull p (𝟙 H) n v) at h
  change b.inv (e.hom (geometricScalar n d (cohomologyPull p (𝟙 H) n v))) =
    r • (show VR from adj.unit.app V v)
  rw [h, hcomp]
  rw [show adj.homEquiv _ _ b.hom v = b.hom (adj.unit.app V v) from rfl]
  change b.inv.hom (r • b.hom (adj.unit.app V v)) = _
  rw [_root_.map_smul]
  exact congrArg (r • ·) (ConcreteCategory.congr_hom b.hom_inv_id _)

set_option backward.isDefEq.respectTransparency false in
private theorem projectionCohomologyExpansion (T : GroupScheme k) (split : IsSplitTorus T)
    (X : SchemeOver k) (hX : HasFiniteAffineCover X) (F : X.left.Modules) [F.IsQuasicoherent]
    (n : ℕ) :
    ∃ E : (cohomology (T.X ⊗ X) n).obj (Pull (snd T.X X) F) ≃+
      (Character T →₀ (cohomology X n).obj F), ProjectionCohomologyExpansion T X F n E := by
  classical
  let R := groupRingAlgebra (CommAlgCat.of k k) (Character T)
  obtain ⟨j, hχ⟩ := torusCharacterChart T split
  obtain ⟨e, he⟩ := projectionCohomology_baseChange (R := R) j X hX F n
  let V := (cohomology X n).obj F
  let B := (ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R R)
  let i : R ≃ₗ[k] B :=
    { Equiv.refl R with
      map_add' := fun _ _ => rfl
      map_smul' := fun r s => Algebra.smul_def r s }
  let basis := (MonoidAlgebra.basis (Character T) k).map i
  let D := TensorProduct.equivFinsuppOfBasisLeft (N := V) basis
  let E := e.toLinearEquiv.toAddEquiv.trans D.toAddEquiv
  refine ⟨E, fun χ v => ?_⟩
  letI : Flat (snd T.X X).left := isFlat_projection T X
  change D (e.hom (geometricScalar n ((fst T.X X).left.appTop (characterFunction χ))
    (cohomologyPull (snd T.X X) (𝟙 (Pull (snd T.X X) F)) n v))) = _
  rw [he, hχ]
  have h : (Scheme.ΓSpecIso (affineRing R)).hom
      ((Scheme.ΓSpecIso (affineRing R)).inv (MonoidAlgebra.of k (Character T) χ)) =
      MonoidAlgebra.of k (Character T) χ :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (affineRing R)).inv_hom_id _
  rw [h]
  change D ((MonoidAlgebra.of k (Character T) χ * (1 : R)) ⊗ₜ[k,algebraMap k R] v) = _
  rw [mul_one]
  change D (basis χ ⊗ₜ[k] v) = _
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, Module.Basis.repr_self]
  simp

end ProductCohomology

section InverseTransportCohomology

open Scheme.Modules
open private comparePull pullCongr_refl transport_symm_eq_eval inverseTransport_cocycle
  eq_of_weighted_sums appTop_comp_apply
  from LinearAlgebraicGroups.Representation.EquivariantAffineModules
open private pullback_isQuasicoherent
  from LinearAlgebraicGroups.Representation.CoherentCohomologyAlgebraBaseChange

variable {Z : SchemeOver k} {F : X.left.Modules}

private abbrev inverseTransportOnCohomology (L : Linearization a F) (t : Z ⟶ T.X)
    (x : Z ⟶ X) [Flat (actOn a t x).left] (n : ℕ) :=
  cohomologyPull (actOn a t x) (transport a L.iso t x).inv n

private def inverseCohomologyCoefficients (L : Linearization a F) (n : ℕ)
    (E : (cohomology (T.X ⊗ X) n).obj (Pull (snd T.X X) F) ≃+
      (Character T →₀ (cohomology X n).obj F)) (v : (cohomology X n).obj F) :
    Character T →₀ (cohomology X n).obj F :=
  letI : Flat a.smul.left := isFlat_action a
  E (cohomologyPull a.smul L.iso.inv n v)

set_option backward.isDefEq.respectTransparency false in
private theorem inverseCohomology_expansion (L : Linearization a F) (n : ℕ)
    (E : (cohomology (T.X ⊗ X) n).obj (Pull (snd T.X X) F) ≃+
      (Character T →₀ (cohomology X n).obj F))
    (hE : ProjectionCohomologyExpansion T X F n E)
    (t : Z ⟶ T.X) (x : Z ⟶ X)
    [Flat (lift t x).left] [Flat x.left] [Flat (actOn a t x).left]
    (v : (cohomology X n).obj F) :
    inverseTransportOnCohomology L t x n v =
      (inverseCohomologyCoefficients L n E v).sum
        (fun χ w => geometricScalar n (t.left.appTop (characterFunction χ))
          (cohomologyPull x (𝟙 (Pull x F)) n w)) := by
  classical
  let p := snd T.X X
  let l := lift t x
  let B := cohomologyPull l (comparePull F l p (lift_snd t x)).hom n
  letI : Flat p.left := isFlat_projection T X
  letI : Flat a.smul.left := isFlat_action a
  let prev := cohomologyPull a.smul L.iso.inv n v
  let z := inverseCohomologyCoefficients L n E v
  have hcomp : B prev = inverseTransportOnCohomology L t x n v := by
    apply cohomologyPull_comp_apply a.smul l (actOn a t x) rfl
    have ht := congrArg Iso.hom (transport_symm_eq_eval L.iso t x)
    change (transport a L.iso t x).inv =
      (comparePull F l a.smul rfl).inv ≫
        (Scheme.Modules.pullback l.left).map L.iso.inv ≫ (comparePull F l p (lift_snd t x)).hom at ht
    rw [ht, Iso.hom_inv_id_assoc]
  have hp (w : (cohomology X n).obj F) :
      B (cohomologyPull p (𝟙 (Pull p F)) n w) = cohomologyPull x (𝟙 (Pull x F)) n w := by
    apply cohomologyPull_comp_apply p l x (lift_snd t x)
    rw [(Scheme.Modules.pullback l.left).map_id, Category.id_comp, Category.comp_id]
  have hb (χ : Character T) (w : (cohomology X n).obj F) :
      B (geometricScalar n ((fst T.X X).left.appTop (characterFunction χ))
        (cohomologyPull p (𝟙 (Pull p F)) n w)) =
      geometricScalar n (t.left.appTop (characterFunction χ)) (cohomologyPull x (𝟙 (Pull x F)) n w) := by
    let r := (fst T.X X).left.appTop (characterFunction χ)
    have h := ConcreteCategory.congr_hom
      (cohomologyPull_multiply l (comparePull F l p (lift_snd t x)).hom r n)
      (cohomologyPull p (𝟙 (Pull p F)) n w)
    change B _ = geometricScalar n (l.left.appTop r) (B _) at h
    rw [hp] at h
    have hl : l.left.appTop r = t.left.appTop (characterFunction χ) := by
      dsimp only [r]
      rw [← appTop_comp_apply, ← Over.comp_left, lift_fst]
    rwa [hl] at h
  have hrebuild : prev = z.sum (fun χ w =>
      geometricScalar n ((fst T.X X).left.appTop (characterFunction χ))
        (cohomologyPull p (𝟙 (Pull p F)) n w)) := by
    apply E.injective
    change z = E _
    rw [Finsupp.sum, map_sum]
    refine (Finsupp.sum_single z).symm.trans (Finset.sum_congr rfl fun χ _ => ?_)
    exact (hE χ (z χ)).symm
  rw [← hcomp, hrebuild, Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun χ _ => hb χ (z χ)

set_option backward.isDefEq.respectTransparency false in
private theorem inverseCohomology_pullback (L : Linearization a F) (n : ℕ)
    (t : Z ⟶ T.X) (x : Z ⟶ X) (l : Z ⟶ T.X ⊗ X) (hl : l = lift t x)
    [Flat l.left] [Flat (actOn a t x).left]
    (hp : l ≫ snd T.X X = x) (v : (cohomology X n).obj F) :
    letI : Flat a.smul.left := isFlat_action a
    cohomologyPull l (comparePull F l (snd T.X X) hp).hom n
        (cohomologyPull a.smul L.iso.inv n v) =
      inverseTransportOnCohomology L t x n v := by
  subst l
  letI : Flat a.smul.left := isFlat_action a
  apply cohomologyPull_comp_apply a.smul (lift t x) (actOn a t x) rfl
  have ht := congrArg Iso.hom (transport_symm_eq_eval L.iso t x)
  change (transport a L.iso t x).inv =
    (comparePull F (lift t x) a.smul rfl).inv ≫
      (Scheme.Modules.pullback (lift t x).left).map L.iso.inv ≫
        (comparePull F (lift t x) (snd T.X X) hp).hom at ht
  rw [ht, Iso.hom_inv_id_assoc]

private theorem multiplyCohomology_natural {Y : SchemeOver k} {F H : Y.left.Modules}
    (c : F ⟶ H) (n : ℕ) (r : Γ(Y.left, ⊤)) :
    geometricScalar n r ≫ (cohomology Y n).map c =
      (cohomology Y n).map c ≫ geometricScalar n r := by
  rw [← Functor.map_comp, ← Functor.map_comp, EquivariantAffineModules.multiply_natural]

private theorem inverseCohomology_cocycle (L : Linearization a F) (n : ℕ)
    (s t : Z ⟶ T.X) (x : Z ⟶ X)
    [Flat (actOn a s (actOn a t x)).left] [Flat (actOn a (s * t) x).left]
    (v : (cohomology X n).obj F) :
    (cohomology Z n).map (transport a L.iso t x).inv
      (inverseTransportOnCohomology L s (actOn a t x) n v) =
    inverseTransportOnCohomology L (s * t) x n v := by
  let w := (L.mul Z s t x).choose
  have h := inverseTransport_cocycle L s t x w
  have h' : (transport a L.iso s (actOn a t x)).inv ≫ (transport a L.iso t x).inv =
      (pullCongr F w).hom ≫ (transport a L.iso (s * t) x).inv := by
    apply (cancel_epi (pullCongr F w).inv).mp
    simpa only [ComposesTo, Category.assoc, Iso.inv_hom_id_assoc] using h
  change ((cohomologyPull (actOn a s (actOn a t x))
    (transport a L.iso s (actOn a t x)).inv n ≫
      (cohomology Z n).map (transport a L.iso t x).inv) v) = _
  rw [← cohomologyPull_postcomp, h', cohomologyPull_congr w]

open private isPullback_tensor_snd from LinearAlgebraicGroups.Flag.SmoothOrbit
open private isPullback_tensor_fst from LinearAlgebraicGroups.RootData.RankOneFlag

private theorem tensor_id_flat {A B C : SchemeOver k} (f : B ⟶ C) [Flat f.left] :
    Flat (𝟙 A ⊗ₘ f).left :=
  MorphismProperty.of_isPullback ((isPullback_tensor_snd (A := A) f).flip.map (Over.forget _))
    ‹Flat f.left›

private theorem id_tensor_flat {A B C : SchemeOver k} (f : A ⟶ B) [Flat f.left] :
    Flat (f ⊗ₘ 𝟙 C).left :=
  MorphismProperty.of_isPullback ((isPullback_tensor_fst f C).flip.map (Over.forget _))
    ‹Flat f.left›

private theorem flat_comp_over {X Y Z : SchemeOver k}
    (f : Z ⟶ Y) (g : Y ⟶ X) [Flat f.left] [Flat g.left] :
    Flat (f ≫ g).left :=
  inferInstanceAs (Flat (f.left ≫ g.left))

private theorem nestedActionLift_flat (a : ModObj T.X X) :
    let Y := T.X ⊗ X
    Flat (lift (fst T.X Y) (snd T.X Y ≫ a.smul)).left := by
  let Y := T.X ⊗ X
  have h : lift (fst T.X Y) (snd T.X Y ≫ a.smul) = 𝟙 T.X ⊗ₘ a.smul := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [Y]
  change Flat (lift (fst T.X Y) (snd T.X Y ≫ a.smul)).left
  rw [h]
  let : Flat a.smul.left := isFlat_action a
  exact tensor_id_flat a.smul

private theorem productActionLift_flat (T : GroupScheme k) (X : SchemeOver k) :
    let Y := T.X ⊗ X
    Flat (lift (fst T.X Y * (snd T.X Y ≫ fst T.X X)) (snd T.X Y ≫ snd T.X X)).left := by
  let Y := T.X ⊗ X
  have h : lift (fst T.X Y * (snd T.X Y ≫ fst T.X X)) (snd T.X Y ≫ snd T.X X) =
      (α_ T.X T.X X).inv ≫ (μ[T.X] ⊗ₘ 𝟙 X) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, Category.assoc, tensorHom_fst, ← Category.assoc]
      change lift (fst T.X Y) (snd T.X Y ≫ fst T.X X) ≫ μ[T.X] = _
      apply congrArg (· ≫ μ[T.X])
      apply CartesianMonoidalCategory.hom_ext <;> simp [Y]
    · simp [Y]
  change Flat (lift (fst T.X Y * (snd T.X Y ≫ fst T.X X)) (snd T.X Y ≫ snd T.X X)).left
  rw [h]
  let : Flat (μ[T.X]).left := isFlat_action (ModObj.regular T.X)
  let : Flat (μ[T.X] ⊗ₘ 𝟙 X).left := id_tensor_flat μ[T.X]
  exact flat_comp_over (α_ T.X T.X X).inv (μ[T.X] ⊗ₘ 𝟙 X)

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Comparing coefficients at two independent universal elements shows
that each coefficient in the expansion is already a weight vector. -/
private theorem inverseCohomology_coefficients_weight (split : IsSplitTorus T)
    (hX : Specs.FlagCohomology.HasFiniteAffineCover X) [F.IsQuasicoherent]
    (L : Linearization a F) (n : ℕ)
    (E : (cohomology (T.X ⊗ X) n).obj (Pull (snd T.X X) F) ≃+
      (Character T →₀ (cohomology X n).obj F))
    (hE : ProjectionCohomologyExpansion T X F n E)
    (v : (cohomology X n).obj F) (χ : Character T) :
    inverseCohomologyCoefficients L n E (inverseCohomologyCoefficients L n E v χ) =
      Finsupp.single χ (inverseCohomologyCoefficients L n E v χ) := by
  classical
  let Y := T.X ⊗ X
  let Z := T.X ⊗ Y
  let p := snd T.X X
  let q := snd T.X Y
  let s := fst T.X Y
  let t := q ≫ fst T.X X
  let x := q ≫ p
  let y := actOn a t x
  let P := Pull p F
  let z := inverseCohomologyCoefficients L n E v
  have hq : q = lift t x := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [t, x, p]
  have hy : y = q ≫ a.smul := by
    change lift t x ≫ a.smul = q ≫ a.smul
    rw [← hq]
  letI : IsAffine T.X.left := torus_isAffine T split
  have pb := Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (fst T.X X) p) (tensorProductIsBinaryProduct T.X X)
  letI : IsAffineHom p.left :=
    MorphismProperty.of_isPullback pb (show IsAffineHom T.X.hom from inferInstance)
  letI : P.IsQuasicoherent := pullback_isQuasicoherent p.left F
  have hY := affinePullback_hasFiniteAffineCover p.left hX
  obtain ⟨D, hD⟩ := projectionCohomologyExpansion T split Y hY P n
  letI : Flat p.left := isFlat_projection T X
  letI : Flat q.left := isFlat_projection T Y
  letI : Flat a.smul.left := isFlat_action a
  letI : Flat x.left := flat_comp_over q p
  letI : Flat y.left := hy ▸ flat_comp_over q a.smul
  letI : Flat (lift s y).left := hy.symm ▸ nestedActionLift_flat a
  letI : Flat (lift (s * t) x).left := productActionLift_flat T X
  letI : Flat (actOn a s y).left := flat_comp_over (lift s y) a.smul
  letI : Flat (actOn a (s * t) x).left := flat_comp_over (lift (s * t) x) a.smul
  let B := cohomologyPull q (pullComp F q p).hom n
  let c (i : Character T) := s.left.appTop (characterFunction i)
  let d (i : Character T) := (fst T.X X).left.appTop (characterFunction i)
  let cₜ (i : Character T) := t.left.appTop (characterFunction i)
  let U := cohomologyPull p (𝟙 P) n
  let A := cohomologyPull a.smul L.iso.inv n
  let V := (cohomology X n).obj F
  let l (_ : Character T) (w : V) := A w
  let r (i : Character T) (w : V) := geometricScalar n (d i) (U w)
  let j (i : Character T) (w : (cohomology Y n).obj P) :=
    geometricScalar n (c i) (cohomologyPull q (𝟙 (Pull q P)) n w)
  have hB (w : (cohomology Y n).obj P) :
      B w = (cohomology Z n).map (pullComp F q p).hom (cohomologyPull q (𝟙 (Pull q P)) n w) := by
    have h := cohomologyPull_postcomp q (𝟙 (Pull q P)) (pullComp F q p).hom n
    rw [Category.id_comp] at h
    exact ConcreteCategory.congr_hom h w
  have hBj (i : Character T) (w : (cohomology Y n).obj P) :
      (cohomology Z n).map (pullComp F q p).hom (j i w) = geometricScalar n (c i) (B w) :=
    (ConcreteCategory.congr_hom (multiplyCohomology_natural (pullComp F q p).hom n (c i))
      (cohomologyPull q (𝟙 (Pull q P)) n w)).trans
      (congrArg (geometricScalar n (c i)) (hB w).symm)
  have hA (w : V) : B (A w) = inverseTransportOnCohomology L t x n w := by
    have h := inverseCohomology_pullback L n t x q hq rfl w
    have hc : (comparePull F q p (rfl : q ≫ p = x)).hom = (pullComp F q p).hom := by
      simp only [comparePull, Iso.trans_hom, pullCongr_refl, Category.comp_id]
    rwa [hc] at h
  have hP (w : V) : B (U w) = cohomologyPull x (𝟙 (Pull x F)) n w := by
    apply cohomologyPull_comp_apply p q x rfl
    rw [(Scheme.Modules.pullback q.left).map_id P, Category.id_comp, Category.comp_id]
    simp only [comparePull, Iso.trans_hom, pullCongr_refl, Category.comp_id]
  have hr (i : Character T) (w : V) :
      B (r i w) = geometricScalar n (cₜ i) (cohomologyPull x (𝟙 (Pull x F)) n w) := by
    have h := ConcreteCategory.congr_hom (cohomologyPull_multiply q (pullComp F q p).hom (d i) n) (U w)
    change B (r i w) = geometricScalar n (q.left.appTop (d i)) (B (U w)) at h
    rw [hP] at h
    have ht : q.left.appTop (d i) = cₜ i := (appTop_comp_apply q.left _ _).symm
    rwa [ht] at h
  have h := inverseCohomology_cocycle L n s t x v
  rw [inverseCohomology_expansion L n E hE s y, inverseCohomology_expansion L n E hE (s * t) x,
    Finsupp.sum, Finsupp.sum, map_sum] at h
  have hleft (i : Character T) (w : V) :
      (cohomology Z n).map (transport a L.iso t x).inv
        (geometricScalar n (c i) (cohomologyPull y (𝟙 (Pull y F)) n w)) =
      geometricScalar n (c i) (B (l i w)) := by
    have hn := ConcreteCategory.congr_hom (multiplyCohomology_natural (transport a L.iso t x).inv n (c i))
      (cohomologyPull y (𝟙 (Pull y F)) n w)
    change (cohomology Z n).map (transport a L.iso t x).inv
      (geometricScalar n (c i) (cohomologyPull y (𝟙 (Pull y F)) n w)) = geometricScalar n (c i)
      ((cohomology Z n).map (transport a L.iso t x).inv (cohomologyPull y (𝟙 (Pull y F)) n w)) at hn
    have hc := cohomologyPull_postcomp y (𝟙 (Pull y F)) (transport a L.iso t x).inv n
    rw [Category.id_comp] at hc
    exact hn.trans (congrArg (geometricScalar n (c i))
      ((ConcreteCategory.congr_hom hc w).symm.trans (hA w).symm))
  have hright (i : Character T) (w : V) :
      geometricScalar n ((s * t).left.appTop (characterFunction i)) (cohomologyPull x (𝟙 (Pull x F)) n w) =
      geometricScalar n (c i) (B (r i w)) := by
    rw [EquivariantAffineModules.characterFunction_at_mul, hr]
    have he := congrArg ((cohomology Z n).map)
      (EquivariantAffineModules.multiply_comp (Pull x F) (cₜ i) (c i))
    rw [CategoryTheory.Functor.map_comp] at he
    exact (ConcreteCategory.congr_hom he (cohomologyPull x (𝟙 (Pull x F)) n w)).symm
  have hs : z.sum (fun i w => j i (l i w)) = z.sum (fun i w => j i (r i w)) := by
    apply ((cohomology Z n).mapIso (pullComp F q p)).toLinearEquiv.injective
    change (cohomology Z n).map (pullComp F q p).hom (z.sum (fun i w => j i (l i w))) =
      (cohomology Z n).map (pullComp F q p).hom (z.sum (fun i w => j i (r i w)))
    simp only [Finsupp.sum, map_sum, hBj]
    exact (Finset.sum_congr rfl (fun i _ => hleft i (z i))).symm.trans
      (h.trans (Finset.sum_congr rfl (fun i _ => hright i (z i))))
  have coeff (q' : Character T) :
      l q' (z q') = r q' (z q') :=
    eq_of_weighted_sums D j hD z l r
      (fun _ => A.hom.map_zero)
      (fun i => by simp only [r, map_zero]) hs q'
  exact (congrArg E (coeff χ)).trans (hE χ (z χ))

end InverseTransportCohomology

section CohomologyWeightDecomposition

open scoped DirectSum
open private comparePull
  from LinearAlgebraicGroups.Representation.EquivariantAffineModules
open Specs.FlagCohomology (HasFiniteAffineCover)
open Scheme.Modules

private theorem projectionCohomology_injective
    {F : X.left.Modules} (n : ℕ)
    (E : (cohomology (T.X ⊗ X) n).obj (Pull (snd T.X X) F) ≃+
      (Character T →₀ (cohomology X n).obj F))
    (hE : ProjectionCohomologyExpansion T X F n E) :
    letI : Flat (snd T.X X).left := isFlat_projection T X
    Function.Injective (cohomologyPull (snd T.X X) (𝟙 (Pull (snd T.X X) F)) n) := by
  classical
  intro v w hv
  have he := congrArg (fun x => E (geometricScalar n
    ((fst T.X X).left.appTop (characterFunction (1 : Character T))) x)) hv
  rw [hE 1 v, hE 1 w] at he
  simpa only [Finsupp.single_eq_same] using DFunLike.congr_fun he 1

set_option backward.isDefEq.respectTransparency false in
private theorem inverseCohomologyCoefficients_injective {F : X.left.Modules}
    (L : Linearization a F) (n : ℕ)
    (E : (cohomology (T.X ⊗ X) n).obj (Pull (snd T.X X) F) ≃+
      (Character T →₀ (cohomology X n).obj F))
    (hE : ProjectionCohomologyExpansion T X F n E) :
    Function.Injective (inverseCohomologyCoefficients L n E) := by
  let Y := T.X ⊗ X
  let p := snd T.X X
  let s := (actionShear T a).inv
  have h : s ≫ a.smul = p := by
    rw [← actionShear_snd T a, Iso.inv_hom_id_assoc]
  letI : IsIso s.left := inferInstanceAs (IsIso ((Over.forget _).map s))
  letI : Flat p.left := isFlat_projection T X
  letI : Flat a.smul.left := isFlat_action a
  let e := (Scheme.Modules.pullback s.left).mapIso L.iso.symm
  let b := comparePull F s a.smul h
  let c := e.inv ≫ b.hom
  have hc (v : (cohomology X n).obj F) :
      cohomologyPull s c n (cohomologyPull a.smul L.iso.inv n v) =
        cohomologyPull p (𝟙 (Pull p F)) n v := by
    apply cohomologyPull_comp_apply a.smul s p h
    change b.hom ≫ 𝟙 _ = e.hom ≫ e.inv ≫ b.hom
    simp only [Category.comp_id, e.hom_inv_id_assoc]
  intro v w hv
  have hv' : cohomologyPull a.smul L.iso.inv n v = cohomologyPull a.smul L.iso.inv n w :=
    E.injective hv
  apply projectionCohomology_injective n E hE
  rw [← hc v, ← hc w, hv']

private theorem geometricScalar_mul {Y : SchemeOver k} (F : Y.left.Modules)
    (n : ℕ) (r s : Γ(Y.left, ⊤)) :
    geometricScalar (H := F) n r ≫ geometricScalar n s = geometricScalar n (s * r) := by
  rw [← Functor.map_comp, EquivariantAffineModules.multiply_comp]

private theorem geometricScalar_one {Y : SchemeOver k} (F : Y.left.Modules) (n : ℕ) :
    geometricScalar (H := F) n 1 = 𝟙 _ := by
  change (cohomology Y n).map (multiply F 1) = _
  rw [EquivariantAffineModules.multiply_one, (cohomology Y n).map_id]

set_option backward.isDefEq.respectTransparency false in
private theorem mem_weight_iff_inverseTransport (split : IsSplitTorus T)
    {F : EquivariantCoherent a} {n : ℕ} (m : CohomologyPullbacks F n)
    (χ : Character T) (v : (cohomology X n).obj F.sheaf) :
    letI : Flat (snd T.X X).left := isFlat_projection T X
    letI : Flat a.smul.left := isFlat_action a
    v ∈ cohomologyWeightSpace m χ ↔
      cohomologyPull a.smul F.lin.iso.inv n v =
        geometricScalar n ((fst T.X X).left.appTop (characterFunction χ⁻¹))
          (cohomologyPull (snd T.X X) (𝟙 (Pull (snd T.X X) F.sheaf)) n v) := by
  let Y := T.X ⊗ X
  let p := snd T.X X
  let P := Pull p F.sheaf
  let H := Pull a.smul F.sheaf
  letI : Flat p.left := isFlat_projection T X
  letI : Flat a.smul.left := isFlat_action a
  let b := (cohomology Y n).mapIso F.lin.iso
  let c (i : Character T) := (fst T.X X).left.appTop (characterFunction i)
  let u := cohomologyPull p (𝟙 P) n v
  let w := b.inv (m.viaAction v)
  have h₁ : m.viaProjection v = b.hom u := by
    rw [inducedCohomologyMap_unique _ _ n m.projection_induced
      (cohomologyPull_induced p F.lin.iso.hom n)]
    have h := cohomologyPull_postcomp p (𝟙 P) F.lin.iso.hom n
    rw [Category.id_comp] at h
    exact ConcreteCategory.congr_hom h v
  have h₂ : cohomologyPull a.smul F.lin.iso.inv n v = w := by
    change _ = b.inv (m.viaAction v)
    rw [inducedCohomologyMap_unique _ _ n m.action_induced
      (cohomologyPull_induced a.smul (𝟙 H) n)]
    have h := cohomologyPull_postcomp a.smul (𝟙 H) F.lin.iso.inv n
    rw [Category.id_comp] at h
    exact ConcreteCategory.congr_hom h v
  have hw : b.hom w = m.viaAction v := ConcreteCategory.congr_hom b.inv_hom_id _
  have hb := multiplyCohomology_natural F.lin.iso.hom n (c χ)
  rw [mem_cohomologyWeightSpace, h₁, ← hw, h₂]
  change b.hom u = geometricScalar n (c χ) (b.hom w) ↔
    w = geometricScalar n (c χ⁻¹) u
  rw [← show b.hom (geometricScalar n (c χ) w) = geometricScalar n (c χ) (b.hom w) from
    ConcreteCategory.congr_hom hb w]
  change b.toLinearEquiv u = b.toLinearEquiv (geometricScalar n (c χ) w) ↔
    w = geometricScalar n (c χ⁻¹) u
  rw [b.toLinearEquiv.injective.eq_iff]
  have hmul : c χ⁻¹ * c χ = 1 := by
    dsimp only [c]
    rw [← map_mul, ← EquivariantAffineModules.characterFunction_mul split,
      inv_mul_cancel, EquivariantAffineModules.characterFunction_one split, map_one]
  have comp (x : (cohomology Y n).obj P) :
      geometricScalar n (c χ⁻¹) (geometricScalar n (c χ) x) = x := by
    rw [← ModuleCat.comp_apply, geometricScalar_mul, hmul, geometricScalar_one]
    rfl
  have comp' (x : (cohomology Y n).obj P) :
      geometricScalar n (c χ) (geometricScalar n (c χ⁻¹) x) = x := by
    rw [← ModuleCat.comp_apply, geometricScalar_mul, mul_comm, hmul, geometricScalar_one]
    rfl
  exact ⟨fun h => (comp w).symm.trans (congrArg (geometricScalar n (c χ⁻¹)) h.symm),
    fun h => (comp' u).symm.trans (congrArg (geometricScalar n (c χ)) h.symm)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem mem_weight_iff_inverseCohomologyCoefficients (split : IsSplitTorus T)
    {F : EquivariantCoherent a} {n : ℕ} (m : CohomologyPullbacks F n)
    (E : (cohomology (T.X ⊗ X) n).obj (Pull (snd T.X X) F.sheaf) ≃+
      (Character T →₀ (cohomology X n).obj F.sheaf))
    (hE : ProjectionCohomologyExpansion T X F.sheaf n E)
    (χ : Character T) (v : (cohomology X n).obj F.sheaf) :
    v ∈ cohomologyWeightSpace m χ ↔
      inverseCohomologyCoefficients F.lin n E v = Finsupp.single χ⁻¹ v := by
  rw [mem_weight_iff_inverseTransport split m χ v, ← hE χ⁻¹ v]
  exact E.injective.eq_iff.symm

/-- Finite coefficient expansions into eigenspaces give the internal
direct sum of those eigenspaces. -/
private theorem internal_of_weightCoefficients {Λ V : Type u} [AddCommGroup V] [Module k V]
    [DecidableEq Λ] (D : V →+ Λ →₀ V) (hD : Function.Injective D)
    (W : Λ → Submodule k V)
    (hW : ∀ i v, v ∈ W i ↔ D v = Finsupp.single i v)
    (hc : ∀ i v, D v i ∈ W i) :
    DirectSum.IsInternal W := by
  let C := DirectSum.coeAddMonoidHom W
  have heval (i : Λ) (z : ⨁ j, W j) : D (C z) i = (z i : V) := by
    let S := AddSubmonoidClass.subtype (W i)
    let ev : (⨁ j, W j) →+ W i := DFinsupp.evalAddMonoidHom i
    have e : (Finsupp.applyAddHom i).comp (D.comp C) = S.comp ev := by
      apply DirectSum.addHom_ext
      intro j x
      change D (C (DirectSum.of (fun j => W j) j x)) i = _
      rw [DirectSum.coeAddMonoidHom_of, (hW j x).mp x.property, Finsupp.single_apply]
      change (if j = i then (x : V) else 0) = (DirectSum.of (fun j => W j) j x i : V)
      by_cases h : j = i <;> simpa [h] using (DirectSum.coe_of_apply j i x).symm
    exact DFunLike.congr_fun e z
  refine ⟨fun x y h => ?_, fun v => ?_⟩
  · ext i : 1
    apply Subtype.ext
    rw [← heval, ← heval, h]
  · let z := D v
    refine ⟨∑ i ∈ z.support, DirectSum.of (fun j => W j) i ⟨z i, hc i v⟩, ?_⟩
    apply hD
    rw [map_sum, map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    have h (i : Λ) : D (z i) = Finsupp.single i (z i) := (hW i _).mp (hc i v)
    simpa only [h, Finsupp.sum] using Finsupp.sum_single z

set_option backward.isDefEq.respectTransparency false in
theorem exists_cohomologyWeightGrading (split : IsSplitTorus T) (hX : HasFiniteAffineCover X)
    (F : EquivariantCoherent a) (n : ℕ) (m : CohomologyPullbacks F n) :
    ∃ G : WeightGrading k (Character T) ((cohomology X n).obj F.sheaf),
      ∀ χ, G.piece χ = cohomologyWeightSpace m χ := by
  classical
  letI := F.coherent.exists_quasicoherentData.choose.isQuasicoherent
  obtain ⟨E, hE⟩ := projectionCohomologyExpansion T split X hX F.sheaf n
  letI : Flat a.smul.left := isFlat_action a
  let V := (cohomology X n).obj F.sheaf
  let D : V →+ (Character T →₀ V) :=
    E.toAddMonoidHom.comp (cohomologyPull a.smul F.lin.iso.inv n).hom.toAddMonoidHom
  let W (χ : Character T) := cohomologyWeightSpace m χ⁻¹
  have hw (χ : Character T) (v : V) : v ∈ W χ ↔ D v = Finsupp.single χ v := by
    change _ ↔ inverseCohomologyCoefficients F.lin n E v = _
    rw [mem_weight_iff_inverseCohomologyCoefficients split m E hE, inv_inv]
  have hi : DirectSum.IsInternal W :=
    internal_of_weightCoefficients D (inverseCohomologyCoefficients_injective F.lin n E hE)
      W hw (fun χ v => (hw χ (D v χ)).mpr
        (inverseCohomology_coefficients_weight split hX F.lin n E hE v χ))
  refine ⟨⟨cohomologyWeightSpace m, ?_⟩, fun χ => rfl⟩
  apply (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
  refine ⟨?_, ?_⟩
  · have h := hi.submodule_iSupIndep.comp (Equiv.inv (Character T)).injective
    have he : W ∘ (Equiv.inv (Character T)) = cohomologyWeightSpace m := by
      funext χ
      change cohomologyWeightSpace m ((χ⁻¹)⁻¹) = _
      rw [inv_inv]
    exact he ▸ h
  · rw [← hi.submodule_iSup_eq_top]
    exact (Equiv.inv (Character T)).iSup_congr (fun χ => by simp)

end CohomologyWeightDecomposition

section ExactCohomology

variable (A B C : ℕ → ModuleCat.{u} k)
variable [∀ n, Module.Finite k (A n)] [∀ n, Module.Finite k (B n)]
variable [∀ n, Module.Finite k (C n)]

/-- The numerical contribution of a weight to the Euler characteristic is
additive in a bounded cohomology long exact sequence. -/
theorem alternatingFinrank_add
    (f : ∀ n, A n ⟶ B n) (g : ∀ n, B n ⟶ C n) (δ : ∀ n, C n ⟶ A (n + 1))
    (h0 : Function.Injective (f 0))
    (hB : ∀ n, Function.Exact (f n) (g n))
    (hC : ∀ n, Function.Exact (g n) (δ n))
    (hA : ∀ n, Function.Exact (δ n) (f (n + 1)))
    (N : ℕ) (hN : IsZero (A N)) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (Module.finrank k (B n) : ℤ)) =
      (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (Module.finrank k (A n) : ℤ)) +
      (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (Module.finrank k (C n) : ℤ)) := by
  let r (n : ℕ) : ℤ := Module.finrank k (LinearMap.ker (f n).hom)
  have hr0 : r 0 = 0 := by
    simp [r, LinearMap.ker_eq_bot.mpr h0]
  have hrN : r N = 0 := by
    let : Subsingleton (A N) := ModuleCat.isZero_iff_subsingleton.mp hN
    simp [r, Module.finrank_zero_of_subsingleton]
  have hdim (n : ℕ) :
      (Module.finrank k (A n) : ℤ) - (Module.finrank k (B n) : ℤ) +
        (Module.finrank k (C n) : ℤ) = r n + r (n + 1) := by
    have hf := (f n).hom.finrank_range_add_finrank_ker
    have hg := (g n).hom.finrank_range_add_finrank_ker
    have hd := (δ n).hom.finrank_range_add_finrank_ker
    have eqB := (hB n).linearMap_ker_eq
    have eqC := (hC n).linearMap_ker_eq
    have eqA := (hA n).linearMap_ker_eq
    change LinearMap.ker (g n).hom = LinearMap.range (f n).hom at eqB
    change LinearMap.ker (δ n).hom = LinearMap.range (g n).hom at eqC
    change LinearMap.ker (f (n + 1)).hom = LinearMap.range (δ n).hom at eqA
    rw [eqB] at hg
    rw [eqC, ← eqA] at hd
    unfold r
    omega
  have htelescope (m : ℕ) :
      (∑ n ∈ Finset.range m, (-1 : ℤ) ^ n * (r n + r (n + 1))) =
        r 0 - (-1 : ℤ) ^ m * r m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  have hsum :
      ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
        ((Module.finrank k (A n) : ℤ) - (Module.finrank k (B n) : ℤ) +
          (Module.finrank k (C n) : ℤ)) = 0 := by
    simp only [hdim, htelescope, hr0, hrN, mul_zero, sub_zero]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  linarith

end ExactCohomology

section EulerConstruction

open private weightProject weightProject_of_mem weightProject_natural
  gradedCharacter gradedCharacter_coeff
  from LinearAlgebraicGroups.Representation.EquivariantAffineModules

variable (m : ∀ (F : EquivariantCoherent a) (n : ℕ), CohomologyPullbacks F n)
variable (G : ∀ (F : EquivariantCoherent a) (n : ℕ),
  WeightGrading k (Character T) ((cohomology X n).obj F.sheaf))
variable (hG : ∀ F n χ, (G F n).piece χ = cohomologyWeightSpace (m F n) χ)
variable (hfin : ∀ (F : EquivariantCoherent a) (n : ℕ),
  Module.Finite k ((cohomology X n).obj F.sheaf))

private def degreeCharacter (F : EquivariantCoherent a) (n : ℕ) : CharacterRing T :=
  letI := hfin F n
  gradedCharacter (G F n)

include m hG

/-- A grading by the actual universal cohomology weights yields its
finite-dimensional character. -/
theorem isCohomologyCharacter_of_weightGrading (F : EquivariantCoherent a) (n : ℕ) :
    IsCohomologyCharacter F n (degreeCharacter G hfin F n) := by
  let := hfin F n
  exact ⟨hfin F n, m F n, fun χ => (gradedCharacter_coeff (G F n) χ).trans
    (congrArg (fun V : Submodule k ((cohomology X n).obj F.sheaf) =>
      (Module.finrank k V : ℤ)) (hG F n χ))⟩

private def alternatingCharacter (N : ℕ) (F : EquivariantCoherent a) : CharacterRing T :=
  ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n • degreeCharacter G hfin F n

theorem isEulerCharacter_of_weightGrading (N : ℕ) (F : EquivariantCoherent a)
    (hN : ∀ n ≥ N, IsZero ((cohomology X n).obj F.sheaf)) :
    IsEulerCharacter F (alternatingCharacter G hfin N F) :=
  ⟨N, degreeCharacter G hfin F, isCohomologyCharacter_of_weightGrading m G hG hfin F, hN, rfl⟩

omit m hG

private theorem weightRestrict_exact
    {V W U : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup U] [Module k U]
    (GV : WeightGrading k (Character T) V) (GW : WeightGrading k (Character T) W)
    (GU : WeightGrading k (Character T) U) (f : V →ₗ[k] W) (g : W →ₗ[k] U)
    (hf : PreservesWeight GV GW f) (hg : PreservesWeight GW GU g)
    (h : Function.Exact f g) (χ : Character T) :
    Function.Exact (f.restrict (hf χ)) (g.restrict (hg χ)) := by
  intro y
  constructor
  · intro hy
    have hy' : g y = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (h y).mp hy'
    refine ⟨weightProject GV χ x, ?_⟩
    exact (weightProject_natural GV GW f hf χ x).trans <|
      (congrArg (weightProject GW χ) hx).trans (weightProject_of_mem GW χ y)
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((h (f x)).mpr ⟨x, rfl⟩)

/-- If the cohomology long exact sequence preserves weights, finite
alternating characters are additive. -/
theorem alternatingCharacter_add_of_exact
    {F H K : EquivariantCoherent a}
    (f : F.sheaf ⟶ H.sheaf) (g : H.sheaf ⟶ K.sheaf)
    (δ : ∀ n, (cohomology X n).obj K.sheaf ⟶ (cohomology X (n + 1)).obj F.sheaf)
    (hf : ∀ n, PreservesWeight (G F n) (G H n) ((cohomology X n).map f).hom)
    (hg : ∀ n, PreservesWeight (G H n) (G K n) ((cohomology X n).map g).hom)
    (hδ : ∀ n, PreservesWeight (G K n) (G F (n + 1)) (δ n).hom)
    (h0 : Function.Injective ((cohomology X 0).map f))
    (hH : ∀ n, Function.Exact ((cohomology X n).map f) ((cohomology X n).map g))
    (hK : ∀ n, Function.Exact ((cohomology X n).map g) (δ n))
    (hF : ∀ n, Function.Exact (δ n) ((cohomology X (n + 1)).map f))
    (N : ℕ) (hN : IsZero ((cohomology X N).obj F.sheaf)) :
    alternatingCharacter G hfin N H =
      alternatingCharacter G hfin N F + alternatingCharacter G hfin N K := by
  classical
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro χ
  let A i := ModuleCat.of k ((G F i).piece χ)
  let B i := ModuleCat.of k ((G H i).piece χ)
  let C i := ModuleCat.of k ((G K i).piece χ)
  let (i : ℕ) := hfin F i
  let (i : ℕ) := hfin H i
  let (i : ℕ) := hfin K i
  let (i : ℕ) : Module.Finite k (A i) := inferInstanceAs (Module.Finite k ((G F i).piece χ))
  let (i : ℕ) : Module.Finite k (B i) := inferInstanceAs (Module.Finite k ((G H i).piece χ))
  let (i : ℕ) : Module.Finite k (C i) := inferInstanceAs (Module.Finite k ((G K i).piece χ))
  let f' (i : ℕ) : A i ⟶ B i := ModuleCat.ofHom (((cohomology X i).map f).hom.restrict (hf i χ))
  let g' (i : ℕ) : B i ⟶ C i := ModuleCat.ofHom (((cohomology X i).map g).hom.restrict (hg i χ))
  let δ' (i : ℕ) : C i ⟶ A (i + 1) := ModuleCat.ofHom ((δ i).hom.restrict (hδ i χ))
  have hzero : IsZero (A N) := by
    let : Subsingleton ((cohomology X N).obj F.sheaf) := ModuleCat.isZero_iff_subsingleton.mp hN
    exact ModuleCat.isZero_iff_subsingleton.mpr (inferInstanceAs (Subsingleton ((G F N).piece χ)))
  have h := alternatingFinrank_add A B C f' g' δ'
    (fun x y eq => Subtype.ext (h0 (congrArg Subtype.val eq)))
    (fun n => weightRestrict_exact _ _ _ _ _ (hf n) (hg n) (hH n) χ)
    (fun n => weightRestrict_exact _ _ _ _ _ (hg n) (hδ n) (hK n) χ)
    (fun n => weightRestrict_exact _ _ _ _ _ (hδ n) (hf (n + 1)) (hF n) χ) N hzero
  have hterm (F : EquivariantCoherent a) (n : ℕ) :
      (((-1 : ℤ) ^ n) • degreeCharacter G hfin F n).coeff χ =
        (-1 : ℤ) ^ n * (Module.finrank k ((G F n).piece χ) : ℤ) := by
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply]
    change (-1 : ℤ) ^ n * (degreeCharacter G hfin F n).coeff χ = _
    simp only [degreeCharacter, gradedCharacter_coeff]
  simpa only [alternatingCharacter, MonoidAlgebra.coeff_add, Finsupp.add_apply,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, hterm, A, B, C] using h

/-- The cutoff sum is compatible with a shift of all cohomology weights. -/
theorem alternatingCharacter_twist
    {F H : EquivariantCoherent a} (χ : Character T) (N : ℕ)
    (e : ∀ n ψ, (G H n).piece (χ * ψ) ≃ₗ[k] (G F n).piece ψ) :
    alternatingCharacter G hfin N H = eChar χ • alternatingCharacter G hfin N F := by
  classical
  have h (n : ℕ) : degreeCharacter G hfin H n = eChar χ * degreeCharacter G hfin F n := by
    ext ψ
    change (degreeCharacter G hfin H n).coeff ψ =
      (MonoidAlgebra.single χ 1 * degreeCharacter G hfin F n).coeff ψ
    rw [MonoidAlgebra.coeff_single_mul_apply, one_mul]
    simp only [degreeCharacter, gradedCharacter_coeff]
    have h := (e n (χ⁻¹ * ψ)).finrank_eq
    rw [mul_inv_cancel_left] at h
    exact_mod_cast h
  unfold alternatingCharacter
  simp only [h, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact (mul_smul_comm ((-1 : ℤ) ^ n) (eChar χ) (degreeCharacter G hfin F n)).symm


/-- The additive and twist-compatible signed character descends uniquely
through the presentation by short exact sequences and character twists. -/
theorem exists_eulerMap_of_relations
    (hex : ∀ {F H K : EquivariantCoherent a}
      (f : F.sheaf ⟶ H.sheaf) (g : H.sheaf ⟶ K.sheaf) (w : f ≫ g = 0),
      EquivariantHom f → EquivariantHom g → (ShortComplex.mk f g w).ShortExact →
      ∀ {cF cH cK}, IsEulerCharacter F cF → IsEulerCharacter H cH →
        IsEulerCharacter K cK → cH = cF + cK)
    (htw : ∀ {χ : Character T} {F H : EquivariantCoherent a},
      IsTwist χ F H → ∀ {cF cH}, IsEulerCharacter F cF → IsEulerCharacter H cH →
        cH = eChar χ • cF)
    (hexists : ∀ F : EquivariantCoherent a, ∃ c, IsEulerCharacter F c) :
    ∃! E : GZero a →ₗ[CharacterRing T] CharacterRing T,
      ∀ F, IsEulerCharacter F (E (classOf F)) := by
  classical
  choose value hvalue using hexists
  let exactRelation {F H K} f g w hf hg h :=
    hex (F := F) (H := H) (K := K) f g w hf hg h (hvalue F) (hvalue H) (hvalue K)
  let twistRelation {χ F H} h :=
    htw (χ := χ) (F := F) (H := H) h (hvalue F) (hvalue H)
  let L := EquivariantAffineModules.liftClassMap value @exactRelation @twistRelation
  have hL (F : EquivariantCoherent a) : IsEulerCharacter F (L (classOf F)) := by
    simpa only [L, EquivariantAffineModules.liftClassMap_classOf] using hvalue F
  exact ⟨L, hL, fun E hE => EquivariantAffineModules.classMap_ext (fun F =>
    eulerCharacter_unique F (hE F) (hL F))⟩

end EulerConstruction

section FlagEuler

open Specs.FlagCohomology (HasFiniteAffineCover)

set_option backward.isDefEq.respectTransparency false in
/-- The finite signed characters of the split torus on flag cohomology
define the character-ring linear Euler map. -/
theorem flagEulerMap : FlagEulerMap.{u} := by
  classical
  intro k _ G P Q a _
  let t := torusAction P.torus a
  let T := P.torus.group
  letI : IsAffine T.X.left := torus_isAffine T P.split
  have hX : HasFiniteAffineCover Q.scheme :=
    FlagCohomology.finiteAffineCover Q.scheme
      ((LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q).2.1
  obtain ⟨hfin, N, hN⟩ := flagCoherentCohomologyFinite P Q t
  let m (F : EquivariantCoherent t) (n : ℕ) := (cohomologyPullbacks_nonempty F n).some
  choose grading hgrading using fun (F : EquivariantCoherent t) (n : ℕ) =>
    exists_cohomologyWeightGrading P.split hX F n (m F n)
  let value (F : EquivariantCoherent t) := alternatingCharacter grading hfin N F
  have hvalue (F : EquivariantCoherent t) : IsEulerCharacter F (value F) :=
    isEulerCharacter_of_weightGrading m grading hgrading hfin N F (hN F)
  have hex {F H K : EquivariantCoherent t}
      (f : F.sheaf ⟶ H.sheaf) (g : H.sheaf ⟶ K.sheaf) (w : f ≫ g = 0)
      (hf : EquivariantHom f) (hg : EquivariantHom g) (he : (ShortComplex.mk f g w).ShortExact) :
      value H = value F + value K := by
    obtain ⟨δ, ⟨h0, hH, hK, hF⟩, hd⟩ := equivariantCohomology_longExact hX f g w hf hg he m
    apply alternatingCharacter_add_of_exact grading hfin f g δ _ _ _ h0 hH hK hF N (hN F N le_rfl)
    · intro n χ v hv
      rw [hgrading] at hv ⊢
      exact equivariantHom_preserves_cohomologyWeights _ _ f hf χ hv
    · intro n χ v hv
      rw [hgrading] at hv ⊢
      exact equivariantHom_preserves_cohomologyWeights _ _ g hg χ hv
    · intro n χ v hv
      rw [hgrading] at hv ⊢
      exact hd n χ v hv
  let E := EquivariantAffineModules.liftClassMap value @hex
    (fun {χ F H} hh => eulerCharacter_unique H (hvalue H)
      (isEulerCharacter_twist P.split χ hh (hvalue F)))
  have hE (F : EquivariantCoherent t) : IsEulerCharacter F (E (classOf F)) := by
    simpa only [E, EquivariantAffineModules.liftClassMap_classOf] using hvalue F
  refine ⟨E, hE, fun x F hx _ hF => ?_⟩
  letI : IsClosedImmersion x.left := hx
  exact eulerCharacter_unique F (hE F) (pointEulerCharacter P.split x F hF)

end FlagEuler

section UniversalCharacterEvaluation

open private act_extend_natural characterValue_natural
  from LinearAlgebraicGroups.Representation.RootWeightAction
open Specs.RootWeightAction (Representation act extendVector weightSpace mem_weightSpace)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open private appTop_comp_apply appTop_Spec_map
  from LinearAlgebraicGroups.Representation.EquivariantAffineModules

set_option backward.isDefEq.respectTransparency false in
private theorem characterValue_eval (R : TestAlgebra k) (t : GroupPoints T R) (χ : Character T) :
    (Scheme.ΓSpecIso (affineRing R)).hom (t.left.appTop (characterFunction χ)) =
      characterValue χ R t := by
  let B := MonoidAlgebra k IntegerCharacters
  let g : CommAlgCat.of k B ⟶ R :=
    ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (t ≫ χ.hom.hom)).unop
  have hg : (testSpec k).map g.op = t ≫ χ.hom.hom :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  have hle : Spec.map (CommRingCat.ofHom g.hom.toRingHom) = (t ≫ χ.hom.hom).left :=
    congrArg Over.Hom.left hg
  change (Scheme.ΓSpecIso (affineRing R)).hom
      (t.left.appTop (χ.hom.hom.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv
        (MonoidAlgebra.of k _ integerGenerator)))) = g.hom _
  rw [← appTop_comp_apply, ← Over.comp_left]
  have he := congrArg (fun f : Spec (affineRing R) ⟶ Spec (CommRingCat.of B) =>
    f.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (MonoidAlgebra.of k _ integerGenerator))) hle
  refine (congrArg (fun z => (Scheme.ΓSpecIso (affineRing R)).hom z) he.symm).trans ?_
  rw [appTop_Spec_map]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (affineRing R)).inv_hom_id _

private theorem characterFunction_inversePoint (split : IsSplitTorus T)
    {Y : SchemeOver k} (t : Y ⟶ T.X) (χ : Character T) :
    (t⁻¹).left.appTop (characterFunction χ⁻¹) = t.left.appTop (characterFunction χ) := by
  let b := t.left.appTop (characterFunction χ)
  let c := t.left.appTop (characterFunction χ⁻¹)
  let d := (t⁻¹).left.appTop (characterFunction χ⁻¹)
  have hb : b * c = 1 := by
    dsimp only [b, c]
    rw [← map_mul, ← EquivariantAffineModules.characterFunction_mul split, mul_inv_cancel,
      EquivariantAffineModules.characterFunction_one split, map_one]
  have hd : c * d = 1 := by
    dsimp only [c, d]
    rw [← EquivariantAffineModules.characterFunction_at_mul, mul_inv_cancel,
      EquivariantAffineModules.characterFunction_at_one]
  change d = b
  calc
    d = (b * c) * d := by rw [hb, one_mul]
    _ = b := by rw [mul_assoc, hd, mul_one]

set_option backward.isDefEq.respectTransparency false in
private theorem weightSpace_at_universal {G : AffineAlgebraicGroup k}
    {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I)
    (T : ClosedSubgroup G.val) (R : TestAlgebra k) (j : affineScheme R ≅ T.group.X)
    (χ : Character T.group) (v : I → k) :
    v ∈ weightSpace ρ T χ ↔
      act ρ R (j.hom ≫ T.inclusion.hom.hom) (extendVector R v) =
        characterValue χ R j.hom • extendVector R v := by
  rw [mem_weightSpace]
  refine ⟨fun h => h R j.hom, fun h S t => ?_⟩
  let b : R ⟶ S := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (t ≫ j.inv)).unop
  have hb : (testSpec k).map b.op = t ≫ j.inv :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  have hj : mapPoints b j.hom = t := by
    change (testSpec k).map b.op ≫ j.hom = t
    exact (congrArg (· ≫ j.hom) hb).trans
      ((Category.assoc (t : affineScheme S ⟶ T.group.X) j.inv j.hom).trans
        (by rw [j.inv_hom_id, Category.comp_id]))
  have hact := act_extend_natural ρ b (j.hom ≫ T.inclusion.hom.hom) v
  have hc := characterValue_natural χ b j.hom
  rw [h] at hact
  rw [hj] at hc
  have ht : mapPoints b (j.hom ≫ T.inclusion.hom.hom) = t ≫ T.inclusion.hom.hom := by
    change (testSpec k).map b.op ≫ j.hom ≫ T.inclusion.hom.hom = _
    exact (Category.assoc ((testSpec k).map b.op) j.hom T.inclusion.hom.hom).symm.trans
      (congrArg (· ≫ T.inclusion.hom.hom) hj)
  rw [ht] at hact
  funext i
  have hi := congrFun hact i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, extendVector, AlgHom.commutes] at hi ⊢
  rw [← hc] at hi
  exact hi

end UniversalCharacterEvaluation

section DerivedTransportComparison

open Specs.FlagCohomology (extendScheme extendToAlgebra extensionProjection extensionProjection_over
  IsCohomologyMap groundRingHom)
open Scheme.Modules
open private projectionToOriginal projectionToTestScheme extensionAsSchemeOverField
  from Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private extensionProductIso extensionProductIso_snd extensionProductIso_fst
  from LinearAlgebraicGroups.Representation.FlagCovarianceLinearization
open private comparePull transport_symm_eq_eval appTop_comp_apply
  from LinearAlgebraicGroups.Representation.EquivariantAffineModules
open private cohomologyMap_natural
  from LinearAlgebraicGroups.Representation.CoherentCohomologyAlgebraBaseChange

variable {R : TestAlgebra k}
private def inversePointCoefficient {F : X.left.Modules} (L : Linearization a F)
    (t : GroupPoints T R) (f : (extensionAsSchemeOverField R X) ⟶ (extensionAsSchemeOverField R X))
    (w : f ≫ (projectionToOriginal R X) = actOn a ((projectionToTestScheme R X) ≫ t) (projectionToOriginal R X))
    {M : ((extendScheme R).obj X).left.Modules} (e : Pull (projectionToOriginal R X) F ≅ M) :
    (Scheme.Modules.pullback f.left).obj M ⟶ M :=
  (Scheme.Modules.pullback f.left).map e.inv ≫ (pullComp F f (projectionToOriginal R X)).hom ≫
    (pullCongr F w).hom ≫ (transport a L.iso ((projectionToTestScheme R X) ≫ t) (projectionToOriginal R X)).inv ≫ e.hom

set_option backward.isDefEq.respectTransparency false in
private theorem cohomologyPull_comp_toAlgebra_apply
    {Y : SchemeOver k} {Z : Specs.FlagCohomology.SchemeOverRing R}
    (f : Y ⟶ X) (g : Z.left ⟶ Y.left) (p : Z.left ⟶ X.left)
    [Flat f.left] [Flat g] (w : g ≫ f.left = p)
    (wg : g ≫ Y.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (wp : p ≫ X.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))
    {F : X.left.Modules} {H : Y.left.Modules} {K : Z.left.Modules}
    (c : Pull f F ⟶ H) (d : (Scheme.Modules.pullback g).obj H ⟶ K)
    (b : (Scheme.Modules.pullback p).obj F ⟶ K)
    (hb : (pullbackComp g f.left).hom.app F ≫ (pullbackCongr w).hom.app F ≫ b =
      (Scheme.Modules.pullback g).map c ≫ d) (n : ℕ) {m r}
    (hm : IsCohomologyMap (algebraMap k R) g wg (cohomologyAdjoint g d) n m)
    (hr : IsCohomologyMap (algebraMap k R) p wp (cohomologyAdjoint p b) n r)
    (v : (cohomology X n).obj F) : m (cohomologyPull f c n v) = r v := by
  have h := cohomologyPull_induced f c n
  unfold InducesOnCohomology at h
  exact induced_comp_apply (X := X) (Y := Y) (Z := Z) (RingHom.id k)
    (algebraMap k R) (algebraMap k R) (RingHom.comp_id _) f.left g p w _ wg wp c d b hb n h hm hr v

set_option maxHeartbeats 1100000 in
set_option backward.isDefEq.respectTransparency false in
private theorem cohomologyInversePoint_comparison
    {F : X.left.Modules} (L : Linearization a F) (j : affineScheme R ≅ T.X)
    (f : (extensionAsSchemeOverField R X) ⟶ (extensionAsSchemeOverField R X)) [Flat f.left] (w : f ≫ (projectionToOriginal R X) = actOn a ((projectionToTestScheme R X) ≫ j.hom) (projectionToOriginal R X))
    (wf : f.left ≫ ((extendScheme R).obj X).hom = ((extendScheme R).obj X).hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)))
    {M : ((extendScheme R).obj X).left.Modules} (e : Pull (projectionToOriginal R X) F ≅ M) (n : ℕ)
    (b : (extendToAlgebra (k := k) (K := R)).obj ((cohomology X n).obj F) ≅
      (cohomology ((extendScheme R).obj X) n).obj M)
    (hb : IsCohomologyMap (algebraMap k R) (extensionProjection R X) (extensionProjection_over R X)
      (cohomologyAdjoint (extensionProjection R X) e.hom) n
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ b.hom))
    (m : (cohomology ((extendScheme R).obj X) n).obj M ⟶ (cohomology ((extendScheme R).obj X) n).obj M)
    (hm : IsCohomologyMap (RingHom.id R) f.left wf
      (cohomologyAdjoint f.left (inversePointCoefficient L j.hom f w e)) n
      (m ≫ (ModuleCat.restrictScalarsId'App (RingHom.id R) rfl _).inv))
    (χ : Character T) (v : (cohomology X n).obj F) :
    let p := snd T.X X
    letI : Flat p.left := isFlat_projection T X
    letI : Flat a.smul.left := isFlat_action a
    let b₀ := (ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ b.hom
    cohomologyPull a.smul L.iso.inv n v =
        geometricScalar n ((fst T.X X).left.appTop (characterFunction χ))
          (cohomologyPull p (𝟙 (Pull p F)) n v) ↔
      m (b₀ v) = characterValue χ R j.hom • (show (cohomology ((extendScheme R).obj X) n).obj M from b₀ v) := by
  let Y : SchemeOver k := T.X ⊗ X
  let Z := (extendScheme R).obj X
  let p : Y ⟶ X := snd T.X X
  let q : (extensionAsSchemeOverField R X) ⟶ Y := (extensionProductIso j X).hom
  let t := (projectionToTestScheme R X) ≫ j.hom
  let H : Y.left.Modules := Pull p F
  have hp : q ≫ p = (projectionToOriginal R X) := extensionProductIso_snd j X
  have hq : q = lift t (projectionToOriginal R X) := rfl
  let u := actOn a t (projectionToOriginal R X)
  have ha : q ≫ a.smul = u := by rw [hq]
  let P := comparePull F q p hp
  let C : (Scheme.Modules.pullback q.left).obj H ≅ M := P ≪≫ e
  have wq : q.left ≫ Y.hom = ((extendScheme R).obj X).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) :=
    Over.w q
  let : IsIso q.left := inferInstanceAs (IsIso ((Over.forget _).map q))
  obtain ⟨J, hJ⟩ := exists_inducedIso (Z := Y) (Y := ((extendScheme R).obj X)) (algebraMap k R) q.left wq C n
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap k R)
  let b₀ := adj.homEquiv _ _ b.hom
  let : Flat (projectionToOriginal R X).left := FlatCohomology.flatScalarExtension k R X
  let : Flat p.left := isFlat_projection T X
  let : Flat a.smul.left := isFlat_action a
  let A := cohomologyPull a.smul L.iso.inv n
  let B := cohomologyPull p (𝟙 H) n
  let d := (fst T.X X).left.appTop (characterFunction χ)
  have hB : J.hom (B v) = b₀ v := by
    refine cohomologyPull_comp_toAlgebra_apply (Z := Z) p q.left (projectionToOriginal R X).left
      (congrArg Over.Hom.left hp) wq (extensionProjection_over R X) (𝟙 H) C.hom e.hom ?_ n hJ hb v
    change P.hom ≫ e.hom = (Scheme.Modules.pullback q.left).map (𝟙 H) ≫ C.hom
    rw [(Scheme.Modules.pullback q.left).map_id, Category.id_comp]
    rfl
  have hA : J.hom (A v) = m (b₀ v) := by
    let c := (transport a L.iso t (projectionToOriginal R X)).inv ≫ e.hom
    let φ := algebraMap k R
    have wu : u.left ≫ X.hom = ((extendScheme R).obj X).hom ≫ Spec.map (CommRingCat.ofHom φ) := Over.w u
    let : Flat u.left := ha ▸ flat_comp_over q a.smul
    obtain ⟨r, hr⟩ := flatCohomologyMap_bridge (X := X) (Y := ((extendScheme R).obj X))
      φ u.left wu (cohomologyAdjoint u.left c) n
    have h₁ : J.hom (A v) = r v := by
      refine cohomologyPull_comp_toAlgebra_apply (Z := Z) a.smul q.left u.left
        (congrArg Over.Hom.left ha) wq wu L.iso.inv C.hom c ?_ n hJ hr v
      change (comparePull F q a.smul ha).hom ≫ c =
        (Scheme.Modules.pullback q.left).map L.iso.inv ≫ C.hom
      have he := congrArg Iso.hom (transport_symm_eq_eval L.iso t (projectionToOriginal R X))
      have he' : (transport a L.iso t (projectionToOriginal R X)).inv = (comparePull F q a.smul ha).inv ≫
          (Scheme.Modules.pullback q.left).map L.iso.inv ≫ P.hom := by
        exact he
      simp only [c, he', Category.assoc, Iso.hom_inv_id_assoc, C, Iso.trans_hom]
    have h₂ : m (b₀ v) = r v := by
      refine induced_comp_apply (X := X) (Y := Z) (Z := Z) φ (RingHom.id R) φ
        (RingHom.id_comp _) (projectionToOriginal R X).left f.left u.left
        (congrArg Over.Hom.left w) _ wf wu e.hom (inversePointCoefficient L j.hom f w e)
        c ?_ n hb hm hr v
      change (pullComp F f (projectionToOriginal R X)).hom ≫ (pullCongr F w).hom ≫ c =
        (Scheme.Modules.pullback f.left).map e.hom ≫ inversePointCoefficient L j.hom f w e
      have invId : (Scheme.Modules.pullback f.left).map e.hom ≫
          (Scheme.Modules.pullback f.left).map e.inv = 𝟙 _ :=
        ((Scheme.Modules.pullback f.left).mapIso e).hom_inv_id
      simp only [inversePointCoefficient, reassoc_of% invId, c, t]
    exact h₁.trans h₂.symm
  have hd : q.left.appTop d = groundRingHom ((extendScheme R).obj X) (characterValue χ R j.hom) := by
    change q.left.appTop ((fst T.X X).left.appTop (characterFunction χ)) = _
    rw [← appTop_comp_apply, ← Over.comp_left, extensionProductIso_fst j X, Over.comp_left,
      appTop_comp_apply]
    unfold groundRingHom
    change ((extendScheme R).obj X).hom.appTop (j.hom.left.appTop (characterFunction χ)) =
      ((extendScheme R).obj X).hom.appTop ((Scheme.ΓSpecIso (affineRing R)).inv (characterValue χ R j.hom))
    rw [← characterValue_eval R j.hom χ]
    exact congrArg ((extendScheme R).obj X).hom.appTop
      (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (affineRing R)).hom_inv_id _).symm
  let r := characterValue χ R j.hom
  have hmul : geometricScalar n d ≫ J.hom =
      J.hom ≫ (ModuleCat.restrictScalars (algebraMap k R)).map
        ((cohomology ((extendScheme R).obj X) n).map (FlagCohomology.sheafScalarMap ((extendScheme R).obj X) r M)) := by
    refine cohomologyMap_natural (X := Y) (Y := Z) (algebraMap k R) q.left wq (multiply H d)
      (FlagCohomology.sheafScalarMap Z r M) (α := cohomologyAdjoint q.left C.hom)
      (α' := cohomologyAdjoint q.left C.hom) ?_ n hJ hJ
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
    congr 1
    have hscalar : FlagCohomology.sheafScalarMap Z r M =
        multiply (X := extensionAsSchemeOverField R X) M (groundRingHom Z r) := rfl
    rw [EquivariantAffineModules.pullback_multiply, hd, hscalar,
      EquivariantAffineModules.multiply_natural]
  rw [FlagCohomology.cohomology_map_scalar] at hmul
  have h := ConcreteCategory.congr_hom hmul (B v)
  change J.hom (geometricScalar n d (B v)) = r • (show (cohomology ((extendScheme R).obj X) n).obj M from J.hom (B v)) at h
  rw [hB] at h
  change A v = geometricScalar n d (B v) ↔ m (b₀ v) = r • (show (cohomology ((extendScheme R).obj X) n).obj M from b₀ v)
  rw [← h, ← hA]
  exact J.toLinearEquiv.injective.eq_iff.symm

end DerivedTransportComparison

section FlagLineCohomology

open scoped TensorProduct ChangeOfRings
open Scheme.Modules
open Specs.FlagCohomology (FlagKernelPair flagLineData flagLineSheaf CohomologyBasis
  CohomologyIndex IsFlagCohomologyAction IsCohomologyMap extendScheme extendToAlgebra
  extensionProjection extensionProjection_over pointTranslation_over extendedCoordinates)
open Specs.FlagCovarianceLinearization (AgreesWithFlagCohomologyAction)
open Specs.RootWeightAction (Representation act extendVector weightSpace)
open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private translationArrow pointTranslation_isIso
  from LinearAlgebraicGroups.Representation.FlagCohomology
open private coefficientFormula from LinearAlgebraicGroups.Representation.FormalCharacters

private theorem extendedCoordinates_of_unit {I : Type u} [Fintype I]
    (R : TestAlgebra k) {V : ModuleCat.{u} k} (b : Module.Basis I k V) (v : V) :
    extendedCoordinates R b
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).unit.app V v) =
      extendVector R (b.equivFun v) := by
  letI : Algebra k R := (algebraMap k R).toAlgebra
  funext i
  change (b.baseChange R).equivFun ((1 : R) ⊗ₜ[k] v) i = algebraMap k R (b.equivFun v i)
  rw [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul, Module.Basis.equivFun_apply]
  simp [Algebra.smul_def]

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {aG : ModObj G.val.X Q.scheme}
variable {p : BorelProjection P} {χ : Character P.torus.group} {h : FlagKernelPair Q}

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem flagLineCohomology_weight
    (ℓ : Linearization (torusAction P.torus aG) (flagLineSheaf Q p χ h))
    (hℓ : AgreesWithFlagCohomologyAction Q aG p χ h ℓ)
    (hF : (flagLineSheaf Q p χ h).IsFinitePresentation)
    (n : ℕ) (b : CohomologyBasis (p := p) (χ := χ) h n)
    (ρ : Representation G.val (CohomologyIndex (p := p) (χ := χ) h n))
    (hρ : IsFlagCohomologyAction h aG n b ρ)
    (m₀ : CohomologyPullbacks (⟨_, hF, ℓ⟩ : EquivariantCoherent (torusAction P.torus aG)) n)
    (ψ : Character P.torus.group) (v : (cohomology Q.scheme n).obj (flagLineSheaf Q p χ h)) :
    v ∈ cohomologyWeightSpace m₀ ψ ↔ b.equivFun v ∈ weightSpace ρ P.torus ψ := by
  let T := P.torus.group
  let X := Q.scheme
  let F := flagLineSheaf Q p χ h
  obtain ⟨R₀, ⟨j⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr (torus_isAffine T P.split)
  let R : TestAlgebra k := R₀.unop
  let j' : affineScheme R ≅ T.X := j ≪≫ asIso (ι[T.X])
  have hj' : j'.hom = j.hom⁻¹ := rfl
  let Y := (extendScheme R).obj X
  let D := flagLineData Q p χ h
  let M := (D.extend R).sheaf
  obtain ⟨E⟩ := FlagCohomology.flagCohomologyBaseChange Q p χ h R
  let π := projectionToOriginal R X
  let e : Pull π F ≅ M := @asIso _ _ _ _ _ E.sheafIso
  let g : GroupPoints G.val R := j.hom ≫ P.torus.inclusion.hom.hom
  let f := translationArrow R aG.smul g⁻¹
  let : IsIso f.left := @pointTranslation_isIso _ _ R _ _ _ aG g⁻¹
  obtain ⟨w, hw⟩ := hℓ R j.hom E
  obtain ⟨m, hm, hc⟩ := hw n
  let y := projectionToTestScheme R X
  have w' : f ≫ π = actOn (torusAction P.torus aG) (y ≫ j'.hom) π := by
    rw [hj']
    exact w
  let c := inversePointCoefficient ℓ j'.hom f w' e
  have hm' : IsCohomologyMap (RingHom.id R) f.left (pointTranslation_over aG.smul R g⁻¹)
      (cohomologyAdjoint f.left c) n
      (m ≫ (ModuleCat.restrictScalarsId'App (RingHom.id R) rfl _).inv) := by
    exact hm
  let B := (ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ (E.iso n).hom
  have hb : IsCohomologyMap (algebraMap k R) π.left (extensionProjection_over R X)
      (cohomologyAdjoint π.left e.hom) n B := by
    have he : cohomologyAdjoint π.left e.hom = E.coefficientMap :=
      Equiv.apply_symm_apply _ _
    rw [he]
    exact E.induced n
  rw [mem_weight_iff_inverseTransport P.split m₀ ψ v]
  have hmcomp := cohomologyInversePoint_comparison ℓ j' f w'
    (pointTranslation_over aG.smul R g⁻¹) e n (E.iso n) hb m hm' ψ⁻¹ v
  dsimp only at hmcomp
  rw [hmcomp, weightSpace_at_universal ρ P.torus R j]
  have hχ : characterValue ψ⁻¹ R j'.hom = characterValue ψ R j.hom := by
    rw [← characterValue_eval, ← characterValue_eval, hj']
    exact congrArg (fun z => (Scheme.ΓSpecIso (affineRing R)).hom z)
      (characterFunction_inversePoint P.split j.hom ψ)
  rw [hχ]
  let d := (E.iso n).toLinearEquiv.symm.trans (extendedCoordinates R b)
  have hB : d (B v) = extendVector R (b.equivFun v) := by
    change d ((E.iso n).hom ((ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).unit.app _ v)) = _
    change extendedCoordinates R b ((E.iso n).toLinearEquiv.symm ((E.iso n).toLinearEquiv _)) = _
    rw [LinearEquiv.symm_apply_apply]
    exact extendedCoordinates_of_unit R b v
  have hC : d (m (B v)) = act ρ R g (d (B v)) := hc b ρ hρ (B v)
  constructor
  · intro h
    rw [← hB, ← hC, h, _root_.map_smul]
  · intro h
    apply d.injective
    rw [hC, _root_.map_smul, hB]
    exact h

set_option backward.isDefEq.respectTransparency false in
/-- The character computed from the linearization on the covariance
sheaf is the character of the specified rational flag cohomology action. -/
private theorem flagLineCohomology_character
    (ℓ : Linearization (torusAction P.torus aG) (flagLineSheaf Q p χ h))
    (hℓ : AgreesWithFlagCohomologyAction Q aG p χ h ℓ)
    (hF : (flagLineSheaf Q p χ h).IsFinitePresentation)
    (n : ℕ) (b : CohomologyBasis (p := p) (χ := χ) h n)
    (ρ : Representation G.val (CohomologyIndex (p := p) (χ := χ) h n))
    (hρ : IsFlagCohomologyAction h aG n b ρ) :
    IsCohomologyCharacter (⟨_, hF, ℓ⟩ : EquivariantCoherent (torusAction P.torus aG)) n
      (Specs.FormalCharacters.formalCharacter P.torus ρ) := by
  let F : EquivariantCoherent (torusAction P.torus aG) := ⟨_, hF, ℓ⟩
  obtain ⟨m⟩ := cohomologyPullbacks_nonempty F n
  refine ⟨Module.Finite.of_surjective b.equivFun.symm.toLinearMap b.equivFun.symm.surjective,
    m, fun ψ => ?_⟩
  rw [(coefficientFormula P.torus P.split ρ).2 ψ]
  unfold Specs.FormalCharacters.multiplicity
  have e : (cohomologyWeightSpace m ψ).map b.equivFun.toLinearMap = weightSpace ρ P.torus ψ := by
    ext v
    obtain ⟨w, rfl⟩ := b.equivFun.surjective v
    rw [Submodule.mem_map_equiv]
    simpa only [LinearEquiv.symm_apply_apply] using flagLineCohomology_weight ℓ hℓ hF n b ρ hρ m ψ w
  exact congrArg (fun d : ℕ => (d : ℤ)) (b.equivFun.ofSubmodules _ _ e).finrank_eq.symm

end FlagLineCohomology

section CovarianceCoordinates

open Scheme.Modules
open Specs.FlagCohomology (CovarianceData FlagKernelPair flagLineData flagLineSheaf
  flagTransition structureModule pullbackRegular)
open private pullCongr_refl
  from LinearAlgebraicGroups.Representation.EquivariantAffineModules
open private overPullbackRegular
  from Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private pullbackOnOpen pullbackOnOpen_comp pullbackOnOpen_congr pullbackOnOpen_restrict_global
  overPullbackRegular_app pullbackRegular_app firstLeft_w secondLeft_w
  covariance_app_eq_zero regularSection_mem_covariance
  from LinearAlgebraicGroups.Representation.FlagCohomology
open private pushforwardCongr_refl
  from LinearAlgebraicGroups.Representation.CoherentCohomologyAlgebraBaseChange
open private transpose_comp
  from LinearAlgebraicGroups.Representation.FlagCovarianceLinearization

variable {Z : SchemeOver k}

set_option backward.isDefEq.respectTransparency false in
private def regularPull (f : Z ⟶ X) : Pull f (structureModule X.left) ≅ structureModule Z.left := by
  letI : (SheafOfModules.pushforward f.left.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f.left).IsRightAdjoint
  let G := TopologicalSpace.Opens.map f.left.base
  let E := CategoryTheory.Functor.fromPUnit.{0} (⊤ : X.left.Opens)
  letI : E.Final := CategoryTheory.Functor.final_fromPUnit_of_isTerminal isTerminalTop
  have ht : IsTerminal (G.obj (⊤ : X.left.Opens)) := by
    change IsTerminal (⊤ : Z.left.Opens)
    exact isTerminalTop
  letI : (CategoryTheory.Functor.fromPUnit.{0} (G.obj (⊤ : X.left.Opens))).Final :=
    CategoryTheory.Functor.final_fromPUnit_of_isTerminal ht
  letI : (E ⋙ G).Final := CategoryTheory.Functor.final_of_natIso
    (F := CategoryTheory.Functor.fromPUnit.{0} (G.obj (⊤ : X.left.Opens)))
    (Discrete.natIso (fun _ => Iso.refl _))
  letI : G.Final :=
    CategoryTheory.Functor.final_of_final_comp E G
  exact @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit (F := G) f.left.toRingCatSheafHom)
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (F := G) f.left.toRingCatSheafHom)

set_option backward.isDefEq.respectTransparency false in
private theorem regularPull_induced (f : Z ⟶ X) :
    cohomologyAdjoint f.left (regularPull f).hom = pullbackRegular f.left := by
  let : (SheafOfModules.pushforward f.left.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f.left).IsRightAdjoint
  change (SheafOfModules.pullbackPushforwardAdjunction f.left.toRingCatSheafHom).homEquiv _ _
    (SheafOfModules.pullbackObjUnitToUnit f.left.toRingCatSheafHom) = _
  rw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro z
  exact (pullbackRegular_app f.left U (show Γ(X.left, U) from z)).symm

private def covarianceCoordinate (D : CovarianceData X) (g : Z ⟶ D.torsor)
    (x : Z ⟶ X) (w : g ≫ D.projection = x) :
    Pull x D.sheaf ⟶ structureModule Z.left :=
  ((pullbackPushforwardAdjunction x.left).homEquiv _ _).symm
    (D.inclusion ≫ overPullbackRegular D.projection.left x.left g.left
      (congrArg Over.Hom.left w))

set_option backward.isDefEq.respectTransparency false in
private theorem covarianceCoordinate_congr (D : CovarianceData X) (g : Z ⟶ D.torsor)
    {x x' : Z ⟶ X} (w : g ≫ D.projection = x) (w' : x = x') :
    (pullCongr D.sheaf w').hom ≫ covarianceCoordinate D g x' (w.trans w') =
      covarianceCoordinate D g x w := by
  subst x'
  rw [pullCongr_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem flagLineCoordinate_eq_covarianceCoordinate
    {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G} (Q : Presentation P.negative)
    (p : BorelProjection P) (χ : Character P.torus.group) (h : FlagKernelPair Q) (g : Z ⟶ G.val.X) :
    flagLineCoordinate Q p χ h g =
      covarianceCoordinate (flagLineData Q p χ h) g (g ≫ Q.projection) rfl := by
  let D := flagLineData Q p χ h
  unfold covarianceCoordinate overPullbackRegular flagLineCoordinate
  have hr : (pushforwardCongr (rfl : g.left ≫ Q.projection.left =
      g.left ≫ Q.projection.left)).hom.app (structureModule Z.left) = 𝟙 _ :=
    pushforwardCongr_refl _ _
  change _ = ((pullbackPushforwardAdjunction (g.left ≫ Q.projection.left)).homEquiv _ _).symm
    (D.inclusion ≫ (pushforward Q.projection.left).map (pullbackRegular g.left) ≫
      (pushforwardComp g.left Q.projection.left).hom.app _ ≫
      (pushforwardCongr (rfl : g.left ≫ Q.projection.left = g.left ≫ Q.projection.left)).hom.app _)
  rw [hr, Category.comp_id, transpose_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem covarianceCoordinate_comp (D : CovarianceData X) (g : Z ⟶ D.torsor)
    {W : SchemeOver k} (f : W ⟶ Z) :
    covarianceCoordinate D (f ≫ g) (f ≫ (g ≫ D.projection)) (Category.assoc f g D.projection) =
        (pullComp D.sheaf f (g ≫ D.projection)).inv ≫
        (Scheme.Modules.pullback f.left).map (covarianceCoordinate D g (g ≫ D.projection) rfl) ≫
        (regularPull f).hom := by
  let x := g ≫ D.projection
  let A := pullbackPushforwardAdjunction (f ≫ x).left
  apply (A.homEquiv _ _).injective
  unfold covarianceCoordinate
  rw [Equiv.apply_symm_apply]
  have hw := cohomologyAdjoint_comp x.left f.left (rfl : f.left ≫ x.left = (f ≫ x).left)
    (((pullbackPushforwardAdjunction x.left).homEquiv _ _).symm
      (D.inclusion ≫ overPullbackRegular D.projection.left x.left g.left rfl)) (regularPull f).hom
  have hi : (pullbackCongr (rfl : f.left ≫ x.left = f.left ≫ x.left)).inv.app D.sheaf = 𝟙 _ := rfl
  rw [hi, Category.id_comp, pushforwardCongr_refl, Category.comp_id, regularPull_induced] at hw
  dsimp only [cohomologyAdjoint] at hw
  rw [Equiv.apply_symm_apply] at hw
  refine Eq.trans ?_ hw
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforward_map_app,
    overPullbackRegular_app]
  let z : Γ(D.torsor.left, D.projection.left ⁻¹ᵁ U) := D.inclusion.app U s
  let v := pullbackOnOpen D.projection.left x.left g.left rfl U z
  change pullbackOnOpen D.projection.left (f ≫ x).left (f.left ≫ g.left)
    (Category.assoc _ _ _) U z =
    (pullbackRegular f.left).app (x.left ⁻¹ᵁ U) v
  refine (ConcreteCategory.congr_hom
    (pullbackOnOpen_comp D.projection.left x.left (f ≫ x).left g.left f.left rfl rfl U) z).symm.trans ?_
  exact (congrArg (fun q => q v) (Scheme.Hom.appLE_eq_app f.left)).trans
    (pullbackRegular_app f.left _ v).symm

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem covarianceCoordinate_overlap (D : CovarianceData X) (j : Z ⟶ D.overlap)
    (x : Z ⟶ X) (w : j ≫ D.overlapProjection = x) :
    let w₀ : (j ≫ D.first) ≫ D.projection = x :=
      (Category.assoc _ _ _).trans ((congrArg (j ≫ ·) D.fst_w).trans w)
    let w₁ : (j ≫ D.second) ≫ D.projection = x :=
      (Category.assoc _ _ _).trans ((congrArg (j ≫ ·) D.snd_w).trans w)
    covarianceCoordinate D (j ≫ D.second) x w₁ =
      covarianceCoordinate D (j ≫ D.first) x w₀ ≫
        multiply (structureModule Z.left) (j.left.appTop D.multiplier) := by
  intro w₀ w₁
  let A := pullbackPushforwardAdjunction x.left
  let q := D.projection.left
  let r := D.overlapProjection.left
  let J := j.left
  let b₀ := D.first.left
  let b₁ := D.second.left
  let c := J.appTop D.multiplier
  apply (A.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [A, covarianceCoordinate, Equiv.apply_symm_apply]
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  let z : Γ(D.torsor.left, q ⁻¹ᵁ U) := D.inclusion.app U s
  let W := x.left ⁻¹ᵁ U
  let e := pullbackOnOpen r x.left J (congrArg Over.Hom.left w) U
  have h := (covariance_app_eq_zero D U z).mp (regularSection_mem_covariance D U s)
  have he := congrArg (fun z => e z) h
  change _ = e (_ * _) at he
  rw [map_mul] at he
  have h₀ := ConcreteCategory.congr_hom
    (pullbackOnOpen_comp q r x.left b₀ J (firstLeft_w D) (congrArg Over.Hom.left w) U) z
  have h₁ := ConcreteCategory.congr_hom
    (pullbackOnOpen_comp q r x.left b₁ J (secondLeft_w D) (congrArg Over.Hom.left w) U) z
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforward_map_app, overPullbackRegular_app]
  change pullbackOnOpen q x.left (J ≫ b₁) (congrArg Over.Hom.left w₁) U z =
    Z.left.presheaf.map W.leTop.op c *
      pullbackOnOpen q x.left (J ≫ b₀) (congrArg Over.Hom.left w₀) U z
  rw [← h₁, ← h₀, mul_comm]
  rw [pullbackOnOpen_restrict_global r x.left J (congrArg Over.Hom.left w) U] at he
  exact he

end CovarianceCoordinates

section PointCoordinate

open Scheme.Modules
open Specs.FlagCohomology (structureModule FlagKernelPair flagLineData flagLineSheaf openScheme
  openInclusion bundleSectionCoordinate)
open private bundleChartsOnOpens chartToCovariance sectionsOfChart
  bundleCoordinateMap bundleCoordinateMap_graph bundleGraph coordinate_agrees restrictOver
  restrictOver_inclusion lineCoordinate_testPoint lineCoordinate_linePoint
  overPullbackRegular_app preimage_le pullbackOnOpen ChartLinearity openLineCoordinate
  lineCoordinate_openLineCoordinate_symm chartTrivializationIso
  from LinearAlgebraicGroups.Representation.FlagCohomology
open private sectionsSubsingleton_bot from LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness
open private overPullbackRegular openRestriction
  from Specs.LinearAlgebraicGroups.Representation.FlagCohomology

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {aG : ModObj G.val.X Q.scheme}
variable {p : BorelProjection P} {χ : Character P.torus.group} {h : FlagKernelPair Q}

private def liftIntoOpen {X Y : SchemeOver k} (x : Y ⟶ X) (U : X.left.Opens)
    (hx : ∀ z : Y.left, x.left z ∈ U) : Y ⟶ openScheme X U :=
  letI le : Set.range x.left ⊆ Set.range U.ι := by
    rw [U.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hx z
  Over.homMk (IsOpenImmersion.lift U.ι x.left le) (by
    change IsOpenImmersion.lift U.ι x.left le ≫ U.ι ≫ X.hom = Y.hom
    rw [IsOpenImmersion.lift_fac_assoc, Over.w x])

private theorem liftIntoOpen_comp {X Y : SchemeOver k} (x : Y ⟶ X) (U : X.left.Opens)
    (hx : ∀ z : Y.left, x.left z ∈ U) :
    liftIntoOpen x U hx ≫ openInclusion X U = x :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac ..)

private theorem affineBasePoint_left (k : Type u) [Field k] :
    (toUnit (affineScheme (CommAlgCat.of k k))).left = 𝟙 (Spec (CommRingCat.of k)) := by
  have hw := Over.w (toUnit (affineScheme (CommAlgCat.of k k)))
  change _ ≫ 𝟙 (Spec (CommRingCat.of k)) = Spec.map (𝟙 (CommRingCat.of k)) at hw
  exact (Category.comp_id _).symm.trans (hw.trans (Spec.map_id _))

set_option backward.isDefEq.respectTransparency false in
private theorem basePointLineHom_isIso (F : (basePoint k).left.Modules)
    (e : F ≅ structureModule (basePoint k).left) (f : F ⟶ structureModule (basePoint k).left)
    (hf : f ≠ 0) : IsIso f := by
  let Pt := basePoint k
  let : Subsingleton Pt.left := basePoint_subsingleton
  let M := structureModule Pt.left
  let g : M ⟶ M := e.inv ≫ f
  let r : Γ(Pt.left, ⊤) := g.app ⊤ (1 : Γ(Pt.left, ⊤))
  have hg : g = multiply M r := by
    apply Scheme.Modules.hom_ext
    intro U
    rcases TopologicalSpace.Opens.eq_bot_or_top U with hU | hU
    · subst U
      apply ConcreteCategory.hom_ext
      intro z
      exact @Subsingleton.elim (M.val.obj (op ⊥)) (sectionsSubsingleton_bot M) _ _
    · subst U
      apply ConcreteCategory.hom_ext
      intro z
      change g.app ⊤ z = (multiply M r).val.app (op ⊤) z
      rw [EquivariantAffineModules.multiply_app_top]
      let rone : Γ(M, ⊤) := (1 : Γ(Pt.left, ⊤))
      let c : Γ(Pt.left, ⊤) := z
      have h := g.app_smul (U := ⊤) c rone
      change g.app ⊤ (show Γ(Pt.left, ⊤) from c * 1) = c * r at h
      rw [show c * (1 : Γ(Pt.left, ⊤)) = c from mul_one c] at h
      exact h.trans (mul_comm c r)
  have h0 : r ≠ 0 := by
    intro h
    apply hf
    have hz : multiply M r = 0 := by
      rw [h]
      apply Scheme.Modules.hom_ext
      intro U
      apply ConcreteCategory.hom_ext
      intro z
      change (Pt.left.presheaf.map U.leTop.op) (0 : Γ(Pt.left, ⊤)) • z = (0 : Γ(M, U))
      rw [map_zero, zero_smul]
    exact (cancel_epi e.inv).mp (hg.trans hz |>.trans (comp_zero (f := e.inv)).symm)
  let a := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hu : IsUnit (a r) := isUnit_iff_ne_zero.mpr (fun e => h0 (a.injective (e.trans (map_zero a).symm)))
  have hr : IsUnit r := (MulEquiv.isUnit_map a).mp hu
  let u := hr.unit
  have he : multiply M r = (EquivariantAffineModules.multiplyUnit M u).hom :=
    congrArg (multiply M) hr.unit_spec.symm
  let : IsIso g := by rw [hg, he]; infer_instance
  have ht : f = e.hom ≫ g := by simp only [g, Iso.hom_inv_id_assoc]
  rw [ht]
  infer_instance

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
private theorem chartGenerator_at_lift (L : AssociatedBundle Q aG p χ)
    {W : Q.scheme.left.Opens} {t : openScheme Q.scheme W ⨯ affineLine k ⟶ L.total}
    (ht : IsPullback prod.fst t (openInclusion Q.scheme W) L.projection)
    (hl : ChartLinearity t) (g : basePoint k ⟶ G.val.X)
    (hg : ∀ z : (basePoint k).left, (g ≫ Q.projection).left z ∈ W) :
    let D := flagLineData Q p χ h
    let V := Q.projection.left ⁻¹ᵁ W
    let s := chartToCovariance h ht (𝟙 W) 1
    let hV : (⊤ : (basePoint k).left.Opens) ≤ g.left ⁻¹ᵁ V := fun z _ => hg z
    IsUnit (g.left.appLE V ⊤ hV (D.inclusion.app W s)) := by
  intro D V s hV
  let g' := liftIntoOpen g V (fun z => hV (show z ∈ ⊤ from trivial))
  let A := openScheme G.val.X V
  let i := openInclusion G.val.X V
  have hgi : g' ≫ i = g := liftIntoOpen_comp g V _
  let q := restrictOver Q.projection W V le_rfl
  let Z := sectionsOfChart ht (𝟙 W) 1
  let z := bundleCoordinateMap L W Z
  have hs : D.inclusion.app W s = V.topIso.hom (FlagCohomology.lineCoordinate z) := by
    rw [← FlagCohomology.bundleSectionsOnOpen_coordinate h W L]
    change bundleSectionCoordinate L W ((FlagCohomology.bundleSectionsOnOpen h W L)
      ((FlagCohomology.bundleSectionsOnOpen h W L).symm (sectionsOfChart ht (𝟙 W) 1))) = _
    rw [Equiv.apply_symm_apply, coordinate_agrees]
  have hι : V.ι.appLE V ⊤ V.ι_preimage_self.ge = V.topIso.inv := by
    simp only [Scheme.Opens.ι, Scheme.ofRestrict_appLE, Scheme.Opens.topIso_inv]
    congr 2
  have hap : g.left.appLE V ⊤ hV (D.inclusion.app W s) =
      g'.left.appTop (FlagCohomology.lineCoordinate z) := by
    have hcomp := Scheme.Hom.appLE_comp_appLE g'.left V.ι V ⊤ ⊤
      V.ι_preimage_self.ge (by simp)
    have he' : g'.left.appLE ⊤ ⊤ le_rfl = g'.left.appTop := Scheme.Hom.appLE_eq_app g'.left
    rw [hι, he'] at hcomp
    have hcongr {f f' : (basePoint k).left ⟶ G.val.X.left} (e : f = f')
        (hf : ⊤ ≤ f ⁻¹ᵁ V) (hf' : ⊤ ≤ f' ⁻¹ᵁ V) :
        f.appLE V ⊤ hf = f'.appLE V ⊤ hf' := by
      subst f'
      rfl
    have he : g'.left ≫ V.ι = g.left := congrArg Over.Hom.left hgi
    rw [hcongr he _ hV] at hcomp
    rw [← hcomp, CommRingCat.comp_apply, hs]
    exact congrArg (fun v => g'.left.appTop v)
      (ConcreteCategory.congr_hom V.topIso.hom_inv_id (FlagCohomology.lineCoordinate z))
  rw [hap]
  let R := CommAlgCat.of k k
  let e : affineScheme R ⟶ basePoint k := toUnit _
  let u : Points A R := e ≫ g'
  let g₀ : Points G.val.X R := e ≫ g
  let x := u ≫ q
  have hg₀ : u ≫ i = g₀ := (Category.assoc _ _ _).trans (congrArg (e ≫ ·) hgi)
  have hq : q ≫ openInclusion Q.scheme W = i ≫ Q.projection :=
    restrictOver_inclusion Q.projection W V le_rfl
  have hx : x ≫ openInclusion Q.scheme W = g₀ ≫ Q.projection := by
    change (u ≫ q) ≫ _ = _
    rw [Category.assoc u q, hq, ← Category.assoc u i, hg₀]
  obtain ⟨c, hc⟩ := hl R x g₀ hx
  have hgraph := congrArg (u ≫ ·) (bundleCoordinateMap_graph L W Z)
  change u ≫ (prod.lift i z ≫ L.trivialization) = u ≫ q ≫ Z.val at hgraph
  simp only [← Category.assoc, prod.comp_lift] at hgraph
  have hZ : Z.val = prod.lift (𝟙 _) ((openLineCoordinate Q.scheme W).symm 1) ≫ t := by
    change prod.lift (openRestriction Q.scheme (𝟙 W))
      ((openLineCoordinate Q.scheme W).symm 1) ≫ t = _
    congr 2
    apply Over.OverMorphism.ext
    exact Q.scheme.left.homOfLE_rfl W
  have oneCoord : x ≫ (openLineCoordinate Q.scheme W).symm 1 = linePoint R 1 := by
    rw [lineCoordinate_testPoint]
    congr 1
    rw [lineCoordinate_openLineCoordinate_symm, map_one, map_one, map_one]
  have hh : prod.lift g₀ (u ≫ z) ≫ L.trivialization =
      prod.lift g₀ (linePoint R (c : R)) ≫ L.trivialization := by
    calc
      _ = x ≫ Z.val := by simpa only [hg₀, x, Category.assoc] using hgraph
      _ = prod.lift x (linePoint R 1) ≫ t := by rw [hZ, ← Category.assoc, prod.comp_lift,
        Category.comp_id, oneCoord]
      _ = _ := by simpa only [mul_one] using hc 1
  have hz := congrArg (fun a => FlagCohomology.lineCoordinate
    (a ≫ (prod.snd : G.val.X ⨯ affineLine k ⟶ affineLine k)))
    (L.trivializes.hom_ext (by simp) hh)
  simp only [prod.lift_snd] at hz
  rw [FlagCohomology.lineCoordinate_comp, lineCoordinate_linePoint] at hz
  have hui : u.left = g'.left := by
    change e.left ≫ g'.left = g'.left
    exact (congrArg (· ≫ g'.left) (affineBasePoint_left k)).trans (Category.id_comp _)
  have hz' : g'.left.appTop (FlagCohomology.lineCoordinate z) =
      (Scheme.ΓSpecIso (affineRing R)).inv (c : R) :=
    (congrArg (fun f => f.appTop (FlagCohomology.lineCoordinate z)) hui).symm.trans hz
  exact hz'.symm ▸ c.isUnit.map (Scheme.ΓSpecIso (affineRing R)).inv.hom

private theorem appLE_top_eq_zero {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (U : Z.Opens) (V : Y.Opens) (hV : V = ⊤)
    (a : Γ(Z, U)) (h₁ : V ≤ g ⁻¹ᵁ U) (h₂ : ⊤ ≤ g ⁻¹ᵁ U)
    (h : g.appLE U V h₁ a = 0) :
    g.appLE U ⊤ h₂ a = 0 := by
  subst V
  exact h

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
/-- The regular coordinate on the covariance sheaf is a trivialization
of the ordinary fiber at the chosen lift. -/
private theorem flagLineCoordinate_point_isIso (L : AssociatedBundle Q aG p χ)
    (g : basePoint k ⟶ G.val.X) :
    IsIso (flagLineCoordinate Q p χ h g) := by
  let x := g ≫ Q.projection
  let D := flagLineData Q p χ h
  let y₀ : (basePoint k).left := IsLocalRing.closedPoint k
  obtain ⟨U, t, hU, ht, hl⟩ := bundleChartsOnOpens L (x.left y₀)
  have hx (y : (basePoint k).left) : x.left y ∈ U :=
    (basePoint_subsingleton.elim y₀ y) ▸ hU
  let y := liftIntoOpen x U hx
  let j := openInclusion Q.scheme U
  let F := (Scheme.Modules.overEquiv U).functor
  let Hj : D.sheaf.restrict U.ι ≅ structureModule U.toScheme :=
    ((Scheme.Modules.overFunctorEquiv U).app D.sheaf).symm ≪≫
      F.mapIso (chartTrivializationIso h ht hl).symm ≪≫
      U.sheafOfModulesEquivOverUnit Q.scheme.left.ringCatSheaf
  let e := (pullCongr D.sheaf (liftIntoOpen_comp x U hx).symm) ≪≫
    (pullComp D.sheaf y j).symm ≪≫ (Scheme.Modules.pullback y.left).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app D.sheaf).symm ≪≫ Hj) ≪≫ regularPull y
  apply basePointLineHom_isIso _ e
  rw [flagLineCoordinate_eq_covarianceCoordinate]
  intro hz
  let A := pullbackPushforwardAdjunction x.left
  let α := D.inclusion ≫ overPullbackRegular Q.projection.left x.left g.left rfl
  have hzero : α = 0 := by
    have hc := congrArg (A.homEquiv D.sheaf (structureModule (basePoint k).left)) hz
    have he : A.homEquiv D.sheaf (structureModule (basePoint k).left) (0 : Pull x D.sheaf ⟶ _) = 0 := by
      rw [Adjunction.homEquiv_unit, (pushforward x.left).map_zero, comp_zero]
    exact (Equiv.apply_symm_apply _ _).symm.trans (hc.trans he)
  let s := chartToCovariance h ht (𝟙 U) 1
  have hc : pullbackOnOpen Q.projection.left x.left g.left rfl U (D.inclusion.app U s) = 0 := by
    have ha := ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f U) hzero) s
    simp only [α, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Scheme.Modules.Hom.zero_app, ModuleCat.hom_zero, LinearMap.zero_apply] at ha
    exact (overPullbackRegular_app Q.projection.left x.left g.left rfl U
      (D.inclusion.app U s)).symm.trans ha
  have htop : x.left ⁻¹ᵁ U = ⊤ := top_unique fun y _ => hx y
  have hu := chartGenerator_at_lift (h := h) L ht hl g hx
  have hzero' := appLE_top_eq_zero g.left (Q.projection.left ⁻¹ᵁ U) (x.left ⁻¹ᵁ U)
    htop (D.inclusion.app U s) (preimage_le _ _ _ rfl _) (fun y _ => hx y) hc
  let : Nontrivial Γ((basePoint k).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
  exact hu.ne_zero hzero'

end PointCoordinate

section WeylFiberCharacter

open Specs.FlagCohomology (CovarianceData FlagKernelPair flagLineData flagLineSheaf flagTransition
  structureModule cohomologyZero HasFiniteAffineCover)
open Scheme.Modules
open private evalPullIso evalPullIso_comp_congr transport_eq_evalPullIso appTop_comp_apply
  equivariant_actOn
  from LinearAlgebraicGroups.Representation.EquivariantAffineModules
open private compareTransport TransportMatches
  from LinearAlgebraicGroups.Representation.FlagCovarianceLinearization
open private quotient_right_mul
  from LinearAlgebraicGroups.Representation.FlagLineBundle

private theorem evalPullIso_transport_target {Z : SchemeOver k}
    {F : X.left.Modules} (ℓ : Linearization a F)
    (s : Z ⟶ T.X) (x y : Z ⟶ X) (l : Z ⟶ T.X ⊗ X) (hl : l = lift s x)
    (hp : l ≫ snd T.X X = x) (hw : l ≫ a.smul = y)
    (e : actOn a s x = y) :
    (evalPullIso ℓ.iso l hp hw).hom =
      (transport a ℓ.iso s x).hom ≫ (pullCongr F e).hom := by
  subst l
  rw [transport_eq_evalPullIso]
  exact (evalPullIso_comp_congr ℓ.iso (lift s x) (lift_snd s x) rfl e).symm



set_option maxHeartbeats 700000 in
set_option backward.isDefEq.respectTransparency false in
private theorem terminalPullback_multiply {F : X.left.Modules} (ℓ : Linearization a F)
    (x : basePoint k ⟶ X) (hx : IsEquivariantMap a (terminalAction T) x)
    (w : actOn a (fst T.X (basePoint k)) (snd T.X (basePoint k) ≫ x) = snd T.X (basePoint k) ≫ x)
    (c : Pull (snd T.X (basePoint k) ≫ x) F ⟶ structureModule (T.X ⊗ basePoint k).left)
    [IsIso c] (r : Γ((T.X ⊗ basePoint k).left, ⊤))
    (h : (transport a ℓ.iso (fst T.X (basePoint k)) (snd T.X (basePoint k) ≫ x)).hom ≫
      (pullCongr F w).hom ≫ c = c ≫ multiply (structureModule (T.X ⊗ basePoint k).left) r) :
    (EquivariantAffineModules.pullbackLinearizationIso hx ℓ.iso).hom =
      multiply (Pull (snd T.X (basePoint k)) (Pull x F)) r := by
  let Z := T.X ⊗ basePoint k
  let y : Z ⟶ basePoint k := snd T.X (basePoint k)
  let s := fst T.X (basePoint k)
  let x' := y ≫ x
  let v : Z ⟶ T.X ⊗ X := 𝟙 T.X ⊗ₘ x
  have hv : v = lift s x' := by
    apply CartesianMonoidalCategory.hom_ext
    · change (𝟙 T.X ⊗ₘ x) ≫ fst T.X X = lift s x' ≫ fst T.X X
      rw [tensorHom_fst, Category.comp_id, lift_fst]
    · change (𝟙 T.X ⊗ₘ x) ≫ snd T.X X = lift s x' ≫ snd T.X X
      rw [tensorHom_snd, lift_snd]
  let e := (pullComp F y x).hom
  let τ := (EquivariantAffineModules.pullbackLinearizationIso hx ℓ.iso).hom
  have hτ : τ ≫ e = e ≫ (transport a ℓ.iso s x').hom ≫ (pullCongr F w).hom := by
    have hvp : v ≫ snd T.X X = x' := tensorHom_snd (𝟙 T.X) x
    have hva : v ≫ a.smul = x' := hx.symm
    change (e ≫ (evalPullIso ℓ.iso v hvp hva).hom ≫ (pullComp F y x).inv) ≫
      (pullComp F y x).hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact congrArg (e ≫ ·) (evalPullIso_transport_target ℓ s x' x' v hv hvp hva w)
  apply (cancel_mono (e ≫ c)).mp
  calc
    τ ≫ e ≫ c = e ≫ (transport a ℓ.iso s x').hom ≫ (pullCongr F w).hom ≫ c := by
      exact (Category.assoc τ e c).symm.trans
        ((congrArg (· ≫ c) hτ).trans (by simp only [Category.assoc]))
    _ = (e ≫ c) ≫ multiply (structureModule Z.left) r := by rw [h, Category.assoc]
    _ = multiply (Pull y (Pull x F)) r ≫ (e ≫ c) := (EquivariantAffineModules.multiply_natural (e ≫ c) r).symm

set_option backward.isDefEq.respectTransparency false in
private theorem terminalPoint_equivariant (x : basePoint k ⟶ X)
    (h : actOn a (fst T.X (basePoint k)) (snd T.X (basePoint k) ≫ x) = snd T.X (basePoint k) ≫ x) :
    IsEquivariantMap a (terminalAction T) x := by
  let s := fst T.X (basePoint k)
  let y := snd T.X (basePoint k)
  have hv : 𝟙 T.X ⊗ₘ x = lift s (y ≫ x) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [tensorHom_fst, Category.comp_id, lift_fst]
    · rw [tensorHom_snd, lift_snd]
  change y ≫ x = (𝟙 T.X ⊗ₘ x) ≫ a.smul
  rw [hv]
  exact h.symm

private theorem basePoint_openCover :
    (⨆ (_ : PUnit.{u+1}), (⊤ : (basePoint k).left.Opens)) = ⊤ :=
  top_unique (le_iSup (fun _ : PUnit.{u+1} => (⊤ : (basePoint k).left.Opens)) PUnit.unit)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem fiberCharacter_of_scalar (split : IsSplitTorus T)
    (x : basePoint k ⟶ X) (F : EquivariantCoherent a)
    (hx : IsEquivariantMap a (terminalAction T) x)
    (i : Pull x F.sheaf ≅ structureModule (basePoint k).left) (ψ : Character T)
    (hτ : (EquivariantAffineModules.pullbackLinearizationIso hx F.lin.iso).hom =
      multiply (Pull (snd T.X (basePoint k)) (Pull x F.sheaf))
        ((fst T.X (basePoint k)).left.appTop (characterFunction ψ))) :
    IsFiberCharacter x F (eChar ψ) := by
  classical
  let Pt := basePoint k
  let b := terminalAction T
  let M := Pull x F.sheaf
  let τ := EquivariantAffineModules.pullbackLinearization hx F.lin
  have hM : M.IsFinitePresentation := by
    apply ProjectiveFiniteness.isFinitePresentation_of_local_rank_one_restrict M
      (fun _ : PUnit.{u+1} => ⊤) (TopologicalSpace.IsOpenCover.mk basePoint_openCover)
    intro z
    exact ((Scheme.Modules.restrictFunctor _).mapIso i ≪≫ Scheme.Modules.restrictUnitIso _).symm
  let H : EquivariantCoherent b := ⟨M, hM, τ⟩
  refine ⟨H, Iso.refl _, ?_, ?_⟩
  · intro S r j
    let hh := equivariant_actOn hx (t := r) (y := j)
    refine ⟨hh, ?_⟩
    change (Scheme.Modules.pullback j.left).map (𝟙 M) ≫ _ ≫ _ ≫ _ ≫ _ ≫
      (Scheme.Modules.pullback (actOn b r j).left).map (𝟙 M) = (transport b τ.iso r j).hom
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    have he := congrArg (· ≫ (pullComp F.sheaf (actOn b r j) x).inv)
      (EquivariantAffineModules.pullbackLinearization_transport hx F.lin.iso r j).symm
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at he
    exact he
  let y := snd T.X Pt
  let r := (fst T.X Pt).left.appTop (characterFunction ψ)
  have hw (z : Γ(H.sheaf, ⊤)) : HasSectionWeight H.lin z ψ := by
    change (EquivariantAffineModules.pullbackLinearizationIso hx F.lin.iso).hom.val.app (op ⊤)
      (pullSection y.left M z) = r • pullSection y.left M z
    rw [hτ]
    exact EquivariantAffineModules.multiply_app_top (Pull y M) r (pullSection y.left M z)
  obtain ⟨m⟩ := cohomologyPullbacks_nonempty H 0
  have hPt : HasFiniteAffineCover Pt := by
    let : IsAffine Pt.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
    refine ⟨PUnit.{u+1}, inferInstance, fun _ => ⊤, basePoint_openCover, fun s _ => ?_⟩
    have he : (⨅ (j : PUnit.{u+1}) (_ : j ∈ (s : Set PUnit.{u+1})), (⊤ : Pt.left.Opens)) = ⊤ :=
      top_unique (le_iInf fun _ => le_iInf fun _ => le_rfl)
    simpa only [he] using isAffineOpen_top Pt.left
  obtain ⟨B, hB⟩ := exists_cohomologyWeightGrading split hPt H 0 m
  have hp : cohomologyWeightSpace m ψ = ⊤ := Submodule.eq_top_iff'.mpr fun v =>
    (cohomologyWeights_zero m ψ v).mpr (hw _)
  have hoth (ν : Character T) (hν : ν ≠ ψ) : cohomologyWeightSpace m ν = ⊥ := by
    have hd := B.internal.submodule_iSupIndep.pairwiseDisjoint hν
    change Disjoint (B.piece ν) (B.piece ψ) at hd
    rw [hB ν, hB ψ, hp, disjoint_top] at hd
    exact hd
  refine cohomologyCharacter_of_line H 0 m
    ((cohomology Pt 0).mapIso i ≪≫ (cohomologyZero Pt).app _ ≪≫ basePointSectionsIso) ψ ?_
  intro ν z
  by_cases eq : ν = ψ
  · subst ν
    simp [hp]
  · simp only [hoth ν eq, eq, false_or, Submodule.mem_bot]

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {aG : ModObj G.val.X Q.scheme}
variable {p : BorelProjection P} {χ : Character P.torus.group} {h : FlagKernelPair Q}

set_option backward.isDefEq.respectTransparency false in
private theorem flagTransition_of_factor {Z : SchemeOver k} (g : Z ⟶ G.val.X)
    (b : Z ⟶ P.negative.group.X) (t : Z ⟶ P.torus.group.X) (ψ : Character P.torus.group)
    (hb : b ≫ (p.projection ≫ χ).hom.hom = t ≫ ψ.hom.hom) :
    (prod.lift g b).left.appTop (flagTransition p χ) =
      (t⁻¹).left.appTop (characterFunction ψ) := by
  let B := Specs.DiagonalizableGroups.groupAlgebra k Specs.DiagonalizableGroups.IntegerCharacters
  let u := (Scheme.ΓSpecIso (CommRingCat.of B)).inv (MonoidAlgebra.of k _
    Specs.DiagonalizableGroups.integerGenerator)
  let r : G.val.X ⨯ P.negative.group.X ⟶ (specGroup B).X :=
    (prod.snd : G.val.X ⨯ P.negative.group.X ⟶ P.negative.group.X)⁻¹ ≫ (p.projection ≫ χ).hom.hom
  change (prod.lift g b).left.appTop (r.left.appTop u) =
    (t⁻¹).left.appTop (ψ.hom.hom.left.appTop u)
  rw [← appTop_comp_apply, ← appTop_comp_apply, ← Over.comp_left, ← Over.comp_left]
  have he : prod.lift g b ≫ r = t⁻¹ ≫ ψ.hom.hom := by
    unfold r
    rw [← Category.assoc, GrpObj.comp_inv, prod.lift_snd]
    exact (GrpObj.inv_comp b _).trans ((congrArg Inv.inv hb).trans (GrpObj.inv_comp t _).symm)
  exact congrArg (fun f : Z ⟶ (specGroup B).X => f.left.appTop u) he

set_option maxHeartbeats 950000 in
set_option backward.isDefEq.respectTransparency false in
private theorem fiber_eval_overlap {Z : SchemeOver k} (g : Z ⟶ G.val.X)
    (b : Z ⟶ P.negative.group.X) (g' : Z ⟶ G.val.X)
    (hg' : g' = g * (b ≫ P.negative.inclusion.hom.hom))
    (x : Z ⟶ Q.scheme) (hg : g ≫ Q.projection = x) (wg : g' ≫ Q.projection = x) :
    covarianceCoordinate (flagLineData Q p χ h) g' x wg =
      covarianceCoordinate (flagLineData Q p χ h) g x hg ≫ multiply
        (structureModule Z.left) ((prod.lift g b).left.appTop (flagTransition p χ)) := by
  let D := flagLineData Q p χ h
  let j : Z ⟶ D.overlap := prod.lift g b
  have h₀ : j ≫ D.first = g := prod.lift_fst _ _
  have h₁ : j ≫ D.second = g' := by
    change prod.lift g b ≫ Specs.HomogeneousQuotient.rightMultiplication P.negative = _
    rw [Specs.HomogeneousQuotient.rightMultiplication, MonObj.comp_mul, prod.lift_fst,
      ← Category.assoc, prod.lift_snd, hg']
  have hj : j ≫ D.overlapProjection = x := by
    rw [← D.fst_w, ← Category.assoc, h₀]
    exact hg
  let compare (g₀ g₁ : Z ⟶ D.torsor) (e₀ : j ≫ D.first = g₀) (e₁ : j ≫ D.second = g₁)
      (w₀ : g₀ ≫ D.projection = x) (w₁ : g₁ ≫ D.projection = x) :
      covarianceCoordinate D g₁ x w₁ = covarianceCoordinate D g₀ x w₀ ≫
        multiply (structureModule Z.left) (j.left.appTop D.multiplier) := by
    subst g₀ g₁
    exact covarianceCoordinate_overlap D j x hj
  exact compare g g' h₀ h₁ hg wg


private theorem transportMatches_congr_coordinates {Z : SchemeOver k}
    {F : X.left.Modules} {M : Z.left.Modules} (L : Linearization a F)
    (s : Z ⟶ T.X) {x y : Z ⟶ X} {c c' : Pull x F ⟶ M} {d d' : Pull y F ⟶ M}
    (hc : c = c') (hd : d = d') (ht : TransportMatches a L.iso s c d) :
    TransportMatches a L.iso s c' d' := hc ▸ hd ▸ ht

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem covarianceCoordinate_fixed_transport
    (ℓ : Linearization (torusAction P.torus aG) (flagLineSheaf Q p χ h))
    (ht : IsFlagLineBundleTransport Q aG p χ h ℓ)
    {Z : SchemeOver k} (s : Z ⟶ P.torus.group.X) (g g' : Z ⟶ G.val.X)
    (hg' : g' = lift (s ≫ P.torus.inclusion.hom.hom) g ≫ μ[G.val.X])
    {x : Z ⟶ Q.scheme} (w₀ : g ≫ Q.projection = x) (w₁ : g' ≫ Q.projection = x)
    (f : actOn (torusAction P.torus aG) s x = x) :
    (transport (torusAction P.torus aG) ℓ.iso s x).hom ≫ (pullCongr (flagLineSheaf Q p χ h) f).hom ≫
      covarianceCoordinate (flagLineData Q p χ h) g' x w₁ =
      covarianceCoordinate (flagLineData Q p χ h) g x w₀ := by
  let D := flagLineData Q p χ h
  let t := torusAction P.torus aG
  have h₀ : TransportMatches t ℓ.iso s (flagLineCoordinate Q p χ h g) (flagLineCoordinate Q p χ h g') := by
    subst g'
    exact ht Z s g
  have h₁ := transportMatches_congr_coordinates ℓ s
    (flagLineCoordinate_eq_covarianceCoordinate Q p χ h g)
    (flagLineCoordinate_eq_covarianceCoordinate Q p χ h g') h₀
  obtain ⟨_, he⟩ := compareTransport t ℓ.iso rfl w₀ w₁
    (covarianceCoordinate_congr D g rfl w₀) (covarianceCoordinate_congr D g' rfl w₁) h₁
  exact he

set_option backward.isDefEq.respectTransparency false in
private theorem coordinate_scalar_of_inverse {Z : SchemeOver k} {H : Z.left.Modules}
    (a : H ⟶ H) (c : H ⟶ structureModule Z.left) (r d : Γ(Z.left, ⊤))
    (he : r * d = 1) (h : a ≫ c ≫ multiply (structureModule Z.left) d = c) :
    a ≫ c = c ≫ multiply (structureModule Z.left) r := by
  let O := structureModule Z.left
  have hcancel : multiply (X := Z) O d ≫ multiply (X := Z) O r = 𝟙 O := by
    calc
      _ = multiply (X := Z) O (r * d) := EquivariantAffineModules.multiply_comp O d r
      _ = 𝟙 O := (congrArg (multiply (X := Z) O) he).trans (EquivariantAffineModules.multiply_one O)
  have hc : c ≫ multiply (X := Z) O d ≫ multiply (X := Z) O r = c := by
    rw [hcancel, Category.comp_id]
  have h' := congrArg (· ≫ multiply (X := Z) O r) h
  simp only [Category.assoc] at h'
  exact (congrArg (a ≫ ·) hc).symm.trans h'

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
/-- A change of torsor lift by a Borel factor converts transport preserving
both lift coordinates into multiplication in the coordinate at the fixed flag. -/
private theorem fiberTransport_of_borelFactor
    (ℓ : Linearization (torusAction P.torus aG) (flagLineSheaf Q p χ h))
    (ht : IsFlagLineBundleTransport Q aG p χ h ℓ)
    {Z : SchemeOver k} (s : Z ⟶ P.torus.group.X) (g : Z ⟶ G.val.X)
    (u : Z ⟶ P.negative.group.X) (ψ : Character P.torus.group)
    (hχ : u ≫ (p.projection ≫ χ).hom.hom = s ≫ ψ.hom.hom)
    (hgu : lift (s ≫ P.torus.inclusion.hom.hom) g ≫ μ[G.val.X] = g * (u ≫ P.negative.inclusion.hom.hom))
    {x' : Z ⟶ Q.scheme} (hgy : g ≫ Q.projection = x')
    (hfix : actOn (torusAction P.torus aG) s x' = x') :
    let c := covarianceCoordinate (flagLineData Q p χ h) g x' hgy
    (transport (torusAction P.torus aG) ℓ.iso s x').hom ≫ (pullCongr (flagLineSheaf Q p χ h) hfix).hom ≫ c =
      c ≫ multiply (structureModule Z.left) (s.left.appTop (characterFunction ψ)) := by
  intro c
  let t := torusAction P.torus aG
  let F := flagLineSheaf Q p χ h
  let D := flagLineData Q p χ h
  let g' := lift (s ≫ P.torus.inclusion.hom.hom) g ≫ μ[G.val.X]
  have hg'y : g' ≫ Q.projection = x' := by
    change (lift (s ≫ P.torus.inclusion.hom.hom) g ≫ μ[G.val.X]) ≫ Q.projection = x'
    rw [hgu, quotient_right_mul]
    exact hgy
  let r := s.left.appTop (characterFunction ψ)
  let r' := (s⁻¹).left.appTop (characterFunction ψ)
  have hrr' : r * r' = 1 := by
    dsimp only [r, r']
    rw [← EquivariantAffineModules.characterFunction_at_mul, mul_inv_cancel,
      EquivariantAffineModules.characterFunction_at_one]
  have hshift : covarianceCoordinate D g' x' hg'y = c ≫ multiply (structureModule Z.left) r' :=
    (fiber_eval_overlap (h := h) g u g' hgu x' hgy hg'y).trans
      (congrArg (fun f => c ≫ multiply (structureModule Z.left) f) (flagTransition_of_factor g u s ψ hχ))
  have he := covarianceCoordinate_fixed_transport ℓ ht s g g' rfl hgy hg'y hfix
  rw [hshift] at he
  let tr := (transport t ℓ.iso s x').hom ≫ (pullCongr F hfix).hom
  have htr : tr ≫ c ≫ multiply (structureModule Z.left) r' = c :=
    (Category.assoc _ _ _).trans he
  exact (Category.assoc _ _ _).symm.trans (coordinate_scalar_of_inverse tr c r r' hrr' htr)

set_option backward.isDefEq.respectTransparency false in
private theorem flagLineCoordinate_comp_isIso
    {Y Z : SchemeOver k} (y : Z ⟶ Y) (g : Y ⟶ G.val.X)
    [IsIso (flagLineCoordinate Q p χ h g)] :
    IsIso (covarianceCoordinate (flagLineData Q p χ h) (y ≫ g) (y ≫ (g ≫ Q.projection))
      (Category.assoc y g Q.projection)) := by
  let D := flagLineData Q p χ h
  let F := flagLineSheaf Q p χ h
  let a := (pullComp F y (g ≫ Q.projection)).inv
  let b := (Scheme.Modules.pullback y.left).map (flagLineCoordinate Q p χ h g)
  let d := (regularPull y).hom
  have ec : covarianceCoordinate D (y ≫ g) (y ≫ (g ≫ Q.projection)) (Category.assoc y g Q.projection) =
      a ≫ b ≫ d := by
    refine (covarianceCoordinate_comp D g y).trans ?_
    exact congrArg (fun f => a ≫ (Scheme.Modules.pullback y.left).map f ≫ d)
      (flagLineCoordinate_eq_covarianceCoordinate Q p χ h g).symm
  exact ec.symm ▸ (inferInstance : IsIso (a ≫ b ≫ d))

set_option backward.isDefEq.respectTransparency false in
private theorem fixedFlag_of_borelFactor
    (ℓ : Linearization (torusAction P.torus aG) (flagLineSheaf Q p χ h))
    (ht : IsFlagLineBundleTransport Q aG p χ h ℓ)
    (g₀ : basePoint k ⟶ G.val.X) (u : P.torus.group.X ⊗ basePoint k ⟶ P.negative.group.X)
    (hgu : (fst P.torus.group.X (basePoint k) ≫ P.torus.inclusion.hom.hom) * (snd P.torus.group.X (basePoint k) ≫ g₀) =
      (snd P.torus.group.X (basePoint k) ≫ g₀) * (u ≫ P.negative.inclusion.hom.hom)) :
    actOn (torusAction P.torus aG) (fst P.torus.group.X (basePoint k))
      (snd P.torus.group.X (basePoint k) ≫ (g₀ ≫ Q.projection)) =
      snd P.torus.group.X (basePoint k) ≫ (g₀ ≫ Q.projection) := by
  let Z := P.torus.group.X ⊗ basePoint k
  let s := fst P.torus.group.X (basePoint k)
  let y := snd P.torus.group.X (basePoint k)
  let x' := y ≫ (g₀ ≫ Q.projection)
  let g := y ≫ g₀
  let t := torusAction P.torus aG
  have hgy : g ≫ Q.projection = x' := Category.assoc _ _ _
  have hg'y : ((s ≫ P.torus.inclusion.hom.hom) * g) ≫ Q.projection = x' :=
    (congrArg (· ≫ Q.projection) hgu).trans ((quotient_right_mul Q g u).trans hgy)
  obtain ⟨w₀, _⟩ := ht Z s g
  exact (congrArg (actOn t s) hgy).symm.trans (w₀.trans hg'y)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem flagFiberLinearization_of_borelFactor
    (ℓ : Linearization (torusAction P.torus aG) (flagLineSheaf Q p χ h))
    (ht : IsFlagLineBundleTransport Q aG p χ h ℓ)
    (g₀ : basePoint k ⟶ G.val.X) [IsIso (flagLineCoordinate Q p χ h g₀)]
    (ψ : Character P.torus.group) (u : P.torus.group.X ⊗ basePoint k ⟶ P.negative.group.X)
    (hχ : u ≫ (p.projection ≫ χ).hom.hom = fst P.torus.group.X (basePoint k) ≫ ψ.hom.hom)
    (hgu : (fst P.torus.group.X (basePoint k) ≫ P.torus.inclusion.hom.hom) * (snd P.torus.group.X (basePoint k) ≫ g₀) =
      (snd P.torus.group.X (basePoint k) ≫ g₀) * (u ≫ P.negative.inclusion.hom.hom))
    (hfix : actOn (torusAction P.torus aG) (fst P.torus.group.X (basePoint k))
      (snd P.torus.group.X (basePoint k) ≫ (g₀ ≫ Q.projection)) =
      snd P.torus.group.X (basePoint k) ≫ (g₀ ≫ Q.projection))
    (hx : IsEquivariantMap (torusAction P.torus aG) (terminalAction P.torus.group) (g₀ ≫ Q.projection)) :
    (EquivariantAffineModules.pullbackLinearizationIso hx ℓ.iso).hom =
      multiply (Pull (snd P.torus.group.X (basePoint k)) (Pull (g₀ ≫ Q.projection) (flagLineSheaf Q p χ h)))
        ((fst P.torus.group.X (basePoint k)).left.appTop (characterFunction ψ)) := by
  let T := P.torus.group
  let t := torusAction P.torus aG
  let F := flagLineSheaf Q p χ h
  let Z := T.X ⊗ basePoint k
  let s := fst T.X (basePoint k)
  let y := snd T.X (basePoint k)
  let x := g₀ ≫ Q.projection
  let x' := y ≫ x
  let g := y ≫ g₀
  let D := flagLineData Q p χ h
  have hgy : g ≫ Q.projection = x' := Category.assoc _ _ _
  let c := covarianceCoordinate D g x' hgy
  let : IsIso c := flagLineCoordinate_comp_isIso (p := p) (χ := χ) (h := h) y g₀
  let r := s.left.appTop (characterFunction ψ)
  have htr : (transport t ℓ.iso s x').hom ≫ (pullCongr F hfix).hom ≫ c =
      c ≫ multiply (structureModule Z.left) r :=
    fiberTransport_of_borelFactor ℓ ht s g u ψ hχ hgu hgy hfix
  exact terminalPullback_multiply (T := T) (X := Q.scheme) (a := t) (F := F)
    ℓ x hx hfix c r htr

set_option backward.isDefEq.respectTransparency false in
private theorem flagFiberCharacter_of_borelFactor
    (hF : (flagLineSheaf Q p χ h).IsFinitePresentation)
    (ℓ : Linearization (torusAction P.torus aG) (flagLineSheaf Q p χ h))
    (ht : IsFlagLineBundleTransport Q aG p χ h ℓ)
    (g₀ : basePoint k ⟶ G.val.X) [IsIso (flagLineCoordinate Q p χ h g₀)]
    (ψ : Character P.torus.group) (u : P.torus.group.X ⊗ basePoint k ⟶ P.negative.group.X)
    (hχ : u ≫ (p.projection ≫ χ).hom.hom = fst P.torus.group.X (basePoint k) ≫ ψ.hom.hom)
    (hgu : (fst P.torus.group.X (basePoint k) ≫ P.torus.inclusion.hom.hom) * (snd P.torus.group.X (basePoint k) ≫ g₀) =
      (snd P.torus.group.X (basePoint k) ≫ g₀) * (u ≫ P.negative.inclusion.hom.hom)) :
    IsFiberCharacter (g₀ ≫ Q.projection) (⟨_, hF, ℓ⟩ : EquivariantCoherent (torusAction P.torus aG)) (eChar ψ) := by
  have hfix := fixedFlag_of_borelFactor ℓ ht g₀ u hgu
  have hx := terminalPoint_equivariant (g₀ ≫ Q.projection) hfix
  exact fiberCharacter_of_scalar P.split (g₀ ≫ Q.projection) ⟨_, hF, ℓ⟩ hx
    (asIso (flagLineCoordinate Q p χ h g₀)) ψ
    (flagFiberLinearization_of_borelFactor ℓ ht g₀ ψ u hχ hgu hfix hx)

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency false in
private theorem flagLineWeylFiberCharacter
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ aG.smul)
    (hF : (flagLineSheaf Q p χ h).IsFinitePresentation)
    (ℓ : Linearization (torusAction P.torus aG) (flagLineSheaf Q p χ h))
    (ht : IsFlagLineBundleTransport Q aG p χ h ℓ)
    [IsCommMonObj P.torus.group.X] {D : Datum P.torus}
    (J : Identification D) (w : D.rootDatum.weylGroup)
    (n : basePoint k ⟶ J.normalizer.group.X) (hn : RepresentsWeylElement J w n) :
    IsFiberCharacter ((n ≫ J.normalizer.inclusion.hom.hom) ≫ Q.projection)
      (⟨_, hF, ℓ⟩ : EquivariantCoherent (torusAction P.torus aG))
      (eChar ((J.labelEquiv w).val χ)) := by
  classical
  let T := P.torus.group
  let Pt := basePoint k
  let ψ := (J.labelEquiv w).val χ
  let g₀ := n ≫ J.normalizer.inclusion.hom.hom
  let Z := T.X ⊗ Pt
  let s := fst T.X Pt
  let y := snd T.X Pt
  let g := y ≫ g₀
  let g' := lift (s ≫ P.torus.inclusion.hom.hom) g ≫ μ[G.val.X]
  have hgy₀ : g = toUnit Z ≫ n ≫ J.normalizer.inclusion.hom.hom := by
    exact congrArg (fun f : Z ⟶ Pt => f ≫ n ≫ J.normalizer.inclusion.hom.hom) (Subsingleton.elim _ _)
  obtain ⟨u, hu, hχ⟩ := weylBorelFactor J w n hn p χ s
  have hgu : g' = g * (u ≫ P.negative.inclusion.hom.hom) := by
    change (s ≫ P.torus.inclusion.hom.hom) * g = _
    rw [hgy₀]
    exact hu
  obtain ⟨A⟩ := exists_associatedBundle Q p χ aG ha
  let : IsIso (flagLineCoordinate Q p χ h g₀) := flagLineCoordinate_point_isIso A g₀
  exact flagFiberCharacter_of_borelFactor hF ℓ ht g₀ ψ u hχ hgu

/-- The associated covariance line has its torus linearization, the
prescribed formal cohomology characters and Weyl fiber characters. -/
theorem flagLineBundleCharacters : FlagLineBundleCharacters.{u} := by
  intro k _ G P Q a p χ h ha
  obtain ⟨ℓ, htrans, hcoho⟩ := FlagCovarianceLinearization.flagCovarianceLinearization Q a p χ h ha
  let hf := flagLineSheaf_finitePresentation Q a p χ h ha
  refine ⟨hf, ℓ, htrans, ?_, ?_⟩
  · intro i b ρ hρ
    exact flagLineCohomology_character ℓ hcoho hf i b ρ hρ
  · intro _ D J w n hn
    simpa only [Category.assoc] using flagLineWeylFiberCharacter ha hf ℓ htrans J w n hn

end WeylFiberCharacter

end

end LinearAlgebraicGroups.Representation.FlagEquivariantEulerMap
