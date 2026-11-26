import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalMarkedAdjoint
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FinCases

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalMarkedAdjoint

open _root_.LinearAlgebraicGroups.Specs
open Specs.AutomorphismSequence
open _root_.LinearAlgebraicGroups.Descent.AutomorphismSequence (innerAut_eq_one_iff)
open Specs.CentralIsogenies (IsCentralIsogeny)
open Specs.ExceptionalAffineRootSystems (e6Partner exceptionalCartan)
open Specs.RamifiedExceptionalMarkedAdjoint
open Fppf (IsFppf schemeTopology)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open private groupSections_isSheaf groupSectionsMap_locallySurjective
  groupSheaf_separated descends_iso_of_locallySurjective projection_eq_one_iff
  groupSectionsMap groupSectionsFullyFaithful from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private centralizes_precomp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre

theorem naturalPointComparison {F : Type u} [Field F] {G H : GroupScheme F}
    (e : G ≅ H) : NaturalPointComparison e := by
  intro R R' f g
  exact (NatTrans.naturality_apply ((groupPointsFunctor F).mapIso e).hom f g).symm

private theorem mapsCentralPoint {F : Type u} [Field F] {G H : GroupScheme F}
    (f : G ⟶ H) (hf : IsFppf f.hom.hom.left) {U : SchemeOver F} (g : U ⟶ G.X)
    (hg : innerAut g = 1) : innerAut (g ≫ f.hom.hom) = 1 := by
  rw [innerAut_eq_one_iff, centralizes_iff]
  intro V v x
  rw [innerAut_eq_one_iff, centralizes_iff] at hg
  let m := IsMonHom.monoidHom f.hom.hom V
  have goalEq : (⟨m (v ≫ g) * x⟩ : (groupSections H).obj (op V)) =
      ⟨x * m (v ≫ g)⟩ := by
    let p := groupSectionsMap f
    letI := groupSectionsMap_locallySurjective f hf
    apply groupSheaf_separated (groupSections_isSheaf H)
      (Presheaf.imageSieve_mem (schemeTopology F) p ⟨x⟩)
    rintro W a ⟨y, hy⟩
    let n := IsMonHom.monoidHom f.hom.hom W
    have hy' : n y.down = a ≫ x := congrArg ULift.down hy
    apply ULift.ext
    change a ≫ (m (v ≫ g) * x) = a ≫ (x * m (v ≫ g))
    have ha : a ≫ m (v ≫ g) = n ((a ≫ v) ≫ g) := by
      simp only [Category.assoc]
      rfl
    rw [MonObj.comp_mul, MonObj.comp_mul, ha, ← hy', ← n.map_mul, ← n.map_mul]
    apply congrArg n
    simpa only [Grp.id_hom_hom, Category.comp_id] using (hg W (a ≫ v) y.down).eq
  change (v ≫ (g ≫ f.hom.hom)) * x = x * (v ≫ (g ≫ f.hom.hom))
  have hm : m (v ≫ g) = v ≫ (g ≫ f.hom.hom) := by
    change (v ≫ g) ≫ f.hom.hom = v ≫ (g ≫ f.hom.hom)
    exact Category.assoc v g f.hom.hom
  rw [← hm]
  exact congrArg (fun z => (z.down : V ⟶ H.X)) goalEq

private theorem mapsCentralPointIso {F : Type u} [Field F] {G H : GroupScheme F}
    (e : G ≅ H) {U : SchemeOver F} (g : U ⟶ G.X) (hg : innerAut g = 1) :
    innerAut (g ≫ e.hom.hom.hom) = 1 := by
  apply mapsCentralPoint e.hom _ g hg
  haveI : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver F) ⋙ Over.forget _).map_isIso e.hom
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem centralPoint_iso_iff {F : Type u} [Field F] {G H : GroupScheme F}
    (e : G ≅ H) {U : SchemeOver F} (g : U ⟶ G.X) :
    innerAut g = 1 ↔ innerAut (g ≫ e.hom.hom.hom) = 1 := by
  refine ⟨mapsCentralPointIso e g, fun h => ?_⟩
  have hh := mapsCentralPointIso e.symm _ h
  have he := congrArg (fun f : G ⟶ G => f.hom.hom) e.hom_inv_id
  change e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ at he
  change innerAut ((g ≫ e.hom.hom.hom) ≫ e.inv.hom.hom) = 1 at hh
  simpa only [Category.assoc, he, Category.comp_id] using hh

private theorem factorThroughKernel_iff {F : Type u} [Field F] {G H : GroupScheme F}
    (f : G ⟶ H) {N : ClosedSubgroup G} (hN : IsSchemeKernel f N)
    {U : SchemeOver F} (x : U ⟶ G.X) :
    x ≫ f.hom.hom = 1 ↔ ∃ n : U ⟶ N.group.X, n ≫ N.inclusion.hom.hom = x := by
  constructor
  · intro h
    exact ⟨hN.lift x (toUnit _) h, hN.lift_fst _ _ _⟩
  · rintro ⟨n, rfl⟩
    rw [Category.assoc, hN.w, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _

/-- The adjoint comparison follows from the universal property of the fppf
quotient once the target has trivial scheme centre. -/
theorem compareAdjointQuotient {F : Type u} [Field F] {G G' H : AffineAlgebraicGroup F}
    (f : G.val ⟶ H.val) (hf : IsCentralIsogeny f)
    (hH : ∀ (U : SchemeOver F) (g : U ⟶ H.val.X), innerAut g = 1 → g = 1)
    (j : G.val ≅ G'.val) (Q : AdjointQuotient G') :
    ∃ e : H.val ≅ Q.quotient.val,
      f ≫ e.hom = j.hom ≫ Q.projection ∧ NaturalPointComparison e := by
  obtain ⟨hfin, hflat, hsurj, N, hN, hcentral⟩ := hf
  letI := hfin
  letI : LocallyOfFiniteType H.val.X.hom := H.property.2.1
  letI : IsLocallyNoetherian H.val.X.left := LocallyOfFiniteType.isLocallyNoetherian H.val.X.hom
  have ff : IsFppf f.hom.hom.left := ⟨hflat, hsurj, inferInstance⟩
  have fker (U : SchemeOver F) (g : U ⟶ G.val.X) :
      g ≫ f.hom.hom = 1 ↔ innerAut g = 1 := by
    constructor
    · intro hg
      obtain ⟨n, rfl⟩ := (factorThroughKernel_iff f hN g).mp hg
      rw [innerAut_eq_one_iff]
      exact centralizes_precomp hcentral n
    · exact fun h => hH U _ (mapsCentralPoint f ff g h)
  let p := groupSectionsMap f
  let q := groupSectionsMap Q.projection
  let i := (yonedaGrp ⋙ (Functor.whiskeringRight _ _ _).obj Fppf.liftGroups.{u,u+1}).mapIso j
  have hk (U : (SchemeOver F)ᵒᵖ) (x : (groupSections G.val).obj U) :
      p.app U x = 1 ↔ (i.hom ≫ q).app U x = 1 := by
    change ULift.up (x.down ≫ f.hom.hom) = ULift.up 1 ↔
      ULift.up ((x.down ≫ j.hom.hom.hom) ≫ Q.projection.hom.hom) = ULift.up 1
    rw [ULift.up_inj, ULift.up_inj, fker, projection_eq_one_iff]
    exact centralPoint_iso_iff j x.down
  obtain ⟨e, he⟩ := descends_iso_of_locallySurjective p q i
    (groupSectionsMap_locallySurjective f ff)
    (groupSectionsMap_locallySurjective Q.projection Q.fppf)
    (groupSections_isSheaf H.val) (groupSections_isSheaf Q.quotient.val) (by
      intro U x y
      have h := hk U (x / y)
      change p.app U x = p.app U y ↔ (i.hom ≫ q).app U x = (i.hom ≫ q).app U y
      simpa only [map_div, div_eq_one] using h)
  let J : GroupScheme F ⥤ _ :=
    yonedaGrp ⋙ (Functor.whiskeringRight _ _ _).obj Fppf.liftGroups.{u,u+1}
  let ff := groupSectionsFullyFaithful (k := F)
  let a := ff.preimageIso e
  refine ⟨a, ?_, naturalPointComparison a⟩
  apply ff.map_injective
  change groupSectionsMap (f ≫ a.hom) = groupSectionsMap (j.hom ≫ Q.projection)
  rw [show groupSectionsMap (f ≫ a.hom) = p ≫ groupSectionsMap a.hom from J.map_comp f a.hom,
    show groupSectionsMap a.hom = e.hom from ff.map_preimage _]
  exact he.trans (J.map_comp j.hom Q.projection).symm

section Centre

open Specs.SchemeCentre (rootLattice)
open Specs.DiagonalizableGroups (groupAlgebra diagonalClosedInclusion)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.CharacterDescent (Character)

private def diagonal_trivial {F M : Type u} [Field F] [CommGroup M] [Subsingleton M] :
    IsTerminal (specGroup (groupAlgebra F M)).X := by
  let A := CommHopfAlgCat.of F F
  let e : groupAlgebra F M ≅ A :=
    CommHopfAlgCat.isoMk (MonoidAlgebra.bialgEquivOfSubsingleton M)
  let e₀ := (Grp.forget (SchemeOver F)).mapIso
    ((hopfSpec (CommRingCat.of F)).mapIso e.op)
  have hA : (specGroup A).X.hom = 𝟙 _ := Spec.map_id _
  let e₁ : (specGroup A).X ≅ Over.mk (𝟙 (Spec (CommRingCat.of F))) :=
    Over.isoMk (Iso.refl _) (by simpa using hA.symm)
  exact (isTerminalTensorUnit (C := SchemeOver F)).ofIso (e₁.symm ≪≫ e₀)

theorem centreFreeOfRootLattice {F : Type u} [Field F] (G : AffineAlgebraicGroup F)
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group)
    (hm : IsGeometricallyMaximal T) (ht : rootLattice T = ⊤)
    (U : SchemeOver F) (g : U ⟶ G.val.X) (hg : innerAut g = 1) :
    g = 1 := by
  obtain ⟨_, e, _, hi, hZ, _⟩ :=
    LinearAlgebraicGroups.RootData.SchemeCentre.schemeCentre G hG T hs hm
  let Z : ClosedSubgroup G.val :=
    ⟨specGroup (groupAlgebra F (Character T.group ⧸ rootLattice T)),
      diagonalClosedInclusion F (rootLattice T) ≫ e.hom ≫ T.inclusion, hi⟩
  letI : Subsingleton (Character T.group ⧸ rootLattice T) := by
    rw [ht]
    exact QuotientGroup.subsingleton_quotient_top
  have hz : IsTerminal Z.group.X := diagonal_trivial
  obtain ⟨z, rfl⟩ := (hZ U g).mp ((innerAut_eq_one_iff g).mp hg)
  rw [hz.hom_ext z 1, MonObj.one_comp]

open Specs.RelativeFormComparison (fieldTest)
open private fppf_mem transportInner from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

private theorem finiteFieldTest_fppf (F K : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] : IsFppf (fieldTest F K).hom := by
  let a : CommRingCat.of F ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap F K)
  change IsFppf (Spec.map a)
  have hf : Flat (Spec.map a) ∧ Surjective (Spec.map a) :=
    (flat_and_surjective_SpecMap_iff a).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have hfin : IsFinite (Spec.map a) :=
    (IsFinite.SpecMap_iff a).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsLocallyNoetherian (Spec (CommRingCat.of F)) := inferInstance
  letI := hfin
  exact ⟨hf.1, hf.2, inferInstance⟩

/-- A group whose finite-field trivialization identifies it with a
centre-free group has trivial scheme centre. -/
theorem centreFreeOfRelativeIso {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {G H : GroupScheme F}
    (e : relativePoints G (fieldTest F K) ≅ relativePoints H (fieldTest F K))
    (hH : ∀ (U : SchemeOver F) (g : U ⟶ H.X), innerAut g = 1 → g = 1)
    (U : SchemeOver F) (g : U ⟶ G.X) (hg : innerAut g = 1) :
    g = 1 := by
  let T := fieldTest F K
  let W : SchemeOver F := Over.mk (pullback.fst U.hom T.hom ≫ U.hom)
  let a : W ⟶ U := Over.homMk (pullback.fst U.hom T.hom)
  let b : W ⟶ T := Over.homMk (pullback.snd U.hom T.hom) pullback.condition.symm
  have hb : IsFppf a.left := by
    obtain ⟨h₁, h₂, h₃⟩ := finiteFieldTest_fppf F K
    exact ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback U.hom T.hom).flip h₁,
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback U.hom T.hom).flip h₂,
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback U.hom T.hom).flip h₃⟩
  have hga : innerAut (a ≫ g) = 1 :=
    (innerAut_eq_one_iff _).mpr (centralizes_precomp ((innerAut_eq_one_iff _).mp hg) a)
  let V : Over T := Over.mk b
  have htr := transportInner e V (a ≫ g)
  rw [hga, map_one] at htr
  have hone := hH W _ htr.symm
  have ha : a ≫ g = 1 :=
    (e.app (op V)).groupIsoToMulEquiv.injective (hone.trans (map_one _).symm)
  let J : Sieve U :=
    { arrows := fun _ p => p ≫ g = 1
      downward_closed := fun h f => by simp only [Category.assoc, h, MonObj.comp_one] }
  have hh : (⟨g⟩ : (groupSections G).obj (op U)) = ⟨1⟩ := by
    apply groupSheaf_separated (groupSections_isSheaf G) (fppf_mem a hb (S := J) ha)
    intro V f hf
    apply ULift.ext
    exact hf.trans (MonObj.comp_one f).symm
  exact congrArg (fun x => (x.down : U ⟶ G.X)) hh


end Centre

section Diagram

private def e6Degree (i : Fin 6) : ℕ :=
  ∑ j : Fin 6, if exceptionalCartan 6 i j = -1 then 1 else 0

/-- The only nonidentity permutation preserving the E₆ Cartan matrix swaps
the two arms of length two. -/
theorem e6Partner_of_nontrivial (p : Equiv.Perm (Fin 6))
    (hp : ∀ i j, exceptionalCartan 6 (p i) (p j) = exceptionalCartan 6 i j)
    (hne : p ≠ 1) : ∀ i, p i = e6Partner i := by
  have hd (i : Fin 6) : e6Degree (p i) = e6Degree i := by
    unfold e6Degree
    rw [← Equiv.sum_comp p (fun j => if exceptionalCartan 6 (p i) j = -1 then (1 : ℕ) else 0)]
    simp only [hp]
  have h3 : p 3 = 3 :=
    (show ∀ i : Fin 6, e6Degree i = e6Degree 3 → i = 3 by decide) _ (hd 3)
  have h1 : p 1 = 1 :=
    (show ∀ i : Fin 6, e6Degree i = e6Degree 1 →
      exceptionalCartan 6 i 3 = exceptionalCartan 6 1 3 → i = 1 by decide)
      _ (hd 1) (by simpa only [h3] using hp 1 3)
  have ends : p 0 = 0 ∨ p 0 = 5 :=
    (show ∀ i : Fin 6, e6Degree i = e6Degree 0 →
      exceptionalCartan 6 i 3 = exceptionalCartan 6 0 3 → i = 0 ∨ i = 5 by decide)
      _ (hd 0) (by simpa only [h3] using hp 0 3)
  have ends' : p 5 = 0 ∨ p 5 = 5 :=
    (show ∀ i : Fin 6, e6Degree i = e6Degree 5 →
      exceptionalCartan 6 i 3 = exceptionalCartan 6 5 3 → i = 0 ∨ i = 5 by decide)
      _ (hd 5) (by simpa only [h3] using hp 5 3)
  have nextLeft : ∀ i : Fin 6, exceptionalCartan 6 0 i = -1 → i = 2 := by decide
  have nextRight : ∀ i : Fin 6, exceptionalCartan 6 5 i = -1 → i = 4 := by decide
  rcases ends with h0 | h0
  · have h5 : p 5 = 5 := ends'.resolve_left
      (fun h => (by decide : (5 : Fin 6) ≠ 0) (p.injective (h.trans h0.symm)))
    have h2 := nextLeft (p 2) (h0 ▸ hp 0 2)
    have h4 := nextRight (p 4) (h5 ▸ hp 5 4)
    exfalso
    apply hne
    apply Equiv.ext
    intro i
    fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5
  · have h5 : p 5 = 0 := ends'.resolve_right
      (fun h => (by decide : (5 : Fin 6) ≠ 0) (p.injective (h.trans h0.symm)))
    have h2 := nextRight (p 2) (h0 ▸ hp 0 2)
    have h4 := nextLeft (p 4) (h5 ▸ hp 5 4)
    intro i
    fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5

open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.ExceptionalAffineBruhat (ExceptionalNumbering)
open Specs.ExceptionalValuedTorusNormalizer (simplePermutation)
open Specs.IntegralSemisimpleModel (Model)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)

open private basedIso_ext_weight from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence

private theorem basedIso_eq_one_of_simple {D : BasedRootDatum.{u}} (e : BasedIso D D)
    (hspan : D.datum.rootSpan ℤ = ⊤ ∨ D.datum.corootSpan ℤ = ⊤)
    (h : ∀ i : D.base.support, e.val.indexEquiv i = i) : e = 𝟙 D := by
  apply basedIso_ext_weight
  intro x
  change e.val.weightEquiv x = x
  rcases hspan with hX | hY
  · have he : e.val.weightEquiv.toLinearMap = LinearMap.id := by
      apply LinearMap.ext_on (s := D.datum.root '' (D.base.support : Set D.I))
      · exact D.base.span_int_root_support.trans hX
      · rintro _ ⟨i, hi, rfl⟩
        change e.val.weightEquiv (D.datum.root i) = D.datum.root i
        rw [show e.val.weightEquiv (D.datum.root i) = D.datum.root (e.val.indexEquiv i)
          from e.val.toHom.root_weightMap_apply D.datum D.datum i, h ⟨i, hi⟩]
    exact DFunLike.congr_fun he x
  · have he : e.val.coweightEquiv.toLinearMap = LinearMap.id := by
      apply LinearMap.ext_on (s := D.datum.coroot '' (D.base.support : Set D.I))
      · exact D.base.span_int_coroot_support.trans hY
      · rintro _ ⟨i, hi, rfl⟩
        have hn : e.val.indexEquiv.symm i = i :=
          e.val.indexEquiv.symm_apply_eq.mpr (h ⟨i, hi⟩).symm
        change e.val.coweightEquiv (D.datum.coroot i) = D.datum.coroot i
        rw [show e.val.coweightEquiv (D.datum.coroot i) =
            D.datum.coroot (e.val.indexEquiv.symm i) from
          e.val.toHom.coroot_coweightMap_apply D.datum D.datum i, hn]
    apply D.datum.toPerfPair.injective
    ext y
    have hy := DFunLike.congr_fun
      (e.val.toHom.weight_coweight_transpose_apply D.datum D.datum y) x
    change D.datum.toLinearMap (e.val.weightEquiv x) y =
      D.datum.toLinearMap x (e.val.coweightEquiv y) at hy
    rw [show e.val.coweightEquiv y = y from DFunLike.congr_fun he y] at hy
    exact hy

/-- In either full lattice E₆ marking, the nonidentity based automorphism
induces the indicated involution on the numbered simple roots. -/
theorem basedE6Partner {D : BasedRootDatum.{u}} (b : Fin 6 ≃ D.base.support)
    (hb : ExceptionalNumbering D 6 b)
    (hspan : D.datum.rootSpan ℤ = ⊤ ∨ D.datum.corootSpan ℤ = ⊤)
    (e : BasedIso D D) (hne : e ≠ 𝟙 D) :
    ∀ i, e.val.indexEquiv (b i) = b (e6Partner i) := by
  let p : Equiv.Perm (Fin 6) := b.trans ((simplePermutation D e).trans b.symm)
  have hp (i : Fin 6) : b (p i) = simplePermutation D e (b i) := b.apply_symm_apply _
  have hi (i : Fin 6) : (b (p i) : D.I) = e.val.indexEquiv (b i) :=
    congrArg Subtype.val (hp i)
  have hpne : p ≠ 1 := by
    intro h
    apply hne
    apply basedIso_eq_one_of_simple e hspan
    intro a
    obtain ⟨i, rfl⟩ := b.surjective a
    rw [← hi, h]
    rfl
  have hpC (i j : Fin 6) :
      exceptionalCartan 6 (p i) (p j) = exceptionalCartan 6 i j := by
    rw [← hb.2 (p i) (p j), ← hb.2 i j, hi, hi]
    exact e.val.toHom.pairing
  intro i
  rw [← hi, e6Partner_of_nontrivial p hpC hpne i]

/-- Agreement on the simple labels of a marked central cover determines
agreement on every absolute root label. -/
theorem coverDiagramCommutes {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : MarkedCentralCover M M') (b : Fin 6 ≃ D.base.support)
    (b' : Fin 6 ≃ E.base.support) (hb : ∀ i, c.rootEquiv (b i) = b' i)
    (e : BasedIso D D) (e' : BasedIso E E)
    (he : ∀ i, e.val.indexEquiv (b i) = b (e6Partner i))
    (he' : ∀ i, e'.val.indexEquiv (b' i) = b' (e6Partner i)) :
    ∀ i, c.rootEquiv (e.val.indexEquiv i) = e'.val.indexEquiv (c.rootEquiv i) := by
  let a := e.val.weightEquiv.toLinearMap.comp c.pullCharacter
  let a' := c.pullCharacter.comp e'.val.weightEquiv.toLinearMap
  have hroot (i : D.I) : e.val.weightEquiv (D.datum.root i) =
      D.datum.root (e.val.indexEquiv i) :=
    e.val.toHom.root_weightMap_apply D.datum D.datum i
  have hroot' (i : E.I) : e'.val.weightEquiv (E.datum.root i) =
      E.datum.root (e'.val.indexEquiv i) :=
    e'.val.toHom.root_weightMap_apply E.datum E.datum i
  have hsimple : Set.EqOn a a' (E.datum.root '' (E.base.support : Set E.I)) := by
    rintro x ⟨i, hi, rfl⟩
    obtain ⟨j, hj⟩ := b'.surjective ⟨i, hi⟩
    have hj' : (b' j : E.I) = i := congrArg Subtype.val hj
    subst i
    change e.val.weightEquiv (c.pullCharacter (E.datum.root (b' j))) =
      c.pullCharacter (e'.val.weightEquiv (E.datum.root (b' j)))
    rw [← hb j, c.roots, hroot, he, hroot', hb j, he', ← hb (e6Partner j), c.roots]
  intro i
  have hi : E.datum.root (c.rootEquiv i) ∈
      Submodule.span ℤ (E.datum.root '' (E.base.support : Set E.I)) :=
    E.base.root_mem_span_int _
  have h := LinearMap.eqOn_span hsimple hi
  change e.val.weightEquiv (c.pullCharacter (E.datum.root (c.rootEquiv i))) =
    c.pullCharacter (e'.val.weightEquiv (E.datum.root (c.rootEquiv i))) at h
  apply E.datum.root.injective
  apply c.characterInjective
  simpa only [c.roots, hroot, hroot'] using h

/-- A nontrivial homomorphism out of a quadratic Galois group is nontrivial
on its nonidentity field automorphism. -/
theorem quadraticDiagram_ne_one {F L : Type u} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (h₂ : Module.finrank F L = 2)
    {D : Type*} [Group D] (ω : Gal(L/F) →* D) (hω : ω ≠ 1)
    (σ : Gal(L/F)) (hσ : σ ≠ 1) : ω σ ≠ 1 := by
  have hc := (IsGalois.card_aut_eq_finrank F L).trans h₂
  obtain ⟨a, b, hab, h⟩ := Nat.card_eq_two_iff.mp hc
  have cases (s : Gal(L/F)) : s = a ∨ s = b := by
    have hs : s ∈ ({a, b} : Set (Gal(L/F))) := by rw [h]; exact Set.mem_univ _
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hs
  have hall (s : Gal(L/F)) : s = 1 ∨ s = σ := by
    rcases cases 1 with h₁ | h₁ <;> rcases cases σ with h₂ | h₂
    · exact (hσ (h₂.trans h₁.symm)).elim
    · simpa only [← h₁, ← h₂] using cases s
    · exact (cases s).symm.imp (·.trans h₁.symm) (·.trans h₂.symm)
    · exact (hσ (h₂.trans h₁.symm)).elim
  intro hzero
  apply hω
  ext s
  rcases hall s with rfl | rfl
  · exact map_one _
  · exact hzero


end Diagram

section MarkedPoints

open Specs.Pinning (AttachedDatum BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model)
open Specs.ExceptionalAffineBruhat (RamifiedReference)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.AdjointCocharacters (coordinateHopfIso)
open Specs.RelativeFormComparison (fieldTest)
open Specs.SchemeCentre (rootLattice)
open Specs.CharacterPairing (absoluteRoots)
open Specs.CharacterDescent (Character)
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private hopfIsoEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison

/-- Recover the chosen field marking from the integral model on all test
algebras. -/
theorem markedFibreExists {D : BasedRootDatum.{u}} (M : Model D)
    (F : Type u) [Field F] : Nonempty (MarkedFibre M F) := by
  obtain ⟨A, P, e, t, z, hT, hz, hEval, hRoot⟩ := M.fieldFibre F
  exact ⟨⟨A, P, e, t, z, hT, (fun a => congrArg Subtype.val (hz a)), hEval, hRoot⟩⟩

private theorem rootLattice_eq_top_of_span {F : Type u} [Field F] {P : Pinning.SplitBorelPair F}
    (D : AttachedDatum P) (h : D.toBased.datum.rootSpan ℤ = ⊤) : rootLattice P.T = ⊤ := by
  letI := D.comm
  have hr : Set.range D.datum.rootDatum.root = Additive.toMul ⁻¹' absoluteRoots P.T := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [D.datum.root_eq]
      exact i.property
    · intro hx
      exact ⟨⟨Additive.toMul x, hx⟩, D.datum.root_eq _⟩
  have H : (rootLattice P.T).toAddSubgroup.toIntSubmodule =
      D.toBased.datum.rootSpan ℤ := by
    apply Submodule.toAddSubgroup_injective
    change (rootLattice P.T).toAddSubgroup =
      (Submodule.span ℤ (Set.range D.datum.rootDatum.root)).toAddSubgroup
    rw [Submodule.span_int_eq_addSubgroupClosure, rootLattice, Subgroup.toAddSubgroup_closure, hr]
  rw [h] at H
  apply (Subgroup.eq_top_iff' _).mpr
  intro x
  change Additive.ofMul x ∈ (rootLattice P.T).toAddSubgroup.toIntSubmodule
  rw [H]
  exact Submodule.mem_top

theorem markedAdjointCentreFree {F L : Type u} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] {D : BasedRootDatum.{u}} {M : Model D}
    (R : RamifiedReference F L M) (h : D.datum.rootSpan ℤ = ⊤)
    (U : SchemeOver F) (g : U ⟶ R.descent.group.val.X) (hg : innerAut g = 1) :
    g = 1 := by
  let P := R.fibre.realization
  let e := P.datumIso.val
  have hs : P.attached.toBased.datum.rootSpan ℤ = ⊤ := by
    unfold RootPairing.rootSpan
    have he : Set.range (e.weightEquiv ∘ D.datum.root) =
        Set.range P.attached.toBased.datum.root := by
      have hfun : e.weightEquiv ∘ D.datum.root =
          P.attached.toBased.datum.root ∘ e.indexEquiv := funext fun i =>
        e.toHom.root_weightMap_apply _ _ i
      rw [hfun, Set.range_comp, e.indexEquiv.surjective.range_eq, Set.image_univ]
    change Submodule.span ℤ (Set.range P.attached.toBased.datum.root) = ⊤
    rw [← he, Set.range_comp]
    change Submodule.span ℤ (e.weightEquiv.toLinearMap '' Set.range D.datum.root) = ⊤
    rw [← Submodule.map_span]
    change (D.datum.rootSpan ℤ).map e.weightEquiv.toLinearMap = ⊤
    rw [h, Submodule.map_top, LinearMap.range_eq_top.mpr e.weightEquiv.surjective]
  let i := hopfIsoEquiv (extendedGroupIso (k := F) L)
    (coordinateHopfIso P.pinned.pair.G) (coordinateHopfIso R.descent.group)
    R.descent.data.groupIso
  exact centreFreeOfRelativeIso i.symm
    (centreFreeOfRootLattice P.pinned.pair.G P.pinned.pair.reductive
      P.pinned.pair.T P.pinned.pair.split P.pinned.pair.maximal
      (rootLattice_eq_top_of_span P.attached hs)) U g hg

/-- Compare the marked adjoint descendant with the full scheme-centre
quotient of the same form. The point maps commute with all coefficient
extensions and automorphisms by naturality. -/
theorem compareMarkedAdjointCoefficients {F L : Type u} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (R : RamifiedReference F L M) (R' : RamifiedReference F L M')
    (hroot : E.datum.rootSpan ℤ = ⊤)
    {G : AffineAlgebraicGroup F} (j : R.descent.group.val ≅ G.val)
    (φ : R.descent.group.val ⟶ R'.descent.group.val) (hφ : IsCentralIsogeny φ)
    (Q : AdjointQuotient G) :
    ∃ e : R'.descent.group.val ≅ Q.quotient.val,
      φ ≫ e.hom = j.hom ≫ Q.projection ∧ NaturalPointComparison e :=
  compareAdjointQuotient φ hφ (markedAdjointCentreFree R' hroot) j Q

end MarkedPoints

section PinnedDescent

open Specs.QuasiSplitInnerForms (PinnedRepresentative pinnedSection trivialOuterAction)
open Specs.PinnedPairDescent (DescendedPair)
open Specs.RelativeFormComparison (fieldTest fieldMap transportedAut HopfConjugates)
open Specs.AdjointCocharacters (coordinateHopfIso)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (Cocycle restriction)
open private groundIso restrict_ground restrict_trans hopfIsoEquiv hopfIsoEquiv_trans restrict_hopfIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison
open private extendedGroupIso extendedSpecIso_hom_fst from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private isoOfInvariant pinnedHopfDifference raiseInversePullback
  conjugatesByTransportedDifference relativeInversePullback
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
open private inversePullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.PinnedPairDescent
open private transportedDifference transportedDifference_raise from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms

attribute [local instance] Specs.QuasiSplitInnerForms.basedAutTopology
  Specs.QuasiSplitInnerForms.basedAutDiscrete Specs.QuasiSplitInnerForms.fieldGalTopology

/-- A prescribed finite pinned descent gives the inflated pinned
displacement over the separable closure. -/
theorem inflatedPinnedTrivialization
    {F S : Type u} [Field F] [Field S] [Algebra F S] [IsSepClosure F S]
    (L : FiniteGaloisIntermediateField F S)
    {A : RootGroups.AdditiveLine F} {P : Pinning.PinnedGroup A} {D : Pinning.AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q) (ω : Gal(L/F) →* Aut D.toBased)
    (W : DescendedPair (l := l) L ω) :
    ∃ i : relativePoints P.pair.G.val (fieldTest F S) ≅
        relativePoints W.group.val (fieldTest F S),
      ∀ σ, transportedAut F S i σ = pinnedSection E (ω (restriction L σ)) := by
  let h := _root_.LinearAlgebraicGroups.Descent.Forms.raiseIso (S := S) W.data.groupIso
  let t := extendedGroupIso (k := F) S
  let p := coordinateHopfIso P.pair.G
  let w := coordinateHopfIso W.group
  let i := hopfIsoEquiv t p w h
  refine ⟨i, fun σ => ?_⟩
  let f := Functor.mapAut P (forgetPinning (A := A)) (l (ω (restriction L σ)))
  have hd : transportedDifference h σ = inversePullback (K := S) (G := P.pair.G) f := by
    change transportedDifference
      (_root_.LinearAlgebraicGroups.Descent.Forms.raiseIso W.data.groupIso) σ = _
    rw [transportedDifference_raise L, pinnedHopfDifference, W.outer_eq]
    exact raiseInversePullback L f
  have hr := restrict_hopfIso t (extendedSpecIso_hom_fst S) p w σ
    (conjugatesByTransportedDifference h σ)
  apply Aut.ext
  change restrictIso (fieldMap F S σ) i ≪≫ i.symm =
    (pinnedSection E (ω (restriction L σ))).asIso
  rw [hr, hopfIsoEquiv_trans t p p w, Iso.trans_assoc]
  change hopfIsoEquiv t p p (transportedDifference h σ).asIso ≪≫
    (i ≪≫ i.symm) = _
  rw [Iso.self_symm_id, Iso.trans_refl, hd,
    show pinnedSection E (ω (restriction L σ)) = scalarAut f (fieldTest F S)
      from E.sectionOnConstants _ _]
  exact relativeInversePullback (S := S) P.pair.G f

/-- Two descents with equal inflated displacement after a ground-field
comparison are isomorphic over the ground field. -/
theorem compareDescents
    {F S : Type u} [Field F] [Field S] [Algebra F S] [IsSepClosure F S]
    {G G' U V : AffineAlgebraicGroup F} (e : G.val ≅ G'.val)
    (i : relativePoints G'.val (fieldTest F S) ≅ relativePoints U.val (fieldTest F S))
    (j : relativePoints G.val (fieldTest F S) ≅ relativePoints V.val (fieldTest F S))
    (h : ∀ σ, transportedAut F S j σ =
      (Aut.autMulEquivOfIso (groundIso (S := S) e).symm) (transportedAut F S i σ)) :
    Nonempty (U.val ≅ V.val) := by
  let E := groundIso (S := S) e
  have heq (σ : Gal(S/F)) : transportedAut F S (E ≪≫ i) σ = transportedAut F S j σ := by
    rw [h σ]
    apply Aut.ext
    change restrictIso (fieldMap F S σ) (E ≪≫ i) ≪≫ (E ≪≫ i).symm =
      E ≪≫ (restrictIso (fieldMap F S σ) i ≪≫ i.symm) ≪≫ E.symm
    rw [restrict_trans]
    have hE : restrictIso (fieldMap F S σ) E = E := restrict_ground e σ
    rw [hE]
    apply Iso.ext
    simp
  obtain ⟨C⟩ := _root_.LinearAlgebraicGroups.Descent.RelativeFormComparison.relativeFormClassification
    (S := S) U
  apply isoOfInvariant C ((E ≪≫ i).symm ≪≫ j)
  intro σ
  have hd := _root_.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.differenceOfTrivializations
    (E ≪≫ i) j σ
  rw [heq σ, mul_inv_cancel, map_one] at hd
  have hc := congrArg (fun a => a.asIso) hd
  dsimp only [transportedAut] at hc
  change restrictIso (fieldMap F S σ) ((E ≪≫ i).symm ≪≫ j) ≪≫
    ((E ≪≫ i).symm ≪≫ j).symm = Iso.refl _ at hc
  have hcomp := congrArg (fun f => f ≪≫ ((E ≪≫ i).symm ≪≫ j)) hc
  simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl, Iso.refl_trans] using hcomp

open Specs.Pinning (AttachedDatum BasedIso PinnedIso PinnedGroup transportCharacter)
open Specs.CharacterDescent (Character Cocharacter)
open _root_.LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open _root_.LinearAlgebraicGroups.Classification.PinnedUniqueness (pinnedIsoUniqueness)
open _root_.LinearAlgebraicGroups.Descent.AutomorphismSequence
  (exactSequence_exists adjointTorus_exists splitSequence_of_geometry)
open private pinnedLift basedIso_ext_weight from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
open private localPairAlignment recognizesBasedAction_of_lattices pinnedScalarAligned
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

private def pinnedDatumAction {F : Type u} [Field F] {A : RootGroups.AdditiveLine F}
    {P : PinnedGroup A} (D : AttachedDatum P.pair) : Aut P →* Aut D.toBased where
  toFun f := Aut.of ((Groupoid.isoEquivHom _ _).symm (inducedBasedIso f.asIso.hom D D))
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply basedIso_ext_weight
    intro x
    change Additive.ofMul (𝟙 _ ≫ Additive.toMul x) = x
    rw [Category.id_comp]
    rfl
  map_mul' f g := by
    apply Aut.ext
    apply Iso.ext
    apply basedIso_ext_weight
    intro x
    change Additive.ofMul ((f.asIso.hom.torus.inv ≫ g.asIso.hom.torus.inv) ≫ Additive.toMul x) =
      Additive.ofMul (f.asIso.hom.torus.inv ≫ g.asIso.hom.torus.inv ≫ Additive.toMul x)
    rw [Category.assoc]

private theorem pinnedDatumAction_bijective
    {F : Type u} [Field F] {A : RootGroups.AdditiveLine F}
    {P : PinnedGroup A} (D : AttachedDatum P.pair) : Function.Bijective (pinnedDatumAction D) := by
  constructor
  · intro f g h
    apply Aut.ext
    apply Iso.ext
    apply pinnedIsoUniqueness
    intro χ
    exact Additive.ofMul.injective
      (congrArg (fun a : Aut D.toBased =>
        a.asIso.hom.val.weightEquiv (Additive.ofMul χ)) h)
  · intro d
    obtain ⟨f, hf⟩ := pinnedLift P P D D d.asIso.hom
    refine ⟨Aut.of ((Groupoid.isoEquivHom _ _).symm f), ?_⟩
    apply Aut.ext
    apply Iso.ext
    exact hf

/-- Choose a split sequence whose datum is the one in the supplied marking. -/
theorem splitSequenceForAttachedDatum
    {F : Type u} [Field F] {A : RootGroups.AdditiveLine F}
    {P : PinnedGroup A} (D : AttachedDatum P.pair) :
    ∃ (l : Aut D.toBased ≃* Aut P) (Q : AdjointQuotient P.pair.G),
      Nonempty (SplitSequence P D l Q) := by
  let m := MulEquiv.ofBijective (pinnedDatumAction D) (pinnedDatumAction_bijective D)
  let l := m.symm
  have hl (d : Aut D.toBased) :
      let f := (l d).asIso.hom
      (∀ χ : Character P.pair.T.group,
        d.asIso.hom.val.weightEquiv (Additive.ofMul χ) =
          Additive.ofMul (transportCharacter f.torus χ)) ∧
      (∀ c : Cocharacter P.pair.T.group,
        d.asIso.hom.val.coweightEquiv (Additive.ofMul c) =
          Additive.ofMul (c ≫ f.torus.inv)) := by
    have hd : inducedBasedIso (l d).asIso.hom D D = d.asIso.hom :=
      congrArg (fun t => t.asIso.hom) (m.apply_symm_apply d)
    dsimp only
    rw [← hd]
    constructor <;> intro _ <;> rfl
  obtain ⟨Q, O, ⟨H⟩⟩ := exactSequence_exists P.pair.G
  obtain ⟨T⟩ := adjointTorus_exists P D Q
  exact ⟨l, Q, splitSequence_of_geometry l hl H T
    (recognizesBasedAction_of_lattices l hl) (localPairAlignment P)⟩

/-- The pinned section acts on the actual character lattice by its
prescribed based automorphism. -/
theorem pinnedSectionDatumAction {F : Type u} [Field F] {A : RootGroups.AdditiveLine F}
    {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q) (d : Aut D.toBased) :
    inducedBasedIso (l d).asIso.hom D D = d.asIso.hom := by
  let T := 𝟙_ (SchemeOver F)
  let a := pinnedScalarAligned (l d) T
  have hs := E.sectionOnConstants T d
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app E.rightInverse (op T))
    (show (constantGroup (k := F) (Aut D.toBased)).obj (op T) from
      ⟨LocallyConstant.const _ d⟩)
  change E.toExactSequence.outer.app (op T)
    (E.sectionMap.app (op T) ⟨LocallyConstant.const _ d⟩) = _ at h
  rw [hs] at h
  have he := (E.latticeAction T _ a d h).1
  apply basedIso_ext_weight
  intro x
  let U : Over T := Over.mk (toUnit P.pair.T.group.X)
  have hc := he (Additive.toMul x) U (𝟙 P.pair.T.group.X)
  change ((𝟙 P.pair.T.group.X) ≫ (l d).asIso.hom.torus.inv.hom.hom) ≫
    (Additive.toMul x).hom.hom = (𝟙 P.pair.T.group.X) ≫
      (Additive.toMul (d.asIso.hom.val.weightEquiv x)).hom.hom at hc
  apply Additive.toMul.injective
  apply Grp.hom_ext
  change (l d).asIso.hom.torus.inv.hom.hom ≫ (Additive.toMul x).hom.hom = _
  simpa only [Category.id_comp] using hc


private theorem additiveLine_unique {F : Type u} [Field F]
    (A B : RootGroups.AdditiveLine F) : A = B := by
  have hd := Polynomial.algHom_ext (A.comultiplication.trans B.comultiplication.symm)
  have he := Polynomial.algHom_ext (A.counit.trans B.counit.symm)
  have hi := Polynomial.algHom_ext (A.antipode.trans B.antipode.symm)
  obtain ⟨⟨da, ea, ia, _, _, _, _, _⟩, _, _, _⟩ := A
  obtain ⟨⟨db, eb, ib, _, _, _, _, _⟩, _, _, _⟩ := B
  dsimp only at hd he hi
  subst db eb ib
  rfl

private theorem pinnedIntertwines {F : Type u} [Field F] {A : RootGroups.AdditiveLine F}
    {P P' : PinnedGroup A} {D : AttachedDatum P.pair} {D' : AttachedDatum P'.pair}
    {l : Aut D.toBased ≃* Aut P} {l' : Aut D'.toBased ≃* Aut P'}
    {Q : AdjointQuotient P.pair.G} {Q' : AdjointQuotient P'.pair.G}
    (E : SplitSequence P D l Q) (E' : SplitSequence P' D' l' Q')
    (d : D.toBased ≅ D'.toBased) (f : PinnedIso P P')
    (hf : inducedBasedIso f D D' = d.hom) (a : Aut D.toBased) :
    (l a).asIso.hom ≫ f = f ≫ (l' (Aut.autMulEquivOfIso d a)).asIso.hom := by
  apply pinnedIsoUniqueness
  intro χ
  let b := Aut.autMulEquivOfIso d a
  have he : a.asIso.hom ≫ d.hom = d.hom ≫ b.asIso.hom := by
    change a.asIso.hom ≫ d.hom = d.hom ≫ (d.inv ≫ a.asIso.hom ≫ d.hom)
    simp only [← Category.assoc, d.hom_inv_id, Category.id_comp]
  have hw := congrArg (fun e : BasedIso D.toBased D'.toBased =>
    Additive.toMul (e.val.weightEquiv (Additive.ofMul χ))) he
  rw [← hf, ← pinnedSectionDatumAction E a, ← pinnedSectionDatumAction E' b] at hw
  exact hw

/-- The split pinned comparison conjugates the inflated Galois action, so it
identifies the finite marked descent with the designated pinned representative. -/
private theorem compareMarkedRepresentative
    {F S : Type u} [Field F] [Field S] [Algebra F S] [IsSepClosure F S]
    (L : FiniteGaloisIntermediateField F S)
    {A B : RootGroups.AdditiveLine F} {P : PinnedGroup A} {P' : PinnedGroup B}
    {D : AttachedDatum P.pair} {D' : AttachedDatum P'.pair}
    {l : Aut D.toBased ≃* Aut P} {l' : Aut D'.toBased ≃* Aut P'}
    {Q : AdjointQuotient P.pair.G} {Q' : AdjointQuotient P'.pair.G}
    (E : SplitSequence P D l Q) (E' : SplitSequence P' D' l' Q')
    (d : D.toBased ≅ D'.toBased) (ω : Gal(L/F) →* Aut D.toBased)
    (outer : Cocycle (trivialOuterAction (k := F) (S := S) D.toBased))
    (houter : ∀ σ, outer σ = ω (restriction L σ)) (V : PinnedRepresentative E outer)
    (W : DescendedPair (l := l') L ((Aut.autMulEquivOfIso d).toMonoidHom.comp ω)) :
    Nonempty (W.group.val ≅ V.model.val.val) := by
  have hline := additiveLine_unique A B
  subst B
  obtain ⟨f, hf⟩ := pinnedLift P P' D D' d.hom
  obtain ⟨i, hi⟩ := inflatedPinnedTrivialization L E'
    ((Aut.autMulEquivOfIso d).toMonoidHom.comp ω) W
  obtain ⟨e⟩ := compareDescents f.group i V.trivialization (fun σ => by
    rw [V.transport_eq, hi, houter]
    let a := ω (restriction L σ)
    let b := Aut.autMulEquivOfIso d a
    rw [show pinnedSection (S := S) E a =
      scalarAut ((forgetPinning (A := A)).mapAut P (l a)) (fieldTest F S)
      from E.sectionOnConstants _ _]
    change _ = (Aut.autMulEquivOfIso (groundIso (S := S) f.group).symm)
      (pinnedSection (S := S) E' b)
    rw [show pinnedSection (S := S) E' b =
      scalarAut ((forgetPinning (A := A)).mapAut P' (l' b)) (fieldTest F S)
      from E'.sectionOnConstants _ _]
    apply Aut.ext
    apply Iso.ext
    let J : GroupScheme F ⥤ _ :=
      yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget (fieldTest F S)).op
    change J.map (l a).asIso.hom.group.hom =
      J.map f.group.hom ≫ J.map (l' b).asIso.hom.group.hom ≫ J.map f.group.inv
    apply (cancel_mono (J.map f.group.hom)).mp
    simp only [Category.assoc, ← J.map_comp, f.group.inv_hom_id, Category.comp_id]
    exact J.congr_map (congrArg (fun t : PinnedIso P P' => t.group.hom)
      (pinnedIntertwines E E' d f hf a)))
  exact ⟨e⟩

end PinnedDescent

section Lattices

open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.ExceptionalAffineBruhat (ExceptionalNumbering)
open Specs.ExceptionalValuedTorusNormalizer (simpleCorootBasis)
open Module
open private derivedDatum derivedDatum_coroots_span derivedBase_height
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open private dualRank from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private basedIso_ext_weight from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence

private abbrev dualDatum (D : BasedRootDatum.{u}) : BasedRootDatum.{u} := by
  letI := D.freeX
  letI := D.freeY
  letI := D.finiteRoots
  letI := D.reduced
  letI : Module.IsTorsionFree ℤ D.Y := inferInstance
  exact
    { I := D.I
      X := D.Y
      Y := D.X
      finiteRoots := D.finiteRoots
      freeX := D.freeY
      freeY := D.freeX
      finiteX := D.finiteY
      finiteY := D.finiteX
      datum := D.datum.flip
      reduced := inferInstance
      base := D.base.flip }

/-- The adjoint lattice has the root span for characters and its full
integral dual for cocharacters. The index and simple labels are unchanged. -/
private abbrev adjointDatum (D : BasedRootDatum.{u}) : BasedRootDatum.{u} :=
  dualDatum (derivedDatum (dualDatum D))

private theorem adjointRootSpan (D : BasedRootDatum.{u}) :
    (adjointDatum D).datum.rootSpan ℤ = ⊤ :=
  derivedDatum_coroots_span (dualDatum D)

private theorem exceptionalNumberingOfCorootSpan {D : BasedRootDatum.{u}}
    (h : D.datum.corootSpan ℤ = ⊤) (b : Fin 6 ≃ D.base.support)
    (hb : ∀ i j, D.datum.pairing (b i) (b j) = exceptionalCartan 6 i j) :
    ExceptionalNumbering D 6 b := by
  classical
  let B := (simpleCorootBasis D h).reindex b.symm
  exact ⟨(Module.finrank_eq_card_basis B).trans (Fintype.card_fin _), hb⟩

private theorem adjointNumbering {D : BasedRootDatum.{u}}
    (b : Fin 6 ≃ D.base.support)
    (hb : ∀ i j, D.datum.pairing (b i) (b j) = exceptionalCartan 6 i j) :
    ExceptionalNumbering (adjointDatum D) 6 b := by
  classical
  have h := (exceptionalNumberingOfCorootSpan
    (D := dualDatum (adjointDatum D)) (adjointRootSpan D) b (fun i j => by
      change D.datum.pairing (b j) (b i) = exceptionalCartan 6 i j
      rw [hb j i]
      fin_cases i <;> fin_cases j <;> decide)).1
  letI := D.freeX
  letI := D.finiteX
  refine ⟨?_, hb⟩
  change Module.finrank ℤ (Dual ℤ (D.datum.rootSpan ℤ)) = 6
  rw [dualRank]
  exact h

private def adjointWeightEquiv {D : BasedRootDatum.{u}} (e : BasedIso D D) :
    (adjointDatum D).X ≃ₗ[ℤ] (adjointDatum D).X := by
  have h : (D.datum.rootSpan ℤ).map e.val.weightEquiv.toLinearMap =
      D.datum.rootSpan ℤ := by
    unfold RootPairing.rootSpan
    rw [Submodule.map_span, ← Set.range_comp]
    have he : e.val.weightEquiv.toLinearMap ∘ D.datum.root =
        D.datum.root ∘ e.val.indexEquiv := funext fun i =>
      e.val.toHom.root_weightMap_apply _ _ i
    rw [he, Set.range_comp, e.val.indexEquiv.surjective.range_eq, Set.image_univ]
  exact (e.val.weightEquiv.submoduleMap (D.datum.rootSpan ℤ)).trans
    (LinearEquiv.ofEq _ _ h)

private theorem adjointWeightEquiv_apply {D : BasedRootDatum.{u}} (e : BasedIso D D)
    (x : (adjointDatum D).X) :
    (adjointWeightEquiv e x).val = e.val.weightEquiv x.val := rfl

private def adjointBasedIso {D : BasedRootDatum.{u}} (e : BasedIso D D) :
    BasedIso (adjointDatum D) (adjointDatum D) := by
  let a := adjointWeightEquiv e
  refine ⟨{
    weightMap := a.toLinearMap
    coweightMap := a.dualMap.toLinearMap
    indexEquiv := e.val.indexEquiv
    bijective_weightMap := a.bijective
    bijective_coweightMap := a.dualMap.bijective
    weight_coweight_transpose := rfl
    root_weightMap := ?_
    coroot_coweightMap := ?_ }, e.property⟩
  · funext i
    apply Subtype.ext
    exact e.val.toHom.root_weightMap_apply _ _ i
  · funext i
    ext x
    change D.datum.toLinearMap (e.val.weightEquiv x.val) (D.datum.coroot i) =
      D.datum.toLinearMap x.val (D.datum.coroot (e.val.indexEquiv.symm i))
    have hp := DFunLike.congr_fun
      (e.val.toHom.weight_coweight_transpose_apply _ _ (D.datum.coroot i)) x.val
    change D.datum.toLinearMap (e.val.weightEquiv x.val) (D.datum.coroot i) =
      D.datum.toLinearMap x.val (e.val.coweightEquiv (D.datum.coroot i)) at hp
    rw [show e.val.coweightEquiv (D.datum.coroot i) =
      D.datum.coroot (e.val.indexEquiv.symm i) from e.val.toHom.coroot_coweightMap_apply _ _ i] at hp
    exact hp

private def adjointDatumAction (D : BasedRootDatum.{u}) : Aut D →* Aut (adjointDatum D) where
  toFun e := Aut.of ((Groupoid.isoEquivHom _ _).symm (adjointBasedIso e.asIso.hom))
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply basedIso_ext_weight
    intro x
    apply Subtype.ext
    rfl
  map_mul' e f := by
    apply Aut.ext
    apply Iso.ext
    apply basedIso_ext_weight
    intro x
    apply Subtype.ext
    rfl

end Lattices

section IntegralTorsor

attribute [-instance] ULift.module

open Specs.IntegralSemisimpleModel (Integers IntegralGroup fibre integerAlgebra)
open Specs.IntegralCentralQuotient (HopfSpectrum spectrumOfHopfHom IsRightTorsor IsCentral)
open private rightTorsor_over central_translation fibreMap_property
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralCentralQuotient

private theorem kernelOfTranslationPullback {C : Type*} [Category C]
    [CartesianMonoidalCategory C] {G H Z : Grp C} (q : G ⟶ H) (z : Z ⟶ G)
    (h : IsPullback (fst G.X Z.X)
      (fst G.X Z.X * (snd G.X Z.X ≫ z.hom.hom)) q.hom.hom q.hom.hom) :
    IsPullback z.hom.hom (toUnit Z.X) q.hom.hom η[H.X] := by
  have hw : z.hom.hom ≫ q.hom.hom = toUnit Z.X ≫ η[H.X] := by
    have h' := congrArg (fun f => lift (1 : Z.X ⟶ G.X) (𝟙 Z.X) ≫ f) h.w
    have hr : lift (1 : Z.X ⟶ G.X) (𝟙 Z.X) ≫
        (fst G.X Z.X * (snd G.X Z.X ≫ z.hom.hom)) = z.hom.hom := by
      simp only [MonObj.comp_mul, lift_fst, lift_snd_assoc, Category.id_comp, one_mul]
    rw [← Category.assoc, ← Category.assoc, lift_fst, hr, MonObj.one_comp] at h'
    exact h'.symm
  have equalImages (s : PullbackCone q.hom.hom η[H.X]) :
      (1 : s.pt ⟶ G.X) ≫ q.hom.hom = s.fst ≫ q.hom.hom := by
    rw [s.condition, MonObj.one_comp, toUnit_unique s.snd (toUnit s.pt)]
    rfl
  let t (s : PullbackCone q.hom.hom η[H.X]) := h.lift 1 s.fst (equalImages s)
  have ht (s : PullbackCone q.hom.hom η[H.X]) : t s ≫ fst G.X Z.X = 1 :=
    h.lift_fst _ _ _
  have hx (s : PullbackCone q.hom.hom η[H.X]) :
      (t s ≫ snd G.X Z.X) ≫ z.hom.hom = s.fst := by
    have h' := h.lift_snd (1 : s.pt ⟶ G.X) s.fst (equalImages s)
    simpa only [t, MonObj.comp_mul, ht, one_mul, Category.assoc] using h'
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
    (PullbackCone.IsLimit.mk hw (fun s => t s ≫ snd G.X Z.X) hx
      (fun _ => toUnit_unique _ _) ?_)
  intro s m hm _
  have hpair : lift (1 : s.pt ⟶ G.X) m = t s := by
    apply h.hom_ext
    · rw [lift_fst, ht]
    · rw [h.lift_snd]
      simp only [MonObj.comp_mul, lift_fst, lift_snd_assoc, one_mul, hm]
  simpa only [lift_snd] using congrArg (· ≫ snd G.X Z.X) hpair

private theorem integralFibreTorsor
    {A B N : Type u} [CommRing A] [CommRing B] [HopfAlgebra Integers.{u} A]
    [HopfAlgebra Integers.{u} B] [CommGroup N]
    (j : B →ₐc[Integers.{u}] A) (π : A →ₐc[Integers.{u}] MonoidAlgebra Integers.{u} N)
    (h : IsRightTorsor j π) (hc : IsCentral π) (hπ : Function.Surjective π)
    (k : Type u) [Field k] :
    ∃ hz : IsClosedImmersion ((fibre k).map (spectrumOfHopfHom π)).hom.hom.left,
      let Z : ClosedSubgroup ((fibre k).obj (HopfSpectrum Integers A)) :=
        ⟨_, (fibre k).map (spectrumOfHopfHom π), hz⟩
      IsSchemeKernel ((fibre k).map (spectrumOfHopfHom j)) Z ∧
        Centralizes (𝟙 _) Z.inclusion.hom.hom := by
  classical
  letI := integerAlgebra k
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k)))
  let G := HopfSpectrum Integers.{u} A
  let H := HopfSpectrum Integers.{u} B
  let Z := HopfSpectrum Integers.{u} (MonoidAlgebra Integers.{u} N)
  let q := spectrumOfHopfHom j
  let z := spectrumOfHopfHom π
  let z' := (fibre k).map z
  let G' := (fibre k).obj G
  let Z' := (fibre k).obj Z
  letI : GrpObj (F.obj G.X) := G'.grp
  let e := (prodComparisonIso F G.X Z.X).symm
  have hfst : e.hom ≫ F.map (fst G.X Z.X) = fst G'.X Z'.X := by
    change (prodComparisonIso F G.X Z.X).inv ≫ F.map (fst G.X Z.X) = fst (F.obj G.X) (F.obj Z.X)
    rw [← CartesianMonoidalCategory.prodComparison_fst, ← prodComparisonIso_hom,
      Iso.inv_hom_id_assoc]
  have hsnd : e.hom ≫ F.map (snd G.X Z.X) = snd G'.X Z'.X := by
    change (prodComparisonIso F G.X Z.X).inv ≫ F.map (snd G.X Z.X) = snd (F.obj G.X) (F.obj Z.X)
    rw [← CartesianMonoidalCategory.prodComparison_snd, ← prodComparisonIso_hom,
      Iso.inv_hom_id_assoc]
  have hmap :
      e.hom ≫ F.map (fst G.X Z.X * (snd G.X Z.X ≫ z.hom.hom)) =
        fst G'.X Z'.X * (snd G'.X Z'.X ≫ z'.hom.hom) := by
    rw [F.map_mul, MonObj.comp_mul, hfst, F.map_comp, ← Category.assoc, hsnd]
    rfl
  have hp : IsPullback (fst G'.X Z'.X)
      (fst G'.X Z'.X * (snd G'.X Z'.X ≫ z'.hom.hom))
      ((fibre k).map q).hom.hom ((fibre k).map q).hom.hom :=
    ((rightTorsor_over π j h).map F).of_iso' e
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.comp_id] using hfst)
    (by simpa only [Iso.refl_hom, Category.comp_id] using hmap)
    (by
      change 𝟙 _ ≫ F.map q.hom.hom = F.map q.hom.hom ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id])
    (by
      change 𝟙 _ ≫ F.map q.hom.hom = F.map q.hom.hom ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id])
  have hk := kernelOfTranslationPullback ((fibre k).map q) z' hp
  have hclosed : IsClosedImmersion z'.hom.hom.left := by
    exact fibreMap_property k z @IsClosedImmersion
      (IsClosedImmersion.spec_of_surjective _ hπ)
  let C : ClosedSubgroup G' := ⟨Z', z', hclosed⟩
  refine ⟨hclosed, hk, ?_⟩
  have hcenter := central_translation π hc (fst G.X Z.X) (snd G.X Z.X)
  have hm := congrArg (fun f => e.hom ≫ F.map f) hcenter
  rw [hmap, F.map_mul, MonObj.comp_mul, hfst, F.map_comp, ← Category.assoc, hsnd] at hm
  rw [centralizes_iff]
  intro U a x
  change fst G'.X Z'.X * (snd G'.X Z'.X ≫ z'.hom.hom) =
    (snd G'.X Z'.X ≫ z'.hom.hom) * fst G'.X Z'.X at hm
  have hu' := congrArg (fun f => lift x a ≫ f) hm
  change (a ≫ C.inclusion.hom.hom) * x = x * (a ≫ C.inclusion.hom.hom)
  have hl : lift x a ≫ fst G'.X Z'.X = x := lift_fst _ _
  have hr : lift x a ≫ (snd G'.X Z'.X ≫ z'.hom.hom) = a ≫ z'.hom.hom := lift_snd_assoc _ _ _
  rw [MonObj.comp_mul, MonObj.comp_mul, hl, hr] at hu'
  exact hu'.symm

end IntegralTorsor

section IntegralAdjoint

open WithConv
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.IntegralCentralQuotient
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover PreservesIntegralMarking integralPointHom)
open Specs.ExceptionalMarkedRootDescent (markedRootPoint MarkedFibre)
open Specs.CentralIsogenies (IsTorusRestriction)
open Spec IntegralCentralQuotient

attribute [-instance] ULift.module

private abbrev ZRing := Integers.{u}

open private affineSpectrum coordinatePoints coordinatePoints_comp coordinatePoints_polynomial
  coordinatePoints_antipode markedTorusCoordinates markedTorusCoordinates_spec
  markedRootCoordinates markedRootCoordinates_spec integralPointMap
  rankOneCoordinates torusValuesOfAlgHom torusValuesOfAlgHom_eq torusValuesOfAlgHom_apply
  torusPoint_as_coordinates cellDomainIso markedCellCoordinates_spec orderedCell
  model_reductiveFibres reductiveFibres_precompose rootOrderings_exist
  integralGroup_geometricallyIntegral smoothConnectedOfGeometricFibres
  markedTorusCoordinates_surjective markedRootCoordinates_surjective central_of_openRootCell
  modelOfMarking rankOneNatural rankOneNatural_apply_upper rankOneNatural_apply_lower
  rankOneNatural_apply_diagonal quotientTorusRestriction_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization

private def integralRankOneCoordinates {D : BasedRootDatum.{u}} (M : Model D)
    {A : CommHopfAlgCat.{u} ZRing} (e : HopfSpectrum ZRing A ≅ M.group) (a : D.I) :
    RankOneMap ZRing A :=
  rankOneCoordinates (M.rankOne a ≫ Functor.whiskerLeft integralSpec.rightOp
    (yonedaGrp.map e.inv))

private def corootOnCharacters (D : BasedRootDatum.{u}) (a : D.I) :
    Multiplicative D.X →* Multiplicative ℤ :=
  (D.datum.coroot' a).toAddMonoidHom.toMultiplicative

private theorem cocharacterEval_eq {D : BasedRootDatum.{u}} (a : D.I)
    (S : IntegralAlgebra.{u}) (s : Sˣ) :
    coordinatePoints S (toConv (cocharacterEval (corootOnCharacters D a) S s)) =
      torusPoint D S (cocharacter D (D.datum.coroot a) S s) := rfl

private theorem integralRankOneCompatibility {D : BasedRootDatum.{u}} (M : Model D)
    {A : CommHopfAlgCat.{u} ZRing} (e : HopfSpectrum ZRing A ≅ M.group) (a : D.I) :
    RankOneCompatibility (markedTorusCoordinates e M.torus)
      (markedRootCoordinates e (M.root a))
      (markedRootCoordinates e (M.root (D.datum.reflectionPerm a a)))
      (corootOnCharacters D a) (integralRankOneCoordinates M e a) := by
  let r := integralRankOneCoordinates M e a
  have hc (S : IntegralAlgebra.{u}) (s : Matrix.SpecialLinearGroup (Fin 2) S) :
      coordinatePoints S (r.hom S s) = (M.rankOne a).app S s ≫ e.inv.hom.hom := by
    exact (coordinatePoints S).apply_symm_apply _
  constructor
  · intro S z
    constructor
    · apply WithConv.toConv_injective
      apply (coordinatePoints S).injective
      rw [coordinatePoints_polynomial, markedRootCoordinates_spec, ← Category.assoc]
      exact (hc S _).trans (congrArg (· ≫ e.inv.hom.hom) (M.rankOneUpper a S z))
    · apply WithConv.toConv_injective
      apply (coordinatePoints S).injective
      rw [coordinatePoints_polynomial, markedRootCoordinates_spec, ← Category.assoc]
      exact (hc S _).trans (congrArg (· ≫ e.inv.hom.hom) (M.rankOneLower a S z))
  · intro S s
    apply WithConv.toConv_injective
    apply (coordinatePoints S).injective
    rw [coordinatePoints_comp, markedTorusCoordinates_spec,
      Grp.comp_hom_hom, ← Category.assoc, cocharacterEval_eq]
    exact (hc S _).trans (congrArg (· ≫ e.inv.hom.hom) (M.rankOneDiagonal a S s))

private theorem integralRootScalarAction {D : BasedRootDatum.{u}} (M : Model D)
    {A : CommHopfAlgCat.{u} ZRing} (e : HopfSpectrum ZRing A ≅ M.group) (a : D.I) :
    RootScalarAction (markedTorusCoordinates e M.torus)
      (markedRootCoordinates e (M.root a)) (Multiplicative.ofAdd (D.datum.root a)) := by
  intro S r p
  dsimp only
  apply (coordinatePoints S).injective
  simp only [map_mul, coordinatePoints_antipode, coordinatePoints_comp,
    coordinatePoints_polynomial, markedRootCoordinates_spec, markedTorusCoordinates_spec,
    Grp.comp_hom_hom, ← Category.assoc]
  let f := integralPointMap e.inv S
  change f _ * f _ * (f _)⁻¹ = f _
  let v := torusValuesOfAlgHom S p
  have hpoint : coordinatePoints S (toConv p) = torusPoint D S v := by
    rw [torusPoint_as_coordinates, torusValuesOfAlgHom_eq]
  rw [hpoint]
  have hv : (v (Multiplicative.ofAdd (D.datum.root a)) : S) =
      p (MonoidAlgebra.of ZRing _ (Multiplicative.ofAdd (D.datum.root a))) :=
    torusValuesOfAlgHom_apply _ _ _
  let a₀ : IntegralPoints M.group S := torusPoint D S v ≫ M.torus.hom.hom
  let x₀ : IntegralPoints M.group S := M.line.point S r ≫ (M.root a).hom.hom
  let y₀ : IntegralPoints M.group S :=
    M.line.point S ((v (Multiplicative.ofAdd (D.datum.root a)) : S) * r) ≫ (M.root a).hom.hom
  have hc : a₀ * x₀ * a₀⁻¹ = y₀ := M.conjugation S v a r
  have he : f (a₀ * x₀ * a₀⁻¹) = f y₀ := congrArg f hc
  simp only [map_mul] at he
  have hi : f (a₀⁻¹) = (f a₀)⁻¹ := map_inv f a₀
  rw [hi] at he
  change f a₀ * f x₀ * (f a₀)⁻¹ =
    f (M.line.point S (p (MonoidAlgebra.of ZRing _ (Multiplicative.ofAdd (D.datum.root a))) * r) ≫
      (M.root a).hom.hom)
  rw [← hv]
  exact he

open private quotientCell spectrumOfHopfHom_comp spectrumOfAlgHom_comp
  torusProjection_torsor characterRestriction_surjective fibreMap_property
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
open private lineProductIso markedRootProduct_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization

private abbrev rootCharacters (D : BasedRootDatum.{u}) : Subgroup (Multiplicative D.X) :=
  (D.datum.rootSpan ℤ).toAddSubgroup.toSubgroup

private abbrev characterQuotient (D : BasedRootDatum.{u}) :
    Multiplicative D.X →* (Multiplicative D.X ⧸ rootCharacters D) :=
  QuotientGroup.mk' (rootCharacters D)

private def adjointCharacters (D : BasedRootDatum.{u}) :
    Multiplicative (adjointDatum D).X ≃* (characterQuotient D).ker where
  toFun x := ⟨Multiplicative.ofAdd x.toAdd.val, by
    rw [QuotientGroup.ker_mk']
    exact x.toAdd.property⟩
  invFun x := Multiplicative.ofAdd ⟨x.val.toAdd, by
    generalize hx : x.val = a
    have h : a ∈ (characterQuotient D).ker := hx ▸ x.property
    rw [QuotientGroup.ker_mk'] at h
    exact h⟩
  left_inv x := rfl
  right_inv x := rfl
  map_mul' x y := rfl

private def adjointTorusIso (D : BasedRootDatum.{u}) :
    HopfSpectrum ZRing (MonoidAlgebra ZRing (characterQuotient D).ker) ≅
      splitTorus (adjointDatum D) :=
  (hopfSpec (CommRingCat.of ZRing)).mapIso
    (CommHopfAlgCat.isoMk
      (MonoidAlgebra.domCongrBialgEquiv ZRing ZRing (adjointCharacters D))).op

private theorem adjointPositive (D : BasedRootDatum.{u}) (i : D.I) :
    D.base.IsPos i ↔ (adjointDatum D).base.IsPos i := by
  obtain ⟨f, _, _, hf⟩ := D.base.exists_root_eq_sum_int i
  have h : (adjointDatum D).datum.root i =
      ∑ j ∈ (adjointDatum D).base.support, f j • (adjointDatum D).datum.root j := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact hf
  rw [RootPairing.Base.isPos_iff, RootPairing.Base.isPos_iff,
    RootPairing.Base.height_eq_sum h, RootPairing.Base.height_eq_sum hf]
  rfl

private theorem integralModelIntegral {D : BasedRootDatum.{u}} (M : Model D) :
    IsIntegral M.group.X.left := by
  letI : IsDomain ZRing := ULift.ringEquiv.injective.isDomain (ULift.ringEquiv : ZRing ≃+* ℤ)
  letI : IsNoetherianRing ZRing := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  letI : IsIntegral Base.{u} := inferInstanceAs (IsIntegral (Spec (CommRingCat.of ZRing)))
  letI : IsLocallyNoetherian Base.{u} :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of ZRing)))
  letI := M.smooth
  letI := M.quasiCompact
  letI := M.connected
  letI := integralGroup_geometricallyIntegral M.group
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian M.group.X.hom

private abbrev IntegralFibreQuotient {G H T T' : IntegralGroup.{u}}
    (t : T ⟶ G) (map : G ⟶ H) (torusMap : T ⟶ T') (k : Type u) [Field k] : Prop :=
    let q := (fibre k).map map
    let qT := (fibre k).map torusMap
    IsFinite q.hom.hom.left ∧ Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
      Flat qT.hom.hom.left ∧ Surjective qT.hom.hom.left ∧
      ∃ (Z : ClosedSubgroup ((fibre k).obj G)) (z : Z.group ⟶ (fibre k).obj T),
        z ≫ (fibre k).map t = Z.inclusion ∧ IsSchemeKernel q Z ∧
          Centralizes (𝟙 _) Z.inclusion.hom.hom

private structure MarkedQuotientMap {D E : BasedRootDatum.{u}} (M : Model D) (N : Model E) where
  map : M.group ⟶ N.group
  torusMap : splitTorus D ⟶ splitTorus E
  torusComm : M.torus ≫ map = torusMap ≫ N.torus
  fibre : ∀ (k : Type u) [Field k], IntegralFibreQuotient M.torus map torusMap k

set_option maxHeartbeats 500000 in
private theorem integralQuotientOnFibre {G H Q T T₀ T₁ Z : IntegralGroup.{u}}
    (t : T ⟶ G) (e : H ≅ G) (eT : T₀ ≅ T₁) (q : H ⟶ Q) (p : T ⟶ T₀)
    (j : Z ⟶ H) (i : Z ⟶ T) (hcomm : j ≫ e.hom = i ≫ t)
    (hfin : IsFinite q.hom.hom.left) (hflat : Flat q.hom.hom.left)
    (hsurj : Surjective q.hom.hom.left) (hflatT : Flat p.hom.hom.left)
    (hsurjT : Surjective p.hom.hom.left) (k : Type u) [Field k]
    (hz : IsClosedImmersion ((fibre k).map j).hom.hom.left)
    (hk : IsSchemeKernel ((fibre k).map q) ⟨_, (fibre k).map j, hz⟩)
    (hc : Centralizes (𝟙 ((fibre k).obj H)) ((fibre k).map j).hom.hom) :
    IntegralFibreQuotient t (e.inv ≫ q) (p ≫ eT.hom) k := by
  letI := integerAlgebra k
  let F := fibre k
  let U := Grp.forget (SchemeOver k)
  let W := F ⋙ U ⋙ Over.forget _
  let ek := F.mapIso e
  let jz := F.map j
  let jz' := jz ≫ ek.hom
  have hclosed : IsClosedImmersion jz'.hom.hom.left := by
    change IsClosedImmersion (jz.hom.hom.left ≫ (U ⋙ Over.forget _).map ek.hom)
    letI := hz
    infer_instance
  let Z' : ClosedSubgroup (F.obj G) := ⟨F.obj Z, jz', hclosed⟩
  have hker : IsSchemeKernel (F.map (e.inv ≫ q)) Z' := by
    refine hk.of_iso' (Iso.refl _) (U.mapIso ek.symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · change 𝟙 _ ≫ jz.hom.hom = (jz.hom.hom ≫ ek.hom.hom.hom) ≫ ek.inv.hom.hom
      have hcancel : ek.hom.hom.hom ≫ ek.inv.hom.hom = 𝟙 _ := (U.mapIso ek).hom_inv_id
      rw [Category.id_comp, Category.assoc, hcancel, Category.comp_id]
    · simp
    · change ek.inv.hom.hom ≫ (F.map q).hom.hom = (F.map (e.inv ≫ q)).hom.hom ≫ 𝟙 _
      rw [Category.comp_id, F.map_comp]
      rfl
    · simp
  have hcen : Centralizes (𝟙 _) Z'.inclusion.hom.hom := (innerAut_eq_one_iff _).mp
    (mapsCentralPointIso ek jz.hom.hom ((innerAut_eq_one_iff _).mpr hc))
  have source {P : MorphismProperty Scheme.{u}} [P.RespectsIso] :
      P (W.map (e.inv ≫ q)) ↔ P (W.map q) := by
    rw [W.map_comp e.inv q]
    exact MorphismProperty.cancel_left_of_respectsIso P (W.map e.inv) (W.map q)
  have target {P : MorphismProperty Scheme.{u}} [P.RespectsIso] :
      P (W.map (p ≫ eT.hom)) ↔ P (W.map p) := by
    rw [W.map_comp p eT.hom]
    exact MorphismProperty.cancel_right_of_respectsIso P (W.map p) (W.map eT.hom)
  refine ⟨source.mpr (fibreMap_property k q @IsFinite hfin),
    source.mpr (fibreMap_property k q @Flat hflat),
    source.mpr (fibreMap_property k q @Surjective hsurj),
    target.mpr (fibreMap_property k p @Flat hflatT),
    target.mpr (fibreMap_property k p @Surjective hsurjT), Z', F.map i, ?_, hker, hcen⟩
  change F.map i ≫ F.map t = F.map j ≫ F.map e.hom
  rw [← F.map_comp, ← F.map_comp, hcomm]

private theorem markedQuotientFibre {D E : BasedRootDatum.{u}} {M : Model D} {N : Model E}
    (c : MarkedQuotientMap M N) (k : Type u) [Field k]
    (C : MarkedFibre M k) (C' : MarkedFibre N k) :
    let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
    let fT := C.torusIso.inv ≫ (fibre k).map c.torusMap ≫ C'.torusIso.hom
    IsCentralIsogeny f ∧ IsTorusRestriction f fT ∧
      ∃ Z : ClosedSubgroup C.realization.pinned.pair.G.val,
        IsSchemeKernel f Z ∧
          Specs.SchemeDerivedGroup.IsSubgroupOf Z C.realization.pinned.pair.T ∧
          Centralizes (𝟙 _) Z.inclusion.hom.hom := by
  let F := fibre k
  let T := C.realization.pinned.pair.T
  let T' := C'.realization.pinned.pair.T
  let e := C.groupIso
  let e' := C'.groupIso
  let t := C.torusIso
  let t' := C'.torusIso
  let q := F.map c.map
  let qT := F.map c.torusMap
  obtain ⟨hfin, hflat, hsurj, hflatT, hsurjT, Z, z, hz, hk, hc⟩ := c.fibre k
  let U := Grp.forget (SchemeOver k)
  let W := U ⋙ Over.forget _
  let f := e.inv ≫ q ≫ e'.hom
  let fT := t.inv ≫ qT ≫ t'.hom
  have property {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
      {X Y X' Y' : GroupScheme k} (a : X ≅ X') (b : Y ≅ Y') (g : X ⟶ Y)
      (h : P (W.map g)) : P (W.map (a.inv ≫ g ≫ b.hom)) := by
    simp only [Functor.map_comp, MorphismProperty.cancel_left_of_respectsIso,
      MorphismProperty.cancel_right_of_respectsIso, h]
  have hclosed : IsClosedImmersion (W.map (Z.inclusion ≫ e.hom)) := by
    letI := Z.isClosedImmersion
    change IsClosedImmersion (Z.inclusion.hom.hom.left ≫ W.map e.hom)
    infer_instance
  let Z' : ClosedSubgroup C.realization.pinned.pair.G.val := ⟨Z.group, Z.inclusion ≫ e.hom, hclosed⟩
  have hk' : IsSchemeKernel f Z' := by
    refine hk.of_iso' (Iso.refl _) (U.mapIso e.symm) (Iso.refl _) (U.mapIso e'.symm)
      ?_ ?_ ?_ ?_
    · change 𝟙 _ ≫ Z.inclusion.hom.hom = (Z.inclusion.hom.hom ≫ e.hom.hom.hom) ≫ e.inv.hom.hom
      simp only [Category.id_comp, Category.assoc]
      rw [show e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ from (U.mapIso e).hom_inv_id, Category.comp_id]
    · simp
    · change e.inv.hom.hom ≫ q.hom.hom =
        (e.inv.hom.hom ≫ q.hom.hom ≫ e'.hom.hom.hom) ≫ e'.inv.hom.hom
      simp only [Category.assoc]
      rw [show e'.hom.hom.hom ≫ e'.inv.hom.hom = 𝟙 _ from (U.mapIso e').hom_inv_id, Category.comp_id]
    · exact (Category.id_comp _).trans (IsMonHom.one_hom e'.inv.hom.hom).symm
  have hc' : Centralizes (𝟙 _) Z'.inclusion.hom.hom :=
    (innerAut_eq_one_iff _).mp (mapsCentralPointIso e Z.inclusion.hom.hom
      ((innerAut_eq_one_iff _).mpr hc))
  have ht := C.torus_comm
  have ht' := C'.torus_comm
  have hcomm : fT ≫ T'.inclusion = T.inclusion ≫ f := by
    change t.inv ≫ qT ≫ t'.hom ≫ T'.inclusion = T.inclusion ≫ e.inv ≫ q ≫ e'.hom
    rw [← ht', ← Functor.map_comp_assoc, ← c.torusComm, Functor.map_comp, Category.assoc]
    change F.map M.torus ≫ e.hom = t.hom ≫ T.inclusion at ht
    have hT : t.inv ≫ F.map M.torus = T.inclusion ≫ e.inv := by
      apply (cancel_mono e.hom).mp
      rw [Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id, ht, t.inv_hom_id_assoc]
    rw [← Category.assoc t.inv (F.map M.torus), hT, Category.assoc]
  refine ⟨⟨property e e' q hfin, property e e' q hflat, property e e' q hsurj, Z', hk', hc'⟩,
    ⟨hcomm, property t t' qT hflatT, property t t' qT hsurjT⟩, Z', hk', ⟨z ≫ t.hom, ?_⟩, hc'⟩
  change (z ≫ t.hom) ≫ T.inclusion = Z.inclusion ≫ e.hom
  rw [Category.assoc, ← ht, ← Category.assoc, hz]

open private domainCongrBialgEquiv_toBialgHom
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization

private theorem torusCoordinateMap {X Y : Type u} [CommGroup X] [CommGroup Y]
    (g : Y →* X) (S : IntegralAlgebra.{u}) (v : X →* Sˣ) :
    coordinatePoints S (toConv (MonoidAlgebra.lift ZRing S X ((Units.coeHom S).comp v))) ≫
      (spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom ZRing g)).hom.hom =
    coordinatePoints S (toConv (MonoidAlgebra.lift ZRing S Y ((Units.coeHom S).comp (v.comp g)))) := by
  rw [← coordinatePoints_comp]
  apply congrArg (fun f => coordinatePoints S (toConv f))
  apply MonoidAlgebra.algHom_ext
  · intro a
    rw [AlgHom.comp_apply]
    change MonoidAlgebra.lift ZRing S X ((Units.coeHom S).comp v)
      (MonoidAlgebra.mapDomainBialgHom ZRing g (MonoidAlgebra.single a 1)) = _
    rw [MonoidAlgebra.mapDomainBialgHom_single g a 1]
    change MonoidAlgebra.lift ZRing S X ((Units.coeHom S).comp v)
        (MonoidAlgebra.of ZRing X (g a)) =
      MonoidAlgebra.lift ZRing S Y ((Units.coeHom S).comp (v.comp g))
        (MonoidAlgebra.of ZRing Y a)
    rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of]
    rfl
  · ext

private theorem torusCoordinateMapOfEquiv {X Y : Type u} [CommGroup X] [CommGroup Y]
    (g : Y ≃* X) (S : IntegralAlgebra.{u}) (v : X →* Sˣ) :
    coordinatePoints S (toConv (MonoidAlgebra.lift ZRing S X ((Units.coeHom S).comp v))) ≫
      ((hopfSpec (CommRingCat.of ZRing)).mapIso
        (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv ZRing ZRing g)).op).hom.hom.hom =
    coordinatePoints S (toConv (MonoidAlgebra.lift ZRing S Y ((Units.coeHom S).comp
      (v.comp g.toMonoidHom)))) := by
  change _ ≫ (spectrumOfHopfHom (MonoidAlgebra.domCongrBialgEquiv ZRing ZRing g).toBialgHom).hom.hom = _
  rw [domainCongrBialgEquiv_toBialgHom]
  exact torusCoordinateMap g.toMonoidHom S v

private def adjointTorusMap (D : BasedRootDatum.{u}) :
    splitTorus D ⟶ splitTorus (adjointDatum D) :=
  spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom ZRing (characterQuotient D).ker.subtype) ≫
    (adjointTorusIso D).hom

private theorem adjointTorusMap_point {D : BasedRootDatum.{u}} (S : IntegralAlgebra.{u})
    (v : TorusValues D S) :
    torusPoint D S v ≫ (adjointTorusMap D).hom.hom =
      torusPoint (adjointDatum D) S
        (v.comp ((D.datum.rootSpan ℤ).subtype.toAddMonoidHom.toMultiplicative)) := by
  let z := (characterQuotient D).ker.subtype
  let i := spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom ZRing z)
  let j := (adjointTorusIso D).hom.hom.hom
  refine (Category.assoc (torusPoint D S v) i.hom.hom j).symm.trans ?_
  exact (congrArg (· ≫ j) (torusCoordinateMap z S v)).trans
    (torusCoordinateMapOfEquiv (adjointCharacters D) S (v.comp z))

private theorem rootCellPrecompose {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {N P T N' P' T' G : C} [MonObj G]
    (n : N' ⟶ N) (t : T' ⟶ T) (p : P' ⟶ P)
    (x : N ⟶ G) (y : T ⟶ G) (z : P ⟶ G) :
    (n ⊗ₘ (t ⊗ₘ p)) ≫ ((fst _ _ ≫ x) * (snd _ _ ≫ ((fst _ _ ≫ y) * (snd _ _ ≫ z)))) =
      (fst _ _ ≫ n ≫ x) * (snd _ _ ≫ ((fst _ _ ≫ t ≫ y) * (snd _ _ ≫ p ≫ z))) := by
  simp only [MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc]

private theorem transportedTorusSquare {C : Type*} [Category C] {T G A T₀ T₁ Q : C}
    (t : T ⟶ G) (e : A ≅ G) (q : A ⟶ Q)
    (z : T ⟶ T₀) (eT : T₀ ≅ T₁) (i : T₀ ⟶ Q)
    (h : z ≫ i = (t ≫ e.inv) ≫ q) :
    t ≫ (e.inv ≫ q) = (z ≫ eT.hom) ≫ (eT.inv ≫ i) := by
  rw [← Category.assoc t e.inv, ← h, Category.assoc z eT.hom, eT.hom_inv_id_assoc]

private theorem transportedKernelInclusion {C : Type*} [Category C] {Z T A G : C}
    (t : T ⟶ G) (e : A ≅ G) (i : Z ⟶ T) (j : Z ⟶ A)
    (h : j = i ≫ (t ≫ e.inv)) : j ≫ e.hom = i ≫ t := by
  rw [h, Category.assoc i, Category.assoc t, e.inv_hom_id, Category.comp_id]

set_option maxHeartbeats 2000000 in
private theorem markedAdjointCover (D : BasedRootDatum.{u})
    (hfinite : Finite (Multiplicative D.X ⧸ rootCharacters D)) (M : Model D) :
    ∃ (N : Model (adjointDatum D)) (c : MarkedCentralCover M N),
      ∀ i : D.I, c.rootEquiv i = i := by
  classical
  letI := D.freeX
  letI := D.finiteX
  letI : Module.Free ℤ (Additive (Multiplicative D.X)) := D.freeX
  letI : Module.Finite ℤ (Additive (Multiplicative D.X)) := D.finiteX
  letI : Fintype (Multiplicative D.X ⧸ rootCharacters D) := Fintype.ofFinite _
  letI : IsNoetherianRing ZRing := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  let E := adjointDatum D
  let z := characterQuotient D
  have hz : Function.Surjective z := QuotientGroup.mk'_surjective _
  have hα (a : D.I) : z (Multiplicative.ofAdd (D.datum.root a)) = 1 := by
    change Multiplicative.ofAdd (D.datum.root a) ∈ z.ker
    rw [QuotientGroup.ker_mk']
    change D.datum.root a ∈ D.datum.rootSpan ℤ
    exact Submodule.subset_span (Set.mem_range_self a)
  obtain ⟨A, ⟨e⟩⟩ := affineSpectrum M.group M.affine
  let t := markedTorusCoordinates e M.torus
  let x (a : D.I) := markedRootCoordinates e (M.root a)
  let r := integralRankOneCoordinates M e
  let π := (MonoidAlgebra.mapDomainBialgHom ZRing z).comp t
  have ht := markedTorusCoordinates_surjective e M.torus M.torusClosed
  have hπ : Function.Surjective π := (characterRestriction_surjective z hz).comp ht
  have he := markedTorusCoordinates_spec e M.torus
  have hopen (neg pos : List D.I)
      (hn : Specs.OrderedRootProducts.Enumerates neg {i | ¬ D.base.IsPos i})
      (hp : Specs.OrderedRootProducts.Enumerates pos {i | D.base.IsPos i}) :
      IsOpenImmersion (IntegralCentralQuotient.cellMap t x neg pos).left := by
    rw [markedCellCoordinates_spec, Over.comp_left, Over.comp_left]
    letI := M.openCell neg pos hn hp
    letI : IsOpenImmersion (orderedCell M.line M.torus M.root neg pos).left := inferInstanceAs
      (IsOpenImmersion (Specs.IntegralSemisimpleModel.cellMap M.line M.torus M.root neg pos).left)
    let i := (Over.forget _).mapIso (cellDomainIso (splitTorus D) M.line neg pos)
    let g := (Grp.forget IntegralScheme.{u} ⋙ Over.forget _).mapIso e
    change IsOpenImmersion (i.hom ≫ (orderedCell M.line M.torus M.root neg pos).left ≫ g.inv)
    infer_instance
  let g := (Grp.forget IntegralScheme.{u} ⋙ Over.forget _).mapIso e
  have hs : Smooth (HopfSpectrum ZRing A).X.hom := by
    rw [← Over.w e.hom.hom.hom]
    change Smooth (g.hom ≫ M.group.X.hom)
    letI := M.smooth
    infer_instance
  have hred : ReductiveFibres (spectrumOfHopfHom t) := by
    rw [he]
    intro K _ _ _
    obtain ⟨H, f, hc, hH, hm⟩ := model_reductiveFibres M K
    let F := fibreGroup K (R := ZRing)
    let eK := F.mapIso e ≪≫ f
    have h : F.map (M.torus ≫ e.inv) ≫ eK.hom = F.map M.torus ≫ f.hom := by
      change F.map (M.torus ≫ e.inv) ≫ (F.map e.hom ≫ f.hom) = _
      have hc' : F.map e.inv ≫ F.map e.hom = 𝟙 _ := (F.mapIso e).inv_hom_id
      rw [F.map_comp, Category.assoc, reassoc_of% hc']
    refine ⟨H, eK, ?_⟩
    rw [h]
    exact ⟨hc, hH, hm⟩
  obtain ⟨neg, pos, hn, hp⟩ := rootOrderings_exist D
  letI : IsIntegral M.group.X.left := integralModelIntegral M
  letI : IsIntegral (Spec (CommRingCat.of A)) := by
    let i : Spec (CommRingCat.of A) ≅ M.group.X.left := g
    exact IsIntegral.of_isIso i.inv
  letI : _root_.IsReduced A := (affine_isReduced_iff (CommRingCat.of A)).mp inferInstance
  letI : IrreducibleSpace (HopfSpectrum ZRing A).X.left :=
    inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of A)))
  have hcentral := central_of_openRootCell z t x
    (fun a => Multiplicative.ofAdd (D.datum.root a)) hα (integralRootScalarAction M e)
    neg pos (hopen neg pos hn hp)
  have geom : GeometricQuotient.{u} :=
    LinearAlgebraicGroups.Classification.IntegralCentralQuotient.integralCentralQuotient.{u}.2.2
  have hd : (neg ++ pos).Nodup := by
    refine List.nodup_append.mpr ⟨hn.1, hp.1, ?_⟩
    rintro a ha _ hb rfl
    exact (hn.2 a |>.mp ha) (hp.2 a |>.mp hb)
  have hall (i : D.I) : i ∈ neg ++ pos := by
    by_cases hi : D.base.IsPos i
    · exact List.mem_append_right _ ((hp.2 i).mpr hi)
    · exact List.mem_append_left _ ((hn.2 i).mpr hi)
  obtain ⟨hB, j, t₀, hj, hq, hflat, hfp, hRed, _, _, ht₀, _, _, hr⟩ :=
    geom z t x neg pos (fun i => D.datum.reflectionPerm i i)
      (fun i => Multiplicative.ofAdd (D.datum.root i)) (corootOnCharacters D) r
      hz ht hcentral hs hred hd hall (hopen neg pos hn hp)
      (fun a => ⟨markedRootCoordinates_surjective e _ (M.rootClosed a),
        integralRootScalarAction M e a, integralRankOneCompatibility M e a⟩)
  let B := ↥(invariants π)
  letI : HopfAlgebra ZRing B := hB
  letI : Algebra ZRing B := hB.toHopfAlgebraStruct.toBialgebra.toAlgebra
  letI : Flat (HopfSpectrum ZRing B).X.hom := hflat
  letI : LocallyOfFinitePresentation (HopfSpectrum ZRing B).X.hom := hfp
  let Q := HopfSpectrum ZRing B
  let q : HopfSpectrum ZRing A ⟶ Q := spectrumOfHopfHom j
  let q₀ : M.group ⟶ Q := e.inv ≫ q
  let T₀ := HopfSpectrum ZRing (MonoidAlgebra ZRing z.ker)
  let eT : T₀ ≅ splitTorus E := adjointTorusIso D
  let z₀ := MonoidAlgebra.mapDomainBialgHom ZRing z.ker.subtype
  let zT : splitTorus D ⟶ T₀ := spectrumOfHopfHom z₀
  let qT : splitTorus D ⟶ splitTorus E := zT ≫ eT.hom
  let χ : E.X →ₗ[ℤ] D.X := (D.datum.rootSpan ℤ).subtype
  have hqT (S : IntegralAlgebra.{u}) (w : TorusValues D S) :
      torusPoint D S w ≫ qT.hom.hom =
        torusPoint E S (w.comp χ.toAddMonoidHom.toMultiplicative) :=
    adjointTorusMap_point (D := D) S w
  let i₀ : T₀ ⟶ Q := spectrumOfHopfHom t₀
  let t' : splitTorus E ⟶ Q := eT.inv ≫ i₀
  let x₀ (a : D.I) := (x a).comp j.toAlgHom
  let x' (a : D.I) := M.root a ≫ q₀
  have htc : M.torus ≫ q₀ = qT ≫ t' := by
    have hcoords : z₀.comp t₀ = t.comp j := ht₀
    let fromCoordinates (f : B →ₐc[ZRing] MonoidAlgebra ZRing (Multiplicative D.X)) :
        splitTorus D ⟶ Q := spectrumOfHopfHom f
    have hz₀ : fromCoordinates (z₀.comp t₀) = zT ≫ i₀ :=
      spectrumOfHopfHom_comp t₀ z₀
    have hq' : fromCoordinates (t.comp j) = (M.torus ≫ e.inv) ≫ q :=
      (spectrumOfHopfHom_comp j t).trans (congrArg (· ≫ q) he)
    have h : zT ≫ i₀ = (M.torus ≫ e.inv) ≫ q :=
      hz₀.symm.trans ((congrArg fromCoordinates hcoords).trans hq')
    exact transportedTorusSquare (C := IntegralGroup.{u}) M.torus e q zT eT i₀ h
  have hx (a : D.I) : (x' a).hom.hom = spectrumOfAlgHom (x₀ a) := by
    rw [spectrumOfAlgHom_comp, markedRootCoordinates_spec]
    rfl
  obtain ⟨hSmooth, hConn⟩ := smoothConnectedOfGeometricFibres i₀ hRed
  have hts : Function.Surjective t₀ := quotientTorusRestriction_surjective z t ht j t₀
    (fun b hb => ⟨⟨b, hb⟩, hj _⟩) ht₀
  have hRed' := reductiveFibres_precompose eT.symm i₀ hRed
  let torusCoordinates (S : IntegralAlgebra.{u}) (w : TorusValues E S) :=
    MonoidAlgebra.lift ZRing S z.ker ((Units.coeHom S).comp (w.comp (adjointCharacters D).symm.toMonoidHom))
  have heval (S : IntegralAlgebra.{u}) (w : TorusValues E S) :
      torusPoint E S w ≫ eT.inv.hom.hom =
        coordinatePoints S (toConv (torusCoordinates S w)) :=
    torusCoordinateMapOfEquiv (adjointCharacters D).symm S w
  have hcell (negative positive : List E.I)
      (hn : Specs.OrderedRootProducts.Enumerates negative {i | ¬ E.base.IsPos i})
      (hp : Specs.OrderedRootProducts.Enumerates positive {i | E.base.IsPos i}) :
      IsOpenImmersion (Specs.IntegralSemisimpleModel.cellMap M.line t' x' negative positive).left := by
    have hn' : Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i} :=
      ⟨hn.1, fun a => (hn.2 a).trans (not_congr (adjointPositive D a).symm)⟩
    have hp' : Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i} :=
      ⟨hp.1, fun a => (hp.2 a).trans (adjointPositive D a).symm⟩
    letI := (quotientCell z hz t j t₀ ht₀ x negative positive
      (hopen negative positive hn' hp') hcentral hq).1
    let i := MonoidalCategory.tensorIso (lineProductIso M.line negative).symm
      (MonoidalCategory.tensorIso ((Grp.forget IntegralScheme.{u}).mapIso eT).symm
        (lineProductIso M.line positive).symm)
    have hroot (a : E.I) : spectrumOfAlgHom (x₀ a) = (x' a).hom.hom := (hx a).symm
    have hprod (l : List E.I) :
        (lineProductIso M.line l).inv ≫ IntegralCentralQuotient.rootProduct x₀ l =
          Specs.IntegralSemisimpleModel.rootProduct M.line x' l := by
      induction l with
      | nil => simp [lineProductIso, IntegralCentralQuotient.rootProduct, IntegralSemisimpleModel.rootProduct]
      | cons a l ih =>
        simp only [lineProductIso, IntegralCentralQuotient.rootProduct,
          IntegralSemisimpleModel.rootProduct, hroot a, MonoidalCategory.tensorIso_inv,
          Iso.refl_inv, MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc,
          Category.id_comp, ih]
        rfl
    have h : i.hom ≫ IntegralCentralQuotient.cellMap t₀ x₀ negative positive =
        Specs.IntegralSemisimpleModel.cellMap M.line t' x' negative positive := by
      refine (rootCellPrecompose (lineProductIso M.line negative).inv
        eT.inv.hom.hom (lineProductIso M.line positive).inv
        (IntegralCentralQuotient.rootProduct x₀ negative) i₀.hom.hom
        (IntegralCentralQuotient.rootProduct x₀ positive)).trans ?_
      simp only [← Category.assoc, hprod]
      rfl
    rw [← h, Over.comp_left]
    let i' := (Over.forget _).mapIso i
    change IsOpenImmersion (i'.hom ≫ (IntegralCentralQuotient.cellMap t₀ x₀ negative positive).left)
    infer_instance
  let N₀ : IntegralMarking E :=
    { group := Q
      affine := inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))
      locallyOfFinitePresentation := hfp
      quasiCompact := by
        letI : IsAffine (Spec (CommRingCat.of ZRing)) := inferInstance
        letI : IsAffine Q.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))
        infer_instance
      smooth := hSmooth
      connected := hConn
      line := M.line
      torus := t'
      torusClosed := by
        let i := (Grp.forget IntegralScheme.{u} ⋙ Over.forget _).mapIso eT
        letI : IsClosedImmersion i₀.hom.hom.left := IsClosedImmersion.spec_of_surjective _ hts
        change IsClosedImmersion (i.inv ≫ i₀.hom.hom.left)
        infer_instance
      root := x'
      rootClosed a := by
        change IsClosedImmersion ((x' a).hom.hom).left
        rw [hx]
        exact IsClosedImmersion.spec_of_surjective _ (hr a).1
      conjugation S w a v := by
        obtain ⟨_, ha, hscalar, _, _, _⟩ := hr a
        have hA : (⟨_, ha⟩ : z.ker) = adjointCharacters D (Multiplicative.ofAdd (E.datum.root a)) :=
          Subtype.ext rfl
        rw [hA] at hscalar
        have hval : torusCoordinates S w (MonoidAlgebra.of ZRing _
            (adjointCharacters D (Multiplicative.ofAdd (E.datum.root a)))) =
              (w (Multiplicative.ofAdd (E.datum.root a)) : S) := by
          dsimp only [torusCoordinates]
          rw [MonoidAlgebra.lift_of]
          exact congrArg (fun b => (w b : S)) ((adjointCharacters D).symm_apply_apply _)
        have h := congrArg (coordinatePoints S) (hscalar S v (torusCoordinates S w))
        simp only [map_mul, coordinatePoints_antipode, coordinatePoints_comp,
          coordinatePoints_polynomial, hval] at h
        rw [← heval] at h
        simpa only [t', Grp.comp_hom_hom, ← Category.assoc, hx] using h
      openCell := hcell
      rankOne a := M.rankOne a ≫ Functor.whiskerLeft integralSpec.rightOp (yonedaGrp.map q₀)
      rankOneUpper a S v := congrArg (· ≫ q₀.hom.hom) (M.rankOneUpper a S v)
      rankOneLower a S v := congrArg (· ≫ q₀.hom.hom) (M.rankOneLower a S v)
      rankOneDiagonal a S v := by
        change (M.rankOne a).app S _ ≫ q₀.hom.hom =
          torusPoint E S (cocharacter E (E.datum.coroot a) S v) ≫ t'.hom.hom
        rw [M.rankOneDiagonal, Category.assoc, ← Grp.comp_hom_hom, htc, Grp.comp_hom_hom,
          ← Category.assoc, hqT S] <;> rfl }
  have hn' : Specs.OrderedRootProducts.Enumerates neg {i | ¬ E.base.IsPos i} :=
    ⟨hn.1, fun a => (hn.2 a).trans (not_congr (adjointPositive D a))⟩
  have hp' : Specs.OrderedRootProducts.Enumerates pos {i | E.base.IsPos i} :=
    ⟨hp.1, fun a => (hp.2 a).trans (adjointPositive D a)⟩
  let N := modelOfMarking N₀ hRed' neg pos hn' hp'
  let push : D.Y →ₗ[ℤ] E.Y := χ.dualMap.comp D.datum.toLinearMap.flip
  let Z := HopfSpectrum ZRing (MonoidAlgebra ZRing (Multiplicative D.X ⧸ rootCharacters D))
  let zmap := MonoidAlgebra.mapDomainBialgHom ZRing z
  let i : Z ⟶ splitTorus D := spectrumOfHopfHom zmap
  let jz : Z ⟶ HopfSpectrum ZRing A := spectrumOfHopfHom π
  have hzComp : jz = i ≫ (M.torus ≫ e.inv) :=
    (spectrumOfHopfHom_comp t zmap).trans (congrArg (i ≫ ·) he)
  have hz' : jz ≫ e.hom = i ≫ M.torus :=
    transportedKernelInclusion (C := IntegralGroup.{u}) M.torus e i jz hzComp
  have hT := torusProjection_torsor (R := ZRing) z hz
  have hfibre : ∀ (k : Type u) [Field k], IntegralFibreQuotient M.torus q₀ qT k := by
    intro k _
    obtain ⟨hzClosed, hk, hc⟩ := integralFibreTorsor j π hq hcentral hπ k
    exact integralQuotientOnFibre M.torus e eT q zT jz i hz' hq.1 hq.2.1
      hq.2.2.1 hT.2.1 hT.2.2.1 k hzClosed hk hc
  let C : MarkedQuotientMap M N := ⟨q₀, qT, htc, hfibre⟩
  have hindex : Finite (Multiplicative D.X ⧸ χ.toAddMonoidHom.toMultiplicative.range) := by
    have heq : χ.toAddMonoidHom.toMultiplicative.range = rootCharacters D := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.toAdd.property
      · intro hx
        exact ⟨Multiplicative.ofAdd ⟨x.toAdd, hx⟩, rfl⟩
    rwa [heq]
  let c : MarkedCentralCover M N :=
    { map := q₀
      torusMap := qT
      rootEquiv := Equiv.refl _
      pullCharacter := χ
      pushCocharacter := push
      characterInjective := Subtype.val_injective
      characterIndex := hindex
      roots := fun _ => rfl
      coroots := fun _ => rfl
      reflections := fun _ _ => rfl
      pairing := fun _ _ => rfl
      marking := by
        refine ⟨adjointPositive D, fun S a v => ?_, fun S w => ?_⟩
        · exact Category.assoc (M.line.point S v) (M.root a).hom.hom q₀.hom.hom
        · change (torusPoint D S w ≫ M.torus.hom.hom) ≫ q₀.hom.hom =
            torusPoint E S (w.comp χ.toAddMonoidHom.toMultiplicative) ≫ t'.hom.hom
          rw [Category.assoc, ← Grp.comp_hom_hom, htc, Grp.comp_hom_hom,
            ← Category.assoc, hqT S]
      torusComm := htc
      fibre := markedQuotientFibre C }
  exact ⟨N, c, fun _ => rfl⟩

end IntegralAdjoint

section Assembly

open Specs.Pinning (AttachedDatum BasedRootDatum BasedIso PinnedGroup)
open Specs.RootGroups (AdditiveLine)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.IntegralSemisimpleModel (Model)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalAffineBruhat (RamifiedReference ExceptionalNumbering)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open Specs.ExceptionalLocalRootCoordinates (ramificationIndex)
open Specs.QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction)
open Specs.PinnedPairDescent (DescendedPair)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (Cocycle restriction)
open _root_.LinearAlgebraicGroups.Descent.PinnedPairDescent (pinnedPairDescent)
open _root_.LinearAlgebraicGroups.Classification.IntegralRealization (integralRealization)
open private latticeCriterion_pair rootFullRank_iff finiteMultiplicativeQuotient_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

attribute [local instance] Specs.QuasiSplitInnerForms.basedAutTopology
  Specs.QuasiSplitInnerForms.basedAutDiscrete Specs.QuasiSplitInnerForms.fieldGalTopology

private theorem ramifiedMarkedDescent
    {F L : Type u} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M F) (ω : Gal(L/F) →* Aut D) :
    ∃ R : RamifiedReference F L M, R.fibre = C ∧
      ∀ σ, R.diagram σ = (ω σ).asIso.hom := by
  let P := C.realization
  let d := (Groupoid.isoEquivHom D P.attached.toBased).symm P.datumIso
  obtain ⟨l, Q, ⟨E⟩⟩ := splitSequenceForAttachedDatum P.attached
  let ω' := (Aut.autMulEquivOfIso d).toMonoidHom.comp ω
  obtain ⟨W⟩ := pinnedPairDescent (K := L) E ω'
  let R : RamifiedReference F L M := ⟨C, l, Q, E, ω', W⟩
  refine ⟨R, rfl, fun σ => ?_⟩
  change ((Aut.autMulEquivOfIso d.symm) ((Aut.autMulEquivOfIso d) (ω σ))).asIso.hom = _
  rw [show Aut.autMulEquivOfIso d.symm = (Aut.autMulEquivOfIso d).symm from rfl,
    MulEquiv.symm_apply_apply]

private theorem assembleMarkedReference
    (cover : ∀ D : BasedRootDatum.{u},
      Finite (Multiplicative D.X ⧸ rootCharacters D) →
      ∀ M : Model D, ∃ (M' : Model (adjointDatum D)) (c : MarkedCentralCover M M'),
        ∀ i : D.I, c.rootEquiv i = i) :
    MarkedReference.{u} := by
  intro F S _ _ _ _ _ _ _ A P D l Q E hSS hSC hE6 L _ _ _ _ h₂ _ ω hω outer houter V
  obtain ⟨b, hb⟩ := hE6
  letI := D.comm
  let Dsc := D.toBased
  let Dad := adjointDatum Dsc
  have hsc : Dsc.datum.corootSpan ℤ = ⊤ :=
    (latticeCriterion_pair integralRealization P.pair D hSS).mp hSC
  have had := adjointRootSpan Dsc
  have hfin : Finite (Multiplicative Dsc.X ⧸ rootCharacters Dsc) := by
    letI := Dsc.freeX
    letI := Dsc.finiteX
    apply (finiteMultiplicativeQuotient_iff (rootCharacters Dsc)).mpr
    change Finite (Dsc.X ⧸ Dsc.datum.rootSpan ℤ)
    exact (Submodule.finiteQuotient_iff _).mpr ((rootFullRank_iff P.pair D).mp hSS)
  obtain ⟨M⟩ := integralRealization Dsc
  obtain ⟨M', c, hc⟩ := cover Dsc hfin M
  obtain ⟨C⟩ := markedFibreExists M F
  obtain ⟨C'⟩ := markedFibreExists M' F
  let d := (Groupoid.isoEquivHom Dsc C.realization.attached.toBased).symm C.realization.datumIso
  obtain ⟨pin, Qsc, ⟨Esc⟩⟩ := splitSequenceForAttachedDatum C.realization.attached
  let ωsc := (Aut.autMulEquivOfIso d).toMonoidHom.comp ω
  obtain ⟨W⟩ := pinnedPairDescent (K := L) Esc ωsc
  let R : RamifiedReference F L M := ⟨C, pin, Qsc, Esc, ωsc, W⟩
  have hdiagram (σ : Gal(L/F)) : R.diagram σ = (ω σ).asIso.hom := by
    change ((Aut.autMulEquivOfIso d.symm) ((Aut.autMulEquivOfIso d) (ω σ))).asIso.hom = _
    rw [show Aut.autMulEquivOfIso d.symm = (Aut.autMulEquivOfIso d).symm from rfl,
      MulEquiv.symm_apply_apply]
  obtain ⟨R', _, hdiagram'⟩ :=
    ramifiedMarkedDescent C' ((adjointDatumAction Dsc).comp ω)
  obtain ⟨j⟩ := compareMarkedRepresentative L E Esc d ω outer houter V W
  have hnum := exceptionalNumberingOfCorootSpan hsc b hb
  have hnum' := adjointNumbering b hb
  refine ⟨Dsc, Dad, M, M', c, b, b, R, R', j, hnum, hnum', hsc, had, ?_,
    naturalPointComparison j, ?_⟩
  · intro σ hσ
    have hne : (ω σ).asIso.hom ≠ 𝟙 Dsc := by
      intro h
      apply quadraticDiagram_ne_one h₂ ω hω σ hσ
      apply Aut.ext
      exact Iso.ext h
    have hsimp := basedE6Partner b hnum (Or.inr hsc) _ hne
    rw [hdiagram σ, hdiagram' σ]
    change (∀ i, (ω σ).asIso.hom.val.indexEquiv (b i) = b (e6Partner i)) ∧
      (∀ i, (adjointBasedIso (ω σ).asIso.hom).val.indexEquiv (b i) = b (e6Partner i)) ∧
      (∀ i, c.rootEquiv ((ω σ).asIso.hom.val.indexEquiv i) =
        (adjointBasedIso (ω σ).asIso.hom).val.indexEquiv (c.rootEquiv i))
    refine ⟨hsimp, hsimp, fun i => ?_⟩
    rw [hc, hc]
    rfl
  · intro φ hφ Q'
    exact compareMarkedAdjointCoefficients R R' had j φ hφ Q'

/-- The common ramified E₆ reference and its adjoint quotient comparison. -/
theorem markedReference_conditional.{a, b, c}
    (_ : Specs.ExceptionalAffineBruhat.CoxeterDoubleCosets.{a, b, c})
    (_ : Specs.ExceptionalAffineBruhat.E6CoweightClass)
    (_ : Specs.ExceptionalAffineBruhat.E6ProjectedLattices)
    (_ : Specs.ExceptionalAffineBruhat.LeftCosetIndex.{a})
    (_ : Specs.ExceptionalAffineBruhat.RamifiedAffineBruhatComparison.{a})
    (_ : Specs.ExceptionalAffineBruhat.RankOneDoubleCosetProduct.{a})
    (_ : Specs.ExceptionalAffineBruhat.RankOneWallConjugation.{a})
    (_ : Specs.ExceptionalAffineBruhat.RankOneWallMultiplication.{a})
    (_ : Specs.ExceptionalAffineBruhat.ResidueLayerCounts.{a})
    (_ : Specs.ExceptionalAffineBruhat.ResiduePowerCounts.{a})
    (_ : Specs.ExceptionalAffineBruhat.SplitAffineBruhatComparison.{a}) :
    MarkedReference.{a} :=
  assembleMarkedReference markedAdjointCover

end Assembly

end
end LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalMarkedAdjoint

universe v8_closure_1c0aa6f6612d0d3e_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedExceptionalMarkedAdjoint».«markedReference» : _root_.«LinearAlgebraicGroups».«Specs».«RamifiedExceptionalMarkedAdjoint».«MarkedReference».{v8_closure_1c0aa6f6612d0d3e_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedExceptionalMarkedAdjoint».«markedReference_conditional».{v8_closure_1c0aa6f6612d0d3e_u0, 0, 0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_1c0aa6f6612d0d3e_u0, 0, 0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_1c0aa6f6612d0d3e_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_1c0aa6f6612d0d3e_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_1c0aa6f6612d0d3e_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_1c0aa6f6612d0d3e_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_1c0aa6f6612d0d3e_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_1c0aa6f6612d0d3e_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_1c0aa6f6612d0d3e_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_1c0aa6f6612d0d3e_u0})
