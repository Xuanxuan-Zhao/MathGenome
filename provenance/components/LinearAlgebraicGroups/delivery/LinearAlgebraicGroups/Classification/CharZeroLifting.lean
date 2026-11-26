import Specs.LinearAlgebraicGroups.Classification.CharZeroLifting
import LinearAlgebraicGroups.RootData.SchemeCentre
import LinearAlgebraicGroups.Classification.RationalRealization
import LinearAlgebraicGroups.Affine.SchemeImageQuotient
import LinearAlgebraicGroups.Affine.AdjointRepresentation
import LinearAlgebraicGroups.Flag.SmoothOrbit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic.Group
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups.CharZeroLifting

open _root_.LinearAlgebraicGroups.Specs
open Specs.CharZeroLifting
open Specs.CharacterDescent (Character Cocharacter compositionPairing)
open Specs.CharacterPairing (adjointWeightVectors pairing)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.FiniteWordClosure (evaluate wordDomain)
open Specs.RationalRealization (DominantGenericLift WordGeneratedGroup generator)
open Specs.AdjointRepresentation (reduction constants GroupPoints RelativeTangent)
open _root_.LinearAlgebraicGroups.RootData (integralCartan)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap diagonalClosedInclusion
  diagonalRestriction)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.AbstractPairing (Root)
open Specs.Pinning (SplitBorelPair)
open Specs.OrderedRootProducts (RootSubgroupFamily rootCellMap rootProduct)
open Specs.Pinning (PinnedGroup AttachedDatum CoordinateVectors IsSimple RootCoordinate SimpleRoot)
open Specs.RootGroups (AdditiveLine rootPoint)

open private integerHomEquiv specIso
  from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private split_character_presentation centralizes_precomp from LinearAlgebraicGroups.RootData.SchemeCentre
open private irreducible_of_geometricallyConnected from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private mono_over centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private isIso_of_schemeIso from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private tangent_coordinates from LinearAlgebraicGroups.Affine.AdjointRepresentation
open private existsOverFactorEtale from LinearAlgebraicGroups.Affine.Components
open private isPullback_tensor_structure from LinearAlgebraicGroups.Flag.SmoothOrbit
open private schemeKernel_exists isMonHom_of_comp_closed
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

variable {k : Type u} [Field k]

private abbrev underlying : GroupScheme k ⥤ SchemeOver k := Grp.forget _

private abbrev scheme : GroupScheme k ⥤ Scheme :=
  underlying ⋙ Over.forget (Spec (CommRingCat.of k))

private theorem exponent_comm {M N : Type u} [CommGroup M] [CommGroup N]
    (a : M →* N) (m : M) : a.comp (integerHomEquiv M m) = integerHomEquiv N (a m) := by
  ext z
  exact map_zpow a m z.down.toAdd

private theorem torusMapOfPresentations {S T : GroupScheme k}
    [Group.FG (Character S)]
    (eS : specGroup (groupAlgebra k (Character S)) ≅ S)
    (eT : specGroup (groupAlgebra k (Character T)) ≅ T)
    (heS : ∀ χ : Character S, eS.hom ≫ χ =
      specGroupMap (groupAlgebraMap k (integerHomEquiv (Character S) χ)))
    (heT : ∀ χ : Character T, eT.hom ≫ χ =
      specGroupMap (groupAlgebraMap k (integerHomEquiv (Character T) χ)))
    (a : Character T →* Character S) (ha : Function.Injective a)
    (hfin : Finite (Character S ⧸ a.range)) :
    ∃ t : S ⟶ T, (∀ χ : Character T, t ≫ χ = a χ) ∧
      Surjective t.hom.hom.left ∧
      (∃ N : ClosedSubgroup S, IsSchemeKernel t N ∧ IsFinite N.group.X.hom) ∧
      (Function.Bijective a → IsIso t) := by
  let e := MulEquiv.ofBijective a.rangeRestrict
    ⟨fun _ _ h => ha (congrArg Subtype.val h), a.rangeRestrict_surjective⟩
  let j : specGroup (groupAlgebra k a.range) ≅ specGroup (groupAlgebra k (Character T)) :=
    specIso (A := groupAlgebra k (Character T)) (B := groupAlgebra k a.range)
      (MonoidAlgebra.domCongrBialgEquiv k k e)
  let r := diagonalRestriction k a.range
  let g := specGroupMap (groupAlgebraMap k a)
  have hg : r ≫ j.hom = g := by
    change specGroupMap (groupAlgebraMap k a.range.subtype) ≫
      specGroupMap (groupAlgebraMap k e.toMonoidHom) = _
    rw [← specGroupMap_comp]
    congr 1
    apply CommHopfAlgCat.hom_ext
    change (MonoidAlgebra.mapDomainBialgHom k a.range.subtype).comp
      (MonoidAlgebra.mapDomainBialgHom k e.toMonoidHom) = _
    rw [← MonoidAlgebra.mapDomainBialgHom_comp]
    rfl
  obtain ⟨hi, _, hrs, _, hR, _, _⟩ :=
    _root_.LinearAlgebraicGroups.DiagonalizableGroups.diagonalRestrictionKernelAndQuotient
      k (Character S) a.range
  let c := j ≪≫ eT
  let t := eS.inv ≫ g ≫ eT.hom
  have ht' : eS.hom ≫ t = g ≫ eT.hom := by simp [t]
  have htr : eS.hom ≫ t = r ≫ c.hom := by
    rw [ht', ← hg]
    simp [c, Category.assoc]
  have ht : Surjective t.hom.hom.left := by
    have hs : IsIso (scheme.map eS.inv) := scheme.map_isIso eS.inv
    have ht : IsIso (scheme.map c.hom) := scheme.map_isIso c.hom
    have hr : Surjective (scheme.map r) := hrs
    have he : t = eS.inv ≫ r ≫ c.hom := by
      rw [← htr, Iso.inv_hom_id_assoc]
    change Surjective (scheme.map t)
    rw [he, Functor.map_comp, Functor.map_comp]
    infer_instance
  let i := diagonalClosedInclusion k a.range ≫ eS.hom
  have hi' : IsClosedImmersion i.hom.hom.left := by
    have : IsIso (scheme.map eS.hom) := scheme.map_isIso eS.hom
    have : IsClosedImmersion (scheme.map (diagonalClosedInclusion k a.range)) := hi
    change IsClosedImmersion (scheme.map (diagonalClosedInclusion k a.range ≫ eS.hom))
    rw [Functor.map_comp]
    infer_instance
  let N : ClosedSubgroup S := ⟨specGroup (groupAlgebra k (Character S ⧸ a.range)), i, hi'⟩
  refine ⟨t, fun χ => ?_, ht, ⟨N, ?_, ?_⟩, fun hb => ?_⟩
  · apply (cancel_epi eS.hom).mp
    rw [← Category.assoc, ht', Category.assoc, heT, heS, ← specGroupMap_comp]
    congr 1
    apply CommHopfAlgCat.hom_ext
    change (MonoidAlgebra.mapDomainBialgHom k a).comp
        (MonoidAlgebra.mapDomainBialgHom k (integerHomEquiv _ χ)) = _
    rw [← MonoidAlgebra.mapDomainBialgHom_comp, exponent_comm a χ]
    rfl
  · change IsPullback i.hom.hom (toUnit _) t.hom.hom η[T.X]
    apply hR.of_iso (Iso.refl _) (underlying.mapIso eS) (Iso.refl _) (underlying.mapIso c)
    · simp [i]
    · exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
    · exact congrArg (fun f : _ ⟶ T => f.hom.hom) htr.symm
    · change η[(specGroup (groupAlgebra k a.range)).X] ≫ c.hom.hom.hom = (𝟙 _) ≫ η[T.X]
      rw [Category.id_comp]
      exact IsMonHom.one_hom (f := c.hom.hom.hom)
  · have : Finite (Character S ⧸ a.range) := hfin
    change IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap k (MonoidAlgebra k (Character S ⧸ a.range)))))
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr
      (Module.Finite.of_basis (MonoidAlgebra.basis (Character S ⧸ a.range) k)))
  · let e' := MulEquiv.ofBijective a hb
    have : IsIso g := inferInstanceAs
      (IsIso (specIso (A := groupAlgebra k (Character T)) (B := groupAlgebra k (Character S))
        (MonoidAlgebra.domCongrBialgEquiv k k e')).hom)
    dsimp only [t]
    infer_instance

/-- The lift on split tori has the prescribed character map and finite
scheme kernel. The construction works over any field. -/
theorem torusMap {S T : GroupScheme k} (hS : IsSplitTorus S) (hT : IsSplitTorus T)
    (a : Character T →* Character S) (ha : Function.Injective a)
    (hfin : Finite (Character S ⧸ a.range)) :
    ∃ t : S ⟶ T, (∀ χ : Character T, t ≫ χ = a χ) ∧
      Surjective t.hom.hom.left ∧
      (∃ N : ClosedSubgroup S, IsSchemeKernel t N ∧ IsFinite N.group.X.hom) ∧
      (Function.Bijective a → IsIso t) := by
  obtain ⟨hfg, eS, heS⟩ := split_character_presentation hS
  obtain ⟨_, eT, heT⟩ := split_character_presentation hT
  exact torusMapOfPresentations eS eT heS heT a ha hfin

/-- Pullback on characters determines the direct image of the coroots by
perfectness of the torus pairing. -/
theorem map_coroot {P Q : Pinning.SplitBorelPair k}
    {D : AttachedDatum P} {E : AttachedDatum Q} (h : LatticeMap D E)
    (t : P.T.group ⟶ Q.T.group) (ht : ∀ χ : Character Q.T.group, t ≫ χ = h.characters χ)
    (α : Root P.T) : attachedCoroot D α ≫ t = attachedCoroot E (h.roots α) := by
  let _ := E.comm
  suffices he : Additive.ofMul (attachedCoroot D α ≫ t) =
      Additive.ofMul (attachedCoroot E (h.roots α)) from congrArg Additive.toMul he
  apply E.datum.rootDatum.flip.toPerfPair.injective
  ext x
  let χ : Character Q.T.group := Additive.toMul x
  change E.datum.rootDatum.toLinearMap (Additive.ofMul χ) (Additive.ofMul (attachedCoroot D α ≫ t)) =
    E.datum.rootDatum.toLinearMap (Additive.ofMul χ) (Additive.ofMul (attachedCoroot E (h.roots α)))
  rw [E.datum.pairing_eq, E.datum.pairing_eq]
  calc
    _ = pairing P.T.group (t ≫ χ) (attachedCoroot D α) := by
      unfold pairing compositionPairing
      rw [Category.assoc]
    _ = _ := by rw [ht χ]; exact h.coroot_eq α χ

/-- The two integral pairings on roots and coroots agree under the given
bijection. In particular, the Cartan matrices agree on corresponding simple roots. -/
theorem pairing_eq {P Q : Pinning.SplitBorelPair k}
    {D : AttachedDatum P} {E : AttachedDatum Q} (h : LatticeMap D E)
    (α β : Root P.T) :
    pairing P.T.group β.val (attachedCoroot D α) =
      pairing Q.T.group (h.roots β).val (attachedCoroot E (h.roots α)) := by
  rw [← h.root_eq β]
  exact h.coroot_eq α (h.roots β).val

private theorem isPos_iff_evaluation {I X Y : Type u} [Finite I] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) (b : P.Base) (f : X →ₗ[ℤ] ℤ)
    (hf : ∀ i ∈ b.support, 0 < f (P.root i)) (i : I) :
    b.IsPos i ↔ 0 < f (P.root i) := by
  have hpos {j : I} (hj : b.IsPos j) : 0 < f (P.root j) := by
    refine RootPairing.Base.IsPos.induction_on_add hj hf ?_
    intro l m n h hl hm
    rw [h, map_add]
    exact add_pos hl (hf m hm)
  refine ⟨hpos, fun hi => ?_⟩
  by_contra h
  have hneg := hpos ((RootPairing.Base.IsPos.neg_iff_not b i).2 h)
  change 0 < f (P.root (P.reflectionPerm i i)) at hneg
  rw [P.root_reflectionPerm, P.reflection_apply_self, map_neg] at hneg
  exact (not_lt_of_ge (le_of_lt hi)) (neg_pos.mp hneg)

private theorem pairing_comp {S T : GroupScheme k} (t : S ⟶ T)
    (χ : Character T) (c : Cocharacter S) :
    pairing T χ (c ≫ t) = pairing S (t ≫ χ) c := by
  unfold pairing compositionPairing
  rw [Category.assoc]

private theorem isPos_iff_positiveRoots {P : SplitBorelPair k}
    (D : AttachedDatum P) (c : Cocharacter P.T.group)
    (hc : letI := D.comm; ∀ a ∈ D.base.support, a ∈ positiveRoots P.T c)
    (a : Root P.T) :
    letI := D.comm
    D.base.IsPos a ↔ a ∈ positiveRoots P.T c := by
  let := D.comm
  let := D.datum.finiteRoots
  let f := D.datum.rootDatum.toLinearMap.flip (Additive.ofMul c)
  have hf (i : Root P.T) :
      f (D.datum.rootDatum.root i) = pairing P.T.group i.val c := by
    dsimp only [f, LinearMap.flip_apply]
    rw [D.datum.root_eq, D.datum.pairing_eq]
  exact (isPos_iff_evaluation D.datum.rootDatum D.base f
    (fun i hi => (hf i).symm ▸ hc i hi) a).trans (by
      change 0 < f (D.datum.rootDatum.root a) ↔ 0 < pairing P.T.group a.val c
      rw [hf])

/-- The based root bijection carries the given positive system to the other
one, and every chamber cocharacter of the first Borel pushes to the second. -/
private theorem map_borel_chamber {P Q : SplitBorelPair k}
    {D : AttachedDatum P} {E : AttachedDatum Q} (h : LatticeMap D E)
    (t : P.T.group ⟶ Q.T.group) (ht : ∀ χ : Character Q.T.group, t ≫ χ = h.characters χ)
    (c : Cocharacter P.T.group) (hc : IsRegular P.T c)
    (hP : subgroupRoots P.T P.B = positiveRoots P.T c) :
    IsRegular Q.T (c ≫ t) ∧ subgroupRoots Q.T Q.B = positiveRoots Q.T (c ≫ t) ∧
      ∀ α : Root P.T, α ∈ subgroupRoots P.T P.B ↔ h.roots α ∈ subgroupRoots Q.T Q.B := by
  have hp (α : Root P.T) :
      pairing Q.T.group (h.roots α).val (c ≫ t) = pairing P.T.group α.val c := by
    rw [pairing_comp, ht, h.root_eq]
  have hreg (β : Root Q.T) : pairing Q.T.group β.val (c ≫ t) ≠ 0 := by
    obtain ⟨α, rfl⟩ := h.roots.surjective β
    rw [hp]
    exact hc α
  have hB : Specs.BorelsAndChambers.BorelsThroughT.{u} :=
    LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT
  obtain ⟨d, _, _, _, hd⟩ := (hB Q.G Q.reductive Q.T Q.split Q.maximal).1
    Q.B Q.borel Q.containsTorus
  let := E.comm
  have hEd (β : Root Q.T) (hβ : β ∈ E.base.support) : β ∈ positiveRoots Q.T d := by
    rw [← hd]
    exact ((E.simple_iff β).mp hβ).1
  have hEc (β : Root Q.T) (hβ : β ∈ E.base.support) : β ∈ positiveRoots Q.T (c ≫ t) := by
    obtain ⟨α, rfl⟩ := h.roots.surjective β
    have ha := (h.simple_iff α).mp ((E.simple_iff _).mp hβ)
    have hα := ha.1
    rw [hP] at hα
    change 0 < pairing Q.T.group (h.roots α).val (c ≫ t)
    rwa [hp]
  have he : subgroupRoots Q.T Q.B = positiveRoots Q.T (c ≫ t) := by
    rw [hd]
    ext β
    exact (isPos_iff_positiveRoots E d hEd β).symm.trans
      (isPos_iff_positiveRoots E (c ≫ t) hEc β)
  refine ⟨hreg, he, fun α => ?_⟩
  rw [hP, he]
  change 0 < pairing P.T.group α.val c ↔ 0 < pairing Q.T.group (h.roots α).val (c ≫ t)
  rw [hp]

/-- The simple indices of the two actual attached data give the same Cartan
matrix when both are written in the order determined by the root bijection. -/
private theorem integralCartan_reindex {P Q : SplitBorelPair k}
    {D : AttachedDatum P} {E : AttachedDatum Q} (h : LatticeMap D E) :
    letI := D.comm
    letI := E.comm
    ∃ e : D.base.support ≃ E.base.support, (∀ i, (e i).val = h.roots i.val) ∧
      ∀ i j, integralCartan E.datum.rootDatum E.base (e i) (e j) =
        integralCartan D.datum.rootDatum D.base i j := by
  let := D.comm
  let := E.comm
  let e : D.base.support ≃ E.base.support :=
    h.roots.subtypeEquiv fun i =>
      (D.simple_iff i).trans ((h.simple_iff i).symm.trans (E.simple_iff (h.roots i)).symm)
  refine ⟨e, fun _ => rfl, fun i j => ?_⟩
  change E.datum.rootDatum.toLinearMap (E.datum.rootDatum.root (h.roots j.val))
      (E.datum.rootDatum.coroot (h.roots i.val)) =
    D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root j.val) (D.datum.rootDatum.coroot i.val)
  rw [D.datum.root_eq, E.datum.root_eq]
  change E.datum.rootDatum.toLinearMap (Additive.ofMul (h.roots j.val).val)
      (Additive.ofMul (attachedCoroot E (h.roots i.val))) =
    D.datum.rootDatum.toLinearMap (Additive.ofMul j.val.val) (Additive.ofMul (attachedCoroot D i.val))
  rw [D.datum.pairing_eq, E.datum.pairing_eq]
  exact (pairing_eq h i.val j.val).symm

/-- A comparison of scheme product parametrizations gives a surjective
homomorphism on the closed subgroups whenever the comparison is surjective. -/
private theorem surjective_subgroup_map_of_parametrizations
    {G H : GroupScheme k} (f : G ⟶ H) (B : ClosedSubgroup G) (C : ClosedSubgroup H)
    {X Y : SchemeOver k} (e : X ≅ B.group.X) (e' : Y ≅ C.group.X)
    (a : X ⟶ Y) (ha : Surjective a.left)
    (h : e.hom ≫ B.inclusion.hom.hom ≫ f.hom.hom =
      a ≫ e'.hom ≫ C.inclusion.hom.hom) :
    ∃ b : B.group ⟶ C.group, B.inclusion ≫ f = b ≫ C.inclusion ∧
      Surjective b.hom.hom.left := by
  let m := e.inv ≫ a ≫ e'.hom
  have hm : m ≫ C.inclusion.hom.hom = (B.inclusion ≫ f).hom.hom := by
    change m ≫ C.inclusion.hom.hom = B.inclusion.hom.hom ≫ f.hom.hom
    rw [Category.assoc, Category.assoc, ← h, Iso.inv_hom_id_assoc]
  have := C.isClosedImmersion
  have := isMonHom_of_comp_closed m (B.inclusion ≫ f) C.inclusion hm
  let b := Grp.homMk m
  refine ⟨b, Grp.hom_ext _ _ hm.symm, ?_⟩
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  have : IsIso e'.hom.left := (Over.forget _).map_isIso e'.hom
  change Surjective (e.inv.left ≫ a.left ≫ e'.hom.left)
  infer_instance

/-- The kernel of the specified torus map is already central in the
ambient source group. Every source root is the pullback of a target root. -/
theorem torusKernel_central {P Q : Pinning.SplitBorelPair k}
    {D : AttachedDatum P} {E : AttachedDatum Q} (h : LatticeMap D E)
    (t : P.T.group ⟶ Q.T.group) (ht : ∀ χ : Character Q.T.group, t ≫ χ = h.characters χ)
    (N : ClosedSubgroup P.T.group) (hN : IsSchemeKernel t N) :
    Centralizes (𝟙 P.G.val) (N.inclusion ≫ P.T.inclusion).hom.hom := by
  obtain ⟨_, _, _, _, _, hcentre⟩ := LinearAlgebraicGroups.RootData.SchemeCentre.schemeCentre
    P.G P.reductive P.T P.split P.maximal
  haveI := P.G.property.1
  haveI := P.T.isClosedImmersion
  haveI : IsAffine P.T.group.X.left := isAffine_of_isAffineHom P.T.inclusion.hom.hom.left
  haveI := N.isClosedImmersion
  obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr
    (isAffine_of_isAffineHom N.inclusion.hom.hom.left)
  let n : AdjointRepresentation.GroupPoints P.T.group B.unop := e.hom ≫ N.inclusion.hom.hom
  have hk : N.inclusion.hom.hom ≫ t.hom.hom = 1 := hN.w
  have hn : n ≫ t.hom.hom = 1 := by
    rw [show n = e.hom ≫ N.inclusion.hom.hom from rfl, Category.assoc, hk, MonObj.comp_one]
  have hc := (hcentre B.unop n).mpr (by
    intro χ hχ
    let α : Root P.T := ⟨χ, hχ⟩
    let β := h.roots α
    have hχ' : t ≫ β.val = χ := (ht β.val).trans (h.root_eq α)
    rw [← hχ', Grp.comp_hom_hom, ← Category.assoc, hn, MonObj.one_comp])
  have hpre := centralizes_precomp hc e.inv
  simpa only [n, Grp.comp_hom_hom, Category.assoc, Iso.inv_hom_id_assoc] using hpre

/-- If there are no roots, the empty ordered cell shows that the torus is
the entire group. -/
theorem isIso_torusInclusion_of_no_roots (P : Pinning.SplitBorelPair k)
    (U : RootSubgroupFamily P.T) (h : IsEmpty (Root P.T)) :
    IsIso P.T.inclusion := by
  let M := specGroup (groupAlgebra k Specs.DiagonalizableGroups.IntegerCharacters)
  let c : Cocharacter P.T.group := Grp.homMk'' (1 : M.X ⟶ P.T.group.X)
    (by rw [MonObj.comp_one, MonObj.one_eq_one])
    (by
      have hmul : (1 : M.X ⟶ P.T.group.X) ⊗ₘ (1 : M.X ⟶ P.T.group.X) =
          lift (fst M.X M.X ≫ (1 : M.X ⟶ P.T.group.X))
            (snd M.X M.X ≫ (1 : M.X ⟶ P.T.group.X)) := by
        rw [← lift_map, lift_fst_snd, Category.id_comp]
      rw [hmul, ← CategoryTheory.Hom.mul_def, MonObj.comp_one, MonObj.comp_one,
        MonObj.comp_one, one_mul])
  have hopen := LinearAlgebraicGroups.RootData.OrderedRootProducts.regularRootCell
    P.G P.reductive P.T P.split P.maximal c
    (fun α => (h.false α).elim) U [] []
    ⟨List.nodup_nil, fun α => (h.false α).elim⟩
    ⟨List.nodup_nil, fun α => (h.false α).elim⟩
  let S := 𝟙_ (SchemeOver k)
  let Y := S ⊗ (P.T.group.X ⊗ S)
  let p : Y ⟶ P.T.group.X := snd _ _ ≫ fst _ _
  let i : S ⟶ Y := lift (𝟙 _) (lift η[P.T.group.X] (𝟙 _))
  have hY : Nonempty Y.left := ⟨i.left (IsLocalRing.closedPoint k)⟩
  have := P.G.property.2.1
  have := P.G.property.2.2
  have := P.reductive.2.1
  have := irreducible_of_geometricallyConnected P.G.val
  have hp : rootCellMap P.T U [] [] = p ≫ P.T.inclusion.hom.hom := by
    simp [rootCellMap, rootProduct, OrderedRootProducts.product, p, S, Category.assoc]
  have := P.T.isClosedImmersion
  have hnonempty : Nonempty (OrderedRootProducts.product (fun α => (U α).val.group.X) [] ⊗
      (P.T.group.X ⊗ OrderedRootProducts.product (fun α => (U α).val.group.X) [])).left := hY
  have hdom : IsDominant (rootCellMap P.T U [] []).left := by
    let := hopen
    exact ⟨(rootCellMap P.T U [] []).left.isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty _)⟩
  have : IsDominant (p.left ≫ P.T.inclusion.hom.hom.left) := by
    rw [show p.left ≫ P.T.inclusion.hom.hom.left = (rootCellMap P.T U [] []).left from
      congrArg Over.Hom.left hp.symm]
    exact hdom
  haveI : IsDominant P.T.inclusion.hom.hom.left := IsDominant.of_comp p.left _
  haveI : Surjective P.T.inclusion.hom.hom.left :=
    surjective_of_isDominant_of_isClosed_range _ P.T.inclusion.hom.hom.left.isClosedEmbedding.isClosed_range
  haveI : Smooth P.G.val.X.hom := P.reductive.1
  haveI := isReduced_of_smooth_over_field P.G.val.X.hom
  haveI := isIso_of_isClosedImmersion_of_surjective P.T.inclusion.hom.hom.left
  exact isIso_of_schemeIso P.T.inclusion

private theorem isIso_borelInclusion (P : Pinning.SplitBorelPair k) [IsIso P.T.inclusion] :
    IsIso P.B.inclusion := by
  obtain ⟨j, hj⟩ := P.containsTorus
  letI : Mono P.B.inclusion := Functor.mono_of_mono_map underlying
    (by exact mono_over _ P.B.isClosedImmersion)
  letI : IsSplitEpi P.B.inclusion := IsSplitEpi.mk' ⟨inv P.T.inclusion ≫ j, by
    rw [Category.assoc, hj, IsIso.inv_hom_id]⟩
  exact isIso_of_mono_of_isSplitEpi _

/-- The lifting assertion in the rootless case. The two torus inclusions and
the two Borel inclusions are isomorphisms, so the torus map already gives
the required ambient map. -/
theorem lifting_of_no_roots {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair) (h : LatticeMap D E)
    (hEmpty : IsEmpty (Root P.pair.T)) : Lifts P Q D E h := by
  haveI := isIso_torusInclusion_of_no_roots P.pair P.roots hEmpty
  haveI := isIso_torusInclusion_of_no_roots Q.pair Q.roots ⟨fun α => hEmpty.false (h.roots.symm α)⟩
  haveI := isIso_borelInclusion P.pair
  haveI := isIso_borelInclusion Q.pair
  obtain ⟨t, hχ, hts, ⟨N, hN, hfin⟩, htiso⟩ :=
    torusMap P.pair.split Q.pair.split h.characters h.injective h.finiteIndex
  let f := inv P.pair.T.inclusion ≫ t ≫ Q.pair.T.inclusion
  have hf : P.pair.T.inclusion ≫ f = t ≫ Q.pair.T.inclusion := by simp [f]
  let b := P.pair.B.inclusion ≫ f ≫ inv Q.pair.B.inclusion
  have hbs : b ≫ Q.pair.B.inclusion = P.pair.B.inclusion ≫ f := by simp [b]
  haveI : Surjective (scheme.map t) := hts
  haveI : Surjective (scheme.map f) := by
    dsimp only [f]
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  haveI : Surjective (scheme.map b) := by
    dsimp only [b]
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  let n := N.inclusion ≫ P.pair.T.inclusion
  haveI : IsClosedImmersion (scheme.map n) := by
    haveI : IsClosedImmersion (scheme.map N.inclusion) := N.isClosedImmersion
    haveI : IsClosedImmersion (scheme.map P.pair.T.inclusion) := P.pair.T.isClosedImmersion
    dsimp only [n]
    rw [Functor.map_comp]
    infer_instance
  let N' : ClosedSubgroup P.pair.G.val := ⟨N.group, n, ‹IsClosedImmersion (scheme.map n)›⟩
  refine ⟨f, t, b, ⟨‹Surjective (scheme.map f)›, N', ?_, hfin, ?_⟩, hts,
    ‹Surjective (scheme.map b)›, hf, hbs.symm, hχ, fun α => (hEmpty.false α.val).elim, ?_⟩
  · change IsPullback n.hom.hom (toUnit _) f.hom.hom η[Q.pair.G.val.X]
    apply hN.of_iso (Iso.refl _) (underlying.mapIso (asIso P.pair.T.inclusion))
      (Iso.refl _) (underlying.mapIso (asIso Q.pair.T.inclusion))
    · simp [n]
    · exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
    · exact congrArg (fun g : P.pair.T.group ⟶ Q.pair.G.val => g.hom.hom) hf.symm
    · change η[Q.pair.T.group.X] ≫ Q.pair.T.inclusion.hom.hom = (𝟙 _) ≫ η[Q.pair.G.val.X]
      rw [Category.id_comp]
      exact IsMonHom.one_hom (f := Q.pair.T.inclusion.hom.hom)
  · exact torusKernel_central h t hχ N hN
  · intro hbij
    haveI := htiso hbij
    dsimp only [f]
    infer_instance


/-- A dominant section over an open chart fills the whole inverse image
when the projection is separated and its source is reduced. -/
private theorem openSection_isIso {U X Y : Scheme.{u}} (s : U ⟶ X) (p : X ⟶ Y)
    [IsReduced X] [IsDominant s] [IsOpenImmersion (s ≫ p)] [IsSeparated p] :
    IsIso (pullback.lift s (𝟙 U) (by simp : s ≫ p = 𝟙 U ≫ (s ≫ p))) := by
  let i := s ≫ p
  let q := pullback.snd p i
  let l : U ⟶ pullback p i := pullback.lift s (𝟙 U) (by simp [i])
  have hl : l ≫ q = 𝟙 U := pullback.lift_snd _ _ _
  have : IsSeparated q := MorphismProperty.pullback_snd p i inferInstance
  have : IsClosedImmersion (l ≫ q) := hl ▸ (inferInstance : IsClosedImmersion (𝟙 U))
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l q
  let f := pullback.fst p i
  have : IsOpenImmersion f := MorphismProperty.pullback_fst p i inferInstance
  have : IsReduced (pullback p i : Scheme.{u}) := isReduced_of_isOpenImmersion f
  have hlf : l ≫ f = s := pullback.lift_fst _ _ _
  have : IsDominant (l ≫ f) := hlf.symm ▸ inferInstance
  have : IsDominant l := IsDominant.of_comp_of_isOpenImmersion l f
  have : Surjective l :=
    surjective_of_isDominant_of_isClosed_range _ l.isClosedEmbedding.isClosed_range
  exact isIso_of_isClosedImmersion_of_surjective l

private theorem isIso_of_dominant_mono
    (G H : AffineAlgebraicGroup k) (f : G.val ⟶ H.val)
    [IsDominant f.hom.hom.left] [Mono f.hom.hom] [IsReduced H.val.X.left] :
    IsIso f := by
  obtain ⟨I, p, i, ⟨hcomp, hflat, _, _, hpa, hic⟩, _, _⟩ :=
    LinearAlgebraicGroups.schemeImageFactorization G H f
  have hleft : p.hom.hom.left ≫ i.hom.hom.left = f.hom.hom.left :=
    congrArg (fun g => g.hom.hom.left) hcomp
  have : IsDominant (p.hom.hom.left ≫ i.hom.hom.left) := hleft.symm ▸ inferInstance
  have : IsDominant i.hom.hom.left := IsDominant.of_comp p.hom.hom.left _
  have : Surjective i.hom.hom.left :=
    surjective_of_isDominant_of_isClosed_range _ i.hom.hom.left.isClosedEmbedding.isClosed_range
  have : IsIso i.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  have : Flat f.hom.hom.left := by rw [← hleft]; infer_instance
  have : QuasiCompact f.hom.hom.left := by rw [← hleft]; infer_instance
  have : Surjective f.hom.hom.left := by rw [← hleft]; infer_instance
  have : IsIso f.hom.hom.left := Flat.isIso_of_surjective_of_mono f.hom.hom.left
  exact isIso_of_schemeIso f

private theorem mono_iff_trivial_kernel {G H : GroupScheme k} (f : G ⟶ H) :
    Mono f.hom.hom ↔
      ∀ (X : SchemeOver k) (x : X ⟶ G.X), x ≫ f.hom.hom = 1 → x = 1 := by
  constructor
  · intro hm X x hx
    apply (cancel_mono f.hom.hom).mp
    rwa [MonObj.one_comp]
  · intro hm
    refine ⟨fun {X} a b hab => ?_⟩
    apply mul_inv_eq_one.mp
    apply hm X
    rw [MonObj.mul_comp, GrpObj.inv_comp, hab, mul_inv_cancel]

/-- A group homomorphism with a dominant lift of an open chart containing
the identity is an isomorphism when the source is reduced and the target is integral. -/
private theorem isIso_of_dominant_open_lift (G H : AffineAlgebraicGroup k)
    (f : G.val ⟶ H.val) [IsReduced G.val.X.left] [IsIntegral H.val.X.left]
    {U : SchemeOver k} (s : U ⟶ G.val.X) (e : 𝟙_ (SchemeOver k) ⟶ U) (he : e ≫ s = 1)
    (hopen : IsOpenImmersion (s ≫ f.hom.hom).left) [IsDominant s.left] : IsIso f := by
  have := G.property.1
  have := H.property.1
  let j := s.left ≫ f.hom.hom.left
  have : IsOpenImmersion j := hopen
  have : Nonempty U.left := ⟨e.left (IsLocalRing.closedPoint k)⟩
  let l : U.left ⟶ pullback f.hom.hom.left j := pullback.lift s.left (𝟙 U.left) (by simp [j])
  have : IsIso l := openSection_isIso s.left f.hom.hom.left
  let q := pullback.snd f.hom.hom.left j
  have hl : l ≫ q = 𝟙 U.left := pullback.lift_snd _ _ _
  have : IsIso (l ≫ q) := hl ▸ (inferInstance : IsIso (𝟙 U.left))
  have : IsIso q := IsIso.of_isIso_comp_left l q
  have : IsDominant j := ⟨j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have : IsDominant f.hom.hom.left := IsDominant.of_comp s.left _
  have : Mono f.hom.hom := (mono_iff_trivial_kernel f).mpr (by
    intro X x hx
    let u := toUnit X ≫ e
    have hu : u ≫ s = (1 : X ⟶ G.val.X) := by
      rw [Category.assoc, he, MonObj.comp_one]
    have hxu : x ≫ f.hom.hom = u ≫ (s ≫ f.hom.hom) := by
      rw [← Category.assoc, hu, MonObj.one_comp, hx]
    let a := pullback.lift x.left u.left (congrArg Over.Hom.left hxu)
    have ha : a = u.left ≫ l := (cancel_mono q).mp (by
      rw [Category.assoc, hl, Category.comp_id]
      exact pullback.lift_snd _ _ _)
    apply Over.OverMorphism.ext
    rw [← hu]
    change x.left = u.left ≫ s.left
    calc
      x.left = a ≫ pullback.fst f.hom.hom.left j := (pullback.lift_fst _ _ _).symm
      _ = u.left ≫ s.left := by rw [ha, Category.assoc, pullback.lift_fst])
  exact isIso_of_dominant_mono G H f

/-- The final kernel criterion for a proposed lift. Centrality forces the
scheme kernel into the source torus, and the restriction then detects it. -/
theorem isIso_of_centralIsogeny_of_torusIso (P Q : Pinning.SplitBorelPair k)
    (f : P.G.val ⟶ Q.G.val) (t : P.T.group ⟶ Q.T.group) [IsIso t]
    (h : IsCentralIsogeny f) (ht : P.T.inclusion ≫ f = t ≫ Q.T.inclusion) : IsIso f := by
  obtain ⟨hf, N, hN, _, hc⟩ := h
  obtain ⟨_, e, _, hZ, hrep, _⟩ := LinearAlgebraicGroups.RootData.SchemeCentre.schemeCentre
    P.G P.reductive P.T P.split P.maximal
  obtain ⟨z, hz⟩ := (hrep _ _).mp hc
  let q := diagonalClosedInclusion k (Specs.SchemeCentre.rootLattice P.T)
  let r : N.group.X ⟶ P.T.group.X := z ≫ (q ≫ e.hom).hom.hom
  have hr : r ≫ P.T.inclusion.hom.hom = N.inclusion.hom.hom := by
    simpa only [r, q, Grp.comp_hom_hom, Category.assoc] using hz
  haveI : Mono Q.T.inclusion.hom.hom := mono_over _ Q.T.isClosedImmersion
  haveI : IsIso (underlying.map t) := underlying.map_isIso t
  have hk : N.inclusion.hom.hom = 1 := by
    have hr' : r = 1 := by
      apply (cancel_mono (t.hom.hom ≫ Q.T.inclusion.hom.hom)).mp
      change r ≫ (t ≫ Q.T.inclusion).hom.hom =
        (1 : N.group.X ⟶ P.T.group.X) ≫ (t ≫ Q.T.inclusion).hom.hom
      rw [← ht, Grp.comp_hom_hom, ← Category.assoc r, hr, MonObj.one_comp]
      exact hN.w
    rw [← hr, hr', MonObj.one_comp]
  have : Mono f.hom.hom := (mono_iff_trivial_kernel f).mpr (by
    intro X z hz
    have hw : z ≫ f.hom.hom = toUnit X ≫ η[Q.G.val.X] := hz
    let l := hN.lift z (toUnit X) hw
    have hl : l ≫ N.inclusion.hom.hom = z := hN.lift_fst _ _ _
    rw [hk, MonObj.comp_one] at hl
    exact hl.symm)
  have := hf
  have : Smooth Q.G.val.X.hom := Q.reductive.1
  have := isReduced_of_smooth_over_field Q.G.val.X.hom
  exact isIso_of_dominant_mono P.G Q.G f

private theorem formallyUnramified_of_unique_dual_points (A : TestAlgebra k)
    [Algebra.Smooth k A]
    (h : ∀ (p q : A ⟶ CommAlgCat.of k (DualNumber A)),
      p ≫ reduction A = q ≫ reduction A → p = q) : Algebra.FormallyUnramified k A := by
  let D := KaehlerDifferential.D k A
  have hD (a : A) : D a = 0 := by
    by_contra ha
    obtain ⟨ell, he⟩ := Module.Projective.exists_dual_ne_zero A ha
    let p : A ⟶ CommAlgCat.of k (DualNumber A) :=
      ConcreteCategory.ofHom
        { toFun := fun b => ⟨b, ell (D b)⟩
          map_zero' := by apply TrivSqZeroExt.ext <;> simp
          map_one' := by apply TrivSqZeroExt.ext <;> simp
          map_add' := fun x y => by
            apply TrivSqZeroExt.ext
            · rfl
            · change ell (D (x + y)) = ell (D x) + ell (D y)
              simp only [map_add]
          map_mul' := fun x y => by
            apply TrivSqZeroExt.ext
            · rfl
            · change ell (D (x * y)) = x * ell (D y) + ell (D x) * y
              simp only [D.leibniz, map_add, map_smul, smul_eq_mul, mul_comm y]
          commutes' := fun t => by
            apply TrivSqZeroExt.ext
            · rfl
            · change ell (D (algebraMap k A t)) = 0
              rw [D.map_algebraMap, map_zero] }
    have hr : p ≫ reduction A = constants A ≫ reduction A :=
      CommAlgCat.hom_ext (AlgHom.ext (fun _ => rfl))
    exact he (congrArg TrivSqZeroExt.snd (ConcreteCategory.congr_hom (h p (constants A) hr) a))
  constructor
  suffices (⊤ : Submodule A (KaehlerDifferential k A)) ≤ ⊥ by
    exact (subsingleton_iff_forall_eq 0).mpr fun y => this Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation k A, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact hD x

private theorem relativeTangent_subsingleton (G : AffineAlgebraicGroup k)
    (hs : Subsingleton (Lie k G.val)) (R : TestAlgebra k) :
    Subsingleton (RelativeTangent G.val R) := by
  obtain ⟨s⟩ := LinearAlgebraicGroups.identityLieBracket k G
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨n, b, ⟨T⟩⟩ := tangent_coordinates G s
  have hn : IsEmpty (ULift.{u} (Fin n)) := ⟨fun j => b.ne_zero j (hs.elim (b j) _)⟩
  exact (T.equiv R).surjective.subsingleton

/-- An affine algebraic group with zero identity tangent is finite étale. -/
private theorem finite_etale_of_trivial_lie [CharZero k] (G : AffineAlgebraicGroup k)
    (hs : Subsingleton (Lie k G.val)) :
    IsFinite G.val.X.hom ∧ Etale G.val.X.hom := by
  obtain ⟨A₀, ⟨e⟩⟩ := essImage_algSpec.mpr G.property.1
  let A := A₀.unop
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  have hsm : Smooth ((testSpec k).obj A₀).hom := by
    rw [← Over.w e.hom]
    have := LinearAlgebraicGroups.characteristicZeroSmoothness k G
    infer_instance
  have halg : Algebra.Smooth k A := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) at hsm
    exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm)
  have hu : Algebra.FormallyUnramified k A := formallyUnramified_of_unique_dual_points A (by
    let R := A
    intro p q hpq
    let x : GroupPoints G.val (CommAlgCat.of k (DualNumber R)) :=
      (testSpec k).map p.op ≫ e.hom
    let y : GroupPoints G.val (CommAlgCat.of k (DualNumber R)) :=
      (testSpec k).map q.op ≫ e.hom
    let r := (((groupPointsFunctor k).obj G.val).map (reduction R)).hom
    have hrxy : r x = r y := by
      change (testSpec k).map (reduction R).op ≫ (testSpec k).map p.op ≫ e.hom =
        (testSpec k).map (reduction R).op ≫ (testSpec k).map q.op ≫ e.hom
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        ← op_comp, ← op_comp, hpq]
    let v : RelativeTangent G.val R := ⟨x * y⁻¹, by
      change r (x * y⁻¹) = 1
      rw [map_mul, map_inv, hrxy, mul_inv_cancel]⟩
    have huv := relativeTangent_subsingleton G hs R
    have hv : x * y⁻¹ = 1 := congrArg (fun z : RelativeTangent G.val R => z.toMul.val) (huv.elim v 0)
    have hxy := mul_inv_eq_one.mp hv
    apply Quiver.Hom.op_inj
    apply ff.map_injective
    exact (cancel_mono e.hom).mp hxy)
  have ht : LocallyOfFiniteType ((testSpec k).obj A₀).hom := by
    rw [← Over.w e.hom]
    have := G.property.2.1
    infer_instance
  have hft : Algebra.FiniteType k A := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) at ht
    exact RingHom.finiteType_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp ht)
  have hfin : Module.Finite k A := Algebra.FormallyUnramified.finite_of_free k A
  have het : Algebra.Etale k A := Algebra.Etale.iff_formallyUnramified_and_smooth.mpr ⟨hu, halg⟩
  have hf : IsFinite ((testSpec k).obj A₀).hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfin)
  have hg : Etale ((testSpec k).obj A₀).hom := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr het)
  have hei : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  rw [← Over.w e.inv]
  exact ⟨inferInstance, inferInstance⟩

/-- Conjugation on an étale normal subgroup factors through its projection
from the product with a geometrically connected group. -/
private theorem centralizes_etale_kernel (G : AffineAlgebraicGroup k)
    [GeometricallyConnected G.val.X.hom] {H : GroupScheme k} (f : G.val ⟶ H)
    (N : ClosedSubgroup G.val) (hN : IsSchemeKernel f N) [Etale N.group.X.hom] :
    Centralizes (𝟙 G.val) N.inclusion.hom.hom := by
  have hnormal := IsMonHom.Normal.of_isPullback_η f.hom.hom hN
  obtain ⟨c, hc⟩ := hnormal.exists_comp_eq_conj
  have hc' : c ≫ N.inclusion.hom.hom = subgroupConjugation N.inclusion := by
    simpa [subgroupConjugation, GrpObj.conj, MonObj.comp_mul, GrpObj.comp_inv] using hc
  let q := snd G.val.X N.group.X
  have hpb := isPullback_tensor_structure G.val.X N.group.X
  have : Flat q.left := MorphismProperty.of_isPullback hpb inferInstance
  have : QuasiCompact q.left := MorphismProperty.of_isPullback hpb G.property.2.2
  have : GeometricallyConnected q.left := MorphismProperty.of_isPullback hpb inferInstance
  obtain ⟨g, hg⟩ := existsOverFactorEtale q c
  have : Mono N.inclusion.hom.hom := mono_over _ N.isClosedImmersion
  let s := lift (1 : N.group.X ⟶ G.val.X) (𝟙 N.group.X)
  have hs : s ≫ q = 𝟙 _ := lift_snd _ _
  have hz : s ≫ c = 𝟙 N.group.X := by
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [Category.assoc, hc']
    simp [subgroupConjugation, s, MonObj.comp_mul, GrpObj.comp_inv]
  have hg' : g = 𝟙 N.group.X := by
    calc
      g = s ≫ q ≫ g := by rw [← Category.assoc, hs, Category.id_comp]
      _ = 𝟙 _ := by rw [hg, hz]
  have hcq : c = q := by rw [← hg, hg', Category.comp_id]
  apply (centralizes_iff _ _).mpr
  intro S x y
  have hxy := congrArg (fun a => lift y x ≫ a) hc'
  rw [hcq] at hxy
  have he : y * (x ≫ N.inclusion.hom.hom) * y⁻¹ = x ≫ N.inclusion.hom.hom := by
    simpa only [subgroupConjugation, q, Category.assoc, MonObj.comp_mul,
      GrpObj.comp_inv, lift_fst, lift_snd, lift_snd_assoc] using hxy.symm
  change Commute (x ≫ N.inclusion.hom.hom) y
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- In characteristic zero, the scheme kernel of an injective differential
is finite étale. -/
private theorem etale_kernel_of_injective_differential [CharZero k]
    (G H : AffineAlgebraicGroup k)
    (f : G.val ⟶ H.val) (hf : Function.Injective (mapPointKernel f)) :
    ∃ N : ClosedSubgroup G.val, IsSchemeKernel f N ∧ IsFinite N.group.X.hom ∧
      Etale N.group.X.hom := by
  have := H.property.1
  obtain ⟨N, hN⟩ := schemeKernel_exists f
  have hm : Mono N.inclusion.hom.hom := mono_over _ N.isClosedImmersion
  have hd : Function.Injective (mapPointKernel N.inclusion) := by
    intro x y hxy
    apply Additive.toMul.injective
    apply Subtype.ext
    apply (cancel_mono N.inclusion.hom.hom).mp
    exact congrArg (fun z : Lie k G.val => z.toMul.val) hxy
  have hzero : Subsingleton (Lie k N.group) := by
    refine subsingleton_of_forall_eq 0 fun x => hd (hf ?_)
    rw [map_zero, map_zero]
    apply Additive.toMul.injective
    apply Subtype.ext
    change (x.toMul.val ≫ N.inclusion.hom.hom) ≫ f.hom.hom = 1
    rw [Category.assoc, show N.inclusion.hom.hom ≫ f.hom.hom = 1 from hN.w, MonObj.comp_one]
  obtain ⟨hfin, het⟩ := finite_etale_of_trivial_lie (Unipotent.closedSubgroupAlgebraicGroup N) hzero
  exact ⟨N, hN, hfin, het⟩

/-- A geometrically connected group centralizes its finite étale kernel. -/
private theorem finite_central_kernel_of_injective_differential [CharZero k]
    (G H : AffineAlgebraicGroup k) [GeometricallyConnected G.val.X.hom]
    (f : G.val ⟶ H.val) (hf : Function.Injective (mapPointKernel f)) :
    ∃ N : ClosedSubgroup G.val, IsSchemeKernel f N ∧ IsFinite N.group.X.hom ∧
      Centralizes (𝟙 G.val) N.inclusion.hom.hom := by
  obtain ⟨N, hN, hfin, het⟩ := etale_kernel_of_injective_differential G H f hf
  exact ⟨N, hN, hfin, centralizes_etale_kernel G f N hN⟩

/-- An injective differential and dominance give a central isogeny from a
geometrically connected affine algebraic group in characteristic zero. -/
private theorem centralIsogeny_of_dominant_of_injective_differential [CharZero k]
    (G H : AffineAlgebraicGroup k) [GeometricallyConnected G.val.X.hom]
    (f : G.val ⟶ H.val) [IsDominant f.hom.hom.left]
    (hf : Function.Injective (mapPointKernel f)) : IsCentralIsogeny f := by
  obtain ⟨I, p, i, ⟨hcomp, _, hsurj, _, _, hic⟩, _, _⟩ :=
    LinearAlgebraicGroups.schemeImageFactorization G H f
  have hleft : p.hom.hom.left ≫ i.hom.hom.left = f.hom.hom.left :=
    congrArg (fun g => g.hom.hom.left) hcomp
  have : IsDominant (p.hom.hom.left ≫ i.hom.hom.left) := hleft.symm ▸ inferInstance
  have : IsDominant i.hom.hom.left := IsDominant.of_comp p.hom.hom.left _
  have : Surjective i.hom.hom.left :=
    surjective_of_isDominant_of_isClosed_range _ i.hom.hom.left.isClosedEmbedding.isClosed_range
  have : Surjective f.hom.hom.left := by rw [← hleft]; infer_instance
  exact ⟨this, finite_central_kernel_of_injective_differential G H f hf⟩

/-- With an étale kernel, a lift of an open chart is itself an open immersion. -/
private theorem isOpenImmersion_of_open_lift {G H : GroupScheme k} (f : G ⟶ H)
    (N : ClosedSubgroup G) (hN : IsSchemeKernel f N) [Etale N.group.X.hom]
    {U : SchemeOver k} (s : U ⟶ G.X) [IsOpenImmersion (s ≫ f.hom.hom).left] :
    IsOpenImmersion s.left := by
  let p := f.hom.hom
  let j := s ≫ p
  let V := pullback p j
  let a : V ⟶ G.X := pullback.fst p j
  let b : V ⟶ U := pullback.snd p j
  let l : U ⟶ V := pullback.lift s (𝟙 U) (by simp [j])
  have ha : l ≫ a = s := pullback.lift_fst _ _ _
  have hb : l ≫ b = 𝟙 U := pullback.lift_snd _ _ _
  have hj : a ≫ p = b ≫ s ≫ p := pullback.condition
  have hw : (a / (b ≫ s)) ≫ p = toUnit V ≫ η[H.X] := by
    rw [GrpObj.div_comp, Category.assoc, hj]
    exact div_self' (b ≫ s ≫ p)
  let d := hN.lift (a / (b ≫ s)) (toUnit V) hw
  have hd : d ≫ N.inclusion.hom.hom = a / (b ≫ s) := hN.lift_fst _ _ _
  have hmono : Mono N.inclusion.hom.hom := mono_over _ N.isClosedImmersion
  have hl : l ≫ d = toUnit U ≫ η[N.group.X] := by
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [Category.assoc, hd, GrpObj.comp_div, ha, ← Category.assoc, hb, Category.id_comp,
      Category.assoc, IsMonHom.one_hom]
    exact div_self' s
  have hpb : IsPullback l (toUnit U) d η[N.group.X] := by
    refine IsPullback.of_isLimit' ⟨hl⟩ (PullbackCone.IsLimit.mk hl
      (fun c => c.fst ≫ b) ?_ (fun _ => toUnit_unique _ _) ?_)
    · intro c
      have hh := congrArg (fun z => z ≫ N.inclusion.hom.hom) c.condition
      simp only [Category.assoc, hd, GrpObj.comp_div, IsMonHom.one_hom] at hh
      have hh1 : c.fst ≫ a / (c.fst ≫ b ≫ s) = 1 := by
        rw [hh, toUnit_unique c.snd (toUnit c.pt)]
        rfl
      have h : c.fst ≫ a = c.fst ≫ b ≫ s := div_eq_one.mp hh1
      apply pullback.hom_ext
      · rw [Category.assoc, ha]
        exact (Category.assoc _ _ _).trans h.symm
      · change (c.fst ≫ b) ≫ l ≫ b = c.fst ≫ b
        rw [hb, Category.comp_id]
    · intro c m hm _
      rw [← hm, Category.assoc, hb, Category.comp_id]
  have hη : IsOpenImmersion (η[N.group.X]).left := by
    have hcomp : Etale ((η[N.group.X]).left ≫ N.group.X.hom) :=
      (Over.w (η[N.group.X])).symm ▸ inferInstanceAs (Etale (𝟙 _))
    have hη' : Etale (η[N.group.X]).left := Etale.of_comp _ N.group.X.hom
    have hsec : (η[N.group.X]).left ≫ N.group.X.hom = 𝟙 (Spec (CommRingCat.of k)) :=
      Over.w (η[N.group.X])
    have hId : IsIso (𝟙 (Spec (CommRingCat.of k))) := inferInstance
    have hm : Mono (η[N.group.X]).left := mono_of_mono_fac hsec
    exact IsOpenImmersion.of_flat_of_mono _
  have hleft := hpb.map (Over.forget (Spec (CommRingCat.of k)))
  have : IsOpenImmersion l.left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hleft.flip hη
  have : IsOpenImmersion a.left := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    ((IsPullback.of_hasPullback p j).map (Over.forget _)).flip
    (show IsOpenImmersion j.left from inferInstance)
  have hs : l.left ≫ a.left = s.left := congrArg Over.Hom.left ha
  rw [← hs]
  infer_instance

/-- A split open chart and an injective differential force a projection
from an integral affine algebraic group to be an isomorphism. -/
private theorem isIso_of_open_chart_of_injective_differential [CharZero k]
    (G H : AffineAlgebraicGroup k) [IsIntegral G.val.X.left] [IsIntegral H.val.X.left]
    (f : G.val ⟶ H.val) (hf : Function.Injective (mapPointKernel f))
    {U : SchemeOver k} (s : U ⟶ G.val.X) (e : 𝟙_ (SchemeOver k) ⟶ U) (he : e ≫ s = 1)
    (hopen : IsOpenImmersion (s ≫ f.hom.hom).left) : IsIso f := by
  obtain ⟨N, hN, _, hEtale⟩ := etale_kernel_of_injective_differential G H f hf
  have : IsOpenImmersion s.left := isOpenImmersion_of_open_lift f N hN s
  have : Nonempty U.left := ⟨e.left (IsLocalRing.closedPoint k)⟩
  have : IsDominant s.left := ⟨s.left.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  exact isIso_of_dominant_open_lift G H f s e he hopen

section WordTangents

variable {J R : Type*} [Group J] [Group R]

/-- The right translate of a lift back to the identity, using a section of reduction. -/
private def displacement (r : J →* R) (c : R →* J) (x : J) : J :=
  x * (c (r x))⁻¹

private def displacementSubgroup (r : J →* R) (c : R →* J) (S : Subgroup J) :
    Subgroup J where
  carrier := {x | displacement r c x ∈ S ∧ c (r x) ∈ Subgroup.normalizer (S : Set _)}
  one_mem' := by
    change displacement r c 1 ∈ S ∧ c (r 1) ∈ Subgroup.normalizer (S : Set _)
    simp [displacement]
  mul_mem' := by
    intro x y hx hy
    change displacement r c x ∈ S ∧ c (r x) ∈ Subgroup.normalizer (S : Set _) at hx
    change displacement r c y ∈ S ∧ c (r y) ∈ Subgroup.normalizer (S : Set _) at hy
    change displacement r c (x * y) ∈ S ∧ c (r (x * y)) ∈ Subgroup.normalizer (S : Set _)
    have h : displacement r c (x * y) = displacement r c x *
        (c (r x) * displacement r c y * (c (r x))⁻¹) := by
      simp only [displacement, map_mul]
      group
    rw [h, map_mul, map_mul]
    exact ⟨S.mul_mem hx.1 ((Subgroup.mem_normalizer_iff.mp hx.2 _).mp hy.1), (Subgroup.normalizer (S : Set J)).mul_mem hx.2 hy.2⟩
  inv_mem' := by
    intro x hx
    change displacement r c x ∈ S ∧ c (r x) ∈ Subgroup.normalizer (S : Set _) at hx
    change displacement r c x⁻¹ ∈ S ∧ c (r x⁻¹) ∈ Subgroup.normalizer (S : Set _)
    have h : displacement r c x⁻¹ = (c (r x))⁻¹ * (displacement r c x)⁻¹ * c (r x) := by
      simp only [displacement, map_inv]
      group
    rw [h, map_inv, map_inv]
    exact ⟨(Subgroup.mem_normalizer_iff''.mp hx.2 _).mp (S.inv_mem hx.1), (Subgroup.normalizer (S : Set J)).inv_mem hx.2⟩

/-- If a subgroup contains the displacements of every factor, and each constant
factor normalizes it, the subgroup contains the displacement of the signed word. -/
private theorem evaluate_displacement {k : Type u} [Field k] {G : GroupScheme k}
    {X T T₀ : SchemeOver k} (f : X ⟶ G.X)
    (r : (T ⟶ G.X) →* (T₀ ⟶ G.X)) (c : (T₀ ⟶ G.X) →* (T ⟶ G.X))
    (S : Subgroup (T ⟶ G.X))
    (h : ∀ a : T ⟶ X, displacement r c (a ≫ f) ∈ S)
    (hn : ∀ a : T ⟶ X, c (r (a ≫ f)) ∈ Subgroup.normalizer (S : Set _))
    (n : ℕ) (p : T ⟶ wordDomain X n) : displacement r c (evaluate f n p) ∈ S := by
  let D := displacementSubgroup r c S
  have hD (a : T ⟶ X) : a ≫ f ∈ D := ⟨h a, hn a⟩
  have hw : evaluate f n p ∈ D := by
    induction n with
    | zero => exact D.one_mem
    | succ n ih =>
      unfold evaluate
      exact D.mul_mem (D.mul_mem (hD _) (D.inv_mem (hD _))) (ih _)
  exact hw.1

variable [CharZero k]

private theorem liftGenericPoint (h : DominantGenericLift.{u})
    {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra k A] [Algebra k B]
    [Algebra k (DualNumber (FractionRing B))]
    (f : A →ₐ[k] B) (hf : Function.Injective f) (hft : f.toRingHom.FiniteType)
    (q : A →ₐ[k] DualNumber (FractionRing B))
    (hq : ∀ a, (q a).fst = algebraMap B (FractionRing B) (f a)) :
    ∃ p : B →ₐ[k] DualNumber (FractionRing B),
      (∀ b, (p b).fst = algebraMap B (FractionRing B) b) ∧ p.comp f = q := by
  let : Algebra A B := f.toRingHom.toAlgebra
  have : Algebra.FiniteType A B := hft
  have : CharZero A := charZero_of_injective_algebraMap (algebraMap k A).injective
  obtain ⟨p, hp, hpq⟩ := h (A := A) (B := B) hf q.toRingHom hq
  have hp' (x : A) : p (f x) = q x := DFunLike.congr_fun hpq x
  let p' : B →ₐ[k] DualNumber (FractionRing B) :=
    { p with
      commutes' := fun x => by
        change p (algebraMap k B x) = algebraMap k _ x
        rw [← f.commutes, hp', q.commutes] }
  exact ⟨p', hp, AlgHom.ext hp'⟩

private abbrev affineSpec {k : Type u} [Field k] (R : TestAlgebra k) : SchemeOver k :=
  (testSpec k).obj (op R)

private def genericTestAlgebra (B : TestAlgebra k) : TestAlgebra k :=
  CommAlgCat.of k (FractionRing B)

private def genericInclusion (B : TestAlgebra k) : B ⟶ genericTestAlgebra B :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom k B (FractionRing B))

/-- A dual point above the generic source point's image lifts along the affine map. -/
private theorem liftGenericAffinePoint (h : DominantGenericLift.{u})
    {A B : TestAlgebra k} [IsDomain A] [IsDomain B] (f : A ⟶ B)
    (hf : Function.Injective f.hom) (hft : f.hom.toRingHom.FiniteType)
    (q : Points (affineSpec A) (CommAlgCat.of k (DualNumber (genericTestAlgebra B))))
    (hq : mapPoints (reduction (genericTestAlgebra B)) q =
      (testSpec k).map (f ≫ genericInclusion B).op) :
    ∃ p : Points (affineSpec B) (CommAlgCat.of k (DualNumber (genericTestAlgebra B))),
      mapPoints (reduction (genericTestAlgebra B)) p =
        (testSpec k).map (genericInclusion B).op ∧
      p ≫ (testSpec k).map f.op = q := by
  let R := genericTestAlgebra B
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let q' : A ⟶ CommAlgCat.of k (DualNumber R) := (ff.preimage q).unop
  have hq' : (testSpec k).map q'.op = q := ff.map_preimage q
  have he : q' ≫ reduction R = f ≫ genericInclusion B := by
    apply Quiver.Hom.op_inj
    apply ff.map_injective
    rw [op_comp, Functor.map_comp, hq']
    exact hq
  have hval (x : A) : (q'.hom x).fst = algebraMap B (FractionRing B) (f.hom x) :=
    ConcreteCategory.congr_hom he x
  let : Algebra k (DualNumber (FractionRing B)) :=
    (CommAlgCat.of k (DualNumber R)).algebra
  obtain ⟨p, hp, hpf⟩ := liftGenericPoint h f.hom hf hft q'.hom hval
  let pC : B ⟶ CommAlgCat.of k (DualNumber R) :=
    ConcreteCategory.ofHom (show B →ₐ[k] DualNumber R from p)
  have hp0 : pC ≫ reduction R = genericInclusion B := CommAlgCat.hom_ext (AlgHom.ext hp)
  have hpf' : f ≫ pC = q' := CommAlgCat.hom_ext hpf
  refine ⟨(testSpec k).map pC.op, ?_, ?_⟩
  · change (testSpec k).map (reduction R).op ≫ (testSpec k).map pC.op = _
    rw [← Functor.map_comp, ← op_comp, hp0]
  · rw [← Functor.map_comp, ← op_comp, hpf', hq']

private abbrev reducePoints (H : GroupScheme k) (R : TestAlgebra k) :=
  (((groupPointsFunctor k).obj H).map (reduction R)).hom

private abbrev constantPoints (H : GroupScheme k) (R : TestAlgebra k) :=
  (((groupPointsFunctor k).obj H).map (constants R)).hom

omit [CharZero k] in
private theorem reduce_constant (H : GroupScheme k) (R : TestAlgebra k)
    (x : GroupPoints H R) : reducePoints H R (constantPoints H R x) = x := by
  change (testSpec k).map (reduction R).op ≫ (testSpec k).map (constants R).op ≫ x = x
  have hr : constants R ≫ reduction R = 𝟙 R := CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, hr, op_id]
  have hi : (testSpec k).map (𝟙 (op R)) = 𝟙 _ := (testSpec k).map_id _
  rw [hi, Category.id_comp]

omit [CharZero k] in
private theorem displacement_factors {G H : GroupScheme k} (a : G ⟶ H)
    (R : TestAlgebra k) (x : GroupPoints G (CommAlgCat.of k (DualNumber R))) :
    displacement (reducePoints H R) (constantPoints H R) (x ≫ a.hom.hom) =
      displacement (reducePoints G R) (constantPoints G R) x ≫ a.hom.hom := by
  unfold displacement
  rw [MonObj.mul_comp, GrpObj.inv_comp]
  congr 2

omit [CharZero k] in
private theorem displacement_of_translated_tangent {G : GroupScheme k} (R : TestAlgebra k)
    (x : GroupPoints G R) (v : RelativeTangent G R) :
    displacement (reducePoints G R) (constantPoints G R)
        (v.toMul.val * constantPoints G R x) = v.toMul.val := by
  rw [displacement, map_mul, v.toMul.property, one_mul, reduce_constant, mul_inv_cancel_right]

/-- Every generic relative tangent of a subgroup with a dominant word map
satisfies the translated tangent constraint imposed on the word factors. -/
private theorem relativeTangent_mem_of_dominant_word (h : DominantGenericLift.{u})
    {G : GroupScheme k} (N : ClosedSubgroup G) {X : SchemeOver k}
    (g : X ⟶ G.X) (n : ℕ) (w : wordDomain X n ⟶ N.group.X)
    (hw : ∀ (T : SchemeOver k) (p : T ⟶ wordDomain X n),
      p ≫ w ≫ N.inclusion.hom.hom = evaluate g n p)
    {A B : TestAlgebra k} [IsDomain A] [IsDomain B]
    (eW : affineSpec B ≅ wordDomain X n) (eN : affineSpec A ≅ N.group.X)
    (f : A ⟶ B) (hf : Function.Injective f.hom) (hft : f.hom.toRingHom.FiniteType)
    (hf' : eW.hom ≫ w = (testSpec k).map f.op ≫ eN.hom) :
    let R := genericTestAlgebra B
    let r := reducePoints G R
    let c := constantPoints G R
    ∀ (S : Subgroup (GroupPoints G (CommAlgCat.of k (DualNumber R)))),
      (∀ a : Points X (CommAlgCat.of k (DualNumber R)), displacement r c (a ≫ g) ∈ S) →
      (∀ a : Points X (CommAlgCat.of k (DualNumber R)),
        c (r (a ≫ g)) ∈ Subgroup.normalizer (S : Set (GroupPoints G (CommAlgCat.of k (DualNumber R))))) →
      ∀ v : RelativeTangent N.group R, v.toMul.val ≫ N.inclusion.hom.hom ∈ S := by
  dsimp only
  intro S hS hN v
  let R := genericTestAlgebra B
  let base : GroupPoints N.group R :=
    (testSpec k).map (f ≫ genericInclusion B).op ≫ eN.hom
  let z : GroupPoints N.group (CommAlgCat.of k (DualNumber R)) :=
    v.toMul.val * constantPoints N.group R base
  have hz : reducePoints N.group R z = base := by
    dsimp only [z]
    rw [map_mul, v.toMul.property, one_mul, reduce_constant]
  let q := z ≫ eN.inv
  have hq : mapPoints (reduction R) q =
      (testSpec k).map (f ≫ genericInclusion B).op := by
    change reducePoints N.group R z ≫ eN.inv = _
    rw [hz, show base = _ ≫ eN.hom from rfl, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨p, _, hp⟩ := liftGenericAffinePoint h f hf hft q hq
  let p' := p ≫ eW.hom
  have hwp : p' ≫ w = z := by
    rw [show p' = p ≫ eW.hom from rfl, Category.assoc, hf', ← Category.assoc,
      hp, show q = z ≫ eN.inv from rfl, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he := evaluate_displacement g (reducePoints G R) (constantPoints G R) S hS hN n p'
  rw [← hw, ← Category.assoc p', hwp, displacement_factors,
    displacement_of_translated_tangent] at he
  exact he

end WordTangents

section FunctionFields

open scoped Polynomial
open Polynomial

/-- An affine map into an integral scheme is dominant if its composite to
the base is dominant and the intermediate function field is algebraic
over the base function field. -/
private theorem injective_of_algebraic_fraction_ring
    {A B C F K : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [CommRing C]
    [Field F] [Field K] [Algebra A B] [Algebra A K] [Algebra B K] [IsFractionRing B K]
    [Algebra A F] [IsFractionRing A F] [Algebra F K]
    [IsScalarTower A B K] [IsScalarTower A F K] [Algebra.IsAlgebraic F K]
    (g : B →+* C) (hg : Function.Injective (g.comp (algebraMap A B))) :
    Function.Injective g := by
  apply (RingHom.injective_iff_ker_eq_bot g).mpr
  apply le_antisymm ?_ bot_le
  intro x hx
  rw [Ideal.mem_bot]
  by_contra hn
  let y := algebraMap B K x
  have hy : y ≠ 0 := fun h => hn ((IsFractionRing.injective B K) (h.trans (map_zero _).symm))
  have hy' : IsIntegral F y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  let q := IsLocalization.integerNormalization (nonZeroDivisors A) (minpoly F y)
  have hq : aeval y q = 0 := IsLocalization.integerNormalization_aeval_eq_zero _
    (minpoly F y) (minpoly.aeval F y)
  have hq' : q.eval₂ (algebraMap A B) x = 0 := by
    apply IsFractionRing.injective B K
    rw [map_zero, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq]
    exact hq
  have hz : q.eval₂ (g.comp (algebraMap A B)) (g x) = 0 := by
    rw [← Polynomial.hom_eval₂, hq', map_zero]
  rw [RingHom.mem_ker.mp hx, Polynomial.eval₂_at_zero] at hz
  have hcz : q.coeff 0 = 0 := hg (hz.trans (map_zero _).symm)
  obtain ⟨d, hd, hqeq⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors A) (minpoly F y)
  have hm := congrArg (fun p : F[X] => p.coeff 0) hqeq
  change ((q.map (algebraMap A F)).coeff 0) = _ at hm
  rw [Polynomial.coeff_map, hcz, map_zero, Polynomial.coeff_smul, Algebra.smul_def] at hm
  exact (mul_ne_zero
    (fun hz => nonZeroDivisors.ne_zero hd (IsFractionRing.injective A F (hz.trans (map_zero _).symm)))
    (minpoly.coeff_zero_ne_zero hy' hy)) hm.symm

/-- If no generic dual-number deformation can move over the base, the
intermediate fraction field is algebraic over the base fraction field. -/
private theorem fraction_algebraic_of_no_generic_deformations
    {A B F K L : Type u} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [Field F] [Field K] [Field L] [Algebra A F] [Algebra A K] [Algebra F K] [Algebra B K]
    [IsScalarTower A B K] [IsScalarTower A F K] [IsFractionRing B K] [Algebra K L]
    [Algebra.EssFiniteType F K]
    (h : ∀ q : B →+* DualNumber L,
      (∀ b, (q b).fst = algebraMap K L (algebraMap B K b)) →
      (∀ a, (q (algebraMap A B a)).snd = 0) →
      ∀ b, (q b).snd = 0) : Algebra.IsAlgebraic F K := by
  have hu : Algebra.FormallyUnramified F K := by
    constructor
    refine subsingleton_of_forall_eq 0 fun z => ?_
    by_contra hz
    obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_ne_zero K hz
    let D := KaehlerDifferential.D F K
    let j : K →+* DualNumber L :=
      { toFun := fun x => ⟨algebraMap K L x, algebraMap K L (ell (D x))⟩
        map_zero' := by ext <;> simp
        map_one' := by ext <;> simp
        map_add' := fun x y => by
          apply TrivSqZeroExt.ext
          · exact map_add (algebraMap K L) x y
          · change algebraMap K L (ell (D (x + y))) =
              algebraMap K L (ell (D x)) + algebraMap K L (ell (D y))
            simp only [map_add]
        map_mul' := fun x y => by
          apply TrivSqZeroExt.ext
          · exact map_mul (algebraMap K L) x y
          · change algebraMap K L (ell (D (x * y))) =
              algebraMap K L x * algebraMap K L (ell (D y)) +
                algebraMap K L (ell (D x)) * algebraMap K L y
            simp only [D.leibniz, map_add, map_smul, smul_eq_mul, map_mul,
              mul_comm (algebraMap K L y)] }
    let q := j.comp (algebraMap B K)
    have hs : ∀ b, (q b).snd = 0 := h q (fun _ => rfl) (fun a => by
      change algebraMap K L (ell (D (algebraMap B K (algebraMap A B a)))) = 0
      rw [← IsScalarTower.algebraMap_apply A B K, IsScalarTower.algebraMap_apply A F K,
        D.map_algebraMap, map_zero, map_zero])
    have hj : j = (TrivSqZeroExt.inlHom L L).comp (algebraMap K L) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors B)
      apply RingHom.ext
      intro b
      apply TrivSqZeroExt.ext
      · rfl
      · exact hs b
    have hD (x : K) : ell (D x) = 0 := by
      apply (algebraMap K L).injective
      rw [map_zero]
      exact congrArg TrivSqZeroExt.snd (DFunLike.congr_fun hj x)
    have hker : ⊤ ≤ LinearMap.ker ell := by
      rw [← KaehlerDifferential.span_range_derivation F K, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hD x
    exact hell (hker Submodule.mem_top)
  let := (Algebra.FormallyUnramified.iff_isSeparable F K).mp hu
  infer_instance

end FunctionFields

private theorem map_ad_pow {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L') (x y : L) (n : ℕ) :
    f ((LieAlgebra.ad R L x ^ n) y) = (LieAlgebra.ad R L' (f x) ^ n) (f y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, LieHom.map_lie, ih]

/-- The Lie homomorphism defined by an assignment satisfying the Serre relations. -/
private theorem serre_lift {R I L : Type*} [CommRing R] [DecidableEq I]
    [LieRing L] [LieAlgebra R L] (A : Matrix I I ℤ) (E F H : I → L)
    (hHH : ∀ i j, ⁅H i, H j⁆ = 0)
    (hEF : ∀ i j, ⁅E i, F j⁆ = if i = j then H i else 0)
    (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j)
    (hHF : ∀ i j, ⁅H i, F j⁆ = -(A i j • F j))
    (hE : ∀ i j, (LieAlgebra.ad R L (E i) ^ (-A i j).toNat) ⁅E i, E j⁆ = 0)
    (hF : ∀ i j, (LieAlgebra.ad R L (F i) ^ (-A i j).toNat) ⁅F i, F j⁆ = 0) :
    ∃ f : Matrix.ToLieAlgebra R A →ₗ⁅R⁆ L,
      (∀ i, f (generator R A (.E i)) = E i) ∧
      (∀ i, f (generator R A (.F i)) = F i) ∧
      (∀ i, f (generator R A (.H i)) = H i) := by
  let v : CartanMatrix.Generators I → L :=
    fun x => match x with
    | .E i => E i
    | .F i => F i
    | .H i => H i
  let f := FreeLieAlgebra.lift R v
  have hgen (x : CartanMatrix.Generators I) : f (FreeLieAlgebra.of R x) = v x :=
    FreeLieAlgebra.lift_of_apply v x
  let K := CartanMatrix.Relations.toIdeal R A
  have hk : K ≤ f.ker := by
    apply LieSubmodule.lieSpan_le.mpr
    intro x hx
    change f x = 0
    simp only [CartanMatrix.Relations.toSet, Set.mem_union] at hx
    rcases hx with (((((⟨⟨i, j⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) |
      ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩)
    · simpa [CartanMatrix.Relations.HH, hgen, v] using hHH i j
    · by_cases hi : i = j
      · subst j
        simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, Function.comp_apply,
          ↓reduceIte, map_sub, LieHom.map_lie, hgen, v]
        simpa using sub_eq_zero.mpr (hEF i i)
      · simpa [CartanMatrix.Relations.EF, hi, hgen, v] using hEF i j
    · simp [CartanMatrix.Relations.HE, hgen, v, hHE]
    · simp [CartanMatrix.Relations.HF, hgen, v, hHF]
    · simpa [CartanMatrix.Relations.adE, map_ad_pow, hgen, v] using hE i j
    · simpa [CartanMatrix.Relations.adF, map_ad_pow, hgen, v] using hF i j
  let g : Matrix.ToLieAlgebra R A →ₗ⁅R⁆ L :=
    { K.toSubmodule.liftQ f.toLinearMap hk with
      map_lie' := by
        intro a b
        induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
        exact f.map_lie a b }
  refine ⟨g, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · exact hgen (.E i)
  · exact hgen (.F i)
  · exact hgen (.H i)

/-- A Lie comparison preserving the root lines and the pinned tangent vectors
pairs the split root coordinates with their prescribed derivatives. -/
private theorem paired_root_coordinates (vectors : CoordinateVectors.{u})
    {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair) (h : LatticeMap D E)
    (e : Lie k P.pair.G.val ≃ Lie k Q.pair.G.val) (hzero : e 0 = 0)
    (hroot : ∀ (α : Root P.pair.T) (v : Lie k P.pair.G.val),
      v ∈ adjointWeightVectors P.pair.T α.val →
      e v ∈ adjointWeightVectors Q.pair.T (h.roots α).val)
    (hpin : ∀ (α : SimpleRoot P.pair) (v : Lie k P.pair.G.val),
      v.toMul.val =
        rootPoint ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion)
          (CommAlgCat.of k (DualNumber k)) DualNumber.eps →
      (e v).toMul.val =
        rootPoint ((Q.pin (h.simpleRoot α)).val.hom ≫ (Q.roots (h.roots α.val)).val.inclusion)
          (CommAlgCat.of k (DualNumber k)) DualNumber.eps)
    (α : Root P.pair.T) :
    ∃ (x : RootCoordinate A P.pair.T (P.roots α).val α.val)
      (y : RootCoordinate A Q.pair.T (Q.roots (h.roots α)).val (h.roots α).val)
      (v : Lie k P.pair.G.val),
      v.toMul.val =
        rootPoint (x.val.hom ≫ (P.roots α).val.inclusion)
          (CommAlgCat.of k (DualNumber k)) DualNumber.eps ∧
      (e v).toMul.val =
        rootPoint (y.val.hom ≫ (Q.roots (h.roots α)).val.inclusion)
          (CommAlgCat.of k (DualNumber k)) DualNumber.eps ∧
      ∀ s : IsSimple P.pair α, x = P.pin ⟨α, s⟩ ∧ y = Q.pin (h.simpleRoot ⟨α, s⟩) := by
  classical
  obtain ⟨a, ha, _⟩ := vectors A P.pair α (P.roots α).val (P.roots α).property
  obtain ⟨b, hb, _⟩ := vectors A Q.pair (h.roots α) (Q.roots (h.roots α)).val
    (Q.roots (h.roots α)).property
  obtain ⟨w, hw, hwn⟩ := α.property.2
  let x := if s : IsSimple P.pair α then P.pin ⟨α, s⟩ else a.symm ⟨w, hw, hwn⟩
  let u := a x
  let z : Pinning.RootVector Q.pair.T (h.roots α).val :=
    ⟨e u.val, hroot α u.val u.property.1, fun hz => u.property.2 (e.injective (hz.trans hzero.symm))⟩
  let y := b.symm z
  have hy : b y = z := b.apply_symm_apply z
  refine ⟨x, y, u.val, ha x, ?_, fun s => ?_⟩
  · exact (congrArg (fun t : Pinning.RootVector Q.pair.T (h.roots α).val => t.val.toMul.val)
      hy.symm).trans (hb y)
  · have hx : x = P.pin ⟨α, s⟩ := dite_eq_left s
    refine ⟨hx, b.injective ?_⟩
    rw [hy]
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    have hP : u.val.toMul.val = rootPoint ((P.pin ⟨α, s⟩).val.hom ≫ (P.roots α).val.inclusion)
        (CommAlgCat.of k (DualNumber k)) DualNumber.eps := by rw [← hx]; exact ha x
    exact (hpin ⟨α, s⟩ u.val hP).trans (hb _).symm

/-- Assemble the lift from the projections of the algebraic graph and the
specified maps on the torus, Borel and simple root coordinates. -/
private theorem lifts_of_graph_projections [CharZero k] {A : AdditiveLine k}
    (P Q : PinnedGroup A) (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair)
    (h : LatticeMap D E) (M : AffineAlgebraicGroup k)
    (p₁ : M.val ⟶ P.pair.G.val) (p₂ : M.val ⟶ Q.pair.G.val)
    [IsIso p₁] [IsDominant p₂.hom.hom.left]
    (hd : Function.Injective (mapPointKernel p₂))
    (t : P.pair.T.group ⟶ Q.pair.T.group) (iT : P.pair.T.group ⟶ M.val)
    (ht₁ : iT ≫ p₁ = P.pair.T.inclusion) (ht₂ : iT ≫ p₂ = t ≫ Q.pair.T.inclusion)
    (hts : Surjective t.hom.hom.left)
    (hχ : ∀ χ : Character Q.pair.T.group, t ≫ χ = h.characters χ)
    (hti : Function.Bijective h.characters → IsIso t)
    (b : P.pair.B.group ⟶ Q.pair.B.group) (iB : P.pair.B.group ⟶ M.val)
    (hb₁ : iB ≫ p₁ = P.pair.B.inclusion) (hb₂ : iB ≫ p₂ = b ≫ Q.pair.B.inclusion)
    (hbs : Surjective b.hom.hom.left)
    (hpin : ∀ α : Pinning.SimpleRoot P.pair, ∃ i : A.group ⟶ M.val,
      i ≫ p₁ = (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion ∧
      i ≫ p₂ = (Q.pin (h.simpleRoot α)).val.hom ≫ (Q.roots (h.roots α.val)).val.inclusion) :
    Lifts P Q D E h := by
  let f := inv p₁ ≫ p₂
  have hfac {X : GroupScheme k} (i : X ⟶ M.val) : i ≫ p₁ ≫ f = i ≫ p₂ := by
    dsimp only [f]
    rw [IsIso.hom_inv_id_assoc]
  have ht : P.pair.T.inclusion ≫ f = t ≫ Q.pair.T.inclusion := by
    rw [← ht₁, Category.assoc, hfac, ht₂]
  have hb : P.pair.B.inclusion ≫ f = b ≫ Q.pair.B.inclusion := by
    rw [← hb₁, Category.assoc, hfac, hb₂]
  have hp (α : Pinning.SimpleRoot P.pair) :
      (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion ≫ f =
        (Q.pin (h.simpleRoot α)).val.hom ≫ (Q.roots (h.roots α.val)).val.inclusion := by
    obtain ⟨i, hi₁, hi₂⟩ := hpin α
    rw [← Category.assoc, ← hi₁, Category.assoc, hfac, hi₂]
  have hdom : IsDominant f.hom.hom.left := by
    have h₁ : IsIso (scheme.map (inv p₁)) := scheme.map_isIso (inv p₁)
    have h₂ : IsDominant (scheme.map p₂) := inferInstanceAs (IsDominant p₂.hom.hom.left)
    change IsDominant (scheme.map (inv p₁ ≫ p₂))
    rw [Functor.map_comp]
    infer_instance
  have hf : Function.Injective (mapPointKernel f) := by
    intro x y hxy
    have hp₁ : IsIso (underlying.map (inv p₁)) := underlying.map_isIso (inv p₁)
    have hmono : Mono (inv p₁).hom.hom := inferInstanceAs (Mono (underlying.map (inv p₁)))
    have hxy' : mapPointKernel p₂ (mapPointKernel (inv p₁) x) =
        mapPointKernel p₂ (mapPointKernel (inv p₁) y) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (x.toMul.val ≫ (inv p₁).hom.hom) ≫ p₂.hom.hom =
        (y.toMul.val ≫ (inv p₁).hom.hom) ≫ p₂.hom.hom
      simp only [Category.assoc]
      exact congrArg (fun z : Lie k Q.pair.G.val => z.toMul.val) hxy
    apply Additive.toMul.injective
    apply Subtype.ext
    apply (cancel_mono (inv p₁).hom.hom).mp
    exact congrArg (fun z : Lie k M.val => z.toMul.val) (hd hxy')
  have := P.pair.reductive.2.1
  have hf' := centralIsogeny_of_dominant_of_injective_differential P.pair.G Q.pair.G f hf
  refine ⟨f, t, b, hf', hts, hbs, ht, hb, hχ, hp, fun hbij => ?_⟩
  have := hti hbij
  exact isIso_of_centralIsogeny_of_torusIso P.pair Q.pair f t hf' ht


section GraphGroup

open Specs.RationalRealization (WordGeneratedGroup)
open Specs.FiniteWordClosure (power)
open Specs.AdjointRepresentation (dualMap)

private theorem affine_tensor (X Y : SchemeOver k) [IsAffine X.left] [IsAffine Y.left] :
    IsAffine (X ⊗ Y).left :=
  IsAffine.of_isPullback (isPullback_tensor_structure X Y)

private theorem affine_power (X : SchemeOver k) [IsAffine X.left] (n : ℕ) :
    IsAffine (power X n).left := by
  induction n with
  | zero => exact inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  | succ n ih => exact affine_tensor X (power X n)

private def productGroup (G H : AffineAlgebraicGroup k) : AffineAlgebraicGroup k := by
  have hG := G.property
  have hH := H.property
  let X := G.val.X
  let Y := H.val.X
  have : IsAffine X.left := hG.1
  have : IsAffine Y.left := hH.1
  have : LocallyOfFiniteType X.hom := hG.2.1
  have : QuasiCompact X.hom := hG.2.2
  have : LocallyOfFiniteType Y.hom := hH.2.1
  have : QuasiCompact Y.hom := hH.2.2
  have hp := isPullback_tensor_structure X Y
  have : LocallyOfFiniteType (fst X Y).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp.flip inferInstance
  have : QuasiCompact (fst X Y).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance
  refine ⟨G.val ⊗ H.val, affine_tensor X Y, ?_, ?_⟩
  · change LocallyOfFiniteType (X ⊗ Y).hom
    rw [← Over.w (fst X Y)]
    infer_instance
  · change QuasiCompact (X ⊗ Y).hom
    rw [← Over.w (fst X Y)]
    infer_instance

/-- Affine schemes detect equality of points after an injective map of the test algebras. -/
private theorem mapPoints_injective_of_affine {X : SchemeOver k} [IsAffine X.left]
    {R S : TestAlgebra k} (a : R ⟶ S) (ha : Function.Injective a.hom) :
    Function.Injective (mapPoints a : Points X R → Points X S) := by
  obtain ⟨T, ⟨e⟩⟩ := essImage_algSpec.mpr (show IsAffine X.left from inferInstance)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  intro x y h
  let x' := ff.preimage (x ≫ e.inv)
  let y' := ff.preimage (y ≫ e.inv)
  have hx : (testSpec k).map x' = x ≫ e.inv := ff.map_preimage _
  have hy : (testSpec k).map y' = y ≫ e.inv := ff.map_preimage _
  have he : (testSpec k).map (a.op ≫ x') = (testSpec k).map (a.op ≫ y') := by
    rw [Functor.map_comp, Functor.map_comp, hx, hy, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun t => t ≫ e.inv) h
  have he' := Quiver.Hom.op_inj (ff.map_injective he)
  have hh : x' = y' := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    apply ha
    exact ConcreteCategory.congr_hom he' z
  apply (cancel_mono e.inv).mp
  rw [← hx, ← hy, hh]

private theorem dualMap_injective {R S : TestAlgebra k} {a : R ⟶ S}
    (ha : Function.Injective a.hom) : Function.Injective (dualMap a).hom := by
  intro x y h
  apply TrivSqZeroExt.ext
  · apply ha
    exact congrArg TrivSqZeroExt.fst h
  · apply ha
    exact congrArg TrivSqZeroExt.snd h

/-- Lift a group morphism along a closed subgroup using a scheme factorization. -/
private theorem lift_hom_of_closed_factor {G H : GroupScheme k} (N : ClosedSubgroup G)
    (f : H ⟶ G) (a : H.X ⟶ N.group.X) (ha : a ≫ N.inclusion.hom.hom = f.hom.hom) :
    ∃ b : H ⟶ N.group, b ≫ N.inclusion = f := by
  have := N.isClosedImmersion
  have := isMonHom_of_comp_closed a f N.inclusion ha
  exact ⟨Grp.homMk a, Grp.hom_ext _ _ ha⟩

/-- A closed subgroup containing a pointed family also contains any group
homomorphism obtained by restricting the family along a scheme morphism. -/
private theorem lift_hom_of_family {G H : GroupScheme k} (N : ClosedSubgroup G)
    {X : SchemeOver k} {g : X ⟶ G.X} (a : X ⟶ N.group.X)
    (ha : a ≫ N.inclusion.hom.hom = g)
    (f : H ⟶ G) (b : H.X ⟶ X) (hb : b ≫ g = f.hom.hom) :
    ∃ j : H ⟶ N.group, j ≫ N.inclusion = f :=
  lift_hom_of_closed_factor N f (b ≫ a) (by rw [Category.assoc, ha, hb])

private theorem finite_type_power (X : SchemeOver k) [LocallyOfFiniteType X.hom] (n : ℕ) :
    LocallyOfFiniteType (power X n).hom := by
  induction n with
  | zero => exact inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))))
  | succ n ih =>
    haveI : LocallyOfFiniteType (power X n).hom := ih
    have := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (isPullback_tensor_structure X (power X n))
      (show LocallyOfFiniteType X.hom from inferInstance)
    change LocallyOfFiniteType (X ⊗ power X n).hom
    rw [← Over.w (snd X (power X n))]
    infer_instance

private theorem affine_dominant_presentation {X Y : SchemeOver k}
    [IsAffine X.left] [IsAffine Y.left] [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] (w : X ⟶ Y) [IsSchemeTheoreticallyDominant w.left] :
    ∃ (A B : TestAlgebra k) (_ : IsDomain A) (_ : IsDomain B)
      (eX : affineSpec B ≅ X) (eY : affineSpec A ≅ Y) (f : A ⟶ B),
      Function.Injective f.hom ∧ f.hom.toRingHom.FiniteType ∧
      eX.hom ≫ w = (testSpec k).map f.op ≫ eY.hom := by
  obtain ⟨A₀, ⟨eY⟩⟩ := essImage_algSpec.mpr (show IsAffine Y.left from inferInstance)
  obtain ⟨B₀, ⟨eX⟩⟩ := essImage_algSpec.mpr (show IsAffine X.left from inferInstance)
  let A := A₀.unop
  let B := B₀.unop
  have : IsIso eX.inv.left := (Over.forget _).map_isIso eX.inv
  have : IsIso eY.inv.left := (Over.forget _).map_isIso eY.inv
  have hA := IsIntegral.of_isIso eY.inv.left
  have hB := IsIntegral.of_isIso eX.inv.left
  have iA : IsDomain A := (affine_isIntegral_iff (.of A)).mp hA
  have iB : IsDomain B := (affine_isIntegral_iff (.of B)).mp hB
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let z := eX.hom ≫ w ≫ eY.inv
  let f : A ⟶ B := (ff.preimage z).unop
  have hz : (testSpec k).map f.op = z := ff.map_preimage _
  have hfac : eX.hom ≫ w = (testSpec k).map f.op ≫ eY.hom := by
    rw [hz]
    simp [z]
  have : IsIso eX.hom.left := (Over.forget _).map_isIso eX.hom
  have hz' : Spec.map (CommRingCat.ofHom f.hom.toRingHom) =
      eX.hom.left ≫ w.left ≫ eY.inv.left := congrArg Over.Hom.left hz
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) :=
    hz'.symm ▸ inferInstance
  have hi : IsAffineHom (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) := inferInstance
  have hinj : Function.Injective (Spec.map (CommRingCat.ofHom f.hom.toRingHom)).appTop :=
    (Spec.map (CommRingCat.ofHom f.hom.toRingHom)).app_injective ⊤
  have hinj' : Function.Injective f.hom := by
    intro x y h
    have he := congrArg (fun j => j x) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom f.hom.toRingHom))
    have he' := congrArg (fun j => j y) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom f.hom.toRingHom))
    apply (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm.injective
    apply hinj
    exact he.symm.trans ((congrArg (Scheme.ΓSpecIso (.of B)).inv h).trans he')
  have hftX : LocallyOfFiniteType (affineSpec B).hom := by
    rw [← Over.w eX.hom]
    infer_instance
  have hm : LocallyOfFiniteType (((testSpec k).map f.op).left ≫ (affineSpec A).hom) :=
    (Over.w ((testSpec k).map f.op)).symm ▸ hftX
  have hft : LocallyOfFiniteType ((testSpec k).map f.op).left :=
    locallyOfFiniteType_of_comp _ (affineSpec A).hom
  exact ⟨A, B, iA, iB, eX, eY, f, hinj',
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft, hfac⟩

/-- A tangent over the ground field, viewed over a test algebra. -/
private def extendTangent {G : GroupScheme k} (R : TestAlgebra k) (v : Lie k G) :
    RelativeTangent G R :=
  ⟨mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val, by
    let a : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    have ha : dualMap a ≫ reduction R = reduction (CommAlgCat.of k k) ≫ a :=
      CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)
    change (testSpec k).map (reduction R).op ≫ (testSpec k).map (dualMap a).op ≫ v.toMul.val = 1
    rw [← Category.assoc, ← Functor.map_comp, ← op_comp, ha, op_comp, Functor.map_comp,
      Category.assoc]
    change (testSpec k).map a.op ≫ reduceTangentPoints G v.toMul.val = 1
    rw [v.toMul.property, MonObj.comp_one]⟩

/-- The dominant-word bound descends to injectivity of the ground-field
differential when projection is injective on the relative tangent constraint. -/
private theorem differential_injective_of_constraint {G H : GroupScheme k}
    (N : ClosedSubgroup G) [IsAffine N.group.X.left] (R : TestAlgebra k) [Nontrivial R]
    (q : G ⟶ H) (S : Subgroup (GroupPoints G (CommAlgCat.of k (DualNumber R))))
    (hS : ∀ v : RelativeTangent N.group R, v.toMul.val ≫ N.inclusion.hom.hom ∈ S)
    (hq : ∀ a ∈ S, ∀ b ∈ S, a ≫ q.hom.hom = b ≫ q.hom.hom → a = b) :
    Function.Injective (mapPointKernel (N.inclusion ≫ q)) := by
  intro v w h
  let a := (extendTangent R v).toMul.val ≫ N.inclusion.hom.hom
  let b := (extendTangent R w).toMul.val ≫ N.inclusion.hom.hom
  have hab : a ≫ q.hom.hom = b ≫ q.hom.hom := by
    dsimp only [a, b, extendTangent]
    simp only [mapPoints, Category.assoc]
    exact congrArg (fun z : Lie k H =>
      mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) z.toMul.val) h
  have he : a = b := hq a (hS (extendTangent R v)) b (hS (extendTangent R w)) hab
  have hmono : Mono N.inclusion.hom.hom := mono_over _ N.isClosedImmersion
  have he' := (cancel_mono N.inclusion.hom.hom).mp he
  apply Additive.toMul.injective
  apply Subtype.ext
  exact mapPoints_injective_of_affine _ (dualMap_injective (algebraMap k R).injective) he'

/-- The relative tangents allowed by a paired multiplication family. -/
private def PairedTangentConstraint {G H : GroupScheme k} {X : SchemeOver k}
    (g₁ : X ⟶ G.X) (g₂ : X ⟶ H.X) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
      let R := CommAlgCat.of k K
      let J := G ⊗ H
      let r := reducePoints J R
      let c := constantPoints J R
      let f : X ⟶ J.X := lift g₁ g₂
      ∃ S : Subgroup (GroupPoints J (CommAlgCat.of k (DualNumber R))),
        (∀ a : Points X (CommAlgCat.of k (DualNumber R)), displacement r c (a ≫ f) ∈ S) ∧
        (∀ a : Points X (CommAlgCat.of k (DualNumber R)),
          c (r (a ≫ f)) ∈ Subgroup.normalizer (S : Set _)) ∧
        (∀ a ∈ S, ∀ b ∈ S, a ≫ fst G.X H.X = b ≫ fst G.X H.X → a = b) ∧
        (∀ a ∈ S, ∀ b ∈ S, a ≫ snd G.X H.X = b ≫ snd G.X H.X → a = b)

/-- A pointed paired family with injective projection on its tangent
constraint generates an algebraic subgroup whose first projection is invertible. -/
private theorem graph_of_pointed_family [CharZero k] (word : WordGeneratedGroup.{u})
    (generic : DominantGenericLift.{u}) (G H : AffineAlgebraicGroup k)
    [IsIntegral G.val.X.left]
    {X : SchemeOver k} [IsAffine X.left] [LocallyOfFiniteType X.hom]
    (x₀ : 𝟙_ (SchemeOver k) ⟶ X) (g₁ : X ⟶ G.val.X) (g₂ : X ⟶ H.val.X)
    (hg₁ : x₀ ≫ g₁ = 1) (hg₂ : x₀ ≫ g₂ = 1)
    [IsOpenImmersion g₁.left] [IsDominant g₂.left]
    (hpow : ∀ n, IsIntegral (power X n).left)
    (h : PairedTangentConstraint g₁ g₂) :
    ∃ (N : ClosedSubgroup (G.val ⊗ H.val)) (a : X ⟶ N.group.X),
      a ≫ N.inclusion.hom.hom = (lift g₁ g₂ : X ⟶ (G.val ⊗ H.val).X) ∧
      IsIso (N.inclusion ≫ fst G.val H.val) ∧
      IsDominant (N.inclusion ≫ snd G.val H.val).hom.hom.left ∧
      Function.Injective (mapPointKernel (N.inclusion ≫ snd G.val H.val)) := by
  let J := productGroup G H
  let f : X ⟶ J.val.X := lift g₁ g₂
  have hf₀ : x₀ ≫ f = 1 := by
    apply CartesianMonoidalCategory.hom_ext
    · change (x₀ ≫ f) ≫ (fst G.val H.val).hom.hom = _
      rw [Category.assoc, show f ≫ (fst G.val H.val).hom.hom = g₁ from lift_fst _ _,
        hg₁, MonObj.one_comp]
    · change (x₀ ≫ f) ≫ (snd G.val H.val).hom.hom = _
      rw [Category.assoc, show f ≫ (snd G.val H.val).hom.hom = g₂ from lift_snd _ _,
        hg₂, MonObj.one_comp]
  obtain ⟨N, n, w, _, hN, hdom, _, ⟨a, ha⟩, _, hw⟩ := word J X f x₀ inferInstance hf₀ hpow
  let M := Unipotent.closedSubgroupAlgebraicGroup (G := J) N
  have : IsIntegral N.group.X.left := hN
  have : IsIntegral M.val.X.left := hN
  have : IsAffine N.group.X.left := M.property.1
  have : IsAffine (wordDomain X n).left := affine_power X _
  have : IsIntegral (wordDomain X n).left := hpow _
  have : LocallyOfFiniteType (wordDomain X n).hom := finite_type_power X _
  obtain ⟨A, B, iA, iB, eW, eN, g, hg, hft, he⟩ := affine_dominant_presentation w
  let R := genericTestAlgebra B
  haveI : Nontrivial R := inferInstanceAs (Nontrivial (FractionRing B))
  obtain ⟨S, hs, hn, h₁, h₂⟩ := h (FractionRing B)
  have hS := relativeTangent_mem_of_dominant_word generic N f n w hw eW eN g hg hft he S hs hn
  let p₁ := N.inclusion ≫ fst G.val H.val
  let p₂ := N.inclusion ≫ snd G.val H.val
  have hd₁ : Function.Injective (mapPointKernel p₁) :=
    differential_injective_of_constraint N R (fst G.val H.val) S hS h₁
  have hd₂ : Function.Injective (mapPointKernel p₂) :=
    differential_injective_of_constraint N R (snd G.val H.val) S hS h₂
  have h₁' : a ≫ p₁.hom.hom = g₁ := by
    change a ≫ N.inclusion.hom.hom ≫ fst G.val.X H.val.X = g₁
    rw [← Category.assoc, ha, lift_fst]
  have h₂' : a ≫ p₂.hom.hom = g₂ := by
    change a ≫ N.inclusion.hom.hom ≫ snd G.val.X H.val.X = g₂
    rw [← Category.assoc, ha, lift_snd]
  have ha₀ : x₀ ≫ a = 1 := by
    have : Mono N.inclusion.hom.hom := mono_over _ N.isClosedImmersion
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [Category.assoc, ha, hf₀, MonObj.one_comp]
  have hp₁ : IsIso p₁ := isIso_of_open_chart_of_injective_differential M G p₁ hd₁ a x₀
    ha₀ (h₁'.symm ▸ inferInstanceAs (IsOpenImmersion g₁.left))
  have h₂'' : a.left ≫ p₂.hom.hom.left = g₂.left := congrArg Over.Hom.left h₂'
  have : IsDominant (a.left ≫ p₂.hom.hom.left) := h₂''.symm ▸ inferInstance
  exact ⟨N, a, ha, hp₁, IsDominant.of_comp a.left _, hd₂⟩

end GraphGroup


/-- A pair of cells with the relative tangent constraint determines a central
isogeny between the two ambient groups. -/
private theorem centralIsogeny_of_paired_cells [CharZero k]
    (word : WordGeneratedGroup.{u}) (generic : DominantGenericLift.{u})
    (G H : AffineAlgebraicGroup k) [GeometricallyConnected G.val.X.hom]
    [IsIntegral G.val.X.left]
    {X : SchemeOver k} [IsAffine X.left] [LocallyOfFiniteType X.hom]
    (x₀ : 𝟙_ (SchemeOver k) ⟶ X) (g₁ : X ⟶ G.val.X) (g₂ : X ⟶ H.val.X)
    (hg₁ : x₀ ≫ g₁ = 1) (hg₂ : x₀ ≫ g₂ = 1)
    [IsOpenImmersion g₁.left] [IsDominant g₂.left]
    (hpow : ∀ n, IsIntegral (Specs.FiniteWordClosure.power X n).left)
    (h : PairedTangentConstraint g₁ g₂) :
    ∃ f : G.val ⟶ H.val, IsCentralIsogeny f ∧ g₁ ≫ f.hom.hom = g₂ := by
  obtain ⟨N, a, ha, hp₁, hp₂, hd₂⟩ := graph_of_pointed_family word generic G H x₀ g₁ g₂
    hg₁ hg₂ hpow h
  let p₁ := N.inclusion ≫ fst G.val H.val
  let p₂ := N.inclusion ≫ snd G.val H.val
  haveI : IsIso p₁ := hp₁
  haveI : IsDominant p₂.hom.hom.left := hp₂
  let f := inv p₁ ≫ p₂
  have h₁ : a ≫ p₁.hom.hom = g₁ := by
    change a ≫ N.inclusion.hom.hom ≫ fst G.val.X H.val.X = g₁
    rw [← Category.assoc, ha, lift_fst]
  have h₂ : a ≫ p₂.hom.hom = g₂ := by
    change a ≫ N.inclusion.hom.hom ≫ snd G.val.X H.val.X = g₂
    rw [← Category.assoc, ha, lift_snd]
  have hcell : g₁ ≫ f.hom.hom = g₂ := by
    have hh : p₁ ≫ f = p₂ := IsIso.hom_inv_id_assoc p₁ p₂
    rw [← h₁, Category.assoc, ← Grp.comp_hom_hom, hh, h₂]
  have hdom : IsDominant f.hom.hom.left := by
    haveI : IsIso (scheme.map (inv p₁)) := scheme.map_isIso (inv p₁)
    haveI : IsDominant (scheme.map p₂) := hp₂
    change IsDominant (scheme.map (inv p₁ ≫ p₂))
    rw [Functor.map_comp]
    infer_instance
  have hd : Function.Injective (mapPointKernel f) := by
    intro v w hvw
    have hh : mapPointKernel p₂ (mapPointKernel (inv p₁) v) =
        mapPointKernel p₂ (mapPointKernel (inv p₁) w) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (v.toMul.val ≫ (inv p₁).hom.hom) ≫ p₂.hom.hom =
        (w.toMul.val ≫ (inv p₁).hom.hom) ≫ p₂.hom.hom
      have hh := congrArg (fun z : Lie k H.val => z.toMul.val) hvw
      change v.toMul.val ≫ (inv p₁).hom.hom ≫ p₂.hom.hom =
        w.toMul.val ≫ (inv p₁).hom.hom ≫ p₂.hom.hom at hh
      simpa only [Category.assoc] using hh
    have he := congrArg (fun z : Lie k N.group => z.toMul.val) (hd₂ hh)
    haveI : IsIso (underlying.map (inv p₁)) := underlying.map_isIso (inv p₁)
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (cancel_mono (underlying.map (inv p₁))).mp he
  exact ⟨f, centralIsogeny_of_dominant_of_injective_differential G H f hd, hcell⟩


section OpenPowers

open Specs.FiniteWordClosure (power)
open private tensorHom_property from LinearAlgebraicGroups.Affine.Components
open private geometricallyIrreducible_of_connected smooth_geometricallyIrreducible_tensor
  geometry_of_smooth_geometricallyIrreducible from LinearAlgebraicGroups.Solvable.WordDomainGeometry

private def powerMap {X Y : SchemeOver k} (f : X ⟶ Y) (n : ℕ) :
    power X n ⟶ power Y n :=
  match n with
  | 0 => 𝟙 _
  | m + 1 => f ⊗ₘ powerMap f m

private theorem powerMap_open {X Y : SchemeOver k} (f : X ⟶ Y) [IsOpenImmersion f.left]
    (n : ℕ) : IsOpenImmersion (powerMap f n).left := by
  induction n with
  | zero => exact inferInstanceAs (IsOpenImmersion (𝟙 (Spec (CommRingCat.of k))))
  | succ n ih =>
    exact tensorHom_property f (powerMap f n) @IsOpenImmersion inferInstance ih

private def powerPoint {X : SchemeOver k} (x : 𝟙_ (SchemeOver k) ⟶ X) (n : ℕ) :
    𝟙_ (SchemeOver k) ⟶ power X n :=
  match n with
  | 0 => 𝟙 _
  | m + 1 => lift x (powerPoint x m)

private theorem smooth_irreducible_power {Y : SchemeOver k} [Smooth Y.hom]
    [GeometricallyIrreducible Y.hom] (n : ℕ) :
    Smooth (power Y n).hom ∧ GeometricallyIrreducible (power Y n).hom := by
  induction n with
  | zero =>
    change Smooth (𝟙 (Spec (CommRingCat.of k))) ∧ GeometricallyIrreducible (𝟙 (Spec (CommRingCat.of k)))
    refine ⟨inferInstance, ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩⟩
    intro K _ j
    exact (pullback.snd (𝟙 _) j).homeomorph.irreducibleSpace_iff.mpr inferInstance
  | succ n ih =>
    have := ih.1
    have := ih.2
    exact smooth_geometricallyIrreducible_tensor Y (power Y n)

private theorem integral_power_of_pointed_open {X Y : SchemeOver k} [Smooth Y.hom]
    [GeometricallyIrreducible Y.hom] (f : X ⟶ Y) [IsOpenImmersion f.left]
    (x : 𝟙_ (SchemeOver k) ⟶ X) (n : ℕ) : IsIntegral (power X n).left := by
  obtain ⟨hsm, hirr⟩ := smooth_irreducible_power (Y := Y) n
  have : IsIntegral (power Y n).left :=
    (geometry_of_smooth_geometricallyIrreducible (power Y n)).2.2
  have : IsOpenImmersion (powerMap f n).left := powerMap_open f n
  have : Nonempty (power X n).left := ⟨(powerPoint x n).left (IsLocalRing.closedPoint k)⟩
  exact isIntegral_of_isOpenImmersion (powerMap f n).left

end OpenPowers

section BasisChange

open scoped Matrix
open Specs.AdjointRepresentation (TangentCoordinates RelativeTangent dualMap conjugate GroupPoints)
open Specs.StandardGroups (generalLinearPoints)
open InfinitesimalCommutator (matrixDifferential)
open private conjugationTransformation conjugationMatrix_spec differential_formula
  from LinearAlgebraicGroups.Affine.AdjointRepresentation


/-- Express the same relative tangent family in an arbitrary finite basis. -/
private def changeTangentBasis {G : GroupScheme k} {I J : Type u}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [AddCommGroup (Lie k G)] [Module k (Lie k G)]
    {b : Module.Basis I k (Lie k G)} (T : TangentCoordinates G I b)
    (d : Module.Basis J k (Lie k G)) : TangentCoordinates G J d := by
  let C (R : TestAlgebra k) := (b.toMatrix d).map (algebraMap k R)
  let D (R : TestAlgebra k) := (d.toMatrix b).map (algebraMap k R)
  have hcomp₁ (R : TestAlgebra k) : D R * C R = 1 := by
    dsimp only [D, C]
    rw [← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip]
    exact map_one ((algebraMap k R).mapMatrix : Matrix J J k →+* Matrix J J R)
  have hcomp₂ (R : TestAlgebra k) : C R * D R = 1 := by
    dsimp only [D, C]
    rw [← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip]
    exact map_one ((algebraMap k R).mapMatrix : Matrix I I k →+* Matrix I I R)
  let E (R : TestAlgebra k) : (J → R) ≃+ (I → R) :=
    { toFun := (C R).mulVec
      invFun := (D R).mulVec
      left_inv := fun _ => by
        rw [Matrix.mulVec_mulVec, hcomp₁, Matrix.one_mulVec]
      right_inv := fun _ => by
        rw [Matrix.mulVec_mulVec, hcomp₂, Matrix.one_mulVec]
      map_add' := fun x y => Matrix.mulVec_add _ _ _ }
  refine ⟨fun R => (E R).trans (T.equiv R), ?_, ?_, ?_⟩
  · intro R r a
    change (T.equiv R (C R *ᵥ (r • a))).toMul.val =
      mapPoints (AdjointRepresentation.scale R r) (T.equiv R (C R *ᵥ a)).toMul.val
    rw [Matrix.mulVec_smul, T.smul]
  · intro R S e a
    change (T.equiv S (C S *ᵥ (fun i => e.hom (a i)))).toMul.val =
      mapPoints (dualMap e) (T.equiv R (C R *ᵥ a)).toMul.val
    rw [← T.naturality]
    apply congrArg (fun w => (T.equiv S w).toMul.val)
    have hC : (C R).map e.hom = C S := by
      ext i j
      exact e.hom.commutes (b.toMatrix d i j)
    rw [← hC]
    funext i
    exact (RingHom.map_mulVec e.hom.toRingHom (C R) a i).symm
  · intro z
    change (T.equiv (CommAlgCat.of k k) (C (CommAlgCat.of k k) *ᵥ d.equivFun z)).toMul.val = _
    have he : C (CommAlgCat.of k k) = b.toMatrix d := by ext i j; rfl
    rw [he]
    change (T.equiv (CommAlgCat.of k k) (b.toMatrix d *ᵥ d.repr z)).toMul.val = _
    rw [Module.Basis.toMatrix_mulVec_repr]
    exact T.at_base z

private theorem tangentCoordinatesOfBasis (G : AffineAlgebraicGroup k)
    (s : IdentityLieStructure G.val) {I : Type u} [Fintype I] [DecidableEq I] :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ b : Module.Basis I k (Lie k G.val), Nonempty (TangentCoordinates G.val I b) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro b
  obtain ⟨n, d, ⟨T⟩⟩ := tangent_coordinates G s
  exact ⟨changeTangentBasis T b⟩

/-- The adjoint representation written in any prescribed tangent basis. -/
private theorem adjointOfCoordinates (G : AffineAlgebraicGroup k)
    (s : IdentityLieStructure G.val) {I : Type u} [Fintype I] [DecidableEq I] :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ {b : Module.Basis I k (Lie k G.val)} (T : TangentCoordinates G.val I b),
    ∃ (L : AffineAlgebraicGroup k)
      (l : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k I)
      (Ad : G.val ⟶ L.val),
      (∀ (R : TestAlgebra k) (g : GroupPoints G.val R) (v : I → R),
        let M := (l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R g)
        (T.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (T.equiv R v)) ∧
      (∀ (x y : Lie k G.val), matrixDifferential Ad l x *ᵥ b.equivFun y = b.equivFun ⁅x, y⁆) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro b T
  let L := LinearAlgebraicGroups.StandardGroups.generalLinearGroup k I
  let l := LinearAlgebraicGroups.StandardGroups.generalLinearGroupPointsIso k I
  let a := conjugationTransformation T
  let E := groupHomEquiv G.val L.val G.property.1
  let Ad := E.symm (a ≫ l.inv)
  have ha : (groupPointsFunctor k).map Ad ≫ l.hom = a := by
    have he : (groupPointsFunctor k).map Ad = a ≫ l.inv := E.apply_symm_apply (a ≫ l.inv)
    rw [he, Category.assoc, l.inv_hom_id, Category.comp_id]
  have hAd (R : TestAlgebra k) (g : GroupPoints G.val R) (v : I → R) :
      let M := (l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R g)
      (T.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (T.equiv R v) := by
    have h := congrArg (fun q : (groupPointsFunctor k).obj G.val ⟶ generalLinearPoints k I =>
      (q.app R).hom g) ha
    change (l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R g) = _ at h
    dsimp only
    rw [h]
    exact conjugationMatrix_spec T g v
  exact ⟨L, l, Ad, hAd, differential_formula T l Ad hAd s.commutator_law⟩

end BasisChange


section RelativeCoordinates

open Specs.AdjointRepresentation (TangentCoordinates dualMap scale conjugate)
open private mapRelativeKernel
  from LinearAlgebraicGroups.Affine.AdjointRepresentation

variable {G H : GroupScheme k} {I J : Type u}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [AddCommGroup (Lie k G)] [Module k (Lie k G)]
  [AddCommGroup (Lie k H)] [Module k (Lie k H)]
  {b : Module.Basis I k (Lie k G)} {d : Module.Basis J k (Lie k H)}

private def relativeDifferential (T : TangentCoordinates G I b) (U : TangentCoordinates H J d)
    (f : G ⟶ H) (R : TestAlgebra k) : (I → R) →ₗ[R] J → R := by
  let φ := mapRelativeKernel ((groupPointsFunctor k).map f) R
  refine {
    toFun := fun a => (U.equiv R).symm (φ (T.equiv R a))
    map_add' := fun x y => by simp only [map_add]
    map_smul' := ?_ }
  intro r a
  simp only [RingHom.id_apply]
  apply (U.equiv R).injective
  rw [AddEquiv.apply_symm_apply]
  apply Subtype.ext
  change (T.equiv R (r • a)).toMul.val ≫ f.hom.hom =
    (U.equiv R (r • (U.equiv R).symm (φ (T.equiv R a)))).toMul.val
  rw [U.smul, AddEquiv.apply_symm_apply, T.smul]
  exact Category.assoc _ _ _

private theorem relativeDifferential_spec
    (T : TangentCoordinates G I b) (U : TangentCoordinates H J d)
    (f : G ⟶ H) (R : TestAlgebra k) (a : I → R) :
    (U.equiv R (relativeDifferential T U f R a)).toMul.val =
      (T.equiv R a).toMul.val ≫ f.hom.hom := by
  change (U.equiv R ((U.equiv R).symm
    (mapRelativeKernel ((groupPointsFunctor k).map f) R (T.equiv R a)))).toMul.val = _
  rw [AddEquiv.apply_symm_apply]
  rfl

private theorem relativeDifferential_natural
    (T : TangentCoordinates G I b) (U : TangentCoordinates H J d)
    (f : G ⟶ H) {R S : TestAlgebra k} (e : R ⟶ S) (x : I → R) :
    relativeDifferential T U f S (fun i => e.hom (x i)) =
      fun j => e.hom (relativeDifferential T U f R x j) := by
  apply (U.equiv S).injective
  apply Subtype.ext
  change (U.equiv S (relativeDifferential T U f S (fun i => e.hom (x i)))).toMul.val =
    (U.equiv S (fun j => e.hom (relativeDifferential T U f R x j))).toMul.val
  rw [relativeDifferential_spec, U.naturality, T.naturality, relativeDifferential_spec]
  exact Category.assoc _ _ _

private theorem relativeDifferential_base
    (T : TangentCoordinates G I b) (U : TangentCoordinates H J d)
    (f : G ⟶ H) (x : Lie k G) :
    relativeDifferential T U f (CommAlgCat.of k k) (b.equivFun x) =
      d.equivFun (mapPointKernel f x) := by
  apply (U.equiv (CommAlgCat.of k k)).injective
  apply Subtype.ext
  change (U.equiv (CommAlgCat.of k k)
    (relativeDifferential T U f (CommAlgCat.of k k) (b.equivFun x))).toMul.val =
    (U.equiv (CommAlgCat.of k k) (d.equivFun (mapPointKernel f x))).toMul.val
  rw [relativeDifferential_spec, U.at_base, T.at_base]
  rfl

/-- Agreement of two differentials in their ground-field coordinates
implies agreement of the relative tangent maps over every test algebra. -/
private theorem relativeDifferential_eq_of_base
    {G' : GroupScheme k} [AddCommGroup (Lie k G')] [Module k (Lie k G')]
    {d' : Module.Basis J k (Lie k G')} (T : TangentCoordinates G I b)
    (U : TangentCoordinates H J d) (V : TangentCoordinates G' J d')
    (f : G ⟶ H) (g : G ⟶ G')
    (h : ∀ x, d.equivFun (mapPointKernel f x) = d'.equivFun (mapPointKernel g x))
    (R : TestAlgebra k) : relativeDifferential T U f R = relativeDifferential T V g R := by
  apply (Pi.basisFun R I).ext
  intro i
  let e : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  have he : (Pi.basisFun R I) i = fun j => e.hom (b.equivFun (b i) j) := by
    funext j
    simp only [Pi.basisFun_apply, Module.Basis.equivFun_self, Pi.single_apply]
    by_cases h : i = j
    · subst j; simp
    · simp [h, Ne.symm h]
  rw [he, relativeDifferential_natural, relativeDifferential_natural,
    relativeDifferential_base, relativeDifferential_base, h]

end RelativeCoordinates

section TangentGraph

open Specs.AdjointRepresentation (TangentCoordinates conjugate)
open Specs.StandardGroups (generalLinearPoints)

variable {G H : GroupScheme k} {I : Type u} [Fintype I] [DecidableEq I]
  [AddCommGroup (Lie k G)] [Module k (Lie k G)]
  [AddCommGroup (Lie k H)] [Module k (Lie k H)]
  {b : Module.Basis I k (Lie k G)} {d : Module.Basis I k (Lie k H)}

private def tangentGraph (T : TangentCoordinates G I b) (U : TangentCoordinates H I d)
    (R : TestAlgebra k) : Subgroup (GroupPoints (G ⊗ H) (CommAlgCat.of k (DualNumber R))) where
  carrier := {a | ∃ v, a ≫ fst G.X H.X = (T.equiv R v).toMul.val ∧
    a ≫ snd G.X H.X = (U.equiv R v).toMul.val}
  one_mem' := by
    refine ⟨0, ?_, ?_⟩
    · change (1 : GroupPoints (G ⊗ H) (CommAlgCat.of k (DualNumber R))) ≫
        (fst G H).hom.hom = _
      rw [MonObj.one_comp, map_zero]
      rfl
    · change (1 : GroupPoints (G ⊗ H) (CommAlgCat.of k (DualNumber R))) ≫
        (snd G H).hom.hom = _
      rw [MonObj.one_comp, map_zero]
      rfl
  mul_mem' := by
    rintro a b ⟨v, ha₁, ha₂⟩ ⟨w, hb₁, hb₂⟩
    refine ⟨v + w, ?_, ?_⟩
    · change (a * b) ≫ (fst G H).hom.hom = _
      rw [MonObj.mul_comp, Grp.fst_hom_hom, ha₁, hb₁, map_add]
      rfl
    · change (a * b) ≫ (snd G H).hom.hom = _
      rw [MonObj.mul_comp, Grp.snd_hom_hom, ha₂, hb₂, map_add]
      rfl
  inv_mem' := by
    rintro a ⟨v, h₁, h₂⟩
    refine ⟨-v, ?_, ?_⟩
    · change a⁻¹ ≫ (fst G H).hom.hom = _
      rw [GrpObj.inv_comp, Grp.fst_hom_hom, h₁, map_neg]
      rfl
    · change a⁻¹ ≫ (snd G H).hom.hom = _
      rw [GrpObj.inv_comp, Grp.snd_hom_hom, h₂, map_neg]
      rfl

private theorem tangentGraph_fst_injective
    (T : TangentCoordinates G I b) (U : TangentCoordinates H I d) (R : TestAlgebra k) :
    ∀ a ∈ tangentGraph T U R, ∀ b ∈ tangentGraph T U R,
      a ≫ fst G.X H.X = b ≫ fst G.X H.X → a = b := by
  rintro a ⟨v, ha₁, ha₂⟩ b ⟨w, hb₁, hb₂⟩ hab
  have he : v = w := (T.equiv R).injective (Subtype.ext (ha₁.symm.trans (hab.trans hb₁)))
  exact CartesianMonoidalCategory.hom_ext _ _ hab (ha₂.trans (he ▸ hb₂).symm)

private theorem tangentGraph_snd_injective
    (T : TangentCoordinates G I b) (U : TangentCoordinates H I d) (R : TestAlgebra k) :
    ∀ a ∈ tangentGraph T U R, ∀ b ∈ tangentGraph T U R,
      a ≫ snd G.X H.X = b ≫ snd G.X H.X → a = b := by
  rintro a ⟨v, ha₁, ha₂⟩ b ⟨w, hb₁, hb₂⟩ hab
  have he : v = w := (U.equiv R).injective (Subtype.ext (ha₂.symm.trans (hab.trans hb₂)))
  exact CartesianMonoidalCategory.hom_ext _ _ (ha₁.trans (he ▸ hb₁).symm) hab

/-- Paired constant points with the same adjoint action normalize the
relative tangent graph. -/
private theorem tangentGraph_normalizer
    (T : TangentCoordinates G I b) (U : TangentCoordinates H I d) (R : TestAlgebra k)
    (g : GroupPoints (G ⊗ H) R) (m : (I → R) ≃ (I → R))
    (h₁ : ∀ v, (T.equiv R (m v)).toMul.val = conjugate (g ≫ fst G.X H.X) (T.equiv R v))
    (h₂ : ∀ v, (U.equiv R (m v)).toMul.val = conjugate (g ≫ snd G.X H.X) (U.equiv R v)) :
    constantPoints (G ⊗ H) R g ∈ Subgroup.normalizer (tangentGraph T U R : Set _) := by
  let c := constantPoints (G ⊗ H) R g
  have hp₁ (z : GroupPoints (G ⊗ H) (CommAlgCat.of k (DualNumber R))) (v : I → R)
      (hz : z ≫ fst G.X H.X = (T.equiv R v).toMul.val) :
      (c * z * c⁻¹) ≫ fst G.X H.X = (T.equiv R (m v)).toMul.val := by
    change (c * z * c⁻¹) ≫ (fst G H).hom.hom = _
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, Grp.fst_hom_hom, hz, h₁]
    rfl
  have hp₂ (z : GroupPoints (G ⊗ H) (CommAlgCat.of k (DualNumber R))) (v : I → R)
      (hz : z ≫ snd G.X H.X = (U.equiv R v).toMul.val) :
      (c * z * c⁻¹) ≫ snd G.X H.X = (U.equiv R (m v)).toMul.val := by
    change (c * z * c⁻¹) ≫ (snd G H).hom.hom = _
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, Grp.snd_hom_hom, hz, h₂]
    rfl
  apply Subgroup.mem_normalizer_iff.mpr
  intro z
  constructor
  · rintro ⟨v, hv₁, hv₂⟩
    exact ⟨m v, hp₁ z v hv₁, hp₂ z v hv₂⟩
  · rintro ⟨w, hw₁, hw₂⟩
    obtain ⟨v, rfl⟩ := m.surjective w
    let p : GroupPoints (G ⊗ H) (CommAlgCat.of k (DualNumber R)) :=
      lift (T.equiv R v).toMul.val (U.equiv R v).toMul.val
    have hp : p ∈ tangentGraph T U R := ⟨v, lift_fst _ _, lift_snd _ _⟩
    have h : c * z * c⁻¹ = c * p * c⁻¹ := CartesianMonoidalCategory.hom_ext _ _
      (hw₁.trans (hp₁ p v (lift_fst _ _)).symm)
      (hw₂.trans (hp₂ p v (lift_snd _ _)).symm)
    have he : z = p := mul_left_cancel (mul_right_cancel h)
    exact he ▸ hp

end TangentGraph


section PairedMorphisms

open Specs.AdjointRepresentation (TangentCoordinates conjugate)

variable {G H C : GroupScheme k} {I J : Type u}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [AddCommGroup (Lie k G)] [Module k (Lie k G)]
  [AddCommGroup (Lie k H)] [Module k (Lie k H)]
  [AddCommGroup (Lie k C)] [Module k (Lie k C)]
  {b : Module.Basis I k (Lie k G)} {d : Module.Basis I k (Lie k H)}
  {a : Module.Basis J k (Lie k C)}

private theorem displacement_reduces_to_one {G : GroupScheme k} (R : TestAlgebra k)
    (x : GroupPoints G (CommAlgCat.of k (DualNumber R))) :
    reducePoints G R (displacement (reducePoints G R) (constantPoints G R) x) = 1 := by
  rw [displacement, map_mul, map_inv, reduce_constant, mul_inv_cancel]

/-- Paired homomorphisms with matching differentials and adjoint actions
have displacements in the relative tangent graph. -/
private theorem paired_morphism_mem
    (T : TangentCoordinates G I b) (U : TangentCoordinates H I d)
    (V : TangentCoordinates C J a) (p : C ⟶ G) (q : C ⟶ H)
    (hD : ∀ x, b.equivFun (mapPointKernel p x) = d.equivFun (mapPointKernel q x))
    (R : TestAlgebra k)
    (hAd : ∀ g : GroupPoints C R, ∃ m : (I → R) ≃ (I → R),
      (∀ v, (T.equiv R (m v)).toMul.val = conjugate (g ≫ p.hom.hom) (T.equiv R v)) ∧
      (∀ v, (U.equiv R (m v)).toMul.val = conjugate (g ≫ q.hom.hom) (U.equiv R v)))
    (x : GroupPoints C (CommAlgCat.of k (DualNumber R))) :
    (x ≫ (lift p q).hom.hom) ∈ displacementSubgroup (reducePoints (G ⊗ H) R)
      (constantPoints (G ⊗ H) R) (tangentGraph T U R) := by
  let F : C ⟶ G ⊗ H := lift p q
  have h₁ : F.hom.hom ≫ fst G.X H.X = p.hom.hom :=
    congrArg (fun f : C ⟶ G => f.hom.hom) (lift_fst p q)
  have h₂ : F.hom.hom ≫ snd G.X H.X = q.hom.hom :=
    congrArg (fun f : C ⟶ H => f.hom.hom) (lift_snd p q)
  constructor
  · change displacement (reducePoints (G ⊗ H) R) (constantPoints (G ⊗ H) R)
      (x ≫ F.hom.hom) ∈ tangentGraph T U R
    rw [displacement_factors F]
    let z : RelativeTangent C R :=
      ⟨displacement (reducePoints C R) (constantPoints C R) x, displacement_reduces_to_one R x⟩
    obtain ⟨v, hv⟩ := (V.equiv R).surjective z
    have hD' := relativeDifferential_eq_of_base V T U p q hD R
    refine ⟨relativeDifferential V T p R v, ?_, ?_⟩
    · change (z.toMul.val ≫ F.hom.hom) ≫ fst G.X H.X = _
      rw [Category.assoc, h₁, relativeDifferential_spec, hv]
    · change (z.toMul.val ≫ F.hom.hom) ≫ snd G.X H.X = _
      rw [Category.assoc, h₂, hD', relativeDifferential_spec, hv]
  · let g := reducePoints C R x
    obtain ⟨m, hm₁, hm₂⟩ := hAd g
    have h₁' : (g ≫ F.hom.hom) ≫ fst G.X H.X = g ≫ p.hom.hom := by rw [Category.assoc, h₁]
    have h₂' : (g ≫ F.hom.hom) ≫ snd G.X H.X = g ≫ q.hom.hom := by rw [Category.assoc, h₂]
    change constantPoints (G ⊗ H) R (g ≫ F.hom.hom) ∈ _
    apply tangentGraph_normalizer T U R (g ≫ F.hom.hom) m
    · simpa only [h₁'] using hm₁
    · simpa only [h₂'] using hm₂

end PairedMorphisms

section PolynomialActions

open Polynomial
open scoped Polynomial Matrix
open Specs.StandardGroups (generalLinearPoints)
open private rootPoint_natural rootPoint_eq rootPoint_zero additivePoints_add
  from LinearAlgebraicGroups.RootData.RootGroups


private theorem aeval_dual_number {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (a b : R) (p : k[X]) :
    (aeval (show DualNumber R from ⟨a, b⟩) p : DualNumber R) =
      (show DualNumber R from ⟨aeval a p, b * aeval a (derivative p)⟩) := by
  let f : k[X] →ₐ[k] DualNumber R :=
    { toFun := fun q => ⟨aeval a q, b * aeval a (derivative q)⟩
      map_zero' := by apply TrivSqZeroExt.ext <;> simp
      map_one' := by apply TrivSqZeroExt.ext <;> simp
      map_add' := fun x y => by
        apply TrivSqZeroExt.ext
        · exact map_add (aeval a) x y
        · change b * aeval a (derivative (x + y)) =
            b * aeval a (derivative x) + b * aeval a (derivative y)
          simp only [map_add, mul_add]
      map_mul' := fun x y => by
        apply TrivSqZeroExt.ext
        · exact map_mul (aeval a) x y
        · change b * aeval a (derivative (x * y)) =
            aeval a x * (b * aeval a (derivative y)) + (b * aeval a (derivative x)) * aeval a y
          simp only [derivative_mul, map_add, map_mul, mul_add, mul_assoc, mul_left_comm]
          exact add_comm _ _
      commutes' := fun x => by
        apply TrivSqZeroExt.ext
        · exact (aeval a).commutes x
        · change b * aeval a (derivative (C x)) = 0
          simp }
  have h : (aeval (⟨a, b⟩ : DualNumber R) : k[X] →ₐ[k] DualNumber R) = f := by
    apply Polynomial.algHom_ext
    rw [aeval_X]
    change (⟨a, b⟩ : DualNumber R) = ⟨aeval a X, b * aeval a (derivative X)⟩
    rw [derivative_X, aeval_X, map_one, mul_one]
  exact DFunLike.congr_fun h p

private theorem polynomial_additive_matrix_differential {k J : Type*} [Field k] [Fintype J]
    (P : Matrix J J k[X])
    (h : ∀ s t : DualNumber (k[X]),
      P.map (aeval (s + t)) = P.map (aeval s) * P.map (aeval t)) :
    P.map derivative = P * (P.map fun q => C (q.coeff 1)) := by
  have hX (p : k[X]) : aeval (X : k[X]) p = p := by
    have he : aeval (X : k[X]) = AlgHom.id k (k[X]) :=
      Polynomial.algHom_ext (by simp)
    exact DFunLike.congr_fun he p
  have h0 (p : k[X]) : aeval (0 : k[X]) p = C (p.coeff 0) :=
    (Polynomial.coeff_zero_eq_aeval_zero' p).symm
  have h1 (p : k[X]) : aeval (0 : k[X]) (derivative p) = C (p.coeff 1) := by
    rw [h0, coeff_derivative]
    simp
  apply Matrix.ext
  intro i j
  have he := congrArg (fun M : Matrix J J (DualNumber (k[X])) => (M i j).snd)
    (h ⟨X, 0⟩ ⟨0, 1⟩)
  have hxt : (⟨X, 0⟩ : DualNumber (k[X])) + ⟨0, 1⟩ = ⟨X, 1⟩ := by
    apply TrivSqZeroExt.ext <;> simp
  rw [hxt] at he
  simp only [Matrix.map_apply, Matrix.mul_apply, TrivSqZeroExt.snd_sum, aeval_dual_number,
    hX, h1, DualNumber.snd_mul] at he
  dsimp only [TrivSqZeroExt.fst, TrivSqZeroExt.snd] at he
  simpa only [Matrix.map_apply, Matrix.mul_apply, one_mul, zero_mul, mul_zero, add_zero] using he

/-- Polynomial matrix solutions of the same constant-coefficient differential
equation agree if they have the same constant term. -/
private theorem matrixPolynomial_eq_of_constant_coefficient_ode
    {k I J : Type*} [Field k] [CharZero k] [Fintype J]
    (P Q : Matrix I J k[X]) (D : Matrix J J k)
    (h0 : ∀ i j, (P i j).coeff 0 = (Q i j).coeff 0)
    (hP : P.map derivative = P * D.map C)
    (hQ : Q.map derivative = Q * D.map C) : P = Q := by
  have eqn (M : Matrix I J k[X]) (hM : M.map derivative = M * D.map C)
      (n : ℕ) (i : I) (j : J) :
      (M i j).coeff (n + 1) * (n + 1 : k) =
        ∑ l, (M i l).coeff n * D l j := by
    have h := congrArg (fun N : Matrix I J k[X] => (N i j).coeff n) hM
    simpa only [Matrix.map_apply, Matrix.mul_apply, Polynomial.coeff_derivative,
      Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C] using h
  have h (n : ℕ) (i : I) (j : J) : (P i j).coeff n = (Q i j).coeff n := by
    induction n generalizing i j with
    | zero => exact h0 i j
    | succ n ih =>
      apply mul_right_cancel₀ (show (n + 1 : k) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
      rw [eqn P hP n, eqn Q hQ n]
      simp only [ih]
  exact Matrix.ext fun i j => Polynomial.ext fun n => h n i j

/-- The coefficient recurrence for a polynomial matrix solving (P' = PD). -/
private theorem matrixPolynomial_coefficient_recurrence {k J : Type*} [Field k] [Fintype J]
    (P : Matrix J J k[X]) (D : Matrix J J k) (hP : P.map derivative = P * D.map C)
    (n : ℕ) :
    (n + 1 : k) • (P.map fun p => p.coeff (n+1)) = (P.map fun p => p.coeff n) * D := by
  ext i j
  have h := congrArg (fun N : Matrix J J k[X] => (N i j).coeff n) hP
  simpa only [Matrix.map_apply, Matrix.mul_apply, Polynomial.coeff_derivative,
    Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C, Matrix.smul_apply, smul_eq_mul,
    mul_comm (n+1 : k)] using h

/-- If the differential preserves a subspace and kills a class in the
quotient, the additive action fixes that class. -/
private theorem polynomial_matrix_displacement_mem {k J : Type*} [Field k] [CharZero k]
    [Fintype J] [DecidableEq J] (P : Matrix J J k[X]) (D : Matrix J J k)
    (h0 : P.map (fun p => p.coeff 0) = 1) (hP : P.map derivative = P * D.map C)
    (W : Submodule k (J → k)) (hD : ∀ w ∈ W, D *ᵥ w ∈ W) (v : J → k)
    (hv : D *ᵥ v ∈ W) (t : k) : (P.map (aeval t)) *ᵥ v - v ∈ W := by
  classical
  let A (n : ℕ) := P.map (fun p => p.coeff n)
  have hcoeff (n : ℕ) (w : J → k) (hw : D *ᵥ w ∈ W) : A (n+1) *ᵥ w ∈ W := by
    induction n generalizing w with
    | zero =>
      have h := congrArg (fun M : Matrix J J k => M *ᵥ w)
        (matrixPolynomial_coefficient_recurrence P D hP 0)
      rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.one_mulVec] at h
      have he : A 1 *ᵥ w = D *ᵥ w := by
        simpa only [Nat.cast_zero, zero_add, one_smul] using h
      rwa [he]
    | succ n ih =>
      have hn : (n.succ + 1 : k) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n.succ
      have h := congrArg (fun M : Matrix J J k => M *ᵥ w)
        (matrixPolynomial_coefficient_recurrence P D hP (n+1))
      rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec] at h
      have hw' : A (n+1) *ᵥ (D *ᵥ w) ∈ W := ih _ (hD _ hw)
      have hmem := W.smul_mem (n.succ + 1 : k)⁻¹ hw'
      change (n.succ + 1 : k)⁻¹ • ((P.map fun p => p.coeff (n+1)) *ᵥ (D *ᵥ w)) ∈ W at hmem
      rw [← h, smul_smul, inv_mul_cancel₀ hn, one_smul] at hmem
      exact hmem
  let N := (Finset.univ : Finset (J × J)).sup (fun p => (P p.1 p.2).natDegree) + 1
  have hN (i j : J) : (P i j).natDegree < N :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun p : J × J => (P p.1 p.2).natDegree)
      (Finset.mem_univ (i, j)))
  have hM : (P.map (aeval t)) = ∑ n ∈ Finset.range N, t ^ n • A n := by
    ext i j
    rw [Matrix.map_apply, Polynomial.aeval_eq_sum_range' (hN i j) t]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, A, smul_eq_mul]
    congr 1
    ext n
    exact mul_comm _ _
  have hpos : N = (N - 1) + 1 := by dsimp [N]
  have hzero : A 0 = 1 := h0
  rw [hM, Matrix.sum_mulVec, hpos, Finset.sum_range_succ', pow_zero, hzero,
    one_smul, Matrix.one_mulVec, add_sub_cancel_right]
  refine W.sum_mem fun n _ => ?_
  rw [Matrix.smul_mulVec]
  exact W.smul_mem _ (hcoeff n v hv)


/-- A natural additive matrix action in characteristic zero is determined
by its constant term and its differential at the origin. -/
private theorem additive_matrix_action_eq_of_differential
    {k J : Type u} [Field k] [CharZero k] [Fintype J]
    (p q : ∀ R : TestAlgebra k, R → Matrix J J R)
    (hp : ∀ {R S : TestAlgebra k} (f : R ⟶ S) (t : R),
      p S (f.hom t) = (p R t).map f.hom)
    (hq : ∀ {R S : TestAlgebra k} (f : R ⟶ S) (t : R),
      q S (f.hom t) = (q R t).map f.hom)
    (hpadd : ∀ (R : TestAlgebra k) (x y : R), p R (x + y) = p R x * p R y)
    (hqadd : ∀ (R : TestAlgebra k) (x y : R), q R (x + y) = q R x * q R y)
    (h0 : p (CommAlgCat.of k k) 0 = q (CommAlgCat.of k k) 0)
    (hd : ∀ i j, (p (CommAlgCat.of k (DualNumber k)) DualNumber.eps i j).snd =
      (q (CommAlgCat.of k (DualNumber k)) DualNumber.eps i j).snd) :
    ∀ (R : TestAlgebra k) (t : R), p R t = q R t := by
  let U := CommAlgCat.of k (Polynomial k)
  let P := p U Polynomial.X
  let Q := q U Polynomial.X
  have evalBase (R : TestAlgebra k) (t : R) (s : ∀ S : TestAlgebra k, S → Matrix J J S)
      (hs : ∀ {R' S : TestAlgebra k} (f : R' ⟶ S) (x : R'),
        s S (f.hom x) = (s R' x).map f.hom) :
      s R t = (s U Polynomial.X).map (Polynomial.aeval t) := by
    let f : U ⟶ R := ConcreteCategory.ofHom (Polynomial.aeval t)
    have hf : f.hom Polynomial.X = t := Polynomial.aeval_X t
    change s R t = (s U Polynomial.X).map f.hom
    simpa only [hf] using hs f (Polynomial.X : U)
  have hp' := fun R t => evalBase R t p hp
  have hq' := fun R t => evalBase R t q hq
  let V := CommAlgCat.of k (DualNumber U)
  have hDP : P.map derivative = P * (P.map fun x => C (x.coeff 1)) := by
    apply polynomial_additive_matrix_differential
    intro s t
    simpa only [hp' V, P] using hpadd V s t
  have hDQ : Q.map derivative = Q * (Q.map fun x => C (x.coeff 1)) := by
    apply polynomial_additive_matrix_differential
    intro s t
    simpa only [hq' V, Q] using hqadd V s t
  have hC (i j : J) : (P i j).coeff 0 = (Q i j).coeff 0 := by
    rw [coeff_zero_eq_aeval_zero, coeff_zero_eq_aeval_zero]
    exact congrArg (fun M => M i j)
      ((hp' (CommAlgCat.of k k) 0).symm.trans (h0.trans (hq' (CommAlgCat.of k k) 0)))
  have hD : P.map (fun x => x.coeff 1) = Q.map (fun x => x.coeff 1) := by
    apply Matrix.ext
    intro i j
    have he := hd i j
    rw [hp' (CommAlgCat.of k (DualNumber k)), hq' (CommAlgCat.of k (DualNumber k))] at he
    change ((aeval (DualNumber.eps : DualNumber k)) (P i j)).snd =
      ((aeval (DualNumber.eps : DualNumber k)) (Q i j)).snd at he
    have hEps : (DualNumber.eps : DualNumber k) = (show DualNumber k from ⟨0, 1⟩) := rfl
    rw [hEps, aeval_dual_number, aeval_dual_number] at he
    dsimp only [TrivSqZeroExt.snd] at he
    simpa only [one_mul, ← coeff_zero_eq_aeval_zero,
      coeff_derivative, Nat.cast_zero, zero_add, Nat.cast_one, mul_one, Matrix.map_apply] using he
  have hC' : P.map (fun x => C (x.coeff 1)) = Q.map (fun x => C (x.coeff 1)) :=
    congrArg (fun M : Matrix J J k => M.map C) hD
  have hDP' : P.map derivative = P * (Q.map (fun x => x.coeff 1)).map C :=
    hDP.trans (congrArg (fun M => P * M) hC')
  have he : P = Q := matrixPolynomial_eq_of_constant_coefficient_ode P Q
    (Q.map (fun x => x.coeff 1)) hC hDP' hDQ
  intro R t
  exact (hp' R t).trans ((congrArg (fun N => N.map (aeval t)) he).trans (hq' R t).symm)

private noncomputable def rootMatrix {k J : Type u} [Field k] [Fintype J] [DecidableEq J]
    {A : AdditiveLine k} {G : GroupScheme k} (x : A.group ⟶ G)
    (e : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    (R : TestAlgebra k) (t : R) : Matrix J J R :=
  ((e.hom.app R).hom (rootPoint x R t)).val

private theorem rootMatrix_natural {k J : Type u} [Field k] [Fintype J] [DecidableEq J]
    {A : AdditiveLine k} {G : GroupScheme k} (x : A.group ⟶ G)
    (e : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    {R S : TestAlgebra k} (b : R ⟶ S) (t : R) :
    rootMatrix x e S (b.hom t) = (rootMatrix x e R t).map b.hom := by
  have he := congrArg (fun f => f.hom (rootPoint x R t)) (e.hom.naturality b)
  change (e.hom.app S).hom (mapPoints b (rootPoint x R t)) =
    ((e.hom.app R).hom (rootPoint x R t)).map b.hom.toRingHom at he
  rw [rootPoint_natural] at he
  exact congrArg (fun m : Matrix.GeneralLinearGroup J S => m.val) he

private theorem rootMatrix_add {k J : Type u} [Field k] [Fintype J] [DecidableEq J]
    {A : AdditiveLine k} {G : GroupScheme k} (x : A.group ⟶ G)
    (e : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    (R : TestAlgebra k) (s t : R) :
    rootMatrix x e R (s + t) = rootMatrix x e R s * rootMatrix x e R t := by
  have h : rootPoint x R (s + t) = rootPoint x R s * rootPoint x R t := by
    rw [rootPoint_eq, rootPoint_eq, rootPoint_eq, additivePoints_add, MonObj.mul_comp]
  dsimp only [rootMatrix]
  rw [h, map_mul]
  rfl

/-- Root homomorphisms acting through a common matrix index have equal
actions on every test algebra when their tangent matrices agree. -/
private theorem rootMatrix_eq_of_differential {k J : Type u}
    [Field k] [CharZero k] [Fintype J] [DecidableEq J] {A : AdditiveLine k} {G H : GroupScheme k}
    (x : A.group ⟶ G) (y : A.group ⟶ H)
    (e : (groupPointsFunctor k).obj G ≅ generalLinearPoints k J)
    (f : (groupPointsFunctor k).obj H ≅ generalLinearPoints k J)
    (hd : ∀ i j, (rootMatrix x e (CommAlgCat.of k (DualNumber k)) DualNumber.eps i j).snd =
      (rootMatrix y f (CommAlgCat.of k (DualNumber k)) DualNumber.eps i j).snd)
    (R : TestAlgebra k) (t : R) : rootMatrix x e R t = rootMatrix y f R t := by
  apply additive_matrix_action_eq_of_differential (rootMatrix x e) (rootMatrix y f)
    (rootMatrix_natural x e) (rootMatrix_natural y f) (rootMatrix_add x e) (rootMatrix_add y f) _ hd
  simp only [rootMatrix, rootPoint_zero, map_one]

end PolynomialActions


/-- If the rank-one word reflects the proposed Cartan vector and its
additive factors are determined by the adjoint differentials, that vector
lies on the bracket line. -/
private theorem coroot_mem_bracket_line {k L : Type*} [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] (x y h : L) (u v : L → L)
    (hx : ⁅h, x⁆ = (2 : k) • x) (hy : ⁅h, y⁆ = (-2 : k) • y)
    (hxx : ⁅x, ⁅x, y⁆⁆ ∈ k ∙ x) (hyy : ⁅y, ⁅x, y⁆⁆ ∈ k ∙ y)
    (hu : ∀ (W : Submodule k L), (∀ z ∈ W, ⁅x, z⁆ ∈ W) →
      ∀ z, ⁅x, z⁆ ∈ W → u z - z ∈ W)
    (hv : ∀ (W : Submodule k L), (∀ z ∈ W, ⁅y, z⁆ ∈ W) →
      ∀ z, ⁅y, z⁆ ∈ W → v z - z ∈ W)
    (hreflect : u (v (u h)) = -h) :
    h ∈ k ∙ ⁅x, y⁆ := by
  let w := ⁅x, y⁆
  let W := k ∙ x ⊔ k ∙ y ⊔ k ∙ w
  have hlx : (k ∙ x) ≤ W := le_sup_left.trans le_sup_left
  have hly : (k ∙ y) ≤ W := le_sup_right.trans le_sup_left
  have hlw : (k ∙ w) ≤ W := le_sup_right
  have hxW : x ∈ W := hlx (Submodule.mem_span_singleton_self x)
  have hyW : y ∈ W := hly (Submodule.mem_span_singleton_self y)
  have hwW : w ∈ W := hlw (Submodule.mem_span_singleton_self w)
  have hneg : ⁅y, x⁆ = -w := (lie_skew y x).symm
  have hxW' : ∀ z ∈ W, ⁅x, z⁆ ∈ W := by
    have hle : W ≤ W.comap (LieAlgebra.ad k L x) := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Submodule.span_singleton_le_iff_mem]
      · change ⁅x, x⁆ ∈ W
        rw [lie_self]
        exact W.zero_mem
      · exact hwW
      · change ⁅x, w⁆ ∈ W
        exact hlx hxx
    exact fun _ hz => hle hz
  have hyW' : ∀ z ∈ W, ⁅y, z⁆ ∈ W := by
    have hle : W ≤ W.comap (LieAlgebra.ad k L y) := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Submodule.span_singleton_le_iff_mem]
      · change ⁅y, x⁆ ∈ W
        rw [hneg]
        exact W.neg_mem hwW
      · change ⁅y, y⁆ ∈ W
        rw [lie_self]
        exact W.zero_mem
      · change ⁅y, w⁆ ∈ W
        exact hly hyy
    exact fun _ hz => hle hz
  have hxh : ⁅x, h⁆ ∈ W := by
    rw [← lie_skew x h, hx]
    exact W.neg_mem (W.smul_mem _ hxW)
  have hyh : ⁅y, h⁆ ∈ W := by
    rw [← lie_skew y h, hy]
    exact W.neg_mem (W.smul_mem _ hyW)
  have h₁ : u h - h ∈ W := hu W hxW' h hxh
  have h₂ : v (u h) - u h ∈ W := hv W hyW' _ (by
    convert W.add_mem (hyW' _ h₁) hyh using 1
    rw [lie_sub, sub_add_cancel])
  have h₂' : v (u h) - h ∈ W := by
    convert W.add_mem h₂ h₁ using 1
    abel
  have h₃ : u (v (u h)) - v (u h) ∈ W := hu W hxW' _ (by
    convert W.add_mem (hxW' _ h₂') hxh using 1
    rw [lie_sub, sub_add_cancel])
  have hd : (-2 : k) • h ∈ W := by
    have h := W.add_mem h₃ h₂'
    rw [hreflect] at h
    convert h using 1
    rw [neg_smul, two_smul]
    abel
  have hW : h ∈ W := by
    have he := W.smul_mem ((-2 : k)⁻¹) hd
    rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (-2 : k) ≠ 0), one_smul] at he
  let C := LieAlgebra.ad k L h
  let p : L →ₗ[k] L := LinearMap.id - (4 : k)⁻¹ • (C ∘ₗ C)
  have hp_eq (z : L) : p z = z - (4 : k)⁻¹ • ⁅h, ⁅h, z⁆⁆ := rfl
  have hpx : p x = 0 := by
    rw [hp_eq, hx, lie_smul, hx, smul_smul, smul_smul]
    have h : (4 : k)⁻¹ * 2 * 2 = 1 := by norm_num
    rw [h, one_smul, sub_self]
  have hpy : p y = 0 := by
    rw [hp_eq, hy, lie_smul, hy, smul_smul, smul_smul]
    have h : (4 : k)⁻¹ * -2 * -2 = 1 := by norm_num
    rw [h, one_smul, sub_self]
  have hpw : p w = w := by
    have hw : ⁅h, w⁆ = 0 := by
      change ⁅h, ⁅x, y⁆⁆ = 0
      rw [leibniz_lie, hx, hy, smul_lie, lie_smul, neg_smul, add_neg_cancel]
    simp [hp_eq, hw]
  have hph : p h = h := by simp [hp_eq]
  have hl : W ≤ (k ∙ w).comap p := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Submodule.span_singleton_le_iff_mem]
    · change p x ∈ k ∙ w
      rw [hpx]
      exact (k ∙ w).zero_mem
    · change p y ∈ k ∙ w
      rw [hpy]
      exact (k ∙ w).zero_mem
    · change p w ∈ k ∙ w
      rw [hpw]
      exact Submodule.mem_span_singleton_self w
  have hm : p h ∈ k ∙ w := hl hW
  rwa [hph] at hm


section Cells

open Specs.OrderedRootProducts (Enumerates product)
open Specs.RankOneFlag (SameSubgroup)
open private subgroupIso from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private tensorHom_property from LinearAlgebraicGroups.Affine.Components
open private geometricallyIrreducible_of_connected geometry_of_smooth_geometricallyIrreducible
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open _root_.LinearAlgebraicGroups.CocharacterDynamics
  (LimitDecomposition oppositeCocharacter multiplyFactors)

private theorem list_enumerates {I : Type u} [Finite I] (S : Set I) :
    ∃ l : List I, Enumerates l S := by
  classical
  let s := S.toFinite.toFinset
  exact ⟨s.toList, s.nodup_toList, fun i => by simp [s]⟩

private theorem enumerates_map {I J : Type u} {S : Set I} {T : Set J}
    (e : I ≃ J) (he : ∀ i, i ∈ S ↔ e i ∈ T)
    {l : List I} (hl : Enumerates l S) : Enumerates (l.map e) T := by
  refine ⟨hl.1.map e.injective, fun j => ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective j
  rw [List.mem_map_of_injective e.injective]
  exact (hl.2 i).trans (he i)

/-- A map of ordered root factors with the same order on the two sides. -/
private def rootProductIso {G H : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val}
    (U : RootSubgroupFamily T) (V : RootSubgroupFamily S) (d : Root T → Root S)
    (e : ∀ α, (U α).val.group ≅ (V (d α)).val.group) (l : List (Root T)) :
    product (fun α => (U α).val.group.X) l ≅ product (fun α => (V α).val.group.X) (l.map d) :=
  match l with
  | [] => Iso.refl _
  | α :: l => tensorIso (underlying.mapIso (e α)) (rootProductIso U V d e l)

private theorem rootProduct_eval_cons {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (α : Root T) (l : List (Root T)) {X : SchemeOver k}
    (a : X ⟶ (U α).val.group.X) (b : X ⟶ product (fun β => (U β).val.group.X) l) :
    lift a b ≫ rootProduct U (α :: l) =
      (a ≫ (U α).val.inclusion.hom.hom) * (b ≫ rootProduct U l) := by
  rw [rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]

private theorem rootProductIso_comp {G H : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val}
    (U : RootSubgroupFamily T) (V : RootSubgroupFamily S) (d : Root T → Root S)
    (e : ∀ α, (U α).val.group ≅ (V (d α)).val.group) (f : G.val ⟶ H.val)
    (l : List (Root T))
    (h : ∀ α ∈ l, (U α).val.inclusion ≫ f = (e α).hom ≫ (V (d α)).val.inclusion) :
    rootProduct U l ≫ f.hom.hom = (rootProductIso U V d e l).hom ≫ rootProduct V (l.map d) := by
  induction l with
  | nil =>
    change (1 : (𝟙_ (SchemeOver k)) ⟶ G.val.X) ≫ f.hom.hom =
      𝟙 _ ≫ (1 : (𝟙_ (SchemeOver k)) ⟶ H.val.X)
    rw [MonObj.one_comp, Category.id_comp]
  | cons α l ih =>
    let a := (e α).hom.hom.hom
    let b := (rootProductIso U V d e l).hom
    change rootProduct U (α :: l) ≫ f.hom.hom = (a ⊗ₘ b) ≫ rootProduct V (d α :: l.map d)
    have hh : (U α).val.inclusion.hom.hom ≫ f.hom.hom = a ≫ (V (d α)).val.inclusion.hom.hom :=
      congrArg (fun q => q.hom.hom) (h α (List.mem_cons_self ..))
    have hh' := ih fun β hβ => h β (List.mem_cons_of_mem _ hβ)
    rw [← lift_fst_comp_snd_comp, rootProduct_eval_cons, rootProduct, MonObj.mul_comp, Category.assoc,
      Category.assoc, hh', hh, Category.assoc, Category.assoc]

/-- The scheme family of identity coordinates in an ordered root product. -/
private def rootProductUnit {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    (U : RootSubgroupFamily T) {X : SchemeOver k} (l : List (Root T)) :
    X ⟶ product (fun α => (U α).val.group.X) l :=
  match l with
  | [] => toUnit X
  | _ :: l => lift 1 (rootProductUnit U l)

private theorem rootProductUnit_comp {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    (U : RootSubgroupFamily T) {X : SchemeOver k} (l : List (Root T)) :
    rootProductUnit U (X := X) l ≫ rootProduct U l = 1 := by
  induction l with
  | nil => simp [rootProductUnit, rootProduct, MonObj.comp_one]
  | cons α l ih =>
    simp [rootProductUnit, rootProduct, MonObj.comp_mul, MonObj.one_comp, ih]

private theorem rootProductUnit_map {G H : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val}
    (U : RootSubgroupFamily T) (V : RootSubgroupFamily S) (d : Root T → Root S)
    (e : ∀ α, (U α).val.group ≅ (V (d α)).val.group)
    {X : SchemeOver k} (l : List (Root T)) :
    rootProductUnit U (X := X) l ≫ (rootProductIso U V d e l).hom =
      rootProductUnit V (l.map d) := by
  induction l with
  | nil =>
    change toUnit X ≫ 𝟙 _ = toUnit X
    exact Category.comp_id _
  | cons α l ih =>
    change lift (1 : X ⟶ (U α).val.group.X) (rootProductUnit U l) ≫
      ((underlying.mapIso (e α)).hom ⊗ₘ (rootProductIso U V d e l).hom) = lift (1 : X ⟶ (V (d α)).val.group.X) _
    rw [lift_map, ih]
    change lift ((1 : X ⟶ (U α).val.group.X) ≫ (e α).hom.hom.hom) _ = _
    rw [MonObj.one_comp]

/-- Insert a single factor in an ordered product, with identity sections in the other factors. -/
private theorem rootProduct_single_factor {G H : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val}
    (U : RootSubgroupFamily T) (V : RootSubgroupFamily S) (d : Root T → Root S)
    (e : ∀ α, (U α).val.group ≅ (V (d α)).val.group)
    (l : List (Root T)) (α : Root T) (hα : α ∈ l) :
    ∃ a : (U α).val.group.X ⟶ product (fun j => (U j).val.group.X) l,
      a ≫ rootProduct U l = (U α).val.inclusion.hom.hom ∧
      a ≫ (rootProductIso U V d e l).hom ≫ rootProduct V (l.map d) =
        ((e α).hom ≫ (V (d α)).val.inclusion).hom.hom := by
  classical
  induction l with
  | nil => simp at hα
  | cons β l ih =>
    rcases List.mem_cons.mp hα with rfl | hα
    · let a : (U α).val.group.X ⟶
          product (fun j => (U j).val.group.X) (α :: l) :=
        lift (𝟙 _) (rootProductUnit U l)
      refine ⟨a, ?_, ?_⟩
      · simp only [a, rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
          Category.id_comp, rootProductUnit_comp, mul_one]
      · change a ≫ (((underlying.mapIso (e α)).hom ⊗ₘ (rootProductIso U V d e l).hom) ≫
          rootProduct V ((d α) :: l.map d)) = _
        rw [show a = lift (𝟙 _) (rootProductUnit U l) from rfl, ← Category.assoc, lift_map,
          rootProductUnit_map, Category.id_comp]
        rw [rootProduct_eval_cons, rootProductUnit_comp, mul_one]
        rfl
    · obtain ⟨a, h₁, h₂⟩ := ih hα
      let z : (U α).val.group.X ⟶ product (fun j => (U j).val.group.X) (β :: l) :=
        lift (1 : (U α).val.group.X ⟶ (U β).val.group.X) a
      refine ⟨z, ?_, ?_⟩
      · simp only [z, rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
          MonObj.one_comp, h₁, one_mul]
      · change z ≫ (((underlying.mapIso (e β)).hom ⊗ₘ (rootProductIso U V d e l).hom) ≫
          rootProduct V ((d β) :: l.map d)) = _
        rw [show z = lift (1 : (U α).val.group.X ⟶ (U β).val.group.X) a from rfl,
          ← Category.assoc, lift_map]
        change (lift ((1 : (U α).val.group.X ⟶ (U β).val.group.X) ≫ (e β).hom.hom.hom)
          (a ≫ (rootProductIso U V d e l).hom)) ≫ _ = _
        rw [rootProduct_eval_cons, MonObj.one_comp, MonObj.one_comp, Category.assoc, h₂, one_mul]

/-- Multiplication of the torus and the ordered positive factors parametrizes
the specified Borel. -/
private theorem borelParametrization (contracting : Specs.OrderedRootProducts.ContractingProduct.{u})
    (regular : Specs.BorelsAndChambers.RegularCocharacterBorel.{u})
    (P : SplitBorelPair k) (U : RootSubgroupFamily P.T) (c : Cocharacter P.T.group)
    (D : LimitDecomposition (c ≫ P.T.inclusion)) (hc : IsRegular P.T c)
    (hB : SameSubgroup P.B D.parabolic) (l : List (Root P.T))
    (hl : Enumerates l (positiveRoots P.T c)) :
    ∃ e : P.T.group.X ⊗ product (fun α => (U α).val.group.X) l ≅ P.B.group.X,
      e.hom ≫ P.B.inclusion.hom.hom =
        (fst _ _ ≫ P.T.inclusion.hom.hom) * (snd _ _ ≫ rootProduct U l) := by
  let eB := subgroupIso (A := D.parabolic) (B := P.B) ⟨hB.2, hB.1⟩
  have hC := (regular P.G P.reductive P.T P.split P.maximal c hc D).1
  let eT := subgroupIso (A := P.T) (B := D.centralizer) ⟨hC.2, hC.1⟩
  obtain ⟨eU, heU⟩ := ((contracting P.G P.reductive P.T P.split P.maximal).2.2 c).2 D U l hl
  letI := D.product_iso
  let j := tensorIso (underlying.mapIso eT.val) eU
  let m := multiplyFactors D.sectionMap D.contractingToParabolic
  let e := j ≪≫ asIso m ≪≫ underlying.mapIso eB.val
  refine ⟨e, ?_⟩
  have hb := congrArg (fun g : D.parabolic.group ⟶ P.G.val => g.hom.hom) eB.property
  have ht := congrArg (fun g : P.T.group ⟶ P.G.val => g.hom.hom) eT.property
  have hS := congrArg (fun g : D.centralizer.group ⟶ P.G.val => g.hom.hom) D.section_in_G
  have hU := congrArg (fun g : D.contracting.group ⟶ P.G.val => g.hom.hom) D.contracting_in_G
  change j.hom ≫ m ≫ eB.val.hom.hom.hom ≫ P.B.inclusion.hom.hom = _
  change eB.val.hom.hom.hom ≫ P.B.inclusion.hom.hom = _ at hb
  change eT.val.hom.hom.hom ≫ D.centralizer.inclusion.hom.hom = _ at ht
  change D.sectionMap.hom.hom ≫ D.parabolic.inclusion.hom.hom = _ at hS
  change D.contractingToParabolic.hom.hom ≫ D.parabolic.inclusion.hom.hom = _ at hU
  rw [hb, ← Category.assoc]
  simp only [j, m, multiplyFactors, MonObj.mul_comp, MonObj.comp_mul, Category.assoc,
    tensorIso_hom, hS, hU]
  let p := eT.val.hom.hom.hom
  change ((p ⊗ₘ eU.hom) ≫ _ ≫ D.centralizer.inclusion.hom.hom) *
    ((p ⊗ₘ eU.hom) ≫ _ ≫ D.contracting.inclusion.hom.hom) = _
  rw [← Category.assoc (p ⊗ₘ eU.hom), tensorHom_fst, ← Category.assoc (p ⊗ₘ eU.hom),
    tensorHom_snd, Category.assoc, ht, Category.assoc, heU]

private theorem rootCell_eval {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T) (negative positive : List (Root T))
    {X : SchemeOver k} (a : X ⟶ product (fun α => (U α).val.group.X) negative)
    (b : X ⟶ T.group.X) (c : X ⟶ product (fun α => (U α).val.group.X) positive) :
    lift a (lift b c) ≫ rootCellMap T U negative positive =
      (a ≫ rootProduct U negative) * ((b ≫ T.inclusion.hom.hom) * (c ≫ rootProduct U positive)) := by
  simp only [rootCellMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]

/-- Equality on the paired open cell recovers the prescribed maps on its
individual torus and root factors. -/
private theorem hom_agrees_on_cell_factors {G H : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val}
    (U : RootSubgroupFamily T) (V : RootSubgroupFamily S) (d : Root T → Root S)
    (e : ∀ α, (U α).val.group ≅ (V (d α)).val.group)
    (f : G.val ⟶ H.val) (t : T.group ⟶ S.group) (negative positive : List (Root T))
    (h : rootCellMap T U negative positive ≫ f.hom.hom =
      ((rootProductIso U V d e negative).hom ⊗ₘ (t.hom.hom ⊗ₘ (rootProductIso U V d e positive).hom)) ≫
        rootCellMap S V (negative.map d) (positive.map d)) :
    T.inclusion ≫ f = t ≫ S.inclusion ∧
      ∀ α, α ∈ negative ∨ α ∈ positive → (U α).val.inclusion ≫ f = (e α).hom ≫ (V (d α)).val.inclusion := by
  let negativeIso := (rootProductIso U V d e negative).hom
  let positiveIso := (rootProductIso U V d e positive).hom
  have he {X : SchemeOver k} (a : X ⟶ product (fun α => (U α).val.group.X) negative)
      (b : X ⟶ T.group.X) (c : X ⟶ product (fun α => (U α).val.group.X) positive) :
      ((a ≫ rootProduct U negative) * ((b ≫ T.inclusion.hom.hom) * (c ≫ rootProduct U positive))) ≫ f.hom.hom =
        ((a ≫ negativeIso) ≫ rootProduct V (negative.map d)) *
          (((b ≫ t.hom.hom) ≫ S.inclusion.hom.hom) * ((c ≫ positiveIso) ≫ rootProduct V (positive.map d))) := by
    have hh := congrArg (fun q => lift a (lift b c) ≫ q) h
    change lift a (lift b c) ≫ _ ≫ f.hom.hom =
      lift a (lift b c) ≫ (negativeIso ⊗ₘ (t.hom.hom ⊗ₘ positiveIso)) ≫ _ at hh
    simpa only [← Category.assoc (lift a (lift b c)), lift_map, rootCell_eval] using hh
  constructor
  · apply Grp.hom_ext
    change T.inclusion.hom.hom ≫ f.hom.hom = t.hom.hom ≫ S.inclusion.hom.hom
    simpa only [rootProductUnit_comp, rootProductUnit_map, mul_one, one_mul, Category.id_comp,
      negativeIso, positiveIso] using he (rootProductUnit U negative) (𝟙 T.group.X) (rootProductUnit U positive)
  · intro α hmem
    apply Grp.hom_ext
    change (U α).val.inclusion.hom.hom ≫ f.hom.hom =
      ((e α).hom ≫ (V (d α)).val.inclusion).hom.hom
    rcases hmem with hmem | hmem
    · obtain ⟨a, ha, ha'⟩ := rootProduct_single_factor U V d e negative α hmem
      have hh := he a (1 : (U α).val.group.X ⟶ T.group.X) (rootProductUnit U positive)
      simpa only [ha, rootProductUnit_comp, rootProductUnit_map, MonObj.one_comp, one_mul,
        mul_one, Category.assoc, negativeIso, positiveIso, ha'] using hh
    · obtain ⟨a, ha, ha'⟩ := rootProduct_single_factor U V d e positive α hmem
      have hh := he (rootProductUnit U negative) (1 : (U α).val.group.X ⟶ T.group.X) a
      simpa only [ha, rootProductUnit_comp, rootProductUnit_map, MonObj.one_comp, one_mul,
        mul_one, Category.assoc, negativeIso, positiveIso, ha'] using hh

private theorem affine_root_product (P : SplitBorelPair k) (U : RootSubgroupFamily P.T)
    (l : List (Root P.T)) : IsAffine (product (fun α => (U α).val.group.X) l).left := by
  induction l with
  | nil => exact inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  | cons α l ih =>
    have : IsAffine (U α).val.group.X.left :=
      (Unipotent.closedSubgroupAlgebraicGroup (G := P.G) (U α).val).property.1
    have : IsAffine (product (fun β => (U β).val.group.X) l).left := ih
    exact affine_tensor _ _

/-- Two ordered cells and their tangent constraint give the lift, including
the scheme map on the specified Borels and the pinning equations. -/
private theorem lifts_of_paired_root_cells [CharZero k]
    (word : WordGeneratedGroup.{u}) (generic : DominantGenericLift.{u})
    {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair) (h : LatticeMap D E)
    (t : P.pair.T.group ⟶ Q.pair.T.group) (hts : Surjective t.hom.hom.left)
    (htχ : ∀ χ : Character Q.pair.T.group, t ≫ χ = h.characters χ)
    (hti : Function.Bijective h.characters → IsIso t)
    (e : ∀ α, (P.roots α).val.group ≅ (Q.roots (h.roots α)).val.group)
    (he : ∀ α : SimpleRoot P.pair, (P.pin α).val.hom ≫ (e α.val).hom = (Q.pin (h.simpleRoot α)).val.hom)
    (c : Cocharacter P.pair.T.group) (d : Cocharacter Q.pair.T.group)
    (C : LimitDecomposition (c ≫ P.pair.T.inclusion))
    (F : LimitDecomposition (d ≫ Q.pair.T.inclusion))
    (hc : IsRegular P.pair.T c) (hd : IsRegular Q.pair.T d)
    (hC : SameSubgroup P.pair.B C.parabolic) (hF : SameSubgroup Q.pair.B F.parabolic)
    (hchamber : subgroupRoots P.pair.T P.pair.B = positiveRoots P.pair.T c)
    (negative positive : List (Root P.pair.T))
    (hNegative : Enumerates negative (positiveRoots P.pair.T (oppositeCocharacter c)))
    (hPositive : Enumerates positive (positiveRoots P.pair.T c))
    (hNegative' : Enumerates (negative.map h.roots) (positiveRoots Q.pair.T (oppositeCocharacter d)))
    (hPositive' : Enumerates (positive.map h.roots) (positiveRoots Q.pair.T d))
    (hTangent :
      PairedTangentConstraint (rootCellMap P.pair.T P.roots negative positive)
        (((rootProductIso P.roots Q.roots h.roots e negative).hom ⊗ₘ
          (t.hom.hom ⊗ₘ (rootProductIso P.roots Q.roots h.roots e positive).hom)) ≫
          rootCellMap Q.pair.T Q.roots (negative.map h.roots) (positive.map h.roots))) :
    Lifts P Q D E h := by
  let G := P.pair.G
  let H := Q.pair.G
  let g₁ := rootCellMap P.pair.T P.roots negative positive
  let g₂' := rootCellMap Q.pair.T Q.roots (negative.map h.roots) (positive.map h.roots)
  let negativeIso := rootProductIso P.roots Q.roots h.roots e negative
  let positiveIso := rootProductIso P.roots Q.roots h.roots e positive
  let j := negativeIso.hom ⊗ₘ (t.hom.hom ⊗ₘ positiveIso.hom)
  let g₂ := j ≫ g₂'
  let X := product (fun α => (P.roots α).val.group.X) negative ⊗
    (P.pair.T.group.X ⊗ product (fun α => (P.roots α).val.group.X) positive)
  haveI : Smooth G.val.X.hom := P.pair.reductive.1
  haveI : Smooth H.val.X.hom := Q.pair.reductive.1
  haveI : GeometricallyConnected G.val.X.hom := P.pair.reductive.2.1
  haveI : GeometricallyConnected H.val.X.hom := Q.pair.reductive.2.1
  haveI : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  haveI : ConnectedSpace H.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton H.val.X.hom
  haveI : GeometricallyIrreducible G.val.X.hom := geometricallyIrreducible_of_connected G
  haveI : IsIntegral G.val.X.left :=
    (geometry_of_smooth_geometricallyIrreducible G.val.X).2.2
  haveI : GeometricallyIrreducible H.val.X.hom := geometricallyIrreducible_of_connected H
  haveI : IrreducibleSpace H.val.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton H.val.X.hom
  have hCell : Specs.OrderedRootProducts.RegularRootCell.{u} :=
    LinearAlgebraicGroups.RootData.OrderedRootProducts.regularRootCell
  haveI : IsOpenImmersion g₁.left :=
    hCell G P.pair.reductive P.pair.T P.pair.split P.pair.maximal c hc P.roots negative positive hNegative hPositive
  haveI : IsOpenImmersion g₂'.left :=
    hCell H Q.pair.reductive Q.pair.T Q.pair.split Q.pair.maximal d hd Q.roots _ _ hNegative' hPositive'
  haveI : IsAffine P.pair.T.group.X.left :=
    (Unipotent.closedSubgroupAlgebraicGroup P.pair.T).property.1
  haveI : IsAffine (product (fun α => (P.roots α).val.group.X) negative).left := affine_root_product P.pair P.roots negative
  haveI : IsAffine (product (fun α => (P.roots α).val.group.X) positive).left := affine_root_product P.pair P.roots positive
  haveI : IsAffine (P.pair.T.group.X ⊗ product (fun α => (P.roots α).val.group.X) positive).left :=
    affine_tensor _ _
  haveI : IsAffine X.left := affine_tensor _ _
  haveI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  haveI : LocallyOfFiniteType (g₁.left ≫ G.val.X.hom) := inferInstance
  haveI : LocallyOfFiniteType X.hom := Over.w g₁ ▸ inferInstance
  let x₀ : 𝟙_ (SchemeOver k) ⟶ X :=
    lift (rootProductUnit P.roots negative) (lift 1 (rootProductUnit P.roots positive))
  have hx₁ : x₀ ≫ g₁ = 1 := by
    dsimp only [x₀, g₁]
    rw [rootCell_eval, rootProductUnit_comp, rootProductUnit_comp, MonObj.one_comp, mul_one, mul_one]
  have hx₂ : x₀ ≫ g₂ = 1 := by
    dsimp only [x₀, g₂, j, g₂', negativeIso, positiveIso]
    rw [← Category.assoc, lift_map, lift_map, rootProductUnit_map, rootProductUnit_map,
      MonObj.one_comp, rootCell_eval, rootProductUnit_comp, rootProductUnit_comp, MonObj.one_comp,
      mul_one, mul_one]
  have hpow := integral_power_of_pointed_open g₁ x₀
  haveI : IsIso negativeIso.hom.left := (Over.forget _).map_isIso negativeIso.hom
  haveI : IsIso positiveIso.hom.left := (Over.forget _).map_isIso positiveIso.hom
  have hsur := tensorHom_property t.hom.hom positiveIso.hom @Surjective hts inferInstance
  haveI : Surjective j.left :=
    tensorHom_property negativeIso.hom _ @Surjective inferInstance hsur
  have hnon : (Set.range g₂'.left).Nonempty :=
    ⟨_, ⟨j.left (x₀.left (IsLocalRing.closedPoint k)), rfl⟩⟩
  haveI : IsDominant g₂'.left := ⟨g₂'.left.isOpenEmbedding.isOpen_range.dense hnon⟩
  haveI : IsDominant g₂.left := inferInstanceAs (IsDominant (j.left ≫ g₂'.left))
  obtain ⟨f, hf, hfcell⟩ := centralIsogeny_of_paired_cells word generic G H x₀ g₁ g₂
    hx₁ hx₂ hpow hTangent
  obtain ⟨ht, hr⟩ := hom_agrees_on_cell_factors P.roots Q.roots h.roots e f t negative positive hfcell
  have hr' := rootProductIso_comp P.roots Q.roots h.roots e f positive (fun α hα => hr α (Or.inr hα))
  have hContracting : Specs.OrderedRootProducts.ContractingProduct.{u} :=
    LinearAlgebraicGroups.RootData.OrderedRootProducts.contractingProduct
  have hRegular : Specs.BorelsAndChambers.RegularCocharacterBorel.{u} :=
    LinearAlgebraicGroups.RootData.BorelsAndChambers.regularCocharacterBorel
  obtain ⟨bP, hbP⟩ := borelParametrization hContracting hRegular P.pair P.roots c C hc hC positive hPositive
  obtain ⟨bQ, hbQ⟩ := borelParametrization hContracting hRegular Q.pair Q.roots d F hd hF _ hPositive'
  have htb : P.pair.T.inclusion.hom.hom ≫ f.hom.hom =
      t.hom.hom ≫ Q.pair.T.inclusion.hom.hom := congrArg (fun g => g.hom.hom) ht
  have hb : bP.hom ≫ P.pair.B.inclusion.hom.hom ≫ f.hom.hom =
      (t.hom.hom ⊗ₘ positiveIso.hom) ≫ bQ.hom ≫ Q.pair.B.inclusion.hom.hom := by
    rw [← Category.assoc bP.hom, hbP, hbQ, MonObj.mul_comp, MonObj.comp_mul]
    simp only [Category.assoc, htb, hr', positiveIso, tensorHom_fst_assoc, tensorHom_snd_assoc]
  obtain ⟨b, hb₁, hb₂⟩ := surjective_subgroup_map_of_parametrizations f P.pair.B Q.pair.B
    bP bQ _ hsur hb
  refine ⟨f, t, b, hf, hts, hb₂, ht, hb₁, htχ, fun α => ?_, fun hbij => ?_⟩
  · have hs : α.val ∈ positive := (hPositive.2 _).mpr (hchamber ▸ α.property.1)
    rw [hr α.val (Or.inr hs), ← Category.assoc, he α]
  · haveI := hti hbij
    exact isIso_of_centralIsogeny_of_torusIso P.pair Q.pair f t hf ht

private theorem lift_mul_points {G H : GroupScheme k} {X : SchemeOver k}
    (a b : X ⟶ G.X) (c d : X ⟶ H.X) :
    (lift (a * b) (c * d) : X ⟶ (G ⊗ H).X) =
      lift a c * lift b d := by
  apply CartesianMonoidalCategory.hom_ext
  · change lift (a * b) (c * d) ≫ (fst G H).hom.hom =
      (lift a c * lift b d) ≫ (fst G H).hom.hom
    rw [MonObj.mul_comp, Grp.fst_hom_hom, lift_fst, lift_fst, lift_fst]
  · change lift (a * b) (c * d) ≫ (snd G H).hom.hom =
      (lift a c * lift b d) ≫ (snd G H).hom.hom
    rw [MonObj.mul_comp, Grp.snd_hom_hom, lift_snd, lift_snd, lift_snd]

private theorem lift_one_points {G H : GroupScheme k} {X : SchemeOver k} :
    (lift (1 : X ⟶ G.X) (1 : X ⟶ H.X) : X ⟶ (G ⊗ H).X) = 1 := by
  apply CartesianMonoidalCategory.hom_ext
  · change _ ≫ (fst G H).hom.hom = (1 : X ⟶ (G ⊗ H).X) ≫ (fst G H).hom.hom
    rw [MonObj.one_comp, Grp.fst_hom_hom, lift_fst]
  · change _ ≫ (snd G H).hom.hom = (1 : X ⟶ (G ⊗ H).X) ≫ (snd G H).hom.hom
    rw [MonObj.one_comp, Grp.snd_hom_hom, lift_snd]

/-- Tangent conditions on individual paired root factors extend to their ordered product. -/
private theorem ordered_root_product_mem {G H : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val}
    (U : RootSubgroupFamily T) (V : RootSubgroupFamily S) (d : Root T → Root S)
    (e : ∀ α, (U α).val.group ≅ (V (d α)).val.group)
    {X : SchemeOver k} (K : Subgroup (X ⟶ (G.val ⊗ H.val).X))
    (h : ∀ α (x : X ⟶ (U α).val.group.X),
      (lift (x ≫ (U α).val.inclusion.hom.hom)
        (x ≫ (e α).hom.hom.hom ≫ (V (d α)).val.inclusion.hom.hom) :
          X ⟶ (G.val ⊗ H.val).X) ∈ K)
    (l : List (Root T)) (x : X ⟶ product (fun α => (U α).val.group.X) l) :
    (lift (x ≫ rootProduct U l)
      (x ≫ (rootProductIso U V d e l).hom ≫ rootProduct V (l.map d)) :
        X ⟶ (G.val ⊗ H.val).X) ∈ K := by
  induction l with
  | nil =>
    change (lift (x ≫ (1 : (𝟙_ (SchemeOver k)) ⟶ G.val.X))
      (x ≫ 𝟙 _ ≫ (1 : (𝟙_ (SchemeOver k)) ⟶ H.val.X)) : X ⟶ (G.val ⊗ H.val).X) ∈ K
    rw [Category.id_comp, MonObj.comp_one, MonObj.comp_one, lift_one_points]
    exact K.one_mem
  | cons α l ih =>
    let a := x ≫ fst (U α).val.group.X (product (fun β => (U β).val.group.X) l)
    let b := x ≫ snd (U α).val.group.X (product (fun β => (U β).val.group.X) l)
    let j := (e α).hom.hom.hom
    let m := (rootProductIso U V d e l).hom
    have hx : lift a b = x := lift_comp_fst_snd x
    have h1 : x ≫ rootProduct U (α :: l) =
        (a ≫ (U α).val.inclusion.hom.hom) * (b ≫ rootProduct U l) :=
      hx ▸ rootProduct_eval_cons U α l a b
    have h2 : x ≫ (j ⊗ₘ m) ≫ rootProduct V (d α :: l.map d) =
        (a ≫ j ≫ (V (d α)).val.inclusion.hom.hom) * (b ≫ m ≫ rootProduct V (l.map d)) := by
      rw [← hx, ← Category.assoc, lift_map, rootProduct_eval_cons]
      simp only [Category.assoc]
    change (lift (x ≫ rootProduct U (α :: l))
      (x ≫ (j ⊗ₘ m) ≫ rootProduct V (d α :: l.map d)) : X ⟶ (G.val ⊗ H.val).X) ∈ K
    rw [h1, h2, lift_mul_points]
    exact K.mul_mem (h α a) (ih b)

/-- Multiplicative closure of the constraint tests the whole paired cell
once it has been tested on the torus and root factors. -/
private theorem paired_cell_mem {G H : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val}
    (U : RootSubgroupFamily T) (V : RootSubgroupFamily S) (d : Root T → Root S)
    (e : ∀ α, (U α).val.group ≅ (V (d α)).val.group) (t : T.group ⟶ S.group)
    {Z : SchemeOver k} (K : Subgroup (Z ⟶ (G.val ⊗ H.val).X))
    (hT : ∀ z : Z ⟶ T.group.X,
      (lift (z ≫ T.inclusion.hom.hom) (z ≫ t.hom.hom ≫ S.inclusion.hom.hom) :
        Z ⟶ (G.val ⊗ H.val).X) ∈ K)
    (hU : ∀ α (z : Z ⟶ (U α).val.group.X),
      (lift (z ≫ (U α).val.inclusion.hom.hom)
        (z ≫ (e α).hom.hom.hom ≫ (V (d α)).val.inclusion.hom.hom) :
          Z ⟶ (G.val ⊗ H.val).X) ∈ K)
    (negative positive : List (Root T))
    (x : Z ⟶ product (fun α => (U α).val.group.X) negative ⊗
      (T.group.X ⊗ product (fun α => (U α).val.group.X) positive)) :
    (x ≫ lift (rootCellMap T U negative positive)
      (((rootProductIso U V d e negative).hom ⊗ₘ (t.hom.hom ⊗ₘ
        (rootProductIso U V d e positive).hom)) ≫
        rootCellMap S V (negative.map d) (positive.map d)) : Z ⟶ (G.val ⊗ H.val).X) ∈ K := by
  let a := x ≫ fst _ _
  let b := x ≫ snd _ _ ≫ fst _ _
  let c := x ≫ snd _ _ ≫ snd _ _
  let j := (rootProductIso U V d e negative).hom
  let m := (rootProductIso U V d e positive).hom
  have hx : lift a (lift b c) = x := by
    dsimp only [a, b, c]
    rw [← Category.assoc x (snd _ _), ← Category.assoc x (snd _ _),
      lift_comp_fst_snd, lift_comp_fst_snd]
  rw [← hx]
  simp only [comp_lift, rootCell_eval]
  rw [← Category.assoc (lift a (lift b c)), lift_map, lift_map, rootCell_eval,
    lift_mul_points, lift_mul_points]
  exact K.mul_mem (ordered_root_product_mem U V d e K hU negative a)
    (K.mul_mem (hT b) (ordered_root_product_mem U V d e K hU positive c))

/-- The compatible torus and root factors give the required constraint for
the affine family used in the dominant word argument. -/
private theorem paired_cell_tangent_constraint {G H : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val}
    (U : RootSubgroupFamily T) (V : RootSubgroupFamily S) (d : Root T → Root S)
    (e : ∀ α, (U α).val.group ≅ (V (d α)).val.group) (t : T.group ⟶ S.group)
    {I : Type u} [Fintype I] [DecidableEq I]
    [AddCommGroup (Lie k G.val)] [Module k (Lie k G.val)]
    [AddCommGroup (Lie k H.val)] [Module k (Lie k H.val)]
    {b₁ : Module.Basis I k (Lie k G.val)} {b₂ : Module.Basis I k (Lie k H.val)}
    (C₁ : AdjointRepresentation.TangentCoordinates G.val I b₁)
    (C₂ : AdjointRepresentation.TangentCoordinates H.val I b₂)
    (hT : ∀ (R : TestAlgebra k) (z : GroupPoints T.group (CommAlgCat.of k (DualNumber R))),
      (lift (z ≫ T.inclusion.hom.hom) (z ≫ t.hom.hom ≫ S.inclusion.hom.hom) :
        GroupPoints (G.val ⊗ H.val) (CommAlgCat.of k (DualNumber R))) ∈
        displacementSubgroup (reducePoints (G.val ⊗ H.val) R)
          (constantPoints (G.val ⊗ H.val) R) (tangentGraph C₁ C₂ R))
    (hU : ∀ α (R : TestAlgebra k)
      (z : GroupPoints (U α).val.group (CommAlgCat.of k (DualNumber R))),
      (lift (z ≫ (U α).val.inclusion.hom.hom)
        (z ≫ (e α).hom.hom.hom ≫ (V (d α)).val.inclusion.hom.hom) :
          GroupPoints (G.val ⊗ H.val) (CommAlgCat.of k (DualNumber R))) ∈
        displacementSubgroup (reducePoints (G.val ⊗ H.val) R)
          (constantPoints (G.val ⊗ H.val) R) (tangentGraph C₁ C₂ R))
    (negative positive : List (Root T)) :
    PairedTangentConstraint (rootCellMap T U negative positive)
      (((rootProductIso U V d e negative).hom ⊗ₘ
        (t.hom.hom ⊗ₘ (rootProductIso U V d e positive).hom)) ≫
        rootCellMap S V (negative.map d) (positive.map d)) := by
  intro K _ _
  let R := CommAlgCat.of k K
  let H₀ := tangentGraph C₁ C₂ R
  let r := reducePoints (G.val ⊗ H.val) R
  let c := constantPoints (G.val ⊗ H.val) R
  let J := displacementSubgroup r c H₀
  have h := paired_cell_mem U V d e t J (hT R) (fun α => hU α R) negative positive
  exact ⟨H₀, fun x => (h x).1, fun x => (h x).2,
    tangentGraph_fst_injective C₁ C₂ R, tangentGraph_snd_injective C₁ C₂ R⟩

end Cells


private def infinitesimalUnit {k : Type*} [CommRing k] :
    Multiplicative k →* (DualNumber k)ˣ where
  toFun a := ⟨(⟨1, a.toAdd⟩ : DualNumber k), ⟨1, -a.toAdd⟩,
    TrivSqZeroExt.ext (by change (1 : k) * 1 = 1; simp) (by change (1 : k) * -a.toAdd + a.toAdd * 1 = 0; simp),
    TrivSqZeroExt.ext (by change (1 : k) * 1 = 1; simp) (by change (1 : k) * a.toAdd + -a.toAdd * 1 = 0; simp)⟩
  map_one' := Units.ext (TrivSqZeroExt.ext rfl rfl)
  map_mul' a b := Units.ext (TrivSqZeroExt.ext (by change (1 : k) = 1 * 1; simp) (by
    change a.toAdd + b.toAdd = (1 : k) * b.toAdd + a.toAdd * 1
    simp [add_comm]))

private theorem infinitesimalUnit_pow {k : Type*} [CommRing k] (a : k) (n : ℤ) :
    (↑(infinitesimalUnit (Multiplicative.ofAdd a) ^ n) : DualNumber k) =
      ⟨1, (n : k) * a⟩ := by
  rw [← map_zpow, ← ofAdd_zsmul]
  change (⟨1, n • a⟩ : DualNumber k) = ⟨1, (n : k) * a⟩
  rw [zsmul_eq_mul]

/-- Integer powers of one fixed unit already distinguish integral characters
after restricting to a cocharacter. -/
private theorem two_unit_zpow_injective (k : Type*) [Field k] [CharZero k] :
    ∃ z : kˣ, Function.Injective (fun n : ℤ => (↑(z ^ n) : k)) := by
  let q := Units.mk0 (2 : ℚ) (by norm_num)
  let f := Rat.castHom k
  let z := Units.map f.toMonoidHom q
  refine ⟨z, fun m n h => ?_⟩
  have he (n : ℤ) : (↑(z ^ n) : k) = f ((2 : ℚ) ^ n) := by
    rw [show z = Units.map f.toMonoidHom q from rfl, ← map_zpow]
    change f (↑(q ^ n) : ℚ) = _
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  change (↑(z ^ m) : k) = (↑(z ^ n) : k) at h
  rw [he, he] at h
  exact (zpow_right_strictMono₀ (show (1 : ℚ) < 2 by norm_num)).injective (f.injective h)

open private adjointWeightVectors_iff from LinearAlgebraicGroups.RootData.CharacterPairing


section MatrixTangents

open Specs.CharacterPairing (characterValue)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open scoped Matrix
open Specs.AdjointRepresentation (TangentCoordinates conjugate)
open Specs.StandardGroups (generalLinearPoints)
open InfinitesimalCommutator (matrixDifferential)

private theorem mulVec_dual_snd {I : Type u} [Fintype I]
    (M : Matrix I I (DualNumber k)) (v : I → k) (i : I) :
    ((M *ᵥ (fun j => algebraMap k (DualNumber k) (v j))) i).snd =
      ((M.map TrivSqZeroExt.snd) *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct, TrivSqZeroExt.snd_sum, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro j _
  change (M i j).fst * 0 + (M i j).snd * v j = (M i j).snd * v j
  simp

private theorem matrix_eq_of_mulVec_eq {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    {M N : Matrix I I R} (h : ∀ v : I → R, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have he := congrFun (h (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using he

/-- Infinitesimal conjugation by a cocharacter acts on a root vector by its
integral character pairing. -/
private theorem lie_coroot_weight {G L : GroupScheme k} {I : Type u}
    [Fintype I] [DecidableEq I] [LieRing (Lie k G)] [LieAlgebra k (Lie k G)]
    {b : Module.Basis I k (Lie k G)} (C : TangentCoordinates G I b)
    (l : (groupPointsFunctor k).obj L ≅ generalLinearPoints k I) (Ad : G ⟶ L)
    (hAd : ∀ (R : TestAlgebra k) (g : GroupPoints G R) (v : I → R),
      let M := (l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R g)
      (C.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (C.equiv R v))
    (hbr : ∀ (p v : Lie k G), matrixDifferential Ad l p *ᵥ b.equivFun v = b.equivFun ⁅p, v⁆)
    (T : ClosedSubgroup G) (c : Cocharacter T.group) (χ : Character T.group)
    (p v : Lie k G) (hv : v ∈ adjointWeightVectors T χ)
    (hp : p.toMul.val =
      cocharacterPoint c (CommAlgCat.of k (DualNumber k)) (infinitesimalUnit (Multiplicative.ofAdd 1))
        ≫ T.inclusion.hom.hom) :
    b.equivFun ⁅p, v⁆ = (pairing T.group χ c : k) • b.equivFun v := by
  let R := CommAlgCat.of k (DualNumber k)
  let z := infinitesimalUnit (Multiplicative.ofAdd (1 : k))
  let t := cocharacterPoint c R z
  let M := ((l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R p.toMul.val)).val
  let V : I → R := fun i => algebraMap k R (b.equivFun v i)
  have hw := ((adjointWeightVectors_iff C l Ad hAd T χ v).mp hv) R t
  have hp' : p.toMul.val = t ≫ T.inclusion.hom.hom := hp
  have hc : (((groupPointsFunctor k).map (T.inclusion ≫ Ad)).app R) t =
      (((groupPointsFunctor k).map Ad).app R) p.toMul.val := by
    change t ≫ (T.inclusion ≫ Ad).hom.hom = p.toMul.val ≫ Ad.hom.hom
    rw [hp', Grp.comp_hom_hom, Category.assoc]
  change _ *ᵥ V = characterValue χ R t • V at hw
  rw [hc] at hw
  change M *ᵥ V = characterValue χ R t • V at hw
  have hh := (LinearAlgebraicGroups.RootData.CharacterPairing.characterPairingComposition
    T.group χ c).2 R z
  change characterValue χ R t = _ at hh
  rw [hh, infinitesimalUnit_pow, mul_one] at hw
  funext i
  have hi := congrArg (fun v : I → R => (v i).snd) hw
  change ((M *ᵥ V) i).snd = (⟨1, (pairing T.group χ c : k)⟩ *
    algebraMap k (DualNumber k) (b.equivFun v i) : DualNumber k).snd at hi
  rw [mulVec_dual_snd] at hi
  have hi' : ((matrixDifferential Ad l p) *ᵥ b.equivFun v) i =
      (pairing T.group χ c : k) * b.equivFun v i := by
    rw [DualNumber.snd_mul] at hi
    change ((matrixDifferential Ad l p) *ᵥ b.equivFun v) i =
      (1 : k) * 0 + (pairing T.group χ c : k) * b.equivFun v i at hi
    simpa only [mul_zero, zero_add] using hi
  exact (congrFun (hbr p v).symm i).trans hi'

end MatrixTangents


section MatchedRootActions

open scoped Matrix
open Specs.AdjointRepresentation (TangentCoordinates conjugate)
open Specs.StandardGroups (generalLinearPoints)
open InfinitesimalCommutator (matrixDifferential)
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups

private theorem basis_map_coordinates {G H : GroupScheme k} {I : Type u} [Fintype I]
    [LieRing (Lie k G)] [LieAlgebra k (Lie k G)] [LieRing (Lie k H)] [LieAlgebra k (Lie k H)]
    (b : Module.Basis I k (Lie k G)) (e : Lie k G ≃ₗ⁅k⁆ Lie k H) (v : Lie k G) :
    (b.map e.toLinearEquiv).equivFun (e v) = b.equivFun v := by
  rw [Module.Basis.map_equivFun, LinearEquiv.trans_apply]
  congr 1
  exact e.toLinearEquiv.symm_apply_apply v

/-- In compatible Lie bases, the adjoint matrices of paired root
parametrizations agree over each test algebra. -/
private theorem paired_root_adjoint_matrices [CharZero k]
    {G H L₁ L₂ : GroupScheme k} {I : Type u} [Fintype I] [DecidableEq I]
    [LieRing (Lie k G)] [LieAlgebra k (Lie k G)] [LieRing (Lie k H)] [LieAlgebra k (Lie k H)]
    (b : Module.Basis I k (Lie k G)) (e : Lie k G ≃ₗ⁅k⁆ Lie k H)
    (Ad₁ : G ⟶ L₁) (Ad₂ : H ⟶ L₂)
    (l₁ : (groupPointsFunctor k).obj L₁ ≅ generalLinearPoints k I)
    (l₂ : (groupPointsFunctor k).obj L₂ ≅ generalLinearPoints k I)
    (h₁ : ∀ (x y : Lie k G), matrixDifferential Ad₁ l₁ x *ᵥ b.equivFun y = b.equivFun ⁅x, y⁆)
    (h₂ : ∀ (x y : Lie k H), matrixDifferential Ad₂ l₂ x *ᵥ (b.map e.toLinearEquiv).equivFun y =
      (b.map e.toLinearEquiv).equivFun ⁅x, y⁆)
    {A : AdditiveLine k} (x : A.group ⟶ G) (y : A.group ⟶ H) (v : Lie k G)
    (hv : v.toMul.val = rootPoint x (CommAlgCat.of k (DualNumber k)) DualNumber.eps)
    (hw : (e v).toMul.val = rootPoint y (CommAlgCat.of k (DualNumber k)) DualNumber.eps)
    (R : TestAlgebra k) (s : R) :
    rootMatrix (x ≫ Ad₁) l₁ R s = rootMatrix (y ≫ Ad₂) l₂ R s := by
  have hmat : matrixDifferential Ad₁ l₁ v = matrixDifferential Ad₂ l₂ (e v) := by
    apply matrix_eq_of_mulVec_eq
    intro a
    obtain ⟨z, rfl⟩ := b.equivFun.surjective a
    rw [h₁, ← basis_map_coordinates b e z, h₂, ← LieEquiv.map_lie, basis_map_coordinates]
  apply rootMatrix_eq_of_differential
  intro i j
  have hz := congrArg (fun M : Matrix I I k => M i j) hmat
  let R₀ := CommAlgCat.of k (DualNumber k)
  change ((rootMatrix (x ≫ Ad₁) l₁ R₀ DualNumber.eps i j).snd : k) =
    (rootMatrix (y ≫ Ad₂) l₂ R₀ DualNumber.eps i j).snd
  unfold rootMatrix
  rw [rootPoint_comp, rootPoint_comp, ← hv, ← hw]
  exact hz

end MatchedRootActions

section SerreAndWeights
open scoped DirectSum TensorProduct


/-- A Lie map into a larger coefficient ring extends to the tensor product
by the scalar action on its target. -/
private def extendLieHom {R K L M : Type*} [CommRing R] [CommRing K] [Algebra R K]
    [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra K M] [LieAlgebra R M] [IsScalarTower R K M]
    (f : L →ₗ⁅R⁆ M) : K ⊗[R] L →ₗ⁅K⁆ M := by
  let b : K →ₗ[K] L →ₗ[R] M :=
    { toFun := fun a => a • f.toLinearMap
      map_add' := fun a b => add_smul a b f.toLinearMap
      map_smul' := fun a b => by simp only [RingHom.id_apply, smul_eq_mul, mul_smul] }
  let F := TensorProduct.AlgebraTensorModule.lift b
  have h (a : K) (x : L) : F (a ⊗ₜ[R] x) = a • f x := rfl
  refine { toLinearMap := F, map_lie' := ?_ }
  intro x y
  change F ⁅x, y⁆ = ⁅F x, F y⁆
  induction x with
  | tmul a x =>
    induction y with
    | tmul b y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, h, h, h, f.map_lie, smul_lie, lie_smul, smul_smul]
    | add a' b' ha hb =>
      rw [lie_add, map_add, ha, hb, map_add, lie_add]
  | add a b ha hb =>
    rw [add_lie, map_add, ha, hb, map_add, add_lie]

private theorem extendLieHom_tmul {R K L M : Type*} [CommRing R] [CommRing K] [Algebra R K]
    [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra K M] [LieAlgebra R M] [IsScalarTower R K M]
    (f : L →ₗ⁅R⁆ M) (a : K) (x : L) :
    extendLieHom f (a ⊗ₜ[R] x) = a • f x := rfl


/-- An internal sum of weight spaces detects simultaneous eigenvectors
as soon as distinct weights differ at some operator. -/
private theorem mem_weight_of_eigenvalues {k V I T : Type*} [Field k] [AddCommGroup V] [Module k V]
    [DecidableEq I] (W : I → Submodule k V) (hW : DirectSum.IsInternal W)
    (a : T → Module.End k V) (w : I → T → k)
    (hd : ∀ (j : I) t (v : W j), a t v.val = w j t • v.val)
    (i : I) (hsep : ∀ j ≠ i, W j ≠ ⊥ → ∃ t, w j t ≠ w i t)
    (v : V) (hv : ∀ t, a t v = w i t • v) : v ∈ W i := by
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hW
  let p (j : I) : V →ₗ[k] W j :=
    (DirectSum.component k I (fun j => W j) j).comp e.symm.toLinearMap
  have he (j : I) (z : W j) : e.symm z.val = DirectSum.of (fun j => W j) j z :=
    e.symm_apply_eq.mpr (DirectSum.coeLinearMap_of W j z).symm
  have hπ (t : T) (j : I) (x : V) : p j (a t x) = w j t • p j x := by
    obtain ⟨z, rfl⟩ := e.surjective x
    refine DirectSum.induction_on z ?_ ?_ ?_
    · simp
    · intro l u
      have hz : e (DirectSum.of (fun j => W j) l u) = u.val :=
        DirectSum.coeLinearMap_of W l u
      rw [hz, hd, map_smul]
      change w l t • DirectSum.component k I (fun j => W j) j (e.symm u.val) =
        w j t • DirectSum.component k I (fun j => W j) j (e.symm u.val)
      rw [he]
      by_cases hj : l = j
      · subst l; rfl
      · change w l t • DirectSum.of (fun j => W j) l u j =
          w j t • DirectSum.of (fun j => W j) l u j
        rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj), smul_zero, smul_zero]
    · intro x y hx hy
      simp only [map_add, hx, hy, smul_add]
  have hz (j : I) (hji : j ≠ i) : p j v = 0 := by
    by_cases hb : W j = ⊥
    · apply Subtype.ext
      exact (Submodule.mem_bot k).mp (hb ▸ (p j v).property)
    · obtain ⟨t, ht⟩ := hsep j hji hb
      have h := hπ t j v
      rw [hv t, map_smul] at h
      apply (smul_right_injective (W j) (sub_ne_zero.mpr ht))
      change (w j t - w i t) • p j v = (w j t - w i t) • (0 : W j)
      rw [sub_smul, ← h, sub_self, smul_zero]
  have H : e.symm v = DirectSum.of (fun j => W j) i (p i v) := by
    ext1 j
    change p j v = (DirectSum.of (fun j => W j) i (p i v)) j
    by_cases h : j = i
    · subst j
      rw [DirectSum.of_eq_same]
    · rw [hz j h, DirectSum.of_eq_of_ne _ _ _ h]
  have h : v = (p i v).val :=
    (e.apply_symm_apply v).symm.trans ((congrArg e H).trans (DirectSum.coeLinearMap_of W i (p i v)))
  exact h.symm ▸ (p i v).property


/-- A finite-index inclusion of abelian lattices gives a bijection on
homomorphisms to the additive group of a characteristic-zero field. -/
private theorem restrict_characters_to_additive_bijective
    {X Y k : Type*} [CommGroup X] [CommGroup Y] [Field k] [CharZero k]
    (f : Y →* X) (hf : Function.Injective f) [Finite (X ⧸ f.range)] :
    Function.Bijective (fun g : X →* Multiplicative k => g.comp f) := by
  classical
  let n := Nat.card (X ⧸ f.range)
  have hn : (n : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := X ⧸ f.range)).ne'
  have hpow (x : X) : x ^ n ∈ f.range := by
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  let p : X →* f.range :=
    { toFun := fun x => ⟨x ^ n, hpow x⟩
      map_one' := Subtype.ext (one_pow _)
      map_mul' := fun x y => Subtype.ext (mul_pow _ _ _) }
  let e := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  constructor
  · intro g g' h
    apply MonoidHom.ext
    intro x
    obtain ⟨y, hy⟩ := hpow x
    have he := DFunLike.congr_fun h y
    change g (f y) = g' (f y) at he
    rw [hy, map_pow, map_pow] at he
    have hh := congrArg Multiplicative.toAdd he
    change n • (g x).toAdd = n • (g' x).toAdd at hh
    rw [nsmul_eq_mul, nsmul_eq_mul] at hh
    exact Multiplicative.toAdd.injective (mul_left_cancel₀ hn hh)
  · intro g
    let b := g.comp (e.symm.toMonoidHom.comp p)
    let a : X →* Multiplicative k :=
      { toFun := fun x => Multiplicative.ofAdd ((n : k)⁻¹ * (b x).toAdd)
        map_one' := by
          apply Multiplicative.toAdd.injective
          change (n : k)⁻¹ * (b 1).toAdd = 0
          rw [map_one]
          exact mul_zero _
        map_mul' := fun x y => by
          apply Multiplicative.toAdd.injective
          change (n : k)⁻¹ * (b (x * y)).toAdd =
            (n : k)⁻¹ * (b x).toAdd + (n : k)⁻¹ * (b y).toAdd
          rw [map_mul]
          exact mul_add _ _ _ }
    refine ⟨a, MonoidHom.ext fun y => ?_⟩
    have hh : p (f y) = e (y ^ n) := by
      apply Subtype.ext
      change f y ^ n = f (y ^ n)
      rw [map_pow]
    apply Multiplicative.toAdd.injective
    change (n : k)⁻¹ * (g (e.symm (p (f y)))).toAdd = (g y).toAdd
    rw [hh, e.symm_apply_apply, map_pow]
    change (n : k)⁻¹ * (n • (g y).toAdd) = (g y).toAdd
    rw [nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end SerreAndWeights


private theorem lieRing_eq_of_group_and_bracket {L : Type*} (r s : LieRing L)
    (ha : r.toAddCommGroup = s.toAddCommGroup) (hb : r.toBracket = s.toBracket) : r = s := by
  cases r
  cases s
  dsimp only at ha hb
  cases ha
  cases hb
  rfl

/-- The laws on dual-number points determine the identity Lie structure. -/
private theorem identityLieStructure_eq {G : GroupScheme k} [IsAffine G.X.left]
    (s t : IdentityLieStructure G) : s = t := by
  have hgroup : s.lieRing.toAddCommGroup = t.lieRing.toAddCommGroup :=
    AddCommGroup.toAddGroup_injective (s.group_law.trans t.group_law.symm)
  have hbr := identityLieBracketUnique k G _ _ s.commutator_law t.commutator_law
  have hbracket : s.lieRing.toBracket = t.lieRing.toBracket :=
    congrArg Bracket.mk hbr
  have hring := lieRing_eq_of_group_and_bracket s.lieRing t.lieRing hgroup hbracket
  rcases s with ⟨sR, sG, sK, sS, sB⟩
  rcases t with ⟨tR, tG, tK, tS, tB⟩
  dsimp only at hring
  subst tR
  have hLie : sK = tK := LieAlgebra.ext (sS.trans tS.symm)
  subst tK
  rfl

private theorem identityLieStructure_eq_canonical (G : AffineAlgebraicGroup k)
    (s : IdentityLieStructure G.val) : s = identityLieStructure G := by
  letI : IsAffine G.val.X.left := G.property.1
  exact identityLieStructure_eq s (identityLieStructure G)

section TorusTangents

open Specs.CharacterPairing (characterValue)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open LinearAlgebraicGroups.DiagonalizableGroups (groupAlgebraPointsIso)
open private value_for_presented_character from LinearAlgebraicGroups.RootData.SchemeCentre
open private characterUnit characterValue_eq_unit characterUnit_natural
  from LinearAlgebraicGroups.RootData.RootGroups

/-- Values of the characters identify the points of a split torus over
any test algebra. -/
private theorem torusPointCharacters {T : GroupScheme k} (hT : IsSplitTorus T)
    (R : TestAlgebra k) :
    ∃ e : GroupPoints T R ≃ (Character T →* Rˣ), e 1 = 1 ∧
      ∀ (t : GroupPoints T R) (χ : Character T), e t χ = characterUnit χ R t := by
  obtain ⟨_, a, ha⟩ := split_character_presentation hT
  let E := (groupPointsFunctor k).mapIso a.symm ≪≫ groupAlgebraPointsIso k (Character T)
  let e := MulEquiv.ofBijective (E.hom.app R).hom
    (ConcreteCategory.bijective_of_isIso (E.hom.app R))
  refine ⟨e.toEquiv, map_one e, fun t χ => Units.ext ?_⟩
  change ((show Character T →* Rˣ from
    (groupAlgebraPointsIso k (Character T)).hom.app R (t ≫ a.inv.hom.hom)) χ : R) =
      (characterUnit χ R t : R)
  rw [← value_for_presented_character a ha, characterValue_eq_unit]

private theorem infinitesimalUnit_injective :
    Function.Injective (infinitesimalUnit (k := k)) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  exact congrArg (fun w : (DualNumber k)ˣ => w.val.snd) hab

private theorem characterAtTangent {T : GroupScheme k} (χ : Character T) (v : Lie k T) :
    characterUnit χ (CommAlgCat.of k (DualNumber k)) v.toMul.val =
      infinitesimalUnit (Multiplicative.ofAdd
        (characterUnit χ (CommAlgCat.of k (DualNumber k)) v.toMul.val).val.snd) := by
  have h := characterUnit_natural χ (dualReduction k) v.toMul.val
  change characterUnit χ (CommAlgCat.of k k) (reduceTangentPoints T v.toMul.val) =
    Units.map _ _ at h
  rw [v.toMul.property] at h
  have h1 : characterUnit χ (CommAlgCat.of k k) (1 : GroupPoints T (CommAlgCat.of k k)) =
      1 := by
    unfold characterUnit
    rw [MonObj.one_comp, map_one]
  rw [h1] at h
  apply Units.ext
  apply TrivSqZeroExt.ext
  · exact congrArg Units.val h.symm
  · rfl

/-- The tangent to a split torus assigns to each character its coefficient
of the square-zero parameter. -/
private theorem torusTangentCharacters {T : GroupScheme k} (hT : IsSplitTorus T) :
    ∃ e : Lie k T ≃ (Character T →* Multiplicative k),
      ∀ (v : Lie k T) (χ : Character T),
        characterUnit χ (CommAlgCat.of k (DualNumber k)) v.toMul.val =
          infinitesimalUnit (e v χ) := by
  let D := CommAlgCat.of k (DualNumber k)
  let K := CommAlgCat.of k k
  obtain ⟨a, _, ha⟩ := torusPointCharacters hT D
  obtain ⟨b, hb₁, hb⟩ := torusPointCharacters hT K
  let f₀ (v : Lie k T) (χ : Character T) : Multiplicative k :=
    Multiplicative.ofAdd (a v.toMul.val χ).val.snd
  have hf₀ (v : Lie k T) (χ : Character T) :
      a v.toMul.val χ = infinitesimalUnit (f₀ v χ) := by
    unfold f₀
    rw [ha]
    exact characterAtTangent χ v
  let f (v : Lie k T) : Character T →* Multiplicative k :=
    { toFun := f₀ v
      map_one' := by
        apply infinitesimalUnit_injective
        rw [← hf₀, map_one, map_one]
      map_mul' := by
        intro χ ψ
        apply infinitesimalUnit_injective
        rw [map_mul infinitesimalUnit, ← hf₀, ← hf₀, ← hf₀, map_mul] }
  have hf (v : Lie k T) (χ : Character T) : a v.toMul.val χ = infinitesimalUnit (f v χ) :=
    hf₀ v χ
  have hinj : Function.Injective f := by
    intro u v h
    apply Additive.toMul.injective
    apply Subtype.ext
    apply a.injective
    apply MonoidHom.ext
    intro χ
    rw [hf, hf, h]
  have hsurj : Function.Surjective f := by
    intro g
    obtain ⟨z, hz⟩ := a.surjective (infinitesimalUnit.comp g)
    change a z = infinitesimalUnit.comp g at hz
    have hzχ (χ : Character T) : characterUnit χ D z = infinitesimalUnit (g χ) :=
      (ha z χ).symm.trans (DFunLike.congr_fun hz χ)
    have hred : reduceTangentPoints T z = 1 := by
      apply b.injective
      change b (reduceTangentPoints T z) = b 1
      rw [hb₁]
      apply MonoidHom.ext
      intro χ
      rw [hb]
      change characterUnit χ K (mapPoints (dualReduction k) z) = (1 : Kˣ)
      rw [characterUnit_natural, hzχ]
      rfl
    let v : Lie k T := Additive.ofMul ⟨z, hred⟩
    refine ⟨v, MonoidHom.ext fun χ => infinitesimalUnit_injective ?_⟩
    rw [← hf, ha]
    exact hzχ χ
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun v χ => (ha _ _).symm.trans (hf v χ)⟩

/-- A finite-index injection on split character lattices has invertible
differential in characteristic zero. -/
private theorem torusDifferential_bijective [CharZero k] {T S : GroupScheme k}
    (hT : IsSplitTorus T) (hS : IsSplitTorus S) (t : T ⟶ S)
    (a : Character S →* Character T) (ha : Function.Injective a)
    (hfin : Finite (Character T ⧸ a.range))
    (ht : ∀ χ : Character S, t ≫ χ = a χ) :
    Function.Bijective (mapPointKernel t) := by
  letI := hfin
  obtain ⟨e, he⟩ := torusTangentCharacters hT
  obtain ⟨f, hf⟩ := torusTangentCharacters hS
  have h (v : Lie k T) : f (mapPointKernel t v) = (e v).comp a := by
    apply MonoidHom.ext
    intro χ
    apply infinitesimalUnit_injective
    change infinitesimalUnit (f (mapPointKernel t v) χ) = infinitesimalUnit (e v (a χ))
    rw [← hf, ← he]
    unfold characterUnit
    have hcomp := congrArg (fun g : Character T => g.hom.hom) (ht χ)
    change (t.hom.hom ≫ χ.hom.hom) = (a χ).hom.hom at hcomp
    exact congrArg _ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hcomp))
  have hb := restrict_characters_to_additive_bijective (k := k) a ha
  constructor
  · intro x y hxy
    exact e.injective (hb.1 ((h x).symm.trans ((congrArg f hxy).trans (h y))))
  · intro y
    obtain ⟨g, hg⟩ := hb.2 (f y)
    obtain ⟨x, rfl⟩ := e.surjective g
    exact ⟨x, f.injective ((h x).trans hg)⟩

end TorusTangents

section LieWeights

open Specs.CharacterPairing (absoluteRoots adjointWeightSpace characterValue)
open Specs.AdjointRepresentation (TangentCoordinates)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open _root_.LinearAlgebraicGroups.RootData.CharacterPairing
  (adjointWeightSpaceVectors characterPairingComposition)
open private adjointWeightsInternal
  from LinearAlgebraicGroups.RootData.RootGroups
open private unitPointHom unitPointHom_apply from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open _root_.LinearAlgebraicGroups.CocharacterDynamics (mapPoints_unitPoint)

/-- The derivative of a cocharacter on the standard infinitesimal unit. -/
private def cocharacterTangent {T : GroupScheme k} (c : Cocharacter T) : Lie k T :=
  Additive.ofMul
    ⟨cocharacterPoint c (CommAlgCat.of k (DualNumber k))
      (infinitesimalUnit (Multiplicative.ofAdd 1)), by
      change mapPoints (dualReduction k) ((_ ≫ c.hom.hom) : GroupPoints T _) = 1
      rw [show (mapPoints (dualReduction k)
          (unitPoint (CommAlgCat.of k (DualNumber k))
            (infinitesimalUnit (Multiplicative.ofAdd (1 : k))) ≫ c.hom.hom)) =
          mapPoints (dualReduction k) (unitPoint (CommAlgCat.of k (DualNumber k))
            (infinitesimalUnit (Multiplicative.ofAdd (1 : k)))) ≫ c.hom.hom from
        (Category.assoc _ _ _).symm, mapPoints_unitPoint]
      have h : Units.map (dualReduction k).hom.toMonoidHom
          (infinitesimalUnit (Multiplicative.ofAdd (1 : k))) = 1 := Units.ext rfl
      rw [h, ← unitPointHom_apply, map_one, MonObj.one_comp]⟩

private abbrev corootTangent {G : GroupScheme k} (T : ClosedSubgroup G)
    (c : Cocharacter T.group) : Lie k G :=
  mapPointKernel T.inclusion (cocharacterTangent c)

private theorem pairing_mul {P : SplitBorelPair k} (D : AttachedDatum P)
    (χ ψ : Character P.T.group) (c : Cocharacter P.T.group) :
    pairing P.T.group (χ * ψ) c = pairing P.T.group χ c + pairing P.T.group ψ c := by
  letI := D.comm
  rw [← D.datum.pairing_eq, ← D.datum.pairing_eq χ c, ← D.datum.pairing_eq ψ c]
  change D.datum.rootDatum.toLinearMap (Additive.ofMul χ + Additive.ofMul ψ) (Additive.ofMul c) = _
  simp only [map_add, LinearMap.add_apply]

private theorem exists_pairing_ne {P : SplitBorelPair k} (D : AttachedDatum P)
    {χ ψ : Character P.T.group} (h : χ ≠ ψ) :
    ∃ c : Cocharacter P.T.group, pairing P.T.group χ c ≠ pairing P.T.group ψ c := by
  classical
  by_contra! he
  apply h
  apply Additive.ofMul.injective
  letI := D.comm
  apply D.datum.rootDatum.toPerfPair.injective
  ext c
  exact (D.datum.pairing_eq χ (Additive.toMul c)).trans
    ((he (Additive.toMul c)).trans (D.datum.pairing_eq ψ (Additive.toMul c)).symm)

/-- In characteristic zero the integral torus characters are separated
by the infinitesimal actions of the cocharacters. -/
private theorem weight_iff_corootTangents [CharZero k] (P : SplitBorelPair k)
    (D : AttachedDatum P) (s : IdentityLieStructure P.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI : AddCommGroup (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup
    letI : Module k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule
    letI : SMul k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
    letI : Zero (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup.toZero
    letI : SMul ℤ (Specs.Lie k P.G.val) := s.lieRing.toSubNegMonoid.toZSMul.toSMul
    ∀ (χ : Character P.T.group) (v : Lie k P.G.val),
      v ∈ adjointWeightVectors P.T χ ↔
        ∀ (c : Cocharacter P.T.group), ⁅corootTangent P.T c, v⁆ = (pairing P.T.group χ c : k) • v := by
  have hCanonical_s := identityLieStructure_eq_canonical P.G s
  subst s
  let s := identityLieStructure P.G
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : AddCommGroup (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup
  letI : Module k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule
  letI : SMul k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  letI : Zero (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup.toZero
  letI : SMul ℤ (Specs.Lie k P.G.val) := s.lieRing.toSubNegMonoid.toZSMul.toSMul
  obtain ⟨_, b, C, L, l, Ad, hAd, hbr, _⟩ :=
    _root_.LinearAlgebraicGroups.adjointRepresentation k P.G s
  let W (χ : Character P.T.group) := adjointWeightSpace P.T χ s
  have hW := adjointWeightsInternal P.G P.T P.split s
  have hmem (χ : Character P.T.group) (v : Lie k P.G.val) :
      v ∈ W χ ↔ v ∈ adjointWeightVectors P.T χ :=
    Set.ext_iff.mp (adjointWeightSpaceVectors P.G P.T s χ) v
  have he (χ : Character P.T.group) (v : Lie k P.G.val)
      (hv : v ∈ adjointWeightVectors P.T χ) (c : Cocharacter P.T.group) :
      ⁅corootTangent P.T c, v⁆ = (pairing P.T.group χ c : k) • v := by
    apply b.equivFun.injective
    rw [map_smul]
    exact lie_coroot_weight C l Ad hAd hbr P.T c χ _ v hv rfl
  intro χ v
  refine ⟨he χ v, fun hv => (hmem χ v).mp ?_⟩
  apply mem_weight_of_eigenvalues W hW
    (fun c => LieAlgebra.ad k (Lie k P.G.val) (corootTangent P.T c))
    (fun ψ c => (pairing P.T.group ψ c : k))
    (fun ψ c w => he ψ w.val ((hmem ψ w.val).mp w.property) c) χ _ v hv
  intro ψ hψ _
  obtain ⟨c, hc⟩ := exists_pairing_ne D hψ
  exact ⟨c, fun h => hc (Int.cast_injective h)⟩

private theorem lieBracket_weight [CharZero k] (P : SplitBorelPair k)
    (D : AttachedDatum P) (s : IdentityLieStructure P.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI : AddCommGroup (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup
    letI : Module k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule
    letI : SMul k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
    letI : Zero (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup.toZero
    letI : SMul ℤ (Specs.Lie k P.G.val) := s.lieRing.toSubNegMonoid.toZSMul.toSMul
    ∀ {χ ψ : Character P.T.group} {v w : Lie k P.G.val},
      v ∈ adjointWeightVectors P.T χ → w ∈ adjointWeightVectors P.T ψ →
      ⁅v, w⁆ ∈ adjointWeightVectors P.T (χ * ψ) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : AddCommGroup (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup
  letI : Module k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule
  letI : SMul k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  letI : Zero (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup.toZero
  letI : SMul ℤ (Specs.Lie k P.G.val) := s.lieRing.toSubNegMonoid.toZSMul.toSMul
  intro χ ψ v w hv hw
  apply (weight_iff_corootTangents P D s _ _).mpr
  intro c
  with_unfolding_all
    rw [LieRing.leibniz_lie, (weight_iff_corootTangents P D s _ _).mp hv c,
    (weight_iff_corootTangents P D s _ _).mp hw c, pairing_mul D,
    Int.cast_add, smul_lie, lie_smul, add_smul]

private theorem weight_zero_of_not_root {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} {χ : Character T.group} {v : Lie k G.val}
    (hχ : χ ≠ 1) (hroot : χ ∉ absoluteRoots T) (hv : v ∈ adjointWeightVectors T χ) :
    v = 0 := by
  classical
  by_contra hn
  exact hroot ⟨hχ, v, hv, hn⟩

end LieWeights

section RootStrings

open Specs.CharacterPairing (absoluteRoots)
open scoped Matrix
open private canonicalZero_eq from LinearAlgebraicGroups.RootData.CharacterPairing

/-- Iterating the adjoint action of one eigenvector shifts a weight by
the corresponding integer multiple of its character. -/
private theorem ad_pow_weight [CharZero k] (P : SplitBorelPair k) (D : AttachedDatum P)
    (s : IdentityLieStructure P.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI : AddCommGroup (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup
    letI : Module k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule
    letI : SMul k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
    letI : Zero (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup.toZero
    letI : SMul ℤ (Specs.Lie k P.G.val) := s.lieRing.toSubNegMonoid.toZSMul.toSMul
    ∀ {χ ψ : Character P.T.group} {x y : Lie k P.G.val},
      x ∈ adjointWeightVectors P.T χ → y ∈ adjointWeightVectors P.T ψ →
      ∀ n : ℕ, (LieAlgebra.ad k (Lie k P.G.val) x ^ n) y ∈
        adjointWeightVectors P.T (χ ^ n * ψ) := by
  have hCanonical_s := identityLieStructure_eq_canonical P.G s
  subst s
  let s := identityLieStructure P.G
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : AddCommGroup (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup
  letI : Module k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule
  letI : SMul k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  letI : Zero (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup.toZero
  letI : SMul ℤ (Specs.Lie k P.G.val) := s.lieRing.toSubNegMonoid.toZSMul.toSMul
  intro χ ψ x y hx hy n
  induction n with
  | zero => simpa only [pow_zero, one_mul, Module.End.one_apply] using hy
  | succ n ih =>
    simpa only [pow_succ', mul_assoc, Module.End.mul_apply, LieAlgebra.ad_apply] using
      lieBracket_weight P D s hx ih

private theorem ad_pow_succ_apply {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (x y : L) (n : ℕ) :
    (LieAlgebra.ad K L x ^ (n + 1)) y = (LieAlgebra.ad K L x ^ n) ⁅x, y⁆ := by
  rw [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply]

/-- The first character above a simple root string, in either sign, is
nontrivial and is not a root. -/
private theorem simpleString_end {P : SplitBorelPair k} (D : AttachedDatum P) :
    letI := D.comm
    ∀ (i j : D.base.support), i ≠ j →
    let n := (-integralCartan D.datum.rootDatum D.base i j).toNat + 1
    let χ := i.val.val ^ n * j.val.val
    (χ ≠ 1 ∧ χ ∉ absoluteRoots P.T) ∧ (χ⁻¹ ≠ 1 ∧ χ⁻¹ ∉ absoluteRoots P.T) := by
  letI := D.comm
  letI := D.datum.finiteRoots
  intro i j hij
  let R := D.datum.rootDatum
  let n := (-integralCartan R D.base i j).toNat + 1
  let χ := i.val.val ^ n * j.val.val
  change (χ ≠ 1 ∧ χ ∉ absoluteRoots P.T) ∧ (χ⁻¹ ≠ 1 ∧ χ⁻¹ ∉ absoluteRoots P.T)
  have hli := D.base.linearIndependent_pair_of_ne hij
  have hn : n = R.chainTopCoeff i j + 1 := by
    unfold n integralCartan
    have hs := congrArg Int.toNat (D.base.chainTopCoeff_eq_of_ne hij)
    have hp := R.algebraMap_pairingIn ℤ j i
    rw [Algebra.algebraMap_self, RingHom.id_apply] at hp
    rw [hp] at hs
    simpa only [Int.toNat_natCast] using congrArg (fun m : ℕ => m + 1) hs.symm
  have hmem : R.root j + n • R.root i ∉ Set.range R.root := by
    rw [R.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli, hn]
    exact Nat.not_succ_le_self _
  have hχ : Additive.ofMul χ = R.root j + n • R.root i := by
    rw [D.datum.root_eq, D.datum.root_eq]
    change (n • Additive.ofMul i.val.val) + Additive.ofMul j.val.val =
      Additive.ofMul j.val.val + n • Additive.ofMul i.val.val
    exact add_comm _ _
  have hχ₀ : χ ≠ 1 := by
    intro h
    rw [h] at hχ
    have hzero : (n : ℤ) • R.root i + (1 : ℤ) • R.root j = 0 := by
      rw [one_smul, natCast_zsmul, add_comm]
      exact hχ.symm
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hli) _ _ hzero).2
  refine ⟨⟨hχ₀, ?_⟩, ⟨fun h => hχ₀ (inv_eq_one.mp h), ?_⟩⟩
  · intro hr
    exact hmem ⟨⟨χ, hr⟩, (D.datum.root_eq ⟨χ, hr⟩).trans hχ⟩
  · intro hr
    apply hmem
    apply (R.neg_mem_range_root_iff).mp
    refine ⟨⟨χ⁻¹, hr⟩, ?_⟩
    rw [← hχ, D.datum.root_eq]
    rfl

/-- A difference of two distinct simple roots is neither zero nor a root. -/
private theorem simpleDifference_not_root {P : SplitBorelPair k}
    (D : AttachedDatum P) :
    letI := D.comm
    ∀ (i j : D.base.support), i ≠ j →
      i.val.val * j.val.val⁻¹ ≠ 1 ∧ i.val.val * j.val.val⁻¹ ∉ absoluteRoots P.T := by
  letI := D.comm
  intro i j hij
  constructor
  · intro h
    exact hij (Subtype.ext (Subtype.ext (mul_inv_eq_one.mp h)))
  · intro h
    apply D.base.sub_notMem_range_root i.property j.property
    refine ⟨⟨_, h⟩, ?_⟩
    rw [D.datum.root_eq, D.datum.root_eq, D.datum.root_eq]
    rfl

/-- A simple pair of opposite weights has the Serre relations once its
bracket has been normalized to the attached coroot tangent. -/
private theorem serreRelationsForTriples [CharZero k] (P : SplitBorelPair k)
    (D : AttachedDatum P) (s : IdentityLieStructure P.G.val) :
    letI := D.comm
    letI := Classical.decEq D.base.support
    letI := s.lieRing
    letI := s.lieAlgebra
    letI : AddCommGroup (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup
    letI : Module k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule
    letI : SMul k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
    letI : Zero (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup.toZero
    letI : SMul ℤ (Specs.Lie k P.G.val) := s.lieRing.toSubNegMonoid.toZSMul.toSMul
    ∀ (e f : D.base.support → Lie k P.G.val),
    let L := Lie k P.G.val
    let A := integralCartan D.datum.rootDatum D.base
    let H := fun i : D.base.support => corootTangent P.T (attachedCoroot D i.val)
    (∀ i, e i ∈ adjointWeightVectors P.T i.val.val) →
    (∀ i, f i ∈ adjointWeightVectors P.T i.val.val⁻¹) →
    (∀ i, ⁅e i, f i⁆ = H i) →
      (∀ i j, ⁅H i, H j⁆ = 0) ∧
      (∀ i j, ⁅e i, f j⁆ = if i = j then H i else 0) ∧
      (∀ i j, ⁅H i, e j⁆ = A i j • e j) ∧
      (∀ i j, ⁅H i, f j⁆ = -(A i j • f j)) ∧
      (∀ i j, (LieAlgebra.ad k L (e i) ^ (-A i j).toNat) ⁅e i, e j⁆ = 0) ∧
      (∀ i j, (LieAlgebra.ad k L (f i) ^ (-A i j).toNat) ⁅f i, f j⁆ = 0) := by
  classical
  letI := D.comm
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : AddCommGroup (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup
  letI : Module k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule
  letI : SMul k (Specs.Lie k P.G.val) := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  letI : Zero (Specs.Lie k P.G.val) := s.lieRing.toAddCommGroup.toZero
  letI : SMul ℤ (Specs.Lie k P.G.val) := s.lieRing.toSubNegMonoid.toZSMul.toSMul
  intro e f L A H he hf hEF
  have hpair (i j : D.base.support) :
      pairing P.T.group j.val.val (attachedCoroot D i.val) = A i j := by
    change _ = D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root j.val)
      (D.datum.rootDatum.coroot i.val)
    rw [D.datum.root_eq, ← D.datum.pairing_eq]
    rfl
  have htorus (i : D.base.support) : H i ∈ adjointWeightVectors P.T 1 :=
    (LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups P.G P.reductive P.T P.split
      P.maximal).1.2 ▸ ⟨cocharacterTangent (attachedCoroot D i.val), rfl⟩
  have h1 (c : Cocharacter P.T.group) : pairing P.T.group 1 c = 0 := by
    rw [← D.datum.pairing_eq]
    change D.datum.rootDatum.toLinearMap 0 (Additive.ofMul c) = 0
    simp
  have hinv (χ : Character P.T.group) (c : Cocharacter P.T.group) :
      pairing P.T.group χ⁻¹ c = -pairing P.T.group χ c := by
    rw [← D.datum.pairing_eq, ← D.datum.pairing_eq χ c]
    change D.datum.rootDatum.toLinearMap (-Additive.ofMul χ) (Additive.ofMul c) = _
    rw [map_neg, LinearMap.neg_apply]
  have hzero := canonicalZero_eq s
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_,
    fun i j => ?_, fun i j => ?_⟩
  · with_unfolding_all
      rw [(weight_iff_corootTangents P D s _ _).mp (htorus j), h1, Int.cast_zero, zero_smul]
  · by_cases h : i = j
    · subst j
      simpa only [ite_true] using hEF i
    · rw [ite_eq_right h]
      obtain ⟨h₁, h₂⟩ := simpleDifference_not_root D i j h
      exact (weight_zero_of_not_root h₁ h₂ (lieBracket_weight P D s (he i) (hf j))).trans hzero
  · with_unfolding_all
      rw [(weight_iff_corootTangents P D s _ _).mp (he j), hpair, Int.cast_smul_eq_zsmul k]
  · with_unfolding_all
      rw [(weight_iff_corootTangents P D s _ _).mp (hf j), hinv, hpair, Int.cast_neg,
        neg_smul, Int.cast_smul_eq_zsmul k]
      exact congrArg (fun a : AddGroup (Lie k P.G.val) =>
        a.toNeg.neg (A i j • f j)) s.group_law
  · by_cases h : i = j
    · subst j
      with_unfolding_all rw [lie_self, map_zero]
    · obtain ⟨⟨h₁, h₂⟩, _⟩ := simpleString_end D i j h
      have hw := ad_pow_weight P D s (he i) (he j) ((-A i j).toNat + 1)
      rw [ad_pow_succ_apply] at hw
      exact (weight_zero_of_not_root h₁ h₂ hw).trans hzero
  · by_cases h : i = j
    · subst j
      with_unfolding_all rw [lie_self, map_zero]
    · obtain ⟨_, ⟨h₁, h₂⟩⟩ := simpleString_end D i j h
      have hw := ad_pow_weight P D s (hf i) (hf j) ((-A i j).toNat + 1)
      rw [ad_pow_succ_apply, inv_pow, ← mul_inv] at hw
      exact (weight_zero_of_not_root h₁ h₂ hw).trans hzero

end RootStrings

section RankOneLie

open scoped Matrix Polynomial
open Polynomial
open Specs.RootGroups (CorootReflection HasScalarAction IsRootSubgroup rankOneWord)
open Specs.CharacterPairing (absoluteRoots adjointWeightSpace characterValue)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.AdjointRepresentation (TangentCoordinates conjugate)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private unitPointHom unitPointHom_apply from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open Specs.StandardGroups (generalLinearPoints)
open InfinitesimalCommutator (matrixDifferential)
open private rootPoint_comp rootPoint_natural rootPoint_zero rootPoint_eps_reduces
  rootPoint_injective_of_mono characterUnit characterValue_eq_unit
  cocharacterPoint_inv conjugation_by_word rankOneWord_natural
  from LinearAlgebraicGroups.RootData.RootGroups
open private comp_pointConj mapPoints_pointConj pointConj from LinearAlgebraicGroups.RootData.AbstractPairing

private abbrev baseTest (k : Type u) [Field k] := CommAlgCat.of k k
private abbrev dualTest (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)

private def rootTangent {A : AdditiveLine k} {G : GroupScheme k} (x : A.group ⟶ G) :
    Lie k G :=
  Additive.ofMul ⟨rootPoint x (dualTest k) DualNumber.eps, rootPoint_eps_reduces x⟩

private theorem rootTangent_comp {A : AdditiveLine k} {G H : GroupScheme k}
    (x : A.group ⟶ G) (f : G ⟶ H) :
    rootTangent (x ≫ f) = mapPointKernel f (rootTangent x) := by
  apply Additive.toMul.injective
  exact Subtype.ext (rootPoint_comp x f (dualTest k) DualNumber.eps)

private theorem rootTangent_ne_zero {A : AdditiveLine k} {G : GroupScheme k} (x : A.group ⟶ G)
    [Mono x.hom.hom] : rootTangent x ≠ 0 := by
  intro h
  have hz := congrArg (fun v : Lie k G => v.toMul.val) h
  change rootPoint x (dualTest k) DualNumber.eps = 1 at hz
  rw [← rootPoint_zero x (dualTest k)] at hz
  have he := rootPoint_injective_of_mono x _ hz
  exact one_ne_zero (congrArg (fun z : DualNumber k => z.snd) he)

private theorem rootTangent_weight {A : AdditiveLine k} {G : GroupScheme k}
    {T U : ClosedSubgroup G} {χ : Character T.group} (x : A.group ⟶ U.group)
    (hU : IsRootSubgroup T U χ) :
    rootTangent (x ≫ U.inclusion) ∈ adjointWeightVectors T χ := by
  rw [rootTangent_comp]
  exact hU.2.2.2 ⟨_, rfl⟩

/-- Conjugating an identity tangent by a rational point gives another
identity tangent. -/
private def conjugateTangent {G : GroupScheme k} (g : GroupPoints G (baseTest k))
    (v : Lie k G) : Lie k G := by
  let z := constantPoints G (baseTest k) g
  let p := z * v.toMul.val * z⁻¹
  have hp : reduceTangentPoints G p = 1 := by
    change reducePoints G (baseTest k) (z * v.toMul.val * z⁻¹) = 1
    rw [map_mul, map_mul, map_inv]
    change reducePoints G (baseTest k) (constantPoints G (baseTest k) g) *
      reduceTangentPoints G v.toMul.val *
      (reducePoints G (baseTest k) (constantPoints G (baseTest k) g))⁻¹ = 1
    rw [reduce_constant, v.toMul.property, mul_one, mul_inv_cancel]
  exact Additive.ofMul (⟨p, hp⟩ : (reduceTangentPoints G).ker)

private theorem conjugateTangent_mul {G : GroupScheme k}
    (g h : GroupPoints G (baseTest k)) (v : Lie k G) :
    conjugateTangent (g * h) v = conjugateTangent g (conjugateTangent h v) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change constantPoints G (baseTest k) (g * h) * v.toMul.val *
      (constantPoints G (baseTest k) (g * h))⁻¹ =
    constantPoints G (baseTest k) g *
      (constantPoints G (baseTest k) h * v.toMul.val *
        (constantPoints G (baseTest k) h)⁻¹) * (constantPoints G (baseTest k) g)⁻¹
  rw [map_mul]
  group

/-- A subspace preserved by the bracket with a root tangent is preserved by
the corresponding root group. The induced action fixes the class of any
vector whose bracket with that tangent belongs to the subspace. -/
private theorem rootConjugation_sub_mem [CharZero k] (G : AffineAlgebraicGroup k)
    (s : IdentityLieStructure G.val) {A : AdditiveLine k} (x : A.group ⟶ G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (W : Submodule k (Lie k G.val)), (∀ v ∈ W, ⁅rootTangent x, v⁆ ∈ W) →
      ∀ (v : Lie k G.val), ⁅rootTangent x, v⁆ ∈ W → ∀ t : k,
        conjugateTangent (rootPoint x (baseTest k) t) v - v ∈ W := by
  have hCanonical_s := identityLieStructure_eq_canonical G s
  subst s
  let s := identityLieStructure G
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : AddCommGroup (Lie k G.val) := s.lieRing.toAddCommGroup
  letI : Module k (Lie k G.val) := s.lieAlgebra.toModule
  intro W hW v hv t
  obtain ⟨_, b, C, L, l, Ad, hAd, hbr, _⟩ := _root_.LinearAlgebraicGroups.adjointRepresentation k G s
  let U := CommAlgCat.of k (Polynomial k)
  let P := rootMatrix (x ≫ Ad) l U Polynomial.X
  let D := matrixDifferential Ad l (rootTangent x)
  have he (R : TestAlgebra k) (a : R) : rootMatrix (x ≫ Ad) l R a = P.map (aeval a) := by
    let f : U ⟶ R := CommAlgCat.ofHom (aeval a)
    have hx : f.hom Polynomial.X = a := Polynomial.aeval_X a
    change rootMatrix (x ≫ Ad) l R a = P.map f.hom
    simpa only [hx] using rootMatrix_natural (x ≫ Ad) l f (Polynomial.X : U)
  have h0 : P.map (fun p => p.coeff 0) = 1 := by
    have h := (he (baseTest k) 0).symm
    rw [rootMatrix, rootPoint_zero, map_one] at h
    ext i j
    change (P i j).coeff 0 = (1 : Matrix _ _ k) i j
    rw [coeff_zero_eq_aeval_zero]
    exact congrArg (fun M : Matrix _ _ k => M i j) h
  have hD : P.map (fun p => p.coeff 1) = D := by
    have h := he (dualTest k) DualNumber.eps
    ext i j
    have h' := congrArg (fun M : Matrix _ _ (DualNumber k) => (M i j).snd) h
    have hx : (mapPointKernel Ad (rootTangent x)).toMul.val =
        rootPoint (x ≫ Ad) (dualTest k) DualNumber.eps := (rootPoint_comp _ _ _ _).symm
    change (((l.hom.app (dualTest k)).hom
      (rootPoint (x ≫ Ad) (dualTest k) DualNumber.eps)).val i j).snd =
        ((aeval (DualNumber.eps : DualNumber k)) (P i j)).snd at h'
    rw [← hx] at h'
    change D i j = ((aeval (DualNumber.eps : DualNumber k)) (P i j)).snd at h'
    change (P i j).coeff 1 = D i j
    rw [h']
    rw [show (DualNumber.eps : DualNumber k) = (⟨0, 1⟩ : DualNumber k) from rfl,
      aeval_dual_number]
    simpa only [TrivSqZeroExt.snd, one_mul, ← coeff_zero_eq_aeval_zero,
      coeff_derivative, Nat.cast_zero, zero_add, Nat.cast_one, mul_one]
  have hode : P.map derivative = P * D.map Polynomial.C := by
    rw [← hD]
    apply polynomial_additive_matrix_differential
    intro a b
    let V := CommAlgCat.of k (DualNumber U)
    simpa only [he V] using rootMatrix_add (x ≫ Ad) l V a b
  let E := b.equivFun
  let M := W.map E.toLinearMap
  have hm (z : Lie k G.val) : E z ∈ M ↔ z ∈ W := by
    constructor
    · rintro ⟨y, hy, h⟩
      exact E.injective h ▸ hy
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hDP (p : _ → k) (hp : p ∈ M) : D *ᵥ p ∈ M := by
    obtain ⟨z, rfl⟩ := E.surjective p
    rw [hbr]
    exact (hm _).mpr (hW z ((hm z).mp hp))
  have hh := polynomial_matrix_displacement_mem P D h0 hode M hDP (E v)
    (show D *ᵥ E v ∈ M from (hbr _ _).symm ▸ (hm _).mpr hv) t
  rw [← he (baseTest k) t] at hh
  have hconj : E (conjugateTangent (rootPoint x (baseTest k) t) v) =
      (rootMatrix (x ≫ Ad) l (baseTest k) t) *ᵥ E v := by
    apply (C.equiv (baseTest k)).injective
    apply Additive.toMul.injective
    apply Subtype.ext
    change (C.equiv (baseTest k) (E (conjugateTangent (rootPoint x (baseTest k) t) v))).toMul.val =
      (C.equiv (baseTest k) (rootMatrix (x ≫ Ad) l (baseTest k) t *ᵥ E v)).toMul.val
    rw [C.at_base]
    have hh := hAd (baseTest k) (rootPoint x (baseTest k) t) (E v)
    change (C.equiv (baseTest k)
      (((l.hom.app _).hom (rootPoint x (baseTest k) t ≫ Ad.hom.hom)).val *ᵥ E v)).toMul.val =
      conjugate (rootPoint x (baseTest k) t) (C.equiv (baseTest k) (E v)) at hh
    let z := constantPoints G.val (baseTest k) (rootPoint x (baseTest k) t)
    change _ = z * (C.equiv (baseTest k) (b.equivFun v)).toMul.val * z⁻¹ at hh
    rw [C.at_base v] at hh
    change z * v.toMul.val * z⁻¹ =
      (C.equiv (baseTest k) (rootMatrix (x ≫ Ad) l (baseTest k) t *ᵥ E v)).toMul.val
    simpa only [rootMatrix, rootPoint_comp] using hh.symm
  rw [← hconj] at hh
  apply (hm _).mp
  have hs : E (conjugateTangent (rootPoint x (baseTest k) t) v - v) =
      E (conjugateTangent (rootPoint x (baseTest k) t) v) - E v :=
    E.toLinearMap.map_sub _ _
  rw [hs]
  exact hh

private theorem attachedCoordinates {P : SplitBorelPair k} (D : AttachedDatum P)
    (α : Root P.T) :
    ∃ (U V : ClosedSubgroup P.G.val) (A : AdditiveLine k)
      (x : A.group ≅ U.group) (y : A.group ≅ V.group),
      IsRootSubgroup P.T U α.val ∧ IsRootSubgroup P.T V α.val⁻¹ ∧
      HasScalarAction P.T α.val (x.hom ≫ U.inclusion) ∧
      HasScalarAction P.T α.val⁻¹ (y.hom ≫ V.inclusion) ∧
      ∃ r : CorootReflection P.T α.val (x.hom ≫ U.inclusion) (y.hom ≫ V.inclusion),
        r.coroot = attachedCoroot D α := by
  letI := D.comm
  obtain ⟨C, c, _, _, Ppos, Pneg, _, Q, F, a, A, x, y, hU, hV, h⟩ := D.datum.attached α
  dsimp only at h
  obtain ⟨hx, hy, r, hr⟩ := h
  let U := subgroupOfSubgroup C.subgroup Ppos.contracting
  let V := subgroupOfSubgroup C.subgroup Pneg.contracting
  refine ⟨U, V, A, x.root, y.root, hU, hV, hx, hy, r, hr⟩

private theorem oppositeRoot_value {P : SplitBorelPair k} (D : AttachedDatum P)
    (α : Root P.T) :
    letI := D.comm
    (D.datum.rootDatum.reflectionPerm α α).val = α.val⁻¹ := by
  letI := D.comm
  apply Additive.ofMul.injective
  rw [← D.datum.root_eq, D.datum.rootDatum.root_reflectionPerm, RootPairing.reflection_apply_self,
    D.datum.root_eq]
  rfl

private theorem rootLine_eq_span {P : SplitBorelPair k} (s : IdentityLieStructure P.G.val)
    (α : Root P.T) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ v : Lie k P.G.val, v ∈ adjointWeightVectors P.T α.val → v ≠ 0 →
      adjointWeightSpace P.T α.val s = k ∙ v := by
  have hCanonical_s := identityLieStructure_eq_canonical P.G s
  subst s
  let s := identityLieStructure P.G
  letI := s.lieRing
  letI := s.lieAlgebra
  intro v hv h₀
  obtain ⟨_, b, _⟩ := tangent_coordinates P.G s
  letI : Module.Finite k (Lie k P.G.val) := Module.Finite.of_basis b
  have hdim := (LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups P.G P.reductive
    P.T P.split P.maximal).2 α.val α.property |>.1 s
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span hv)
  · rw [hdim, finrank_span_singleton h₀]

private theorem constantPoint_extend {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (R : TestAlgebra k) :
    mapPoints (CommAlgCat.ofHom (Algebra.ofId k R))
        (toUnit _ ≫ g : GroupPoints G (baseTest k)) = (toUnit _ ≫ g : GroupPoints G R) := by
  unfold mapPoints
  rw [← Category.assoc]
  congr 1
  exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _

private theorem conjugateTangent_point {G : GroupScheme k} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (v : Lie k G) :
    (conjugateTangent (G := G) (toUnit _ ≫ g) v).toMul.val =
      pointConj (G := G) (S := (testSpec k).obj (op (dualTest k))) g v.toMul.val := by
  let n₀ : GroupPoints G (baseTest k) := toUnit _ ≫ g
  let n₁ : GroupPoints G (dualTest k) := toUnit _ ≫ g
  have hn : constantPoints G (baseTest k) n₀ = n₁ := constantPoint_extend g (dualTest k)
  change constantPoints G (baseTest k) n₀ * v.toMul.val *
      (constantPoints G (baseTest k) n₀)⁻¹ = n₁ * v.toMul.val * n₁⁻¹
  rw [hn]

private theorem word_reflects_coroot {G : GroupScheme k} {T : ClosedSubgroup G}
    {χ : Character T.group} {A : AdditiveLine k} {x y : A.group ⟶ G}
    (R : CorootReflection T χ x y) (hx : HasScalarAction T χ x)
    (hy : HasScalarAction T χ⁻¹ y) :
    conjugateTangent (rankOneWord x y (baseTest k) 1) (corootTangent T R.coroot) =
      -corootTangent T R.coroot := by
  let S := dualTest k
  let b : Sˣ := infinitesimalUnit (Multiplicative.ofAdd 1)
  let t := cocharacterPoint R.coroot S b
  have hrep (B : TestAlgebra k) : (toUnit _ ≫ R.representative : GroupPoints G B) =
      rankOneWord x y B 1 := by
    have h := congrArg (mapPoints (CommAlgCat.ofHom (Algebra.ofId k B))) R.representative_word
    rw [constantPoint_extend, rankOneWord_natural, map_one] at h
    exact h
  have hval : characterUnit χ S t = b ^ (2 : ℤ) := by
    apply Units.ext
    rw [← characterValue_eq_unit, (LinearAlgebraicGroups.RootData.CharacterPairing.characterPairingComposition T.group χ R.coroot).2 S b, R.root_pairing]
  have h := conjugation_by_word T χ hx hy R.coroot R.representative hrep R.coroot_word S t
  dsimp only at h
  rw [hval] at h
  let m : GroupPoints G S := t ≫ T.inclusion.hom.hom
  have hcoe :
      (cocharacterPoint R.coroot S (b ^ (2 : ℤ)) ≫ T.inclusion.hom.hom) =
        m ^ (2 : ℤ) := by
    let a := (((groupPointsFunctor k).map (R.coroot ≫ T.inclusion)).app S).hom.comp (unitPointHom S)
    have ha (u : Sˣ) : a u = cocharacterPoint R.coroot S u ≫ T.inclusion.hom.hom := by
      change unitPointHom S u ≫ (R.coroot ≫ T.inclusion).hom.hom = _
      rw [unitPointHom_apply, Grp.comp_hom_hom, ← Category.assoc]
      rfl
    change _ = (t ≫ T.inclusion.hom.hom : GroupPoints G S) ^ (2 : ℤ)
    rw [← ha, show t = cocharacterPoint R.coroot S b from rfl, ← ha]
    exact a.map_zpow b 2
  let n : GroupPoints G S := toUnit _ ≫ R.representative
  have hn : n * m * n⁻¹ = (m ^ (2 : ℤ))⁻¹ * m := by
    rw [hcoe] at h
    exact h
  have h' : n * m * n⁻¹ = m⁻¹ := by
    rw [hn, zpow_ofNat, pow_two]
    group
  rw [← R.representative_word]
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [conjugateTangent_point]
  exact h'

/-- The attached coroot is the bracket of the pinned vector and a suitably
normalized opposite vector. -/
private theorem pinnedLieTriple [CharZero k] {A : AdditiveLine k} (P : PinnedGroup A)
    (D : AttachedDatum P.pair) (s : IdentityLieStructure P.pair.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ α : SimpleRoot P.pair,
    let x := rootTangent ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion)
    let h := corootTangent P.pair.T (attachedCoroot D α.val)
    x ∈ adjointWeightVectors P.pair.T α.val.val ∧ x ≠ 0 ∧
      ∃ y ∈ adjointWeightVectors P.pair.T α.val.val⁻¹, y ≠ 0 ∧ ⁅x, y⁆ = h := by
  have hCanonical_s := identityLieStructure_eq_canonical P.pair.G s
  subst s
  let s := identityLieStructure P.pair.G
  classical
  letI := D.comm
  letI := s.lieRing
  letI := s.lieAlgebra
  intro α x h
  let T := P.pair.T
  let G := P.pair.G
  let a := α.val.val
  let x₀ := (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion
  have hx : x ∈ adjointWeightVectors T a :=
    rootTangent_weight (P.pin α).val.hom (P.roots α.val).property
  have hxn : x ≠ 0 := by
    have : Mono ((P.roots α.val).val.inclusion.hom.hom) :=
      mono_over _ (P.roots α.val).val.isClosedImmersion
    change rootTangent x₀ ≠ 0
    have : Mono x₀.hom.hom := by
      change Mono ((P.pin α).val.hom.hom.hom ≫ (P.roots α.val).val.inclusion.hom.hom)
      infer_instance
    exact rootTangent_ne_zero x₀
  refine ⟨hx, hxn, ?_⟩
  obtain ⟨U, V, B, p, n, hU, hV, hp, hn, r, hr⟩ := attachedCoordinates D α.val
  let p₀ := p.hom ≫ U.inclusion
  let n₀ := n.hom ≫ V.inclusion
  let X := rootTangent p₀
  let Y := rootTangent n₀
  have hxw : X ∈ adjointWeightVectors T a := rootTangent_weight p.hom hU
  have hyw : Y ∈ adjointWeightVectors T a⁻¹ := rootTangent_weight n.hom hV
  have hx₀ : X ≠ 0 := by
    have : Mono U.inclusion.hom.hom := mono_over _ U.isClosedImmersion
    have : Mono p₀.hom.hom := by
      change Mono (p.hom.hom.hom ≫ U.inclusion.hom.hom)
      infer_instance
    exact rootTangent_ne_zero p₀
  have hy₀ : Y ≠ 0 := by
    have : Mono V.inclusion.hom.hom := mono_over _ V.isClosedImmersion
    have : Mono n₀.hom.hom := by
      change Mono (n.hom.hom.hom ≫ V.inclusion.hom.hom)
      infer_instance
    exact rootTangent_ne_zero n₀
  have hi : pairing T.group a (attachedCoroot D α.val) = 2 := by
    rw [← hr]
    exact r.root_pairing
  have hinv : pairing T.group a⁻¹ (attachedCoroot D α.val) = -2 := by
    have hg := pairing_mul D a a⁻¹ (attachedCoroot D α.val)
    rw [mul_inv_cancel, hi] at hg
    have hz : pairing T.group 1 (attachedCoroot D α.val) = 0 := by
      rw [← D.datum.pairing_eq]
      change D.datum.rootDatum.toLinearMap 0 _ = 0
      simp
    rw [hz] at hg
    change 0 = 2 + pairing T.group a⁻¹ (attachedCoroot D α.val) at hg
    omega
  have hHx : ⁅h, X⁆ = (2 : k) • X := by
    have h' := (weight_iff_corootTangents P.pair D s _ _).mp hxw (attachedCoroot D α.val)
    change ⁅h, X⁆ = (pairing T.group a (attachedCoroot D α.val) : k) • X at h'
    rw [hi] at h'
    simpa only [Int.cast_ofNat] using h'
  have hHy : ⁅h, Y⁆ = (-2 : k) • Y := by
    have h' := (weight_iff_corootTangents P.pair D s _ _).mp hyw (attachedCoroot D α.val)
    change ⁅h, Y⁆ = (pairing T.group a⁻¹ (attachedCoroot D α.val) : k) • Y at h'
    rw [hinv] at h'
    simpa only [Int.cast_neg, Int.cast_ofNat] using h'
  have hH₀ : h ≠ 0 := by
    intro hz
    rw [hz, zero_lie] at hHx
    exact hx₀ ((smul_eq_zero.mp hHx.symm).resolve_left (by norm_num))
  let β := D.datum.rootDatum.reflectionPerm α.val α.val
  have hβ : β.val = a⁻¹ := oppositeRoot_value D α.val
  have Wpos := rootLine_eq_span s α.val X hxw hx₀
  have Wneg := rootLine_eq_span s β Y (hβ.symm ▸ hyw) hy₀
  rw [hβ] at Wneg
  have hbr := lieBracket_weight P.pair D s hxw hyw
  rw [mul_inv_cancel] at hbr
  have hxx : ⁅X, ⁅X, Y⁆⁆ ∈ k ∙ X := by
    rw [← Wpos]
    apply Submodule.subset_span
    simpa only [mul_one] using lieBracket_weight P.pair D s hxw hbr
  have hyy : ⁅Y, ⁅X, Y⁆⁆ ∈ k ∙ Y := by
    rw [← Wneg]
    apply Submodule.subset_span
    simpa only [mul_one] using lieBracket_weight P.pair D s hyw hbr
  let u := conjugateTangent (rootPoint p₀ (baseTest k) (1 : k))
  let v := conjugateTangent (rootPoint n₀ (baseTest k) (-1 : k))
  have href : u (v (u h)) = -h := by
    have hz := word_reflects_coroot r hp hn
    rw [hr] at hz
    simpa only [rankOneWord, inv_one, Units.val_one, conjugateTangent_mul] using hz
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
    (coroot_mem_bracket_line X Y h u v hHx hHy hxx hyy
      (fun W hW z hz => rootConjugation_sub_mem G s p₀ W hW z hz 1)
      (fun W hW z hz => rootConjugation_sub_mem G s n₀ W hW z hz (-1)) href)
  have hxspan : x ∈ k ∙ X := Wpos ▸ Submodule.subset_span hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxspan
  have hc₀ : c ≠ 0 := by
    intro hh
    rw [hh, zero_smul] at hc
    exact hxn hc.symm
  have hb₀ : b ≠ 0 := by
    intro hh
    rw [hh, zero_smul] at hb
    exact hH₀ hb.symm
  let y := (c⁻¹ * b) • Y
  refine ⟨y, ?_, smul_ne_zero (mul_ne_zero (inv_ne_zero hc₀) hb₀) hy₀, ?_⟩
  · have hh : y ∈ adjointWeightSpace T a⁻¹ s :=
      (adjointWeightSpace T a⁻¹ s).smul_mem _ (Submodule.subset_span hyw)
    exact Set.ext_iff.mp (LinearAlgebraicGroups.RootData.CharacterPairing.adjointWeightSpaceVectors
      G T s _) y |>.mp hh
  · change ⁅x, (c⁻¹ * b) • Y⁆ = h
    rw [← hc, smul_lie, lie_smul, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc₀, one_mul, hb]

end RankOneLie

section CartanTangents

open scoped Matrix TensorProduct
open Specs.CharacterPairing (adjointWeightSpace characterValue absoluteRoots)
open Specs.AdjointRepresentation (TangentCoordinates)
open Specs.StandardGroups (generalLinearPoints)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open InfinitesimalCommutator (matrixDifferential)
open private unitEquiv from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private characterUnit characterValue_eq_unit characterUnit_natural
  from LinearAlgebraicGroups.RootData.RootGroups

private noncomputable def differential {G H : GroupScheme k}
    [IsAffine G.X.left] [IsAffine H.X.left] (f : G ⟶ H)
    (s : IdentityLieStructure G) (t : IdentityLieStructure H) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI := t.lieRing
    letI := t.lieAlgebra
    Lie k G →ₗ⁅k⁆ Lie k H :=
  (identityDifferentialLieHom k G H f s t).choose

private theorem differential_apply {G H : GroupScheme k}
    [IsAffine G.X.left] [IsAffine H.X.left] (f : G ⟶ H)
    (s : IdentityLieStructure G) (t : IdentityLieStructure H) (v : Lie k G) :
    differential f s t v = mapPointKernel f v :=
  (identityDifferentialLieHom k G H f s t).choose_spec v

private def characterTangentValue {T : GroupScheme k} (χ : Character T) (v : Lie k T) : k :=
  (characterUnit χ (CommAlgCat.of k (DualNumber k)) v.toMul.val).val.snd

private theorem characterTangent_factors {T S : GroupScheme k}
    (t : T ⟶ S) (χ : Character S) (v : Lie k T) :
    characterTangentValue χ (mapPointKernel t v) = characterTangentValue (t ≫ χ) v := by
  unfold characterTangentValue characterUnit
  simp only [Grp.comp_hom_hom, Category.assoc, show
    (mapPointKernel t v).toMul.val = v.toMul.val ≫ t.hom.hom from rfl]

private def characterTangent {T : GroupScheme k} (s : IdentityLieStructure T)
    (χ : Character T) :
    letI := s.lieRing
    letI := s.lieAlgebra
    Lie k T →ₗ[k] k := by
  letI := s.lieRing
  letI := s.lieAlgebra
  let R := CommAlgCat.of k (DualNumber k)
  let u := (unitEquiv R).toMonoidHom.comp (((groupPointsFunctor k).map χ).app R).hom
  have hu (z : GroupPoints T R) : u z = characterUnit χ R z := rfl
  refine { toFun := characterTangentValue χ, map_add' := ?_, map_smul' := ?_ }
  · intro v w
    have h := congrArg (fun a : AddGroup (Lie k T) => (a.toAdd.add v w).toMul.val) s.group_law
    change (@Add.add _ s.lieRing.toAddCommGroup.toAdd v w).toMul.val = v.toMul.val * w.toMul.val at h
    change (u (@Add.add _ s.lieRing.toAddCommGroup.toAdd v w).toMul.val).val.snd = (u v.toMul.val).val.snd + (u w.toMul.val).val.snd
    rw [h, map_mul, hu, hu]
    rw [characterAtTangent χ v, characterAtTangent χ w]
    change (1 : k) * _ + _ * (1 : k) = _ + _
    rw [one_mul, mul_one, add_comm]
    rfl
  · intro r v
    have h := congrFun (congrFun s.scalar_law r) v
    let sm := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
    have hval : (scalePointKernel T r v).toMul.val =
        mapPoints (CommAlgCat.ofHom (dualNumberScale r)) v.toMul.val := rfl
    have hh := (congrArg (fun z : Lie k T => z.toMul.val) h).trans hval
    change (characterUnit χ R (@SMul.smul k (Lie k T) sm r v).toMul.val).val.snd =
      r * characterTangentValue χ v
    rw [hh, characterUnit_natural, Units.coe_map]
    change ((dualNumberScale r) ((characterUnit χ R v.toMul.val).val)).snd =
      r * characterTangentValue χ v
    rw [dualNumberScale, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply]
    rfl

private theorem characterTangent_apply {T : GroupScheme k} (s : IdentityLieStructure T)
    (χ : Character T) (v : Lie k T) :
    characterTangent s χ v = characterTangentValue χ v := rfl

private theorem characterTangent_cocharacter {T : GroupScheme k} (χ : Character T)
    (c : Cocharacter T) :
    characterTangentValue χ (cocharacterTangent c) = (pairing T χ c : k) := by
  let R := CommAlgCat.of k (DualNumber k)
  let b : Rˣ := infinitesimalUnit (Multiplicative.ofAdd 1)
  have h := (LinearAlgebraicGroups.RootData.CharacterPairing.characterPairingComposition T χ c).2 R b
  rw [characterValue_eq_unit, infinitesimalUnit_pow, mul_one] at h
  exact congrArg (fun z : DualNumber k => z.snd) h

/-- Any infinitesimal torus element acts on each weight through the
differential of that weight's character. -/
private theorem torusTangent_bracket (P : SplitBorelPair k)
    (s : IdentityLieStructure P.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (v : Lie k P.T.group) (χ : Character P.T.group) (w : Lie k P.G.val),
      w ∈ adjointWeightVectors P.T χ →
        ⁅mapPointKernel P.T.inclusion v, w⁆ = characterTangentValue χ v • w := by
  have hCanonical_s := identityLieStructure_eq_canonical P.G s
  subst s
  let s := identityLieStructure P.G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨_, b, C, L, l, Ad, hAd, hbr, _⟩ := _root_.LinearAlgebraicGroups.adjointRepresentation k P.G s
  intro v χ w hw
  let R := CommAlgCat.of k (DualNumber k)
  let p := mapPointKernel P.T.inclusion v
  let M := ((l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R p.toMul.val)).val
  let V := fun i => algebraMap k R (b.equivFun w i)
  have hv := ((adjointWeightVectors_iff C l Ad hAd P.T χ w).mp hw) R v.toMul.val
  change M *ᵥ V = characterValue χ R v.toMul.val • V at hv
  rw [characterValue_eq_unit, characterAtTangent] at hv
  apply b.equivFun.injective
  rw [← hbr, map_smul]
  funext i
  have h := congrArg (fun a : _ → R => (a i).snd) hv
  change ((M *ᵥ V) i).snd =
    (⟨1, characterTangentValue χ v⟩ * algebraMap k (DualNumber k) (b.equivFun w i) : DualNumber k).snd at h
  rw [mulVec_dual_snd, DualNumber.snd_mul] at h
  change ((matrixDifferential Ad l p) *ᵥ b.equivFun w) i =
    (1 : k) * 0 + characterTangentValue χ v * b.equivFun w i at h
  change _ = characterTangentValue χ v * b.equivFun w i
  simpa only [mul_zero, zero_add] using h

open scoped DirectSum
open private adjointWeightsInternal
  from LinearAlgebraicGroups.RootData.RootGroups

private theorem torusTangent_central (P : SplitBorelPair k)
    (s : IdentityLieStructure P.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ v : Lie k P.T.group, (∀ α : Root P.T, characterTangentValue α.val v = 0) →
      ∀ w : Lie k P.G.val, ⁅mapPointKernel P.T.inclusion v, w⁆ = 0 := by
  have hCanonical_s := identityLieStructure_eq_canonical P.G s
  subst s
  let s := identityLieStructure P.G
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : AddCommGroup (Lie k P.G.val) := s.lieRing.toAddCommGroup
  letI : Module k (Lie k P.G.val) := s.lieAlgebra.toModule
  letI : SMul k (Lie k P.G.val) := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  letI : Add (Lie k P.G.val) := s.lieRing.toAdd
  letI : Zero (Lie k P.G.val) := s.lieRing.toZero
  intro v hv w
  let W := fun χ : Character P.T.group => adjointWeightSpace P.T χ s
  obtain ⟨z, rfl⟩ := (adjointWeightsInternal P.G P.T P.split s).2 w
  let f := DirectSum.coeLinearMap W
  with_unfolding_all change ⁅mapPointKernel P.T.inclusion v, f z⁆ = 0
  refine DirectSum.induction_on z (by with_unfolding_all rw [map_zero f, lie_zero]) ?_ ?_
  · intro χ w
    have hwe : w.val ∈ adjointWeightVectors P.T χ :=
      Set.ext_iff.mp (LinearAlgebraicGroups.RootData.CharacterPairing.adjointWeightSpaceVectors
        P.G P.T s χ) w.val |>.mp w.property
    rw [DirectSum.coeLinearMap_of, torusTangent_bracket P s _ _ _ hwe]
    by_cases hχ : χ = 1
    · subst χ
      obtain ⟨e, he⟩ := torusTangentCharacters P.split
      unfold characterTangentValue
      rw [he, map_one, map_one]
      change (0 : k) • w.val = 0
      with_unfolding_all exact zero_smul k w.val
    · by_cases hw : (w.val : Lie k P.G.val) = 0
      · with_unfolding_all rw [hw, smul_zero]
      · with_unfolding_all rw [hv ⟨χ, hχ, w.val, hwe, hw⟩, zero_smul]
  · intro a b ha hb
    with_unfolding_all rw [map_add f, lie_add, ha, hb, add_zero]

/-- The simple characters cut out the same tangent kernel as all roots. -/
private theorem characterTangent_all_of_simple {P : SplitBorelPair k} (D : AttachedDatum P)
    (v : Lie k P.T.group) :
    letI := D.comm
    (∀ α : D.base.support, characterTangentValue α.val.val v = 0) →
      ∀ β : Root P.T, characterTangentValue β.val v = 0 := by
  letI := D.comm
  intro hv β
  obtain ⟨e, he⟩ := torusTangentCharacters P.split
  let l : Additive (Character P.T.group) →+ k := (e v).toAdditive
  have hl (χ : Character P.T.group) : l (Additive.ofMul χ) = characterTangentValue χ v := by
    have h := congrArg (fun z : (DualNumber k)ˣ => z.val.snd) (he v χ)
    exact h.symm
  rw [← hl, ← D.datum.root_eq]
  obtain ⟨a, _, _, hβ⟩ := D.base.exists_root_eq_sum_int β
  rw [hβ, map_sum]
  apply Finset.sum_eq_zero
  intro α hα
  rw [map_zsmul, D.datum.root_eq, hl, hv ⟨α, hα⟩, smul_zero]

end CartanTangents

section LieGeneration

open scoped DirectSum

open Specs.CharacterPairing (adjointWeightSpace characterValue)
open Specs.AdjointRepresentation (dualMap scale)
open private canonicalZero_eq from LinearAlgebraicGroups.RootData.CharacterPairing
open private adjointWeightsInternal from LinearAlgebraicGroups.RootData.RootGroups
open Specs.RootGroups (CorootReflection HasScalarAction rankOneWord)
open private pointConj comp_pointConj mapPoints_pointConj
  from LinearAlgebraicGroups.RootData.AbstractPairing

private theorem conjugateTangent_ne_zero {G : GroupScheme k}
    (g : GroupPoints G (baseTest k)) {v : Lie k G} (hv : v ≠ 0) :
    conjugateTangent g v ≠ 0 := by
  intro h
  apply hv
  have h' := congrArg (fun p : Lie k G => p.toMul.val) h
  let z := constantPoints G (baseTest k) g
  change z * v.toMul.val * z⁻¹ = 1 at h'
  have h'' : z * v.toMul.val * z⁻¹ = z * 1 * z⁻¹ := by simpa only [mul_one, mul_inv_cancel]
  apply Additive.toMul.injective
  exact Subtype.ext (mul_left_cancel (mul_right_cancel h''))

/-- The inverse torus conjugation transports the character of an adjoint
weight vector under the rational normalizer action. -/
private theorem conjugateTangent_weight {G : GroupScheme k} {T : ClosedSubgroup G}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} {e : T.group ≅ T.group}
    (he : (e.hom ≫ T.inclusion).hom.hom = pointConj g T.inclusion.hom.hom)
    {χ : Character T.group} {v : Lie k G}
    (hv : v ∈ adjointWeightVectors T χ) :
    conjugateTangent (toUnit _ ≫ g) v ∈ adjointWeightVectors T (e.inv ≫ χ) := by
  intro R t
  let s : GroupPoints T.group R := t ≫ e.inv.hom.hom
  have ht : t ≫ T.inclusion.hom.hom = pointConj g (s ≫ T.inclusion.hom.hom) := by
    rw [← comp_pointConj, ← he]
    change t ≫ T.inclusion.hom.hom = t ≫ (e.inv ≫ e.hom ≫ T.inclusion).hom.hom
    rw [e.inv_hom_id_assoc]
  have hχ : characterValue (e.inv ≫ χ) R t = characterValue χ R s := by
    unfold characterValue
    simp only [s, Grp.comp_hom_hom, Category.assoc]
  let b := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
  let x := mapPoints b v.toMul.val
  let y := mapPoints (constants R) (s ≫ T.inclusion.hom.hom)
  have hxy : y * x * y⁻¹ = mapPoints (scale R (characterValue χ R s)) x := hv R s
  change mapPoints (constants R) (t ≫ T.inclusion.hom.hom) *
    mapPoints b (conjugateTangent (toUnit _ ≫ g) v).toMul.val *
    (mapPoints (constants R) (t ≫ T.inclusion.hom.hom))⁻¹ =
      mapPoints (scale R (characterValue (e.inv ≫ χ) R t))
        (mapPoints b (conjugateTangent (toUnit _ ≫ g) v).toMul.val)
  simp only [ht, hχ, conjugateTangent_point, mapPoints_pointConj]
  change pointConj g y * pointConj g x * (pointConj g y)⁻¹ =
    pointConj g (mapPoints (scale R (characterValue χ R s)) x)
  rw [← hxy]
  unfold pointConj
  group

private theorem reflectionCharacter {P : SplitBorelPair k} (D : AttachedDatum P)
    (α β : Root P.T) {A : AdditiveLine k} {x y : A.group ⟶ P.G.val}
    (r : CorootReflection P.T α.val x y) (hr : r.coroot = attachedCoroot D α) :
    letI := D.comm
    r.conjugation.inv ≫ β.val = (D.datum.rootDatum.reflectionPerm α β).val := by
  letI := D.comm
  apply Additive.ofMul.injective
  have hpair : D.datum.rootDatum.coroot' α (Additive.ofMul β.val) =
      pairing P.T.group β.val r.coroot := by
    rw [hr]
    exact D.datum.pairing_eq _ _
  rw [r.reflection, ofMul_mul, ofMul_zpow,
    ← D.datum.root_eq (D.datum.rootDatum.reflectionPerm α β),
    D.datum.rootDatum.root_reflectionPerm, RootPairing.reflection_apply, D.datum.root_eq β,
    D.datum.root_eq α, hpair, sub_eq_add_neg, neg_smul]

/-- The simple root lines and their opposite lines generate every nonzero
weight line in the Lie algebra. -/
private theorem lieSubalgebra_contains_roots [CharZero k] (P : SplitBorelPair k)
    (D : AttachedDatum P) (s : IdentityLieStructure P.G.val) :
    letI := D.comm
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ W : LieSubalgebra k (Lie k P.G.val),
      (∀ α ∈ D.base.support, adjointWeightSpace P.T α.val s ≤ W.toSubmodule ∧
        adjointWeightSpace P.T α.val⁻¹ s ≤ W.toSubmodule) →
      ∀ β : Root P.T, adjointWeightSpace P.T β.val s ≤ W.toSubmodule := by
  have hCanonical_s := identityLieStructure_eq_canonical P.G s
  subst s
  let s := identityLieStructure P.G
  classical
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  letI := D.datum.freeCharacters
  letI := s.lieRing
  letI := s.lieAlgebra
  intro W hW β
  let R := D.datum.rootDatum
  let neg (α : Root P.T) := R.reflectionPerm α α
  let L (α : Root P.T) := adjointWeightSpace P.T α.val s
  have hneg (α : Root P.T) : (neg α).val = α.val⁻¹ := oppositeRoot_value D α
  have hnegneg (α : Root P.T) : neg (neg α) = α := by
    apply Subtype.ext
    rw [hneg, hneg, inv_inv]
  have hcomm (α δ : Root P.T) :
      R.reflectionPerm α (neg δ) = neg (R.reflectionPerm α δ) := by
    have h (i : Root P.T) : R.root (neg i) = - R.root i := by
      rw [D.datum.root_eq, D.datum.root_eq, hneg]
      rfl
    apply R.root.injective
    rw [R.root_reflectionPerm, h, h, R.root_reflectionPerm]
    exact (R.reflection α).toLinearMap.map_neg (R.root δ)
  have hreflection (α : Root P.T) (ha : α ∈ D.base.support) (δ : Root P.T)
      (hδ : L δ ≤ W.toSubmodule) : L (R.reflectionPerm α δ) ≤ W.toSubmodule := by
    obtain ⟨U, V, A, x, y, hx, hy, _, _, r, hr⟩ := attachedCoordinates D α
    let p := x.hom ≫ U.inclusion
    let q := y.hom ≫ V.inclusion
    have hpx : rootTangent p ∈ W :=
      (hW α ha).1 (Submodule.subset_span (rootTangent_weight x.hom hx))
    have hqy : rootTangent q ∈ W :=
      (hW α ha).2 (Submodule.subset_span (rootTangent_weight y.hom hy))
    have hstable (z : Lie k P.G.val) (hz : z ∈ W) :
        ∀ (B : AdditiveLine k) (w : B.group ⟶ P.G.val),
          rootTangent w ∈ W → ∀ t : k, conjugateTangent (rootPoint w (baseTest k) t) z ∈ W := by
      intro B w hw t
      have hh := rootConjugation_sub_mem P.G s w W.toSubmodule
        (fun u hu => W.lie_mem hw hu) z (W.lie_mem hw hz) t
      have ha := W.add_mem hh hz
      have eq : conjugateTangent (rootPoint w (baseTest k) t) z - z + z =
          conjugateTangent (rootPoint w (baseTest k) t) z := sub_add_cancel _ _
      rwa [eq] at ha
    obtain ⟨z, hzw, hzn⟩ := δ.property.2
    have hzW : z ∈ W := hδ (Submodule.subset_span hzw)
    let g : GroupPoints P.G.val (baseTest k) := toUnit _ ≫ r.representative
    let v := conjugateTangent g z
    have hvW : v ∈ W := by
      change conjugateTangent (toUnit _ ≫ r.representative) z ∈ W
      rw [r.representative_word, rankOneWord, conjugateTangent_mul, conjugateTangent_mul]
      exact hstable _ (hstable _ (hstable _ hzW _ p hpx _) _ q hqy _) _ p hpx _
    have hvw := conjugateTangent_weight r.conjugates hzw
    rw [reflectionCharacter D α δ r hr] at hvw
    change v ∈ adjointWeightVectors P.T (R.reflectionPerm α δ).val at hvw
    rw [show L (R.reflectionPerm α δ) = k ∙ v from
      rootLine_eq_span s _ v hvw (conjugateTangent_ne_zero g hzn)]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr hvW
  have hh := D.base.induction_reflect β
    (p := fun δ => L δ ≤ W.toSubmodule ∧ L (neg δ) ≤ W.toSubmodule)
    (fun α ha => ⟨ha.2, (hnegneg α).symm ▸ ha.1⟩)
    (fun α ha => ⟨(hW α ha).1, by
      change adjointWeightSpace P.T (neg α).val s ≤ W.toSubmodule
      rw [hneg]
      exact (hW α ha).2⟩)
    (fun δ α hd ha => ⟨hreflection α ha δ hd.1, hcomm α δ ▸ hreflection α ha (neg δ) hd.2⟩)
  exact hh.1

/-- A Lie subalgebra containing the torus tangents and all nonzero weight
lines is the full Lie algebra. -/
private theorem lieSubalgebra_eq_top_of_weights (P : SplitBorelPair k)
    (s : IdentityLieStructure P.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ W : LieSubalgebra k (Lie k P.G.val),
      (∀ v : Lie k P.T.group, mapPointKernel P.T.inclusion v ∈ W) →
      (∀ α : Root P.T, adjointWeightSpace P.T α.val s ≤ W.toSubmodule) →
      W = ⊤ := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : AddCommGroup (Lie k P.G.val) := s.lieRing.toAddCommGroup
  letI : Module k (Lie k P.G.val) := s.lieAlgebra.toModule
  letI : Add (Lie k P.G.val) := s.lieRing.toAdd
  letI : Zero (Lie k P.G.val) := s.lieRing.toZero
  intro W hT hR
  apply top_unique
  intro x _
  let M := fun χ : Character P.T.group => adjointWeightSpace P.T χ s
  obtain ⟨z, hz⟩ := (adjointWeightsInternal P.G P.T P.split s).2 x
  let F := DirectSum.coeLinearMap M
  change F z = x at hz
  rw [← hz]
  refine DirectSum.induction_on z (by rw [map_zero F]; exact W.zero_mem) ?_ ?_
  · intro χ y
    change DirectSum.coeLinearMap M (DirectSum.of (fun χ => M χ) χ y) ∈ W
    rw [DirectSum.coeLinearMap_of]
    have hy : y.val ∈ adjointWeightVectors P.T χ :=
      (Set.ext_iff.mp (LinearAlgebraicGroups.RootData.CharacterPairing.adjointWeightSpaceVectors
        P.G P.T s χ) y.val).mp y.property
    by_cases hχ : χ = 1
    · subst χ
      have h := (LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups P.G P.reductive
        P.T P.split P.maximal).1.2
      obtain ⟨v, hv⟩ := h.symm ▸ hy
      rw [← hv]
      exact hT v
    · by_cases hy₀ : y.val = 0
      · rw [hy₀]
        exact W.zero_mem
      · exact hR ⟨χ, hχ, y.val, hy, fun h => hy₀ (h.trans (canonicalZero_eq s))⟩ y.property
  · intro a b ha hb
    rw [map_add F]
    exact W.add_mem ha hb

end LieGeneration

section LiePresentation

open scoped Matrix TensorProduct
open Specs.CharacterPairing (adjointWeightSpace absoluteRoots)
open Specs.RationalRealization (generator)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open private det_integralCartan_ne_zero from LinearAlgebraicGroups.RootData.EuclideanComparison
open private finrank_of_internal_character_weights zero_weight_finrank adjointWeightsInternal
  from LinearAlgebraicGroups.RootData.RootGroups

private theorem cocharacterTangent_comp {T S : GroupScheme k} (c : Cocharacter T) (t : T ⟶ S) :
    cocharacterTangent (c ≫ t) = mapPointKernel t (cocharacterTangent c) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  let R := CommAlgCat.of k (DualNumber k)
  let b : Rˣ := infinitesimalUnit (Multiplicative.ofAdd 1)
  change cocharacterPoint (c ≫ t) R b = cocharacterPoint c R b ≫ t.hom.hom
  unfold cocharacterPoint
  change unitPoint R b ≫ (c ≫ t).hom.hom = (unitPoint R b ≫ c.hom.hom) ≫ t.hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

private theorem mapPointKernel_comp_apply {G H L : GroupScheme k} (f : G ⟶ H) (g : H ⟶ L)
    (v : Lie k G) : mapPointKernel (f ≫ g) v = mapPointKernel g (mapPointKernel f v) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change v.toMul.val ≫ (f.hom.hom ≫ g.hom.hom) = (v.toMul.val ≫ f.hom.hom) ≫ g.hom.hom
  exact (Category.assoc v.toMul.val f.hom.hom g.hom.hom).symm

private def simpleEvaluation {P : SplitBorelPair k} (D : AttachedDatum P)
    (sT : IdentityLieStructure P.T.group) :
    letI := D.comm
    letI := sT.lieRing
    letI := sT.lieAlgebra
    Lie k P.T.group →ₗ[k] (D.base.support → k) := by
  letI := D.comm
  letI := sT.lieRing
  letI := sT.lieAlgebra
  exact LinearMap.pi fun α => characterTangent sT α.val.val

/-- The simple coroot tangents map onto the full tuple of simple-root
evaluations, by invertibility of the finite-type Cartan matrix. -/
private theorem simpleCorootSums_surject [CharZero k] {P : SplitBorelPair k}
    (D : AttachedDatum P) (sT : IdentityLieStructure P.T.group) :
    letI := D.comm
    letI := sT.lieRing
    letI := sT.lieAlgebra
    letI : SMul k (Lie k P.T.group) := sT.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
    ∀ w : D.base.support → k, ∃ a : D.base.support → k,
      simpleEvaluation D sT (∑ i, a i • cocharacterTangent (attachedCoroot D i.val)) = w := by
  classical
  letI := D.comm
  letI := sT.lieRing
  letI := sT.lieAlgebra
  letI : AddCommGroup (Lie k P.T.group) := sT.lieRing.toAddCommGroup
  letI : Module k (Lie k P.T.group) := sT.lieAlgebra.toModule
  letI : SMul k (Lie k P.T.group) := sT.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.finiteCocharacters
  letI := D.datum.reduced
  intro w
  let A := integralCartan D.datum.rootDatum D.base
  let M : Matrix D.base.support D.base.support k := (Int.castRingHom k).mapMatrix A.transpose
  have hdet : M.det ≠ 0 := by
    change ((Int.castRingHom k).mapMatrix A.transpose).det ≠ 0
    rw [← RingHom.map_det, Matrix.det_transpose]
    intro h
    apply det_integralCartan_ne_zero D.datum.rootDatum D.base
    exact Int.cast_injective (show (A.det : k) = ((0 : ℤ) : k) from h.trans (Int.cast_zero (R := k)).symm)
  let a := M⁻¹ *ᵥ w
  refine ⟨a, ?_⟩
  have hm : M *ᵥ a = w := by
    change M *ᵥ (M⁻¹ *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  rw [← hm]
  funext j
  change characterTangent sT j.val.val (∑ i, a i • cocharacterTangent (attachedCoroot D i.val)) =
    (M *ᵥ a) j
  rw [map_sum, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, characterTangent_apply, characterTangent_cocharacter]
  have hpair : pairing P.T.group j.val.val (attachedCoroot D i.val) = A i j := by
    change _ = D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root j.val)
      (D.datum.rootDatum.coroot i.val)
    rw [D.datum.root_eq, ← D.datum.pairing_eq]
    rfl
  rw [hpair, smul_eq_mul, mul_comm]
  rfl

private theorem lieRank_eq_torus_add_roots {P : SplitBorelPair k} (D : AttachedDatum P)
    (s : IdentityLieStructure P.G.val) (sT : IdentityLieStructure P.T.group) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI := sT.lieRing
    letI := sT.lieAlgebra
    Module.finrank k (Lie k P.G.val) = Module.finrank k (Lie k P.T.group) + Nat.card (Root P.T) := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := sT.lieRing
  letI := sT.lieAlgebra
  obtain ⟨_, b, _⟩ := tangent_coordinates P.G s
  letI : Module.Finite k (Lie k P.G.val) := Module.Finite.of_basis b
  have hΦ := LinearAlgebraicGroups.RootData.CharacterPairing.finiteAbsoluteRoots P.G P.T P.split
  have h := finrank_of_internal_character_weights (absoluteRoots P.T)
    (fun χ => adjointWeightSpace P.T χ s) (adjointWeightsInternal P.G P.T P.split s) hΦ
    (LinearAlgebraicGroups.RootData.CharacterPairing.absoluteRootWeights P.T s)
    (fun α hα => (LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups P.G P.reductive
      P.T P.split P.maximal).2 α hα |>.1 s)
  rw [zero_weight_finrank P.G P.reductive P.T P.split P.maximal s sT] at h
  exact h.trans (congrArg (_ + ·) (Nat.card_coe_set_eq _).symm)

/-- The simple pinning of an actual reductive group gives a map from the
scalar-extended rational Serre presentation of its Cartan matrix. -/
private theorem serreMapOfPinning [CharZero k] {A : AdditiveLine k}
    (P : PinnedGroup A) (D : AttachedDatum P.pair) (s : IdentityLieStructure P.pair.G.val)
    {I : Type u} [DecidableEq I] (M : Matrix I I ℤ) :
    letI := D.comm
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (j : I ≃ D.base.support)
      (_ : ∀ a b, integralCartan D.datum.rootDatum D.base (j a) (j b) = M a b),
      let α (i : I) : SimpleRoot P.pair := ⟨(j i).val, (D.simple_iff _).mp (j i).property⟩
      ∃ f : (k ⊗[ℚ] Matrix.ToLieAlgebra ℚ M) →ₗ⁅k⁆ Lie k P.pair.G.val,
        (∀ i, f (1 ⊗ₜ[ℚ] generator ℚ M (.E i)) =
          rootTangent ((P.pin (α i)).val.hom ≫ (P.roots (α i).val).val.inclusion)) ∧
        (∀ i, let v := f (1 ⊗ₜ[ℚ] generator ℚ M (.F i))
              v ∈ adjointWeightVectors P.pair.T (α i).val.val⁻¹ ∧ v ≠ 0) ∧
        (∀ i, f (1 ⊗ₜ[ℚ] generator ℚ M (.H i)) = corootTangent P.pair.T (attachedCoroot D (α i).val)) := by
  classical
  letI := D.comm
  letI := s.lieRing
  letI := s.lieAlgebra
  intro j hj α
  let L := Lie k P.pair.G.val
  let a (i : D.base.support) : SimpleRoot P.pair := ⟨i.val, (D.simple_iff _).mp i.property⟩
  let X (i : D.base.support) := rootTangent ((P.pin (a i)).val.hom ≫ (P.roots i.val).val.inclusion)
  let H (i : D.base.support) := corootTangent P.pair.T (attachedCoroot D i.val)
  have ht := fun i : D.base.support => pinnedLieTriple P D s (a i)
  choose Y hY hY₀ hXY using fun i => (ht i).2.2
  obtain ⟨hHH, hEF, hHE, hHF, hE, hF⟩ :=
    serreRelationsForTriples P.pair D s X Y (fun i => (ht i).1) hY hXY
  let Qmodule : Module ℚ L := Module.compHom L (algebraMap ℚ k)
  letI : Module ℚ L := Qmodule
  letI : SMul k L := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  letI : SMul ℚ L := Qmodule.toDistribMulAction.toMulAction.toSMul
  letI : IsScalarTower ℚ k L :=
    IsScalarTower.of_algebraMap_smul (R := ℚ) (A := k) (M := L) fun _ _ => rfl
  letI : LieAlgebra ℚ L :=
    { toModule := Qmodule, lie_smul := fun a x y => lie_smul (algebraMap ℚ k a) x y }
  letI : Zero L := s.lieRing.toZero
  letI : SMul ℤ L := s.lieRing.toSubNegMonoid.toZSMul.toSMul
  have had (x y : L) (n : ℕ) :
      (LieAlgebra.ad ℚ L x ^ n) y = (LieAlgebra.ad k L x ^ n) y := by
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, ih]
  have h₁ (a b : I) : ⁅X (j a), Y (j b)⁆ = if a = b then H (j a) else 0 := by
    simpa only [j.injective.eq_iff] using hEF (j a) (j b)
  have h₂ (a b : I) : ⁅H (j a), X (j b)⁆ = M a b • X (j b) := by
    simpa only [hj] using hHE (j a) (j b)
  have h₃ (a b : I) : ⁅H (j a), Y (j b)⁆ = -(M a b • Y (j b)) := by
    simpa only [hj] using hHF (j a) (j b)
  have h₄ (a b : I) : (LieAlgebra.ad ℚ L (X (j a)) ^ (-M a b).toNat) ⁅X (j a), X (j b)⁆ = 0 := by
    rw [had]
    have h := hE (j a) (j b)
    rw [hj] at h
    exact h
  have h₅ (a b : I) : (LieAlgebra.ad ℚ L (Y (j a)) ^ (-M a b).toNat) ⁅Y (j a), Y (j b)⁆ = 0 := by
    rw [had]
    have h := hF (j a) (j b)
    rw [hj] at h
    exact h
  have hneg (x : L) : s.lieRing.toNeg.neg x = -x :=
    congrArg (fun a : AddGroup (Lie k P.pair.G.val) => a.toNeg.neg x) s.group_law
  obtain ⟨f, hf₁, hf₂, hf₃⟩ := serre_lift (R := ℚ) M (X ∘ j) (Y ∘ j) (H ∘ j)
    (fun a b => hHH (j a) (j b)) (by
      intro a b
      by_cases heq : a = b
      · simpa only [ite_eq_left heq, Function.comp_apply] using h₁ a b
      · simpa only [ite_eq_right heq, Function.comp_apply] using h₁ a b)
    h₂ (by
      intro a b
      change ⁅H (j a), Y (j b)⁆ = s.lieRing.toNeg.neg (M a b • Y (j b))
      rw [hneg]
      exact h₃ a b) h₄ h₅
  refine ⟨extendLieHom f, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [extendLieHom_tmul, one_smul, hf₁]
    rfl
  · dsimp only
    rw [extendLieHom_tmul, one_smul, hf₂]
    exact ⟨hY (j i), hY₀ (j i)⟩
  · rw [extendLieHom_tmul, one_smul, hf₃]
    rfl

private def centralAugmentation {S Z L : Type u} [LieRing S] [LieRing Z] [LieRing L]
    [LieAlgebra k S] [LieAlgebra k Z] [LieAlgebra k L]
    (f : S →ₗ⁅k⁆ L) (g : Z →ₗ[k] L) (hZ : ∀ a b : Z, ⁅a, b⁆ = 0)
    (hg : ∀ (z : Z) (x : L), ⁅g z, x⁆ = 0) : (S × Z) →ₗ⁅k⁆ L where
  toLinearMap := f.toLinearMap.coprod g
  map_lie' := by
    intro a b
    change f ⁅a.1, b.1⁆ + g ⁅a.2, b.2⁆ = ⁅f a.1 + g a.2, f b.1 + g b.2⁆
    rw [hZ, map_zero, add_zero, LieHom.map_lie, add_lie, hg, add_zero, lie_add,
      ← lie_skew (f a.1) (g b.2), hg, neg_zero, add_zero]

private theorem surjLie_of_cartan_and_simple_lines [CharZero k]
    {P : SplitBorelPair k} (D : AttachedDatum P) (s : IdentityLieStructure P.G.val)
    {S : Type u} [LieRing S] [LieAlgebra k S] :
    letI := D.comm
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ f : S →ₗ⁅k⁆ Lie k P.G.val,
      (∀ v : Lie k P.T.group, mapPointKernel P.T.inclusion v ∈ Set.range f) →
      (∀ i : D.base.support, ∃ x y : Lie k P.G.val, x ∈ Set.range f ∧ y ∈ Set.range f ∧
        x ∈ adjointWeightVectors P.T i.val.val ∧ y ∈ adjointWeightVectors P.T i.val.val⁻¹ ∧
        x ≠ 0 ∧ y ≠ 0) →
      Function.Surjective f := by
  letI := D.comm
  letI := s.lieRing
  letI := s.lieAlgebra
  intro f hT hsimple
  have hW (α : Root P.T) (ha : α ∈ D.base.support) :
      adjointWeightSpace P.T α.val s ≤ f.range.toSubmodule ∧
        adjointWeightSpace P.T α.val⁻¹ s ≤ f.range.toSubmodule := by
    obtain ⟨x, y, hx, hy, hxw, hyw, hx₀, hy₀⟩ := hsimple ⟨α, ha⟩
    let β := D.datum.rootDatum.reflectionPerm α α
    have hβ : β.val = α.val⁻¹ := oppositeRoot_value D α
    rw [rootLine_eq_span s α x hxw hx₀, ← hβ, rootLine_eq_span s β y (hβ.symm ▸ hyw) hy₀]
    exact ⟨(Submodule.span_singleton_le_iff_mem _ _).mpr hx, (Submodule.span_singleton_le_iff_mem _ _).mpr hy⟩
  have hf := lieSubalgebra_eq_top_of_weights P s f.range hT (lieSubalgebra_contains_roots P D s f.range hW)
  intro x
  have hx : x ∈ f.range := hf.symm ▸ (show x ∈ (⊤ : LieSubalgebra k (Lie k P.G.val)) from trivial)
  exact hx

end LiePresentation

section LieComparison

open scoped Matrix TensorProduct
open Specs.CharacterPairing (adjointWeightSpace)
open Specs.RationalRealization (generator)
open _root_.LinearAlgebraicGroups.RationalRealization (serreStructure)

@[instance_reducible]
private def abelianLieRing (Z : Type*) [AddCommGroup Z] : LieRing Z where
  bracket _ _ := 0
  add_lie _ _ _ := (zero_add 0).symm
  lie_add _ _ _ := (zero_add 0).symm
  lie_self _ := rfl
  leibniz_lie _ _ _ := (zero_add 0).symm

@[instance_reducible]
private def abelianLieAlgebra (Z : Type*) [AddCommGroup Z] [Module k Z] :
    @LieAlgebra k Z _ (abelianLieRing Z) := by
  letI := abelianLieRing Z
  exact { lie_smul := fun a _ _ => (smul_zero a).symm }

set_option maxHeartbeats 5000000 in
/-- Compare the pinned Lie algebras over the ground field, using the
coroots to identify the semisimple Cartans and the torus differential
to identify the central summands. -/
private theorem pinnedLieComparison [CharZero k] {A : AdditiveLine k}
    (P Q : PinnedGroup A) (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair)
    (h : LatticeMap D E) (t : P.pair.T.group ⟶ Q.pair.T.group)
    (ht : ∀ χ : Character Q.pair.T.group, t ≫ χ = h.characters χ)
    (s : IdentityLieStructure P.pair.G.val) (r : IdentityLieStructure Q.pair.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI := r.lieRing
    letI := r.lieAlgebra
    ∃ e : Lie k P.pair.G.val ≃ₗ⁅k⁆ Lie k Q.pair.G.val,
      (∀ v, e (mapPointKernel P.pair.T.inclusion v) =
        mapPointKernel Q.pair.T.inclusion (mapPointKernel t v)) ∧
      (∀ (α : Root P.pair.T) v, v ∈ adjointWeightVectors P.pair.T α.val →
        e v ∈ adjointWeightVectors Q.pair.T (h.roots α).val) ∧
      (∀ α : SimpleRoot P.pair,
        e (rootTangent ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion)) =
          rootTangent ((Q.pin (h.simpleRoot α)).val.hom ≫ (Q.roots (h.roots α.val)).val.inclusion)) := by
  have hCanonical_s := identityLieStructure_eq_canonical P.pair.G s
  subst s
  let s := identityLieStructure P.pair.G
  have hCanonical_r := identityLieStructure_eq_canonical Q.pair.G r
  subst r
  let r := identityLieStructure Q.pair.G
  classical
  letI := D.comm
  letI := E.comm
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := r.lieRing
  letI := r.lieAlgebra
  let T := Specs.Unipotent.closedSubgroupAlgebraicGroup P.pair.T
  let U := Specs.Unipotent.closedSubgroupAlgebraicGroup Q.pair.T
  let sT : IdentityLieStructure P.pair.T.group := identityLieStructure T
  let sU : IdentityLieStructure Q.pair.T.group := identityLieStructure U
  letI := sT.lieRing
  letI := sT.lieAlgebra
  letI := sU.lieRing
  letI := sU.lieAlgebra
  letI : IsAffine P.pair.T.group.X.left := T.property.1
  letI : IsAffine Q.pair.T.group.X.left := U.property.1
  letI : IsAffine P.pair.G.val.X.left := P.pair.G.property.1
  letI : IsAffine Q.pair.G.val.X.left := Q.pair.G.property.1
  letI : AddCommGroup (Lie k P.pair.G.val) := s.lieRing.toAddCommGroup
  letI : Module k (Lie k P.pair.G.val) := s.lieAlgebra.toModule
  letI : SMul k (Lie k P.pair.G.val) := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  letI : AddCommGroup (Lie k Q.pair.G.val) := r.lieRing.toAddCommGroup
  letI : Module k (Lie k Q.pair.G.val) := r.lieAlgebra.toModule
  letI : SMul k (Lie k Q.pair.G.val) := r.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  letI : AddCommGroup (Lie k P.pair.T.group) := sT.lieRing.toAddCommGroup
  letI : Module k (Lie k P.pair.T.group) := sT.lieAlgebra.toModule
  letI : SMul k (Lie k P.pair.T.group) := sT.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  letI : AddCommGroup (Lie k Q.pair.T.group) := sU.lieRing.toAddCommGroup
  letI : Module k (Lie k Q.pair.T.group) := sU.lieAlgebra.toModule
  letI : SMul k (Lie k Q.pair.T.group) := sU.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  obtain ⟨_, bP, _⟩ := tangent_coordinates P.pair.G s
  obtain ⟨_, bQ, _⟩ := tangent_coordinates Q.pair.G r
  obtain ⟨_, bT, _⟩ := tangent_coordinates T sT
  obtain ⟨_, bU, _⟩ := tangent_coordinates U sU
  letI : Module.Finite k (Lie k P.pair.G.val) := Module.Finite.of_basis bP
  letI : Module.Finite k (Lie k Q.pair.G.val) := Module.Finite.of_basis bQ
  letI : Module.Finite k (Lie k P.pair.T.group) := Module.Finite.of_basis bT
  letI : Module.Finite k (Lie k Q.pair.T.group) := Module.Finite.of_basis bU
  let dt := differential t sT sU
  have hdtv (v : Lie k P.pair.T.group) : dt v = mapPointKernel t v :=
    differential_apply t sT sU v
  have hdt : Function.Bijective dt := by
    have hd : (dt : Lie k P.pair.T.group → Lie k Q.pair.T.group) = mapPointKernel t :=
      funext (differential_apply t sT sU)
    rw [hd]
    exact torusDifferential_bijective P.pair.split Q.pair.split t
      h.characters h.injective h.finiteIndex ht
  let I := D.base.support
  let M := integralCartan D.datum.rootDatum D.base
  let S := k ⊗[ℚ] Matrix.ToLieAlgebra ℚ M
  let g (c : CartanMatrix.Generators I) : S := 1 ⊗ₜ[ℚ] generator ℚ M c
  let ϕ := simpleEvaluation D sT
  let Z : Submodule k (Lie k P.pair.T.group) := LinearMap.ker ϕ
  letI : AddCommGroup Z := inferInstance
  letI : Module k Z := inferInstance
  letI : Module.Free k Z := Module.Free.of_divisionRing k Z
  letI : Module.Finite k Z := Module.Finite.of_injective Z.subtype Subtype.val_injective
  letI : LieRing Z := abelianLieRing Z
  letI : LieAlgebra k Z := abelianLieAlgebra Z
  obtain ⟨j, hj, hM⟩ := integralCartan_reindex h
  obtain ⟨f, hfE, hfF, hfH⟩ := serreMapOfPinning P D s M (Equiv.refl I) fun _ _ => rfl
  obtain ⟨p, hpE, hpF, hpH⟩ := serreMapOfPinning Q E r M j hM
  let ι₁ := differential P.pair.T.inclusion sT s
  let ι₂ := differential Q.pair.T.inclusion sU r
  let z₁ : Z →ₗ[k] Lie k P.pair.G.val := ι₁.toLinearMap.comp Z.subtype
  let z₂ : Z →ₗ[k] Lie k Q.pair.G.val := ι₂.toLinearMap.comp (dt.toLinearMap.comp Z.subtype)
  have hzero (z : Z) (α : Root P.pair.T) : characterTangentValue α.val z.val = 0 := by
    apply characterTangent_all_of_simple D z.val
    intro i
    have h := congrFun z.property i
    change characterTangent sT i.val.val z.val = 0 at h
    rw [characterTangent_apply] at h
    exact h
  have hzero₂ (z : Z) (α : Root Q.pair.T) : characterTangentValue α.val (dt z.val) = 0 := by
    obtain ⟨β, rfl⟩ := h.roots.surjective α
    rw [hdtv, characterTangent_factors, ht, h.root_eq]
    exact hzero z β
  have hz₁ (z : Z) (w : Lie k P.pair.G.val) : ⁅z₁ z, w⁆ = 0 := by
    change ⁅ι₁ z.val, w⁆ = 0
    rw [differential_apply]
    exact torusTangent_central P.pair s z.val (hzero z) w
  have hz₂ (z : Z) (w : Lie k Q.pair.G.val) : ⁅z₂ z, w⁆ = 0 := by
    change ⁅ι₂ (dt z.val), w⁆ = 0
    rw [differential_apply]
    exact torusTangent_central Q.pair r (dt z.val) (hzero₂ z) w
  let F := centralAugmentation f z₁ (fun _ _ => rfl) hz₁
  let J := centralAugmentation p z₂ (fun _ _ => rfl) hz₂
  have hmark₁ (i : I) : f (g (.H i)) = ι₁ (cocharacterTangent (attachedCoroot D i.val)) :=
    (hfH i).trans (differential_apply P.pair.T.inclusion sT s _).symm
  have hmark₂ (i : I) : p (g (.H i)) = ι₂ (dt (cocharacterTangent (attachedCoroot D i.val))) := by
    rw [hdtv, ← cocharacterTangent_comp, map_coroot h t ht]
    change _ = differential Q.pair.T.inclusion sU r _
    rw [differential_apply]
    simpa only [hj] using hpH i
  have hCartan (v : Lie k P.pair.T.group) : ∃ w : S × Z,
      F w = mapPointKernel P.pair.T.inclusion v ∧
        J w = mapPointKernel Q.pair.T.inclusion (dt v) := by
    obtain ⟨a, ha⟩ := simpleCorootSums_surject D sT (ϕ v)
    let u : Lie k P.pair.T.group := ∑ i : I, a i • cocharacterTangent (attachedCoroot D i.val)
    let b : S := ∑ i : I, a i • g (.H i)
    let z : Z := ⟨v - u, by change ϕ (v - u) = 0; rw [map_sub, ha, sub_self]⟩
    refine ⟨(b, z), ?_, ?_⟩
    · change f b + ι₁ (v - u) = _
      rw [show f b = ι₁ u by simp only [b, u, map_sum, map_smul, hmark₁],
        ← map_add, add_sub_cancel, differential_apply]
    · change p b + ι₂ (dt (v - u)) = _
      rw [show p b = ι₂ (dt u) by simp only [b, u, map_sum, map_smul, hmark₂],
        ← map_add, ← map_add, add_sub_cancel, differential_apply]
  have hFg (c : CartanMatrix.Generators I) : F (g c, 0) = f (g c) := by
    change f (g c) + z₁ 0 = _
    rw [map_zero, add_zero]
  have hJg (c : CartanMatrix.Generators I) : J (g c, 0) = p (g c) := by
    change p (g c) + z₂ 0 = _
    rw [map_zero, add_zero]
  have hf : Function.Surjective F := by
    apply surjLie_of_cartan_and_simple_lines D s F
    · intro v
      obtain ⟨w, hw, _⟩ := hCartan v
      exact ⟨w, hw⟩
    · intro i
      let α : SimpleRoot P.pair := ⟨i.val, (D.simple_iff _).mp i.property⟩
      have hX := pinnedLieTriple P D s α
      exact ⟨f (g (.E i)), f (g (.F i)), ⟨_, hFg (.E i)⟩, ⟨_, hFg (.F i)⟩,
        hfE i ▸ (hX.1 : rootTangent _ ∈ _), (hfF i).1,
        hfE i ▸ (hX.2.1 : rootTangent _ ≠ 0), (hfF i).2⟩
  have hp : Function.Surjective J := by
    apply surjLie_of_cartan_and_simple_lines E r J
    · intro v
      obtain ⟨u, rfl⟩ := hdt.2 v
      obtain ⟨w, _, hw⟩ := hCartan u
      exact ⟨w, hw⟩
    · intro i
      obtain ⟨a, rfl⟩ := j.surjective i
      let α : SimpleRoot Q.pair := ⟨(j a).val, (E.simple_iff _).mp (j a).property⟩
      have hX := pinnedLieTriple Q E r α
      exact ⟨p (g (.E a)), p (g (.F a)), ⟨_, hJg (.E a)⟩, ⟨_, hJg (.F a)⟩,
        hpE a ▸ (hX.1 : rootTangent _ ∈ _), (hpF a).1,
        hpE a ▸ (hX.2.1 : rootTangent _ ≠ 0), (hpF a).2⟩
  obtain ⟨_, _, hSfinite, hSdim, _⟩ := @serreStructure D.toBased (inferInstance : DecidableEq I)
  letI : Module.Finite ℚ (Matrix.ToLieAlgebra ℚ M) := hSfinite
  have hSrk : Module.finrank k S = I.card + Nat.card (Root P.pair.T) :=
    Module.finrank_baseChange.trans hSdim
  have hϕ : Function.Surjective ϕ := by
    intro w
    obtain ⟨a, ha⟩ := simpleCorootSums_surject D sT w
    exact ⟨_, ha⟩
  have hZdim : Fintype.card I + Module.finrank k Z = Module.finrank k (Lie k P.pair.T.group) := by
    have hh := ϕ.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hϕ, finrank_top, Module.finrank_fintype_fun_eq_card] at hh
    exact hh
  have hdim : Module.finrank k (S × Z) = Module.finrank k (Lie k P.pair.G.val) := by
    rw [Module.finrank_prod, hSrk, lieRank_eq_torus_add_roots D s sT, ← hZdim]
    have hI : Fintype.card I = I.card := Fintype.card_coe I
    rw [hI]
    omega
  have hdim' : Module.finrank k (S × Z) = Module.finrank k (Lie k Q.pair.G.val) := by
    rw [hdim, lieRank_eq_torus_add_roots D s sT, lieRank_eq_torus_add_roots E r sU,
      (LinearEquiv.ofBijective dt.toLinearMap hdt).finrank_eq, Nat.card_congr h.roots]
  let eF := LieEquiv.ofBijective F
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hf, hf⟩
  let eJ := LieEquiv.ofBijective J
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mpr hp, hp⟩
  let e := eF.symm.trans eJ
  have he (w : S × Z) : e (F w) = J w := by
    change eJ (eF.symm (eF w)) = eJ w
    rw [eF.symm_apply_apply]
  have heT (v : Lie k P.pair.T.group) : e (mapPointKernel P.pair.T.inclusion v) =
        mapPointKernel Q.pair.T.inclusion (mapPointKernel t v) := by
    obtain ⟨w, hw, hw'⟩ := hCartan v
    rw [← hw, he, hw', hdtv]
  refine ⟨e, heT, ?_, ?_⟩
  · intro α v hv
    apply (weight_iff_corootTangents Q.pair E r _ _).mpr
    intro c
    obtain ⟨u, hu⟩ := hdt.2 (cocharacterTangent c)
    have hu' : mapPointKernel t u = cocharacterTangent c := (differential_apply t sT sU u).symm.trans hu
    have hh : characterTangentValue α.val u = (pairing Q.pair.T.group (h.roots α).val c : k) := by
      rw [← characterTangent_cocharacter, ← hu', characterTangent_factors, ht, h.root_eq]
    rw [show corootTangent Q.pair.T c = e (mapPointKernel P.pair.T.inclusion u) by rw [heT, hu'],
      ← LieEquiv.map_lie, torusTangent_bracket P.pair s _ _ _ hv, hh, map_smul]
  · intro α
    let i : I := ⟨α.val, (D.simple_iff _).mpr α.property⟩
    have hα : (⟨(j i).val, (E.simple_iff _).mp (j i).property⟩ : SimpleRoot Q.pair) =
        h.simpleRoot α := Subtype.ext (hj i)
    have hi := hfE i
    change f (g (.E i)) = rootTangent ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion) at hi
    rw [← hi, ← hFg, he, hJg, hpE i]
    exact congrArg (fun β : SimpleRoot Q.pair =>
      rootTangent ((Q.pin β).val.hom ≫ (Q.roots β.val).val.inclusion)) hα

end LieComparison

section LiftingFromLie

open scoped Matrix DirectSum
open Specs.CharacterPairing (absoluteRoots adjointWeightSpace characterValue pairing)
open Specs.AdjointRepresentation (TangentCoordinates conjugate)
open Specs.StandardGroups (generalLinearPoints)
open Specs.RankOneFlag (SameSubgroup)
open Specs.OrderedRootProducts (Enumerates)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition oppositeCocharacter)
open private rootPoint_comp rootPoint_eq rootPoint_natural additiveLine_tangent_point adjointWeightsInternal
  from LinearAlgebraicGroups.RootData.RootGroups
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

private theorem rootPoint_scaledTangent {A : AdditiveLine k} {G : GroupScheme k}
    (s : IdentityLieStructure G) (x : A.group ⟶ G) (a : k) :
    letI := s.lieRing
    letI := s.lieAlgebra
    (a • rootTangent x).toMul.val = rootPoint x (dualTest k) (⟨0, a⟩ : DualNumber k) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  change mapPoints (CommAlgCat.ofHom (dualNumberScale a))
      (rootPoint x (dualTest k) DualNumber.eps) = _
  rw [rootPoint_natural]
  apply congrArg (rootPoint x (dualTest k))
  apply TrivSqZeroExt.ext
  · change ((dualNumberScale a) DualNumber.eps).fst = 0
    rw [dualNumberScale, TrivSqZeroExt.fst_map]
    rfl
  · change ((dualNumberScale a) DualNumber.eps).snd = a
    rw [dualNumberScale, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply]
    exact mul_one a

private theorem torusAdjoint_agree {P Q : SplitBorelPair k}
    {D : AttachedDatum P} {E : AttachedDatum Q} (h : LatticeMap D E)
    (t : P.T.group ⟶ Q.T.group) (ht : ∀ χ : Character Q.T.group, t ≫ χ = h.characters χ)
    (s : IdentityLieStructure P.G.val) (r : IdentityLieStructure Q.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI := r.lieRing
    letI := r.lieAlgebra
    ∀ (e : Lie k P.G.val ≃ₗ⁅k⁆ Lie k Q.G.val)
      (_ : ∀ v, e (mapPointKernel P.T.inclusion v) = mapPointKernel Q.T.inclusion (mapPointKernel t v))
      (_ : ∀ (α : Root P.T) v, v ∈ adjointWeightVectors P.T α.val →
        e v ∈ adjointWeightVectors Q.T (h.roots α).val)
      {I : Type u} [Fintype I] [DecidableEq I] (b : Module.Basis I k (Lie k P.G.val))
      {C₁ : TangentCoordinates P.G.val I b} {C₂ : TangentCoordinates Q.G.val I (b.map e.toLinearEquiv)}
      {L₁ L₂ : GroupScheme k}
      (l₁ : (groupPointsFunctor k).obj L₁ ≅ generalLinearPoints k I)
      (l₂ : (groupPointsFunctor k).obj L₂ ≅ generalLinearPoints k I)
      (Ad₁ : P.G.val ⟶ L₁) (Ad₂ : Q.G.val ⟶ L₂)
      (_ : ∀ (R : TestAlgebra k) (g : GroupPoints P.G.val R) (v : I → R),
        let M := (l₁.hom.app R).hom (((groupPointsFunctor k).map Ad₁).app R g)
        (C₁.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (C₁.equiv R v))
      (_ : ∀ (R : TestAlgebra k) (g : GroupPoints Q.G.val R) (v : I → R),
        let M := (l₂.hom.app R).hom (((groupPointsFunctor k).map Ad₂).app R g)
        (C₂.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (C₂.equiv R v))
      (R : TestAlgebra k) (z : GroupPoints P.T.group R),
      let M := (l₁.hom.app R).hom (((groupPointsFunctor k).map Ad₁).app R (z ≫ P.T.inclusion.hom.hom))
      let N := (l₂.hom.app R).hom (((groupPointsFunctor k).map Ad₂).app R
        (z ≫ t.hom.hom ≫ Q.T.inclusion.hom.hom))
      M.val = N.val := by
  have hCanonical_s := identityLieStructure_eq_canonical P.G s
  subst s
  let s := identityLieStructure P.G
  have hCanonical_r := identityLieStructure_eq_canonical Q.G r
  subst r
  let r := identityLieStructure Q.G
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := r.lieRing
  letI := r.lieAlgebra
  letI : AddCommGroup (Lie k P.G.val) := s.lieRing.toAddCommGroup
  letI : Module k (Lie k P.G.val) := s.lieAlgebra.toModule
  letI : AddCommGroup (Lie k Q.G.val) := r.lieRing.toAddCommGroup
  letI : Module k (Lie k Q.G.val) := r.lieAlgebra.toModule
  letI : Add (Lie k P.G.val) := s.lieRing.toAdd
  letI : Zero (Lie k P.G.val) := s.lieRing.toZero
  intro e he hroot I instI decI b C₁ C₂ L₁ L₂ l₁ l₂ Ad₁ Ad₂ hAd₁ hAd₂ R z M N
  let S := fun χ : Character P.T.group => adjointWeightSpace P.T χ s
  let V (v : Lie k P.G.val) : I → R := fun i => algebraMap k R (b.equivFun v i)
  have hall (v : Lie k P.G.val) : M.val *ᵥ V v = N.val *ᵥ V v := by
    obtain ⟨y, rfl⟩ := (adjointWeightsInternal P.G P.T P.split s).2 v
    let F := DirectSum.coeLinearMap S
    change M.val *ᵥ V (F y) = N.val *ᵥ V (F y)
    have hV (x y : Lie k P.G.val) : V (x + y) = V x + V y := by
      funext i
      simp [V]
    have hVzero : V 0 = 0 := by
      funext i
      change algebraMap k R ((b.equivFun) 0 i) = 0
      have h : b.equivFun (0 : Lie k P.G.val) = (0 : I → k) := b.equivFun.map_zero
      rw [h]
      exact map_zero _
    refine DirectSum.induction_on y (by rw [map_zero F, hVzero, Matrix.mulVec_zero, Matrix.mulVec_zero]) ?_ ?_
    · intro χ w
      rw [DirectSum.coeLinearMap_of]
      have hw : w.val ∈ adjointWeightVectors P.T χ :=
        (Set.ext_iff.mp (LinearAlgebraicGroups.RootData.CharacterPairing.adjointWeightSpaceVectors
          P.G P.T s χ) w.val).mp w.property
      let z' : GroupPoints Q.T.group R := z ≫ t.hom.hom
      have hw₁ := ((adjointWeightVectors_iff C₁ l₁ Ad₁ hAd₁ P.T χ w.val).mp hw) R z
      change M.val *ᵥ V w.val = characterValue χ R z • V w.val at hw₁
      have useWeight (ψ : Character Q.T.group) (hw' : e w.val ∈ adjointWeightVectors Q.T ψ)
          (hψ : t ≫ ψ = χ) : M.val *ᵥ V w.val = N.val *ᵥ V w.val := by
        have hw₂ := ((adjointWeightVectors_iff C₂ l₂ Ad₂ hAd₂ Q.T ψ (e w.val)).mp hw') R z'
        let V' (a : Lie k Q.G.val) : I → R :=
          fun i => algebraMap k R ((b.map e.toLinearEquiv).equivFun a i)
        change N.val *ᵥ V' (e w.val) = characterValue ψ R z' • V' (e w.val) at hw₂
        have hV' (a : Lie k P.G.val) : V' (e a) = V a := by
          dsimp only [V', V]
          rw [basis_map_coordinates b e]
        rw [hV'] at hw₂
        have hval : characterValue ψ R z' = characterValue χ R z := by
          rw [← hψ]
          unfold characterValue
          simp only [z', Grp.comp_hom_hom, Category.assoc]
        rw [hw₁, hw₂, hval]
      by_cases hχ : χ = 1
      · subst χ
        have hP := (LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups P.G P.reductive
          P.T P.split P.maximal).1.2
        obtain ⟨v, hv⟩ := hP.symm ▸ hw
        apply useWeight 1
        · rw [← hv, he]
          exact (LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups Q.G Q.reductive
            Q.T Q.split Q.maximal).1.2 ▸ ⟨_, rfl⟩
        · apply Grp.hom_ext
          exact MonObj.comp_one _
      · by_cases h₀ : w.val = 0
        · rw [h₀, hVzero, Matrix.mulVec_zero, Matrix.mulVec_zero]
        · let α : Root P.T := ⟨χ, hχ, w.val, hw, h₀⟩
          exact useWeight (h.roots α).val (hroot α w.val hw) ((ht _).trans (h.root_eq α))
    · intro y₁ y₂ h₁ h₂
      rw [map_add F, hV, Matrix.mulVec_add, Matrix.mulVec_add, h₁, h₂]
  apply Matrix.ext
  intro i j
  have h := congrFun (hall (b j)) i
  have hv : V (b j) = Pi.single j (1 : R) := by
    funext l
    change algebraMap k R (b.equivFun (b j) l) = (Pi.single j (1 : R) : I → R) l
    rw [Module.Basis.equivFun_self]
    by_cases h : l = j
    · subst l
      simp
    · simp [h, Ne.symm h]
  rw [hv, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  exact h

-- Equality of the matrices gives a common invertible operator on
-- relative tangents.
private def matrixActionEquiv {I : Type u} [Fintype I] [DecidableEq I] {R : Type u}
    [CommRing R] (M : Matrix.GeneralLinearGroup I R) : (I → R) ≃ (I → R) :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv (Matrix.GeneralLinearGroup.toLin M)).toEquiv

private theorem matrixActionEquiv_apply {I : Type u} [Fintype I] [DecidableEq I]
    {R : Type u} [CommRing R] (M : Matrix.GeneralLinearGroup I R) (v : I → R) :
    matrixActionEquiv M v = M.val *ᵥ v := rfl

private theorem point_comp_pair {C G H : GroupScheme k} {R : TestAlgebra k}
    (p : C ⟶ G) (q : C ⟶ H) (z : GroupPoints C R) :
    z ≫ (lift p q).hom.hom = lift (z ≫ p.hom.hom) (z ≫ q.hom.hom) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, Category.assoc]
    exact congrArg (fun f : C ⟶ G => z ≫ f.hom.hom) (lift_fst p q)
  · rw [lift_snd, Category.assoc]
    exact congrArg (fun f : C ⟶ H => z ≫ f.hom.hom) (lift_snd p q)

set_option maxHeartbeats 3000000 in
private theorem liftFromLieComparison [CharZero k]
    (word : WordGeneratedGroup.{u}) (generic : DominantGenericLift.{u})
    {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair) (h : LatticeMap D E)
    (t : P.pair.T.group ⟶ Q.pair.T.group)
    (ht : ∀ χ : Character Q.pair.T.group, t ≫ χ = h.characters χ)
    (hts : Surjective t.hom.hom.left) (hti : Function.Bijective h.characters → IsIso t)
    (s : IdentityLieStructure P.pair.G.val) (r : IdentityLieStructure Q.pair.G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI := r.lieRing
    letI := r.lieAlgebra
    ∀ (e : Lie k P.pair.G.val ≃ₗ⁅k⁆ Lie k Q.pair.G.val),
      (∀ v, e (mapPointKernel P.pair.T.inclusion v) =
        mapPointKernel Q.pair.T.inclusion (mapPointKernel t v)) →
      (∀ (α : Root P.pair.T) v, v ∈ adjointWeightVectors P.pair.T α.val →
        e v ∈ adjointWeightVectors Q.pair.T (h.roots α).val) →
      (∀ α : SimpleRoot P.pair,
        e (rootTangent ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion)) =
          rootTangent ((Q.pin (h.simpleRoot α)).val.hom ≫ (Q.roots (h.roots α.val)).val.inclusion)) →
      Lifts P Q D E h := by
  have hCanonical_s := identityLieStructure_eq_canonical P.pair.G s
  subst s
  let s := identityLieStructure P.pair.G
  have hCanonical_r := identityLieStructure_eq_canonical Q.pair.G r
  subst r
  let r := identityLieStructure Q.pair.G
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := r.lieRing
  letI := r.lieAlgebra
  intro e he hroot hpin
  let G := P.pair.G
  let H := Q.pair.G
  obtain ⟨_, b, C₁, L₁, l₁, Ad₁, hAd₁, hbr₁, _⟩ := _root_.LinearAlgebraicGroups.adjointRepresentation k G s
  obtain ⟨C₂⟩ := tangentCoordinatesOfBasis H r (b.map e.toLinearEquiv)
  obtain ⟨L₂, l₂, Ad₂, hAd₂, hbr₂⟩ := adjointOfCoordinates H r C₂
  let T := Specs.Unipotent.closedSubgroupAlgebraicGroup P.pair.T
  let sT := identityLieStructure T
  letI := sT.lieRing
  letI := sT.lieAlgebra
  obtain ⟨_, _, ⟨CT⟩⟩ := tangent_coordinates T sT
  let B : AffineAlgebraicGroup k :=
    letI := A.operations.hopf
    Specs.StandardGroups.spectrum k (Polynomial k)
  let sB := identityLieStructure B
  letI := sB.lieRing
  letI := sB.lieAlgebra
  obtain ⟨_, _, ⟨CB⟩⟩ := tangent_coordinates B sB
  have hpins (α : SimpleRoot P.pair) (v : Lie k G.val)
      (hv : v.toMul.val = rootPoint ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion)
        (dualTest k) DualNumber.eps) :
      (e v).toMul.val = rootPoint ((Q.pin (h.simpleRoot α)).val.hom ≫
        (Q.roots (h.roots α.val)).val.inclusion) (dualTest k) DualNumber.eps := by
    have hv' : v = rootTangent _ := Additive.toMul.injective (Subtype.ext hv)
    rw [hv', hpin]
    rfl
  choose x y v hv hw hxy using fun α =>
    paired_root_coordinates LinearAlgebraicGroups.Classification.Pinning.coordinateVectors
      P Q D E h e.toLinearEquiv.toEquiv e.toLinearEquiv.map_zero hroot hpins α
  let j (α : Root P.pair.T) := (x α).val.symm ≪≫ (y α).val
  have hj (α : SimpleRoot P.pair) :
      (P.pin α).val.hom ≫ (j α.val).hom = (Q.pin (h.simpleRoot α)).val.hom := by
    obtain ⟨hx, hy⟩ := hxy α.val α.property
    change (P.pin α).val.hom ≫ ((x α.val).val.inv ≫ (y α.val).val.hom) = _
    rw [hx, hy, Iso.hom_inv_id_assoc]
  have hTor (R : TestAlgebra k) (z : GroupPoints P.pair.T.group (CommAlgCat.of k (DualNumber R))) :
      (lift (z ≫ P.pair.T.inclusion.hom.hom) (z ≫ t.hom.hom ≫ Q.pair.T.inclusion.hom.hom) :
        GroupPoints (G.val ⊗ H.val) (CommAlgCat.of k (DualNumber R))) ∈
      displacementSubgroup (reducePoints (G.val ⊗ H.val) R) (constantPoints (G.val ⊗ H.val) R)
        (tangentGraph C₁ C₂ R) := by
    have hD (x : Lie k T.val) : b.equivFun (mapPointKernel P.pair.T.inclusion x) =
        (b.map e.toLinearEquiv).equivFun (mapPointKernel (t ≫ Q.pair.T.inclusion) x) := by
      rw [← basis_map_coordinates b e, he]
      congr 1 <;> first | rfl | (apply Additive.toMul.injective; exact Subtype.ext (Category.assoc _ _ _))
    have hp := paired_morphism_mem C₁ C₂ CT P.pair.T.inclusion
      (t ≫ Q.pair.T.inclusion) hD R (fun g => ?_) z
    · simpa only [point_comp_pair, Grp.comp_hom_hom, Category.assoc] using hp
    let M := (l₁.hom.app R).hom (((groupPointsFunctor k).map Ad₁).app R
      (g ≫ P.pair.T.inclusion.hom.hom))
    have hm := torusAdjoint_agree h t ht s r e he hroot b l₁ l₂ Ad₁ Ad₂ hAd₁ hAd₂ R g
    refine ⟨matrixActionEquiv M, fun w => ?_, fun w => ?_⟩
    · exact hAd₁ R _ w
    · rw [matrixActionEquiv_apply, hm]
      exact hAd₂ R _ w
  have hRoot (α : Root P.pair.T) (R : TestAlgebra k)
      (z : GroupPoints (P.roots α).val.group (CommAlgCat.of k (DualNumber R))) :
      (lift (z ≫ (P.roots α).val.inclusion.hom.hom)
        (z ≫ (j α).hom.hom.hom ≫ (Q.roots (h.roots α)).val.inclusion.hom.hom) :
          GroupPoints (G.val ⊗ H.val) (CommAlgCat.of k (DualNumber R))) ∈
        displacementSubgroup (reducePoints (G.val ⊗ H.val) R) (constantPoints (G.val ⊗ H.val) R)
          (tangentGraph C₁ C₂ R) := by
    let p := (x α).val.hom ≫ (P.roots α).val.inclusion
    let q := (y α).val.hom ≫ (Q.roots (h.roots α)).val.inclusion
    have hD (u : Lie k B.val) : b.equivFun (mapPointKernel p u) =
        (b.map e.toLinearEquiv).equivFun (mapPointKernel q u) := by
      obtain ⟨a, ha⟩ := additiveLine_tangent_point A (Iso.refl _) u
      have h (u : Lie k B.val) {J : AffineAlgebraicGroup k}
          (s₀ : IdentityLieStructure J.val) (f : B.val ⟶ J.val) :
          letI := s₀.lieRing
          letI := s₀.lieAlgebra
          u.toMul.val = rootPoint (Iso.refl _).hom (dualTest k) (⟨0,a⟩ : DualNumber k) →
            mapPointKernel f u = a • rootTangent f := by
        letI := s₀.lieRing
        letI := s₀.lieAlgebra
        intro hu
        apply Additive.toMul.injective
        apply Subtype.ext
        change u.toMul.val ≫ f.hom.hom = _
        rw [rootPoint_scaledTangent s₀ f, hu, ← rootPoint_comp]
        simp only [Iso.refl_hom, Category.id_comp]
      have hp : rootTangent p = v α := Additive.toMul.injective (Subtype.ext (hv α).symm)
      have hq : rootTangent q = e (v α) := Additive.toMul.injective (Subtype.ext (hw α).symm)
      have hmap : e (a • v α) = a • e (v α) := by
        with_unfolding_all exact e.toLinearEquiv.map_smul a (v α)
      rw [h u s p ha, h u r q ha, hp, hq, ← hmap, basis_map_coordinates]
    let z₀ : GroupPoints B.val (CommAlgCat.of k (DualNumber R)) := z ≫ (x α).val.inv.hom.hom
    have hpair := paired_morphism_mem C₁ C₂ CB p q hD R (fun g => ?_) z₀
    · have hleft : (x α).val.inv ≫ p = (P.roots α).val.inclusion := by simp [p]
      have hright : (x α).val.inv ≫ q = (j α).hom ≫ (Q.roots (h.roots α)).val.inclusion :=
        (Category.assoc _ _ _).symm
      have h₁ : z₀ ≫ p.hom.hom = z ≫ (P.roots α).val.inclusion.hom.hom := by
        change (z ≫ (x α).val.inv.hom.hom) ≫ p.hom.hom = _
        rw [Category.assoc, ← Grp.comp_hom_hom, hleft]
      have h₂ : z₀ ≫ q.hom.hom = z ≫ (j α).hom.hom.hom ≫
          (Q.roots (h.roots α)).val.inclusion.hom.hom := by
        change (z ≫ (x α).val.inv.hom.hom) ≫ q.hom.hom = _
        rw [Category.assoc, ← Grp.comp_hom_hom, hright, Grp.comp_hom_hom]
      simpa only [point_comp_pair, h₁, h₂] using hpair
    obtain ⟨a, ha⟩ := (LinearAlgebraicGroups.RootData.RootGroups.additivePoints A R).surjective g
    have ha' : rootPoint (𝟙 A.group) R a = g := by
      rw [rootPoint_eq]
      change (LinearAlgebraicGroups.RootData.RootGroups.additivePoints A R) a ≫ 𝟙 _ = _
      rw [Category.comp_id, ha]
    have hgp : g ≫ p.hom.hom = rootPoint p R a := by rw [← ha', ← rootPoint_comp, Category.id_comp]
    have hgq : g ≫ q.hom.hom = rootPoint q R a := by rw [← ha', ← rootPoint_comp, Category.id_comp]
    let M := (l₁.hom.app R).hom (((groupPointsFunctor k).map Ad₁).app R (g ≫ p.hom.hom))
    have hm := paired_root_adjoint_matrices b e Ad₁ Ad₂ l₁ l₂ hbr₁ hbr₂ p q (v α) (hv α) (hw α) R a
    have hm' : M.val = ((l₂.hom.app R).hom (((groupPointsFunctor k).map Ad₂).app R
        (g ≫ q.hom.hom))).val := by
      change ((l₁.hom.app R).hom (g ≫ p.hom.hom ≫ Ad₁.hom.hom)).val = _
      rw [← Category.assoc, hgp]
      change _ = ((l₂.hom.app R).hom ((g ≫ q.hom.hom) ≫ Ad₂.hom.hom)).val
      rw [hgq]
      simpa only [rootMatrix, rootPoint_comp] using hm
    refine ⟨matrixActionEquiv M, fun w => ?_, fun w => ?_⟩
    · exact hAd₁ R _ w
    · rw [matrixActionEquiv_apply, hm']
      exact hAd₂ R _ w
  let borels := @LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT k _
  obtain ⟨c, C, hc, hC, hchamber⟩ := (borels G P.pair.reductive P.pair.T P.pair.split P.pair.maximal).1
    P.pair.B P.pair.borel P.pair.containsTorus
  let d := c ≫ t
  obtain ⟨hd, hchamber', _⟩ := map_borel_chamber h t ht c hc hchamber
  obtain ⟨F⟩ := LinearAlgebraicGroups.CocharacterDynamics.existsLimitDecomposition H (d ≫ Q.pair.T.inclusion)
  obtain ⟨_, hFB, hFT, hFroots, _, _⟩ := LinearAlgebraicGroups.RootData.BorelsAndChambers.regularCocharacterBorel
    H Q.pair.reductive Q.pair.T Q.pair.split Q.pair.maximal d hd F
  have hsystem : Specs.BorelsAndChambers.IsPositiveSystem Q.pair.T (positiveRoots Q.pair.T d) :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.positiveSystemsFromCocharacters
      H Q.pair.reductive Q.pair.T Q.pair.split Q.pair.maximal (positiveRoots Q.pair.T d)).mpr ⟨d, hd, rfl⟩
  obtain ⟨_, _, _, _, huniq⟩ :=
    ((borels H Q.pair.reductive Q.pair.T Q.pair.split Q.pair.maximal).2 _).mp hsystem
  have hF : SameSubgroup Q.pair.B F.parabolic := by
    have h₁ := huniq Q.pair.B Q.pair.borel Q.pair.containsTorus hchamber'
    have h₂ := huniq F.parabolic hFB hFT hFroots
    exact ⟨subgroupOf_trans h₁.2 h₂.1, subgroupOf_trans h₂.2 h₁.1⟩
  letI := D.comm
  letI := D.datum.finiteRoots
  obtain ⟨negative, hNegative⟩ := list_enumerates (positiveRoots P.pair.T (oppositeCocharacter c))
  obtain ⟨positive, hPositive⟩ := list_enumerates (positiveRoots P.pair.T c)
  have hpos (α : Root P.pair.T) (c₀ : Cocharacter P.pair.T.group) :
      α ∈ positiveRoots P.pair.T c₀ ↔ h.roots α ∈ positiveRoots Q.pair.T (c₀ ≫ t) := by
    change 0 < pairing P.pair.T.group α.val c₀ ↔
      0 < pairing Q.pair.T.group (h.roots α).val (c₀ ≫ t)
    rw [pairing_comp, ht, h.root_eq]
  have hopp : oppositeCocharacter c ≫ t = oppositeCocharacter d := Category.assoc _ _ _
  apply lifts_of_paired_root_cells word generic P Q D E h t hts ht hti j hj c d C F hc hd hC hF
    hchamber negative positive hNegative hPositive
  · exact enumerates_map h.roots (by simpa only [hopp] using fun α => hpos α (oppositeCocharacter c))
      hNegative
  · exact enumerates_map h.roots (fun α => hpos α c) hPositive
  · exact paired_cell_tangent_constraint P.roots Q.roots h.roots j t C₁ C₂ hTor hRoot negative positive

end LiftingFromLie

/-- In characteristic zero an ordinary based root-data isogeny lifts to
a central isogeny respecting the specified split pinnings. -/
theorem centralIsogeny : Statement.{u} := by
  intro k _ _ A P Q D E h
  by_cases h₀ : IsEmpty (Root P.pair.T)
  · exact lifting_of_no_roots P Q D E h h₀
  obtain ⟨t, ht, hts, _, hti⟩ := torusMap P.pair.split Q.pair.split
    h.characters h.injective h.finiteIndex
  let s := identityLieStructure P.pair.G
  let r := identityLieStructure Q.pair.G
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := r.lieRing
  letI := r.lieAlgebra
  obtain ⟨e, heT, heR, heP⟩ := pinnedLieComparison P Q D E h t ht s r
  exact liftFromLieComparison
    LinearAlgebraicGroups.RationalRealization.wordGeneratedGroup
    LinearAlgebraicGroups.RationalRealization.dominantGenericLift
    P Q D E h t ht hts hti s r e heT heR heP

end
end LinearAlgebraicGroups.CharZeroLifting
