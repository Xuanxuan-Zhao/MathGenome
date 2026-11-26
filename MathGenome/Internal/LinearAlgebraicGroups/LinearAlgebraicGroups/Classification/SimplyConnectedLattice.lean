import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRealization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.OrdinaryCentralLifting
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Noetherian

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open Module
open scoped BigOperators

universe u

namespace LinearAlgebraicGroups.Classification.SimplyConnectedLattice
noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

variable {I X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]

private abbrev corootSpan (P : RootDatum (ι := I) X Y) :=
  Submodule.span ℤ (Set.range P.coroot)

private theorem dualRank (V : Type u) [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V] :
    finrank ℤ (Dual ℤ V) = finrank ℤ V :=
  (Free.chooseBasis ℤ V).toDualEquiv.finrank_eq.symm

private theorem corootRank (P : RootDatum (ι := I) X Y) (B : P.Base) :
    finrank ℤ (corootSpan P) = finrank ℤ (Submodule.span ℤ (Set.range P.root)) := by
  classical
  unfold corootSpan
  rw [← B.span_int_coroot_support, ← B.span_int_root_support]
  have h₁ : Set.range (fun i : B.support => P.coroot i) = P.coroot '' ↑B.support := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have h₂ : Set.range (fun i : B.support => P.root i) = P.root '' ↑B.support := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← h₁, ← h₂]
  exact (finrank_span_eq_card (b := fun i : B.support => P.coroot i)
    B.linearIndepOn_coroot).trans
    (finrank_span_eq_card (b := fun i : B.support => P.root i)
      B.linearIndepOn_root).symm

private def restrictCharacters (P : RootDatum (ι := I) X Y) :
    X →ₗ[ℤ] Dual ℤ (corootSpan P) :=
  (corootSpan P).subtype.dualMap.comp P.toLinearMap

private theorem restrictCharacters_injective (P : RootDatum (ι := I) X Y)
    (h : Finite (Y ⧸ corootSpan P)) : Function.Injective (restrictCharacters P) := by
  letI := h
  apply (LinearMap.ker_eq_bot.mp ?_)
  rw [LinearMap.ker_eq_bot']
  intro x hx
  apply P.toLinearMap.toPerfPair.injective
  change P.toLinearMap x = P.toLinearMap 0
  ext y
  have hy : (corootSpan P).toAddSubgroup.index • y ∈ corootSpan P :=
    by simpa using! AddSubgroup.nsmul_index_mem (corootSpan P).toAddSubgroup y
  have hyzero : P.toLinearMap x ((corootSpan P).toAddSubgroup.index • y) = 0 :=
    LinearMap.congr_fun hx ⟨_, hy⟩
  rw [map_nsmul, nsmul_eq_mul] at hyzero
  have hn : (↑(corootSpan P).toAddSubgroup.index : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Y ⧸ corootSpan P)).ne'
  simp [((mul_eq_zero.mp hyzero).resolve_left hn)]

private def corootDatum (P : RootDatum (ι := I) X Y)
    (h : Function.Injective (restrictCharacters P)) :
    RootDatum (ι := I) (Dual ℤ (corootSpan P)) (corootSpan P) where
  toLinearMap := LinearMap.id
  root := ⟨restrictCharacters P ∘ P.root, h.comp P.root.injective⟩
  coroot := ⟨fun i => ⟨P.coroot i, Submodule.subset_span ⟨i, rfl⟩⟩,
    fun _ _ hij => P.coroot.injective (congrArg Subtype.val hij)⟩
  root_coroot_two i := P.root_coroot_two i
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    change restrictCharacters P (P.root j) -
      P.toLinearMap (P.root j) (P.coroot i) • restrictCharacters P (P.root i) = _
    rw [← map_smul, ← map_sub, P.reflectionPerm_root]
    rfl
  reflectionPerm_coroot i j := by
    apply Subtype.ext
    exact P.reflectionPerm_coroot i j

private theorem corootDatum_reduced (P : RootDatum (ι := I) X Y) (hP : P.IsReduced)
    (h : Function.Injective (restrictCharacters P)) : (corootDatum P h).IsReduced := by
  constructor
  intro i j hij
  have hdep : ¬ LinearIndependent ℤ ![P.root i, P.root j] := by
    intro hl
    apply hij
    have hm := hl.map' (restrictCharacters P) (LinearMap.ker_eq_bot.mpr h)
    convert hm using 1
    ext a
    fin_cases a <;> rfl
  obtain hEq | hNeg := hP.eq_or_eq_neg i j hdep
  · exact Or.inl (congrArg (restrictCharacters P) hEq)
  · exact Or.inr ((congrArg (restrictCharacters P) hNeg).trans (map_neg _ _))

private theorem mem_closure_map {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (f : A →+ B) (s : Set A) {x : A} (hx : x ∈ AddSubmonoid.closure s) :
    f x ∈ AddSubmonoid.closure (f '' s) := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx => exact AddSubmonoid.subset_closure ⟨x, hx, rfl⟩
  | zero => simpa using (AddSubmonoid.closure (f '' s)).zero_mem
  | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy

private def corootDatumBase (P : RootDatum (ι := I) X Y) (B : P.Base)
    (h : Function.Injective (restrictCharacters P)) : (corootDatum P h).Base where
  support := B.support
  linearIndepOn_root := B.linearIndepOn_root.map' _ (LinearMap.ker_eq_bot.mpr h)
  linearIndepOn_coroot := by
    apply LinearIndependent.of_comp (corootSpan P).subtype
    exact B.linearIndepOn_coroot
  root_mem_or_neg_mem i := by
    have hs : (restrictCharacters P) '' (P.root '' ↑B.support) =
        (corootDatum P h).root '' ↑B.support := Set.image_image _ _ _
    have transfer {x} (hx : x ∈ AddSubmonoid.closure (P.root '' ↑B.support)) :
        restrictCharacters P x ∈ AddSubmonoid.closure ((corootDatum P h).root '' ↑B.support) := by
      rw [← hs]
      exact mem_closure_map (restrictCharacters P).toAddMonoidHom _ hx
    rcases B.root_mem_or_neg_mem i with hi | hi
    · exact Or.inl (transfer hi)
    · exact Or.inr (by simpa only [map_neg, corootDatum, Function.comp_apply, Function.Embedding.coeFn_mk] using transfer hi)
  coroot_mem_or_neg_mem i := by
    let P' := corootDatum P h
    let L := corootSpan P
    let C := AddSubmonoid.closure (P'.coroot '' (B.support : Set I))
    have hs : C.map L.subtype.toAddMonoidHom =
        AddSubmonoid.closure (P.coroot '' (B.support : Set I)) := by
      rw [AddMonoidHom.map_mclosure, Set.image_image]
      rfl
    have transfer {y : L} (hy : (y : Y) ∈ AddSubmonoid.closure (P.coroot '' ↑B.support)) :
        y ∈ C := by
      rw [← hs] at hy
      obtain ⟨z, hz, he⟩ := hy
      exact (Subtype.ext he : z = y) ▸ hz
    rcases B.coroot_mem_or_neg_mem i with hi | hi
    · exact Or.inl (transfer (y := P'.coroot i) hi)
    · exact Or.inr (transfer (y := -P'.coroot i) hi)

private theorem corootDatum_span (P : RootDatum (ι := I) X Y)
    (h : Function.Injective (restrictCharacters P)) :
    Submodule.span ℤ (Set.range (corootDatum P h).coroot) = ⊤ := by
  apply Submodule.map_injective_of_injective (corootSpan P).subtype_injective
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  congr 1
  exact (Set.range_comp _ _).symm

private theorem corootFullRank (P : RootDatum (ι := I) X Y) (B : P.Base) :
    finrank ℤ (corootSpan P) = finrank ℤ Y ↔
      finrank ℤ (Submodule.span ℤ (Set.range P.root)) = finrank ℤ X := by
  have h : finrank ℤ X = finrank ℤ Y :=
    P.toLinearMap.toPerfPair.finrank_eq.trans (dualRank Y)
  rw [corootRank P B, h]

private theorem restrictCharacters_surjective (P : RootDatum (ι := I) X Y)
    (h : corootSpan P = ⊤) : Function.Surjective (restrictCharacters P) := by
  intro χ
  have hs : Function.Surjective (corootSpan P).subtype :=
    (LinearMap.range_eq_top).mp ((corootSpan P).range_subtype.trans h)
  let e := LinearEquiv.ofBijective (corootSpan P).subtype ⟨Subtype.val_injective, hs⟩
  refine ⟨P.toLinearMap.toPerfPair.symm (e.symm.toLinearMap.dualMap χ), ?_⟩
  ext y
  change P.toLinearMap.toPerfPair (P.toLinearMap.toPerfPair.symm
    (e.symm.toLinearMap.dualMap χ)) (e y) = χ y
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg χ (e.symm_apply_apply y)

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

open _root_.LinearAlgebraicGroups.Specs
open Specs.SimplyConnectedLattice
open Specs.AbstractPairing (Datum IsAttachedCoroot Root)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.CentralIsogenies (IsCentralIsogeny IsTorusRestriction characterPullback)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap diagonalRestriction diagonalClosedInclusion)
open Specs.GeometricRadicals (GeometricGroup IsReductive IsSemisimple IsSplitTorus IsTorus
  IsMaximalTorus baseChangedSubgroup)
open Specs.Pinning (AttachedDatum BasedRootDatum PinnedGroup SplitBorelPair)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.RootGroups (AdditiveLine)
open Specs.SchemeCentre (rootLattice)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Classification.CentralIsogenies (centralIsogenyComparison kernel_le_maximalTorus)
open private reductive_of_semisimple flat_of_surjective_torus_map
  diagonalIso diagonalCharacterMap pairing_pushforward
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private schemeKernel_sections schemeKernel_exists quotientRepresentsImage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private groupAlgebraMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private isIso_of_schemeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private torus_smooth_connected_solvable from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private splitTorusSmooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
open private reducedIdentityPreimage soluble_of_finite_to_commutative finite_zero_isTrivial
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
open private isIso_of_trivial_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private baseChangeMapPullback baseChangeKernelSquare
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private exists_regular_cocharacter from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private theorem finiteDiagonal_iff (M : Type u) [CommGroup M] :
    IsFinite (specGroup (groupAlgebra k M)).X.hom ↔ Finite M := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k M)))) ↔ _
  rw [IsFinite.SpecMap_iff]
  change (algebraMap k (MonoidAlgebra k M)).Finite ↔ _
  rw [RingHom.finite_algebraMap]
  constructor
  · intro h
    letI := h
    exact (MonoidAlgebra.basis M k).linearIndependent.finite
  · intro h
    letI := Fintype.ofFinite M
    exact Module.Finite.of_basis (MonoidAlgebra.basis M k)

private theorem finiteMultiplicativeQuotient_iff {M : Type u} [CommGroup M]
    (N : Subgroup M) :
    Finite (M ⧸ N) ↔ Finite (Additive M ⧸ N.toAddSubgroup.toIntSubmodule) := by
  let e : (M ⧸ N) ≃ (Additive M ⧸ N.toAddSubgroup.toIntSubmodule) :=
    Quotient.congr (Equiv.refl M) (fun a b => by
      change QuotientGroup.leftRel N a b ↔ QuotientAddGroup.leftRel N.toAddSubgroup a b
      exact Iff.rfl)
  constructor
  · intro h
    exact Finite.of_equiv _ e
  · intro h
    exact Finite.of_equiv _ e.symm

private theorem rootFullRank_iff (P : SplitBorelPair k) (D : AttachedDatum P) :
    letI := D.comm
    IsSemisimple P.G ↔
      finrank ℤ (Submodule.span ℤ (Set.range D.datum.rootDatum.root)) =
        finrank ℤ (Additive (Character P.T.group)) := by
  letI := D.comm
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  obtain ⟨_, e, _, hi, hz, _⟩ :=
    RootData.SchemeCentre.schemeCentre P.G P.reductive P.T P.split P.maximal
  let Z : ClosedSubgroup P.G.val :=
    ⟨specGroup (groupAlgebra k (Character P.T.group ⧸ rootLattice P.T)),
      diagonalClosedInclusion k (rootLattice P.T) ≫ e.hom ≫ P.T.inclusion, hi⟩
  have hroots : Set.range D.datum.rootDatum.root =
      Additive.toMul ⁻¹' absoluteRoots P.T := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [D.datum.root_eq]
      exact i.property
    · intro hx
      exact ⟨⟨Additive.toMul x, hx⟩, D.datum.root_eq _⟩
  have heq : (rootLattice P.T).toAddSubgroup.toIntSubmodule =
      Submodule.span ℤ (Set.range D.datum.rootDatum.root) := by
    apply Submodule.toAddSubgroup_injective
    change (rootLattice P.T).toAddSubgroup = _
    rw [Submodule.span_int_eq_addSubgroupClosure, rootLattice, Subgroup.toAddSubgroup_closure, hroots]
  have hquot : Finite (Additive (Character P.T.group) ⧸ (rootLattice P.T).toAddSubgroup.toIntSubmodule) ↔
      finrank ℤ (Submodule.span ℤ (Set.range D.datum.rootDatum.root)) =
        finrank ℤ (Additive (Character P.T.group)) := by
    rw [heq]
    exact Submodule.finiteQuotient_iff _
  exact (Reductive.CentralDerived.semisimpleIffFiniteCentre P.G P.reductive Z hz).trans
    ((finiteDiagonal_iff (k := k) _).trans ((finiteMultiplicativeQuotient_iff _).trans hquot))

private theorem semisimple_iff_corootFullRank (P : SplitBorelPair k) (D : AttachedDatum P) :
    letI := D.comm
    IsSemisimple P.G ↔
      finrank ℤ (corootLattice D) = finrank ℤ (Additive (Cocharacter P.T.group)) := by
  letI := D.comm
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  exact (rootFullRank_iff P D).trans (corootFullRank _ D.base).symm

private def simplyConnectedDatum (D : BasedRootDatum.{u})
    (h : Finite (D.Y ⧸ corootSpan D.datum)) : BasedRootDatum.{u} := by
  letI := D.freeY
  letI := D.finiteY
  letI := D.freeX
  letI := D.finiteX
  exact {
    I := D.I
    X := Dual ℤ (corootSpan D.datum)
    Y := corootSpan D.datum
    finiteRoots := D.finiteRoots
    freeX := inferInstance
    finiteX := inferInstance
    freeY := inferInstance
    finiteY := inferInstance
    datum := corootDatum D.datum (restrictCharacters_injective D.datum h)
    reduced := corootDatum_reduced D.datum D.reduced _
    base := corootDatumBase D.datum D.base _ }

private theorem realization_corootSpan {A : AdditiveLine k}
    {D : BasedRootDatum.{u}} (F : RationalRealization.Realization D A)
    (h : corootSpan D.datum = ⊤) : corootLattice F.attached = ⊤ := by
  letI := F.attached.comm
  let e := F.datumIso.val
  have hcoroot (i : D.I) :
      e.coweightEquiv.symm (D.datum.coroot i) =
        F.attached.datum.rootDatum.coroot (e.indexEquiv i) := by
    apply e.coweightEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact ((RootPairing.Hom.coroot_coweightMap_apply D.datum F.attached.toBased.datum
      (e.indexEquiv i) e.toHom).trans
        (congrArg D.datum.coroot (e.indexEquiv.symm_apply_apply i))).symm
  have hr : e.coweightEquiv.symm '' Set.range D.datum.coroot =
      Set.range F.attached.toBased.datum.coroot := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨e.indexEquiv i, (hcoroot i).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨D.datum.coroot (e.indexEquiv.symm j), ⟨_, rfl⟩, ?_⟩
      exact (hcoroot _).trans
        (congrArg F.attached.toBased.datum.coroot (e.indexEquiv.apply_symm_apply j))
  change Submodule.span ℤ (Set.range F.attached.toBased.datum.coroot) = ⊤
  calc
    Submodule.span ℤ (Set.range F.attached.toBased.datum.coroot) =
        Submodule.span ℤ (e.coweightEquiv.symm '' Set.range D.datum.coroot) := by rw [hr]
    _ = (corootSpan D.datum).map e.coweightEquiv.symm.toLinearMap :=
      (Submodule.map_span e.coweightEquiv.symm.toLinearMap _).symm
    _ = ⊤ := by
      rw [h, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr e.coweightEquiv.symm.surjective

private theorem of_fullCorootLattice (P : SplitBorelPair k) (D : AttachedDatum P)
    (h : corootLattice D = ⊤) : IsSemisimple P.G := by
  letI := D.comm
  apply (semisimple_iff_corootFullRank P D).mpr
  rw [h, finrank_top]

private abbrev underlying (k : Type u) [Field k] : GroupScheme k ⥤ Scheme.{u} :=
  Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))

private theorem splitTorusMap_of_injective_pullback
    (P Q : SplitBorelPair k) (τ : P.T.group ⟶ Q.T.group)
    (hτ : Function.Injective (characterPullback τ)) :
    Flat τ.hom.hom.left ∧ Surjective τ.hom.hom.left ∧
      (Function.Surjective (characterPullback τ) → IsIso τ) := by
  obtain ⟨fg, eP, heP, _, _, _⟩ :=
    RootData.SchemeCentre.schemeCentre P.G P.reductive P.T P.split P.maximal
  obtain ⟨_, eQ, heQ, _, _, _⟩ :=
    RootData.SchemeCentre.schemeCentre Q.G Q.reductive Q.T Q.split Q.maximal
  letI := fg
  let l := characterPullback τ
  have hd := diagonalCharacterMap τ eP eQ heP heQ
  let j : Character Q.T.group ≃* l.range :=
    MulEquiv.ofBijective l.rangeRestrict ⟨fun x y h => hτ (congrArg Subtype.val h),
      fun ⟨x, hx⟩ => by obtain ⟨y, rfl⟩ := hx; exact ⟨y, rfl⟩⟩
  have hj : l.range.subtype.comp j.toMonoidHom = l := rfl
  let i := diagonalIso (k := k) j
  have hdiag : diagonalRestriction k l.range ≫ i.hom = specGroupMap (groupAlgebraMap k l) := by
    change specGroupMap (groupAlgebraMap k l.range.subtype) ≫
      specGroupMap (groupAlgebraMap k j.toMonoidHom) = _
    rw [← specGroupMap_comp, groupAlgebraMap_comp, hj]
  have hτeq : τ = eP.inv ≫ diagonalRestriction k l.range ≫ i.hom ≫ eQ.hom := by
    rw [← Category.assoc (diagonalRestriction k l.range), hdiag, ← hd]
    simp
  obtain ⟨_, hflat, hsurj, _, _, _⟩ :=
    DiagonalizableGroups.diagonalRestrictionKernelAndQuotient k (Character P.T.group) l.range
  letI := hflat
  letI := hsurj
  have hmorph := congrArg (underlying k).map hτeq
  simp only [Functor.map_comp] at hmorph
  rw [show (underlying k).map τ = τ.hom.hom.left from rfl] at hmorph
  have hflat' : Flat τ.hom.hom.left := by
    rw [hmorph]
    change Flat ((underlying k).map eP.inv ≫
      (diagonalRestriction k l.range).hom.hom.left ≫
      (underlying k).map i.hom ≫ (underlying k).map eQ.hom)
    infer_instance
  have hsurj' : Surjective τ.hom.hom.left := by
    rw [hmorph]
    change Surjective ((underlying k).map eP.inv ≫
      (diagonalRestriction k l.range).hom.hom.left ≫
      (underlying k).map i.hom ≫ (underlying k).map eQ.hom)
    infer_instance
  refine ⟨hflat', hsurj', fun hs => ?_⟩
  let a : Character Q.T.group ≃* Character P.T.group := MulEquiv.ofBijective l ⟨hτ, hs⟩
  let b := diagonalIso (k := k) a
  have hb : eP.hom ≫ τ = b.hom ≫ eQ.hom := hd
  rw [show τ = eP.inv ≫ b.hom ≫ eQ.hom by rw [← hb]; simp]
  infer_instance

private theorem restrictionCharacters_eq {T S : GroupScheme k}
    (τ : T ⟶ S) :
    CellHomomorphism.pullbackCharacters τ = characterPullback τ :=
  MonoidHom.ext fun _ => rfl

private theorem liftFromCorootDatum {A : AdditiveLine k}
    (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (hfin : letI := D.comm; Finite ((Additive (Cocharacter P.pair.T.group)) ⧸ corootLattice D))
    (F : RationalRealization.Realization (simplyConnectedDatum D.toBased hfin) A) :
    letI := D.comm
    letI := F.attached.comm
    ∃ (f : F.pinned.pair.G.val ⟶ P.pair.G.val) (τ : F.pinned.pair.T.group ⟶ P.pair.T.group),
      IsCentralIsogeny f ∧ IsTorusRestriction f τ ∧
      (corootLattice D = ⊤ → IsIso f) ∧
      ∃ e : Additive (Cocharacter F.pinned.pair.T.group) ≃ₗ[ℤ] corootLattice D,
        ∀ c : Cocharacter F.pinned.pair.T.group,
          (e (Additive.ofMul c)).val = Additive.ofMul (c ≫ τ) := by
  letI := D.comm
  letI := F.attached.comm
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  let B := simplyConnectedDatum D.toBased hfin
  let E := F.attached
  let e := F.datumIso.val
  let l := e.weightEquiv.toLinearMap.comp (restrictCharacters D.datum.rootDatum)
  let h : Character P.pair.T.group →* Character F.pinned.pair.T.group :=
    (l.toAddMonoidHom).toMultiplicative
  have hinj : Function.Injective h := by
    intro χ ψ hχψ
    have hEq : e.weightEquiv (restrictCharacters D.datum.rootDatum (Additive.ofMul χ)) =
        e.weightEquiv (restrictCharacters D.datum.rootDatum (Additive.ofMul ψ)) := hχψ
    exact congrArg Additive.toMul ((restrictCharacters_injective D.datum.rootDatum hfin)
      (e.weightEquiv.injective hEq))
  have hindex : Finite (Character F.pinned.pair.T.group ⧸ h.range) := by
    apply (finiteMultiplicativeQuotient_iff _).mpr
    have hl : h.range.toAddSubgroup.toIntSubmodule = LinearMap.range l := by
      ext x
      rfl
    rw [hl]
    letI := E.datum.freeCharacters
    letI := E.datum.finiteCharacters
    apply Submodule.finiteQuotientOfFreeOfRankEq
    have hr := (Submodule.finiteQuotient_iff (corootLattice D)).mp hfin
    calc
      finrank ℤ (LinearMap.range l) = finrank ℤ D.toBased.X :=
        (LinearEquiv.ofInjective l hinj).finrank_eq.symm
      _ = finrank ℤ D.toBased.Y :=
        D.datum.rootDatum.toLinearMap.toPerfPair.finrank_eq.trans (dualRank _)
      _ = finrank ℤ (corootLattice D) := hr.symm
      _ = finrank ℤ B.X := (dualRank _).symm
      _ = finrank ℤ E.toBased.X := e.weightEquiv.finrank_eq
  let d : Root F.pinned.pair.T ≃ Root P.pair.T := e.indexEquiv.symm
  have hroot (α : Root F.pinned.pair.T) : h (d α).val = α.val := by
    apply Additive.ofMul.injective
    change e.weightEquiv (restrictCharacters D.datum.rootDatum (Additive.ofMul (d α).val)) =
      Additive.ofMul α.val
    rw [← D.datum.root_eq, ← E.datum.root_eq]
    exact (RootPairing.Hom.root_weightMap_apply _ _ (d α) e.toHom).trans
      (congrArg E.datum.rootDatum.root (e.indexEquiv.apply_symm_apply α))
  have htranspose (χ : Character P.pair.T.group) (c : Cocharacter F.pinned.pair.T.group) :
      pairing F.pinned.pair.T.group (h χ) c =
      D.datum.rootDatum.toLinearMap (Additive.ofMul χ) (e.coweightEquiv (Additive.ofMul c)).val := by
    rw [← E.datum.pairing_eq]
    exact e.toLinearMap_weightEquiv (restrictCharacters D.datum.rootDatum (Additive.ofMul χ))
      (Additive.ofMul c)
  have hcoroot (α : Root F.pinned.pair.T) (χ : Character P.pair.T.group) :
      pairing F.pinned.pair.T.group (h χ) (Additive.toMul (E.datum.rootDatum.coroot α)) =
      pairing P.pair.T.group χ (Additive.toMul (D.datum.rootDatum.coroot (d α))) := by
    rw [htranspose, ← D.datum.pairing_eq]
    exact congrArg (fun y : corootLattice D => D.datum.rootDatum.toLinearMap (Additive.ofMul χ) y.val)
      (RootPairing.Hom.coroot_coweightMap_apply B.datum E.toBased.datum α e.toHom)
  have hbase (α : Root F.pinned.pair.T) : α ∈ E.base.support ↔ d α ∈ D.base.support := by
    have hh := F.datumIso.property
    change e.indexEquiv '' (D.base.support : Set (Root P.pair.T)) =
      (E.base.support : Set (Root F.pinned.pair.T)) at hh
    change α ∈ (E.base.support : Set (Root F.pinned.pair.T)) ↔ d α ∈ (D.base.support : Set (Root P.pair.T))
    rw [← hh]
    rw [Equiv.image_eq_preimage_symm]
    exact Iff.rfl
  obtain ⟨τ, f, hτ, hmatch, hfinite, hflat, hsurj, ⟨N, _, _, hi, hN⟩, hiso, _⟩ :=
    Classification.OrdinaryCentralLifting.ordinaryCentralLifting
      F.pinned P E D d h hinj hindex hroot hcoroot hbase
  rw [restrictionCharacters_eq] at hτ
  have hfT := splitTorusMap_of_injective_pullback F.pinned.pair P.pair τ (hτ.symm ▸ hinj)
  refine ⟨f, τ, ⟨hfinite, hflat, hsurj, ⟨⟨N.group, N.inclusion ≫ F.pinned.pair.T.inclusion, hi⟩,
    hN⟩⟩, ⟨hmatch.1.symm, hfT.1, hfT.2.1⟩, ?_, e.coweightEquiv, ?_⟩
  · intro htop
    apply hiso
    intro χ
    obtain ⟨ψ, hψ⟩ := e.weightEquiv.surjective (Additive.ofMul χ)
    obtain ⟨ζ, hζ⟩ := restrictCharacters_surjective D.datum.rootDatum htop ψ
    refine ⟨ζ.toMul, ?_⟩
    change Additive.toMul (e.weightEquiv (restrictCharacters D.datum.rootDatum ζ)) = χ
    rw [hζ, hψ]
    rfl
  · intro c
    apply D.datum.rootDatum.toLinearMap.flip.toPerfPair.injective
    ext χ
    change D.datum.rootDatum.toLinearMap χ (e.coweightEquiv (Additive.ofMul c)).val =
      D.datum.rootDatum.toLinearMap χ (Additive.ofMul (c ≫ τ))
    calc
      _ = pairing F.pinned.pair.T.group (h χ.toMul) c := (htranspose χ.toMul c).symm
      _ = pairing F.pinned.pair.T.group (characterPullback τ χ.toMul) c := by
        rw [hτ]
      _ = pairing P.pair.T.group χ.toMul (c ≫ τ) := (pairing_pushforward τ χ.toMul c).symm
      _ = _ := (D.datum.pairing_eq χ.toMul (c ≫ τ)).symm


open private maximalTorus_of_geometricallyMaximal geometricallyMaximal_of_maximal_split
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private image_of_geometric_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
open private descendClosedFactor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_multiplicativeType from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isMonHom_of_comp_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

private def splitBorelPair (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T) :
    SplitBorelPair k := by
  let hex := exists_regular_cocharacter G T hs
  let c := hex.choose
  let D := Classical.choice (LinearAlgebraicGroups.CocharacterDynamics.existsLimitDecomposition G
    (c ≫ T.inclusion))
  have h := RootData.BorelsAndChambers.regularCocharacterBorel G hG T hs hm c hex.choose_spec D
  exact ⟨G, hG, T, hs, hm, D.parabolic, h.2.1, h.2.2.1⟩

private theorem maximalTorus_lift [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (Q : SplitBorelPair k) (f : G.val ⟶ Q.G.val) (hf : IsCentralIsogeny f) :
    ∃ (T : ClosedSubgroup G.val) (τ : T.group ⟶ Q.T.group),
      IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧ IsTorusRestriction f τ := by
  letI := hf.1
  letI := hf.2.1
  letI := hf.2.2.1
  letI := hG.2.1
  letI := Q.G.property.2.1
  letI := LocallyOfFiniteType.isLocallyNoetherian Q.G.val.X.hom
  let L := closedSubgroupAlgebraicGroup Q.T
  have hQt := isTorus_of_split Q.split
  have hQmax := maximalTorus_of_geometricallyMaximal Q.G Q.T hQt Q.maximal
  have hQt' := torus_smooth_connected_solvable L hQt
  obtain ⟨T, p, hp, hs, hc, hpfin, hpsurj, _, hlift⟩ :=
    reducedIdentityPreimage (G := G) (Q := Q.G) f hG.1
      (GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom) Q.T hQt'.2.1
  let A := closedSubgroupAlgebraicGroup T
  letI := torus_commutative L hQt
  letI := hpfin
  obtain ⟨U, D, d, hU, hd, hDs, _, _⟩ := GeometricTorusSplitting.splitting A hs hc
    (soluble_of_finite_to_commutative (G := A) (Q := L) p hs hc)
  let U₀ := closedSubgroupAlgebraicGroup (G := A) U
  have hzero : U.inclusion ≫ p = 0 :=
    Unipotent.homFromUnipotentToMultiplicativeType U₀ L _ hU.2.2.2.1
      (torus_multiplicativeType ((isTorus_iff_coordinates L).mp hQt))
  letI := U.isClosedImmersion
  have hfin : IsFinite (U.inclusion ≫ p).hom.hom.left :=
    inferInstanceAs (IsFinite (U.inclusion.hom.hom.left ≫ p.hom.hom.left))
  have htriv := finite_zero_isTrivial (G := U₀) (Q := L) _ hfin hzero hU.1 hU.2.1
  letI : IsIso d := isIso_of_trivial_kernel d U hd htriv
  obtain ⟨r, ⟨e⟩⟩ := hDs
  have hTsplit : IsSplitTorus T.group := ⟨r, ⟨asIso d ≪≫ e⟩⟩
  letI : Flat p.hom.hom.left := flat_of_surjective_torus_map p Q.split hpsurj
  have hmax : IsMaximalTorus T := by
    refine ⟨isTorus_of_split hTsplit, ?_⟩
    intro S hS hTS
    obtain ⟨a, ha⟩ := hTS
    obtain ⟨V, b, hV, hb⟩ := image_of_geometric_torus
      (G := closedSubgroupAlgebraicGroup S) (Q := Q.G) (S.inclusion ≫ f) hS
    letI := V.isClosedImmersion
    letI : Mono V.inclusion.hom.hom := Over.mono_of_mono_left _
    letI : IsAffine T.group.X.left := A.property.1
    letI : IsAffine Q.T.group.X.left := L.property.1
    letI := hpsurj
    have hcomm : (a ≫ b) ≫ V.inclusion = p ≫ Q.T.inclusion := by
      rw [Category.assoc, hb, ← Category.assoc, ha, hp]
    obtain ⟨v, hv⟩ := descendClosedFactor p.hom.hom V.inclusion.hom.hom Q.T.inclusion.hom.hom
      (a ≫ b).hom.hom (congrArg (Grp.forget (SchemeOver k)).map hcomm)
    letI := isMonHom_of_comp_closed v Q.T.inclusion V.inclusion hv
    obtain ⟨w, hw⟩ := hQmax.2 V hV ⟨Grp.homMk v, Grp.hom_ext _ _ hv⟩
    have hbf : S.inclusion ≫ f = (b ≫ w) ≫ Q.T.inclusion := by
      rw [Category.assoc, hw, hb]
    have hS' := torus_smooth_connected_solvable (closedSubgroupAlgebraicGroup S) hS
    exact hlift S (b ≫ w) hbf hS'.1 hS'.2.1
  exact ⟨T, p, hTsplit, geometricallyMaximal_of_maximal_split G T hmax hTsplit,
    hp.symm, inferInstance, hpsurj⟩

private def pushCocharacters {T S : GroupScheme k} [IsCommMonObj T.X] [IsCommMonObj S.X]
    (τ : T ⟶ S) : Additive (Cocharacter T) →ₗ[ℤ] Additive (Cocharacter S) :=
  (show Cocharacter T →* Cocharacter S from
    { toFun := fun c => c ≫ τ
      map_one' := Grp.hom_ext _ _ (MonObj.one_comp τ.hom.hom)
      map_mul' := fun c d => Grp.hom_ext _ _ (MonObj.mul_comp c.hom.hom d.hom.hom τ.hom.hom)
    }).toAdditive.toIntLinearMap

private theorem dualSurjective {X₁ X₂ Y₁ Y₂ : Type u}
    [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup Y₁] [AddCommGroup Y₂]
    (b₁ : X₁ →ₗ[ℤ] Y₁ →ₗ[ℤ] ℤ) (b₂ : X₂ →ₗ[ℤ] Y₂ →ₗ[ℤ] ℤ)
    [b₁.IsPerfPair] [b₂.IsPerfPair]
    (h : X₂ →ₗ[ℤ] X₁) (g : Y₁ →ₗ[ℤ] Y₂)
    (ht : ∀ x y, b₁ (h x) y = b₂ x (g y))
    (hf : Finite (X₁ ⧸ LinearMap.range h)) (hg : Function.Surjective g) :
    Function.Surjective h := by
  letI := hf
  have hgi : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro y hy
    apply b₁.flip.toPerfPair.injective
    ext x
    have hx : (LinearMap.range h).toAddSubgroup.index • x ∈ LinearMap.range h :=
      by simpa using! AddSubgroup.nsmul_index_mem (LinearMap.range h).toAddSubgroup x
    obtain ⟨z, hz⟩ := hx
    have hz' : b₁ (h z) y = 0 := by rw [ht, hy, map_zero]
    rw [hz, map_nsmul, LinearMap.coe_smul, Pi.smul_apply, nsmul_eq_mul] at hz'
    have hn : (↑(LinearMap.range h).toAddSubgroup.index : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := X₁ ⧸ LinearMap.range h)).ne'
    simpa using (mul_eq_zero.mp hz').resolve_left hn
  let e := LinearEquiv.ofBijective g ⟨hgi, hg⟩
  intro x
  let z := b₂.toPerfPair.symm (e.symm.toLinearMap.dualMap (b₁ x))
  refine ⟨z, b₁.toPerfPair.injective ?_⟩
  ext y
  change b₁ (h z) y = b₁ x y
  rw [ht]
  change b₂.toPerfPair z (e y) = _
  rw [show b₂.toPerfPair z = _ from b₂.toPerfPair.apply_symm_apply _]
  exact congrArg (b₁ x) (e.symm_apply_apply y)

private theorem centralIsogeny_iso_of_torus_iso (P Q : SplitBorelPair k)
    (f : P.G.val ⟶ Q.G.val) (τ : P.T.group ⟶ Q.T.group)
    (hf : IsCentralIsogeny f) (hτ : IsTorusRestriction f τ) [IsIso τ] :
    IsIso f := by
  obtain ⟨hfin, hflat, hsurj, N, hk, hc⟩ := hf
  obtain ⟨a, ha⟩ := kernel_le_maximalTorus RootData.SchemeCentre.schemeCentre
    P.G P.reductive P.T P.split P.maximal N hc
  letI := Q.T.isClosedImmersion
  letI : Mono Q.T.inclusion.hom.hom := Over.mono_of_mono_left _
  haveI : Mono τ.hom.hom := inferInstanceAs (Mono ((Grp.forget (SchemeOver k)).map τ))
  have hkill (Y : SchemeOver k) (z : Y ⟶ N.group.X) :
      z ≫ N.inclusion.hom.hom = 1 := by
    have hh := (schemeKernel_sections hk (z ≫ N.inclusion.hom.hom)).mp ⟨z, rfl⟩
    have hcomp : N.inclusion ≫ f = a ≫ τ ≫ Q.T.inclusion := by
      rw [← ha, Category.assoc, hτ.1]
    have hza : (z ≫ a.hom.hom) ≫ τ.hom.hom = 1 := by
      apply (cancel_mono Q.T.inclusion.hom.hom).mp
      rw [MonObj.one_comp, Category.assoc, Category.assoc]
      change z ≫ (a ≫ τ ≫ Q.T.inclusion).hom.hom = _
      rw [← hcomp]
      change z ≫ N.inclusion.hom.hom ≫ f.hom.hom = 1
      rwa [← Category.assoc]
    have hz : z ≫ a.hom.hom = 1 :=
      (cancel_mono τ.hom.hom).mp (hza.trans (MonObj.one_comp τ.hom.hom).symm)
    rw [← ha]
    change z ≫ a.hom.hom ≫ P.T.inclusion.hom.hom = 1
    rw [← Category.assoc, hz, MonObj.one_comp]
  letI : Mono f.hom.hom := ⟨fun {Y} x y he => by
    have hh : (x * y⁻¹) ≫ f.hom.hom = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, he, mul_inv_cancel]
    obtain ⟨z, hz⟩ := (schemeKernel_sections hk _).mpr hh
    exact mul_inv_eq_one.mp (hz.symm.trans (hkill Y z))⟩
  letI := hflat
  letI := hsurj
  letI := P.G.property.1
  letI := Q.G.property.1
  letI : IsIso f.hom.hom.left := AlgebraicGeometry.Flat.isIso_of_surjective_of_mono _
  exact isIso_of_schemeIso f

private theorem noCentralCovers_of_span [IsAlgClosed k] (Q : SplitBorelPair k) (E : AttachedDatum Q)
    (hE : corootLattice E = ⊤) (G : AffineAlgebraicGroup k) (hG : IsSemisimple G)
    (f : G.val ⟶ Q.G.val) (hf : IsCentralIsogeny f) : IsIso f := by
  have hr := reductive_of_semisimple G hG
  obtain ⟨T, τ, hs, hm, hfT⟩ := maximalTorus_lift G hr Q f hf
  let P := splitBorelPair G hr T hs hm
  let D := Classification.Pinning.attachedDatum P
  letI : IsCommMonObj P.T.group.X := D.comm
  letI := E.comm
  obtain ⟨hinj, hfin, hb, hcmp⟩ :=
    centralIsogenyComparison G Q.G hr Q.reductive T Q.T hs hm Q.split Q.maximal f τ hf hfT.1 hfT.2.2
  let τP : P.T.group ⟶ Q.T.group := τ
  let h := (characterPullback τP).toAdditive.toIntLinearMap
  let g := pushCocharacters τP
  have hgs : Function.Surjective g := by
    apply LinearMap.range_eq_top.mp
    apply eq_top_iff.mpr
    rw [← hE]
    apply Submodule.span_le.mpr
    rintro _ ⟨β, rfl⟩
    let α : Root P.T := ⟨characterPullback τP β.val, hb.mapsTo β.property⟩
    have ht := (hcmp β.val β.property α.property).2 _ _ (D.datum.attached α) (E.datum.attached β)
    refine ⟨D.datum.rootDatum.coroot α, ?_⟩
    exact Additive.toMul.injective ht
  have hfin' : Finite (Additive (Character P.T.group) ⧸ LinearMap.range h) :=
    (finiteMultiplicativeQuotient_iff (characterPullback τP).range).mp hfin
  have hsurj : Function.Surjective (characterPullback τP) :=
    dualSurjective D.datum.rootDatum.toLinearMap E.datum.rootDatum.toLinearMap h g
      (fun x y => (D.datum.pairing_eq (characterPullback τP x.toMul) y.toMul).trans
        ((pairing_pushforward τP x.toMul y.toMul).symm.trans
          (E.datum.pairing_eq x.toMul (y.toMul ≫ τP)).symm)) hfin' hgs
  letI := (splitTorusMap_of_injective_pullback P Q τP hinj).2.2 hsurj
  exact centralIsogeny_iso_of_torus_iso P Q f τP hf hfT

open private fieldSpecMap_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

private theorem centralIsogeny_postIso {G H J : GroupScheme k} {f : G ⟶ H}
    (e : H ≅ J) (hf : IsCentralIsogeny f) : IsCentralIsogeny (f ≫ e.hom) := by
  obtain ⟨hfin, hflat, hsurj, N, hN, hc⟩ := hf
  letI := hfin
  letI := hflat
  letI := hsurj
  letI : IsIso e.hom.hom.hom.left := (underlying k).map_isIso e.hom
  refine ⟨inferInstanceAs (IsFinite (f.hom.hom.left ≫ e.hom.hom.hom.left)),
    inferInstanceAs (Flat (f.hom.hom.left ≫ e.hom.hom.hom.left)),
    inferInstanceAs (Surjective (f.hom.hom.left ≫ e.hom.hom.hom.left)), N, ?_, hc⟩
  refine hN.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Grp.forget (SchemeOver k)).mapIso e) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · change η[H.X] ≫ e.hom.hom.hom = 𝟙 _ ≫ η[J.X]
    rw [Category.id_comp]
    exact IsMonHom.one_hom e.hom.hom.hom

private theorem centralIsogeny_baseChange (K : Type u) [Field K] [Algebra k K]
    (P : SplitBorelPair k) {G : GroupScheme k} (f : P.G.val ⟶ G) (hf : IsCentralIsogeny f) :
    IsCentralIsogeny ((groupBaseChange k K).map f) := by
  let F := groupBaseChange k K
  obtain ⟨hfin, hflat, hsurj, N, hN, hc⟩ := hf
  let hclosed {P Q : GroupScheme k} (g : P ⟶ Q) (hg : IsClosedImmersion g.hom.hom.left) :
      IsClosedImmersion ((F.map g).hom.hom.left) :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) g.hom.hom).flip hg
  let N' := baseChangedSubgroup K N (hclosed N.inclusion N.isClosedImmersion)
  have hN' : IsSchemeKernel (F.map f) N' := baseChangeKernelSquare f N.inclusion hN
  obtain ⟨_, e, _, hZc, hZ, _⟩ :=
    RootData.SchemeCentre.schemeCentre P.G P.reductive P.T P.split P.maximal
  let Z : ClosedSubgroup P.G.val :=
    ⟨specGroup (groupAlgebra k (Character P.T.group ⧸ rootLattice P.T)),
      diagonalClosedInclusion k (rootLattice P.T) ≫ e.hom ≫ P.T.inclusion, hZc⟩
  change RepresentsSubgroup Z (fun _ g => Centralizes (𝟙 P.G.val) g) at hZ
  obtain ⟨j, hj⟩ := hZ _ _ |>.mp hc
  letI := Z.isClosedImmersion
  letI := isMonHom_of_comp_closed j N.inclusion Z.inclusion hj
  let a : N.group ⟶ Z.group := Grp.homMk j
  have ha : a ≫ Z.inclusion = N.inclusion := Grp.hom_ext _ _ hj
  obtain ⟨zc, hz⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange k K (𝟙 P.G.val) Z hZ
  have hz' : RepresentsSubgroup (scalarExtendedSubgroup K Z zc)
      (fun _ g => Centralizes (𝟙 (F.obj P.G.val)) g) := by
    change RepresentsSubgroup (scalarExtendedSubgroup K Z zc)
      (fun _ g => Centralizes (F.map (𝟙 P.G.val)) g) at hz
    rw [F.map_id] at hz
    exact hz
  have hc' := (hz' _ _).mpr ⟨(F.map a).hom.hom, by
    change (F.map a).hom.hom ≫ (F.map Z.inclusion).hom.hom = (F.map N.inclusion).hom.hom
    exact congrArg (Grp.forget (SchemeOver K)).map
      ((F.map_comp _ _).symm.trans (F.congr_map ha))⟩
  let hp := (baseChangeMapPullback (K := K) f.hom.hom).flip
  exact ⟨MorphismProperty.of_isPullback hp hfin, MorphismProperty.of_isPullback hp hflat,
    MorphismProperty.of_isPullback hp hsurj, N', hN', hc'⟩

private theorem isIso_of_scalarExtension (K : Type u) [Field K] [Algebra k K]
    {G Q : GroupScheme k} (f : G ⟶ Q) (hf : IsIso ((groupBaseChange k K).map f)) :
    IsIso f := by
  letI := hf
  letI : Surjective (fieldSpecMap k K) := fieldSpecMap_surjective K
  letI : Surjective (pullback.fst Q.X.hom (fieldSpecMap k K)) := inferInstance
  letI : Flat (pullback.fst Q.X.hom (fieldSpecMap k K)) := inferInstance
  letI : QuasiCompact (pullback.fst Q.X.hom (fieldSpecMap k K)) := inferInstance
  letI : IsIso f.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := .isomorphisms _)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (baseChangeMapPullback (K := K) f.hom.hom)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      ((underlying K).map_isIso ((groupBaseChange k K).map f))
  exact isIso_of_schemeIso f

private theorem torusIso_of_isIso (P Q : SplitBorelPair k)
    (f : P.G.val ⟶ Q.G.val) (τ : P.T.group ⟶ Q.T.group)
    (hτ : IsTorusRestriction f τ) [IsIso f] : IsIso τ := by
  letI : IsIso f.hom.hom.left := (underlying k).map_isIso f
  letI := P.T.isClosedImmersion
  letI := Q.T.isClosedImmersion
  have h := congrArg (underlying k).map hτ.1
  simp only [Functor.map_comp] at h
  change τ.hom.hom.left ≫ Q.T.inclusion.hom.hom.left =
    P.T.inclusion.hom.hom.left ≫ f.hom.hom.left at h
  letI : IsClosedImmersion (τ.hom.hom.left ≫ Q.T.inclusion.hom.hom.left) :=
    h.symm ▸ inferInstanceAs (IsClosedImmersion (P.T.inclusion.hom.hom.left ≫ f.hom.hom.left))
  letI := IsClosedImmersion.of_comp_isClosedImmersion τ.hom.hom.left Q.T.inclusion.hom.hom.left
  letI := hτ.2.2
  letI : Smooth Q.T.group.X.hom := splitTorusSmooth Q.split
  letI : IsReduced Q.T.group.X.left := isReduced_of_smooth_over_field Q.T.group.X.hom
  letI := isIso_of_isClosedImmersion_of_surjective τ.hom.hom.left
  exact isIso_of_schemeIso τ

private def fibreTowerIso (k K : Type u) [Field k] [Field K] [Algebra k K] :
    IntegralSemisimpleModel.fibre K ≅
      IntegralSemisimpleModel.fibre k ⋙ groupBaseChange k K := by
  letI := IntegralSemisimpleModel.integerAlgebra (k := k)
  letI := IntegralSemisimpleModel.integerAlgebra (k := K)
  let f := fieldSpecMap k K
  let g := Spec.map (CommRingCat.ofHom (algebraMap IntegralSemisimpleModel.Integers.{u} k))
  have eq : f ≫ g = Spec.map (CommRingCat.ofHom (algebraMap IntegralSemisimpleModel.Integers.{u} K)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact map_intCast (algebraMap k K) x.down
  let e : Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap IntegralSemisimpleModel.Integers.{u} K))) ≅ Over.pullback g ⋙ Over.pullback f :=
    eq ▸ Over.pullbackComp f g
  exact Functor.mapGrpNatIso e ≪≫ Functor.mapGrpCompIso

private theorem model_simplyConnected {D : BasedRootDatum.{u}} (M : IntegralSemisimpleModel.Model D)
    (hD : corootSpan D.datum = ⊤) {G : AffineAlgebraicGroup k}
    (e : (IntegralSemisimpleModel.fibre k).obj M.group ≅ G.val) :
    GeometricallySimplyConnected G := by
  let K := AlgebraicClosure k
  obtain ⟨A, F, eK, _, _, _, _, _, _⟩ := M.fieldFibre K
  let q : (GeometricGroup G).val ≅ F.pinned.pair.G.val :=
    ((groupBaseChange k K).mapIso e).symm ≪≫
      ((fibreTowerIso k K).app M.group).symm ≪≫ eK
  intro H hH f hf
  letI := noCentralCovers_of_span F.pinned.pair F.attached (realization_corootSpan F hD)
    H hH (f ≫ q.hom) (centralIsogeny_postIso q hf)
  exact IsIso.of_isIso_comp_right f q.hom

private theorem exists_coroot_cover (realize : IntegralRealization.Statement.{u})
    (P : SplitBorelPair k) (D : AttachedDatum P)
    (hP : IsSemisimple P.G) :
    letI := D.comm
    ∃ (S : SplitBorelPair k) (E : AttachedDatum S)
      (f : S.G.val ⟶ P.G.val) (τ : S.T.group ⟶ P.T.group),
      IsSemisimple S.G ∧ GeometricallySimplyConnected S.G ∧ IsCentralIsogeny f ∧
      IsTorusRestriction f τ ∧ corootLattice E = ⊤ ∧
      (corootLattice D = ⊤ → IsIso f) ∧
      letI := E.comm
      ∃ e : Additive (Cocharacter S.T.group) ≃ₗ[ℤ] corootLattice D,
        ∀ c : Cocharacter S.T.group, (e (Additive.ofMul c)).val = Additive.ofMul (c ≫ τ) := by
  letI := D.comm
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  have hfin := (Submodule.finiteQuotient_iff (corootLattice D)).mpr
    ((semisimple_iff_corootFullRank P D).mp hP)
  let B := simplyConnectedDatum D.toBased hfin
  have hB : corootSpan B.datum = ⊤ :=
    corootDatum_span D.datum.rootDatum (restrictCharacters_injective D.datum.rootDatum hfin)
  obtain ⟨M⟩ := realize B
  obtain ⟨A, F, e, _, _, _, _, _, _⟩ := M.fieldFibre k
  obtain ⟨U, ⟨pin⟩⟩ := Classification.Pinning.pinningsExist A P
  let Q : PinnedGroup A := ⟨P, U, pin⟩
  have hF := realization_corootSpan F hB
  obtain ⟨f, τ, hf, hτ, hi, eY, heY⟩ := liftFromCorootDatum Q D hfin F
  exact ⟨F.pinned.pair, F.attached, f, τ, of_fullCorootLattice _ _ hF,
    model_simplyConnected M hB e, hf, hτ, hF, hi, eY, heY⟩

private theorem latticeCriterion_pair (realize : IntegralRealization.Statement.{u})
    (P : SplitBorelPair k) (D : AttachedDatum P) (hP : IsSemisimple P.G) :
    GeometricallySimplyConnected P.G ↔ corootLattice D = ⊤ := by
  letI := D.comm
  obtain ⟨S, E, f, τ, hS, hSC, hf, hτ, _, hi, eY, heY⟩ := exists_coroot_cover realize P D hP
  letI := E.comm
  let K := AlgebraicClosure k
  constructor
  · intro h
    have hSK : IsSemisimple (GeometricGroup S.G) :=
      (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) S.G hS.1 hS.2.1).mpr hS
    letI := isIso_of_scalarExtension K f
      (h (GeometricGroup S.G) hSK _ (centralIsogeny_baseChange K S f hf))
    letI := torusIso_of_isIso S P f τ hτ
    apply eq_top_iff.mpr
    intro y _
    exact (eY (Additive.ofMul (y.toMul ≫ inv τ))).property |> fun hy => by
      rwa [heY, Category.assoc, IsIso.inv_hom_id, Category.comp_id] at hy
  · intro h
    letI := hi h
    let q := (groupBaseChange k K).mapIso (asIso f)
    intro H hH p hp
    letI := hSC H hH (p ≫ q.inv) (centralIsogeny_postIso q.symm hp)
    exact IsIso.of_isIso_comp_right p q.inv

open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

private theorem corootLatticeOf_eq (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    [IsCommMonObj T.group.X] (D E : Datum T) :
    corootLatticeOf D = corootLatticeOf E := by
  letI := G.property.1
  obtain ⟨N, hN⟩ := schemeKernel_exists (𝟙 G.val)
  have hn : N.inclusion.hom.hom = 1 := by
    have h : N.inclusion.hom.hom ∈ SubgroupSections N N.group.X := by
      change ∃ n : N.group.X ⟶ N.group.X, n ≫ N.inclusion.hom.hom = N.inclusion.hom.hom
      exact ⟨𝟙 _, Category.id_comp _⟩
    have h' := (schemeKernel_sections hN N.inclusion.hom.hom).mp h
    change N.inclusion.hom.hom ≫ 𝟙 G.val.X = 1 at h'
    simpa only [Category.comp_id] using h' 
  have hcen : Centralizes (𝟙 G.val) N.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro Y g t
    rw [hn, MonObj.comp_one]
    exact Commute.one_left _
  have hid : IsCentralIsogeny (𝟙 G.val) :=
    ⟨inferInstanceAs (IsFinite (𝟙 G.val.X.left)),
      inferInstanceAs (Flat (𝟙 G.val.X.left)), inferInstanceAs (Surjective (𝟙 G.val.X.left)),
      N, hN, hcen⟩
  obtain ⟨_, _, _, hpair⟩ := centralIsogenyComparison G G hG hG T T hs hm hs hm
    (𝟙 G.val) (𝟙 T.group) hid (by simp) (inferInstanceAs (Surjective (𝟙 T.group.X.left)))
  have hcor (β : Root T) : D.rootDatum.coroot β = E.rootDatum.coroot β := by
    have hχ : characterPullback (𝟙 T.group) β.val = β.val := by
      change 𝟙 T.group ≫ β.val = β.val
      exact Category.id_comp _
    have hα : characterPullback (𝟙 T.group) β.val ∈ absoluteRoots T := hχ.symm ▸ β.property
    have hβ : (⟨characterPullback (𝟙 T.group) β.val, hα⟩ : Root T) = β := Subtype.ext hχ
    have hc : IsAttachedCoroot T ⟨characterPullback (𝟙 T.group) β.val, hα⟩
        (Additive.toMul (D.rootDatum.coroot β)) := hβ.symm ▸ D.attached β
    have hp := (hpair β.val β.property hα).2 _ _ hc (E.attached β)
    apply Additive.toMul.injective
    simpa only [Category.comp_id] using hp
  unfold corootLatticeOf
  congr 1
  exact congrArg Set.range (funext hcor)

private theorem corootLattice_splitBorelPair (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    [IsCommMonObj T.group.X] (D : Datum T) :
    corootLattice (Classification.Pinning.attachedDatum (splitBorelPair G hG T hs hm)) =
      corootLatticeOf D :=
  corootLatticeOf_eq G hG T hs hm _ D

/-- The geometric criterion for simple connectedness on the integral cocharacter lattice. -/
theorem latticeCriterion_conditional (realize : IntegralRealization.Statement.{u}) :
    LatticeCriterion.{u} := by
  intro k _ G hG T hs hm _ D
  let hGr := reductive_of_semisimple G hG
  let P := splitBorelPair G hGr T hs hm
  let E := Classification.Pinning.attachedDatum P
  have h := latticeCriterion_pair realize P E hG
  rw [corootLattice_splitBorelPair G hGr T hs hm D] at h
  exact h

/-- The cover is the split model of the integral coroot sublattice and
its dual, with the map on cocharacters given by inclusion. -/
theorem splitCover_conditional (realize : IntegralRealization.Statement.{u}) :
    SplitCover.{u} := by
  intro k _ G hG T hs hm _ D
  let hGr := reductive_of_semisimple G hG
  let P := splitBorelPair G hGr T hs hm
  let E := Classification.Pinning.attachedDatum P
  obtain ⟨S, F, f, τ, hS, hSC, hf, hτ, hF, _, e, he⟩ := exists_coroot_cover realize P E hG
  letI : IsCommMonObj P.T.group.X := E.comm
  letI := F.comm
  have hE : corootLattice E = corootLatticeOf D := corootLattice_splitBorelPair G hGr T hs hm D
  refine ⟨S, F, f, τ, hS, hSC, hf, hτ, hF, e.trans (LinearEquiv.ofEq _ _ hE), ?_⟩
  exact he

open private normalOfCentral from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
open private reductive_finiteImage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
open private smooth_baseChange_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open Specs.SchemeDerivedGroup (RepresentsQuotient)

private theorem reductiveOfFiniteImage {G Q : AffineAlgebraicGroup k} (q : G.val ⟶ Q.val)
    [IsFinite q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] (hG : IsReductive G) : IsReductive Q := by
  let K := AlgebraicClosure k
  let qK : (GeometricGroup G).val ⟶ (GeometricGroup Q).val := (groupBaseChange k K).map q
  have hpb := (baseChangeMapPullback (K := K) q.hom.hom).flip
  letI : IsFinite qK.hom.hom.left :=
    MorphismProperty.of_isPullback hpb (inferInstance : IsFinite q.hom.hom.left)
  letI : Flat qK.hom.hom.left :=
    MorphismProperty.of_isPullback hpb (inferInstance : Flat q.hom.hom.left)
  letI : Surjective qK.hom.hom.left :=
    MorphismProperty.of_isPullback hpb (inferInstance : Surjective q.hom.hom.left)
  letI : LocallyOfFinitePresentation qK.hom.hom.left :=
    MorphismProperty.of_isPullback hpb (inferInstance : LocallyOfFinitePresentation q.hom.hom.left)
  have hGK := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  have hQK := reductive_finiteImage qK hGK
  have hs := (smooth_baseChange_iff (K := K) Q.val.X).mp hQK.1
  letI : Surjective (fieldSpecMap k K) := fieldSpecMap_surjective K
  letI : GeometricallyConnected (pullback.snd Q.val.X.hom (fieldSpecMap k K)) := hQK.2.1
  have hc := LinearAlgebraicGroups.geometricallyConnectedOfSurjectiveBaseChange
    Q.val.X.hom (fieldSpecMap k K)
  exact (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) Q hs hc).mp hQK

private theorem finite_of_finiteSelfPullback {W X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    {a b : W ⟶ X} (q : X ⟶ Y) (sq : IsPullback a b q q)
    (hf : Flat q) (hs : Surjective q) (ha : IsFinite a) : IsFinite q := by
  let e := X.isoSpec
  let d := Y.isoSpec
  let f := e.inv ≫ q ≫ d.hom
  letI := hf
  letI := hs
  letI : Surjective f := inferInstanceAs (Surjective (e.inv ≫ q ≫ d.hom))
  letI : Flat f := inferInstanceAs (Flat (e.inv ≫ q ≫ d.hom))
  have sq' : IsPullback (a ≫ e.hom) (b ≫ e.hom) f f := by
    apply sq.of_iso (Iso.refl _) e e d
    · simp
    · simp
    · simp [f]
    · simp [f]
  have hf' : IsFinite (pullback.fst f f) := by
    letI := ha
    haveI : IsFinite (a ≫ e.hom) := inferInstance
    rw [← sq'.isoPullback_inv_fst]
    infer_instance
  have hfin : IsFinite f := by
    refine of_pullback_fst_Spec_of_codescendsAlong (P := @IsFinite)
      (Q' := RingHom.FaithfullyFlat) (Q := RingHom.Finite) (P' := @Surjective ⊓ @Flat)
      RingHom.Finite.codescendsAlong_faithfullyFlat ?_ ?_ ⟨inferInstance, inferInstance⟩ hf'
    · intro R S g hg
      rwa [← flat_and_surjective_SpecMap_iff, and_comm]
    · exact IsFinite.SpecMap_iff _
  letI := hfin
  have hcomp : q = e.hom ≫ f ≫ d.inv := by simp [f]
  rw [hcomp]
  infer_instance
private theorem semisimple_of_rootLattice_top (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (ht : rootLattice T = ⊤) : IsSemisimple G := by
  obtain ⟨_, e, _, hi, hZ, _⟩ := RootData.SchemeCentre.schemeCentre G hG T hs hm
  let Z : ClosedSubgroup G.val :=
    ⟨specGroup (groupAlgebra k (Character T.group ⧸ rootLattice T)),
      diagonalClosedInclusion k (rootLattice T) ≫ e.hom ≫ T.inclusion, hi⟩
  have hfin : Finite (Character T.group ⧸ rootLattice T) := by
    rw [ht]
    letI := QuotientGroup.subsingleton_quotient_top (G := Character T.group)
    infer_instance
  exact (Reductive.CentralDerived.semisimpleIffFiniteCentre G hG Z hZ).mpr
    ((finiteDiagonal_iff (k := k) _).mpr hfin)

/-- The adjoint form is the full scheme-centre quotient, with the paired
root and coroot data carried by its torus map. -/
theorem adjointForm_conditional (_realize : IntegralRealization.Statement.{u}) :
    AdjointForm.{u} := by
  intro k _ G hG T hs hm
  have hr := reductive_of_semisimple G hG
  obtain ⟨_, e, _, hi, hZ, _⟩ := RootData.SchemeCentre.schemeCentre G hr T hs hm
  let Z : ClosedSubgroup G.val :=
    ⟨specGroup (groupAlgebra k (Character T.group ⧸ rootLattice T)),
      diagonalClosedInclusion k (rootLattice T) ≫ e.hom ≫ T.inclusion, hi⟩
  change RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 G.val) z) at hZ
  have hZf := (Reductive.CentralDerived.semisimpleIffFiniteCentre G hr Z hZ).mp hG
  have hZc := (hZ _ Z.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨P⟩ := (HomogeneousQuotient.homogeneousQuotient k G Z).1
  obtain ⟨L, Q, f, q, i, E, hkernel, hqker, hfac, _, hproj⟩ :=
    HomogeneousQuotient.quotientAffineComparison G Z P (normalOfCentral Z hZc)
  have hq : RepresentsQuotient Z q := quotientRepresentsImage hfac hkernel
  have hp : IsPullback (prod.fst : G.val.X ⨯ Z.group.X ⟶ G.val.X)
      (Specs.HomogeneousQuotient.rightMultiplication Z) q.hom.hom q.hom.hom := by
    refine (HomogeneousQuotient.quotientPullback P).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) E (by simp) (by simp) ?_ ?_
    all_goals simpa only [Iso.refl_hom, Category.id_comp] using hproj
  have hp' := hp.map (Over.forget (Spec (CommRingCat.of k)))
  have hprojFin : IsFinite (prod.fst : G.val.X ⨯ Z.group.X ⟶ G.val.X).left :=
    MorphismProperty.of_isPullback
      (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd G.val.X Z.group.X)).flip hZf
  letI := G.property.1
  letI := Q.property.1
  letI : IsFinite q.hom.hom.left :=
    finite_of_finiteSelfPullback q.hom.hom.left hp' hfac.2.1 hfac.2.2.1 hprojFin
  letI := hfac.2.1
  letI := hfac.2.2.1
  letI := hfac.2.2.2.1
  have hqiso : IsCentralIsogeny q :=
    ⟨inferInstance, inferInstance, inferInstance, Z, hqker, hZc⟩
  have hQr : IsReductive Q := reductiveOfFiniteImage q hr
  obtain ⟨Tad, qT, hsad, hmad, hqT, hχ, hL⟩ :=
    Classification.CentralIsogenies.adjointCharacterLattice_of_quotient G hG T hs hm Z hZ Q q hq
  obtain ⟨_, _, hbij, hcmp⟩ :=
    centralIsogenyComparison G Q hr hQr T Tad hs hm hsad hmad q qT hqiso hqT.1 hqT.2.2
  have himage : characterPullback qT '' absoluteRoots Tad = absoluteRoots T :=
    Set.Subset.antisymm hbij.mapsTo.image_subset hbij.surjOn
  have hgen : (rootLattice Tad).map (characterPullback qT) = (characterPullback qT).range := by
    rw [rootLattice, MonoidHom.map_closure, himage, ← rootLattice, hL]
  have htop : rootLattice Tad = ⊤ := by
    apply (Subgroup.map_injective hχ)
    simpa only [Subgroup.map_top] using hgen
  exact ⟨Z, Q, q, hZ, hq, hqiso, semisimple_of_rootLattice_top Q hQr Tad hsad hmad htop,
    Tad, qT, hsad, hmad, hqT, hχ, hL, htop, hbij,
    fun χ c => pairing_pushforward qT χ c,
    fun β hβ hα c cad hc hcad => (hcmp β hβ hα).2 c cad hc hcad⟩

end
end LinearAlgebraicGroups.Classification.SimplyConnectedLattice

universe v8_closure_8d70daccbfcc53b8_u0
theorem _root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm» : _root_.«LinearAlgebraicGroups».«Specs».«SimplyConnectedLattice».«AdjointForm».{v8_closure_8d70daccbfcc53b8_u0} :=
  @_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm_conditional».{v8_closure_8d70daccbfcc53b8_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«IntegralRealization».«integralRealization».{v8_closure_8d70daccbfcc53b8_u0})
theorem _root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion» : _root_.«LinearAlgebraicGroups».«Specs».«SimplyConnectedLattice».«LatticeCriterion».{v8_closure_8d70daccbfcc53b8_u0} :=
  @_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion_conditional».{v8_closure_8d70daccbfcc53b8_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«IntegralRealization».«integralRealization».{v8_closure_8d70daccbfcc53b8_u0})
theorem _root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover» : _root_.«LinearAlgebraicGroups».«Specs».«SimplyConnectedLattice».«SplitCover».{v8_closure_8d70daccbfcc53b8_u0} :=
  @_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover_conditional».{v8_closure_8d70daccbfcc53b8_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«IntegralRealization».«integralRealization».{v8_closure_8d70daccbfcc53b8_u0})
