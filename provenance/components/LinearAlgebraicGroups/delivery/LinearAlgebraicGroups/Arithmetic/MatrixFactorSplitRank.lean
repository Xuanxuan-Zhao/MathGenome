import Specs.LinearAlgebraicGroups.Arithmetic.MatrixFactorSplitRank
import LinearAlgebraicGroups.Descent.RelativeRank
import LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.MatrixFactorSplitRank

open _root_.LinearAlgebraicGroups.Specs
open Specs.MatrixFactorSplitRank
open Specs.GeometricRadicals
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.RelativeRank
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.StandardGroups (multiplicativePowerGroup)
open Specs.CharacterDescent (Cocharacter StandardLattice)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Pinning (PinnedGroup)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.DiagonalizableGroups (IntegerCharacters)

open private splitTorusImage tensorSplitTorus from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private dimension_of_iso standard_torus_dimension from LinearAlgebraicGroups.Descent.RelativeRank
open private productSubgroup cocharacterProduct from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
open private firstInclusion secondInclusion from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private affineProduct from LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
open private pushSubgroup from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent

open private cocharactersOfIso homToDual latticeCoordinates from LinearAlgebraicGroups.RootData.CharacterPairing
open private isTorus_of_split from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent

noncomputable section

variable {F : Type u} [Field F]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
set_option linter.style.haveILetI false

private theorem split_torus_dimension {T : GroupScheme F} {r : ℕ}
    (e : T ≅ (multiplicativePowerGroup F (ULift.{u} (Fin r))).val) :
    topologicalKrullDim T.X.left = (r : WithBot ℕ∞) :=
  (dimension_of_iso e).trans (standard_torus_dimension r)

private noncomputable def splitCocharacterCoordinates {T : GroupScheme F}
    [IsCommMonObj T.X] {r : ℕ}
    (e : T ≅ (multiplicativePowerGroup F (ULift.{u} (Fin r))).val) :
    Additive (Cocharacter T) ≃ₗ[ℤ] (Fin r → ℤ) := by
  let M := StandardLattice.{u} r
  let i := Classical.choice (LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := F) r)
  let c := (LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := F) r).choose_spec.choose
  let d : Additive (M →* IntegerCharacters.{u}) ≃ₗ[ℤ] Additive (Cocharacter T) :=
    (c.trans (cocharactersOfIso (i ≪≫ e.symm))).toAdditive.toIntLinearEquiv
  exact (d.symm.trans (homToDual M)).trans
    (((Pi.basisFun ℤ (Fin r)).map (latticeCoordinates r).symm).dualBasis.equivFun)

private theorem product_torus_dimension {A B : AffineAlgebraicGroup F} {m n : ℕ}
    (e : A.val ≅ (multiplicativePowerGroup F (ULift.{u} (Fin m))).val)
    (f : B.val ≅ (multiplicativePowerGroup F (ULift.{u} (Fin n))).val) :
    topologicalKrullDim (A.val ⊗ B.val).X.left = ((m + n : ℕ) : WithBot ℕ∞) := by
  obtain ⟨r, ⟨g⟩⟩ := tensorSplitTorus A B ⟨m, ⟨e⟩⟩ ⟨n, ⟨f⟩⟩
  letI : IsCommMonObj A.val.X := torus_commutative A (isTorus_of_split ⟨m, ⟨e⟩⟩)
  letI : IsCommMonObj B.val.X := torus_commutative B (isTorus_of_split ⟨n, ⟨f⟩⟩)
  letI : IsCommMonObj (A.val ⊗ B.val).X := torus_commutative (affineProduct A B)
    (isTorus_of_split ⟨r, ⟨g⟩⟩)
  let a := splitCocharacterCoordinates e
  let b := splitCocharacterCoordinates f
  let c := splitCocharacterCoordinates g
  have hr := ((c.symm.trans (cocharacterProduct A.val B.val)).trans (a.prodCongr b)).finrank_eq
  have hr' : r = m + n := by simpa [Module.finrank_prod] using hr
  simpa only [hr'] using split_torus_dimension g

private theorem product_maximal {A B : AffineAlgebraicGroup F}
    {S : ClosedSubgroup A.val} {T : ClosedSubgroup B.val}
    (hS : IsMaximalSplitTorus S) (hT : IsMaximalSplitTorus T) :
    IsMaximalSplitTorus (productSubgroup S T) := by
  refine ⟨tensorSplitTorus (closedSubgroupAlgebraicGroup S) (closedSubgroupAlgebraicGroup T)
    hS.1 hT.1, ?_⟩
  rintro V hv ⟨i, hi⟩
  let V₀ := closedSubgroupAlgebraicGroup (G := affineProduct A B) V
  obtain ⟨I, p, hp, hp'⟩ := splitTorusImage V₀ A hv (V.inclusion ≫ fst A.val B.val)
  obtain ⟨J, q, hq, hq'⟩ := splitTorusImage V₀ B hv (V.inclusion ≫ snd A.val B.val)
  have hSI : IsSubgroupOf S I := by
    refine ⟨firstInclusion S.group T.group ≫ i ≫ p, ?_⟩
    simp only [Category.assoc, hp'.1, reassoc_of% hi]
    change firstInclusion S.group T.group ≫ (S.inclusion ⊗ₘ T.inclusion) ≫ fst A.val B.val = _
    rw [tensorHom_fst, ← Category.assoc, lift_fst, Category.id_comp]
  have hTJ : IsSubgroupOf T J := by
    refine ⟨secondInclusion S.group T.group ≫ i ≫ q, ?_⟩
    simp only [Category.assoc, hq'.1, reassoc_of% hi]
    change secondInclusion S.group T.group ≫ (S.inclusion ⊗ₘ T.inclusion) ≫ snd A.val B.val = _
    rw [tensorHom_snd, ← Category.assoc, lift_snd, Category.id_comp]
  obtain ⟨a, ha⟩ := hS.2 I hp hSI
  obtain ⟨b, hb⟩ := hT.2 J hq hTJ
  refine ⟨lift (p ≫ a) (q ≫ b), ?_⟩
  change lift (p ≫ a) (q ≫ b) ≫ (S.inclusion ⊗ₘ T.inclusion) = V.inclusion
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tensorHom_fst, lift_fst_assoc, Category.assoc, ha, hp'.1]
  · rw [Category.assoc, tensorHom_snd, lift_snd_assoc, Category.assoc, hb, hq'.1]

private theorem push_maximal {G H : GroupScheme F} (e : G ≅ H) {S : ClosedSubgroup G}
    (hS : IsMaximalSplitTorus S) : IsMaximalSplitTorus (pushSubgroup e S) := by
  refine ⟨hS.1, ?_⟩
  rintro V hv ⟨i, hi⟩
  let V' := pushSubgroup e.symm V
  have hi' : IsSubgroupOf S V' := by
    refine ⟨i, ?_⟩
    change i ≫ V.inclusion ≫ e.inv = S.inclusion
    rw [← Category.assoc, hi]
    change (S.inclusion ≫ e.hom) ≫ e.inv = _
    simp
  obtain ⟨j, hj⟩ := hS.2 V' hv hi'
  refine ⟨j, ?_⟩
  change j ≫ S.inclusion ≫ e.hom = V.inclusion
  rw [← Category.assoc, hj]
  change (V.inclusion ≫ e.inv) ≫ e.hom = _
  simp

theorem productSplitRank : ProductSplitRank.{u} := by
  intro F _ H A B hH hA hB e
  obtain ⟨⟨S, hS⟩, dS⟩ := Descent.RelativeRank.maximalSplitDimension A hA
  obtain ⟨⟨T, hT⟩, dT⟩ := Descent.RelativeRank.maximalSplitDimension B hB
  obtain ⟨m, ⟨s⟩⟩ := hS.1
  obtain ⟨n, ⟨t⟩⟩ := hT.1
  let j : A.val ⊗ B.val ≅ Limits.prod A.val B.val :=
    (tensorProductIsBinaryProduct A.val B.val).conePointUniqueUpToIso (limit.isLimit (pair _ _))
  let i := j ≪≫ e.symm
  let V := pushSubgroup i (productSubgroup S T)
  have hV := push_maximal i (product_maximal hS hT)
  have hdim : topologicalKrullDim V.group.X.left = ((m + n : ℕ) : WithBot ℕ∞) :=
    product_torus_dimension (A := closedSubgroupAlgebraicGroup S)
      (B := closedSubgroupAlgebraicGroup T) s t
  refine ⟨m, n, (dS _ hS).symm.trans (split_torus_dimension s),
    (dT _ hT).symm.trans (split_torus_dimension t), ?_⟩
  rw [← (Descent.RelativeRank.maximalSplitDimension H hH).2 V hV, hdim, Nat.cast_add]

open Specs.AutomorphismSequence (IsSeparableForm)
open Specs.SimplyConnectedLattice (corootLatticeOf)

open private groupBaseChangeTowerIso from LinearAlgebraicGroups.Relative.RationalCocharacter
open private extendMatrixPoints from LinearAlgebraicGroups.Arithmetic.TypeAMatrixDescentData
open private maximalTorus_of_geometricallyMaximal from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private centralIsogeny_postIso splitBorelPair from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private extendSubgroup trivial_of_subgroup_of_trivial from LinearAlgebraicGroups.RootData.RankOneFlag
open private split_baseChange_dimension split_dimension_le_rank from LinearAlgebraicGroups.Descent.RelativeRank
open private transport_normal from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private exists_maximal_torus_over from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_smooth_connected_solvable from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private group_irreducible_of_connected from LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private factor_closed isIso_of_schemeIso from LinearAlgebraicGroups.Reductive.GeometricRadicals

private theorem geometricIsoOfForm {S U : AffineAlgebraicGroup F} (h : IsSeparableForm S U) :
    Nonempty ((GeometricGroup S).val ≅ (GeometricGroup U).val) := by
  obtain ⟨K, _, _, _, ⟨e⟩⟩ := h
  let L := AlgebraicClosure F
  let a : K →ₐ[F] L := IsAlgClosed.lift
  letI : Algebra K L := a.toRingHom.toAlgebra
  letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun x => (a.commutes x).symm
  let i := groupBaseChangeTowerIso (k := F) (K := K) (L := L)
  exact ⟨(i.app S.val).symm ≪≫ (groupBaseChange K L).mapIso e ≪≫ i.app U.val⟩

private theorem relative_rank_iso {G H : AffineAlgebraicGroup F} (e : G.val ≅ H.val) :
    relativeRank G = relativeRank H := by
  have le_of_iso {A B : AffineAlgebraicGroup F} (f : A.val ≅ B.val) :
      relativeRank A ≤ relativeRank B := by
    apply iSup_le
    rintro ⟨S, hS⟩
    exact split_dimension_le_rank B (pushSubgroup f S) hS
  exact le_antisymm (le_of_iso e) (le_of_iso e.symm)

private theorem matrix_rank_one [IsAlgClosed F] {S : AffineAlgebraicGroup F}
    (s : SpecialMatrixPoints S 2) : relativeRank S = 1 := by
  obtain ⟨T, L, M, B, _, _, _, _⟩ := RootData.SpecialLinearDatum.matrixPinnedDatum F 1 S s
  have hT := maximalTorus_of_geometricallyMaximal S T.subgroup (isTorus_of_split T.split) B.maximal
  have hmax : IsMaximalSplitTorus T.subgroup :=
    ⟨T.split, fun V hv hTV => hT.2 V (isTorus_of_split hv) hTV⟩
  let P := multiplicativePowerGroup F (ULift.{u} (Fin 1))
  letI : IsAffine T.subgroup.group.X.left := (closedSubgroupAlgebraicGroup T.subgroup).property.1
  letI : IsAffine P.val.X.left := P.property.1
  let e : T.subgroup.group ≅ P.val :=
    groupIsoOfPointIso (T.pointsIso ≪≫
      (LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroupPointsIso F
        (ULift.{u} (Fin 1))).symm)
  exact ((Descent.RelativeRank.maximalSplitDimension S B.reductive).2 _ hmax).symm.trans
    (split_torus_dimension e)

private theorem semisimple_of_geometricIso {S U : AffineAlgebraicGroup F}
    (e : (GeometricGroup S).val ≅ (GeometricGroup U).val)
    (hS : IsSemisimple S) (hU : IsReductive U) : IsSemisimple U := by
  refine ⟨hU.1, hU.2.1, ?_⟩
  let R := geometricSolvableRadical U
  let R' := pushSubgroup e.symm R
  have hR := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest U
  have hS' := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest S
  have hsub : IsSubgroupOf R' (geometricSolvableRadical S) :=
    hS'.2.2 R' ⟨hR.1.1, hR.1.2.1, transport_normal e.symm R hR.1.2.2⟩ hR.2.1
  exact trivial_of_subgroup_of_trivial (A := R') hsub hS.2.2

private theorem simplyConnected_of_geometricIso {S U : AffineAlgebraicGroup F}
    (e : (GeometricGroup S).val ≅ (GeometricGroup U).val)
    (hS : GeometricallySimplyConnected S) : GeometricallySimplyConnected U := by
  intro X hX f hf
  haveI := hS X hX (f ≫ e.inv) (centralIsogeny_postIso e.symm hf)
  have h : (f ≫ e.inv) ≫ e.hom = f := by simp
  exact h ▸ inferInstanceAs (IsIso ((f ≫ e.inv) ≫ e.hom))

/-- A closed embedding of a curve into an irreducible space of dimension at most one
is surjective when the source is irreducible and has positive dimension. -/
private theorem surjective_of_closedEmbedding_of_dim_one {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [IrreducibleSpace X] [IrreducibleSpace Y]
    {f : X → Y} (hf : Topology.IsClosedEmbedding f)
    (hx : 0 < topologicalKrullDim X) (hy : topologicalKrullDim Y ≤ 1) :
    Function.Surjective f := by
  classical
  letI : OrderTop (TopologicalSpace.IrreducibleCloseds X) :=
    { top := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
      le_top := fun _ => Set.subset_univ _ }
  letI : OrderTop (TopologicalSpace.IrreducibleCloseds Y) :=
    { top := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
      le_top := fun _ => Set.subset_univ _ }
  open TopologicalSpace.IrreducibleCloseds in
  let g := map f hf.continuous
  have hg : StrictMono g := map_strictMono_of_isInducing hf.isInducing
  letI := Order.krullDim_pos_iff_of_orderTop.mp hx
  obtain ⟨Z, hZ⟩ := exists_ne (⊤ : TopologicalSpace.IrreducibleCloseds X)
  by_contra hn
  have ht : g ⊤ ≠ ⊤ := by
    intro eq
    apply hn
    have hr := congrArg (fun A : TopologicalSpace.IrreducibleCloseds Y => (A : Set Y)) eq
    change closure (f '' Set.univ) = Set.univ at hr
    rw [Set.image_univ, hf.isClosed_range.closure_eq] at hr
    exact Set.range_eq_univ.mp hr
  have hm := Order.krullDim_le_one_iff_forall_isMin.mp hy (g ⊤) ht
  exact (not_lt_of_ge (hm (hg (lt_top_iff_ne_top.mpr hZ)).le)) (hg (lt_top_iff_ne_top.mpr hZ))

private theorem geometrically_maximal_of_dimension_one {U : AffineAlgebraicGroup F}
    (hU : IsReductive U) (hgeom : geometricRank U = 1)
    (T : ClosedSubgroup U.val) (hT : IsSplitTorus T.group)
    (hd : topologicalKrullDim T.group.X.left = 1) : IsGeometricallyMaximal T := by
  let K := AlgebraicClosure F
  let A := GeometricGroup U
  let T' := extendSubgroup K T
  obtain ⟨hT', hd'⟩ := split_baseChange_dimension K hT
  refine ⟨T'.isClosedImmersion, isTorus_of_split hT', ?_⟩
  intro V hv hTV
  change IsSubgroupOf T' V at hTV
  change IsSubgroupOf V T'
  obtain ⟨W, hw, ⟨j, hj⟩⟩ := exists_maximal_torus_over A V hv
  obtain ⟨i, hi⟩ := hTV
  have hij : (i ≫ j) ≫ W.inclusion = T'.inclusion := by rw [Category.assoc, hj, hi]
  letI := factor_closed (H := T') (N := W) hij
  have h₁ := torus_smooth_connected_solvable (closedSubgroupAlgebraicGroup (G := A) T')
    (isTorus_of_split hT')
  have h₂ := torus_smooth_connected_solvable (closedSubgroupAlgebraicGroup (G := A) W) hw.1
  letI : ConnectedSpace (closedSubgroupAlgebraicGroup (G := A) T').val.X.left := h₁.2.1
  letI : ConnectedSpace (closedSubgroupAlgebraicGroup (G := A) W).val.X.left := h₂.2.1
  letI : IrreducibleSpace T'.group.X.left :=
    group_irreducible_of_connected (closedSubgroupAlgebraicGroup (G := A) T')
  letI : IrreducibleSpace W.group.X.left :=
    group_irreducible_of_connected (closedSubgroupAlgebraicGroup (G := A) W)
  have hW : topologicalKrullDim W.group.X.left = 1 :=
    ((Descent.RelativeRank.maximalGeometricDimension U hU).2 W hw).trans hgeom
  have hdim : topologicalKrullDim T'.group.X.left = 1 := hd'.trans hd
  have hs := surjective_of_closedEmbedding_of_dim_one
    (IsClosedImmersion.isClosedEmbedding (i ≫ j).hom.hom.left)
    (hdim.symm ▸ (zero_lt_one : (0 : WithBot ℕ∞) < 1)) hW.le
  letI : Surjective ((i ≫ j).hom.hom.left) := ⟨hs⟩
  letI : Smooth W.group.X.hom := h₂.1
  letI : IsReduced W.group.X.left := isReduced_of_smooth_over_field W.group.X.hom
  letI := isIso_of_isClosedImmersion_of_surjective (i ≫ j).hom.hom.left
  haveI := isIso_of_schemeIso (i ≫ j)
  refine ⟨j ≫ inv (i ≫ j), ?_⟩
  rw [Category.assoc, ← hij, IsIso.inv_hom_id_assoc, hj]

private theorem split_rank_one_matrix_points {S U : AffineAlgebraicGroup F}
    (s : SpecialMatrixPoints S 2) (hU : IsReductive U) (hsemi : IsSemisimple U)
    (hsc : GeometricallySimplyConnected U) (T : ClosedSubgroup U.val)
    (t : T.group ≅ (multiplicativePowerGroup F (ULift.{u} (Fin 1))).val)
    (hmax : IsGeometricallyMaximal T) : Nonempty (SpecialMatrixPoints U 2) := by
  classical
  let P := splitBorelPair U hU T ⟨1, ⟨t⟩⟩ hmax
  let D := Classification.Pinning.attachedDatum P
  letI := D.comm
  have hspan := (Classification.SimplyConnectedLattice.latticeCriterion P.G hsemi P.T
    P.split P.maximal D.datum).mp hsc
  have hb : Submodule.span ℤ (Set.range
        (fun j : D.toBased.base.support => D.toBased.datum.coroot j)) = ⊤ := by
    rw [show Set.range (fun j : D.toBased.base.support => D.toBased.datum.coroot j) =
        D.toBased.datum.coroot '' (D.toBased.base.support : Set D.toBased.I) from
      (Set.image_eq_range _ _).symm, D.toBased.base.span_int_coroot_support]
    exact hspan
  let b := Module.Basis.mk D.toBased.base.linearIndepOn_coroot hb.ge
  let t' : P.T.group ≅ (multiplicativePowerGroup F (ULift.{u} (Fin 1))).val := t
  let e := splitCocharacterCoordinates t'
  letI := D.toBased.finiteRoots
  letI := Fintype.ofFinite D.toBased.base.support
  have hc : Fintype.card D.toBased.base.support = 1 := by
    calc
      _ = Module.finrank ℤ D.toBased.Y := (Module.finrank_eq_card_basis b).symm
      _ = 1 := by
        change Module.finrank ℤ (Additive (Cocharacter P.T.group)) = 1
        simpa using e.finrank_eq
  let j := Fintype.equivOfCardEq (by simpa using hc.symm : Fintype.card (Fin 1) =
    Fintype.card D.toBased.base.support)
  have hD : Specs.OuterTypeAModels.HasSimplyConnectedTypeA 1 D.toBased := by
    refine ⟨j, b, Module.Basis.mk_apply _ _, ?_⟩
    intro i l
    have h : l = i := Subsingleton.elim _ _
    subst l
    rw [ite_eq_left rfl]
    exact D.toBased.datum.pairing_same (j i)
  obtain ⟨A, Q, hQ, hcomp⟩ := OuterTypeAModels.splitMatrixComparison 1 S s
  obtain ⟨V, ⟨p⟩⟩ := Classification.Pinning.pinningsExist A P
  obtain ⟨q⟩ := hcomp ⟨P, V, p⟩ D hD
  have f : U.val ≅ S.val := hQ ▸ q.group
  exact ⟨(groupPointsFunctor F).mapIso f ≪≫ s⟩

theorem rankOneFormSplitRank : RankOneFormSplitRank.{u} := by
  intro F _ S U s hU hform
  obtain ⟨e⟩ := geometricIsoOfForm hform
  let K := AlgebraicClosure F
  have hgeom : geometricRank U = 1 := (relative_rank_iso e.symm).trans
    (matrix_rank_one (extendMatrixPoints (K := K) s))
  obtain ⟨⟨T, hT⟩, hdim⟩ := Descent.RelativeRank.maximalSplitDimension U hU
  obtain ⟨r, ⟨t⟩⟩ := hT.1
  have hrank : relativeRank U = (r : WithBot ℕ∞) :=
    (hdim T hT).symm.trans (split_torus_dimension t)
  have hr : r ≤ 1 := by
    have hle := (Descent.RelativeRank.rankComparison U hU).1
    rw [hrank, hgeom] at hle
    exact_mod_cast hle
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with rfl | rfl
  · exact Or.inl hrank
  · refine Or.inr ⟨hrank, ?_⟩
    have hmax := geometrically_maximal_of_dimension_one hU hgeom T hT.1 (split_torus_dimension t)
    have hsemi := semisimple_of_geometricIso e (RootData.SpecialLinearDatum.semisimple F 1 S s) hU
    obtain ⟨_, _, _, _, _, _, _, hsc⟩ := RootData.SpecialLinearDatum.matrixPinnedDatum F 1 S s
    exact split_rank_one_matrix_points s hU hsemi (simplyConnected_of_geometricIso e hsc) T t hmax

end

end LinearAlgebraicGroups.Arithmetic.MatrixFactorSplitRank
