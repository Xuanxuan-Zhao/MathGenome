import Specs.LinearAlgebraicGroups.Descent.RelativeRank
import LinearAlgebraicGroups.Descent.AdjointCocharacters
import LinearAlgebraicGroups.Descent.NormOneTorus
import LinearAlgebraicGroups.Reductive.CocharacterDynamics
import LinearAlgebraicGroups.Relative.RationalCocharacter
import LinearAlgebraicGroups.Relative.MaximalSplitTori
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Zero

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj BigOperators TensorProduct

universe u

namespace LinearAlgebraicGroups.Descent.RelativeRank

noncomputable section

open LinearAlgebraicGroups.Specs
open Specs.RelativeRank (RelativeRankType MaximalSplitDimension MaximalGeometricDimension
  RankComparison ProperDynamicParabolic AdjointParabolicCriterion
  SemisimpleParabolicCriterion QuadraticNormOneRanks IsCentralCocharacter HasProperParabolic)
open Specs.AdjointCocharacters (IsAdjointQuotient powerOnGm)
open Specs.BorelProper (IsParabolic)
open Specs.CharacterDescent (Cocharacter StandardLattice)
open Specs.DiagonalizableGroups (diagonalGroup groupAlgebra groupAlgebraMap IntegerCharacters)
open Specs.GeometricRadicals (GeometricGroup IsMaximalTorus IsReductive IsSemisimple
  IsSmoothConnectedNormal IsSplitTorus IsTrivialSubgroup identitySubgroup)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (IsUnipotent closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition existsLimitDecomposition
  limitSubgroupsSmooth geometricallyConnectedLimitSubgroups contractingSubgroupUnipotent)

open private limitIsParabolic limitSectionMemIff splitTorusImage
  from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private extendSubgroup subgroupIso_of_same from LinearAlgebraicGroups.RootData.RankOneFlag
open private normal_postcompose_iso from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private definingIdeal definingIdeal_le factor_iso_of_definingIdeal_eq factor_closed
  from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private definingIdeal_prime_of_torus exists_maximal_torus_over inclusion_mono
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private liftToSchemeKernel normalOfSchemeKernel
  from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private trivialOfSubgroup from LinearAlgebraicGroups.Reductive.CentralDerived
open private solvable_of_smooth_connected_unipotent
  from LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private trivial_baseChange_iff from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private connected_of_geometricallyConnected smooth_baseChangedGroup connected_baseChangedGroup
  reductive_geometricGroup from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private split_of_maximal from LinearAlgebraicGroups.RootData.BorelNormalizer
open private isTorus_of_split splitTorus_baseChange from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private multiplicative_group_iso from LinearAlgebraicGroups.Relative.LeviConjugacy
open private trivialSchemeIso from LinearAlgebraicGroups.Multiplicative.NormOneTorus
open private extendedGroupIso specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private krull_dimension_localization_away from LinearAlgebraicGroups.RootData.RootGroups

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

def relativeRank : RelativeRankType.{u} := Specs.RelativeRank.relativeRank

def geometricRank : RelativeRankType.{u} := Specs.RelativeRank.geometricRank

private theorem inclusion_iso_of_section {G : GroupScheme k} (S : ClosedSubgroup G)
    (s : G ⟶ S.group) (hs : s ≫ S.inclusion = 𝟙 _) : IsIso S.inclusion := by
  letI := inclusion_mono S
  exact ⟨⟨s, (cancel_mono S.inclusion).mp (by simp [Category.assoc, hs]), hs⟩⟩

private theorem dimension_of_iso {G H : GroupScheme k} (e : G ≅ H) :
    topologicalKrullDim G.X.left = topologicalKrullDim H.X.left := by
  let f := ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso e
  exact IsHomeomorph.topologicalKrullDim_eq _ f.hom.homeomorph.isHomeomorph

private theorem dimension_of_subgroup_le {G : GroupScheme k} {S T : ClosedSubgroup G}
    (h : IsSubgroupOf S T) : topologicalKrullDim S.group.X.left ≤ topologicalKrullDim T.group.X.left := by
  obtain ⟨j, hj⟩ := h
  letI := factor_closed (H := S) (N := T) hj
  exact (IsClosedImmersion.isClosedEmbedding j.hom.hom.left).isInducing.topologicalKrullDim_le

private theorem split_dimension_le_rank (G : AffineAlgebraicGroup k)
    (S : ClosedSubgroup G.val) (hs : IsSplitTorus S.group) :
    topologicalKrullDim S.group.X.left ≤ relativeRank G :=
  le_iSup (fun T : {T : ClosedSubgroup G.val // IsSplitTorus T.group} ↦
    topologicalKrullDim T.val.group.X.left) ⟨S, hs⟩

private theorem rank_le_dimension (G : AffineAlgebraicGroup k) :
    relativeRank G ≤ topologicalKrullDim G.val.X.left := by
  apply iSup_le
  intro T
  letI := T.val.isClosedImmersion
  exact T.val.inclusion.hom.hom.left.isClosedEmbedding.isInducing.topologicalKrullDim_le

private theorem maximal_split_over (G : AffineAlgebraicGroup k)
    (S : ClosedSubgroup G.val) (hs : IsSplitTorus S.group) :
    ∃ T : ClosedSubgroup G.val, IsMaximalSplitTorus T ∧ IsSubgroupOf S T := by
  classical
  letI := G.property.1
  letI := G.property.2.1
  letI : IsLocallyNoetherian G.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
  letI : IsNoetherianRing Γ(G.val.X.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let heights : Set ℕ := {n | ∃ T : ClosedSubgroup G.val, IsSplitTorus T.group ∧
    IsSubgroupOf S T ∧ (definingIdeal T).height.toNat = n}
  obtain ⟨n, ⟨T, ht, hst, hheight⟩, hmin⟩ := wellFounded_lt.has_min heights
    ⟨_, S, hs, ⟨𝟙 _, Category.id_comp _⟩, rfl⟩
  refine ⟨T, ⟨ht, ?_⟩, hst⟩
  rintro V hv ⟨j, hj⟩
  have hle := definingIdeal_le j hj
  haveI := definingIdeal_prime_of_torus T (isTorus_of_split ht)
  haveI := definingIdeal_prime_of_torus V (isTorus_of_split hv)
  have heq : definingIdeal V = definingIdeal T := by
    by_contra hne
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
    have hV := ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := definingIdeal V))
    have hT := ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := definingIdeal T))
    have hv' : (definingIdeal V).height.toNat < n :=
      hheight ▸ ENat.natCast_lt_natCast.mp (hV.symm ▸ hT.symm ▸ hlt)
    obtain ⟨i, hi⟩ := hst
    exact hmin _ ⟨V, hv, ⟨i ≫ j, by rw [Category.assoc, hj, hi]⟩, rfl⟩ hv'
  haveI := factor_iso_of_definingIdeal_eq j hj heq.symm
  exact ⟨CategoryTheory.inv j, by rw [← hj, IsIso.inv_hom_id_assoc]⟩

private theorem split_rank_eq_dimension (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (ht : IsMaximalSplitTorus T) :
    topologicalKrullDim T.group.X.left = relativeRank G := by
  change _ = ⨆ S : {S : ClosedSubgroup G.val // IsSplitTorus S.group},
    topologicalKrullDim S.val.group.X.left
  apply le_antisymm
  · exact split_dimension_le_rank G T ht.1
  · apply iSup_le
    rintro ⟨S, hs⟩
    obtain ⟨V, hv, hsv⟩ := maximal_split_over G S hs
    obtain ⟨_, e, _⟩ := LinearAlgebraicGroups.Relative.MaximalSplitTori.maximalSplitToriConjugate
      G hG V T hv ht
    exact (dimension_of_subgroup_le hsv).trans_eq (dimension_of_iso e)

private def empty_power_iso :
    (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin 0))).val ≅
      Grp.trivial (SchemeOver k) := by
  let A := Specs.StandardGroups.LaurentPowerCoordinates k (ULift.{u} (Fin 0))
  let h := (LinearAlgebraicGroups.StandardGroups.tensorPowerCoordinatesSpecification.1
    k (ULift.{u} (Fin 0))).2
  let i : CommAlgCat.of k A ≅ CommAlgCat.of k k := CommAlgCat.isoMk (Classical.choice h)
  let j := (testSpec k).mapIso i.symm.op
  let e : (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin 0))).val.X ≅
      𝟙_ (SchemeOver k) := j ≪≫ trivialSchemeIso k
  have ht := isTerminalTensorUnit (C := SchemeOver k)
  letI : IsMonHom e.hom := ⟨ht.hom_ext _ _, ht.hom_ext _ _⟩
  exact Grp.mkIso' e

private theorem trivial_split_torus :
    IsSplitTorus (Grp.trivial (SchemeOver k)) :=
  ⟨0, ⟨empty_power_iso.symm⟩⟩

theorem maximalSplitDimension : MaximalSplitDimension.{u} := by
  intro k _ G hG
  obtain ⟨T, ht, _⟩ := maximal_split_over G (identitySubgroup G) trivial_split_torus
  exact ⟨⟨T, ht⟩, fun S hs ↦ split_rank_eq_dimension G hG S hs⟩

private theorem split_maximal_of_maximal_torus [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} (ht : IsMaximalTorus T) : IsMaximalSplitTorus T :=
  ⟨split_of_maximal (A := G) ht, fun S hs hts ↦ ht.2 S (isTorus_of_split hs) hts⟩

theorem maximalGeometricDimension : MaximalGeometricDimension.{u} := by
  intro k _ G hG
  let H := GeometricGroup G
  obtain ⟨T, ht, _⟩ := exists_maximal_torus_over H (identitySubgroup H)
    (isTorus_of_split trivial_split_torus)
  exact ⟨⟨T, ht⟩, fun S hs ↦
    split_rank_eq_dimension H (reductive_geometricGroup G hG) S (split_maximal_of_maximal_torus hs)⟩

private theorem laurent_localization {I : Type u} [Fintype I] :
    ∃ f : MvPolynomial I k, f ≠ 0 ∧ Nonempty
      (Localization.Away f ≃+* AddMonoidAlgebra k (I → ℤ)) := by
  classical
  let P := MvPolynomial I k
  let A := AddMonoidAlgebra k (I → ℤ)
  let v : (I →₀ ℕ) →+ (I → ℤ) :=
    { toFun := fun a i ↦ (a i : ℤ)
      map_zero' := by ext i; simp
      map_add' := by intro a b; ext i; simp }
  have hv : Function.Injective v := by
    intro a b h
    exact Finsupp.ext fun i ↦ Int.ofNat_inj.mp (congrFun h i)
  let F : P →ₐ[k] A := AddMonoidAlgebra.mapDomainAlgHom k k v
  letI : Algebra P A := F.toRingHom.toAlgebra
  have hF : Function.Injective F := AddMonoidAlgebra.mapDomain_injective hv
  let w : I →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ ↦ 1
  have hw (i : I) : w i = 1 := congrFun (Finsupp.equivFunOnFinite.apply_symm_apply (fun _ : I => (1 : ℕ))) i
  let f : P := AddMonoidAlgebra.single w 1
  have hf : f ≠ 0 := AddMonoidAlgebra.single_eq_zero.not.mpr one_ne_zero
  have hFf : F f = AddMonoidAlgebra.single (v w) 1 :=
    AddMonoidAlgebra.mapDomain_single
  letI : IsLocalization.Away f A := by
    apply (isLocalization_iff (Submonoid.powers f) A).mpr
    change (∀ y : Submonoid.powers f, IsUnit (F y)) ∧
      (∀ z : A, ∃ x : P × Submonoid.powers f, z * F x.2 = F x.1) ∧
      ∀ {x y : P}, F x = F y → ∃ c : Submonoid.powers f, c * x = c * y
    constructor
    · rintro ⟨y, n, rfl⟩
      rw [map_pow, hFf]
      refine IsUnit.pow _ ⟨⟨_, AddMonoidAlgebra.single (-v w) 1, ?_, ?_⟩, rfl⟩
      · change (AddMonoidAlgebra.single (v w) (1 : k)) *
          AddMonoidAlgebra.single (-v w) (1 : k) = 1
        rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul]
        rfl
      · change (AddMonoidAlgebra.single (-v w) (1 : k)) *
          AddMonoidAlgebra.single (v w) (1 : k) = 1
        rw [AddMonoidAlgebra.single_mul_single, neg_add_cancel, one_mul]
        rfl
    constructor
    · suffices ∀ z : A, ∃ (n : ℕ) (p : P), z * F (f ^ n) = F p by
        intro z
        obtain ⟨n, p, hp⟩ := this z
        exact ⟨(p, ⟨f ^ n, n, rfl⟩), hp⟩
      intro z
      induction z using AddMonoidAlgebra.induction_on with
      | of m =>
          let n := ∑ i : I, (-(m i)).toNat
          have hnonneg (i : I) : 0 ≤ m i + (n : ℤ) := by
            have hle : (-(m i)).toNat ≤ n := Finset.single_le_sum (f := fun j : I ↦ (-(m j)).toNat) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
            omega
          let a : I →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i ↦ (m i + (n : ℤ)).toNat)
          have ha (i : I) : (a i : ℤ) = m i + (n : ℤ) := by
            have hi : a i = (m i + (n : ℤ)).toNat := congrFun (Finsupp.equivFunOnFinite.apply_symm_apply (fun j : I => (m j + (n : ℤ)).toNat)) i
            rw [hi, Int.toNat_of_nonneg (hnonneg i)]
          refine ⟨n, AddMonoidAlgebra.single a 1, ?_⟩
          change AddMonoidAlgebra.single m 1 * F (f ^ n) = F (AddMonoidAlgebra.single a 1)
          rw [map_pow, hFf, AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.single_mul_single, mul_one]
          change _ = AddMonoidAlgebra.mapDomain v (AddMonoidAlgebra.single a 1)
          rw [AddMonoidAlgebra.mapDomain_single]
          congr 1
          funext i
          change m i + n • (w i : ℤ) = (a i : ℤ)
          rw [ha, hw]
          simp
      | add x y hx hy =>
          obtain ⟨n, p, hp⟩ := hx
          obtain ⟨m, q, hq⟩ := hy
          refine ⟨n + m, p * f ^ m + q * f ^ n, ?_⟩
          rw [add_mul, map_add, map_mul, map_mul, pow_add, map_mul]
          congr 1
          · rw [← mul_assoc, hp]
          · rw [mul_comm (F (f ^ n)), ← mul_assoc, hq]
      | smul r z hz =>
          obtain ⟨n, p, hp⟩ := hz
          refine ⟨n, r • p, ?_⟩
          rw [smul_mul_assoc, hp, map_smul]
    · intro x y hxy
      exact ⟨1, by rw [hF hxy]⟩
  exact ⟨f, hf, ⟨(IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) A).toRingEquiv⟩⟩

private theorem standard_torus_dimension (r : ℕ) :
    topologicalKrullDim (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val.X.left =
      (r : WithBot ℕ∞) := by
  let I := ULift.{u} (Fin r)
  change topologicalKrullDim (PrimeSpectrum (AddMonoidAlgebra k (I → ℤ))) = _
  obtain ⟨f, hf, ⟨e⟩⟩ := laurent_localization (k := k) (I := I)
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← ringKrullDim_eq_of_ringEquiv e,
    krull_dimension_localization_away (k := k) hf,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    (ringKrullDimZero_iff_ringKrullDim_eq_zero (R := k)).mp inferInstance, zero_add]
  simp [I]

private theorem split_baseChange_dimension (K : Type u) [Field K] [Algebra k K]
    {T : GroupScheme k} (h : IsSplitTorus T) :
    IsSplitTorus ((groupBaseChange k K).obj T) ∧
    topologicalKrullDim ((groupBaseChange k K).obj T).X.left = topologicalKrullDim T.X.left := by
  obtain ⟨r, ⟨e⟩⟩ := h
  obtain ⟨j⟩ := splitTorus_baseChange (k := k) K r
  let f : (groupBaseChange k K).obj T ≅
      (Specs.StandardGroups.multiplicativePowerGroup K (ULift.{u} (Fin r))).val :=
    (groupBaseChange k K).mapIso e ≪≫ j
  refine ⟨⟨r, ⟨f⟩⟩, ?_⟩
  rw [dimension_of_iso f, standard_torus_dimension, dimension_of_iso e, standard_torus_dimension]

theorem rankComparison : RankComparison.{u} := by
  intro k _ G hG
  let K := AlgebraicClosure k
  have hle : relativeRank G ≤ geometricRank G := by
    apply iSup_le
    rintro ⟨S, hs⟩
    obtain ⟨hs', hd⟩ := split_baseChange_dimension K hs
    exact hd.symm.le.trans (split_dimension_le_rank (GeometricGroup G) (extendSubgroup K S) hs')
  refine ⟨hle, fun hsplit ↦ le_antisymm hle ?_⟩
  obtain ⟨T, ht, hc, hmax⟩ := hsplit.2
  obtain ⟨_, hd⟩ := split_baseChange_dimension K ht
  calc
    geometricRank G = topologicalKrullDim ((groupBaseChange k K).obj T.group).X.left :=
      ((maximalGeometricDimension G hG).2 _ hmax).symm
    _ = topologicalKrullDim T.group.X.left := hd
    _ ≤ relativeRank G := split_dimension_le_rank G T ht

private theorem rank_eq_dimension_of_split {G : AffineAlgebraicGroup k}
    (hG : IsSplitTorus G.val) : relativeRank G = topologicalKrullDim G.val.X.left := by
  let I : ClosedSubgroup G.val := ⟨G.val, 𝟙 _, inferInstanceAs (IsClosedImmersion (𝟙 G.val.X.left))⟩
  exact le_antisymm (rank_le_dimension G) (split_dimension_le_rank G I hG)

private theorem contracting_trivial_of_whole (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (c : Cocharacter G.val) (D : LimitDecomposition c) [IsIso D.parabolic.inclusion] :
    IsTrivialSubgroup D.contracting := by
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected (X := G.val.X) hG.2.1
  have hs := (limitSubgroupsSmooth G c D).2.1
  have hc := (geometricallyConnectedLimitSubgroups G c D).2.1
  have hu := contractingSubgroupUnipotent G c D
  have hn : IsNormalSubgroup D.contracting.inclusion := by
    let U : ClosedSubgroup D.parabolic.group :=
      ⟨D.contracting.group, D.contractingToParabolic, factor_closed D.contracting_in_G⟩
    have h := normal_postcompose_iso D.contractingToParabolic (asIso D.parabolic.inclusion)
      (normalOfSchemeKernel (U := U) (d := D.limit) D.isKernel)
    change IsNormalSubgroup (D.contractingToParabolic ≫ D.parabolic.inclusion) at h
    simpa only [D.contracting_in_G] using h
  let K := AlgebraicClosure k
  let N := extendSubgroup K D.contracting
  have hn' := baseChangeNormalSubgroup k K D.contracting.inclusion hn
  -- Reductivity kills the smooth connected normal contracting group geometrically.
  have hN : IsSmoothConnectedNormal (G := GeometricGroup G) N := by
    have hs' := smooth_baseChangedGroup (K := K) (A := D.contracting.group) hs
    have hc' := connected_baseChangedGroup (K := K) (closedSubgroupAlgebraicGroup D.contracting)
      (connected_of_geometricallyConnected (X := D.contracting.group.X) hc)
    exact ⟨hs', hc', hn'⟩
  have hu' : IsUnipotent (closedSubgroupAlgebraicGroup (G := GeometricGroup G) N) := by
    obtain ⟨M, f, hf⟩ := (LinearAlgebraicGroups.Unipotent.unipotenceFieldExtension
      (K := K) (closedSubgroupAlgebraicGroup D.contracting)).mpr hu
    exact ⟨M, f, hf⟩
  have hrad := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G
  exact (trivial_baseChange_iff (K := K) D.contracting.group).mp
    (trivialOfSubgroup (hrad.2.2 N hN hu') hG.2.2)

private theorem isCentral_of_whole (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (c : Cocharacter G.val) (D : LimitDecomposition c) [IsIso D.parabolic.inclusion] :
    IsCentralCocharacter c := by
  obtain ⟨e⟩ := contracting_trivial_of_whole G hG c D
  have hU : IsSubgroupOf D.contracting D.centralizer := by
    refine ⟨0, ?_⟩
    exact (IsZero.eq_of_src ((Grp.isZero_trivial _).of_iso e) _ _)
  intro X x
  let y := x ≫ (CategoryTheory.inv D.parabolic.inclusion).hom.hom
  have hy : y ≫ D.parabolic.inclusion.hom.hom = x := by
    have h := (Grp.forget (SchemeOver k)).congr_map (IsIso.inv_hom_id D.parabolic.inclusion)
    change (CategoryTheory.inv D.parabolic.inclusion).hom.hom ≫ D.parabolic.inclusion.hom.hom = 𝟙 _ at h
    simp only [y, Category.assoc, h, Category.comp_id]
  apply (D.centralizer_points _ _).2
  rw [← hy]
  exact (limitSectionMemIff D hU y).2 ⟨y ≫ D.limit.hom.hom, rfl⟩

private theorem whole_of_isCentral {H : GroupScheme k} (c : Cocharacter H)
    (D : LimitDecomposition c) (hc : IsCentralCocharacter c) : IsIso D.parabolic.inclusion := by
  obtain ⟨i, hi⟩ := (D.centralizer_points _ _).mp (hc _ (𝟙 _))
  obtain ⟨j, hj⟩ := factor_group_through_subgroup D.centralizer (𝟙 H) i hi
  exact inclusion_iso_of_section D.parabolic (j ≫ D.sectionMap)
    (by rw [Category.assoc, D.section_in_G, hj])

theorem properDynamicParabolic : ProperDynamicParabolic.{u} := by
  intro k _ G hG c D
  refine ⟨limitIsParabolic G hG c D, ?_⟩
  exact not_congr ⟨fun h ↦ by letI := h; exact isCentral_of_whole G hG c D, whole_of_isCentral c D⟩

private theorem central_iff_comp_eq_zero {G Q : AffineAlgebraicGroup k}
    {Z : ClosedSubgroup G.val} {q : G.val ⟶ Q.val} (hq : IsAdjointQuotient Z q)
    (c : Cocharacter G.val) : IsCentralCocharacter c ↔ c ≫ q = 0 := by
  constructor
  · intro hc
    have hcent : Centralizes (𝟙 G.val) c.hom.hom := by
      apply (centralizes_iff _ _).mpr
      intro X t x
      simpa using ((centralizes_iff c x).mp (hc X x) X (𝟙 X) t).symm
    obtain ⟨i, hi⟩ := (hq.1 _ _).mp hcent
    obtain ⟨j, hj⟩ := factor_group_through_subgroup Z c i hi
    have hz : Z.inclusion ≫ q = 0 := by
      apply Grp.hom_ext
      exact hq.2.1.w
    rw [← hj, Category.assoc, hz, comp_zero]
  · intro hc
    obtain ⟨i, hi⟩ := liftToSchemeKernel hq.2.1 c hc
    have hcent := (hq.1 _ _).mpr ⟨i.hom.hom, congrArg (Grp.forget (SchemeOver k)).map hi⟩
    intro X x
    apply (centralizes_iff _ _).mpr
    intro U t y
    simpa using ((centralizes_iff (𝟙 G.val) c.hom.hom).mp hcent U y (t ≫ x)).symm

private theorem gm_dimension :
    topologicalKrullDim (specGroup (groupAlgebra k IntegerCharacters.{u})).X.left = 1 := by
  obtain ⟨i⟩ := multiplicative_group_iso (k := k)
  rw [dimension_of_iso i, standard_torus_dimension]
  rfl

private theorem gm_id_ne_zero :
    𝟙 (specGroup (groupAlgebra k IntegerCharacters.{u})) ≠ 0 := by
  intro h
  let e := ((IsZero.iff_id_eq_zero _).mpr h).iso (Grp.isZero_trivial (SchemeOver k))
  have hd := dimension_of_iso (e ≪≫ empty_power_iso.symm)
  rw [gm_dimension, standard_torus_dimension] at hd
  exact one_ne_zero hd

private theorem cocharacter_of_split_power {T : GroupScheme k} {r : ℕ} (hr : 0 < r)
    (e : T ≅ (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val) :
    ∃ c : Cocharacter T, c ≠ 0 := by
  let M := StandardLattice.{u} r
  let i : Fin r := ⟨0, hr⟩
  let a : M →* IntegerCharacters.{u} := Pi.evalMonoidHom _ i
  let b : IntegerCharacters.{u} →* M := MonoidHom.pi fun _ ↦ MonoidHom.id _
  have hab : a.comp b = MonoidHom.id _ := MonoidHom.ext fun _ ↦ rfl
  obtain ⟨j⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  let g := j ≪≫ e.symm
  let c : Cocharacter T := specGroupMap (groupAlgebraMap k a) ≫ g.hom
  let d : T ⟶ specGroup (groupAlgebra k IntegerCharacters.{u}) :=
    g.inv ≫ specGroupMap (groupAlgebraMap k b)
  have hcd : c ≫ d = 𝟙 _ := by
    simp only [c, d, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← specGroupMap_comp]
    have h : groupAlgebraMap k b ≫ groupAlgebraMap k a = 𝟙 _ := by
      apply CommHopfAlgCat.hom_ext
      change (MonoidAlgebra.mapDomainBialgHom k a).comp (MonoidAlgebra.mapDomainBialgHom k b) = _
      rw [← MonoidAlgebra.mapDomainBialgHom_comp, hab, MonoidAlgebra.mapDomainBialgHom_id]
      rfl
    rw [h]
    exact (hopfSpec (CommRingCat.of k)).map_id _
  refine ⟨c, fun hc ↦ gm_id_ne_zero (k := k) ?_⟩
  rw [← hcd, hc, zero_comp]

private theorem rank_nonneg (G : AffineAlgebraicGroup k) : 0 ≤ relativeRank G := by
  have h := split_dimension_le_rank G (identitySubgroup G) trivial_split_torus
  change topologicalKrullDim (Grp.trivial (SchemeOver k)).X.left ≤ relativeRank G at h
  rwa [← dimension_of_iso (empty_power_iso (k := k)), standard_torus_dimension] at h

private instance integerCharactersFG : Group.FG IntegerCharacters.{u} :=
  let e : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
  Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

private instance integerCharactersTorsionFree : IsMulTorsionFree IntegerCharacters.{u} :=
  let e : IntegerCharacters.{u} ≃* Multiplicative ℤ := MulEquiv.ulift
  Function.Injective.isMulTorsionFree e.toMonoidHom e.injective

private theorem positive_rank_iff_cocharacter (G : AffineAlgebraicGroup k) :
    0 < relativeRank G ↔ ∃ c : Cocharacter G.val, c ≠ 0 := by
  constructor
  · intro h
    have hS : ∃ S : ClosedSubgroup G.val, IsSplitTorus S.group ∧
        0 < topologicalKrullDim S.group.X.left := by
      by_contra! hnone
      exact h.not_ge (iSup_le fun S ↦ hnone S.val S.property)
    obtain ⟨S, ⟨r, ⟨e⟩⟩, hd⟩ := hS
    rw [dimension_of_iso e, standard_torus_dimension] at hd
    have hr : 0 < r := by
      by_contra! hn
      rw [Nat.eq_zero_of_le_zero hn] at hd
      exact (lt_irrefl 0) hd
    obtain ⟨c, hc⟩ := cocharacter_of_split_power hr e
    letI := inclusion_mono S
    refine ⟨c ≫ S.inclusion, fun h ↦ hc ((cancel_mono S.inclusion).mp ?_)⟩
    simpa only [zero_comp] using h
  · rintro ⟨c, hc⟩
    let M := diagonalGroup k IntegerCharacters.{u}
    obtain ⟨T, p, ⟨r, ⟨e⟩⟩, hp⟩ := splitTorusImage M G ⟨1, multiplicative_group_iso⟩ c
    have hr : r ≠ 0 := by
      rintro rfl
      haveI := (Grp.isZero_trivial _).of_iso (e ≪≫ empty_power_iso)
      have h : p = 0 := IsZero.eq_of_tgt this _ _
      exact hc (by rw [← hp.1, h, zero_comp])
    have hd : (r : WithBot ℕ∞) ≤ relativeRank G := by
      rw [← standard_torus_dimension (k := k), ← dimension_of_iso e]
      exact split_dimension_le_rank G T ⟨r, ⟨e⟩⟩
    apply lt_of_lt_of_le _ hd
    exact_mod_cast Nat.pos_of_ne_zero hr

open private groupAlgebraMap_injective from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

private theorem powerOnGm_epi (n : ℕ) (hn : 0 < n) : Epi (powerOnGm k n) := by
  let a := groupAlgebraMap k (powMonoidHom (α := IntegerCharacters.{u}) n)
  haveI : Algebra.FiniteType k (groupAlgebra k IntegerCharacters.{u}) :=
    inferInstanceAs (Algebra.FiniteType k (MonoidAlgebra k IntegerCharacters.{u}))
  have ha := groupAlgebraMap_injective (k := k) (powMonoidHom (α := IntegerCharacters.{u}) n)
    (fun x y h ↦ eq_of_pow_eq_pow_of_commute hn.ne' (Commute.all x y) h)
  have h := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom a.hom.toAlgHom.toRingHom)).mpr
    (hopfFaithfulFlatness k a ha)
  letI : Flat (powerOnGm k n).hom.hom.left := h.1
  letI : Surjective (powerOnGm k n).hom.hom.left := h.2
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  exact F.epi_of_epi_map (f := powerOnGm k n)
    (Flat.epi_of_flat_of_surjective (powerOnGm k n).hom.hom.left)

private theorem exists_proper_dynamic_of_noncentral (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (c : Cocharacter G.val) (hc : ¬ IsCentralCocharacter c) :
    HasProperParabolic G := by
  obtain ⟨D⟩ := existsLimitDecomposition G c
  obtain ⟨hp, h⟩ := properDynamicParabolic G hG c D
  exact ⟨D.parabolic, hp, h.mpr hc⟩

private theorem proper_parabolic_cocharacter (G : AffineAlgebraicGroup k)
    (hP : HasProperParabolic G) :
    ∃ c : Cocharacter G.val, ¬ IsCentralCocharacter c := by
  obtain ⟨P, hp, hproper⟩ := hP
  obtain ⟨c, D, hsame, _⟩ := LinearAlgebraicGroups.Relative.RationalCocharacter.rationalParabolic G P hp
  obtain ⟨e, he⟩ := subgroupIso_of_same hsame
  refine ⟨c, fun hc ↦ hproper ?_⟩
  haveI := whole_of_isCentral c D hc
  rw [← he]
  infer_instance

theorem adjointParabolicCriterion : AdjointParabolicCriterion.{u} := by
  intro k _ G Q Z q hG hq
  change HasProperParabolic G ↔ 0 < relativeRank Q
  rw [positive_rank_iff_cocharacter]
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := proper_parabolic_cocharacter G hp
    exact ⟨c ≫ q, fun h ↦ hc ((central_iff_comp_eq_zero hq c).mpr h)⟩
  · rintro ⟨a, ha⟩
    obtain ⟨n, hn, c, hc⟩ := LinearAlgebraicGroups.Descent.AdjointCocharacters.adjointCocharacterLift
      Z q hG hq a
    apply exists_proper_dynamic_of_noncentral G hG c
    intro hz
    haveI := powerOnGm_epi (k := k) n hn
    apply ha
    apply (cancel_epi (powerOnGm k n)).mp
    rw [← hc, (central_iff_comp_eq_zero hq c).mp hz, comp_zero]

open private finiteSpectrumIff from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies

private theorem finite_group_dimension_le_zero (G : AffineAlgebraicGroup k)
    (hG : IsFinite G.val.X.hom) : topologicalKrullDim G.val.X.left ≤ 0 := by
  let A := Specs.AdjointCocharacters.coordinateHopf G
  let e := Specs.AdjointCocharacters.coordinateHopfIso G
  let i := ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso e
  haveI := hG
  have h : (specGroup A).X.hom = i.hom ≫ G.val.X.hom := e.hom.hom.hom.w.symm
  haveI : IsFinite (specGroup A).X.hom := h ▸ inferInstance
  haveI : Module.Finite k A := (finiteSpectrumIff A).mp inferInstance
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  rw [← dimension_of_iso e]
  change topologicalKrullDim (PrimeSpectrum A) ≤ _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact Order.krullDim_nonpos_iff_forall_isMax.mpr fun p ↦ by
    letI : p.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime p.asIdeal
    intro q hpq
    exact (Ideal.IsMaximal.eq_of_le inferInstance q.isPrime.ne_top hpq).ge

private theorem cocharacter_into_finite_is_zero (G : AffineAlgebraicGroup k)
    (hG : IsFinite G.val.X.hom) (c : Cocharacter G.val) : c = 0 := by
  by_contra hc
  have h := (positive_rank_iff_cocharacter G).mpr ⟨c, hc⟩
  exact h.not_ge ((rank_le_dimension G).trans (finite_group_dimension_le_zero G hG))

private theorem reductive_of_semisimple (G : AffineAlgebraicGroup k)
    (hG : IsSemisimple G) : IsReductive G := by
  let U := Specs.GeometricRadicals.geometricUnipotentRadical G
  have hU := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G
  have hR := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G
  have hsol := solvable_of_smooth_connected_unipotent (closedSubgroupAlgebraicGroup U)
    hU.1.1 hU.1.2.1 hU.2.1
  exact ⟨hG.1, hG.2.1, trivialOfSubgroup (hR.2.2 U hU.1 hsol) hG.2.2⟩

theorem semisimpleParabolicCriterion : SemisimpleParabolicCriterion.{u} := by
  intro k _ G hss
  have hG := reductive_of_semisimple G hss
  obtain ⟨Z, Q, q, hq, _⟩ :=
    LinearAlgebraicGroups.Descent.AdjointCocharacters.adjointQuotientExists G hG
  change HasProperParabolic G ↔ 0 < relativeRank G
  rw [positive_rank_iff_cocharacter]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := proper_parabolic_cocharacter G h
    exact ⟨c, fun hz ↦ hc ((central_iff_comp_eq_zero hq c).mpr (by rw [hz, zero_comp]))⟩
  · rintro ⟨c, hc⟩
    apply exists_proper_dynamic_of_noncentral G hG c
    intro hcent
    obtain ⟨a, ha⟩ := liftToSchemeKernel hq.2.1 c ((central_iff_comp_eq_zero hq c).mp hcent)
    have hfin := (LinearAlgebraicGroups.Reductive.CentralDerived.semisimpleIffFiniteCentre G hG Z hq.1).mp hss
    have hz := cocharacter_into_finite_is_zero (closedSubgroupAlgebraicGroup Z) hfin a
    exact hc (by rw [← ha, hz, zero_comp])


open Coalgebra
open private gmCharacterEquiv gmCharacter_fixed from LinearAlgebraicGroups.Descent.AdjointCocharacters
open private splitHopfIso counit_is_identity from LinearAlgebraicGroups.Multiplicative.NormOneTorus
open private geometricHopfMaps_ext extendedHopfMap_equivariant includeScalarExtension_injective
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open Specs.CharacterDescent (GeometricCharacters)
open Specs.SmoothnessAndIsogenies (pullbackCharacter)

private theorem baseChange_counit_unit_apply (K : Type u) [Field K] [Algebra k K]
    (A B : HopfAlgebraCategory k) (x : extendedHopf K A) :
    (extendedHopfMap K (hopfCounit A ≫ hopfUnit B)).hom x =
      algebraMap K (extendedHopf K B) (counit (R := K) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    change a ⊗ₜ[k] (algebraMap k B (counit (R := k) b)) =
      (counit (R := K) (a ⊗ₜ[k] b)) ⊗ₜ[k] (1 : B)
    rw [TensorProduct.counit_tmul]
    change a ⊗ₜ[k] (algebraMap k B (counit (R := k) b)) =
      ((counit (R := k) b) • a) ⊗ₜ[k] (1 : B)
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

private theorem norm_one_cocharacter_zero {K : Type u} [Field K] [Algebra k K]
    [Algebra.IsQuadraticExtension k K] [Algebra.IsSeparable k K]
    {W H : AffineAlgebraicGroup k}
    {e : (groupPointsFunctor k).obj W.val ≅ WeilRestriction.extendedUnits k K}
    {n : W.val ⟶ H.val} (T : Specs.NormOneTorus.KernelModel e n)
    (c : Cocharacter (specGroup T.coordinate)) : c = 0 := by
  let A := T.coordinate
  let B := groupAlgebra k IntegerCharacters.{u}
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let f : A ⟶ B := (ff.preimage c).unop
  have hf : specGroupMap f = c := ff.map_preimage c
  obtain ⟨σ, hσ, _⟩ := LinearAlgebraicGroups.NormOneTorus.quadraticAutomorphism k K
  have hres : AlgEquiv.restrictNormalHom K σ ≠ 1 := by
    intro h
    change σ.restrictNormal K = 1 at h
    apply hσ
    ext x
    have he := AlgEquiv.restrictNormal_commutes σ K x
    simpa [h] using he.symm
  obtain ⟨χ, hχ⟩ := LinearAlgebraicGroups.Descent.NormOneTorus.kernelGeometry.2.2
    k K W H e n T K
  have htrivial (x : GeometricCharacters K A) : pullbackCharacter K f x = 1 := by
    obtain ⟨m, rfl⟩ := χ.surjective x
    have h1 := (hχ σ m).2 hres
    have h2 := extendedHopfMap_equivariant K f σ (χ m).val
    have h3 := gmCharacter_fixed (k := k) K σ (pullbackCharacter K f (χ m))
    have h4 : pullbackCharacter K f (χ m⁻¹) = pullbackCharacter K f (χ m) := by
      apply GroupLike.val_injective
      change (extendedHopfMap K f).hom (χ m⁻¹).val = _
      rw [← h1]
      change (extendedHopfMap K f).hom
          ((Descent.SemilinearAction.scalarExtension (K := K) A).act σ (χ m).val) = _
      change (extendedHopfMap K f).hom
          ((Descent.SemilinearAction.scalarExtension (K := K) A).act σ (χ m).val) =
        (Descent.SemilinearAction.scalarExtension (K := K) B).act σ
          ((extendedHopfMap K f).hom (χ m).val) at h2
      rw [h2]
      exact congrArg GroupLike.val h3
    let deg := (gmCharacterEquiv (k := k) K).symm
    let p := deg.toMonoidHom.comp ((pullbackCharacter K f).comp χ.toMonoidHom)
    let y : IntegerCharacters.{u} := p m
    have hi : p m⁻¹ = y := congrArg deg h4
    have hy : y⁻¹ = y := (map_inv p m).symm.trans hi
    have hsq : y ^ 2 = 1 := by
      calc
        y ^ 2 = y⁻¹ * y := by rw [pow_two, hy]
        _ = 1 := inv_mul_cancel y
    have hy₁ : y = 1 := eq_of_pow_eq_pow_of_commute (by decide : 2 ≠ 0)
      (Commute.one_right y) (by simpa only [one_pow] using hsq)
    exact deg.injective (hy₁.trans (map_one deg).symm)
  let z := hopfCounit A ≫ hopfUnit B
  have hz : specGroupMap z = 0 := by
    rw [show z = hopfCounit A ≫ hopfUnit B from rfl, specGroupMap_comp, counit_is_identity, comp_zero]
  have hdiag : Specs.CharacterDescent.IsDiagonalizable (extendedHopf K A) := by
    let M : Specs.DiagonalizableGroups.FGAbelianGroup.{u} := ⟨CommGrpCat.of IntegerCharacters.{u}, inferInstance⟩
    exact ⟨M, ⟨splitHopfIso σ hσ T (AlgHom.id k K)⟩⟩
  have hext : extendedHopfMap K f = extendedHopfMap K z := by
    apply geometricHopfMaps_ext K hdiag
    intro x
    change pullbackCharacter K f x = _
    rw [htrivial x]
    apply GroupLike.val_injective
    change (1 : extendedHopf K B) = (extendedHopfMap K z).hom x.val
    have hε := x.isGroupLikeElem_val.counit_eq_one
    -- Base change of the counit followed by the unit sends a group-like element to one.
    exact ((baseChange_counit_unit_apply K A B x.val).trans
      ((congrArg (algebraMap K (extendedHopf K B)) hε).trans (map_one _))).symm
  have heq : f = z := by
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.ext
    intro a
    apply includeScalarExtension_injective K B
    exact congrArg (fun g => g.hom ((1 : K) ⊗ₜ[k] a)) hext
  rw [← hf, heq, hz]

theorem quadraticNormOneRanks : QuadraticNormOneRanks.{u} := by
  intro k K _ _ _ _ _ W H e n T
  letI := T.finiteType
  let S := Specs.StandardGroups.spectrum k T.coordinate
  change relativeRank S = 0 ∧ geometricRank S = 1
  constructor
  · apply le_antisymm _ (rank_nonneg S)
    apply le_of_not_gt
    rw [positive_rank_iff_cocharacter]
    rintro ⟨c, hc⟩
    exact hc (norm_one_cocharacter_zero T c)
  · let L := AlgebraicClosure k
    let j : K →ₐ[k] L := IsAlgClosed.lift
    obtain ⟨σ, hσ, _⟩ := LinearAlgebraicGroups.NormOneTorus.quadraticAutomorphism k K
    let d := splitHopfIso σ hσ T j
    let i : (groupBaseChange k L).obj S.val ≅ specGroup (groupAlgebra L IntegerCharacters.{u}) :=
      (extendedGroupIso L T.coordinate).symm ≪≫ (hopfSpec (CommRingCat.of L)).mapIso d.op
    have hs : IsSplitTorus (GeometricGroup S).val := by
      obtain ⟨a⟩ := multiplicative_group_iso (k := L)
      exact ⟨1, ⟨i ≪≫ a⟩⟩
    change relativeRank (GeometricGroup S) = 1
    exact (rank_eq_dimension_of_split hs).trans ((dimension_of_iso i).trans gm_dimension)

end

end LinearAlgebraicGroups.Descent.RelativeRank
