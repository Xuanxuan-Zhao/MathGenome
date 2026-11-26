import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOmittedNodeLevis
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeChambers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeReflections
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerLeviDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerProductFactors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeANormOneModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeASplitRank
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MatrixFactorSplitRank
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SplitLeviMatrixComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Degree
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.MatrixDivision
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup

/-! The omitted-node Levis for the nonsplit inner E₆ and E₇ indices. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalOmittedNodeLevis

open LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character Cocharacter compositionPairing)
open Specs.CharacterPairing (absoluteRoots characterValue pairing powerMorphism)
open Specs.DiagonalizableGroups (diagonalGroup groupAlgebra IntegerCharacters)
open Specs.ExceptionalOmittedNodeLevis
open Specs.QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits subgroupAlongIso)
open Specs.QuasiSplitOrbitDerivedRoots (SplitFace)
open Specs.StandardParabolicLevi (HasFace leviRoots)
open Specs.OuterTypeAModels (HasAbsoluteSimplyConnectedTypeA)
open QuasiSplitOrbitLevis (attachedCorootBasis rationalDerivedLeviTorus splitLeviCocharacterSpan)
open QuasiSplitOrbitDerivedRoots (faceAttachedCoroots faceBorelRoots faceRootRestrictions
  splitDerivedSimplyConnected)
open private subgroupPreimage subgroupPreimage_pullback face_preimage_borel splitFace_reductive
  faceRootEquivalence attachedBase_regular face_character_span_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open Specs.CentralIsogenies (characterPullback)
open private pairing_pushforward from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private splitLeviForFace derivedSubgroupOfIso cocharacterFactorsThroughIntersection splitOfClosedTorus
  cocharacter_lifts_generate closedSubgroup_mono
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
open private simplyConnected_of_compared_baseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open Specs.BorelProper (IsParabolic)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.GeometricRadicals (GeometricGroup IsReductive IsSemisimple IsSmoothConnectedNormal IsSplitTorus IsTorus
  baseChangedSubgroup geometricSolvableRadical)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.CentralDerived (firstProjection)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup IsSolvable IsSubgroupOf RepresentsQuotient)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open Specs.Relative.RelativeChambers (relativeRoots)
open Specs.Relative.MaximalSplitTori (IsMinimalParabolic)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open CocharacterDynamics (LimitDecomposition cocharacterPoint existsLimitDecomposition
  laurentAlgebra laurentParameter unitPoint limitSubgroupsSmooth
  geometricallyConnectedLimitSubgroups)
open private reductive_of_semisimple inclusion_iso_of_section
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
open private limitParabolic_root_iff pushLimitParabolic geometricMaximal_of_rationalMaximal
  cocharacterCentralizerReductive groupBaseChangeTowerIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open private pushSubgroup normal_postcompose_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private extendSubgroup extend_subgroupOf subgroupOf_of_extend same_subgroup_trans
  cocharacter_ext_units subgroupIso_of_same limits_subgroups_extend from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private subgroupOf_trans factor_group_through_subgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private schemeKernel_postcompose_iso torus_smooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
open private isIso_of_scalarExtension centralIsogeny_postIso centralIsogeny_baseChange torusIso_of_isIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private trivialOfSubgroup centralInclusion mulMap postMul flatOfSurjectiveHom
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private baseChangeMapPullback baseChangeKernelSquare from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private pointHom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private isIso_of_schemeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private lieImage_mono subgroupOf_limit_of_rootSigns connected_of_geometricallyConnected
  torus_subgroupOf_centralizer rootsOfIso splitTorus_baseChange pairing_one smooth_baseChangedGroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private wholeSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RationalRealization
open Reductive.CentralDerived (derivedSemisimple derivedTorusQuotient)
open SchemeDerivedGroup (derivedSubgroupExists)
open Relative.RelativeChambers (limitParabolicThroughSplitTorus parabolicThroughSplitTorus
  minimalLimitParabolic relativeRootsByRestriction)
open RootData.CharacterPairing (characterPairingComposition perfectCharacterPairing
  characterValuesDetectCharacters)
open private characterValue_one isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private powerMorphism_eq_zpow from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeReflections
open private exists_integralValues from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SimpleRoots
open private characterValue_extend from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeChambers
open private laurentParameter_pow from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SpecialLinearDatum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- Extending a character and cocharacter together preserves the integer
exponent of their composite. Test on the universal Laurent monomial. -/
private theorem pairing_baseChange {S : GroupScheme F} (χ : Character S) (c : Cocharacter S)
    (e : MultiplicativeComparison F K) (he : PreservesUnits e) :
    pairing ((groupBaseChange F K).obj S) ((groupBaseChange F K).map χ ≫ e.inv)
      (e.hom ≫ (groupBaseChange F K).map c) = pairing S χ c := by
  let R₀ := CommAlgCat.of K K
  let R := laurentAlgebra R₀
  let t := laurentParameter R₀
  let S' := (groupBaseChange F K).obj S
  let d := e.hom ≫ (groupBaseChange F K).map c
  let ψ := (groupBaseChange F K).map χ ≫ e.inv
  have hc : baseChangePoint F K S.X R (cocharacterPoint d R t) =
      cocharacterPoint c ((restrictTestAlgebra F K).obj R) t := by
    change baseChangePoint F K S.X R
      ((unitPoint R t ≫ e.hom.hom.hom) ≫ (baseChange F K).map c.hom.hom) = _
    rw [baseChangePointsSchemeNaturality F K c.hom.hom, he R t]
    rfl
  have h := characterValue_extend χ e he R (cocharacterPoint d R t)
  rw [hc, (characterPairingComposition S χ c).2,
    (characterPairingComposition S' ψ d).2] at h
  change (↑(t ^ pairing S' ψ d) : R) = ↑(t ^ pairing S χ c) at h
  rw [laurentParameter_pow, laurentParameter_pow] at h
  exact (AddMonoidAlgebra.single_left_inj (one_ne_zero : (1 : K) ≠ 0)).mp h

variable {G : AffineAlgebraicGroup F} {n r : ℕ}

/-- The actual pairing is obtained by pairing against the restricted root. -/
private theorem pairing_restricted_simple (A : AdaptedPair G n) (white : Fin r → Fin n)
    (encode : Multiplicative (Fin r → ℤ) →* Character A.S.group)
    (h : ∀ i : Fin n, A.splitInAbsolute ≫ (A.numbering i).val.val =
      (groupBaseChange F (SeparableClosure F)).map
        (encode (Multiplicative.ofAdd (fun j => (Pi.single i 1 : Fin n → ℤ) (white j)))) ≫
        A.multiplicative.inv)
    (c : Cocharacter A.S.group) (i : Fin n) :
    pairing A.pair.T.group (A.numbering i).val.val (A.geometricCocharacter c) =
      pairing A.S.group
        (encode (Multiplicative.ofAdd (fun j => (Pi.single i 1 : Fin n → ℤ) (white j)))) c := by
  let d := A.multiplicative.hom ≫ (groupBaseChange F (SeparableClosure F)).map c
  calc
    _ = pairing ((groupBaseChange F (SeparableClosure F)).obj A.S.group)
        (A.splitInAbsolute ≫ (A.numbering i).val.val) d := by
          unfold pairing compositionPairing
          simp only [AdaptedPair.geometricCocharacter, d, Category.assoc]
    _ = _ := by
      rw [h i]
      exact pairing_baseChange _ c A.multiplicative A.multiplicative_eq

/-- Choose a rational cocharacter of the specified split torus on the
absolute face obtained by omitting one white node. -/
theorem exists_omitted_node_cocharacter (A : AdaptedPair G n) {white : Fin r → Fin n}
    (hwhite : Function.Injective white) (hw : HasWhiteRestrictions A white) (j₀ : Fin r) :
    ∃ c : Cocharacter A.S.group, ∀ i : Fin n,
      let p := pairing A.pair.T.group (A.numbering i).val.val (A.geometricCocharacter c)
      if i = white j₀ then 0 < p else p = 0 := by
  classical
  obtain ⟨encode, hinj, hres⟩ := hw
  obtain ⟨comm, hfree, hfinite, _, _, P, hP, hp⟩ :=
    perfectCharacterPairing A.S.group A.maximalSplit.1
  letI := comm
  letI := hfree
  letI := hfinite
  letI := hP
  let restriction : (Fin r → ℤ) →ₗ[ℤ] Additive (Character A.S.group) :=
    AddMonoidHom.toIntLinearMap
      { toFun := fun v => Additive.ofMul (encode (Multiplicative.ofAdd v))
        map_zero' := encode.map_one
        map_add' := encode.map_mul }
  have hrestriction : Function.Injective restriction := hinj
  let b := Pi.basisFun ℤ (Fin r)
  have hli : LinearIndependent ℤ (fun j => restriction (b j)) :=
    b.linearIndependent.map' restriction (LinearMap.ker_eq_bot.mpr hrestriction)
  obtain ⟨f, m, hm, hf⟩ := exists_integralValues hli (fun j => if j = j₀ then 1 else 0)
  let y := P.flip.toPerfPair.symm f
  let c : Cocharacter A.S.group := y.toMul
  have hvalue (v : Fin r → ℤ) :
      pairing A.S.group (encode (Multiplicative.ofAdd v)) c = f (restriction v) := by
    rw [← hp]
    exact DFunLike.congr_fun (P.flip.toPerfPair.apply_symm_apply f) (restriction v)
  refine ⟨c, fun i => ?_⟩
  dsimp only
  rw [pairing_restricted_simple A white encode hres, hvalue]
  by_cases hi : i ∈ Set.range white
  · obtain ⟨j, rfl⟩ := hi
    have hv : (fun l => (Pi.single (white j) 1 : Fin n → ℤ) (white l)) = b j := by
      rw [show b j = Pi.single j 1 from Pi.basisFun_apply ℤ (Fin r) j]
      funext l
      by_cases h : l = j
      · subst l
        simp
      · have h' : white l ≠ white j := fun e => h (hwhite e)
        simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
    rw [hv, hf]
    by_cases hj : j = j₀
    · subst j
      simpa using hm
    · have hnj : white j ≠ white j₀ := fun e => hj (hwhite e)
      simp [hj, hnj]
  · have hv : (fun l => (Pi.single i 1 : Fin n → ℤ) (white l)) = 0 := by
      funext l
      have h : white l ≠ i := fun e => hi ⟨l, e⟩
      exact Pi.single_eq_of_ne h 1
    rw [hv, map_zero, map_zero]
    have h : i ≠ white j₀ := fun e => hi ⟨j₀, e.symm⟩
    simp [h]


private theorem pushSubgroup_le_iff {A B : GroupScheme F} (e : A ≅ B)
    (X Y : ClosedSubgroup A) :
    IsSubgroupOf (pushSubgroup e X) (pushSubgroup e Y) ↔ IsSubgroupOf X Y := by
  change (∃ j : X.group ⟶ Y.group, j ≫ (Y.inclusion ≫ e.hom) = X.inclusion ≫ e.hom) ↔ _
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (Iso.cancel_iso_hom_right _ _ e).mp (by simpa only [Category.assoc] using hj)⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, by rw [← Category.assoc, hj]⟩

private theorem absolute_cocharacter_comparison (A : AdaptedPair G n)
    (c : Cocharacter A.S.group) :
    (A.geometricCocharacter c ≫ A.pair.T.inclusion) ≫ A.ambient.hom =
      A.multiplicative.hom ≫ (groupBaseChange F (SeparableClosure F)).map (c ≫ A.S.inclusion) := by
  simp only [AdaptedPair.geometricCocharacter, AdaptedPair.splitInAbsolute, Category.assoc, A.torus_eq]
  rw [← Functor.map_comp, A.intoTorus_eq, Functor.map_comp]

private theorem push_centralizer (A B : AffineAlgebraicGroup F)
    (e : A.val ≅ B.val) (c : Cocharacter A.val)
    (D : LimitDecomposition c) (E : LimitDecomposition (c ≫ e.hom)) :
    IsSubgroupOf (pushSubgroup e D.centralizer) E.centralizer := by
  let x := D.centralizer.inclusion.hom.hom
  have hc : Centralizes c x := (D.centralizer_points _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hx : Centralizes (c ≫ e.hom) (x ≫ e.hom.hom.hom) := by
    apply (centralizes_iff _ _).mpr
    intro U t u
    exact ((centralizes_iff _ _).mp hc U t u).map (IsMonHom.monoidHom e.hom.hom.hom U)
  obtain ⟨j, hj⟩ := (E.centralizer_points _ _).mp hx
  exact factor_group_through_subgroup E.centralizer (D.centralizer.inclusion ≫ e.hom) j hj

private theorem limitCentralizer_eq_of_cast {J : GroupScheme F} {a b : Cocharacter J}
    (h : a = b) (L : LimitDecomposition a) :
    (h ▸ L : LimitDecomposition b).centralizer = L.centralizer := by
  cases h
  rfl

private theorem push_centralizer_same (A B : AffineAlgebraicGroup F)
    (e : A.val ≅ B.val) (c : Cocharacter A.val)
    (D : LimitDecomposition c) (E : LimitDecomposition (c ≫ e.hom)) :
    SameSubgroup (pushSubgroup e D.centralizer) E.centralizer := by
  refine ⟨push_centralizer A B e c D E, ?_⟩
  have h : c = (c ≫ e.hom) ≫ e.inv := by simp [Category.assoc]
  have h' := push_centralizer B A e.symm (c ≫ e.hom) E (h ▸ D)
  rw [limitCentralizer_eq_of_cast h D] at h'
  obtain ⟨j, hj⟩ := h'
  refine ⟨j, ?_⟩
  change j ≫ D.centralizer.inclusion = E.centralizer.inclusion ≫ e.inv at hj
  change j ≫ (D.centralizer.inclusion ≫ e.hom) = E.centralizer.inclusion
  rw [← Category.assoc, hj, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Compare the rational limit parabolic with the one in the marked absolute
pair, using base change on the subgroup functors. -/
private theorem exists_absolute_limit (A : AdaptedPair G n) (c : Cocharacter A.S.group)
    (L : LimitDecomposition (c ≫ A.S.inclusion)) :
    ∃ D : LimitDecomposition (A.geometricCocharacter c ≫ A.pair.T.inclusion),
      SameSubgroup (pushSubgroup A.ambient D.parabolic)
        (extendSubgroup (SeparableClosure F) L.parabolic) ∧
      SameSubgroup (pushSubgroup A.ambient D.centralizer)
        (extendSubgroup (SeparableClosure F) L.centralizer) := by
  let H := baseChangedAlgebraicGroup (SeparableClosure F) G
  let ext := groupBaseChange F (SeparableClosure F)
  let d := A.geometricCocharacter c ≫ A.pair.T.inclusion
  obtain ⟨D⟩ := existsLimitDecomposition A.pair.G d
  have hd := absolute_cocharacter_comparison A c
  obtain ⟨E⟩ := existsLimitDecomposition H (d ≫ A.ambient.hom)
  have hE := pushLimitParabolic A.pair.G H A.ambient D E
  have hZ := push_centralizer_same A.pair.G H A.ambient d D E
  have hL := limits_subgroups_extend G L A.multiplicative A.multiplicative_eq (hd ▸ E)
  have hP : (hd ▸ E : LimitDecomposition
      (A.multiplicative.hom ≫ ext.map (c ≫ A.S.inclusion))).parabolic = E.parabolic := by
    generalize d ≫ A.ambient.hom = a at E hd
    generalize A.multiplicative.hom ≫ ext.map (c ≫ A.S.inclusion) = b at hd ⊢
    cases hd
    rfl
  have hC := limitCentralizer_eq_of_cast hd E
  exact ⟨D, same_subgroup_trans hE (hP ▸ hL.1), same_subgroup_trans hZ (hC ▸ hL.2.2)⟩

private theorem absolute_limits_le (A : AdaptedPair G n)
    (c d : Cocharacter A.pair.T.group)
    (C : LimitDecomposition (c ≫ A.pair.T.inclusion))
    (D : LimitDecomposition (d ≫ A.pair.T.inclusion)) :
    IsSubgroupOf C.parabolic D.parabolic ↔
      ∀ α : Specs.AbstractPairing.Root A.pair.T,
        0 ≤ pairing A.pair.T.group α.val c → 0 ≤ pairing A.pair.T.group α.val d := by
  constructor
  · intro h α hα
    exact (limitParabolic_root_iff _ _ d D α).mp (Set.Subset.trans
      ((limitParabolic_root_iff _ _ c C α).mpr hα) (lieImage_mono h))
  · intro h
    letI := A.pair.reductive.1
    letI : ConnectedSpace A.pair.G.val.X.left :=
      connected_of_geometricallyConnected A.pair.reductive.2.1
    refine subgroupOf_limit_of_rootSigns A.pair.G A.pair.reductive A.pair.T C.parabolic
      A.pair.split A.pair.maximal (limitSubgroupsSmooth _ _ C).1
      (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups _ _ C).1)
      (subgroupOf_trans (torus_subgroupOf_centralizer A.pair.split c C)
        ⟨C.sectionMap, C.section_in_G⟩) d D ?_
    intro α hα
    exact h α ((limitParabolic_root_iff _ _ c C α).mp hα)

/-- Inclusion of the rational limit parabolics is tested by all the
corresponding weak inequalities on absolute roots. -/
theorem limit_parabolics_le_iff (A : AdaptedPair G n) (c d : Cocharacter A.S.group)
    (C : LimitDecomposition (c ≫ A.S.inclusion))
    (D : LimitDecomposition (d ≫ A.S.inclusion)) :
    IsSubgroupOf C.parabolic D.parabolic ↔
      ∀ α : Specs.AbstractPairing.Root A.pair.T,
        0 ≤ pairing A.pair.T.group α.val (A.geometricCocharacter c) →
        0 ≤ pairing A.pair.T.group α.val (A.geometricCocharacter d) := by
  obtain ⟨C', hC, _⟩ := exists_absolute_limit A c C
  obtain ⟨D', hD, _⟩ := exists_absolute_limit A d D
  rw [← absolute_limits_le A _ _ C' D']
  constructor
  · intro h
    apply (pushSubgroup_le_iff A.ambient _ _).mp
    exact subgroupOf_trans hC.1 (subgroupOf_trans (extend_subgroupOf h) hD.2)
  · intro h
    apply subgroupOf_of_extend (K := SeparableClosure F)
    exact subgroupOf_trans hC.2 (subgroupOf_trans ((pushSubgroup_le_iff A.ambient _ _).mpr h) hD.1)


private theorem root_pairing_expansion (A : AdaptedPair G n)
    (α : Specs.AbstractPairing.Root A.pair.T) :
    ∃ v : Fin n → ℤ, ((∀ i, 0 ≤ v i) ∨ (∀ i, v i ≤ 0)) ∧
      ∀ d : Cocharacter A.pair.T.group,
        pairing A.pair.T.group α.val d = ∑ i, v i *
          pairing A.pair.T.group (A.numbering i).val.val d := by
  classical
  letI := A.datum.comm
  let D := A.datum.datum
  obtain ⟨v, _, hsign, hroot⟩ := A.datum.base.exists_root_eq_sum_int α
  refine ⟨fun i => v (A.numbering i).val,
    hsign.imp (fun h i => h.le _) (fun h i => h.le _), ?_⟩
  intro d
  let ev : Additive (Character A.pair.T.group) →ₗ[ℤ] ℤ :=
    D.rootDatum.toLinearMap.flip (Additive.ofMul d)
  have hev (j : Specs.AbstractPairing.Root A.pair.T) :
      ev (D.rootDatum.root j) = pairing A.pair.T.group j.val d := by
    change D.rootDatum.toLinearMap (D.rootDatum.root j) (Additive.ofMul d) = _
    rw [D.root_eq, D.pairing_eq]
  change D.rootDatum.root α = ∑ j ∈ A.datum.base.support,
    v j • D.rootDatum.root j at hroot
  have h := congrArg ev hroot
  simp only [map_sum, map_smul, hev, zsmul_eq_mul] at h
  rw [← Finset.sum_finset_coe] at h
  exact h.trans (Equiv.sum_comp
    (show Fin n ≃ A.datum.base.support from A.numbering) (fun j =>
      v j.val * pairing A.pair.T.group j.val.val d)).symm

private theorem negative_root_pairing (A : AdaptedPair G n)
    (α : Specs.AbstractPairing.Root A.pair.T) :
    ∃ β : Specs.AbstractPairing.Root A.pair.T, ∀ d : Cocharacter A.pair.T.group,
      pairing A.pair.T.group β.val d = - pairing A.pair.T.group α.val d := by
  letI := A.datum.comm
  let D := A.datum.datum
  refine ⟨D.rootDatum.reflectionPerm α α, fun d => ?_⟩
  rw [← D.pairing_eq, ← D.pairing_eq, ← D.root_eq, ← D.root_eq,
    RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, map_neg]
  rfl

private theorem parabolic_iso_of_absolute_nonnegative (A : AdaptedPair G n)
    (c : Cocharacter A.S.group) (L : LimitDecomposition (c ≫ A.S.inclusion))
    (hc : ∀ α : Specs.AbstractPairing.Root A.pair.T,
      0 ≤ pairing A.pair.T.group α.val (A.geometricCocharacter c)) :
    IsIso L.parabolic.inclusion := by
  obtain ⟨D, hD, _⟩ := exists_absolute_limit A c L
  let B := wholeSubgroup (SeparableClosure F) A.pair.G.val
  have hB : IsSubgroupOf B D.parabolic := by
    apply subgroupOf_limit_of_rootSigns A.pair.G A.pair.reductive A.pair.T B
      A.pair.split A.pair.maximal A.pair.reductive.1
      (connected_of_geometricallyConnected A.pair.reductive.2.1)
      ⟨A.pair.T.inclusion, Category.comp_id _⟩ (A.geometricCocharacter c) D
    exact fun α _ => hc α
  have hK : IsSubgroupOf (extendSubgroup (SeparableClosure F) (wholeSubgroup F G.val))
      (pushSubgroup A.ambient B) := by
    refine ⟨A.ambient.inv, ?_⟩
    change A.ambient.inv ≫ (𝟙 _ ≫ A.ambient.hom) =
      (groupBaseChange F (SeparableClosure F)).map (𝟙 _)
    simp
  obtain ⟨j, hj⟩ := subgroupOf_of_extend (K := SeparableClosure F)
    (subgroupOf_trans hK (subgroupOf_trans ((pushSubgroup_le_iff A.ambient _ _).mpr hB) hD.1))
  exact inclusion_iso_of_section _ j hj

private theorem absolute_nonnegative_of_parabolic_iso (A : AdaptedPair G n)
    (c : Cocharacter A.S.group) (L : LimitDecomposition (c ≫ A.S.inclusion))
    (hL : IsIso L.parabolic.inclusion) (α : Specs.AbstractPairing.Root A.pair.T) :
    0 ≤ pairing A.pair.T.group α.val (A.geometricCocharacter c) := by
  obtain ⟨D, hD, _⟩ := exists_absolute_limit A c L
  let ext := groupBaseChange F (SeparableClosure F)
  let e := ext.mapIso (asIso L.parabolic.inclusion)
  have hP : IsSubgroupOf (pushSubgroup A.ambient (wholeSubgroup (SeparableClosure F) A.pair.G.val))
      (extendSubgroup (SeparableClosure F) L.parabolic) := by
    refine ⟨A.ambient.hom ≫ e.inv, ?_⟩
    change (A.ambient.hom ≫ e.inv) ≫ e.hom = 𝟙 _ ≫ A.ambient.hom
    simp
  have hB := (pushSubgroup_le_iff A.ambient _ _).mp (subgroupOf_trans hP hD.2)
  apply (limitParabolic_root_iff _ _ (A.geometricCocharacter c) D α).mp
  intro x hx
  apply lieImage_mono hB
  refine ⟨x, ?_⟩
  change mapPointKernel (𝟙 A.pair.G.val) x = x
  rw [show mapPointKernel (𝟙 A.pair.G.val) =
      mapDualKernel (𝟙 ((groupPointsFunctor (SeparableClosure F)).obj A.pair.G.val)) by
    exact congrArg (fun f => mapDualKernel f)
      ((groupPointsFunctor (SeparableClosure F)).map_id A.pair.G.val)]
  exact Subtype.ext rfl

/-- An integral cocharacter with the prescribed simple-root signs defines
a maximal proper rational parabolic. -/
theorem omitted_node_limit_maximal (A : AdaptedPair G n) (node : Fin n)
    (hG : IsReductive G) (c : Cocharacter A.S.group)
    (L : LimitDecomposition (c ≫ A.S.inclusion))
    (hc : ∀ i, let p := pairing A.pair.T.group (A.numbering i).val.val (A.geometricCocharacter c)
      if i = node then 0 < p else p = 0) :
    IsParabolic G L.parabolic ∧ ¬ IsIso L.parabolic.inclusion ∧
      ∀ Q : ClosedSubgroup G.val, IsParabolic G Q → IsSubgroupOf L.parabolic Q →
        IsIso Q.inclusion ∨ IsSubgroupOf Q L.parabolic := by
  classical
  obtain ⟨hp, hSL⟩ := limitParabolicThroughSplitTorus G hG A.S A.maximalSplit.1 c L
  let val (d : Cocharacter A.S.group) (i : Fin n) :=
    pairing A.pair.T.group (A.numbering i).val.val (A.geometricCocharacter d)
  have hpos : 0 < val c node := by simpa [val] using hc node
  have hz (i : Fin n) (hi : i ≠ node) : val c i = 0 := by simpa [val, hi] using hc i
  have hnonneg (i : Fin n) : 0 ≤ val c i := by
    by_cases hi : i = node
    · exact hi ▸ hpos.le
    · exact (hz i hi).symm ▸ le_rfl
  refine ⟨hp, ?_, ?_⟩
  · intro hIso
    obtain ⟨β, hβ⟩ := negative_root_pairing A (A.numbering node).val
    have h := absolute_nonnegative_of_parabolic_iso A c L hIso β
    rw [hβ] at h
    exact (not_le_of_gt hpos) (neg_nonneg.mp h)
  · intro Q hQ hLQ
    obtain ⟨d, D, hQD⟩ := parabolicThroughSplitTorus G A.S A.maximalSplit Q hQ
      (subgroupOf_trans hSL hLQ)
    have hs := (limit_parabolics_le_iff A c d L D).mp (subgroupOf_trans hLQ hQD.1)
    have hd (i : Fin n) : 0 ≤ val d i := hs (A.numbering i).val (hnonneg i)
    have hdz (i : Fin n) (hi : i ≠ node) : val d i = 0 := by
      obtain ⟨β, hβ⟩ := negative_root_pairing A (A.numbering i).val
      apply le_antisymm _ (hd i)
      have ha := hs β (by rw [hβ]; exact neg_nonneg.mpr (hz i hi).le)
      rw [hβ] at ha
      exact neg_nonneg.mp ha
    have hm (α : Specs.AbstractPairing.Root A.pair.T) :
        ∃ m : ℤ, (∀ z : Cocharacter A.S.group, (∀ i ≠ node, val z i = 0) →
          pairing A.pair.T.group α.val (A.geometricCocharacter z) = m * val z node) := by
      obtain ⟨v, _, hv⟩ := root_pairing_expansion A α
      refine ⟨v node, fun z hz' => (hv _).trans ?_⟩
      exact Finset.sum_eq_single node
        (fun j _ hj => by rw [show pairing _ _ _ = val z j from rfl, hz' j hj, mul_zero])
        (fun h => (h (Finset.mem_univ node)).elim)
    rcases (hd node).eq_or_lt with he | he
    · obtain ⟨j, hj⟩ := hQD.2
      haveI := parabolic_iso_of_absolute_nonnegative A d D (fun α => by
        obtain ⟨m, hm'⟩ := hm α
        rw [hm' d hdz, ← he, mul_zero])
      exact Or.inl (inclusion_iso_of_section Q (inv D.parabolic.inclusion ≫ j)
        (by rw [Category.assoc, hj, IsIso.inv_hom_id]))
    · refine Or.inr (subgroupOf_trans hQD.1 ((limit_parabolics_le_iff A d c D L).mpr ?_))
      intro α ha
      obtain ⟨m, hm'⟩ := hm α
      rw [hm' d hdz] at ha
      rw [hm' c hz]
      exact mul_nonneg (nonneg_of_mul_nonneg_left ha he) hpos.le


set_option maxHeartbeats 800000 in
/-- A white simple root in the specified index restricts to an actual
relative root of the given rational split torus. -/
private theorem white_simple_restricts_to_root (A : AdaptedPair G n) {white : Fin r → Fin n}
    (encode : Multiplicative (Fin r → ℤ) →* Character A.S.group)
    (hinj : Function.Injective encode)
    (hres : ∀ i : Fin n, A.splitInAbsolute ≫ (A.numbering i).val.val =
      (groupBaseChange F (SeparableClosure F)).map
        (encode (Multiplicative.ofAdd (fun j => (Pi.single i 1 : Fin n → ℤ) (white j)))) ≫
        A.multiplicative.inv)
    (j : Fin r) :
    encode (Multiplicative.ofAdd (fun l => (Pi.single (white j) 1 : Fin n → ℤ) (white l))) ∈
      relativeRoots A.S := by
  let K := SeparableClosure F
  let ext := groupBaseChange F K
  let T' := extendSubgroup K A.T
  have hsplit : Specs.GeometricRadicals.IsSplitTorus T'.group := by
    obtain ⟨p, ⟨e⟩⟩ := A.pair.split
    exact ⟨p, ⟨A.torus ≪≫ e⟩⟩
  obtain ⟨e, he, hInj, hRoots⟩ := relativeRootsByRestriction G A.S A.T A.intoTorus
    A.intoTorus_eq A.maximalSplit.1 T'.isClosedImmersion hsplit
  have he' : e = A.multiplicative := by
    apply Iso.ext
    apply cocharacter_ext_units
    intro R t
    exact (baseChangePointsEquiv K _ R).injective
      ((he R t).trans (A.multiplicative_eq R t).symm)
  subst e
  let a := (A.numbering (white j)).val.val
  let ψ := encode (Multiplicative.ofAdd (fun l =>
    (Pi.single (white j) 1 : Fin n → ℤ) (white l)))
  have hTorus : T'.inclusion ≫ A.ambient.inv = A.torus.hom ≫ A.pair.T.inclusion := by
    change ext.map A.T.inclusion ≫ A.ambient.inv = _
    rw [← A.torus_eq, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ha : (A.torus.hom ≫ a) ∈ absoluteRoots T' :=
    (rootsOfIso (T := T') (S := A.pair.T) A.ambient.symm A.torus hTorus a).mpr
      (A.numbering (white j)).val.property
  have h_one : ext.map (1 : Character A.S.group) ≫ A.multiplicative.inv = 1 := by
    apply characterValuesDetectCharacters (splitTorus_baseChange A.maximalSplit.1)
    intro R t
    rw [characterValue_extend 1 A.multiplicative A.multiplicative_eq,
      characterValue_one, characterValue_one]
  have hψ : ψ ≠ 1 := by
    intro h
    have heq := hinj (h.trans encode.map_one.symm)
    have hj := congrArg (fun w : Multiplicative (Fin r → ℤ) => w.toAdd j) heq
    change (Pi.single (white j) 1 : Fin n → ℤ) (white j) = 0 at hj
    simp at hj
  have himg : ext.map ψ ≫ A.multiplicative.inv ∈
        ((fun b : Character T'.group => ext.map A.intoTorus ≫ b) '' absoluteRoots T') \ {1} := by
    refine ⟨⟨A.torus.hom ≫ a, ha, ?_⟩, ?_⟩
    · change ext.map A.intoTorus ≫ (A.torus.hom ≫ a) = ext.map ψ ≫ A.multiplicative.inv
      rw [← Category.assoc]
      exact hres (white j)
    · intro h
      exact hψ (hInj ((Set.mem_singleton_iff.mp h).trans h_one.symm))
  have habs := (Set.ext_iff.mp hRoots (ext.map ψ ≫ A.multiplicative.inv)).mpr himg
  obtain ⟨b, hb, heq⟩ := habs
  change ψ ∈ relativeRoots A.S
  rwa [← hInj heq]

/-- The limit of the omitted-node cocharacter contains the specified
minimal rational parabolic through the adapted Borel. -/
theorem minimal_parabolic_le_omitted_node_limit (A : AdaptedPair G n)
    (hG : IsReductive G) {white : Fin r → Fin n}
    (hw : HasWhiteRestrictions A white) (j₀ : Fin r)
    (c : Cocharacter A.S.group) (L : LimitDecomposition (c ≫ A.S.inclusion))
    (hc : ∀ i, let p := pairing A.pair.T.group (A.numbering i).val.val (A.geometricCocharacter c)
      if i = white j₀ then 0 < p else p = 0) :
    IsSubgroupOf A.J L.parabolic := by
  classical
  obtain ⟨d, D, hJD⟩ := parabolicThroughSplitTorus G A.S A.maximalSplit A.J A.minimalParabolic.1
    (subgroupOf_trans ⟨A.intoTorus, A.intoTorus_eq⟩ A.torusInParabolic)
  have hmin : IsMinimalParabolic G D.parabolic := by
    refine ⟨(limitParabolicThroughSplitTorus G hG A.S A.maximalSplit.1 d D).1, ?_⟩
    intro Q hQ hQD
    exact subgroupOf_trans hJD.2 (A.minimalParabolic.2 Q hQ (subgroupOf_trans hQD hJD.2))
  have hregular := (minimalLimitParabolic G hG A.S A.maximalSplit d D).mp hmin
  obtain ⟨D', hD, _⟩ := exists_absolute_limit A d D
  have hB : IsSubgroupOf A.pair.B D'.parabolic := by
    apply (pushSubgroup_le_iff A.ambient _ _).mp
    have hBJ : IsSubgroupOf (pushSubgroup A.ambient A.pair.B)
        (extendSubgroup (SeparableClosure F) A.J) := ⟨A.borel, A.borel_eq⟩
    exact subgroupOf_trans hBJ (subgroupOf_trans (extend_subgroupOf hJD.1) hD.2)
  let val (x : Cocharacter A.S.group) (i : Fin n) :=
    pairing A.pair.T.group (A.numbering i).val.val (A.geometricCocharacter x)
  have hdn (i : Fin n) : 0 ≤ val d i := by
    have hs := ((A.datum.simple_iff _).mp (A.numbering i).property).1
    apply (limitParabolic_root_iff _ _ (A.geometricCocharacter d) D' (A.numbering i).val).mp
    exact Set.Subset.trans hs (lieImage_mono hB)
  obtain ⟨encode, hinj, hres⟩ := hw
  let ψ := encode (Multiplicative.ofAdd (fun l =>
    (Pi.single (white j₀) 1 : Fin n → ℤ) (white l)))
  have hψ : ψ ∈ relativeRoots A.S :=
    white_simple_restricts_to_root A encode hinj hres j₀
  have hdp : 0 < val d (white j₀) := by
    have hn := hregular ⟨ψ, hψ⟩
    have he := pairing_restricted_simple A white encode hres d (white j₀)
    exact lt_of_le_of_ne (hdn (white j₀)) (fun e => hn (he.symm.trans e.symm))
  have hcp : 0 < val c (white j₀) := by simpa [val] using hc (white j₀)
  have hcz (i : Fin n) (hi : i ≠ white j₀) : val c i = 0 := by
    simpa [val, hi] using hc i
  refine subgroupOf_trans hJD.1 ((limit_parabolics_le_iff A d c D L).mpr ?_)
  intro α hα
  obtain ⟨v, hs, hv⟩ := root_pairing_expansion A α
  rw [hv] at hα ⊢
  change 0 ≤ ∑ i, v i * val d i at hα
  change 0 ≤ ∑ i, v i * val c i
  rw [Finset.sum_eq_single (white j₀)
    (fun j _ hj => by rw [hcz j hj, mul_zero]) (by simp)]
  apply mul_nonneg _ hcp.le
  rcases hs with hnonneg | hnonpos
  · exact hnonneg _
  · have hs : ∑ i, v i * val d i = 0 :=
      le_antisymm (Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonpos_of_nonneg (hnonpos i) (hdn i))) hα
    have h0 := (Finset.sum_eq_zero_iff_of_nonpos
      (fun i _ => mul_nonpos_of_nonpos_of_nonneg (hnonpos i) (hdn i))).mp hs
      (white j₀) (Finset.mem_univ _)
    exact le_of_eq ((mul_eq_zero.mp h0).resolve_right hdp.ne').symm



/-- Choose the actual limit decomposition of the cocharacter dual to the
omitted white node, together with the rational maximality and incidence. -/
theorem exists_omitted_node_limit (A : AdaptedPair G n)
    (hG : IsReductive G) {white : Fin r → Fin n} (hwhite : Function.Injective white)
    (hw : HasWhiteRestrictions A white) (j₀ : Fin r) :
    ∃ (c : Cocharacter A.S.group) (L : LimitDecomposition (c ≫ A.S.inclusion)),
      (∀ i, let p := pairing A.pair.T.group (A.numbering i).val.val (A.geometricCocharacter c)
        if i = white j₀ then 0 < p else p = 0) ∧
      IsParabolic G L.parabolic ∧ ¬ IsIso L.parabolic.inclusion ∧
      IsSubgroupOf A.J L.parabolic ∧
      (∀ Q : ClosedSubgroup G.val, IsParabolic G Q → IsSubgroupOf L.parabolic Q →
        IsIso Q.inclusion ∨ IsSubgroupOf Q L.parabolic) := by
  obtain ⟨c, hc⟩ := exists_omitted_node_cocharacter A hwhite hw j₀
  obtain ⟨L⟩ := existsLimitDecomposition G (c ≫ A.S.inclusion)
  obtain ⟨hp, hproper, hmax⟩ := omitted_node_limit_maximal A _ hG c L hc
  exact ⟨c, L, hc, hp, hproper, minimal_parabolic_le_omitted_node_limit A hG hw j₀ c L hc, hmax⟩

/-- Construct the reductive centralizer, its derived quotient torus, and
the lift of a cocharacter of the specified split torus into the centralizer. -/
theorem derived_quotient_of_omitted_node_limit (A : AdaptedPair G n)
    (hG : IsReductive G) (c δ : Cocharacter A.S.group)
    (L : LimitDecomposition (c ≫ A.S.inclusion)) :
    ∃ (H : ClosedSubgroup L.centralizer.group) (Q : AffineAlgebraicGroup F)
      (q : L.centralizer.group ⟶ Q.val) (s : Cocharacter L.centralizer.group),
      let M := closedSubgroupAlgebraicGroup L.centralizer
      IsReductive M ∧ IsDerivedSubgroup H ∧
        IsSemisimple (closedSubgroupAlgebraicGroup (G := M) H) ∧
        IsTorus Q.val ∧ IsSchemeKernel q H ∧ RepresentsQuotient H q ∧
        s ≫ L.centralizer.inclusion = δ ≫ A.S.inclusion := by
  have hT := geometricMaximal_of_rationalMaximal G hG.1
    (connected_of_geometricallyConnected hG.2.1) A.T A.maximalTorus
  have he : c ≫ A.S.inclusion = (c ≫ A.intoTorus) ≫ A.T.inclusion := by
    rw [Category.assoc, A.intoTorus_eq]
  have hR := cocharacterCentralizerReductive G hG A.T A.maximalTorus.1 hT
    (c ≫ A.intoTorus) (he ▸ L)
  rw [limitCentralizer_eq_of_cast he L] at hR
  let M := closedSubgroupAlgebraicGroup L.centralizer
  obtain ⟨H, hH⟩ := derivedSubgroupExists M
  obtain ⟨Q, q, hk, hq, hQ⟩ := derivedTorusQuotient M hR H hH
  obtain ⟨j, hj⟩ := torus_subgroupOf_centralizer A.maximalSplit.1 c L
  exact ⟨H, Q, q, δ ≫ j, hR, hH, derivedSemisimple M hR H hH, hQ, hk, hq,
    (Category.assoc _ _ _).trans (congrArg (δ ≫ ·) hj)⟩

/-- Once the given coroot is an isomorphism onto the quotient after
extension, use its inverse to identify the rational quotient with Gₘ. -/
theorem normalize_derived_torus_quotient {M Q : GroupScheme F}
    (H : ClosedSubgroup M) (q : M ⟶ Q) (s : Cocharacter M) (hk : IsSchemeKernel q H)
    (hq : RepresentsQuotient H q)
    (hs : IsIso ((groupBaseChange F K).map (s ≫ q))) :
    ∃ p : Character M, IsSchemeKernel p H ∧ RepresentsQuotient H p ∧
      s ≫ p = 𝟙 _ := by
  letI := isIso_of_scalarExtension K (s ≫ q) hs
  let e := (asIso (s ≫ q)).symm
  obtain ⟨j, hj⟩ := hq
  refine ⟨q ≫ e.hom, (schemeKernel_postcompose_iso q e H).mpr hk, ?_, ?_⟩
  · let Y := (Grp.forget (SchemeOver F)) ⋙ (fppfOver F).uliftYoneda
    refine ⟨j ≪≫ Y.mapIso e, ?_⟩
    change rightQuotientProjection H ≫ (j.hom ≫ Y.map e.hom) = Y.map (q ≫ e.hom)
    rw [← Category.assoc, Y.map_comp]
    exact congrArg (· ≫ Y.map e.hom) hj
  · rw [← Category.assoc]
    exact (asIso (s ≫ q)).hom_inv_id

/-- Form the local quaternion witness for a central division factor of
degree two using the cyclic presentation over the unramified subfield. -/
theorem local_quaternion_of_degree_two
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {B : Type u} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (hd : _root_.Specs.RM03.CSA.degree F B = 2) : IsLocalQuaternion (F := F) B := by
  obtain ⟨w, hw, _⟩ := LocalDivisionAlgebras.valuation_exists hB
  obtain ⟨r⟩ := LocalDivisionAlgebras.residue_field hB w hw
  exact ⟨hB, w, hd, hw, r, (LocalDivisionAlgebras.cyclic_structure hB w hw r).2.2⟩


/-- The remaining E₆ chain in Bourbaki order, with indices starting at zero. -/
def e6LeviChain : Fin 5 → Fin 6 := ![0, 2, 3, 4, 5]

/-- The A₅ chain in E₇ after deleting the third Bourbaki node. -/
def e7LeviChain : Fin 5 → Fin 7 := ![1, 3, 4, 5, 6]

theorem e6_levi_cartan :
    Function.Injective e6LeviChain ∧
    (∀ i : Fin 6, i ∈ Set.range e6LeviChain ↔ i ≠ 1) ∧
    (∀ i j, CartanMatrix.E 6 (e6LeviChain i) (e6LeviChain j) = CartanMatrix.A 5 i j) ∧
    (∀ i, e6LeviChain i ∈ Set.range (![1, 3] : Fin 2 → Fin 6) ↔ i = 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Function.Injective
    decide +kernel
  · change ∀ i : Fin 6, (∃ j : Fin 5, e6LeviChain j = i) ↔ i ≠ 1
    decide +kernel
  · decide +kernel
  · change ∀ i : Fin 5, (∃ j : Fin 2, (![1, 3] : Fin 2 → Fin 6) j = e6LeviChain i) ↔ i = 2
    decide +kernel

theorem e7_levi_cartan :
    Function.Injective e7LeviChain ∧
    (∀ i : Fin 7, i ∈ Set.range e7LeviChain ↔ i ≠ 0 ∧ i ≠ 2) ∧
    (∀ i j, CartanMatrix.E 7 (e7LeviChain i) (e7LeviChain j) = CartanMatrix.A 5 i j) ∧
    (∀ i, CartanMatrix.E 7 0 (e7LeviChain i) = 0 ∧ CartanMatrix.E 7 (e7LeviChain i) 0 = 0) ∧
    (∀ i, e7LeviChain i ∈ Set.range (![0, 2, 3, 5] : Fin 4 → Fin 7) ↔ i = 1 ∨ i = 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Function.Injective
    decide +kernel
  · change ∀ i : Fin 7, (∃ j : Fin 5, e7LeviChain j = i) ↔ i ≠ 0 ∧ i ≠ 2
    decide +kernel
  · decide +kernel
  · decide +kernel
  · change ∀ i : Fin 5,
      (∃ j : Fin 4, (![0, 2, 3, 5] : Fin 4 → Fin 7) j = e7LeviChain i) ↔ i = 1 ∨ i = 3
    decide +kernel

private def e6LeviVertices : Fin 5 ≃ {i : Fin 6 // i ≠ 1} := by
  obtain ⟨hinj, hrange, _, _⟩ := e6_levi_cartan
  let f : Fin 5 → {i : Fin 6 // i ≠ 1} := fun i =>
    ⟨e6LeviChain i, (hrange _).mp ⟨i, rfl⟩⟩
  refine Equiv.ofBijective f ⟨fun i j h => hinj (congrArg Subtype.val h), ?_⟩
  intro j
  obtain ⟨i, hi⟩ := (hrange j.val).mpr j.property
  exact ⟨i, Subtype.ext hi⟩

private def e7LeviVertex : Fin 1 ⊕ Fin 5 → {i : Fin 7 // i ≠ 2}
  | .inl _ => ⟨0, by decide⟩
  | .inr i => ⟨e7LeviChain i, ((e7_levi_cartan.2.1 _).mp ⟨i, rfl⟩).2⟩

private def e7LeviVertices : (Fin 1 ⊕ Fin 5) ≃ {i : Fin 7 // i ≠ 2} :=
  Equiv.ofBijective e7LeviVertex (by
    constructor
    · unfold Function.Injective
      decide +kernel
    · unfold Function.Surjective
      decide +kernel)

private theorem e7LeviVertex_cartan :
    ∀ i j : Fin 1 ⊕ Fin 5, CartanMatrix.E 7 (e7LeviVertex i).val (e7LeviVertex j).val =
      Specs.SplitLeviMatrixComparison.productCartan i j := by
  decide +kernel

private theorem semisimple_of_group_iso {A B : AffineAlgebraicGroup F}
    (e : A.val ≅ B.val) (hA : IsSemisimple A) : IsSemisimple B := by
  let θ := (Grp.forget (SchemeOver F) ⋙ Over.forget _).mapIso e
  have hθ : θ.inv ≫ A.val.X.hom = B.val.X.hom := Over.w e.inv.hom.hom
  have hs : Smooth B.val.X.hom := by
    rw [← hθ]
    letI := hA.1
    infer_instance
  have hc : GeometricallyConnected B.val.X.hom := by
    rw [GeometricallyConnected.eq_geometrically, ← hθ]
    exact (geometrically (ConnectedSpace ·)).cancel_left_of_respectsIso θ.inv
      A.val.X.hom |>.mpr hA.2.1.geometrically_connectedSpace
  refine ⟨hs, hc, ?_⟩
  let U := geometricSolvableRadical B
  let g := (groupBaseChange F (AlgebraicClosure F)).mapIso e.symm
  let V := pushSubgroup g U
  have hU := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest B
  have hV : IsSmoothConnectedNormal (G := GeometricGroup A) V :=
    ⟨hU.1.1, hU.1.2.1, normal_postcompose_iso U.inclusion g hU.1.2.2⟩
  have hsolv : IsSolvable V.group := hU.2.1
  have h := (LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest A).2.2
    V hV hsolv
  obtain ⟨eV⟩ := trivialOfSubgroup h hA.2.2
  exact ⟨eV⟩

/-- The full geometric coroot lattice can be tested on the actual marked
pair over the separable closure. Base-change its split cover to the
algebraic closure of the ground field and apply simple connectedness there. -/
theorem adapted_absolute_coroot_lattice (A : AdaptedPair G n)
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G) :
    IsSemisimple A.pair.G ∧ corootLattice A.datum = ⊤ := by
  let K := SeparableClosure F
  let L := AlgebraicClosure F
  have hA : IsSemisimple A.pair.G := semisimple_of_group_iso A.ambient.symm
    ((Reductive.RadicalBaseChange.semisimpleFieldExtension G hG.1 hG.2.1).mpr hG)
  refine ⟨hA, ?_⟩
  letI := A.datum.comm
  obtain ⟨P, D, f, τ, hp, _, hf, hτ, _, E, hE⟩ :=
    Classification.SimplyConnectedLattice.splitCover A.pair.G hA A.pair.T A.pair.split
      A.pair.maximal A.datum.datum
  let j : (groupBaseChange K L).obj A.pair.G.val ≅ (GeometricGroup G).val :=
    (groupBaseChange K L).mapIso A.ambient ≪≫ (groupBaseChangeTowerIso (k := F) (K := K)).app G.val
  have hPf : IsSemisimple (baseChangedAlgebraicGroup L P.G) :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension P.G hp.1 hp.2.1).mpr hp
  haveI := hSC (baseChangedAlgebraicGroup L P.G) hPf
    ((groupBaseChange K L).map f ≫ j.hom)
      (centralIsogeny_postIso j (centralIsogeny_baseChange L P f hf))
  letI := isIso_of_scalarExtension L f (IsIso.of_isIso_comp_right _ j.hom)
  letI := torusIso_of_isIso P A.pair f τ hτ
  apply top_le_iff.mp
  intro y _
  have he := hE (y.toMul ≫ inv τ)
  change (E (Additive.ofMul (y.toMul ≫ inv τ))).val = _ at he
  have hy : ((y.toMul ≫ inv τ) ≫ τ) = y.toMul := by simp [Category.assoc]
  rw [hy] at he
  change Additive.ofMul y.toMul ∈ corootLattice A.datum
  rw [← he]
  exact (E (Additive.ofMul (y.toMul ≫ inv τ))).property

/-- The subset of the numbered simple roots left in the Levi. -/
def remainingSimpleRoots (A : AdaptedPair G n) (node : Fin n) :
    Set (Specs.AbstractPairing.Root A.pair.T) :=
  {α | α ∈ A.datum.toBased.base.support ∧ α ≠ (A.numbering node).val}

set_option maxHeartbeats 1200000 in
/-- Realize the remaining root subsystem in the base change of the
derived subgroup of the chosen rational limit centralizer. -/
theorem exists_split_derived_face (A : AdaptedPair G n) (node : Fin n)
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (c : Cocharacter A.S.group) (L : LimitDecomposition (c ≫ A.S.inclusion))
    (hc : ∀ i, let p := pairing A.pair.T.group (A.numbering i).val.val (A.geometricCocharacter c)
      if i = node then 0 < p else p = 0)
    (hL : IsReductive (closedSubgroupAlgebraicGroup L.centralizer))
    (H : ClosedSubgroup L.centralizer.group) (hH : IsDerivedSubgroup H) :
    ∃ (S : SplitFace A.datum (remainingSimpleRoots A node))
      (j : (groupBaseChange F (SeparableClosure F)).obj L.centralizer.group ≅ S.levi.group)
      (e : (groupBaseChange F (SeparableClosure F)).obj H.group ≅ S.group.val),
      j.hom ≫ S.levi.inclusion ≫ A.ambient.hom =
        (groupBaseChange F (SeparableClosure F)).map L.centralizer.inclusion ∧
      e.hom ≫ S.derived.inclusion = (groupBaseChange F (SeparableClosure F)).map H.inclusion ≫ j.hom ∧
      S.group = baseChangedAlgebraicGroup (SeparableClosure F)
        (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L.centralizer) H) ∧
      GeometricallySimplyConnected S.group ∧
      letI := A.datum.comm
      ∀ y : A.datum.toBased.Y,
        (∃ z : Cocharacter S.torus.group, z ≫ S.toAmbientTorus = y.toMul) ↔
          y ∈ Submodule.span ℤ (A.datum.datum.rootDatum.coroot '' remainingSimpleRoots A node) := by
  classical
  let K := SeparableClosure F
  let ext := groupBaseChange F K
  let M := closedSubgroupAlgebraicGroup L.centralizer
  letI := A.datum.comm
  let I := remainingSimpleRoots A node
  have hI : I ⊆ A.datum.base.support := fun _ h => h.1
  obtain ⟨D, _, hDZ⟩ := exists_absolute_limit A c L
  have hface : HasFace A.datum.base I (A.geometricCocharacter c) := by
    constructor
    · intro α hα
      let i := A.numbering.symm ⟨α, hI hα⟩
      have hi : A.numbering i = ⟨α, hI hα⟩ := A.numbering.apply_symm_apply _
      have hne : i ≠ node := by
        intro r
        apply hα.2
        exact (congrArg Subtype.val hi).symm.trans (congrArg (fun j => (A.numbering j).val) r)
      have h := hc i
      simp only [hne, ite_false, hi] at h
      exact h
    · intro α hα
      have he : α = (A.numbering node).val := by
        by_contra h
        exact hα.2 ⟨hα.1, h⟩
      simpa only [he, ite_true] using hc node
  have hD := splitLeviForFace A.pair A.datum I (A.geometricCocharacter c) D hface
  obtain ⟨j, hj⟩ := subgroupIso_of_same ⟨hDZ.2, hDZ.1⟩
  let j' : ext.obj L.centralizer.group ≅ D.centralizer.group := j
  have hjsq : j'.hom ≫ D.centralizer.inclusion ≫ A.ambient.hom =
      ext.map L.centralizer.inclusion := hj
  obtain ⟨hHK, hdk, _⟩ := Reductive.DerivedSubgroup.derivedSubgroupBaseChange K M H hH hL.1 hL.2.1
  let HK := baseChangedSubgroup K H hHK
  let HA := subgroupAlongIso j' HK
  have hHA : IsDerivedSubgroup HA := derivedSubgroupOfIso j' HK hdk
  obtain ⟨hSS, hLat⟩ := adapted_absolute_coroot_lattice A hG hSC
  have hAS := (Classification.SimplyConnectedLattice.latticeCriterion
    A.pair.G hSS A.pair.T A.pair.split A.pair.maximal A.datum.datum).mpr hLat
  have hRed : IsReductive (closedSubgroupAlgebraicGroup D.centralizer) := by
    obtain ⟨_, _, _, _, _, _, _, hred, _⟩ := hD
    exact hred
  obtain ⟨V, v, hv, hvClosed, hvTorus, hvMax, _⟩ := rationalDerivedLeviTorus
    A.pair.G A.pair.T (isTorus_of_split A.pair.split) A.pair.maximal
      (A.geometricCocharacter c) D hRed HA hHA
  have hspan : ∀ y : A.datum.toBased.Y,
      (∃ z : Cocharacter V.group, z ≫ v = y.toMul) ↔
        y ∈ Submodule.span ℤ (A.datum.datum.rootDatum.coroot '' I) := by
    intro y
    exact (cocharacterFactorsThroughIntersection _ _ _ _ hv y.toMul).trans
      (splitLeviCocharacterSpan A.pair A.datum hSS hAS I hI (A.geometricCocharacter c) D hD HA hHA y)
  obtain ⟨T, t, U, hU, hZ, _, _, hRed, ht, htMax, _, hRoots⟩ := hD
  let S : SplitFace A.datum I :=
    { simple := hI
      kernelTorus := U
      kernel := hU
      levi := D.centralizer
      centralizer := hZ
      reductive := hRed
      leviTorus := T
      torusIso := t
      torusInclusion := ht
      leviTorusMaximal := htMax
      leviRoots_eq := hRoots
      derived := HA
      isDerived := hHA
      torus := V
      toAmbientTorus := v
      intersection := hv
      torusSplit := splitOfClosedTorus (closedSubgroupAlgebraicGroup
        (G := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup D.centralizer) HA) V)
        hvTorus A.pair.split v hvClosed
      torusMaximal := hvMax }
  refine ⟨S, j', Iso.refl _, hjsq, ?_, rfl, splitDerivedSimplyConnected A.datum I S hspan, hspan⟩
  exact Category.id_comp _

/-- The derived subgroup of the rational centralizer is geometrically simply
connected, with the original rational inclusion retained by the split comparison. -/
theorem omitted_node_derived_simply_connected (A : AdaptedPair G n) (node : Fin n)
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (c : Cocharacter A.S.group) (L : LimitDecomposition (c ≫ A.S.inclusion))
    (hc : ∀ i, let p := pairing A.pair.T.group (A.numbering i).val.val (A.geometricCocharacter c)
      if i = node then 0 < p else p = 0)
    (hL : IsReductive (closedSubgroupAlgebraicGroup L.centralizer))
    (H : ClosedSubgroup L.centralizer.group) (hH : IsDerivedSubgroup H) :
    GeometricallySimplyConnected
      (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L.centralizer) H) := by
  obtain ⟨S, _, e, _, _, _, hS, _⟩ := exists_split_derived_face A node hG hSC c L hc hL H hH
  exact simplyConnected_of_compared_baseChange _ S.group e hS

/-- The omitted fundamental weight is an actual character of the absolute
torus. It kills the torus of the derived Levi and has value one on the
omitted simple coroot, in the integral pairing. -/
private theorem exists_omitted_node_character (A : AdaptedPair G n) (node : Fin n)
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (S : SplitFace A.datum (remainingSimpleRoots A node))
    (hspan : letI := A.datum.comm
      ∀ y : A.datum.toBased.Y,
        (∃ z : Cocharacter S.torus.group, z ≫ S.toAmbientTorus = y.toMul) ↔
          y ∈ Submodule.span ℤ (A.datum.datum.rootDatum.coroot '' remainingSimpleRoots A node)) :
    ∃ χ : Character A.pair.T.group,
      (A.datum.toBased.datum.coroot (A.numbering node)).toMul ≫ χ = 𝟙 _ ∧
      S.toAmbientTorus ≫ χ = 1 := by
  classical
  letI := A.datum.comm
  obtain ⟨hss, hLat⟩ := adapted_absolute_coroot_lattice A hG hSC
  have hSC' := (Classification.SimplyConnectedLattice.latticeCriterion A.pair.G hss
    A.pair.T A.pair.split A.pair.maximal A.datum.datum).mpr hLat
  obtain ⟨b, hb⟩ := attachedCorootBasis A.pair A.datum hss hSC'
  let j := A.numbering node
  let f : Additive (Cocharacter A.pair.T.group) →ₗ[ℤ] ℤ := b.coord j
  let χ : Character A.pair.T.group := (A.datum.datum.rootDatum.toLinearMap.toPerfPair.symm f).toMul
  have hχ (y : A.datum.toBased.Y) : pairing A.pair.T.group χ y.toMul = f y := by
    rw [← A.datum.datum.pairing_eq]
    exact DFunLike.congr_fun
      (A.datum.datum.rootDatum.toLinearMap.toPerfPair.apply_symm_apply f) y
  have hone : f (A.datum.toBased.datum.coroot j) = 1 := by
    change (b.repr (A.datum.datum.rootDatum.coroot j.val)) j = 1
    rw [← hb, Module.Basis.repr_self, Finsupp.single_eq_same]
  refine ⟨χ, ?_, ?_⟩
  · have h := ((characterPairingComposition A.pair.T.group χ
      (A.datum.toBased.datum.coroot j).toMul).1 1).mpr
        ((hχ _).trans hone)
    change (A.datum.toBased.datum.coroot j).toMul ≫ χ = powerMorphism 1 at h
    simpa only [powerMorphism_eq_zpow, zpow_one] using h
  have hz : Submodule.span ℤ
      (A.datum.datum.rootDatum.coroot '' remainingSimpleRoots A node) ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, hα, rfl⟩
    let i : A.datum.base.support := ⟨α, hα.1⟩
    have hij : i ≠ j := fun h => hα.2 (congrArg Subtype.val h)
    apply LinearMap.mem_ker.mpr
    change (b.repr (A.datum.datum.rootDatum.coroot i.val)) j = 0
    rw [← hb, Module.Basis.repr_self, Finsupp.single_eq_of_ne hij.symm]
  have hpair (z : Cocharacter S.torus.group) :
      pairing S.torus.group (S.toAmbientTorus ≫ χ) z = 0 := by
    have hcomp : pairing S.torus.group (S.toAmbientTorus ≫ χ) z =
        pairing A.pair.T.group χ (z ≫ S.toAmbientTorus) := by
      unfold pairing compositionPairing
      rw [Category.assoc]
    rw [hcomp]
    exact (hχ (Additive.ofMul (z ≫ S.toAmbientTorus))).trans
      (LinearMap.mem_ker.mp (hz ((hspan _).mp ⟨z, rfl⟩)))
  obtain ⟨comm, _, _, _, _, P, hP, hp⟩ :=
    perfectCharacterPairing S.torus.group S.torusSplit
  letI := comm
  letI := hP
  apply Additive.ofMul.injective
  apply P.toPerfPair.injective
  ext z
  change P (Additive.ofMul (S.toAmbientTorus ≫ χ)) (Additive.ofMul z.toMul) =
    P (Additive.ofMul 1) (Additive.ofMul z.toMul)
  rw [hp, hp, hpair, pairing_one _ S.torusSplit]

private theorem torus_hom_eq_on_basis {M B : GroupScheme K} (T : ClosedSubgroup M)
    (hT : IsAffine T.group.X.left) (hS : IsSplitTorus T.group)
    [IsCommMonObj T.group.X]
    {J : Type u} (b : Module.Basis J ℤ (Additive (Cocharacter T.group)))
    {f g : T.group ⟶ B}
    (h : ∀ j, (b j).toMul ≫ f = (b j).toMul ≫ g) : f = g := by
  apply (groupHomComparison K T.group B hT).1
  ext R x
  let E := (pointHom f R).eqLocus (pointHom g R)
  have he : E = ⊤ := cocharacter_lifts_generate T hS (fun j => (b j).toMul)
    (by simp) R E (fun j t => by
      change (unitPoint R t ≫ (b j).toMul.hom.hom) ≫ f.hom.hom =
        (unitPoint R t ≫ (b j).toMul.hom.hom) ≫ g.hom.hom
      simp only [Category.assoc, ← Grp.comp_hom_hom, h j])
  exact show x ∈ E by simp [he]

/-- The central torus lies in the maximal torus. The faithfully flat central
product with the derived group then makes the restriction of the quotient
map to the maximal torus surjective. -/
private theorem maximal_torus_surjects_onto_derived_quotient
    (M : AffineAlgebraicGroup K) (hM : IsReductive M)
    (T H : ClosedSubgroup M.val) (hT : IsTorus T.group) (hmax : IsGeometricallyMaximal T)
    (hH : IsDerivedSubgroup H) {Q : GroupScheme K} (q : M.val ⟶ Q)
    (hk : IsSchemeKernel q H) (hq : Surjective q.hom.hom.left) :
    Surjective (T.inclusion ≫ q).hom.hom.left := by
  obtain ⟨Z, hZ, Z₀, hZ₀, _⟩ := Reductive.CentralDerived.centralTorusExists M hM
  let p := Z₀.inclusion ≫ Z.inclusion
  have hp := centralInclusion hZ Z₀
  have hc : Centralizes T.inclusion p.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro U t z
    have hcomm := (centralizes_iff _ _).mp hp U t (z ≫ T.inclusion.hom.hom)
    simpa only [Grp.id_hom_hom, Category.comp_id, p] using hcomm
  obtain ⟨i, hi⟩ := (Reductive.TorusCentralizer.maximalTorusCentralizer M hM T hT hmax _ _).mp hc
  obtain ⟨a, ha⟩ := factor_group_through_subgroup T p i hi
  obtain ⟨m, hm⟩ := mulMap p H.inclusion hp
  have hms := (Reductive.CentralDerived.centralProductFaithfullyFlat M hM
    Z hZ Z₀ hZ₀ H hH m hm).2
  have hHq := (schemeKernel_sections hk H.inclusion.hom.hom).mp
    ⟨𝟙 _, by
      change (𝟙 _) ≫ H.inclusion.hom.hom = H.inclusion.hom.hom
      exact Category.id_comp _⟩
  have he : m ≫ q = firstProjection Z₀.group H.group ≫ a ≫ T.inclusion ≫ q := by
    apply Grp.hom_ext
    have hzero : (snd Z₀.group H.group ≫ H.inclusion).hom.hom ≫ q.hom.hom = 1 := by
      simp only [Grp.comp_hom_hom, Category.assoc, hHq, MonObj.comp_one]
    calc
      _ = (fst Z₀.group H.group ≫ p).hom.hom ≫ q.hom.hom := by
        rw [Grp.comp_hom_hom, hm, postMul, hzero, mul_one]
      _ = _ := by rw [← ha]; simp only [Grp.comp_hom_hom, Category.assoc, firstProjection]
  letI := hms
  letI := hq
  have hsurj : Surjective (m ≫ q).hom.hom.left := by
    change Surjective (m.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  rw [he] at hsurj
  exact ⟨Function.Surjective.of_comp hsurj.1⟩

private theorem coroot_section_mono
    (A : AdaptedPair G n) (node : Fin n)
    (S : SplitFace A.datum (remainingSimpleRoots A node))
    (u : Cocharacter A.pair.T.group) (χ : Character A.pair.T.group)
    (hu : u ≫ χ = 𝟙 _) (hχ : S.toAmbientTorus ≫ χ = 1)
    {Q : GroupScheme (SeparableClosure F)} (q : S.levi.group ⟶ Q)
    (hk : IsSchemeKernel q S.derived) :
    Mono (u ≫ S.torusIso.hom ≫ S.leviTorus.inclusion ≫ q).hom.hom.left := by
  let K := SeparableClosure F
  let d := u ≫ S.torusIso.hom ≫ S.leviTorus.inclusion
  have hdu : d ≫ S.levi.inclusion = u ≫ A.pair.T.inclusion := by
    simp only [d, Category.assoc, S.torusInclusion]
  let f := (d ≫ q).hom.hom
  have hk₁ {X : SchemeOver K} (x : X ⟶ (specGroup (groupAlgebra K IntegerCharacters)).X)
      (hx : x ≫ f = 1) : x = 1 := by
    have h : (x ≫ d.hom.hom) ≫ q.hom.hom = 1 := by
      rwa [Category.assoc, ← Grp.comp_hom_hom]
    obtain ⟨y, hy⟩ := (schemeKernel_sections hk (x ≫ d.hom.hom)).mpr h
    change y ≫ S.derived.inclusion.hom.hom = x ≫ d.hom.hom at hy
    have he : (x ≫ u.hom.hom) ≫ A.pair.T.inclusion.hom.hom =
        y ≫ (S.derived.inclusion ≫ S.levi.inclusion).hom.hom := by
      calc
        _ = x ≫ (u ≫ A.pair.T.inclusion).hom.hom := Category.assoc _ _ _
        _ = x ≫ (d ≫ S.levi.inclusion).hom.hom :=
          congrArg (fun j => x ≫ j.hom.hom) hdu.symm
        _ = _ := by
          rw [Grp.comp_hom_hom, ← Category.assoc, ← hy, Category.assoc, ← Grp.comp_hom_hom]
    let pb := S.intersection.map (Grp.forget (SchemeOver K))
    let z := pb.lift (x ≫ u.hom.hom) y he
    have hz : z ≫ S.toAmbientTorus.hom.hom = x ≫ u.hom.hom := pb.lift_fst _ _ _
    calc
      x = x ≫ (u ≫ χ).hom.hom := by rw [hu]; exact (Category.comp_id _).symm
      _ = z ≫ (S.toAmbientTorus ≫ χ).hom.hom := by
        simp only [Grp.comp_hom_hom, ← Category.assoc, hz]
      _ = 1 := by simp [hχ, MonObj.comp_one]
  letI : Mono f := ⟨fun {X} x y h => by
    have he : (x * y⁻¹) ≫ f = 1 := by
      change IsMonHom.monoidHom f X (x * y⁻¹) = 1
      change IsMonHom.monoidHom f X x = IsMonHom.monoidHom f X y at h
      rw [map_mul, map_inv, h, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hk₁ _ he)⟩
  change Mono f.left
  infer_instance

set_option maxHeartbeats 1200000 in
private theorem split_face_coroot_quotient_iso (A : AdaptedPair G n) (node : Fin n)
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (S : SplitFace A.datum (remainingSimpleRoots A node))
    (hspan : letI := A.datum.comm
      ∀ y : A.datum.toBased.Y,
        (∃ z : Cocharacter S.torus.group, z ≫ S.toAmbientTorus = y.toMul) ↔
          y ∈ Submodule.span ℤ (A.datum.datum.rootDatum.coroot '' remainingSimpleRoots A node))
    (Q : AffineAlgebraicGroup (SeparableClosure F)) (q : S.levi.group ⟶ Q.val)
    (hQ : Smooth Q.val.X.hom) (hk : IsSchemeKernel q S.derived) (hq : Surjective q.hom.hom.left) :
    IsIso ((A.datum.toBased.datum.coroot (A.numbering node)).toMul ≫
      S.torusIso.hom ≫ S.leviTorus.inclusion ≫ q) := by
  classical
  let K := SeparableClosure F
  letI := A.datum.comm
  let j := A.numbering node
  let u := (A.datum.toBased.datum.coroot j).toMul
  let τ := S.torusIso.hom ≫ S.leviTorus.inclusion
  let p := τ ≫ q
  let d := u ≫ p
  let M := closedSubgroupAlgebraicGroup S.levi
  obtain ⟨hss, hLat⟩ := adapted_absolute_coroot_lattice A hG hSC
  have hSC' := (Classification.SimplyConnectedLattice.latticeCriterion A.pair.G hss
    A.pair.T A.pair.split A.pair.maximal A.datum.datum).mpr hLat
  obtain ⟨b, hb⟩ := attachedCorootBasis A.pair A.datum hss hSC'
  obtain ⟨χ, hχu, hχS⟩ := exists_omitted_node_character A node hG hSC S hspan
  have hτ : τ ≫ S.levi.inclusion = A.pair.T.inclusion := by
    simpa only [τ, Category.assoc] using S.torusInclusion
  letI : Mono S.levi.inclusion := closedSubgroup_mono S.levi
  have he : p = χ ≫ d := by
    apply torus_hom_eq_on_basis A.pair.T
      (closedSubgroupAlgebraicGroup A.pair.T).property.1 A.pair.split b
    intro i
    by_cases hi : i = j
    · subst i
      rw [hb]
      change d = u ≫ χ ≫ d
      rw [← Category.assoc, hχu, Category.id_comp]
    · have hroot : i.val ∈ remainingSimpleRoots A node :=
        ⟨i.property, fun h => hi (Subtype.ext h)⟩
      obtain ⟨z, hz⟩ := (hspan (b i)).mpr (hb i ▸ Submodule.subset_span ⟨i.val, hroot, rfl⟩)
      have hz' : z ≫ S.toAmbientTorus = (b i).toMul := hz
      have hzero : (b i).toMul ≫ χ = 1 := by
        rw [← hz', Category.assoc, hχS]
        apply Grp.hom_ext
        exact MonObj.comp_one _
      have hd : (b i).toMul ≫ τ = z ≫ S.torus.inclusion ≫ S.derived.inclusion := by
        apply (cancel_mono S.levi.inclusion).1
        calc
          _ = (z ≫ S.toAmbientTorus) ≫ A.pair.T.inclusion := by
            simp only [Category.assoc, hτ, hz']
          _ = (z ≫ S.torus.inclusion ≫ S.derived.inclusion) ≫ S.levi.inclusion := by
            rw [Category.assoc, S.intersection.w]
            simp only [Category.assoc]
      have hHq := (schemeKernel_sections hk S.derived.inclusion.hom.hom).mp
        ⟨𝟙 _, by
          change (𝟙 _) ≫ S.derived.inclusion.hom.hom = S.derived.inclusion.hom.hom
          exact Category.id_comp _⟩
      have hq0 : (S.derived.inclusion ≫ q).hom.hom = 1 := hHq
      apply Grp.hom_ext
      have eq₁ : (b i).toMul ≫ p = (z ≫ S.torus.inclusion) ≫ (S.derived.inclusion ≫ q) := by
        change (b i).toMul ≫ τ ≫ q = (z ≫ S.torus.inclusion) ≫ (S.derived.inclusion ≫ q)
        rw [← Category.assoc, hd]
        simp only [Category.assoc]
      have eq₂ : (b i).toMul ≫ χ ≫ d = (1 : Character (specGroup (groupAlgebra K IntegerCharacters))) ≫ d := by
        rw [← Category.assoc, hzero]
      rw [eq₁, eq₂]
      simp only [Grp.comp_hom_hom, hq0, MonObj.comp_one]
      exact ((IsMonHom.monoidHom d.hom.hom _).map_one).symm
  have hT : IsSplitTorus S.leviTorus.group := by
    obtain ⟨r, ⟨e⟩⟩ := A.pair.split
    exact ⟨r, ⟨S.torusIso.symm ≪≫ e⟩⟩
  have hp : Surjective p.hom.hom.left := by
    haveI := maximal_torus_surjects_onto_derived_quotient M S.reductive S.leviTorus S.derived
      (isTorus_of_split hT) S.leviTorusMaximal S.isDerived q hk hq
    change Surjective (S.torusIso.hom.hom.hom.left ≫ (S.leviTorus.inclusion ≫ q).hom.hom.left)
    haveI : IsIso S.torusIso.hom.hom.hom.left :=
      ((Grp.forget (SchemeOver K)) ⋙ Over.forget _).map_isIso S.torusIso.hom
    infer_instance
  have hdSurj : Surjective d.hom.hom.left := by
    rw [he] at hp
    exact ⟨Function.Surjective.of_comp hp.1⟩
  haveI : Mono d.hom.hom.left := coroot_section_mono A node S u χ hχu hχS q hk
  haveI := hdSurj
  let D : AffineAlgebraicGroup K := diagonalGroup K IntegerCharacters
  haveI : Flat d.hom.hom.left := flatOfSurjectiveHom (A := D) (B := Q) d hQ hdSurj
  letI : IsAffine Q.val.X.left := Q.property.1
  letI : IsAffine (specGroup (groupAlgebra K IntegerCharacters)).X.left := D.property.1
  letI : IsAffineHom d.hom.hom.left := isAffineHom_of_isAffine _
  letI : IsIso d.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  exact isIso_of_schemeIso d

set_option maxHeartbeats 1000000 in
/-- The rational coroot induces the isomorphism with the actual torus quotient.
The omitted-coroot character controls its scheme kernel after scalar extension. -/
theorem omitted_node_quotient_section (A : AdaptedPair G n) (node : Fin n)
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (c δ : Cocharacter A.S.group)
    (hδ : A.geometricCocharacter δ = (A.datum.toBased.datum.coroot (A.numbering node)).toMul)
    (L : LimitDecomposition (c ≫ A.S.inclusion))
    (hc : ∀ i, let p := pairing A.pair.T.group (A.numbering i).val.val (A.geometricCocharacter c)
      if i = node then 0 < p else p = 0)
    (hL : IsReductive (closedSubgroupAlgebraicGroup L.centralizer))
    (H : ClosedSubgroup L.centralizer.group) (hH : IsDerivedSubgroup H)
    (Q : AffineAlgebraicGroup F) (q : L.centralizer.group ⟶ Q.val) (hQ : IsTorus Q.val)
    (hk : IsSchemeKernel q H) (hq : RepresentsQuotient H q) (s : Cocharacter L.centralizer.group)
    (hs : s ≫ L.centralizer.inclusion = δ ≫ A.S.inclusion) :
    ∃ p : Character L.centralizer.group, IsSchemeKernel p H ∧ RepresentsQuotient H p ∧
      s ≫ p = 𝟙 _ := by
  let K := SeparableClosure F
  let E := groupBaseChange F K
  let M := closedSubgroupAlgebraicGroup L.centralizer
  obtain ⟨S, j, e, hj, he, _, _, hspan⟩ := exists_split_derived_face A node hG hSC c L hc hL H hH
  let QK := baseChangedAlgebraicGroup K Q
  let qK : S.levi.group ⟶ QK.val := j.inv ≫ E.map q
  have hqK : j.hom ≫ qK = E.map q := by simp [qK]
  let U := Grp.forget (SchemeOver K)
  have hkK : IsSchemeKernel qK S.derived := by
    apply (baseChangeKernelSquare (K := K) q H.inclusion hk).of_iso
      (U.mapIso e) (U.mapIso j) (Iso.refl _) (Iso.refl _)
    · exact (U.map_comp _ _).symm.trans ((U.congr_map he).symm.trans (U.map_comp _ _))
    · exact toUnit_unique _ _
    · change U.map (E.map q) ≫ 𝟙 _ = U.map j.hom ≫ U.map qK
      rw [Category.comp_id, ← U.map_comp, hqK]
    · simp
  have hqF := (Classification.CentralIsogenies.representsQuotient_isFppfGroupQuotient
    (G := M) (Q := Q) hq).2.2.1
  letI : Surjective (E.map q).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) q.hom.hom).flip hqF
  haveI : IsIso j.inv.hom.hom.left :=
    (U ⋙ Over.forget _).map_isIso j.inv
  have hsurj : Surjective qK.hom.hom.left := by
    change Surjective (j.inv.hom.hom.left ≫ (E.map q).hom.hom.left)
    infer_instance
  have hSmooth : Smooth QK.val.X.hom := smooth_baseChangedGroup (torus_smooth Q hQ)
  let u : Cocharacter A.pair.T.group := (A.datum.toBased.datum.coroot (A.numbering node)).toMul
  have hiso := split_face_coroot_quotient_iso A node hG hSC S hspan QK qK hSmooth hkK hsurj
  letI : Mono S.levi.inclusion := closedSubgroup_mono S.levi
  have hcomp : A.multiplicative.hom ≫ E.map s ≫ j.hom =
      u ≫ S.torusIso.hom ≫ S.leviTorus.inclusion := by
    apply (cancel_mono (S.levi.inclusion ≫ A.ambient.hom)).mp
    have ht : S.torusIso.hom ≫ S.leviTorus.inclusion ≫ S.levi.inclusion ≫ A.ambient.hom =
        A.pair.T.inclusion ≫ A.ambient.hom := by
      simpa only [Category.assoc] using congrArg (· ≫ A.ambient.hom) S.torusInclusion
    simp only [Category.assoc, hj, ht]
    change A.multiplicative.hom ≫ E.map s ≫ E.map L.centralizer.inclusion = _
    rw [← E.map_comp, hs]
    exact ((absolute_cocharacter_comparison A δ).symm.trans (by rw [hδ])).trans
      (Category.assoc _ _ _)
  have hqComp : A.multiplicative.hom ≫ E.map (s ≫ q) =
      u ≫ S.torusIso.hom ≫ S.leviTorus.inclusion ≫ qK := by
    calc
      _ = (A.multiplicative.hom ≫ E.map s ≫ j.hom) ≫ qK := by
        simp only [Category.assoc, hqK, E.map_comp]
      _ = _ := by rw [hcomp]; simp only [Category.assoc]
  haveI : IsIso (A.multiplicative.hom ≫ E.map (s ≫ q)) := hqComp.symm ▸ hiso
  exact normalize_derived_torus_quotient H q s hk hq
    (IsIso.of_isIso_comp_left A.multiplicative.hom (E.map (s ≫ q)))

set_option maxHeartbeats 1200000 in
/-- Read the based root datum of the split derived Levi on the Borel
obtained by intersecting with the marked ambient Borel. -/
theorem split_derived_face_cartan (A : AdaptedPair G n) (node : Fin n)
    (S : SplitFace A.datum (remainingSimpleRoots A node))
    (hspan : letI := A.datum.comm
      ∀ y : A.datum.toBased.Y,
        (∃ z : Cocharacter S.torus.group, z ≫ S.toAmbientTorus = y.toMul) ↔
          y ∈ Submodule.span ℤ (A.datum.datum.rootDatum.coroot '' remainingSimpleRoots A node)) :
    ∃ (P : Pinning.SplitBorelPair (SeparableClosure F)) (_ : P.G = S.group)
      (D : Pinning.AttachedDatum P) (v : {i : Fin n // i ≠ node} ≃ D.toBased.base.support),
      ∀ i j, D.toBased.datum.pairing (v i) (v j) = CartanMatrix.E n i.val j.val := by
  classical
  letI := A.datum.comm
  let I := remainingSimpleRoots A node
  let Φ := leviRoots A.datum.datum I
  let B := subgroupPreimage S.inclusion A.pair.B
  obtain ⟨hB, htB⟩ := face_preimage_borel S hspan A.pair.B A.pair.borel A.pair.containsTorus
  let P : Pinning.SplitBorelPair (SeparableClosure F) :=
    { G := S.group, T := S.torus, B := B
      reductive := splitFace_reductive S, split := S.torusSplit, maximal := S.torusMaximal
      borel := hB, containsTorus := htB }
  obtain ⟨D⟩ := Classification.Pinning.datumExists P
  letI := D.comm
  obtain ⟨r, hr⟩ := faceRootEquivalence S
  have positive (a : Φ) :
      r a ∈ subgroupRoots P.T P.B ↔ a.val ∈ subgroupRoots A.pair.T A.pair.B := by
    have ha := (faceRootRestrictions A.datum I S a.val a.property).1
    rw [show r a = ⟨S.toAmbientTorus ≫ a.val.val, ha⟩ from Subtype.ext (hr a)]
    exact faceBorelRoots A.datum I S _ _ _ (subgroupPreimage_pullback S.inclusion A.pair.B)
      a.val a.property ha
  obtain ⟨c, _, hc, hbase⟩ := attachedBase_regular A.datum
  obtain ⟨d, hd⟩ := Flag.StandardParabolicLevi.exists_face_cocharacter (D := A.datum.datum)
    A.datum.base I S.simple
  have hsign (a : Specs.AbstractPairing.Root A.pair.T) :=
    Flag.StandardParabolicLevi.face_root_signs hc hbase hd a
  let V := A.datum.datum.rootDatum
  have subspan (a : I) : a.val ∈ Φ :=
    Submodule.subset_span ⟨a.val, a.property, rfl⟩
  have sums_stay (a : Φ) {x y : Specs.AbstractPairing.Root A.pair.T}
      (hx : x ∈ subgroupRoots A.pair.T A.pair.B) (hy : y ∈ subgroupRoots A.pair.T A.pair.B)
      (h : a.val.val = x.val * y.val) : x ∈ Φ ∧ y ∈ Φ := by
    have hxy : pairing A.pair.T.group a.val.val d =
        pairing A.pair.T.group x.val d + pairing A.pair.T.group y.val d := by
      rw [h, ← A.datum.datum.pairing_eq, ← A.datum.datum.pairing_eq x.val,
        ← A.datum.datum.pairing_eq y.val]
      exact map_add (V.toLinearMap.flip (Additive.ofMul d)) _ _
    have h0 := (hsign a.val).1.mpr a.property
    have hx0 := (hsign x).2 hx
    have hy0 := (hsign y).2 hy
    exact ⟨(hsign x).1.mp (by omega), (hsign y).1.mp (by omega)⟩
  have summands_lift (a x y : Φ) (h : (r a).val = (r x).val * (r y).val) :
      a.val.val = x.val.val * y.val.val := by
    apply Additive.ofMul.injective
    change Additive.ofMul a.val.val = Additive.ofMul x.val.val + Additive.ofMul y.val.val
    rw [← A.datum.datum.root_eq a.val, ← A.datum.datum.root_eq x.val, ← A.datum.datum.root_eq y.val]
    apply face_character_span_injective S hspan a.property
      (Submodule.add_mem _ x.property y.property)
    rw [map_add, A.datum.datum.root_eq, A.datum.datum.root_eq, A.datum.datum.root_eq]
    change Additive.ofMul (S.toAmbientTorus ≫ a.val.val) =
      Additive.ofMul ((S.toAmbientTorus ≫ x.val.val) * (S.toAmbientTorus ≫ y.val.val))
    exact congrArg Additive.ofMul (by simpa only [hr] using h)
  have hs : ∀ a : Φ, r a ∈ D.base.support ↔ a.val ∈ I := by
    intro a
    rw [D.simple_iff]
    constructor
    · intro h
      have ha : Pinning.IsSimple A.pair a.val := by
        refine ⟨(positive a).mp h.1, ?_⟩
        intro x hx y hy he
        obtain ⟨hx', hy'⟩ := sums_stay a hx hy he
        apply h.2 (r ⟨x, hx'⟩) ((positive _).mpr hx) (r ⟨y, hy'⟩) ((positive _).mpr hy)
        simp only [hr]
        change characterPullback S.toAmbientTorus a.val.val =
          characterPullback S.toAmbientTorus x.val * characterPullback S.toAmbientTorus y.val
        rw [he, map_mul]
      have hab := (A.datum.simple_iff a.val).mpr ha
      by_contra hI
      exact (hd.2 a.val ⟨hab, hI⟩).ne' ((hsign a.val).1.mpr a.property)
    · intro ha
      have h := (A.datum.simple_iff a.val).mp (S.simple ha)
      refine ⟨(positive a).mpr h.1, ?_⟩
      intro x hx y hy hxy
      let x' := r.symm x
      let y' := r.symm y
      have hx' : r x' ∈ subgroupRoots P.T P.B := by simpa only [x', r.apply_symm_apply] using hx
      have hy' : r y' ∈ subgroupRoots P.T P.B := by simpa only [y', r.apply_symm_apply] using hy
      exact h.2 x'.val ((positive x').mp hx') y'.val ((positive y').mp hy')
        (summands_lift a x' y' (by simpa only [x', y', r.apply_symm_apply] using hxy))
  let a (i : {i : Fin n // i ≠ node}) : Φ :=
    ⟨(A.numbering i.val).val, subspan
      ⟨(A.numbering i.val).val, (A.numbering i.val).property,
        fun h => i.property (A.numbering.injective (Subtype.ext h))⟩⟩
  let v₀ (i : {i : Fin n // i ≠ node}) : D.base.support :=
    ⟨r (a i), (hs (a i)).mpr
      ⟨(A.numbering i.val).property, fun h => i.property (A.numbering.injective (Subtype.ext h))⟩⟩
  have hv : Function.Bijective v₀ := by
    constructor
    · intro i j he
      have h := r.injective (congrArg Subtype.val he)
      have e : (A.numbering i.val).val = (A.numbering j.val).val :=
        congrArg (fun x : Φ => x.val) h
      exact Subtype.ext (A.numbering.injective (Subtype.ext e))
    · intro rootImage
      let rootLift := r.symm rootImage.val
      have hg : r rootLift = rootImage.val := r.apply_symm_apply rootImage.val
      have hLift : rootLift.val ∈ I := (hs rootLift).mp (hg.symm ▸ rootImage.property)
      let j := A.numbering.symm ⟨rootLift.val, S.simple hLift⟩
      have h : (A.numbering j).val = rootLift.val :=
        congrArg Subtype.val (A.numbering.apply_symm_apply _)
      have hj : j ≠ node := fun ej => hLift.2 (by simpa only [ej] using h.symm)
      refine ⟨⟨j, hj⟩, Subtype.ext ?_⟩
      change r (a ⟨j, hj⟩) = rootImage.val
      exact (congrArg r (Subtype.ext h)).trans hg
  refine ⟨P, rfl, D, Equiv.ofBijective v₀ hv, ?_⟩
  intro i j
  let q := (D.datum.rootDatum.coroot (r (a j))).toMul
  have hq : q ≫ S.toAmbientTorus = (V.coroot (a j).val).toMul := by
    have hβ := (faceRootRestrictions A.datum I S (a j).val (a j).property).1
    apply faceAttachedCoroots A.datum I S (a j).val (a j).property hβ
    simpa only [← hr, q] using D.datum.attached (r (a j))
  change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root (r (a i)))
    (D.datum.rootDatum.coroot (r (a j))) = _
  calc
    _ = pairing P.T.group (r (a i)).val q := by
      rw [D.datum.root_eq]
      exact D.datum.pairing_eq (r (a i)).val q
    _ = pairing A.pair.T.group (a i).val.val (q ≫ S.toAmbientTorus) := by
      have hr₀ : (r (a i)).val = S.toAmbientTorus ≫ (a i).val.val := hr (a i)
      rw [hr₀, pairing_pushforward]
      rfl
    _ = _ := by
      rw [hq, ← A.datum.datum.pairing_eq, ← A.datum.datum.root_eq]
      exact A.cartan_eq i.val j.val


private theorem omitted_node_split_marking (A : AdaptedPair G n) (node : Fin n)
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (c : Cocharacter A.S.group) (L : LimitDecomposition (c ≫ A.S.inclusion))
    (hc : ∀ i, let p := pairing A.pair.T.group (A.numbering i).val.val (A.geometricCocharacter c)
      if i = node then 0 < p else p = 0)
    (hL : IsReductive (closedSubgroupAlgebraicGroup L.centralizer))
    (H : ClosedSubgroup L.centralizer.group) (hH : IsDerivedSubgroup H) :
    ∃ (P : Pinning.SplitBorelPair (SeparableClosure F)),
      P.G = baseChangedAlgebraicGroup (SeparableClosure F)
        (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L.centralizer) H) ∧
      IsSemisimple P.G ∧ GeometricallySimplyConnected P.G ∧
      ∃ (D : Pinning.AttachedDatum P) (v : {i : Fin n // i ≠ node} ≃ D.toBased.base.support),
        ∀ i j, D.toBased.datum.pairing (v i) (v j) = CartanMatrix.E n i.val j.val := by
  obtain ⟨S, _, _, _, _, hGroup, hS, hspan⟩ :=
    exists_split_derived_face A node hG hSC c L hc hL H hH
  obtain ⟨P, eqP, D, v, hv⟩ := split_derived_face_cartan A node S hspan
  have hSS := derivedSemisimple (closedSubgroupAlgebraicGroup S.levi) S.reductive S.derived S.isDerived
  exact ⟨P, eqP.trans hGroup, eqP.symm ▸ hSS, eqP.symm ▸ hS, D, v, hv⟩

/-- The derived Levi omitting the second E₆ node has absolute simply
connected type A₅. Its split datum is marked by the original Levi chain. -/
theorem e6_derived_absolute_type_a (A : AdaptedPair G 6)
    (hG : IsSemisimple G) (hSC : GeometricallySimplyConnected G)
    (c : Cocharacter A.S.group) (L : LimitDecomposition (c ≫ A.S.inclusion))
    (hc : ∀ i, let p := pairing A.pair.T.group (A.numbering i).val.val (A.geometricCocharacter c)
      if i = 1 then 0 < p else p = 0)
    (hL : IsReductive (closedSubgroupAlgebraicGroup L.centralizer))
    (H : ClosedSubgroup L.centralizer.group) (hH : IsDerivedSubgroup H) :
    HasAbsoluteSimplyConnectedTypeA 5
      (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L.centralizer) H) := by
  obtain ⟨P, hP, hSS, hSC', D, v, hv⟩ := omitted_node_split_marking A 1 hG hSC c L hc hL H hH
  refine ⟨SeparableClosure F, inferInstance, inferInstance, inferInstance, P, hP,
    hSS, hSC', D, e6LeviVertices.trans v, ?_⟩
  intro i j
  exact (hv (e6LeviVertices i) (e6LeviVertices j)).trans (e6_levi_cartan.2.2.1 i j)

section DerivedSplitRank

open Specs.CharacterDescent (StandardLattice)
open Specs.RankOneFlag (IsKernelSubtorus)
open Specs.RelativeRank (relativeRank)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open private latticeCoordinates charactersOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private kernel_subtorus_in_splitPresentation latticeCharacter saturatedProjection_apply_self
  saturatedProjection saturatedProjection_prod_injective saturatedProjection_surjective saturatedQuotient_split
  SaturatedQuotient integerCharacters_hasUniqueRoots
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private standard_torus_dimension dimension_of_iso split_rank_eq_dimension dimension_of_subgroup_le
  maximal_split_over gm_id_ne_zero from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
open private factor_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private liftToSchemeKernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel

set_option maxHeartbeats 600000 in
/-- A nontrivial character of a split torus cuts out a largest split subtorus
of codimension one. This statement also applies to a nonprimitive character. -/
private theorem split_character_kernel_dimension {T : GroupScheme F} (hT : IsSplitTorus T)
    (χ : Character T) (hχ : χ ≠ 1) :
    ∃ (r : ℕ) (V : ClosedSubgroup T),
      IsSplitTorus V.group ∧ IsKernelSubtorus χ V ∧
      topologicalKrullDim V.group.X.left = (r : WithBot ℕ∞) ∧
      topologicalKrullDim T.X.left = ((r + 1 : ℕ) : WithBot ℕ∞) := by
  classical
  obtain ⟨s, ⟨i⟩⟩ := hT
  obtain ⟨d⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := F) s
  let j := d ≪≫ i.symm
  let M := StandardLattice.{u} s
  letI : Module.Finite ℤ (Additive M) := Module.Finite.equiv (latticeCoordinates s).symm
  letI : Group.FG M := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  obtain ⟨x, hx⟩ := (latticeCharacter (k := F) M).surjective (j.hom ≫ χ)
  have hxn : x ≠ 1 := by
    intro h
    apply hχ
    have he := congrArg (j.inv ≫ ·) hx
    rw [h, map_one, Iso.inv_hom_id_assoc] at he
    apply he.symm.trans
    apply Grp.hom_ext
    exact MonObj.comp_one j.inv.hom.hom
  obtain ⟨k, hk⟩ : ∃ k : Fin s, x k ≠ 1 := by
    by_contra! h
    exact hxn (funext h)
  let f : M →* IntegerCharacters.{u} := Pi.evalMonoidHom _ k
  letI := integerCharacters_hasUniqueRoots
  letI : HasUniqueRoots M := inferInstanceAs (HasUniqueRoots (Fin s → IntegerCharacters.{u}))
  let π := saturatedProjection x
  let N := π.ker
  let U : Submodule ℤ (Additive M) := (AddMonoidHom.toIntLinearMap π.toAdditive).ker
  have hp : Module.finrank ℤ U = 1 := by
    let f' : Additive M →ₗ[ℤ] ℤ :=
      ((MulEquiv.ulift : IntegerCharacters.{u} ≃* Multiplicative ℤ).toAdditive.toIntLinearEquiv).toLinearMap.comp
        (AddMonoidHom.toIntLinearMap f.toAdditive)
    have hf : Function.Injective (f'.domRestrict U) := by
      intro a b h
      apply Subtype.ext
      apply saturatedProjection_prod_injective x f hk
      have ha : π a.val.toMul = 1 := a.property
      have hb : π b.val.toMul = 1 := b.property
      change (π a.val.toMul, f a.val.toMul) = (π b.val.toMul, f b.val.toMul)
      rw [ha, hb]
      exact congrArg (Prod.mk 1) ((MulEquiv.ulift : IntegerCharacters.{u} ≃* Multiplicative ℤ).injective h)
    have hu : Module.finrank ℤ U ≤ 1 := by
      simpa using (LinearMap.finrank_le_finrank_of_injective hf)
    have hpos : 0 < Module.finrank ℤ U := by
      let a : U := ⟨Additive.ofMul x, saturatedProjection_apply_self x⟩
      have ha : a ≠ 0 := fun h => hxn (congrArg (fun t : U => t.val.toMul) h)
      letI : Nontrivial U := ⟨⟨a, 0, ha⟩⟩
      exact (Module.finrank_pos_iff_of_free ℤ U).mpr inferInstance
    omega
  have hs : Module.finrank ℤ (Additive (M ⧸ N)) + 1 = s := by
    let e₁ := (AddMonoidHom.toIntLinearMap π.toAdditive).quotKerEquivOfSurjective
      (saturatedProjection_surjective x)
    let e₂ : Additive (M ⧸ N) ≃ₗ[ℤ] Additive (SaturatedQuotient x) :=
      (QuotientGroup.quotientKerEquivOfSurjective π
      (saturatedProjection_surjective x)).toAdditive.toIntLinearEquiv
    have h := U.finrank_quotient_add_finrank
    rw [hp, (e₁.trans e₂.symm).finrank_eq, (latticeCoordinates s).finrank_eq] at h
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] using h
  obtain ⟨V, hV, e, _⟩ := kernel_subtorus_in_splitPresentation j χ x hx
  obtain ⟨r, ⟨t⟩⟩ := saturatedQuotient_split (k := F) M x
  have hr : Module.finrank ℤ (Additive (M ⧸ N)) = r := by
    obtain ⟨t'⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := F) r
    let t'' := t ≪≫ t'.symm
    let z : (M ⧸ N) ≃* StandardLattice.{u} r := (latticeCharacter (k := F) (M ⧸ N)).trans
      ((charactersOfIso t'').trans (latticeCharacter (k := F) (StandardLattice.{u} r)).symm)
    let y : Additive (M ⧸ N) ≃ₗ[ℤ] (Fin r → ℤ) :=
      z.toAdditive.toIntLinearEquiv.trans (latticeCoordinates r)
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] using y.finrank_eq
  refine ⟨r, V, ⟨r, ⟨e.symm ≪≫ t⟩⟩, hV, ?_, ?_⟩
  · exact (dimension_of_iso (e.symm ≪≫ t)).trans (standard_torus_dimension r)
  · rw [dimension_of_iso i, standard_torus_dimension, ← hs, hr]

set_option maxHeartbeats 800000 in
/-- Intersect a maximal split torus with the kernel of a split quotient
character on a reductive group. Its largest split subtorus is maximal in
the kernel, because the ambient maximal split tori are conjugate. -/
private theorem split_rank_of_character_kernel (M : AffineAlgebraicGroup F)
    (hM : IsReductive M) (S : ClosedSubgroup M.val) (hS : IsMaximalSplitTorus S)
    (p : Character M.val) (H : ClosedSubgroup M.val) (hk : IsSchemeKernel p H)
    (hχ : S.inclusion ≫ p ≠ (1 : Character S.group)) :
    ∃ r : ℕ, relativeRank (closedSubgroupAlgebraicGroup (G := M) H) = (r : WithBot ℕ∞) ∧
      topologicalKrullDim S.group.X.left = ((r + 1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨r, V, hV, hVχ, hdimV, hdimS⟩ :=
    split_character_kernel_dimension hS.1 (S.inclusion ≫ p) hχ
  have hzero : (subgroupOfSubgroup S V).inclusion ≫ p = 0 := by
    change (V.inclusion ≫ S.inclusion) ≫ p = _
    rw [Category.assoc]
    exact hVχ.2.1
  obtain ⟨j, hj⟩ := liftToSchemeKernel hk (subgroupOfSubgroup S V).inclusion hzero
  let VH : ClosedSubgroup H.group := ⟨_, j, factor_closed hj⟩
  refine ⟨r, ?_, hdimS⟩
  apply le_antisymm
  · apply iSup_le
    rintro ⟨W, hW⟩
    let W' := subgroupOfSubgroup H W
    obtain ⟨T, hT, ⟨a, ha⟩⟩ := maximal_split_over M W' hW
    obtain ⟨g, e, he⟩ := Relative.MaximalSplitTori.maximalSplitToriConjugate M hM T S hT hS
    let b : W.group ⟶ T.group := a
    letI : IsClosedImmersion b.hom.hom.left := factor_closed ha
    letI : IsIso e.hom.hom.hom.left :=
      ((Grp.forget (SchemeOver F)) ⋙ Over.forget _).map_isIso e.hom
    let W'' : ClosedSubgroup S.group :=
      ⟨W.group, b ≫ e.hom, IsClosedImmersion.comp _ _⟩
    have hz : W''.inclusion ≫ (S.inclusion ≫ p) = 1 := by
      apply Grp.hom_ext
      change b.hom.hom ≫ (e.hom ≫ S.inclusion).hom.hom ≫ p.hom.hom =
        (1 : W.group.X ⟶ _)
      have hw : b.hom.hom ≫ T.inclusion.hom.hom ≫ p.hom.hom = 1 := by
        rw [← Category.assoc, show b.hom.hom ≫ T.inclusion.hom.hom =
          W.inclusion.hom.hom ≫ H.inclusion.hom.hom from
            congrArg (fun f => f.hom.hom) ha]
        let w : W.group.X ⟶ H.group.X := W.inclusion.hom.hom
        change (w ≫ H.inclusion.hom.hom) ≫ p.hom.hom = 1
        have hh : H.inclusion.hom.hom ≫ p.hom.hom = 1 := hk.w
        rw [Category.assoc, hh, MonObj.comp_one]
      rw [he]
      simp only [MonObj.comp_mul, GrpObj.comp_inv, MonObj.mul_comp, GrpObj.inv_comp,
        Category.assoc, hw, mul_one, mul_inv_cancel]
    have h := dimension_of_subgroup_le (hVχ.2.2 W'' (isTorus_of_split hW) hz)
    exact h.trans_eq hdimV
  · have h := le_iSup
      (fun T : {T : ClosedSubgroup H.group // IsSplitTorus T.group} =>
        topologicalKrullDim T.val.group.X.left) ⟨VH, hV⟩
    change topologicalKrullDim V.group.X.left ≤ _ at h
    rwa [hdimV] at h

/-- In the specified rational limit Levi the derived split rank is one less
than the ambient split rank. The given coroot is used to test the quotient. -/
theorem omitted_node_derived_split_rank (A : AdaptedPair G n) (hG : IsReductive G)
    (c δ : Cocharacter A.S.group) (L : LimitDecomposition (c ≫ A.S.inclusion))
    (hL : IsReductive (closedSubgroupAlgebraicGroup L.centralizer))
    (H : ClosedSubgroup L.centralizer.group) (p : Character L.centralizer.group)
    (hk : IsSchemeKernel p H) (s : Cocharacter L.centralizer.group)
    (hs : s ≫ L.centralizer.inclusion = δ ≫ A.S.inclusion)
    (hsp : s ≫ p = 𝟙 _) :
    ∃ r : ℕ, relativeRank (closedSubgroupAlgebraicGroup
      (G := closedSubgroupAlgebraicGroup L.centralizer) H) = (r : WithBot ℕ∞) ∧
      relativeRank G = ((r + 1 : ℕ) : WithBot ℕ∞) := by
  let M := closedSubgroupAlgebraicGroup L.centralizer
  obtain ⟨j, hj⟩ := torus_subgroupOf_centralizer A.maximalSplit.1 c L
  let S : ClosedSubgroup M.val := ⟨_, j, factor_closed hj⟩
  have hS : IsMaximalSplitTorus S := by
    refine ⟨A.maximalSplit.1, ?_⟩
    rintro T hT ⟨v, hv⟩
    have hST : IsSubgroupOf A.S (subgroupOfSubgroup L.centralizer T) :=
      ⟨v, by
        change v ≫ T.inclusion ≫ L.centralizer.inclusion = A.S.inclusion
        rw [← Category.assoc, show v ≫ T.inclusion = j from hv, hj]⟩
    obtain ⟨w, hw⟩ := A.maximalSplit.2 _ hT hST
    refine ⟨w, ?_⟩
    letI := closedSubgroup_mono L.centralizer
    apply (cancel_mono L.centralizer.inclusion).mp
    rw [Category.assoc, show S.inclusion ≫ L.centralizer.inclusion = A.S.inclusion from hj]
    exact hw
  have hs' : δ ≫ j = s := by
    letI := closedSubgroup_mono L.centralizer
    apply (cancel_mono L.centralizer.inclusion).mp
    rw [Category.assoc, hj, hs]
  have hχ : S.inclusion ≫ p ≠ (1 : Character S.group) := by
    intro h
    apply gm_id_ne_zero (k := F)
    rw [← hsp, ← hs', Category.assoc, show j ≫ p = 1 from h]
    apply Grp.hom_ext
    exact MonObj.comp_one δ.hom.hom
  obtain ⟨r, hr, he⟩ := split_rank_of_character_kernel M hL S hS p H hk hχ
  exact ⟨r, hr, (split_rank_eq_dimension G hG A.S A.maximalSplit).symm.trans he⟩

end DerivedSplitRank

section DivisionMatrixModels

open scoped TensorProduct
open _root_.Specs.RM03.CSA (degree isCentralSimple isCentralDivision)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)
open _root_.RM03.CSA.NormOneGroup (normAt_natural normAt_eq_det extendSplitting
  extendSplitting_tmul changeCoefficients)
open Specs.OuterTypeAModels (RepresentsNormOne)
open Specs.RelativeRank (relativeRank)
open private dimension_of_iso standard_torus_dimension from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
open private groupIsoOfPointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeASplitRank

private abbrev normOneTensorEquiv {A B : Type u} [Ring A] [Ring B] [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) (R : Type u) [CommRing R] [Algebra F R] :
    R ⊗[F] A ≃ₐ[R] R ⊗[F] B :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e

private theorem normOneTensorEquiv_natural {A B R T : Type u}
    [Ring A] [Ring B] [Algebra F A] [Algebra F B]
    [CommRing R] [Algebra F R] [CommRing T] [Algebra F T]
    (e : A ≃ₐ[F] B) (g : R →ₐ[F] T) (x : R ⊗[F] A) :
    changeCoefficients g (normOneTensorEquiv e R x) =
      normOneTensorEquiv e T (changeCoefficients g x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem normAt_eq_det_of_size {A E R : Type u} [Ring A] [Algebra F A]
    [Field E] [Algebra F E] [CommRing R] [Algebra F R] [Algebra E R] [IsScalarTower F E R]
    (hA : isCentralSimple F A) {J : Type u} [Fintype J] (b : Module.Basis J F A)
    {n : ℕ} (e : E ⊗[F] A ≃ₐ[E] Matrix (Fin n) (Fin n) E) (x : R ⊗[F] A) :
    normAt hA b x = (extendSplitting e x).det := by
  have h := _root_.RM03.CSA.degree_eq_matrix_size hA e
  cases h
  exact normAt_eq_det hA b e x

private theorem normAt_transport_algebra {A B R : Type u} [Ring A] [Ring B]
    [Algebra F A] [Algebra F B] [CommRing R] [Algebra F R]
    (hA : isCentralSimple F A) (hB : isCentralSimple F B) (e : A ≃ₐ[F] B)
    {I J : Type u} [Fintype I] [Fintype J] (a : Module.Basis I F A) (b : Module.Basis J F B)
    (x : R ⊗[F] A) :
    normAt hB b (normOneTensorEquiv e R x) = normAt hA a x := by
  let E := AlgebraicClosure F
  let R' := E ⊗[F] R
  let g : R →ₐ[F] R' := Algebra.TensorProduct.includeRight
  have hg : Function.Injective g :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F E).injective
  obtain ⟨eB⟩ := _root_.RM03.CSA.algEquiv_matrix_algebraicClosure hB
  let eA := (normOneTensorEquiv e E).trans eB
  have he (y : R' ⊗[F] A) : extendSplitting eB (normOneTensorEquiv e R' y) =
      extendSplitting eA y := by
    induction y using TensorProduct.inductionOn with
    | tmul r a =>
      rw [show normOneTensorEquiv e R' (r ⊗ₜ[F] a) = r ⊗ₜ[F] e a from rfl,
        extendSplitting_tmul, extendSplitting_tmul]
      rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  apply hg
  change g (_root_.RM03.CSA.NormOneGroup.normAt hB b (normOneTensorEquiv e R x)) =
    g (_root_.RM03.CSA.NormOneGroup.normAt hA a x)
  rw [← normAt_natural hB b g, ← normAt_natural hA a g, normOneTensorEquiv_natural,
    normAt_eq_det hB b eB]
  exact (congrArg Matrix.det (he (changeCoefficients g x))).trans
    (normAt_eq_det_of_size hA a eA _).symm

/-- Transport the entire reduced-norm-one functor through an algebra
isomorphism, including multiplication and all test-algebra maps. -/
theorem represents_norm_one_of_alg_equiv {A B : Type u} [Ring A] [Ring B]
    [Algebra F A] [Algebra F B] {H : AffineAlgebraicGroup F}
    (hA : isCentralSimple F A) (hB : isCentralSimple F B) (e : A ≃ₐ[F] B)
    {I J : Type u} [Fintype I] [Fintype J] (a : Module.Basis I F A) (b : Module.Basis J F B)
    (h : RepresentsNormOne hA a H) : RepresentsNormOne hB b H := by
  obtain ⟨p, hm, hn⟩ := h
  let q (R : TestAlgebra F) :
      {x : R ⊗[F] A // normAt hA a x = 1} ≃ {x : R ⊗[F] B // normAt hB b x = 1} :=
    Equiv.subtypeEquiv (normOneTensorEquiv e R).toEquiv (fun x => by
      change normAt hA a x = 1 ↔ normAt hB b (normOneTensorEquiv e R x) = 1
      rw [normAt_transport_algebra hA hB e a b])
  refine ⟨fun R => (p R).trans (q R), ?_, ?_⟩
  · intro R x y
    change normOneTensorEquiv e R (p R (x * y)).val =
      normOneTensorEquiv e R (p R x).val * normOneTensorEquiv e R (p R y).val
    rw [hm, map_mul]
  · intro R T f x
    change normOneTensorEquiv e T (p T (mapPoints f x)).val =
      changeCoefficients f.hom (normOneTensorEquiv e R (p R x).val)
    rw [hn, normOneTensorEquiv_natural]
    rfl

/-- The specified reduced-norm-one form of a matrix algebra over a central
division algebra has split rank one less than the matrix size. -/
theorem represented_division_matrix_rank {H : AffineAlgebraicGroup F}
    {B : Type u} [DivisionRing B] [Algebra F B] (hB : isCentralDivision F B) (n : ℕ)
    (hA : isCentralSimple F (Matrix (Fin (n + 1)) (Fin (n + 1)) B))
    {J : Type u} [Fintype J] (b : Module.Basis J F (Matrix (Fin (n + 1)) (Fin (n + 1)) B))
    (h : RepresentsNormOne hA b H) :
    relativeRank H = (n : WithBot ℕ∞) := by
  obtain ⟨operations, P, S, _, hs, hS, _, hBound⟩ := InnerTypeASplitRank.splitRank n hB hA b
  obtain ⟨p, hmul, hnatural⟩ := h
  let H₀ := @Specs.StandardGroups.spectrum F _
    (LinearAlgebraicGroups.Descent.InnerTypeA.Specification.NormOneCoordinates hA b) _
    operations.hopf inferInstance
  let j (R : TestAlgebra F) :
      ((groupPointsFunctor F).obj H.val).obj R ≃*
      ((groupPointsFunctor F).obj H₀.val).obj R :=
    { toEquiv := (p R).trans (P.point R).symm
      map_mul' := fun x y => by
        apply (P.point R).injective
        apply Subtype.ext
        change (P.point R ((P.point R).symm (p R (x * y)))).val =
          (P.point R ((P.point R).symm (p R x) * (P.point R).symm (p R y))).val
        rw [P.mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hmul] }
  let e : (groupPointsFunctor F).obj H.val ≅ (groupPointsFunctor F).obj H₀.val :=
    NatIso.ofComponents (fun R => (j R).toGrpIso) (fun f => by
      ext x
      apply (P.point _).injective
      apply Subtype.ext
      change (P.point _ ((P.point _).symm (p _ (mapPoints f x)))).val =
        (P.point _ (mapPoints f ((P.point _).symm (p _ x)))).val
      rw [P.natural, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hnatural f x)
  obtain ⟨g, _⟩ := groupIsoOfPointIso H H₀ e
  have torus_dimension {T : GroupScheme F} {r : ℕ}
      (i : T ≅ (Specs.StandardGroups.multiplicativePowerGroup F (ULift.{u} (Fin r))).val) :
      topologicalKrullDim T.X.left = (r : WithBot ℕ∞) :=
    (dimension_of_iso i).trans (standard_torus_dimension r)
  unfold relativeRank
  apply le_antisymm
  · apply iSup_le
    rintro ⟨T, ⟨r, ⟨i⟩⟩⟩
    have hr := hBound r (pushSubgroup g T) ⟨i⟩
    change topologicalKrullDim T.group.X.left ≤ (n : WithBot ℕ∞)
    rw [torus_dimension i]
    exact_mod_cast hr
  · obtain ⟨i⟩ := hs
    have h := le_iSup
      (fun T : {T : ClosedSubgroup H.val // IsSplitTorus T.group} =>
        topologicalKrullDim T.val.group.X.left)
      ⟨pushSubgroup g.symm S, hS.1⟩
    change topologicalKrullDim S.group.X.left ≤ _ at h
    rwa [torus_dimension i] at h

set_option maxHeartbeats 600000 in
private theorem norm_one_division_presentation {A : Type u} [Ring A] [Algebra F A]
    {H : AffineAlgebraicGroup F} (hA : isCentralSimple F A)
    {J : Type u} [Fintype J] (b : Module.Basis J F A) (h : RepresentsNormOne hA b H)
    {r : ℕ} (hr : relativeRank H = (r : WithBot ℕ∞)) :
    ∃ (B : Type u) (_ : DivisionRing B) (_ : Algebra F B),
      isCentralSimple F B ∧ degree F A = (r + 1) * degree F B ∧
        RepresentsDivisionMatrixNormOne H (r + 1) B := by
  obtain ⟨m, B, dB, aB, hB, hm₀, ⟨e⟩⟩ := _root_.RM03.CSA.MatrixDivision.exists_presentation F A hA
  have hB' : isCentralSimple F B := _root_.RM03.CSA.isCentralSimple_of_isCentralDivision F B hB
  cases m with
  | zero => exact (Nat.not_lt_zero 0 hm₀).elim
  | succ m =>
    let M := Matrix (Fin (m + 1)) (Fin (m + 1)) B
    have hM : isCentralSimple F M := InnerTypeASplitRank.centralSimpleMatrix hm₀ hB'
    letI := hM.2.2
    let bM : Module.Basis (ULift.{u} (Fin (Module.finrank F M))) F M :=
      (Module.finBasis F M).reindex Equiv.ulift.symm
    have hHM := represents_norm_one_of_alg_equiv hA hM e b bM h
    have hr' := represented_division_matrix_rank hB m hM bM hHM
    have he : m = r := by
      have he' := hr'.symm.trans hr
      exact_mod_cast he'
    subst m
    have hmul := _root_.RM03.CSA.degree_matrix_division hA hB hm₀ e
    refine ⟨B, dB, aB, hB', hmul, ?_⟩
    exact ⟨hM, bM, hHM⟩

/-- The degree-six algebra and the split rank determine the division
degree in the matrix presentation of the norm-one group. -/
theorem degree_six_norm_one_matrix_model {A : Type u} [Ring A] [Algebra F A]
    {H : AffineAlgebraicGroup F} (hA : isCentralSimple F A) (hd : degree F A = 6)
    {J : Type u} [Fintype J] (b : Module.Basis J F A) (h : RepresentsNormOne hA b H)
    {r d : ℕ} (hr : relativeRank H = (r : WithBot ℕ∞)) (hm : (r + 1) * d = 6) :
    ∃ (B : Type u) (_ : DivisionRing B) (_ : Algebra F B),
      isCentralSimple F B ∧ degree F B = d ∧ RepresentsDivisionMatrixNormOne H (r + 1) B := by
  obtain ⟨B, dB, aB, hB, hmul, hModel⟩ := norm_one_division_presentation hA b h hr
  exact ⟨B, dB, aB, hB, Nat.mul_left_cancel (Nat.succ_pos r) (hmul.symm.trans (hd.trans hm.symm)), hModel⟩

end DivisionMatrixModels

section ExceptionalLeviModels

open Specs.GeometricRadicals (IsSplitReductive)
open Specs.QuasiSplitInnerForms (AreInnerForms)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.RelativeRank (relativeRank)
open _root_.Specs.RM03.CSA (degree)
open Specs.SplitLeviMatrixComparison (chainCartan)
open private maximalTransport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private schemeIsoEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison

private theorem omitted_node_inner_reference (A : AdaptedPair G n)
    (hG : IsReductive G) (hInner : IsInner G)
    (c : Cocharacter A.S.group) (L : LimitDecomposition (c ≫ A.S.inclusion))
    (hL : IsReductive (closedSubgroupAlgebraicGroup L.centralizer))
    (H : ClosedSubgroup L.centralizer.group) (hH : IsDerivedSubgroup H) :
    ∃ R : AffineAlgebraicGroup F, IsSplitReductive R ∧
      AreInnerForms (S := SeparableClosure F) R
        (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L.centralizer) H) ∧
      Nonempty ((groupBaseChange F (SeparableClosure F)).obj R.val ≅
        (groupBaseChange F (SeparableClosure F)).obj H.group) := by
  let E := groupBaseChange F (SeparableClosure F)
  let T := transportSubgroup A.ambient A.pair.T
  obtain ⟨G₀, hG₀, hForm⟩ := hInner
  have ht : (E.map c ≫ A.splitInAbsolute) ≫ T.inclusion = E.map (c ≫ A.S.inclusion) := by
    calc
      _ = E.map c ≫ E.map A.intoTorus ≫ E.map A.T.inclusion := by
        change (E.map c ≫ (E.map A.intoTorus ≫ A.torus.hom)) ≫
          (A.pair.T.inclusion ≫ A.ambient.hom) = _
        simp only [Category.assoc, A.torus_eq]
        rfl
      _ = _ := by rw [← E.map_comp, A.intoTorus_eq, ← E.map_comp]
  obtain ⟨_, L₀, H₀, _, _, hR, _, _, e, _, _, _, V, inn, hLift, hInj, i, _, hi⟩ :=
    Descent.InnerLeviDescent.innerLeviDescent G₀ G hG₀ hG hForm (c ≫ A.S.inclusion)
      L hL H hH T A.pair.split (maximalTransport A.ambient A.pair.T A.pair.maximal)
      ⟨E.map c ≫ A.splitInAbsolute, ht⟩
  exact ⟨closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L₀.centralizer) H₀,
    hR, ⟨V, inn, hLift, hInj, i, hi⟩, ⟨e⟩⟩

private theorem e7_model_of_inner_product
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (Q₁ Q₂ R H : AffineAlgebraicGroup F) (hQ₁ : IsSplitReductive Q₁) (hQ₂ : IsSplitReductive Q₂)
    (s₁ : SpecialMatrixPoints Q₁ 2) (s₂ : SpecialMatrixPoints Q₂ 6)
    (hH : IsReductive H) (b : R.val ≅ Limits.prod Q₁.val Q₂.val)
    (hInner : AreInnerForms (S := SeparableClosure F) R H) (hRank : relativeRank H = 3) :
    HasE7LeviModel H := by
  obtain ⟨H₁, H₂, e, hH₁, hH₂, _, i₁, i₂, _, _, hi₂, _⟩ :=
    Descent.InnerProductFactors.innerProductFactors Q₁ Q₂ R H hQ₁ hQ₂ hH b hInner
  obtain ⟨V₂, inn₂, hLift₂, hInj₂, hDisp₂⟩ := hi₂
  have hInner₂ : AreInnerForms (S := SeparableClosure F) Q₂ H₂ :=
    ⟨V₂, inn₂, hLift₂, hInj₂, i₂, hDisp₂⟩
  have hForm₁ : Specs.AutomorphismSequence.IsSeparableForm Q₁ H₁ :=
    ⟨SeparableClosure F, inferInstance, inferInstance, inferInstance,
      ⟨(schemeIsoEquiv (SeparableClosure F) Q₁.val H₁.val).symm i₁⟩⟩
  obtain ⟨A, _, _, hA, hdA, _, _, a, ha⟩ :=
    InnerTypeANormOneModel.innerTypeANormOneModel hInner₂ ⟨Iso.refl _⟩ s₂
  obtain ⟨r₁, r₂, hr₁, hr₂, hSum⟩ := MatrixFactorSplitRank.productSplitRank H H₁ H₂ hH hH₁ hH₂ e
  obtain ⟨B, dB, aB, hB, hdB, hModel⟩ := norm_one_division_presentation hA a ha hr₂
  have hrs : r₁ + r₂ = 3 := by
    have he : ((r₁ + r₂ : ℕ) : WithBot ℕ∞) = 3 := by
      simpa only [Nat.cast_add] using hSum.symm.trans hRank
    exact_mod_cast he
  have hDegree : (r₂ + 1) * degree F B = 6 := hdB.symm.trans hdA
  have hNonzero : relativeRank H₁ ≠ 0 := by
    intro h
    have hz : r₁ = 0 := by exact_mod_cast hr₁.symm.trans h
    have hr : r₂ = 3 := by omega
    have hDiv : 4 ∣ 6 := ⟨degree F B, by simpa only [hr] using hDegree.symm⟩
    exact (by decide : ¬ 4 ∣ 6) hDiv
  obtain ⟨hone, ⟨s⟩⟩ := (MatrixFactorSplitRank.rankOneFormSplitRank Q₁ H₁ s₁ hH₁ hForm₁).resolve_left
    hNonzero
  have hr₁' : r₁ = 1 := by exact_mod_cast hr₁.symm.trans hone
  have hr₂' : r₂ = 2 := by omega
  subst r₂
  have hd : degree F B = 2 := by omega
  exact ⟨H₁, H₂, s, B, dB, aB, local_quaternion_of_degree_two hB hd, hModel, ⟨e⟩⟩

/-- The omitted-node Levi in the nonsplit inner E₆ index. -/
theorem e6OmittedNodeLevi : E6OmittedNodeLevi.{u} := by
  intro F _ _ _ _ G A hG hSC hInner _ hRank hWhite δ hδ
  have hRed := reductive_of_semisimple G hG
  have hInj : Function.Injective (![1, 3] : Fin 2 → Fin 6) := by
    unfold Function.Injective
    decide +kernel
  obtain ⟨c, L, hc, hPar, hProper, hJ, hMax⟩ := exists_omitted_node_limit A hRed hInj hWhite 0
  obtain ⟨H, Q, q, s, hL, hH, _, hQ, hk, hq, hs⟩ :=
    derived_quotient_of_omitted_node_limit A hRed c δ L
  obtain ⟨p, hp, hquot, hsp⟩ := omitted_node_quotient_section A 1 hG hSC c δ hδ L hc hL H hH Q q hQ hk hq s hs
  refine ⟨c, L, hc, hPar, hProper, hJ, hMax, H, p, s, hH,
    omitted_node_derived_simply_connected A 1 hG hSC c L hc hL H hH, hp, hquot, hsp, hs, ?_⟩
  obtain ⟨t, ht, htG⟩ := omitted_node_derived_split_rank A hRed c δ L hL H p hp s hs hsp
  have ht' : t = 1 := by
    have he : t + 1 = 2 := by exact_mod_cast htG.symm.trans hRank
    omega
  subst t
  obtain ⟨R, hR, hInner', ⟨e⟩⟩ := omitted_node_inner_reference A hRed hInner c L hL H hH
  obtain ⟨P, hP, hPS, hPSC, D, v, hv⟩ := omitted_node_split_marking A 1 hG hSC c L hc hL H hH
  have hChain : ∀ i j : Fin 5, CartanMatrix.A 5 i j = chainCartan i j := by decide +kernel
  obtain ⟨Q₂, _, ⟨s₂⟩, f⟩ := SplitLeviMatrixComparison.singleChain R hR P hPS hPSC
    (eqToIso (congrArg Subtype.val hP) ≪≫ e.symm) D (e6LeviVertices.trans v) fun i j =>
      (hv (e6LeviVertices i) (e6LeviVertices j)).trans ((e6_levi_cartan.2.2.1 i j).trans (hChain i j))
  obtain ⟨B, _, _, hB, hdB, _, _, b, hb⟩ := InnerTypeANormOneModel.innerTypeANormOneModel hInner' f s₂
  exact degree_six_norm_one_matrix_model hB hdB b hb ht (d := 3) (by decide)

/-- The omitted-node Levi in the nonsplit inner E₇ index. -/
theorem e7OmittedNodeLevi : E7OmittedNodeLevi.{u} := by
  intro F _ _ _ _ G A hG hSC hInner _ hRank hWhite δ hδ
  have hRed := reductive_of_semisimple G hG
  have hInj : Function.Injective (![0, 2, 3, 5] : Fin 4 → Fin 7) := by
    unfold Function.Injective
    decide +kernel
  obtain ⟨c, L, hc, hPar, hProper, hJ, hMax⟩ := exists_omitted_node_limit A hRed hInj hWhite 1
  obtain ⟨H, Q, q, s, hL, hH, hSS, hQ, hk, hq, hs⟩ :=
    derived_quotient_of_omitted_node_limit A hRed c δ L
  obtain ⟨p, hp, hquot, hsp⟩ := omitted_node_quotient_section A 2 hG hSC c δ hδ L hc hL H hH Q q hQ hk hq s hs
  refine ⟨c, L, hc, hPar, hProper, hJ, hMax, H, p, s, hH,
    omitted_node_derived_simply_connected A 2 hG hSC c L hc hL H hH, hp, hquot, hsp, hs, ?_⟩
  obtain ⟨t, ht, htG⟩ := omitted_node_derived_split_rank A hRed c δ L hL H p hp s hs hsp
  have ht' : t = 3 := by
    have he : t + 1 = 4 := by exact_mod_cast htG.symm.trans hRank
    omega
  subst t
  obtain ⟨R, hR, hInner', ⟨e⟩⟩ := omitted_node_inner_reference A hRed hInner c L hL H hH
  obtain ⟨P, hP, hPS, hPSC, D, v, hv⟩ := omitted_node_split_marking A 2 hG hSC c L hc hL H hH
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, ⟨s₁⟩, ⟨s₂⟩, ⟨f⟩⟩ :=
    SplitLeviMatrixComparison.twoBlocks R hR P hPS hPSC (eqToIso (congrArg Subtype.val hP) ≪≫ e.symm)
      D (e7LeviVertices.trans v) fun i j =>
        (hv (e7LeviVertices i) (e7LeviVertices j)).trans (e7LeviVertex_cartan i j)
  exact e7_model_of_inner_product Q₁ Q₂ R _ hQ₁ hQ₂ s₁ s₂ (reductive_of_semisimple _ hSS) f hInner' ht

end ExceptionalLeviModels

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalOmittedNodeLevis
