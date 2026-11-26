import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianLeviDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OrthogonalDerivedLevi
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RankOneOddDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TransitiveLeviDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianMarkedLevi
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.PolynomialAlgebra
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianLeviDescent

open LinearAlgebraicGroups.Specs
open TrialitarianAlbertDescentSpecification (DiagramPresentation)
open Specs.RelativeFormComparison (transportedAut)
open Specs.QuasiSplitInnerForms (outerHom)

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable {F E S : Type u} [Field F] [Field E] [Field S] [Algebra F E] [Algebra F S]
  {G : AffineAlgebraicGroup F}

/-- The permutation of marked vertices given by the outer part of the
transported coefficient automorphism. -/
def markedPermutation (D : DiagramPresentation G E S) (σ : Gal(S/F)) :
    Equiv.Perm (Fin 4) :=
  let a := outerHom D.autSequence (transportedAut F S D.form σ)
  let e := a.asIso.hom.val.indexEquiv
  D.roots.trans ((e.subtypeEquiv (fun i => by
    let I : Set D.datum.toBased.I := D.datum.toBased.base.support
    change i ∈ I ↔ e i ∈ I
    have he : e '' I = I := a.asIso.hom.property
    have hm : e i ∈ e '' I ↔ e i ∈ I := by rw [he]
    exact e.injective.mem_set_image.symm.trans hm)).trans D.roots.symm)

theorem markedPermutation_apply (D : DiagramPresentation G E S) (σ : Gal(S/F))
    (i : Fin 4) :
    (D.roots (markedPermutation D σ i)).val =
      (outerHom D.autSequence (transportedAut F S D.form σ)).asIso.hom.val.indexEquiv
        (D.roots i).val := by
  simp [markedPermutation]

theorem markedPermutation_outer (D : DiagramPresentation G E S) (σ : Gal(S/F))
    (e : E →ₐ[F] S) :
    markedPermutation D σ (D.numbering e).castSucc =
      (D.numbering (σ.toAlgHom.comp e)).castSucc := by
  apply D.roots.injective
  apply Subtype.ext
  rw [markedPermutation_apply]
  exact D.diagramAction σ e

private theorem markedPermutation_central (D : DiagramPresentation G E S) (σ : Gal(S/F)) :
    markedPermutation D σ 3 = 3 := by
  by_contra h
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr h
  let e := σ.symm.toAlgHom.comp (D.numbering.symm i)
  have he : σ.toAlgHom.comp e = D.numbering.symm i := by
    ext x
    exact σ.apply_symm_apply _
  have hm := markedPermutation_outer D σ e
  rw [he, Equiv.apply_symm_apply, hi] at hm
  exact Fin.castSucc_ne_last (D.numbering e) ((markedPermutation D σ).injective hm)

/-- The stabilizer of the distinguished outer vertex is exactly the
Galois subgroup fixing the actual cubic subfield in the given tower. -/
theorem fixesDistinguishedVertex_iff [Algebra E S] [IsScalarTower F E S]
    (D : DiagramPresentation G E S) (σ : Gal(S/F)) :
    let e : E →ₐ[F] S := IsScalarTower.toAlgHom F E S
    markedPermutation D σ (D.numbering e).castSucc = (D.numbering e).castSucc ↔
      σ.toAlgHom.comp e = e := by
  dsimp only
  rw [markedPermutation_outer]
  exact ⟨fun h => D.numbering.injective (Fin.castSucc_injective _ h), fun h => by rw [h]⟩

private theorem conjugateEmbeddings [Module.Finite F E] [Algebra.IsSeparable F E]
    [IsSepClosure F S] (e f : E →ₐ[F] S) :
    ∃ σ : Gal(S/F), σ.toAlgHom.comp e = f := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element F E
  have hmin : minpoly F (f x) = minpoly F (e x) :=
    (minpoly.algHom_eq f f.injective x).trans (minpoly.algHom_eq e e.injective x).symm
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := F) S).mp hmin
  refine ⟨σ, ?_⟩
  apply AlgHom.ext_of_adjoin_eq_top
    ((IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
      (fun y _ => Algebra.IsAlgebraic.isAlgebraic (R := F) y)).mp hx)
  intro y hy
  have hxy : y = x := Set.mem_singleton_iff.mp hy
  subst y
  exact hσ

/-- A proper nonempty stable set of simple vertices consists either of
the central vertex or of the full orbit of the three embeddings of E. -/
theorem stableMarkedSubset [Module.Finite F E] [Algebra.IsSeparable F E]
    [IsSepClosure F S] (D : DiagramPresentation G E S)
    (J : Set (Fin 4)) (hne : J.Nonempty) (hproper : J ≠ Set.univ)
    (hstable : ∀ σ i, i ∈ J → markedPermutation D σ i ∈ J) :
    J = {3} ∨ J = Set.range (fun i : Fin 3 => i.castSucc) := by
  by_cases hout : ∃ i : Fin 3, i.castSucc ∈ J
  · obtain ⟨i, hi⟩ := hout
    have houter (j : Fin 3) : j.castSucc ∈ J := by
      let e := D.numbering.symm i
      let f := D.numbering.symm j
      obtain ⟨σ, hσ⟩ := conjugateEmbeddings e f
      have he : D.numbering e = i := D.numbering.apply_symm_apply i
      have hf : D.numbering f = j := D.numbering.apply_symm_apply j
      have h := markedPermutation_outer D σ e
      rw [hσ, he, hf] at h
      exact h ▸ hstable σ _ hi
    have hc : (3 : Fin 4) ∉ J := by
      intro hc
      apply hproper
      apply Set.eq_univ_of_forall
      intro j
      by_cases hj : j = 3
      · exact hj.symm ▸ hc
      · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
        exact houter i
    right
    apply Set.ext
    intro j
    constructor
    · intro hj
      have hn : j ≠ Fin.last 3 := by
        intro he
        subst j
        exact hc hj
      exact Fin.exists_castSucc_eq.mpr hn
    · rintro ⟨i, rfl⟩
      exact houter i
  · have hc (j : Fin 4) (hj : j ∈ J) : j = 3 := by
      by_contra h
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr h
      exact hout ⟨i, hj⟩
    obtain ⟨j, hj⟩ := hne
    left
    exact Set.ext fun k => ⟨hc k, fun hk =>
      ((hc j hj).trans (show k = 3 from hk).symm) ▸ hj⟩

/-- All embeddings of a finite separable field land in one finite Galois
layer of the chosen separable closure. -/
theorem exists_finiteGaloisContainingEmbeddings [Module.Finite F E]
    [Algebra.IsSeparable F E] [IsSepClosure F S] :
    ∃ K : FiniteGaloisIntermediateField F S,
      ∀ (e : E →ₐ[F] S) (x : E), e x ∈ K.toIntermediateField := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element F E
  let s : Set S := Set.range (fun e : E →ₐ[F] S => e a)
  letI : Finite s := (Set.finite_range _).to_subtype
  let K := FiniteGaloisIntermediateField.adjoin F s
  refine ⟨K, fun e x => ?_⟩
  have h : a ∈ K.toIntermediateField.comap e :=
    FiniteGaloisIntermediateField.subset_adjoin F s ⟨e, rfl⟩
  have htop : ⊤ ≤ K.toIntermediateField.comap e :=
    ha ▸ IntermediateField.adjoin_simple_le_iff.mpr h
  exact htop (show x ∈ (⊤ : IntermediateField F E) from IntermediateField.mem_top)

/-- The inclusion of a layer containing the images of all embeddings
identifies its embedding labels with those of the separable closure. -/
def finiteGaloisEmbeddings (K : FiniteGaloisIntermediateField F S)
    (hK : ∀ (e : E →ₐ[F] S) (x : E), e x ∈ K.toIntermediateField) :
    (E →ₐ[F] K) ≃ (E →ₐ[F] S) :=
  Equiv.ofBijective (fun e => K.toIntermediateField.val.comp e) ⟨
    fun _ _ hef => AlgHom.ext fun x => Subtype.ext (DFunLike.congr_fun hef x),
    fun e => ⟨e.codRestrict K.toIntermediateField.toSubalgebra (hK e), AlgHom.ext fun _ => rfl⟩⟩

theorem finiteGaloisEmbeddings_restriction [IsGalois F S]
    (K : FiniteGaloisIntermediateField F S)
    (hK : ∀ (e : E →ₐ[F] S) (x : E), e x ∈ K.toIntermediateField)
    (σ : Gal(S/F)) (e : E →ₐ[F] K) :
    finiteGaloisEmbeddings K hK ((AlgEquiv.restrictNormalHom K σ).toAlgHom.comp e) =
      σ.toAlgHom.comp (finiteGaloisEmbeddings K hK e) := by
  apply AlgHom.ext
  intro x
  exact AlgEquiv.restrictNormal_commutes σ K (e x)

section MinimalParabolic

open Specs.BorelProper (IsParabolic)
open Specs.Relative.MaximalSplitTori (IsMinimalParabolic)
open Specs.GeometricRadicals (IsReductive)
open Specs.CharacterDescent (Cocharacter)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open CocharacterDynamics (LimitDecomposition existsLimitDecomposition oppositeCocharacter)
open private limitIsParabolic centralizesOfOppositeLimitsWhole
  leviParabolicIsWhole from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private inclusion_mono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private subgroupIso_of_same from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag

/-- Every minimal parabolic in a reductive group with a noncentral
ground-field cocharacter is a proper closed subgroup scheme. -/
theorem minimalParabolic_proper_of_noncentral (hG : IsReductive G)
    {P : ClosedSubgroup G.val} (hP : IsMinimalParabolic G P)
    {c : Cocharacter G.val} {X : SchemeOver F} {g : X ⟶ G.val.X}
    (hc : ¬ Centralizes c g) : ¬ IsIso P.inclusion := by
  intro h
  letI := h
  have whole (Q : ClosedSubgroup G.val) (hQ : IsParabolic G Q) : IsIso Q.inclusion := by
    obtain ⟨r, hr⟩ := hP.2 Q hQ ⟨Q.inclusion ≫ inv P.inclusion, by simp⟩
    letI := inclusion_mono Q
    haveI : IsSplitEpi Q.inclusion :=
      ⟨⟨inv P.inclusion ≫ r, by rw [Category.assoc, hr, IsIso.inv_hom_id]⟩⟩
    exact isIso_of_mono_of_isSplitEpi _
  obtain ⟨D⟩ := existsLimitDecomposition G c
  obtain ⟨D'⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  letI := whole D.parabolic (limitIsParabolic G hG c D)
  letI := whole D'.parabolic (limitIsParabolic G hG _ D')
  exact hc (centralizesOfOppositeLimitsWhole G c D D' g)

/-- The Levi of a minimal rational parabolic has no noncentral cocharacter
defined over the ground field. The assertion is on all test schemes. -/
theorem minimalParabolicLevi_centralizes (P : ClosedSubgroup G.val)
    (hP : IsMinimalParabolic G P) {c : Cocharacter G.val} (D : LimitDecomposition c)
    (hPD : Specs.RankOneFlag.SameSubgroup P D.parabolic)
    (hL : IsReductive (closedSubgroupAlgebraicGroup D.centralizer))
    (d : Cocharacter D.centralizer.group) {X : SchemeOver F}
    (g : X ⟶ D.centralizer.group.X) : Centralizes d g := by
  let L := closedSubgroupAlgebraicGroup D.centralizer
  obtain ⟨e, _⟩ := subgroupIso_of_same hPD
  obtain ⟨A⟩ := existsLimitDecomposition L d
  obtain ⟨B⟩ := existsLimitDecomposition L (oppositeCocharacter d)
  letI : IsIso A.parabolic.inclusion := leviParabolicIsWhole P hP D e A.parabolic (limitIsParabolic L hL _ A)
  letI : IsIso B.parabolic.inclusion := leviParabolicIsWhole P hP D e B.parabolic (limitIsParabolic L hL _ B)
  exact centralizesOfOppositeLimitsWhole L d A B g

end MinimalParabolic

section Centralizer

open scoped CategoryTheory.MonObj
open Specs.GeometricBorelConjugacy (IsKBorel IsBorel IsQuasiSplit ConjugatesSubgroups subgroupOfSubgroup)
open Specs.GeometricRadicals (GeometricGroup IsReductive IsSplitTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open private exists_maximal_torus_over subgroupOfSubgroup_le conjugationIso comp_conjugate conjugate
  restrictSubgroup compose_restrict transportSubgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private conjugates_inverse conjugate_isKBorel isBorel_of_same connected_of_reductive
  extendSubgroup subgroup_extend
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private torus_baseChange_algClosure from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private reductive_geometricGroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private preimageSubgroup intersection_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicIntersection
open private subgroup_of_intersection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection

private theorem borelContainingSplitTorus (hq : IsQuasiSplit G) (A : ClosedSubgroup G.val)
    (hA : IsSplitTorus A.group) : ∃ B : ClosedSubgroup G.val, IsKBorel B ∧ IsSubgroupOf A B := by
  obtain ⟨B, hB⟩ := hq.2
  have hmin := QuasiSplitFixedWeyl.borelIsMinimalParabolic G hq.1 B hB
  obtain ⟨g, T, hg⟩ :=
    _root_.LinearAlgebraicGroups.Relative.MaximalSplitTori.splitTorusConjugateIntoMinimalParabolic
      G B A hmin hA
  let B' := transportSubgroup (conjugationIso g⁻¹) B
  let C := subgroupOfSubgroup B T
  have hc : ConjugatesSubgroups g A C := hg
  obtain ⟨e, he⟩ := conjugates_inverse hc
  have h : e.hom ≫ A.inclusion = T.inclusion ≫ B'.inclusion := by
    apply Grp.hom_ext
    rw [he]
    change _ = T.inclusion.hom.hom ≫ B.inclusion.hom.hom ≫
      (conjugationIso g⁻¹).hom.hom.hom
    change _ = T.inclusion.hom.hom ≫ B.inclusion.hom.hom ≫
      conjugate g⁻¹ (𝟙 G.val.X)
    change conjugate g⁻¹
      (T.inclusion.hom.hom ≫ B.inclusion.hom.hom) = _
    rw [← Category.assoc, comp_conjugate, Category.comp_id]
  refine ⟨B', conjugate_isKBorel B hB g⁻¹, e.inv ≫ T.inclusion, ?_⟩
  change (e.inv ≫ T.inclusion) ≫ B'.inclusion = A.inclusion
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m : C.group ⟶ G.val => e.inv ≫ m) h.symm).trans (e.inv_hom_id_assoc _))

/-- The scheme centralizer of any split torus in a quasi-split group
has a ground-field Borel, obtained by intersection with a Borel
containing that torus. -/
theorem centralizer_isQuasiSplit (hq : IsQuasiSplit G)
    {A C : ClosedSubgroup G.val} (hA : IsSplitTorus A.group) (hC : IsCentralizer A C)
    (hCr : IsReductive (closedSubgroupAlgebraicGroup C)) :
    IsQuasiSplit (closedSubgroupAlgebraicGroup C) := by
  obtain ⟨B, hB, hAB⟩ := borelContainingSplitTorus hq A hA
  let K := AlgebraicClosure F
  let G' := GeometricGroup G
  let A' : ClosedSubgroup G'.val := extendSubgroup K A
  let B' : ClosedSubgroup G'.val := extendSubgroup K B
  let C' : ClosedSubgroup G'.val := extendSubgroup K C
  have hB' : IsBorel B' := hB.choose_spec
  have hA' := torus_baseChange_algClosure (closedSubgroupAlgebraicGroup A)
    (isTorus_of_split hA)
  have hAB' : IsSubgroupOf A' B' := subgroup_extend K hAB
  obtain ⟨a, ha⟩ := hAB'
  let A₀ := restrictSubgroup A' B' a ha
  obtain ⟨T₀, hT₀, hAT⟩ := exists_maximal_torus_over (closedSubgroupAlgebraicGroup B') A₀ hA'
  let T := subgroupOfSubgroup B' T₀
  have hg := reductive_geometricGroup G hq.1
  have hT := (LinearAlgebraicGroups.MaximalToriConjugate.borelMaximalTorusIff
    G' hg.1 (connected_of_reductive G' hg) B' hB' T₀).mp hT₀
  have hAT' : IsSubgroupOf A' T := by
    rw [← compose_restrict A' B' a ha]
    exact (subgroupOfSubgroup_le B' A₀ T₀).mpr hAT
  obtain ⟨_, hC'⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange F K A.inclusion C hC
  obtain ⟨L, hL, hLB⟩ :=
    LinearAlgebraicGroups.Reductive.SubtorusCentralizer.centralizerBorel
      G' hg.1 (connected_of_reductive G' hg) T A' hT hA' hAT' C' hC'
      B' hB' ⟨T₀.inclusion, rfl⟩
  let D := preimageSubgroup C.inclusion B
  let D' := extendSubgroup K D
  have hp := LinearAlgebraicGroups.baseChangeSubgroupPullback F K
    (IsPullback.of_hasPullback C.inclusion B.inclusion)
  have hD' : Specs.UnipotentRadicalIntersection.IsSchemeIntersection {C', B'}
      (subgroupOfSubgroup C' D') := by
    apply intersection_spec (P := C') (Q := B') hp
    rfl
  have hsame : Specs.RankOneFlag.SameSubgroup L D' := by
    constructor
    · apply (subgroupOfSubgroup_le C' L D').mp
      exact (subgroup_of_intersection hD').mpr
        ((subgroup_of_intersection hL).mp ⟨𝟙 _, Category.id_comp _⟩)
    · apply (subgroupOfSubgroup_le C' D' L).mp
      exact (subgroup_of_intersection hL).mpr
        ((subgroup_of_intersection hD').mp ⟨𝟙 _, Category.id_comp _⟩)
  exact ⟨hCr, D, D'.isClosedImmersion,
    isBorel_of_same (A := GeometricGroup (closedSubgroupAlgebraicGroup C)) hsame hLB⟩

open private splitTorus_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

/-- Quasi-splitness over an extension gives a Borel of the scalar extension
of the centralizer of the original split torus. -/
theorem baseChangedCentralizer_isQuasiSplit
    (hq : IsQuasiSplit (baseChangedAlgebraicGroup E G))
    {A C : ClosedSubgroup G.val} (hA : IsSplitTorus A.group) (hC : IsCentralizer A C)
    (hCr : IsReductive (closedSubgroupAlgebraicGroup C)) :
    IsQuasiSplit (baseChangedAlgebraicGroup E (closedSubgroupAlgebraicGroup C)) := by
  let H := baseChangedAlgebraicGroup E G
  let A' : ClosedSubgroup H.val := extendSubgroup E A
  let C' : ClosedSubgroup H.val := extendSubgroup E C
  obtain ⟨_, hc⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange F E A.inclusion C hC
  have hr := (LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension
    (K := E) (closedSubgroupAlgebraicGroup C) hCr.1 hCr.2.1).mpr hCr
  exact centralizer_isQuasiSplit (G := H) (A := A') (C := C') hq
    (splitTorus_baseChange hA) hc hr

open Specs.BorelsAndChambers (contractingSubgroup)
open CocharacterDynamics (LimitDecomposition existsLimitDecomposition limitSubgroupsSmooth
  geometricallyConnectedLimitSubgroups contractingSubgroupUnipotent)
open private gm_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private limits_subgroups_extend subgroupIso_of_same
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private solvable_of_torus_kernel connected_of_geometricallyConnected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private isSplitTorus_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private subgroupOf_trans from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private limitContainsBorel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori

/-- A limit parabolic with torus Levi is a ground-field Borel. -/
theorem isKBorel_of_torusLevi (hG : IsReductive G)
    {c : CharacterDescent.Cocharacter G.val} (D : LimitDecomposition c)
    (hC : Specs.GeometricRadicals.IsTorus D.centralizer.group) :
    IsKBorel D.parabolic := by
  let K := AlgebraicClosure F
  let H := GeometricGroup G
  have hH := reductive_geometricGroup G hG
  obtain ⟨i, hi⟩ := gm_baseChange F K
  let d : CharacterDescent.Cocharacter H.val := i.hom ≫ (groupBaseChange F K).map c
  obtain ⟨D'⟩ := existsLimitDecomposition H d
  obtain ⟨hP, _, hZ⟩ := limits_subgroups_extend G D i hi D'
  obtain ⟨e, _⟩ := subgroupIso_of_same hZ
  have hC' := torus_baseChange_algClosure (closedSubgroupAlgebraicGroup D.centralizer) hC
  have hs : IsSplitTorus D'.centralizer.group := by
    obtain ⟨n, ⟨f⟩⟩ :=
      isSplitTorus_of_torus (baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup D.centralizer)) hC'
    exact ⟨n, ⟨e ≪≫ f⟩⟩
  letI := hH.1
  letI := connected_of_reductive H hH
  obtain ⟨hPs, hUs, _⟩ := limitSubgroupsSmooth H d D'
  obtain ⟨hPc, hUc, _⟩ := geometricallyConnectedLimitSubgroups H d D'
  let B := closedSubgroupAlgebraicGroup D'.parabolic
  let C := closedSubgroupAlgebraicGroup D'.centralizer
  have hU : Specs.Unipotent.IsUnipotent (closedSubgroupAlgebraicGroup (G := B) (contractingSubgroup D')) := by
    obtain ⟨M, j, hj⟩ := contractingSubgroupUnipotent H d D'
    exact ⟨M, j, hj⟩
  have hsol := solvable_of_torus_kernel (A := B) (L := C) (contractingSubgroup D') D'.limit D'.isKernel
    hs hPs (connected_of_geometricallyConnected hPc) hUs (connected_of_geometricallyConnected hUc) hU
  have hBs : Specs.GeometricBorelConjugacy.IsSmoothConnectedSolvable D'.parabolic :=
    ⟨hPs, connected_of_geometricallyConnected hPc, hsol⟩
  obtain ⟨P, hB, hBP⟩ := limitContainsBorel H hH d D'
  have hB' := isBorel_of_same (A := H) ⟨hBP, hB.2 _ hBs hBP⟩ hB
  exact ⟨(extendSubgroup K D.parabolic).isClosedImmersion, isBorel_of_same (A := H) hP hB'⟩

section OriginalLevi

open Specs.GeometricRadicals (identitySubgroup)
open Specs.Relative.MaximalSplitTori (IsMinimalParabolic IsMaximalSplitTorus)
open Specs.RankOneFlag (SameSubgroup)
open Specs.StandardParabolicLevi (IsContractingRadical)
open Specs.CharacterDescent (Cocharacter)
open private minimalParabolicExists maximalSplitOfConjugate maximalSplitInParabolic
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private maximalSplitTorusAbove from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeWeylScheme
open private trivial_isSplitTorus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags

/-- Choose a proper minimal rational parabolic and a maximal split torus of
the original group inside it. The resulting Levi centralizes that torus
scheme-theoretically. -/
theorem exists_properMinimalParabolicLevi (hG : IsReductive G)
    {d : Cocharacter G.val} {X : SchemeOver F} {g : X ⟶ G.val.X}
    (hd : ¬ Centralizes d g) :
    ∃ (P : ClosedSubgroup G.val) (A : ClosedSubgroup P.group)
      (c : Cocharacter A.group) (D : LimitDecomposition (c ≫ (subgroupOfSubgroup P A).inclusion)),
      IsMinimalParabolic G P ∧ ¬ IsIso P.inclusion ∧
      IsMaximalSplitTorus (subgroupOfSubgroup P A) ∧
      SameSubgroup P D.parabolic ∧ IsContractingRadical D ∧
      IsReductive (closedSubgroupAlgebraicGroup D.centralizer) ∧
      IsCentralizer (subgroupOfSubgroup P A) D.centralizer := by
  obtain ⟨P, hP⟩ := minimalParabolicExists G hG
  obtain ⟨S, hS, _⟩ := maximalSplitTorusAbove G (identitySubgroup G) trivial_isSplitTorus
  obtain ⟨_, A, hA⟩ :=
    _root_.LinearAlgebraicGroups.Relative.MaximalSplitTori.splitTorusConjugateIntoMinimalParabolic
      G P S hP hS.1
  have hmax := maximalSplitOfConjugate hA hS
  obtain ⟨c, D, hPD, hU, hC, _, hcent⟩ :=
    _root_.LinearAlgebraicGroups.Relative.MaximalSplitTori.minimalParabolicLevi
      G P hP A (maximalSplitInParabolic hmax)
  exact ⟨P, A, c, D, hP, minimalParabolic_proper_of_noncentral hG hP hd,
    hmax, hPD, hU, hC, hcent⟩

open private kBorel_smooth_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private torus_of_iso inclusion_mono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

/-- A quasi-split Levi of a minimal parabolic is a torus. Thus its ambient
minimal parabolic is itself a Borel. -/
theorem isQuasiSplit_of_quasiSplitMinimalLevi
    {P : ClosedSubgroup G.val} (hP : IsMinimalParabolic G P)
    {c : Cocharacter G.val} (D : LimitDecomposition c) (hPD : SameSubgroup P D.parabolic)
    (hq : IsQuasiSplit (closedSubgroupAlgebraicGroup D.centralizer)) :
    IsQuasiSplit G := by
  let L := closedSubgroupAlgebraicGroup D.centralizer
  obtain ⟨hL, B, hB⟩ := hq
  obtain ⟨hs, hc⟩ := kBorel_smooth_connected L B hB
  obtain ⟨T₀, hT₀, hmax⟩ :=
    LinearAlgebraicGroups.MaximalToriExist.geometricallyMaximalTorusExists
      (closedSubgroupAlgebraicGroup B) hs hc
  let T := subgroupOfSubgroup B T₀
  let K := AlgebraicClosure F
  let B' : ClosedSubgroup (GeometricGroup L).val := extendSubgroup K B
  let T₀' : ClosedSubgroup B'.group := extendSubgroup K T₀
  have hTm : Specs.RankOneFlag.IsGeometricallyMaximal T := by
    refine ⟨(extendSubgroup K T).isClosedImmersion, ?_⟩
    have hT' := (LinearAlgebraicGroups.MaximalToriConjugate.borelMaximalTorusIff
      (GeometricGroup L) (reductive_geometricGroup L hL).1
      (connected_of_reductive (GeometricGroup L) (reductive_geometricGroup L hL))
      B' hB.choose_spec T₀').mp hmax.choose_spec
    have hEq : extendSubgroup K T = subgroupOfSubgroup B' T₀' := by
      let F' := groupBaseChange F K
      have same {a b : F'.obj T₀.group ⟶ (GeometricGroup L).val}
          (ha : IsClosedImmersion a.hom.hom.left) (hb : IsClosedImmersion b.hom.hom.left)
          (h : a = b) :
          (⟨F'.obj T₀.group, a, ha⟩ : ClosedSubgroup (GeometricGroup L).val) =
            ⟨F'.obj T₀.group, b, hb⟩ := by cases h; rfl
      exact same _ _ (F'.map_comp T₀.inclusion B.inclusion)
    change Specs.GeometricRadicals.IsMaximalTorus (extendSubgroup K T)
    rw [hEq]
    exact hT'
  obtain ⟨d, hd⟩ :=
    QuasiSplitFixedWeyl.borelTorusCentralizer L hL B T hB hT₀ hTm ⟨T₀.inclusion, rfl⟩
  obtain ⟨s, hs⟩ := (hd _ (𝟙 L.val.X)).mp
    (minimalParabolicLevi_centralizes P hP D hPD hL (d ≫ T.inclusion) (𝟙 L.val.X))
  obtain ⟨f, hf⟩ := factor_group_through_subgroup T (𝟙 L.val) s hs
  letI := inclusion_mono T
  haveI : IsSplitEpi T.inclusion := ⟨⟨f, hf⟩⟩
  letI : IsIso T.inclusion := isIso_of_mono_of_isSplitEpi T.inclusion
  have htor := torus_of_iso (asIso T.inclusion) hT₀
  exact ⟨hP.1.1, D.parabolic, isKBorel_of_torusLevi hP.1.1 D htor⟩

end OriginalLevi

end Centralizer

section GeometricLevi

open scoped CategoryTheory.MonObj
open Specs.BorelProper (IsParabolic)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricBorelConjugacy (IsBorel subgroupOfSubgroup)
open Specs.GeometricRadicals (IsMaximalTorus IsReductive IsTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open CocharacterDynamics (LimitDecomposition)
open private cocharacter_centralizes_self from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private connected_of_reductive from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private maximalTorus_of_geometricallyMaximal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private restrictSubgroup local_maximal_of_ambient compose_restrict inclusion_mono
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torusSectionsCentralize from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

/-- The defining one-parameter subgroup of a Levi factors through each
geometrically maximal torus of that Levi. -/
theorem cocharacter_factors_through_leviTorus
    {c : Cocharacter G.val} (L : LimitDecomposition c)
    (hL : IsReductive (closedSubgroupAlgebraicGroup L.centralizer))
    (T : ClosedSubgroup L.centralizer.group) (hT : IsTorus T.group)
    (hm : Specs.RankOneFlag.IsGeometricallyMaximal T) :
    ∃ a : Cocharacter T.group, a ≫ (subgroupOfSubgroup L.centralizer T).inclusion = c := by
  obtain ⟨j, hj⟩ := (L.centralizer_points _ _).mp (cocharacter_centralizes_self c)
  obtain ⟨d, hd⟩ := factor_group_through_subgroup L.centralizer c j hj
  let e := L.centralizer.inclusion
  haveI := L.centralizer.isClosedImmersion
  haveI : Mono e.hom.hom := Over.mono_of_mono_left _
  have hcent : Centralizes T.inclusion d.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro Y x t
    have ht := (L.centralizer_points _ _).mpr ⟨t ≫ T.inclusion.hom.hom, rfl⟩
    have h := (centralizes_iff _ _).mp ht Y (𝟙 Y) x
    change (x ≫ d.hom.hom) * (t ≫ T.inclusion.hom.hom) =
      (t ≫ T.inclusion.hom.hom) * (x ≫ d.hom.hom)
    apply (cancel_mono e.hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    have hd' : d.hom.hom ≫ e.hom.hom = c.hom.hom :=
      congrArg (fun f => f.hom.hom) hd
    simpa only [Category.assoc, Category.id_comp, hd'] using h.symm.eq
  have hC := Reductive.TorusCentralizer.maximalTorusCentralizer
    (closedSubgroupAlgebraicGroup L.centralizer) hL T hT hm
  obtain ⟨m, hm'⟩ := (hC _ _).mp hcent
  obtain ⟨a, ha⟩ := factor_group_through_subgroup T d m hm'
  exact ⟨a, by change a ≫ T.inclusion ≫ e = c; rw [← Category.assoc, ha, hd]⟩

/-- A maximal torus of the limit Levi is maximal in the ambient group.
Any larger torus contains the defining cocharacter, so is already in the
scheme centralizer. -/
theorem leviTorus_isMaximalInAmbient
    {c : Cocharacter G.val} (L : LimitDecomposition c)
    (hL : IsReductive (closedSubgroupAlgebraicGroup L.centralizer))
    (T : ClosedSubgroup L.centralizer.group) (hT : IsTorus T.group)
    (hm : Specs.RankOneFlag.IsGeometricallyMaximal T) :
    IsMaximalTorus (subgroupOfSubgroup L.centralizer T) := by
  let V := subgroupOfSubgroup L.centralizer T
  obtain ⟨a, ha⟩ := cocharacter_factors_through_leviTorus L hL T hT hm
  have hmax := maximalTorus_of_geometricallyMaximal
    (closedSubgroupAlgebraicGroup L.centralizer) T hT hm
  refine ⟨hT, fun W hW ⟨i, hi⟩ => ?_⟩
  have he : (a ≫ i) ≫ W.inclusion = c := by
    rw [Category.assoc, hi]
    exact ha
  have hc := torusSectionsCentralize (G := G) (T := W) hW (a ≫ i) (𝟙 W.group.X)
  rw [he, Category.id_comp] at hc
  obtain ⟨r, hr⟩ := (L.centralizer_points _ _).mp hc
  obtain ⟨f, hf⟩ := factor_group_through_subgroup L.centralizer W.inclusion r hr
  let W' := restrictSubgroup W L.centralizer f hf
  haveI := L.centralizer.isClosedImmersion
  haveI : Mono L.centralizer.inclusion := inclusion_mono L.centralizer
  have hTW : IsSubgroupOf T W' := by
    refine ⟨i, (cancel_mono L.centralizer.inclusion).mp ?_⟩
    change (i ≫ f) ≫ L.centralizer.inclusion = _
    rw [Category.assoc, hf, hi]
    rfl
  obtain ⟨s, hs⟩ := hmax.2 W' hW hTW
  refine ⟨s, ?_⟩
  change s ≫ T.inclusion ≫ L.centralizer.inclusion = W.inclusion
  rw [← Category.assoc, hs]
  exact hf

open private limitContainsBorel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private geometricBorelThroughTorus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open CocharacterDynamics (limitSubgroupsSmooth)

/-- A Borel pair in the geometric parabolic, with the original cocharacter
factored through its torus in the actual Levi. -/
theorem exists_borelPair_in_limitParabolic [IsAlgClosed F]
    (hG : IsReductive G) {c : Cocharacter G.val} (L : LimitDecomposition c)
    (hL : IsReductive (closedSubgroupAlgebraicGroup L.centralizer)) :
    ∃ (T : ClosedSubgroup L.centralizer.group) (B : ClosedSubgroup G.val)
      (a : Cocharacter T.group),
      IsTorus T.group ∧ Specs.RankOneFlag.IsGeometricallyMaximal T ∧
      IsMaximalTorus (subgroupOfSubgroup L.centralizer T) ∧ IsBorel B ∧
      IsSubgroupOf (subgroupOfSubgroup L.centralizer T) B ∧
      IsSubgroupOf B L.parabolic ∧ a ≫ (subgroupOfSubgroup L.centralizer T).inclusion = c := by
  obtain ⟨T, hT, hm⟩ := MaximalToriExist.geometricallyMaximalTorusExists
    (closedSubgroupAlgebraicGroup L.centralizer) hL.1
    (connected_of_reductive (closedSubgroupAlgebraicGroup L.centralizer) hL)
  obtain ⟨a, ha⟩ := cocharacter_factors_through_leviTorus L hL T hT hm
  have hmax := leviTorus_isMaximalInAmbient L hL T hT hm
  let V := subgroupOfSubgroup L.centralizer T
  let j := T.inclusion ≫ L.sectionMap
  have hj : j ≫ L.parabolic.inclusion = V.inclusion := by
    change (T.inclusion ≫ L.sectionMap) ≫ L.parabolic.inclusion = _
    rw [Category.assoc, L.section_in_G]
    rfl
  let W := restrictSubgroup V L.parabolic j hj
  have hw := compose_restrict V L.parabolic j hj
  have hW := local_maximal_of_ambient L.parabolic W (hw.symm ▸ hmax)
  obtain ⟨B, hB, hBP⟩ := limitContainsBorel G hG c L
  letI := hG.1
  letI := hG.2.1
  obtain ⟨_, Q, hQ, hTQ, hQP⟩ := geometricBorelThroughTorus
    Flag.StandardParabolics.standardParabolicClassification G L.parabolic B
    hG (limitSubgroupsSmooth G c L).1 hB hBP W hW
  have hVQ : IsSubgroupOf V Q := hw ▸ hTQ
  exact ⟨T, Q, a, hT, hm, hmax, hQ, hVQ, hQP, ha⟩

end GeometricLevi

section ParabolicType

open scoped CategoryTheory.MonObj
open Specs.BorelProper (IsParabolic)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups IsBorel subgroupOfSubgroup)
open Specs.RankOneFlag (SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private borel_in_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolics
open private geometricParabolicConnected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open private restrictSubgroup compose_restrict transportSubgroup conjugationIso conjugates_in_ambient
  conjugates_trans normalizes_of_conjugates_self conjugates_preserves_borel
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private isKBorel_iff_of_isAlgClosed conjugates_transport_ambient conjugates_same_target
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private borel_transport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private conjugatesInclusions from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeWeylScheme

/-- Two geometrically conjugate parabolics through a fixed Borel agree.
The conjugating point is corrected inside the receiving parabolic by
conjugacy of its Borels. -/
theorem sameParabolic_of_conjugate_containingBorel [IsAlgClosed F]
    {P Q B : ClosedSubgroup G.val} (hQ : IsParabolic G Q)
    (hB : IsBorel B) (hBP : IsSubgroupOf B P) (hBQ : IsSubgroupOf B Q)
    {g : 𝟙_ (SchemeOver F) ⟶ G.val.X} (hg : ConjugatesSubgroups g P Q) :
    SameSubgroup P Q := by
  let B' := transportSubgroup (conjugationIso g) B
  have hB' : IsBorel B' := borel_transport hB (conjugationIso g)
  have hconj : ConjugatesSubgroups g B B' := conjugates_transport_ambient B g
  obtain ⟨i, hi⟩ := hBQ
  obtain ⟨j, hj⟩ := conjugatesInclusions hconj hg hBP
  let C := restrictSubgroup B Q i hi
  let C' := restrictSubgroup B' Q j hj
  have hC := compose_restrict B Q i hi
  have hC' := compose_restrict B' Q j hj
  have hCB : IsBorel C := borel_in_subgroup C (hC.symm ▸ hB)
  have hCB' : IsBorel C' := borel_in_subgroup C' (hC'.symm ▸ hB')
  have hcQ := geometricParabolicConnected Flag.StandardParabolics.standardParabolicClassification
    G Q B hQ.1 hQ.2.1 hB ⟨i, hi⟩
  obtain ⟨a, ha⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.borelsConjugate
    (closedSubgroupAlgebraicGroup Q) hQ.2.1 hcQ C' C hCB' hCB
  let x := a ≫ Q.inclusion.hom.hom
  have ht : ConjugatesSubgroups x B' B := by
    have ht' := conjugates_in_ambient Q ha
    change ConjugatesSubgroups x (subgroupOfSubgroup Q (restrictSubgroup B' Q j hj))
      (subgroupOfSubgroup Q (restrictSubgroup B Q i hi)) at ht'
    rw [hC, hC'] at ht'
    exact ht'
  have hb : ConjugatesSubgroups (x * g) B B := conjugates_trans hconj ht
  have hN := RootData.BorelNormalizer.groundFieldBorelNormalizer G hQ.1 B
    ((isKBorel_iff_of_isAlgClosed G B).mpr hB)
  obtain ⟨b, hb'⟩ := (hN _ _).mp (normalizes_of_conjugates_self B hb)
  obtain ⟨p, hp⟩ := hBP
  let y := b ≫ p.hom.hom
  have hy : y ≫ P.inclusion.hom.hom = x * g := by
    change (b ≫ p.hom.hom) ≫ P.inclusion.hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, hp]
    exact hb'
  have hPP : ConjugatesSubgroups (x * g) P P := hy ▸ conjugates_preserves_borel P y
  have hPQ : ConjugatesSubgroups (x * g) P Q :=
    conjugates_trans hg (conjugates_preserves_borel Q a)
  exact conjugates_same_target hPP hPQ

end ParabolicType

section LimitComparison

open scoped CategoryTheory.MonObj
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.RankOneFlag (SameSubgroup)
open CocharacterDynamics (HasExtension LimitDecomposition)
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private hasLimit_hom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private same_subgroup_of_same_affine_points same_subgroup_of_same_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

private theorem centralizes_postcomp {A H J : GroupScheme F} (f : H ⟶ J)
    (c : A ⟶ H) {X : SchemeOver F} {x : X ⟶ H.X} (hx : Centralizes c x) :
    Centralizes (c ≫ f) (x ≫ f.hom.hom) := by
  apply (centralizes_iff _ _).mpr
  intro Y y t
  have h := ((centralizes_iff _ _).mp hx Y y t).map (IsMonHom.monoidHom f.hom.hom Y)
  change Commute ((y ≫ x) ≫ f.hom.hom) ((t ≫ c.hom.hom) ≫ f.hom.hom) at h
  simpa only [Category.assoc, Grp.comp_hom_hom] using h

/-- A closed subgroup inclusion carries a witness of noncentrality into the
ambient group. -/
theorem noncentralCocharacter_inclusion {H : GroupScheme F} (B : ClosedSubgroup H)
    (c : Cocharacter B.group) {X : SchemeOver F} (x : X ⟶ B.group.X)
    (hx : ¬ Centralizes c x) :
    ¬ Centralizes (c ≫ B.inclusion) (x ≫ B.inclusion.hom.hom) := by
  intro h
  apply hx
  apply (centralizes_iff _ _).mpr
  intro Y y t
  haveI := B.isClosedImmersion
  haveI : Mono B.inclusion.hom.hom := Over.mono_of_mono_left _
  have hcomm := (centralizes_iff _ _).mp h Y y t
  apply Commute.of_map (f := IsMonHom.monoidHom B.inclusion.hom.hom Y)
  · exact fun _ _ => (cancel_mono B.inclusion.hom.hom).mp
  · change Commute ((y ≫ x) ≫ B.inclusion.hom.hom) ((t ≫ c.hom.hom) ≫ B.inclusion.hom.hom)
    simpa only [Category.assoc, Grp.comp_hom_hom] using hcomm

/-- A comparison of the defining cocharacters identifies the embedded limit
parabolics and embedded Levis under the same isomorphism. -/
theorem limitParabolicLevi_transport {H : AffineAlgebraicGroup F}
    (e : G.val ≅ H.val) {c : Cocharacter G.val} {d : Cocharacter H.val}
    (D : LimitDecomposition c) (L : LimitDecomposition d) (he : c ≫ e.hom = d) :
    SameSubgroup L.parabolic (transportSubgroup e D.parabolic) ∧
      SameSubgroup L.centralizer (transportSubgroup e D.centralizer) := by
  have hd : d ≫ e.inv = c := by rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hei : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 H.val.X :=
    (Grp.forget (SchemeOver F)).congr_map e.inv_hom_id
  constructor
  · apply same_subgroup_of_same_affine_points (G := H) L.parabolic_points
    intro R x
    constructor
    · rintro ⟨z, hz⟩
      have hback := hasLimit_hom e.inv hz
      rw [hd] at hback
      obtain ⟨p, hp⟩ := (D.parabolic_points R _).mp ⟨_, hback⟩
      change p ≫ D.parabolic.inclusion.hom.hom = x ≫ e.inv.hom.hom at hp
      refine ⟨p, ?_⟩
      change p ≫ D.parabolic.inclusion.hom.hom ≫ e.hom.hom.hom = x
      rw [← Category.assoc, hp, Category.assoc, hei, Category.comp_id]
    · rintro ⟨p, hp⟩
      change p ≫ D.parabolic.inclusion.hom.hom ≫ e.hom.hom.hom = x at hp
      let p₀ : GroupPoints G.val R := p ≫ D.parabolic.inclusion.hom.hom
      obtain ⟨z, hz⟩ := (D.parabolic_points R p₀).mpr ⟨p, rfl⟩
      have h := hasLimit_hom e.hom hz
      change CocharacterDynamics.HasLimit (c ≫ e.hom)
        ((p ≫ D.parabolic.inclusion.hom.hom) ≫ e.hom.hom.hom) (z ≫ e.hom.hom.hom) at h
      rw [he, Category.assoc, hp] at h
      exact ⟨_, h⟩
  · apply same_subgroup_of_same_sections (H := H) L.centralizer_points
    intro X x
    constructor
    · intro hx
      have hh := centralizes_postcomp e.inv d hx
      rw [hd] at hh
      obtain ⟨p, hp⟩ := (D.centralizer_points _ _).mp hh
      refine ⟨p, ?_⟩
      change p ≫ D.centralizer.inclusion.hom.hom ≫ e.hom.hom.hom = x
      rw [← Category.assoc, hp, Category.assoc, hei, Category.comp_id]
    · rintro ⟨p, hp⟩
      change p ≫ D.centralizer.inclusion.hom.hom ≫ e.hom.hom.hom = x at hp
      have hh := centralizes_postcomp e.hom c
        ((D.centralizer_points _ _).mpr ⟨p, rfl⟩)
      rwa [he, Category.assoc, hp] at hh

end LimitComparison

section WeilCocharacters

open scoped TensorProduct CategoryTheory.MonObj
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.StandardGroups (multiplicativePoints)
open _root_.LinearAlgebraicGroups.WeilRestriction (extendScalars)
open Specs.QuasiSplitInducedWeilProduct (scalarExtensionOfGroundField weilFieldPointIso)
open private integerPointsIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

private def diagonalUnits (F E : Type u) [Field F] [Field E] [Algebra F E] :
    multiplicativePoints F ⟶ extendScalars F E ⋙ multiplicativePoints E where
  app R := GrpCat.ofHom (Units.map
    (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := R) (B := E)).toMonoidHom)
  naturality R T a := by
    apply GrpCat.ext
    intro x
    let r : Rˣ := x
    apply Units.ext
    change Algebra.TensorProduct.map a.hom (AlgHom.id F E) ((r : R) ⊗ₜ[F] (1 : E)) =
      a.hom (r : R) ⊗ₜ[F] (1 : E)
    exact Algebra.TensorProduct.map_tmul _ _ _ _

private def multiplicationProjection (R : TestAlgebra E) :
    (extendScalars F E).obj ((restrictTestAlgebra F E).obj R) ⟶ R := by
  let R₀ := (restrictTestAlgebra F E).obj R
  letI : Algebra F R := R₀.algebra
  letI : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq' rfl
  let p := Algebra.TensorProduct.lift (AlgHom.id F R) (IsScalarTower.toAlgHom F E R)
    (fun x y => Commute.all x _)
  let T := (extendScalars F E).obj R₀
  letI : Algebra E T := T.algebra
  exact ConcreteCategory.ofHom (C := CommAlgCat E)
    ({ p.toRingHom with
       commutes' := fun a => by
         change p (1 ⊗ₜ[F] a) = algebraMap E R a
         simp [p] } : T →ₐ[E] R)

private theorem multiplicationProjection_tmul (R : TestAlgebra E)
    (r : (restrictTestAlgebra F E).obj R) (a : E) :
    (multiplicationProjection (F := F) R).hom
        (show ((extendScalars F E).obj ((restrictTestAlgebra F E).obj R)) from r ⊗ₜ[F] a) =
      r * algebraMap E R a := by
  letI : Algebra F R := ((restrictTestAlgebra F E).obj R).algebra
  letI : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq' rfl
  change (Algebra.TensorProduct.lift (AlgHom.id F R) (IsScalarTower.toAlgHom F E R)
    (fun x _ => Commute.all x _)) (r ⊗ₜ[F] a) = _
  simp

private def fieldAlgebraMap (R : TestAlgebra E) :
    CommAlgCat.of F F ⟶ (restrictTestAlgebra F E).obj R := by
  let T := (restrictTestAlgebra F E).obj R
  letI : Algebra F T := T.algebra
  exact ConcreteCategory.ofHom (C := CommAlgCat F) (Algebra.ofId F T)

private def extensionAlgebraMap (R : TestAlgebra E) : CommAlgCat.of E E ⟶ R :=
  CommAlgCat.ofHom (Algebra.ofId _ _)

private theorem multiplicationProjection_fieldAlgebraMap (R : TestAlgebra E) :
    (extendScalars F E).map (fieldAlgebraMap (F := F) R) ≫ multiplicationProjection R =
      (scalarExtensionOfGroundField (F := F) E).hom ≫ extensionAlgebraMap R := by
  apply CommAlgCat.hom_ext
  let T := (extendScalars F E).obj (CommAlgCat.of F F)
  letI : Algebra E T := T.algebra
  apply AlgHom.toRingHom_injective
  apply RingHom.ext
  intro z
  change F ⊗[F] E at z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a b =>
    simp only [AlgHom.coe_toRingHom, CommAlgCat.hom_comp, AlgHom.comp_apply]
    change (multiplicationProjection R).hom
        (Algebra.TensorProduct.map (Algebra.ofId F ((restrictTestAlgebra F E).obj R))
          (AlgHom.id F E) (a ⊗ₜ[F] b)) =
      algebraMap E R (Algebra.TensorProduct.lid F E (a ⊗ₜ[F] b))
    rw [Algebra.TensorProduct.map_tmul]
    rw [multiplicationProjection_tmul, Algebra.TensorProduct.lid_tmul, Algebra.smul_def, map_mul]
    rfl

private theorem diagonalUnits_projection (R : TestAlgebra E) (t : Rˣ) :
    ((multiplicativePoints E).map (multiplicationProjection (F := F) R))
      ((diagonalUnits F E).app ((restrictTestAlgebra F E).obj R) t) = t := by
  apply Units.ext
  let r : (restrictTestAlgebra F E).obj R := (t : R)
  change (multiplicationProjection R).hom (r ⊗ₜ[F] (1 : E)) = r
  rw [multiplicationProjection_tmul, map_one, mul_one]

/-- A cocharacter of an E-group gives a cocharacter of its Weil restriction.
Noncentrality against an E-rational point is detected over the same field by
the multiplication projection, also for a nonnormal extension. -/
theorem weilRestriction_noncentralCocharacter {H : GroupScheme E} {W : GroupScheme F}
    (e : (groupPointsFunctor F).obj W ≅ extendScalars F E ⋙ (groupPointsFunctor E).obj H)
    (c : multiplicativePoints E ⟶ (groupPointsFunctor E).obj H)
    (R : TestAlgebra E) (t : Rˣ) (g : Points H.X (CommAlgCat.of E E))
    (h : ¬ Commute (c.app R t : Points H.X R) (mapPoints (extensionAlgebraMap R) g)) :
    ∃ (a : Cocharacter W) (X : SchemeOver F) (x : X ⟶ W.X), ¬ Centralizes a x := by
  let M := specGroup (groupAlgebra F IntegerCharacters)
  let m := DiagonalizableGroups.groupAlgebraPointsIso F IntegerCharacters ≪≫ integerPointsIso
  let d := m.hom ≫ diagonalUnits F E ≫ Functor.whiskerLeft (extendScalars F E) c ≫ e.inv
  have hM : IsAffine M.X.left := by
    change IsAffine (Spec (CommRingCat.of (groupAlgebra F IntegerCharacters)))
    infer_instance
  let a := (groupHomEquiv M W hM).symm d
  have ha : (groupPointsFunctor F).map a = d :=
    (groupHomEquiv M W hM).apply_symm_apply d
  let U := (restrictTestAlgebra F E).obj R
  let t₀ := m.inv.app U t
  let p := multiplicationProjection (F := F) R
  let x := (weilFieldPointIso e).inv g
  let f := fieldAlgebraMap (F := F) R
  refine ⟨a, _, x, fun hx => h ?_⟩
  have hcomm := (centralizes_iff a x).mp hx ((testSpec F).obj (Opposite.op U))
    ((testSpec F).map f.op) t₀
  change Commute (mapPoints f x) (t₀ ≫ a.hom.hom) at hcomm
  have he := hcomm.symm.map ((e.hom.app U).hom)
  have hp := he.map ((((groupPointsFunctor E).obj H).map p).hom)
  have ht : e.hom.app U (t₀ ≫ a.hom.hom) =
      c.app ((extendScalars F E).obj U) ((diagonalUnits F E).app U t) := by
    have heq := ConcreteCategory.congr_hom (NatTrans.congr_app ha U) t₀
    change t₀ ≫ a.hom.hom =
      e.inv.app U (c.app _ ((diagonalUnits F E).app U (m.hom.app U t₀))) at heq
    rw [heq]
    have he₀ := (m.app U).groupIsoToMulEquiv.apply_symm_apply t
    change m.hom.app U t₀ = t at he₀
    rw [he₀]
    exact (e.app U).groupIsoToMulEquiv.apply_symm_apply _
  change Commute (((groupPointsFunctor E).obj H).map p (e.hom.app U (t₀ ≫ a.hom.hom)))
    (((groupPointsFunctor E).obj H).map p (e.hom.app U (mapPoints f x))) at hp
  rw [ht] at hp
  have hc := ConcreteCategory.congr_hom (c.naturality p) ((diagonalUnits F E).app U t)
  change c.app R (((multiplicativePoints E).map p) ((diagonalUnits F E).app U t)) =
    ((groupPointsFunctor E).obj H).map p
        (c.app ((extendScalars F E).obj U) ((diagonalUnits F E).app U t)) at hc
  rw [← hc, diagonalUnits_projection] at hp
  have hg := ConcreteCategory.congr_hom (e.hom.naturality f) x
  change e.hom.app U (mapPoints f x) =
    ((groupPointsFunctor E).obj H).map ((extendScalars F E).map f) (e.hom.app _ x) at hg
  rw [hg] at hp
  have hmap := ConcreteCategory.congr_hom
    (((groupPointsFunctor E).obj H).map_comp ((extendScalars F E).map f) p)
    (e.hom.app _ x)
  change ((groupPointsFunctor E).obj H).map ((extendScalars F E).map f ≫ p) (e.hom.app _ x) =
    ((groupPointsFunctor E).obj H).map p
      (((groupPointsFunctor E).obj H).map ((extendScalars F E).map f) (e.hom.app _ x)) at hmap
  rw [← hmap, multiplicationProjection_fieldAlgebraMap] at hp
  have hg' : ((groupPointsFunctor E).obj H).map
      ((scalarExtensionOfGroundField (F := F) E).hom ≫ extensionAlgebraMap R)
      (e.hom.app _ x) = mapPoints (extensionAlgebraMap R) g := by
    rw [Functor.map_comp]
    have hx : ((groupPointsFunctor E).obj H).map
        (scalarExtensionOfGroundField (F := F) E).hom (e.hom.app _ x) = g :=
      (weilFieldPointIso e).groupIsoToMulEquiv.apply_symm_apply g
    change mapPoints (extensionAlgebraMap R)
      (((groupPointsFunctor E).obj H).map (scalarExtensionOfGroundField E).hom
        (e.hom.app _ x)) = _
    rw [hx]
  rwa [hg'] at hp

end WeilCocharacters

section DivisionLevi

open scoped TensorProduct
open _root_.Specs.RM03.CSA (isCentralSimple)
open RM03.CSA (degree BaseChange)
open Specs.StandardGroups (additivePoints)
open private matrixOne from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting

/-- A central simple algebra of degree two either is split over the ground field
or has division scalar extension along any finite extension of odd degree. -/
theorem degreeTwoCSA_split_or_oddBaseChange_division {A : Type u} [Ring A] [Algebra F A]
    [Module.Finite F E] (hA : isCentralSimple F A) (hd : degree F A = 2)
    (he : Odd (Module.finrank F E)) :
    Nonempty (A ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) ∨
      Nontrivial (BaseChange F E A) ∧ ∀ x : BaseChange F E A, x ≠ 0 → IsUnit x := by
  obtain ⟨n, B, _, _, hB, hn, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation F A hA
  have hB' := RM03.CSA.isCentralSimple_of_isCentralDivision F B hB
  have hdeg := RM03.CSA.degree_matrix_division hA hB hn e
  change RM03.CSA.degree F A = 2 at hd
  rw [hd] at hdeg
  have hpos := RM03.CSA.degree_pos hB'
  have hnle : n ≤ 2 := by nlinarith
  by_cases hn₁ : n = 1
  · subst n
    have hdB : degree F B = 2 := by simpa using hdeg.symm
    obtain ⟨hnB, hunit⟩ := LocalQuadraticSplitting.odd_extension_division hB hdB he
    let e' : BaseChange F E A ≃ₐ[E] BaseChange F E B :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E) (e.trans matrixOne)
    exact Or.inr ⟨e'.symm.injective.nontrivial, fun x hx => by
      simpa using (hunit (e' x) (fun h => hx (e'.injective (h.trans e'.map_zero.symm)))).map
        e'.symm.toMonoidHom⟩
  · have hn₂ : n = 2 := by omega
    subst n
    have hdB : RM03.CSA.degree F B = 1 := by omega
    have hb : Module.finrank F B = 1 := by
      simpa [hdB] using RM03.CSA.finrank_eq_degree_sq hB'
    obtain ⟨b⟩ := (Module.nonempty_algEquiv_iff_finrank_eq_one (R := F) (S := B)).mpr hb
    exact Or.inl ⟨e.trans (b.symm.mapMatrix (m := Fin 2))⟩

/-- A group functor represented faithfully in a division algebra's units has
no nontrivial additive one-parameter subgroup. At the universal parameter
the image is a polynomial unit, hence constant. -/
theorem additiveHom_trivial_of_division
    {A : Type u} [Ring A] [Algebra F A] [Nontrivial A]
    (hA : ∀ x : A, x ≠ 0 → IsUnit x)
    (H : TestAlgebra F ⥤ GrpCat.{u})
    (v : ∀ R : TestAlgebra F, H.obj R →* (R ⊗[F] A))
    (hv : ∀ R, Function.Injective (v R))
    (hn : ∀ {R T : TestAlgebra F} (f : R ⟶ T) (x : H.obj R),
      v T (H.map f x) = Algebra.TensorProduct.map f.hom (AlgHom.id F A) (v R x))
    (c : additivePoints F ⟶ H) (R : TestAlgebra F) (r : R) :
    c.app R (Multiplicative.ofAdd r) = 1 := by
  letI : NoZeroDivisors A := ⟨fun {x y} h => or_iff_not_imp_left.mpr (fun hx => by
    obtain ⟨a, rfl⟩ := hA x hx
    exact (Units.mul_right_inj a).mp (h.trans (mul_zero _).symm))⟩
  let P := CommAlgCat.of F (Polynomial F)
  let X : (additivePoints F).obj P := Multiplicative.ofAdd (Polynomial.X : Polynomial F)
  let x := v P (c.app P X)
  let e : P ⊗[F] A ≃ₐ[F] Polynomial A :=
    (Algebra.TensorProduct.comm F (Polynomial F) A).trans (polyEquivTensor F A).symm
  have hunit : IsUnit (e x) := ((Group.isUnit (c.app P X)).map (v P)).map e.toMonoidHom
  have hconst : x = (1 : P) ⊗ₜ[F] (e x).coeff 0 := by
    apply e.injective
    change e x = (polyEquivTensor F A).symm ((e x).coeff 0 ⊗ₜ[F] (1 : Polynomial F))
    rw [polyEquivTensor_symm_apply_tmul_eq_smul]
    simpa only [Polynomial.map_one, Polynomial.smul_eq_C_mul, mul_one] using
      Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hunit)
  have eval (t : R) : v R (c.app R (Multiplicative.ofAdd t)) =
      (1 : R) ⊗ₜ[F] (e x).coeff 0 := by
    let a : P ⟶ R := CommAlgCat.ofHom (Polynomial.aeval t)
    have ht : (additivePoints F).map a X =
        (Multiplicative.ofAdd t : (additivePoints F).obj R) :=
      congrArg Multiplicative.ofAdd (Polynomial.aeval_X t)
    have hc := ConcreteCategory.congr_hom (c.naturality a) X
    change c.app R ((additivePoints F).map a X) = H.map a (c.app P X) at hc
    change v R (c.app R (Multiplicative.ofAdd t : (additivePoints F).obj R)) = _
    rw [← ht, hc, hn]
    change Algebra.TensorProduct.map a.hom (AlgHom.id F A) x = _
    conv_lhs => rw [hconst]
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have hzero : Multiplicative.ofAdd (0 : R) = (1 : Multiplicative R) := rfl
  have hzero' : c.app R (Multiplicative.ofAdd (0 : R)) = 1 :=
    (congrArg (c.app R).hom hzero).trans ((c.app R).hom.map_one)
  exact (hv R) ((eval r).trans ((eval 0).symm.trans (congrArg (v R) hzero')))

end DivisionLevi

section Descent

open Specs.CharacterDescent (Cocharacter)
open Specs.QuasiSplitInducedWeilProduct (ProductDescent)
open Specs.Arithmetic.TrialitarianLeviDescent (QuasiSplitDescent)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.Descent.Forms (spectrumIso)
open TrialitarianAlbertDescentSpecification (cartanD4)
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private torus_of_empty_face from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OrthogonalDerivedLevi
open private subgroupIso_of_same from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag

/-- In a product indexed by a singleton, the projection is an isomorphism of
the actual group schemes. -/
private theorem singletonFactorIso {K I : Type u} [Field K] [Algebra F K]
    [Unique I] [MulAction Gal(K/F) I] (X : ProductDescent (F := F) (K := K) (I := I)) :
    Nonempty (specGroup X.total ≅ specGroup (X.factor default)) := by
  let p := X.projection default
  have hp (R : TestAlgebra K) : Function.Bijective
      (fun x : X.total →ₐ[K] R => x.comp p.hom.toAlgHom) :=
    (Equiv.piUnique (fun i => X.factor i →ₐ[K] R)).bijective.comp (X.product R)
  obtain ⟨s, hs⟩ := (hp (CommAlgCat.of K (X.factor default))).surjective (AlgHom.id K _)
  change s.comp p.hom.toAlgHom = AlgHom.id K (X.factor default) at hs
  have ht : p.hom.toAlgHom.comp s = AlgHom.id K X.total := by
    apply (hp (CommAlgCat.of K X.total)).injective
    change (p.hom.toAlgHom.comp s).comp p.hom.toAlgHom = (AlgHom.id K _).comp p.hom.toAlgHom
    rw [AlgHom.comp_assoc, hs, AlgHom.comp_id, AlgHom.id_comp]
  have hleft : Function.LeftInverse s p.hom := fun x => DFunLike.congr_fun hs x
  have hright : Function.RightInverse s p.hom := fun x => DFunLike.congr_fun ht x
  exact ⟨spectrumIso (CommHopfAlgCat.isoMk
    (BialgEquiv.ofBijective p.hom ⟨hleft.injective, hright.surjective⟩)).symm⟩

/-- A trialitarian form that is isotropic over the ground field and quasi-split
over its marked cubic diagram field is quasi-split over the ground field. -/
theorem quasiSplitDescent : QuasiSplitDescent.{u} := by
  classical
  intro F E S _ _ _ _ _ _ _ _ _ _ _ _ _ hdegree G D a ha hss _ hIsotropic hq
  have hG := reductive_of_semisimple G hss
  obtain ⟨c, Y, g, hg⟩ := hIsotropic
  obtain ⟨P, A, d, M, hP, hPproper, hA, hPM, _, hL, hC⟩ :=
    exists_properMinimalParabolicLevi hG hg
  obtain ⟨p, hp⟩ := subgroupIso_of_same hPM
  have hMproper : ¬ IsIso M.parabolic.inclusion := by
    intro h
    letI := h
    apply hPproper
    rw [← hp]
    infer_instance
  have hqL := baseChangedCentralizer_isQuasiSplit hq hA.1 hC hL
  have hno (H : ClosedSubgroup M.centralizer.group)
      (h : ∃ (c : Cocharacter H.group) (Y : SchemeOver F) (g : Y ⟶ H.group.X),
        ¬ Centralizes c g) : False := by
    obtain ⟨c, Y, g, hg⟩ := h
    exact noncentralCocharacter_inclusion H c g hg
      (minimalParabolicLevi_centralizes P hP M hPM hL (c ≫ H.inclusion) (g ≫ H.inclusion.hom.hom))
  obtain ⟨K₀, hK₀⟩ := exists_finiteGaloisContainingEmbeddings (F := F) (E := E) (S := S)
  obtain ⟨K, d₀, M₀, aK, pK, lK, iK, J, hK, hiK, hpK, hlK, hproper, hface, hstable, hcompat⟩ :=
    TrialitarianMarkedLevi.markedFace F S D.pinned D.datum D.autSequence G hG
      a D.form ha _ M K₀ hMproper
  let v (i : Fin 4) : D.datum.toBased.I := (D.roots i).val
  have hv : Function.Injective v := fun _ _ h => D.roots.injective (Subtype.ext h)
  have hvs : Set.range v = D.datum.toBased.base.support := by
    ext α
    constructor
    · rintro ⟨i, rfl⟩
      exact (D.roots i).property
    · intro hα
      exact ⟨D.roots.symm ⟨α, hα⟩, congrArg Subtype.val (D.roots.apply_symm_apply ⟨α, hα⟩)⟩
  let Jm := v ⁻¹' J
  have hJ : v '' Jm = J := Set.image_preimage_eq_of_subset (hvs.symm ▸ hproper.le)
  have hJproper : Jm ≠ Set.univ := by
    intro h
    apply hproper.ne
    rw [← hJ, h, Set.image_univ, hvs]
  have hJstable (σ : Gal(S/F)) (i : Fin 4) (hi : i ∈ Jm) : markedPermutation D σ i ∈ Jm := by
    change (D.roots (markedPermutation D σ i)).val ∈ J
    rw [markedPermutation_apply, ← hcompat σ, ← hstable (σ.restrictNormal K)]
    exact ⟨v i, hi, rfl⟩
  by_cases hEmptyMark : Jm = ∅
  · have hEmpty : J = ∅ := by rw [← hJ, hEmptyMark, Set.image_empty]
    have htor := torus_of_empty_face D.datum M M₀ lK (hEmpty ▸ hface)
    exact ⟨hG, M.parabolic, isKBorel_of_torusLevi hG M htor⟩
  have hne : Jm.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmptyMark
  rcases stableMarkedSubset D Jm hne hJproper hJstable with hcentral | houter
  · let I := PUnit.{u + 1}
    letI : MulAction Gal(K/F) I :=
      { smul := fun _ i => i
        one_smul := fun _ => rfl
        mul_smul := fun _ _ _ => rfl }
    let r : I ↪ D.datum.toBased.I :=
      ⟨fun _ => v 3, fun _ _ _ => Subsingleton.elim _ _⟩
    have hr : Set.range r = J := by
      rw [← hJ, hcentral, Set.image_singleton]
      exact Set.range_const
    have haction (τ : Gal(K/F)) (i : I) :
        (outerHom D.autSequence (transportedAut F K iK τ)).asIso.hom.val.indexEquiv (r i) =
          r (τ • i) := by
      obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective S (F := F) (K₁ := K) τ
      change σ.restrictNormal K = τ at hσ
      change _ = (D.roots 3).val
      rw [← hσ, hcompat σ]
      exact (markedPermutation_apply D σ 3).symm.trans
        (congrArg v (markedPermutation_central D σ))
    obtain ⟨H, X, j, t, _, _, hsplit, _, hqH, _⟩ :=
      OrthogonalDerivedLevi.derivedFactors F K I D.pinned D.datum D.autSequence
        D.semisimple D.simplyConnected G _ M hL d₀ M₀ aK pK lK iK hiK hpK hlK r
        (hr.symm ▸ hproper.le) (hr.symm ▸ hface)
        (fun i j h => (h (Subsingleton.elim i j)).elim) haction
    obtain ⟨s⟩ := hsplit (default : I)
    obtain ⟨e₁⟩ := singletonFactorIso X
    let e := (groupBaseChange F K).mapIso j.symm ≪≫ (t X.descent.coordinate).symm ≪≫
      spectrumIso X.descent.comparison ≪≫ e₁
    have hodd : Odd (Module.finrank F E) := by rw [hdegree]; decide
    exact (hno H (RankOneOddDescent.rankOneDescent F E K hodd (closedSubgroupAlgebraicGroup H)
      ⟨(groupPointsFunctor K).mapIso e ≪≫ s⟩ (hqH E hqL))).elim
  · have hKall (e : E →ₐ[F] S) (x : E) : e x ∈ K.toIntermediateField := hK (hK₀ e x)
    let labels := finiteGaloisEmbeddings K hKall
    let vertices := labels.trans D.numbering
    let I := E →ₐ[F] K
    letI : MulAction Gal(K/F) I :=
      { smul := fun σ e => σ.toAlgHom.comp e
        one_smul := fun _ => AlgHom.ext fun _ => rfl
        mul_smul := fun _ _ _ => AlgHom.ext fun _ => rfl }
    let r : I ↪ D.datum.toBased.I :=
      ⟨fun e => v (vertices e).castSucc,
        fun _ _ h => vertices.injective (Fin.castSucc_injective _ (hv h))⟩
    have hr : Set.range r = J := by
      rw [← hJ, houter, ← Set.range_comp' v (fun i : Fin 3 => i.castSucc)]
      ext α
      constructor
      · rintro ⟨e, rfl⟩
        exact ⟨vertices e, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨vertices.symm i, congrArg (fun j : Fin 3 => v j.castSucc)
          (vertices.apply_symm_apply i)⟩
    have horth (e f : I) (hef : e ≠ f) :
        D.datum.toBased.datum.pairing (r e) (r f) = 0 := by
      change D.datum.toBased.datum.pairing (D.roots (vertices e).castSucc).val
        (D.roots (vertices f).castSucc).val = 0
      have hdistinct : (vertices e).castSucc ≠ (vertices f).castSucc :=
        fun h => hef (vertices.injective (Fin.castSucc_injective _ h))
      have hnotCentral : ¬ ((vertices e).castSucc = 3 ∨ (vertices f).castSucc = 3) :=
        not_or.mpr ⟨Fin.castSucc_ne_last (vertices e), Fin.castSucc_ne_last (vertices f)⟩
      rw [D.cartan, cartanD4, ite_eq_right hdistinct, ite_eq_right hnotCentral]
    have haction (τ : Gal(K/F)) (e : I) :
        (outerHom D.autSequence (transportedAut F K iK τ)).asIso.hom.val.indexEquiv (r e) =
          r (τ • e) := by
      obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective S (F := F) (K₁ := K) τ
      change σ.restrictNormal K = τ at hσ
      have he : labels (τ • e) = σ.toAlgHom.comp (labels e) :=
        hσ ▸ finiteGaloisEmbeddings_restriction K hKall σ e
      change _ = (D.roots (D.numbering (labels (τ • e))).castSucc).val
      rw [he, ← hσ, hcompat σ]
      exact D.diagramAction σ (labels e)
    obtain ⟨H, X, j, _, _, _, hsplit, _, hqH, _⟩ :=
      OrthogonalDerivedLevi.derivedFactors F K I D.pinned D.datum D.autSequence
        D.semisimple D.simplyConnected G _ M hL d₀ M₀ aK pK lK iK hiK hpK hlK r
        (hr.symm ▸ hproper.le) (hr.symm ▸ hface) horth haction
    letI : Infinite (WithZero (Multiplicative ℤ)) :=
      Infinite.of_injective (WithZero.exp : ℤ → WithZero (Multiplicative ℤ)) WithZero.exp_injective
    let vF := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
    letI : Infinite F := Infinite.of_surjective (vF ∘ ValuativeRel.valuation F)
      (vF.surjective.comp ValuativeRel.valuation_surjective)
    letI : Infinite E := Infinite.of_injective (algebraMap F E) (algebraMap F E).injective
    have hn := TransitiveLeviDescent.transitiveFactorDescent F E K I
      (Equiv.refl I) (labels.symm (IsScalarTower.toAlgHom F E S)) (fun _ _ => rfl)
      (closedSubgroupAlgebraicGroup H) X ⟨j⟩ hsplit (hqH E hqL)
    exact (hno H hn.2).elim

end Descent

end

end LinearAlgebraicGroups.Arithmetic.TrialitarianLeviDescent
