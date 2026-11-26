import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.MaximalSplitTori
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.LeviConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicIntersection
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalFlagLifting
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveFlags
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.SplitContractingRadical
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj BigOperators

universe u

namespace LinearAlgebraicGroups.Relative.MaximalSplitTori

open LinearAlgebraicGroups.Specs
open Specs.Relative.MaximalSplitTori
open Specs.BorelProper (IsParabolic)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups IsBorel subgroupOfSubgroup)
open Specs.GeometricRadicals (GeometricGroup IsReductive IsSplitTorus IsTorus IsUnipotentRadical identitySubgroup)
open Specs.RankOneFlag (SameSubgroup)
open Specs.SchemeDerivedGroup (IsSplitSolvable IsSubgroupOf)
open Specs.QuotientEmbedding (Presentation)
open Specs.TorsorObstruction (rationalCosetMap)
open Specs.Fppf (fieldBase)
open Specs.Unipotent (IsSplitUnipotent closedSubgroupAlgebraicGroup)
open Specs.StandardGroups (multiplicativePowerGroup multiplicativePowerPoints)
open Specs.BorelsAndChambers (contractingSubgroup IsRegular subgroupRoots positiveRoots)
open Specs.CharacterDescent (Cocharacter StandardLattice)
open Specs.DiagonalizableGroups (IntegerCharacters diagonalGroup groupAlgebra)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (absoluteRoots pairing)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition existsLimitDecomposition
  limitSubgroupsSmooth multiplyFactors oppositeCocharacter oppositeLimitIntersection)

open private subgroupQuotientAction fixed_subgroup_conjugate
  transportSubgroup borel_transport innerIso innerMap comp_innerMap descends geometricSmooth geometricConnected
  quotientMapExists subgroup_quotient_fiber subgroup_quotient_pullback quotientSeparatedFiniteType
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private factor_group_through_subgroup subgroupOf_trans subgroupOf_mutual_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

open private splitSolvable_of_splitTorusQuotient
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.BorelFixedPoint
open private SchemeDerivedGroup.kernel_normal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private quotientRepresentsImage
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private multiplicative_group_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.LeviConjugacy
open private preimageSubgroup preimageSquare smoothPreimage limitSmooth limitKernelUnderIso
  splitQuotientIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicIntersection
open private restrictSubgroup compose_restrict inclusion_mono subgroupOfSubgroup_le conjugates_in_ambient conjugates_trans
  exists_maximal_torus_over
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private subgroupIso_of_same extendSubgroup parabolic_of_cast limits_subgroups_extend
  opposite_opposite contracting_of_cast
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private exists_regular_cocharacter centralizer_of_regular regular_isBorel
  subgroupRoots_of_regular subgroupOf_limit_of_rootSigns reductive_geometricGroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private cocharacterImageIsTorus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open private geometricMaximal_of_maximal split_of_maximal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private pushSubgroup radical_transport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private definingIdeal definingIdeal_le factor_iso_of_definingIdeal_eq
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private compareRepresentatives from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private gm_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private split_preimage_quotient from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SimpleParabolicProduct
open private centralizes_split_power exists_coordinateCocharacter centralizes_precomp_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private latticeEquivOfBasis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
open private centralizes_iff comp_conjugateFamily
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private conjugates_inverse from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]
variable {G : AffineAlgebraicGroup k}

private theorem properParabolicQuotient (G : AffineAlgebraicGroup k)
    (P : ClosedSubgroup G.val) (hP : IsParabolic G P) :
    ∃ Q : Presentation P, IsProper Q.scheme.hom := by
  obtain ⟨⟨Q⟩, hQ⟩ := ProjectiveFlags.smoothProjectiveQuotient k G P hP
  exact ⟨Q, (hQ Q).2.1⟩

/-- A split solvable subgroup is rationally conjugate into any parabolic.
The conjugation condition concerns the subgroup scheme over the field. -/
private theorem splitSolvableConjugateInto
    (P : ClosedSubgroup G.val) (hP : IsParabolic G P)
    (H : ClosedSubgroup G.val) (hH : IsSplitSolvable H.group) :
    ∃ g : 𝟙_ (SchemeOver k) ⟶ G.val.X, IsSubgroupOf (transportSubgroup H (innerIso g)) P := by
  obtain ⟨Q, hQ⟩ := properParabolicQuotient G P hP
  let b := subgroupQuotientAction (B := H) Q
  obtain ⟨Z, i, _, hi, ⟨z⟩⟩ := splitSolvableFixedPoint
    (closedSubgroupAlgebraicGroup H) Q.scheme b hH hQ
    ⟨(1 : 𝟙_ (SchemeOver k) ⟶ G.val.X) ≫ Q.projection⟩
  let x : fieldBase k ⟶ Q.scheme := z ≫ i
  let ηQ := Q.quotientIso.hom.hom.app (Opposite.op (fieldBase k))
  have ηQ_bijective := ConcreteCategory.bijective_of_isIso ηQ
  obtain ⟨s, hs⟩ := ηQ_bijective.2 (ULift.up x)
  obtain ⟨a, ha⟩ := (Relative.RationalFlagLifting.rationalFlagLifting G P hP).2 s
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  have he : ηQ (rationalCosetMap P (QuotientGroup.mk g)) =
      ULift.up (g ≫ Q.projection) :=
    congrArg (fun m ↦ m.hom.app (Opposite.op (fieldBase k)) (ULift.up g))
      Q.quotientProjection
  have hg : g ≫ Q.projection = z ≫ i :=
    ULift.up.inj (he.symm.trans ((congrArg ηQ ha).trans hs))
  have hz : IsFixedBy b.smul (g ≫ Q.projection) := by
    rw [hg]
    exact (hi _ _).2 ⟨z, rfl⟩
  obtain ⟨f, hf⟩ := fixed_subgroup_conjugate Q g hz
  refine ⟨g⁻¹, factor_group_through_subgroup P
    (transportSubgroup H (innerIso g⁻¹)).inclusion f ?_⟩
  change f ≫ P.inclusion.hom.hom = H.inclusion.hom.hom ≫ (innerMap g⁻¹).hom.hom
  rw [comp_innerMap, GrpObj.comp_inv, inv_inv]
  exact hf

private theorem transportBorelWitness {K : Type u} [Field K]
    {A : GroupScheme k} (F : GroupScheme k ⥤ GroupScheme K)
    (P : ClosedSubgroup A) (e : A ≅ A)
    (hclosed : IsClosedImmersion (F.map P.inclusion).hom.hom.left)
    (B : ClosedSubgroup (F.obj A)) (hB : IsBorel B)
    (j : B.group ⟶ F.obj P.group) (hj : j ≫ F.map P.inclusion = B.inclusion) :
    ∃ (_ : IsClosedImmersion (F.map (transportSubgroup P e).inclusion).hom.hom.left)
      (B' : ClosedSubgroup (F.obj A)), IsBorel B' ∧
      ∃ j' : B'.group ⟶ F.obj P.group,
        j' ≫ F.map (transportSubgroup P e).inclusion = B'.inclusion := by
  let E := F.mapIso e
  have hR : IsClosedImmersion (F.map (transportSubgroup P e).inclusion).hom.hom.left := by
    let := hclosed
    let : IsIso E.hom.hom.hom.left :=
      ((Grp.forget (SchemeOver K)) ⋙ Over.forget _).map_isIso E.hom
    change IsClosedImmersion (F.map (P.inclusion ≫ e.hom)).hom.hom.left
    rw [F.map_comp]
    exact IsClosedImmersion.comp (F.map P.inclusion).hom.hom.left E.hom.hom.hom.left
  refine ⟨hR, transportSubgroup B E, borel_transport hB E, j, ?_⟩
  change j ≫ F.map (P.inclusion ≫ e.hom) = B.inclusion ≫ F.map e.hom
  rw [F.map_comp, ← Category.assoc, hj]

/-- Conjugation preserves the smoothness and geometric Borel condition. -/
private theorem parabolicTransport {P : ClosedSubgroup G.val} (hP : IsParabolic G P)
    (e : G.val ≅ G.val) : IsParabolic G (transportSubgroup P e) := by
  obtain ⟨hclosed, B, hB, j, hj⟩ := hP.2.2
  refine ⟨hP.1, hP.2.1, ?_⟩
  exact transportBorelWitness (groupBaseChange k (AlgebraicClosure k)) P e hclosed B hB j hj

private theorem transportSubgroupOf
    {K : GroupScheme k} {A B : ClosedSubgroup K} (h : IsSubgroupOf A B) (e : K ≅ K) :
    IsSubgroupOf (transportSubgroup A e) (transportSubgroup B e) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, by change a ≫ B.inclusion ≫ e.hom = A.inclusion ≫ e.hom
               rw [← Category.assoc, ha]⟩

private theorem transportSubgroupCancel {K : GroupScheme k} (P : ClosedSubgroup K) (e : K ≅ K) :
    transportSubgroup (transportSubgroup P e) e.symm = P := by
  cases P
  simp only [transportSubgroup, Iso.symm_hom, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem minimalParabolicTransport {P : ClosedSubgroup G.val}
    (hP : IsMinimalParabolic G P) (e : G.val ≅ G.val) :
    IsMinimalParabolic G (transportSubgroup P e) := by
  refine ⟨parabolicTransport hP.1 e, ?_⟩
  intro Q hQ hQP
  have h := transportSubgroupOf hQP e.symm
  rw [transportSubgroupCancel] at h
  have h' := transportSubgroupOf (hP.2 _ (parabolicTransport hQ e.symm) h) e
  have he : transportSubgroup (transportSubgroup Q e.symm) e = Q := by
    exact transportSubgroupCancel Q e.symm
  rwa [he] at h'

private theorem conjugates_of_sameTransport {K : GroupScheme k} {A B : ClosedSubgroup K}
    (g : 𝟙_ (SchemeOver k) ⟶ K.X)
    (h : SameSubgroup (transportSubgroup A (innerIso g)) B) : ConjugatesSubgroups g A B := by
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso h.1 h.2
  refine ⟨e, ?_⟩
  rw [he]
  change A.inclusion.hom.hom ≫ (innerMap g).hom.hom = _
  exact comp_innerMap g _

/-- An isomorphism on the underlying schemes of a group homomorphism gives
an isomorphism of group schemes with the prescribed forward map. -/
private def groupIsoOfUnderlyingIso {A B : GroupScheme k}
    (f : A ⟶ B) [IsIso f.hom.hom] : A ≅ B :=
  Grp.mkIso (asIso f.hom.hom) (IsMonHom.one_hom f.hom.hom) (IsMonHom.mul_hom f.hom.hom)

private theorem trivialIdentityKernel (A : AffineAlgebraicGroup k) :
    IsSchemeKernel (𝟙 A.val) (identitySubgroup A) := by
  change IsPullback η[A.val.X] (toUnit (𝟙_ (SchemeOver k))) (𝟙 A.val.X) η[A.val.X]
  rw [show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from Subsingleton.elim _ _]
  exact IsPullback.of_id_snd

private theorem splitTorusSplitSolvable (A : AffineAlgebraicGroup k) (h : IsSplitTorus A.val) :
    IsSplitSolvable A.val :=
  splitSolvable_of_splitTorusQuotient (identitySubgroup A) (𝟙 A.val)
    (trivialIdentityKernel A) h (𝟙 A.val) (Category.id_comp _) (fun _ e ↦ .trivial ⟨e⟩)

private theorem splitUnipotentSplitSolvable (A : AffineAlgebraicGroup k)
    (h : IsSplitUnipotent A) : IsSplitSolvable A.val := by
  obtain ⟨_, n, S, hS⟩ := h
  have hs (i : ℕ) (hi : i ≤ n) :
      ∀ L : AffineAlgebraicGroup k, (L.val ≅ (S.term i).val) → IsSplitSolvable L.val := by
    induction hi using Nat.decreasingInduction with
    | self =>
      intro L e
      exact .trivial ⟨e ≪≫ S.bottom⟩
    | of_succ i hi ih =>
      intro L e
      obtain ⟨Q, q, hq, hfactor⟩ := hS i hi
      let F := Grp.forget (SchemeOver k)
      let E := F ⋙ Over.forget (Spec (CommRingCat.of k))
      let j := S.step i ≫ e.inv
      let p := e.hom ≫ q
      have : IsIso e.hom.hom.hom.left := E.map_isIso e.hom
      have : IsIso e.inv.hom.hom.left := E.map_isIso e.inv
      have hj : IsClosedImmersion j.hom.hom.left := by
        letI := S.closed i
        change IsClosedImmersion ((S.step i).hom.hom.left ≫ e.inv.hom.hom.left)
        infer_instance
      let N : ClosedSubgroup L.val := ⟨_, j, hj⟩
      have hk : IsSchemeKernel p N := by
        change IsPullback j.hom.hom (toUnit (S.term (i + 1)).val.X) p.hom.hom η[Q.val.X]
        apply hq.1.of_iso' (Iso.refl _) (F.mapIso e) (Iso.refl _) (Iso.refl _)
        · change 𝟙 _ ≫ (S.step i).hom.hom = F.map (j ≫ e.hom)
          rw [Category.id_comp, show j ≫ e.hom = S.step i by simp [j]]
          rfl
        · simp
        · change F.map p = F.map p ≫ 𝟙 _
          simp
        · exact (Category.id_comp _).trans (Category.comp_id _).symm
      rcases hfactor with ht | hGa
      · obtain ⟨et⟩ := ht
        let hterm : IsTerminal Q.val.X :=
          isTerminalTensorUnit.ofIso (F.mapIso et).symm
        haveI : IsIso η[Q.val.X] := isIso_of_isTerminal isTerminalTensorUnit hterm _
        haveI : IsIso j.hom.hom := hk.isIso_fst_of_isIso
        exact ih L (groupIsoOfUnderlyingIso j).symm
      · letI := hq.2.1
        letI := hq.2.2.1
        letI := hq.2.2.2.1
        letI := L.property.1
        letI := Q.property.1
        have hp : IsImageFactorization p p (𝟙 Q.val) := by
          refine ⟨Category.comp_id _, ?_, ?_, ?_, inferInstance, ?_⟩
          · change Flat (e.hom.hom.hom.left ≫ q.hom.hom.left)
            infer_instance
          · change Surjective (e.hom.hom.hom.left ≫ q.hom.hom.left)
            infer_instance
          · change LocallyOfFinitePresentation (e.hom.hom.hom.left ≫ q.hom.hom.left)
            infer_instance
          · change IsClosedImmersion (𝟙 Q.val.X.left)
            infer_instance
        exact .step N (SchemeDerivedGroup.kernel_normal hk) (ih _ (Iso.refl _)) Q p
          (quotientRepresentsImage hp hk) (Or.inl hGa)
  exact hs 0 (Nat.zero_le n) A S.top.symm

/-- In the limit decomposition, membership in a subgroup containing the
contracting kernel is determined by membership of the limit section. -/
private theorem limitSectionMemIff {c : CharacterDescent.Cocharacter G.val}
    (D : LimitDecomposition c) {A : ClosedSubgroup G.val}
    (hU : IsSubgroupOf D.contracting A) {X : SchemeOver k} (x : X ⟶ D.parabolic.group.X) :
    x ≫ D.parabolic.inclusion.hom.hom ∈ SubgroupSections A X ↔
      x ≫ (D.limit ≫ D.centralizer.inclusion).hom.hom ∈ SubgroupSections A X := by
  let l : X ⟶ D.parabolic.group.X := x ≫ (D.limit ≫ D.sectionMap).hom.hom
  let d := l⁻¹ * x
  have hl : l ≫ D.limit.hom.hom = x ≫ D.limit.hom.hom := by
    change (x ≫ (D.limit ≫ D.sectionMap).hom.hom) ≫ D.limit.hom.hom = _
    rw [Category.assoc]
    change x ≫ ((D.limit ≫ D.sectionMap) ≫ D.limit).hom.hom = _
    rw [Category.assoc, D.section_limit, Category.comp_id]
  have hd : d ≫ D.limit.hom.hom = 1 := by
    simp only [d, MonObj.mul_comp, GrpObj.inv_comp, hl, inv_mul_cancel]
  obtain ⟨u, hu, _⟩ := D.isKernel.exists_lift d (toUnit X)
    (show d ≫ D.limit.hom.hom = toUnit X ≫ η[D.centralizer.group.X] from hd)
  obtain ⟨uA, huA⟩ := hU
  have hdA : d ≫ D.parabolic.inclusion.hom.hom ∈ SubgroupSections A X := by
    refine ⟨u ≫ uA.hom.hom, ?_⟩
    have huA' := (Grp.forget (SchemeOver k)).congr_map huA
    have huG := (Grp.forget (SchemeOver k)).congr_map D.contracting_in_G
    change (u ≫ uA.hom.hom) ≫ A.inclusion.hom.hom = d ≫ D.parabolic.inclusion.hom.hom
    rw [Category.assoc, show uA.hom.hom ≫ A.inclusion.hom.hom = D.contracting.inclusion.hom.hom
      from huA', ← show D.contractingToParabolic.hom.hom ≫ D.parabolic.inclusion.hom.hom =
        D.contracting.inclusion.hom.hom from huG, ← Category.assoc, hu]
  have hlG : l ≫ D.parabolic.inclusion.hom.hom =
      x ≫ (D.limit ≫ D.centralizer.inclusion).hom.hom := by
    change (x ≫ (D.limit ≫ D.sectionMap).hom.hom) ≫ D.parabolic.inclusion.hom.hom = _
    rw [Category.assoc]
    change x ≫ ((D.limit ≫ D.sectionMap) ≫ D.parabolic.inclusion).hom.hom = _
    rw [Category.assoc, D.section_in_G]
  rw [← hlG]
  constructor
  · intro hx
    have he : x * d⁻¹ = l := by dsimp only [d]; group
    have hm := (SubgroupSections A X).mul_mem hx ((SubgroupSections A X).inv_mem hdA)
    rwa [← GrpObj.inv_comp, ← MonObj.mul_comp, he] at hm
  · intro hx
    have he : l * d = x := by dsimp only [d]; group
    have hm := (SubgroupSections A X).mul_mem hx hdA
    rwa [← MonObj.mul_comp, he] at hm

/-- If the radical is contained in the second parabolic, minimality says that
the intersection contains the whole first parabolic. -/
private theorem minimalParabolicContained
    (P A : ClosedSubgroup G.val) (hP : IsMinimalParabolic G P) (hA : IsParabolic G A)
    (D₀c : CharacterDescent.Cocharacter G.val) (D₀ : LimitDecomposition D₀c)
    (e₀ : P.group ≅ D₀.parabolic.group) (he₀ : e₀.hom ≫ D₀.parabolic.inclusion = P.inclusion)
    (hD₀rad : StandardParabolicLevi.IsContractingRadical D₀)
    (hU₀ : IsSubgroupOf D₀.contracting A) :
    IsSubgroupOf P A := by
  obtain ⟨H, a, c, D, e, hH, ha, he, hRad, rest⟩ :=
    Relative.ParabolicIntersection.intersectionProjection G P A hP.1 hA
  obtain ⟨I, p, J, q, _, hp, _, hPb, hJ, _⟩ := rest
  let V := pushSubgroup e.symm (contractingSubgroup D)
  let V₀ := pushSubgroup e₀.symm (contractingSubgroup D₀)
  let P' := closedSubgroupAlgebraicGroup P
  have hV : IsUnipotentRadical P' V :=
    radical_transport (A := closedSubgroupAlgebraicGroup D.parabolic) (B := P')
      e.symm (contractingSubgroup D) hRad.1
  have hV₀ : IsUnipotentRadical P' V₀ :=
    radical_transport (A := closedSubgroupAlgebraicGroup D₀.parabolic) (B := P')
      e₀.symm (contractingSubgroup D₀) hD₀rad.1
  obtain ⟨v, hv⟩ := hV₀.2.2 V hV.1 hV.2.1
  have hVinc : V.inclusion ≫ P.inclusion = D.contracting.inclusion := by
    change (D.contractingToParabolic ≫ e.inv) ≫ P.inclusion = _
    rw [Category.assoc, ← he, e.inv_hom_id_assoc, D.contracting_in_G]
  have hV₀inc : V₀.inclusion ≫ P.inclusion = D₀.contracting.inclusion := by
    change (D₀.contractingToParabolic ≫ e₀.inv) ≫ P.inclusion = _
    rw [Category.assoc, ← he₀, e₀.inv_hom_id_assoc, D₀.contracting_in_G]
  have hU : IsSubgroupOf D.contracting A := by
    obtain ⟨b, hb⟩ := hU₀
    exact ⟨v ≫ b, by rw [Category.assoc, hb, ← hV₀inc, ← Category.assoc, hv, hVinc]⟩
  let JP := subgroupOfSubgroup P J
  obtain ⟨w, hw⟩ := hP.2 JP hJ ⟨J.inclusion, rfl⟩
  change P.group ⟶ J.group at w
  have hw' : w ≫ J.inclusion = 𝟙 P.group := by
    haveI := inclusion_mono P
    apply (cancel_mono P.inclusion).mp
    rw [Category.id_comp, Category.assoc]
    exact hw
  have hs : (w ≫ q) ≫ I.inclusion = e.hom ≫ D.limit := by
    apply Grp.hom_ext
    have h := congrArg (w.hom.hom ≫ ·) hPb.w
    rw [← Category.assoc] at h
    have hw'' := (Grp.forget (SchemeOver k)).congr_map hw'
    change w.hom.hom ≫ J.inclusion.hom.hom = 𝟙 P.group.X at hw''
    rw [hw'', Category.id_comp, ← Category.assoc] at h
    exact h.symm
  have hself : H.inclusion.hom.hom ∈ SubgroupSections H H.group.X := by
    refine ⟨𝟙 H.group.X, ?_⟩
    change 𝟙 H.group.X ≫ H.inclusion.hom.hom = H.inclusion.hom.hom
    exact Category.id_comp _
  have hh : H.inclusion.hom.hom ∈ SubgroupSections A H.group.X :=
    (hH _ _).1 hself A (by simp)
  have heH : (a ≫ e.hom ≫ D.parabolic.inclusion).hom.hom = H.inclusion.hom.hom := by
    rw [he, ha]
  obtain ⟨f, hf⟩ := (limitSectionMemIff D hU (a ≫ e.hom).hom.hom).1
    (show (a ≫ e.hom ≫ D.parabolic.inclusion).hom.hom ∈ SubgroupSections A H.group.X
      from heH.symm ▸ hh)
  have hpA : f ≫ A.inclusion.hom.hom = p.hom.hom ≫
      (I.inclusion ≫ D.centralizer.inclusion).hom.hom := by
    change f ≫ A.inclusion.hom.hom =
      ((p ≫ I.inclusion) ≫ D.centralizer.inclusion).hom.hom
    rw [hp.1]
    exact hf
  letI := hp.2.1
  letI := hp.2.2.1
  letI := hp.2.2.2.1
  letI := A.isClosedImmersion
  haveI : Mono A.inclusion.hom.hom := Over.mono_of_mono_left _
  obtain ⟨j, hj⟩ := descends p.hom.hom f (fun X y z hyz ↦ by
    apply (cancel_mono A.inclusion.hom.hom).mp
    simp only [Category.assoc, hpA, ← Category.assoc y p.hom.hom, hyz])
  have hji : j ≫ A.inclusion.hom.hom = (I.inclusion ≫ D.centralizer.inclusion).hom.hom := by
    haveI : Epi p.hom.hom := Over.epi_of_epi_left _
    apply (cancel_epi p.hom.hom).mp
    rw [← Category.assoc, hj, hpA]
  have htA : e.hom.hom.hom ≫ (D.limit ≫ D.centralizer.inclusion).hom.hom ∈
      SubgroupSections A P.group.X := by
    refine ⟨(w ≫ q).hom.hom ≫ j, ?_⟩
    change ((w ≫ q).hom.hom ≫ j) ≫ A.inclusion.hom.hom =
      e.hom.hom.hom ≫ (D.limit ≫ D.centralizer.inclusion).hom.hom
    rw [Category.assoc, hji]
    change (((w ≫ q) ≫ I.inclusion) ≫ D.centralizer.inclusion).hom.hom = _
    rw [hs, Category.assoc]
    rfl
  have hxA := (limitSectionMemIff D hU e.hom.hom.hom).2 htA
  change (e.hom ≫ D.parabolic.inclusion).hom.hom ∈ SubgroupSections A P.group.X at hxA
  rw [he] at hxA
  obtain ⟨m, hm⟩ := hxA
  exact factor_group_through_subgroup A P.inclusion m hm

/-- The minimal parabolics are conjugate under the ground-field points. -/
theorem minimalParabolicsConjugate : MinimalParabolicsConjugate.{u} := by
  intro k _ G P Q hP hQ
  obtain ⟨c, D, hPD, hRad, hSplit⟩ :=
    SplitContractingRadical.parabolicSplitRadical G P hP.1
  obtain ⟨e, he⟩ := subgroupIso_of_same hPD
  obtain ⟨g, hU⟩ := splitSolvableConjugateInto Q hQ.1 D.contracting
    (splitUnipotentSplitSolvable (closedSubgroupAlgebraicGroup D.contracting) hSplit)
  let E := innerIso g
  let R := transportSubgroup Q E.symm
  have hR := minimalParabolicTransport hQ E.symm
  have hUR : IsSubgroupOf D.contracting R := by
    have h := transportSubgroupOf hU E.symm
    rwa [transportSubgroupCancel] at h
  have hPR := minimalParabolicContained P R hP hR.1 c D e he hRad hUR
  have hRP := hR.2 P hP.1 hPR
  refine ⟨g, conjugates_of_sameTransport g ⟨?_, ?_⟩⟩
  · have h := transportSubgroupOf hPR E
    have hcancel : transportSubgroup R E = Q := by
      exact transportSubgroupCancel Q E.symm
    rwa [hcancel] at h
  · have h := transportSubgroupOf hRP E
    have hcancel : transportSubgroup R E = Q := by
      exact transportSubgroupCancel Q E.symm
    rwa [hcancel] at h

/-- Every split torus has a rational conjugate inside the prescribed minimal
parabolic. The fixed-point argument even applies to an arbitrary parabolic. -/
theorem splitTorusConjugateIntoMinimalParabolic : SplitTorusConjugateIntoMinimalParabolic.{u} := by
  intro k _ G P S hP hS
  obtain ⟨g, i, hi⟩ := splitSolvableConjugateInto P hP.1 S
    (splitTorusSplitSolvable (closedSubgroupAlgebraicGroup S) hS)
  let A := transportSubgroup S (innerIso g)
  let T := restrictSubgroup A P i hi
  have hh : (subgroupOfSubgroup P T).inclusion = A.inclusion := hi
  refine ⟨g, T, conjugates_of_sameTransport g ⟨⟨𝟙 _, ?_⟩, ⟨𝟙 _, ?_⟩⟩⟩
  · rw [Category.id_comp, hh]
  · rw [Category.id_comp, hh]

private theorem minimalParabolicExists (G : AffineAlgebraicGroup k) (hG : IsReductive G) :
    ∃ P : ClosedSubgroup G.val, IsMinimalParabolic G P := by
  letI := G.property.1
  letI := G.property.2.1
  letI : IsLocallyNoetherian G.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
  letI : IsNoetherianRing Γ(G.val.X.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let C : ClosedSubgroup G.val := ⟨G.val, 𝟙 _, inferInstanceAs (IsClosedImmersion (𝟙 G.val.X.left))⟩
  haveI := hG.2.1
  have hconn : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  obtain ⟨B, hB⟩ := GeometricBorelConjugacy.borelExists (GeometricGroup G)
    (geometricSmooth G hG.1) (geometricConnected G hconn)
  let F := groupBaseChange k (AlgebraicClosure k)
  have hCclosed : IsClosedImmersion (F.map C.inclusion).hom.hom.left := by
    change IsClosedImmersion (F.map (𝟙 G.val)).hom.hom.left
    rw [F.map_id]
    change IsClosedImmersion (𝟙 (F.obj G.val).X.left)
    infer_instance
  have hC : IsParabolic G C := by
    refine ⟨hG, hG.1, hCclosed, B, hB, B.inclusion, ?_⟩
    change B.inclusion ≫ F.map (𝟙 G.val) = B.inclusion
    rw [F.map_id]
    exact Category.comp_id B.inclusion
  let ideals : Set (Ideal Γ(G.val.X.left, ⊤)) :=
    {I | ∃ P : ClosedSubgroup G.val, IsParabolic G P ∧ definingIdeal P = I}
  obtain ⟨_, ⟨P, hP, rfl⟩, hmax⟩ := wellFounded_gt.has_min ideals
    ⟨definingIdeal C, C, hC, rfl⟩
  refine ⟨P, hP, ?_⟩
  rintro Q hQ ⟨f, hf⟩
  have hI : definingIdeal Q = definingIdeal P := by
    by_contra hne
    exact hmax (definingIdeal Q) ⟨Q, hQ, rfl⟩
      (lt_of_le_of_ne (definingIdeal_le f hf) (Ne.symm hne))
  haveI := factor_iso_of_definingIdeal_eq f hf hI
  exact ⟨inv f, by rw [← hf, IsIso.inv_hom_id_assoc]⟩

private theorem maximalSplitOfConjugate {K : GroupScheme k} {A B : ClosedSubgroup K}
    {g : 𝟙_ (SchemeOver k) ⟶ K.X} (h : ConjugatesSubgroups g A B)
    (hA : IsMaximalSplitTorus A) : IsMaximalSplitTorus B := by
  obtain ⟨e, he⟩ := h
  let E := innerIso g
  have he' : e.hom ≫ B.inclusion = A.inclusion ≫ E.hom := by
    apply Grp.hom_ext
    change (e.hom ≫ B.inclusion).hom.hom =
      A.inclusion.hom.hom ≫ (innerMap g).hom.hom
    rw [comp_innerMap]
    exact he
  refine ⟨?_, ?_⟩
  · obtain ⟨r, ⟨m⟩⟩ := hA.1
    exact ⟨r, ⟨e.symm ≪≫ m⟩⟩
  · rintro C hC ⟨b, hb⟩
    let C' := transportSubgroup C E.symm
    have hAC' : IsSubgroupOf A C' := ⟨e.hom ≫ b, by
      change (e.hom ≫ b) ≫ C.inclusion ≫ E.inv = A.inclusion
      rw [Category.assoc, ← Category.assoc b, hb, ← Category.assoc e.hom, he',
        Category.assoc, E.hom_inv_id, Category.comp_id]⟩
    obtain ⟨a, ha⟩ := hA.2 C' hC hAC'
    exact ⟨a ≫ e.hom, by
      change a ≫ A.inclusion = C.inclusion ≫ E.inv at ha
      rw [Category.assoc, he', ← Category.assoc, ha, Category.assoc,
        E.inv_hom_id, Category.comp_id]⟩

private theorem maximalSplitInParabolic {P : ClosedSubgroup G.val} {S : ClosedSubgroup P.group}
    (h : IsMaximalSplitTorus (subgroupOfSubgroup P S)) : IsMaximalSplitTorus S :=
  ⟨h.1, fun T hT hST ↦ (subgroupOfSubgroup_le P T S).1
    (h.2 (subgroupOfSubgroup P T) hT ((subgroupOfSubgroup_le P S T).2 hST))⟩

/-- The global conjugacy follows from the radical's conjugation action in a
minimal parabolic and rational conjugation of split tori into that parabolic. -/
private theorem globalConjugacyOfLocal
    (conjugateInto : SplitTorusConjugateIntoMinimalParabolic.{u})
    (localConjugacy : MaximalSplitToriConjugateByRadical.{u}) :
    MaximalSplitToriConjugate.{u} := by
  intro k _ G hG S T hS hT
  obtain ⟨P, hP⟩ := minimalParabolicExists G hG
  obtain ⟨g, A, hg⟩ := conjugateInto G P S hP hS.1
  obtain ⟨h, B, hh⟩ := conjugateInto G P T hP hT.1
  obtain ⟨c, D, hD, hRad, _⟩ := SplitContractingRadical.parabolicSplitRadical G P hP.1
  obtain ⟨e, _⟩ := subgroupIso_of_same hD
  let U := pushSubgroup e.symm (contractingSubgroup D)
  have hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U :=
    radical_transport (A := closedSubgroupAlgebraicGroup D.parabolic)
      (B := closedSubgroupAlgebraicGroup P) e.symm (contractingSubgroup D) hRad.1
  obtain ⟨a, ha⟩ := localConjugacy G P hP U hU A B
    (maximalSplitInParabolic (G := G) (P := P) (maximalSplitOfConjugate hg hS))
    (maximalSplitInParabolic (G := G) (P := P) (maximalSplitOfConjugate hh hT))
  exact ⟨_, conjugates_trans (conjugates_trans hg (conjugates_in_ambient P ha))
    (conjugates_inverse hh)⟩

/-- A sufficiently large multiple preserves the signs of all nonzero pairings,
and the regular perturbation gives a sign on the zero roots. -/
private theorem regularPerturbation (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) (c : Cocharacter T.group) :
    ∃ d : Cocharacter T.group, IsRegular T d ∧
      ∀ α : ↥(absoluteRoots T), α ∈ positiveRoots T d → 0 ≤ pairing T.group α.val c := by
  classical
  obtain ⟨r, hr⟩ := exists_regular_cocharacter G T hT
  obtain ⟨hComm, _, _, _, _, P, _, hpair⟩ :=
    RootData.CharacterPairing.perfectCharacterPairing T.group hT
  letI := hComm
  letI : Finite ↥(absoluteRoots T) := RootData.CharacterPairing.finiteAbsoluteRoots G T hT
  letI := Fintype.ofFinite ↥(absoluteRoots T)
  let n : ℤ := (∑ α : ↥(absoluteRoots T), |pairing T.group α.val r|) + 1
  have hn (α : ↥(absoluteRoots T)) : -n < pairing T.group α.val r ∧ pairing T.group α.val r < n := by
    have h := Finset.single_le_sum
      (f := fun β : ↥(absoluteRoots T) ↦ |pairing T.group β.val r|)
      (fun β _ ↦ abs_nonneg _) (Finset.mem_univ α)
    have h₁ := neg_abs_le (pairing T.group α.val r)
    have h₂ := le_abs_self (pairing T.group α.val r)
    dsimp only [n]
    omega
  let d : Cocharacter T.group := (n • Additive.ofMul c + Additive.ofMul r).toMul
  have he (α : ↥(absoluteRoots T)) :
      pairing T.group α.val d = n * pairing T.group α.val c + pairing T.group α.val r := by
    rw [← hpair, ← hpair, ← hpair]
    change P (Additive.ofMul α.val) (n • Additive.ofMul c + Additive.ofMul r) =
      n * P (Additive.ofMul α.val) (Additive.ofMul c) + P (Additive.ofMul α.val) (Additive.ofMul r)
    rw [map_add, map_smul, Int.zsmul_eq_mul]
  have hneg (α : ↥(absoluteRoots T)) (ha : pairing T.group α.val c < 0) :
      pairing T.group α.val d < 0 := by
    have hmul := mul_le_mul_of_nonneg_left
      (show pairing T.group α.val c ≤ -1 by omega)
      (show 0 ≤ n from by have h := hn α; omega)
    rw [mul_neg_one] at hmul
    rw [he]
    have h := hn α
    omega
  have hpos (α : ↥(absoluteRoots T)) (ha : 0 < pairing T.group α.val c) :
      0 < pairing T.group α.val d := by
    have hmul := mul_le_mul_of_nonneg_left
      (show 1 ≤ pairing T.group α.val c by omega)
      (show 0 ≤ n from by have h := hn α; omega)
    rw [mul_one] at hmul
    rw [he]
    have h := hn α
    omega
  refine ⟨d, ?_, ?_⟩
  · intro α
    rcases lt_trichotomy (pairing T.group α.val c) 0 with h | h | h
    · exact (hneg α h).ne
    · rw [he, h, mul_zero, zero_add]
      exact hr α
    · exact (hpos α h).ne'
  · intro α hα
    change 0 < pairing T.group α.val d at hα
    exact le_of_not_gt (fun h ↦ (hneg α h).not_gt hα)

/-- On a geometric fibre, choose the Borel of a regular cocharacter
having the same signs away from the vanishing roots. -/
private theorem limitContainsBorel [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (c : Cocharacter G.val) (D : LimitDecomposition c) :
    ∃ B : ClosedSubgroup G.val, IsBorel B ∧ IsSubgroupOf B D.parabolic := by
  obtain ⟨S, p, hS, hp, _, _⟩ := cocharacterImageIsTorus G c
  obtain ⟨T, hT, j, hj⟩ := exists_maximal_torus_over G S hS
  have hTs := split_of_maximal hT
  have hTm := geometricMaximal_of_maximal G T hT
  let a : Cocharacter T.group := p ≫ j
  have ha : c = a ≫ T.inclusion := by
    dsimp only [a]
    rw [Category.assoc, hj, hp]
  let D' := ha ▸ D
  obtain ⟨b, hb, hsign⟩ := regularPerturbation G T hTs a
  obtain ⟨E⟩ := existsLimitDecomposition G (b ≫ T.inclusion)
  have hZ := centralizer_of_regular G hG T hTs hTm b hb E
  have hB := regular_isBorel G hG T hTs hTm b hb E hZ
  have hTB := subgroupOf_trans hZ.2 ⟨E.sectionMap, E.section_in_G⟩
  have hroots := subgroupRoots_of_regular G T b hb E
  refine ⟨E.parabolic, hB, ?_⟩
  have h := subgroupOf_limit_of_rootSigns G hG T E.parabolic hTs hTm
    hB.1.1 hB.1.2.1 hTB a D' (fun α hα ↦ hsign α (hroots ▸ hα))
  change IsSubgroupOf E.parabolic (ha ▸ D : LimitDecomposition (a ≫ T.inclusion)).parabolic at h
  rwa [parabolic_of_cast] at h

private theorem limitIsParabolic (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (c : Cocharacter G.val) (D : LimitDecomposition c) : IsParabolic G D.parabolic := by
  letI := hG.1
  let K := AlgebraicClosure k
  let Gbar := GeometricGroup G
  obtain ⟨e, he⟩ := gm_baseChange k K
  let cbar : Cocharacter Gbar.val := e.hom ≫ (groupBaseChange k K).map c
  obtain ⟨E⟩ := existsLimitDecomposition Gbar cbar
  obtain ⟨hD, _, _⟩ := limits_subgroups_extend G D e he E
  obtain ⟨B, hB, hBE⟩ := limitContainsBorel Gbar (reductive_geometricGroup G hG) cbar E
  exact ⟨hG, (limitSubgroupsSmooth G c D).1, (extendSubgroup K D.parabolic).isClosedImmersion,
    B, hB, subgroupOf_trans hBE hD.1⟩

/-- Pullback along the projection to a Levi takes its parabolics to
parabolics of the ambient reductive group. -/
private theorem parabolicPreimageOfSplitProjection
    (G L : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val) (hP : IsParabolic G P)
    (I : ClosedSubgroup L.val) (hI : IsParabolic L I)
    (q : P.group ⟶ L.val) (hq : Smooth q.hom.hom.left)
    (s : L.val ⟶ P.group) (hs : s ≫ q = 𝟙 L.val) :
    ∃ (J : ClosedSubgroup P.group) (r : J.group ⟶ I.group),
      IsPullback J.inclusion.hom.hom r.hom.hom q.hom.hom I.inclusion.hom.hom ∧
      IsParabolic G (subgroupOfSubgroup P J) := by
  let J := preimageSubgroup q I
  let r : J.group ⟶ I.group := pullback.snd q I.inclusion
  have hp := preimageSquare q I
  have hsmooth := smoothPreimage hp hq hI.2.1
  let t : I.group ⟶ J.group :=
    pullback.lift (I.inclusion ≫ s) (𝟙 _) (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  have ht : I.inclusion ≫ s = t ≫ J.inclusion := (pullback.lift_fst _ _ _).symm
  let JP := subgroupOfSubgroup P J
  obtain ⟨⟨Q⟩, _⟩ := HomogeneousQuotient.homogeneousQuotient k G JP
  obtain ⟨R, hR⟩ := properParabolicQuotient G P hP
  obtain ⟨S, hS⟩ := properParabolicQuotient L I hI
  obtain ⟨⟨W⟩, _⟩ := HomogeneousQuotient.homogeneousQuotient k (closedSubgroupAlgebraicGroup P) J
  obtain ⟨f, hf⟩ := quotientMapExists Q R ⟨J.inclusion, rfl⟩
  let x : 𝟙_ (SchemeOver k) ⟶ R.scheme := (1 : _ ⟶ G.val.X) ≫ R.projection
  let X := pullback f x
  obtain ⟨E⟩ := subgroup_quotient_fiber J Q R f hf
  obtain ⟨e, _⟩ := split_preimage_quotient q s hs r hp t ht W S
  let isoX : X ≅ S.scheme := (compareRepresentatives W E).symm ≪≫ e
  haveI : IsIso isoX.hom.left := (Over.forget _).map_isIso isoX.hom
  haveI : IsProper X.hom := by
    letI := hS
    rw [← Over.w isoX.hom]
    infer_instance
  have hLoc := (subgroup_quotient_pullback Q R f hf).map (Over.forget _)
  have hprod := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd G.val.X X)
  have hleft : IsProper (prod.fst : G.val.X ⨯ X ⟶ G.val.X).left :=
    MorphismProperty.of_isPullback (P := @IsProper) hprod.flip inferInstance
  haveI : QuasiCompact R.projection.left := by
    letI := G.property.1
    letI := G.property.2.1
    letI : IsLocallyNoetherian G.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
    letI : IsNoetherian G.val.X.left := ⟨⟩
    infer_instance
  have hfClosed : UniversallyClosed f.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) hLoc.flip
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨R.surjective, R.flat⟩, (inferInstance : QuasiCompact R.projection.left)⟩
      hleft.toUniversallyClosed
  have hQclosed : UniversallyClosed Q.scheme.hom := by
    rw [← Over.w f]
    exact MorphismProperty.comp_mem _ _ _ hfClosed hR.toUniversallyClosed
  have hQ : IsProper Q.scheme.hom :=
    (isProper_iff _).mpr ⟨(quotientSeparatedFiniteType Q).1, hQclosed, (quotientSeparatedFiniteType Q).2⟩
  letI := hP.1.2.1
  have hGc : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  exact ⟨J, r, hp, hP.1, hsmooth, (BorelProper.quotientProperIff G hP.1.1 hGc JP hsmooth Q).mp hQ⟩

/-- Any parabolic of the Levi of a minimal parabolic is the full Levi. -/
private theorem leviParabolicIsWhole (P : ClosedSubgroup G.val) (hP : IsMinimalParabolic G P)
    {c : Cocharacter G.val} (D : LimitDecomposition c) (e : P.group ≅ D.parabolic.group)
    (I : ClosedSubgroup D.centralizer.group)
    (hI : IsParabolic (closedSubgroupAlgebraicGroup D.centralizer) I) :
    IsIso I.inclusion := by
  let q := e.hom ≫ D.limit
  let s := D.sectionMap ≫ e.inv
  have hs : s ≫ q = 𝟙 D.centralizer.group := by simp [s, q, D.section_limit]
  have hq : Smooth q.hom.hom.left := by
    haveI : IsIso e.hom.hom.hom.left :=
      ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map_isIso e.hom
    letI := hP.1.1.1
    letI := limitSmooth D (limitSubgroupsSmooth G c D).2.1
    change Smooth (e.hom.hom.hom.left ≫ D.limit.hom.hom.left)
    infer_instance
  obtain ⟨J, r, hp, hJ⟩ := parabolicPreimageOfSplitProjection
    G (closedSubgroupAlgebraicGroup D.centralizer) P hP.1 I hI q hq s hs
  obtain ⟨b, hb⟩ := hP.2 _ hJ ⟨J.inclusion, rfl⟩
  have hbj : b ≫ J.inclusion = 𝟙 P.group := by
    letI := inclusion_mono P
    apply (cancel_mono P.inclusion).mp
    change b ≫ J.inclusion ≫ P.inclusion = P.inclusion at hb
    simpa only [Category.assoc, Category.id_comp] using hb
  have hqr : J.inclusion ≫ q = r ≫ I.inclusion := Grp.hom_ext _ _ hp.w
  have hsbr : (s ≫ b ≫ r) ≫ I.inclusion = 𝟙 D.centralizer.group := by
    simp only [Category.assoc]
    rw [← hqr, ← Category.assoc b, hbj, Category.id_comp, hs]
  haveI := inclusion_mono I
  let t := s ≫ b ≫ r
  have ht : t ≫ I.inclusion = 𝟙 D.centralizer.group := hsbr
  have ht' : I.inclusion ≫ t = 𝟙 I.group := (cancel_mono I.inclusion).mp (by
    rw [Category.assoc, ht, Category.comp_id, Category.id_comp])
  exact ⟨⟨t, ht', ht⟩⟩

/-- If the two opposite limit parabolics are the whole group, the
contracting kernel is trivial, so the limit centralizer is the whole group. -/
private theorem centralizesOfOppositeLimitsWhole (L : AffineAlgebraicGroup k)
    (c : Cocharacter L.val) (D : LimitDecomposition c)
    (E : LimitDecomposition (oppositeCocharacter c))
    [IsIso D.parabolic.inclusion] [IsIso E.parabolic.inclusion]
    {X : SchemeOver k} (g : X ⟶ L.val.X) : Centralizes c g := by
  let hc := (opposite_opposite c).symm
  let D' : LimitDecomposition (oppositeCocharacter (oppositeCocharacter c)) := hc ▸ D
  have hDE : D'.contracting = D.contracting := contracting_of_cast hc D
  have hp := oppositeLimitIntersection L (oppositeCocharacter c) E D'
  change IsPullback (η[D'.contracting.group.X]) (η[E.parabolic.group.X])
    D'.contracting.inclusion.hom.hom E.parabolic.inclusion.hom.hom at hp
  rw [hDE] at hp
  let y := (D.contracting.inclusion ≫ inv E.parabolic.inclusion).hom.hom
  have hy : 𝟙 D.contracting.group.X ≫ D.contracting.inclusion.hom.hom =
      y ≫ E.parabolic.inclusion.hom.hom := by
    change (𝟙 D.contracting.group ≫ D.contracting.inclusion).hom.hom =
      ((D.contracting.inclusion ≫ inv E.parabolic.inclusion) ≫ E.parabolic.inclusion).hom.hom
    simp
  let a := hp.lift (𝟙 _) y hy
  have ha : a ≫ η[D.contracting.group.X] = 𝟙 _ := hp.lift_fst _ _ _
  have hunit : D.contracting.inclusion.hom.hom = 1 := by
    have h := congrArg (· ≫ D.contracting.inclusion.hom.hom) ha
    simpa only [Category.assoc, IsMonHom.one_hom, MonObj.one_eq_one, MonObj.comp_one,
      MonObj.one_comp, Category.id_comp] using h.symm
  have hU : IsSubgroupOf D.contracting D.centralizer := by
    apply factor_group_through_subgroup D.centralizer D.contracting.inclusion 1
    rw [MonObj.one_comp, hunit]
  let x := g ≫ (inv D.parabolic.inclusion).hom.hom
  have hx : x ≫ D.parabolic.inclusion.hom.hom = g := by
    have h := (Grp.forget (SchemeOver k)).congr_map (IsIso.inv_hom_id D.parabolic.inclusion)
    change (inv D.parabolic.inclusion).hom.hom ≫ D.parabolic.inclusion.hom.hom = 𝟙 _ at h
    rw [Category.assoc, h, Category.comp_id]
  apply (D.centralizer_points _ _).2
  rw [← hx]
  exact (limitSectionMemIff D hU x).2 ⟨x ≫ D.limit.hom.hom, by rfl⟩

private theorem leviCentralizesSplitTorus (P : ClosedSubgroup G.val)
    (hP : IsMinimalParabolic G P) {c : Cocharacter G.val}
    (D : LimitDecomposition c) (e : P.group ≅ D.parabolic.group)
    (hL : IsReductive (closedSubgroupAlgebraicGroup D.centralizer))
    (S : ClosedSubgroup D.centralizer.group) (hS : IsSplitTorus S.group)
    {X : SchemeOver k} (g : X ⟶ D.centralizer.group.X) : Centralizes S.inclusion g := by
  classical
  let L := closedSubgroupAlgebraicGroup D.centralizer
  obtain ⟨n, ⟨f⟩⟩ := hS
  let i := f.inv ≫ S.inclusion
  choose a ha using (fun j : ULift.{u} (Fin n) ↦ exists_coordinateCocharacter (k := k) j)
  have h : Centralizes i g := (centralizes_split_power i a ha g).2 (fun j ↦ by
    obtain ⟨A⟩ := existsLimitDecomposition L (a j ≫ i)
    obtain ⟨B⟩ := existsLimitDecomposition L (oppositeCocharacter (a j ≫ i))
    haveI := leviParabolicIsWhole P hP D e A.parabolic (limitIsParabolic L hL _ A)
    haveI := leviParabolicIsWhole P hP D e B.parabolic (limitIsParabolic L hL _ B)
    exact centralizesOfOppositeLimitsWhole L _ A B g)
  exact (centralizes_precomp_iso f.symm S.inclusion g).1 h

/-- The scheme image of a split torus is split, since its character
group is a subgroup of the finite-rank free character lattice. -/
private theorem splitTorusImage (A B : AffineAlgebraicGroup k)
    (ha : IsSplitTorus A.val) (f : A.val ⟶ B.val) :
    ∃ (I : ClosedSubgroup B.val) (p : A.val ⟶ I.group), IsSplitTorus I.group ∧
      IsImageFactorization f p I.inclusion := by
  obtain ⟨r, ⟨e⟩⟩ := ha
  obtain ⟨e'⟩ := CharacterDescent.standardSplitTorus (k := k) r
  let M := StandardLattice.{u} r
  let z : IntegerCharacters.{u} ≃* Multiplicative ℤ := MulEquiv.ulift
  letI : Group.FG IntegerCharacters.{u} :=
    Group.fg_of_surjective (f := z.symm.toMonoidHom) z.symm.surjective
  letI : Group.FG M := by
    apply Group.fg_def.mpr
    simpa only [Subgroup.pi_top] using
      (Subgroup.FG.pi (P := fun (_ : Fin r) ↦ (⊤ : Subgroup IntegerCharacters)) fun _ ↦
        Group.fg_def.mp (inferInstance : Group.FG IntegerCharacters.{u}))
  let e₀ := e ≪≫ e'.symm
  obtain ⟨J, p, i, hi, _, _⟩ := schemeImageFactorization A B f
  let q := e₀.inv ≫ p
  letI := hi.2.1
  letI := hi.2.2.1
  haveI : IsIso e₀.inv.hom.hom.left := ((Grp.forget _) ⋙ Over.forget _).map_isIso e₀.inv
  have hq : Flat q.hom.hom.left ∧ Surjective q.hom.hom.left := by
    change Flat (e₀.inv.hom.hom.left ≫ p.hom.hom.left) ∧
      Surjective (e₀.inv.hom.hom.left ≫ p.hom.hom.left)
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨N, ⟨b, _⟩, _⟩ :=
    (DiagonalizableGroups.diagonalFaithfullyFlatQuotients k M ⟨J.val, J.property.1⟩ q).mp hq
  letI := DiagonalizableGroups.subgroupFG N
  letI : Module.Finite ℤ (Additive N) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let z₁ (j : Fin r) : Additive N →+ ℤ :=
    (z.toMonoidHom.comp ((Pi.evalMonoidHom _ j).comp N.subtype)).toAdditive
  letI : Module.IsTorsionFree ℤ (Additive N) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro n x hnx
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      apply Additive.toMul.injective
      apply Subtype.ext
      funext j
      apply z.injective
      apply Multiplicative.toAdd.injective
      change z₁ j x = 0
      have hz : n * z₁ j x = 0 := by
        rw [← Int.zsmul_eq_mul, ← map_zsmul, hnx, map_zero]
      exact (mul_eq_zero.mp hz).resolve_left hn
  obtain ⟨s, v⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive N)
  let a := CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k (latticeEquivOfBasis v))
  let t := (hopfSpec (CommRingCat.of k)).mapIso a.op
  obtain ⟨j⟩ := CharacterDescent.standardSplitTorus (k := k) s
  exact ⟨⟨J.val, i, hi.2.2.2.2.2⟩, p, ⟨s, ⟨b.symm ≪≫ t.symm ≪≫ j⟩⟩, hi⟩

private theorem tensorUnderlyingAffine (A B : AffineAlgebraicGroup k) :
    IsAffine (A.val ⊗ B.val).X.left := by
  letI := A.property.1
  letI := B.property.1
  have h := Over.isPullback_of_binaryFan_isLimit _
    (tensorProductIsBinaryProduct A.val.X B.val.X)
  exact IsAffine.of_isPullback h

private theorem tensorSplitTorus (A B : AffineAlgebraicGroup k)
    (hA : IsSplitTorus A.val) (hB : IsSplitTorus B.val) : IsSplitTorus (A.val ⊗ B.val) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := hA
  obtain ⟨n, ⟨f⟩⟩ := hB
  let M := ULift.{u} (Fin m)
  let N := ULift.{u} (Fin n)
  let W := ULift.{u} (Fin (m + n))
  let w : M ⊕ N ≃ W := (Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
    (finSumFinEquiv.trans Equiv.ulift.symm)
  let Pa := (groupPointsFunctor k).mapIso e ≪≫ StandardGroups.multiplicativePowerGroupPointsIso k M
  let Pb := (groupPointsFunctor k).mapIso f ≪≫ StandardGroups.multiplicativePowerGroupPointsIso k N
  let E (R : TestAlgebra k) :
      GroupPoints (A.val ⊗ B.val) R ≃* (W → Rˣ) := by
    let a := (Pa.app R).groupIsoToMulEquiv
    let b := (Pb.app R).groupIsoToMulEquiv
    refine
      { toFun := fun x j ↦ Sum.elim (a (x ≫ fst A.val.X B.val.X))
          (b (x ≫ snd A.val.X B.val.X)) (w.symm j)
        invFun := fun v ↦ lift (a.symm (fun i ↦ v (w (.inl i))))
          (b.symm (fun i ↦ v (w (.inr i))))
        left_inv := ?_
        right_inv := ?_
        map_mul' := ?_ }
    · intro x
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]
        apply a.injective
        rw [MulEquiv.apply_symm_apply]
        funext i
        dsimp only
        rw [Equiv.symm_apply_apply, Sum.elim_inl]
      · rw [lift_snd]
        apply b.injective
        rw [MulEquiv.apply_symm_apply]
        funext i
        dsimp only
        rw [Equiv.symm_apply_apply, Sum.elim_inr]
    · intro v
      funext j
      obtain ⟨i, rfl⟩ := w.surjective j
      dsimp only
      cases i with
      | inl i =>
        rw [Equiv.symm_apply_apply, Sum.elim_inl, lift_fst, MulEquiv.apply_symm_apply]
      | inr i =>
        rw [Equiv.symm_apply_apply, Sum.elim_inr, lift_snd, MulEquiv.apply_symm_apply]
    · intro x y
      change Points (A.val.X ⊗ B.val.X) R at x y
      funext j
      cases h : w.symm j with
      | inl i =>
        simp only [Pi.mul_apply, h, Sum.elim_inl]
        change a ((x * y) ≫ fst A.val.X B.val.X) i =
          a (x ≫ fst A.val.X B.val.X) i * a (y ≫ fst A.val.X B.val.X) i
        rw [MonObj.mul_comp, map_mul]
        rfl
      | inr i =>
        simp only [Pi.mul_apply, h, Sum.elim_inr]
        change b ((x * y) ≫ snd A.val.X B.val.X) i =
          b (x ≫ snd A.val.X B.val.X) i * b (y ≫ snd A.val.X B.val.X) i
        rw [MonObj.mul_comp, map_mul]
        rfl
  let U : (groupPointsFunctor k).obj (A.val ⊗ B.val) ≅ multiplicativePowerPoints (k := k) W :=
    NatIso.ofComponents (fun R ↦ (E R).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro x
      change Points (A.val.X ⊗ B.val.X) R at x
      funext j
      change Sum.elim
          (Pa.hom.app S (((testSpec k).map f.op ≫ x) ≫ fst A.val.X B.val.X))
          (Pb.hom.app S (((testSpec k).map f.op ≫ x) ≫ snd A.val.X B.val.X)) (w.symm j) =
        Units.map f.hom.toMonoidHom
          (Sum.elim (Pa.hom.app R (x ≫ fst A.val.X B.val.X))
            (Pb.hom.app R (x ≫ snd A.val.X B.val.X)) (w.symm j))
      cases h : w.symm j with
      | inl i =>
        have ha : Pa.hom.app S ((testSpec k).map f.op ≫ (x ≫ fst A.val.X B.val.X)) i =
            Units.map f.hom.toMonoidHom (Pa.hom.app R (x ≫ fst A.val.X B.val.X) i) :=
          congrArg (fun g ↦ g (x ≫ fst A.val.X B.val.X) i) (Pa.hom.naturality f)
        simpa only [h, Sum.elim_inl, Category.assoc] using ha
      | inr i =>
        have hb : Pb.hom.app S ((testSpec k).map f.op ≫ (x ≫ snd A.val.X B.val.X)) i =
            Units.map f.hom.toMonoidHom (Pb.hom.app R (x ≫ snd A.val.X B.val.X) i) :=
          congrArg (fun g ↦ g (x ≫ snd A.val.X B.val.X) i) (Pb.hom.naturality f)
        simpa only [h, Sum.elim_inr, Category.assoc] using hb)
  let V := multiplicativePowerGroup k W
  let J := U ≪≫ (StandardGroups.multiplicativePowerGroupPointsIso k W).symm
  let F := groupPointsFunctor k
  obtain ⟨v, hv⟩ := (groupHomComparison k (A.val ⊗ B.val) V.val (tensorUnderlyingAffine A B)).2 J.hom
  obtain ⟨v', hv'⟩ := (groupHomComparison k V.val (A.val ⊗ B.val) V.property.1).2 J.inv
  refine ⟨m + n, ⟨⟨v, v', ?_, ?_⟩⟩⟩
  · apply (groupHomComparison k _ _ (tensorUnderlyingAffine A B)).1
    change F.map (v ≫ v') = F.map (𝟙 _)
    change F.map v = J.hom at hv
    change F.map v' = J.inv at hv'
    rw [F.map_comp, hv, hv', J.hom_inv_id, F.map_id]
  · apply (groupHomComparison k _ _ V.property.1).1
    change F.map (v' ≫ v) = F.map (𝟙 _)
    change F.map v = J.hom at hv
    change F.map v' = J.inv at hv'
    rw [F.map_comp, hv, hv', J.inv_hom_id, F.map_id]
    rfl

private def commutingProductMap {A B H : GroupScheme k}
    (i : A ⟶ H) (j : B ⟶ H)
    (h : ∀ (X : SchemeOver k) (a : X ⟶ A.X) (b : X ⟶ B.X),
      Commute (a ≫ i.hom.hom) (b ≫ j.hom.hom)) : A ⊗ B ⟶ H := by
  let W := (A ⊗ B).X
  let a : W ⟶ H.X := fst A.X B.X ≫ i.hom.hom
  let b : W ⟶ H.X := snd A.X B.X ≫ j.hom.hom
  refine Grp.homMk'' (a * b) ?_ ?_
  · simp only [MonObj.comp_mul, MonObj.one_eq_one, a, b, MonObj.one_comp, one_mul]
  · let x := fst W W
    let y := snd W W
    have hμ : μ[W] = x * y := by
      change _ = lift (fst W W) (snd W W) ≫ μ[W]
      rw [lift_fst_snd, Category.id_comp]
    have hs : Commute (x ≫ b) (y ≫ a) := by
      have h := (h _ (y ≫ fst A.X B.X) (x ≫ snd A.X B.X)).symm
      simpa only [a, b, Category.assoc] using h
    have he : ((a * b) ⊗ₘ (a * b)) ≫ μ[H.X] =
        (x ≫ (a * b)) * (y ≫ (a * b)) := by
      change _ = lift (fst W W ≫ (a * b)) (snd W W ≫ (a * b)) ≫ μ[H.X]
      rw [lift_fst_comp_snd_comp]
    rw [hμ, he, MonObj.comp_mul, MonObj.mul_comp, MonObj.mul_comp, MonObj.comp_mul, MonObj.comp_mul]
    exact (hs.mul_mul_mul_comm (x ≫ a) (y ≫ b)).symm

/-- Commuting split subtori are contained in a split torus, obtained
as the scheme image of their multiplication. -/
private theorem splitTorusUpperBound (H : AffineAlgebraicGroup k) (A B : ClosedSubgroup H.val)
    (hA : IsSplitTorus A.group) (hB : IsSplitTorus B.group)
    (h : ∀ (X : SchemeOver k) (a : X ⟶ A.group.X) (b : X ⟶ B.group.X),
      Commute (a ≫ A.inclusion.hom.hom) (b ≫ B.inclusion.hom.hom)) :
    ∃ T : ClosedSubgroup H.val, IsSplitTorus T.group ∧ IsSubgroupOf A T ∧ IsSubgroupOf B T := by
  obtain ⟨r, ⟨e⟩⟩ := tensorSplitTorus (closedSubgroupAlgebraicGroup A)
    (closedSubgroupAlgebraicGroup B) hA hB
  let V := multiplicativePowerGroup k (ULift.{u} (Fin r))
  let m := commutingProductMap A.inclusion B.inclusion h
  let f : V.val ⟶ H.val := e.inv ≫ m
  obtain ⟨T, p, hT, hp⟩ := splitTorusImage V H ⟨r, ⟨Iso.refl _⟩⟩ f
  let i : A.group ⟶ A.group ⊗ B.group :=
    lift (𝟙 _) (toUnit A.group ≫ (default : Grp.trivial (SchemeOver k) ⟶ B.group))
  let j : B.group ⟶ A.group ⊗ B.group :=
    lift (toUnit B.group ≫ (default : Grp.trivial (SchemeOver k) ⟶ A.group)) (𝟙 _)
  have hi : i ≫ m = A.inclusion := by
    apply Grp.hom_ext
    change lift (𝟙 A.group.X) (1 : A.group.X ⟶ B.group.X) ≫
      ((fst _ _ ≫ A.inclusion.hom.hom) * (snd _ _ ≫ B.inclusion.hom.hom)) = _
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, Category.id_comp, MonObj.one_comp, mul_one]
  have hj : j ≫ m = B.inclusion := by
    apply Grp.hom_ext
    change lift (1 : B.group.X ⟶ A.group.X) (𝟙 B.group.X) ≫
      ((fst _ _ ≫ A.inclusion.hom.hom) * (snd _ _ ≫ B.inclusion.hom.hom)) = _
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, Category.id_comp, MonObj.one_comp, one_mul]
  refine ⟨T, hT, ⟨i ≫ e.hom ≫ p, ?_⟩, ⟨j ≫ e.hom ≫ p, ?_⟩⟩
  · simp [hp.1, f, hi]
  · simp [hp.1, f, hj]

private theorem cocharacterFactorsThroughMaximalSplit (H : AffineAlgebraicGroup k)
    (S T : ClosedSubgroup H.val) (hS : IsMaximalSplitTorus S) (hT : IsTorus T.group)
    (j : S.group ⟶ T.group) (hj : j ≫ T.inclusion = S.inclusion) (c : Cocharacter T.group) :
    ∃ a : Cocharacter S.group, a ≫ j = c := by
  let S' := restrictSubgroup S T j hj
  let T' := closedSubgroupAlgebraicGroup T
  let e : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
  letI : Group.FG IntegerCharacters.{u} := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  let M := diagonalGroup k IntegerCharacters.{u}
  have hM : IsSplitTorus M.val := ⟨1, multiplicative_group_iso⟩
  obtain ⟨R, p, hR, hp⟩ := splitTorusImage M T' hM c
  letI : IsCommMonObj T.group.X := torus_commutative T' hT
  obtain ⟨V, hV, hSV, hRV⟩ := splitTorusUpperBound T' S' R hS.1 hR
    (fun X a b ↦ by
      letI : CommMonoid (X ⟶ T.group.X) := Hom.commMonoid
      exact Commute.all (a ≫ S'.inclusion.hom.hom) (b ≫ R.inclusion.hom.hom))
  have hs : IsSubgroupOf S (subgroupOfSubgroup T V) := by
    rw [← compose_restrict S T j hj]
    exact (subgroupOfSubgroup_le T S' V).2 hSV
  have hVs : IsSubgroupOf V S' := by
    apply (subgroupOfSubgroup_le T V S').1
    rw [compose_restrict S T j hj]
    exact hS.2 (subgroupOfSubgroup T V) hV hs
  obtain ⟨v, hv⟩ := subgroupOf_trans hRV hVs
  exact ⟨p ≫ v, by
    change (p ≫ v) ≫ S'.inclusion = c
    rw [Category.assoc, hv, hp.1]⟩

/-- In a minimal parabolic the defining cocharacter can be taken in the
specified maximal split torus. The associated Levi is its scheme centralizer. -/
theorem minimalParabolicLevi : MinimalParabolicLevi.{u} := by
  intro k _ G P hP S hS
  let P' := closedSubgroupAlgebraicGroup P
  obtain ⟨T, hT, j, hj⟩ := exists_maximal_torus_over P' S (isTorus_of_split hS.1)
  obtain ⟨d, D, hPD, hL, hRad⟩ := RationalCocharacter.rationalParabolicThroughTorus G P hP.1 T hT
  obtain ⟨a, ha⟩ := cocharacterFactorsThroughMaximalSplit P' S T hS hT.1 j hj d
  have heq : d ≫ (subgroupOfSubgroup P T).inclusion = a ≫ (subgroupOfSubgroup P S).inclusion := by
    change d ≫ T.inclusion ≫ P.inclusion = a ≫ S.inclusion ≫ P.inclusion
    have h : a ≫ S.inclusion = d ≫ T.inclusion := by
      rw [← hj, ← Category.assoc, ha]
    simpa only [Category.assoc] using congrArg (· ≫ P.inclusion) h.symm
  let Sg := subgroupOfSubgroup P S
  let Tg := subgroupOfSubgroup P T
  have hSD : IsSubgroupOf Sg D.centralizer := by
    letI : IsCommMonObj T.group.X := torus_commutative (closedSubgroupAlgebraicGroup T) hT.1
    have hTg : Centralizes (d ≫ Tg.inclusion) Sg.inclusion.hom.hom := by
      apply (centralizes_iff _ _).2
      intro X b t
      letI : CommMonoid (X ⟶ T.group.X) := Hom.commMonoid
      have h := (Commute.all (b ≫ j.hom.hom) (t ≫ d.hom.hom)).map
        (IsMonHom.monoidHom Tg.inclusion.hom.hom X)
      have hinc : j ≫ Tg.inclusion = Sg.inclusion := by
        change j ≫ T.inclusion ≫ P.inclusion = S.inclusion ≫ P.inclusion
        rw [← Category.assoc, hj]
      change Commute ((b ≫ j.hom.hom) ≫ Tg.inclusion.hom.hom)
        ((t ≫ d.hom.hom) ≫ Tg.inclusion.hom.hom) at h
      change Commute (b ≫ Sg.inclusion.hom.hom) (t ≫ d.hom.hom ≫ Tg.inclusion.hom.hom)
      simpa only [Category.assoc, show j.hom.hom ≫ Tg.inclusion.hom.hom =
        Sg.inclusion.hom.hom from (Grp.forget _).congr_map hinc] using h
    obtain ⟨b, hb⟩ := (D.centralizer_points _ _).1 hTg
    exact factor_group_through_subgroup D.centralizer Sg.inclusion b hb
  obtain ⟨jL, hjL⟩ := hSD
  let SL := restrictSubgroup Sg D.centralizer jL hjL
  obtain ⟨e, _⟩ := subgroupIso_of_same hPD
  have hC : RepresentsSubgroup D.centralizer (fun _ g ↦ Centralizes Sg.inclusion g) := by
    intro X g
    constructor
    · intro hg
      apply (D.centralizer_points X g).1
      rw [heq]
      apply (centralizes_iff _ _).2
      intro Y x y
      exact (centralizes_iff Sg.inclusion g).1 hg Y x (y ≫ a.hom.hom)
    · rintro ⟨b, rfl⟩
      apply (centralizes_iff _ _).2
      intro Y x y
      have hh := leviCentralizesSplitTorus P hP D e hL SL hS.1 b
      have h := ((centralizes_iff _ _).1 hh Y x y).map
        (IsMonHom.monoidHom D.centralizer.inclusion.hom.hom Y)
      have hfac : jL.hom.hom ≫ D.centralizer.inclusion.hom.hom = Sg.inclusion.hom.hom :=
        (Grp.forget _).congr_map hjL
      change Commute ((x ≫ b) ≫ D.centralizer.inclusion.hom.hom)
        ((y ≫ jL.hom.hom) ≫ D.centralizer.inclusion.hom.hom) at h
      simpa only [Category.assoc, hfac] using h
  have hlast (f : Cocharacter G.val) (h : d ≫ Tg.inclusion = f) :
      let E : LimitDecomposition f := h ▸ D
      SameSubgroup P E.parabolic ∧ StandardParabolicLevi.IsContractingRadical E ∧
        IsReductive (closedSubgroupAlgebraicGroup E.centralizer) ∧
        IsSubgroupOf Sg E.centralizer ∧
        RepresentsSubgroup E.centralizer (fun _ g ↦ Centralizes Sg.inclusion g) := by
    subst f
    exact ⟨hPD, hRad, hL, ⟨jL, hjL⟩, hC⟩
  exact ⟨a, heq ▸ D, hlast _ heq⟩

private theorem schemeKernelOfSameSubgroup {A B : GroupScheme k} {q : A ⟶ B}
    {M N : ClosedSubgroup A} (hN : IsSchemeKernel q N) (hMN : SameSubgroup M N) :
    IsSchemeKernel q M := by
  obtain ⟨e, he⟩ := subgroupIso_of_same hMN
  let F := Grp.forget (SchemeOver k)
  apply hN.of_iso' (F.mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change F.map (e.hom ≫ N.inclusion) = M.inclusion.hom.hom ≫ 𝟙 _
    rw [he, Category.comp_id]
    rfl
  · exact toUnit_unique _ _
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

private theorem subgroupTransportOfFactor {H : GroupScheme k}
    {A B : ClosedSubgroup H} (g : 𝟙_ (SchemeOver k) ⟶ H.X)
    (f : A.group.X ⊗ 𝟙_ (SchemeOver k) ⟶ B.group.X)
    (hf : f ≫ B.inclusion.hom.hom = conjugateFamily A.inclusion g) :
    IsSubgroupOf (transportSubgroup A (innerIso g)) B := by
  apply factor_group_through_subgroup B (transportSubgroup A (innerIso g)).inclusion
    (lift (𝟙 _) (toUnit _) ≫ f)
  change (lift (𝟙 _) (toUnit _) ≫ f) ≫ B.inclusion.hom.hom =
    A.inclusion.hom.hom ≫ (innerMap g).hom.hom
  rw [Category.assoc, hf, comp_conjugateFamily, lift_snd_assoc, lift_fst_assoc,
    Category.id_comp, comp_innerMap]

private theorem maximalSplitToriInSameLevi (P : ClosedSubgroup G.val)
    (hP : IsMinimalParabolic G P) {c : Cocharacter G.val}
    (D : LimitDecomposition c) (e : P.group ≅ D.parabolic.group)
    (he : e.hom ≫ D.parabolic.inclusion = P.inclusion)
    (hL : IsReductive (closedSubgroupAlgebraicGroup D.centralizer))
    (S T : ClosedSubgroup P.group) (hS : IsMaximalSplitTorus S) (hT : IsMaximalSplitTorus T)
    (jS : S.group ⟶ D.centralizer.group) (jT : T.group ⟶ D.centralizer.group)
    (hSg : jS ≫ D.centralizer.inclusion = S.inclusion ≫ P.inclusion)
    (hTg : jT ≫ D.centralizer.inclusion = T.inclusion ≫ P.inclusion) :
    SameSubgroup S T := by
  let L := closedSubgroupAlgebraicGroup D.centralizer
  let s := D.sectionMap ≫ e.inv
  have hs : s ≫ P.inclusion = D.centralizer.inclusion := by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc, D.section_in_G]
  have hS' : IsSubgroupOf (subgroupOfSubgroup P S) D.centralizer := ⟨jS, hSg⟩
  have hT' : IsSubgroupOf (subgroupOfSubgroup P T) D.centralizer := ⟨jT, hTg⟩
  let A := restrictSubgroup (subgroupOfSubgroup P S) D.centralizer jS hSg
  let B := restrictSubgroup (subgroupOfSubgroup P T) D.centralizer jT hTg
  have hComm (X : SchemeOver k) (a : X ⟶ A.group.X) (b : X ⟶ B.group.X) :
      Commute (a ≫ A.inclusion.hom.hom) (b ≫ B.inclusion.hom.hom) := by
    have hc := leviCentralizesSplitTorus P hP D e hL B hT.1 (a ≫ A.inclusion.hom.hom)
    simpa only [Category.id_comp] using (centralizes_iff _ _).1 hc X (𝟙 _) b
  obtain ⟨V, hV, ⟨a, ha⟩, ⟨b, hb⟩⟩ := splitTorusUpperBound L A B hS.1 hT.1 hComm
  let Lp := restrictSubgroup D.centralizer P s hs
  let W := subgroupOfSubgroup Lp V
  haveI := inclusion_mono P
  have liftInclusion {R : ClosedSubgroup P.group}
      (j : R.group ⟶ D.centralizer.group)
      (hj : j ≫ D.centralizer.inclusion = R.inclusion ≫ P.inclusion)
      (v : R.group ⟶ V.group) (hv : v ≫ V.inclusion = j) : IsSubgroupOf R W := by
    refine ⟨v, (cancel_mono P.inclusion).mp ?_⟩
    change (v ≫ V.inclusion ≫ s) ≫ P.inclusion = R.inclusion ≫ P.inclusion
    calc
      _ = (v ≫ V.inclusion) ≫ s ≫ P.inclusion := by simp only [Category.assoc]
      _ = _ := by rw [hs, hv, hj]
  have hSW := liftInclusion jS hSg a ha
  have hTW := liftInclusion jT hTg b hb
  exact ⟨subgroupOf_trans hSW (hT.2 W hV hTW), subgroupOf_trans hTW (hS.2 W hV hSW)⟩

/-- Two maximal split tori of a minimal parabolic are conjugate by
a rational point of its unipotent radical. -/
theorem maximalSplitToriConjugateByRadical : MaximalSplitToriConjugateByRadical.{u} := by
  intro k _ G P hP U hU S T hS hT
  obtain ⟨c, D, hD, hRadD, hRedD, ⟨jS, hjS⟩, _⟩ := minimalParabolicLevi G P hP S hS
  obtain ⟨d, E, hE, hRadE, _, ⟨jT, hjT⟩, _⟩ := minimalParabolicLevi G P hP T hT
  obtain ⟨e, he⟩ := subgroupIso_of_same hD
  obtain ⟨f, hf⟩ := subgroupIso_of_same hE
  let P' := closedSubgroupAlgebraicGroup P
  let L := closedSubgroupAlgebraicGroup D.centralizer
  let q := e.hom ≫ D.limit
  let p := f.hom ≫ E.limit
  let s := D.sectionMap ≫ e.inv
  let t := E.sectionMap ≫ f.inv
  have hs : s ≫ P.inclusion = D.centralizer.inclusion := by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc, D.section_in_G]
  have ht : t ≫ P.inclusion = E.centralizer.inclusion := by
    rw [Category.assoc, ← hf, f.inv_hom_id_assoc, E.section_in_G]
  have hqs : s ≫ q = 𝟙 D.centralizer.group := by simp [s, q, D.section_limit]
  have hpt : t ≫ p = 𝟙 E.centralizer.group := by simp [t, p, E.section_limit]
  let LS := restrictSubgroup D.centralizer P s hs
  let LT := restrictSubgroup E.centralizer P t ht
  let N := pushSubgroup e.symm (contractingSubgroup D)
  let M := pushSubgroup f.symm (contractingSubgroup E)
  have hN : IsUnipotentRadical P' N :=
    radical_transport (A := closedSubgroupAlgebraicGroup D.parabolic) (B := P')
      e.symm (contractingSubgroup D) hRadD.1
  have hM : IsUnipotentRadical P' M :=
    radical_transport (A := closedSubgroupAlgebraicGroup E.parabolic) (B := P')
      f.symm (contractingSubgroup E) hRadE.1
  have hNU : SameSubgroup U N := ⟨hN.2.2 U hU.1 hU.2.1, hU.2.2 N hN.1 hN.2.1⟩
  have hNM : SameSubgroup N M := ⟨hM.2.2 N hN.1 hN.2.1, hN.2.2 M hM.1 hM.2.1⟩
  have hkN : IsSchemeKernel q N := limitKernelUnderIso D e
  have hkM : IsSchemeKernel p M := limitKernelUnderIso E f
  have hkU : IsSchemeKernel q U := schemeKernelOfSameSubgroup hkN hNU
  have hLS : IsIso (LS.inclusion ≫ q) := by change IsIso (s ≫ q); rw [hqs]; infer_instance
  obtain ⟨i, hi⟩ := splitQuotientIso hqs hpt hkN hkM hNM
  have hiq : p ≫ i.inv = q := by
    rw [← hi, Category.assoc, i.hom_inv_id, Category.comp_id]
  have hLT : IsIso (LT.inclusion ≫ q) := by
    change IsIso (t ≫ q)
    rw [← hiq, ← Category.assoc, hpt, Category.id_comp]
    infer_instance
  obtain ⟨a, ha⟩ :=
    Relative.LeviConjugacy.leviConjugacy G P hP.1 U hU L q hkU LT LS hLT hLS
  let g := a ≫ U.inclusion.hom.hom
  have htr : Specs.LeviConjugacy.Transports LT LS g :=
    (ha _ a).2 (by rw [toUnit_unique (toUnit (𝟙_ (SchemeOver k))) (𝟙 _), Category.id_comp])
  obtain ⟨⟨v, hv⟩, _⟩ := htr
  have hconj := subgroupTransportOfFactor (A := LT) (B := LS) g v hv
  let T' := transportSubgroup T (innerIso g)
  haveI := inclusion_mono P
  have hTL : IsSubgroupOf T LT := ⟨jT, (cancel_mono P.inclusion).1 (by
    change jT ≫ t ≫ P.inclusion = T.inclusion ≫ P.inclusion
    rw [ht]
    exact hjT)⟩
  obtain ⟨j, hj⟩ := subgroupOf_trans (transportSubgroupOf hTL (innerIso g)) hconj
  have hj' : j ≫ D.centralizer.inclusion = T'.inclusion ≫ P.inclusion := by
    rw [← hs, ← Category.assoc]
    exact congrArg (· ≫ P.inclusion) hj
  have hident : SameSubgroup T' T' := ⟨⟨𝟙 _, Category.id_comp _⟩, ⟨𝟙 _, Category.id_comp _⟩⟩
  have hT' : IsMaximalSplitTorus T' := maximalSplitOfConjugate
    (conjugates_of_sameTransport (A := T) (B := T') g hident) hT
  have hsame := maximalSplitToriInSameLevi P hP D e he hRedD S T' hS hT' jS j hjS hj'
  refine ⟨a⁻¹, ?_⟩
  have hinv := conjugates_inverse
    (conjugates_of_sameTransport (A := T) (B := S) g ⟨hsame.2, hsame.1⟩)
  simpa only [g, GrpObj.inv_comp] using hinv

/-- Maximal split tori are conjugate under the ground-field points of the
connected reductive group. -/
theorem maximalSplitToriConjugate : MaximalSplitToriConjugate.{u} :=
  globalConjugacyOfLocal
    splitTorusConjugateIntoMinimalParabolic maximalSplitToriConjugateByRadical

end

end LinearAlgebraicGroups.Relative.MaximalSplitTori
