import Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
import LinearAlgebraicGroups.Arithmetic.QuasiSplitComponentDescent
import LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
import LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
import LinearAlgebraicGroups.Relative.MaximalSplitTori
import LinearAlgebraicGroups.Relative.RelativeBruhat
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Pointwise TensorProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration

open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.QuasiSplitLocalGeneration
open Specs.QuasiSplitPinnedPairModel (BorelPair Marking)
open Specs.GeometricRadicals (IsSemisimple IsReductive)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open Specs.Relative.RelativeWeylScheme (QuotientData rationalProjection)
open Specs.QuasiSplitOrbitAmbientWords (RationalPoints onRational groundPointIso)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.RankOneFlag (SameSubgroup)
open CocharacterDynamics (LimitDecomposition)
open private rationalSectionsEquiv from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open Specs.CharacterDescent (Cocharacter)

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

private abbrev rationalSubgroup {G : GroupScheme F} (H : ClosedSubgroup G) :=
  SubgroupSections H (𝟙_ (SchemeOver F))
open Specs.SimpleParabolicProduct (doubleCoset)

open ValuativeRel in
theorem infiniteOfIsLocalField (F : Type u) [Field F] (hF : IsLocalField F) : Infinite F := by
  rcases hF with ⟨r, t, h⟩ | ⟨e⟩ | ⟨e⟩
  · let := r
    let := t
    let := h
    obtain ⟨a, ha, hval⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
    apply Infinite.of_injective (fun n : ℕ => a ^ n)
    intro i j hij
    apply pow_right_injective₀ (a := valuation F a)
      (zero_lt_iff.mpr ((valuation F).ne_zero_iff.mpr ha)) hval.ne
    simpa only [map_pow] using congrArg (valuation F) hij
  · obtain ⟨e⟩ := e
    exact Infinite.of_injective e.symm e.symm.injective
  · obtain ⟨e⟩ := e
    exact Infinite.of_injective e.symm e.symm.injective

private theorem generationFromDoubleCosets {S P : ClosedSubgroup G.val}
    (H : Subgroup (𝟙_ (SchemeOver F) ⟶ G.val.X)) (D : QuotientData S)
    (n : D.splitImage.labels → (𝟙_ (SchemeOver F) ⟶ D.normalizer.group.X))
    (hcover : (⋃ w, doubleCoset P (𝟙_ (SchemeOver F))
      (n w ≫ D.normalizer.inclusion.hom.hom)) = Set.univ)
    (hP : rationalSubgroup P ≤ H)
    (hn : ∀ w, n w ≫ D.normalizer.inclusion.hom.hom ∈ H) : H = ⊤ := by
  apply top_unique
  intro g _
  have hg : g ∈ ⋃ w, doubleCoset P (𝟙_ (SchemeOver F))
      (n w ≫ D.normalizer.inclusion.hom.hom) := hcover.symm ▸ Set.mem_univ _
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hg
  obtain ⟨pn, hpn, q, hq, rfl⟩ := Set.mem_mul.mp hw
  obtain ⟨p, hp, m, hm, rfl⟩ := Set.mem_mul.mp hpn
  have hm' : m = n w ≫ D.normalizer.inclusion.hom.hom := by
    have hu : toUnit (𝟙_ (SchemeOver F)) = 𝟙 _ := by
      exact isTerminalTensorUnit.hom_ext _ _
    simpa only [Set.mem_singleton_iff, hu, Category.id_comp] using hm
  exact H.mul_mem (H.mul_mem (hP hp) (hm' ▸ hn w)) (hP hq)

private theorem generationFromRelativeBruhat (hG : IsReductive G)
    (S P : ClosedSubgroup G.val) (hS : IsMaximalSplitTorus S) (hP : IsMinimalParabolic G P)
    (hSP : IsSubgroupOf S P) (H : Subgroup (𝟙_ (SchemeOver F) ⟶ G.val.X))
    (hPH : rationalSubgroup P ≤ H)
    (hgen : ∀ D : QuotientData S, ∃ s : Set D.splitImage.labels, Subgroup.closure s = ⊤ ∧
      ∀ w ∈ s, ∃ n : 𝟙_ (SchemeOver F) ⟶ D.normalizer.group.X,
        rationalProjection D n = D.splitImage.constantGroup.sectionPoint w ∧
        n ≫ D.normalizer.inclusion.hom.hom ∈ H) : H = ⊤ := by
  classical
  obtain ⟨D, hZ, e, he, _, hbruhat⟩ :=
    Relative.RelativeBruhat.relativeBruhat G hG S P hS hP hSP
  let := hZ
  let label : (𝟙_ (SchemeOver F) ⟶ D.normalizer.group.X) →* D.splitImage.labels :=
    e.toMonoidHom.comp (QuotientGroup.mk' _)
  let incl : (𝟙_ (SchemeOver F) ⟶ D.normalizer.group.X) →*
      (𝟙_ (SchemeOver F) ⟶ G.val.X) :=
    IsMonHom.monoidHom D.normalizer.inclusion.hom.hom _
  obtain ⟨s, hs, hrep⟩ := hgen D
  obtain ⟨q, hq⟩ := rationalSectionsEquiv D.splitImage.constantGroup
  have hlabel_inj : Function.Injective D.splitImage.constantGroup.sectionPoint := by
    intro x y h
    exact q.injective ((hq x).trans (h.trans (hq y).symm))
  have hmap : Subgroup.map label (H.comap incl) = ⊤ := by
    apply top_unique
    rw [← hs]
    apply (Subgroup.closure_le _).2
    intro w hw
    obtain ⟨n, hn, hnH⟩ := hrep w hw
    exact ⟨n, hnH, hlabel_inj ((he n).symm.trans hn)⟩
  have hall (w : D.splitImage.labels) : ∃ n, n ∈ H.comap incl ∧ label n = w := by
    have hm : w ∈ Subgroup.map label (H.comap incl) := hmap.symm ▸ Subgroup.mem_top _
    exact hm
  choose n hnH hn using hall
  have hn' (w : D.splitImage.labels) :
      Specs.Relative.RelativeWeylScheme.rationalProjection D (n w) =
        D.splitImage.constantGroup.sectionPoint w := (he (n w)).trans (congrArg _ (hn w))
  exact generationFromDoubleCosets H D n (hbruhat n hn').1 hPH hnH

private theorem rationalLimitFactorization {G : GroupScheme F} {c : Cocharacter G}
    (D : LimitDecomposition c) (g : 𝟙_ (SchemeOver F) ⟶ G.X)
    (hg : g ∈ rationalSubgroup D.parabolic) :
    ∃ t ∈ rationalSubgroup D.centralizer, ∃ a ∈ rationalSubgroup D.contracting, g = t * a := by
  let m := CocharacterDynamics.multiplyFactors D.sectionMap D.contractingToParabolic
  have : IsIso m := D.product_iso
  change ∃ p : 𝟙_ (SchemeOver F) ⟶ D.parabolic.group.X,
    p ≫ D.parabolic.inclusion.hom.hom = g at hg
  obtain ⟨p, rfl⟩ := hg
  let z := p ≫ inv m
  let t := z ≫ fst _ _
  let a := z ≫ snd _ _
  refine ⟨t ≫ D.centralizer.inclusion.hom.hom, ⟨t, rfl⟩,
    a ≫ D.contracting.inclusion.hom.hom, ⟨a, rfl⟩, ?_⟩
  change p ≫ D.parabolic.inclusion.hom.hom = _
  have hp : z ≫ m = p := by
    rw [show z = p ≫ inv m from rfl, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hp]
  change (z ≫ CocharacterDynamics.multiplyFactors D.sectionMap D.contractingToParabolic) ≫
    D.parabolic.inclusion.hom.hom = _
  rw [CocharacterDynamics.multiplyFactors, MonObj.comp_mul, MonObj.mul_comp]
  have ht : D.sectionMap.hom.hom ≫ D.parabolic.inclusion.hom.hom =
      D.centralizer.inclusion.hom.hom :=
    congrArg (fun f : D.centralizer.group ⟶ G => f.hom.hom) D.section_in_G
  have ha : D.contractingToParabolic.hom.hom ≫ D.parabolic.inclusion.hom.hom =
      D.contracting.inclusion.hom.hom :=
    congrArg (fun f : D.contracting.group ⟶ G => f.hom.hom) D.contracting_in_G
  simp only [t, a, Category.assoc, ht, ha]

private theorem rationalSubgroup_mono {G : GroupScheme F} {A B : ClosedSubgroup G}
    (h : IsSubgroupOf A B) : rationalSubgroup A ≤ rationalSubgroup B := by
  intro x hx
  change ∃ a : 𝟙_ (SchemeOver F) ⟶ A.group.X, a ≫ A.inclusion.hom.hom = x at hx
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨j, hj⟩ := h
  refine ⟨a ≫ j.hom.hom, ?_⟩
  change (a ≫ j.hom.hom) ≫ B.inclusion.hom.hom = a ≫ A.inclusion.hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, hj]

open private sameSubgroupIso from LinearAlgebraicGroups.Relative.RationalFlagLifting
open private pushRadical from LinearAlgebraicGroups.Relative.LeviConjugacy
open private restrictSubgroup compose_restrict subgroupOfSubgroup_le
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

set_option backward.isDefEq.respectTransparency false in
private theorem borelPointsInGenerated (M : BorelPair G) (S : ClosedSubgroup G.val)
    (hS : IsMaximalSplitTorus S) (hB : IsMinimalParabolic G M.positive)
    (hSB : IsSubgroupOf S M.positive)
    (hC : RepresentsSubgroup M.torus (fun _ g ↦ Centralizes S.inclusion g))
    (H : Subgroup (𝟙_ (SchemeOver F) ⟶ G.val.X))
    (hT : rationalSubgroup M.torus ≤ H)
    (hU : rationalSubgroup (M.subgroup .positiveRadical) ≤ H) :
    rationalSubgroup M.positive ≤ H := by
  obtain ⟨j, hj⟩ := hSB
  let S' := restrictSubgroup S M.positive j hj
  have hSS : subgroupOfSubgroup M.positive S' = S := compose_restrict S M.positive j hj
  have hS' : IsMaximalSplitTorus S' := by
    constructor
    · exact hS.1
    · intro L hL hSL
      apply (subgroupOfSubgroup_le M.positive L S').mp
      rw [hSS]
      apply hS.2 _ hL
      rw [← hSS]
      exact (subgroupOfSubgroup_le M.positive S' L).mpr hSL
  obtain ⟨c, D, hD, hrad, _, _, hcent⟩ :=
    Relative.MaximalSplitTori.minimalParabolicLevi G M.positive hB S' hS'
  have hc : IsSubgroupOf D.centralizer M.torus := by
    have h := (hcent _ D.centralizer.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
    change Centralizes (j ≫ M.positive.inclusion) D.centralizer.inclusion.hom.hom at h
    rw [hj] at h
    obtain ⟨f, hf⟩ := (hC _ _).mp h
    exact factor_group_through_subgroup M.torus D.centralizer.inclusion f hf
  obtain ⟨e, he⟩ := sameSubgroupIso (show SameSubgroup D.parabolic M.positive from ⟨hD.2, hD.1⟩)
  have hrad' := pushRadical (A := closedSubgroupAlgebraicGroup D.parabolic)
    (B := closedSubgroupAlgebraicGroup M.positive) e hrad.1
  obtain ⟨a, ha⟩ := M.positiveUnipotentRadical.2.2 _ hrad'.1 hrad'.2.1
  have hDU : IsSubgroupOf D.contracting (M.subgroup .positiveRadical) := by
    refine ⟨a, ?_⟩
    change a ≫ M.positiveRadical.inclusion ≫ M.positive.inclusion = D.contracting.inclusion
    rw [← Category.assoc, ha]
    change (D.contractingToParabolic ≫ e.hom) ≫ M.positive.inclusion = _
    rw [Category.assoc, he, D.contracting_in_G]
  intro g hg
  obtain ⟨t, ht, a, ha, rfl⟩ :=
    rationalLimitFactorization D g (rationalSubgroup_mono hD.1 hg)
  exact H.mul_mem (hT (rationalSubgroup_mono hc ht)) (hU (rationalSubgroup_mono hDU ha))

private theorem generationInFiniteProduct {I : Type u} [Finite I] {A : I → Type v}
    [∀ i, Group (A i)] (U V : ∀ i, Subgroup (A i))
    (hgen : ∀ i, U i ⊔ V i = ⊤) :
    Subgroup.pi Set.univ U ⊔ Subgroup.pi Set.univ V = ⊤ := by
  classical
  simp only [Subgroup.sup_eq_closure] at hgen ⊢
  let H := Subgroup.closure ((Subgroup.pi Set.univ U : Set (∀ i, A i)) ∪
    (Subgroup.pi Set.univ V : Set (∀ i, A i)))
  apply top_unique
  intro x _
  apply Subgroup.pi_mem_of_mulSingle_mem x
  intro i
  have hlocal : Subgroup.closure ((U i : Set (A i)) ∪ (V i : Set (A i))) ≤
      H.comap (MonoidHom.mulSingle A i) := by
    apply (Subgroup.closure_le _).2
    intro a ha
    apply Subgroup.subset_closure
    rcases ha with ha | ha
    · exact Or.inl (by
        intro j _
        by_cases hj : j = i
        · subst j
          simpa using ha
        · simp [Pi.mulSingle_eq_of_ne hj])
    · exact Or.inr (by
        intro j _
        by_cases hj : j = i
        · subst j
          simpa using ha
        · simp [Pi.mulSingle_eq_of_ne hj])
  exact hlocal ((hgen i).symm ▸ Subgroup.mem_top (x i))


private theorem generationFromComponents [Infinite F] (hG : IsSemisimple G)
    (hsc : GeometricallySimplyConnected G) (M : BorelPair G)
    (simpleCase : ∀ {E : Type u} [Field E] [Infinite E] (J : AffineAlgebraicGroup E),
      IsAbsolutelyAlmostSimple J → GeometricallySimplyConnected J →
      ∀ N : BorelPair J, generatedByBorelRadicals N = ⊤) :
    generatedByBorelRadicals M = ⊤ := by
  classical
  obtain ⟨K, hK, hFK, hfd, hGal, A, P, D, lift, w, S, hB, hT, hD, hl, ha,
    hcmp, W, ρ, hρ, descent⟩ := QuasiSplitComponentDescent.componentDescent G hG hsc M
  letI := hK
  letI := hFK
  letI := hfd
  letI := hGal
  letI := ρ
  obtain ⟨t, d, pieces, p, ht, hd, hp, e, he, hmark⟩ := descent
  let U (o : _) := (onRational ((pieces o).pair.subgroup .positiveRadical).inclusion).range
  let V (o : _) := (onRational ((pieces o).pair.subgroup .negativeRadical).inclusion).range
  have hgen (o : _) : U o ⊔ V o = ⊤ := by
    let E := Specs.QuasiSplitComponentDescent.orbitField (F := F) (K := K) o.out
    letI : Infinite E := Infinite.of_injective (algebraMap F E) (algebraMap F E).injective
    exact simpleCase _ (pieces o).absolutelyAlmostSimple (pieces o).simplyConnected (pieces o).pair
  let f := e.toMonoidHom
  have himage (m : Marking) :
      ((onRational (M.subgroup m).inclusion).range.map f) =
      Subgroup.pi Set.univ (fun o => (onRational ((pieces o).pair.subgroup m).inclusion).range) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact fun o _ => (hmark m x).mp hx o
    · intro hy
      refine ⟨e.symm y, (hmark m _).mpr ?_, e.apply_symm_apply y⟩
      intro o
      rw [e.apply_symm_apply]
      exact hy o (Set.mem_univ o)
  have hmap : (generatedByBorelRadicals M).map f = ⊤ := by
    unfold generatedByBorelRadicals
    rw [Subgroup.map_sup, himage, himage]
    exact generationInFiniteProduct U V hgen
  apply top_unique
  intro x _
  obtain ⟨y, hy, hyx⟩ : f x ∈ (generatedByBorelRadicals M).map f :=
    hmap.symm ▸ Subgroup.mem_top _
  exact e.injective hyx ▸ hy

open Specs.GeometricBorelConjugacy (ConjugatesSubgroups)
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.AbstractPairing (Root)
open Specs.DatumAndWeyl (Identification)
open Specs.Pinning (AttachedDatum)
open Specs.QuasiSplitOrbitAmbientWords (BorelRadical extendPoint)
open Specs.QuasiSplitOrbitLevis
open Specs.Arithmetic.QuasiSplitFixedWeyl
open Specs.Relative.RelativeWeylScheme (rationalProjection)
open private conjugates_iff_iso conjugationIso from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private conjugates_of_normalizes from LinearAlgebraicGroups.RootData.BorelNormalizer
open private normalizes_of_conjugates_self from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private largestSplitSubtorus_preserved relativeFixedComparison scalarDatumAction
  length_add_of_descents generation_pulledBack from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
open private labelConjugation inducedConjugation_unique from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private automorphism_eq_of_weight from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private attachedBase_regular from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private orbitRoots_eq_fiber from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
open private comp_conjugateFamily from LinearAlgebraicGroups.Affine.Stabilizers

private def borelRadicals (M : BorelPair G) : Bool → BorelRadical G
  | true => ⟨M.positive, M.positiveBorel, M.positiveRadical, M.positiveUnipotentRadical⟩
  | false => ⟨M.negative, M.negativeBorel, M.negativeRadical, M.negativeUnipotentRadical⟩

private theorem oppositeRadicalWords_eq (M : BorelPair G) :
    oppositeRadicalWords (borelRadicals M) = generatedByBorelRadicals M := by
  unfold oppositeRadicalWords generatedByBorelRadicals
  rw [Subgroup.sup_eq_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨s, hs⟩
    cases s
    · exact Or.inr hs
    · exact Or.inl hs
  · rintro (h | h)
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩

private def terminalPointHom (J : GroupScheme F) :
    (𝟙_ (SchemeOver F) ⟶ J.X) →* RationalPoints J where
  toFun x := (groundPointIso F).inv ≫ x
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

private theorem terminalSubgroup_mem {J : GroupScheme F} (S : ClosedSubgroup J)
    (x : 𝟙_ (SchemeOver F) ⟶ J.X) :
    x ∈ rationalSubgroup S ↔ terminalPointHom J x ∈ (onRational S.inclusion).range := by
  change (∃ p : 𝟙_ (SchemeOver F) ⟶ S.group.X, p ≫ S.inclusion.hom.hom = x) ↔
    ∃ p : RationalPoints S.group, p ≫ S.inclusion.hom.hom = (groundPointIso F).inv ≫ x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(groundPointIso F).inv ≫ p, Category.assoc _ _ _⟩
  · rintro ⟨p, hp⟩
    refine ⟨(groundPointIso F).hom ≫ p, ?_⟩
    erw [Category.assoc, hp, Iso.hom_inv_id_assoc]

private theorem normalizesSplitSubtorus (T : ClosedSubgroup G.val)
    (S : ClosedSubgroup T.group) (hS : IsLargestSplitSubtorus S)
    (g : 𝟙_ (SchemeOver F) ⟶ G.val.X) (hg : Normalizes T.inclusion g) :
    Normalizes (subgroupOfSubgroup T S).inclusion g := by
  obtain ⟨a, ha⟩ := (conjugates_iff_iso g T T).mp (conjugates_of_normalizes T hg)
  obtain ⟨b, hb⟩ := largestSplitSubtorus_preserved S hS a
  apply normalizes_of_conjugates_self
  apply (conjugates_iff_iso g _ _).mpr
  refine ⟨b, ?_⟩
  change b.hom ≫ (S.inclusion ≫ T.inclusion) =
    (S.inclusion ≫ T.inclusion) ≫ (conjugationIso g).hom
  rw [← Category.assoc, hb, Category.assoc, ha, Category.assoc]

private theorem conjugateLe_precomp {J L : GroupScheme F} (i : L ⟶ J)
    {X Y : SchemeOver F} (f : X ⟶ Y) (g : Y ⟶ J.X) (h : ConjugateLe i g) :
    ConjugateLe i (f ≫ g) := by
  obtain ⟨z, hz⟩ := h
  refine ⟨lift (fst L.X X) (snd L.X X ≫ f) ≫ z, ?_⟩
  rw [Category.assoc, hz, comp_conjugateFamily, lift_fst_assoc, lift_snd_assoc]
  rfl

private theorem absoluteLabel_unique {K : Type u} [Field K] {J : AffineAlgebraicGroup K}
    {T : ClosedSubgroup J.val} [IsCommMonObj T.group.X] {D : Specs.AbstractPairing.Datum T}
    (A B : Identification D) (a b : D.rootDatum.weylGroup)
    (n : 𝟙_ (SchemeOver K) ⟶ A.normalizer.group.X)
    (m : 𝟙_ (SchemeOver K) ⟶ B.normalizer.group.X)
    (he : n ≫ A.normalizer.inclusion.hom.hom = m ≫ B.normalizer.inclusion.hom.hom)
    (ha : n ≫ A.quotient.hom.hom = A.image.constantGroup.sectionPoint (A.labelEquiv a))
    (hb : m ≫ B.quotient.hom.hom = B.image.constantGroup.sectionPoint (B.labelEquiv b)) :
    a = b := by
  have hA := labelConjugation A.image (A.labelEquiv a) n ha
  rw [he] at hA
  have eq := inducedConjugation_unique hA (labelConjugation B.image (B.labelEquiv b) m hb)
  apply Subtype.ext
  apply automorphism_eq_of_weight
  intro χ
  rw [A.characterAction, B.characterAction, A.image.characterAction, B.image.characterAction, eq]

open private intersection pullbackIntersection from LinearAlgebraicGroups.Relative.ParabolicIntersection
open private subgroup_of_sections inclusion_mem_sections
  from LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection

private theorem rationalOppositePair (M : BorelPair G) :
    Nonempty (RationalOppositePair M.torus (borelRadicals M true).borel
      (borelRadicals M false).borel) := by
  let P := M.positive
  let Q := M.negative
  let I := intersection P Q
  have hI := pullbackIntersection P Q
  have hTI : IsSubgroupOf M.torus I := by
    apply subgroup_of_sections
    exact (hI _ _).2 ((M.intersection _ _).1 (inclusion_mem_sections M.torus))
  have hIT : IsSubgroupOf I M.torus := by
    apply subgroup_of_sections
    exact (M.intersection _ _).2 ((hI _ _).1 (inclusion_mem_sections I))
  obtain ⟨e, he⟩ := sameSubgroupIso (show SameSubgroup M.torus I from ⟨hTI, hIT⟩)
  refine ⟨⟨M.positiveBorel, M.negativeBorel,
    e.hom ≫ pullback.fst P.inclusion Q.inclusion,
    e.hom ≫ pullback.snd P.inclusion Q.inclusion, ?_, ?_⟩⟩
  · refine IsPullback.of_iso_pullback ⟨?_⟩ e rfl rfl
    exact (Category.assoc _ _ _).trans
      ((congrArg (e.hom ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans he

section OrbitAssembly

open RootPairing
open Specs.Pinning (Pinning)
open Specs.RootGroups (AdditiveLine)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.SimpleRoots (IsBaseFor evaluate wordLength)
open Specs.StandardParabolicLevi (leviRoots parabolicWeylGroup)
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies

variable {K : Type u} [Field K] [Algebra F K]

private theorem faceWord_isLongest {P : Specs.Pinning.SplitBorelPair K}
    (D : AttachedDatum P) (I : Set (Root P.T)) :
    letI := D.comm
    ∀ (w : D.datum.rootDatum.weylGroup),
      I ⊆ D.base.support → ∀ (c : Cocharacter P.T.group),
      Specs.BorelsAndChambers.IsRegular P.T c →
      IsBaseFor D.datum.rootDatum (evaluate D.datum c) D.base →
      w ∈ parabolicWeylGroup D.datum I →
      (∀ j ∈ leviRoots D.datum I, 0 < evaluate D.datum c (D.datum.rootDatum.root j) →
        evaluate D.datum c (w.val.weightEquiv (D.datum.rootDatum.root j)) < 0) →
      IsLongest D.datum.rootDatum D.base I w := by
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  intro w hI c hc hb hw hneg
  let p := D.datum.rootDatum
  let f := evaluate D.datum c
  have hreg (j : Root P.T) : f (p.root j) ≠ 0 := by
    change p.toLinearMap (p.root j) (Additive.ofMul c) ≠ 0
    rw [D.datum.root_eq, D.datum.pairing_eq]
    exact hc j
  have hdesc (j : Root P.T) (hj : j ∈ I) : f (p.root (p.weylGroupToPerm w j)) < 0 := by
    change f (p.root (w.val.indexEquiv j)) < 0
    have hwj := w.val.toHom.root_weightMap_apply p p j
    change w.val.weightEquiv (p.root j) = p.root (w.val.indexEquiv j) at hwj
    rw [← hwj]
    exact hneg j (Submodule.subset_span ⟨j, hj, rfl⟩) ((hb.simple_iff j).mp (hI hj)).1
  refine ⟨hw, fun a ha => ?_⟩
  have h := length_add_of_descents p f hreg D.base hb hI hdesc ha
  change wordLength p D.base a ≤ wordLength p D.base w
  omega

private theorem basedAction_stable {P : Specs.Pinning.SplitBorelPair K}
    (D : AttachedDatum P) (a : Aut D.toBased) (i : Root P.T) : letI := D.comm
    a.asIso.hom.val.indexEquiv i ∈ D.base.support ↔ i ∈ D.base.support := by
  letI := D.comm
  let t := a.asIso.hom.val.indexEquiv
  have h : t '' (D.base.support : Set (Root P.T)) = (D.base.support : Set (Root P.T)) :=
    a.asIso.hom.property
  constructor
  · intro hi
    obtain ⟨j, hj, eq⟩ : t i ∈ t '' (D.base.support : Set (Root P.T)) := h.symm ▸ hi
    exact t.injective eq ▸ hj
  · intro hi
    change t i ∈ (D.base.support : Set (Root P.T))
    rw [← h]
    exact ⟨i, hi, rfl⟩

private theorem terminalNormalizerPoint {T : ClosedSubgroup G.val} (g : RationalPoints G.val)
    (hg : Normalizes T.inclusion g) :
    Normalizes T.inclusion ((groundPointIso F).hom ≫ g) := by
  have h := (LinearAlgebraicGroups.normalizesIff F T.inclusion T.isClosedImmersion _ _).mp hg
  apply (LinearAlgebraicGroups.normalizesIff F T.inclusion T.isClosedImmersion _ _).mpr
  refine ⟨conjugateLe_precomp _ (groundPointIso F).hom g h.1, ?_⟩
  have eq : ((groundPointIso F).hom ≫ g)⁻¹ = (groundPointIso F).hom ≫ g⁻¹ :=
    (GrpObj.comp_inv (groundPointIso F).hom g).symm
  rw [eq]
  exact conjugateLe_precomp _ (groundPointIso F).hom g⁻¹ h.2

private theorem terminalAbsoluteLabel {V : ClosedSubgroup (baseChangedAlgebraicGroup K G).val}
    [IsCommMonObj V.group.X] {D : Specs.AbstractPairing.Datum V}
    (W : Identification D) (w : D.rootDatum.weylGroup)
    (g : RationalPoints G.val) (n : RationalPoints W.normalizer.group)
    (h : onRational W.normalizer.inclusion n = extendPoint (K := K) G.val g)
    (hw : onRational W.quotient n = toUnit _ ≫ W.image.constantGroup.sectionPoint (W.labelEquiv w)) :
    ∃ r : 𝟙_ (SchemeOver K) ⟶ W.normalizer.group.X,
      r ≫ W.normalizer.inclusion.hom.hom = scalarExtendedRationalPoint K ((groundPointIso F).hom ≫ g) ∧
      r ≫ W.quotient.hom.hom = W.image.constantGroup.sectionPoint (W.labelEquiv w) := by
  refine ⟨(groundPointIso K).hom ≫ n, ?_, ?_⟩
  · have he := congrArg ((groundPointIso K).hom ≫ ·) h
    change (groundPointIso K).hom ≫ n ≫ W.normalizer.inclusion.hom.hom =
      (groundPointIso K).hom ≫ (groundPointIso K).inv ≫
        scalarExtendedRationalPoint K ((groundPointIso F).hom ≫ g) at he
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using he
  · have he := congrArg ((groundPointIso K).hom ≫ ·) hw
    change (groundPointIso K).hom ≫ n ≫ W.quotient.hom.hom =
      (groundPointIso K).hom ≫ toUnit _ ≫ W.image.constantGroup.sectionPoint (W.labelEquiv w) at he
    have hu : (groundPointIso K).hom ≫ toUnit _ = 𝟙 (𝟙_ (SchemeOver K)) :=
      isTerminalTensorUnit.hom_ext _ _
    simpa only [Category.assoc, ← Category.assoc (groundPointIso K).hom (toUnit _), hu,
      Category.id_comp] using he

private theorem transferAbsoluteLabel {J : AffineAlgebraicGroup K} {V : ClosedSubgroup J.val}
    [IsCommMonObj V.group.X] {D : Specs.AbstractPairing.Datum V}
    (A B : Identification D) (w : D.rootDatum.weylGroup)
    (n : 𝟙_ (SchemeOver K) ⟶ B.normalizer.group.X)
    (hn : n ≫ B.quotient.hom.hom = B.image.constantGroup.sectionPoint (B.labelEquiv w)) :
    ∃ r : 𝟙_ (SchemeOver K) ⟶ A.normalizer.group.X,
      r ≫ A.normalizer.inclusion.hom.hom = n ≫ B.normalizer.inclusion.hom.hom ∧
      r ≫ A.quotient.hom.hom = A.image.constantGroup.sectionPoint (A.labelEquiv w) := by
  obtain ⟨r, hr⟩ := (A.representsNormalizer _ _).mp
    ((B.representsNormalizer _ _).mpr ⟨n, rfl⟩)
  obtain ⟨l, hl⟩ := rationalSectionsEquiv A.image.constantGroup
  obtain ⟨v, hv⟩ := l.surjective (r ≫ A.quotient.hom.hom)
  have hvl := hv.symm.trans (hl v)
  have eq : A.labelEquiv.symm v = w :=
    absoluteLabel_unique A B _ _ r n hr (by simpa only [MulEquiv.apply_symm_apply] using hvl) hn
  refine ⟨r, hr, ?_⟩
  rw [← eq, MulEquiv.apply_symm_apply]
  exact hvl

open Specs.QuasiSplitOrbitTorusProduct (OrbitTorusDecomposition CocharacterLattice)

private theorem torusProductWords {I : Type u} [Finite I]
    (T : ClosedSubgroup G.val) (ρ : Gal(K/F) →* Equiv.Perm I)
    (b : Module.Basis I ℤ (CocharacterLattice K (closedSubgroupAlgebraicGroup T)))
    (C : @MulAction.orbitRel.Quotient Gal(K/F) I _ (MulAction.compHom I ρ) → ClosedSubgroup T.group)
    (hC : OrbitTorusDecomposition ρ (closedSubgroupAlgebraicGroup T) b C)
    (H : Subgroup (RationalPoints G.val))
    (hwords : ∀ o (t : RationalPoints (C o).group), onRational ((C o).inclusion ≫ T.inclusion) t ∈ H) :
    (onRational T.inclusion).range ≤ H := by
  classical
  letI : MulAction Gal(K/F) I := MulAction.compHom I ρ
  let O := MulAction.orbitRel.Quotient Gal(K/F) I
  obtain ⟨hcomm, _, _, _, _, hprod, _⟩ := hC
  letI : IsCommMonObj T.group.X := hcomm
  let J (o : O) := (C o).group
  let P : Fan J := limit.cone (Discrete.functor J)
  obtain ⟨e, he⟩ := hprod P (limit.isLimit _)
  rintro _ ⟨t, rfl⟩
  let s := onRational e.inv t
  have hs : onRational e.hom s = t := by
    change (t ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = t
    have h := congrArg (fun f : T.group ⟶ T.group => f.hom.hom) e.inv_hom_id
    erw [Category.assoc, ← Grp.comp_hom_hom, h, Category.comp_id]
  let f := onRational T.inclusion
  change t ∈ H.comap f
  rw [← hs]
  change ((groupPointsFunctor F).map e.hom).app _ s ∈ H.comap f
  rw [he]
  letI : Fintype O := Fintype.ofFinite O
  letI : CommGroup (RationalPoints T.group) := CategoryTheory.Hom.commGroup
  exact (H.comap f).prod_mem (fun o _ => hwords o (onRational (P.proj o) s))

private abbrev actualDiagramAction {T B : ClosedSubgroup G.val}
    (P : SplitPairOver (K := K) G T B) (D : AttachedDatum P.pair)
    (W : letI := D.comm; Identification D.datum) :
    letI := D.comm; Gal(K/F) →* D.datum.rootDatum.Aut :=
  letI : IsCommMonObj (baseChangedSubgroup K T P.torusClosed).group.X := D.comm
  scalarDatumAction (G := G) (T := T) (hT := P.torusClosed) W P.split

private def HasLongestOrbitLifts (M : BorelPair G)
    (P : SplitPairOver (K := K) G M.torus (borelRadicals M true).borel) (D : AttachedDatum P.pair)
    (W : letI := D.comm; Identification D.datum) : Prop :=
  letI := D.comm
  let p := D.datum.rootDatum
  let ρ := actualDiagramAction P D W
  ∀ i ∈ D.base.support,
    ∃ (w : p.weylGroup) (g : 𝟙_ (SchemeOver F) ⟶ G.val.X) (r : 𝟙_ (SchemeOver K) ⟶ W.normalizer.group.X),
      IsLongest p D.base (rootOrbit p ρ i) w ∧
      terminalPointHom G.val g ∈ generatedByBorelRadicals M ∧ Normalizes M.torus.inclusion g ∧
      r ≫ W.normalizer.inclusion.hom.hom = scalarExtendedRationalPoint K g ∧
      r ≫ W.quotient.hom.hom = W.image.constantGroup.sectionPoint (W.labelEquiv w)

set_option maxHeartbeats 185000 in
private theorem orbitLeviWords [FiniteDimensional F K] [IsGalois F K] [Infinite F]
    (M : BorelPair G) (hG : IsReductive G) (habs : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G)
    (P : SplitPairOver (K := K) G M.torus (borelRadicals M true).borel) (D : AttachedDatum P.pair)
    (W : letI := D.comm; Identification D.datum)
    {A₀ : AdditiveLine F} {A : AdditiveLine K} (U : RootSubgroupFamily P.pair.T)
    (p : Pinning A P.pair U) (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (m : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased)
    (hm : PreservesUnits m) (hpin : IsAmbientPinnedAction D p a m ω)
    (hAction : letI := D.comm
      letI : IsCommMonObj (baseChangedSubgroup K M.torus P.torusClosed).group.X := D.comm
     ∀ σ (i : Root P.pair.T),
      (actualDiagramAction P D W σ).indexEquiv i =
        (ω σ).asIso.hom.val.indexEquiv i) :
    (onRational M.torus.inclusion).range ≤ generatedByBorelRadicals M ∧ HasLongestOrbitLifts M P D W := by
  classical
  letI := D.comm
  letI : IsCommMonObj (baseChangedSubgroup K M.torus P.torusClosed).group.X := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  obtain ⟨pair⟩ := rationalOppositePair M
  obtain ⟨L, b, c, _, _, htorus, _, hfaces⟩ :=
    QuasiSplitOrbitLevis.rationalOrbitLevis G M.torus (borelRadicals M) P D pair hG M.isTorus
      M.maximal habs hsc U p a m ω hm hpin
  let ρ : Gal(K/F) →* Equiv.Perm D.base.support := (simplePermutation D).comp ω
  letI : MulAction Gal(K/F) D.base.support := MulAction.compHom D.base.support ρ
  let O := MulAction.orbitRel.Quotient Gal(K/F) D.base.support
  let q : D.base.support → O := Quotient.mk (MulAction.orbitRel Gal(K/F) D.base.support)
  have hΓ := oppositeRadicalWords_eq M
  constructor
  · apply torusProductWords M.torus ρ b (fun o => (L o).embeddedTorus D) htorus
    intro o t
    obtain ⟨_, _, _, _, _, _, _, _, hw⟩ := hfaces o
    exact hΓ ▸ (hw.1 t).2
  · intro i hi
    let j : D.base.support := ⟨i, hi⟩
    let o := q j
    let I := Subtype.val '' {j' | q j' = o}
    let δ := actualDiagramAction P D W
    have heq : I = rootOrbit D.datum.rootDatum δ i := by
      rw [show I = orbitRootSet D ω j from orbitRoots_eq_fiber D ω j]
      apply Set.Subset.antisymm
      · rintro _ ⟨j', ⟨σ, rfl⟩, rfl⟩
        exact ⟨σ, hAction σ i⟩
      · rintro _ ⟨σ, rfl⟩
        exact ⟨ρ σ j, ⟨σ, rfl⟩, (hAction σ i).symm⟩
    obtain ⟨_, _, _, _, _, _, _, _, hwords⟩ := hfaces o
    obtain ⟨c', W', x, v', n', hreg', hbase', _, hg, hn, hmem, hneg, hproj, hlabel⟩ := hwords.2
    have hlong : IsLongest D.datum.rootDatum D.base (rootOrbit D.datum.rootDatum δ i) v' := by
      rw [← heq]
      exact faceWord_isLongest D I v' (L o).simple c' hreg' hbase' hmem hneg
    let g₀ := onRational ((L o).derived.inclusion ≫ (L o).limit.centralizer.inclusion) x
    let g := (groundPointIso F).hom ≫ g₀
    obtain ⟨s, hs, hsl⟩ := terminalAbsoluteLabel (G := G) (V := P.pair.T) (D := D.datum)
      W' v' g₀ n' hproj hlabel
    obtain ⟨r, hr, hrl⟩ := transferAbsoluteLabel W W' v' s hsl
    refine ⟨v', g, r, hlong, ?_, terminalNormalizerPoint g₀ hn, hr.trans hs, hrl⟩
    change (groundPointIso F).inv ≫ (groundPointIso F).hom ≫ g₀ ∈ _
    erw [Iso.inv_hom_id_assoc]
    exact hΓ ▸ hg

set_option maxHeartbeats 180000 in
private theorem relativeGeneratorsFromLongestLifts [IsGalois F K]
    (M : BorelPair G) (hG : IsReductive G)
    (P : SplitPairOver (K := K) G M.torus (borelRadicals M true).borel) (D : AttachedDatum P.pair)
    (W : letI := D.comm; Identification D.datum)
    (hL : HasLongestOrbitLifts M P D W)
    (hstable : letI := D.comm
      letI : IsCommMonObj (baseChangedSubgroup K M.torus P.torusClosed).group.X := D.comm
      ∀ σ (i : Root P.pair.T),
      (actualDiagramAction P D W σ).indexEquiv i ∈ D.base.support ↔ i ∈ D.base.support)
    (S : ClosedSubgroup M.torus.group) (hS : IsLargestSplitSubtorus S)
    (hMax : IsMaximalSplitTorus (subgroupOfSubgroup M.torus S))
    (hC : RepresentsSubgroup M.torus (fun _ g ↦ Centralizes (subgroupOfSubgroup M.torus S).inclusion g))
    (hP : IsMinimalParabolic G M.positive) (hSP : IsSubgroupOf (subgroupOfSubgroup M.torus S) M.positive)
    (Q : QuotientData (subgroupOfSubgroup M.torus S)) :
    ∃ s : Set Q.splitImage.labels, Subgroup.closure s = ⊤ ∧
      ∀ w ∈ s, ∃ n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X,
        rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w ∧
        terminalPointHom G.val (n ≫ Q.normalizer.inclusion.hom.hom) ∈ generatedByBorelRadicals M := by
  classical
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  let P₀ := D.datum.rootDatum
  let δ := actualDiagramAction P D W
  letI : IsCommMonObj (baseChangedSubgroup K M.torus P.torusClosed).group.X := D.comm
  obtain ⟨e, _, _, hproject⟩ :=
    relativeFixedComparison (hT := P.torusClosed) W P.split hG S hS M.positive hMax hP hSP hC Q
  obtain ⟨c₀, hc₀, _, hb₀⟩ := attachedBase_regular D
  let f := evaluate D.datum c₀
  have hreg (i : Root P.pair.T) : f (P₀.root i) ≠ 0 := by
    change P₀.toLinearMap (P₀.root i) (Additive.ofMul c₀) ≠ 0
    rw [D.datum.root_eq, D.datum.pairing_eq]
    exact hc₀ i
  let X : Set P₀.weylGroup := {v | ∃ i ∈ D.base.support, IsLongest P₀ D.base (rootOrbit P₀ δ i) v}
  let Y : Set Q.splitImage.labels := {v | (e v).val ∈ X}
  have hgen : Subgroup.closure X = fixedWeyl P₀ δ :=
    QuasiSplitFixedWeyl.orbitGeneration P₀ f hreg D.base hb₀ δ hstable
  refine ⟨Y, generation_pulledBack (fixedWeyl P₀ δ) e hgen, ?_⟩
  rintro v ⟨i, hi, hv⟩
  obtain ⟨v', g, r, hlong, hg, hnorm, hr, hrl⟩ := hL i hi
  obtain ⟨n, hnG⟩ := (Q.normalizerProperty _ _).mp (normalizesSplitSubtorus M.torus S hS g hnorm)
  obtain ⟨l, hl⟩ := rationalSectionsEquiv Q.splitImage.constantGroup
  obtain ⟨v₀, hv₀⟩ := l.surjective (rationalProjection Q n)
  have hlabel₀ : rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint v₀ :=
    hv₀.symm.trans (hl v₀)
  obtain ⟨s, hs, hsl⟩ := hproject n v₀ hlabel₀
  have he : (e v₀).val = v' :=
    absoluteLabel_unique W W _ _ s r (hs.trans (by rw [hnG, hr])) hsl hrl
  have hI : rootOrbit P₀ δ i ⊆ D.base.support := by
    rintro _ ⟨σ, rfl⟩
    exact (hstable σ i).mpr hi
  have hv' : v' = (e v).val :=
    (QuasiSplitFixedWeyl.longestElements P₀ f hreg D.base hb₀ _ hI).unique hlong hv
  have eq : v₀ = v := e.injective (Subtype.ext (he.trans hv'))
  exact ⟨n, eq ▸ hlabel₀, hnG.symm ▸ hg⟩

private theorem terminalPointHom_surjective (J : GroupScheme F) :
    Function.Surjective (terminalPointHom J) := by
  intro g
  refine ⟨(groundPointIso F).hom ≫ g, ?_⟩
  change (groundPointIso F).inv ≫ (groundPointIso F).hom ≫ g = g
  exact (groundPointIso F).inv_hom_id_assoc g

private theorem generationFromRelativeBruhatMapped {A : Type v} [Group A]
    (hG : IsReductive G) (S P : ClosedSubgroup G.val) (hS : IsMaximalSplitTorus S)
    (hP : IsMinimalParabolic G P) (hSP : IsSubgroupOf S P)
    (f : (𝟙_ (SchemeOver F) ⟶ G.val.X) →* A) (hf : Function.Surjective f) (H : Subgroup A)
    (hPH : rationalSubgroup P ≤ H.comap f)
    (hL : ∀ Q : QuotientData S, ∃ s : Set Q.splitImage.labels, Subgroup.closure s = ⊤ ∧
      ∀ w ∈ s, ∃ n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X,
        rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w ∧
        f (n ≫ Q.normalizer.inclusion.hom.hom) ∈ H) : H = ⊤ := by
  have he := generationFromRelativeBruhat hG S P hS hP hSP (H.comap f) hPH hL
  apply top_unique
  intro g _
  obtain ⟨x, rfl⟩ := hf g
  exact (he.symm ▸ Subgroup.mem_top x : x ∈ H.comap f)

private theorem terminalSubgroup_map {J : GroupScheme F} (S : ClosedSubgroup J) :
    (rationalSubgroup S).map (terminalPointHom J) = (onRational S.inclusion).range := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (terminalSubgroup_mem S x).mp hx
  · intro hg
    obtain ⟨x, rfl⟩ := terminalPointHom_surjective J g
    exact ⟨x, (terminalSubgroup_mem S x).mpr hg, rfl⟩

private theorem terminalSubgroup_le_comap {J : GroupScheme F} (S : ClosedSubgroup J)
    (H : Subgroup (RationalPoints J)) (h : (onRational S.inclusion).range ≤ H) :
    rationalSubgroup S ≤ H.comap (terminalPointHom J) :=
  Subgroup.map_le_iff_le_comap.mp ((terminalSubgroup_map S).symm ▸ h)

private theorem terminalBorelInGenerated (M : BorelPair G)
    (S : ClosedSubgroup G.val) (hS : IsMaximalSplitTorus S)
    (hP : IsMinimalParabolic G M.positive) (hSP : IsSubgroupOf S M.positive)
    (hC : RepresentsSubgroup M.torus (fun _ g ↦ Centralizes S.inclusion g))
    (hT : (onRational M.torus.inclusion).range ≤ generatedByBorelRadicals M) :
    rationalSubgroup M.positive ≤ (generatedByBorelRadicals M).comap (terminalPointHom G.val) := by
  let Γ := generatedByBorelRadicals M
  let U := M.subgroup .positiveRadical
  have hU : (onRational U.inclusion).range ≤ Γ :=
    le_sup_left (a := (onRational U.inclusion).range)
      (b := (onRational (M.subgroup .negativeRadical).inclusion).range)
  exact borelPointsInGenerated M S hS hP hSP hC (Γ.comap (terminalPointHom G.val))
    (terminalSubgroup_le_comap M.torus Γ hT) (terminalSubgroup_le_comap U Γ hU)

private theorem generationWithRelativeGenerators (M : BorelPair G) (hG : IsReductive G)
    (S : ClosedSubgroup G.val) (hS : IsMaximalSplitTorus S)
    (hP : IsMinimalParabolic G M.positive) (hSP : IsSubgroupOf S M.positive)
    (hC : RepresentsSubgroup M.torus (fun _ g ↦ Centralizes S.inclusion g))
    (hT : (onRational M.torus.inclusion).range ≤ generatedByBorelRadicals M)
    (hL : ∀ Q : QuotientData S, ∃ s : Set Q.splitImage.labels, Subgroup.closure s = ⊤ ∧
      ∀ w ∈ s, ∃ n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X,
        rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w ∧
        terminalPointHom G.val (n ≫ Q.normalizer.inclusion.hom.hom) ∈ generatedByBorelRadicals M) :
    generatedByBorelRadicals M = ⊤ := by
  exact generationFromRelativeBruhatMapped (A := RationalPoints G.val) hG S M.positive hS hP hSP
    (terminalPointHom G.val) (terminalPointHom_surjective G.val) (generatedByBorelRadicals M)
    (terminalBorelInGenerated M S hS hP hSP hC hT) hL

private theorem generationFromLongestLifts [IsGalois F K]
    (M : BorelPair G) (hG : IsReductive G)
    (P : SplitPairOver (K := K) G M.torus (borelRadicals M true).borel) (D : AttachedDatum P.pair)
    (W : letI := D.comm; Identification D.datum)
    (hT : (onRational M.torus.inclusion).range ≤ generatedByBorelRadicals M)
    (hL : HasLongestOrbitLifts M P D W)
    (hstable : letI := D.comm
      letI : IsCommMonObj (baseChangedSubgroup K M.torus P.torusClosed).group.X := D.comm
      ∀ σ (i : Root P.pair.T),
      (actualDiagramAction P D W σ).indexEquiv i ∈ D.base.support ↔ i ∈ D.base.support) :
    generatedByBorelRadicals M = ⊤ := by
  obtain ⟨pair⟩ := rationalOppositePair M
  obtain ⟨S, hS, hMax, hC, hP, hSP⟩ :=
    QuasiSplitFixedWeyl.quasiSplitCentralizer G hG M.positive M.torus M.positiveBorel M.isTorus
      M.maximal ⟨pair.toPositive, pair.positiveSquare⟩
  exact generationWithRelativeGenerators M hG (subgroupOfSubgroup M.torus S) hMax hP hSP hC hT
    (relativeGeneratorsFromLongestLifts M hG P D W hL hstable S hS hMax hC hP hSP)

end OrbitAssembly

section PinnedAssembly

open Specs.Pinning (SplitBorelPair PinnedGroup PinnedIso SimpleRoot RootCoordinate AttachedDatum)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.QuasiSplitOrbitDerivedRoots (pinnedRootMap coefficientAction comparedAction diagramSimple)
open Specs.QuasiSplitPinnedPairModel (MarkedComparison MatchesCoordinateComparison)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AdjointCocharacters (coordinateHopf coordinateHopfIso coordinateHopfMap)
open LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open private rootsEquivOfIso simple_iff_of_roots transportedPositives pushScalarAction pinnedLift
  from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private charactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private rootSubgroup_of_coordinate exists_weylIdentification
  from LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private additiveLineIso from LinearAlgebraicGroups.RootData.RootGroups
open private reparametrizePin reparametrizeRootMap pinsOfBasedIso compareMarkedCoroots
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis

variable {K : Type u} [Field K] [Algebra F K]

/-- Transport the chosen root coordinates through an isomorphism of split pairs. -/
private theorem transportGivenPinning {A : AdditiveLine K} (J : PinnedGroup A)
    (P : SplitBorelPair K) (g : J.pair.G.val ≅ P.G.val) (t : J.pair.T.group ≅ P.T.group)
    (b : J.pair.B.group ≅ P.B.group)
    (ht : J.pair.T.inclusion ≫ g.hom = t.hom ≫ P.T.inclusion)
    (hb : J.pair.B.inclusion ≫ g.hom = b.hom ≫ P.B.inclusion) :
    ∃ (U : RootSubgroupFamily P.T) (p : Specs.Pinning.Pinning A P U)
      (f : PinnedIso J ⟨P, U, p⟩), f.group = g ∧ f.torus = t ∧ f.borel = b := by
  classical
  obtain ⟨U, _⟩ := Classification.Pinning.pinningsExist A P
  let d := rootsEquivOfIso g t ht
  let j : SimpleRoot J.pair ≃ SimpleRoot P := d.subtypeEquiv
    (simple_iff_of_roots d (charactersOfIso t) (fun _ => rfl)
      (transportedPositives g t ht b hb))
  let V (β : SimpleRoot P) := transportSubgroup g (J.roots (j.symm β).val).val
  have hscalar (β : SimpleRoot P) :
      HasScalarAction P.T β.val.val ((J.pin (j.symm β)).val.hom ≫ (V β).inclusion) := by
    have h := pushScalarAction g t ht _ _ (J.pin (j.symm β)).property
    have e : t.inv ≫ (j.symm β).val.val = β.val.val :=
      congrArg (fun z : SimpleRoot P => z.val.val) (j.apply_symm_apply β)
    simpa only [e, V, transportSubgroup, Category.assoc] using h
  have hsame (β : SimpleRoot P) : SameSubgroup (V β) (U β.val).val := by
    have h := (J.roots (j.symm β).val).property
    have hv := rootSubgroup_of_coordinate (⟨(J.pin (j.symm β)).val, hscalar β⟩ :
      RootCoordinate A P.T (V β) β.val.val) h.1 h.2.1
    obtain ⟨_, _, _, _, _, ho⟩ := ((RootData.RootGroups.rootSubgroups P.G P.reductive P.T
      P.split P.maximal).2 β.val.val β.val.property).2.2
    obtain ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ := ho _ hv
    obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := ho _ (U β.val).property
    exact ⟨⟨a' ≫ c, by rw [Category.assoc, hc, ha']⟩, ⟨c' ≫ a, by rw [Category.assoc, ha, hc']⟩⟩
  let e (β : SimpleRoot P) := sameSubgroupIso (hsame β)
  let x (β : SimpleRoot P) := (J.pin (j.symm β)).val ≪≫ (e β).val
  have hx (β : SimpleRoot P) :
      (x β).hom ≫ (U β.val).val.inclusion = (J.pin (j.symm β)).val.hom ≫ (V β).inclusion := by
    simp only [x, Iso.trans_hom, Category.assoc, (e β).property]
  let p : Specs.Pinning.Pinning A P U := fun β => ⟨x β, (hx β).symm ▸ hscalar β⟩
  have hp (β : SimpleRoot P) : pinnedRootMap p β = pinnedRootMap J.pin (j.symm β) ≫ g.hom := by
    exact (hx β).trans (Category.assoc _ _ _).symm
  refine ⟨U, p, ⟨g, t, b, ht, hb, ?_⟩, rfl, rfl, rfl⟩
  ext v
  constructor
  · rintro ⟨_, ⟨α, rfl⟩, rfl⟩
    refine ⟨j α, Prod.ext rfl ?_⟩
    change pinnedRootMap p (j α) = pinnedRootMap J.pin α ≫ g.hom
    exact (hp (j α)).trans
      (congrArg (fun β => pinnedRootMap J.pin β ≫ g.hom) (j.symm_apply_apply α))
  · rintro ⟨β, rfl⟩
    exact ⟨_, ⟨j.symm β, rfl⟩, Prod.ext
      (congrArg (fun z : SimpleRoot P => z.val.val) (j.apply_symm_apply β)) (hp β).symm⟩

private def simpleVerticesOfBasedIso {D E : Specs.Pinning.BasedRootDatum.{u}} (e : D ≅ E) :
    D.base.support ≃ E.base.support := by
  let f := e.hom.val.indexEquiv
  have h : f '' (D.base.support : Set D.I) = (E.base.support : Set E.I) := e.hom.property
  exact f.subtypeEquiv (fun i => by
    change i ∈ (D.base.support : Set D.I) ↔ f i ∈ (E.base.support : Set E.I)
    rw [← h]
    constructor
    · exact fun hi => ⟨i, hi, rfl⟩
    · rintro ⟨i', hi', heq⟩
      exact f.injective heq ▸ hi')

set_option maxHeartbeats 900000 in
private theorem splitPinnedCoordinates {A₀ : AdditiveLine F} (Q : PinnedGroup A₀)
    (D₀ : AttachedDatum Q.pair) (P : SplitBorelPair K)
    (g : (groupBaseChange F K).obj Q.pair.G.val ≅ P.G.val)
    (t : (groupBaseChange F K).obj Q.pair.T.group ≅ P.T.group)
    (b : (groupBaseChange F K).obj Q.pair.B.group ≅ P.B.group)
    (ht : (groupBaseChange F K).map Q.pair.T.inclusion ≫ g.hom = t.hom ≫ P.T.inclusion)
    (hb : (groupBaseChange F K).map Q.pair.B.inclusion ≫ g.hom = b.hom ≫ P.B.inclusion)
    (m : MultiplicativeComparison F K) (hm : PreservesUnits m) :
    ∃ (A : AdditiveLine K) (U : RootSubgroupFamily P.T) (p : Specs.Pinning.Pinning A P U)
      (D : AttachedDatum P) (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
      (e : D₀.toBased.base.support ≃ D.toBased.base.support),
      let J : PinnedGroup A := ⟨P, U, p⟩
      letI := D₀.comm
      letI := D.comm
      (∀ i, pinnedRootMap J.pin (simpleRootsOfAttachedDatum J D (e i)) =
        a.inv ≫ (groupBaseChange F K).map (pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q D₀ i)) ≫ g.hom) ∧
      (∀ i, simpleCorootOfAttachedDatum J D (simpleRootsOfAttachedDatum J D (e i)) =
        m.hom ≫ (groupBaseChange F K).map (simpleCorootOfAttachedDatum Q D₀
          (simpleRootsOfAttachedDatum Q D₀ i)) ≫ t.hom) := by
  -- Use both fibres of the same integral realization to preserve the labels.
  let C := groupBaseChange F K
  obtain ⟨A₁, A, R₁, R, gR, tR, aR, bR, htR, hbR, hroot, hcoroot⟩ :=
    QuasiSplitOrbitLevis.integralSplitComparison (F := F) (K := K) D₀.toBased
  let z := additiveLineIso A₁ A₀
  let Q₁ := reparametrizePin Q z
  obtain ⟨f, hf⟩ := pinnedLift Q₁ R₁.pinned D₀ R₁.attached R₁.datumIso
  let a := C.mapIso z.symm ≪≫ aR.symm
  let g' := gR ≪≫ C.mapIso f.group.symm ≪≫ g
  let t' := tR ≪≫ C.mapIso f.torus.symm ≪≫ t
  let b' := bR ≪≫ C.mapIso f.borel.symm ≪≫ b
  have ht' : R.pinned.pair.T.inclusion ≫ g'.hom = t'.hom ≫ P.T.inclusion := by
    have h := C.congr_map f.symm.torus_comm
    change C.map (R₁.pinned.pair.T.inclusion ≫ f.group.inv) =
      C.map (f.torus.inv ≫ Q.pair.T.inclusion) at h
    simp only [Functor.map_comp] at h
    change R.pinned.pair.T.inclusion ≫ (gR.hom ≫ C.map f.group.inv ≫ g.hom) =
      (tR.hom ≫ C.map f.torus.inv ≫ t.hom) ≫ P.T.inclusion
    rw [← Category.assoc R.pinned.pair.T.inclusion gR.hom, htR]
    change (tR.hom ≫ C.map R₁.pinned.pair.T.inclusion) ≫ C.map f.group.inv ≫ g.hom = _
    simp only [Category.assoc]
    rw [← Category.assoc (C.map R₁.pinned.pair.T.inclusion), h, Category.assoc, ht]
  have hb' : R.pinned.pair.B.inclusion ≫ g'.hom = b'.hom ≫ P.B.inclusion := by
    have h := C.congr_map f.symm.borel_comm
    change C.map (R₁.pinned.pair.B.inclusion ≫ f.group.inv) =
      C.map (f.borel.inv ≫ Q.pair.B.inclusion) at h
    simp only [Functor.map_comp] at h
    change R.pinned.pair.B.inclusion ≫ (gR.hom ≫ C.map f.group.inv ≫ g.hom) =
      (bR.hom ≫ C.map f.borel.inv ≫ b.hom) ≫ P.B.inclusion
    rw [← Category.assoc R.pinned.pair.B.inclusion gR.hom, hbR]
    change (bR.hom ≫ C.map R₁.pinned.pair.B.inclusion) ≫ C.map f.group.inv ≫ g.hom = _
    simp only [Category.assoc]
    rw [← Category.assoc (C.map R₁.pinned.pair.B.inclusion), h, Category.assoc, hb]
  obtain ⟨U, p, v, hvG, hvT, _⟩ := transportGivenPinning R.pinned P g' t' b' ht' hb'
  let J : PinnedGroup A := ⟨P, U, p⟩
  obtain ⟨D⟩ := Classification.Pinning.datumExists P
  let e := simpleVerticesOfBasedIso (asIso R.datumIso ≪≫ asIso (inducedBasedIso v R.attached D))
  letI := D₀.comm
  letI := R₁.attached.comm
  letI := R.attached.comm
  letI := D.comm
  refine ⟨A, U, p, D, a, e, ?_, ?_⟩
  all_goals intro i
  all_goals
    have hF := pinsOfBasedIso f R₁.datumIso hf (simpleRootsOfAttachedDatum Q₁ D₀ i)
      (R₁.simpleRoot i) rfl
    have hK := pinsOfBasedIso v (inducedBasedIso v R.attached D) rfl (R.simpleRoot i)
      (simpleRootsOfAttachedDatum J D (e i)) rfl
  · rw [← hK.2.1, hvG]
    change R.rootMap i ≫ gR.hom ≫ C.map f.group.inv ≫ g.hom = _
    have hF' : R₁.rootMap i ≫ f.group.inv =
        z.hom ≫ pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q D₀ i) := by
      rw [← show _ = R₁.rootMap i from hF.2.1, Category.assoc, f.group.hom_inv_id, Category.comp_id,
        reparametrizeRootMap]
      rfl
    rw [← Category.assoc, hroot]
    change (aR.hom ≫ C.map (R₁.rootMap i)) ≫ C.map f.group.inv ≫ g.hom =
      (aR.hom ≫ C.map z.hom) ≫ C.map (pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q D₀ i)) ≫ g.hom
    simp only [Category.assoc]
    rw [← Category.assoc (C.map (R₁.rootMap i)), ← C.map_comp, hF', C.map_comp, Category.assoc]
  · rw [← hK.2.2, hvT]
    change simpleCorootOfAttachedDatum R.pinned R.attached (R.simpleRoot i) ≫ tR.hom ≫
      C.map f.torus.inv ≫ t.hom = _
    have hF' : simpleCorootOfAttachedDatum R₁.pinned R₁.attached (R₁.simpleRoot i) ≫ f.torus.inv =
        simpleCorootOfAttachedDatum Q D₀ (simpleRootsOfAttachedDatum Q D₀ i) := by
      rw [← hF.2.2, Category.assoc, f.torus.hom_inv_id, Category.comp_id]
      rfl
    rw [← Category.assoc, compareMarkedCoroots R₁ R tR m (hcoroot m hm) i]
    change (m.hom ≫ C.map (simpleCorootOfAttachedDatum R₁.pinned R₁.attached (R₁.simpleRoot i))) ≫
      C.map f.torus.inv ≫ t.hom = _
    simp only [Category.assoc]
    rw [← Category.assoc (C.map (simpleCorootOfAttachedDatum R₁.pinned R₁.attached (R₁.simpleRoot i))),
      ← C.map_comp, hF']

section PinnedScalarAction

open Specs.AutomorphismSequence (forgetPinning)
open LinearAlgebraicGroups.Descent.Forms (spectrumIso)
open LinearAlgebraicGroups.Descent (SemilinearAction)
open private scalarExtensionIso_unique twist_eq_iff coefficientAction_hom_inv
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
open private scalarExtensionComparison scalarExtensionComparison_coefficients
  coefficientRingMap coefficientRingMap_apply from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitTorusProduct
open private extendedCoordinateIso_natural from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private twistMorphism multiplicativeBaseChange
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private closedSubgroup_mono from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
open private coefficientAction_naturality from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
open private scalarMorphism scalarMorphism_comp scalarMorphism_baseChange
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

private abbrev schemeHom {k : Type u} [Field k] {X Y : GroupScheme k} (f : X ⟶ Y) :=
  f.hom.hom.left

set_option maxHeartbeats 500000 in
private theorem pinnedComparison_inverseCoefficients
    {A₀ : AdditiveLine F} {Q : PinnedGroup A₀} {D₀ : AttachedDatum Q.pair}
    {l : Aut D₀.toBased ≃* Aut Q} {M : BorelPair G} {N : BorelPair Q.pair.G}
    (d : PinnedTwist K D₀ l M.positive M.torus) (e : MarkedComparison (K := K) N M)
    (he : MatchesCoordinateComparison e d.groupIso) (σ : Gal(K/F)) :
    coefficientAction σ G.val ≫ schemeHom e.groupIso.inv =
      schemeHom e.groupIso.inv ≫
        schemeHom ((groupBaseChange F K).map (l (d.outer σ)).asIso.hom.group.inv) ≫
        coefficientAction σ Q.pair.G.val := by
  let H := Q.pair.G
  let C := groupBaseChange F K
  let F₀ := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  let a (X : AffineAlgebraicGroup F) := (scalarExtensionComparison (K := K) X).val
  let u (X : AffineAlgebraicGroup F) := schemeHom (a X).hom
  let b := (l (d.outer σ)).asIso.hom
  let c (X : AffineAlgebraicGroup F) :=
    CommRingCat.ofHom (coefficientRingMap σ (Specs.AdjointCocharacters.coordinateHopf X)).toRingHom
  let s := CommRingCat.ofHom d.groupIso.hom.hom.toAlgHom.toRingHom
  let v := CommRingCat.ofHom
    (extendedHopfMap K (Specs.AdjointCocharacters.coordinateHopfMap (G := H) (H := H) b.group.inv)).hom.toAlgHom.toRingHom
  obtain ⟨j, hj, eq⟩ := he
  rw [scalarExtensionIso_unique j hj (Specs.AdjointCocharacters.coordinateHopf H),
    scalarExtensionIso_unique j hj (Specs.AdjointCocharacters.coordinateHopf G)] at eq
  have he' : e.groupIso = (a H).symm ≪≫ spectrumIso d.groupIso ≪≫ a G := by
    rw [eq]
    apply Iso.ext
    simp only [a, scalarExtensionComparison, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Functor.mapIso_inv]
    rfl
  have hs : Spec.map s ≫ u H = u G ≫ schemeHom e.groupIso.inv := by
    have hh : (spectrumIso d.groupIso).inv ≫ (a H).hom = (a G).hom ≫ e.groupIso.inv := by
      rw [he']
      simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]
    exact F₀.congr_map hh
  have hv : Spec.map v ≫ u H = u H ≫ schemeHom (C.map b.group.inv) :=
    F₀.congr_map (extendedCoordinateIso_natural (K := K) b.group.inv)
  have hc (X : AffineAlgebraicGroup F) : u X ≫ coefficientAction σ X.val = Spec.map (c X) ≫ u X :=
    scalarExtensionComparison_coefficients (scalarExtensionComparison (K := K) X) σ
  have hr : s ≫ c G = (c H ≫ v) ≫ s := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    have eqb : (Functor.mapAut Q (forgetPinning (A := A₀)) (l (d.outer σ))).asIso.inv = b.group.inv := by
      apply (cancel_mono b.group.hom).mp
      exact (Functor.mapAut Q (forgetPinning (A := A₀)) (l (d.outer σ))).asIso.inv_hom_id.trans
        b.group.inv_hom_id.symm
    have h := d.twistedAction σ x
    dsimp only at h
    rw [eqb] at h
    change coefficientRingMap σ (Specs.AdjointCocharacters.coordinateHopf G) (d.groupIso.hom.hom x) =
      d.groupIso.hom.hom ((extendedHopfMap K (Specs.AdjointCocharacters.coordinateHopfMap (G := H) (H := H) b.group.inv)).hom
        (coefficientRingMap σ (Specs.AdjointCocharacters.coordinateHopf H) x))
    simpa only [coefficientRingMap_apply] using h
  have hspec : Spec.map (c G) ≫ Spec.map s = Spec.map s ≫ Spec.map v ≫ Spec.map (c H) := by
    simpa only [Spec.map_comp, Category.assoc] using congrArg Spec.map hr
  haveI : IsIso (u G) := F₀.map_isIso (a G).hom
  apply (cancel_epi (u G)).mp
  calc
    u G ≫ coefficientAction σ G.val ≫ schemeHom e.groupIso.inv =
        (Spec.map (c G) ≫ Spec.map s) ≫ u H := by
      rw [← Category.assoc, hc G, Category.assoc, ← hs, Category.assoc]
    _ = u G ≫ schemeHom e.groupIso.inv ≫ schemeHom (C.map b.group.inv) ≫ coefficientAction σ H.val := by
      simp only [hspec, Category.assoc]
      rw [← hc H]
      simp only [reassoc_of% hv, reassoc_of% hs]

private theorem pinnedComparison_groupAction
    {A₀ : AdditiveLine F} {Q : PinnedGroup A₀} {D₀ : AttachedDatum Q.pair}
    {l : Aut D₀.toBased ≃* Aut Q} {M : BorelPair G} {N : BorelPair Q.pair.G}
    (d : PinnedTwist K D₀ l M.positive M.torus) (e : MarkedComparison (K := K) N M)
    (he : MatchesCoordinateComparison e d.groupIso) (σ : Gal(K/F)) :
    scalarMorphism σ e.groupIso.hom =
      (groupBaseChange F K).map (l (d.outer σ)).asIso.hom.group.hom ≫ e.groupIso.hom := by
  let C := groupBaseChange F K
  let f := (l (d.outer σ)).asIso.hom
  let F₀ := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  have hv : (l (d.outer σ⁻¹)).asIso.hom.group.inv = f.group.hom := by
    rw [map_inv, map_inv]
    rw [Aut.inv_asIso]
    have hh : (l (d.outer σ)).asIso.inv = f.symm := by
      apply (cancel_mono f).mp
      exact (l (d.outer σ)).asIso.inv_hom_id.trans (Groupoid.inv_comp f).symm
    change (l (d.outer σ)).asIso.inv.group.inv = f.group.hom
    rw [hh]
    rfl
  have h := pinnedComparison_inverseCoefficients d e he σ⁻¹
  rw [hv] at h
  have eq := congrArg (fun z => schemeHom e.groupIso.hom ≫ z ≫ schemeHom e.groupIso.hom) h
  let g := F₀.mapIso e.groupIso
  change g.hom ≫ (coefficientAction σ⁻¹ G.val ≫ g.inv) ≫ g.hom =
    g.hom ≫ (g.inv ≫ schemeHom (C.map f.group.hom) ≫
      coefficientAction σ⁻¹ Q.pair.G.val) ≫ g.hom at eq
  change twistMorphism σ⁻¹ e.groupIso.hom = C.map f.group.hom ≫ e.groupIso.hom
  apply (twist_eq_iff σ⁻¹ _ _).mpr
  change g.hom ≫ coefficientAction σ⁻¹ G.val =
    coefficientAction σ⁻¹ Q.pair.G.val ≫ schemeHom (C.map f.group.hom) ≫ g.hom
  have hnat : coefficientAction σ⁻¹ Q.pair.G.val ≫ schemeHom (C.map f.group.hom) =
      schemeHom (C.map f.group.hom) ≫ coefficientAction σ⁻¹ Q.pair.G.val :=
    coefficientAction_naturality σ⁻¹ f.group.hom
  have hgi : g.inv ≫ g.hom = 𝟙 (pullback G.val.X.hom (fieldSpecMap F K)) := g.inv_hom_id
  simpa only [Category.assoc, hgi, Category.comp_id, g.hom_inv_id_assoc, reassoc_of% hnat] using eq

private theorem pinnedComparison_torusAction
    {A₀ : AdditiveLine F} {Q : PinnedGroup A₀} {D₀ : AttachedDatum Q.pair}
    {l : Aut D₀.toBased ≃* Aut Q} {M : BorelPair G} {N : BorelPair Q.pair.G}
    (d : PinnedTwist K D₀ l M.positive M.torus) (e : MarkedComparison (K := K) N M)
    (he : MatchesCoordinateComparison e d.groupIso)
    (t : (groupBaseChange F K).obj Q.pair.T.group ≅ (groupBaseChange F K).obj M.torus.group)
    (ht : (groupBaseChange F K).map Q.pair.T.inclusion ≫ e.groupIso.hom =
      t.hom ≫ (groupBaseChange F K).map M.torus.inclusion)
    (σ : Gal(K/F)) :
    scalarMorphism σ t.hom = (groupBaseChange F K).map (l (d.outer σ)).asIso.hom.torus.hom ≫
      t.hom := by
  let C := groupBaseChange F K
  let f := (l (d.outer σ)).asIso.hom
  letI : Mono (C.map M.torus.inclusion) := closedSubgroup_mono
    (baseChangedSubgroup K M.torus (baseChangeClosedSubgroup F K M.torus.inclusion M.torus.isClosedImmersion))
  apply (cancel_mono (C.map M.torus.inclusion)).mp
  have eq := congrArg (scalarMorphism σ) ht
  simp only [scalarMorphism_comp, scalarMorphism_baseChange, pinnedComparison_groupAction d e he σ] at eq
  rw [← eq, ← Category.assoc, ← C.map_comp, f.torus_comm, C.map_comp, Category.assoc, ht, Category.assoc]

section ActualPinning

open RootPairing
open Specs.Pinning (BasedIso)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.QuasiSplitPinnedPairModel (IsBasedLift)
open Specs.QuasiSplitOrbitDerivedRoots (diagramRoot)
open private basedIso_ext_weight from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private scalarDatum_coweight scalarDatum_isScalarAction scalarCocharacter scalarCocharacter_comparison
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

private theorem restrictToBasedAction {P : SplitBorelPair K} (D : AttachedDatum P) :
    letI := D.comm
    ∀ (δ : Gal(K/F) →* D.datum.rootDatum.Aut),
      (∀ σ, (δ σ).indexEquiv '' (D.base.support : Set (Root P.T)) = (D.base.support : Set (Root P.T))) →
      ∃ ω : Gal(K/F) →* Aut D.toBased, ∀ σ, (ω σ).asIso.hom.val = δ σ := by
  letI := D.comm
  intro δ hδ
  let f (σ : Gal(K/F)) : BasedIso D.toBased D.toBased := ⟨δ σ, hδ σ⟩
  refine ⟨{ toFun := fun σ => Aut.of (asIso (f σ))
            map_one' := ?_
            map_mul' := ?_ }, fun _ => rfl⟩
  · apply Aut.ext
    apply Iso.ext
    apply Subtype.ext
    exact δ.map_one
  · intro σ τ
    apply Aut.ext
    apply Iso.ext
    apply Subtype.ext
    exact δ.map_mul σ τ

private theorem simpleImages_preserveBase {P : SplitBorelPair K} (D : AttachedDatum P)
    {I : Type u} (e : I ≃ D.toBased.base.support) (π : Equiv.Perm I) (f : Equiv.Perm (Root P.T))
    (h : ∀ i, f (e i).val = (e (π i)).val) : letI := D.comm
    f '' (D.base.support : Set (Root P.T)) = (D.base.support : Set (Root P.T)) := by
  letI := D.comm
  ext j
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨l, hl⟩ := e.surjective ⟨i, hi⟩
    have he := congrArg Subtype.val hl
    change (e l).val = i at he
    rw [← he, h l]
    exact (e (π l)).property
  · intro hj
    obtain ⟨i, hi⟩ := (π.trans e).surjective ⟨j, hj⟩
    refine ⟨(e i).val, (e i).property, (h i).trans ?_⟩
    exact congrArg Subtype.val hi

open private coefficientAction_hom_inv twist_eq_iff from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis

private theorem characterActionForOrbitLevis {T B : ClosedSubgroup G.val}
    (P : SplitPairOver (K := K) G T B) (D : AttachedDatum P.pair)
    (W : letI := D.comm; Identification D.datum)
    (ω : Gal(K/F) →* Aut D.toBased)
    (hω : letI : IsCommMonObj (baseChangedSubgroup K T P.torusClosed).group.X := D.comm
      ∀ σ, (ω σ).asIso.hom.val = actualDiagramAction P D W σ) :
    let m := multiplicativeBaseChange F K
    (∀ σ (α : Root P.pair.T),
      fieldConjugation σ⁻¹ T.group ≫ schemeHom (diagramRoot ω σ α).val =
        schemeHom α.val ≫ comparedAction σ⁻¹ m.symm) ∧ IsActualDiagramAction D m ω := by
  letI := D.comm
  letI : IsCommMonObj (baseChangedSubgroup K T P.torusClosed).group.X := D.comm
  let m := multiplicativeBaseChange F K
  let M := multiplicativeGroup F
  let L := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  have hs := scalarDatum_isScalarAction (G := G) (T := T) (hT := P.torusClosed) W P.split
  have hm : schemeHom m.hom ≫ schemeHom m.inv = 𝟙 _ := (L.mapIso m).hom_inv_id
  refine ⟨?_, ?_⟩
  · intro σ α
    have hx := hs.1 σ α.val
    have hv := (actualDiagramAction P D W σ).toHom.root_weightMap_apply
      D.datum.rootDatum D.datum.rootDatum α
    change (actualDiagramAction P D W σ).weightEquiv (D.datum.rootDatum.root α) =
      D.datum.rootDatum.root ((actualDiagramAction P D W σ).indexEquiv α) at hv
    rw [D.datum.root_eq, D.datum.root_eq, ← hω σ] at hv
    change schemeHom ((Additive.toMul ((actualDiagramAction P D W σ).weightEquiv
        (Additive.ofMul α.val))) ≫ m.hom) =
      coefficientAction σ T.group ≫ schemeHom (α.val ≫ m.hom) ≫ coefficientAction σ⁻¹ M at hx
    rw [← hω σ] at hx
    erw [hv] at hx
    have h := congrArg (fun z => (coefficientAction σ⁻¹ T.group ≫ z) ≫ schemeHom m.inv) hx
    change (coefficientAction σ⁻¹ T.group ≫
        (schemeHom (diagramRoot ω σ α).val ≫ schemeHom m.hom)) ≫ schemeHom m.inv =
      (coefficientAction σ⁻¹ T.group ≫ coefficientAction σ T.group ≫
        (schemeHom α.val ≫ schemeHom m.hom) ≫ coefficientAction σ⁻¹ M) ≫ schemeHom m.inv at h
    have he : coefficientAction σ⁻¹ T.group ≫ coefficientAction σ T.group = 𝟙 _ := by
      simpa only [inv_inv] using coefficientAction_hom_inv σ⁻¹ T.group
    change coefficientAction σ⁻¹ T.group ≫ schemeHom (diagramRoot ω σ α).val =
      schemeHom α.val ≫ schemeHom m.hom ≫ coefficientAction σ⁻¹ M ≫ schemeHom m.inv
    simpa only [Category.assoc, hm, Category.comp_id,
      reassoc_of% he, Category.id_comp] using h
  · intro σ y
    have hx := hs.2 σ y.toMul
    rw [← hω σ] at hx
    change schemeHom (m.inv ≫ (cocharacterAction D (ω σ) y).toMul) =
      coefficientAction σ M ≫ schemeHom (m.inv ≫ y.toMul) ≫ coefficientAction σ⁻¹ T.group at hx
    have h := congrArg (coefficientAction σ⁻¹ M ≫ ·) hx
    have he : coefficientAction σ⁻¹ M ≫ coefficientAction σ M = 𝟙 _ := by
      simpa only [inv_inv] using coefficientAction_hom_inv σ⁻¹ M
    change coefficientAction σ⁻¹ M ≫ schemeHom (m.inv ≫ (cocharacterAction D (ω σ) y).toMul) =
      schemeHom (m.inv ≫ y.toMul) ≫ coefficientAction σ⁻¹ T.group
    simpa only [Category.assoc, reassoc_of% he, Category.id_comp] using h

set_option maxHeartbeats 450000 in
private theorem ambientPinningAction
    {A₀ : AdditiveLine F} {Q : PinnedGroup A₀} (D₀ : AttachedDatum Q.pair)
    (l : Aut D₀.toBased ≃* Aut Q) (hl : IsBasedLift D₀ l)
    {M : BorelPair G} {N : BorelPair Q.pair.G}
    (d : PinnedTwist K D₀ l M.positive M.torus) (e : MarkedComparison (K := K) N M)
    (he : MatchesCoordinateComparison e d.groupIso)
    (t : (groupBaseChange F K).obj Q.pair.T.group ≅ (groupBaseChange F K).obj M.torus.group)
    (ht : (groupBaseChange F K).map Q.pair.T.inclusion ≫ e.groupIso.hom =
      t.hom ≫ (groupBaseChange F K).map M.torus.inclusion)
    (P : SplitPairOver (K := K) G M.torus (borelRadicals M true).borel)
    {A : AdditiveLine K} (U : RootSubgroupFamily P.pair.T) (p : Specs.Pinning.Pinning A P.pair U)
    (D : AttachedDatum P.pair) (W : letI := D.comm; Identification D.datum)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (j : D₀.toBased.base.support ≃ D.toBased.base.support)
    (hx : ∀ i, pinnedRootMap p (simpleRootsOfAttachedDatum ⟨P.pair, U, p⟩ D (j i)) =
      a.inv ≫ (groupBaseChange F K).map (pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q D₀ i)) ≫ e.groupIso.hom)
    (hy : ∀ i, simpleCorootOfAttachedDatum ⟨P.pair, U, p⟩ D (simpleRootsOfAttachedDatum ⟨P.pair, U, p⟩ D (j i)) =
      (multiplicativeBaseChange F K).hom ≫ (groupBaseChange F K).map (simpleCorootOfAttachedDatum Q D₀
        (simpleRootsOfAttachedDatum Q D₀ i)) ≫ t.hom) :
    ∃ ω : Gal(K/F) →* Aut D.toBased,
      IsAmbientPinnedAction D p a (multiplicativeBaseChange F K) ω ∧
      letI : IsCommMonObj (baseChangedSubgroup K M.torus P.torusClosed).group.X := D.comm
      ∀ σ, (ω σ).asIso.hom.val = actualDiagramAction P D W σ := by
  letI := D₀.comm
  letI := D.comm
  letI : IsCommMonObj (baseChangedSubgroup K M.torus P.torusClosed).group.X := D.comm
  let δ := actualDiagramAction P D W
  let m := multiplicativeBaseChange F K
  let C := groupBaseChange F K
  let J : PinnedGroup A := ⟨P.pair, U, p⟩
  let π (σ : Gal(K/F)) := simplePermutation D₀ (d.outer σ)
  let f (σ : Gal(K/F)) := (l (d.outer σ)).asIso.hom
  let x₀ (i : D₀.base.support) := pinnedRootMap Q.pin (simpleRootsOfAttachedDatum Q D₀ i)
  let x (i : D₀.base.support) := pinnedRootMap p (simpleRootsOfAttachedDatum J D (j i))
  let y₀ (i : D₀.base.support) := simpleCorootOfAttachedDatum Q D₀ (simpleRootsOfAttachedDatum Q D₀ i)
  let y (i : D₀.base.support) := simpleCorootOfAttachedDatum J D (simpleRootsOfAttachedDatum J D (j i))
  have hmarks (σ : Gal(K/F)) (i : D₀.base.support) :
      x₀ i ≫ (f σ).group.hom = x₀ (π σ i) ∧ y₀ i ≫ (f σ).torus.hom = y₀ (π σ i) := by
    have hf : inducedBasedIso (f σ) D₀ D₀ = (d.outer σ).asIso.hom :=
      basedIso_ext_weight _ _ (fun z => ((hl (d.outer σ)).1 z.toMul).symm)
    exact (pinsOfBasedIso (f σ) (d.outer σ).asIso.hom hf
      (simpleRootsOfAttachedDatum Q D₀ i) (simpleRootsOfAttachedDatum Q D₀ (π σ i)) rfl).2
  have hyn (i : D₀.base.support) : m.inv ≫ y i = C.map (y₀ i) ≫ t.hom := by
    have hh : y i = m.hom ≫ C.map (y₀ i) ≫ t.hom := hy i
    rw [hh, Iso.inv_hom_id_assoc]
  have hco (σ : Gal(K/F)) (i : D₀.base.support) : scalarCocharacter σ (T := M.torus.group) (y i) =
      y (π σ i) := by
    apply (cancel_epi m.inv).mp
    rw [scalarCocharacter_comparison]
    change scalarMorphism σ (m.inv ≫ y i) = m.inv ≫ y (π σ i)
    rw [hyn, hyn, scalarMorphism_comp, scalarMorphism_baseChange, pinnedComparison_torusAction d e he t ht σ,
      ← Category.assoc, ← C.map_comp, (hmarks σ i).2]
  have hindex (σ : Gal(K/F)) (i : D₀.base.support) : (δ σ).indexEquiv (j i).val = (j (π σ i)).val := by
    let r := D.datum.rootDatum
    apply r.coroot.injective
    have hv := (δ σ).toHom.coroot_coweightMap_apply r r ((δ σ).indexEquiv (j i).val)
    change (δ σ).coweightEquiv (r.coroot ((δ σ).indexEquiv (j i).val)) =
      r.coroot ((δ σ).indexEquiv.symm ((δ σ).indexEquiv (j i).val)) at hv
    rw [Equiv.symm_apply_apply] at hv
    have hv' : r.coroot ((δ σ).indexEquiv (j i).val) =
        (δ σ).coweightEquiv.symm (r.coroot (j i).val) := by
      apply (δ σ).coweightEquiv.injective
      rw [LinearEquiv.apply_symm_apply]
      exact hv
    rw [hv']
    exact (scalarDatum_coweight (G := G) (T := M.torus) (hT := P.torusClosed) W P.split σ (y i)).trans
      (congrArg Additive.ofMul (hco σ i))
  obtain ⟨ω, hω⟩ := restrictToBasedAction D δ (fun σ =>
    simpleImages_preserveBase D j (π σ) (δ σ).indexEquiv (hindex σ))
  have hc := characterActionForOrbitLevis P D W ω hω
  refine ⟨ω, ⟨hc.1, hc.2, ?_⟩, hω⟩
  intro σ α
  let i := j.symm ⟨α.val, (D.simple_iff α.val).mpr α.property⟩
  have hi : simpleRootsOfAttachedDatum J D (j i) = α := by
    apply Subtype.ext
    change (j i).val = α.val
    exact congrArg (fun x : D.toBased.base.support => x.val)
      (j.apply_symm_apply ⟨α.val, (D.simple_iff _).mpr α.property⟩)
  have hi' : diagramSimple ω σ α = simpleRootsOfAttachedDatum J D (j (π σ i)) := by
    apply Subtype.ext
    change (ω σ).asIso.hom.val.indexEquiv α.val = (j (π σ i)).val
    rw [hω σ, ← hi]
    exact hindex σ i
  have hr (i : D₀.base.support) : a.hom ≫ x i = C.map (x₀ i) ≫ e.groupIso.hom := by
    rw [show x i = _ from hx i, Iso.hom_inv_id_assoc]
  have hσ : scalarMorphism σ (a.hom ≫ x i) = a.hom ≫ x (π σ i) := by
    rw [hr, hr, scalarMorphism_comp, scalarMorphism_baseChange,
      pinnedComparison_groupAction d e he σ, ← Category.assoc, ← C.map_comp, (hmarks σ i).1]
  have h := (twist_eq_iff σ⁻¹ _ _).mp hσ
  rw [hi']
  change comparedAction σ⁻¹ a ≫ schemeHom (x (π σ i)) =
    schemeHom (pinnedRootMap p α) ≫ coefficientAction σ⁻¹ G.val
  rw [← hi]
  let L := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  letI : IsIso (schemeHom a.hom) := L.map_isIso a.hom
  apply (cancel_epi (schemeHom a.hom)).mp
  change schemeHom a.hom ≫ (schemeHom a.inv ≫ coefficientAction σ⁻¹ A₀.group ≫
      schemeHom a.hom) ≫ schemeHom (x (π σ i)) =
    schemeHom a.hom ≫ schemeHom (x i) ≫ coefficientAction σ⁻¹ G.val
  have hai : schemeHom a.hom ≫ schemeHom a.inv = 𝟙 _ := (L.mapIso a).hom_inv_id
  have h' := h.symm
  change coefficientAction σ⁻¹ A₀.group ≫ (schemeHom a.hom ≫ schemeHom (x (π σ i))) =
      (schemeHom a.hom ≫ schemeHom (x i)) ≫ coefficientAction σ⁻¹ G.val at h'
  simpa only [Category.assoc, reassoc_of% hai, Category.id_comp] using h'

end ActualPinning

private def comparisonOnMark {Q : AffineAlgebraicGroup F} {N : BorelPair Q} {M : BorelPair G}
    (e : MarkedComparison (K := K) N M) (m : Marking) {V : ClosedSubgroup Q.val}
    (h : N.subgroup m = V) :
    (groupBaseChange F K).obj V.group ≅ (groupBaseChange F K).obj (M.subgroup m).group :=
  (groupBaseChange F K).mapIso (eqToIso (congrArg (fun U : ClosedSubgroup Q.val => U.group) h.symm)) ≪≫
    e.subgroupIso m

private theorem comparisonOnMark_commutes {Q : AffineAlgebraicGroup F} {N : BorelPair Q} {M : BorelPair G}
    (e : MarkedComparison (K := K) N M) (m : Marking) {V : ClosedSubgroup Q.val}
    (h : N.subgroup m = V) :
    (groupBaseChange F K).map V.inclusion ≫ e.groupIso.hom = (comparisonOnMark e m h).hom ≫
      (groupBaseChange F K).map (M.subgroup m).inclusion := by
  subst V
  simpa [comparisonOnMark] using e.commutes m

end PinnedScalarAction


open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies

open private multiplicativeBaseChange multiplicativeBaseChange_unit
  from LinearAlgebraicGroups.Relative.RationalCocharacter

private theorem splitPairAfterExtension {K : Type u} [Field K] [Algebra F K]
    (M : BorelPair G) (hred : IsReductive G)
    (hsplit : Specs.GeometricRadicals.IsSplitTorus ((groupBaseChange F K).obj M.torus.group)) :
    Nonempty (SplitPairOver (K := K) G M.torus (borelRadicals M true).borel) := by
  obtain ⟨hcB, _, hcT, hredK, hBK, _, hTK, _⟩ :=
    QuasiSplitBorelPairBaseChange.extendBorelPair (K := K) G hred M.positive M.negative M.torus
      M.positiveBorel M.negativeBorel M.isTorus M.maximal M.intersection hsplit
  obtain ⟨pair⟩ := rationalOppositePair M
  let C := groupBaseChange F K
  refine ⟨⟨hcT, hcB, hredK, hsplit, hTK, hBK, C.map pair.toPositive, ?_⟩⟩
  change C.map pair.toPositive ≫ C.map M.positive.inclusion = C.map M.torus.inclusion
  exact (C.map_comp _ _).symm.trans (C.congr_map pair.positiveSquare)

section SimpleCase

variable {K : Type u} [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Infinite F]

private theorem generationFromBasedOrbitWords (M : BorelPair G) (hred : IsReductive G)
    (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    (P : SplitPairOver (K := K) G M.torus (borelRadicals M true).borel) (D : AttachedDatum P.pair)
    (W : letI := D.comm; Identification D.datum)
    {A₀ : AdditiveLine F} {A : AdditiveLine K} (U : RootSubgroupFamily P.pair.T)
    (p : Specs.Pinning.Pinning A P.pair U) (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (m : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased)
    (hm : PreservesUnits m) (hpin : IsAmbientPinnedAction D p a m ω)
    (hω : letI := D.comm; ∀ σ, (ω σ).asIso.hom.val = actualDiagramAction P D W σ) :
    generatedByBorelRadicals M = ⊤ := by
  letI := D.comm
  have hact (σ : Gal(K/F)) (i : Root P.pair.T) :
      (actualDiagramAction P D W σ).indexEquiv i = (ω σ).asIso.hom.val.indexEquiv i :=
    congrArg (fun v : D.datum.rootDatum.Aut => v.indexEquiv i) (hω σ).symm
  obtain ⟨hTor, hWord⟩ := orbitLeviWords M hred hG hsc P D W U p a m ω hm hpin hact
  apply generationFromLongestLifts M hred P D W hTor hWord
  intro σ i
  rw [hact σ i]
  exact basedAction_stable D (ω σ) i

set_option maxHeartbeats 320000 in
private theorem generationFromMarkedPinning
    (M : BorelPair G) (hred : IsReductive G) (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G)
    {A₀ : AdditiveLine F} {Q : PinnedGroup A₀} (D₀ : AttachedDatum Q.pair)
    (l : Aut D₀.toBased ≃* Aut Q) (hl : Specs.QuasiSplitPinnedPairModel.IsBasedLift D₀ l)
    (d : PinnedTwist K D₀ l M.positive M.torus) {N : BorelPair Q.pair.G}
    (e : MarkedComparison (K := K) N M) (he : MatchesCoordinateComparison e d.groupIso)
    (hT : N.torus = Q.pair.T) (hB : N.positive = Q.pair.B)
    (P : SplitPairOver (K := K) G M.torus (borelRadicals M true).borel) :
    generatedByBorelRadicals M = ⊤ := by
  let m := multiplicativeBaseChange F K
  have hm : PreservesUnits m := fun R a => multiplicativeBaseChange_unit K R a
  let t := comparisonOnMark e .torus hT
  let b := comparisonOnMark e .positive hB
  have ht := comparisonOnMark_commutes e .torus hT
  have hb := comparisonOnMark_commutes e .positive hB
  obtain ⟨A, U, p, D, a, j, hp, hco⟩ :=
    splitPinnedCoordinates Q D₀ P.pair e.groupIso t b ht hb m hm
  obtain ⟨W⟩ := exists_weylIdentification P.pair D
  obtain ⟨ω, hpin, hω⟩ :=
    ambientPinningAction D₀ l hl d e he t ht P U p D W a j hp hco
  exact generationFromBasedOrbitWords M hred hG hsc P D W U p a m ω hm hpin hω

end SimpleCase

private theorem generationForAbsolutelyAlmostSimple [Infinite F] (hG : IsAbsolutelyAlmostSimple G)
    (hsc : GeometricallySimplyConnected G) (M : BorelPair G) :
    generatedByBorelRadicals M = ⊤ := by
  have hred := reductive_of_semisimple G hG.1
  obtain ⟨K, hK, hFK, hfd, hGal, A₀, Q, D₀, l, d, N, hB, hT, _, _, hl, hsplit, _, e, he⟩ :=
    QuasiSplitPinnedPairModel.initialPinnedComparison G hG.1 hsc M
  letI := hK
  letI := hFK
  letI := hfd
  letI := hGal
  obtain ⟨P⟩ := splitPairAfterExtension M hred hsplit
  exact generationFromMarkedPinning M hred hG hsc D₀ l hl d e he hT hB P

/-- The rational points are generated by the two specified opposite Borel radicals. -/
theorem quasiSplitLocalGeneration : Specs.QuasiSplitLocalGeneration.Statement.{u} := by
  intro F _ hF G hG hsc M
  letI := infiniteOfIsLocalField F hF
  apply generationFromComponents hG hsc M
  intro E _ _ J hJ hc N
  exact generationForAbsolutelyAlmostSimple (G := J) hJ hc N

end PinnedAssembly

end

end LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
