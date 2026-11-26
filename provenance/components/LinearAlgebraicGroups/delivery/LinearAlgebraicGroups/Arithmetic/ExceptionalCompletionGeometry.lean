import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalCompletionGeometry
import LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LieAlgebrasAndRepresentations
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalCompletionGeometry

open LinearAlgebraicGroups.Specs
open Specs.AbsoluteDynkinTypes (HasDynkinType IsAbsolutelyAlmostSimple)
open Specs.ExceptionalCompletionGeometry (HasAbsoluteType RealCompletionGeometricExtension)
open Specs.GeometricRadicals (GeometricGroup IsSemisimple IsReductive)
open Specs.Pinning (AttachedDatum BasedIso BasedRootDatum SplitBorelPair)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open Specs.Unipotent (baseChangedAlgebraicGroup)

open private groupBaseChangeTower trivial_baseChange_iff
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometric_coroot_lattice reductive_of_semisimple
  from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private fibreTowerIso realization_corootSpan noCentralCovers_of_span centralIsogeny_postIso
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private forgetClassification_reverse basedIso_base_iff maximalTransport pushKBorel
  pinAlignedPairs from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

/-- The geometric group after field extension is obtained from the original
geometric group by extending along an embedding of algebraic closures. -/
theorem geometricScalarExtensionIso {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) :
    ∃ a : Algebra (AlgebraicClosure k) (AlgebraicClosure K),
      letI := a
      IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K) ∧
        Nonempty ((baseChangedAlgebraicGroup (AlgebraicClosure K) (GeometricGroup G)).val ≅
          (GeometricGroup (baseChangedAlgebraicGroup K G)).val) := by
  let E := AlgebraicClosure k
  let L := AlgebraicClosure K
  let f : E →ₐ[k] L := IsAlgClosed.lift
  let a : Algebra E L := f.toRingHom.toAlgebra
  letI := a
  have h : IsScalarTower k E L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      exact (f.commutes x).symm)
  letI := h
  exact ⟨a, h, ⟨((groupBaseChangeTower (K := E) L).app G.val).symm ≪≫
    (groupBaseChangeTower (K := K) L).app G.val⟩⟩

private theorem isZero_baseChange_iff {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : GroupScheme k) : IsZero ((groupBaseChange k K).obj G) ↔ IsZero G := by
  have ht (L : Type u) [Field L] (H : GroupScheme L) :
      IsZero H ↔ Nonempty (H ≅ Grp.trivial (SchemeOver L)) :=
    ⟨fun h => ⟨h.iso (Grp.isZero_trivial _)⟩,
      fun ⟨j⟩ => (Grp.isZero_trivial _).of_iso j⟩
  exact (ht K _).trans ((trivial_baseChange_iff G).trans (ht k _).symm)

private theorem dynkinType_of_basedIso {D E : BasedRootDatum.{u}} (d : BasedIso D E)
    {t : FiniteDynkinType} (ht : HasDynkinType (RootData.integralCartan D.datum D.base) t) :
    HasDynkinType (RootData.integralCartan E.datum E.base) t := by
  let e := d.val.indexEquiv.subtypeEquiv (basedIso_base_iff d)
  obtain ⟨f, hf⟩ := ht
  refine ⟨e.symm.trans f, ?_⟩
  intro i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  change E.datum.pairing (d.val.indexEquiv j.val) (d.val.indexEquiv i.val) =
    t.cartan (f (e.symm (e i))) (f (e.symm (e j)))
  rw [e.symm_apply_apply, e.symm_apply_apply, ← hf i j]
  exact d.val.toHom.pairing (i := j.val) (j := i.val)

private theorem connectedDiagram_of_basedIso {D E : BasedRootDatum.{u}} (d : BasedIso D E)
    (h : (Specs.AbsoluteDynkinTypes.integralDiagram
      (RootData.integralCartan D.datum D.base)).IsConnected) :
    (Specs.AbsoluteDynkinTypes.integralDiagram
      (RootData.integralCartan E.datum E.base)).IsConnected := by
  classical
  let e := d.val.indexEquiv.subtypeEquiv (basedIso_base_iff d)
  have pair (i j : D.base.support) :
      RootData.integralCartan E.datum E.base (e i) (e j) =
        RootData.integralCartan D.datum D.base i j :=
    d.val.toHom.pairing (i := j.val) (j := i.val)
  have edge (i j : D.base.support) :
      (Specs.AbsoluteDynkinTypes.integralDiagram
        (RootData.integralCartan D.datum D.base)).edges i j ≠ 0 →
      (Specs.AbsoluteDynkinTypes.integralDiagram
        (RootData.integralCartan E.datum E.base)).edges (e i) (e j) ≠ 0 := by
    by_cases hij : i = j
    · subst j
      simp [Specs.AbsoluteDynkinTypes.integralDiagram]
    · have hne : e i ≠ e j := fun h => hij (e.injective h)
      simp only [Specs.AbsoluteDynkinTypes.integralDiagram, ite_eq_right hij, ite_eq_right hne, pair]
      exact fun h => h
  refine ⟨h.1.map e, ?_⟩
  intro i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  induction h.2 i j with
  | rel i j h => exact .rel _ _ (edge _ _ h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

open private corootFullRank restrictCharacters_injective
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

/-- A coreflection-invariant kernel in a connected full-coroot datum is either
zero or the whole lattice when the codomain is torsion-free. -/
private theorem cocharacterKernel_dichotomy {D : BasedRootDatum.{u}} {V : Type u}
    [AddCommGroup V] [Module.IsTorsionFree ℤ V]
    (hspan : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤)
    (hconn : (Specs.AbsoluteDynkinTypes.integralDiagram
      (RootData.integralCartan D.datum D.base)).IsConnected)
    (f : D.Y →ₗ[ℤ] V) (h : ∀ (i : D.I) (y : D.Y), f y = 0 →
      f (D.datum.coreflection i y) = 0) :
    Function.Injective f ∨ f = 0 := by
  classical
  letI := D.freeX
  letI := D.freeY
  letI := D.finiteX
  letI := D.finiteY
  by_cases hf : Function.Injective f
  · exact Or.inl hf
  right
  obtain ⟨y, hy, hy₀⟩ : ∃ y, f y = 0 ∧ y ≠ 0 := by
    have hex : ¬ ∀ y, f y = 0 → y = 0 :=
      fun h => hf ((injective_iff_map_eq_zero f).mpr h)
    push Not at hex
    exact hex
  have hfin : Finite (D.X ⧸ Submodule.span ℤ (Set.range D.datum.root)) := by
    apply (Submodule.finiteQuotient_iff _).mpr
    apply (corootFullRank D.datum D.base).mp
    change Module.finrank ℤ (Submodule.span ℤ (Set.range D.datum.coroot)) = _
    rw [hspan, finrank_top]
  have hySimple : ∃ i : D.base.support, D.datum.root' i.val y ≠ 0 := by
    by_contra! hz
    apply hy₀
    apply restrictCharacters_injective D.datum.flip hfin
    apply LinearMap.ext
    intro x
    have vanish (z : D.X) (hz' : z ∈ Submodule.span ℤ (D.datum.root '' ↑D.base.support)) :
        D.datum.toLinearMap.flip y z = 0 := by
      induction hz' using Submodule.span_induction with
      | mem z hz' =>
        obtain ⟨i, hi, rfl⟩ := hz'
        exact hz ⟨i, hi⟩
      | zero => exact map_zero _
      | add x z _ _ hx hz => rw [map_add, hx, hz, add_zero]
      | smul a x _ hx => rw [map_smul, hx, smul_zero]
    have hx : x.val ∈ Submodule.span ℤ (D.datum.root '' ↑D.base.support) := by
      rw [D.base.span_int_root_support]
      exact x.property
    change D.datum.toLinearMap.flip y x.val = D.datum.toLinearMap.flip 0 x.val
    rw [vanish _ hx, map_zero, LinearMap.zero_apply]
  have kill (i : D.I) (y : D.Y) (hy : f y = 0) (hne : D.datum.root' i y ≠ 0) :
      f (D.datum.coroot i) = 0 := by
    have hy' := h i y hy
    rw [RootPairing.coreflection_apply, map_sub, map_smul, hy, zero_sub, neg_eq_zero] at hy'
    exact (smul_eq_zero.mp hy').resolve_left hne
  obtain ⟨i₀, hi₀⟩ := hySimple
  have prop {i j : D.base.support}
      (he : (Specs.AbsoluteDynkinTypes.integralDiagram
        (RootData.integralCartan D.datum D.base)).edges i j ≠ 0) :
      f (D.datum.coroot i.val) = 0 ↔ f (D.datum.coroot j.val) = 0 := by
    have h₁ : D.datum.pairing i.val j.val ≠ 0 := by
      intro hz
      apply he
      simp [Specs.AbsoluteDynkinTypes.integralDiagram, RootData.integralCartan, hz]
    have h₂ : D.datum.pairing j.val i.val ≠ 0 := by
      intro hz
      apply he
      simp [Specs.AbsoluteDynkinTypes.integralDiagram, RootData.integralCartan, hz]
    exact ⟨fun hi => kill j.val _ hi h₂, fun hj => kill i.val _ hj h₁⟩
  have hsimple (j : D.base.support) : f (D.datum.coroot j.val) = 0 := by
    have eqv (i j : D.base.support) :
        Relation.EqvGen (fun a b => (Specs.AbsoluteDynkinTypes.integralDiagram
          (RootData.integralCartan D.datum D.base)).edges a b ≠ 0) i j →
        (f (D.datum.coroot i.val) = 0 ↔ f (D.datum.coroot j.val) = 0) := by
      intro hh
      induction hh with
      | rel _ _ hab => exact prop hab
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact (eqv i₀ j (hconn.2 i₀ j)).mp (kill i₀.val y hy hi₀)
  have hker : Submodule.span ℤ (D.datum.coroot '' ↑D.base.support) ≤ f.ker :=
    Submodule.span_le.mpr (by rintro z ⟨j, hj, rfl⟩; exact hsimple ⟨j, hj⟩)
  rw [D.base.span_int_coroot_support, hspan] at hker
  exact LinearMap.ker_eq_top.mp (top_le_iff.mp hker)

open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.GeometricRadicals (IsSplitTorus IsSmoothConnectedNormal IsTrivialSubgroup)
open Specs.CharacterPairing (pairing characterValue)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private conjugation_unique from LinearAlgebraicGroups.RootData.AbstractPairing
open private pairing_pushforward from LinearAlgebraicGroups.Classification.CentralIsogenies
open private pairing_eq_iff from LinearAlgebraicGroups.RootData.CharacterPairing
open private powerMorphism_zero from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private split_character_hom_ext from LinearAlgebraicGroups.Classification.NormalizerComparison
open private pushCocharacters from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

private theorem group_morphism_eq_one {k : Type u} [Field k] {G H : GroupScheme k}
    {f : G ⟶ H} (h : f = 0) : f.hom.hom = 1 := by
  subst f
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem map_conjugate_eq_one {k : Type u} [Field k] {G H : GroupScheme k}
    (f : G ⟶ H) {X : SchemeOver k} (g x : X ⟶ G.X) (hx : x ≫ f.hom.hom = 1) :
    (g * x * g⁻¹) ≫ f.hom.hom = 1 := by
  simp only [MonObj.mul_comp, GrpObj.inv_comp, hx, mul_one, mul_inv_cancel]

set_option maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem cocharacter_kernel_coreflection {k : Type u} [Field k]
    (P : SplitBorelPair k) (D : AttachedDatum P) {H : GroupScheme k} (f : P.G.val ⟶ H)
    (i : Root P.T) (y : Additive (Cocharacter P.T.group))
    (hy : y.toMul ≫ P.T.inclusion ≫ f = 0) :
    letI := D.comm
    (D.datum.rootDatum.coreflection i y).toMul ≫ P.T.inclusion ≫ f = 0 := by
  letI := D.comm
  let R := D.datum.rootDatum
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r, hr⟩ := D.datum.attached i
  obtain ⟨N, hN, act, ha⟩ := D.datum.normalizerAction
  obtain ⟨n, hn⟩ := (hN _ _).mp r.normalizes
  obtain ⟨e, he, haχ, hac⟩ := ha n
  have he' : e = r.conjugation :=
    conjugation_unique P.T (he.trans (by rw [r.conjugates, hn]))
  have ha' : act n = RootPairing.Equiv.reflection R i := by
    apply RootPairing.Equiv.weightHom_injective R
    apply LinearEquiv.ext
    intro x
    change (act n).weightEquiv (Additive.ofMul x.toMul) =
      (RootPairing.Equiv.reflection R i).weightEquiv x
    rw [haχ, he', r.reflection, RootPairing.Equiv.reflection_weightEquiv,
      RootPairing.reflection_apply]
    change Additive.ofMul (x.toMul * i.val ^ (-pairing P.T.group x.toMul r.coroot)) =
      x - R.toLinearMap x (R.coroot i) • R.root i
    rw [hr, ← D.datum.pairing_eq, D.datum.root_eq, sub_eq_add_neg, ← neg_smul]
    rfl
  have h := hac y.toMul
  rw [ha', RootPairing.Equiv.reflection_coweightEquiv, he'] at h
  change R.coreflection i y = Additive.ofMul (y.toMul ≫ r.conjugation.hom) at h
  rw [h]
  change (y.toMul ≫ r.conjugation.hom) ≫ P.T.inclusion ≫ f = 0
  have hy' : (y.toMul ≫ P.T.inclusion).hom.hom ≫ f.hom.hom = 1 := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using group_morphism_eq_one hy
  have he'' : ((y.toMul ≫ r.conjugation.hom) ≫ P.T.inclusion ≫ f) =
      y.toMul ≫ (r.conjugation.hom ≫ P.T.inclusion) ≫ f := by simp only [Category.assoc]
  rw [he'']
  apply Grp.hom_ext
  change y.toMul.hom.hom ≫ (r.conjugation.hom ≫ P.T.inclusion).hom.hom ≫ f.hom.hom = 1
  rw [← Category.assoc, r.conjugates, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
  exact map_conjugate_eq_one f _ _ hy'

set_option backward.isDefEq.respectTransparency false in
private theorem splitTorus_hom_eq_zero {k : Type u} [Field k] {S T : GroupScheme k}
    (hS : IsSplitTorus S) (hT : IsSplitTorus T) (f : S ⟶ T)
    (hf : ∀ c : Cocharacter S, c ≫ f = 0) : f = 0 := by
  apply split_character_hom_ext hS hT
  intro χ
  rw [zero_comp]
  obtain ⟨hcomm, _, _, _, _, B, hB, hpair⟩ :=
    RootData.CharacterPairing.perfectCharacterPairing S hS
  letI := hcomm
  letI := hB
  have hz (c : Cocharacter S) : pairing S (f ≫ χ) c = 0 := by
    change pairing S (CentralIsogenies.characterPullback f χ) c = 0
    rw [← pairing_pushforward f χ c, hf]
    apply (pairing_eq_iff χ _ 0).mp
    change (0 : Cocharacter T) ≫ χ = _
    rw [zero_comp, powerMorphism_zero]
    rfl
  have hh : B.toPerfPair (Additive.ofMul (f ≫ χ)) = B.toPerfPair 0 := by
    ext y
    change B (Additive.ofMul (f ≫ χ)) (Additive.ofMul y.toMul) = B 0 (Additive.ofMul y.toMul)
    rw [hpair (f ≫ χ) y.toMul, hz, map_zero, LinearMap.zero_apply]
  exact congrArg Additive.toMul (B.toPerfPair.injective hh)

open Specs.RootGroups (AdditiveLine HasScalarAction rootPoint)
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint oppositeCocharacter)
open Specs.OrderedRootProducts (Enumerates product rootProduct rootCellMap)
open private rootPoint_add from LinearAlgebraicGroups.Classification.RankOneRelations
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups
open private product_affine scheme_hom_eq_of_schematicallyDominant
  from LinearAlgebraicGroups.Classification.PinnedUniqueness
open private irreducible_of_geometricallyConnected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private isReduced_of_smooth_over_field
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private exists_regular_cocharacter maximalTorus_of_geometricallyMaximal
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private affine_tensor from LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private affine_subgroup from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem rootCoordinate_comp_eq_zero {k : Type u} [Field k] [CharZero k]
    (P : SplitBorelPair k) (D : AttachedDatum P) (i : Root P.T)
    {A : AdditiveLine k} (x : A.group ⟶ P.G.val) (hx : HasScalarAction P.T i.val x)
    {H : GroupScheme k} (f : P.G.val ⟶ H) (hf : P.T.inclusion ≫ f = 0) :
    x ≫ f = 0 := by
  letI := D.comm
  let c := (D.datum.rootDatum.coroot i).toMul
  have hpair : pairing P.T.group i.val c = 2 := by
    rw [← D.datum.pairing_eq, ← D.datum.root_eq i]
    change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root i)
      (D.datum.rootDatum.coroot i) = 2
    rw [RootPairing.root_coroot_eq_pairing, RootPairing.pairing_same]
  let R := CommAlgCat.of k (Polynomial k)
  let b : Rˣ := Units.map (algebraMap k R) (Units.mk0 2 (by norm_num : (2 : k) ≠ 0))
  let t := cocharacterPoint c R b
  have hχ : characterValue i.val R t = (4 : R) := by
    rw [(RootData.CharacterPairing.characterPairingComposition P.T.group i.val c).2,
      hpair, zpow_ofNat]
    change (algebraMap k (Polynomial k) 2) ^ 2 = (4 : Polynomial k)
    rw [map_ofNat]
    norm_num
  let a : R := algebraMap k R ((3 : k)⁻¹) * Polynomial.X
  have ha : (3 : R) * a = Polynomial.X := by
    change (3 : Polynomial k) * (algebraMap k (Polynomial k) ((3 : k)⁻¹) * Polynomial.X) = _
    rw [← map_ofNat (algebraMap k (Polynomial k)) (n := 3), ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ (by norm_num : (3 : k) ≠ 0), map_one, one_mul]
  let g : GroupPoints P.G.val R := t ≫ P.T.inclusion.hom.hom
  have hg : g ≫ f.hom.hom = 1 := by
    change t ≫ (P.T.inclusion.hom.hom ≫ f.hom.hom) = 1
    rw [← Grp.comp_hom_hom, hf]
    exact MonObj.comp_one t
  let fR : GroupPoints P.G.val R →* GroupPoints H R :=
    (((groupPointsFunctor k).map f).app R).hom
  have hgR : fR g = 1 := hg
  have hh : fR (rootPoint x R a) =
      fR (rootPoint x R a) * fR (rootPoint x R (3 * a)) := by
    have h := congrArg fR (hx R t a)
    change fR (g * rootPoint x R a * g⁻¹) =
      fR (rootPoint x R (characterValue i.val R t * a)) at h
    rw [hχ, show (4 : R) * a = a + 3 * a by ring, rootPoint_add] at h
    simpa only [map_mul, map_inv, hgR, inv_one, one_mul, mul_one] using h
  have hz : rootPoint (x ≫ f) R Polynomial.X = 1 := by
    rw [rootPoint_comp, ← ha]
    change fR (rootPoint x R (3 * a)) = 1
    exact mul_left_cancel (hh.symm.trans (mul_one _).symm)
  apply Grp.hom_ext
  change (x ≫ f).hom.hom = 1
  unfold rootPoint at hz
  rw [Polynomial.aeval_X_left] at hz
  change (testSpec k).map (𝟙 (Opposite.op (CommAlgCat.of k (Polynomial k)))) ≫
    (x ≫ f).hom.hom = 1 at hz
  have hid : (testSpec k).map (𝟙 (Opposite.op (CommAlgCat.of k (Polynomial k)))) =
      𝟙 A.group.X := (testSpec k).map_id _
  have he := congrArg (fun a : A.group.X ⟶ A.group.X => a ≫ (x ≫ f).hom.hom) hid
  exact (Category.id_comp _).symm.trans (he.symm.trans hz)

set_option backward.isDefEq.respectTransparency false in
private theorem eq_zero_of_trivial_torus_restriction {k : Type u} [Field k] [CharZero k]
    (P : SplitBorelPair k) (D : AttachedDatum P) {H : AffineAlgebraicGroup k}
    (f : P.G.val ⟶ H.val) (hf : P.T.inclusion ≫ f = 0) : f = 0 := by
  classical
  let T := P.T
  let G := P.G
  have roots (i : Root T) :
      ∃ U : {S : ClosedSubgroup G.val // Specs.RootGroups.IsRootSubgroup T S i.val},
        ∃ (A : AdditiveLine k) (x : A.group ≅ U.val.group),
          HasScalarAction T i.val (x.hom ≫ U.val.inclusion) := by
    obtain ⟨U, hU, _, _, ⟨A, x, hx⟩, _⟩ :=
      ((RootData.RootGroups.rootSubgroups G P.reductive T P.split P.maximal).2 i.val i.property).2.2
    exact ⟨⟨U, hU⟩, A, x, hx⟩
  choose U A x hx using roots
  have hU (i : Root T) : (U i).val.inclusion ≫ f = 0 := by
    apply (cancel_epi (x i).hom).mp
    rw [comp_zero, ← Category.assoc]
    exact rootCoordinate_comp_eq_zero P D i _ (hx i) f hf
  obtain ⟨c, hc⟩ := exists_regular_cocharacter G T P.split
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := Fintype.ofFinite (Root T)
  let pos := (Specs.BorelsAndChambers.positiveRoots T c).toFinset
  let neg := (Specs.BorelsAndChambers.positiveRoots T (oppositeCocharacter c)).toFinset
  have hpos : Enumerates pos.toList (Specs.BorelsAndChambers.positiveRoots T c) :=
    ⟨Finset.nodup_toList _, by simp [pos]⟩
  have hneg : Enumerates neg.toList (Specs.BorelsAndChambers.positiveRoots T (oppositeCocharacter c)) :=
    ⟨Finset.nodup_toList _, by simp [neg]⟩
  let j := rootCellMap T U neg.toList pos.toList
  letI : IsOpenImmersion j.left :=
    RootData.OrderedRootProducts.regularRootCell G P.reductive T P.split P.maximal
      c hc U _ _ hneg hpos
  letI := G.property.1
  letI := H.property.1
  letI := G.property.2.1
  letI := G.property.2.2
  letI := P.reductive.2.1
  letI : IrreducibleSpace G.val.X.left := irreducible_of_geometricallyConnected G.val
  letI : Smooth G.val.X.hom := P.reductive.1
  letI : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  letI : IsAffine T.group.X.left := affine_subgroup G.property.1 T
  have points (l : List (Root T)) :
      Nonempty (𝟙_ (SchemeOver k) ⟶ product (fun α => (U α).val.group.X) l) := by
    induction l with
    | nil => exact ⟨𝟙 _⟩
    | cons i l ih => exact ⟨lift η[_] (Classical.choice ih)⟩
  let point := lift (Classical.choice (points neg.toList))
    (lift η[T.group.X] (Classical.choice (points pos.toList)))
  letI : Nonempty (product (fun α => (U α).val.group.X) neg.toList ⊗
      (T.group.X ⊗ product (fun α => (U α).val.group.X) pos.toList)).left :=
    ⟨point.left (IsLocalRing.closedPoint k)⟩
  letI : IsDominant j.left := ⟨j.left.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI := IsSchemeTheoreticallyDominant.of_isDominant j.left
  letI : IsAffine (product (fun α => (U α).val.group.X) neg.toList).left :=
    product_affine _ (fun _ => affine_subgroup G.property.1 _) neg.toList
  letI : IsAffine (product (fun α => (U α).val.group.X) pos.toList).left :=
    product_affine _ (fun _ => affine_subgroup G.property.1 _) pos.toList
  letI : IsAffine (T.group.X ⊗ product (fun α => (U α).val.group.X) pos.toList).left := affine_tensor
  letI : IsAffine (product (fun α => (U α).val.group.X) neg.toList ⊗
      (T.group.X ⊗ product (fun α => (U α).val.group.X) pos.toList)).left := affine_tensor
  letI : QuasiCompact j.left := inferInstance
  have hr (l : List (Root T)) : rootProduct U l ≫ f.hom.hom = 1 := by
    induction l with
    | nil => exact MonObj.one_comp _
    | cons i l ih =>
      change ((_ ≫ (U i).val.inclusion.hom.hom) * (_ ≫ rootProduct U l)) ≫ f.hom.hom = _
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, ← Grp.comp_hom_hom, hU i, ih]
      change (_ ≫ (1 : (U i).val.group.X ⟶ H.val.X)) * (_ ≫ 1) = 1
      rw [MonObj.comp_one, MonObj.comp_one, mul_one]
  have hT : T.inclusion.hom.hom ≫ f.hom.hom = 1 :=
    congrArg (fun v : T.group ⟶ H.val => v.hom.hom) hf
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply scheme_hom_eq_of_schematicallyDominant (i := j.left)
  change (j ≫ f.hom.hom).left = (j ≫ (1 : G.val.X ⟶ H.val.X)).left
  congr 1
  simp only [j, rootCellMap, MonObj.mul_comp, Category.assoc, MonObj.comp_mul,
    hr, hT, MonObj.comp_one, mul_one]

open private image_of_geometric_torus from LinearAlgebraicGroups.Reductive.MaximalToriExist
open private trivialNormalUnipotent from LinearAlgebraicGroups.Reductive.CentralDerived
open private isSplitTorus_of_torus isTorus_of_split
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private exists_maximal_torus_over inclusion_mono
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private schemeKernel_sections isMonHom_of_comp_closed
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient

set_option backward.isDefEq.respectTransparency false in
private theorem normal_subgroup_torus {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (P : SplitBorelPair k) (N : ClosedSubgroup P.G.val) (hN : IsSmoothConnectedNormal N)
    (hne : ¬ IsZero N.group) {L : AffineAlgebraicGroup k} (f : P.G.val ⟶ L.val)
    (hf : IsSchemeKernel f N) :
    ∃ y : Cocharacter P.T.group, y ≠ 0 ∧ y ≫ P.T.inclusion ≫ f = 0 := by
  let A := closedSubgroupAlgebraicGroup N
  have hT : ∃ T : ClosedSubgroup (GeometricGroup A).val,
      GeometricRadicals.IsTorus T.group ∧ ¬ IsTrivialSubgroup T := by
    by_contra! hno
    have hu := LinearAlgebraicGroups.TorusFreeUnipotent.torusFreeUnipotent A hN.1 hN.2.1 hno
    obtain ⟨e⟩ := trivialNormalUnipotent P.G P.reductive N hN hu
    exact hne ((Grp.isZero_trivial _).of_iso e)
  obtain ⟨S, hs, hS⟩ := NontrivialRationalTorus.existsNontrivialTorus k A hN.1 hN.2.1 hT
  let S' := Specs.GeometricBorelConjugacy.subgroupOfSubgroup N S
  obtain ⟨M, hm, j, hj⟩ := exists_maximal_torus_over P.G S' hs
  have hc : ConnectedSpace P.G.val.X.left := by
    letI := P.reductive.2.1
    exact GeometricallyConnected.connectedSpace_of_subsingleton P.G.val.X.hom
  have ht := maximalTorus_of_geometricallyMaximal P.G P.T (isTorus_of_split P.split) P.maximal
  obtain ⟨g, e, he⟩ :=
    MaximalToriConjugate.maximalToriConjugate P.G P.reductive.1 hc M P.T hm ht
  have hSsplit : IsSplitTorus S.group := isSplitTorus_of_torus (closedSubgroupAlgebraicGroup S) hs
  obtain ⟨c, hne⟩ : ∃ c : Cocharacter S.group, c ≠ 0 := by
    by_contra! hall
    have hz : (𝟙 S.group : S.group ⟶ S.group) = 0 :=
      splitTorus_hom_eq_zero hSsplit hSsplit (𝟙 _) (fun c => by
        rw [Category.comp_id]
        exact hall c)
    exact hS ⟨(IsZero.of_mono_eq_zero (𝟙 S.group) hz).iso (Grp.isZero_trivial _)⟩
  let v : Cocharacter S'.group := c
  let y := v ≫ j ≫ e.hom
  have hS' : S'.inclusion ≫ f = 0 := by
    change (S.inclusion ≫ N.inclusion) ≫ f = 0
    rw [Category.assoc, show N.inclusion ≫ f = 0 from Grp.hom_ext _ _ hf.w, comp_zero]
  letI := inclusion_mono S'
  haveI : Mono j := mono_of_mono_fac hj
  refine ⟨y, ?_, ?_⟩
  · intro hy
    apply hne
    change v = 0
    apply (cancel_mono (j ≫ e.hom)).mp
    rw [zero_comp]
    exact hy
  · apply Grp.hom_ext
    have h := group_morphism_eq_one hS'
    have hx : v.hom.hom ≫ j.hom.hom ≫ M.inclusion.hom.hom ≫ f.hom.hom = 1 := by
      rw [← Category.assoc j.hom.hom, ← Grp.comp_hom_hom, hj, ← Grp.comp_hom_hom, h,
        MonObj.comp_one]
    change (v ≫ j).hom.hom ≫ (e.hom ≫ P.T.inclusion).hom.hom ≫ f.hom.hom = 1
    rw [← Category.assoc, he, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
    apply map_conjugate_eq_one f
    simpa only [Grp.comp_hom_hom, Category.assoc] using hx

set_option backward.isDefEq.respectTransparency false in
private theorem normal_subgroups_of_connected_datum {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (P : SplitBorelPair k) (D : AttachedDatum P)
    (hs : corootLattice D = ⊤)
    (hc : (Specs.AbsoluteDynkinTypes.integralDiagram
      (RootData.integralCartan D.toBased.datum D.toBased.base)).IsConnected) :
    ∀ (N : ClosedSubgroup P.G.val), IsSmoothConnectedNormal N →
      IsZero N.group ∨ IsIso N.inclusion := by
  intro N hN
  classical
  by_cases hz : IsZero N.group
  · exact Or.inl hz
  right
  obtain ⟨L, f, hf⟩ := LinearAlgebraicGroups.normalClosedSubgroupKernel P.G N hN.2.2
  obtain ⟨S, p, hsT, hp⟩ := image_of_geometric_torus
    (G := closedSubgroupAlgebraicGroup P.T) (Q := L) (P.T.inclusion ≫ f)
    (isTorus_of_split P.split)
  let hS := isSplitTorus_of_torus (closedSubgroupAlgebraicGroup S) hsT
  obtain ⟨hcomm, _, _, hfree, _, _, _, _⟩ :=
    RootData.CharacterPairing.perfectCharacterPairing S.group hS
  letI := D.comm
  letI := hcomm
  letI := hfree
  let d : D.toBased.Y →ₗ[ℤ] Additive (Cocharacter S.group) := pushCocharacters p
  letI := inclusion_mono S
  have heq (y : D.toBased.Y) : d y = 0 ↔ y.toMul ≫ P.T.inclusion ≫ f = 0 := by
    change Additive.ofMul (y.toMul ≫ p) = 0 ↔ y.toMul ≫ P.T.inclusion ≫ f = 0
    rw [← hp]
    constructor
    · intro hy
      have h : y.toMul ≫ p = 0 := congrArg Additive.toMul hy
      rw [← Category.assoc, h, zero_comp]
    · intro hy
      apply Additive.toMul.injective
      change y.toMul ≫ p = 0
      apply (cancel_mono S.inclusion).mp
      rw [zero_comp, Category.assoc]
      exact hy
  obtain ⟨y, hy, hfy⟩ := normal_subgroup_torus P N hN hz f hf
  have hdy := (heq (Additive.ofMul y)).mpr hfy
  have h := cocharacterKernel_dichotomy (D := D.toBased) hs hc d (fun i y hy =>
    (heq _).mpr (cocharacter_kernel_coreflection P D f i y ((heq y).mp hy)))
  have hd : d = 0 := h.resolve_left (fun hinj => hy (congrArg Additive.toMul
    (hinj (hdy.trans (map_zero d).symm))))
  have hp₀ : p = 0 := splitTorus_hom_eq_zero P.split hS p fun c => by
    have h : d (Additive.ofMul c) = 0 := LinearMap.congr_fun hd (Additive.ofMul c)
    exact congrArg Additive.toMul h
  have hf₀ : f = 0 := eq_zero_of_trivial_torus_restriction P D f (by rw [← hp, hp₀, zero_comp])
  have hmem := (schemeKernel_sections hf (𝟙 P.G.val.X)).mpr
    (by rw [Category.id_comp]; exact group_morphism_eq_one hf₀)
  change (∃ v : P.G.val.X ⟶ N.group.X,
    v ≫ N.inclusion.hom.hom = 𝟙 P.G.val.X) at hmem
  obtain ⟨v, hv⟩ := hmem
  letI := N.isClosedImmersion
  letI := isMonHom_of_comp_closed v (𝟙 P.G.val) N.inclusion hv
  let a : P.G.val ⟶ N.group := Grp.homMk v
  have ha : a ≫ N.inclusion = 𝟙 _ := Grp.hom_ext _ _ hv
  letI := inclusion_mono N
  refine ⟨⟨a, (cancel_mono N.inclusion).mp ?_, ha⟩⟩
  rw [Category.assoc, ha, Category.comp_id, Category.id_comp]

private theorem attachedDatum_of_iso {k : Type u} [Field k]
    (P : SplitBorelPair k) (D : AttachedDatum P) (H : AffineAlgebraicGroup k)
    (hH : IsReductive H) (e : P.G.val ≅ H.val) :
    ∃ (Q : SplitBorelPair k) (_ : Q.G = H) (E : AttachedDatum Q),
      Nonempty (BasedIso D.toBased E.toBased) := by
  let Q : SplitBorelPair k :=
    { G := H
      reductive := hH
      T := transportSubgroup e P.T
      split := P.split
      maximal := maximalTransport e P.T P.maximal
      B := transportSubgroup e P.B
      borel := pushKBorel e P.borel
      containsTorus := by
        obtain ⟨j, hj⟩ := P.containsTorus
        exact ⟨j, by change j ≫ P.B.inclusion ≫ e.hom = P.T.inclusion ≫ e.hom
                     rw [← Category.assoc, hj]⟩ }
  let A := Classification.Pinning.standardAdditiveLine k
  obtain ⟨P', Q', hP', hQ', ⟨j⟩⟩ :=
    pinAlignedPairs P Q A e (Iso.refl _) (by
      change P.T.inclusion ≫ e.hom = 𝟙 P.T.group ≫ (P.T.inclusion ≫ e.hom)
      rw [Category.id_comp]) (Iso.refl _) (by
      change P.B.inclusion ≫ e.hom = 𝟙 P.B.group ≫ (P.B.inclusion ≫ e.hom)
      rw [Category.id_comp])
  let E := Classification.Pinning.attachedDatum Q'.pair
  have h := congrArg SplitBorelPair.G hQ'
  refine ⟨Q'.pair, h, E, ?_⟩
  let D' : AttachedDatum P'.pair := hP'.symm ▸ D
  have same {P₁ P₂ : SplitBorelPair k} (h : P₁ = P₂) (B : AttachedDatum P₂) :
      (show AttachedDatum P₁ from h.symm ▸ B).toBased = B.toBased := by
    cases h
    rfl
  have hD : D'.toBased = D.toBased := same hP' D
  rw [← hD]
  exact ⟨Classification.Pinning.inducedBasedIso j D' E⟩

/-- Compare the two geometric groups through the field fibres of the same
integral model of the original based root datum. -/
private theorem geometricExtension {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero K]
    (G : AffineAlgebraicGroup k) (hG : IsAbsolutelyAlmostSimple G) (hsc : GeometricallySimplyConnected G)
    {t : FiniteDynkinType} (htype : HasAbsoluteType G t) :
    let H := baseChangedAlgebraicGroup K G
    IsAbsolutelyAlmostSimple H ∧ GeometricallySimplyConnected H ∧ HasAbsoluteType H t := by
  let H := baseChangedAlgebraicGroup K G
  let E := AlgebraicClosure k
  let L := AlgebraicClosure K
  obtain ⟨a, ha⟩ := geometricScalarExtensionIso (K := K) G
  letI : Algebra E L := a
  obtain ⟨_, ⟨eG⟩⟩ := ha
  have hH : IsSemisimple H :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) G hG.1.1 hG.1.2.1).mpr hG.1
  have hHL : IsSemisimple (GeometricGroup H) :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := L) H hH.1 hH.2.1).mpr hH
  obtain ⟨P, hP, D, htD⟩ := htype
  let D₀ := D.toBased
  have hspan : Submodule.span ℤ (Set.range D₀.datum.coroot) = ⊤ :=
    geometric_coroot_lattice G hG.1 hsc P hP D
  have hconn := RootData.AbsoluteDynkinTypes.geometricDiagramConnected G hG P hP D hspan
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D₀
  obtain ⟨_, F, eE, _, _, _, _, _, _⟩ := M.fieldFibre E
  obtain ⟨_, F', eL, _, _, _, _, _, _⟩ := M.fieldFibre L
  obtain ⟨d⟩ := forgetClassification_reverse F.pinned.pair P F.attached D
    (F.datumIso.val.symm _ _)
  let f : (Specs.IntegralSemisimpleModel.fibre E).obj M.group ≅ (GeometricGroup G).val :=
    eE ≪≫ d ≪≫ eqToIso (congrArg Subtype.val hP)
  let q : F'.pinned.pair.G.val ≅ (GeometricGroup H).val :=
    eL.symm ≪≫ (fibreTowerIso E L).app M.group ≪≫ (groupBaseChange E L).mapIso f ≪≫ eG
  have hscH : GeometricallySimplyConnected H := by
    intro J hJ p hp
    letI := noCentralCovers_of_span F'.pinned.pair F'.attached
      (realization_corootSpan F' hspan) J hJ (p ≫ q.inv) (centralIsogeny_postIso q.symm hp)
    exact IsIso.of_isIso_comp_right p q.inv
  obtain ⟨Q, hQ, B, ⟨e⟩⟩ := attachedDatum_of_iso F'.pinned.pair F'.attached
    (GeometricGroup H) (reductive_of_semisimple _ hHL) q
  have hspanB := geometric_coroot_lattice H hH hscH Q hQ B
  have hconnB := connectedDiagram_of_basedIso e (connectedDiagram_of_basedIso F'.datumIso hconn)
  have hnorm : ∀ N : ClosedSubgroup (GeometricGroup H).val, IsSmoothConnectedNormal N →
      IsZero N.group ∨ IsIso N.inclusion := by
    rw [← hQ]
    exact normal_subgroups_of_connected_datum Q B hspanB hconnB
  have hnz : ¬ IsZero (GeometricGroup H).val :=
    fun hz => hG.2.1 ((isZero_baseChange_iff (K := L) (GeometricGroup G).val).mp
      (hz.of_iso eG))
  exact ⟨⟨hH, hnz, hnorm⟩, hscH,
    ⟨Q, hQ, B, dynkinType_of_basedIso e (dynkinType_of_basedIso F'.datumIso htD)⟩⟩

theorem realCompletionGeometricExtension : RealCompletionGeometricExtension.{u} := by
  intro K _ _ G w _ t _ hG hsc htype
  haveI : CharZero w.Completion := Algebra.charZero_of_charZero K w.Completion
  exact geometricExtension (K := w.Completion) G hG hsc htype

end LinearAlgebraicGroups.Arithmetic.ExceptionalCompletionGeometry
