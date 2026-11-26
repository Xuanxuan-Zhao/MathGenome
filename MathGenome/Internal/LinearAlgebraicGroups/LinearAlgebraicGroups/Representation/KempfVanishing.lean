import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.KempfVanishing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.IntegralFlagModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PositiveKempfVanishing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.RingTheory.Finiteness.Nakayama

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct nonZeroDivisors

universe u

namespace LinearAlgebraicGroups.Representation.KempfVanishing

open _root_.LinearAlgebraicGroups.Specs
open ArithmeticCohomologyBaseChange (CohomologyReduction IsFiniteAffineCover)
open CharacterDescent (Character)
open FlagCohomology (SchemeOverRing FlagKernelPair cohomology flagCohomology flagLineSheaf)
open FlagLineBundle (BorelProjection OppositeBorelPair)
open InducedNonvanishing (Dominant)
open IntegralFlagGeometry (BaseRing PinnedModel FibreIdentification changeBase fibreSheaf
  fibreProjection primeMap rationalMap)
open Pinning (AttachedDatum BasedRootDatum SplitBorelPair)
open QuotientEmbedding (Presentation)

open private pushforwardEquivalenceOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private basedIso_base_iff pinnedLift pushKBorel rootsEquivOfIso transportedPositives
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
open private centralIsogeny_postIso underlying from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private identity_isogeny from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedNonvanishing
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private subgroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private weightSpace_le_lieImage_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- If a finite module vanishes modulo a proper principal ideal, the determinant
form of Nakayama gives an annihilator congruent to one modulo that ideal. -/
private theorem extension_isZero_of_reduction {A k : Type u} [CommRing A] [Field k]
    (φ : A →+* k) (hφ : Function.Injective φ) (H : ModuleCat.{u} A) [Module.Finite A H]
    (a : A) (ha : Ideal.span {a} ≠ ⊤)
    (hs : Function.Surjective ((a • 𝟙 H : H ⟶ H).hom)) :
    IsZero ((ModuleCat.extendScalars φ).obj H) := by
  have htop : (⊤ : Submodule A H) ≤ Ideal.span {a} • (⊤ : Submodule A H) := by
    intro x _
    obtain ⟨y, hy⟩ := hs x
    change a • y = x at hy
    rw [← hy]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton a)) Submodule.mem_top
  obtain ⟨r, hr, hann⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (Ideal.span {a}) (⊤ : Submodule A H) Module.Finite.fg_top htop
  have hn : r ≠ 0 := by
    intro h
    rw [h, zero_sub] at hr
    exact ha ((Ideal.eq_top_iff_one _).2 (by simpa using (Ideal.span {a}).neg_mem hr))
  have hunit : φ r ≠ 0 := fun h => hn (hφ (h.trans (map_zero φ).symm))
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun x y => ?_⟩
  have hz (z : (ModuleCat.extendScalars φ).obj H) : z = 0 := by
    letI : Algebra A k := φ.toAlgebra
    change k ⊗[A] H at z
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      have e := TensorProduct.smul_tmul (R := A) r ((φ r)⁻¹ * c) x
      have he : r • ((φ r)⁻¹ * c) = c := by
        change φ r * ((φ r)⁻¹ * c) = c
        rw [← mul_assoc, mul_inv_cancel₀ hunit, one_mul]
      rw [he, hann x Submodule.mem_top, TensorProduct.tmul_zero] at e
      exact e
    | add x y hx hy => rw [hx, hy, zero_add]
  exact (hz x).trans (hz y).symm

/-- The injection in the reduction sequence gives surjective multiplication
when the actual prime fibre has zero cohomology. -/
private theorem reduction_surjective {A k : Type u} [CommRing A] [Field k]
    {φ : A →+* k} {a : A} {X : SchemeOverRing A} {L : X.left.Modules}
    (h : CohomologyReduction φ a X L)
    {Idx : Type u} [LinearOrder Idx] [Fintype Idx]
    (U : Idx → X.left.Opens) (hU : IsFiniteAffineCover U)
    (i : ℕ) (hz : IsZero ((cohomology ((changeBase φ).obj X) i).obj (fibreSheaf φ X L))) :
    Function.Surjective ((a • 𝟙 ((cohomology X i).obj L) : _ ⟶ _).hom) := by
  obtain ⟨_, _, _, hseq⟩ := h
  obtain ⟨_, _, hseq⟩ := hseq U hU
  obtain ⟨_, _, _, f, _, _, _, _, _, _, _, hf, _, _⟩ := hseq i
  have hs : Subsingleton ↑((ModuleCat.restrictScalars φ).obj
      ((cohomology ((changeBase φ).obj X) i).obj (fibreSheaf φ X L))) := by
    change Subsingleton ↑((cohomology ((changeBase φ).obj X) i).obj (fibreSheaf φ X L))
    exact ModuleCat.isZero_iff_subsingleton.mp hz
  intro x
  have hx : (LinearMap.range (a • 𝟙 ((cohomology X i).obj L) : _ ⟶ _).hom).mkQ x = 0 :=
    hf (@Subsingleton.elim _ hs _ _)
  exact (Submodule.Quotient.mk_eq_zero _).mp hx

/-- Cohomology of the pullback to a field fibre agrees with that of its
identified opposite-Borel flag and actual associated character line. -/
private theorem fibreCohomology_isZero_iff {A k : Type u} [CommRing A] [Field k]
    {φ : A →+* k} {M : IntegralFlagGeometry.Model A} {D : BasedRootDatum.{u}} {w : D.X}
    (F : FibreIdentification φ M D w) (i : ℕ) :
    let χ : Character F.pair.torus.group :=
      F.torus_eq.symm ▸ Additive.toMul (F.realization.datumIso.val.weightEquiv w)
    IsZero ((cohomology ((changeBase φ).obj M.flag) i).obj (fibreSheaf φ M.flag M.line)) ↔
      IsZero (flagCohomology F.presentation F.projection χ F.kernelPair i) := by
  intro χ
  obtain ⟨_, e, _⟩ := F.lineIso
  let j := F.flagIso.inv.left
  letI : IsIso j := (Over.forget _).map_isIso F.flagIso.inv
  have hj : j ≫ ((changeBase φ).obj M.flag).hom =
      F.presentation.scheme.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
    exact Over.w F.flagIso.inv
  let e' := (Scheme.Modules.pullbackComp j (fibreProjection φ M.flag)).app M.line ≪≫ e
  let P := pushforwardEquivalenceOfIso j
  letI : (Scheme.Modules.pushforward j).IsEquivalence := P.isEquivalence_functor
  let adj := Scheme.Modules.pullbackPushforwardAdjunction j
  letI : (Scheme.Modules.pullback j).IsEquivalence :=
    Functor.isEquivalence_of_iso (P.symm.toAdjunction.leftAdjointUniq adj)
  let α := adj.unit.app (fibreSheaf φ M.flag M.line) ≫
    (Scheme.Modules.pushforward j).map e'.hom
  obtain ⟨c, _⟩ := FlagCohomology.isCohomologyMap_of_isIso j hj α i
  exact c.isZero_iff

private abbrev positivePair {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (P : OppositeBorelPair G) : SplitBorelPair k :=
  ⟨G, P.reductive, P.torus, P.split, P.maximal, P.positive, P.positiveBorel, P.inPositive⟩

private theorem positivePair_eq {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (P : OppositeBorelPair G) (R : SplitBorelPair k) (hG : R.G = G)
    (hT : P.torus = hG ▸ R.T) (hB : P.positive = hG ▸ R.B) :
    R = positivePair P := by
  cases P
  cases R
  dsimp at *
  subst_vars
  rfl

private structure BasedMarking {k : Type u} [Field k] (A : RootGroups.AdditiveLine k)
    (P : SplitBorelPair k) (D : BasedRootDatum.{u}) where
  roots : OrderedRootProducts.RootSubgroupFamily P.T
  pin : Pinning.Pinning A P roots
  attached : AttachedDatum P
  datumIso : Pinning.BasedIso D attached.toBased

private def BasedMarking.pinned {k : Type u} [Field k] {A : RootGroups.AdditiveLine k}
    {P : SplitBorelPair k} {D : BasedRootDatum.{u}} (E : BasedMarking A P D) :
    Pinning.PinnedGroup A :=
  ⟨P, E.roots, E.pin⟩

private def realizationMarking {k : Type u} [Field k] {D : BasedRootDatum.{u}}
    {A : RootGroups.AdditiveLine k} (R : RationalRealization.Realization D A) {P : SplitBorelPair k}
    (hP : R.pinned.pair = P) : BasedMarking A P D :=
  hP ▸ ⟨R.pinned.roots, R.pinned.pin, R.attached, R.datumIso⟩

private theorem realizationMarking_weight {k : Type u} [Field k] {D : BasedRootDatum.{u}}
    {A : RootGroups.AdditiveLine k} (R : RationalRealization.Realization D A) {P : SplitBorelPair k}
    (hP : R.pinned.pair = P) (w : D.X) :
    Additive.toMul ((realizationMarking R hP).datumIso.val.weightEquiv w) =
      cast (congrArg (fun Q : SplitBorelPair k => Character Q.T.group) hP)
        (Additive.toMul (R.datumIso.val.weightEquiv w)) := by
  subst P
  rfl

private def fibreMarking {A k : Type u} [CommRing A] [Field k]
    {φ : A →+* k} {M : IntegralFlagGeometry.Model A} {D : BasedRootDatum.{u}} {w : D.X}
    (F : FibreIdentification φ M D w) :
    BasedMarking F.additive (positivePair F.pair) D :=
  realizationMarking F.realization (positivePair_eq F.pair F.realization.pinned.pair
    rfl F.torus_eq F.positive_eq)

private theorem cast_character {k : Type u} [Field k] {G : GroupScheme k}
    {S T : ClosedSubgroup G} (h : S = T) (χ : Character S.group) :
    cast (congrArg (fun U : ClosedSubgroup G => Character U.group) h) χ = (h ▸ χ) := by
  subst T
  rfl

private theorem fibreMarking_weight {A k : Type u} [CommRing A] [Field k]
    {φ : A →+* k} {M : IntegralFlagGeometry.Model A} {D : BasedRootDatum.{u}} {w : D.X}
    (F : FibreIdentification φ M D w) :
    Additive.toMul ((fibreMarking F).datumIso.val.weightEquiv w) =
      ((F.torus_eq.symm ▸ Additive.toMul (F.realization.datumIso.val.weightEquiv w)) :
        Character F.pair.torus.group) :=
  (realizationMarking_weight _ _ _).trans (cast_character F.torus_eq.symm _)

private theorem dominance_of_markedWeight {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (P : OppositeBorelPair G) {D : BasedRootDatum.{u}} {A : RootGroups.AdditiveLine k}
    (E : BasedMarking A (positivePair P) D) (w : D.X)
    (h : ∀ j : D.base.support, 0 ≤ D.datum.coroot' j.val w) :
    Dominant P (Additive.toMul (E.datumIso.val.weightEquiv w)) := by
  letI := E.attached.comm
  apply (InducedNonvanishing.dominant_iff_datum
    Classification.CentralIsogenies.centralIsogenyComparison P E.attached.datum _).mpr
  intro α
  obtain ⟨j, hj⟩ := E.datumIso.val.indexEquiv.surjective α.val
  have hα : α.val ∈ E.attached.toBased.base.support :=
    (E.attached.simple_iff _).mpr α.property
  have hj' : j ∈ D.base.support := (basedIso_base_iff E.datumIso j).mpr (hj.symm ▸ hα)
  change 0 ≤ E.attached.toBased.datum.coroot' α.val (E.datumIso.val.weightEquiv w)
  rw [← hj, E.datumIso.val.coroot'_weightEquiv]
  exact h ⟨j, hj'⟩

/-- A good prime with vanishing cohomology suffices to kill the finite
cohomology module after extension to a characteristic-zero field. -/
private theorem modelCohomology_vanishes {D : BasedRootDatum.{u}} {w : D.X}
    (hd : ∀ j : D.base.support, 0 ≤ D.datum.coroot' j.val w)
    {k : Type u} [Field k] [CharZero k] (M : PinnedModel D w)
    (hfin : ∀ i : ℕ, Module.Finite (BaseRing.{u} M.m)
      ((cohomology M.model.flag i).obj M.model.line))
    {Idx : Type u} [LinearOrder Idx] [Fintype Idx]
    (U : Idx → M.model.flag.left.Opens) (hU : IsFiniteAffineCover U)
    (hred : ∀ (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ M.m),
      (∃ e : (BaseRing.{u} M.m ⧸ Ideal.span {(p : BaseRing.{u} M.m)}) ≃+*
        IntegralFlagGeometry.PrimeField.{u} p,
        ∀ x : BaseRing.{u} M.m, e (Ideal.Quotient.mk _ x) = primeMap hp x) ∧
      CohomologyReduction (primeMap hp) (p : BaseRing.{u} M.m) M.model.flag M.model.line)
    (i : ℕ) (hi : 0 < i) :
    let φ := (((algebraMap ℚ k).comp ULift.ringEquiv.toRingHom).comp
      (rationalMap M.nonzero))
    IsZero ((cohomology ((changeBase φ).obj M.model.flag) i).obj
      (fibreSheaf φ M.model.flag M.model.line)) := by
  intro φ
  obtain ⟨p, hmp, hpp⟩ := Nat.exists_infinite_primes (M.m + 1)
  letI : Fact p.Prime := ⟨hpp⟩
  have hp : ¬ p ∣ M.m := fun h => (Nat.not_le_of_gt hmp) (Nat.le_of_dvd
    (Nat.pos_of_ne_zero M.nonzero) h)
  obtain ⟨F, _⟩ := M.special p hp
  obtain ⟨⟨e, _⟩, hseq⟩ := hred p hp
  have hdom := dominance_of_markedWeight F.pair (fibreMarking F) w hd
  have hdom' := (congrArg (Dominant F.pair) (fibreMarking_weight F)).mp hdom
  have hz := (fibreCohomology_isZero_iff F i).mpr
    (PositiveKempfVanishing.positiveKempfVanishing p F.pair _ hdom'
      F.presentation F.projection F.kernelPair i hi)
  have hsurj := reduction_surjective hseq U hU i hz
  have hproper : Ideal.span {(p : BaseRing.{u} M.m)} ≠ ⊤ :=
    Ideal.Quotient.nontrivial_iff.mp (e.symm.injective.nontrivial)
  let ψ : ULift.{u} ℚ →+* k := (algebraMap ℚ k).comp ULift.ringEquiv.toRingHom
  letI : Algebra (BaseRing.{u} M.m) (ULift.{u} ℚ) := (rationalMap M.nonzero).toAlgebra
  letI := Cohomology.ArithmeticCohomologyBaseChange.rationalMap_isFractionRing
    (m := (M.m : ℤ)) (Int.natCast_ne_zero.mpr M.nonzero)
  have hφ : Function.Injective φ := ψ.injective.comp
    (IsFractionRing.injective (BaseRing.{u} M.m) (ULift.{u} ℚ))
  have hflat : φ.Flat := (show (rationalMap M.nonzero).Flat from
    IsLocalization.flat (ULift.{u} ℚ) (nonZeroDivisors (BaseRing.{u} M.m))).comp
    (RingHom.Flat.of_isField (Field.toIsField _) ψ)
  letI : IsProper M.model.flag.hom :=
    IntegralFlagGeometry.proper_of_projectiveOver M.model.flag M.model.projective
  letI : CompactSpace M.model.flag.left :=
    QuasiCompact.compactSpace_of_compactSpace M.model.flag.hom
  letI : IsSeparated (terminal.from M.model.flag.left) := by
    rw [← terminal.comp_from M.model.flag.hom]
    infer_instance
  obtain ⟨c, _⟩ := Cohomology.ArithmeticCohomologyBaseChange.flatBaseChange φ hflat
    M.model.flag M.model.line M.lineBundle.1 i
  letI := hfin i
  exact (extension_isZero_of_reduction φ hφ _ _ hproper hsurj).of_iso c.symm

/-- If all integral coroots span the cocharacter lattice, the common
annihilator of the roots in its rationalization is zero. -/
private theorem rationalRootAnnihilator_eq_bot (D : BasedRootDatum.{u})
    (hspan : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    RootData.rationalRootAnnihilator D.datum = ⊥ := by
  classical
  letI := D.finiteRoots
  letI := Fintype.ofFinite D.I
  rw [Submodule.eq_bot_iff]
  intro y hy
  let f := TensorProduct.mk ℤ ℚ D.Y 1
  letI : IsLocalizedModule ℤ⁰ f :=
    IsLocalization.tensorProduct_isLocalizedModule ℤ⁰ ℚ (M := D.Y)
  obtain ⟨⟨x, n⟩, hn⟩ := IsLocalizedModule.surj ℤ⁰ f y
  change n.val • y = f x at hn
  have hx (j : D.I) : D.datum.root' j x = 0 := by
    let l := RootData.extendFunctional ℚ (D.datum.root' j)
    have hyj : l y = 0 := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hy j)
    have h := congrArg l hn
    change l (n.val • y) = l (1 ⊗ₜ[ℤ] x) at h
    rw [LinearMap.map_smul_of_tower, hyj, smul_zero, RootData.extendFunctional_one_tmul] at h
    exact_mod_cast h.symm
  have hxzero : x = 0 := by
    refine D.datum.flip.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero
      (show x ∈ Submodule.span ℤ (Set.range D.datum.coroot) by rw [hspan]; trivial) ?_
    simp [RootPairing.rootForm_apply_apply, RootPairing.coroot', hx]
  have hz : n.val • y = 0 := by rw [hn, hxzero, map_zero]
  exact (smul_right_injective (ℚ ⊗[ℤ] D.Y)
    (show (n.val : ℚ) ≠ 0 by exact_mod_cast nonZeroDivisors.coe_ne_zero n)) (by
      change n.val • y = n.val • (0 : ℚ ⊗[ℤ] D.Y)
      simpa only [smul_zero] using hz)

section MarkedIsomorphism

open BorelsAndChambers (subgroupRoots)
open IsogenyFlagComparison (Restrictions)

variable {k : Type u} [Field k] {G H : AffineAlgebraicGroup k}

/-- A group isomorphism preserving the torus and positive Borel preserves the
opposite Borel, by characterization of a Borel through its root system. -/
private theorem restrictions_of_positiveIso (P : OppositeBorelPair G) (P' : OppositeBorelPair H)
    (f : G.val ≅ H.val) (t : P.torus.group ≅ P'.torus.group)
    (b : P.positive.group ≅ P'.positive.group)
    (ht : P.torus.inclusion ≫ f.hom = t.hom ≫ P'.torus.inclusion)
    (hb : P.positive.inclusion ≫ f.hom = b.hom ≫ P'.positive.inclusion) :
    ∃ r : Restrictions f.hom P P', r.torus = t.hom := by
  let B := transportSubgroup f P.negative
  have hTB : SchemeDerivedGroup.IsSubgroupOf P'.torus B := by
    obtain ⟨j, hj⟩ := P.inNegative
    refine ⟨t.inv ≫ j, ?_⟩
    change (t.inv ≫ j) ≫ P.negative.inclusion ≫ f.hom = P'.torus.inclusion
    simp only [Category.assoc, reassoc_of% hj, ht, Iso.inv_hom_id_assoc]
  obtain ⟨_, _, _, hCorr, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity H P'.reductive P'.torus P'.split P'.maximal
  let d := rootsEquivOfIso (P := positivePair P) (Q := positivePair P') f t ht
  have heq : subgroupRoots P'.torus B = subgroupRoots P'.torus P'.negative := by
    ext β
    obtain ⟨α, rfl⟩ := d.surjective β
    have hpos := transportedPositives (P := positivePair P) (Q := positivePair P') f t ht b hb α
    have hw := weightSpace_le_lieImage_iff f t ht (B := P.negative) (C := B) (Iso.refl _)
      (by simp [B, transportSubgroup]) (d α).val
    have hlabel : t.hom ≫ (d α).val = α.val := t.hom_inv_id_assoc α.val
    rw [hlabel] at hw
    change α ∈ subgroupRoots P.torus P.negative ↔ d α ∈ subgroupRoots P'.torus B at hw
    change α ∈ subgroupRoots P.torus P.positive ↔ d α ∈ subgroupRoots P'.torus P'.positive at hpos
    change d α ∈ subgroupRoots P'.torus B ↔ d α ∈ subgroupRoots P'.torus P'.negative
    rw [← hw, show subgroupRoots P.torus P.negative = _ from P.opposite,
      show subgroupRoots P'.torus P'.negative = _ from P'.opposite]
    exact not_congr hpos
  let b' := subgroupIso ((hCorr.2.2 B P'.negative
    (pushKBorel f P.negativeBorel) P'.negativeBorel hTB P'.inNegative).mp heq)
  letI : IsIso t.hom.hom.hom.left := (underlying k).map_isIso t.hom
  letI : IsIso b'.val.hom.hom.hom.left := (underlying k).map_isIso b'.val.hom
  exact ⟨⟨t.hom, b'.val.hom, ht.symm, b'.property, inferInstance, inferInstance⟩, rfl⟩

end MarkedIsomorphism

private theorem simplyConnectedCharZeroVanishing {k : Type u} [Field k] [CharZero k]
    {G : AffineAlgebraicGroup k} (hG : GeometricRadicals.IsSemisimple G)
    (hsc : SimplyConnectedLattice.GeometricallySimplyConnected G)
    (P : OppositeBorelPair G) (χ : Character P.torus.group) (hχ : Dominant P χ)
    (Q : Presentation P.negative) (b : BorelProjection P) (h : FlagKernelPair Q)
    (i : ℕ) (hi : 0 < i) : IsZero (flagCohomology Q b χ h i) := by
  classical
  let E := Classification.Pinning.attachedDatum (positivePair P)
  letI := E.comm
  let D := E.toBased
  let w : D.X := Additive.ofMul χ
  have hspan : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ :=
    (Classification.SimplyConnectedLattice.latticeCriterion G hG P.torus P.split P.maximal
      E.datum).mp hsc
  have hd (j : D.base.support) : 0 ≤ D.datum.coroot' j.val w := by
    let α : RootWeightAction.SimpleRoot P.torus P.positive :=
      ⟨j.val, (E.simple_iff _).mp j.property⟩
    exact (InducedNonvanishing.dominant_iff_datum
      Classification.CentralIsogenies.centralIsogenyComparison P E.datum χ).mp hχ α
  obtain ⟨M, hfin, _, ⟨Idx, _, _, U, hU⟩, hred⟩ :=
    IntegralFlagModels.integralFlagModel D (rationalRootAnnihilator_eq_bot D hspan) hspan w
  let φ := (((algebraMap ℚ k).comp ULift.ringEquiv.toRingHom).comp (rationalMap M.nonzero))
  have hz := modelCohomology_vanishes hd (k := k) M hfin U hU hred i hi
  obtain ⟨F, _⟩ := M.fieldFibre k φ
  let F' := fibreMarking F
  obtain ⟨V, ⟨pin⟩⟩ := Classification.Pinning.pinningsExist F.additive (positivePair P)
  let Ppin : Pinning.PinnedGroup F.additive := ⟨positivePair P, V, pin⟩
  obtain ⟨f, hf⟩ := pinnedLift Ppin F'.pinned E F'.attached F'.datumIso
  have hχe : Additive.toMul (F'.datumIso.val.weightEquiv w) = f.torus.inv ≫ χ := by
    rw [← hf]
    rfl
  obtain ⟨r, hr⟩ := restrictions_of_positiveIso F.pair P f.symm.group f.symm.torus f.symm.borel
    f.symm.torus_comm f.symm.borel_comm
  have hisog : CentralIsogenies.IsCentralIsogeny f.group.inv := by
    change CentralIsogenies.IsCentralIsogeny f.group.symm.hom
    simpa only [Category.id_comp] using centralIsogeny_postIso f.group.symm
      (identity_isogeny F'.pinned.pair.G)
  apply PositiveKempfVanishing.flagCohomology_isZero_of_centralIsogeny f.group.inv hisog r
    F.presentation Q F.projection b F.kernelPair h χ i
  have hχr : CentralIsogenies.characterPullback r.torus χ =
      (F.torus_eq.symm ▸ Additive.toMul (F.realization.datumIso.val.weightEquiv w)) := by
    change r.torus ≫ χ = _
    rw [hr]
    exact hχe.symm.trans (fibreMarking_weight F)
  rw [hχr]
  exact (fibreCohomology_isZero_iff F i).mp hz

private theorem semisimpleCharZeroVanishing {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {G : AffineAlgebraicGroup k} (hG : GeometricRadicals.IsSemisimple G)
    (P : OppositeBorelPair G) (χ : Character P.torus.group) (hχ : Dominant P χ)
    (Q : Presentation P.negative) (b : BorelProjection P) (h : FlagKernelPair Q)
    (i : ℕ) (hi : 0 < i) : IsZero (flagCohomology Q b χ h i) := by
  obtain ⟨G', P', f, hG', hsc, hf, r, _, hpos⟩ :=
    SimplyConnectedFlagCover.simplyConnectedFlagCover G hG P
  let E := Classification.Pinning.attachedDatum (positivePair P)
  let E' := Classification.Pinning.attachedDatum (positivePair P')
  letI := E.comm
  letI := E'.comm
  let χ' := CentralIsogenies.characterPullback r.torus χ
  have hm := InducedNonvanishing.dominant_iff_datum
    Classification.CentralIsogenies.centralIsogenyComparison P E.datum χ
  have hm' := InducedNonvanishing.dominant_iff_datum
    Classification.CentralIsogenies.centralIsogenyComparison P' E'.datum χ'
  have hχ' := hm'.mpr (PositiveKempfVanishing.isDominant_centralIsogeny_pullback
    f hf r E'.datum E.datum hpos χ (hm.mp hχ))
  obtain ⟨⟨b'⟩, ⟨Q'⟩, _⟩ := LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G' P'
  let h' : FlagKernelPair Q' := HomogeneousQuotient.quotientPullback Q'
  exact PositiveKempfVanishing.flagCohomology_isZero_of_centralIsogeny f hf r
    Q' Q b' b h' h χ i (simplyConnectedCharZeroVanishing hG' hsc P' χ' hχ' Q' b' h' i hi)

private theorem charZeroVanishing_overAlgClosed {k : Type u} [Field k] [CharZero k]
    [IsAlgClosed k] {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G)
    (χ : Character P.torus.group) (Q : Presentation P.negative)
    (b : BorelProjection P) (h : FlagKernelPair Q)
    (h₀ : ¬ IsZero (flagCohomology Q b χ h 0)) (i : ℕ) (hi : 0 < i) :
    IsZero (flagCohomology Q b χ h i) := by
  obtain ⟨_, P', r, _, hD, ⟨b'⟩, ⟨Q'⟩, comparison⟩ :=
    DerivedFlagCohomology.derivedFlagComparison G P
  let h' : FlagKernelPair Q' := HomogeneousQuotient.quotientPullback Q'
  obtain ⟨_, _, _, _, _, _, cohomologyIso⟩ := comparison Q b χ h Q' b' h'
  obtain ⟨e₀, _⟩ := cohomologyIso 0
  obtain ⟨eᵢ, _⟩ := cohomologyIso i
  let χ' : Character P'.torus.group := r.torus ≫ χ
  have hχ' := (PositiveKempfVanishing.dominant_iff_not_isZero_flagCohomologyZero
    P' χ' Q' b' h').mpr (fun hz => h₀ (hz.of_iso e₀))
  exact (semisimpleCharZeroVanishing hD P' χ' hχ' Q' b' h' i hi).of_iso eᵢ

/-- Kempf vanishing for the actual character line of the opposite flag over
an arbitrary field. -/
theorem kempfVanishing : Specs.KempfVanishing.Statement.{u} := by
  classical
  intro k _ G P χ hχ Q b h i hi
  rcases CharP.exists' k with hc | ⟨p, hp, hc⟩
  · letI := hc
    by_cases hG : GeometricRadicals.IsSplitTorus G.val
    · exact PositiveKempfVanishing.splitTorusFlagVanishing P hG Q b χ h i hi
    obtain ⟨F⟩ := FlagCohomologyOverAlgClosure.flagCohomologyOverAlgClosure Q b χ h
    have h₀ := (PositiveKempfVanishing.dominant_iff_not_isZero_flagCohomologyZero P χ Q b h).mp hχ
    have h₀K : ¬ IsZero (flagCohomology F.quotient.presentation F.projection
        (F.multiplicative.character χ) F.kernelPair 0) := by
      intro hz
      exact h₀ ((PositiveKempfVanishing.extendScalars_isZero_iff (K := AlgebraicClosure k) _).mp
        (hz.of_iso (F.cohomologyIso 0)))
    exact (PositiveKempfVanishing.extendScalars_isZero_iff (K := AlgebraicClosure k) _).mp
      ((charZeroVanishing_overAlgClosed F.borels.pair (F.multiplicative.character χ)
        F.quotient.presentation F.projection F.kernelPair h₀K i hi).of_iso (F.cohomologyIso i))
  · letI := hp
    letI := hc
    exact PositiveKempfVanishing.positiveKempfVanishing p P χ hχ Q b h i hi

end

end LinearAlgebraicGroups.Representation.KempfVanishing
