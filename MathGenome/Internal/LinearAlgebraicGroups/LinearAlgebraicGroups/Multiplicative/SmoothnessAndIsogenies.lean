import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.CharacteristicZeroSmoothness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.PowerMapExamples
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Order.Group.PiLex

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Coalgebra Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.SmoothnessAndIsogenies

open LinearAlgebraicGroups.Specs Specs.SmoothnessAndIsogenies Specs.CharacterDescent Specs.DiagonalizableGroups
open CharacterDescent
open MonoidAlgebra

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem reducedGroupAlgebraIff {M : Type u} [CommGroup M] (p : ℕ)
    [Fact p.Prime] [CharP k p] :
    _root_.IsReduced (MonoidAlgebra k M) ↔ (∀ x : M, x ^ p = 1 → x = 1) := by
  classical
  let : CharP (MonoidAlgebra k M) p :=
    charP_of_injective_algebraMap (algebraMap k (MonoidAlgebra k M)).injective p
  constructor
  · intro h x hx
    apply MonoidAlgebra.of_injective (R := k)
    apply frobenius_inj (MonoidAlgebra k M) p
    change (MonoidAlgebra.of k M x) ^ p = (MonoidAlgebra.of k M 1) ^ p
    rw [← map_pow, ← map_pow, hx, one_pow]
  · intro h
    have hi : Function.Injective (powMonoidHom (α := M) p) := by
      intro x y hxy
      apply div_eq_one.mp
      apply h
      exact (div_pow x y p).trans (div_eq_one.mpr hxy)
    have hf : frobenius (MonoidAlgebra k M) p =
        (mapDomainRingHom k (powMonoidHom (α := M) p)).comp (mapRingHom M (frobenius k p)) := by
      apply MonoidAlgebra.ringHom_ext <;> simp [frobenius_def]
    have hg : Function.Injective (mapRingHom M (frobenius k p)) := by
      intro a b hab
      ext m
      exact frobenius_inj k p (by simpa only [coeff_mapRingHom] using congrArg (fun z => z.coeff m) hab)
    have hF : Function.Injective (frobenius (MonoidAlgebra k M) p) :=
      hf ▸ (mapDomain_injective hi).comp hg
    constructor
    intro x hx
    obtain ⟨n, hn⟩ := hx
    have hz : x ^ p ^ n = 0 :=
      pow_eq_zero_of_le ((Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le) hn
    have h0 : (frobenius (MonoidAlgebra k M) p)^[n] 0 = 0 := by
      rw [iterate_frobenius, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
    exact (hF.iterate n) ((iterate_frobenius _ n x).trans (hz.trans h0.symm))

open private specGroup_smooth_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups

private theorem smoothGroupAlgebraIff {M : Type u} [CommGroup M] [Group.FG M]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    Smooth (specGroup (groupAlgebra k M)).X.hom ↔ (∀ x : M, x ^ p = 1 → x = 1) := by
  let A := groupAlgebra k M
  let G := specGroup A
  let : LocallyOfFiniteType G.X.hom := (hopfSpec_locallyOfFiniteType_iff k A).mpr inferInstance
  rw [(groupSmoothnessCriteria k G).1, GeometricallyReduced.eq_geometrically]
  change geometrically (fun Y : Scheme.{u} => AlgebraicGeometry.IsReduced Y)
    (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k M)))) ↔ _
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h
    have hr := h k
    let e := pullbackSymmetry _ _ ≪≫ pullbackSpecIso k k (MonoidAlgebra k M)
    have ht := ObjectProperty.prop_of_iso (P := fun Y : Scheme.{u} => AlgebraicGeometry.IsReduced Y) e hr
    have hR := (affine_isReduced_iff _).mp ht
    exact (reducedGroupAlgebraIff p).mp
      (isReduced_of_injective (Algebra.TensorProduct.includeRight : MonoidAlgebra k M →ₐ[k] _)
        (Algebra.TensorProduct.includeRight_injective (algebraMap k k).injective))
  · intro h L _ _
    let : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
    have : _root_.IsReduced (MonoidAlgebra L M) := (reducedGroupAlgebraIff p).mpr h
    have : _root_.IsReduced (L ⊗[k] MonoidAlgebra k M) :=
      isReduced_of_injective (groupAlgebraBaseChange k L M) (groupAlgebraBaseChange k L M).injective
    let e := pullbackSymmetry _ _ ≪≫ pullbackSpecIso k L (MonoidAlgebra k M)
    exact ObjectProperty.prop_of_iso
      (P := fun Y : Scheme.{u} => AlgebraicGeometry.IsReduced Y) e.symm inferInstance

open private groupLikeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

theorem multiplicativeTypeSmoothness : MultiplicativeTypeSmoothness.{u} := by
  intro k K _ _ _ _ p _ _ A hA
  obtain ⟨M, ⟨e⟩⟩ := (splitsOverSeparableClosure (K := K) A).mp hA
  let : Group.FG M.obj := M.property
  let : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  let χ : M.obj ≃* GeometricCharacters K A := (monomialCharacterEquiv K).trans (groupLikeIso e)
  have hs : Smooth (specGroup A).X.hom ↔ Smooth (specGroup (groupAlgebra K M.obj)).X.hom := by
    rw [specGroup_smooth_iff, specGroup_smooth_iff]
    let E := (CommHopfAlgCat.ofIso e).toAlgEquiv
    constructor
    · intro h
      let : Algebra.Smooth K (K ⊗[k] A) := inferInstance
      exact Algebra.Smooth.of_equiv E.symm
    · intro h
      let : Algebra.Smooth K (K ⊗[k] A) := Algebra.Smooth.of_equiv E
      exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat K
  rw [hs, smoothGroupAlgebraIff p]
  constructor
  · intro h x hx
    obtain ⟨m, rfl⟩ := χ.surjective x
    rw [← map_pow, ← map_one χ] at hx
    rw [h m (χ.injective hx), map_one]
  · intro h m hm
    apply χ.injective
    rw [map_one]
    exact h (χ m) (by rw [← map_pow, hm, map_one])

private def affineOfMultiplicativeType (A : HopfAlgebraCategory k) (h : IsMultiplicativeType A) :
    AffineAlgebraicGroup k :=
  (finiteTypeHopfSpec k).obj (op ⟨A, (multiplicativeTypeProperties A h).1⟩)

theorem multiplicativeTypeSmoothnessCharZero : MultiplicativeTypeSmoothnessCharZero.{u} := by
  intro k _ _ A h
  exact characteristicZeroSmoothness k (affineOfMultiplicativeType A h)

theorem rootsOfUnityNonreduced : RootsOfUnityNonreduced.{u} := by
  intro k _ p n _ _ hn hd
  let : NeZero n := ⟨hn.ne'⟩
  change ¬ AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (rootsOfUnityCoordinates k n)))
  rw [affine_isReduced_iff]
  intro hr
  change _root_.IsReduced (MonoidAlgebra k (ULift.{u} (Multiplicative (ZMod n)))) at hr
  obtain ⟨d, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_mul_pos_left hn
  let x : ULift.{u} (Multiplicative (ZMod (p * d))) := ⟨Multiplicative.ofAdd (d : ZMod (p * d))⟩
  have hx : x ^ p = 1 := by
    apply ULift.ext
    apply Multiplicative.toAdd.injective
    change p • (d : ZMod (p * d)) = 0
    rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_self]
  have he := (reducedGroupAlgebraIff p).mp hr x hx
  have hz : (d : ZMod (p * d)) = 0 := congrArg (fun y => y.down.toAdd) he
  have hlt : d < p * d := by
    simpa using Nat.mul_lt_mul_of_pos_right (Fact.out : p.Prime).one_lt hd0
  have hval := congrArg ZMod.val hz
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.val_zero] at hval
  exact hd0.ne' hval

open private groupAlgebraMap_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private quotientRepresentsImage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

/-- The augmented pushout of a map of group algebras is the group algebra of its cokernel. -/
private theorem groupAlgebraKernelPushout {M N P : Type u} [CommGroup M] [CommGroup N] [CommGroup P]
    (a : M →* N) (q : N →* P) (hq : Function.Surjective q) (he : q.ker = a.range) :
    IsPushout (CommAlgCat.ofHom (groupAlgebraMap k a).hom.toAlgHom)
      (CommAlgCat.ofHom (hopfCounit (groupAlgebra k M)).hom.toAlgHom)
      (CommAlgCat.ofHom (groupAlgebraMap k q).hom.toAlgHom)
      (CommAlgCat.ofHom (hopfUnit (groupAlgebra k P)).hom.toAlgHom) := by
  apply IsPushout.mk'
  · apply CommAlgCat.hom_ext
    apply algHom_ext _ (Subsingleton.elim _ _)
    intro m
    have hm : q (a m) = 1 := show a m ∈ q.ker from he ▸ ⟨m, rfl⟩
    change mapDomainBialgHom k q (mapDomainBialgHom k a (single m 1)) =
      algebraMap k (MonoidAlgebra k P) (counit (R := k) (single m (1 : k)))
    rw [mapDomainBialgHom_single, mapDomainBialgHom_single, hm,
      (isGroupLikeElem_single_one (R := k) (A := k) m).counit_eq_one, map_one, MonoidAlgebra.one_def]
  · intro T f g hf _
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := groupAlgebraMap_surjective (k := k) q hq x
    exact ConcreteCategory.congr_hom hf y
  · intro T f g h
    let φ := (lift k T N).symm f.hom
    have hker : q.ker ≤ φ.ker := by
      rw [he]
      rintro _ ⟨m, rfl⟩
      have hh := ConcreteCategory.congr_hom h (single m (1 : k))
      change f.hom (mapDomainBialgHom k a (single m 1)) =
        g.hom (counit (R := k) (single m (1 : k))) at hh
      rw [mapDomainBialgHom_single,
        (isGroupLikeElem_single_one (R := k) (A := k) m).counit_eq_one, map_one] at hh
      exact hh
    let e := QuotientGroup.quotientKerEquivOfSurjective q hq
    let ψ := (QuotientGroup.lift q.ker φ hker).comp e.symm.toMonoidHom
    refine ⟨CommAlgCat.ofHom (lift k T P ψ), ?_, CommAlgCat.hom_ext (Subsingleton.elim _ _)⟩
    apply CommAlgCat.hom_ext
    apply algHom_ext _ (Subsingleton.elim _ _)
    intro m
    change (lift k T P ψ) (mapDomainBialgHom k q (single m 1)) = f.hom (single m 1)
    rw [mapDomainBialgHom_single]
    rw [lift_single, one_smul, ← lift_symm_apply]
    change ψ (q m) = φ m
    have H : e (QuotientGroup.mk' q.ker m) = q m := rfl
    change QuotientGroup.lift q.ker φ hker (e.symm (q m)) = φ m
    rw [← H, MulEquiv.symm_apply_apply]
    rfl

private def unitHopfSpecIso (k : Type u) [Field k] :
    (specGroup (CommHopfAlgCat.of k k)).X ≅ 𝟙_ (SchemeOver k) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
    change (𝟙 _) ≫ (𝟙 _) = Spec.map (𝟙 (CommRingCat.of k))
    rw [Spec.map_id, Category.comp_id])

private theorem counitSpecCompUnitIso (A : HopfAlgebraCategory k) :
    (specGroupMap (hopfCounit A)).hom.hom =
      (unitHopfSpecIso k).hom ≫ η[(specGroup A).X] := by
  apply Over.OverMorphism.ext
  change (specGroupMap (hopfCounit A)).hom.hom.left =
    𝟙 (Spec (CommRingCat.of k)) ≫ η[(specGroup A).X].left
  exact (hopfSpecOperations k A).2.1.symm.trans (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem hopfKernelSquareOfPushout {A B C : HopfAlgebraCategory k}
    (a : A ⟶ B) (q : B ⟶ C)
    (hp : IsPushout (CommAlgCat.ofHom a.hom.toAlgHom)
      (CommAlgCat.ofHom (hopfCounit A).hom.toAlgHom)
      (CommAlgCat.ofHom q.hom.toAlgHom)
      (CommAlgCat.ofHom (hopfUnit C).hom.toAlgHom)) :
    IsPullback (specGroupMap q).hom.hom (toUnit (specGroup C).X)
      (specGroupMap a).hom.hom η[(specGroup A).X] := by
  let F := algSpec (CommRingCat.of k)
  have : PreservesLimitsOfSize.{u,u} F := AlgebraicGeometry.preservesLimitsOfSize_algSpec
  have h : IsPullback (specGroupMap q).hom.hom (specGroupMap (hopfUnit C)).hom.hom
      (specGroupMap a).hom.hom (specGroupMap (hopfCounit A)).hom.hom :=
    (F.map_isPullback hp.op).flip
  exact h.of_iso (Iso.refl _) (Iso.refl _) (unitHopfSpecIso k) (Iso.refl _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (counitSpecCompUnitIso A))

/-- On split groups the cokernel of the pullback on exponents gives the kernel square. -/
private theorem splitKernelSquare {M N P : Type u} [CommGroup M] [CommGroup N] [CommGroup P]
    (a : M →* N) (q : N →* P) (hq : Function.Surjective q) (he : q.ker = a.range) :
    IsPullback (specGroupMap (groupAlgebraMap k q)).hom.hom (toUnit _)
      (specGroupMap (groupAlgebraMap k a)).hom.hom η[(specGroup (groupAlgebra k M)).X] :=
  hopfKernelSquareOfPushout _ _ (groupAlgebraKernelPushout a q hq he)

open Specs.PowerMapExamples LaurentPolynomial

private def laurentHopfEquiv (k : Type u) [Field k] :
    LaurentPolynomial k ≃ₐc[k] MonoidAlgebra k IntegerCharacters.{u} :=
  (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).trans
    (MonoidAlgebra.domCongrBialgEquiv k k MulEquiv.ulift.symm)

private theorem laurentHopfEquiv_single (m : ℤ) (x : k) :
    laurentHopfEquiv k (AddMonoidAlgebra.single m x) =
      single (⟨Multiplicative.ofAdd m⟩ : IntegerCharacters.{u}) x := by
  change MonoidAlgebra.domCongr k k (MulEquiv.ulift.symm : Multiplicative ℤ ≃* IntegerCharacters.{u})
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k ℤ (AddMonoidAlgebra.single m x)) = _
  rw [AddMonoidAlgebra.toMultiplicativeAlgEquiv_single, MonoidAlgebra.domCongr_single]
  rfl

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem rootsOfUnityPowerSequence : RootsOfUnityPowerSequence.{u} := by
  intro k _ n hn
  let A := torusCoordinates k
  let B := groupAlgebra k IntegerCharacters
  let C := rootsOfUnityCoordinates k n
  let F := hopfSpec (CommRingCat.of k)
  let j : A ≅ B := CommHopfAlgCat.isoMk (laurentHopfEquiv k)
  let a := powMonoidHom (α := IntegerCharacters.{u}) n
  let q := reduceExponents.{u} n
  let f := powerMorphism k n
  let i := specGroupMap (j.hom ≫ groupAlgebraMap k q)
  refine ⟨j, laurentHopfEquiv_single 1 1, ?_⟩
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective x.down.toAdd
    exact ⟨⟨Multiplicative.ofAdd m⟩, ULift.ext (Multiplicative.toAdd.injective hm)⟩
  have hker : q.ker = a.range := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    have heq : q x = 1 ↔ (x.down.toAdd : ZMod n) = 0 := by
      constructor
      · exact congrArg (fun y : ULift.{u} (Multiplicative (ZMod n)) => y.down.toAdd)
      · exact fun h => ULift.ext (Multiplicative.toAdd.injective h)
    rw [heq]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨⟨Multiplicative.ofAdd m⟩, ULift.ext (Multiplicative.toAdd.injective ?_)⟩
      change (n : ℤ) * m = x.down.toAdd
      exact hm.symm
    · rintro ⟨y, rfl⟩
      exact ⟨y.down.toAdd, rfl⟩
  have hj : powerPullback k n ≫ j.hom = j.hom ≫ groupAlgebraMap k a := by
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.coe_toAlgHom_injective
    apply AddMonoidAlgebra.algHom_ext _ (Subsingleton.elim _ _)
    intro m
    change laurentHopfEquiv k (AddMonoidAlgebra.mapDomainBialgHom k (scaleExponents n)
      (AddMonoidAlgebra.single m 1)) =
      mapDomainBialgHom k a (laurentHopfEquiv k (AddMonoidAlgebra.single m 1))
    rw [AddMonoidAlgebra.mapDomainBialgHom_single, laurentHopfEquiv_single,
      laurentHopfEquiv_single, mapDomainBialgHom_single]
    rfl
  have hi : IsClosedImmersion i.hom.hom.left :=
    (hopfMapClosedImmersion k _).mpr
      ((groupAlgebraMap_surjective (k := k) q hq).comp (laurentHopfEquiv k).surjective)
  let N : ClosedSubgroup (specGroup A) := ⟨specGroup C, i, hi⟩
  have hN : IsSchemeKernel f N := by
    let e : (specGroup B).X ≅ (specGroup A).X :=
      (Grp.forget (SchemeOver k)).mapIso (F.mapIso j.op)
    change IsPullback i.hom.hom (toUnit (specGroup C).X) f.hom.hom η[(specGroup A).X]
    apply (splitKernelSquare (k := k) a q hq hker).of_iso (Iso.refl _) e (Iso.refl _) e
    · change _ ≫ (specGroupMap j.hom).hom.hom = _
      rw [← Grp.comp_hom_hom, ← specGroupMap_comp]
      exact (Category.id_comp i.hom.hom).symm
    · exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
    · change (specGroupMap (groupAlgebraMap k a)).hom.hom ≫ (specGroupMap j.hom).hom.hom =
        (specGroupMap j.hom).hom.hom ≫ f.hom.hom
      rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, ← specGroupMap_comp, ← specGroupMap_comp, ← hj]
    · change η[(specGroup B).X] ≫ (specGroupMap j.hom).hom.hom = 𝟙 _ ≫ η[(specGroup A).X]
      rw [Category.id_comp, IsMonHom.one_hom]
  obtain ⟨_, _, _, hf, hflat, hsurj⟩ := PowerMapExamples.powerMapFiniteFaithfullyFlat k n hn
  have hfp : LocallyOfFinitePresentation f.hom.hom.left := by
    let : IsFinite f.hom.hom.left := hf
    let : IsLocallyNoetherian (specGroup A).X.left := by
      change IsLocallyNoetherian (Spec (CommRingCat.of (LaurentPolynomial k)))
      have : Algebra.FiniteType k (MonoidAlgebra k IntegerCharacters.{u}) := inferInstance
      have : Algebra.FiniteType k (LaurentPolynomial k) :=
        Algebra.FiniteType.equiv inferInstance (laurentHopfEquiv k).toAlgEquiv.symm
      have : IsNoetherianRing (LaurentPolynomial k) := Algebra.FiniteType.isNoetherianRing k _
      infer_instance
    infer_instance
  refine ⟨hi, hflat, hsurj, hfp, hN, quotientRepresentsImage (i := 𝟙 _) ?_ hN⟩
  refine ⟨Category.comp_id _, hflat, hsurj, hfp, ?_, ?_⟩
  · change IsAffineHom (Spec.map _)
    infer_instance
  · change IsClosedImmersion (𝟙 _)
    infer_instance

section Connected

open private preconnectedPrimeSpectrum_iff connectedPrimeSpectrum_of_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
private theorem reducedOfSmoothHopf (A : HopfAlgebraCategory k)
    (h : Smooth (specGroup A).X.hom) : _root_.IsReduced A := by
  have : LocallyOfFiniteType (specGroup A).X.hom := inferInstance
  have hgeo := ((groupSmoothnessCriteria k (specGroup A)).1.mp h).geometrically_isReduced
  change geometrically (fun Y : Scheme.{u} => AlgebraicGeometry.IsReduced Y)
    (Spec.map (CommRingCat.ofHom (algebraMap k A))) at hgeo
  exact (affine_isReduced_iff (CommRingCat.of A)).mp (self_of_isIntegral_of_geometrically hgeo)

private def standardLatticeLexEquiv (r : ℕ) :
    Additive (StandardLattice.{u} r) ≃+ Lex (Fin r → ℤ) where
  toFun x := toLex fun i => (x.toMul i).down.toAdd
  invFun x := Additive.ofMul fun i => ⟨Multiplicative.ofAdd (ofLex x i)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem standardLatticeDomain (r : ℕ) :
    IsDomain (MonoidAlgebra k (StandardLattice.{u} r)) := by
  let e := (MonoidAlgebra.toAdditiveBialgEquiv k k (StandardLattice.{u} r)).trans
    (AddMonoidAlgebra.domCongrBialgEquiv k k (standardLatticeLexEquiv r))
  exact e.toAlgEquiv.toRingEquiv.injective.isDomain _

private theorem smoothStandardLattice (r : ℕ) [Group.FG (StandardLattice.{u} r)] :
    Smooth (specGroup (groupAlgebra k (StandardLattice.{u} r))).X.hom := by
  let A := groupAlgebra k (StandardLattice.{u} r)
  let G := specGroup A
  have : LocallyOfFiniteType G.X.hom := (hopfSpec_locallyOfFiniteType_iff k A).mpr inferInstance
  rw [(groupSmoothnessCriteria k G).1, GeometricallyReduced.eq_geometrically]
  change geometrically (fun Y : Scheme.{u} => AlgebraicGeometry.IsReduced Y)
      (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k (StandardLattice.{u} r)))))
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro L _ _
  have : IsDomain (MonoidAlgebra L (StandardLattice.{u} r)) := standardLatticeDomain r
  let e := groupAlgebraBaseChange k L (StandardLattice.{u} r)
  have : _root_.IsReduced (L ⊗[k] MonoidAlgebra k (StandardLattice.{u} r)) :=
    isReduced_of_injective e e.injective
  exact ObjectProperty.prop_of_iso
    (P := fun Y : Scheme.{u} => AlgebraicGeometry.IsReduced Y)
    (pullbackSymmetry _ _ ≪≫ pullbackSpecIso k L _).symm inferInstance

private theorem connectedGeometricSpectrum (A : HopfAlgebraCategory k)
    (hA : IsMultiplicativeType A) [ConnectedSpace (specGroup A).X.left] :
    GeometricallyConnected (specGroup A).X.hom := by
  let G := affineOfMultiplicativeType A hA
  have : ConnectedSpace G.val.X.left := ‹ConnectedSpace (specGroup A).X.left›
  obtain ⟨Q, H, q, i, h, _, _, _⟩ := identityComponentAndQuotient k G
  have hi : Function.Surjective i.hom.hom.left := Set.range_eq_univ.mp
    (h.identityComponent.trans (PreconnectedSpace.connectedComponent_eq_univ _))
  have : IsIso i.hom.hom.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨h.openImmersion, ⟨hi⟩⟩
  change GeometricallyConnected G.val.X.hom
  constructor
  intro L _ q Y a b hp
  let e := asIso i.hom.hom.left
  apply h.geometricallyConnected.geometrically_connectedSpace q (a ≫ e.inv) b
  apply hp.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
  · exact (Category.id_comp _).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · change G.val.X.hom ≫ 𝟙 _ = e.inv ≫ H.X.hom
    rw [Category.comp_id, ← Over.w i.hom.hom, ← Category.assoc]
    change G.val.X.hom = (e.inv ≫ e.hom) ≫ G.val.X.hom
    rw [e.inv_hom_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

private theorem finiteOrderCastNeZero {M : Type u} [CommGroup M]
    [_root_.IsReduced (MonoidAlgebra k M)] (m : M) (hn : 0 < orderOf m) :
    (orderOf m : k) ≠ 0 := by
  intro hz
  have hd := (CharP.cast_eq_zero_iff k (ringChar k) (orderOf m)).mp hz
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · let : Fact (ringChar k).Prime := ⟨hp⟩
    let x := m ^ (orderOf m / ringChar k)
    have horder : orderOf x = ringChar k := orderOf_pow_orderOf_div hn.ne' hd
    have hx : x ^ ringChar k = 1 := horder ▸ pow_orderOf_eq_one x
    have hx' := (reducedGroupAlgebraIff (k := k) (M := M) (ringChar k)).mp inferInstance x hx
    rw [hx', orderOf_one] at horder
    exact hp.ne_one horder.symm
  · rw [hp, zero_dvd_iff] at hd
    exact hn.ne' hd

/-- Averaging over a finite cyclic subgroup produces an idempotent. Its augmentation
is one and its invariance under the generator rules out that it equals one. -/
private theorem noFiniteOrderOfConnectedSplit {M : Type u} [CommGroup M]
    [_root_.IsReduced (MonoidAlgebra k M)] [PreconnectedSpace (PrimeSpectrum (MonoidAlgebra k M))]
    (m : M) (hn : 0 < orderOf m) : m = 1 := by
  let R := MonoidAlgebra k M
  let n := orderOf m
  let x : R := MonoidAlgebra.of k M m
  have hxn : x ^ n = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  let S : R := ∑ i ∈ Finset.range n, x ^ i
  have hS : S * x = S := by
    have h := geom_sum_mul x n
    change S * (x - 1) = x ^ n - 1 at h
    rwa [hxn, sub_self, mul_sub, mul_one, sub_eq_zero] at h
  have hp (i : ℕ) : S * x ^ i = S := by
    induction i with
    | zero => simp
    | succ i hi => rw [pow_succ, ← mul_assoc, hi, hS]
  have hSS : S * S = (n : R) * S := by
    change S * (∑ i ∈ Finset.range n, x ^ i) = _
    rw [Finset.mul_sum]
    simp only [hp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  let c : R := algebraMap k R ((n : k)⁻¹)
  have hc : c * (n : R) = 1 := by
    change algebraMap k R ((n : k)⁻¹) * (n : R) = 1
    rw [← map_natCast (algebraMap k R), ← map_mul,
      inv_mul_cancel₀ (finiteOrderCastNeZero (k := k) m hn), map_one]
  have he : IsIdempotentElem (c * S) := by
    calc
      (c * S) * (c * S) = c * (c * (S * S)) := by ac_rfl
      _ = c * S := by rw [hSS, ← mul_assoc c (n : R) S, hc, one_mul]
  have hε : Bialgebra.counitAlgHom k R (c * S) = 1 := by
    have hx : Bialgebra.counitAlgHom k R x = 1 := (isGroupLikeElem_of (R := k) m).counit_eq_one
    change Bialgebra.counitAlgHom k R (c * ∑ i ∈ Finset.range n, x ^ i) = 1
    rw [map_mul, AlgHom.commutes, map_sum]
    simp only [map_pow, hx, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (finiteOrderCastNeZero (k := k) m hn)
  rcases (preconnectedPrimeSpectrum_iff.mp inferInstance) (c * S) he with h | h
  · rw [h, map_zero] at hε
    exact (zero_ne_one hε).elim
  · apply MonoidAlgebra.of_injective (R := k)
    have hh : (c * S) * x = c * S := by rw [mul_assoc, hS]
    simpa only [h, one_mul, map_one] using hh

private def latticeEquivOfBasis {M : Type u} [CommGroup M] {r : ℕ}
    (b : Module.Basis (Fin r) ℤ (Additive M)) : M ≃* StandardLattice.{u} r where
  toFun x i := ⟨Multiplicative.ofAdd (b.equivFun (Additive.ofMul x) i)⟩
  invFun y := (b.equivFun.symm fun i => (y i).down.toAdd).toMul
  left_inv x := b.equivFun.symm_apply_apply (Additive.ofMul x)
  right_inv y := by
    funext i
    apply ULift.ext
    apply Multiplicative.toAdd.injective
    exact congrFun (b.equivFun.apply_symm_apply (fun j => (y j).down.toAdd)) i
  map_mul' x y := by
    funext i
    apply ULift.ext
    apply Multiplicative.toAdd.injective
    exact congrFun (map_add b.equivFun (Additive.ofMul x) (Additive.ofMul y)) i

set_option backward.isDefEq.respectTransparency false in
theorem smoothConnectedMultiplicativeType : SmoothConnectedMultiplicativeType.{u} := by
  intro k _ A
  constructor
  · intro h
    refine ⟨torusIsMultiplicativeType A h, ?_, ?_⟩
    all_goals obtain ⟨E, _, _, _, r, ⟨e⟩⟩ := h
    · have : Group.FG (StandardLattice.{u} r) := by
        let e : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
        have : Group.FG IntegerCharacters.{u} :=
          Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
        apply Group.fg_def.mpr
        simpa only [Subgroup.pi_top] using
          (Subgroup.FG.pi (P := fun (_ : Fin r) => (⊤ : Subgroup IntegerCharacters)) fun _ =>
            Group.fg_def.mp (inferInstance : Group.FG IntegerCharacters.{u}))
      have : Algebra.Smooth E (MonoidAlgebra E (StandardLattice.{u} r)) :=
        (specGroup_smooth_iff (groupAlgebra E (StandardLattice.{u} r))).mp (smoothStandardLattice r)
      have : Algebra.Smooth E (E ⊗[k] A) :=
        Algebra.Smooth.of_equiv (CommHopfAlgCat.ofIso e).toAlgEquiv
      exact (specGroup_smooth_iff A).mpr (Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat E)
    · have : IsDomain (MonoidAlgebra E (StandardLattice.{u} r)) := standardLatticeDomain r
      let j := (CommHopfAlgCat.ofIso e).toAlgEquiv.symm
      have : IsDomain (E ⊗[k] A) := j.injective.isDomain j.toRingEquiv.toRingHom
      change ConnectedSpace (PrimeSpectrum A)
      let i : A →ₐ[k] E ⊗[k] A := Algebra.TensorProduct.includeRight
      exact connectedPrimeSpectrum_of_injective i.toRingHom
        (Algebra.TensorProduct.includeRight_injective (B := A) (algebraMap k E).injective)
  · rintro ⟨hA, hSmooth, hConn⟩
    let E := SeparableClosure k
    obtain ⟨M, ⟨e⟩⟩ := (splitsOverSeparableClosure (K := E) A).mp hA
    have : Group.FG M.obj := M.property
    let j := (CommHopfAlgCat.ofIso e).toAlgEquiv
    have : Algebra.Smooth k A := (specGroup_smooth_iff A).mp hSmooth
    have : Algebra.Smooth E (MonoidAlgebra E M.obj) := Algebra.Smooth.of_equiv j.symm
    have : _root_.IsReduced (MonoidAlgebra E M.obj) :=
      reducedOfSmoothHopf (groupAlgebra E M.obj) ((specGroup_smooth_iff _).mpr inferInstance)
    have : GeometricallyConnected (specGroup A).X.hom := connectedGeometricSpectrum A hA
    have hExt : ConnectedSpace (PrimeSpectrum (E ⊗[k] A)) := by
      rw [GeometricallyConnected.eq_geometrically] at this
      have hp := (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mp this) E
      let i := pullbackSymmetry _ _ ≪≫ pullbackSpecIso k E A
      exact i.hom.homeomorph.connectedSpace_iff.mp hp
    have : PreconnectedSpace (PrimeSpectrum (MonoidAlgebra E M.obj)) :=
      (connectedPrimeSpectrum_of_injective j.toRingHom j.injective).toPreconnectedSpace
    have : Module.Finite ℤ (Additive M.obj) :=
      Module.Finite.iff_addGroup_fg.mpr inferInstance
    have : Module.IsTorsionFree ℤ (Additive M.obj) := by
      apply Module.IsTorsionFree.of_smul_eq_zero
      intro a m hm
      by_cases ha : a = 0
      · exact Or.inl ha
      right
      have hd : (orderOf m.toMul : ℤ) ∣ a := orderOf_dvd_iff_zpow_eq_one.mpr hm
      have hn : 0 < orderOf m.toMul := by
        by_contra! h
        exact ha (by simpa [Nat.eq_zero_of_le_zero h] using hd)
      exact noFiniteOrderOfConnectedSplit (k := E) m.toMul hn
    obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive M.obj)
    let h := MonoidAlgebra.domCongrBialgEquiv E E (latticeEquivOfBasis b)
    exact ⟨E, inferInstance, inferInstance, inferInstance, r,
      ⟨(CommHopfAlgCat.isoMk h).symm ≪≫ e⟩⟩

end Connected

section Isogenies

open private schemeKernel_exists isMonHom_of_comp_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private extendedGroupIso extendedSpecIso_natural specGroupMap_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private baseChangeKernelSquare from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private groupLikeSpanOfSplit groupAlgebraOfCharacters groupAlgebraOfCharacters_hom_single
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

variable {A B C : HopfAlgebraCategory k}

set_option backward.isDefEq.respectTransparency.types false in
private theorem kernelPresentation (f : A ⟶ B) :
    ∃ (C : HopfAlgebraCategory k) (q : B ⟶ C)
      (hq : IsClosedImmersion (specGroupMap q).hom.hom.left),
      IsSchemeKernel (specGroupMap f) ⟨specGroup C, specGroupMap q, hq⟩ := by
  have : IsAffine (specGroup A).X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  obtain ⟨N, hN⟩ := schemeKernel_exists (specGroupMap f)
  have : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  have : IsAffine (specGroup B).X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))
  have hC := (IsClosedImmersion.isAffine_surjective_of_isAffine N.inclusion.hom.hom.left).1
  obtain ⟨C, ⟨e⟩⟩ := essImage_hopfSpec.mpr hC
  let F := hopfSpec (CommRingCat.of k)
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let q : B ⟶ C.unop := (ff.preimage (e.hom ≫ N.inclusion)).unop
  have hq : specGroupMap q = e.hom ≫ N.inclusion := ff.map_preimage _
  have hqOver : (specGroupMap q).hom.hom = e.hom.hom.hom ≫ N.inclusion.hom.hom :=
    congrArg (fun a => a.hom.hom) hq
  have hq' : IsClosedImmersion (specGroupMap q).hom.hom.left := by
    let U := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    have he : IsIso e.hom.hom.hom.left := U.map_isIso e.hom
    rw [congrArg (fun a => a.hom.hom.left) hq]
    change IsClosedImmersion (e.hom.hom.hom.left ≫ N.inclusion.hom.hom.left)
    infer_instance
  refine ⟨C.unop, q, hq', ?_⟩
  let U := Grp.forget (SchemeOver k)
  change IsPullback (specGroupMap q).hom.hom (toUnit (specGroup C.unop).X)
    (specGroupMap f).hom.hom η[(specGroup A).X]
  apply (show IsPullback N.inclusion.hom.hom (toUnit N.group.X)
    (specGroupMap f).hom.hom η[(specGroup A).X] from hN).of_iso'
    (U.mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · exact hqOver.symm.trans (Category.comp_id _).symm
  · exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem extendedKernelSquare (f : A ⟶ B) (q : B ⟶ C)
    (h : IsPullback (specGroupMap q).hom.hom (toUnit (specGroup C).X)
      (specGroupMap f).hom.hom η[(specGroup A).X]) :
    IsPullback (specGroupMap (extendedHopfMap K q)).hom.hom
      (toUnit (specGroup (extendedHopf K C)).X)
      (specGroupMap (extendedHopfMap K f)).hom.hom
      η[(specGroup (extendedHopf K A)).X] := by
  let U := Grp.forget (SchemeOver K)
  apply (baseChangeKernelSquare (k := k) (K := K) (specGroupMap f) (specGroupMap q) h).of_iso'
    (U.mapIso (extendedGroupIso K C)) (U.mapIso (extendedGroupIso K B))
    (Iso.refl _) (U.mapIso (extendedGroupIso K A))
  · exact (extendedSpecIso_natural K q).symm
  · exact (isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _
  · exact (extendedSpecIso_natural K f).symm
  · change 𝟙 _ ≫ η[_] = η[_] ≫ (extendedGroupIso K A).hom.hom.hom
    rw [Category.id_comp, IsMonHom.one_hom]

variable [IsSepClosure k K]

private def splitByCharacters (A : HopfAlgebraCategory k) (h : IsMultiplicativeType A) :
    groupAlgebra K (GeometricCharacters K A) ≅ extendedHopf K A :=
  groupAlgebraOfCharacters _ (groupLikeSpanOfSplit _ ((splitsOverSeparableClosure A).mp h))

private theorem splitByCharacters_single (A : HopfAlgebraCategory k) (h : IsMultiplicativeType A)
    (x : GeometricCharacters K A) :
    (splitByCharacters (K := K) A h).hom.hom (single x (1 : K)) = x.val :=
  groupAlgebraOfCharacters_hom_single K _ x

private theorem splitByCharacters_natural (f : A ⟶ B)
    (hA : IsMultiplicativeType A) (hB : IsMultiplicativeType B) :
    (splitByCharacters (K := K) A hA).hom ≫ extendedHopfMap K f =
      groupAlgebraMap K (pullbackCharacter K f) ≫ (splitByCharacters (K := K) B hB).hom := by
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  apply MonoidAlgebra.algHom_ext _ (Subsingleton.elim _ _)
  intro x
  change (extendedHopfMap K f).hom ((splitByCharacters (K := K) A hA).hom.hom (single x 1)) =
    (splitByCharacters (K := K) B hB).hom.hom (mapDomainBialgHom K (pullbackCharacter K f) (single x 1))
  rw [splitByCharacters_single, mapDomainBialgHom_single, splitByCharacters_single]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Identify the extended coordinate map of the kernel by comparison of two pullback squares. -/
private theorem splitKernelComparison (f : A ⟶ B) (q : B ⟶ C)
    (hA : IsMultiplicativeType A) (hB : IsMultiplicativeType B)
    (hq : IsClosedImmersion (specGroupMap q).hom.hom.left)
    (hN : IsSchemeKernel (specGroupMap f) ⟨specGroup C, specGroupMap q, hq⟩) :
    let a := pullbackCharacter K f
    ∃ J : extendedHopf K C ≅ groupAlgebra K (GeometricCharacters K B ⧸ a.range),
      (splitByCharacters (K := K) B hB).hom ≫ extendedHopfMap K q ≫ J.hom =
        groupAlgebraMap K (QuotientGroup.mk' a.range) := by
  let X := GeometricCharacters K A
  let Y := GeometricCharacters K B
  let a : X →* Y := pullbackCharacter K f
  let Z := Y ⧸ a.range
  let r : Y →* Z := QuotientGroup.mk' a.range
  let A' := groupAlgebra K X
  let B' := groupAlgebra K Y
  let D := groupAlgebra K Z
  let jA : A' ≅ extendedHopf K A := splitByCharacters A hA
  let jB : B' ≅ extendedHopf K B := splitByCharacters B hB
  let F := hopfSpec (CommRingCat.of K)
  let U := Grp.forget (SchemeOver K)
  let i : specGroup (extendedHopf K C) ⟶ specGroup B' :=
    specGroupMap (jB.hom ≫ extendedHopfMap K q)
  let i' : specGroup D ⟶ specGroup B' := specGroupMap (groupAlgebraMap K r)
  have hE := extendedKernelSquare (K := K) f q hN
  have hE' : IsPullback i.hom.hom (toUnit _) (specGroupMap (groupAlgebraMap K a)).hom.hom
      η[(specGroup A').X] := by
    let eA : (specGroup (extendedHopf K A)).X ≅ (specGroup A').X :=
      U.mapIso (F.mapIso jA.op)
    let eB : (specGroup (extendedHopf K B)).X ≅ (specGroup B').X :=
      U.mapIso (F.mapIso jB.op)
    apply hE.of_iso (Iso.refl _) eB (Iso.refl _) eA
    · change (specGroupMap (extendedHopfMap K q)).hom.hom ≫ (specGroupMap jB.hom).hom.hom =
        𝟙 _ ≫ i.hom.hom
      rw [Category.id_comp, ← Grp.comp_hom_hom, ← specGroupMap_comp]
    · simp
    · change (specGroupMap (extendedHopfMap K f)).hom.hom ≫ (specGroupMap jA.hom).hom.hom =
        (specGroupMap jB.hom).hom.hom ≫ (specGroupMap (groupAlgebraMap K a)).hom.hom
      rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, ← specGroupMap_comp, ← specGroupMap_comp,
        splitByCharacters_natural (K := K) f hA hB]
    · change η[_] ≫ (specGroupMap jA.hom).hom.hom = 𝟙 _ ≫ η[_]
      rw [Category.id_comp, IsMonHom.one_hom]
  have hr : r.ker = a.range := by
    ext x
    exact QuotientGroup.eq_one_iff x
  have hrSurj : Function.Surjective r := QuotientGroup.mk_surjective
  have hD := splitKernelSquare (k := K) (M := X) (N := Y) (P := Z) a r hrSurj hr
  let e := hD.isoIsPullback _ _ hE'
  have he : e.hom ≫ i.hom.hom = i'.hom.hom := hD.isoIsPullback_hom_fst _ _ hE'
  have hqS : Function.Surjective q.hom := (hopfMapClosedImmersion k q).mp hq
  have hqS' : Function.Surjective (extendedHopfMap K q).hom :=
    LinearMap.lTensor_surjective K hqS
  have : IsClosedImmersion i.hom.hom.left :=
    (hopfMapClosedImmersion K _).mpr (hqS'.comp (CommHopfAlgCat.ofIso jB).surjective)
  have := isMonHom_of_comp_closed e.hom i' i he
  let e' : specGroup D ≅ specGroup (extendedHopf K C) := Grp.mkIso' e
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of K)
  let J := (ff.preimageIso e').unop
  have hJ : specGroupMap J.hom = e'.hom := ff.map_preimage _
  have hji : e'.hom ≫ i = i' := Grp.hom_ext _ _ he
  refine ⟨J, ?_⟩
  apply specGroupMap_injective
  rw [specGroupMap_comp, specGroupMap_comp, hJ, Category.assoc, ← specGroupMap_comp]
  exact hji

private theorem injectivePullbackIff (f : A ⟶ B)
    (hA : IsMultiplicativeType A) (hB : IsMultiplicativeType B) :
    Function.Injective (pullbackCharacter K f) ↔ Function.Injective f.hom := by
  let X := GeometricCharacters K A
  let Y := GeometricCharacters K B
  let jA := splitByCharacters (K := K) A hA
  let jB := splitByCharacters (K := K) B hB
  let g := extendedHopfMap K f
  constructor
  · intro h
    have hi := (mapDomain_injective (R := K) h)
    have hg : Function.Injective g.hom := by
      intro x y hxy
      obtain ⟨x, rfl⟩ := (CommHopfAlgCat.ofIso jA).surjective x
      obtain ⟨y, rfl⟩ := (CommHopfAlgCat.ofIso jA).surjective y
      have hxy' : (jA.hom ≫ g).hom x = (jA.hom ≫ g).hom y := hxy
      rw [splitByCharacters_natural (K := K) f hA hB] at hxy'
      exact congrArg jA.hom.hom (hi ((CommHopfAlgCat.ofIso jB).injective hxy'))
    intro x y hxy
    apply (Algebra.TensorProduct.includeRight_injective (B := A) (algebraMap k K).injective)
    apply hg
    exact congrArg ((Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B)) hxy
  · intro h x y hxy
    have hg : Function.Injective g.hom :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := K) f.hom.toLinearMap h
    exact GroupLike.val_injective (hg (congrArg GroupLike.val hxy))

private theorem finiteSpectrumIff (C : HopfAlgebraCategory k) :
    IsFinite (specGroup C).X.hom ↔ Module.Finite k C := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k C))) ↔ Module.Finite k C
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap

private theorem kernelFiniteIff (f : A ⟶ B) (q : B ⟶ C)
    (hA : IsMultiplicativeType A) (hB : IsMultiplicativeType B)
    (hq : IsClosedImmersion (specGroupMap q).hom.hom.left)
    (hN : IsSchemeKernel (specGroupMap f) ⟨specGroup C, specGroupMap q, hq⟩) :
    IsFinite (specGroup C).X.hom ↔ Finite (GeometricCharacters K B ⧸ (pullbackCharacter K f).range) := by
  obtain ⟨J, hJ⟩ := splitKernelComparison (K := K) f q hA hB hq hN
  let Z := GeometricCharacters K B ⧸ (pullbackCharacter K f).range
  let e : (K ⊗[k] C) ≃ₗ[K] MonoidAlgebra K Z :=
    (CommHopfAlgCat.ofIso J).toAlgEquiv.toLinearEquiv
  rw [finiteSpectrumIff]
  constructor
  · intro h
    have : Module.Finite K (MonoidAlgebra K Z) := Module.Finite.equiv e
    exact (MonoidAlgebra.basis Z K).linearIndependent.finite
  · intro h
    have : Module.Finite K (MonoidAlgebra K Z) := Module.Finite.of_basis (MonoidAlgebra.basis Z K)
    have : Module.Finite K (K ⊗[k] C) := Module.Finite.equiv e.symm
    exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat K

private theorem finiteOfKernelComparison (f : A ⟶ B)
    (N N' : ClosedSubgroup (specGroup B)) (hN : IsSchemeKernel (specGroupMap f) N)
    (hN' : IsSchemeKernel (specGroupMap f) N') (h : IsFinite N.group.X.hom) :
    IsFinite N'.group.X.hom := by
  let e : N.group.X ≅ N'.group.X := IsPullback.isoIsPullback _ _ hN hN'
  let U := Over.forget (Spec (CommRingCat.of k))
  have : IsIso e.inv.left := U.map_isIso e.inv
  have hf : IsFinite (e.inv.left ≫ N.group.X.hom) := inferInstance
  rwa [Over.w e.inv] at hf

theorem torusIsogenyCriterion : TorusIsogenyCriterion.{u} := by
  intro k K _ _ _ _ A B f hA hB
  have hA' := torusIsMultiplicativeType A hA
  have hB' := torusIsMultiplicativeType B hB
  let g := specGroupMap f
  let r := CommRingCat.ofHom f.hom.toAlgHom.toRingHom
  obtain ⟨C, q, hq, hN⟩ := kernelPresentation f
  let N : ClosedSubgroup (specGroup B) := ⟨specGroup C, specGroupMap q, hq⟩
  have hk := kernelFiniteIff (K := K) f q hA' hB' hq hN
  have hi := injectivePullbackIff (K := K) f hA' hB'
  constructor
  · rintro ⟨hs, N', hN', hfin⟩
    have : _root_.IsReduced A :=
      reducedOfSmoothHopf A ((smoothConnectedMultiplicativeType A).mp hA).2.1
    have hd : DenseRange (PrimeSpectrum.comap r.hom) := hs.surj.denseRange
    have hker := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical r.hom).mp hd
    rw [nilradical_eq_zero] at hker
    have hInjective : Function.Injective r.hom :=
      (RingHom.injective_iff_ker_eq_bot r.hom).mpr (le_bot_iff.mp hker)
    exact ⟨hi.mpr hInjective, hk.mp (finiteOfKernelComparison f N' N hN' hN hfin)⟩
  · rintro ⟨hf, hs⟩
    have : Algebra.FiniteType k A := (multiplicativeTypeProperties A hA').1
    have : Algebra.FiniteType k B := (multiplicativeTypeProperties B hB').1
    obtain ⟨_, hsurj⟩ := (flat_and_surjective_SpecMap_iff r).mpr
      (hopfFaithfulFlatness k f (hi.mp hf))
    exact ⟨hsurj, N, hN, hk.mpr hs⟩

open private extendedHopfMap_equivariant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

theorem characterPullbackEquivariant : CharacterPullbackEquivariant.{u} := by
  intro k K _ _ _ _ A B f _ _ σ x y h
  have he := extendedHopfMap_equivariant K f σ x.val
  exact he.symm.trans (congrArg (extendedHopfMap K f).hom h)

set_option backward.isDefEq.respectTransparency false in
theorem torusIsogenyKernel : TorusIsogenyKernel.{u} := by
  intro k K _ _ _ _ A B f hA hB hf
  have hA' := torusIsMultiplicativeType A hA
  have hB' := torusIsMultiplicativeType B hB
  obtain ⟨C, q, hq, hN⟩ := kernelPresentation f
  obtain ⟨J, hJ⟩ := splitKernelComparison (K := K) f q hA' hB' hq hN
  let a := pullbackCharacter K f
  let Z := GeometricCharacters K B ⧸ a.range
  have hZ : Finite Z := ((torusIsogenyCriterion (K := K) f hA hB).mp hf).2
  have hin := (kernelFiniteIff (K := K) f q hA' hB' hq hN).mpr hZ
  have hM : Group.FG Z := inferInstance
  have hC : IsMultiplicativeType C :=
    (splitsOverSeparableClosure (K := K) C).mpr ⟨⟨CommGrpCat.of Z, hM⟩, ⟨J.symm⟩⟩
  let : CommGroup Z := inferInstanceAs (CommGroup (GeometricCharacters K B ⧸ a.range))
  let d : Z ≃* GroupLike K (MonoidAlgebra K Z) := monomialCharacterEquiv (M := Z) K
  let j : GroupLike K (MonoidAlgebra K Z) ≃* GeometricCharacters K C := groupLikeIso J.symm
  let e := d.trans j
  have heq (x : GeometricCharacters K B) :
      e (QuotientGroup.mk' a.range x) = pullbackCharacter K q x := by
    apply GroupLike.val_injective
    apply (CommHopfAlgCat.ofIso J).injective
    have he := ConcreteCategory.congr_hom (congrArg
        (fun z => (forgetHopfAlgebra K).map z) hJ) (single x (1 : K))
    change J.hom.hom ((extendedHopfMap K q).hom
      ((splitByCharacters (K := K) B hB').hom.hom (single x 1))) =
        mapDomainBialgHom K (QuotientGroup.mk' a.range) (single x 1) at he
    rw [splitByCharacters_single, mapDomainBialgHom_single] at he
    have hel : J.hom.hom (e (QuotientGroup.mk' a.range x)).val =
        single (QuotientGroup.mk' a.range x) 1 := by
      change J.hom.hom (J.inv.hom (single (QuotientGroup.mk' a.range x) 1)) = _
      exact (CommHopfAlgCat.ofIso J).apply_symm_apply _
    change J.hom.hom (e (QuotientGroup.mk' a.range x)).val =
      J.hom.hom ((extendedHopfMap K q).hom x.val)
    exact hel.trans he.symm
  refine ⟨C, q, hq, hC, hin, hN, e, heq, ?_⟩
  intro σ x y h
  rw [heq, heq]
  exact characterPullbackEquivariant q hB' hC σ x y h

open private geometricCharacterFunctor_full geometricCharacterFunctor_faithful
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

theorem torusIsogenyCorrespondence : TorusIsogenyCorrespondence.{u} := by
  intro k K _ _ _ _ A B hA hB g hG hg hfin
  have hA' := torusIsMultiplicativeType A hA
  have hB' := torusIsMultiplicativeType B hB
  let X : MultiplicativeTypeHopf k := ⟨⟨A, (multiplicativeTypeProperties A hA').1⟩, hA'⟩
  let Y : MultiplicativeTypeHopf k := ⟨⟨B, (multiplicativeTypeProperties B hB').1⟩, hB'⟩
  let F := geometricCharacterFunctor (k := k) K
  have : F.Full := geometricCharacterFunctor_full K
  have : F.Faithful := geometricCharacterFunctor_faithful K
  let G : F.obj X ⟶ F.obj Y := ObjectProperty.homMk
    { hom := CommGrpCat.ofHom g
      comm σ := by
        apply CommGrpCat.ext
        intro x
        apply GroupLike.val_injective
        exact (hG σ x _ rfl).symm }
  let f : X ⟶ Y := F.preimage G
  have hf : F.map f = G := F.map_preimage G
  have he : pullbackCharacter K f.hom.hom = g :=
    congrArg (fun t => t.hom.hom.hom) hf
  have hF : IsTorusIsogeny f.hom.hom := (torusIsogenyCriterion (K := K) f.hom.hom hA hB).mpr
    (by rw [he]; exact ⟨hg, hfin⟩)
  refine ⟨f.hom.hom, ⟨hF, he⟩, ?_⟩
  rintro f' ⟨_, hf'⟩
  let a : X ⟶ Y := ObjectProperty.homMk (InducedCategory.homMk f')
  have ha : F.map a = G := by
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact CommGrpCat.ext (DFunLike.congr_fun hf')
  exact congrArg (fun z : X ⟶ Y => z.hom.hom) (F.map_injective (ha.trans hf.symm))

end Isogenies

end

end LinearAlgebraicGroups.SmoothnessAndIsogenies
