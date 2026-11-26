import LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import LinearAlgebraicGroups.Reductive.GeometricRadicals
import LinearAlgebraicGroups.Unipotent.Orthogonality
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Noetherian.Nilpotent
import Specs.LinearAlgebraicGroups.Reductive.WeilRestrictionBoundary

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.WeilRestrictionBoundary

open Specs.WeilRestrictionBoundary
open Algebra.TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

private theorem residue_surjective {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (e : K →ₐ[k] L) :
    Function.Surjective (residue e) :=
  fun x => ⟨x ⊗ₜ[k] (1 : K), by simp [residue]⟩

theorem localTensorAlgebra : LocalTensorAlgebra.{u} := by
  intro k K _ _ _ _ _ hproper e
  dsimp only
  let L := AlgebraicClosure k
  let A := L ⊗[k] K
  let r : A →ₐ[L] L := residue e
  let J := RingHom.ker r.toRingHom
  have hr := residue_surjective e
  have hmax : J.IsMaximal := RingHom.ker_isMaximal_of_surjective r.toRingHom hr
  obtain ⟨q, hq⟩ := ExpChar.exists k
  let : ExpChar k q := hq
  let : ExpChar A q := expChar_of_injective_algebraMap (algebraMap k A).injective q
  have hnil (x : K) : IsNilpotent ((1 : L) ⊗ₜ[k] x - e x ⊗ₜ[k] (1 : K)) := by
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem k q x
    refine ⟨q ^ n, ?_⟩
    rw [sub_pow_expChar_pow, tmul_pow, tmul_pow, one_pow, one_pow, ← map_pow, ← hy,
      e.commutes, ← tmul_one_eq_one_tmul, sub_self]
  have hdif (a : A) : a - algebraMap L A (r a) ∈ nilradical A := by
    induction a using TensorProduct.inductionOn with
    | tmul l x =>
      change l ⊗ₜ[k] x - (l * e x) ⊗ₜ[k] (1 : K) ∈ nilradical A
      have h : l ⊗ₜ[k] x - (l * e x) ⊗ₜ[k] (1 : K) =
          (l ⊗ₜ[k] (1 : K)) * ((1 : L) ⊗ₜ[k] x - e x ⊗ₜ[k] (1 : K)) := by
        simp [mul_sub, tmul_mul_tmul]
      rw [h]
      exact Ideal.mul_mem_left _ _ ((mem_nilradical).mpr (hnil x))
    | add a b ha hb =>
      rw [map_add, map_add, add_sub_add_comm]
      exact Ideal.add_mem _ ha hb
  have hj : J ≤ nilradical A := by
    intro a ha
    have h : r a = 0 := ha
    simpa only [h, map_zero, sub_zero] using hdif a
  have : IsNoetherianRing A := IsNoetherianRing.of_finite L A
  have hn : IsNilpotent J :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian J)).mpr hj
  have hl : IsLocalRing A := by
    refine IsLocalRing.of_unique_max_ideal ⟨J, hmax, fun I hI => ?_⟩
    let : I.IsPrime := hI.isPrime
    exact (hmax.eq_of_le hI.ne_top (hj.trans (nilradical_le_prime I))).symm
  have hne : J ≠ ⊥ := by
    intro h
    have hi : Function.Injective r := (RingHom.injective_iff_ker_eq_bot r.toRingHom).mpr h
    let i := AlgEquiv.ofBijective r ⟨hi, hr⟩
    have hdim := i.toLinearEquiv.finrank_eq
    let b := Module.Free.chooseBasis k K
    have hdim' := Module.finrank_eq_card_basis (b.baseChange L)
    have hdim'' := Module.finrank_eq_card_basis b
    have hrank : Module.finrank k K = 1 := by
      rw [hdim'', ← hdim', hdim, Module.finrank_self]
    exact hproper (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hrank).2
  exact ⟨hl, hmax, hne, hn, hr, Ideal.quotientKerAlgEquivOfSurjective hr,
    Ideal.quotientKerAlgEquivOfSurjective_mk hr⟩


open WeilRestriction (extendedUnits extendScalars tensorMap multiplicativeRestriction
  multiplicativeRestrictionUnits)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.GeometricRadicals (IsTrivialSubgroup)
open Specs.StandardGroups (multiplicativePoints)

open private pointsFullyFaithful from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

private def fromPoints {k : Type u} [Field k] (G H : AffineAlgebraicGroup k)
    (f : (groupPointsFunctor k).obj G.val ⟶ (groupPointsFunctor k).obj H.val) :
    G.val ⟶ H.val :=
  (G.groupHomEquiv H).symm f

@[simp] private theorem map_fromPoints {k : Type u} [Field k] (G H : AffineAlgebraicGroup k)
    (f : (groupPointsFunctor k).obj G.val ⟶ (groupPointsFunctor k).obj H.val) :
    (groupPointsFunctor k).map (fromPoints G H f) = f :=
  (G.groupHomEquiv H).apply_symm_apply f

private def representedGroupIso {k : Type u} [Field k] {G H : AffineAlgebraicGroup k}
    {F : TestAlgebra k ⥤ GrpCat.{u}}
    (e : (groupPointsFunctor k).obj G.val ≅ F) (d : (groupPointsFunctor k).obj H.val ≅ F) :
    G.val ≅ H.val :=
  (inducedFunctor Subtype.val : AffineAlgebraicGroupCategory k ⥤ _).mapIso
    ((pointsFullyFaithful k).preimageIso (X := G) (Y := H) (e ≪≫ d.symm))

private theorem geometry_of_open_affineSpace {k : Type u} [Field k] {index : Type u}
    [Finite index] (G : GroupScheme k)
    (i : G.X.left ⟶ AffineSpace index (Spec (CommRingCat.of k))) [IsOpenImmersion i]
    (hi : i ≫ (AffineSpace index (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) = G.X.hom) :
    Smooth G.X.hom ∧ GeometricallyConnected G.X.hom := by
  constructor
  · rw [← hi]
    infer_instance
  · rw [geometricallyConnected_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
    intro F _ f
    let S := Spec (CommRingCat.of k)
    let T := Spec (CommRingCat.of F)
    let j : pullback G.X.hom f ⟶ AffineSpace index T :=
      (AffineSpace.isPullback_map f).lift
        (pullback.fst G.X.hom f ≫ i) (pullback.snd G.X.hom f) (by
          rw [Category.assoc, hi, pullback.condition])
    let hA := AffineSpace.isPullback_map (n := index) f
    have hj₁ : j ≫ AffineSpace.map index f = pullback.fst G.X.hom f ≫ i :=
      hA.lift_fst _ _ _
    have hj₂ : j ≫ (AffineSpace index T ↘ T) = pullback.snd G.X.hom f :=
      hA.lift_snd _ _ _
    have hs : IsPullback (pullback.fst G.X.hom f) j i (AffineSpace.map index f) := by
      have hc : IsPullback (j ≫ (AffineSpace index T ↘ T)) (pullback.fst G.X.hom f)
          f (i ≫ (AffineSpace index S ↘ S)) := by
        rw [hj₂, hi]
        exact (IsPullback.of_hasPullback G.X.hom f).flip
      exact ((IsPullback.paste_horiz_iff hA.flip hj₁).mp hc).flip
    have : IsOpenImmersion j :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) hs inferInstance
    have : Nonempty (pullback G.X.hom f : Scheme) := by
      let e : S ⟶ G.X.left := (η[G.X]).left
      have he : e ≫ G.X.hom = 𝟙 S := (η[G.X]).w
      exact ⟨(pullback.lift (f ≫ e) (𝟙 T) (by rw [Category.assoc, he, Category.comp_id,
        Category.id_comp])) (IsLocalRing.closedPoint F)⟩
    have : IrreducibleSpace (pullback G.X.hom f : Scheme) :=
      j.isOpenEmbedding.irreducibleSpace
    infer_instance

theorem smoothGeometricallyConnected : SmoothGeometricallyConnected.{u} := by
  intro k K _ _ _ _ G h
  obtain ⟨e⟩ := h
  let b := Module.Free.chooseBasis k K
  let H := WeilRestriction.openNormGroup b
  let d := representedGroupIso e (WeilRestriction.openNormGroupPoints b)
  let P := MvPolynomial (Module.Free.ChooseBasisIndex k K) k
  let D := WeilRestriction.NormCoordinates b
  let a : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of P) :=
    Spec.map (CommRingCat.ofHom (algebraMap P D))
  let c := (AffineSpace.SpecIso (Module.Free.ChooseBasisIndex k K) (CommRingCat.of k)).inv
  have hd : d.hom.hom.hom.left ≫ H.val.X.hom = G.val.X.hom := d.hom.hom.hom.w
  have : IsIso d.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))).map_isIso d.hom
  have : IsOpenImmersion a := by dsimp [a, D, P]; infer_instance
  have : IsIso c := by dsimp [c]; infer_instance
  have : IsOpenImmersion d.hom.hom.hom.left := inferInstance
  have : IsOpenImmersion c := inferInstance
  have : IsOpenImmersion (a ≫ c) := .comp a c
  have : IsOpenImmersion (d.hom.hom.hom.left ≫ a ≫ c) := .comp _ _
  apply geometry_of_open_affineSpace G.val (d.hom.hom.hom.left ≫ a ≫ c)
  have hc : c ≫ (AffineSpace (Module.Free.ChooseBasisIndex k K) (Spec (CommRingCat.of k))
      ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k P)) :=
    AffineSpace.SpecIso_inv_over _
  simp only [Category.assoc, hc]
  rw [← hd]
  congr 1
  change a ≫ Spec.map (CommRingCat.ofHom (algebraMap k P)) =
    Spec.map (CommRingCat.ofHom (algebraMap k D))
  rw [← Spec.map_comp]
  rfl

private def baseChangePointIso {k : Type u} [Field k] (L : Type u) [Field L] [Algebra k L]
    (G : GroupScheme k) : (groupPointsFunctor L).obj ((groupBaseChange k L).obj G) ≅
      restrictTestAlgebra k L ⋙ (groupPointsFunctor k).obj G :=
  NatIso.ofComponents (fun R ↦ (baseChangePointGroupEquiv L G R).toGrpIso) (by
    intro R S a
    apply GrpCat.ext
    intro p
    exact baseChangePointsNaturality k L G.X a p)

open private tensorMap_tmul from LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction

private def evalMap (k K : Type u) [Field k] [Field K] [Algebra k K] (R : TestAlgebra K) :
    (restrictTestAlgebra k K).obj R ⊗[k] K →+* R :=
  let S := (restrictTestAlgebra k K).obj R
  let a : K →ₐ[k] S := ⟨algebraMap K R, fun _ => rfl⟩
  (a.liftEquiv k S K S).toRingHom

@[simp] private theorem evalMap_tmul (k K : Type u) [Field k] [Field K] [Algebra k K]
    (R : TestAlgebra K) (r : R) (x : K) :
    evalMap k K R ((r : (restrictTestAlgebra k K).obj R) ⊗ₜ[k] x) =
      r * algebraMap K R x := by
  rfl

private def evalUnits (k K : Type u) [Field k] [Field K] [Algebra k K] :
    restrictTestAlgebra k K ⋙ extendedUnits k K ⟶ multiplicativePoints K where
  app R := GrpCat.ofHom (Units.map (evalMap k K R).toMonoidHom)
  naturality {R S} f := by
    apply GrpCat.ext
    intro x
    apply Units.ext
    change evalMap k K S (tensorMap k K ((restrictTestAlgebra k K).map f).hom x.val) =
      f.hom (evalMap k K R x.val)
    induction x.val using TensorProduct.inductionOn with
    | tmul a b =>
      rw [tensorMap_tmul, evalMap_tmul, evalMap_tmul, map_mul, f.hom.commutes]
      rfl
    | add a b ha hb => simp only [map_add, ha, hb]

private theorem eval_detects {k K : Type u} [Field k] [Field K] [Algebra k K]
    {F : TestAlgebra k ⥤ GrpCat.{u}} (a : F ⟶ extendedUnits k K)
    (h : ∀ (R : TestAlgebra K) (x : F.obj ((restrictTestAlgebra k K).obj R)),
      (evalUnits k K).app R (a.app _ x) = 1) :
    ∀ (R : TestAlgebra k) (x : F.obj R), a.app R x = 1 := by
  intro R x
  let T := (extendScalars k K).obj R
  let S := (restrictTestAlgebra k K).obj T
  let : Algebra k S := S.algebra
  let iHom : @AlgHom k R S _ _ _ R.algebra S.algebra :=
    { toRingHom := (includeLeftRingHom : R →+* R ⊗[k] K)
      commutes' := fun y => by
        change algebraMap k R y ⊗ₜ[k] (1 : K) = (1 : R) ⊗ₜ[k] algebraMap k K y
        exact tmul_one_eq_one_tmul y }
  let i : R ⟶ S := ConcreteCategory.ofHom (C := TestAlgebra k) iHom
  have hn := ConcreteCategory.congr_hom (a.naturality i) x
  change a.app _ (F.map i x) = (extendedUnits k K).map i (a.app R x) at hn
  have h' := h T (F.map i x)
  rw [hn] at h'
  apply Units.ext
  change (a.app R x : (R ⊗[k] K)ˣ).val = 1
  have he := congrArg (fun z : Tˣ => z.val) h'
  change evalMap k K T (tensorMap k K (S := S) i.hom (a.app R x : (R ⊗[k] K)ˣ).val) = 1 at he
  have hid (z : R ⊗[k] K) : evalMap k K T (tensorMap k K (S := S) i.hom z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul r y =>
      rw [tensorMap_tmul, evalMap_tmul]
      change (r ⊗ₜ[k] (1 : K)) * ((1 : R) ⊗ₜ[k] y) = _
      simp [tmul_mul_tmul]
    | add a b ha hb => simp only [map_add, ha, hb]
  simpa only [hid] using he


section PrincipalUnits

variable {F A : Type u} [Field F] [CommRing A] [Algebra F A]

private abbrev idealTensor (I : Ideal A) (R : TestAlgebra F) :
    (R ⊗[F] I) →ₗ[F] (R ⊗[F] A) :=
  (I.restrictScalars F).subtype.lTensor R

private theorem idealTensor_injective (I : Ideal A) (R : TestAlgebra F) :
    Function.Injective (idealTensor I R) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

private theorem idealTensor_mem_range (I : Ideal A) (R : TestAlgebra F) (x : R ⊗[F] A) :
    x ∈ LinearMap.range (idealTensor I R) ↔ x ∈ extendedPrincipalIdeal I R := by
  exact Iff.of_eq (congrArg (fun P : Submodule F (R ⊗[F] A) ↦ x ∈ P)
    (Ideal.map_includeRight_eq (R := F) (A := R) I)).symm

private theorem extendedIdeal_nilpotent (I : Ideal A) (hI : IsNilpotent I) (R : TestAlgebra F) :
    IsNilpotent (extendedPrincipalIdeal I R) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  let f : A →+* R ⊗[F] A := (includeRight : A →ₐ[F] R ⊗[F] A).toRingHom
  change I.map f ^ n = ⊥
  change I ^ n = ⊥ at hn
  rw [← Ideal.map_pow, hn, Ideal.map_bot]

private def principalUnitOfTensor (I : Ideal A) (hI : IsNilpotent I)
    (R : TestAlgebra F) (z : R ⊗[F] I) : (principalUnits I).obj R := by
  have hmem : idealTensor I R z ∈ extendedPrincipalIdeal I R :=
    (idealTensor_mem_range I R _).mp (LinearMap.mem_range_self _ _)
  have hnil : IsNilpotent (idealTensor I R z) := by
    obtain ⟨n, hn⟩ := extendedIdeal_nilpotent I hI R
    change extendedPrincipalIdeal I R ^ n = ⊥ at hn
    have hp := Ideal.pow_mem_pow hmem n
    rw [hn] at hp
    exact ⟨n, Ideal.mem_bot.mp hp⟩
  let hu := hnil.isUnit_one_add
  refine ⟨hu.unit, (mem_principalUnitsAt I R _).mpr ?_⟩
  rw [IsUnit.unit_spec, add_sub_cancel_left]
  exact hmem

@[simp] private theorem principalUnitOfTensor_val (I : Ideal A) (hI : IsNilpotent I)
    (R : TestAlgebra F) (z : R ⊗[F] I) :
    (principalUnitOfTensor I hI R z).val.val = 1 + idealTensor I R z := by
  unfold principalUnitOfTensor
  exact IsUnit.unit_spec _

private def principalUnitTensorEquiv (I : Ideal A) (hI : IsNilpotent I) (R : TestAlgebra F) :
    (R ⊗[F] I) ≃ (principalUnits I).obj R :=
  Equiv.ofBijective (principalUnitOfTensor I hI R) <| by
    constructor
    · intro x y h
      apply idealTensor_injective I R
      have hv := congrArg (fun v : (principalUnits I).obj R ↦ v.val.val) h
      exact add_left_cancel (by simpa only [principalUnitOfTensor_val] using hv)
    · intro x
      have hx : x.val.val - 1 ∈ extendedPrincipalIdeal I R :=
        (mem_principalUnitsAt I R _).mp x.property
      obtain ⟨z, hz⟩ := (idealTensor_mem_range I R _).mpr hx
      refine ⟨z, Subtype.ext (Units.ext ?_)⟩
      rw [principalUnitOfTensor_val, hz, add_comm, sub_add_cancel]

private theorem principalUnitTensorEquiv_symm_apply (I : Ideal A) (hI : IsNilpotent I)
    (R : TestAlgebra F) (x : (principalUnits I).obj R) :
    idealTensor I R ((principalUnitTensorEquiv I hI R).symm x) = x.val.val - 1 := by
  let e := principalUnitTensorEquiv I hI R
  have h := congrArg (fun v : (principalUnits I).obj R ↦ v.val.val) (e.apply_symm_apply x)
  change (principalUnitOfTensor I hI R (e.symm x)).val.val = _ at h
  rw [principalUnitOfTensor_val] at h
  rw [← h, add_sub_cancel_left]

private theorem idealTensor_naturality (I : Ideal A) {R S : TestAlgebra F}
    (f : R ⟶ S) (z : R ⊗[F] I) :
    idealTensor I S (LinearMap.rTensor I f.hom.toLinearMap z) =
      tensorMap F A f.hom (idealTensor I R z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem principalUnitOfTensor_naturality (I : Ideal A) (hI : IsNilpotent I)
    {R S : TestAlgebra F} (f : R ⟶ S) (z : R ⊗[F] I) :
    principalUnitOfTensor I hI S (LinearMap.rTensor I f.hom.toLinearMap z) =
      (principalUnits I).map f (principalUnitOfTensor I hI R z) := by
  apply Subtype.ext
  apply Units.ext
  change (principalUnitOfTensor I hI S _).val.val =
    tensorMap F A f.hom (principalUnitOfTensor I hI R z).val.val
  simp only [principalUnitOfTensor_val, idealTensor_naturality, map_add, map_one]

private theorem principalUnitTensorEquiv_symm_naturality (I : Ideal A) (hI : IsNilpotent I)
    {R S : TestAlgebra F} (f : R ⟶ S) (x : (principalUnits I).obj R) :
    (principalUnitTensorEquiv I hI S).symm ((principalUnits I).map f x) =
      LinearMap.rTensor I f.hom.toLinearMap ((principalUnitTensorEquiv I hI R).symm x) := by
  apply (principalUnitTensorEquiv I hI S).injective
  rw [Equiv.apply_symm_apply]
  change _ = principalUnitOfTensor I hI S _
  rw [principalUnitOfTensor_naturality]
  exact congrArg (fun x ↦ (principalUnits I).map f x)
    ((principalUnitTensorEquiv I hI R).apply_symm_apply x).symm

private abbrev powerQuotient (I : Ideal A) (i : ℕ) := (I ^ i : Ideal A) ⧸ nextPower (F := F) I i

private theorem power_nilpotent (I : Ideal A) (hI : IsNilpotent I) {i : ℕ} (hi : 0 < i) :
    IsNilpotent (I ^ i) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, le_antisymm ?_ bot_le⟩
  rw [← hn]
  exact pow_le_pow_left' (Ideal.pow_le_pow_right (I := I) (m := 1) hi |>.trans_eq (pow_one I)) n

private theorem idealTensor_nextPower_range (I : Ideal A) (i : ℕ) (R : TestAlgebra F)
    (z : R ⊗[F] (I ^ i : Ideal A)) :
    (nextPower (F := F) I i).mkQ.lTensor R z = 0 ↔
      idealTensor (I ^ i) R z ∈ extendedPrincipalIdeal (I ^ (i + 1)) R := by
  let j : (I ^ (i + 1) : Ideal A) →ₗ[F] (I ^ i : Ideal A) :=
    Submodule.inclusion (show (I ^ (i + 1) : Ideal A).restrictScalars F ≤
      (I ^ i : Ideal A).restrictScalars F from Ideal.pow_le_pow_right (Nat.le_succ i))
  have hj : Function.Exact j (nextPower (F := F) I i).mkQ := by
    intro x
    change _ = 0 ↔ ∃ y, j y = x
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property
  have hcomp (w : R ⊗[F] (I ^ (i + 1) : Ideal A)) :
      idealTensor (I ^ i) R (j.lTensor R w) = idealTensor (I ^ (i + 1)) R w := by
    induction w using TensorProduct.inductionOn with
    | tmul r y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  -- Both sides ask whether z comes from R ⊗ I^(i+1).
  rw [← idealTensor_mem_range (I ^ (i + 1)) R]
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := (lTensor_exact R hj (Submodule.mkQ_surjective _)) z |>.mp hz
    exact ⟨w, (hcomp w).symm⟩
  · rintro ⟨w, hw⟩
    have h := idealTensor_injective (I ^ i) R ((hcomp w).trans hw)
    exact ((lTensor_exact R hj (Submodule.mkQ_surjective _)) z).mpr ⟨w, h⟩

private theorem principalUnitTensor_mul_error (I : Ideal A) (hI : IsNilpotent I)
    (R : TestAlgebra F) (x y : (principalUnits I).obj R) :
    idealTensor I R ((principalUnitTensorEquiv I hI R).symm (x * y) -
        ((principalUnitTensorEquiv I hI R).symm x + (principalUnitTensorEquiv I hI R).symm y)) =
      (x.val.val - 1) * (y.val.val - 1) := by
  simp only [map_sub, map_add, principalUnitTensorEquiv_symm_apply]
  change x.val.val * y.val.val - 1 - _ = _
  ring

private def powerQuotientMap (I : Ideal A) (hI : IsNilpotent I) (i : ℕ) (hi : 0 < i) :
    principalUnits (I ^ i) ⟶ vectorPoints (F := F) (powerQuotient (F := F) I i) where
  app R := GrpCat.ofHom (show (principalUnits (I ^ i)).obj R →*
      (vectorPoints (F := F) (powerQuotient (F := F) I i)).obj R from {
    toFun x := Multiplicative.ofAdd ((nextPower (F := F) I i).mkQ.lTensor R
      ((principalUnitTensorEquiv (I ^ i) (power_nilpotent I hI hi) R).symm x))
    map_one' := by
      have h := principalUnitTensorEquiv_symm_apply (I ^ i) (power_nilpotent I hI hi) R 1
      have h0 : (principalUnitTensorEquiv (I ^ i) (power_nilpotent I hI hi) R).symm 1 = 0 :=
        idealTensor_injective (I ^ i) R (by
          change _ = (1 : R ⊗[F] A) - 1 at h
          simpa using h)
      change (nextPower (F := F) I i).mkQ.lTensor R
        ((principalUnitTensorEquiv (I ^ i) (power_nilpotent I hI hi) R).symm 1) = 0
      rw [h0, map_zero]
    map_mul' x y := by
      apply Multiplicative.toAdd.injective
      change (nextPower (F := F) I i).mkQ.lTensor R
        ((principalUnitTensorEquiv (I ^ i) (power_nilpotent I hI hi) R).symm (x * y)) =
        (nextPower (F := F) I i).mkQ.lTensor R
          ((principalUnitTensorEquiv (I ^ i) (power_nilpotent I hI hi) R).symm x) +
        (nextPower (F := F) I i).mkQ.lTensor R
          ((principalUnitTensorEquiv (I ^ i) (power_nilpotent I hI hi) R).symm y)
      rw [← map_add, ← sub_eq_zero, ← map_sub, idealTensor_nextPower_range,
        principalUnitTensor_mul_error]
      have hx := (mem_principalUnitsAt (I ^ i) R x.val).mp x.property
      have hy := (mem_principalUnitsAt (I ^ i) R y.val).mp y.property
      have hm := Ideal.mul_mem_mul hx hy
      let f : A →+* R ⊗[F] A := (includeRight : A →ₐ[F] R ⊗[F] A).toRingHom
      change _ ∈ (I ^ i).map f * (I ^ i).map f at hm
      rw [← Ideal.map_mul, ← pow_add] at hm
      exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega : i + 1 ≤ i + i)) hm })
  naturality {R S} f := by
    apply GrpCat.ext
    intro x
    apply Multiplicative.toAdd.injective
    change (nextPower (F := F) I i).mkQ.lTensor S
      ((principalUnitTensorEquiv (I ^ i) (power_nilpotent I hI hi) S).symm
        ((principalUnits (I ^ i)).map f x)) =
      LinearMap.rTensor (powerQuotient (F := F) I i) f.hom.toLinearMap ((nextPower (F := F) I i).mkQ.lTensor R
        ((principalUnitTensorEquiv (I ^ i) (power_nilpotent I hI hi) R).symm x))
    rw [principalUnitTensorEquiv_symm_naturality]
    generalize (principalUnitTensorEquiv (I ^ i) (power_nilpotent I hI hi) R).symm x = z
    induction z using TensorProduct.inductionOn with
    | tmul r y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

theorem principalUnitsSuccessiveQuotients : PrincipalUnitsSuccessiveQuotients.{u} := by
  intro F A _ _ _ I hI i hi
  let e (R : TestAlgebra F) := principalUnitTensorEquiv (I ^ i) (power_nilpotent I hI hi) R
  refine ⟨powerQuotientMap I hI i hi, fun R ↦ ⟨?_, ?_, ?_⟩⟩
  · exact Multiplicative.ofAdd.surjective.comp
      ((LinearMap.lTensor_surjective R (Submodule.mkQ_surjective (nextPower (F := F) I i))).comp
        (e R).symm.surjective)
  · intro x
    change (nextPower (F := F) I i).mkQ.lTensor R ((e R).symm x) = 0 ↔ _
    rw [idealTensor_nextPower_range, principalUnitTensorEquiv_symm_apply]
  · intro x z hz
    have he : (e R).symm x = z := idealTensor_injective (I ^ i) R
      ((principalUnitTensorEquiv_symm_apply _ _ _ _).trans hz.symm)
    exact congrArg (fun v ↦ Multiplicative.ofAdd ((nextPower (F := F) I i).mkQ.lTensor R v)) he

end PrincipalUnits


section Representations

open private
  StandardGroups.Representation
  StandardGroups.Representation.mk
  StandardGroups.Representation.hopf
  StandardGroups.Representation.convolutionIso
  StandardGroups.spectrumPointsIso
  from LinearAlgebraicGroups.Affine.StandardGroups

variable {F V A : Type u} [Field F] [AddCommGroup V] [Module F V] [CommRing A] [Algebra F A]

private def tensorCoordinates {index : Type u} [Fintype index]
    (b : Module.Basis index F V) (R : TestAlgebra F) :
    (MvPolynomial index F →ₐ[F] R) ≃ R ⊗[F] V :=
  (show (MvPolynomial index F →ₐ[F] R) ≃ (index → R) from
    { toFun := fun f i ↦ f (MvPolynomial.X i)
      invFun := MvPolynomial.aeval
      left_inv := fun _ ↦ MvPolynomial.algHom_ext (MvPolynomial.aeval_X _)
      right_inv := fun _ ↦ funext (MvPolynomial.aeval_X _) }).trans
    (b.baseChange R).equivFun.symm.toEquiv

private theorem tensorCoordinates_apply {index : Type u} [Fintype index]
    (b : Module.Basis index F V) (R : TestAlgebra F) (f : MvPolynomial index F →ₐ[F] R) :
    tensorCoordinates b R f = ∑ i, f (MvPolynomial.X i) ⊗ₜ[F] b i := by
  change (b.baseChange R).equivFun.symm (fun i ↦ f (MvPolynomial.X i)) = _
  simp only [Module.Basis.equivFun_symm_apply, Module.Basis.baseChange_apply,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem tensorCoordinates_naturality {index : Type u} [Fintype index]
    (b : Module.Basis index F V) {R S : TestAlgebra F} (f : R ⟶ S)
    (p : MvPolynomial index F →ₐ[F] R) :
    tensorCoordinates b S (f.hom.comp p) =
      LinearMap.rTensor V f.hom.toLinearMap (tensorCoordinates b R p) := by
  simp only [tensorCoordinates_apply, AlgHom.comp_apply, map_sum, LinearMap.rTensor_tmul]
  rfl

private abbrev PrincipalCoordinates [Module.Finite F A] (I : Ideal A) :=
  MvPolynomial (Module.Free.ChooseBasisIndex F I) F

private def principalRepresentation [Module.Finite F A] (I : Ideal A) (hI : IsNilpotent I) :
    StandardGroups.Representation (PrincipalCoordinates (F := F) I) (principalUnits (F := F) I) :=
  StandardGroups.Representation.mk
    (fun R ↦ (tensorCoordinates (Module.Free.chooseBasis F I) R).trans (principalUnitTensorEquiv I hI R))
    (by
      intro R S f p
      change principalUnitOfTensor I hI S (tensorCoordinates (Module.Free.chooseBasis F I) S
        (f.hom.comp p)) = (principalUnits I).map f
          (principalUnitOfTensor I hI R (tensorCoordinates (Module.Free.chooseBasis F I) R p))
      rw [tensorCoordinates_naturality, principalUnitOfTensor_naturality])

private def principalUnitGroup [Module.Finite F A] (I : Ideal A) (hI : IsNilpotent I) :
    AffineAlgebraicGroup F :=
  letI := StandardGroups.Representation.hopf (principalRepresentation (F := F) I hI)
  Specs.StandardGroups.spectrum F (PrincipalCoordinates (F := F) I)

private def principalUnitGroupPoints [Module.Finite F A] (I : Ideal A) (hI : IsNilpotent I) :
    (groupPointsFunctor F).obj (principalUnitGroup (F := F) I hI).val ≅ principalUnits I :=
  letI := StandardGroups.Representation.hopf (principalRepresentation (F := F) I hI)
  StandardGroups.spectrumPointsIso
    (StandardGroups.Representation.convolutionIso (principalRepresentation (F := F) I hI))

theorem principalUnitsRepresentable : PrincipalUnitsRepresentable.{u} := by
  intro F A _ _ _ _ I hI
  exact ⟨principalUnitGroup I hI, ⟨principalUnitGroupPoints I hI⟩⟩

private def vectorRepresentation {index : Type u} [Fintype index] (b : Module.Basis index F V) :
    StandardGroups.Representation (MvPolynomial index F) (vectorPoints (F := F) V) :=
  StandardGroups.Representation.mk
    (fun R ↦ (tensorCoordinates b R).trans Multiplicative.ofAdd)
    (fun f p ↦ congrArg Multiplicative.ofAdd (tensorCoordinates_naturality b f p))

theorem vectorGroupsRepresentable : VectorGroupsRepresentable.{u} := by
  intro F V _ _ _ _
  let b := Module.Free.chooseBasis F V
  let P := vectorRepresentation b
  let := StandardGroups.Representation.hopf P
  exact ⟨Specs.StandardGroups.spectrum F (MvPolynomial (Module.Free.ChooseBasisIndex F V) F),
    ⟨StandardGroups.spectrumPointsIso (StandardGroups.Representation.convolutionIso P)⟩⟩

end Representations


section Unipotence

open Specs.Unipotent (HasInvariantVectors IsUnipotent)
open RationalRepresentations (coefficients evaluate tensorCoordinate coaction_apply_basis
  coefficients_isCoactionMatrix matrixPointHom)
open private StandardGroups.Representation.hopf StandardGroups.Representation.convolutionIso
  from LinearAlgebraicGroups.Affine.StandardGroups
open private invariant_iff_coaction from LinearAlgebraicGroups.Unipotent.Criteria
open private tensorCoordinate_evaluation from LinearAlgebraicGroups.Affine.RationalRepresentations

variable {F A V : Type u} [Field F] [CommRing A] [Algebra F A]

/-- A commuting family of unipotent linear operators has a common nonzero fixed vector. -/
private theorem exists_fixed_of_commuting_nilpotent_differences
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
    {index : Type u} (f : index → Module.End F V)
    (hc : ∀ a b, Commute (f a) (f b)) (hn : ∀ a, IsNilpotent (f a - 1)) :
    ∃ v : V, v ≠ 0 ∧ ∀ a, f a v = v := by
  let P (W : Submodule F V) : Prop := W ≠ ⊥ ∧ ∀ a x, x ∈ W → f a x ∈ W
  obtain ⟨W, hW⟩ := exists_minimalFor_of_wellFoundedLT P (fun W ↦ Module.finrank F W)
    ⟨⊤, top_ne_bot, fun _ _ _ ↦ Submodule.mem_top⟩
  have hfix (a : index) : ∀ v ∈ W, f a v = v := by
    let d := f a - 1
    let E := W ⊓ LinearMap.ker d
    have hd (v : V) (hv : v ∈ W) : d v ∈ W := W.sub_mem (hW.prop.2 a v hv) hv
    have hE : P E := by
      constructor
      · intro hbot
        have hzero {v : V} (hv : v ∈ W) (hz : d v = 0) : v = 0 :=
          (Submodule.eq_bot_iff _).mp hbot v ⟨hv, LinearMap.mem_ker.mpr hz⟩
        have hvanish (n : ℕ) (v : V) (hv : v ∈ W) (hz : (d ^ n) v = 0) : v = 0 := by
          induction n generalizing v with
          | zero => simpa only [pow_zero, Module.End.one_apply] using hz
          | succ n ih =>
            rw [pow_succ, Module.End.mul_apply] at hz
            exact hzero hv (ih (d v) (hd v hv) hz)
        obtain ⟨n, hn⟩ := hn a
        change d ^ n = 0 at hn
        exact hW.prop.1 ((Submodule.eq_bot_iff _).mpr fun v hv ↦ hvanish n v hv (by rw [hn]; rfl))
      · intro b v hv
        have hv' : d v = 0 := LinearMap.mem_ker.mp hv.2
        have hdb : Commute d (f b) := (hc a b).sub_left (Commute.one_left _)
        have h := DFunLike.congr_fun hdb.eq v
        simp only [Module.End.mul_apply, hv', map_zero] at h
        exact ⟨hW.prop.2 b v hv.1, LinearMap.mem_ker.mpr h⟩
    have he : E = W := Submodule.eq_of_le_of_finrank_le inf_le_left (hW.le hE)
    intro v hv
    have hv' : v ∈ E := he ▸ hv
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp hv'.2)
  obtain ⟨v, hv, hne⟩ := W.ne_bot_iff.mp hW.prop.1
  exact ⟨v, hne, fun a ↦ hfix a v hv⟩

private theorem principalUnits_boundedExponent (I : Ideal A) (hI : IsNilpotent I)
    (p : ℕ) [ExpChar F p] (hp : 1 < p) [Nontrivial A] :
    ∃ m : ℕ, ∀ x : (principalUnits I).obj (CommAlgCat.of F F), x ^ p ^ m = 1 := by
  let R : TestAlgebra F := CommAlgCat.of F F
  have : ExpChar (R ⊗[F] A) p :=
    expChar_of_injective_algebraMap (algebraMap F (R ⊗[F] A)).injective p
  obtain ⟨n, hn⟩ := extendedIdeal_nilpotent I hI R
  change extendedPrincipalIdeal I R ^ n = ⊥ at hn
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt n hp
  refine ⟨m, fun x ↦ Subtype.ext (Units.ext ?_)⟩
  change (x.val.val : R ⊗[F] A) ^ (p ^ m) = 1
  have hx := (mem_principalUnitsAt I R _).mp x.property
  have hz := Ideal.pow_mem_pow hx (p ^ m)
  have he : extendedPrincipalIdeal I R ^ (p ^ m) = ⊥ :=
    eq_bot_iff.mpr ((Ideal.pow_le_pow_right hm.le).trans_eq hn)
  rw [he, Ideal.mem_bot, sub_pow_expChar_pow, one_pow, sub_eq_zero] at hz
  exact hz

private theorem invariant_of_groundField_points [AddCommGroup V] [Module F V]
    (C : HopfAlgebraCategory F) (ρ : RightComodule F C V) (v : V)
    (hsep : ∀ a b : C, (∀ g : C →ₐ[F] F, g a = g b) → a = b)
    (hfix : ∀ a : C →ₐ[F] F, TensorProduct.rid F V (evaluate C ρ a v) = v) :
    v ∈ RationalRepresentations.invariants C ρ := by
  let b := Module.Free.chooseBasis F V
  apply (invariant_iff_coaction C ρ v).mpr
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  simp only [TensorProduct.equivFinsuppOfBasisLeft_apply]
  change tensorCoordinate b i (ρ.coaction v) = tensorCoordinate b i (v ⊗ₜ[F] (1 : C))
  apply hsep
  intro a
  have he : a.toLinearMap.lTensor V (ρ.coaction v) = v ⊗ₜ[F] (1 : F) := by
    apply (TensorProduct.rid F V).injective
    simpa [evaluate] using hfix a
  change a.toLinearMap (tensorCoordinate b i (ρ.coaction v)) =
    a.toLinearMap (tensorCoordinate b i (v ⊗ₜ[F] (1 : C)))
  rw [← tensorCoordinate_evaluation, ← tensorCoordinate_evaluation, he]
  simp

private theorem principalUnitGroup_unipotent [IsAlgClosed F] [Module.Finite F A] [Nontrivial A]
    (I : Ideal A) (hI : IsNilpotent I) (p : ℕ) [ExpChar F p] (hp : 1 < p) :
    IsUnipotent (principalUnitGroup (F := F) I hI) := by
  classical
  let P := principalRepresentation (F := F) I hI
  let := StandardGroups.Representation.hopf P
  let C := CommHopfAlgCat.of F (PrincipalCoordinates (F := F) I)
  refine ⟨C, ⟨Iso.refl _⟩, ?_⟩
  intro V _ _ _ _ ρ
  let R := CommAlgCat.of F F
  let b := Module.Free.chooseBasis F V
  let action := matrixPointHom C (coefficients C b ρ) (coefficients_isCoactionMatrix C b ρ)
  let f : (convolutionPoints C).obj R →* Module.End F V :=
    (Matrix.toLinAlgEquiv b).toAlgHom.toMonoidHom.comp
      ((Units.coeHom _).comp (action.app R).hom)
  let e := (StandardGroups.Representation.convolutionIso P).app R |>.groupIsoToMulEquiv
  have hcomm (a b : (convolutionPoints C).obj R) : Commute (f a) (f b) := by
    change f a * f b = f b * f a
    rw [← map_mul, ← map_mul]
    apply congrArg f
    apply e.injective
    rw [map_mul, map_mul]
    exact Subtype.ext (mul_comm _ _)
  obtain ⟨m, hm⟩ := principalUnits_boundedExponent (F := F) I hI p hp
  have : ExpChar (Module.End F V) p :=
    expChar_of_injective_algebraMap (algebraMap F (Module.End F V)).injective p
  have hnil (a : (convolutionPoints C).obj R) : IsNilpotent (f a - 1) := by
    have ha : a ^ (p ^ m) = 1 := e.injective (by rw [map_pow, map_one]; exact hm (e a))
    exact ⟨p ^ m, by rw [sub_pow_expChar_pow_of_commute p m (Commute.one_right (f a)), one_pow,
      ← map_pow, ha, map_one, sub_self]⟩
  obtain ⟨v, hv, hfix⟩ := exists_fixed_of_commuting_nilpotent_differences f hcomm hnil
  have hf (a : (convolutionPoints C).obj R) :
      f a = (TensorProduct.rid F V).toLinearMap.comp (evaluate C ρ a.ofConv) := by
    apply b.ext
    intro j
    change (Matrix.toLinAlgEquiv b) (a.ofConv.mapMatrix (coefficients C b ρ)) (b j) =
      TensorProduct.rid F V (evaluate C ρ a.ofConv (b j))
    rw [Matrix.toLinAlgEquiv_self, evaluate, LinearMap.comp_apply, coaction_apply_basis C b]
    simp [AlgHom.mapMatrix_apply]
  refine ⟨v, hv, invariant_of_groundField_points C ρ v ?_ ?_⟩
  · intro x y h
    exact MvPolynomial.funext (fun t ↦ h (MvPolynomial.aeval t))
  · intro a
    exact (DFunLike.congr_fun (hf (toConv a)) v).symm.trans (hfix (toConv a))

end Unipotence


section GroundField

open Specs.CharacterDescent (multiplicativeTypeSpecFunctor)
open Specs.DiagonalizableGroups (IntegerCharacters FGAbelianGroup groupAlgebra)
open Specs.GeometricRadicals (identitySubgroup)
open private multiplicativeType_iff_coordinates from LinearAlgebraicGroups.Unipotent.Orthogonality
open private identity_smoothConnectedNormal identity_unipotent
  from LinearAlgebraicGroups.Reductive.GeometricRadicals

variable {k : Type u} [Field k]

private theorem multiplicativeGroup_of_multiplicativeType :
    (multiplicativeTypeSpecFunctor k).essImage (StandardGroups.multiplicativeGroup k) := by
  let M : FGAbelianGroup.{u} := ⟨CommGrpCat.of IntegerCharacters.{u}, inferInstance⟩
  exact (multiplicativeType_iff_coordinates (DiagonalizableGroups.multiplicativeGroupIso k)).mpr
    ⟨k, inferInstance, inferInstance, inferInstance, M,
      ⟨CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange k k M.obj).symm⟩⟩

private theorem map_zero_app {G H : GroupScheme k} (R : TestAlgebra k)
    (x : ((groupPointsFunctor k).obj G).obj R) :
    ((groupPointsFunctor k).map (0 : G ⟶ H)).app R x = 1 := by
  change x ≫ (toUnit G.X ≫ η[H.X]) = toUnit _ ≫ η[H.X]
  rw [← Category.assoc, comp_toUnit]

private theorem trivial_of_inclusion_zero {G : GroupScheme k} (N : ClosedSubgroup G)
    (h : N.inclusion = 0) : IsTrivialSubgroup N := by
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have : IsClosedImmersion (F.map N.inclusion) := N.isClosedImmersion
  have : Mono N.inclusion := F.mono_of_mono_map inferInstance
  have hz : 𝟙 N.group = 0 :=
    (cancel_mono N.inclusion).mp (by rw [Category.id_comp, zero_comp, h])
  exact ⟨((IsZero.iff_id_eq_zero _).mpr hz).iso (Grp.isZero_trivial _)⟩

theorem groundFieldUnipotentSubgroups : GroundFieldUnipotentSubgroups.{u} := by
  intro k K _ _ _ _ G h U hU
  obtain ⟨g⟩ := h
  let V := closedSubgroupAlgebraicGroup U
  let W := baseChangedAlgebraicGroup K V
  let T := StandardGroups.multiplicativeGroup K
  let t := StandardGroups.multiplicativeGroupPointsIso K
  let a := (groupPointsFunctor k).map U.inclusion ≫ g.hom
  let e := baseChangePointIso K U.group
  let b := e.hom ≫ Functor.whiskerLeft (restrictTestAlgebra k K) a ≫ evalUnits k K ≫ t.inv
  let χ := fromPoints W T b
  have hχ : χ = 0 := Unipotent.homFromUnipotentToMultiplicativeType W T χ
    ((Unipotent.unipotenceFieldExtension V).mpr hU) multiplicativeGroup_of_multiplicativeType
  have hb : b = (groupPointsFunctor K).map (0 : W.val ⟶ T.val) := by
    rw [← hχ]
    exact (map_fromPoints W T b).symm
  have heval (R : TestAlgebra K)
      (x : ((groupPointsFunctor k).obj U.group).obj ((restrictTestAlgebra k K).obj R)) :
      (evalUnits k K).app R (a.app _ x) = 1 := by
    let y := e.inv.app R x
    have hx : e.hom.app R y = x := (e.app R).groupIsoToMulEquiv.apply_symm_apply x
    calc
      _ = t.hom.app R (b.app R y) := by
        change _ = t.hom.app R (t.inv.app R ((evalUnits k K).app R
          (a.app _ (e.hom.app R y))))
        rw [hx]
        exact ((t.app R).groupIsoToMulEquiv.apply_symm_apply _).symm
      _ = 1 := by
        rw [hb]
        have h := map_zero_app (G := W.val) (H := T.val) R y
        exact (congrArg (fun z : ((groupPointsFunctor K).obj T.val).obj R ↦
          t.hom.app R z) h).trans (map_one (t.hom.app R).hom)
  have ha := eval_detects a heval
  apply trivial_of_inclusion_zero U
  apply (AffineAlgebraicGroup.groupHomEquiv V G).injective
  change (groupPointsFunctor k).map U.inclusion = (groupPointsFunctor k).map 0
  ext R x
  apply (g.app R).groupIsoToMulEquiv.injective
  rw [map_zero_app, map_one]
  exact ha R x

theorem groundFieldRadical : GroundFieldRadical.{u} := by
  intro k K _ _ _ _ G g
  refine ⟨identity_smoothConnectedNormal G, identity_unipotent G, ?_⟩
  intro H _ hH
  obtain ⟨e⟩ := groundFieldUnipotentSubgroups G g H hH
  refine ⟨e.hom, ?_⟩
  have hz := (Grp.isZero_trivial (SchemeOver k)).of_iso e
  exact hz.eq_of_src _ _

end GroundField


section GeometricSequence

open _root_.LinearAlgebraicGroups.Specs (IsSchemeKernel)

open WeilRestriction (tensorCancellation)
open Specs.GeometricRadicals (GeometricGroup geometricUnipotentRadical IsSmoothConnectedNormal
  IsUnipotentRadical)
open Specs.Unipotent (IsUnipotent)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open private scalarTensorComparison scalarTensorComparison_natural
  from LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
open private schemeKernel_exists schemeKernel_sections isMonHom_of_comp_closed
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient

private def changedUnitsIso (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] :
    extendedUnits L (L ⊗[k] K) ≅ restrictTestAlgebra k L ⋙ extendedUnits k K :=
  NatIso.ofComponents
    (fun R ↦ (Units.mapEquiv (tensorCancellation k K L R).toMulEquiv).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro x
      apply Units.ext
      exact scalarTensorComparison_natural f x.val)

variable {F A : Type u} [Field F] [CommRing A] [Algebra F A]

@[simp] private theorem residueAt_tmul (r : A →ₐ[F] F) (R : TestAlgebra F) (x : R) (y : A) :
    residueAt r R (x ⊗ₜ[F] y) = x * algebraMap F R (r y) := by
  change TensorProduct.rid F R (x ⊗ₜ[F] r y) = _
  simp [Algebra.smul_def, mul_comm]

private def reduction (r : A →ₐ[F] F) : extendedUnits F A ⟶ multiplicativePoints F where
  app R := GrpCat.ofHom (Units.map (residueAt r R).toMonoidHom)
  naturality {R S} f := by
    apply GrpCat.ext
    intro x
    apply Units.ext
    change residueAt r S (tensorMap F A f.hom x.val) = f.hom (residueAt r R x.val)
    induction x.val using TensorProduct.inductionOn with
    | tmul x y => rw [tensorMap_tmul, residueAt_tmul, residueAt_tmul, map_mul, f.hom.commutes]
    | add x y hx hy => simp only [map_add, hx, hy]

private def scalarSection (F A : Type u) [Field F] [CommRing A] [Algebra F A] :
    multiplicativePoints F ⟶ extendedUnits F A where
  app R := GrpCat.ofHom (Units.map (includeLeft : R →ₐ[F] R ⊗[F] A).toMonoidHom)
  naturality {R S} f := by
    apply GrpCat.ext
    intro x
    apply Units.ext
    rfl

private theorem scalarSection_reduction (r : A →ₐ[F] F) :
    scalarSection F A ≫ reduction r = 𝟙 (multiplicativePoints F) := by
  ext R x
  apply Units.ext
  change residueAt r R (x.val ⊗ₜ[F] (1 : A)) = x.val
  rw [residueAt_tmul, map_one, map_one, mul_one]

private theorem reduction_eq_one (r : A →ₐ[F] F) (hr : Function.Surjective r)
    (R : TestAlgebra F) (x : (R ⊗[F] A)ˣ) :
    (reduction r).app R x = 1 ↔ x ∈ principalUnitsAt (RingHom.ker r.toRingHom) R := by
  have hker : RingHom.ker (residueAt r R).toRingHom =
      extendedPrincipalIdeal (RingHom.ker r.toRingHom) R := by
    change RingHom.ker ((Algebra.TensorProduct.rid F R R).toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id F R) r).toRingHom) = _
    exact (RingHom.ker_comp_of_injective (Algebra.TensorProduct.map (AlgHom.id F R) r).toRingHom
      (f := (Algebra.TensorProduct.rid F R R).toRingEquiv.toRingHom)
      (Algebra.TensorProduct.rid F R R).injective).trans
        (Algebra.TensorProduct.lTensor_ker (A := R) r hr)
  rw [mem_principalUnitsAt, ← hker]
  change (reduction r).app R x = 1 ↔ residueAt r R (x.val - 1) = 0
  rw [Units.ext_iff]
  change residueAt r R x.val = 1 ↔ _
  rw [map_sub, map_one, sub_eq_zero]

private def kernelPrincipalPoints {G T : AffineAlgebraicGroup F} {p : G.val ⟶ T.val}
    (N : ClosedSubgroup G.val) (hN : IsSchemeKernel p N) (r : A →ₐ[F] F)
    (hr : Function.Surjective r)
    (a : (groupPointsFunctor F).obj G.val ≅ extendedUnits F A)
    (t : (groupPointsFunctor F).obj T.val ≅ multiplicativePoints F)
    (hp : (groupPointsFunctor F).map p ≫ t.hom = a.hom ≫ reduction r) :
    (groupPointsFunctor F).obj N.group ≅ principalUnits (RingHom.ker r.toRingHom) := by
  let b := (groupPointsFunctor F).map N.inclusion ≫ a.hom
  have hmem (R : TestAlgebra F) (x : ((groupPointsFunctor F).obj G.val).obj R) :
      a.hom.app R x ∈ principalUnitsAt (RingHom.ker r.toRingHom) R ↔
        ((groupPointsFunctor F).map p).app R x = 1 := by
    rw [← reduction_eq_one r hr]
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hp R) x
    change t.hom.app R (((groupPointsFunctor F).map p).app R x) =
      (reduction r).app R (a.hom.app R x) at h
    rw [← h, ← map_one (t.hom.app R).hom]
    exact (t.app R).groupIsoToMulEquiv.injective.eq_iff
  let c (R : TestAlgebra F) : ((groupPointsFunctor F).obj N.group).obj R →*
      (principalUnits (RingHom.ker r.toRingHom)).obj R :=
    (b.app R).hom.codRestrict _ (fun x ↦
      (hmem R _).mpr ((schemeKernel_sections hN _).mp ⟨x, rfl⟩))
  have hbij (R : TestAlgebra F) : Function.Bijective (c R) := by
    constructor
    · intro x y h
      have : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
      have : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
      apply (cancel_mono N.inclusion.hom.hom).mp
      apply (a.app R).groupIsoToMulEquiv.injective
      exact congrArg Subtype.val h
    · intro z
      let x := a.inv.app R z.val
      have hx : a.hom.app R x = z.val := (a.app R).groupIsoToMulEquiv.apply_symm_apply z.val
      have hx' : a.hom.app R x ∈ principalUnitsAt (RingHom.ker r.toRingHom) R := hx ▸ z.property
      obtain ⟨y, hy⟩ := (schemeKernel_sections hN x).mpr ((hmem R x).mp hx')
      exact ⟨y, Subtype.ext ((congrArg (fun x ↦ a.hom.app R x) hy).trans hx)⟩
  refine NatIso.ofComponents (fun R ↦ (MulEquiv.ofBijective (c R) (hbij R)).toGrpIso) ?_
  intro R S f
  apply GrpCat.ext
  intro z
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (b.naturality f) z

private theorem normal_of_kernel {G T : GroupScheme F} {p : G ⟶ T} {N : ClosedSubgroup G}
    (hN : IsSchemeKernel p N) : IsNormalSubgroup N.inclusion := by
  apply (schemeKernel_sections hN _).mpr
  have h : N.inclusion.hom.hom ≫ p.hom.hom = 1 := hN.w
  rw [Specs.subgroupConjugation, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
    Category.assoc, h, MonObj.comp_one, mul_one, mul_inv_cancel]

private theorem subgroup_of_kernel {G T : GroupScheme F} {p : G ⟶ T} {N : ClosedSubgroup G}
    (hN : IsSchemeKernel p N) (U : ClosedSubgroup G) (hU : U.inclusion ≫ p = 0) :
    IsSubgroupOf U N := by
  have h : U.inclusion.hom.hom ≫ p.hom.hom = 1 :=
    congrArg (fun g : U.group ⟶ T ↦ g.hom.hom) hU
  obtain ⟨j, hj⟩ := (schemeKernel_sections hN U.inclusion.hom.hom).mpr h
  have : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  have := isMonHom_of_comp_closed j U.inclusion N.inclusion hj
  exact ⟨Grp.homMk j, Grp.hom_ext _ _ hj⟩

private theorem principalGeometry [Module.Finite F A] (I : Ideal A) (hI : IsNilpotent I) :
    Smooth (principalUnitGroup (F := F) I hI).val.X.hom ∧
      ConnectedSpace (principalUnitGroup (F := F) I hI).val.X.left := by
  constructor
  · change Smooth (Spec.map (CommRingCat.ofHom (algebraMap F (PrincipalCoordinates (F := F) I))))
    change Smooth (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : F →+* PrincipalCoordinates (F := F) I)))
    rw [← AffineSpace.SpecIso_inv_over (n := Module.Free.ChooseBasisIndex F I) (CommRingCat.of F)]
    infer_instance
  · change ConnectedSpace (Spec (CommRingCat.of (PrincipalCoordinates (F := F) I)))
    infer_instance

private theorem nontrivial_of_principalPoints {G : GroupScheme F} (N : ClosedSubgroup G)
    (I : Ideal A) (hI : IsNilpotent I) (hne : I ≠ ⊥)
    (n : (groupPointsFunctor F).obj N.group ≅ principalUnits I) :
    ¬ IsTrivialSubgroup N := by
  rintro ⟨e⟩
  let R := CommAlgCat.of F F
  have hs : Subsingleton (((groupPointsFunctor F).obj (Grp.trivial (SchemeOver F))).obj R) :=
    ⟨(isTerminalTensorUnit (C := SchemeOver F)).hom_ext⟩
  let d := ((groupPointsFunctor F).mapIso e).app R |>.groupIsoToMulEquiv
  have h : Subsingleton ((principalUnits I).obj R) :=
    ((n.app R).groupIsoToMulEquiv.symm.trans d).injective.subsingleton
  have h' : Subsingleton (F ⊗[F] I) := (principalUnitTensorEquiv I hI R).injective.subsingleton
  have h'' : Subsingleton I := (TensorProduct.lid F I).symm.injective.subsingleton
  exact hne ((Submodule.eq_bot_iff (I : Submodule A A)).mpr fun x hx ↦ congrArg Subtype.val
    (Subsingleton.elim (⟨x, hx⟩ : I) 0))


/-- The geometric radical is the kernel of reduction to the residue field. -/
theorem geometricUnitSequence : GeometricUnitSequence.{u} := by
  intro k K _ _ _ _ _ hproper G g
  classical
  let L := AlgebraicClosure k
  let e : K →ₐ[k] L := IsAlgClosed.lift
  refine ⟨e, ?_⟩
  let A := L ⊗[k] K
  let r : A →ₐ[L] L := residue e
  let J := RingHom.ker r.toRingHom
  let H := GeometricGroup G
  let T := StandardGroups.multiplicativeGroup L
  let t := StandardGroups.multiplicativeGroupPointsIso L
  let c := changedUnitsIso k K L
  let b := baseChangePointIso L G.val ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra k L) g
  let a : (groupPointsFunctor L).obj H.val ≅ extendedUnits L A := b ≪≫ c.symm
  let p := fromPoints H T (a.hom ≫ reduction r ≫ t.inv)
  let s := fromPoints T H (t.hom ≫ scalarSection L A ≫ a.inv)
  have hp : (groupPointsFunctor L).map p ≫ t.hom = a.hom ≫ reduction r := by
    dsimp only [p]
    rw [map_fromPoints]
    simp
  have hs : (groupPointsFunctor L).map s ≫ a.hom = t.hom ≫ scalarSection L A := by
    dsimp only [s]
    rw [map_fromPoints]
    simp
  have hsplit : s ≫ p = 𝟙 T.val := by
    apply (T.groupHomEquiv T).injective
    change (groupPointsFunctor L).map (s ≫ p) = (groupPointsFunctor L).map (𝟙 T.val)
    rw [(groupPointsFunctor L).map_comp, (groupPointsFunctor L).map_id]
    have hp' : (groupPointsFunctor L).map p = a.hom ≫ reduction r ≫ t.inv :=
      map_fromPoints H T _
    calc
      _ = ((groupPointsFunctor L).map s ≫ a.hom) ≫ (reduction r ≫ t.inv) := by
        rw [hp']
        simp only [Category.assoc]
      _ = _ := by
        rw [hs]
        simp only [Category.assoc, reassoc_of% (scalarSection_reduction r),
          Iso.hom_inv_id]
  obtain ⟨_, _, hJ, hnil, hr, _⟩ := localTensorAlgebra hproper e
  have : IsAffine T.val.X.left := T.property.1
  obtain ⟨P, hP⟩ := schemeKernel_exists p
  let f := kernelPrincipalPoints P hP r hr a t hp
  let U := closedSubgroupAlgebraicGroup (G := H) P
  let W := principalUnitGroup (F := L) J hnil
  let d := representedGroupIso (G := U) (H := W) f (principalUnitGroupPoints J hnil)
  let D := Grp.forget (SchemeOver L) ⋙ Over.forget (Spec (CommRingCat.of L))
  let d' := D.mapIso d
  obtain ⟨hWsm, hWc⟩ := principalGeometry (F := L) J hnil
  have hPsm : Smooth P.group.X.hom := by
    have he : d'.hom ≫ W.val.X.hom = P.group.X.hom := d.hom.hom.hom.w
    rw [← he]
    infer_instance
  have hPc : ConnectedSpace P.group.X.left := by
    have : ConnectedSpace (D.obj W.val : Scheme) := hWc
    let e := Scheme.homeoOfIso d'.symm
    exact e.surjective.connectedSpace e.continuous
  obtain ⟨q, hq⟩ := ExpChar.exists k
  let : ExpChar k q := hq
  have hqgt : 1 < q := by
    rcases expChar_is_prime_or_one k q with h | h
    · exact h.one_lt
    · exfalso
      apply hproper
      intro x
      obtain ⟨m, y, hy⟩ := IsPurelyInseparable.pow_mem k q x
      exact ⟨y, by simpa [h] using hy⟩
  let : ExpChar L q := expChar_of_injective_algebraMap (algebraMap k L).injective q
  have hPu : IsUnipotent U := by
    obtain ⟨C, ⟨v⟩, hv⟩ := principalUnitGroup_unipotent (F := L) J hnil q hqgt
    exact ⟨C, ⟨v ≪≫ d.symm⟩, hv⟩
  have hRad : IsUnipotentRadical H P := by
    refine ⟨⟨hPsm, hPc, normal_of_kernel hP⟩, hPu, ?_⟩
    intro M _ hM
    apply subgroup_of_kernel hP M
    exact Unipotent.homFromUnipotentToMultiplicativeType
      (closedSubgroupAlgebraicGroup (G := H) M) T (M.inclusion ≫ p)
      hM multiplicativeGroup_of_multiplicativeType
  let N := geometricUnipotentRadical G
  obtain ⟨j, hj, _⟩ := GeometricRadicals.radicalUnique H IsUnipotent
    (GeometricRadicals.geometricUnipotentRadicalLargest G) hRad
  have hj' : j.inv ≫ N.inclusion = P.inclusion := by rw [← hj, Iso.inv_hom_id_assoc]
  have hN : IsSchemeKernel p N := by
    refine hP.of_iso ((Grp.forget (SchemeOver L)).mapIso j.symm)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_
      ((isTerminalTensorUnit (C := SchemeOver L)).hom_ext _ _) ?_ ?_
    · change P.inclusion.hom.hom ≫ 𝟙 H.val.X = j.inv.hom.hom ≫ N.inclusion.hom.hom
      rw [Category.comp_id]
      exact (congrArg (fun f : P.group ⟶ H.val ↦ f.hom.hom) hj').symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  let n := kernelPrincipalPoints N hN r hr a t hp
  refine ⟨a, T, t, p, s, n, hN, hsplit, nontrivial_of_principalPoints N J hnil hJ n, ?_⟩
  intro R
  refine ⟨?_, ?_, ?_, fun x ↦ rfl⟩
  · intro x
    have h : c.hom.app R (a.hom.app R x) = b.hom.app R x :=
      (c.app R).groupIsoToMulEquiv.apply_symm_apply (b.hom.app R x)
    exact congrArg (fun x : (((restrictTestAlgebra k L).obj R) ⊗[k] K)ˣ ↦ x.val) h
  · intro x
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hp R) x
    exact congrArg (fun x : Rˣ ↦ x.val) h
  · intro x
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hs R) x
    exact congrArg (fun x : (R ⊗[L] A)ˣ ↦ x.val) h

end GeometricSequence

end
end LinearAlgebraicGroups.WeilRestrictionBoundary
