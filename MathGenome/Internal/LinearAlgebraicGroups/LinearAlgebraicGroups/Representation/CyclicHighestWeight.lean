import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.CyclicHighestWeight
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelPositivity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelPositivity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

universe u

namespace LinearAlgebraicGroups.Representation.CyclicHighestWeight

open LinearAlgebraicGroups.Specs Specs.CyclicHighestWeight Specs.RootWeightAction
open Specs.AbstractPairing (Datum Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (IsPositiveSystem subgroupRoots)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.GeometricRadicals (IsSplitTorus IsUnipotentRadical)
open Specs.OrderedRootProducts (RootSubgroupFamily product rootProduct)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

open private contractRight contractRight_tmul map_contractRight coaction_contractRight
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ComoduleFiniteness
open private pointMatrix pointMatrix_evaluation pointMatrix_isCoactionMatrix tensorCoordinate_sum_basis tensorCoordinate_evaluation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

noncomputable section

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable {G : AffineAlgebraicGroup k}

private theorem orbitSpan_le {ρ : Representation G.val I} {X : SchemeOver k}
    {f : X ⟶ G.val.X} {v : I → k} {W : Submodule k (I → k)} :
    orbitSpan ρ f v ≤ W ↔
      ∀ (R : TestAlgebra k) (x : Points X R) (ℓ : R →ₗ[k] k),
        (fun i ↦ ℓ (act ρ R (x ≫ f) (extendVector R v) i)) ∈ W := by
  simp only [orbitSpan, iSup_le_iff, Submodule.span_le, Set.range_subset_iff]
  rfl

private theorem orbitSpan_comp_le (ρ : Representation G.val I) {X Y : SchemeOver k}
    (a : X ⟶ Y) (b : Y ⟶ G.val.X) (v : I → k) :
    orbitSpan ρ (a ≫ b) v ≤ orbitSpan ρ b v := by
  apply orbitSpan_le.mpr
  intro R x ℓ
  simpa only [Category.assoc] using
    (orbitSpan_le.mp (le_refl (orbitSpan ρ b v)) R (x ≫ a) ℓ)

private theorem act_mul (ρ : Representation G.val I)
    (R : TestAlgebra k) (g h : GroupPoints G.val R) (v : I → R) :
    act ρ R (g * h) v = act ρ R g (act ρ R h v) := by
  unfold act
  rw [show ρ.app R (g * h) = ρ.app R g * ρ.app R h from (ρ.app R).hom.map_mul g h]
  exact (Matrix.mulVec_mulVec v _ _).symm

private theorem act_one (ρ : Representation G.val I)
    (R : TestAlgebra k) (v : I → R) : act ρ R 1 v = v := by
  unfold act
  rw [show ρ.app R 1 = 1 from (ρ.app R).hom.map_one]
  exact Matrix.one_mulVec v

private theorem act_smul (ρ : Representation G.val I)
    (R : TestAlgebra k) (g : GroupPoints G.val R) (r : R) (w : I → R) :
    act ρ R g (r • w) = r • act ρ R g w :=
  (actLinear ρ R g).map_smul r w

private theorem act_natural (ρ : Representation G.val I) {R S : TestAlgebra k}
    (b : R ⟶ S) (g : GroupPoints G.val R) (v : I → k) (i : I) :
    act ρ S (mapPoints b g) (extendVector S v) i =
      b.hom (act ρ R g (extendVector R v) i) := by
  have hm := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ρ.naturality b)) g
  have hx : (ρ.app S (mapPoints b g)).val = b.hom.mapMatrix (ρ.app R g).val :=
    congrArg Units.val hm
  have hv : b.hom ∘ extendVector R v = extendVector S v :=
    funext fun i ↦ b.hom.commutes (v i)
  unfold act
  rw [hx, ← hv]
  exact (RingHom.map_mulVec b.hom.toRingHom _ _ i).symm

omit [Fintype I] [DecidableEq I] in
private theorem coactionSpan_minimal {A : HopfAlgebraCategory k}
    (δ : RightComodule k A (I → k)) (v : I → k) :
    v ∈ coactionSpan δ v ∧ δ.IsSubcomodule (coactionSpan δ v) ∧
      ∀ M : Submodule k (I → k), δ.IsSubcomodule M → v ∈ M → coactionSpan δ v ≤ M := by
  classical
  let W := coactionSpan δ v
  have extract (ℓ : A →ₗ[k] k) : contractRight ℓ (I → k) (δ.coaction v) ∈ W :=
    Submodule.subset_span ⟨ℓ, rfl⟩
  have hv := extract (Coalgebra.counit (R := k))
  change TensorProduct.rid k (I → k)
    ((Coalgebra.counit (R := k)).lTensor (I → k) (δ.coaction v)) ∈ W at hv
  rw [δ.counit v] at hv
  refine ⟨hv, ?_, ?_⟩
  · let b := Module.Free.chooseBasis k A
    let c := TensorProduct.equivFinsuppOfBasisRight b (δ.coaction v)
    have hc (i) : c i = contractRight (b.coord i) (I → k) (δ.coaction v) :=
      TensorProduct.equivFinsuppOfBasisRight_apply b _ i
    have hexp : ∑ i ∈ c.support, c i ⊗ₜ[k] b i = δ.coaction v := by
      simpa only [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum] using
        (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply (δ.coaction v)
    suffices W ≤ (LinearMap.range (W.subtype.rTensor A)).comap δ.coaction by
      exact fun w ↦ this w.property
    apply Submodule.span_le.mpr
    rintro _ ⟨ℓ, rfl⟩
    change δ.coaction (contractRight ℓ (I → k) (δ.coaction v)) ∈
      LinearMap.range (W.subtype.rTensor A)
    rw [coaction_contractRight, ← hexp, map_sum, map_sum]
    apply Submodule.sum_mem
    intro j hj
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
    exact ⟨(⟨c j, (hc j).symm ▸ extract (b.coord j)⟩ : W) ⊗ₜ[k] _, rfl⟩
  · intro M hM hv
    obtain ⟨t, ht⟩ := hM ⟨v, hv⟩
    apply Submodule.span_le.mpr
    rintro _ ⟨ℓ, rfl⟩
    change contractRight ℓ (I → k) (δ.coaction v) ∈ M
    rw [← ht, ← map_contractRight]
    exact (contractRight ℓ M t).property

omit [DecidableEq I] in
private theorem contractRight_coordinate {A : Type u} [AddCommGroup A] [Module k A]
    (ℓ : A →ₗ[k] k) (t : (I → k) ⊗[k] A) (i : I) :
    contractRight ℓ (I → k) t i =
      ℓ (RationalRepresentations.tensorCoordinate (Pi.basisFun k I) i t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x a =>
    simp [contractRight_tmul, RationalRepresentations.tensorCoordinate,
      Module.Basis.coord_apply, mul_comm]
  | add a b ha hb => simp [ha, hb]

private theorem coactionComparison : CoactionComparison.{u} := by
  intro k I _ _ _ G ρ A e
  let b := Pi.basisFun k I
  let α := e.hom ≫ ρ
  let δ := RationalRepresentations.pointsCoactionEquiv A b α
  have hM (R : TestAlgebra k) (a : A →ₐ[k] R) (j : I) :
      RationalRepresentations.evaluate A δ a (b j) =
        ∑ i, b i ⊗ₜ[k] (α.app R (toConv a)).val i j := by
    have hc : RationalRepresentations.coefficients A b δ = pointMatrix A α :=
      RationalRepresentations.coefficients_coactionOfMatrix A b _ (pointMatrix_isCoactionMatrix A α)
    rw [RationalRepresentations.evaluate, LinearMap.comp_apply,
      RationalRepresentations.coaction_apply_basis A b δ, hc, pointMatrix_evaluation A α R]
    simp
  have hδ : IsOrbitCoaction e ρ δ := by
    intro R a v i
    let M := (α.app R (toConv a)).val
    have hcoord (j : I) : RationalRepresentations.tensorCoordinate b i
        (RationalRepresentations.evaluate A δ a (b j)) = M i j := by
      rw [hM R a j]
      exact tensorCoordinate_sum_basis b _ i
    change RationalRepresentations.tensorCoordinate b i
      (RationalRepresentations.evaluate A δ a v) = M.mulVec (extendVector R v) i
    calc
      _ = RationalRepresentations.tensorCoordinate b i
          (RationalRepresentations.evaluate A δ a (∑ j, v j • b j)) := by
        congr 2
        exact (b.sum_equivFun v).symm
      _ = ∑ j, v j • M i j := by simp only [map_sum, map_smul, hcoord]
      _ = _ := by simp only [Matrix.mulVec, dotProduct, extendVector, Algebra.smul_def, mul_comm]
  refine ⟨δ, hδ, fun v ↦ ?_⟩
  have heq : orbitSpan ρ (𝟙 G.val.X) v = coactionSpan δ v := by
    apply le_antisymm
    · apply orbitSpan_le.mpr
      intro R x ℓ
      rw [Category.comp_id]
      let a := e.inv.app R x
      have ha : e.hom.app R a = x := by
        exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.inv_hom_id_app R)) x
      rw [← ha]
      let ℓ' := ℓ.comp a.ofConv.toLinearMap
      have hh : (fun i ↦ ℓ (act ρ R (e.hom.app R a) (extendVector R v) i)) =
          contractRight ℓ' (I → k) (δ.coaction v) := by
        funext i
        change ℓ (act ρ R (e.hom.app R (toConv a.ofConv)) (extendVector R v) i) = _
        rw [contractRight_coordinate, ← hδ R a.ofConv]
        exact congrArg ℓ (tensorCoordinate_evaluation b a.ofConv.toLinearMap (δ.coaction v) i)
      rw [hh]
      exact Submodule.subset_span ⟨ℓ', rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨ℓ, rfl⟩
      let R := CommAlgCat.of k A
      let a : A →ₐ[k] R := AlgHom.id k A
      let g : Points G.val.X R := e.hom.app R (toConv a)
      have hmem := orbitSpan_le.mp (le_refl (orbitSpan ρ (𝟙 G.val.X) v)) R g ℓ
      change contractRight ℓ (I → k) (δ.coaction v) ∈ _
      have hh : contractRight ℓ (I → k) (δ.coaction v) =
          fun i ↦ ℓ (act ρ R (g ≫ 𝟙 G.val.X) (extendVector R v) i) := by
        funext i
        rw [Category.comp_id, contractRight_coordinate]
        change _ = ℓ (act ρ R (e.hom.app R (toConv a)) (extendVector R v) i)
        rw [← hδ R a]
        exact congrArg ℓ (tensorCoordinate_evaluation b a.toLinearMap (δ.coaction v) i).symm
      rwa [hh]
  exact ⟨heq, heq.symm ▸ coactionSpan_minimal δ v⟩

private theorem affinePresentation (X : SchemeOver k) [IsAffine X.left] :
    ∃ R : TestAlgebra k, Nonempty ((testSpec k).obj (op R) ≅ X) := by
  obtain ⟨R, hR⟩ := essImage_algSpec.mpr (show IsAffine X.left from inferInstance)
  exact ⟨R.unop, hR⟩

private theorem affineTensor (X Y : SchemeOver k) [IsAffine X.left] [IsAffine Y.left] :
    IsAffine (X ⊗ Y).left := by
  haveI : IsAffineHom Y.hom := inferInstance
  exact IsAffine.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct X Y))

private theorem subgroupAffine (H : ClosedSubgroup G.val) : IsAffine H.group.X.left := by
  haveI := G.property.1
  letI := H.isClosedImmersion
  exact isAffine_of_isAffineHom H.inclusion.hom.hom.left

private theorem dense_of_self_baseChange {X Y : SchemeOver k} (f : X ⟶ Y)
    (h : DenseRange ((baseChange k k).map f).left) : DenseRange f.left := by
  have hid : fieldSpecMap k k = 𝟙 _ := by
    change Scheme.Spec.map (CommRingCat.ofHom (algebraMap k k)).op = _
    rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 _ from by ext x; simp]
    exact CategoryTheory.Functor.map_id _ _
  haveI : IsIso (fieldSpecMap k k) := hid.symm ▸ inferInstanceAs (IsIso (𝟙 _))
  let px := pullback.fst X.hom (fieldSpecMap k k)
  let py := pullback.fst Y.hom (fieldSpecMap k k)
  haveI : IsIso py := inferInstanceAs (IsIso (pullback.fst Y.hom (fieldSpecMap k k)))
  have he : ((baseChange k k).map f).left ≫ py = px ≫ f.left := by
    simp [px, py, Over.pullback_map_left]
  have hh := py.homeomorph.surjective.denseRange.comp h py.continuous
  change DenseRange (((baseChange k k).map f).left ≫ py) at hh
  rw [he] at hh
  exact DenseRange.of_comp (f := f.left) (g := px) hh

private theorem orbitSpan_of_dense (ρ : Representation G.val I)
    {X : SchemeOver k} [IsAffine X.left] [IsReduced G.val.X.left]
    (f : X ⟶ G.val.X) (hf : DenseRange f.left) (v : I → k) :
    orbitSpan ρ f v = orbitSpan ρ (𝟙 G.val.X) v := by
  haveI := G.property.1
  obtain ⟨R, ⟨e⟩⟩ := affinePresentation G.val.X
  obtain ⟨S, ⟨d⟩⟩ := affinePresentation X
  let FF := algSpec.fullyFaithful (R := CommRingCat.of k)
  let b : R ⟶ S := (FF.preimage (d.hom ≫ f ≫ e.inv)).unop
  have hb : (testSpec k).map b.op = d.hom ≫ f ≫ e.inv := FF.map_preimage _
  have hb' : (testSpec k).map b.op ≫ e.hom = d.hom ≫ f := by simp [hb]
  have hd := ((Over.forget _).mapIso e.symm).schemeIsoToHomeo.surjective.denseRange.comp
    (hf.comp ((Over.forget _).mapIso d).schemeIsoToHomeo.surjective.denseRange
      f.left.continuous) e.inv.left.continuous
  have hbd : DenseRange (PrimeSpectrum.comap b.hom.toRingHom) := by
    change DenseRange ((testSpec k).map b.op).left
    rw [hb]
    exact hd
  have hr : _root_.IsReduced R := by
    exact (affine_isReduced_iff (CommRingCat.of R)).mp (isReduced_of_isOpenImmersion e.hom.left)
  have hbinj : Function.Injective b.hom := by
    apply (RingHom.injective_iff_ker_eq_bot b.hom.toRingHom).mpr
    have hh := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mp hbd
    rw [nilradical_eq_zero R, Ideal.zero_eq_bot] at hh
    exact le_antisymm hh bot_le
  apply le_antisymm
  · simpa only [Category.comp_id] using orbitSpan_comp_le ρ f (𝟙 G.val.X) v
  · apply orbitSpan_le.mpr
    intro A x ℓ
    let a : R ⟶ A := (FF.preimage (x ≫ e.inv)).unop
    have ha : mapPoints a e.hom = x := by
      change (testSpec k).map a.op ≫ e.hom = x
      rw [show (testSpec k).map a.op = x ≫ e.inv from FF.map_preimage _]
      simp
    rw [Category.comp_id, ← ha]
    have hsplit : ∃ p : S →ₗ[k] R, p.comp b.hom.toLinearMap = LinearMap.id :=
      LinearMap.exists_leftInverse_of_injective b.hom.toLinearMap (LinearMap.ker_eq_bot.mpr hbinj)
    obtain ⟨p, hp⟩ := hsplit
    let ℓS := (ℓ.comp a.hom.toLinearMap).comp p
    have hm := orbitSpan_le.mp (le_refl (orbitSpan ρ f v)) S d.hom ℓS
    have heq : (fun i ↦ ℓ (act ρ A (mapPoints a e.hom) (extendVector A v) i)) =
        fun i ↦ ℓS (act ρ S (d.hom ≫ f) (extendVector S v) i) := by
      funext i
      have hA := act_natural ρ a (show GroupPoints G.val R from e.hom) v i
      have hS := act_natural ρ b (show GroupPoints G.val R from e.hom) v i
      change act ρ S ((testSpec k).map b.op ≫ e.hom) (extendVector S v) i = _ at hS
      rw [hb'] at hS
      refine (congrArg ℓ hA).trans ?_
      rw [hS]
      change ℓ (a.hom _) = ℓ (a.hom (p (b.hom _)))
      rw [show ∀ y : R, p (b.hom y) = y from fun y ↦ DFunLike.congr_fun hp y]
    rwa [heq]

private theorem cellOrbitSpan_eq (ρ : Representation G.val I) (T B Bneg : ClosedSubgroup G.val)
    (U : ClosedSubgroup B.group) (Uneg : ClosedSubgroup Bneg.group)
    (lam : Character T.group) (v : I → k)
    (hv : IsPrimitive ρ T B U lam v) :
    orbitSpan ρ (OpenCell.cellMap T Uneg U) v =
      orbitSpan ρ (Uneg.inclusion ≫ Bneg.inclusion).hom.hom v := by
  let m := OpenCell.cellMap T Uneg U
  let j := (Uneg.inclusion ≫ Bneg.inclusion).hom.hom
  let i := (U.inclusion ≫ B.inclusion).hom.hom
  apply le_antisymm
  · apply orbitSpan_le.mpr
    intro R x ℓ
    let y : GroupPoints Uneg.group R := x ≫ fst _ _
    let t : GroupPoints T.group R := x ≫ snd _ _ ≫ fst _ _
    let z : GroupPoints U.group R := x ≫ snd _ _ ≫ snd _ _
    let g : GroupPoints G.val R := x ≫ m
    let gn : GroupPoints G.val R := y ≫ j
    let gt : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
    let gu : GroupPoints G.val R := z ≫ i
    have h : g = gn * (gt * gu) := by
      simp only [g, gn, gt, gu, m, OpenCell.cellMap,
        LinearAlgebraicGroups.CocharacterDynamics.multiplyFactors, MonObj.comp_mul]
      rfl
    have hz : act ρ R gu (extendVector R v) = extendVector R v :=
      mem_fixedSpace.mp hv.2.1 R z
    have ht : act ρ R gt (extendVector R v) = characterValue lam R t • extendVector R v :=
      mem_weightSpace.mp hv.2.2 R t
    change (fun a ↦ ℓ (act ρ R g (extendVector R v) a)) ∈ _
    rw [h, act_mul, act_mul, hz, ht, act_smul]
    let b := LinearMap.mulLeft k (characterValue lam R t)
    exact orbitSpan_le.mp (le_refl (orbitSpan ρ j v)) R y (ℓ.comp b)
  · let a : Uneg.group.X ⟶ _ :=
      lift (𝟙 _) (lift (1 : Uneg.group.X ⟶ T.group.X) (1 : Uneg.group.X ⟶ U.group.X))
    have hj : a ≫ m = j := by
      simp only [a, m, OpenCell.cellMap, LinearAlgebraicGroups.CocharacterDynamics.multiplyFactors,
        MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd, Category.id_comp]
      simp [j]
    change orbitSpan ρ j v ≤ orbitSpan ρ m v
    rw [← hj]
    exact orbitSpan_comp_le ρ a m v

private def positiveCone (T B : ClosedSubgroup G.val) :
    Submodule ℕ (Additive (Character T.group)) :=
  Submodule.span ℕ (Set.range fun α : SimpleRoot T B ↦ Additive.ofMul α.val.val)

private theorem dominanceLE_iff (T B : ClosedSubgroup G.val) (mu lam : Character T.group) :
    DominanceLE T B mu lam ↔ Additive.ofMul lam - Additive.ofMul mu ∈ positiveCone T B := by
  rw [positiveCone, Finsupp.mem_span_range_iff_exists_finsupp]
  constructor <;> rintro ⟨c, hc⟩ <;>
    exact ⟨c, hc.symm⟩

private theorem positiveCone_nonneg (T B : ClosedSubgroup G.val)
    (f : Additive (Character T.group) →ₗ[ℤ] ℝ)
    (hf : ∀ α ∈ subgroupRoots T B, 0 < f (Additive.ofMul α.val))
    {x : Additive (Character T.group)} (hx : x ∈ positiveCone T B) : 0 ≤ f x := by
  refine Submodule.span_induction (p := fun x _ ↦ 0 ≤ f x) ?_ (by simp)
    (fun a b _ _ ha hb ↦ by rw [map_add]; exact add_nonneg ha hb)
    (fun n a _ ha ↦ by rw [map_nsmul]; exact nsmul_nonneg ha n) hx
  rintro _ ⟨α, rfl⟩
  exact (hf α.val α.property.1).le

private theorem positiveRoot_mem_cone (T B : ClosedSubgroup G.val) [Finite (Root T)]
    (f : Additive (Character T.group) →ₗ[ℤ] ℝ)
    (hf : ∀ α ∈ subgroupRoots T B, 0 < f (Additive.ofMul α.val))
    (α : Root T) (hα : α ∈ subgroupRoots T B) :
    Additive.ofMul α.val ∈ positiveCone T B := by
  classical
  let g (root₁ : Root T) := f (Additive.ofMul root₁.val)
  have wf : WellFounded (fun a b : Root T ↦ g a < g b) := by
    let s := Set.range g
    have hs : s.Finite := Set.finite_range g
    let e : Root T → s := fun a ↦ ⟨g a, Set.mem_range_self a⟩
    exact (InvImage.wf e (hs.wellFoundedOn (r := (· < ·)))).mono (fun _ _ h ↦ h)
  induction α using wf.induction with
  | h α ih =>
    by_cases hsimple : ∀ (b : Root T), b ∈ subgroupRoots T B →
        ∀ (c : Root T), c ∈ subgroupRoots T B → α.val ≠ b.val * c.val
    · exact Submodule.subset_span ⟨⟨α, hα, hsimple⟩, rfl⟩
    · push Not at hsimple
      obtain ⟨root₁, hroot₁, root₂, hroot₂, h⟩ := hsimple
      have he : Additive.ofMul α.val = Additive.ofMul root₁.val + Additive.ofMul root₂.val := h
      have hg : g α = g root₁ + g root₂ := by exact (congrArg f he).trans (map_add f _ _)
      have hb : g root₁ < g α := hg ▸ lt_add_of_pos_right _ (hf root₂ hroot₂)
      have hc : g root₂ < g α := hg ▸ lt_add_of_pos_left _ (hf root₁ hroot₁)
      rw [he]
      exact Submodule.add_mem _ (ih root₁ hb hroot₁) (ih root₂ hc hroot₂)

private def lowerSpan (ρ : Representation G.val I) (T B : ClosedSubgroup G.val)
    (lam : Character T.group) (v : I → k) : Submodule k (I → k) :=
  Submodule.span k {v} ⊔ ⨆ (mu : {mu : Character T.group // mu ≠ lam ∧ DominanceLE T B mu lam}),
    weightSpace ρ T mu.val

private def extendedSpan (R : TestAlgebra k) (W : Submodule k (I → k)) :
    Submodule R (I → R) :=
  Submodule.span R (extendVector R '' (W : Set (I → k)))

omit [Fintype I] [DecidableEq I] in
private theorem extendedSpan_mem (R : TestAlgebra k) {W : Submodule k (I → k)}
    {w : I → k} (hw : w ∈ W) : extendVector R w ∈ extendedSpan R W :=
  Submodule.subset_span ⟨w, hw, rfl⟩

omit [Fintype I] [DecidableEq I] in
private theorem slice_mem_of_extendedSpan (R : TestAlgebra k) (W : Submodule k (I → k))
    (ℓ : R →ₗ[k] k) {w : I → R} (hw : w ∈ extendedSpan R W) :
    (fun i ↦ ℓ (w i)) ∈ W := by
  revert ℓ
  induction hw using Submodule.span_induction with
  | mem x hx =>
    intro ℓ
    obtain ⟨x, hx, rfl⟩ := hx
    have h : (fun i ↦ ℓ (extendVector R x i)) = ℓ 1 • x := by
      funext i
      change ℓ (algebraMap k R (x i)) = ℓ 1 * x i
      rw [show algebraMap k R (x i) = x i • (1 : R) by simp [Algebra.smul_def]]
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [h]
    exact W.smul_mem _ hx
  | zero =>
    intro ℓ
    change (fun _ : I ↦ ℓ 0) ∈ W
    rw [map_zero]
    exact W.zero_mem
  | add x y hx hy hxx hyy =>
    intro ℓ
    have he : (fun i ↦ ℓ ((x + y) i)) = (fun i ↦ ℓ (x i)) + fun i ↦ ℓ (y i) :=
      funext fun i ↦ ℓ.map_add (x i) (y i)
    rw [he]
    exact W.add_mem (hxx ℓ) (hyy ℓ)
  | smul r x hx ih =>
    intro ℓ
    exact ih (ℓ.comp (LinearMap.mulLeft k r))

private theorem neg_shift (T B : ClosedSubgroup G.val) [IsCommMonObj T.group.X]
    (D : Datum T) (f : Additive (Character T.group) →ₗ[ℤ] ℝ)
    (hf : ∀ α : Root T, f (Additive.ofMul α.val) ≠ 0)
    (hpos : ∀ α : Root T, α ∈ subgroupRoots T B ↔ 0 < f (Additive.ofMul α.val))
    (α : Root T) (ha : α ∉ subgroupRoots T B)
    {mu lam : Character T.group} (hmu : DominanceLE T B mu lam)
    (j : ℕ) (hj : 0 < j) :
    mu * α.val ^ j ≠ lam ∧ DominanceLE T B (mu * α.val ^ j) lam := by
  letI := D.finiteRoots
  let root₁ := D.rootDatum.reflectionPerm α α
  have hb : Additive.ofMul root₁.val = -Additive.ofMul α.val := by
    rw [← D.root_eq root₁, ← D.root_eq α]
    exact D.rootDatum.root_eq_neg_iff.mpr rfl
  have hneg : f (Additive.ofMul α.val) < 0 :=
    lt_of_le_of_ne (not_lt.mp (fun h => ha ((hpos α).mpr h))) (hf α)
  have hbpos : root₁ ∈ subgroupRoots T B := (hpos root₁).mpr (by rw [hb, map_neg]; linarith)
  have hΔ : Additive.ofMul lam - Additive.ofMul (mu * α.val ^ j) =
      (Additive.ofMul lam - Additive.ofMul mu) + j • Additive.ofMul root₁.val := by
    change Additive.ofMul lam - (Additive.ofMul mu + j • Additive.ofMul α.val) = _
    rw [hb, smul_neg]
    abel
  have hp := (dominanceLE_iff T B mu lam).mp hmu
  have hq := positiveRoot_mem_cone T B f (fun a h ↦ (hpos a).mp h) root₁ hbpos
  refine ⟨?_, (dominanceLE_iff T B _ _).mpr (hΔ ▸ (positiveCone T B).add_mem hp
    ((positiveCone T B).smul_mem j hq))⟩
  intro h
  rw [h, sub_self] at hΔ
  have hΔ' := congrArg f hΔ
  rw [map_zero, map_add, map_nsmul] at hΔ'
  have h0 := positiveCone_nonneg T B f (fun a h ↦ (hpos a).mp h) hp
  have hjp : 0 < j • f (Additive.ofMul root₁.val) := nsmul_pos ((hpos root₁).mp hbpos) hj.ne'
  exact (ne_of_gt (add_pos_of_nonneg_of_pos h0 hjp)) hΔ'.symm

private theorem act_root_of_coefficients (ρ : Representation G.val I)
    (R : TestAlgebra k) {A : AdditiveLine k} (x : A.group ⟶ G.val)
    (c : R) (v : I → k) (W : Submodule k (I → k)) (p : I → Polynomial k)
    (hp : ∀ j, (fun i ↦ (p i).coeff j) ∈ W)
    (ha : act ρ R (rootPoint x R c) (extendVector R v) = fun i ↦ Polynomial.aeval c (p i)) :
    act ρ R (rootPoint x R c) (extendVector R v) ∈ extendedSpan R W := by
  let n := (Finset.univ.sup fun i : I ↦ (p i).natDegree) + 1
  have hsum : (fun i ↦ Polynomial.aeval c (p i)) =
      ∑ j ∈ Finset.range n, c ^ j • extendVector R (fun i ↦ (p i).coeff j) := by
    funext i
    have hn : (p i).natDegree < n :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun i : I ↦ (p i).natDegree) (Finset.mem_univ i))
    rw [Polynomial.aeval_eq_sum_range' hn]
    simp only [Finset.sum_apply, Algebra.smul_def]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  rw [ha, hsum]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (extendedSpan_mem R (hp j))

private theorem act_root_preserves_lowerSpan (ρ : Representation G.val I)
    (T B : ClosedSubgroup G.val) (hρ : RootOrbit ρ T) (lam : Character T.group)
    (v : I → k) (hv : v ∈ weightSpace ρ T lam)
    (α : Root T) (H : ClosedSubgroup G.val) (hH : Specs.RootGroups.IsRootSubgroup T H α.val)
    (A : AdditiveLine k) (x : A.group ≅ H.group)
    (hA : Specs.RootGroups.HasScalarAction T α.val (x.hom ≫ H.inclusion))
    (hshift : ∀ {mu}, DominanceLE T B mu lam → ∀ j : ℕ, 0 < j →
       mu * α.val ^ j ≠ lam ∧ DominanceLE T B (mu * α.val ^ j) lam)
    (R : TestAlgebra k) (c : R) {w : I → R}
    (hw : w ∈ extendedSpan R (lowerSpan ρ T B lam v)) :
    act ρ R (rootPoint (x.hom ≫ H.inclusion) R c) w ∈ extendedSpan R (lowerSpan ρ T B lam v) := by
  let W := lowerSpan ρ T B lam v
  let J := {mu : Character T.group // mu ≠ lam ∧ DominanceLE T B mu lam}
  have mem_weight (mu : J) (z : I → k) (hz : z ∈ weightSpace ρ T mu.val) :
      z ∈ W := by
    change z ∈ Submodule.span k {v} ⊔ ⨆ mu : J, weightSpace ρ T mu.val
    apply Submodule.mem_sup_right
    exact Submodule.mem_iSup_of_mem (p := fun mu : J ↦ weightSpace ρ T mu.val) mu hz
  let a := actLinear ρ R (rootPoint (x.hom ≫ H.inclusion) R c)
  change w ∈ (extendedSpan R W).comap a
  have hgen : W ≤ (((extendedSpan R W).comap a).restrictScalars k).comap (extendLinear R) := by
    have hweight (mu : Character T.group) (hle : DominanceLE T B mu lam)
        (z : I → k) (hz : z ∈ weightSpace ρ T mu) (hz' : z ∈ W) :
        a (extendVector R z) ∈ extendedSpan R W := by
      obtain ⟨p, h0, hc, ha⟩ := hρ α H hH A x hA mu ⟨z, hz⟩
      refine act_root_of_coefficients ρ R _ c z W p ?_ (ha R c)
      intro j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [h0]
        exact hz'
      · let nu : J := ⟨mu * α.val ^ j, hshift (mu := mu) hle j hj⟩
        exact mem_weight nu _ (hc j hj)
    change (Submodule.span k {v} ⊔ ⨆ mu : J, weightSpace ρ T mu.val) ≤ _
    apply sup_le
    · rw [Submodule.span_le]
      intro z hz
      have he : z = v := Set.mem_singleton_iff.mp hz
      subst z
      apply hweight lam ((dominanceLE_iff T B lam lam).mpr (by simp)) v hv
      exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton v))
    · apply iSup_le
      intro mu z hz
      exact hweight mu.val mu.property.2 z hz (mem_weight mu z hz)
  apply Submodule.span_le.mpr ?_ hw
  rintro y ⟨z, hz, rfl⟩
  exact hgen hz

private theorem rootPoint_surjective {A : AdditiveLine k} {H : GroupScheme k}
    (x : A.group ≅ H) (R : TestAlgebra k) (p : GroupPoints H R) :
    ∃ c : R, rootPoint x.hom R c = p := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a := (F.preimage (p ≫ x.inv.hom.hom)).unop
  have ha : (testSpec k).map a.op = p ≫ x.inv.hom.hom := F.map_preimage _
  refine ⟨a.hom Polynomial.X, ?_⟩
  have hb : Polynomial.aeval (a.hom Polynomial.X) = a.hom :=
    Polynomial.algHom_ext (Polynomial.aeval_X _)
  unfold rootPoint
  rw [hb]
  change (testSpec k).map a.op ≫ x.hom.hom.hom = (show Points H.X R from p)
  rw [ha]
  have h : x.inv.hom.hom ≫ x.hom.hom.hom = 𝟙 _ := (Grp.forget _).congr_map x.inv_hom_id
  exact (Category.assoc (show Points H.X R from p) _ _).trans (by rw [h, Category.comp_id])

private theorem rootProduct_preserves (ρ : Representation G.val I) (T : ClosedSubgroup G.val)
    (U : RootSubgroupFamily T) (S : Set (Root T)) (l : List (Root T))
    (hl : ∀ α ∈ l, α ∈ S) (R : TestAlgebra k) (W : Submodule R (I → R))
    (hact : ∀ α ∈ S, ∀ p : GroupPoints (U α).val.group R, ∀ w ∈ W,
      act ρ R (p ≫ (U α).val.inclusion.hom.hom) w ∈ W)
    (p : Points (product (fun α => (U α).val.group.X) l) R) (w : I → R) (hw : w ∈ W) :
    act ρ R (p ≫ rootProduct U l) w ∈ W := by
  induction l with
  | nil =>
    have he : p ≫ rootProduct U [] = (1 : GroupPoints G.val R) :=
      MonObj.comp_one p
    rw [he, act_one]
    exact hw
  | cons α l ih =>
    let x := p ≫ fst _ _
    let y := p ≫ snd _ _
    let g : GroupPoints G.val R := p ≫ rootProduct U (α :: l)
    let gx : GroupPoints G.val R := x ≫ (U α).val.inclusion.hom.hom
    let gy : GroupPoints G.val R := y ≫ rootProduct U l
    have he : g = gx * gy := by
      simp only [g, gx, gy, x, y, rootProduct, MonObj.comp_mul, Category.assoc]
    change act ρ R g w ∈ W
    rw [he, act_mul]
    exact hact α (hl α (List.mem_cons_self ..)) x _
      (ih (fun beta hb ↦ hl beta (List.mem_cons_of_mem _ hb)) y)

open Specs.DiagonalizableGroups (integerGenerator)
open private integerHopfHomEquiv_generator from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

private theorem weightProjection (ρ : Representation G.val I)
    (T : ClosedSubgroup G.val) (chi : Character T.group) :
    by
      classical
      exact ∃ P : (I → k) →ₗ[k] (I → k), ∀ mu (w : I → k),
        w ∈ weightSpace ρ T mu → P w = if mu = chi then w else 0 := by
  classical
  let C : AffineGroupCategory k := ⟨T.group, subgroupAffine T⟩
  let A := coordinateHopf C
  let R := CommAlgCat.of k A
  let e : specGroup A ≅ T.group := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso C)
  let t : GroupPoints T.group R := e.hom.hom.hom
  let characters := LinearAlgebraicGroups.CharacterDescent.groupLikeCharacterEquiv A
  let index (mu : Character T.group) : GroupLike k A := characters.symm (e.hom ≫ mu)
  have hinj : Function.Injective index := by
    intro a b hab
    have h := characters.symm.injective hab
    exact (cancel_epi e.hom).mp h
  let value (mu : Character T.group) : A := (index mu).val
  have hc (mu : Character T.group) : characterValue mu R t = value mu := by
    have he : e.hom ≫ mu = characters (index mu) := (characters.apply_symm_apply _).symm
    change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      (e.hom.hom.hom ≫ mu.hom.hom)).unop.hom (MonoidAlgebra.single integerGenerator 1) = _
    change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      (e.hom ≫ mu).hom.hom).unop.hom (MonoidAlgebra.single integerGenerator 1) = _
    rw [he]
    change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      ((testSpec k).map (CommAlgCat.ofHom _).op)).unop.hom
        (MonoidAlgebra.single integerGenerator 1) = _
    rw [Functor.FullyFaithful.preimage_map]
    exact integerHopfHomEquiv_generator A (index mu)
  have hind : LinearIndependent k value := (linearIndep_groupLikeVal (R := k) (A := A)).comp index hinj
  let L := Finsupp.linearCombination k value
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective L (linearIndependent_iff_ker.mp hind)
  let ℓ : A →ₗ[k] k := (Finsupp.lapply chi).comp p
  have hℓ (mu : Character T.group) : ℓ (value mu) = if mu = chi then 1 else 0 := by
    have hs : L (Finsupp.single mu 1) = value mu := by simp [L]
    have h := DFunLike.congr_fun hp (Finsupp.single mu 1)
    change p (L (Finsupp.single mu 1)) = _ at h
    rw [hs] at h
    change (p (value mu)) chi = _
    rw [h]
    exact Finsupp.single_apply
  refine ⟨(LinearMap.pi (fun i : I ↦ ℓ.comp (LinearMap.proj i))).comp
      (((actLinear ρ R (t ≫ T.inclusion.hom.hom)).restrictScalars k).comp (extendLinear R)), ?_⟩
  intro mu w hw
  have hmu := mem_weightSpace.mp hw R t
  funext i
  change ℓ (act ρ R (t ≫ T.inclusion.hom.hom) (extendVector R w) i) = _
  rw [hmu]
  change ℓ (characterValue mu R t * algebraMap k R (w i)) = _
  rw [hc, mul_comm, ← Algebra.smul_def, map_smul, hℓ]
  by_cases h : mu = chi <;> simp [h]

private theorem weights_of_lowerSpan_eq_top (ρ : Representation G.val I)
    (T B : ClosedSubgroup G.val)
    (lam : Character T.group) (v : I → k) (hv : v ∈ weightSpace ρ T lam)
    (hW : lowerSpan ρ T B lam v = ⊤) :
    weightSpace ρ T lam = Submodule.span k {v} ∧
      ∀ mu : Character T.group, mu ≠ lam → weightSpace ρ T mu ≠ ⊥ → DominanceLE T B mu lam := by
  classical
  have detect (chi : Character T.group) (M : Submodule k (I → k))
      (P : (I → k) →ₗ[k] (I → k))
      (hP : ∀ mu w, w ∈ weightSpace ρ T mu → P w = if mu = chi then w else 0)
      (hvP : P v ∈ M)
      (hweight : ∀ (mu : {mu : Character T.group // mu ≠ lam ∧ DominanceLE T B mu lam})
        (w : I → k), w ∈ weightSpace ρ T mu.val → P w ∈ M) :
      weightSpace ρ T chi ≤ M := by
    have hd : lowerSpan ρ T B lam v ≤ M.comap P := by
      apply sup_le
      · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvP)
      · exact iSup_le (fun mu w hw ↦ hweight mu w hw)
    intro w hw
    have hwM := hd (hW ▸ Submodule.mem_top (x := w))
    change P w ∈ M at hwM
    rwa [hP chi w hw, ite_eq_left rfl] at hwM
  constructor
  · obtain ⟨P, hP⟩ := weightProjection ρ T lam
    apply le_antisymm
    · refine detect lam _ P hP ?_ ?_
      · rw [hP lam v hv, ite_eq_left rfl]
        exact Submodule.subset_span (Set.mem_singleton v)
      · intro mu w hw
        rw [hP _ _ hw, ite_eq_right mu.property.1]
        exact Submodule.zero_mem _
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv)
  · intro mu hmu hn
    by_contra hb
    obtain ⟨P, hP⟩ := weightProjection ρ T mu
    apply hn
    apply le_bot_iff.mp
    refine detect mu ⊥ P hP ?_ ?_
    · rw [hP lam v hv, ite_eq_right hmu.symm]
      exact Submodule.zero_mem _
    · intro nu w hw
      have hne : nu.val ≠ mu := fun he ↦ hb (he ▸ nu.property.2)
      rw [hP _ _ hw, ite_eq_right hne]
      exact Submodule.zero_mem _

private theorem act_rational (ρ : Representation G.val I) (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (R : TestAlgebra k) (v : I → k) :
    act ρ R (toUnit _ ≫ n) (extendVector R v) =
      extendVector R (act ρ (CommAlgCat.of k k) (toUnit _ ≫ n) v) := by
  let K := CommAlgCat.of k k
  let a : K ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  let g : GroupPoints G.val K := toUnit _ ≫ n
  have h : mapPoints a g = toUnit _ ≫ n := by
    simp [mapPoints, g]
  have hv : extendVector K v = v := funext fun i ↦ by simp [extendVector, K]
  funext i
  exact (congrArg (fun q : GroupPoints G.val R ↦ act ρ R q (extendVector R v) i) h).symm.trans
    ((act_natural ρ a g v i).trans (by rw [hv]; rfl))

private theorem reflectedWeight (ρ : Representation G.val I) (T : ClosedSubgroup G.val)
    {α : Character T.group} {A : AdditiveLine k} {xp xn : A.group ⟶ G.val}
    (r : Specs.RootGroups.CorootReflection T α xp xn)
    (lam : Character T.group) (v : I → k)
    (hv : v ∈ weightSpace ρ T lam) (hv0 : v ≠ 0) :
    weightSpace ρ T (r.conjugation.inv ≫ lam) ≠ ⊥ := by
  let K := CommAlgCat.of k k
  let n : GroupPoints G.val K := toUnit _ ≫ r.representative
  let z := act ρ K n v
  have hz : z ≠ 0 := by
    intro hz
    have h : act ρ K n⁻¹ z = v := by
      change act ρ K n⁻¹ (act ρ K n v) = v
      rw [← act_mul, inv_mul_cancel, act_one]
    exact hv0 (by rw [← h, hz]; exact (actLinear ρ K n⁻¹).map_zero)
  suffices hz' : z ∈ weightSpace ρ T (r.conjugation.inv ≫ lam) by
    intro h
    rw [h, Submodule.mem_bot] at hz'
    exact hz hz'
  apply mem_weightSpace.mpr
  intro R t
  let nr : GroupPoints G.val R := toUnit _ ≫ r.representative
  let t' : Points T.group.X R := t ≫ r.conjugation.inv.hom.hom
  let g : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
  let g' : GroupPoints G.val R := t' ≫ T.inclusion.hom.hom
  have he : g = nr * g' * nr⁻¹ := by
    have h := congrArg (fun f : T.group.X ⟶ G.val.X ↦ t' ≫ f) r.conjugates
    have hi : r.conjugation.inv.hom.hom ≫ r.conjugation.hom.hom.hom = 𝟙 _ :=
      (Grp.forget _).congr_map r.conjugation.inv_hom_id
    have hleft : t' ≫ (r.conjugation.hom ≫ T.inclusion).hom.hom = g := by
      change (show Points T.group.X R from t) ≫ r.conjugation.inv.hom.hom ≫
        r.conjugation.hom.hom.hom ≫ T.inclusion.hom.hom = _
      rw [← Category.assoc (f := r.conjugation.inv.hom.hom), hi, Category.id_comp]
    rw [hleft, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv] at h
    simp only [Category.assoc, comp_toUnit_assoc] at h
    exact h
  have hmul : g * nr = nr * g' := by rw [he, mul_assoc, inv_mul_cancel, mul_one]
  have hzR : act ρ R nr (extendVector R v) = extendVector R z :=
    act_rational ρ r.representative R v
  change act ρ R g (extendVector R z) = characterValue lam R t' • extendVector R z
  rw [← hzR, ← act_mul, hmul, act_mul]
  have hwt : act ρ R g' (extendVector R v) = characterValue lam R t' • extendVector R v :=
    mem_weightSpace.mp hv R t'
  rw [hwt, act_smul]

private theorem dominance_of_reflections (ρ : Representation G.val I)
    (T B : ClosedSubgroup G.val) [IsCommMonObj T.group.X] (D : Datum T)
    (f : Additive (Character T.group) →ₗ[ℤ] ℝ)
    (hf : ∀ α ∈ subgroupRoots T B, 0 < f (Additive.ofMul α.val))
    (lam : Character T.group) (v : I → k) (hv : v ∈ weightSpace ρ T lam) (hv0 : v ≠ 0)
    (hle : ∀ mu : Character T.group, mu ≠ lam → weightSpace ρ T mu ≠ ⊥ → DominanceLE T B mu lam) :
    IsDominant D B lam := by
  intro α
  obtain ⟨C, cochar, hC, hc, P, N, hPN, Q, F, A, L, pos, neg, hp, hn, hx, hy, r, hr⟩ :=
    D.attached α.val
  let nu := r.conjugation.inv ≫ lam
  have hn0 : weightSpace ρ T nu ≠ ⊥ := reflectedWeight ρ T r lam v hv hv0
  have hnu : DominanceLE T B nu lam := by
    by_cases h : nu = lam
    · exact (dominanceLE_iff T B nu lam).mpr (by simp [h])
    · exact hle nu h hn0
  have hh := positiveCone_nonneg T B f hf ((dominanceLE_iff T B nu lam).mp hnu)
  have he : Additive.ofMul lam - Additive.ofMul nu =
      D.rootDatum.toLinearMap (Additive.ofMul lam) (D.rootDatum.coroot α.val) •
        Additive.ofMul α.val.val := by
    rw [show nu = lam * α.val.val ^ (-Specs.CharacterPairing.pairing T.group lam r.coroot) from
      r.reflection lam]
    change Additive.ofMul lam - (Additive.ofMul lam +
      (-Specs.CharacterPairing.pairing T.group lam r.coroot) • Additive.ofMul α.val.val) = _
    have hp' : Specs.CharacterPairing.pairing T.group lam r.coroot =
        D.rootDatum.toLinearMap (Additive.ofMul lam) (D.rootDatum.coroot α.val) := by
      rw [hr]
      exact (D.pairing_eq lam (Additive.toMul (D.rootDatum.coroot α.val))).symm
    rw [hp', neg_smul]
    abel
  rw [he, map_zsmul, zsmul_eq_mul] at hh
  exact_mod_cast nonneg_of_mul_nonneg_left hh (hf α.val α.property.1)

private theorem highestWeight
    (hWeight : Specs.RootWeightAction.Statement.{u})
    (hCell : Specs.OpenCell.Statement.{u})
    (hBorel : Specs.BorelPositivity.Statement.{u}) : HighestWeight.{u} := by
  classical
  intro k _ G hG T B hT hmax hB hTB
  obtain ⟨comm, D, _, _, _, _, _, hρ⟩ := hWeight G hG T B hT hmax hB hTB
  letI := comm
  refine ⟨comm, D, ?_⟩
  obtain ⟨_, _, _, hBC, _, _, hRad⟩ := hBorel G hG T hT hmax
  obtain ⟨f, hf, hfB⟩ := hBC.1 B hB hTB
  have hpos (α : Root T) : α ∈ subgroupRoots T B ↔ 0 < f (Additive.ofMul α.val) := by
    rw [hfB]
    rfl
  have hneg : IsPositiveSystem T (subgroupRoots T B)ᶜ := by
    refine ⟨-f, fun α h ↦ hf α (neg_eq_zero.mp h), ?_⟩
    ext α
    change α ∉ subgroupRoots T B ↔ 0 < -f (Additive.ofMul α.val)
    rw [hpos, neg_pos]
    exact ⟨fun h ↦ lt_of_le_of_ne (not_lt.mp h) (hf α), fun h ↦ not_lt.mpr h.le⟩
  obtain ⟨Bneg, hBn, hTBn, hOpp⟩ := hBC.2.1 _ hneg
  obtain ⟨Un, _, _, hUn, _, _, _, _, _, hprod⟩ := hRad Bneg hBn hTBn
  intro U' hU' I _ _ ρ lam v hv
  obtain ⟨rootOrbit, _, _, _, _⟩ := hρ ρ
  have horbit (N : ClosedSubgroup G.val) (hN : Specs.GeometricBorelConjugacy.IsKBorel N)
      (hTN : Specs.SchemeDerivedGroup.IsSubgroupOf T N) (hOpp : OpenCell.AreOpposite T B N)
      (R : ClosedSubgroup N.group)
      (hR : IsUnipotentRadical (closedSubgroupAlgebraicGroup N) R) :
      orbitSpan ρ (𝟙 G.val.X) v = orbitSpan ρ (R.inclusion ≫ N.inclusion).hom.hom v := by
    haveI : Smooth G.val.X.hom := hG.1
    haveI : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
    haveI : IsAffine T.group.X.left := subgroupAffine T
    haveI : IsAffine (closedSubgroupAlgebraicGroup B).val.X.left :=
      (closedSubgroupAlgebraicGroup B).property.1
    haveI : IsAffine (T.group.X ⊗ U'.group.X).left := by
      letI : IsAffine U'.group.X.left := subgroupAffine (G := closedSubgroupAlgebraicGroup B) U'
      exact affineTensor _ _
    haveI : IsAffine (R.group.X ⊗ (T.group.X ⊗ U'.group.X)).left := by
      letI : IsAffine R.group.X.left := subgroupAffine (G := closedSubgroupAlgebraicGroup N) R
      exact affineTensor _ _
    have hd := (hCell G hG T hT hmax B N hB hN hTB hTN hOpp R U' hR hU').2.1 k
    exact (orbitSpan_of_dense ρ _ (dense_of_self_baseChange _ hd) v).symm.trans
      (cellOrbitSpan_eq ρ T B N U' R lam v hv)
  refine ⟨horbit, fun hcyclic ↦ ?_⟩
  letI := D.finiteRoots
  let RootCoord (α : Root T) := Σ H : {H : ClosedSubgroup G.val // Specs.RootGroups.IsRootSubgroup T H α.val},
    Σ A : AdditiveLine k, {x : A.group ≅ H.val.group //
      Specs.RootGroups.HasScalarAction T α.val (x.hom ≫ H.val.inclusion)}
  have hcoord (α : Root T) : Nonempty (RootCoord α) := by
    obtain ⟨C, cochar, hred, hp, P, N, hPN, Q, F, A, L, pos, neg, hpos, hneg, hact, _, _⟩ :=
      D.attached α
    exact ⟨⟨⟨_, hpos⟩, L, ⟨pos.root, hact⟩⟩⟩
  let coords (α : Root T) := Classical.choice (hcoord α)
  let roots : RootSubgroupFamily T := fun α ↦ (coords α).1
  let S := subgroupRoots T Bneg
  let Sfin := (Set.toFinite S).toFinset
  let l := Sfin.toList
  have hl : Specs.OrderedRootProducts.Enumerates l S :=
    ⟨Finset.nodup_toList _, by intro α; simp [l, Sfin]⟩
  obtain ⟨E, hE⟩ := hprod roots l hl
  let W := lowerSpan ρ T B lam v
  have hV : v ∈ W := Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
  have hspan : orbitSpan ρ (Un.inclusion ≫ Bneg.inclusion).hom.hom v ≤ W := by
    apply orbitSpan_le.mpr
    intro R x ℓ
    let y := x ≫ E.inv
    have hy : y ≫ rootProduct roots l = x ≫ (Un.inclusion ≫ Bneg.inclusion).hom.hom := by
      rw [← hE]
      simp [y]
    rw [← hy]
    apply slice_mem_of_extendedSpan R W ℓ
    apply rootProduct_preserves ρ T roots S l (fun α h ↦ (hl.2 α).mp h) R (extendedSpan R W) _ y _
      (extendedSpan_mem R hV)
    intro α hα z w hw
    let A := (coords α).2.1
    let p := (coords α).2.2
    obtain ⟨c, hc⟩ := rootPoint_surjective p.val R z
    rw [← hc]
    have he : rootPoint p.val.hom R c ≫ (roots α).val.inclusion.hom.hom =
        rootPoint (p.val.hom ≫ (roots α).val.inclusion) R c := by
      simp only [rootPoint, Category.assoc]
      rfl
    rw [he]
    exact act_root_preserves_lowerSpan ρ T B rootOrbit lam v hv.2.2 α _ (roots α).property A p.val p.property
      (fun h j hj ↦ neg_shift T B D f hf hpos α (by simpa [S, hOpp] using hα) h j hj) R c hw
  have hle := (horbit Bneg hBn hTBn hOpp Un hUn).trans_le hspan
  rw [hcyclic] at hle
  have hW : W = ⊤ := top_le_iff.mp hle
  obtain ⟨hline, hlower⟩ := weights_of_lowerSpan_eq_top ρ T B lam v hv.2.2 hW
  exact ⟨hline, hlower, dominance_of_reflections ρ T B D f
    (fun α h ↦ (hpos α).mp h) lam v hv.2.2 hv.1 hlower⟩

/-- The cyclic highest-weight theorem conditional on root-weight transport,
the open cell, and Borel positivity. -/
theorem cyclicHighestWeight_conditional
    (hWeight : Specs.RootWeightAction.Statement.{u})
    (hCell : Specs.OpenCell.Statement.{u})
    (hBorel : Specs.BorelPositivity.Statement.{u}) :
    Specs.CyclicHighestWeight.Statement.{u} :=
  ⟨coactionComparison, highestWeight hWeight hCell hBorel⟩

end
end LinearAlgebraicGroups.Representation.CyclicHighestWeight

universe v8_closure_bf7693b06039176b_u0
theorem _root_.«LinearAlgebraicGroups».«Representation».«CyclicHighestWeight».«cyclicHighestWeight» : _root_.«LinearAlgebraicGroups».«Specs».«CyclicHighestWeight».«Statement».{v8_closure_bf7693b06039176b_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«CyclicHighestWeight».«cyclicHighestWeight_conditional».{v8_closure_bf7693b06039176b_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«RootWeightAction».«rootWeightAction».{v8_closure_bf7693b06039176b_u0}) (@_root_.«LinearAlgebraicGroups».«Flag».«OpenCell».«openCell».{v8_closure_bf7693b06039176b_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelPositivity».«borelPositivity».{v8_closure_bf7693b06039176b_u0})
