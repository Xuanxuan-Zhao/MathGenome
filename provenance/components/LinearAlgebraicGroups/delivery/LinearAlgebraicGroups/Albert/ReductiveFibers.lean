import Specs.LinearAlgebraicGroups.Albert.ReductiveFibers
import LinearAlgebraicGroups.Albert.IdempotentCharts
import LinearAlgebraicGroups.Albert.SpinWeights
import LinearAlgebraicGroups.Reductive.GeometricRadicals
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Albert.ReductiveFibers

open AlgebraicGeometry CategoryTheory Opposite Matrix WithConv
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open ReductiveFiberSpecification
open IdempotentSpecification (IsSplitAutomorphism ZornIndex)
open TrialitySpecification (Model mapModel)
open CubicSpecification (cubicUnit)
open _root_.LinearAlgebraicGroups.Composition (Zorn)
open scoped Matrix CategoryTheory.MonObj TensorProduct

open private splitAuto_preserves pairedFunctions_map
  from LinearAlgebraicGroups.Albert.IdempotentCharts
open private pointMatrix pointMatrix_isCoactionMatrix pointMatrix_evaluation
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private invariant_iff_coaction from LinearAlgebraicGroups.Unipotent.Criteria
open private sections_normal from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private trivial_of_finite_rational_points from LinearAlgebraicGroups.Albert.SpinWeights

universe u
noncomputable section

set_option backward.isDefEq.respectTransparency false

section Coordinates

variable {R S : Type u} [CommRing R] [CommRing S]

private def diagonalLift (R : Type u) [CommRing R] :
    (b : Bool) → (DiagonalIndex b → R) →ₗ[R] (Fin 3 → R)
  | false => {
      toFun := fun v => ![v 0, v 1, -(v 0 + v 1)]
      map_add' := by
        intro v w
        ext i
        fin_cases i <;> simp [Pi.add_apply, add_comm]
        all_goals abel
      map_smul' := by
        intro c v
        ext i
        fin_cases i <;> simp [Pi.smul_apply, mul_add] }
  | true => {
      toFun := fun v => ![0, v 0, -(v 0)]
      map_add' := by
        intro v w
        ext i
        fin_cases i <;> simp [Pi.add_apply, add_comm]
      map_smul' := by
        intro c v
        ext i
        fin_cases i <;> simp [Pi.smul_apply] }

private def traceLift (b : Bool) (R : Type u) [CommRing R] :
    (TraceIndex.{u} b → R) →ₗ[R] Model R where
  toFun v :=
    (diagonalLift R b (fun i => v ⟨.inl i⟩), fun i =>
      (Zorn.pairedFunctions R).symm (fun j => v ⟨.inr (i, j)⟩))
  map_add' v w := by
    apply Prod.ext
    · exact (diagonalLift R b).map_add _ _
    · funext i
      exact (Zorn.pairedFunctions R).symm.map_add _ _
  map_smul' c v := by
    apply Prod.ext
    · exact (diagonalLift R b).map_smul _ _
    · funext i
      exact (Zorn.pairedFunctions R).symm.map_smul _ _

private theorem trace_eq (x : Model R) : traceMap R x = x.1 0 + x.1 1 + x.1 2 := by
  rw [linearTrace_apply, Fin.sum_univ_three]

private theorem trace_unit : traceMap R (cubicUnit : Model R) = 3 := by
  rw [trace_eq]
  change (1 : R) + 1 + 1 = 3
  norm_num

private theorem traceLift_mem (b : Bool) (v : TraceIndex.{u} b → R) :
    traceLift b R v ∈ traceZero R := by
  rw [LinearMap.mem_ker, trace_eq]
  cases b <;> simp [traceLift, diagonalLift]

private theorem projection_lift (b : Bool) (v : TraceIndex.{u} b → R) :
    traceProjection b R (traceLift b R v) = v := by
  funext i
  rcases i with ⟨j | ⟨j, l⟩⟩
  · cases b <;> fin_cases j <;>
      simp [traceProjection, traceLift, diagonalProjection, diagonalLift]
  · exact congrFun ((Zorn.pairedFunctions R).apply_symm_apply _) l

private theorem projection_map (b : Bool) (f : R →+* S) (x : Model R) :
    traceProjection b S (mapModel f x) = f ∘ traceProjection b R x := by
  funext i
  rcases i with ⟨j | ⟨j, l⟩⟩
  · cases b
    · rfl
    · exact (map_sub f (x.1 1) (x.1 0)).symm
  · exact pairedFunctions_map f (x.2 j) l

private theorem lift_map (b : Bool) (f : R →+* S) (v : TraceIndex.{u} b → R) :
    mapModel f (traceLift b R v) = traceLift b S (f ∘ v) := by
  apply Prod.ext
  · funext i
    cases b <;> fin_cases i <;>
      simp [traceLift, diagonalLift, mapModel, Function.comp_def, map_add]
  · funext i
    apply (Zorn.pairedFunctions S).injective
    funext j
    change Zorn.pairedFunctions S (Composition.ZornSpecification.mapCoordinates f
      ((Zorn.pairedFunctions R).symm fun l => v ⟨.inr (i, l)⟩)) j = _
    rw [pairedFunctions_map, LinearEquiv.apply_symm_apply]
    change f (v ⟨.inr (i, j)⟩) =
      Zorn.pairedFunctions S ((Zorn.pairedFunctions S).symm
        (fun l : ZornIndex => f (v ⟨.inr (i, l)⟩))) j
    rw [LinearEquiv.apply_symm_apply]

private theorem lift_projection_diff (b : Bool) (h₃ : b = true → (3 : R) = 0)
    {x : Model R} (hx : x ∈ traceZero R) :
    x - traceLift b R (traceProjection b R x) =
      (if b then x.1 0 else 0) • (cubicUnit : Model R) := by
  have ht := (LinearMap.mem_ker.mp hx : traceMap R x = 0)
  rw [trace_eq] at ht
  apply Prod.ext
  · cases b
    · funext i
      fin_cases i
      · change x.1 0 - x.1 0 = (0 : R) * 1
        simp
      · change x.1 1 - x.1 1 = (0 : R) * 1
        simp
      · change x.1 2 - (-(x.1 0 + x.1 1)) = (0 : R) * 1
        linear_combination ht
    · have h := h₃ rfl
      funext i
      fin_cases i
      · change x.1 0 - 0 = x.1 0 * 1
        simp
      · change x.1 1 - (x.1 1 - x.1 0) = x.1 0 * 1
        ring
      · change x.1 2 - (-(x.1 1 - x.1 0)) = x.1 0 * 1
        linear_combination ht - x.1 0 * h
  · funext i
    change x.2 i - (Zorn.pairedFunctions R).symm (Zorn.pairedFunctions R (x.2 i)) = _
    rw [LinearEquiv.symm_apply_apply, sub_self]
    change 0 = (if b then x.1 0 else 0) • (0 : Zorn R)
    rw [smul_zero]

private theorem projection_kernel (b : Bool)
    (h₃ : b = true → (3 : R) = 0) (hu : b = false → IsUnit (3 : R))
    {x : Model R} (hx : x ∈ traceZero R) :
    traceProjection b R x = 0 ↔ x ∈ scalarLine R ⊓ traceZero R := by
  constructor
  · intro hp
    refine ⟨Submodule.mem_span_singleton.mpr ⟨if b then x.1 0 else 0, ?_⟩, hx⟩
    simpa [hp] using (lift_projection_diff b h₃ hx).symm
  · intro h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h.1
    cases b
    · have ht := (LinearMap.mem_ker.mp hx : traceMap R (c • cubicUnit) = 0)
      rw [map_smul, trace_unit, smul_eq_mul, ← zero_mul (3 : R), (hu rfl).mul_left_inj] at ht
      simp [ht]
    · funext i
      rcases i with ⟨j | ⟨j, l⟩⟩
      · change c * 1 - c * 1 = 0
        simp
      · change Zorn.pairedFunctions R (c • (0 : Zorn R)) l = 0
        simp

end Coordinates

section Field

variable {k : Type u} [Field k]

private theorem three_zero (R : TestAlgebra k) (h : characteristicThree k = true) :
    (3 : R) = 0 := by
  classical
  have hk : (3 : k) = 0 := by simpa [characteristicThree] using h
  simpa only [map_ofNat, map_zero] using congrArg (algebraMap k R) hk

private theorem three_unit (R : TestAlgebra k) (h : characteristicThree k = false) :
    IsUnit (3 : R) := by
  classical
  have hk : (3 : k) ≠ 0 := by simpa [characteristicThree] using h
  simpa only [map_ofNat] using hk.isUnit.map (algebraMap k R)

theorem traceCoordinates : TraceCoordinatesType.{u} := by
  intro k _
  refine ⟨fun R => ⟨?_, fun x hx => projection_kernel _ (three_zero R) (three_unit R) hx⟩,
    fun f x => projection_map _ f.hom.toRingHom x⟩
  intro v
  exact ⟨⟨traceLift _ R v, traceLift_mem _ v⟩, projection_lift _ v⟩

end Field

section Representation

variable {k : Type u} [Field k] {G : GroupScheme k}
variable (a : SplitAction G)

private theorem isSplitAction (R : TestAlgebra k) (g : Points G.X R) :
    IsSplitAutomorphism (a.action R g) := by
  have h : a.action R g ∈ Set.range (a.action R) := ⟨g, rfl⟩
  rwa [a.image R] at h

private theorem action_mem_traceZero (R : TestAlgebra k) (g : Points G.X R)
    {x : Model R} (hx : x ∈ traceZero R) :
    a.action R g x ∈ traceZero R := by
  change IdempotentSpecification.trace (a.action R g x) = 0
  rw [(splitAuto_preserves _ (isSplitAction a R g)).1 x]
  exact hx

private theorem projection_action (R : TestAlgebra k) (g : Points G.X R)
    {x : Model R} (hx : x ∈ traceZero R) :
    traceProjection (characteristicThree k) R
        (a.action R g (traceLift (characteristicThree k) R
          (traceProjection (characteristicThree k) R x))) =
      traceProjection (characteristicThree k) R (a.action R g x) := by
  let b := characteristicThree k
  let y := traceLift b R (traceProjection b R x)
  have hs := lift_projection_diff b (three_zero R) hx
  have hd : a.action R g x - a.action R g y ∈ scalarLine R ⊓ traceZero R := by
    refine ⟨?_, Submodule.sub_mem _ (action_mem_traceZero a R g hx)
      (action_mem_traceZero a R g (traceLift_mem b _))⟩
    refine Submodule.mem_span_singleton.mpr ⟨if b then x.1 0 else 0, ?_⟩
    rw [← map_sub, show x - y = _ from hs, map_smul, (isSplitAction a R g).1]
  have he := (projection_kernel b (three_zero R) (three_unit R) hd.2).2 hd
  rw [map_sub, sub_eq_zero] at he
  exact he.symm

private def traceAction (R : TestAlgebra k) :
    Points G.X R →* Module.End R (TraceIndex.{u} (characteristicThree k) → R) where
  toFun g := (traceProjection (characteristicThree k) R).comp
    ((a.action R g).toLinearMap.comp (traceLift (characteristicThree k) R))
  map_one' := by
    apply LinearMap.ext
    intro v
    change traceProjection (characteristicThree k) R
      (a.action R 1 (traceLift (characteristicThree k) R v)) = v
    rw [map_one]
    exact projection_lift _ v
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change traceProjection (characteristicThree k) R
        (a.action R (g * h) (traceLift (characteristicThree k) R v)) =
      traceProjection (characteristicThree k) R (a.action R g
        (traceLift (characteristicThree k) R (traceProjection (characteristicThree k) R
          (a.action R h (traceLift (characteristicThree k) R v)))))
    rw [map_mul]
    exact (projection_action a R g (action_mem_traceZero a R h (traceLift_mem _ v))).symm

private def traceMatrices (R : TestAlgebra k) :
    Points G.X R →* Matrix.GeneralLinearGroup (TraceIndex.{u} (characteristicThree k)) R :=
  Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp (traceAction a R).toHomUnits

private theorem traceMatrices_apply (R : TestAlgebra k) (g : Points G.X R)
    (v : TraceIndex.{u} (characteristicThree k) → R) :
    (traceMatrices a R g).val *ᵥ v =
      traceProjection (characteristicThree k) R
        (a.action R g (traceLift (characteristicThree k) R v)) := by
  change (traceMatrices a R g).val.mulVecLin v = _
  rw [← Matrix.GeneralLinearGroup.toLin_apply]
  change ((Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm
    ((traceAction a R).toHomUnits g))).val : Module.End R _) v = _
  rw [MulEquiv.apply_symm_apply]
  rfl

private theorem traceMatrices_action (R : TestAlgebra k) (g : Points G.X R)
    {x : Model R} (hx : x ∈ traceZero R) :
    (traceMatrices a R g).val *ᵥ traceProjection (characteristicThree k) R x =
      traceProjection (characteristicThree k) R (a.action R g x) :=
  (traceMatrices_apply a R g _).trans (projection_action a R g hx)

private def tracePointRepresentation :
    (groupPointsFunctor k).obj G ⟶
      Specs.StandardGroups.generalLinearPoints k (TraceIndex.{u} (characteristicThree k)) where
  app R := GrpCat.ofHom (traceMatrices a R)
  naturality {R S} f := by
    classical
    apply GrpCat.ext
    intro g
    apply Units.ext
    ext i j
    change (traceMatrices a S (mapPoints f g)).val i j = f.hom ((traceMatrices a R g).val i j)
    let b := characteristicThree k
    let v : TraceIndex.{u} b → R := Pi.single j 1
    have hv : f.hom.toRingHom ∘ v = Pi.single j (1 : S) := by
      funext l
      by_cases h : l = j <;> simp [v, h]
    have e (T : TestAlgebra k) (p : Points G.X T) :
        ((traceMatrices a T p).val *ᵥ Pi.single j 1) i =
          (traceMatrices a T p).val i j := by
      rw [Matrix.mulVec_single_one, Matrix.col_apply]
    rw [← e S, ← e R, traceMatrices_apply, traceMatrices_apply]
    have h := a.natural f g (traceLift b R v)
    rw [lift_map, hv] at h
    rw [← h, projection_map]
    rfl

theorem traceRepresentation : TraceRepresentation.{u} := by
  intro k _ G a
  let I := TraceIndex.{u} (characteristicThree k)
  let L := (StandardGroups.generalLinearGroup k I).val
  let e := StandardGroups.generalLinearGroupPointsIso k I
  obtain ⟨ρ, hρ⟩ := (groupHomComparison k G.val L G.property.1).surjective
    (tracePointRepresentation a ≫ e.inv)
  change (groupPointsFunctor k).map ρ = _ at hρ
  refine ⟨L, e, ρ, fun R g x hx => ?_⟩
  have h : (groupPointsFunctor k).map ρ ≫ e.hom = tracePointRepresentation a := by
    rw [hρ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hg := DFunLike.congr_fun (congrArg (fun τ => (τ.app R).hom) h) g
  change e.hom.app R (((groupPointsFunctor k).map ρ).app R g) = traceMatrices a R g at hg
  rw [hg]
  exact traceMatrices_action a R g hx

end Representation

section Reductivity

open LinearAlgebraicGroups.RationalRepresentations
open Specs.GeometricRadicals (GeometricGroup geometricUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup HasInvariantVectors)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency true in
private def baseChangedAction {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme k} (a : SplitAction G) : SplitAction ((groupBaseChange k K).obj G) where
  action R := (a.action ((restrictTestAlgebra k K).obj R)).comp
    (baseChangePointGroupEquiv K G R).toMonoidHom
  injective R := by
    intro p q h
    apply (baseChangePointGroupEquiv K G R).injective
    exact a.injective ((restrictTestAlgebra k K).obj R) h
  image R := by
    let e := baseChangePointGroupEquiv K G R
    let f := a.action ((restrictTestAlgebra k K).obj R)
    calc
      Set.range (f ∘ e) = Set.range f := by
        rw [Set.range_comp, e.surjective.range_eq, Set.image_univ]
      _ = _ := a.image ((restrictTestAlgebra k K).obj R)
  natural {R S} f p x := by
    let eR := baseChangePointGroupEquiv K G R
    let eS := baseChangePointGroupEquiv K G S
    change mapModel f.hom.toRingHom (a.action ((restrictTestAlgebra k K).obj R) (eR p) x) =
      a.action ((restrictTestAlgebra k K).obj S) (eS (mapPoints f p)) (mapModel f.hom.toRingHom x)
    have h : eS (mapPoints f p) =
        mapPoints ((restrictTestAlgebra k K).map f) (eR p) :=
      baseChangePointsNaturality k K G.X f p
    rw [h]
    exact a.natural ((restrictTestAlgebra k K).map f) (eR p) x

/-- A nonzero vector of a matrix representation of a unipotent group is fixed
by every rational point, by evaluating a coaction invariant. -/
private theorem unipotent_fixed_vector {K I : Type u} [Field K] [Fintype I]
    [DecidableEq I] [Nonempty I] (A : HopfAlgebraCategory K) (hU : HasInvariantVectors A)
    (α : convolutionPoints A ⟶ Specs.StandardGroups.generalLinearPoints K I) :
    ∃ x : I → K, x ≠ 0 ∧ ∀ p : (convolutionPoints A).obj (CommAlgCat.of K K),
      (α.app (CommAlgCat.of K K) p).val *ᵥ x = x := by
  let V := I → K
  let b := Pi.basisFun K I
  let C := pointMatrix A α
  let ρ := coactionOfMatrix A b C (pointMatrix_isCoactionMatrix A α)
  obtain ⟨x, hx, hρ⟩ := hU V ρ
  refine ⟨x, hx, fun p => ?_⟩
  let M := (α.app (CommAlgCat.of K K) p).val
  have hM : M = C.map p.ofConv := pointMatrix_evaluation A α _ p
  have he : M.mulVecLin =
      (TensorProduct.rid K V).toLinearMap.comp (evaluate A ρ p.ofConv) := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
    unfold evaluate
    rw [LinearMap.comp_apply, coaction_apply_basis A b ρ, coefficients_coactionOfMatrix]
    ext i
    simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    have hb (l : I) : b l = Pi.single l (1 : K) := Pi.basisFun_apply _ _ _
    simp only [hb]
    change (M *ᵥ Pi.single j 1) i = (∑ l : I, p.ofConv (C l j) • Pi.single l 1) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, hM, Matrix.map_apply, Finset.sum_apply]
    simp [Pi.smul_apply, Pi.single_apply]
  change M.mulVecLin x = x
  rw [he, LinearMap.comp_apply, LinearEquiv.coe_coe]
  unfold evaluate
  rw [LinearMap.comp_apply, (invariant_iff_coaction A ρ x).mp hρ,
    LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_one, TensorProduct.rid_tmul, one_smul]

set_option maxHeartbeats 2000000 in
theorem reductivity : Reductivity.{u} := by
  intro k _ G a hs hc hi hf
  classical
  refine ⟨hs, hc, ?_⟩
  let K := AlgebraicClosure k
  let R := CommAlgCat.of K K
  let B := GeometricGroup G
  let N := geometricUnipotentRadical G
  let aK : SplitAction B.val := baseChangedAction (K := K) a
  let b := characteristicThree K
  let I := TraceIndex.{u} b
  let V := I → K
  let π := traceProjection b K
  let act := traceAction aK R
  let inc : Points N.group.X R → Points B.val.X R := fun n => n ≫ N.inclusion.hom.hom
  have hN := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G
  obtain ⟨A, ⟨e⟩, hU⟩ := hN.2.1
  let β := hopfSpecPointIso A ≪≫ (groupPointsFunctor K).mapIso e
  let α := β.hom ≫ (groupPointsFunctor K).map N.inclusion ≫ tracePointRepresentation aK
  have : Nonempty I := ⟨⟨.inr (0, .inl none)⟩⟩
  obtain ⟨x, hx, hfix⟩ := unipotent_fixed_vector A hU α
  let W : Submodule K V :=
    { carrier := {v | ∀ n, act (inc n) v = v}
      zero_mem' n := map_zero _
      add_mem' hv hw n := by rw [map_add, hv n, hw n]
      smul_mem' := by
        intro c v hv n
        change act (inc n) (c • v) = c • v
        rw [map_smul, hv n] }
  have hxW : x ∈ W := by
    intro n
    let eR := (β.app R).groupIsoToMulEquiv
    have he : β.hom.app R (eR.symm n) = n := eR.apply_symm_apply n
    have h := hfix (eR.symm n)
    change (traceMatrices aK R (inc (β.hom.app R (eR.symm n)))).val *ᵥ x = x at h
    rw [he, traceMatrices_apply] at h
    exact h
  have hstable (g : Points B.val.X R) {v : V} (hv : v ∈ W) : act g v ∈ W := by
    intro n
    have hn := sections_normal hN.1.2.2 ((testSpec K).obj (op R))
    obtain ⟨m, hm⟩ := hn.conj_mem (inc n) ⟨n, rfl⟩ g⁻¹
    have hmul : inc n * g = g * inc m := by
      change inc m = g⁻¹ * inc n * (g⁻¹)⁻¹ at hm
      rw [hm, inv_inv, ← mul_assoc, mul_inv_cancel_left]
    change (act (inc n) * act g) v = act g v
    rw [← map_mul, hmul, map_mul]
    change act g (act (inc m) v) = act g v
    rw [hv m]
  let P : Submodule K (Model K) := traceZero K ⊓ W.comap π
  have hPlo : scalarLine K ⊓ traceZero K ≤ P := by
    intro y hy
    refine ⟨hy.2, ?_⟩
    change π y ∈ W
    change traceProjection b R y ∈ W
    rw [(projection_kernel b (three_zero R) (three_unit R) hy.2).2 hy]
    exact W.zero_mem
  have hPstable : IsInvariant P := by
    intro g hg y hy
    have hga : g ∈ Set.range (aK.action R) := by rw [aK.image]; exact hg
    obtain ⟨p, rfl⟩ := hga
    refine ⟨action_mem_traceZero aK R p hy.1, ?_⟩
    change π (aK.action R p y) ∈ W
    have hp : act p (π y) = π (aK.action R p y) :=
      projection_action aK R p hy.1
    rw [← hp]
    exact hstable p hy.2
  have hPt : P = traceZero K := by
    refine ((hi K).2 P hPlo inf_le_left hPstable).resolve_left ?_
    intro h
    let y := traceLift b R x
    have hy : y ∈ traceZero K := traceLift_mem b x
    have hp : π y = x := projection_lift b x
    have hyP : y ∈ P := by
      refine ⟨hy, ?_⟩
      change π y ∈ W
      rwa [hp]
    rw [h] at hyP
    exact hx (hp.symm.trans ((projection_kernel b (three_zero R) (three_unit R) hy).2 hyP))
  have htriv (n : Points N.group.X R) : aK.action R (inc n) = 1 := by
    apply hf K _ (isSplitAction aK R (inc n))
    intro y hy
    have hyP : y ∈ P := hPt.symm ▸ hy
    have hyW : π y ∈ W := hyP.2
    have hp := (projection_action aK R (inc n) hy).symm.trans (hyW n)
    have hd : aK.action R (inc n) y - y ∈ traceZero K :=
      Submodule.sub_mem _ (action_mem_traceZero aK R (inc n) hy) hy
    apply (projection_kernel b (three_zero R) (three_unit R) hd).1
    rw [map_sub, hp, sub_self]
  have hMono : Mono N.inclusion.hom.hom := by
    have := N.isClosedImmersion
    exact Over.mono_of_mono_left _
  have hsub : Subsingleton (Points N.group.X R) := ⟨fun n m => by
    apply (cancel_mono N.inclusion.hom.hom).mp
    apply aK.injective R
    exact (htriv n).trans (htriv m).symm⟩
  exact trivial_of_finite_rational_points (closedSubgroupAlgebraicGroup N)
    hN.1.1 hN.1.2.1 (@Finite.of_subsingleton _ hsub)

end Reductivity

end
end LinearAlgebraicGroups.Albert.ReductiveFibers
