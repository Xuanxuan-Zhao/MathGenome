import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.IntegralSmoothness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.GeometricFiberGeometry
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IdempotentCharts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntegralSmoothPropagation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ReductiveFibers
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Albert.IntegralSmoothness

open IntegralSmoothnessSpecification
open ReductiveFiberSpecification (traceMap traceZero scalarLine IsInvariant)
open IdempotentSpecification (trace adjoint IsSplitAutomorphism)
open TrialitySpecification (Model modelOp)
open FrameSpecification (frameAxis)
open HermitianSpecification (cyclicNext cyclicPrev)
open IntegralZornDirectionsSpecification (DirectionIndex direction)
open _root_.LinearAlgebraicGroups.Composition (Zorn)
open Composition.ZornSpecification (norm)
set_option backward.isDefEq.respectTransparency false

open private splitAuto_preserves from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IdempotentCharts

theorem traceZeroInvariant : TraceZeroInvariantType := by
  intro k _ g hg x hx
  change trace (g x) = 0
  rw [(splitAuto_preserves g hg).1 x]
  exact hx

section PointKernel

variable {k : Type} [Field k]

private lemma trace_unit : traceMap k cubicUnit = 3 := by
  rw [linearTrace_apply]
  norm_num [CubicSpecification.cubicUnit, Fin.sum_univ_three]

private lemma exists_scalar {x : Model k} (h : x ∈ scalarLine k) :
    ∃ a : k, a • cubicUnit = x :=
  Submodule.mem_span_singleton.mp h

theorem scalarLineIntersection : ScalarLineIntersectionType := by
  intro k _
  constructor
  · intro h₃
    apply inf_eq_left.mpr
    intro x hx
    obtain ⟨a, rfl⟩ := exists_scalar hx
    change traceMap k (a • cubicUnit) = 0
    rw [LinearMap.map_smul, trace_unit, h₃, smul_zero]
  · intro h₃
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨a, ha⟩ := exists_scalar hx.1
    have ht : traceMap k x = 0 := hx.2
    rw [← ha, LinearMap.map_smul, trace_unit, smul_eq_mul, mul_eq_zero] at ht
    rw [← ha, ht.resolve_right h₃, zero_smul]
    exact Submodule.zero_mem _

private lemma block_trace (i : Fin 3) (c : Zorn k) :
    trace (singleBlockCoordinates i c) = 0 := by
  change traceMap k (singleBlockCoordinates i c) = 0
  rw [linearTrace_apply]
  simp [CubicSpecification.singleBlockCoordinates]

private lemma direction_norm (j : DirectionIndex) : norm k (direction k j) = 0 := by
  rw [Zorn.norm_formula]
  rcases j with (_ | j) | (_ | j) <;>
    simp [direction, Composition.ZornSpecification.first, Composition.ZornSpecification.second,
      Composition.Specification.zornNorm]

private lemma block_adjoint (i : Fin 3) (c : Zorn k) :
    adjoint (singleBlockCoordinates i c) =
      diagonalCoordinates (Pi.single i (-norm k c)) := by
  have h := (cubic_single_block_formulas (n := norm k) (fun _ => 1) i c).2.1
  simpa [CubicSpecification.blockWeight] using h

private lemma adjoint_shift (x : Model k) (a : k) (hx : trace x = 0) :
    adjoint (x + a • cubicUnit) = adjoint x - a • x + (a * a) • cubicUnit := by
  have hc : adjointCross (norm k) (fun _ => 1) x cubicUnit =
      trace x • cubicUnit - x := by
    have hsym : adjointCross (norm k) (fun _ => 1) x cubicUnit =
        adjointCross (norm k) (fun _ => 1) cubicUnit x := by
      simp only [CubicSpecification.adjointCross, add_comm x cubicUnit]
      abel
    rw [hsym]
    exact (cubic_unit_identities (n := norm k) (fun _ => 1)).2.2 x
  have hu : adjoint (R := k) cubicUnit = cubicUnit :=
    (cubic_unit_identities (n := norm k) (fun _ => 1)).2.1
  have h := cubicAdjoint_add_smul (n := norm k) (fun _ => 1) x cubicUnit a
  change adjoint (x + a • cubicUnit) = adjoint x +
    a • adjointCross (norm k) (fun _ => 1) x cubicUnit + (a * a) • adjoint cubicUnit at h
  rw [hc, hx, zero_smul, zero_sub, hu, smul_neg] at h
  simpa only [sub_eq_add_neg] using h

private lemma block_square (i : Fin 3) (c : Zorn k) :
    modelOp (singleBlockCoordinates i c) cubicUnit =
      norm k c • (cubicUnit - frameAxis i) := by
  have H := (cubic_operator_identities (fun _ : Fin 3 => 1) (Zorn.isOctonion k)).2.2.2.2.2.2.2.2.1
    (singleBlockCoordinates i c)
  have hs : quadraticTrace (norm k) (fun _ => 1) (singleBlockCoordinates i c) = -norm k c := by
    change traceMap k (adjoint (singleBlockCoordinates i c)) = _
    rw [block_adjoint, linearTrace_apply]
    simp [CubicSpecification.diagonalCoordinates, Pi.single_apply, Finset.sum_ite_eq']
  change modelOp (singleBlockCoordinates i c) cubicUnit =
    adjoint (singleBlockCoordinates i c) + trace (singleBlockCoordinates i c) •
      singleBlockCoordinates i c - quadraticTrace (norm k) (fun _ => 1)
        (singleBlockCoordinates i c) • cubicUnit at H
  rw [block_adjoint, block_trace, hs, zero_smul, add_zero] at H
  rw [H]
  apply Prod.ext
  · funext j
    by_cases h : j = i
    · subst j
      simp [CubicSpecification.diagonalCoordinates, CubicSpecification.cubicUnit,
        FrameSpecification.frameAxis]
    · simp [CubicSpecification.diagonalCoordinates, CubicSpecification.cubicUnit,
        FrameSpecification.frameAxis, h]
  · simp [CubicSpecification.diagonalCoordinates, CubicSpecification.cubicUnit, FrameSpecification.frameAxis]

private def insertBlock (i : Fin 3) : Zorn k →ₗ[k] Model k where
  toFun := singleBlockCoordinates i
  map_add' _ _ := by simp [CubicSpecification.singleBlockCoordinates, Pi.single_add]
  map_smul' _ _ := by simp [CubicSpecification.singleBlockCoordinates, Pi.single_smul]

theorem geometricPointKernel : GeometricPointKernelType := by
  intro k _ g hg h
  by_cases h₃ : (3 : k) = 0
  · have hfix (i : Fin 3) (j : DirectionIndex) :
        g (singleBlockCoordinates i (direction k j)) = singleBlockCoordinates i (direction k j) := by
      let x : Model k := singleBlockCoordinates i (direction k j)
      have ht : trace x = 0 := block_trace i _
      have ha : adjoint x = 0 := by
        dsimp only [x]
        rw [block_adjoint, direction_norm, neg_zero, Pi.single_zero]
        rfl
      obtain ⟨a, ea⟩ := exists_scalar (h x ht).1
      have eg : g x = x + a • cubicUnit := by
        exact (sub_eq_iff_eq_add.mp ea.symm).trans (add_comm _ _)
      have hh : adjoint (x + a • cubicUnit) = 0 := by
        rw [← eg, (splitAuto_preserves g hg).2 x, ha, map_zero]
      rw [adjoint_shift x a ht, ha, zero_sub] at hh
      have hz : a * a = 0 := by
        have H := congrArg (fun y : Model k => y.1 0) hh
        change -(a * 0) + a * a * 1 = 0 at H
        simpa only [mul_zero, neg_zero, zero_add, mul_one] using H
      rw [eg, (mul_eq_zero.mp hz).elim id id, zero_smul, add_zero]
    have hblocks (i : Fin 3) (c : Zorn k) : g (singleBlockCoordinates i c) = singleBlockCoordinates i c := by
      have he : g.toLinearMap.comp (insertBlock i) = insertBlock i := by
        apply (IntegralZornDirections.directionBasis k).ext
        intro j
        rw [IntegralZornDirections.directionBasis_apply]
        exact hfix i j
      exact DFunLike.congr_fun he c
    have haxes (i : Fin 3) : g (frameAxis i) = frameAxis i := by
      have hh := hg.2 (singleBlockCoordinates i (1 : Zorn k)) cubicUnit
      rw [hg.1, hblocks, block_square, Zorn.norm_one, one_smul, map_sub, hg.1] at hh
      exact (sub_right_inj.mp hh)
    have he : g.toLinearMap = LinearMap.id := by
      apply ((Pi.basisFun k (Fin 3)).prod
        (Pi.basis fun _ : Fin 3 => IntegralZornDirections.directionBasis k)).ext
      intro j
      rcases j with i | ⟨i, j⟩
      · rw [Module.Basis.prod_apply, Sum.elim_inl, Function.comp_apply, Pi.basisFun_apply,
          LinearMap.inl_apply, LinearMap.id_apply]
        exact haxes i
      · rw [Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply, Pi.basis_apply,
          LinearMap.inr_apply, LinearMap.id_apply, IntegralZornDirections.directionBasis_apply]
        exact hfix i j
    exact LinearEquiv.toLinearMap_injective he
  · have hzero (x : Model k) (hx : trace x = 0) : g x = x := by
      obtain ⟨a, ha⟩ := exists_scalar (h x hx).1
      have ht : traceMap k (g x - x) = 0 := (h x hx).2
      rw [← ha, LinearMap.map_smul, trace_unit, smul_eq_mul, mul_eq_zero] at ht
      apply sub_eq_zero.mp
      rw [← ha, ht.resolve_right h₃, zero_smul]
    apply LinearEquiv.ext
    intro x
    change g x = x
    let a : k := trace x / 3
    have ht : traceMap k (x - a • cubicUnit) = 0 := by
      rw [map_sub, LinearMap.map_smul, trace_unit, smul_eq_mul, div_mul_cancel₀ _ h₃, sub_self]
    have he := hzero (x - a • cubicUnit) ht
    rw [map_sub, map_smul, hg.1] at he
    exact sub_left_inj.mp he

end PointKernel

section Representation

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open TrialitySpecification (mapModel)
open ShortDirectionSpecification (IntegralPresentation)

open private algebraGroupPresheaf quotientRepresentation groupSpecFunctor groupSpecPointIso
  quotientMatrixEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme
open private albertMatrix albertMatrix_apply albertPoints albertPoints_natural coordinateFinitePresentation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections

noncomputable section

variable (P : IntegralPresentation)

private abbrev coordinateObject := op (CommAlgCat.of ℤ P.Coordinates)

local instance : GrpObj (coordinateObject P) :=
  GrpObj.ofRepresentableBy _ (algebraGroupPresheaf P.subgroup) (quotientRepresentation P.cutsOut)

private def coordinateGroup : Grp (CommAlgCat ℤ)ᵒᵖ :=
  Grp.mk (coordinateObject P)

private abbrev representedGroup : SpinSpecification.GroupScheme ℤ :=
  (groupSpecFunctor ℤ).obj (coordinateGroup P)

private def representedMatrixPoints (S : CommAlgCat ℤ) :
    SpinSpecification.SchemePoints (representedGroup P) S ≃* P.subgroup.subgroup S :=
  let e := groupSpecPointIso (coordinateGroup P) ≪≫ Functor.isoWhiskerLeft (opOp _)
    (yonedaGrpObjIsoOfRepresentableBy _ (algebraGroupPresheaf P.subgroup)
      (quotientRepresentation P.cutsOut))
  (e.app S).groupIsoToMulEquiv

private lemma representedMatrixPoints_eval (S : CommAlgCat ℤ) (f : P.Coordinates →ₐ[ℤ] S) :
    representedMatrixPoints P S ((algSpec (CommRingCat.of ℤ)).map (CommAlgCat.ofHom f).op) =
      quotientMatrixEquiv P.cutsOut f := by
  change (quotientRepresentation P.cutsOut).homEquiv
      ((algSpec.fullyFaithful (R := CommRingCat.of ℤ)).preimage
        ((algSpec (CommRingCat.of ℤ)).map (CommAlgCat.ofHom f).op)) = _
  rw [Functor.FullyFaithful.preimage_map]
  rfl

private def representedAction (S : CommAlgCat ℤ) :
    SpinSpecification.SchemePoints (representedGroup P) S →* (Model S ≃ₗ[S] Model S) :=
  (albertMatrix P S).toMonoidHom.comp
    ((P.subgroup.subgroup S).subtype.comp (representedMatrixPoints P S).toMonoidHom)

private lemma representedAction_eval (S : CommAlgCat ℤ) (f : P.Coordinates →ₐ[ℤ] S) :
    representedAction P S ((algSpec (CommRingCat.of ℤ)).map (CommAlgCat.ofHom f).op) =
      (albertPoints P S f).val := by
  change albertMatrix P S (representedMatrixPoints P S
    ((algSpec (CommRingCat.of ℤ)).map (CommAlgCat.ofHom f).op)).val = _
  rw [representedMatrixPoints_eval]
  rfl

private lemma exists_coordinateMap (S : CommAlgCat ℤ)
    (g : SpinSpecification.SchemePoints (representedGroup P) S) :
    ∃ f : P.Coordinates →ₐ[ℤ] S,
      (algSpec (CommRingCat.of ℤ)).map (CommAlgCat.ofHom f).op = g := by
  obtain ⟨f, hf⟩ := (algSpec.fullyFaithful (R := CommRingCat.of ℤ)).map_surjective g
  exact ⟨f.unop.hom, hf⟩

open private mem_splitAutomorphisms from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections

set_option maxRecDepth 1024 in
theorem integralRepresentation : IntegralRepresentationType := by
  intro P
  refine ⟨⟨representedGroup P, Iso.refl _, ?_, ?_, representedAction P, ?_, ?_, ?_, ?_⟩⟩
  · change IsAffine (Spec (CommRingCat.of P.Coordinates))
    infer_instance
  · change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap ℤ P.Coordinates)))
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.finitePresentation_algebraMap.mpr (coordinateFinitePresentation P)
  · intro S
    exact (albertMatrix P S).injective.comp
      (Subtype.val_injective.comp (representedMatrixPoints P S).injective)
  · intro S
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨f, rfl⟩ := exists_coordinateMap P S g
      rw [representedAction_eval]
      exact (mem_splitAutomorphisms _).mp (albertPoints P S f).property
    · intro hx
      have h := (mem_splitAutomorphisms x).mpr hx
      obtain ⟨f, hf⟩ := (albertPoints P S).surjective ⟨x, h⟩
      refine ⟨(algSpec (CommRingCat.of ℤ)).map (CommAlgCat.ofHom f).op, ?_⟩
      rw [representedAction_eval, hf]
  · intro S T f g x
    obtain ⟨a, rfl⟩ := exists_coordinateMap P S g
    rw [← Functor.map_comp, representedAction_eval]
    change mapModel f.hom.toRingHom ((albertPoints P S a).val x) =
      representedAction P T
        ((algSpec (CommRingCat.of ℤ)).map (CommAlgCat.ofHom (f.hom.comp a)).op)
        (mapModel f.hom.toRingHom x)
    rw [representedAction_eval]
    exact albertPoints_natural P f.hom a x
  · intro S g
    obtain ⟨a, rfl⟩ := exists_coordinateMap P S g
    refine ⟨a, (Category.comp_id _).symm, (quotientMatrixEquiv P.cutsOut a).val, fun _ _ => rfl, ?_⟩
    intro x
    rw [representedAction_eval]
    exact albertMatrix_apply P _ x

theorem integralIdentityCharts : IntegralIdentityChartsType := by
  obtain ⟨P, e, he, hcharts⟩ := ShortDirections.integralSmoothIdentity
  obtain ⟨G⟩ := integralRepresentation P
  refine ⟨P, G, e, he, ?_, hcharts⟩
  let S := CommAlgCat.of ℤ ℤ
  let p : SpinSpecification.SchemePoints G.group S :=
    (algSpec (CommRingCat.of ℤ)).map (CommAlgCat.ofHom e).op ≫ G.coordinates.inv
  have hp : p ≫ G.coordinates.hom = (algSpec (CommRingCat.of ℤ)).map (CommAlgCat.ofHom e).op := by
    simp [p]
  obtain ⟨a, ha, m, hm, hsep⟩ := G.matrixCoordinates S p
  have hae : a = e := by
    have h := (algSpec.fullyFaithful (R := CommRingCat.of ℤ)).map_injective (ha.trans hp)
    exact congrArg (fun g => g.unop.hom) h
  subst a
  have hm₁ : m = 1 := Matrix.GeneralLinearGroup.ext fun i j => (hm i j).trans (he i j)
  have hone : p = 1 := by
    apply G.injective S
    rw [map_one]
    apply LinearEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := (TrialitySpecification.modelBaseChange ℤ S).surjective y
    rw [hsep, hm₁, ← albertMatrix_apply]
    simp only [map_one]
  exact hp.symm.trans (congrArg (· ≫ G.coordinates.hom) hone)

end
end Representation

section MatrixDirections

open ShortDirectionSpecification (Square ThreeMatrices matrixCoordinates matrixAction)
open ShortDirections (specialLinearAction specialLinearAction_coordinates)
open private slTransvection slTransvection_inv specialLinear_groundIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections

variable {k : Type} [Field k]

private lemma slAction_isAuto (g : Matrix.SpecialLinearGroup (Fin 3) k) :
    IsSplitAutomorphism (specialLinearAction k g) := by
  obtain ⟨J, _, hu, ho, _, _, _, _⟩ := Triality.cubicFrameStabilizer k
  have h := specialLinear_groundIso g J hu ho
  have hunit : (specialLinearAction k g) J.unit = J.unit := h.1
  have hop (x y : Model k) : (specialLinearAction k g) (J.groundOp x y) =
      J.groundOp ((specialLinearAction k g) x) ((specialLinearAction k g) y) := h.2 x y
  exact ⟨by simpa only [hu] using hunit, fun x y => by simpa only [ho] using hop x y⟩

private def matrixUnit (i j : Fin 3) : Square k := Matrix.single i j 1

private def matrixBlock (i j : Fin 3) : ThreeMatrices k := (matrixUnit i j, 0, 0)

private def transvectionLinear (p q : Fin 3) (x : ThreeMatrices k) : ThreeMatrices k :=
  let E : Square k := matrixUnit p q
  (E * x.1 - x.1 * E, E * x.2.1, -(x.2.2 * E))

private def transvectionQuadratic (p q : Fin 3) (x : ThreeMatrices k) : ThreeMatrices k :=
  let E : Square k := matrixUnit p q
  (-(E * x.1 * E), 0, 0)

private lemma transvection_expansion (p q : Fin 3) (hpq : p ≠ q) (t : k)
    (x : ThreeMatrices k) :
    matrixAction (slTransvection p q hpq t) x = x +
      t • transvectionLinear p q x + (t * t) • transvectionQuadratic p q x := by
  rw [matrixAction, slTransvection_inv]
  have h (a : k) : Matrix.transvection p q a = 1 + a • (matrixUnit p q : Square k) := by
    simp [Matrix.transvection, matrixUnit, Matrix.smul_single]
  change (Matrix.transvection p q t * x.1 * Matrix.transvection p q (-t),
    Matrix.transvection p q t * x.2.1, x.2.2 * Matrix.transvection p q (-t)) = _
  rw [h, h]
  apply Prod.ext
  · simp only [transvectionLinear, transvectionQuadratic, Prod.fst_add, Prod.smul_fst,
      add_mul, mul_add, one_mul, mul_one, mul_neg, smul_mul_assoc, mul_smul_comm,
      neg_smul, smul_neg, sub_eq_add_neg]
    module
  · apply Prod.ext <;> simp [transvectionLinear, transvectionQuadratic, add_mul, mul_add, mul_neg]

private lemma stableMatrixAction {W : Submodule k (Model k)} (hW : IsInvariant W)
    (g : Matrix.SpecialLinearGroup (Fin 3) k) (x : ThreeMatrices k)
    (hx : x ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap) :
    matrixAction g x ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨_, hW _ (slAction_isAuto g) y hy, specialLinearAction_coordinates g y⟩

/-- Comparing two nonzero parameter values extracts both nonconstant coefficients.
This uses infinitude of the geometric field and works in characteristic two. -/
private lemma transvection_coefficients [Infinite k] {W : Submodule k (Model k)}
    (hW : IsInvariant W) (p q : Fin 3) (hpq : p ≠ q) (x : ThreeMatrices k)
    (hx : x ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap) :
    transvectionLinear p q x ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap ∧
    transvectionQuadratic p q x ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap := by
  classical
  let V := W.map (ShortDirections.coordinateEquiv k).toLinearMap
  let L := transvectionLinear p q x
  let Q := transvectionQuadratic p q x
  have h (t : k) (ht : t ≠ 0) : L + t • Q ∈ V := by
    have hm := V.sub_mem (stableMatrixAction hW (slTransvection p q hpq t) x hx) hx
    rw [transvection_expansion] at hm
    have he : x + t • L + (t * t) • Q - x = t • (L + t • Q) := by
      rw [smul_add, smul_smul]
      abel
    change x + t • L + (t * t) • Q - x ∈ V at hm
    rw [he] at hm
    rwa [Submodule.smul_mem_iff_of_isUnit _ (isUnit_iff_ne_zero.mpr ht)] at hm
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have ha₀ : a ≠ 0 := fun h => ha (by simp [h])
  have ha₁ : a ≠ 1 := fun h => ha (by simp [h])
  have hsub := V.sub_mem (h a ha₀) (h 1 one_ne_zero)
  have he : L + a • Q - (L + (1 : k) • Q) = (a - 1) • Q := by rw [sub_smul, one_smul]; abel
  have hQ : Q ∈ V := (V.smul_mem_iff_of_isUnit
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ha₁))).mp (he ▸ hsub)
  exact ⟨by simpa only [one_smul, add_sub_cancel_right] using V.sub_mem (h 1 one_ne_zero) hQ,
    hQ⟩

private lemma coeff_quadratic_matrix (p q : Fin 3) (x : ThreeMatrices k) :
    transvectionQuadratic p q x = (-x.1 q p) • matrixBlock p q := by
  simp [transvectionQuadratic, matrixBlock, matrixUnit, Matrix.smul_single, Matrix.single_neg]

private lemma block_from_entry [Infinite k] {W : Submodule k (Model k)}
    (hW : IsInvariant W) (p q : Fin 3) (hpq : p ≠ q) (x : ThreeMatrices k)
    (hx : x ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap) (hentry : x.1 q p ≠ 0) :
    matrixBlock p q ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap := by
  have h := (transvection_coefficients hW p q hpq x hx).2
  rw [coeff_quadratic_matrix,
    Submodule.smul_mem_iff_of_isUnit _ (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hentry))] at h
  exact h

private lemma moveRow [Infinite k] {W : Submodule k (Model k)} (hW : IsInvariant W)
    (p q r : Fin 3) (hrp : r ≠ p) (hrq : r ≠ q)
    (h : matrixBlock p q ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap) :
    matrixBlock r q ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap := by
  have h' := (transvection_coefficients hW r p hrp _ h).1
  convert h' using 1
  have hz : Matrix.single p q (1 : k) * Matrix.single r p 1 = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : k)) p q r (Ne.symm hrq) 1
  simp [transvectionLinear, matrixBlock, matrixUnit, hz]

private lemma moveColumn [Infinite k] {W : Submodule k (Model k)} (hW : IsInvariant W)
    (p q r : Fin 3) (hrq : r ≠ q) (hrp : r ≠ p)
    (h : matrixBlock p q ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap) :
    matrixBlock p r ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap := by
  have h' := (transvection_coefficients hW q r hrq.symm _ h).1
  have he : transvectionLinear q r (matrixBlock p q : ThreeMatrices k) = -matrixBlock p r := by
    have hz : Matrix.single q r (1 : k) * Matrix.single p q 1 = 0 :=
      Matrix.single_mul_single_of_ne (c := (1 : k)) q r p hrp 1
    simp [transvectionLinear, matrixBlock, matrixUnit, hz]
  simpa only [he, Submodule.neg_mem_iff] using h'

private lemma blockTranspose [Infinite k] {W : Submodule k (Model k)}
    (hW : IsInvariant W) (p q : Fin 3) (hpq : p ≠ q)
    (h : matrixBlock p q ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap) :
    matrixBlock q p ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap :=
  block_from_entry hW q p hpq.symm _ h (by simp [matrixBlock, matrixUnit])

private lemma allMatrixBlocks [Infinite k] {W : Submodule k (Model k)}
    (hW : IsInvariant W) (p q : Fin 3) (hpq : p ≠ q)
    (h : matrixBlock p q ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap)
    (i j : Fin 3) (hij : i ≠ j) :
    matrixBlock i j ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap := by
  have ht := blockTranspose hW p q hpq h
  by_cases hip : i = p
  · subst i
    by_cases hjq : j = q
    · simpa only [hjq] using h
    · exact moveColumn hW p q j hjq hij.symm h
  by_cases hiq : i = q
  · subst i
    by_cases hjp : j = p
    · simpa only [hjp] using ht
    · exact moveColumn hW q p j hjp hij.symm ht
  have hj : j = p ∨ j = q := by
    revert hpq hij hip hiq
    fin_cases p <;> fin_cases q <;> fin_cases i <;> fin_cases j <;> decide
  rcases hj with hjp | hjq
  · simpa only [hjp] using moveRow hW q p i hiq hip ht
  · simpa only [hjq] using moveRow hW p q i hip hiq h

private lemma diagonal_difference [Infinite k] {W : Submodule k (Model k)}
    (hW : IsInvariant W) (p q : Fin 3) (hpq : p ≠ q)
    (h : matrixBlock p q ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap) :
    matrixBlock q q - matrixBlock p p ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap := by
  have h' := (transvection_coefficients hW q p hpq.symm _ h).1
  convert h' using 1
  apply Prod.ext
  · simp [transvectionLinear, matrixBlock, matrixUnit]
  · simp [transvectionLinear, matrixBlock, matrixUnit]
    rfl

open private coordinates_axis coordinates_first_block from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections

private lemma diagonal_coordinates (a : Fin 3 → k) :
    matrixCoordinates (diagonalCoordinates (A := Zorn k) a) = (Matrix.diagonal a, 0, 0) := by
  apply Prod.ext
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · change ((0 : Square k), (fun _ _ => -(0 : k))) = (0, 0)
    simp only [neg_zero, Pi.zero_def]

private lemma transvection_diagonal (p q : Fin 3) (a : Fin 3 → k) :
    transvectionLinear p q (Matrix.diagonal a, 0, 0) = (a q - a p) • matrixBlock p q := by
  apply Prod.ext
  · ext i j
    simp only [transvectionLinear, matrixBlock, matrixUnit, Matrix.sub_apply, Prod.smul_fst,
      Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]
    by_cases hi : p = i <;> by_cases hj : q = j <;> simp_all [Matrix.single]
  · simp [transvectionLinear, matrixBlock]

open TrialitySpecification (frameStabilizer)
open Composition.ZornSpecification (first)

private lemma frame_mem_isAuto (g : frameStabilizer (R := k)) :
    IsSplitAutomorphism g.val := by
  refine ⟨?_, g.property.2⟩
  have h : (∑ i : Fin 3, frameAxis (R := k) (A := Zorn k) i) = cubicUnit :=
    (hermitian_frame (norm k) (fun _ => 1)).1
  change g.val (cubicUnit : Model k) = cubicUnit
  rw [← h, map_sum]
  exact Finset.sum_congr rfl fun i _ => g.property.1 i

private lemma lower_scalar (x : Model k) (i : Fin 3) :
    (matrixCoordinates x).1 (cyclicNext i) (cyclicPrev i) =
      (Zorn.coordinates k (x.2 i)).2.2.2 := by
  fin_cases i <;> rfl

private lemma polar_first (x : Zorn k) :
    (norm k).polarBilin (first k) x = (Zorn.coordinates k x).2.2.2 := by
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates k).symm.surjective x
  rw [show first k = Zorn.ofCoordinates (1, 0, 0, 0) from rfl, Zorn.polar_formula]
  simp

private lemma exists_direction_pairing (c : Zorn k) (hc : c ≠ 0) :
    ∃ j : DirectionIndex, (norm k).polarBilin (direction k j) c ≠ 0 := by
  by_contra! h
  have he : (norm k).polarBilin.flip c = 0 := by
    apply (IntegralZornDirections.directionBasis k).ext
    intro j
    rw [IntegralZornDirections.directionBasis_apply]
    exact h j
  let := Zorn.perfect k
  apply hc
  apply (LinearMap.IsPerfPair.bijective_right (norm k).polarBilin).injective
  simpa only [map_zero] using he

private lemma octonion_block_detect [Infinite k] {W : Submodule k (Model k)}
    (hW : IsInvariant W) (x : Model k) (hx : x ∈ W) (i : Fin 3) (hi : x.2 i ≠ 0) :
    matrixBlock (cyclicPrev i) (cyclicNext i) ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap := by
  obtain ⟨j, hj⟩ := exists_direction_pairing (x.2 i) hi
  obtain ⟨F, extend, act, _, hfirst, _, hact, _⟩ := IntegralZornDirections.direction_actions
  let u := extend k (F j)
  let g := act k (F j)
  let y := g.val.symm x
  have hy : y ∈ W := hW _ (frame_mem_isAuto g⁻¹) x hx
  have hgy : u.toLinearEquiv (y.2 i) = x.2 i := by
    have he := congrArg (fun z : Model k => z.2 i) (hact k (F j) y)
    exact he.symm.trans (congrArg (fun z : Model k => z.2 i) (g.val.apply_symm_apply x))
  have hp : (norm k).polarBilin (u.toLinearEquiv (first k)) (u.toLinearEquiv (y.2 i)) =
      (norm k).polarBilin (first k) (y.2 i) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      ← map_add, u.map_norm]
  rw [hfirst k j, hgy, polar_first] at hp
  apply block_from_entry hW _ _ (by fin_cases i <;> decide) (matrixCoordinates y) ⟨y, hy, rfl⟩
  rw [lower_scalar, ← hp]
  exact hj

private lemma diagonal_block_detect [Infinite k] {W : Submodule k (Model k)}
    (hW : IsInvariant W) (a : Fin 3 → k) (ha : diagonalCoordinates a ∈ W)
    (p q : Fin 3) (hn : a q ≠ a p) :
    matrixBlock p q ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap := by
  have hpq : p ≠ q := fun h => hn (congrArg a h.symm)
  have hx : (Matrix.diagonal a, 0, 0) ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap :=
    ⟨_, ha, diagonal_coordinates a⟩
  have h := (transvection_coefficients hW p q hpq _ hx).1
  rw [transvection_diagonal, Submodule.smul_mem_iff_of_isUnit _
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hn))] at h
  exact h

private lemma mem_of_matrixCoordinates_mem {W : Submodule k (Model k)} {x : Model k}
    (h : matrixCoordinates x ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap) : x ∈ W := by
  obtain ⟨y, hy, he⟩ := h
  have hyx : y = x := (ShortDirections.coordinateEquiv k).injective he
  rwa [hyx] at hy

private lemma all_octonion_blocks {W : Submodule k (Model k)} (hW : IsInvariant W)
    (hM : ∀ i j : Fin 3, i ≠ j → matrixBlock i j ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap)
    (i : Fin 3) (c : Zorn k) : singleBlockCoordinates i c ∈ W := by
  have h₁ : singleBlockCoordinates i (first k) ∈ W := by
    apply mem_of_matrixCoordinates_mem
    rw [coordinates_first_block]
    exact hM _ _ (by fin_cases i <;> decide)
  obtain ⟨F, _, act, _, hfirst, _, hact, _⟩ := IntegralZornDirections.direction_actions
  have hb (j : DirectionIndex) : singleBlockCoordinates i (direction k j) ∈ W := by
    have h := hW _ (frame_mem_isAuto (act k (F j))) _ h₁
    have he : (act k (F j)).val (singleBlockCoordinates i (first k)) =
        singleBlockCoordinates i (direction k j) := by
      rw [hact]
      apply Prod.ext
      · rfl
      · funext l
        by_cases hl : l = i
        · subst l
          simp [CubicSpecification.singleBlockCoordinates, hfirst]
        · simp [CubicSpecification.singleBlockCoordinates, hl]
    exact he ▸ h
  let b := IntegralZornDirections.directionBasis k
  have hc : (insertBlock i) c = ∑ j, b.repr c j • (insertBlock i) (b j) := by
    conv_lhs => rw [← b.sum_repr c]
    simp only [map_sum, map_smul]
  change (insertBlock i) c ∈ W
  rw [hc]
  apply W.sum_mem
  intro j _
  apply W.smul_mem
  rw [show b j = direction k j from IntegralZornDirections.directionBasis_apply k j]
  exact hb j

private lemma all_trace_zero_diagonals [Infinite k] {W : Submodule k (Model k)}
    (hW : IsInvariant W)
    (hM : ∀ i j : Fin 3, i ≠ j → matrixBlock i j ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap)
    (a : Fin 3 → k) (ha : ∑ i, a i = 0) : diagonalCoordinates a ∈ W := by
  have hD (p q : Fin 3) (hpq : p ≠ q) : frameAxis q - frameAxis p ∈ W := by
    apply mem_of_matrixCoordinates_mem
    change ShortDirections.coordinateEquiv k (frameAxis q - frameAxis p) ∈ _
    rw [map_sub]
    change matrixCoordinates (frameAxis q) - matrixCoordinates (frameAxis p) ∈ _
    simp only [coordinates_axis]
    exact diagonal_difference hW p q hpq (hM p q hpq)
  have he : (diagonalCoordinates a : Model k) =
      a 1 • (frameAxis 1 - frameAxis 0) + a 2 • (frameAxis 2 - frameAxis 0) := by
    rw [Fin.sum_univ_three] at ha
    apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [CubicSpecification.diagonalCoordinates, FrameSpecification.frameAxis]
      linear_combination ha
    · simp [CubicSpecification.diagonalCoordinates, FrameSpecification.frameAxis]
  rw [he]
  exact W.add_mem (W.smul_mem _ (hD _ _ (by decide))) (W.smul_mem _ (hD _ _ (by decide)))

theorem geometricIrreducibility : GeometricIrreducibilityType := by
  intro k _ _
  let x₀ : Model k := singleBlockCoordinates 0 (first k)
  have hx₀ : x₀ ∈ traceZero k := block_trace 0 _
  have hxs : x₀ ∉ scalarLine k := by
    intro H
    obtain ⟨a, ha⟩ := exists_scalar H
    have h := congrArg (fun z : Model k => (Zorn.coordinates k (z.2 0)).1) ha
    have hf : (Zorn.coordinates k (first k)).1 = 1 := rfl
    simp [x₀, CubicSpecification.singleBlockCoordinates, CubicSpecification.cubicUnit, hf] at h
  refine ⟨lt_of_le_of_ne inf_le_right ?_, ?_⟩
  · intro h
    exact hxs (show x₀ ∈ scalarLine k ⊓ traceZero k by rw [h]; exact hx₀).1
  · intro W hS hT hW
    by_cases hB : ∃ p q : Fin 3, p ≠ q ∧ matrixBlock p q ∈ W.map (ShortDirections.coordinateEquiv k).toLinearMap
    · obtain ⟨p, q, hpq, hB⟩ := hB
      have hM := allMatrixBlocks hW p q hpq hB
      right
      apply le_antisymm hT
      intro x hx
      have hD : (diagonalCoordinates x.1 : Model k) ∈ W := by
        apply all_trace_zero_diagonals hW hM
        change traceMap k x = 0 at hx
        rwa [linearTrace_apply] at hx
      have hsum : x = diagonalCoordinates x.1 + ∑ i : Fin 3, singleBlockCoordinates i (x.2 i) := by
        apply Prod.ext
        · simp [Fin.sum_univ_three, CubicSpecification.diagonalCoordinates, CubicSpecification.singleBlockCoordinates]
        · funext i
          fin_cases i <;> simp [Fin.sum_univ_three, CubicSpecification.diagonalCoordinates,
            CubicSpecification.singleBlockCoordinates]
      rw [hsum]
      exact W.add_mem hD (W.sum_mem fun i _ => all_octonion_blocks hW hM i (x.2 i))
    · left
      apply le_antisymm _ hS
      intro x hx
      have hb (i : Fin 3) : x.2 i = 0 := by
        by_contra h
        apply hB
        exact ⟨_, _, by fin_cases i <;> decide, octonion_block_detect hW x hx i h⟩
      have hd : x = diagonalCoordinates x.1 := Prod.ext rfl (funext hb)
      refine ⟨?_, hT hx⟩
      apply Submodule.mem_span_singleton.mpr
      use x.1 0
      apply Prod.ext
      · funext i
        simp only [CubicSpecification.cubicUnit, Prod.smul_fst, Pi.smul_apply,
          smul_eq_mul, mul_one]
        by_contra hn
        apply hB
        have hpq : i ≠ 0 := fun h => hn (congrArg x.1 h.symm)
        refine ⟨i, 0, hpq, diagonal_block_detect hW x.1 ?_ _ _ hn⟩
        rwa [← hd]
      · rw [Prod.smul_snd]
        change x.1 0 • (0 : Fin 3 → Zorn k) = x.2
        rw [smul_zero]
        exact funext fun i => (hb i).symm
end MatrixDirections

section Geometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open TrialitySpecification (mapModel)
open ShortDirectionSpecification (IntegralPresentation)
open ReductiveFiberSpecification (SplitAction)
open private coordinateFinitePresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections

noncomputable section

set_option maxHeartbeats 800000

private def pullbackPointEquiv {S T : Scheme} (f : T ⟶ S) (D : Over T)
    (X : Over S) :
    (D ⟶ (Over.pullback f).obj X) ≃ ((Over.map f).obj D ⟶ X) :=
  ((Over.mapPullbackAdj f).homEquiv D X).symm

private lemma pullbackPointEquiv_left {S T : Scheme} (f : T ⟶ S) {D : Over T}
    {X : Over S} (p : D ⟶ (Over.pullback f).obj X) :
    (pullbackPointEquiv f D X p).left = p.left ≫ pullback.fst X.hom f :=
  rfl

private lemma pullbackPointEquiv_comp {S T : Scheme} (f : T ⟶ S) {D : Over T}
    {X Y : Over S} (p : D ⟶ (Over.pullback f).obj X) (b : X ⟶ Y) :
    pullbackPointEquiv f D Y (p ≫ (Over.pullback f).map b) =
      pullbackPointEquiv f D X p ≫ b :=
  (Over.mapPullbackAdj f).homEquiv_naturality_right_symm p b

private def pullbackPointGroupEquiv {S T : Scheme} (f : T ⟶ S) (D : Over T)
    (G : Grp (Over S)) :
    (D ⟶ ((Over.pullback f).mapGrp.obj G).X) ≃* ((Over.map f).obj D ⟶ G.X) where
  toEquiv := pullbackPointEquiv f D G.X
  map_mul' p q := by
    let F := Over.pullback f
    let p' : D ⟶ F.obj G.X := p
    let q' : D ⟶ F.obj G.X := q
    let t : D ⟶ F.obj (G.X ⊗ G.X) := lift p' q' ≫ Functor.LaxMonoidal.μ F G.X G.X
    have ht : pullbackPointEquiv f D (G.X ⊗ G.X) t =
        lift (pullbackPointEquiv f D G.X p') (pullbackPointEquiv f D G.X q') := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [← pullbackPointEquiv_comp f t (fst G.X G.X), lift_fst]
        congr 1
        change (lift p' q' ≫ Functor.LaxMonoidal.μ F G.X G.X) ≫ F.map (fst G.X G.X) = p'
        rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
      · rw [← pullbackPointEquiv_comp f t (snd G.X G.X), lift_snd]
        congr 1
        change (lift p' q' ≫ Functor.LaxMonoidal.μ F G.X G.X) ≫ F.map (snd G.X G.X) = q'
        rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
    change pullbackPointEquiv f D G.X (t ≫ F.map μ[G.X]) =
      lift (pullbackPointEquiv f D G.X p') (pullbackPointEquiv f D G.X q') ≫ μ[G.X]
    rw [pullbackPointEquiv_comp, ht]

private abbrev integerSpecMap (k : Type) [Field k] :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ k))

private def integerTestSpecIso {k : Type} [Field k] (R : TestAlgebra k) :
    (algSpec (CommRingCat.of ℤ)).obj (op (CommAlgCat.of ℤ R)) ≅
      (Over.map (integerSpecMap k)).obj ((testSpec k).obj (op R)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap k R)) ≫ integerSpecMap k) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1
    ext n
    exact map_intCast (algebraMap k R) n)

private def geometricFiberPointEquiv {P : IntegralPresentation} (G : SplitGroup P)
    {k : Type} [Field k] (R : TestAlgebra k) :
    Points (geometricFiber G k).X R ≃*
      SpinSpecification.SchemePoints G.group (CommAlgCat.of ℤ R) :=
  (pullbackPointGroupEquiv (integerSpecMap k) ((testSpec k).obj (op R)) G.group).trans
    (((yonedaGrpObj G.group.X).mapIso (integerTestSpecIso R).op).groupIsoToMulEquiv)

private lemma geometricFiberPointEquiv_left {P : IntegralPresentation} (G : SplitGroup P)
    {k : Type} [Field k] (R : TestAlgebra k) (g : Points (geometricFiber G k).X R) :
    (geometricFiberPointEquiv G R g).left = g.left ≫
      pullback.fst G.group.X.hom (integerSpecMap k) := by
  change ((integerTestSpecIso R).hom ≫
    pullbackPointEquiv (integerSpecMap k) ((testSpec k).obj (op R)) G.group.X g).left = _
  rw [Over.comp_left, pullbackPointEquiv_left]
  exact Category.id_comp _

/-- The integral split automorphism functor on test algebras over the fiber field. -/
def geometricFiberAction {P : IntegralPresentation} (G : SplitGroup P)
    (k : Type) [Field k] : SplitAction (geometricFiber G k) where
  action R := (G.action (CommAlgCat.of ℤ R)).comp (geometricFiberPointEquiv G R).toMonoidHom
  injective R := (G.injective (CommAlgCat.of ℤ R)).comp (geometricFiberPointEquiv G R).injective
  image R := by
    change Set.range (G.action _ ∘ geometricFiberPointEquiv G R) = _
    rw [Set.range_comp, (geometricFiberPointEquiv G R).surjective.range_eq, Set.image_univ,
      G.image]
  natural {R S} f g x := by
    let a : CommAlgCat.of ℤ R ⟶ CommAlgCat.of ℤ S :=
      CommAlgCat.ofHom (f.hom.restrictScalars ℤ)
    have h : geometricFiberPointEquiv G S (mapPoints f g) =
        (algSpec (CommRingCat.of ℤ)).map a.op ≫ geometricFiberPointEquiv G R g := by
      apply Over.OverMorphism.ext
      let π := pullback.fst G.group.X.hom (integerSpecMap k)
      calc
        _ = (mapPoints f g).left ≫ π := geometricFiberPointEquiv_left G S _
        _ = ((testSpec k).map f.op).left ≫ (g.left ≫ π) := Category.assoc _ _ _
        _ = ((algSpec (CommRingCat.of ℤ)).map a.op).left ≫ (geometricFiberPointEquiv G R g).left :=
          congrArg (((algSpec (CommRingCat.of ℤ)).map a.op).left ≫ ·)
            (geometricFiberPointEquiv_left G R g).symm
        _ = _ := rfl
    change mapModel a.hom.toRingHom (G.action _ (geometricFiberPointEquiv G R g) x) =
      G.action _ (geometricFiberPointEquiv G S (mapPoints f g)) (mapModel a.hom.toRingHom x)
    rw [h]
    exact G.natural a _ x

/-- The propagation theorem uses the canonical integer algebra instance, which
also agrees with the instance obtained from the coordinate quotient. -/
private lemma propagateIntegralSmoothness (A : Type) [CommRing A] [a : Algebra ℤ A]
    [Algebra.FinitePresentation ℤ A] (e : A →ₐ[ℤ] ℤ) (d : ℕ)
    (charts : ∀ (k : Type) [Field k], ∃ f : A, algebraMap ℤ k (e f) ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension d ℤ (Localization.Away f))
    (geometric : ∀ (k : Type) [Field k] [IsAlgClosed k],
      letI : Module ℤ k := Algebra.toModule
      letI : Module ℤ A := Algebra.toModule
      Algebra.Smooth k (k ⊗[ℤ] A) ∧ IrreducibleSpace (PrimeSpectrum (k ⊗[ℤ] A))) :
    SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ∧
      GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) := by
  have ha : a = Ring.toIntAlgebra A := Subsingleton.elim _ _
  subst a
  exact integralSmoothPropagation A e d charts geometric

private lemma coordinateGeometry (P : IntegralPresentation) (e : P.Coordinates →ₐ[ℤ] ℤ)
    (he : P.IsIdentity e)
    (charts : ∀ (k : Type) [Field k], ∃ f : P.Coordinates, algebraMap ℤ k (e f) ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension 52 ℤ (Localization.Away f)) :
    SmoothOfRelativeDimension 52 (coordinateScheme P).hom ∧
      GeometricallyConnected (coordinateScheme P).hom := by
  have := coordinateFinitePresentation P
  have geometric (k : Type) [Field k] [IsAlgClosed k] :
      Algebra.Smooth k (GeometricFiberSpecification.FiberRing P k) ∧
        IrreducibleSpace (PrimeSpectrum (GeometricFiberSpecification.FiberRing P k)) := by
    obtain ⟨hs, hi⟩ := GeometricFiberGeometry.geometricFiberGeometry P e he charts k
    refine ⟨?_, hi⟩
    exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)
  exact propagateIntegralSmoothness P.Coordinates e 52 charts geometric

/-- The integral split Albert automorphism group is smooth of relative dimension 52
with geometrically connected fibers, and its geometric fibers are reductive. -/
theorem integralGeometry : IntegralGeometryType := by
  obtain ⟨P, G, e, he, _, charts⟩ := integralIdentityCharts
  obtain ⟨hs, hc⟩ := coordinateGeometry P e he charts
  have hcoord : G.coordinates.hom.left ≫ (coordinateScheme P).hom = G.group.X.hom :=
    Over.w G.coordinates.hom
  have : IsIso G.coordinates.hom.left := Functor.map_isIso (Over.forget _) G.coordinates.hom
  have hsG : SmoothOfRelativeDimension 52 G.group.X.hom := by
    exact hcoord ▸ (MorphismProperty.cancel_left_of_respectsIso
      (@SmoothOfRelativeDimension 52) G.coordinates.hom.left (coordinateScheme P).hom).2 hs
  have hcG : GeometricallyConnected G.group.X.hom := by
    exact hcoord ▸ (MorphismProperty.cancel_left_of_respectsIso
      (@GeometricallyConnected) G.coordinates.hom.left (coordinateScheme P).hom).2 hc
  have : Smooth G.group.X.hom := SmoothOfRelativeDimension.smooth 52 G.group.X.hom
  refine ⟨P, G, hsG, hcG, ?_⟩
  intro k _ _
  apply ReductiveFibers.reductivity k (algebraicFiber G k) (geometricFiberAction G k)
  · exact inferInstanceAs (Smooth (pullback.snd G.group.X.hom (integerSpecMap k)))
  · exact inferInstanceAs (GeometricallyConnected (pullback.snd G.group.X.hom (integerSpecMap k)))
  · intro K _ _ _
    exact geometricIrreducibility K
  · intro K _ _ _
    exact geometricPointKernel K

end
end Geometry

end LinearAlgebraicGroups.Albert.IntegralSmoothness
