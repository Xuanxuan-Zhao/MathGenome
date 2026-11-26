import LinearAlgebraicGroups.Albert.QuadraticOperators
import Specs.LinearAlgebraicGroups.Albert.FrameParameters
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Group.TypeTags.Basic

/-! The frame and parameter transformations of weighted Hermitian algebras. -/

namespace LinearAlgebraicGroups.Albert

open _root_.LinearAlgebraicGroups.Composition
open scoped BigOperators TensorProduct

universe u v w

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.deprecated false

abbrev frameAxis := @FrameSpecification.frameAxis
abbrev frameProduct := @FrameSpecification.frameProduct

local notation "E" => FrameSpecification.frameAxis
local notation "D" => CubicSpecification.singleBlockCoordinates

open private coordinate_ext tracePairing_diagonal_single tracePairing_block_single
  adjointCross_diagonal adjointCross_block adjointCross_comm
  next_zero next_one next_two prev_zero prev_one prev_two
  from LinearAlgebraicGroups.Albert.CubicIdentities
open private triple_formula opSquare from LinearAlgebraicGroups.Albert.QuadraticOperators

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
variable {n : QuadraticForm R A} (γ : Fin 3 → Rˣ)


private theorem frame_diag (i : Fin 3) :
    HermitianSpecification.assemble n γ (E i) = diagonalIdempotent i := by
  unfold FrameSpecification.frameAxis
  erw [(cubic_matrix_coordinates (n := n) γ).2.1]
  ext j k
  by_cases h : j = k
  · subst k
    by_cases h : i = j <;>
      simp [HermitianSpecification.diagonalIdempotent, Matrix.single, Pi.single_apply, h, eq_comm]
  · simp only [Matrix.diagonal_apply_ne _ h, HermitianSpecification.diagonalIdempotent,
      Matrix.single, Matrix.of_apply, ite_eq_right_iff]
    rw [if_neg (fun ⟨hij, hik⟩ => h (hij.symm.trans hik))]

private theorem frame_adj (i : Fin 3) : CubicSpecification.cubicAdjoint n γ (E i) = 0 := by
  unfold FrameSpecification.frameAxis
  erw [(cubic_diagonal_formulas (n := n) γ (Pi.single i 1)).2]
  apply coordinate_ext
  · intro k
    fin_cases i <;> fin_cases k <;>
      simp [CubicSpecification.diagonalCoordinates, next_zero, next_one, next_two,
        prev_zero, prev_one, prev_two, Pi.single_apply]
  · intro k
    rfl

private theorem frame_trace (i : Fin 3) (y : Coordinates R A) :
    tracePairing n γ (E i) y = y.1 i := by
  rw [tracePairing_comm]
  simp [FrameSpecification.frameAxis, tracePairing_diagonal_single]

private theorem cross_zero_left (y : Coordinates R A) :
    CubicSpecification.adjointCross n γ 0 y = 0 := by
  apply coordinate_ext
  · intro i
    simp [adjointCross_diagonal]
  · intro i
    simp [adjointCross_block]

private theorem frame_op (i : Fin 3) (y : Coordinates R A) :
    QuadraticOperatorSpecification.applyOperator n γ (E i) y = y.1 i • E i := by
  simp only [QuadraticOperatorSpecification.applyOperator, frame_trace, frame_adj, cross_zero_left,
    sub_zero]

private theorem frame_off (i : Fin 3) (y : Coordinates R A) :
    QuadraticOperatorSpecification.triple n γ (E (cyclicNext i)) y (E (cyclicPrev i)) =
      D i (y.2 i) := by
  simp only [QuadraticOperatorSpecification.triple, QuadraticOperatorSpecification.applyOperator,
    map_add, LinearMap.add_apply, frame_trace, frame_adj]
  have hCross : CubicSpecification.cubicAdjoint n γ (E (cyclicNext i) + E (cyclicPrev i) : (Coordinates R A)) = E i := by
    apply coordinate_ext <;> intro k <;> fin_cases i <;> fin_cases k <;>
      simp [CubicSpecification.cubicAdjoint, FrameSpecification.frameAxis,
        CubicSpecification.diagonalCoordinates, Pi.single_apply,
        next_zero, next_one, next_two, prev_zero, prev_one, prev_two]
  simp only [hCross, cross_zero_left, sub_zero]
  apply coordinate_ext <;> intro k <;> fin_cases i <;> fin_cases k <;>
    simp [adjointCross_diagonal, adjointCross_block, FrameSpecification.frameAxis,
      CubicSpecification.diagonalCoordinates, CubicSpecification.singleBlockCoordinates,
      Pi.single_apply, next_zero, next_one, next_two, prev_zero, prev_one, prev_two]

theorem hermitian_frame : FrameSpecification.frameType.{u, v} := by
  intro R A _ _ _ n γ
  refine ⟨?_, frame_diag γ, frame_op γ, frame_off γ, ?_, ?_, ?_⟩
  · apply coordinate_ext <;> intro k <;> fin_cases k <;>
      simp [Fin.sum_univ_three, FrameSpecification.frameAxis,
        CubicSpecification.diagonalCoordinates, CubicSpecification.cubicUnit, Pi.single_apply]
  · intro i m
    erw [frame_op]
    by_cases h : i = m <;>
      simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
        Pi.single_apply, h, eq_comm]
  · intro i
    simp [frame_op, CubicSpecification.cubicUnit]
  · intro y
    simp only [frame_op, frame_off]
    apply coordinate_ext <;> intro k <;> fin_cases k <;>
      simp [Fin.sum_univ_three, FrameSpecification.frameAxis,
        CubicSpecification.diagonalCoordinates, CubicSpecification.singleBlockCoordinates,
        Pi.single_apply]


variable [IsScalarTower R A A] [SMulCommClass R A A]

private theorem trace_unit_frame (i : Fin 3) :
    tracePairing n γ (E i) cubicUnit = 1 :=
  frame_trace γ i cubicUnit

private theorem trace_unit_block (i : Fin 3) (a : A) :
    tracePairing n γ (D i a) cubicUnit = 0 := by
  rw [tracePairing_comm, tracePairing_block_single]
  simp [CubicSpecification.cubicUnit]

private theorem two_half (d : Rˣ) (hd : (d : R) = 2) :
    (↑d⁻¹ : R) * (2 : R) = 1 := by
  rw [← hd]
  exact Units.inv_mul d

private theorem assemble_triple_unit (h : IsOctonionNorm n) (x y : Coordinates R A) :
    assemble n γ (QuadraticOperatorSpecification.triple n γ x cubicUnit y) =
      assemble n γ x * assemble n γ y + assemble n γ y * assemble n γ x := by
  let f : Coordinates R A →ₗ[R] Mat A :=
    (hermitian n γ).subtype.comp (coordinateMap h.toNormLaws γ)
  let U := QuadraticOperatorSpecification.applyOperator n γ
  have sq (z : Coordinates R A) : f (U z cubicUnit) = f z * f z :=
    cubic_operator_matrix_square γ h z
  change f (U (x + y) cubicUnit - U x cubicUnit - U y cubicUnit) = f x * f y + f y * f x
  rw [map_sub, map_sub, sq, sq, sq, map_add, add_mul, mul_add, mul_add]
  abel

set_option maxHeartbeats 1000000 in
theorem hermitian_frame_products : FrameSpecification.productsType.{u, v} := by
  intro R A _ _ _ _ _ n h γ d hd
  dsimp only
  have hh : (↑d⁻¹ : R) + (↑d⁻¹ : R) = 1 := by
    rw [← mul_two]
    exact two_half d hd
  have cross_unit (a : Coordinates R A) :
      adjointCross n γ a cubicUnit = linearTrace n γ a • cubicUnit - a := by
    rw [adjointCross_comm]
    exact (cubic_unit_identities (n := n) γ).2.2 a
  have product (x y : Coordinates R A) :
      FrameSpecification.frameProduct n γ d x y =
      (↑d⁻¹ : R) • (tracePairing n γ x cubicUnit • y + tracePairing n γ y cubicUnit • x -
        (linearTrace n γ (adjointCross n γ x y) • cubicUnit - adjointCross n γ x y)) := by
    rw [FrameSpecification.frameProduct, triple_formula, cross_unit]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i m
    rw [product]
    simp only [trace_unit_frame]
    apply coordinate_ext <;> intro k <;>
      fin_cases i <;> fin_cases m <;> fin_cases k <;>
      simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
        CubicSpecification.cubicUnit, linearTrace_apply, Fin.sum_univ_three,
        adjointCross_diagonal, adjointCross_block, Pi.single_apply,
        next_zero, next_one, next_two, prev_zero, prev_one, prev_two,
        smul_eq_mul, mul_add, hh]
  · intro i a
    rw [product]
    simp only [trace_unit_frame, trace_unit_block, one_smul, zero_smul, add_zero]
    apply coordinate_ext <;> intro k <;> fin_cases i <;> fin_cases k <;>
      simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
        CubicSpecification.singleBlockCoordinates, CubicSpecification.cubicUnit,
        linearTrace_apply, Fin.sum_univ_three, adjointCross_diagonal, adjointCross_block,
        Pi.single_apply, next_zero, next_one, next_two, prev_zero, prev_one, prev_two]
  · intro i a
    rw [product]
    simp only [trace_unit_frame, trace_unit_block, one_smul, zero_smul, add_zero]
    apply coordinate_ext <;> intro k <;> fin_cases i <;> fin_cases k <;>
      simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
        CubicSpecification.singleBlockCoordinates, CubicSpecification.cubicUnit,
        linearTrace_apply, Fin.sum_univ_three, adjointCross_diagonal, adjointCross_block,
        Pi.single_apply, next_zero, next_one, next_two, prev_zero, prev_one, prev_two]
  · intro i a
    rw [product]
    simp only [trace_unit_frame, trace_unit_block, one_smul, zero_smul, add_zero]
    apply coordinate_ext <;> intro k <;> fin_cases i <;> fin_cases k <;>
      simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
        CubicSpecification.singleBlockCoordinates, CubicSpecification.cubicUnit,
        linearTrace_apply, Fin.sum_univ_three, adjointCross_diagonal, adjointCross_block,
        Pi.single_apply, next_zero, next_one, next_two, prev_zero, prev_one, prev_two]
  · intro i a c
    rw [product]
    simp only [trace_unit_block, zero_smul, add_zero, zero_sub]
    apply coordinate_ext <;> intro k <;> fin_cases i <;> fin_cases k <;>
      simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
        CubicSpecification.singleBlockCoordinates, CubicSpecification.cubicUnit,
        linearTrace_apply, Fin.sum_univ_three, adjointCross_diagonal, adjointCross_block,
        Pi.single_apply, next_zero, next_one, next_two, prev_zero, prev_one, prev_two,
        smul_eq_mul, mul_assoc]
  · intro i a c
    rw [product]
    simp only [trace_unit_block, zero_smul, add_zero, zero_sub]
    apply coordinate_ext <;> intro k <;> fin_cases i <;> fin_cases k <;>
      simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
        CubicSpecification.singleBlockCoordinates, CubicSpecification.cubicUnit,
        linearTrace_apply, Fin.sum_univ_three, adjointCross_diagonal, adjointCross_block,
        Pi.single_apply, next_zero, next_one, next_two, prev_zero, prev_one, prev_two]
  · intro x y
    let f : Coordinates R A →ₗ[R] Mat A :=
      (hermitian n γ).subtype.comp (coordinateMap (IsOctonionNorm.toNormLaws h) γ)
    change f ((↑d⁻¹ : R) • QuadraticOperatorSpecification.triple n γ x cubicUnit y) = _
    rw [map_smul]
    exact congrArg ((↑d⁻¹ : R) • ·) (assemble_triple_unit γ h x y)

private def rescaleCoordinates (a b : Fin 3 → Rˣ) : Coordinates R A ≃ₗ[R] Coordinates R A :=
  (LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (M := R) (a i)).prodCongr
    (LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (M := A) (b i))

private theorem rescale_fst (a b : Fin 3 → Rˣ) (x : Coordinates R A) (i : Fin 3) :
    (rescaleCoordinates a b x).1 i = (a i : R) * x.1 i := rfl

private theorem rescale_snd (a b : Fin 3 → Rˣ) (x : Coordinates R A) (i : Fin 3) :
    (rescaleCoordinates a b x).2 i = (b i : R) • x.2 i := rfl

private theorem scaled_unit (b : Fin 3 → Rˣ) :
    rescaleCoordinates (fun _ => 1) b (cubicUnit : (Coordinates R A)) = cubicUnit := by
  apply coordinate_ext <;> intro i <;>
    simp [rescale_fst, rescale_snd, CubicSpecification.cubicUnit]

private theorem map_operator_of_adjoint (γ' : Fin 3 → Rˣ) (F : (Coordinates R A) →ₗ[R] (Coordinates R A))
    (adj : ∀ x, F (cubicAdjoint n γ x) = cubicAdjoint n γ' (F x))
    (pair : ∀ x y, tracePairing n γ x y = tracePairing n γ' (F x) (F y))
    (x y : Coordinates R A) :
    F (QuadraticOperatorSpecification.applyOperator n γ x y) = QuadraticOperatorSpecification.applyOperator n γ' (F x) (F y) := by
  simp only [QuadraticOperatorSpecification.applyOperator, CubicSpecification.adjointCross,
    map_sub, map_smul, map_add, adj, pair]

private def blockUnits (γ : Fin 3 → Rˣ) (i : Fin 3) : Rˣ :=
  γ (cyclicNext i) * γ (cyclicPrev i)

private theorem map_blockUnits (B : Type w) [CommRing B] [Algebra R B] (i : Fin 3) :
    blockUnits (baseChangedWeights B γ) i = Units.map (algebraMap R B) (blockUnits γ i) :=
  (map_mul _ _ _).symm

private theorem scaled_operator (γ' b : Fin 3 → Rˣ)
    (diagonal : ∀ i, blockUnits γ' i * b i ^ 2 = blockUnits γ i)
    (offDiagonal : ∀ i, γ' i * b (cyclicNext i) * b (cyclicPrev i) = b i * γ i)
    (x y : Coordinates R A) :
    let F := rescaleCoordinates (A := A) (fun _ => 1) b
    F (QuadraticOperatorSpecification.applyOperator n γ x y) = QuadraticOperatorSpecification.applyOperator n γ' (F x) (F y) := by
  let F := rescaleCoordinates (A := A) (fun _ => 1) b
  have hd (i : Fin 3) :
      blockWeight γ' i * ((b i : R) * (b i : R)) = blockWeight γ i := by
    simpa [CubicSpecification.blockWeight, blockUnits, pow_two] using
      congrArg (fun t : Rˣ => (t : R)) (diagonal i)
  have ho (i : Fin 3) :
      (γ' i : R) * ((b (cyclicNext i) : R) * (b (cyclicPrev i) : R)) =
        (b i : R) * (γ i : R) := by
    simpa [mul_assoc] using congrArg (fun t : Rˣ => (t : R)) (offDiagonal i)
  apply map_operator_of_adjoint γ γ' F.toLinearMap
  · intro z
    apply coordinate_ext
    · intro i
      simp only [F, LinearEquiv.coe_coe, rescale_fst, Units.val_one, one_mul,
        CubicSpecification.cubicAdjoint, rescale_snd, QuadraticMap.map_smul, smul_eq_mul]
      rw [← mul_assoc, hd]
    · intro i
      simp only [F, LinearEquiv.coe_coe, rescale_snd, rescale_fst, Units.val_one, one_mul,
        CubicSpecification.cubicAdjoint, smul_add, smul_smul, smul_mul_assoc, mul_smul_comm,
        map_smul]
      rw [mul_comm (b (cyclicPrev i) : R) (b (cyclicNext i) : R), ho,
        mul_comm (b i : R) (-z.1 i)]
  · intro z t
    simp only [tracePairing_apply, F, LinearEquiv.coe_coe, rescale_fst, rescale_snd, Units.val_one,
      one_mul, LinearMap.map_smul₂, LinearMap.smul_apply, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hd i]
    ring

open private algebraMap_smul_tmul entry_cases from LinearAlgebraicGroups.Albert.HermitianCoordinates

private theorem rescale_tensor (a b : Fin 3 → Rˣ) (B : Type w) [CommRing B] [Algebra R B]
    (z : B ⊗[R] (Coordinates R A)) :
    coordinatesBaseChange B ((rescaleCoordinates a b).toLinearMap.baseChange B z) =
      rescaleCoordinates (baseChangedWeights B a) (baseChangedWeights B b) (coordinatesBaseChange B z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s x =>
      rw [LinearMap.baseChange_tmul, coordinatesBaseChange_tmul, coordinatesBaseChange_tmul]
      apply coordinate_ext
      · intro i
        simp only [rescale_fst, baseChangedWeights, Units.coe_map, LinearEquiv.coe_coe, map_mul]
        change s * (algebraMap R B (a i : R) * algebraMap R B (x.1 i)) =
          algebraMap R B (a i : R) * (s * algebraMap R B (x.1 i))
        ring
      · intro i
        simp only [rescale_snd, baseChangedWeights, LinearEquiv.coe_coe, Units.coe_map]
        exact (algebraMap_smul_tmul (S := B) (b i : R) s (x.2 i)).symm
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem scaling_isomorphism (h : IsOctonionNorm n) (γ' b : Fin 3 → Rˣ)
    (diagonal : ∀ i, blockUnits γ' i * b i ^ 2 = blockUnits γ i)
    (offDiagonal : ∀ i, γ' i * b (cyclicNext i) * b (cyclicPrev i) = b i * γ i) :
    FrameSpecification.IsParameterIso n h γ γ' (rescaleCoordinates (fun _ => 1) b) := by
  refine ⟨scaled_unit b, ?_⟩
  intro B _ _
  letI := h.projective
  dsimp only
  intro x y
  simp only [rescale_tensor, LinearEquiv.apply_symm_apply]
  have ones : baseChangedWeights B (fun _ => (1 : Rˣ)) = fun _ => 1 := by
    funext i
    exact map_one _
  rw [ones]
  apply scaled_operator
  · intro i
    rw [map_blockUnits, map_blockUnits]
    let m : Rˣ →* Bˣ := Units.map (algebraMap R B).toMonoidHom
    change m (blockUnits γ' i) * (m (b i)) ^ 2 = m (blockUnits γ i)
    rw [← map_pow, ← map_mul, diagonal]
  · intro i
    let m : Rˣ →* Bˣ := Units.map (algebraMap R B).toMonoidHom
    change m (γ' i) * m (b (cyclicNext i)) * m (b (cyclicPrev i)) = m (b i) * m (γ i)
    rw [← map_mul, ← map_mul, ← map_mul, offDiagonal]

private theorem rescale_matrix (γ' b : Fin 3 → Rˣ) (s : Fin 3 → Rˣ)
    (forward : ∀ i,
      γ' (cyclicPrev i) * b i = ((s (cyclicNext i))⁻¹ * s (cyclicPrev i)) * γ (cyclicPrev i))
    (backward : ∀ i,
      γ' (cyclicNext i) * b i = ((s (cyclicPrev i))⁻¹ * s (cyclicNext i)) * γ (cyclicNext i))
    (x : Coordinates R A) (i j : Fin 3) :
    assemble n γ' (rescaleCoordinates (fun _ => 1) b x) i j =
      (↑((s i)⁻¹ * s j) : R) • assemble n γ x i j := by
  rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · simp [assemble_diagonal, rescale_fst, inv_mul_cancel]
  · simp only [assemble_forward, rescale_snd, smul_smul, ← Units.val_mul]
    rw [forward]
  · simp only [assemble_backward, rescale_snd, map_smul, smul_smul, ← Units.val_mul]
    rw [backward]

local macro "unit_abel" : tactic =>
  `(tactic| apply Additive.ofMul.injective <;>
    (simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] <;> abel))

theorem hermitian_common_scaling : FrameSpecification.commonScalingType.{u, v} := by
  intro R A _ _ _ _ _ n h γ a
  let γ' : Fin 3 → Rˣ := fun i => a * γ i
  let b : Fin 3 → Rˣ := fun _ => a⁻¹
  refine ⟨rescaleCoordinates (fun _ => 1) b, scaling_isomorphism γ h γ' b ?_ ?_, ?_⟩
  · intro i
    dsimp [blockUnits, γ', b]
    unit_abel
  · intro i
    dsimp [γ', b]
    unit_abel
  · intro x
    ext i j
    simpa using rescale_matrix (n := n) γ γ' b (fun _ => 1)
      (fun k => by dsimp [γ', b]; unit_abel)
      (fun k => by dsimp [γ', b]; unit_abel) x i j

private theorem three_indices (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i
  decide

theorem hermitian_square_scaling : FrameSpecification.squareScalingType.{u, v} := by
  intro R A _ _ _ _ _ n h γ s
  let γ' : Fin 3 → Rˣ := fun i => s i ^ 2 * γ i
  let b : Fin 3 → Rˣ := fun i => (s (cyclicNext i) * s (cyclicPrev i))⁻¹
  refine ⟨rescaleCoordinates (fun _ => 1) b, scaling_isomorphism γ h γ' b ?_ ?_, ?_⟩
  · intro i
    dsimp [blockUnits, γ', b]
    unit_abel
  · intro i
    rcases three_indices i with rfl | rfl | rfl <;>
      simp only [γ', b, cyclicNext, cyclicPrev, next_zero, next_one, next_two, prev_zero, prev_one, prev_two] <;>
      unit_abel
  · exact rescale_matrix γ γ' b s
      (fun k => by dsimp [γ', b]; unit_abel)
      (fun k => by dsimp [γ', b]; unit_abel)

theorem hermitian_normalization : FrameSpecification.normalizationType.{u, v} := by
  intro R A _ _ _ _ _ n h γ
  let d := γ 0 * γ 1 * γ 2
  let γ' : Fin 3 → Rˣ := fun i => d⁻¹ * γ i
  let s : Fin 3 → Rˣ := fun i => if i = 2 then d else 1
  obtain ⟨F, hF, _⟩ := hermitian_common_scaling h γ d⁻¹
  obtain ⟨G, hG, _⟩ := hermitian_square_scaling h γ' s
  refine ⟨fun i => s i ^ 2 * γ' i, F.trans G, ?_, ?_⟩
  · have hd : s 0 ^ 2 * γ' 0 * (s 1 ^ 2 * γ' 1) * (s 2 ^ 2 * γ' 2) = 1 := by
      simp only [s, γ', d, if_neg (show (0 : Fin 3) ≠ 2 by decide),
        if_neg (show (1 : Fin 3) ≠ 2 by decide), if_pos rfl, one_pow, one_mul]
      unit_abel
    exact congrArg (fun t : Rˣ => (t : R)) hd
  · refine ⟨by rw [LinearEquiv.trans_apply, hF.1, hG.1], ?_⟩
    intro B _ _
    letI := h.projective
    dsimp only
    intro x y
    let e := coordinatesBaseChange (R := R) (A := A) B
    let f := fun z => e (F.toLinearMap.baseChange B (e.symm z))
    let g := fun z => e (G.toLinearMap.baseChange B (e.symm z))
    have comp (z : Coordinates B (B ⊗[R] A)) :
        e ((F.trans G).toLinearMap.baseChange B (e.symm z)) = g (f z) := by
      change e ((G.toLinearMap.comp F.toLinearMap).baseChange B (e.symm z)) = g (f z)
      rw [LinearMap.baseChange_comp]
      simp only [f, g, LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
    change e ((F.trans G).toLinearMap.baseChange B (e.symm (QuadraticOperatorSpecification.applyOperator _ _ x y))) =
      QuadraticOperatorSpecification.applyOperator _ _
        (e ((F.trans G).toLinearMap.baseChange B (e.symm x)))
        (e ((F.trans G).toLinearMap.baseChange B (e.symm y)))
    simp only [comp]
    have hf := hF.2 B x y
    change f (QuadraticOperatorSpecification.applyOperator _ _ x y) = QuadraticOperatorSpecification.applyOperator _ _ (f x) (f y) at hf
    rw [hf]
    exact hG.2 B (f x) (f y)



theorem hermitian_frame_baseChange : FrameSpecification.baseChangeType.{u, v, w} := by
  intro R A _ _ _ _ _ n h γ B _ _
  letI := h.projective
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    change extendCoordinates B _ = _
    rw [extendCoordinates_apply]
    apply coordinate_ext <;> intro j <;>
      by_cases hij : j = i <;>
      simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates, Pi.single_apply, hij]
  · intro i a
    change extendCoordinates B _ = _
    rw [extendCoordinates_apply]
    apply coordinate_ext <;> intro j <;>
      by_cases hij : j = i <;>
      simp [CubicSpecification.singleBlockCoordinates, Pi.single_apply, hij]
  · intro i z
    dsimp only
    erw [frame_op]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
        rw [LinearMap.baseChange_tmul, coordinatesBaseChange_tmul, coordinatesBaseChange_tmul]
        apply coordinate_ext <;> intro j <;>
          by_cases hij : j = i <;>
          simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates, Pi.single_apply,
            hij, mul_assoc]
    | add x y hx hy =>
        simp only [map_add, Prod.fst_add, Pi.add_apply, add_smul, hx, hy]
  · intro i z
    dsimp only
    erw [frame_off]
    induction z using TensorProduct.induction_on with
    | zero =>
        simp [CubicSpecification.singleBlockCoordinates]; rfl
    | tmul s x =>
        rw [LinearMap.baseChange_tmul, coordinatesBaseChange_tmul, coordinatesBaseChange_tmul]
        apply coordinate_ext <;> intro j <;>
          by_cases hij : j = i <;>
          simp [CubicSpecification.singleBlockCoordinates, LinearMap.single_apply, Pi.single_apply, hij]
    | add x y hx hy =>
        simp only [map_add, Prod.snd_add, Pi.add_apply, hx, hy]
        apply coordinate_ext <;> intro j <;>
          by_cases hij : j = i <;>
          simp [CubicSpecification.singleBlockCoordinates, Pi.single_apply, hij]

private def reindex {M : Type*} [AddCommGroup M] [Module R M] (σ : Equiv.Perm (Fin 3)) :
    (Fin 3 → M) ≃ₗ[R] (Fin 3 → M) where
  toFun x i := x (σ i)
  invFun x i := x (σ.symm i)
  left_inv x := funext fun i => by simp
  right_inv x := funext fun i => by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def conjugationEquiv (h : NormLaws n) : A ≃ₗ[R] A :=
  { conjugate n with
    invFun := conjugate n
    left_inv := conjugate_involutive h
    right_inv := conjugate_involutive h }

private def permuteCoordinates (h : NormLaws n) (σ : Equiv.Perm (Fin 3)) (rev : Bool) :
    Coordinates R A ≃ₗ[R] Coordinates R A :=
  (reindex σ).prodCongr ((reindex σ).trans
    (LinearEquiv.piCongrRight fun _ => if rev then conjugationEquiv h else LinearEquiv.refl R A))

private theorem permute_fst (h : NormLaws n) (σ : Equiv.Perm (Fin 3)) (rev : Bool) (x : Coordinates R A) (i : Fin 3) :
    (permuteCoordinates h σ rev x).1 i = x.1 (σ i) := rfl

private theorem permute_snd (h : NormLaws n) (σ : Equiv.Perm (Fin 3)) (rev : Bool) (x : Coordinates R A) (i : Fin 3) :
    (permuteCoordinates h σ rev x).2 i = if rev then conjugate n (x.2 (σ i)) else x.2 (σ i) := by
  cases rev <;> rfl

private theorem orientation_table :
    ∀ f : Fin 3 → Fin 3, f 0 ≠ f 1 → f 0 ≠ f 2 → f 1 ≠ f 2 →
    ∃ rev : Bool, ∀ i,
      f (cyclicNext i) = (if rev then cyclicPrev (f i) else cyclicNext (f i)) ∧
      f (cyclicPrev i) = (if rev then cyclicNext (f i) else cyclicPrev (f i)) := by
  decide

private theorem permuted_operator (h : NormLaws n) (σ : Equiv.Perm (Fin 3)) (rev : Bool)
    (next : ∀ i, σ (cyclicNext i) = (if rev then cyclicPrev (σ i) else cyclicNext (σ i)))
    (prev : ∀ i, σ (cyclicPrev i) = (if rev then cyclicNext (σ i) else cyclicPrev (σ i)))
    (x y : Coordinates R A) :
    let F := permuteCoordinates h σ rev
    F (QuadraticOperatorSpecification.applyOperator n γ x y) = QuadraticOperatorSpecification.applyOperator n (γ ∘ σ) (F x) (F y) := by
  let F := permuteCoordinates h σ rev
  have eta (i : Fin 3) : blockWeight (γ ∘ σ) i = blockWeight γ (σ i) := by
    simp only [CubicSpecification.blockWeight, Function.comp_apply, next, prev]
    cases rev <;> simp [mul_comm]
  have polar (a b : A) : n.polarBilin (conjugate n a) (conjugate n b) = n.polarBilin a b := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add,
      norm_conjugate h]
  apply map_operator_of_adjoint γ (γ ∘ σ) F.toLinearMap
  · intro z
    apply coordinate_ext
    · intro i
      simp only [F, LinearEquiv.coe_coe, permute_fst, CubicSpecification.cubicAdjoint,
        permute_snd, eta, next, prev]
      cases rev <;> simp [norm_conjugate h, mul_comm]
    · intro i
      simp only [F, LinearEquiv.coe_coe, permute_snd, CubicSpecification.cubicAdjoint,
        permute_fst, next, prev, Function.comp_apply]
      cases rev <;> simp [conjugate_mul h, conjugate_involutive h]
  · intro z t
    simp only [tracePairing_apply, F, LinearEquiv.coe_coe, permute_fst, permute_snd, eta]
    rw [← Equiv.sum_comp σ (fun i => z.1 i * t.1 i + blockWeight γ i * n.polarBilin (z.2 i) (t.2 i))]
    cases rev <;> simp [polar]

private theorem permute_tensor (h : IsOctonionNorm n) (σ : Equiv.Perm (Fin 3)) (rev : Bool)
    (B : Type w) [CommRing B] [Algebra R B] (z : B ⊗[R] (Coordinates R A)) :
    letI := h.projective
    coordinatesBaseChange B ((permuteCoordinates (IsOctonionNorm.toNormLaws h) σ rev).toLinearMap.baseChange B z) =
      permuteCoordinates (IsOctonionNorm.toNormLaws (octonion_norm_baseChange h B)) σ rev (coordinatesBaseChange B z) := by
  letI := h.projective
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s x =>
      rw [LinearMap.baseChange_tmul, coordinatesBaseChange_tmul, coordinatesBaseChange_tmul]
      apply coordinate_ext
      · intro i
        rfl
      · intro i
        simp only [LinearEquiv.coe_coe, permute_snd]
        cases rev <;> simp [conjugate_baseChange, LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem hermitian_permutation : FrameSpecification.permutationType.{u, v} := by
  intro R A _ _ _ _ _ n h γ σ
  obtain ⟨rev, orientation⟩ := orientation_table σ
    (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide))
  let F := permuteCoordinates (IsOctonionNorm.toNormLaws h) σ rev
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · apply coordinate_ext <;> intro i <;>
      simp [F, permute_fst, permute_snd, CubicSpecification.cubicUnit]
  · intro B _ _
    letI := h.projective
    dsimp only
    intro x y
    simp only [F, permute_tensor (h := h) σ rev B, LinearEquiv.apply_symm_apply]
    exact permuted_operator (baseChangedWeights B γ) (IsOctonionNorm.toNormLaws (octonion_norm_baseChange h B))
      σ rev (fun i => (orientation i).1) (fun i => (orientation i).2) x y
  · intro x i j
    change assemble n (γ ∘ σ) (F x) i j = assemble n γ x (σ i) (σ j)
    have invol (a : A) := conjugate_involutive (IsOctonionNorm.toNormLaws h) a
    rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
    · simp [assemble_diagonal, F, permute_fst]
    · rw [assemble_forward, (orientation k).1, (orientation k).2]
      cases rev <;> simp [F, permute_snd, assemble_forward, assemble_backward, orientation]
    · rw [assemble_backward, (orientation k).1, (orientation k).2]
      cases rev <;> simp [F, permute_snd, assemble_forward, assemble_backward,
        (orientation k).1, (orientation k).2, invol]


private theorem diagonal_operator (a : Fin 3 → Rˣ) (y : Coordinates R A) :
    QuadraticOperatorSpecification.applyOperator n γ (diagonalCoordinates (fun i => (a i : R))) y =
      rescaleCoordinates (fun i => (a i)^2) (blockUnits a) y := by
  have adj := (cubic_diagonal_formulas (n := n) γ (fun i => (a i : R))).2
  simp only [QuadraticOperatorSpecification.applyOperator, adj]
  apply coordinate_ext
  · intro i
    simp only [rescale_fst, Prod.fst_sub, Pi.sub_apply, Prod.smul_fst, Pi.smul_apply,
      CubicSpecification.diagonalCoordinates, tracePairing_apply, adjointCross_diagonal,
      Pi.zero_apply, LinearMap.zero_apply, map_zero, mul_zero, add_zero, sub_zero,
      Fin.sum_univ_three, smul_eq_mul, Units.val_pow_eq_pow_val]
    rcases three_indices i with rfl | rfl | rfl <;>
      simp only [cyclicNext, cyclicPrev, next_zero, next_one, next_two, prev_zero, prev_one, prev_two] <;>
      ring
  · intro i
    simp [rescale_snd, adjointCross_block, CubicSpecification.diagonalCoordinates, blockUnits]

private def weightUnit (γ : Fin 3 → Rˣ) : Rˣ := γ 0 * γ 1 * γ 2

private theorem block_mul_weight (i : Fin 3) : (γ i : R) * blockWeight γ i = weightUnit γ := by
  rcases three_indices i with rfl | rfl | rfl <;>
    simp only [CubicSpecification.blockWeight, weightUnit, Units.val_mul,
      next_zero, next_one, next_two, prev_zero, prev_one, prev_two] <;> ring

private theorem block_mul_block (i : Fin 3) :
    blockWeight γ (cyclicNext i) * blockWeight γ (cyclicPrev i) =
      weightUnit γ * (γ i : R) := by
  rcases three_indices i with rfl | rfl | rfl <;>
    simp only [CubicSpecification.blockWeight, weightUnit, Units.val_mul, cyclicNext, cyclicPrev,
      next_zero, next_one, next_two, prev_zero, prev_one, prev_two] <;> ring

private theorem cancel_partner (a b : Rˣ) : (a : R) * (b : R) * (↑a⁻¹ : R) = (b : R) := by
  rw [mul_comm (a : R) (b : R), Units.mul_inv_cancel_right]

private theorem block_mul_inv_complement (i : Fin 3) :
    blockWeight γ (cyclicNext i) * (↑(γ (cyclicPrev i))⁻¹ : R) = (γ i : R) ∧
    blockWeight γ (cyclicPrev i) * (↑(γ (cyclicNext i))⁻¹ : R) = (γ i : R) := by
  rcases three_indices i with rfl | rfl | rfl <;>
    simp only [CubicSpecification.blockWeight, cyclicNext, cyclicPrev,
      next_zero, next_one, next_two, prev_zero, prev_one, prev_two] <;>
    constructor <;> first | exact Units.mul_inv_cancel_right _ _ | exact cancel_partner _ _

private theorem isotope_operator (x y : Coordinates R A) :
    let F := rescaleCoordinates γ (blockUnits γ)
    let u : (Coordinates R A) := diagonalCoordinates (fun i => (↑(γ i)⁻¹ : R))
    F (QuadraticOperatorSpecification.applyOperator n γ x y) =
      QuadraticOperatorSpecification.applyOperator n (fun _ => 1) (F x)
        (QuadraticOperatorSpecification.applyOperator n (fun _ => 1) u (F y)) := by
  let F : Coordinates R A ≃ₗ[R] Coordinates R A := rescaleCoordinates γ (blockUnits γ)
  let G : Coordinates R A ≃ₗ[R] Coordinates R A := rescaleCoordinates (fun i => (γ i)⁻¹) (fun _ => 1)
  let H : Coordinates R A ≃ₗ[R] Coordinates R A := rescaleCoordinates (blockUnits γ) (fun _ => weightUnit γ)
  let ones : Fin 3 → Rˣ := fun _ => 1
  let u : (Coordinates R A) := diagonalCoordinates (fun i => (↑(γ i)⁻¹ : R))
  have ones_eta (i : Fin 3) : blockWeight ones i = 1 := by
    simp [ones, CubicSpecification.blockWeight]
  have scale (i : Fin 3) : (blockUnits γ i : R) = blockWeight γ i := rfl
  have invScale (i : Fin 3) : (↑(γ i)⁻¹ : R) * (weightUnit γ : R) = blockWeight γ i := by
    rw [← block_mul_weight γ i, ← mul_assoc, Units.inv_mul, one_mul]
  have invOp : QuadraticOperatorSpecification.applyOperator n ones u (F y) = G y := by
    rw [diagonal_operator]
    apply coordinate_ext
    · intro i
      simp only [G, F, rescale_fst, ← mul_assoc, ← Units.val_mul]
      congr 2
      unit_abel
    · intro i
      have hi : blockUnits (fun j => (γ j)⁻¹) i * blockUnits γ i = 1 := by
        dsimp only [blockUnits]
        unit_abel
      simp only [G, F, rescale_snd, smul_smul, ← Units.val_mul, hi, Units.val_one, one_smul]
  have pair : tracePairing n ones (F x) (G y) = tracePairing n γ x y := by
    simp only [tracePairing_apply, F, G, rescale_fst, rescale_snd, ones_eta, one_mul, Units.val_one,
      one_smul, LinearMap.map_smul₂, LinearMap.smul_apply, smul_eq_mul, scale]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_mul_mul_comm, Units.mul_inv, one_mul]
  have adj : cubicAdjoint n ones (F x) = H (cubicAdjoint n γ x) := by
    apply coordinate_ext
    · intro i
      simp only [F, H, rescale_fst, rescale_snd, CubicSpecification.cubicAdjoint, scale, ones_eta,
        one_mul, QuadraticMap.map_smul, smul_eq_mul]
      simp only [CubicSpecification.blockWeight]
      ring
    · intro i
      simp only [F, H, rescale_fst, rescale_snd, CubicSpecification.cubicAdjoint, scale,
        ones, Units.val_one, one_smul, smul_mul_assoc, mul_smul_comm, map_smul, smul_smul, smul_add]
      rw [neg_mul, mul_right_comm (γ i : R) (x.1 i), block_mul_weight γ i, ← neg_mul,
        one_mul, mul_comm (blockWeight γ (cyclicPrev i)), block_mul_block γ i, mul_neg, neg_mul]
  have cross (z : Coordinates R A) :
      adjointCross n ones (H z) (G y) = F (adjointCross n γ z y) := by
    apply coordinate_ext
    · intro i
      have ⟨h₁, h₂⟩ := block_mul_inv_complement γ i
      simp only [F, G, H, adjointCross_diagonal, rescale_fst, rescale_snd, scale, ones_eta,
        one_mul, Units.val_one, one_smul, LinearMap.map_smul₂, LinearMap.smul_apply, smul_eq_mul]
      rw [mul_mul_mul_comm, h₁, mul_mul_mul_comm (↑(γ (cyclicNext i))⁻¹ : R), mul_comm
        (↑(γ (cyclicNext i))⁻¹ : R) (blockWeight γ (cyclicPrev i)), h₂,
        ← block_mul_weight γ i]
      ring
    · intro i
      simp only [F, G, H, adjointCross_block, rescale_fst, rescale_snd, scale, ones,
        Units.val_one, one_smul, smul_smul, smul_sub, smul_add, smul_mul_assoc,
        mul_smul_comm, map_smul, map_add]
      rw [mul_right_comm (↑(γ i)⁻¹ : R) (y.1 i), invScale,
        mul_comm (blockWeight γ i) (γ i : R), block_mul_weight γ i]
      simp only [one_mul]
      module
  change F (QuadraticOperatorSpecification.applyOperator n γ x y) =
    QuadraticOperatorSpecification.applyOperator n ones (F x) (QuadraticOperatorSpecification.applyOperator n ones u (F y))
  rw [invOp]
  simp only [QuadraticOperatorSpecification.applyOperator, map_sub, map_smul, pair, adj, cross]

private theorem isotope_matrix (x : Coordinates R A) (i j : Fin 3) :
    assemble n (fun _ => 1) (rescaleCoordinates γ (blockUnits γ) x) i j =
      (γ i : R) • assemble n γ x i j := by
  rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · simp [assemble_diagonal, rescale_fst, mul_smul]
  · simp [assemble_forward, rescale_snd, blockUnits, smul_smul]
  · simp [assemble_backward, rescale_snd, blockUnits, smul_smul, mul_comm]

private theorem isotope_unit :
    rescaleCoordinates (A := A) γ (blockUnits γ) cubicUnit =
      diagonalCoordinates (fun i => (γ i : R)) := by
  apply coordinate_ext <;> intro i <;>
    simp [rescale_fst, rescale_snd, CubicSpecification.cubicUnit,
      CubicSpecification.diagonalCoordinates]

private theorem inverse_diagonal_operator :
    QuadraticOperatorSpecification.applyOperator n (fun _ => 1)
      (diagonalCoordinates (fun i => (↑(γ i)⁻¹ : R))) (diagonalCoordinates (fun i => (γ i : R))) =
      diagonalCoordinates (fun i => (↑(γ i)⁻¹ : R)) := by
  rw [diagonal_operator]
  apply coordinate_ext
  · intro i
    simp only [rescale_fst, CubicSpecification.diagonalCoordinates, ← Units.val_mul,
      ← Units.val_pow_eq_pow_val]
    congr 1
    unit_abel
  · intro i
    simp [rescale_snd, CubicSpecification.diagonalCoordinates]

theorem hermitian_isotope : FrameSpecification.isotopeType.{u, v} := by
  intro R A _ _ _ _ _ n h γ
  let F : Coordinates R A ≃ₗ[R] Coordinates R A := rescaleCoordinates γ (blockUnits γ)
  let u : (Coordinates R A) := diagonalCoordinates (fun i => (↑(γ i)⁻¹ : R))
  let v : (Coordinates R A) := diagonalCoordinates (fun i => (γ i : R))
  refine ⟨F, isotope_matrix γ, isotope_unit γ, inverse_diagonal_operator γ, ?_, ?_⟩
  · intro y
    constructor <;> rw [diagonal_operator, diagonal_operator] <;>
      apply coordinate_ext <;> intro i
    all_goals
      simp only [rescale_fst, rescale_snd, smul_smul, ← mul_assoc, ← Units.val_mul, blockUnits]
      first
      | rw [show (_ * _ : Rˣ) = 1 by unit_abel, Units.val_one, one_mul]
      | rw [show (_ * _ : Rˣ) = 1 by unit_abel, Units.val_one, one_smul]
  · intro B _ _
    letI := h.projective
    dsimp only
    intro x y
    simp only [F, rescale_tensor, LinearEquiv.apply_symm_apply, map_blockUnits]
    have eq_u : CubicSpecification.extendCoordinates B u =
        diagonalCoordinates (fun i => (↑(baseChangedWeights B γ i)⁻¹ : B)) := by
      change extendCoordinates B u = _
      rw [extendCoordinates_apply]
      apply coordinate_ext <;> intro i <;>
        simp [u, CubicSpecification.diagonalCoordinates, baseChangedWeights, ← map_inv]
    have etaMap : baseChangedWeights B (blockUnits γ) = blockUnits (baseChangedWeights B γ) :=
      funext fun i => (map_blockUnits γ B i).symm
    rw [eq_u, etaMap]
    exact isotope_operator (n := normBaseChange B n) (baseChangedWeights B γ) x y


open private tensorOperator_apply from LinearAlgebraicGroups.Albert.QuadraticOperators

/-- The scalar-extension condition on a parameter change gives the homomorphism of
the actual weighted Hermitian Jordan structures. Its linear map is the given equivalence. -/
def hermitian_parameterHom (h : IsOctonionNorm n) (γ' : Fin 3 → Rˣ)
    (F : Coordinates R A ≃ₗ[R] Coordinates R A)
    (p : FrameSpecification.IsParameterIso n h γ γ' F) :
    (weightedHermitianJordan γ h).Hom (weightedHermitianJordan γ' h) where
  toLinearMap := F.toLinearMap
  map_unit := p.1
  map_op B _ _ x y := by
    letI := h.projective
    let e := coordinatesBaseChange (R := R) (A := A) B
    apply e.injective
    let U := QuadraticOperatorSpecification.applyOperator (normBaseChange B n) (baseChangedWeights B γ)
    let U' := QuadraticOperatorSpecification.applyOperator (normBaseChange B n) (baseChangedWeights B γ')
    have realize (z t : B ⊗[R] Coordinates R A) :
        e ((weightedHermitianJordan γ h).op B z t) = U (e z) (e t) :=
      tensorOperator_apply γ h B z t
    have realize' (z t : B ⊗[R] Coordinates R A) :
        e ((weightedHermitianJordan γ' h).op B z t) = U' (e z) (e t) :=
      tensorOperator_apply γ' h B z t
    rw [realize']
    have pB := p.2 B (e x) (e y)
    change e (F.toLinearMap.baseChange B (e.symm (U (e x) (e y)))) =
      U' (e (F.toLinearMap.baseChange B (e.symm (e x))))
        (e (F.toLinearMap.baseChange B (e.symm (e y)))) at pB
    simpa only [← realize, LinearEquiv.symm_apply_apply] using pB

theorem hermitian_frame_complements : FrameSpecification.frameComplementsType.{u, v} := by
  intro R A _ _ _ n γ
  dsimp only
  intro i
  refine ⟨frame_trace γ i cubicUnit, frame_adj γ i, ?_, ?_⟩
  · intro m hm
    have other : m = cyclicNext i ∨ m = cyclicPrev i := by
      revert hm
      revert i m
      decide
    have direction (j : Fin 3) :
        cyclicNext (cyclicNext j) = cyclicPrev j ∧ cyclicPrev (cyclicNext j) = j ∧
        cyclicNext (cyclicPrev j) = j ∧ cyclicPrev (cyclicPrev j) = cyclicNext j := by
      revert j
      decide
    have symm (a y b : Coordinates R A) :
        QuadraticOperatorSpecification.triple n γ a y b =
          QuadraticOperatorSpecification.triple n γ b y a := by
      simp only [QuadraticOperatorSpecification.triple, add_comm a b]
      abel
    rcases other with rfl | rfl
    · have hop := frame_off (n := n) γ (cyclicPrev i) cubicUnit
      rw [(direction i).2.2.1, (direction i).2.2.2] at hop
      exact hop.trans (by simp [CubicSpecification.cubicUnit, CubicSpecification.singleBlockCoordinates])
    · have hop := frame_off (n := n) γ (cyclicNext i) cubicUnit
      rw [(direction i).1, (direction i).2.1] at hop
      exact (symm _ _ _).trans (hop.trans (by
        simp [CubicSpecification.cubicUnit, CubicSpecification.singleBlockCoordinates]))
  · intro y
    have comp : (cubicUnit : Coordinates R A) - E i = E (cyclicNext i) + E (cyclicPrev i) := by
      apply coordinate_ext <;> intro j <;> fin_cases i <;> fin_cases j <;>
        simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
          CubicSpecification.cubicUnit, Pi.single_apply, cyclicNext, cyclicPrev,
          next_zero, next_one, next_two, prev_zero, prev_one, prev_two]
    rw [comp]
    have hop := frame_off (n := n) γ i y
    simp only [QuadraticOperatorSpecification.triple, frame_op] at hop
    rw [← hop]
    change _ = y.1 (cyclicNext i) • E (cyclicNext i) + y.1 (cyclicPrev i) • E (cyclicPrev i) + _
    abel

theorem hermitian_isotope_sandwich : FrameSpecification.isotopeSandwichType.{u, v} := by
  intro R A _ _ _ _ _ n h γ
  dsimp only
  let ones : Fin 3 → Rˣ := fun _ => 1
  let u : Coordinates R A := diagonalCoordinates (fun i => (↑(γ i)⁻¹ : R))
  let v : Coordinates R A := diagonalCoordinates (fun i => (γ i : R))
  let U := QuadraticOperatorSpecification.applyOperator n ones
  let M := assemble n ones
  let K := assemble n γ
  let Dγ := M u
  have diagonal : Dγ = Matrix.diagonal (fun i => (↑(γ i)⁻¹ : R) • (1 : A)) :=
    (cubic_matrix_coordinates (n := n) ones).2.1 _
  change (∀ y, M (U u y) = (Dγ * M y) * Dγ) ∧
    (∀ x z, M (QuadraticOperatorSpecification.triple n ones x u z) =
      (M x * Dγ) * M z + (M z * Dγ) * M x)
  refine ⟨?_, ?_⟩
  · intro y
    change M (QuadraticOperatorSpecification.applyOperator n ones (diagonalCoordinates
      (fun i => (↑(γ i)⁻¹ : R))) y) = _
    rw [diagonal_operator, diagonal]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, smul_mul_assoc, one_mul,
      mul_smul_comm, mul_one, smul_smul]
    rcases entry_cases i j with rfl | ⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩
    · simp [M, assemble_diagonal, rescale_fst, Units.val_pow_eq_pow_val, pow_two, mul_smul]
    · simp [M, ones, assemble_forward, rescale_snd, blockUnits, mul_comm]
    · simp [M, ones, assemble_backward, rescale_snd, blockUnits, map_smul]
  · let F : Coordinates R A ≃ₗ[R] Coordinates R A := rescaleCoordinates γ (blockUnits γ)
    have eqF (x : Coordinates R A) (i j : Fin 3) : M (F x) i j = (γ i : R) • K x i j :=
      isotope_matrix γ x i j
    have law (x : Coordinates R A) :
        F (QuadraticOperatorSpecification.applyOperator n γ x cubicUnit) = U (F x) u := by
      have p := isotope_operator (n := n) γ x (cubicUnit : Coordinates R A)
      change F (QuadraticOperatorSpecification.applyOperator n γ x cubicUnit) =
        U (F x) (U u (F cubicUnit)) at p
      have hu : U u (F cubicUnit) = u := by
        change QuadraticOperatorSpecification.applyOperator n ones u (F cubicUnit) = u
        rw [show F cubicUnit = v from isotope_unit γ]
        exact inverse_diagonal_operator γ
      simpa only [hu] using p
    have pol (x z : Coordinates R A) :
        F (QuadraticOperatorSpecification.triple n γ x cubicUnit z) =
          QuadraticOperatorSpecification.triple n ones (F x) u (F z) := by
      simp only [QuadraticOperatorSpecification.triple, map_sub, law, map_add, U]
    have rightScale (x : Coordinates R A) (i j : Fin 3) :
        (M (F x) * Dγ) i j = (↑(γ j)⁻¹ : R) • ((γ i : R) • K x i j) := by
      rw [diagonal, Matrix.mul_diagonal, eqF, mul_smul_comm, mul_one]
    have prod (x z : Coordinates R A) (i j : Fin 3) :
        ((M (F x) * Dγ) * M (F z)) i j = (γ i : R) • (K x * K z) i j := by
      change (∑ k, (M (F x) * Dγ) i k * M (F z) k j) =
        (γ i : R) • ∑ k, K x i k * K z k j
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [rightScale, eqF, smul_mul_assoc, mul_smul_comm, smul_smul]
      have cancel : (γ k : R) * ((↑(γ k)⁻¹ : R) * (γ i : R)) = (γ i : R) := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
      exact congrArg (fun r : R => r • (K x i k * K z k j)) cancel
    intro x z
    obtain ⟨a, rfl⟩ := F.surjective x
    obtain ⟨b, rfl⟩ := F.surjective z
    rw [← pol]
    ext i j
    rw [Matrix.add_apply, prod, prod, eqF, ← smul_add]
    exact congrArg (fun m : Mat A => (γ i : R) • m i j) (assemble_triple_unit γ h a b)

end LinearAlgebraicGroups.Albert
