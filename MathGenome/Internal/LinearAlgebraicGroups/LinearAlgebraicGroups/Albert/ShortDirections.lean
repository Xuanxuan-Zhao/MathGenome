import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.ShortDirections
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.ZornModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.FrameParameters
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntegralZornDirections
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.FrameTangentRank
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SmoothIdentityCriterion
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace LinearAlgebraicGroups.Albert.ShortDirections

open _root_.LinearAlgebraicGroups.Composition
open HermitianSpecification CubicSpecification TrialitySpecification ShortDirectionSpecification
open FrameSpecification

open scoped TensorProduct

universe u
variable {R : Type u} [CommRing R]

private def fromMatrices (x : ThreeMatrices R) : Model R :=
  (fun i => x.1 i i, fun i =>
    Zorn.ofCoordinates (x.1 (cyclicPrev i) (cyclicNext i),
      x.2.1 i, fun j => -x.2.2 j i, x.1 (cyclicNext i) (cyclicPrev i)))

/-- The linear change from the split Hermitian coordinates to three matrices. -/
def coordinateEquiv (R : Type u) [CommRing R] : Model R ≃ₗ[R] ThreeMatrices R where
  toFun := matrixCoordinates
  invFun := fromMatrices
  left_inv x := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      apply (Zorn.coordinates R).injective
      fin_cases i <;>
        simp [fromMatrices, matrixCoordinates, HermitianSpecification.cyclicNext,
          HermitianSpecification.cyclicPrev]
  right_inv x := by
    apply Prod.ext
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · apply Prod.ext
      · rfl
      · ext i j
        change -(-x.2.2 i j) = _
        exact neg_neg _
  map_add' x y := by
    apply Prod.ext
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · apply Prod.ext
      · rfl
      · ext i j
        change -((Zorn.coordinates R (x.2 j)).2.2.1 i +
          (Zorn.coordinates R (y.2 j)).2.2.1 i) = _
        exact neg_add _ _
  map_smul' r x := by
    apply Prod.ext
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · apply Prod.ext
      · rfl
      · ext i j
        change -(r * (Zorn.coordinates R (x.2 j)).2.2.1 i) = _
        exact (mul_neg _ _).symm

theorem matrixCoordinatesEquivalence : MatrixCoordinatesType.{u} :=
  fun R _ => ⟨coordinateEquiv R, fun _ => rfl⟩

private theorem coordinates_unit :
    matrixCoordinates (cubicUnit (R := R) (A := Zorn R)) = ((1 : Square R), 0, 0) := by
  apply Prod.ext
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · apply Prod.ext
    · rfl
    · ext i j
      change -(0 : R) = 0
      exact neg_zero

private theorem zornTrace (x : Zorn R) :
    Composition.AdjointSpecification.trace (ZornSpecification.norm R) x =
      (Zorn.coordinates R x).1 + (Zorn.coordinates R x).2.2.2 := by
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective x
  exact Zorn.trace_formula R a b u v

private def expandedDet (A : Square R) : R :=
  A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 -
    A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0 +
    A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0

private theorem matrixNorm_expanded (A B D : Square R) :
    matrixNorm (A, B, D) = expandedDet A + expandedDet B + expandedDet D -
      ∑ i, ∑ j, (∑ k, A i k * B k j) * D j i := by
  change A.det + B.det + D.det - (A * B * D).trace = _
  rw [Matrix.det_fin_three A, Matrix.det_fin_three B, Matrix.det_fin_three D]
  congr 1

theorem matrixNormFormula : MatrixNormType.{u} := by
  intro R _
  refine ⟨coordinates_unit, ?_⟩
  intro x
  rw [show matrixNorm (matrixCoordinates x) = _ from matrixNorm_expanded _ _ _]
  simp only [splitNorm, CubicSpecification.cubicNorm, CubicSpecification.blockWeight,
    CubicSpecification.weightProduct, Units.val_one, mul_one, one_mul,
    Zorn.norm_formula, zornTrace, Zorn.coordinates_mul, expandedDet,
    Composition.Specification.zornProduct, Composition.Specification.zornNorm,
    dotProduct, cross_apply, Fin.sum_univ_three,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem matrix_mul_inverse (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    (g : Square R) * (↑(g⁻¹) : Square R) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

private theorem action_mul (g h : Matrix.SpecialLinearGroup (Fin 3) R)
    (x : ThreeMatrices R) : matrixAction (g * h) x = matrixAction g (matrixAction h x) := by
  simp only [matrixAction, Matrix.SpecialLinearGroup.coe_mul, mul_inv_rev]
  simp only [← mul_assoc]

private theorem action_one (x : ThreeMatrices R) : matrixAction 1 x = x := by
  simp [matrixAction, Matrix.SpecialLinearGroup.coe_one]

private def actionMatrices (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    ThreeMatrices R ≃ₗ[R] ThreeMatrices R where
  toFun := matrixAction g
  invFun := matrixAction g⁻¹
  left_inv x := by rw [← action_mul, inv_mul_cancel, action_one]
  right_inv x := by rw [← action_mul, mul_inv_cancel, action_one]
  map_add' x y := by simp [matrixAction, mul_add, add_mul]
  map_smul' r x := by simp [matrixAction]

/-- The determinant-one action transported to the split Albert coordinates. -/
def specialLinearAction (R : Type u) [CommRing R] :
    Matrix.SpecialLinearGroup (Fin 3) R →* (Model R ≃ₗ[R] Model R) where
  toFun g := (coordinateEquiv R).trans ((actionMatrices g).trans (coordinateEquiv R).symm)
  map_one' := by
    ext x : 1
    change (coordinateEquiv R).symm (matrixAction 1 (coordinateEquiv R x)) = x
    rw [action_one, LinearEquiv.symm_apply_apply]
  map_mul' g h := by
    ext x : 1
    change (coordinateEquiv R).symm (matrixAction (g * h) (coordinateEquiv R x)) =
      (coordinateEquiv R).symm
        (matrixAction g (coordinateEquiv R ((coordinateEquiv R).symm
          (matrixAction h (coordinateEquiv R x)))))
    rw [action_mul, LinearEquiv.apply_symm_apply]

theorem specialLinearAction_coordinates (g : Matrix.SpecialLinearGroup (Fin 3) R)
    (x : Model R) :
    matrixCoordinates (specialLinearAction R g x) = matrixAction g (matrixCoordinates x) :=
  (coordinateEquiv R).apply_symm_apply _

private theorem action_unit (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    matrixAction g ((1 : Square R), 0, 0) = ((1 : Square R), 0, 0) := by
  simp only [matrixAction, mul_one, mul_zero, zero_mul, matrix_mul_inverse]

private theorem action_norm (g : Matrix.SpecialLinearGroup (Fin 3) R)
    (x : ThreeMatrices R) : matrixNorm (matrixAction g x) = matrixNorm x := by
  have hinv := matrix_mul_inverse g⁻¹
  rw [inv_inv] at hinv
  have hmatrix : (↑g * x.1 * ↑(g⁻¹)) * (↑g * x.2.1) * (x.2.2 * ↑(g⁻¹)) =
      (g : Square R) * (x.1 * x.2.1 * x.2.2) * ↑(g⁻¹) := by
    simp only [mul_assoc, ← mul_assoc (↑(g⁻¹) : Square R) (↑g : Square R), hinv, one_mul]
  simp only [matrixNorm, matrixAction, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
    one_mul, mul_one, hmatrix]
  rw [Matrix.trace_mul_comm, ← mul_assoc, hinv, one_mul]

theorem matrixActionPreservesNorm : MatrixActionType.{u} := by
  intro R _
  refine ⟨specialLinearAction R, specialLinearAction_coordinates, ?_, ?_⟩
  · intro g
    apply (coordinateEquiv R).injective
    change matrixCoordinates (specialLinearAction R g cubicUnit) = matrixCoordinates cubicUnit
    rw [specialLinearAction_coordinates, coordinates_unit, action_unit]
  · intro g x
    rw [(matrixNormFormula R).2, (matrixNormFormula R).2 x,
      specialLinearAction_coordinates, action_norm]

private def mapMatrices {S : Type u} [CommRing S] (f : R →+* S) (x : ThreeMatrices R) :
    ThreeMatrices S :=
  (f.mapMatrix x.1, f.mapMatrix x.2.1, f.mapMatrix x.2.2)

private theorem map_coordinates {S : Type u} [CommRing S] (f : R →+* S) (x : Model R) :
    matrixCoordinates (mapModel f x) = mapMatrices f (matrixCoordinates x) := by
  apply Prod.ext
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · apply Prod.ext
    · rfl
    · ext i j
      exact (map_neg f ((Zorn.coordinates R (x.2 j)).2.2.1 i)).symm

private theorem map_action {S : Type u} [CommRing S] (f : R →+* S)
    (g : Matrix.SpecialLinearGroup (Fin 3) R) (x : ThreeMatrices R) :
    mapMatrices f (matrixAction g x) =
      matrixAction (Matrix.SpecialLinearGroup.map f g) (mapMatrices f x) := by
  simp only [mapMatrices, matrixAction, map_mul, ← map_inv]
  rfl

theorem matrixActionNaturality : MatrixActionNaturalityType.{u} := by
  intro ρ hρ R S _ _ f g x
  apply (coordinateEquiv S).injective
  change matrixCoordinates (mapModel f (ρ R g x)) =
    matrixCoordinates (ρ S (Matrix.SpecialLinearGroup.map f g) (mapModel f x))
  rw [map_coordinates, hρ, map_action, hρ, map_coordinates]

private def slTransvection (p q : Fin 3) (h : p ≠ q) (t : R) :
    Matrix.SpecialLinearGroup (Fin 3) R :=
  ⟨Matrix.transvection p q t, Matrix.det_transvection_of_ne p q h t⟩

private def slOneParameter (p q : Fin 3) (h : p ≠ q) :
    Multiplicative R →* Matrix.SpecialLinearGroup (Fin 3) R where
  toFun t := slTransvection p q h t.toAdd
  map_one' := by
    apply Subtype.ext
    exact Matrix.transvection_zero p q
  map_mul' s t := by
    apply Subtype.ext
    exact (Matrix.transvection_mul_transvection_same p q h s.toAdd t.toAdd).symm

private theorem slTransvection_inv (p q : Fin 3) (h : p ≠ q) (t : R) :
    (slTransvection p q h t)⁻¹ = slTransvection p q h (-t) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change Matrix.transvection p q t * Matrix.transvection p q (-t) = 1
  rw [Matrix.transvection_mul_transvection_same p q h, add_neg_cancel, Matrix.transvection_zero]

private theorem coordinates_axis (i : Fin 3) :
    matrixCoordinates (frameAxis (R := R) (A := Zorn R) i) =
      (Matrix.single i i 1, 0, 0) := by
  apply Prod.ext
  · ext j k
    fin_cases j <;> fin_cases k <;> fin_cases i <;> rfl
  · change ((0 : Square R), (fun _ _ => -(0 : R))) = (0, 0)
    simp only [neg_zero, Pi.zero_def]

private theorem coordinates_first_block (i : Fin 3) :
    matrixCoordinates (singleBlockCoordinates i (ZornSpecification.first R)) =
      (Matrix.single (cyclicPrev i) (cyclicNext i) 1, 0, 0) := by
  apply Prod.ext
  · ext j k
    fin_cases j <;> fin_cases k <;> fin_cases i <;> rfl
  · apply Prod.ext
    · ext j k
      fin_cases i <;> fin_cases j <;> rfl
    · ext j k
      fin_cases i <;> fin_cases k <;> exact neg_zero

private theorem linear_action_axis (p q k : Fin 3) (h : p ≠ q) (t : R) :
    matrixAction (slTransvection p q h t) ((Matrix.single k k 1 : Square R), 0, 0) =
      ((Matrix.single k k 1 : Square R) +
        (if k = q then Matrix.single p q t else 0) -
        (if k = p then Matrix.single p q t else 0), 0, 0) := by
  rw [matrixAction, slTransvection_inv]
  change (Matrix.transvection p q t * Matrix.single k k 1 * Matrix.transvection p q (-t),
    Matrix.transvection p q t * 0, 0 * Matrix.transvection p q (-t)) = _
  have hL : Matrix.single p q t * Matrix.single k k (1 : R) =
      if k = q then Matrix.single p q t else 0 := by
    by_cases hk : k = q
    · subst k
      simp
    · rw [ite_eq_right hk, Matrix.single_mul_single_of_ne (c := t) p q k (Ne.symm hk) 1]
  have hR : Matrix.single k k (1 : R) * Matrix.single p q (-t) =
      if k = p then -(Matrix.single p q t) else 0 := by
    by_cases hk : k = p
    · subst k
      simp [Matrix.single_neg]
    · rw [ite_eq_right hk, Matrix.single_mul_single_of_ne (c := (1 : R)) k k p hk (-t)]
  have hM : (if k = q then Matrix.single p q t else 0) * Matrix.single p q (-t) = 0 := by
    by_cases hk : k = q
    · rw [ite_eq_left hk, Matrix.single_mul_single_of_ne (c := t) p q p (Ne.symm h) (-t)]
    · rw [ite_eq_right hk, zero_mul]
  simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, one_mul, mul_one,
    mul_zero, zero_mul, hL, hR, hM, add_zero, Prod.mk.injEq, and_true]
  simp only [sub_eq_add_neg, apply_ite (fun a : Square R => -a), neg_zero, add_assoc]

theorem transvectionFrame : TransvectionFrameType.{u} := by
  intro R _
  refine ⟨specialLinearAction R, specialLinearAction_coordinates, ?_⟩
  intro i
  let p := cyclicPrev i
  let q := cyclicNext i
  have hpq : p ≠ q := by fin_cases i <;> decide
  have hiq : i ≠ q := by fin_cases i <;> decide
  have hip : i ≠ p := by fin_cases i <;> decide
  refine ⟨slOneParameter p q hpq, fun t => ⟨rfl, ?_, ?_, ?_⟩⟩
  · apply (coordinateEquiv R).injective
    change matrixCoordinates (specialLinearAction R (slTransvection p q hpq t) (frameAxis i)) =
      matrixCoordinates (frameAxis i)
    rw [specialLinearAction_coordinates, coordinates_axis, linear_action_axis]
    simp [hiq, hip]
  · apply (coordinateEquiv R).injective
    rw [map_add, map_smul]
    change matrixCoordinates (specialLinearAction R (slTransvection p q hpq t) (frameAxis q)) =
      matrixCoordinates (frameAxis q) +
        t • matrixCoordinates (singleBlockCoordinates i (ZornSpecification.first R))
    rw [specialLinearAction_coordinates, coordinates_axis, linear_action_axis, coordinates_first_block]
    simp [hpq.symm, p, q]
  · apply (coordinateEquiv R).injective
    rw [map_sub, map_smul]
    change matrixCoordinates (specialLinearAction R (slTransvection p q hpq t) (frameAxis p)) =
      matrixCoordinates (frameAxis p) -
        t • matrixCoordinates (singleBlockCoordinates i (ZornSpecification.first R))
    rw [specialLinearAction_coordinates, coordinates_axis, linear_action_axis, coordinates_first_block]
    simp [hpq, p, q]

section Evaluation

open _root_.Specs.LinearAlgebraicGroups.Albert (QuadraticJordan)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (IsQuadraticDerivation)

private theorem ground_derivation_square (J : QuadraticJordan R (Model R))
    (D : Module.End R (Model R)) (hD : IsQuadraticDerivation J D) (x : Model R) :
    D (J.groundOp x J.unit) =
      J.groundOp (x + D x) J.unit - J.groundOp x J.unit - J.groundOp (D x) J.unit := by
  have h := congrArg (TensorProduct.lid R (Model R))
    (hD.2 R (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] J.unit))
  have hGround (a : Model R) :
      J.op R (1 ⊗ₜ[R] a) (1 ⊗ₜ[R] J.unit) = 1 ⊗ₜ[R] (J.groundOp a J.unit) := by
    apply (TensorProduct.lid R (Model R)).injective
    rw [TensorProduct.lid_tmul, one_smul]
    change _ = ((TensorProduct.lid R (Model R)).conj (J.op R (1 ⊗ₜ[R] a))) J.unit
    rw [LinearEquiv.conj_apply]
    rfl
  simpa [_root_.Specs.LinearAlgebraicGroups.Albert.QuadraticJordan.polar,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    LinearMap.baseChange_tmul, hD.1, ← TensorProduct.tmul_add, hGround]
    using h

private noncomputable def assembleLinear (R : Type u) [CommRing R] :
    Model R →ₗ[R] HermitianSpecification.Mat (Zorn R) :=
  (hermitian (ZornSpecification.norm R) (fun _ => 1)).subtype.comp
    (coordinateMap (Zorn.isOctonion R).toNormLaws (fun _ => 1))

private theorem assembleLinear_apply (x : Model R) :
    assembleLinear R x = assemble (ZornSpecification.norm R) (fun _ => 1) x := rfl

private theorem axis_polar_square (i : Fin 3) (z : Model R) :
    assembleLinear R (modelOp (frameAxis i + z) cubicUnit -
      modelOp (frameAxis i) cubicUnit - modelOp z cubicUnit) =
      diagonalIdempotent i * assembleLinear R z + assembleLinear R z * diagonalIdempotent i := by
  have hs (x : Model R) :
      assembleLinear R (modelOp x cubicUnit) = assembleLinear R x * assembleLinear R x :=
    cubic_operator_matrix_square (fun _ => 1) (Zorn.isOctonion R) x
  have hi : assembleLinear R (frameAxis i) = diagonalIdempotent i :=
    (hermitian_frame (ZornSpecification.norm R) (fun _ => 1)).2.1 i
  rw [map_sub, map_sub, hs, hs, hs, map_add, hi]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  abel

private theorem incident_values (J : QuadraticJordan R (Model R))
    (hunit : J.unit = cubicUnit) (hop : ∀ x y, J.groundOp x y = modelOp x y)
    (D : Module.End R (Model R)) (hD : IsQuadraticDerivation J D) (i : Fin 3) :
    (D (frameAxis i)).1 = 0 ∧ (D (frameAxis i)).2 i = 0 := by
  let z := D (frameAxis i)
  have hz : assembleLinear R z =
      diagonalIdempotent i * assembleLinear R z + assembleLinear R z * diagonalIdempotent i := by
    have h := ground_derivation_square J D hD (frameAxis i)
    have hi : modelOp (frameAxis i) cubicUnit = frameAxis i :=
      (hermitian_frame (ZornSpecification.norm R) (fun _ => 1)).2.2.2.2.2.1 i
    simp only [hunit, hop, hi] at h
    have hs := axis_polar_square i z
    rw [hi] at hs
    exact (congrArg (assembleLinear R) h).trans hs
  let E : HermitianSpecification.Mat (Zorn R) := Matrix.single i i 1
  let X := assembleLinear R z
  have hz' : X = E * X + X * E := hz
  have off (j k : Fin 3) (hj : j ≠ i) (hk : k ≠ i) : X j k = 0 := by
    have h := congrArg (fun A : HermitianSpecification.Mat (Zorn R) => A j k) hz'
    change X j k = (E * X + X * E) j k at h
    rw [Matrix.add_apply, Matrix.single_mul_apply_of_ne 1 i i j k hj X,
      Matrix.mul_single_apply_of_ne 1 i i j k hk X, zero_add] at h
    exact h
  constructor
  · funext j
    have hh : X j j = 0 := by
      by_cases hij : j = i
      · subst j
        have h := congrArg (fun A : HermitianSpecification.Mat (Zorn R) => A i i) hz'
        change X i i = (E * X + X * E) i i at h
        rw [Matrix.add_apply, Matrix.single_mul_apply_same 1 i i i X,
          Matrix.mul_single_apply_same 1 i i i X, one_mul, mul_one] at h
        exact add_eq_left.mp h.symm
      · exact off j j hij hij
    change assemble (ZornSpecification.norm R) (fun _ => 1) z j j = 0 at hh
    rw [assemble_diagonal] at hh
    have h := congrArg (fun a : Zorn R => (Zorn.coordinates R a).1) hh
    change z.1 j * 1 = 0 at h
    exact (mul_one _).symm.trans h
  · have hnext : cyclicNext i ≠ i := by fin_cases i <;> decide
    have hprev : cyclicPrev i ≠ i := by fin_cases i <;> decide
    have hh := off (cyclicNext i) (cyclicPrev i) hnext hprev
    change assemble (ZornSpecification.norm R) (fun _ => 1) z (cyclicNext i) (cyclicPrev i) = 0 at hh
    rw [assemble_forward] at hh
    simpa only [Units.val_one, one_smul] using hh

theorem frameEvaluationSpec : FrameEvaluationType.{u} := by
  intro R _ J hunit hop D hD i
  apply Prod.ext
  · exact (incident_values J hunit hop D hD i).1
  · funext j
    have hsum : ∑ k : Fin 3, D (frameAxis k) = 0 := by
      rw [← map_sum, (hermitian_frame (ZornSpecification.norm R) (fun _ => 1)).1, ← hunit]
      exact hD.1
    let f : Model R →ₗ[R] Zorn R := (LinearMap.proj j).comp (LinearMap.snd R _ _)
    have hsum' := congrArg f hsum
    rw [map_sum, map_zero] at hsum'
    change (∑ k : Fin 3, (D (frameAxis k)).2 j) = 0 at hsum'
    have hz := (incident_values J hunit hop D hD j).2
    have hpair :
        (D (frameAxis (cyclicPrev j))).2 j + (D (frameAxis (cyclicNext j))).2 j = 0 := by
      fin_cases j
      · change (D (frameAxis 0)).2 0 = 0 at hz
        change (∑ k : Fin 3, (D (frameAxis k)).2 0) = 0 at hsum'
        change (D (frameAxis 2)).2 0 + (D (frameAxis 1)).2 0 = 0
        simpa only [Fin.sum_univ_three, hz, zero_add, add_comm] using hsum'
      · change (D (frameAxis 1)).2 1 = 0 at hz
        change (∑ k : Fin 3, (D (frameAxis k)).2 1) = 0 at hsum'
        change (D (frameAxis 0)).2 1 + (D (frameAxis 2)).2 1 = 0
        simpa only [Fin.sum_univ_three, hz, zero_add, add_zero] using hsum'
      · change (D (frameAxis 2)).2 2 = 0 at hz
        change (∑ k : Fin 3, (D (frameAxis k)).2 2) = 0 at hsum'
        change (D (frameAxis 1)).2 2 + (D (frameAxis 0)).2 2 = 0
        simpa only [Fin.sum_univ_three, hz, add_zero, zero_add, add_comm] using hsum'
    change (D (frameAxis i)).2 j =
      if i = cyclicNext j then (D (frameAxis (cyclicNext j))).2 j
      else if i = cyclicPrev j then -((D (frameAxis (cyclicNext j))).2 j) else 0
    by_cases hi : i = cyclicNext j
    · simp [hi]
    · by_cases hp : i = cyclicPrev j
      · rw [ite_eq_right hi, ite_eq_left hp, hp]
        exact eq_neg_of_add_eq_zero_left hpair
      · rw [ite_eq_right hi, ite_eq_right hp]
        have exhaust : ∀ a b : Fin 3, a ≠ cyclicNext b → a ≠ cyclicPrev b → a = b := by
          intro a b
          fin_cases a <;> fin_cases b <;> decide
        rw [exhaust i j hi hp]
        exact hz

theorem frameEvaluationKernel : FrameEvaluationKernelType.{u} := by
  intro R _ J hunit hop D hD
  constructor
  · intro h i
    rw [frameEvaluationSpec R J hunit hop D hD i, h]
    exact Prod.ext rfl (funext fun j => by simp)
  · intro h
    funext j
    change (D (frameAxis (cyclicNext j))).2 j = 0
    rw [h]
    rfl

end Evaluation

section ShortFamilies

set_option backward.isDefEq.respectTransparency false

open _root_.Specs.LinearAlgebraicGroups.Albert
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open IntrinsicCubicSpecification (SplitChart AgreesOnCharts PreservesNorm)
open SplitSpecification (ParaQuadratic)
open IntegralZornDirectionsSpecification (DirectionIndex direction)
open scoped DualNumber

open private extendChart extendChart_apply modelBaseChange_tmul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntrinsicCubic

private theorem splitChart_ground (J : QuadraticJordan R (Model R))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y) :
    ∃ c : SplitChart (ParaQuadratic.ofJordan J) R, c.coordinates = TensorProduct.lid R _ := by
  let K := ParaQuadratic.ofJordan J
  refine ⟨⟨TensorProduct.lid R _, ?_, ?_⟩, rfl⟩
  · change (TensorProduct.lid R (Model R)) (1 ⊗ₜ[R] J.unit) = cubicUnit
    simpa only [TensorProduct.lid_tmul, one_smul] using hu
  · intro x y
    obtain ⟨x, rfl⟩ := (TensorProduct.lid R (Model R)).symm.surjective x
    obtain ⟨y, rfl⟩ := (TensorProduct.lid R (Model R)).symm.surjective y
    simp only [TensorProduct.lid_symm_apply, TensorProduct.lid_tmul, one_smul]
    exact ho x y

private theorem splitChart_over (J : QuadraticJordan R (Model R))
    {c : SplitChart (ParaQuadratic.ofJordan J) R}
    (hc : c.coordinates = TensorProduct.lid R _)
    (S : Type u) [CommRing S] [Algebra R S] :
    ∃ d : SplitChart (ParaQuadratic.ofJordan J) S,
      ∀ a x, d.coordinates (a ⊗ₜ[R] x) = a • mapModel (algebraMap R S) x := by
  refine ⟨extendChart c (Algebra.ofId R S), ?_⟩
  intro a x
  have h := extendChart_apply c (Algebra.ofId R S) (1 ⊗ₜ[R] x)
  rw [hc, TensorProduct.lid_tmul, one_smul, LinearMap.rTensor_tmul] at h
  change (extendChart c (Algebra.ofId R S)).coordinates ((Algebra.ofId R S) 1 ⊗ₜ[R] x) =
    mapModel (algebraMap R S) x at h
  rw [map_one] at h
  have ha : (a ⊗ₜ[R] x : S ⊗[R] Model R) = a • (1 ⊗ₜ[R] x : S ⊗[R] Model R) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [ha, map_smul, h]

private theorem specialLinear_groundIso (g : Matrix.SpecialLinearGroup (Fin 3) R)
    (J : QuadraticJordan R (Model R))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y) :
    (ParaQuadratic.ofJordan J).IsGroundIso (ParaQuadratic.ofJordan J) (specialLinearAction R g) := by
  obtain ⟨K, F, hunit, hground, hAlbert, hF, hcharts, -⟩ := Triality.cubicFrameStabilizer R
  let L := ParaQuadratic.ofJordan K
  let e := specialLinearAction R g
  obtain ⟨c, hc⟩ := splitChart_ground K hunit hground
  have hnorm : PreservesNorm L F e.toLinearMap := by
    refine ⟨?_, ?_⟩
    · rw [show L.unit = cubicUnit from hunit]
      apply (coordinateEquiv R).injective
      change matrixCoordinates (specialLinearAction R g cubicUnit) = matrixCoordinates cubicUnit
      rw [specialLinearAction_coordinates, coordinates_unit, action_unit]
    · intro S _ _ x
      obtain ⟨d, hd⟩ := splitChart_over K hc S
      let eS := specialLinearAction S (Matrix.SpecialLinearGroup.map (algebraMap R S) g)
      have he : ∀ y, d.coordinates (e.toLinearMap.baseChange S y) = eS (d.coordinates y) := by
        intro y
        induction y using TensorProduct.inductionOn with
        | tmul a y =>
          rw [LinearMap.baseChange_tmul, hd, hd, map_smul]
          exact congrArg (a • ·) (matrixActionNaturality specialLinearAction
            (fun _ _ g x => specialLinearAction_coordinates g x) (algebraMap R S) g y)
        | add x y hx hy => simp only [map_add, hx, hy]
      rw [(hcharts S d _).2.2, (hcharts S d x).2.2, he]
      change splitNorm (specialLinearAction S (Matrix.SpecialLinearGroup.map (algebraMap R S) g)
        (d.coordinates x)) = splitNorm (d.coordinates x)
      rw [(matrixNormFormula S).2, (matrixNormFormula S).2 (d.coordinates x),
        specialLinearAction_coordinates, action_norm]
  have he := (L.isIso_iff_ground L e).mp
    ((intrinsic_norm_automorphisms L F hAlbert hF e).mpr hnorm)
  refine ⟨?_, fun x y => ?_⟩
  · change e J.unit = J.unit
    have h := he.1
    change e K.unit = K.unit at h
    simpa only [hu, hunit] using h
  · have hh := he.2 x y
    change e (K.groundOp x y) = K.groundOp (e x) (e y) at hh
    change e (J.groundOp x y) = J.groundOp (e x) (e y)
    simpa only [hground, ho] using hh

private def firstFamily (i : Fin 3) : Multiplicative R →* (Model R ≃ₗ[R] Model R) :=
  (specialLinearAction R).comp
    (slOneParameter (cyclicPrev i) (cyclicNext i) (by fin_cases i <;> decide))

private theorem firstFamily_evaluates (i : Fin 3) (t : R) :
    let a := firstFamily i (Multiplicative.ofAdd t)
    a (frameAxis i) = frameAxis i ∧
    a (frameAxis (cyclicNext i)) = frameAxis (cyclicNext i) +
      t • singleBlockCoordinates i (ZornSpecification.first R) ∧
    a (frameAxis (cyclicPrev i)) = frameAxis (cyclicPrev i) -
      t • singleBlockCoordinates i (ZornSpecification.first R) := by
  obtain ⟨ρ, hρ, h⟩ := transvectionFrame R
  obtain ⟨τ, hτ⟩ := h i
  have hρ' (g : Matrix.SpecialLinearGroup (Fin 3) R) (x : Model R) :
      ρ g x = specialLinearAction R g x :=
    (coordinateEquiv R).injective ((hρ g x).trans (specialLinearAction_coordinates g x).symm)
  have hτ' : τ (Multiplicative.ofAdd t) =
      slTransvection (cyclicPrev i) (cyclicNext i) (by fin_cases i <;> decide) t :=
    Subtype.ext (hτ t).1
  have heval := (hτ t).2
  rw [hρ', hρ', hρ', hτ'] at heval
  exact heval

private theorem firstFamily_natural {S : Type u} [CommRing S]
    (f : R →+* S) (i : Fin 3) (t : R) (x : Model R) :
    mapModel f (firstFamily i (Multiplicative.ofAdd t) x) =
      firstFamily i (Multiplicative.ofAdd (f t)) (mapModel f x) := by
  have he : Matrix.SpecialLinearGroup.map f
      (slOneParameter (cyclicPrev i) (cyclicNext i) (by fin_cases i <;> decide)
        (Multiplicative.ofAdd t)) =
      slOneParameter (cyclicPrev i) (cyclicNext i) (by fin_cases i <;> decide)
        (Multiplicative.ofAdd (f t)) := by
    apply Subtype.ext
    ext p q
    change f (Matrix.transvection (cyclicPrev i) (cyclicNext i) t p q) =
      Matrix.transvection (cyclicPrev i) (cyclicNext i) (f t) p q
    simp only [Matrix.transvection, Matrix.add_apply, map_add, Matrix.one_apply,
      Matrix.single_apply, apply_ite f, map_zero, map_one]
  unfold firstFamily
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← he]
  exact matrixActionNaturality specialLinearAction (fun _ _ g x => specialLinearAction_coordinates g x) f _ x

private noncomputable def octonionConjugator (R : Type u) [CommRing R] (j : DirectionIndex) :
    frameStabilizer (R := R) :=
  IntegralZornDirections.albertAction R (IntegralZornDirections.directionLift j)

/-- Integral one-parameter families obtained by conjugating the matrix transvections. -/
noncomputable def shortFamily (R : Type u) [CommRing R] (i : Fin 3) (j : DirectionIndex) :
    Multiplicative R →* (Model R ≃ₗ[R] Model R) :=
  (MulAut.conj (octonionConjugator R j).val).toMonoidHom.comp (firstFamily i)

private theorem shortFamily_apply (i : Fin 3) (j : DirectionIndex) (t : R) (x : Model R) :
    shortFamily R i j (Multiplicative.ofAdd t) x =
      (octonionConjugator R j).val
        (firstFamily i (Multiplicative.ofAdd t) ((octonionConjugator R j).val.symm x)) := rfl

private theorem shortFamily_natural {S : Type u} [CommRing S]
    (f : R →+* S) (i : Fin 3) (j : DirectionIndex) (t : R) (x : Model R) :
    mapModel f (shortFamily R i j (Multiplicative.ofAdd t) x) =
      shortFamily S i j (Multiplicative.ofAdd (f t)) (mapModel f x) := by
  have h (y : Model R) : mapModel f ((octonionConjugator R j).val y) =
      (octonionConjugator S j).val (mapModel f y) :=
    IntegralZornDirections.albertAction_natural f _ y
  rw [shortFamily_apply, shortFamily_apply, h, firstFamily_natural]
  congr 2
  apply (octonionConjugator S j).val.injective
  rw [← h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

private theorem conjugator_direction (i : Fin 3) (j : DirectionIndex) :
    (octonionConjugator R j).val (singleBlockCoordinates i (ZornSpecification.first R)) =
      singleBlockCoordinates i (direction R j) := by
  rw [octonionConjugator, IntegralZornDirections.albertAction_apply]
  apply Prod.ext
  · rfl
  · funext k
    let g := (IntegralZornDirections.extendAutomorphism R (IntegralZornDirections.directionLift j)).toLinearEquiv
    change g ((Pi.single i (ZornSpecification.first R) : Fin 3 → Zorn R) k) =
      (Pi.single i (direction R j) : Fin 3 → Zorn R) k
    by_cases h : k = i
    · subst k
      rw [Pi.single_eq_same, Pi.single_eq_same]
      exact IntegralZornDirections.extendAutomorphism_direction R j
    · simp [Pi.single_eq_of_ne h]

private theorem shortFamily_evaluates (i : Fin 3) (j : DirectionIndex) (t : R) :
    let a := shortFamily R i j (Multiplicative.ofAdd t)
    a (frameAxis i) = frameAxis i ∧
    a (frameAxis (cyclicNext i)) = frameAxis (cyclicNext i) +
      t • singleBlockCoordinates i (direction R j) ∧
    a (frameAxis (cyclicPrev i)) = frameAxis (cyclicPrev i) -
      t • singleBlockCoordinates i (direction R j) := by
  have hf (k : Fin 3) := (octonionConjugator R j).property.1 k
  have hs (k : Fin 3) : (octonionConjugator R j).val.symm (frameAxis k) = frameAxis k :=
    (LinearEquiv.symm_apply_eq _).mpr (hf k).symm
  obtain ⟨h, hp, hm⟩ := firstFamily_evaluates i t
  simp only [shortFamily_apply, hs, h, hp, hm, map_add, map_sub, map_smul, hf,
    conjugator_direction, and_self]

private theorem shortFamily_groundIso (J : QuadraticJordan R (Model R))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y)
    (i : Fin 3) (j : DirectionIndex) (t : R) :
    (ParaQuadratic.ofJordan J).IsGroundIso (ParaQuadratic.ofJordan J)
      (shortFamily R i j (Multiplicative.ofAdd t)) := by
  let K := ParaQuadratic.ofJordan J
  let c := octonionConjugator R j
  have h (a : frameStabilizer (R := R)) : K.IsGroundIso K a.val :=
    (K.isIso_iff_ground K _).mp (((Triality.frameLaw R K hu ho a.val).mp a.property).2)
  have h₀ : K.IsGroundIso K (firstFamily i (Multiplicative.ofAdd t)) :=
    specialLinear_groundIso _ J hu ho
  refine ⟨?_, ?_⟩
  · change shortFamily R i j (Multiplicative.ofAdd t) J.unit = J.unit
    rw [shortFamily_apply, show c.val.symm J.unit = J.unit from (h c⁻¹).1,
      show firstFamily i (Multiplicative.ofAdd t) J.unit = J.unit from h₀.1]
    exact (h c).1
  · intro x y
    change shortFamily R i j (Multiplicative.ofAdd t) (K.groundOp x y) =
      K.groundOp (shortFamily R i j (Multiplicative.ofAdd t) x)
        (shortFamily R i j (Multiplicative.ofAdd t) y)
    simp only [shortFamily_apply]
    rw [show ∀ a b, c.val.symm (K.groundOp a b) =
      K.groundOp (c.val.symm a) (c.val.symm b) from (h c⁻¹).2, h₀.2, (h c).2]


private noncomputable def integralShortFamilies : IntegralShortFamilies.{u} where
  family := shortFamily
  natural := shortFamily_natural
  preserves _R _ J hu ho i j t :=
    let K := ParaQuadratic.ofJordan J
    (K.isIso_iff_ground K _).mpr (shortFamily_groundIso J hu ho i j t)
  evaluates _ _ := shortFamily_evaluates

theorem integralShortDirections : IntegralShortFamiliesType.{u} := ⟨integralShortFamilies⟩

open private modelBaseChange_operator mapModel_add from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntrinsicCubic
open private map_octonion_zero map_octonion_smul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.Triality
open private map_direction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntegralZornDirections
open private exists_infinitesimal infinitesimal_quadratic_iff infinitesimal_apply
  scalar_eps_tmul secondCoefficient secondCoefficient_tmul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme

private theorem modelBaseChange_pure (S : Type u) [CommRing S] [Algebra R S] (s : S) (x : Model R) :
    modelBaseChange R S (s ⊗ₜ[R] x) = s • mapModel (algebraMap R S) x :=
  modelBaseChange_tmul s x

private theorem mapModel_smul {S : Type u} [CommRing S] (f : R →+* S) (a : R) (x : Model R) :
    mapModel f (a • x) = f a • mapModel f x :=
  Prod.ext (funext fun i => map_mul f a (x.1 i))
    (funext fun i => map_octonion_smul f a (x.2 i))

private theorem mapModel_comp {S T : Type u} [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (x : Model R) :
    mapModel g (mapModel f x) = mapModel (g.comp f) x := rfl

private theorem mapModel_id (x : Model R) : mapModel (RingHom.id R) x = x := rfl

private theorem modelBaseChange_natural {S T : Type u} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) (x : S ⊗[R] Model R) :
    modelBaseChange R T (f.toLinearMap.rTensor (Model R) x) =
      mapModel f.toRingHom (modelBaseChange R S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [LinearMap.rTensor_tmul, modelBaseChange_pure, modelBaseChange_pure,
      mapModel_smul, mapModel_comp]
    rw [show f.toRingHom.comp (algebraMap R S) = algebraMap R T from f.comp_algebraMap]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    exact (mapModel_add f.toRingHom _ _).symm

private theorem splitChart_canonical (J : QuadraticJordan R (Model R))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y)
    (S : Type u) [CommRing S] [Algebra R S] :
    ∃ c : SplitChart (ParaQuadratic.ofJordan J) S, c.coordinates = modelBaseChange R S := by
  obtain ⟨c, hc⟩ := splitChart_ground J hu ho
  obtain ⟨d, hd⟩ := splitChart_over J hc S
  refine ⟨d, ?_⟩
  refine LinearEquiv.ext fun x => ?_
  exact TensorProduct.inductionOn (motive := fun z =>
    d.coordinates z = modelBaseChange R S z) x
    (fun a z => (hd a z).trans (modelBaseChange_pure S a z).symm)
    (fun a b ha hb => by simp only [map_add, ha, hb])

private theorem mapModel_axis {S : Type u} [CommRing S] (f : R →+* S) (i : Fin 3) :
    mapModel f (frameAxis i) = frameAxis i := by
  apply Prod.ext <;> funext j
  · change f ((Pi.single i 1 : Fin 3 → R) j) = (Pi.single i 1 : Fin 3 → S) j
    by_cases h : j = i <;> simp [h]
  · exact map_octonion_zero f

private theorem mapModel_direction {S : Type u} [CommRing S] (f : R →+* S) (i : Fin 3)
    (j : DirectionIndex) :
    mapModel f (singleBlockCoordinates i (direction R j)) =
      singleBlockCoordinates i (direction S j) := by
  apply Prod.ext <;> funext k
  · exact map_zero f
  · change ZornSpecification.mapCoordinates f ((Pi.single i (direction R j) : Fin 3 → Zorn R) k) =
      (Pi.single i (direction S j) : Fin 3 → Zorn S) k
    by_cases h : k = i
    · subst k
      rw [Pi.single_eq_same, Pi.single_eq_same, map_direction]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_octonion_zero]

set_option maxHeartbeats 800000 in
private theorem shortFamily_differential (k : Type u) [Field k] (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y)
    (i : Fin 3) (j : DirectionIndex) (c : k) :
    ∃ D : splitDerivations J,
      (∀ x, shortFamily (DualNumber k) i j (Multiplicative.ofAdd (TrivSqZeroExt.inr c))
        (modelBaseChange k (DualNumber k) x) =
          modelBaseChange k (DualNumber k) (infinitesimal D.val x)) ∧
      frameEvaluation k D.val = c • Pi.single i (direction k j) := by
  let E := DualNumber k
  let B := modelBaseChange k E
  let t : E := TrivSqZeroExt.inr c
  let a := shortFamily E i j (Multiplicative.ofAdd t)
  let g := B.trans (a.trans B.symm)
  let r := TrivSqZeroExt.fstHom k k k
  have hz : ∀ x : Model k, dualModuleReduction (g (1 ⊗ₜ[k] x)) = 1 ⊗ₜ[k] x := by
    intro x
    apply (modelBaseChange k k).injective
    change modelBaseChange k k (r.toLinearMap.rTensor (Model k) (g (1 ⊗ₜ[k] x))) = _
    rw [modelBaseChange_natural, modelBaseChange_pure]
    change mapModel r.toRingHom (B (B.symm (a (B (1 ⊗ₜ[k] x))))) =
      1 • mapModel (algebraMap k k) x
    rw [B.apply_symm_apply, shortFamily_natural]
    change shortFamily k i j (Multiplicative.ofAdd (r t))
      (mapModel r.toRingHom (B (1 ⊗ₜ[k] x))) = _
    rw [show r t = 0 from rfl, show Multiplicative.ofAdd (0 : k) = 1 from rfl,
      map_one]
    change mapModel r.toRingHom (modelBaseChange k E (1 ⊗ₜ[k] x)) =
      (1 : k) • mapModel (algebraMap k k) x
    have h := (modelBaseChange_pure E (1 : E) x).trans
      (one_smul E (mapModel (algebraMap k E) x))
    exact (congrArg (mapModel r.toRingHom) h).trans
      ((mapModel_comp _ _ _).trans ((congrArg (fun f => mapModel f x)
        r.comp_algebraMap).trans (one_smul k (mapModel (algebraMap k k) x)).symm))
  obtain ⟨D, hD⟩ := exists_infinitesimal g.toLinearMap hz
  have hagree (x : E ⊗[k] Model k) : a (B x) = B (infinitesimal D x) := by
    rw [← hD]
    exact (B.apply_symm_apply _).symm
  have hpres : PreservesQuadratic J E (infinitesimal D) := by
    obtain ⟨c, hc⟩ := splitChart_canonical J hu ho E
    have hunit : B (1 ⊗ₜ[k] J.unit) = cubicUnit := by
      have h := c.unit
      rw [hc] at h
      exact h
    have hop (x y : E ⊗[k] Model k) : B (J.op E x y) = modelOp (B x) (B y) := by
      have h := c.op x y
      rw [hc] at h
      exact h
    obtain ⟨JE, _, huE, hoE, -, -, -, -⟩ := Triality.cubicFrameStabilizer E
    have h := shortFamily_groundIso JE huE hoE i j t
    refine ⟨?_, fun x y => ?_⟩
    · apply B.injective
      rw [← hagree, hunit]
      have hh := h.1
      change a JE.unit = JE.unit at hh
      simpa only [huE] using hh
    · apply B.injective
      rw [← hagree, hop, hop, ← hagree, ← hagree]
      have hh := h.2 (B x) (B y)
      change a (JE.groundOp (B x) (B y)) = JE.groundOp (a (B x)) (a (B y)) at hh
      simpa only [hoE] using hh
  refine ⟨⟨D, (infinitesimal_quadratic_iff J D).mp hpres⟩, hagree, ?_⟩
  have haxis (k' : Fin 3) : B (1 ⊗ₜ[k] (frameAxis k' : Model k)) = frameAxis k' := by
    rw [modelBaseChange_pure]
    exact (one_smul E _).trans (mapModel_axis (algebraMap k E) k')
  let z : Model k := singleBlockCoordinates i (direction k j)
  have hdir : B (ε ⊗ₜ[k] (c • z)) = t • singleBlockCoordinates i (direction E j) := by
    rw [modelBaseChange_pure E (ε : E) (c • z), mapModel_smul (algebraMap k E) c z,
      show mapModel (algebraMap k E) z = singleBlockCoordinates i (direction E j)
        from mapModel_direction (algebraMap k E) i j]
    let v : Model E := singleBlockCoordinates i (direction E j)
    have ht : (ε : E) * algebraMap k E c = t := by
      calc
        _ = TrivSqZeroExt.inl c * (ε : E) := mul_comm _ _
        _ = c • (ε : E) := TrivSqZeroExt.inl_mul_eq_smul _ _
        _ = _ := (DualNumber.inr_eq_smul_eps c).symm
    exact (mul_smul (ε : E) (algebraMap k E c) v).symm.trans
      (congrArg (fun a : E => a • v) ht)
  have hcoeff (k' : Fin 3) :
      a (frameAxis k') = B ((1 ⊗ₜ[k] frameAxis k') + ε ⊗ₜ[k] D (frameAxis k')) := by
    rw [← haxis k', hagree, infinitesimal_apply, LinearMap.baseChange_tmul, scalar_eps_tmul]
  obtain ⟨h₀, hpos, hneg⟩ := shortFamily_evaluates i j t
  let s : (E ⊗[k] Model k) →ₗ[k] Model k := secondCoefficient
  have hs₀ (v : Model k) : s (1 ⊗ₜ[k] v) = 0 :=
    (secondCoefficient_tmul (1 : E) v).trans (zero_smul k v)
  have hs₁ (v : Model k) : s (ε ⊗ₜ[k] v) = v :=
    (secondCoefficient_tmul (ε : E) v).trans (one_smul k v)
  have hs (v w : Model k) : s (1 ⊗ₜ[k] v + ε ⊗ₜ[k] w) = w :=
    (s.map_add _ _).trans ((congrArg₂ (· + ·) (hs₀ v) (hs₁ w)).trans (zero_add w))
  have hread (l : Fin 3) (v : Model k)
      (he : a (frameAxis l) = B (1 ⊗ₜ[k] frameAxis l + ε ⊗ₜ[k] v)) :
      D (frameAxis l) = v :=
    (hs (frameAxis l) _).symm.trans
      ((congrArg s (B.injective ((hcoeff l).symm.trans he))).trans (hs (frameAxis l) v))
  have hzero : D (frameAxis i) = 0 := by
    apply hread i 0
    rw [TensorProduct.tmul_zero, add_zero, haxis i]
    exact h₀
  have hplus : D (frameAxis (cyclicNext i)) = c • z := by
    apply hread (cyclicNext i) (c • z)
    rw [B.map_add, haxis, hdir]
    exact hpos
  have hminus : D (frameAxis (cyclicPrev i)) = -(c • z) := by
    apply hread (cyclicPrev i) (-(c • z))
    have hn : B (ε ⊗ₜ[k] (-(c • z))) = -(t • singleBlockCoordinates i (direction E j)) :=
      (congrArg B (TensorProduct.tmul_neg (ε : E) (c • z))).trans
        ((B.map_neg ((ε : E) ⊗ₜ[k] (c • z))).trans (congrArg Neg.neg hdir))
    rw [B.map_add, haxis, hn]
    exact hneg.trans (sub_eq_add_neg (frameAxis (cyclicPrev i) : Model E) _)
  funext l
  change (D (frameAxis (cyclicNext l))).2 l =
    c • (Pi.single i (direction k j) : Fin 3 → Zorn k) l
  by_cases hl : l = i
  · subst l
    rw [hplus]
    exact rfl
  · have hcases : ∀ l i : Fin 3, l ≠ i → cyclicNext l = i ∨ cyclicNext l = cyclicPrev i := by
      decide
    rw [Pi.single_eq_of_ne hl, smul_zero]
    rcases hcases l i hl with h | h
    · rw [h, hzero]
      rfl
    · rw [h, hminus]
      change -(c • (Pi.single i (direction k j) : Fin 3 → Zorn k) l) = 0
      rw [Pi.single_eq_of_ne hl, smul_zero, neg_zero]

theorem shortDifferentials : ShortDifferentialsType.{u} := by
  refine ⟨integralShortFamilies, ?_⟩
  intro k _ J hu ho
  choose D h using fun i j => shortFamily_differential k J hu ho i j 1
  exact ⟨D, fun i j => (h i j).1, fun i j =>
    (h i j).2.trans (one_smul k (Pi.single i (direction k j) : Fin 3 → Zorn k))⟩


section TangentRank

set_option maxHeartbeats 600000

variable {k : Type u} [Field k] {J : QuadraticJordan k (Model k)}

private theorem rankNullity {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [Module.Finite k V] (e : V →ₗ[k] W) :
    Module.finrank k e.range + Module.finrank k e.ker = Module.finrank k V :=
  e.finrank_range_add_finrank_ker

private def shortSum (D : Fin 3 → DirectionIndex → splitDerivations J)
    (t : Fin 3 → DirectionIndex → k) : splitDerivations J :=
  ∑ i, ∑ j, t i j • D i j

private theorem shortSum_evaluation (D : Fin 3 → DirectionIndex → splitDerivations J)
    (hD : ∀ i j, frameEvaluation k (D i j).val = Pi.single i (direction k j))
    (t : Fin 3 → DirectionIndex → k) (l : Fin 3) :
    frameEvaluation k (shortSum D t).val l =
      ∑ j, t l j • IntegralZornDirections.directionBasis k j := by
  classical
  let e := (frameEvaluation k).domRestrict (splitDerivations J)
  change e (shortSum D t) l = _
  have h (i j) : e (D i j) = Pi.single i (direction k j) := hD i j
  simp only [shortSum, map_sum, map_smul, h, Finset.sum_apply, Pi.smul_apply,
    Pi.single_apply, smul_ite, smul_zero]
  rw [Finset.sum_comm, Finset.sum_congr rfl]
  intro j _
  simp only [eq_comm (a := l), Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _),
    IntegralZornDirections.directionBasis_apply]

private theorem evaluation_surjective (D : Fin 3 → DirectionIndex → splitDerivations J)
    (hD : ∀ i j, frameEvaluation k (D i j).val = Pi.single i (direction k j)) :
    Function.Surjective ((frameEvaluation k).domRestrict (splitDerivations J)) := by
  intro z
  let b := IntegralZornDirections.directionBasis k
  let t : Fin 3 → DirectionIndex → k := fun i j => b.repr (z i) j
  refine ⟨shortSum D t, ?_⟩
  funext i
  change frameEvaluation k (shortSum D t).val i = z i
  rw [shortSum_evaluation D hD]
  exact b.sum_repr (z i)

private def frameDerivationsEquiv (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y) :
    FrameTangentSpecification.frameDerivations J ≃ₗ[k]
      LinearMap.ker ((frameEvaluation k).domRestrict (splitDerivations J)) where
  toFun D := ⟨⟨D.val, D.property.1⟩,
    (frameEvaluationKernel k J hu ho D.val D.property.1).mpr D.property.2⟩
  invFun D := ⟨D.val.val, D.val.property,
    (frameEvaluationKernel k J hu ho D.val.val D.val.property).mp D.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option maxHeartbeats 2500000 in
theorem splitTangentRank : SplitTangentRankType.{u} := by
  intro k _ J hu ho
  obtain ⟨F, hF⟩ := shortDifferentials
  obtain ⟨D, -, hD⟩ := hF k J hu ho
  obtain ⟨G, m, E, hE, hrank⟩ := FrameTangent.frameTangentRank k J hu ho
  let e := (frameEvaluation k).domRestrict (splitDerivations J)
  have hs : Function.Surjective e := evaluation_surjective D hD
  refine ⟨hs, ?_, ?_⟩
  · ext d
    change frameEvaluation k d.val = 0 ↔
      IsQuadraticDerivation J d.val ∧ ∀ i, d.val (frameAxis i) = 0
    exact (frameEvaluationKernel k J hu ho d.val d.property).trans
      (and_iff_right d.property).symm
  · let : Module.Finite k (Zorn k) := Module.Finite.of_basis
      (IntegralZornDirections.directionBasis k)
    have hz : Module.finrank k (Zorn k) = 8 := by
      rw [Module.finrank_eq_card_basis (IntegralZornDirections.directionBasis k)]
      decide
    have ht : Module.finrank k (Fin 3 → Zorn k) = 24 := by
      rw [Module.finrank_pi_fintype]
      simp [hz]
    let : Module.Finite k (Model k) := inferInstance
    let : Module.Finite k (Module.End k (Model k)) := inferInstance
    let hfinite : Module.Finite k (splitDerivations J) := inferInstance
    have hd : Module.finrank k (LinearMap.range e) + Module.finrank k (LinearMap.ker e) =
        Module.finrank k (splitDerivations J) := by
      exact @rankNullity k ‹Field k› (splitDerivations J) (Fin 3 → Zorn k)
        (splitDerivations J).addCommGroup (splitDerivations J).module Pi.addCommGroup
        inferInstance hfinite e
    rw [LinearMap.range_eq_top.mpr hs, finrank_top, ht,
      ← (frameDerivationsEquiv J hu ho).finrank_eq, hrank] at hd
    exact hd.symm


theorem frameLieKernel : FrameLieKernelType.{u} := by
  intro k _ J hu ho
  obtain ⟨G, m, e, he, hrank⟩ := FrameTangent.frameTangentRank k J hu ho
  let := m.addGroup
  let := m.module
  let f := frameDerivationsEquiv J hu ho
  refine ⟨G, m, f.symm.trans e, ?_, f.finrank_eq.symm.trans hrank⟩
  intro D x
  exact he (f.symm D) x

end TangentRank

end ShortFamilies

section IntegralParametrization

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open _root_.Specs.LinearAlgebraicGroups.Albert
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open LinearMap.GeneralLinearGroup (congrLinearEquiv generalLinearEquiv)
open IntegralZornDirectionsSpecification (DirectionIndex direction)
open scoped DualNumber

open private matrixActionEquiv matrixAction_natural quotientMatrixEquiv evaluateMatrix
  evaluateCoordinates_entry from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme

private theorem exists_integralPresentation : Nonempty IntegralPresentation := by
  obtain ⟨J, _, hu, hop, _, _, _, _⟩ := Triality.cubicFrameStabilizer ℤ
  let b := (Pi.basisFun ℤ (Fin 3)).prod
    (Pi.basis fun _ : Fin 3 => IntegralZornDirections.directionBasis ℤ)
  let e : (Fin 3 ⊕ (Σ _ : Fin 3, DirectionIndex)) ≃ Fin 27 :=
    Fintype.equivFinOfCardEq (by decide)
  let b₀ : Module.Basis (Fin 27) ℤ (Model ℤ) := b.reindex e
  obtain ⟨H, p, hp, hH, _⟩ := LinearAlgebraicGroups.Albert.Automorphisms.quadraticCoordinates b₀ J
  refine ⟨⟨J, hu, hop, b₀, H, p, hp, fun S _ _ g => ?_⟩⟩
  have h := hH S g
  dsimp only at h
  rw [h]
  constructor
  · rintro ⟨h, hq⟩
    exact ⟨h J.unit (by simp), hq⟩
  · rintro ⟨h, hq⟩
    exact ⟨fun v hv => (Option.mem_some_iff.mp hv) ▸ h, hq⟩

private abbrev IsSplitAutomorphism {S : Type*} [CommRing S] (a : Model S ≃ₗ[S] Model S) : Prop :=
  a cubicUnit = cubicUnit ∧ ∀ x y, a (modelOp x y) = modelOp (a x) (a y)

private def splitAutomorphisms (S : Type*) [CommRing S] : Subgroup (Model S ≃ₗ[S] Model S) :=
  (operationStabilizer modelOp {cubicUnit}).comap (generalLinearEquiv S (Model S)).symm.toMonoidHom

private theorem mem_splitAutomorphisms {S : Type*} [CommRing S] (a : Model S ≃ₗ[S] Model S) :
    a ∈ splitAutomorphisms S ↔ IsSplitAutomorphism a := by
  change ((∀ x ∈ ({cubicUnit} : Set (Model S)), a x = x) ∧
    (∀ x y, a (modelOp x y) = modelOp (a x) (a y))) ↔ IsSplitAutomorphism a
  simp only [Set.mem_singleton_iff, forall_eq]

private theorem preserves_splitCoordinates {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (J : QuadraticJordan R (Model R)) (hu : J.unit = cubicUnit)
    (ho : ∀ x y, J.groundOp x y = modelOp x y)
    (g : Module.End S (S ⊗[R] Model R)) (a : Model S ≃ₗ[S] Model S)
    (h : ∀ x, a (modelBaseChange R S x) = modelBaseChange R S (g x)) :
    PreservesQuadratic J S g ↔ IsSplitAutomorphism a := by
  obtain ⟨c, hc⟩ := splitChart_canonical J hu ho S
  let B := modelBaseChange R S
  have hunit : B (1 ⊗ₜ[R] J.unit) = cubicUnit := by
    have h := c.unit
    rw [hc] at h
    exact h
  have hop (x y : S ⊗[R] Model R) : B (J.op S x y) = modelOp (B x) (B y) := by
    have h := c.op x y
    rw [hc] at h
    exact h
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, fun x y => ?_⟩
    · rw [← hunit, h, h₁]
    · obtain ⟨x, rfl⟩ := B.surjective x
      obtain ⟨y, rfl⟩ := B.surjective y
      rw [← hop, h, h₂, hop, h, h]
  · rintro ⟨h₁, h₂⟩
    refine ⟨B.injective ?_, fun x y => B.injective ?_⟩
    · rw [← h, hunit, h₁]
    · rw [← h, hop, h₂, hop, h, h]

private def albertMatrix (P : IntegralPresentation) (S : Type) [CommRing S] [Algebra ℤ S] :
    Matrix.GeneralLinearGroup (Fin 27) S ≃* (Model S ≃ₗ[S] Model S) :=
  (matrixActionEquiv P.basis S).trans
    ((congrLinearEquiv (modelBaseChange ℤ S)).trans (generalLinearEquiv S (Model S)))

private theorem albertMatrix_apply (P : IntegralPresentation) {S : Type} [CommRing S] [Algebra ℤ S]
    (g : Matrix.GeneralLinearGroup (Fin 27) S) :
    ∀ x, albertMatrix P S g (modelBaseChange ℤ S x) =
      modelBaseChange ℤ S (_root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms.matrixAction P.basis S g x) := by
  intro x
  change modelBaseChange ℤ S (_root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms.matrixAction P.basis S g
    ((modelBaseChange ℤ S).symm (modelBaseChange ℤ S x))) = _
  rw [LinearEquiv.symm_apply_apply]

private def albertPoints (P : IntegralPresentation) (S : Type) [CommRing S] [Algebra ℤ S] :
    (P.Coordinates →ₐ[ℤ] S) ≃ splitAutomorphisms S :=
  (quotientMatrixEquiv P.cutsOut).trans
    (Equiv.subtypeEquiv (albertMatrix P S).toEquiv fun g => by
      rw [P.presents S, mem_splitAutomorphisms]
      exact preserves_splitCoordinates P.jordan P.unit_eq P.ground_op _ _
        (albertMatrix_apply P g))

private theorem albertPoints_natural (P : IntegralPresentation) {S T : Type} [CommRing S] [CommRing T]
    [Algebra ℤ S] [Algebra ℤ T]
    (f : S →ₐ[ℤ] T) (a : P.Coordinates →ₐ[ℤ] S) (x : Model S) :
    mapModel f.toRingHom ((albertPoints P S a).val x) =
      (albertPoints P T (f.comp a)).val (mapModel f.toRingHom x) := by
  let q := Ideal.Quotient.mkₐ ℤ (Ideal.span (Set.range P.equations))
  let g := evaluateMatrix (a.comp q)
  have hg : evaluateMatrix ((f.comp a).comp q) = Matrix.GeneralLinearGroup.map f.toRingHom g :=
    Matrix.GeneralLinearGroup.ext fun _ _ => rfl
  obtain ⟨x, rfl⟩ := (modelBaseChange ℤ S).surjective x
  change mapModel f.toRingHom (albertMatrix P S g (modelBaseChange ℤ S x)) =
    albertMatrix P T (evaluateMatrix ((f.comp a).comp q)) (mapModel f.toRingHom (modelBaseChange ℤ S x))
  rw [albertMatrix_apply, ← modelBaseChange_natural, ← modelBaseChange_natural, hg,
    albertMatrix_apply, matrixAction_natural]

private theorem modelAction_ext (P : IntegralPresentation) {S T : Type} [CommRing S] [CommRing T]
    (f : S →+* T) {a b : Model T ≃ₗ[T] Model T}
    (h : ∀ x : Model S, a (mapModel f x) = b (mapModel f x)) : a = b := by
  apply LinearEquiv.toLinearMap_injective
  apply ((P.basis.baseChange T).map (modelBaseChange ℤ T)).ext
  intro i
  let x := P.basis i
  change a (modelBaseChange ℤ T ((P.basis.baseChange T) i)) =
    b (modelBaseChange ℤ T ((P.basis.baseChange T) i))
  rw [Module.Basis.baseChange_apply, modelBaseChange_pure, one_smul]
  have hh := h (mapModel (algebraMap ℤ S) x)
  have hcomp : f.comp (algebraMap ℤ S) = algebraMap ℤ T := by
    ext n
    exact map_intCast f n
  have hm : mapModel f (mapModel (algebraMap ℤ S) x) = mapModel (algebraMap ℤ T) x :=
    (mapModel_comp _ _ _).trans (congrArg (fun r => mapModel r x) hcomp)
  simpa only [hm] using hh

private def identityPoint (P : IntegralPresentation) : P.Coordinates →ₐ[ℤ] ℤ :=
  (albertPoints P ℤ).symm 1

private theorem identityPoint_isIdentity (P : IntegralPresentation) : P.IsIdentity (identityPoint P) := by
  intro i j
  let q := Ideal.Quotient.mkₐ ℤ (Ideal.span (Set.range P.equations))
  have h := congrArg Subtype.val ((albertPoints P ℤ).apply_symm_apply 1)
  change albertMatrix P ℤ (evaluateMatrix ((identityPoint P).comp q)) = 1 at h
  have hg : evaluateMatrix ((identityPoint P).comp q) = 1 :=
    (albertMatrix P ℤ).injective (h.trans (map_one _).symm)
  exact congrArg (fun g : Matrix.GeneralLinearGroup (Fin 27) ℤ => g.val i j) hg

private theorem identityPoint_over (P : IntegralPresentation) (S : Type) [CommRing S] :
    albertPoints P S ((Algebra.ofId ℤ S).comp (identityPoint P)) = 1 := by
  apply Subtype.ext
  apply modelAction_ext P (Algebra.ofId ℤ S).toRingHom
  intro x
  rw [← albertPoints_natural, identityPoint, Equiv.apply_symm_apply]
  rfl

private instance coordinateFinitePresentation (P : IntegralPresentation) :
    Algebra.FinitePresentation ℤ P.Coordinates := by
  let A := MatrixCoordinates ℤ (Fin 27)
  have : Algebra.FinitePresentation (MvPolynomial (Fin 27 × Fin 27) ℤ) A :=
    IsLocalization.Away.finitePresentation ((genericMatrix ℤ (Fin 27)).det)
  have : Algebra.FinitePresentation ℤ A :=
    Algebra.FinitePresentation.trans ℤ (MvPolynomial (Fin 27 × Fin 27) ℤ) A
  exact Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range P.equations))

open private spinForm spinBasis integralCoordinates octonionSpinEquiv octonionSpinEquiv_natural
  integralCoordinates_locallyStandardSmooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.FrameTangentRank
open private spinRelatedEquiv spinRelated_naturality from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.Triality

private abbrev ShortIndex := Fin 3 × DirectionIndex

private abbrev Parameters := MvPolynomial ShortIndex integralCoordinates

private def framePoints (S : Type) [CommRing S] [Algebra ℤ S] :
    (integralCoordinates →ₐ[ℤ] S) ≃ frameStabilizer (R := S) :=
  (SpinFunctor.pointEquiv spinForm spinBasis S).trans
    (((octonionSpinEquiv S).trans ((spinRelatedEquiv ℤ S).trans
      (Triality.frameTriality S).choose)).toEquiv)

private theorem framePoints_natural {S T : Type} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T]
    (f : S →ₐ[ℤ] T) (a : integralCoordinates →ₐ[ℤ] S) (x : Model S) :
    mapModel f.toRingHom ((framePoints S a).val x) =
      (framePoints T (f.comp a)).val (mapModel f.toRingHom x) := by
  let s := octonionSpinEquiv S (SpinFunctor.pointEquiv spinForm spinBasis S a)
  let t := octonionSpinEquiv T (SpinFunctor.pointEquiv spinForm spinBasis T (f.comp a))
  have ht : t = SpinFunctor.map (ZornSpecification.norm ℤ) _ f s := by
    dsimp only [s, t]
    rw [SpinFunctor.pointEquiv_natural, octonionSpinEquiv_natural]
  change mapModel f.toRingHom (((Triality.frameTriality S).choose (spinRelatedEquiv ℤ S s)).val x) =
    ((Triality.frameTriality T).choose (spinRelatedEquiv ℤ T t)).val (mapModel f.toRingHom x)
  rw [ht, (Triality.frameTriality S).choose_spec, (Triality.frameTriality T).choose_spec]
  exact Prod.ext rfl (funext fun i => spinRelated_naturality ℤ f s i (x.2 i))

private def frameInclusion (S : Type) [CommRing S] :
    frameStabilizer (R := S) →* splitAutomorphisms S := by
  refine Subgroup.inclusion ?_
  intro a (ha : FixesFrame a)
  refine (mem_splitAutomorphisms a).mpr ⟨?_, ha.2⟩
  have hsum : (∑ i : Fin 3, (frameAxis i : Model S)) = cubicUnit :=
    (hermitian_frame (ZornSpecification.norm S) (LowerRankSpecification.untwisted S)).1
  rw [← hsum, map_sum]
  simp only [ha.1]

private def shortElement (S : Type) [CommRing S] (i : ShortIndex) (t : S) : splitAutomorphisms S := by
  let a := shortFamily S i.1 i.2 (Multiplicative.ofAdd t)
  refine ⟨a, (mem_splitAutomorphisms a).mpr ?_⟩
  obtain ⟨J, _, hu, hop, _, _, _, _⟩ := Triality.cubicFrameStabilizer S
  have hg := shortFamily_groundIso J hu hop i.1 i.2 t
  refine ⟨?_, fun x y => ?_⟩
  · have h := hg.1
    change a J.unit = J.unit at h
    simpa only [hu] using h
  · have h := hg.2 x y
    change a (J.groundOp x y) = J.groundOp (a x) (a y) at h
    simpa only [hop] using h

private def shortWord {S : Type} [CommRing S] (t : ShortIndex → S) (l : List ShortIndex) :
    splitAutomorphisms S := (l.map fun i => shortElement S i (t i)).prod

private def shortProduct {S : Type} [CommRing S] (t : ShortIndex → S) : splitAutomorphisms S :=
  shortWord t Finset.univ.toList

private theorem shortWord_natural {S T : Type} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T]
    (f : S →ₐ[ℤ] T) (t : ShortIndex → S) (l : List ShortIndex) (x : Model S) :
    mapModel f.toRingHom ((shortWord t l).val x) =
      (shortWord (fun i => f (t i)) l).val (mapModel f.toRingHom x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change mapModel f.toRingHom (shortFamily S i.1 i.2 (Multiplicative.ofAdd (t i))
      ((shortWord t l).val x)) = shortFamily T i.1 i.2 (Multiplicative.ofAdd (f (t i)))
        ((shortWord (fun i => f (t i)) l).val (mapModel f.toRingHom x))
    rw [shortFamily_natural, ih]
    rfl

private theorem shortWord_zero (S : Type) [CommRing S] (l : List ShortIndex) :
    shortWord (fun _ => (0 : S)) l = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have h : shortElement S i 0 = 1 := Subtype.ext ((shortFamily S i.1 i.2).map_one)
    change shortElement S i 0 * shortWord (fun _ => 0) l = 1
    rw [h, ih, one_mul]

private def productPoint {S : Type} [CommRing S] [Algebra ℤ S] (a : integralCoordinates →ₐ[ℤ] S)
    (t : ShortIndex → S) : splitAutomorphisms S :=
  shortProduct t * frameInclusion S (framePoints S a)

private abbrev coefficients : integralCoordinates →ₐ[ℤ] Parameters :=
  IsScalarTower.toAlgHom ℤ integralCoordinates Parameters

private def parameterEvaluation {S : Type} [CommRing S] [Algebra ℤ S] (f : Parameters →ₐ[ℤ] S) :
    splitAutomorphisms S := productPoint (f.comp coefficients) (fun i => f (MvPolynomial.X i))

private theorem parameterEvaluation_natural {S T : Type} [CommRing S] [CommRing T]
    [Algebra ℤ S] [Algebra ℤ T]
    (f : S →ₐ[ℤ] T) (a : Parameters →ₐ[ℤ] S) (x : Model S) :
    mapModel f.toRingHom ((parameterEvaluation a).val x) =
      (parameterEvaluation (f.comp a)).val (mapModel f.toRingHom x) := by
  change mapModel f.toRingHom ((shortProduct (fun i => a (MvPolynomial.X i))).val
    ((framePoints S (a.comp coefficients)).val x)) =
    (shortProduct (fun i => f (a (MvPolynomial.X i)))).val
      ((framePoints T (f.comp (a.comp coefficients))).val (mapModel f.toRingHom x))
  rw [shortProduct, shortProduct, shortWord_natural, framePoints_natural]

private def multiplicationMap (P : IntegralPresentation) : P.Coordinates →ₐ[ℤ] Parameters :=
  (albertPoints P Parameters).symm (parameterEvaluation (AlgHom.id ℤ Parameters))

private theorem multiplicationMap_evaluates (P : IntegralPresentation) {S : Type} [CommRing S]
    [Algebra ℤ S]
    (a : Parameters →ₐ[ℤ] S) :
    albertPoints P S (a.comp (multiplicationMap P)) = parameterEvaluation a := by
  apply Subtype.ext
  apply modelAction_ext P (S := Parameters) a.toRingHom
  intro x
  have hg := albertPoints_natural P (S := Parameters) a (multiplicationMap P) x
  rw [multiplicationMap, Equiv.apply_symm_apply] at hg
  exact hg.symm.trans (parameterEvaluation_natural (S := Parameters) a (AlgHom.id ℤ Parameters) x)

private def frameIdentity (S : Type) [CommRing S] : integralCoordinates →ₐ[ℤ] S :=
  (framePoints S).symm 1

private def parameterIdentity (S : Type) [CommRing S] : Parameters →ₐ[ℤ] S :=
  MvPolynomial.aevalTower (frameIdentity S) (fun _ => 0)

private theorem parameterIdentity_commutes (P : IntegralPresentation) (S : Type) [CommRing S] :
    (parameterIdentity S).comp (multiplicationMap P) =
      (Algebra.ofId ℤ S).comp (identityPoint P) := by
  apply (albertPoints P S).injective
  rw [multiplicationMap_evaluates, identityPoint_over]
  change productPoint ((parameterIdentity S).comp coefficients)
    (fun i => parameterIdentity S (MvPolynomial.X i)) = 1
  simp only [parameterIdentity, MvPolynomial.aevalTower_comp_toAlgHom, MvPolynomial.aevalTower_X]
  rw [productPoint, shortProduct, shortWord_zero, one_mul, frameIdentity, Equiv.apply_symm_apply, map_one]

open private exists_infinitesimal infinitesimal_quadratic_iff infinitesimal_apply
  infinitesimal_add scalar_eps_tmul secondCoefficient secondCoefficient_tmul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme

variable (k : Type) [Field k]

private abbrev reduction : DualNumber k →ₐ[ℤ] k := TrivSqZeroExt.fstHom ℤ k k

private theorem shortProduct_reduces (t : ShortIndex → k) (x : Model (DualNumber k)) :
    mapModel (reduction k).toRingHom ((shortProduct (TrivSqZeroExt.inr ∘ t)).val x) =
      mapModel (reduction k).toRingHom x := by
  rw [shortProduct, shortWord_natural]
  change (shortWord (fun _ => (0 : k)) Finset.univ.toList).val _ = _
  rw [shortWord_zero]
  rfl

private theorem shortWord_differential {J : QuadraticJordan k (Model k)} (t : ShortIndex → k)
    (D : ShortIndex → splitDerivations J)
    (hD : ∀ i x, shortFamily (DualNumber k) i.1 i.2 (Multiplicative.ofAdd (TrivSqZeroExt.inr (t i)))
      (modelBaseChange k (DualNumber k) x) =
        modelBaseChange k (DualNumber k) (infinitesimal (D i).val x))
    (l : List ShortIndex) (x : DualNumber k ⊗[k] Model k) :
    (shortWord (TrivSqZeroExt.inr ∘ t) l).val (modelBaseChange k (DualNumber k) x) =
      modelBaseChange k (DualNumber k) (infinitesimal ((l.map D).sum : splitDerivations J).val x) := by
  induction l generalizing x with
  | nil =>
    simp only [shortWord, List.map_nil, List.prod_nil, List.sum_nil]
    change modelBaseChange k (DualNumber k) x = modelBaseChange k (DualNumber k) (infinitesimal 0 x)
    simp [infinitesimal]
  | cons i l ih =>
    change shortFamily (DualNumber k) i.1 i.2 (Multiplicative.ofAdd (TrivSqZeroExt.inr (t i)))
      ((shortWord (TrivSqZeroExt.inr ∘ t) l).val (modelBaseChange k (DualNumber k) x)) =
      modelBaseChange k (DualNumber k)
        (infinitesimal ((D i).val + ((l.map D).sum : splitDerivations J).val) x)
    rw [ih, hD, infinitesimal_add]
    rfl

private theorem shortProduct_differential (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y)
    (t : ShortIndex → k) :
    ∃ D : splitDerivations J,
      (∀ x, (shortProduct (TrivSqZeroExt.inr ∘ t)).val (modelBaseChange k (DualNumber k) x) =
        modelBaseChange k (DualNumber k) (infinitesimal D.val x)) ∧
      ∀ l, frameEvaluation k D.val l = ∑ j, t (l, j) • IntegralZornDirections.directionBasis k j := by
  choose D hD using fun i : ShortIndex => shortFamily_differential k J hu ho i.1 i.2 (t i)
  refine ⟨∑ i, D i, fun x => ?_, fun l => ?_⟩
  · rw [shortProduct, shortWord_differential k t D (fun i => (hD i).1), Finset.sum_map_toList]
  · let e := (frameEvaluation k).domRestrict (splitDerivations J)
    have h (i : ShortIndex) : e (D i) = t i • Pi.single i.1 (direction k i.2) := (hD i).2
    change e (∑ i, D i) l = _
    simp only [map_sum, h, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_congr rfl]
    intro j _
    simp only [eq_comm (a := l), Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      IntegralZornDirections.directionBasis_apply]

private theorem exists_splitDifferential (J : QuadraticJordan k (Model k))
    (hu : J.unit = cubicUnit) (ho : ∀ x y, J.groundOp x y = modelOp x y)
    (g : splitAutomorphisms (DualNumber k))
    (hg : ∀ x, mapModel (reduction k).toRingHom (g.val x) = mapModel (reduction k).toRingHom x) :
    ∃ D : splitDerivations J, ∀ x, g.val (modelBaseChange k (DualNumber k) x) =
      modelBaseChange k (DualNumber k) (infinitesimal D.val x) := by
  let B := modelBaseChange k (DualNumber k)
  let L := (B.trans (g.val.trans B.symm)).toLinearMap
  have hL (x : DualNumber k ⊗[k] Model k) : g.val (B x) = B (L x) :=
    (B.apply_symm_apply _).symm
  have hr (x : Model k) : dualModuleReduction (L (1 ⊗ₜ[k] x)) = 1 ⊗ₜ[k] x := by
    apply (modelBaseChange k k).injective
    let f := TrivSqZeroExt.fstHom k k k
    change modelBaseChange k k (f.toLinearMap.rTensor (Model k) (L (1 ⊗ₜ[k] x))) = _
    rw [modelBaseChange_natural, ← hL]
    exact (hg _).trans ((modelBaseChange_natural f (1 ⊗ₜ[k] x)).symm.trans (by
      rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]))
  obtain ⟨D, hD⟩ := exists_infinitesimal L hr
  have hp := (preserves_splitCoordinates J hu ho L g.val hL).mpr
    ((mem_splitAutomorphisms g.val).mp g.property)
  rw [hD] at hp
  exact ⟨⟨D, (infinitesimal_quadratic_iff J D).mp hp⟩, fun x => (hL x).trans (by rw [hD])⟩

private theorem baseChange_axis (i : Fin 3) :
    modelBaseChange k (DualNumber k) (1 ⊗ₜ[k] (frameAxis i : Model k)) = frameAxis i := by
  rw [modelBaseChange_pure (DualNumber k) 1 (frameAxis i)]
  exact (one_smul (DualNumber k) (mapModel (algebraMap k (DualNumber k)) (frameAxis i))).trans
    (mapModel_axis (algebraMap k (DualNumber k)) i)

private theorem infinitesimal_on_pure (D : Module.End k (Model k)) (x : Model k) :
    infinitesimal D (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] x + ε ⊗ₜ[k] D x := by
  rw [infinitesimal_apply, LinearMap.baseChange_tmul, scalar_eps_tmul]

private theorem infinitesimal_end_coefficient (D : Module.End k (Model k)) (x : Model k) :
    secondCoefficient (infinitesimal D (1 ⊗ₜ[k] x)) = D x := by
  rw [infinitesimal_on_pure]
  simp only [map_add, secondCoefficient_tmul, TrivSqZeroExt.snd_one, DualNumber.snd_eps,
    zero_smul, one_smul, zero_add]

private theorem productPoint_injective (s t : ShortIndex → k)
    (a b : integralCoordinates →ₐ[ℤ] DualNumber k)
    (h : productPoint a (TrivSqZeroExt.inr ∘ s) = productPoint b (TrivSqZeroExt.inr ∘ t)) :
    a = b ∧ s = t := by
  obtain ⟨J, _, hu, ho, _, _, _, _⟩ := Triality.cubicFrameStabilizer k
  obtain ⟨D, hD, hDe⟩ := shortProduct_differential k J hu ho s
  obtain ⟨F, hF, hFe⟩ := shortProduct_differential k J hu ho t
  have ha (i : Fin 3) : (framePoints (DualNumber k) a).val (frameAxis i) = frameAxis i :=
    (framePoints (DualNumber k) a).property.1 i
  have hb (i : Fin 3) : (framePoints (DualNumber k) b).val (frameAxis i) = frameAxis i :=
    (framePoints (DualNumber k) b).property.1 i
  have haxes (i : Fin 3) : D.val (frameAxis i) = F.val (frameAxis i) := by
    have he := congrArg (fun g : splitAutomorphisms (DualNumber k) => g.val (frameAxis i)) h
    change (shortProduct (TrivSqZeroExt.inr ∘ s)).val ((framePoints _ a).val (frameAxis i)) =
      (shortProduct (TrivSqZeroExt.inr ∘ t)).val ((framePoints _ b).val (frameAxis i)) at he
    rw [ha, hb, ← baseChange_axis k i, hD, hF] at he
    have hcoeff := congrArg secondCoefficient ((modelBaseChange k (DualNumber k)).injective he)
    simpa only [infinitesimal_end_coefficient] using hcoeff
  have hst : s = t := by
    funext i
    let B := IntegralZornDirections.directionBasis k
    have he : (∑ j, s (i.1, j) • B j) = ∑ j, t (i.1, j) • B j := by
      rw [← hDe, ← hFe]
      exact congrArg (fun x : Model k => x.2 i.1) (haxes (cyclicNext i.1))
    rw [← B.equivFun_symm_apply (fun j => s (i.1, j)),
      ← B.equivFun_symm_apply (fun j => t (i.1, j))] at he
    exact congrFun (B.equivFun.symm.injective he) i.2
  subst t
  have hab := mul_left_cancel h
  refine ⟨(framePoints (DualNumber k)).injective (Subtype.ext ?_), rfl⟩
  exact congrArg (fun g : splitAutomorphisms (DualNumber k) => g.val) hab

private theorem productPoint_surjective (P : IntegralPresentation) (g : splitAutomorphisms (DualNumber k))
    (hg : ∀ x, mapModel (reduction k).toRingHom (g.val x) = mapModel (reduction k).toRingHom x) :
    ∃ (a : integralCoordinates →ₐ[ℤ] DualNumber k) (t : ShortIndex → k),
      (reduction k).comp a = frameIdentity k ∧ productPoint a (TrivSqZeroExt.inr ∘ t) = g := by
  obtain ⟨J, _, hu, ho, _, _, _, _⟩ := Triality.cubicFrameStabilizer k
  obtain ⟨D, hD⟩ := exists_splitDifferential k J hu ho g hg
  let B := IntegralZornDirections.directionBasis k
  let t : ShortIndex → k := fun i => B.repr (frameEvaluation k D.val i.1) i.2
  let q : splitAutomorphisms (DualNumber k) := shortProduct (TrivSqZeroExt.inr ∘ t)
  obtain ⟨F, hF, hFe⟩ := shortProduct_differential k J hu ho t
  have hEval : frameEvaluation k D.val = frameEvaluation k F.val := by
    funext i
    rw [hFe]
    exact (B.sum_repr _).symm
  have haxes (i : Fin 3) : g.val (frameAxis i) = q.val (frameAxis i) := by
    have he : D.val (frameAxis i) = F.val (frameAxis i) := by
      rw [frameEvaluationSpec k J hu ho _ D.property i,
        frameEvaluationSpec k J hu ho _ F.property i, hEval]
    rw [← baseChange_axis k i, hD, show q = shortProduct (TrivSqZeroExt.inr ∘ t) from rfl,
      hF, infinitesimal_on_pure, infinitesimal_on_pure, he]
  let w := q⁻¹ * g
  let v : frameStabilizer (R := DualNumber k) :=
    ⟨w.val, ⟨fun i => by
      change q.val.symm (g.val (frameAxis i)) = frameAxis i
      rw [haxes, q.val.symm_apply_apply], ((mem_splitAutomorphisms w.val).mp w.property).2⟩⟩
  let a := (framePoints (DualNumber k)).symm v
  have hav : framePoints (DualNumber k) a = v := (framePoints (DualNumber k)).apply_symm_apply v
  have hprod : productPoint a (TrivSqZeroExt.inr ∘ t) = g := by
    rw [productPoint, hav, show frameInclusion (DualNumber k) v = w from rfl]
    exact mul_inv_cancel_left q g
  refine ⟨a, t, (framePoints k).injective (Subtype.ext ?_), hprod⟩
  rw [frameIdentity, Equiv.apply_symm_apply]
  apply modelAction_ext P (reduction k).toRingHom
  intro x
  have hx := congrArg (fun z : splitAutomorphisms (DualNumber k) => z.val x) hprod
  change q.val ((framePoints (DualNumber k) a).val x) = g.val x at hx
  rw [← framePoints_natural, ← shortProduct_reduces k t ((framePoints (DualNumber k) a).val x), hx]
  exact hg x

open _root_.Specs.AdvCommAlg.Differentials.Tangent (PointLifts)

private theorem parameterHom_ext {S : Type} [CommRing S] {a b : Parameters →ₐ[ℤ] S}
    (hC : a.comp coefficients = b.comp coefficients)
    (hX : ∀ i, a (MvPolynomial.X i) = b (MvPolynomial.X i)) : a = b :=
  AlgHom.toRingHom_injective (MvPolynomial.ringHom_ext
    (fun c => congrArg (fun f : integralCoordinates →ₐ[ℤ] S => f c) hC) hX)

private theorem parameterLift_variables (a : PointLifts ℤ Parameters k (parameterIdentity k))
    (i : ShortIndex) : a.val (MvPolynomial.X i) = TrivSqZeroExt.inr (a.val (MvPolynomial.X i)).snd := by
  apply TrivSqZeroExt.ext
  · have h := congrArg (fun f : Parameters →ₐ[ℤ] k => f (MvPolynomial.X i)) a.property
    change (a.val (MvPolynomial.X i)).fst = parameterIdentity k (MvPolynomial.X i) at h
    exact h.trans (MvPolynomial.aevalTower_X (frameIdentity k) (fun _ => 0) i)
  · rfl

private def liftPrecomposition (P : IntegralPresentation) :
    PointLifts ℤ Parameters k (parameterIdentity k) →
      PointLifts ℤ P.Coordinates k ((Algebra.ofId ℤ k).comp (identityPoint P)) := fun a =>
  ⟨a.val.comp (multiplicationMap P), by
    rw [← AlgHom.comp_assoc, a.property, parameterIdentity_commutes]⟩

set_option maxRecDepth 2048 in
private theorem liftPrecomposition_bijective (P : IntegralPresentation) :
    Function.Bijective (liftPrecomposition k P) := by
  constructor
  · intro a b hab
    have h := congrArg (fun z => albertPoints P (DualNumber k) z.val) hab
    change albertPoints P (DualNumber k) (a.val.comp (multiplicationMap P)) =
      albertPoints P (DualNumber k) (b.val.comp (multiplicationMap P)) at h
    rw [multiplicationMap_evaluates, multiplicationMap_evaluates] at h
    let t (u : PointLifts ℤ Parameters k (parameterIdentity k)) (i : ShortIndex) :=
      (u.val (MvPolynomial.X i)).snd
    have hval (u : PointLifts ℤ Parameters k (parameterIdentity k)) :
        (fun i => u.val (MvPolynomial.X i)) = TrivSqZeroExt.inr ∘ t u :=
      funext (parameterLift_variables k u)
    change productPoint (a.val.comp coefficients) (fun i => a.val (MvPolynomial.X i)) =
      productPoint (b.val.comp coefficients) (fun i => b.val (MvPolynomial.X i)) at h
    rw [hval a, hval b] at h
    obtain ⟨hC, ht⟩ := productPoint_injective k (t a) (t b) _ _ h
    apply Subtype.ext
    refine parameterHom_ext hC (fun i => ?_)
    rw [parameterLift_variables k a, parameterLift_variables k b]
    exact congrArg (fun t : ShortIndex → k => TrivSqZeroExt.inr (t i)) ht
  · intro x
    let g := albertPoints P (DualNumber k) x.val
    have hg (m : Model (DualNumber k)) :
        mapModel (reduction k).toRingHom (g.val m) = mapModel (reduction k).toRingHom m := by
      let v := mapModel (reduction k).toRingHom m
      have h : mapModel (reduction k).toRingHom (g.val m) =
          (albertPoints P k ((reduction k).comp x.val)).val v :=
        albertPoints_natural P (reduction k) x.val m
      have hx : (reduction k).comp x.val = (Algebra.ofId ℤ k).comp (identityPoint P) := x.property
      let ev : (P.Coordinates →ₐ[ℤ] k) → Model k := fun e => (albertPoints P k e).val v
      have hi : ev ((Algebra.ofId ℤ k).comp (identityPoint P)) = v :=
        congrArg (fun a : splitAutomorphisms k => a.val v) (identityPoint_over P k)
      exact h.trans ((congrArg ev hx).trans hi)
    obtain ⟨a, t, ha, ht⟩ := productPoint_surjective k P g hg
    let z := MvPolynomial.aevalTower a (TrivSqZeroExt.inr ∘ t) (σ := ShortIndex)
    have hz : (reduction k).comp z = parameterIdentity k := by
      apply parameterHom_ext
      · rw [AlgHom.comp_assoc]
        simpa only [z, parameterIdentity, MvPolynomial.aevalTower_comp_toAlgHom] using ha
      · intro i
        simp only [z, AlgHom.comp_apply, parameterIdentity, MvPolynomial.aevalTower_X]
        rfl
    refine ⟨⟨z, hz⟩, Subtype.ext ((albertPoints P (DualNumber k)).injective ?_)⟩
    change albertPoints P (DualNumber k) (z.comp (multiplicationMap P)) = g
    rw [multiplicationMap_evaluates]
    simpa only [parameterEvaluation, z, MvPolynomial.aevalTower_comp_toAlgHom,
      MvPolynomial.aevalTower_X, Function.comp_def] using ht

open _root_.Specs.LinearAlgebraicGroups.Albert.SmoothIdentityCriterion

private instance parameterFinitePresentation : Algebra.FinitePresentation ℤ Parameters :=
  Algebra.FinitePresentation.trans ℤ integralCoordinates Parameters

private def pointPrime {A : Type} [CommRing A] (y : A →+* k) : PrimeSpectrum A :=
  ⟨RingHom.ker y, RingHom.ker_isPrime y⟩

set_option maxHeartbeats 600000 in
private theorem polynomial_smooth_at {A I : Type} [CommRing A] [Algebra ℤ A] [Fintype I] (n : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap ℤ A))
    (y : MvPolynomial I A →ₐ[ℤ] k) :
    letI : Algebra (MvPolynomial I A) k := y.toRingHom.toAlgebra
    pointPrime k y.toRingHom ∈ Algebra.smoothLocus ℤ (MvPolynomial I A) ∧
      Module.finrank k (CotangentFiber ℤ (MvPolynomial I A) k) = Fintype.card I + n := by
  let Parameters := MvPolynomial I A
  let coefficients := IsScalarTower.toAlgHom ℤ A Parameters
  letI : Algebra Parameters k := y.toRingHom.toAlgebra
  obtain ⟨s, hs, H⟩ := h
  have he : ∃ a ∈ s, y (coefficients a) ≠ 0 := by
    by_contra! h
    have hle : Ideal.span s ≤ RingHom.ker (y.comp coefficients).toRingHom :=
      Ideal.span_le.mpr fun a ha => RingHom.mem_ker.mpr (h a ha)
    have h1 : (1 : A) ∈ RingHom.ker (y.comp coefficients).toRingHom :=
      hle (by rw [hs]; trivial)
    exact one_ne_zero ((map_one (y.comp coefficients)).symm.trans (RingHom.mem_ker.mp h1))
  obtain ⟨a, ha, hya⟩ := he
  let Aₐ := Localization.Away a
  let C := MvPolynomial I Aₐ
  have hA := H a ha
  change RingHom.IsStandardSmoothOfRelativeDimension n
    ((algebraMap A Aₐ).comp (algebraMap ℤ A)) at hA
  rw [← IsScalarTower.algebraMap_eq ℤ A Aₐ,
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hA
  letI : Algebra.IsStandardSmoothOfRelativeDimension n ℤ Aₐ := hA
  letI : Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card I) Aₐ C := by
    rw [← Nat.card_eq_fintype_card]
    exact Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial Aₐ I
  letI : Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card I + n) ℤ C :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans (R := ℤ) (S := Aₐ) (T := C) n (Fintype.card I)
  letI : Algebra Parameters C := MvPolynomial.algebraMvPolynomial (σ := I) (R := A) (S := Aₐ)
  have hl : IsLocalization.Away (coefficients a) C := by
    change IsLocalization (Submonoid.powers (MvPolynomial.C a)) C
    rw [← Submonoid.map_powers]
    exact MvPolynomial.isLocalization (Submonoid.powers a) Aₐ
  have hu : IsUnit (y.toRingHom (coefficients a)) := isUnit_iff_ne_zero.mpr hya
  let f : C →+* k := IsLocalization.Away.lift (S := C) (g := y.toRingHom) (coefficients a) hu
  have hf : f.comp (algebraMap Parameters C) = y.toRingHom :=
    IsLocalization.Away.lift_comp (S := C) (g := y.toRingHom) (coefficients a) hu
  letI : Algebra C k := f.toAlgebra
  letI : IsScalarTower Parameters C k := IsScalarTower.of_algebraMap_eq' hf.symm
  letI : Algebra.FormallyEtale Parameters C := Algebra.FormallyEtale.of_isLocalization
    (Submonoid.powers (coefficients a))
  letI : Algebra.IsStandardSmooth ℤ C :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (Fintype.card I + n)
  haveI : Algebra.Smooth ℤ C := inferInstance
  have hmap : algebraMap ℤ C = (algebraMap Parameters C).comp (algebraMap ℤ Parameters) :=
    Subsingleton.elim _ _
  letI := IsScalarTower.of_algebraMap_eq' hmap
  let q := pointPrime k f
  have hq : q ∈ Algebra.smoothLocus ℤ C := by rw [Algebra.smoothLocus_eq_univ]; trivial
  rw [← Algebra.smoothLocus_comap_of_isLocalization (R := ℤ) (Af := C) (coefficients a)] at hq
  have heq : PrimeSpectrum.comap (algebraMap Parameters C) q = pointPrime k y.toRingHom := by
    apply PrimeSpectrum.ext
    change ((⊥ : Ideal k).comap f).comap (algebraMap Parameters C) =
      (⊥ : Ideal k).comap y.toRingHom
    rw [Ideal.comap_comap, hf]
  refine ⟨heq ▸ hq, ?_⟩
  let e := LinearEquiv.ofBijective (cotangentFiberMap ℤ Parameters C k)
    SmoothIdentityCriterion.cotangentFiberMap_bijective_of_formallyEtale
  exact e.finrank_eq.trans (SmoothIdentityCriterion.cotangentFiber_finrank_of_standardSmooth (Fintype.card I + n))

private theorem smooth_of_parameter_lifts {R B C K : Type}
    [CommRing R] [CommRing B] [CommRing C] [Field K]
    [Algebra R B] [Algebra R C] [Algebra R K]
    [Algebra.FinitePresentation R B] [Algebra.FinitePresentation R C]
    (m : B →ₐ[R] C) (x : B →ₐ[R] K) (y : C →ₐ[R] K) (h : y.comp m = x)
    (d : ℕ) (hs : pointPrime K y.toRingHom ∈ Algebra.smoothLocus R C)
    (hd : letI : Algebra C K := y.toRingHom.toAlgebra
          Module.finrank K (CotangentFiber R C K) = d)
    (lifts : PointLifts R C K y → PointLifts R B K x)
    (hLifts : ∀ a, (lifts a).val = a.val.comp m) (hl : Function.Bijective lifts) :
    ∃ b : B, x b ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension d R (Localization.Away b) := by
  letI : Algebra B C := m.toRingHom.toAlgebra
  letI : Algebra B K := x.toRingHom.toAlgebra
  letI : Algebra C K := y.toRingHom.toAlgebra
  letI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun z => (m.commutes z).symm
  letI : IsScalarTower R B K := IsScalarTower.of_algebraMap_eq fun z => (x.commutes z).symm
  letI : IsScalarTower R C K := IsScalarTower.of_algebraMap_eq fun z => (y.commutes z).symm
  letI : IsScalarTower B C K := IsScalarTower.of_algebraMap_eq fun b =>
    (congrArg (fun f : B →ₐ[R] K => f b) h).symm
  apply SmoothIdentityCriterion.smooth_identity_criterion_of_derivations R B C K d hs hd
  obtain ⟨eB, hB, _⟩ := AdvCommAlg.Differentials.point_tangent_lifts R B K x
  obtain ⟨eC, hC, _⟩ := AdvCommAlg.Differentials.point_tangent_lifts R C K y
  have he : (eB : _ → _) ∘ (fun D : Derivation R C K => D.compAlgebraMap B) =
      lifts ∘ eC := by
    funext D
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    change (eB (D.compAlgebraMap B)).val b = (lifts (eC D)).val b
    rw [hLifts, AlgHom.comp_apply, hB, hC]
    apply TrivSqZeroExt.ext
    · exact (congrArg (fun f : B →ₐ[R] K => f b) h).symm
    · rfl
  exact (eB.comp_bijective _).mp (he.symm ▸ hl.comp eC.bijective)

/-- In each residue characteristic the integral identity lies in a basic
open of the split Albert automorphism scheme that is smooth of relative dimension 52. -/
theorem integralSmoothIdentity : IntegralSmoothIdentityType := by
  obtain ⟨P⟩ := exists_integralPresentation
  refine ⟨P, identityPoint P, identityPoint_isIdentity P, ?_⟩
  intro k _
  obtain ⟨hs, hd⟩ := polynomial_smooth_at k 28 integralCoordinates_locallyStandardSmooth
    (parameterIdentity k)
  have hdim : Fintype.card ShortIndex + 28 = 52 := by decide
  rw [hdim] at hd
  exact smooth_of_parameter_lifts (R := ℤ) (B := P.Coordinates) (C := Parameters) (K := k)
    (multiplicationMap P) _ _ (parameterIdentity_commutes P k)
    52 hs hd (liftPrecomposition k P) (fun _ => rfl) (liftPrecomposition_bijective k P)

end
end IntegralParametrization

end LinearAlgebraicGroups.Albert.ShortDirections
