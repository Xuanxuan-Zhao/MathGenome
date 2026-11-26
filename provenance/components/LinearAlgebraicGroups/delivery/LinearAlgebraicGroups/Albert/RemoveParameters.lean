import Specs.LinearAlgebraicGroups.Albert.RemoveParameters
import LinearAlgebraicGroups.Albert.SplitModel
import Mathlib.Tactic.LinearCombination

/-! Parameter removal for Hermitian algebras over split Zorn octonions. -/

namespace LinearAlgebraicGroups.Albert

open _root_.LinearAlgebraicGroups.Composition
open Composition.Specification (zornProduct)
open Composition.AdjointSpecification (trace)
open HermitianSpecification LowerRankSpecification
open QuadraticOperatorSpecification (applyOperator)
open RemoveParametersSpecification (Model blockScaling)
open scoped Matrix TensorProduct

universe u v

abbrev removeZornWeights := @RemoveParametersSpecification.removeZornWeights

variable {R : Type u} [CommRing R] (γ : Fin 3 → Rˣ)

private theorem scaleSlots (i : Fin 3) (a b : R) (u v : Fin 3 → R) :
    blockScaling γ i (Zorn.ofCoordinates (a, u, v, b)) =
      Zorn.ofCoordinates
        ((γ i : R) * a, (γ (cyclicNext i) : R) • u, (γ (cyclicPrev i) : R) • v,
          (γ (cyclicNext i) : R) * (γ (cyclicPrev i) : R) * (↑(γ i)⁻¹ : R) * b) := rfl

private theorem removeZornWeights_diag (x : Model R) (i : Fin 3) :
    (removeZornWeights γ x).1 i = x.1 i := rfl

private theorem removeZornWeights_block (x : Model R) (i : Fin 3) :
    (removeZornWeights γ x).2 i = blockScaling γ i (x.2 i) := rfl

private theorem removeZornWeights_unit : removeZornWeights γ CubicSpecification.cubicUnit = CubicSpecification.cubicUnit :=
  Prod.ext rfl (funext fun i => map_zero (blockScaling γ i))

private theorem scaledBlockNorm (i : Fin 3) (x : Zorn R) :
    Zorn.norm R (blockScaling γ i x) = CubicSpecification.blockWeight γ i * Zorn.norm R x := by
  rcases x with ⟨a, u, v, b⟩
  change Zorn.norm R (blockScaling γ i (Zorn.ofCoordinates (a, u, v, b))) =
    CubicSpecification.blockWeight γ i * Zorn.norm R (Zorn.ofCoordinates (a, u, v, b))
  rw [scaleSlots, Zorn.norm_formula, Zorn.norm_formula]
  simp only [Specification.zornNorm, LinearEquiv.apply_symm_apply,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, CubicSpecification.blockWeight]
  linear_combination
    (γ (cyclicNext i) : R) * (γ (cyclicPrev i) : R) * a * b * (γ i).mul_inv

private theorem zornTripleTrace
    (a b c d e f : R) (u v w t p q : Fin 3 → R) :
    trace (Zorn.norm R)
        ((Zorn.ofCoordinates (a, u, v, b) * Zorn.ofCoordinates (c, w, t, d)) *
          Zorn.ofCoordinates (e, p, q, f)) =
      a * c * e + b * d * f +
        (a * (w ⬝ᵥ q) + c * (p ⬝ᵥ v) + e * (u ⬝ᵥ t)) +
        (b * (t ⬝ᵥ p) + d * (q ⬝ᵥ u) + f * (v ⬝ᵥ w)) +
        ((u ⨯₃ w) ⬝ᵥ p) - ((v ⨯₃ t) ⬝ᵥ q) := by
  change trace (Zorn.norm R)
    (Zorn.ofCoordinates (zornProduct (zornProduct (a, u, v, b) (c, w, t, d)) (e, p, q, f))) = _
  simp only [zornProduct, Zorn.trace_formula, add_dotProduct, sub_dotProduct,
    smul_dotProduct, smul_eq_mul, dotProduct_comm p v, dotProduct_comm q u]
  ring

private theorem scaledTripleTrace (x y z : Zorn R) :
    trace (Zorn.norm R) ((blockScaling γ 0 x * blockScaling γ 1 y) * blockScaling γ 2 z) =
      CubicSpecification.weightProduct γ * trace (Zorn.norm R) ((x * y) * z) := by
  rcases x with ⟨a, u, v, b⟩
  rcases y with ⟨c, w, t, d⟩
  rcases z with ⟨e, p, q, f⟩
  change trace (Zorn.norm R)
    ((blockScaling γ 0 (Zorn.ofCoordinates (a, u, v, b)) *
      blockScaling γ 1 (Zorn.ofCoordinates (c, w, t, d))) *
      blockScaling γ 2 (Zorn.ofCoordinates (e, p, q, f))) =
    CubicSpecification.weightProduct γ * trace (Zorn.norm R)
      ((Zorn.ofCoordinates (a, u, v, b) * Zorn.ofCoordinates (c, w, t, d)) *
        Zorn.ofCoordinates (e, p, q, f))
  rw [scaleSlots, scaleSlots, scaleSlots, zornTripleTrace, zornTripleTrace]
  have n0 : cyclicNext 0 = 1 := rfl
  have n1 : cyclicNext 1 = 2 := rfl
  have n2 : cyclicNext 2 = 0 := rfl
  have p0 : cyclicPrev 0 = 2 := rfl
  have p1 : cyclicPrev 1 = 0 := rfl
  have p2 : cyclicPrev 2 = 1 := rfl
  simp only [n0, n1, n2, p0, p1, p2, CubicSpecification.weightProduct, smul_dotProduct, dotProduct_smul,
    LinearMap.smul_apply, map_smul, smul_eq_mul]
  let A : R := γ 0
  let B : R := γ 1
  let C : R := γ 2
  let A' : R := ↑(γ 0)⁻¹
  let B' : R := ↑(γ 1)⁻¹
  let C' : R := ↑(γ 2)⁻¹
  have hA : B * C * A' * A * A = A * B * C := by
    calc
      _ = A * B * C * (A' * A) := by ring
      _ = _ := by rw [(γ 0).inv_mul, mul_one]
  have hB : C * A * B' * B * B = A * B * C := by
    calc
      _ = A * B * C * (B' * B) := by ring
      _ = _ := by rw [(γ 1).inv_mul, mul_one]
  have hC : A * B * C' * C * C = A * B * C := by
    calc
      _ = A * B * C * (C' * C) := by ring
      _ = _ := by rw [(γ 2).inv_mul, mul_one]
  have hABC : (B * C * A') * (C * A * B') * (A * B * C') = A * B * C := by
    calc
      _ = A * B * C * (A' * A) * (B' * B) * (C' * C) := by ring
      _ = _ := by rw [(γ 0).inv_mul, (γ 1).inv_mul, (γ 2).inv_mul]; simp
  dsimp only [A, B, C, A', B', C'] at hA hB hC hABC
  linear_combination (b * d * f) * hABC +
    (b * (t ⬝ᵥ p)) * hA + (d * (q ⬝ᵥ u)) * hB + (f * (v ⬝ᵥ w)) * hC

/-- The cubic norm in weighted coordinates becomes the untwisted cubic norm. -/
theorem removeZornWeights_norm (x : Model R) :
    CubicSpecification.cubicNorm (Zorn.norm R) (untwisted R) (removeZornWeights γ x) =
      CubicSpecification.cubicNorm (Zorn.norm R) γ x := by
  simp only [CubicSpecification.cubicNorm, removeZornWeights_diag, removeZornWeights_block,
    scaledBlockNorm, scaledTripleTrace]
  have hw (i : Fin 3) : CubicSpecification.blockWeight (untwisted R) i = 1 := by
    simp [CubicSpecification.blockWeight, untwisted]
  simp only [hw, CubicSpecification.weightProduct, untwisted, Units.val_one, one_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

section ScalarExtension

variable (S : Type v) [CommRing S] [Algebra R S]

/-- Identify the scalar extension of each block with the Zorn algebra over the new ring. -/
private noncomputable def zornExtendedCoordinates :
    Coordinates S (S ⊗[R] Zorn R) ≃ₗ[S] Model S :=
  (LinearEquiv.refl S _).prodCongr (LinearEquiv.piCongrRight fun _ => Zorn.baseChange R S)

private theorem zornExtendedNorm (δ : Fin 3 → Sˣ) (x : Coordinates S (S ⊗[R] Zorn R)) :
    CubicSpecification.cubicNorm (Zorn.norm S) δ (zornExtendedCoordinates S x) =
      CubicSpecification.cubicNorm (normBaseChange S (Zorn.norm R)) δ x := by
  let E := Zorn.baseChange R S
  have hn (y : S ⊗[R] Zorn R) : Zorn.norm S (E y) = normBaseChange S (Zorn.norm R) y := by
    rw [Zorn.baseChange_norm]
    rfl
  have ht (y : S ⊗[R] Zorn R) :
      trace (Zorn.norm S) (E y) = trace (normBaseChange S (Zorn.norm R)) y := by
    change (Zorn.norm S).polarBilin (E y) 1 = (normBaseChange S (Zorn.norm R)).polarBilin y 1
    rw [Zorn.baseChange_polar]
    change _ = (Zorn.norm S).polarBilin (E y) (E 1)
    rw [Zorn.baseChange_one]
  have hd (i : Fin 3) : (zornExtendedCoordinates S x).1 i = x.1 i := rfl
  have hb (i : Fin 3) : (zornExtendedCoordinates S x).2 i = E (x.2 i) := rfl
  simp only [CubicSpecification.cubicNorm, hd, hb, hn]
  rw [← Zorn.baseChange_mul, ← Zorn.baseChange_mul, ht]

private theorem mapBlockScaling (i : Fin 3) (x : Zorn R) :
    ZornSpecification.mapCoordinates (algebraMap R S) (blockScaling γ i x) =
      blockScaling (baseChangedWeights S γ) i
        (ZornSpecification.mapCoordinates (algebraMap R S) x) := by
  rcases x with ⟨a, u, v, b⟩
  change ZornSpecification.mapCoordinates (algebraMap R S)
    (blockScaling γ i (Zorn.ofCoordinates (a, u, v, b))) = _
  rw [scaleSlots]
  change Zorn.ofCoordinates
    (algebraMap R S ((γ i : R) * a),
      algebraMap R S ∘ ((γ (cyclicNext i) : R) • u),
      algebraMap R S ∘ ((γ (cyclicPrev i) : R) • v),
      algebraMap R S
        ((γ (cyclicNext i) : R) * (γ (cyclicPrev i) : R) * (↑(γ i)⁻¹ : R) * b)) =
    blockScaling (baseChangedWeights S γ) i
      (Zorn.ofCoordinates (algebraMap R S a, algebraMap R S ∘ u,
        algebraMap R S ∘ v, algebraMap R S b))
  rw [scaleSlots]
  apply (Zorn.coordinates S).injective
  simp only [LinearEquiv.apply_symm_apply, Prod.mk.injEq, baseChangedWeights,
    ← map_inv, Units.coe_map, Function.comp_def, Pi.smul_apply, smul_eq_mul, map_mul]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem extendRemoveZornWeights (x : Model R) :
    zornExtendedCoordinates S (CubicSpecification.extendCoordinates S (removeZornWeights γ x)) =
      removeZornWeights (baseChangedWeights S γ)
        (zornExtendedCoordinates S (CubicSpecification.extendCoordinates S x)) := by
  apply Prod.ext
  · rfl
  · funext i
    change Zorn.baseChange R S (1 ⊗ₜ[R] blockScaling γ i (x.2 i)) =
      blockScaling (baseChangedWeights S γ) i (Zorn.baseChange R S (1 ⊗ₜ[R] x.2 i))
    rw [Zorn.baseChange_tmul, Zorn.baseChange_tmul, one_smul, one_smul, mapBlockScaling]

private theorem removeZornWeights_extendedNorm :
    RemoveParametersSpecification.PreservesCubicNormAfterBaseChange.{u, v} γ (removeZornWeights γ) := by
  intro S _ _ x
  let e := HermitianSpecification.coordinatesBaseChange (R := R) (A := Zorn R) S
  let E := e.trans (zornExtendedCoordinates S)
  let F := removeZornWeights γ
  let δ := baseChangedWeights S γ
  let G := removeZornWeights δ
  have he (z : S ⊗[R] Model R) : E (F.toLinearMap.baseChange S z) = G (E z) := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s y =>
      have scaleTensor (z : Model R) : s ⊗ₜ[R] z = s • ((1 : S) ⊗ₜ[R] z) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, scaleTensor (F y), scaleTensor y]
      simp only [map_smul]
      exact congrArg (fun z : Model S => s • z) (extendRemoveZornWeights γ S y)
  change CubicSpecification.cubicNorm (normBaseChange S (Zorn.norm R)) (untwisted S)
      (e (F.toLinearMap.baseChange S x)) =
    CubicSpecification.cubicNorm (normBaseChange S (Zorn.norm R)) δ (e x)
  rw [← zornExtendedNorm S (untwisted S), ← zornExtendedNorm S δ]
  change CubicSpecification.cubicNorm (Zorn.norm S) (untwisted S) (E (F.toLinearMap.baseChange S x)) =
    CubicSpecification.cubicNorm (Zorn.norm S) δ (E x)
  rw [he, removeZornWeights_norm]

end ScalarExtension

private theorem removeZornWeights_line (x y : Model R) :
    CubicSpecification.cubicLinePolynomial (Zorn.norm R) (untwisted R)
        (removeZornWeights γ x) (removeZornWeights γ y) =
      CubicSpecification.cubicLinePolynomial (Zorn.norm R) γ x y := by
  let P := Polynomial R
  have hw : HermitianSpecification.baseChangedWeights P (untwisted R) = untwisted P := by
    funext i
    exact map_one (Units.map (algebraMap R P).toMonoidHom)
  unfold CubicSpecification.cubicLinePolynomial
  rw [hw]
  simpa only [map_add, map_smul, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    CubicSpecification.extendCoordinates] using
    (removeZornWeights_extendedNorm γ P
      (((1 : P) ⊗ₜ[R] x) + (Polynomial.X : P) • ((1 : P) ⊗ₜ[R] y)))

private theorem removeZornWeights_derivative (x y : Model R) :
    CubicSpecification.normDerivative (Zorn.norm R) (untwisted R) (removeZornWeights γ x) (removeZornWeights γ y) =
      CubicSpecification.normDerivative (Zorn.norm R) γ x y :=
  congrArg (fun p : Polynomial R => p.coeff 1) (removeZornWeights_line γ x y)

private theorem removeZornWeights_linearTrace (x : Model R) :
    CubicSpecification.linearTrace (Zorn.norm R) (untwisted R) (removeZornWeights γ x) = CubicSpecification.linearTrace (Zorn.norm R) γ x := by
  have h := removeZornWeights_derivative γ CubicSpecification.cubicUnit x
  rw [removeZornWeights_unit] at h
  rw [(cubic_trace_coefficients (untwisted R) (Zorn.isOctonion R)).1,
    (cubic_trace_coefficients γ (Zorn.isOctonion R)).1] at h
  exact h

private theorem removeZornWeights_quadraticTrace (x : Model R) :
    CubicSpecification.quadraticTrace (Zorn.norm R) (untwisted R) (removeZornWeights γ x) =
      CubicSpecification.quadraticTrace (Zorn.norm R) γ x := by
  have h := removeZornWeights_derivative γ x CubicSpecification.cubicUnit
  rw [removeZornWeights_unit, cubic_norm_derivative (untwisted R) (Zorn.isOctonion R),
    cubic_norm_derivative γ (Zorn.isOctonion R)] at h
  exact h

private theorem removeZornWeights_pairing (x y : Model R) :
    CubicSpecification.tracePairing (Zorn.norm R) (untwisted R) (removeZornWeights γ x) (removeZornWeights γ y) =
      CubicSpecification.tracePairing (Zorn.norm R) γ x y := by
  have h := quadraticTrace_polar (n := Zorn.norm R) (untwisted R)
    (removeZornWeights γ x) (removeZornWeights γ y)
  rw [← map_add, removeZornWeights_quadraticTrace, removeZornWeights_quadraticTrace,
    removeZornWeights_quadraticTrace, removeZornWeights_linearTrace, removeZornWeights_linearTrace,
    quadraticTrace_polar γ] at h
  linear_combination h

private theorem removeZornWeights_adjoint (x : Model R) :
    removeZornWeights γ (CubicSpecification.cubicAdjoint (Zorn.norm R) γ x) =
      CubicSpecification.cubicAdjoint (Zorn.norm R) (untwisted R) (removeZornWeights γ x) := by
  have hperf := tracePairing_perfect (untwisted R) (Zorn.perfect R)
  apply hperf.bijective_left.injective
  apply LinearMap.ext
  intro z
  obtain ⟨y, rfl⟩ := (removeZornWeights γ).surjective z
  rw [removeZornWeights_pairing, ← cubic_norm_derivative γ (Zorn.isOctonion R),
    ← cubic_norm_derivative (untwisted R) (Zorn.isOctonion R), removeZornWeights_derivative]

private theorem removeZornWeights_cross (x y : Model R) :
    removeZornWeights γ (CubicSpecification.adjointCross (Zorn.norm R) γ x y) =
      CubicSpecification.adjointCross (Zorn.norm R) (untwisted R) (removeZornWeights γ x) (removeZornWeights γ y) := by
  simp only [CubicSpecification.adjointCross, map_add, map_sub, removeZornWeights_adjoint]

private theorem removeZornWeights_operator (x y : Model R) :
    removeZornWeights γ (applyOperator (Zorn.norm R) γ x y) =
      applyOperator (Zorn.norm R) (untwisted R) (removeZornWeights γ x) (removeZornWeights γ y) := by
  simp only [applyOperator, map_sub, map_smul, removeZornWeights_cross, removeZornWeights_adjoint,
    removeZornWeights_pairing]

/-- The explicit scaling is an isomorphism to the split Albert model over the original ring. -/
theorem zorn_weight_removal : RemoveParametersSpecification.ZornWeightRemovalType := by
  intro R _ γ
  refine ⟨removeZornWeights_unit γ, removeZornWeights_norm γ, removeZornWeights_extendedNorm γ,
    removeZornWeights_pairing γ,
    removeZornWeights_linearTrace γ, removeZornWeights_quadraticTrace γ, removeZornWeights_adjoint γ,
    removeZornWeights_operator γ, ?_⟩
  let h := Zorn.isOctonion R
  let δ := untwisted R
  obtain ⟨J, hJu, hJg, hJo, _⟩ := weighted_hermitian_quadratic_jordan γ h
  obtain ⟨K, hKu, hKg, hKo, _⟩ := weighted_hermitian_quadratic_jordan δ h
  let J' := SplitSpecification.ParaQuadratic.ofJordan J
  let K' := SplitSpecification.ParaQuadratic.ofJordan K
  refine ⟨h, J, K, ⟨hJu, hJo⟩, ⟨hKu, hKo⟩, ?_⟩
  apply (SplitSpecification.ParaQuadratic.isIso_iff_ground J' K' (removeZornWeights γ)).2
  refine ⟨?_, fun x y => ?_⟩
  · change removeZornWeights γ J.unit = K.unit
    rw [hJu, hKu, removeZornWeights_unit]
  · change removeZornWeights γ (J.groundOp x y) =
      K.groundOp (removeZornWeights γ x) (removeZornWeights γ y)
    rw [hJg, hKg, removeZornWeights_operator]

end LinearAlgebraicGroups.Albert
