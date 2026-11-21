import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.NonsplitFieldBoundary
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open scoped TensorProduct Matrix
open LieAlgebra Matrix Complex
open Specs.LieAlgebrasAndRepresentations.NonsplitFieldBoundary
open Specs.LieAlgebrasAndRepresentations.RealFormLowRanks (su sl₂ℝ sl₂ℂ)
open LieAlgebrasAndRepresentations.RealForms (complexifyMap IsRealForm)

namespace LieAlgebrasAndRepresentations.NonsplitFieldBoundary

attribute [local instance 100] LieRing.ofAssociativeRing

@[simp] private theorem rotation_zero_coord {k : Type*} [Field k] (v : Plane k) :
    rotation k v 0 = -v 1 := by
  simp [rotation, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] private theorem rotation_one_coord {k : Type*} [Field k] (v : Plane k) :
    rotation k v 1 = v 0 := by
  simp [rotation, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem rotation_no_real_eigenvector {v : Plane ℝ} (hv : v ≠ 0) (t : ℝ)
    (h : rotation ℝ v = t • v) : False := by
  have hsq : rotation ℝ (rotation ℝ v) = -v := by
    ext i
    fin_cases i <;> simp
  have h' : (t ^ 2 + 1) • v = 0 := by
    rw [add_smul]
    rw [one_smul, ← neg_eq_iff_add_eq_zero, pow_two, ← smul_smul, ← h,
      ← map_smul, ← h]
    simp only [hsq, neg_neg]
  exact hv ((smul_eq_zero.mp h').resolve_left (by positivity))

private theorem real_rotation : rotation_real_type := by
  refine ⟨Module.finrank_self ℝ, ⟨fun x y => sub_eq_zero.mpr (mul_comm x y)⟩, ?_, ?_⟩
  · intro W hd hw
    obtain ⟨e₀⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hd
    let e := e₀.symm
    let v : W := e.symm 1
    have hv : (v : Plane ℝ) ≠ 0 := by
      intro h
      have h' : v = 0 := Subtype.ext h
      exact (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa [v] using congrArg e h')
    let w : W := ⟨rotationAction ℝ 1 v, hw 1 v v.property⟩
    have he : w = (e w) • v := by
      apply e.injective
      simp [v]
    apply rotation_no_real_eigenvector hv (e w)
    simpa [w, rotationAction] using congrArg Subtype.val he
  · rintro ⟨n, b, hb⟩
    have hn : n = 2 := by
      have h := Module.finrank_eq_card_basis b
      simpa using h.symm
    subst n
    let v := b (0 : Fin 2)
    let w := rotation ℝ v
    have h1 : b.repr w 1 = 0 := by
      simpa [v, w, rotationAction] using hb 1 1 0 (by decide)
    have h := b.sum_repr w
    rw [Fin.sum_univ_two, h1, zero_smul, add_zero] at h
    exact rotation_no_real_eigenvector (b.ne_zero 0) (b.repr w 0) h.symm

/-- Coordinatewise complexification through the extension of a real basis. -/
private def complexCoordinates {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℝ M]
    (e : M ≃ₗ[ℝ] (Fin n → ℝ)) : (ℂ ⊗[ℝ] M) ≃ₗ[ℂ] (Fin n → ℂ) :=
  ((Module.Basis.ofEquivFun e).baseChange ℂ).equivFun

private theorem complexCoordinates_tmul {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℝ M]
    (e : M ≃ₗ[ℝ] (Fin n → ℝ)) (c : ℂ) (v : M) (i : Fin n) :
    complexCoordinates e (c ⊗ₜ[ℝ] v) i = c * (e v i : ℂ) := by
  simp [complexCoordinates, Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
    Module.Basis.ofEquivFun_repr_apply, Complex.real_smul, mul_comm]

private theorem complex_rotation_eigenvectors (z : ℂ) (v : Plane ℂ) :
    v ∈ (rotation ℂ).eigenspace z ↔ v 1 = -z * v 0 ∧ v 0 = z * v 1 := by
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [rotation_zero_coord, rotation_one_coord, Pi.smul_apply, smul_eq_mul] at h0 h1
    exact ⟨by linear_combination -h0, h1⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp <;> first | linear_combination -h0 | exact h1

private theorem rotation_complex_line (z : ℂ) (hz : z * z = -1) :
    (rotation ℂ).eigenspace z = ℂ ∙ (![1, -z] : Plane ℂ) := by
  ext v
  rw [complex_rotation_eigenvectors, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨h0, _⟩
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [h0]
    ring
  · rintro ⟨a, rfl⟩
    simp
    constructor
    · ring
    · linear_combination a * hz

private theorem complex_rotation : rotation_complex_type := by
  let _ := rotationLieRingModule
  let _ := rotationLieModule
  refine ⟨⟨complexCoordinates (LinearEquiv.refl ℝ _), complexCoordinates_tmul _, ?_⟩, ?_, ?_⟩
  · intro s t r v
    rw [LieAlgebra.ExtendScalars.bracket_tmul]
    change complexCoordinates (LinearEquiv.refl ℝ _) ((s * t) ⊗ₜ[ℝ]
      rotationAction ℝ r v) = (s * (r : ℂ)) •
        rotation ℂ (complexCoordinates (LinearEquiv.refl ℝ _) (t ⊗ₜ[ℝ] v))
    ext i
    fin_cases i <;>
      (simp only [complexCoordinates_tmul, LinearEquiv.refl_apply, Pi.smul_apply, smul_eq_mul]
       simp [rotationAction, complexCoordinates_tmul]
       ring)
  · intro z
    split_ifs with hp hm
    · subst z
      exact rotation_complex_line I I_mul_I
    · subst z
      simpa using rotation_complex_line (-I) (by simp)
    · ext v
      rw [complex_rotation_eigenvectors, Submodule.mem_bot]
      constructor
      · rintro ⟨h0, h1⟩
        have hz : (z - I) * (z + I) ≠ 0 :=
          mul_ne_zero (sub_ne_zero.mpr hp) (by simpa [sub_eq_add_neg] using sub_ne_zero.mpr hm)
        have hprod : ((z - I) * (z + I)) * v 0 = 0 := by
          linear_combination h1 + z * h0 - (v 0) * I_mul_I
        have hv : v 0 = 0 := (mul_eq_zero.mp hprod).resolve_left hz
        ext i
        fin_cases i <;> simp [hv, h0]
      · rintro rfl
        simp
  · refine ⟨(Submodule.disjoint_span_singleton' ?_).2 ?_, codisjoint_iff.mpr ?_⟩
    · intro h
      simpa using congrFun h (0 : Fin 2)
    · intro h
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
      have h0 := congrFun ha (0 : Fin 2)
      have h1 := congrFun ha (1 : Fin 2)
      simp at h0 h1
      have hi : I = -I := by linear_combination -h1 - I * h0
      have := congrArg Complex.im hi
      norm_num at this
    · apply top_unique
      intro v _
      let a := (v 0 + I * v 1) / 2
      let b := (v 0 - I * v 1) / 2
      refine Submodule.mem_sup.mpr ⟨a • ![1, -I], Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
        b • ![1, I], Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      ext i
      fin_cases i <;> simp [a, b]
      · ring
      · linear_combination -(v 1) * I_mul_I


private abbrev SL₂ (k : Type*) [Field k] := SpecialLinear.sl (Fin 2) k

private def slMatrix {k : Type*} [Field k] (a b c : k) : SL₂ k :=
  ⟨!![a, b; c, -a], by
    change Matrix.trace (!![a, b; c, -a] : Matrix (Fin 2) (Fin 2) k) = 0
    simp [Matrix.trace, Fin.sum_univ_two]⟩

private theorem sl_diag {k : Type*} [Field k] (X : SL₂ k) : X.val 1 1 = -X.val 0 0 := by
  have h : X.val.trace = 0 := X.property
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] at h
  exact eq_neg_of_add_eq_zero_right h

private def slCoords (k : Type*) [Field k] : SL₂ k ≃ₗ[k] (Fin 3 → k) where
  toFun X := ![X.val 0 0, X.val 0 1, X.val 1 0]
  invFun v := slMatrix (v 0) (v 1) (v 2)
  left_inv X := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slMatrix, sl_diag]
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' X Y := by funext i; fin_cases i <;> rfl
  map_smul' t X := by funext i; fin_cases i <;> rfl

@[simp] private theorem slCoords_zero {k : Type*} [Field k] (X : SL₂ k) :
    slCoords k X 0 = X.val 0 0 := rfl
@[simp] private theorem slCoords_one {k : Type*} [Field k] (X : SL₂ k) :
    slCoords k X 1 = X.val 0 1 := rfl
@[simp] private theorem slCoords_two {k : Type*} [Field k] (X : SL₂ k) :
    slCoords k X 2 = X.val 1 0 := rfl

private theorem slBracket {k : Type*} [Field k] (X Y : SL₂ k) :
    let x := slCoords k X
    let y := slCoords k Y
    slCoords k ⁅X, Y⁆ =
      ![x 1 * y 2 - x 2 * y 1, 2 * (x 0 * y 1 - x 1 * y 0),
        2 * (x 2 * y 0 - x 0 * y 2)] := by
  funext i
  fin_cases i <;>
    simp [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket, Matrix.mul_apply,
      Fin.sum_univ_two, sl_diag] <;> ring

private theorem skewHermitian (X : su 2) : X.val.valᴴ = -X.val.val := X.property

private theorem su_diag_re (X : su 2) : (X.val.val 0 0).re = 0 := by
  have h := congrArg Complex.re (congrFun (congrFun (skewHermitian X) 0) 0)
  simp [Matrix.conjTranspose_apply] at h
  linarith

private theorem su_lower (X : su 2) : X.val.val 1 0 = -star (X.val.val 0 1) := by
  have h := congrFun (congrFun (skewHermitian X) 1) 0
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
  exact (neg_eq_iff_eq_neg.mp h.symm)

private def suMatrix (a b c : ℝ) : su 2 :=
  ⟨slMatrix ⟨0, a⟩ ⟨b, c⟩ ⟨-b, c⟩, by
    change (slMatrix (⟨0, a⟩ : ℂ) ⟨b, c⟩ ⟨-b, c⟩).valᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [slMatrix, Matrix.conjTranspose_apply, Complex.ext_iff]⟩

private def suCoords : su 2 ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun X := ![(X.val.val 0 0).im, (X.val.val 0 1).re, (X.val.val 0 1).im]
  invFun v := suMatrix (v 0) (v 1) (v 2)
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [suMatrix, slMatrix, sl_diag, su_lower]
    all_goals apply Complex.ext <;> simp [su_diag_re]
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' X Y := by funext i; fin_cases i <;> rfl
  map_smul' t X := by
    funext i
    fin_cases i <;> simp [Pi.smul_apply, Matrix.smul_apply, Complex.real_smul, Complex.mul_re,
      Complex.mul_im]

@[simp] private theorem suCoords_zero (X : su 2) : suCoords X 0 = (X.val.val 0 0).im := rfl
@[simp] private theorem suCoords_one (X : su 2) : suCoords X 1 = (X.val.val 0 1).re := rfl
@[simp] private theorem suCoords_two (X : su 2) : suCoords X 2 = (X.val.val 0 1).im := rfl

private theorem suBracket (X Y : su 2) :
    let x := suCoords X
    let y := suCoords Y
    suCoords ⁅X, Y⁆ =
      ![2 * (x 1 * y 2 - x 2 * y 1), 2 * (x 2 * y 0 - x 0 * y 2),
        2 * (x 0 * y 1 - x 1 * y 0)] := by
  have h := slBracket X.val Y.val
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h0' := congrArg Complex.im h0
  have h1' := congrArg Complex.re h1
  have h1'' := congrArg Complex.im h1
  funext i
  fin_cases i
  · simp [Complex.mul_im, su_lower, Complex.neg_im] at h0' ⊢
    linarith
  · simp [Complex.mul_re, Complex.sub_re, su_diag_re] at h1' ⊢
    linarith
  · simp [Complex.mul_im, Complex.sub_im, su_diag_re] at h1'' ⊢
    linarith

private def coordinatesBasis {M : Type*} [AddCommGroup M] [Module ℝ M]
    (e : M ≃ₗ[ℝ] (Fin 3 → ℝ)) := (Pi.basisFun ℝ (Fin 3)).map e.symm

private theorem coord_trace {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (e : M ≃ₗ[ℝ] (Fin 3 → ℝ)) (x : M) :
    _root_.killingForm ℝ M x x =
      ∑ i : Fin 3, e ⁅x, ⁅x, coordinatesBasis e i⁆⁆ i := by
  classical
  rw [killingForm_apply_apply, LinearMap.trace_eq_matrix_trace ℝ (coordinatesBasis e)]
  simp [Matrix.trace, LinearMap.toMatrix_apply, coordinatesBasis]

private theorem killing_su (X : su 2) :
    _root_.killingForm ℝ (su 2) X X =
      -8 * ((suCoords X 0)^2 + (suCoords X 1)^2 + (suCoords X 2)^2) := by
  rw [coord_trace suCoords, Fin.sum_univ_three]
  simp only [suBracket, coordinatesBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basisFun_apply]
  simp
  ring

private theorem killing_sl (X : sl₂ℝ) :
    _root_.killingForm ℝ sl₂ℝ X X =
      8 * ((slCoords ℝ X 0)^2 + slCoords ℝ X 1 * slCoords ℝ X 2) := by
  rw [coord_trace (slCoords ℝ), Fin.sum_univ_three]
  simp only [slBracket, coordinatesBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basisFun_apply]
  simp
  ring

private def splitDiagonalCoordinates : sl₂ℝ ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  (slCoords ℝ).trans {
    toFun v := ![v 0, (v 1 + v 2) / 2, (v 1 - v 2) / 2]
    invFun v := ![v 0, v 1 + v 2, v 1 - v 2]
    left_inv v := by funext i; fin_cases i <;> simp <;> ring
    right_inv v := by funext i; fin_cases i <;> simp
    map_add' x y := by funext i; fin_cases i <;> simp [Pi.add_apply] <;> ring
    map_smul' t x := by
      funext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
      all_goals ring }

private theorem killing_sl_diagonal (X : sl₂ℝ) :
    _root_.killingForm ℝ sl₂ℝ X X =
      8 * ((splitDiagonalCoordinates X 0)^2 + (splitDiagonalCoordinates X 1)^2 -
        (splitDiagonalCoordinates X 2)^2) := by
  rw [killing_sl]
  change 8 * (_ ^ 2 + _ * _) =
    8 * ((X.val 0 0) ^ 2 + ((X.val 0 1 + X.val 1 0) / 2)^2 - ((X.val 0 1 - X.val 1 0) / 2)^2)
  simp only [slCoords_zero, slCoords_one, slCoords_two]
  ring

private theorem killing_su_neg (x : su 2) (hx : x ≠ 0) : _root_.killingForm ℝ (su 2) x x < 0 := by
  rw [killing_su]
  have h : suCoords x 0 ≠ 0 ∨ suCoords x 1 ≠ 0 ∨ suCoords x 2 ≠ 0 := by
    by_contra! hh
    apply hx
    apply suCoords.injective
    ext i
    fin_cases i
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  rcases h with h | h | h <;> nlinarith [sq_pos_of_ne_zero h]

private theorem forms_distinct : ¬ Nonempty (su 2 ≃ₗ⁅ℝ⁆ sl₂ℝ) := by
  rintro ⟨e⟩
  let y := slMatrix (1 : ℝ) 0 0
  have hy : y ≠ 0 := by
    intro h
    have h0 := congrArg (fun X : sl₂ℝ => X.val 0 0) h
    norm_num [y, slMatrix] at h0
  have hx : e.symm y ≠ 0 := by simpa using hy
  have h := killing_su_neg (e.symm y) hx
  rw [← LieAlgebra.killingForm_of_equiv_apply e (e.symm y) (e.symm y),
    e.apply_symm_apply, killing_sl] at h
  norm_num [y, slMatrix] at h


/-- Extend a real Lie homomorphism into a complex Lie algebra by scalar multiplication. -/
private def extendEmbedding {M L : Type*} [LieRing M] [LieAlgebra ℝ M]
    [LieRing L] [LieAlgebra ℂ L] [LieAlgebra ℝ L] [IsScalarTower ℝ ℂ L] (f : M →ₗ⁅ℝ⁆ L) : (ℂ ⊗[ℝ] M) →ₗ⁅ℂ⁆ L where
  __ := f.toLinearMap.liftBaseChange ℂ
  map_lie' {x y} := by
    change f.toLinearMap.liftBaseChange ℂ ⁅x, y⁆ =
      ⁅f.toLinearMap.liftBaseChange ℂ x, f.toLinearMap.liftBaseChange ℂ y⁆
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
        simp [LieAlgebra.ExtendScalars.bracket_tmul, smul_lie, lie_smul, smul_smul, mul_comm]
      | add y₁ y₂ h₁ h₂ => rw [LieRing.lie_add, map_add, h₁, h₂, map_add, LieRing.lie_add]
    | add x₁ x₂ h₁ h₂ => rw [LieRing.add_lie, map_add, h₁, h₂, map_add, LieRing.add_lie]

@[simp] private theorem extendEmbedding_tmul {M L : Type*} [LieRing M] [LieAlgebra ℝ M]
    [LieRing L] [LieAlgebra ℂ L] [LieAlgebra ℝ L] [IsScalarTower ℝ ℂ L] (f : M →ₗ⁅ℝ⁆ L) (c : ℂ) (x : M) :
    extendEmbedding f (c ⊗ₜ[ℝ] x) = c • f x := rfl

private theorem complexify_su_tmul (c : ℂ) (x : su 2) :
    complexifyMap (su 2) (c ⊗ₜ[ℝ] x) = c • x.val := rfl

private def complexSuCoords : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![I * v 0, v 1 + I * v 2, -v 1 + I * v 2]
  invFun v := ![v 0 / I, (v 1 - v 2) / 2, (v 1 + v 2) / (2 * I)]
  left_inv v := by
    funext i
    fin_cases i <;> simp
    field_simp [I_ne_zero]
    ring
  right_inv v := by
    funext i
    fin_cases i <;> simp <;> field_simp [I_ne_zero] <;>
      first | (ring; done) | linear_combination -(v 0) * I_mul_I
  map_add' x y := by funext i; fin_cases i <;> simp [Pi.add_apply] <;> ring
  map_smul' t x := by funext i; fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul] <;> ring

private theorem complex_mk_eq (a b : ℝ) : (⟨a, b⟩ : ℂ) = (a : ℂ) + I * (b : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem su_real_form : IsRealForm (su 2) := by
  let e := (complexCoordinates suCoords).trans (complexSuCoords.trans (slCoords ℂ).symm)
  suffices hh : (complexifyMap (su 2)).toLinearMap = e.toLinearMap by
    change Function.Bijective (complexifyMap (su 2)).toLinearMap
    rw [hh]
    exact e.bijective
  apply (LinearMap.liftBaseChangeEquiv ℂ).symm.injective
  apply LinearMap.ext
  intro x
  change complexifyMap (su 2) (1 ⊗ₜ[ℝ] x) = e (1 ⊗ₜ[ℝ] x)
  rw [complexify_su_tmul, one_smul]
  apply (slCoords ℂ).injective
  change slCoords ℂ x.val = (slCoords ℂ) ((slCoords ℂ).symm
    (complexSuCoords (complexCoordinates suCoords (1 ⊗ₜ[ℝ] x))))
  rw [LinearEquiv.apply_symm_apply]
  funext i
  have hx : suMatrix (suCoords x 0) (suCoords x 1) (suCoords x 2) = x :=
    suCoords.symm_apply_apply x
  conv_lhs => rw [← hx]
  fin_cases i <;>
    simp [complexSuCoords, complexCoordinates_tmul, suMatrix, slMatrix, complex_mk_eq]

private theorem split_complexification :
    ∃ e : (ℂ ⊗[ℝ] sl₂ℝ) ≃ₗ⁅ℂ⁆ sl₂ℂ, ∀ c x, e (c ⊗ₜ[ℝ] x) = c • splitEmbedding x := by
  let e := (complexCoordinates (slCoords ℝ)).trans (slCoords ℂ).symm
  have hh : (extendEmbedding splitEmbedding).toLinearMap = e.toLinearMap := by
    apply (LinearMap.liftBaseChangeEquiv ℂ).symm.injective
    apply LinearMap.ext
    intro x
    change extendEmbedding splitEmbedding (1 ⊗ₜ[ℝ] x) = e (1 ⊗ₜ[ℝ] x)
    rw [extendEmbedding_tmul, one_smul]
    apply (slCoords ℂ).injective
    change slCoords ℂ (splitEmbedding x) =
      (slCoords ℂ) ((slCoords ℂ).symm (complexCoordinates (slCoords ℝ) (1 ⊗ₜ[ℝ] x)))
    rw [LinearEquiv.apply_symm_apply]
    funext i
    fin_cases i <;> simp [complexCoordinates_tmul, splitEmbedding]
  have hb : Function.Bijective (extendEmbedding splitEmbedding) := by
    change Function.Bijective (extendEmbedding splitEmbedding).toLinearMap
    rw [hh]
    exact e.bijective
  exact ⟨LieEquiv.ofBijective (extendEmbedding splitEmbedding) hb, fun _ _ => rfl⟩

private theorem real_forms_proof : real_forms_type :=
  ⟨su_real_form, split_complexification, killing_su_neg,
    ⟨splitDiagonalCoordinates, killing_sl_diagonal⟩, forms_distinct⟩


open Specs.LieAlgebrasAndRepresentations

private abbrev diagonalCartan := ClassicalRootsA.cartan 1

private theorem mem_diagonal (X : sl₂ℂ) :
    X ∈ diagonalCartan ↔ X.val 0 1 = 0 ∧ X.val 1 0 = 0 := by
  change X.val.IsDiag ↔ _
  constructor
  · intro h
    exact ⟨h (by decide), h (by decide)⟩
  · rintro ⟨h₀, h₁⟩ i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact h₀
    · exact h₁
    · exact (hij rfl).elim

private theorem mem_compact_diagonal (X : su 2) :
    X ∈ compactCartan ↔ X.val.val 0 1 = 0 ∧ X.val.val 1 0 = 0 := mem_diagonal X.val

private def diagElement (a : ℂ) : diagonalCartan :=
  ⟨slMatrix a 0 0, (mem_diagonal _).2 ⟨rfl, rfl⟩⟩

private def compactDiagElement (a : ℝ) : compactCartan :=
  ⟨suMatrix a 0 0, (mem_compact_diagonal _).2
    ⟨rfl, by simp [suMatrix, slMatrix, Complex.ext_iff]⟩⟩

private theorem diag_bracket (X Y : sl₂ℂ) (h : X ∈ diagonalCartan) :
    slCoords ℂ ⁅X, Y⁆ = ![0, 2 * X.val 0 0 * Y.val 0 1, -(2 * X.val 0 0) * Y.val 1 0] := by
  obtain ⟨h₀, h₁⟩ := (mem_diagonal X).1 h
  rw [slBracket]
  funext i
  fin_cases i <;> simp [h₀, h₁, mul_neg, mul_assoc]

private theorem diagonal_cartan : diagonalCartan.IsCartanSubalgebra := by
  let _ : IsLieAbelian diagonalCartan := ⟨fun x y => by
    apply Subtype.ext
    apply (slCoords ℂ).injective
    change slCoords ℂ ⁅x.val, y.val⁆ = slCoords ℂ 0
    obtain ⟨h₀, h₁⟩ := (mem_diagonal y.val).1 y.property
    rw [diag_bracket x.val y.val x.property, map_zero]
    funext i
    fin_cases i <;> simp [h₀, h₁]⟩
  refine ⟨inferInstance, le_antisymm ?_ diagonalCartan.le_normalizer⟩
  intro X hX
  have h := (diagonalCartan.mem_normalizer_iff' X).1 hX (diagElement 1).val (diagElement 1).property
  obtain ⟨h₀, h₁⟩ := (mem_diagonal _).1 h
  have hb := diag_bracket (diagElement 1).val X (diagElement 1).property
  have hb₀ := congrFun hb 1
  have hb₁ := congrFun hb 2
  change (⁅(diagElement 1).val, X⁆ : sl₂ℂ).val 0 1 = 0 at h₀
  change (⁅(diagElement 1).val, X⁆ : sl₂ℂ).val 1 0 = 0 at h₁
  have hD : (diagElement 1).val.val 0 0 = 1 := rfl
  simp [h₀, hD] at hb₀
  simp [h₁, hD] at hb₁
  exact (mem_diagonal X).2 ⟨hb₀, hb₁⟩

private theorem compact_diagonal_cartan : compactCartan.IsCartanSubalgebra := by
  let _ : IsLieAbelian compactCartan := ⟨fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    apply (slCoords ℂ).injective
    change slCoords ℂ ⁅x.val.val, y.val.val⁆ = slCoords ℂ 0
    obtain ⟨h₀, h₁⟩ := (mem_compact_diagonal y.val).1 y.property
    rw [diag_bracket x.val.val y.val.val x.property, map_zero]
    funext i
    fin_cases i <;> simp [h₀, h₁]⟩
  refine ⟨inferInstance, le_antisymm ?_ compactCartan.le_normalizer⟩
  intro X hX
  let D := compactDiagElement 1
  have h := (compactCartan.mem_normalizer_iff' X).1 hX D.val D.property
  obtain ⟨h₀, h₁⟩ := (mem_compact_diagonal _).1 h
  have hb := diag_bracket D.val.val X.val D.property
  have hD : D.val.val.val 0 0 = I := rfl
  have hb₀ := congrFun hb 1
  have hb₁ := congrFun hb 2
  change (⁅D.val.val, X.val⁆ : sl₂ℂ).val 0 1 = 0 at h₀
  change (⁅D.val.val, X.val⁆ : sl₂ℂ).val 1 0 = 0 at h₁
  simp [h₀, hD, I_ne_zero] at hb₀
  simp [h₁, hD, I_ne_zero] at hb₁
  exact (mem_compact_diagonal X).2 ⟨hb₀, hb₁⟩

private theorem diagonal_not_zero_of_coords {X : sl₂ℂ} (hX : X ≠ 0) (h₀ : X.val 0 0 = 0) :
    X.val 0 1 ≠ 0 ∨ X.val 1 0 ≠ 0 := by
  by_contra! h
  apply hX
  apply (slCoords ℂ).injective
  rw [map_zero]
  funext i
  fin_cases i
  · exact h₀
  · exact h.1
  · exact h.2

private def upperRootVector : sl₂ℂ := slMatrix 0 1 0
private def lowerRootVector : sl₂ℂ := slMatrix 0 0 1

private theorem upperRootVector_ne : upperRootVector ≠ 0 := by
  intro h
  have := congrArg (fun x : sl₂ℂ => x.val 0 1) h
  norm_num [upperRootVector, slMatrix] at this

private theorem lowerRootVector_ne : lowerRootVector ≠ 0 := by
  intro h
  have := congrArg (fun x : sl₂ℂ => x.val 1 0) h
  norm_num [lowerRootVector, slMatrix] at this

private theorem diag_upper_eigen (D : sl₂ℂ) (hD : D ∈ diagonalCartan) :
    ⁅D, upperRootVector⁆ = (2 * D.val 0 0) • upperRootVector := by
  apply (slCoords ℂ).injective
  rw [diag_bracket D _ hD, map_smul]
  funext i
  fin_cases i <;> simp [upperRootVector, slMatrix, Pi.smul_apply, smul_eq_mul]

private theorem diag_lower_eigen (D : sl₂ℂ) (hD : D ∈ diagonalCartan) :
    ⁅D, lowerRootVector⁆ = -(2 * D.val 0 0) • lowerRootVector := by
  apply (slCoords ℂ).injective
  rw [diag_bracket D _ hD, map_smul]
  funext i
  fin_cases i <;> simp [lowerRootVector, slMatrix, Pi.smul_apply, smul_eq_mul]

private theorem root_apply (D : diagonalCartan) :
    ClassicalRootsA.root 1 0 1 D = 2 * D.val.val 0 0 := by
  change D.val.val 0 0 - D.val.val 1 1 = _
  rw [sl_diag]
  ring

private theorem complex_type_A1_proof : complex_type_A1_type := by
  let α := ClassicalRootsA.root 1 0 1
  have hα : α (ClassicalRootsA.coroot 1 0 1) = 2 := by
    rw [root_apply]
    change 2 * ((Matrix.single 0 0 1 - Matrix.single 1 1 1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0) = 2
    norm_num [Matrix.single]
  refine ⟨diagonal_cartan, ?_, hα⟩
  change RootDecomposition.rootSet_value diagonalCartan = {α, -α}
  have hα₀ : α ≠ 0 := by
    intro h
    rw [h, LinearMap.zero_apply] at hα
    norm_num at hα
  ext β
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hβ, hroot⟩
    obtain ⟨X, hX, hn⟩ := (Submodule.ne_bot_iff _).1 hroot
    change X ∈ LieModule.weightSpace sl₂ℂ β at hX
    have hwt := (LieModule.mem_weightSpace (β : diagonalCartan → ℂ) X).1 hX
    have hcoord (D : diagonalCartan) :
        ![0, 2 * D.val.val 0 0 * X.val 0 1, -(2 * D.val.val 0 0) * X.val 1 0] =
          β D • slCoords ℂ X := by
      have h := congrArg (slCoords ℂ) (hwt D)
      change slCoords ℂ ⁅D.val, X⁆ = _ at h
      rwa [diag_bracket _ _ D.property, map_smul] at h
    have h₀ : X.val 0 0 = 0 := by
      by_contra hn₀
      apply hβ
      apply LinearMap.ext
      intro D
      have h := congrFun (hcoord D) 0
      exact (mul_eq_zero.mp h.symm).resolve_right hn₀
    rcases diagonal_not_zero_of_coords hn h₀ with hb | hc
    · left
      apply LinearMap.ext
      intro D
      rw [root_apply]
      exact mul_right_cancel₀ hb (congrFun (hcoord D) 1).symm
    · right
      apply LinearMap.ext
      intro D
      rw [LinearMap.neg_apply, root_apply]
      exact mul_right_cancel₀ hc (congrFun (hcoord D) 2).symm
  · rintro (rfl | rfl)
    · refine ⟨hα₀, (Submodule.ne_bot_iff _).2 ⟨upperRootVector, ?_, upperRootVector_ne⟩⟩
      apply (LieModule.mem_weightSpace _ _).2
      intro D
      rw [root_apply]
      exact diag_upper_eigen D.val D.property
    · refine ⟨neg_ne_zero.mpr hα₀, (Submodule.ne_bot_iff _).2 ⟨lowerRootVector, ?_, lowerRootVector_ne⟩⟩
      apply (LieModule.mem_weightSpace _ _).2
      intro D
      rw [LinearMap.neg_apply, root_apply]
      exact diag_lower_eigen D.val D.property

private theorem diag_nonzero_eigenvalues (D : sl₂ℂ) (hD : D ∈ diagonalCartan)
    (z : ℂ) (hz : z ≠ 0) :
    (LieAlgebra.ad ℂ sl₂ℂ D).eigenspace z ≠ ⊥ ↔
      z = 2 * D.val 0 0 ∨ z = -(2 * D.val 0 0) := by
  rw [Submodule.ne_bot_iff]
  constructor
  · rintro ⟨X, hX, hn⟩
    have h := congrArg (slCoords ℂ) (Module.End.mem_eigenspace_iff.1 hX)
    rw [LieAlgebra.ad_apply, diag_bracket _ _ hD, map_smul] at h
    have h₀ : X.val 0 0 = 0 := (mul_eq_zero.mp (congrFun h 0).symm).resolve_left hz
    rcases diagonal_not_zero_of_coords hn h₀ with hb | hc
    · exact Or.inl (mul_right_cancel₀ hb (congrFun h 1).symm)
    · exact Or.inr (mul_right_cancel₀ hc (congrFun h 2).symm)
  · rintro (rfl | rfl)
    · exact ⟨upperRootVector, Module.End.mem_eigenspace_iff.2 (diag_upper_eigen D hD),
        upperRootVector_ne⟩
    · exact ⟨lowerRootVector, Module.End.mem_eigenspace_iff.2 (diag_lower_eigen D hD),
        lowerRootVector_ne⟩


private def diagonalCoords : diagonalCartan ≃ₗ[ℂ] (Fin 1 → ℂ) where
  toFun D _ := D.val.val 0 0
  invFun f := diagElement (f 0)
  left_inv D := by
    apply Subtype.ext
    apply (slCoords ℂ).injective
    obtain ⟨h₀, h₁⟩ := (mem_diagonal _).1 D.property
    funext i
    fin_cases i <;> simp [diagElement, slMatrix, h₀, h₁]
  right_inv f := by funext i; fin_cases i; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def compactDiagCoords : compactCartan ≃ₗ[ℝ] (Fin 1 → ℝ) where
  toFun D _ := suCoords D.val 0
  invFun f := compactDiagElement (f 0)
  left_inv D := by
    apply Subtype.ext
    apply suCoords.injective
    obtain ⟨h₀, _⟩ := (mem_compact_diagonal _).1 D.property
    funext i
    fin_cases i <;> simp [compactDiagElement, suMatrix, slMatrix, h₀]
  right_inv f := by funext i; fin_cases i; rfl
  map_add' X Y := by funext i; exact congrFun (map_add suCoords X.val Y.val) 0
  map_smul' t X := by funext i; exact congrFun (map_smul suCoords t X.val) 0

private def compactCartanEmbedding : compactCartan →ₗ⁅ℝ⁆ diagonalCartan where
  toFun x := ⟨x.val.val, x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

private theorem diagonal_entry (x : su 2) :
    x.val.val 0 0 = (suCoords x 0 : ℂ) * I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, su_diag_re]

private theorem compact_cartan_complexification :
    ∃ e : (ℂ ⊗[ℝ] compactCartan) ≃ₗ⁅ℂ⁆ diagonalCartan,
      ∀ (c : ℂ) (x : compactCartan), (e (c ⊗ₜ[ℝ] x)).val = c • x.val.val := by
  let i := LinearEquiv.smulOfNeZero ℂ (Fin 1 → ℂ) I I_ne_zero
  let e := (complexCoordinates compactDiagCoords).trans (i.trans diagonalCoords.symm)
  have he : (extendEmbedding compactCartanEmbedding).toLinearMap = e.toLinearMap := by
    apply (LinearMap.liftBaseChangeEquiv ℂ).symm.injective
    apply LinearMap.ext
    intro x
    change extendEmbedding compactCartanEmbedding (1 ⊗ₜ[ℝ] x) = e (1 ⊗ₜ[ℝ] x)
    rw [extendEmbedding_tmul, one_smul]
    apply diagonalCoords.injective
    change diagonalCoords (compactCartanEmbedding x) =
      diagonalCoords (diagonalCoords.symm (i (complexCoordinates compactDiagCoords (1 ⊗ₜ[ℝ] x))))
    rw [diagonalCoords.apply_symm_apply]
    funext j
    change x.val.val.val 0 0 = I * complexCoordinates compactDiagCoords (1 ⊗ₜ[ℝ] x) j
    rw [diagonal_entry, complexCoordinates_tmul, one_mul, mul_comm]
    rfl
  have hb : Function.Bijective (extendEmbedding compactCartanEmbedding) := by
    change Function.Bijective (extendEmbedding compactCartanEmbedding).toLinearMap
    rw [he]
    exact e.bijective
  exact ⟨LieEquiv.ofBijective (extendEmbedding compactCartanEmbedding) hb, fun _ _ => rfl⟩

private theorem compact_cartan_proof : compact_cartan_type := by
  refine ⟨compact_diagonal_cartan, compact_cartan_complexification, ?_⟩
  intro x hx
  change suCoords x.val 0 ≠ 0 ∧ _
  refine ⟨?_, ?_⟩
  · intro h
    apply hx
    apply compactDiagCoords.injective
    funext j
    exact h
  · intro z hz
    change ((LieAlgebra.ad ℂ sl₂ℂ x.val.val).eigenspace z ≠ ⊥) ↔
      z = 2 * (suCoords x.val 0 : ℂ) * I ∨ z = -(2 * (suCoords x.val 0 : ℂ) * I)
    rw [diag_nonzero_eigenvalues x.val.val x.property z hz, diagonal_entry, mul_assoc]

/-- The real rotation representation has no invariant line or triangular basis. -/
theorem rotation_real : rotation_real_type := real_rotation

/-- After scalar extension the rotation has the two complementary eigenlines. -/
theorem rotation_complex : rotation_complex_type := complex_rotation

/-- The compact and split matrix algebras are distinct real forms of complex `sl₂`. -/
theorem real_forms : real_forms_type := real_forms_proof

/-- The roots of the complex diagonal Cartan give the Cartan matrix of type A₁. -/
theorem complex_type_A1 : complex_type_A1_type := complex_type_A1_proof

/-- The compact diagonal Cartan gives a pair of opposite imaginary eigenvalues. -/
theorem compact_cartan : compact_cartan_type := compact_cartan_proof

end LieAlgebrasAndRepresentations.NonsplitFieldBoundary
