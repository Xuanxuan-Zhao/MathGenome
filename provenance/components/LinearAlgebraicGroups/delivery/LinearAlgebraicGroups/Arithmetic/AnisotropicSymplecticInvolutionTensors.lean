import Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicSymplecticInvolutionTensors
import LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Tactic.NoncommRing

open CategoryTheory MulOpposite
open scoped TensorProduct Matrix

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicSymplecticInvolutionTensors

open LinearAlgebraicGroups.Specs
open Specs.AnisotropicSymplecticInvolutionTensors
open Specs.SymplecticDivisionForms
open SymplecticIsometryDescent (isometryPoints)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)

noncomputable section

theorem orthogonalAdjointIdempotents : OrthogonalAdjointIdempotents := by
  intro A _ σ
  let s (x : A) : A := MulOpposite.unop (σ x)
  change Function.Involutive s → ∀ z e : A, z + s z = 1 → e ≠ 0 → e * e = e → s e * e = 0 →
    ∃ p : A, p ≠ 0 ∧ p * p = p ∧ s p * p = 0 ∧ p * s p = 0
  intro hs z e hz he₀ he hezero
  have smul (x y : A) : s (x * y) = s y * s x := by simp [s]
  have ssub (x y : A) : s (x - y) = s x - s y := by simp [s]
  have he' : s e * s e = s e := by rw [← smul, he]
  let corner (w : A) := e * w * s e
  have corner_left (w : A) : e * corner w = corner w := by
    simp only [corner, ← mul_assoc, he]
  have corner_right (w : A) : corner w * s e = corner w := by
    change (e * w * s e) * s e = e * w * s e
    rw [mul_assoc, he']
  have corner_mul_e (w : A) : corner w * e = 0 := by
    change (e * w * s e) * e = 0
    rw [mul_assoc, hezero, mul_zero]
  have adj_e_mul_corner (w : A) : s e * corner w = 0 := by
    change s e * (e * w * s e) = 0
    simp only [← mul_assoc, hezero, zero_mul]
  have corner_mul_corner (u w : A) : corner u * corner w = 0 := by
    change (e * u * s e) * corner w = 0
    rw [mul_assoc, adj_e_mul_corner, mul_zero]
  have adj_corner (w : A) : s (corner w) = corner (s w) := by
    simp [corner, smul, hs e, mul_assoc]
  let p : A := e - corner z
  have hpstar : s p = s e - corner (s z) := by simp only [p, ssub, adj_corner]
  have hpe : p * e = e := by
    simp only [p, sub_mul, he, corner_mul_e, sub_zero]
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · intro hp
    rw [hp, zero_mul] at hpe
    exact he₀ hpe.symm
  · calc
      p * p = (p * e) - (e * corner z - corner z * corner z) := by
        simp only [p]
        noncomm_ring
      _ = p := by rw [hpe, corner_left, corner_mul_corner, sub_zero]
  · rw [hpstar]
    simp only [p, sub_mul, mul_sub, hezero, adj_e_mul_corner, corner_mul_e,
      corner_mul_corner, sub_self]
  · have hadd : corner (s z) + corner z = e * s e := by
      have h : s z + z = 1 := by simpa only [add_comm] using hz
      simp [corner, ← add_mul, ← mul_add, h]
    calc
      p * s p = e * s e - (e * corner (s z) + corner z * s e) + corner z * corner (s z) := by
        rw [hpstar]
        simp only [p]
        noncomm_ring
      _ = 0 := by rw [corner_left, corner_right, corner_mul_corner, hadd, sub_self, add_zero]



section Torus

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
  (s : SymplecticIsometryDescent.Involution k A)

private def torusValue {R : Type u} [CommRing R] [Algebra k R]
    (p : A) (t : Rˣ) : R ⊗[k] A :=
  (t : R) ⊗ₜ[k] p + (↑t⁻¹ : R) ⊗ₜ[k] s.toLinearMap p +
    (1 : R) ⊗ₜ[k] (1 - p - s.toLinearMap p)

private theorem torusValue_one {R : Type u} [CommRing R] [Algebra k R] (p : A) :
    torusValue s p (1 : Rˣ) = 1 := by
  rw [torusValue, inv_one, Units.val_one, ← TensorProduct.tmul_add,
    ← TensorProduct.tmul_add, Algebra.TensorProduct.one_def]
  congr 1
  abel

private theorem torusValue_mul {R : Type u} [CommRing R] [Algebra k R]
    (p : A) (hp : p * p = p) (hsp : s.toLinearMap p * p = 0)
    (hps : p * s.toLinearMap p = 0) (t v : Rˣ) :
    torusValue s p (t * v) = torusValue s p t * torusValue s p v := by
  let b := s.toLinearMap p
  let q := 1 - p - b
  change b * p = 0 at hsp
  change p * b = 0 at hps
  have hb : b * b = b := by
    change s.toLinearMap p * s.toLinearMap p = s.toLinearMap p
    rw [← s.map_mul, hp]
  have hpq : p * q = 0 := by simp [q, mul_sub, hp, hps]
  have hqp : q * p = 0 := by simp [q, sub_mul, hp, hsp]
  have hbq : b * q = 0 := by simp only [q, mul_sub, mul_one, hsp, hb, sub_zero, sub_self]
  have hqb : q * b = 0 := by simp only [q, sub_mul, one_mul, hps, hb, sub_zero, sub_self]
  have hq : q * q = q := by rw [show q = 1 - p - b from rfl, sub_mul, sub_mul,
    one_mul, hpq, hbq, sub_zero, sub_zero]
  change ((t * v : Rˣ) : R) ⊗ₜ[k] p + (↑(t * v)⁻¹ : R) ⊗ₜ[k] b +
    (1 : R) ⊗ₜ[k] q = _
  unfold torusValue
  change _ = ((t : R) ⊗ₜ[k] p + (↑t⁻¹ : R) ⊗ₜ[k] b + (1 : R) ⊗ₜ[k] q) *
    ((v : R) ⊗ₜ[k] p + (↑v⁻¹ : R) ⊗ₜ[k] b + (1 : R) ⊗ₜ[k] q)
  simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, hp, hb, hq,
    hpq, hqp, hbq, hqb, hsp, hps, TensorProduct.tmul_zero, add_zero, zero_add, mul_one,
    one_mul, Units.val_mul, mul_inv_rev]
  rw [mul_comm (↑v⁻¹ : R) (↑t⁻¹ : R)]

private theorem torusValue_adj {R : Type u} [CommRing R] [Algebra k R]
    (p : A) (t : Rˣ) :
    (s.baseChange R).toLinearMap (torusValue s p t) = torusValue s p t⁻¹ := by
  have hq : s.toLinearMap (1 - p - s.toLinearMap p) = 1 - p - s.toLinearMap p := by
    rw [map_sub, map_sub, s.map_one, s.involutive]
    abel
  simp only [torusValue, map_add, SymplecticIsometryDescent.Involution.baseChange_tmul,
    s.involutive p, hq, inv_inv]
  rw [add_comm ((t : R) ⊗ₜ[k] s.toLinearMap p)]

private def torusAt (p : A) (hp : p * p = p) (hsp : s.toLinearMap p * p = 0)
    (hps : p * s.toLinearMap p = 0) (R : TestAlgebra k) :
    Rˣ →* (s.baseChange R).isometries where
  toFun t :=
    ⟨⟨torusValue s p t, torusValue s p t⁻¹,
      by rw [← torusValue_mul s p hp hsp hps, mul_inv_cancel, torusValue_one],
      by rw [← torusValue_mul s p hp hsp hps, inv_mul_cancel, torusValue_one]⟩, by
        change (s.baseChange R).toLinearMap (torusValue s p t) * torusValue s p t = 1
        rw [torusValue_adj, ← torusValue_mul s p hp hsp hps, inv_mul_cancel, torusValue_one]⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact torusValue_one s p
  map_mul' t v := by
    apply Subtype.ext
    apply Units.ext
    exact torusValue_mul s p hp hsp hps t v

private def torus (p : A) (hp : p * p = p) (hsp : s.toLinearMap p * p = 0)
    (hps : p * s.toLinearMap p = 0) :
    SplitCocharacter s where
  app R := GrpCat.ofHom (torusAt s p hp hsp hps R)
  naturality R S f := by
    apply GrpCat.ext
    intro t
    apply Subtype.ext
    apply Units.ext
    change torusValue s p (Units.map f.hom.toMonoidHom t) =
      SymplecticIsometryDescent.tensorMap f (torusValue s p t)
    let t' : Rˣ := t
    change torusValue s p (Units.map f.hom.toMonoidHom t') =
      SymplecticIsometryDescent.tensorMap f (torusValue s p t')
    have hv (x : Rˣ) : Units.val (Units.map f.hom.toMonoidHom x) = f.hom (Units.val x) := rfl
    simp only [torusValue, ← map_inv (Units.map f.hom.toMonoidHom) t', hv,
      map_add, SymplecticIsometryDescent.tensorMap, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, map_one]

private theorem torusValue_injective {R : Type u} [CommRing R] [Algebra k R]
    {p : A} (hp₀ : p ≠ 0) (hp : p * p = p) (hsp : s.toLinearMap p * p = 0) :
    Function.Injective (torusValue (R := R) s p) := by
  intro t v h
  have hq : (1 - p - s.toLinearMap p) * p = 0 := by simp [sub_mul, hp, hsp]
  have hm (x : Rˣ) :
      torusValue s p x * ((1 : R) ⊗ₜ[k] p) = (x : R) ⊗ₜ[k] p := by
    simp [torusValue, add_mul, Algebra.TensorProduct.tmul_mul_tmul, hp, hsp, hq]
  have h' := congrArg (fun x => x * ((1 : R) ⊗ₜ[k] p)) h
  rw [hm, hm] at h'
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hp₀
  have ht := congrArg (TensorProduct.map (LinearMap.id : R →ₗ[k] R) f) h'
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, hf] at ht
  apply Units.ext
  simpa using congrArg (Algebra.TensorProduct.rid k R R) ht

theorem isotropicIdempotentSplitTorus : IsotropicIdempotentSplitTorus.{u} := by
  intro k A _ _ _ s z e hz he₀ he hse
  obtain ⟨p, hp₀, hp, hsp, hps⟩ :=
    orthogonalAdjointIdempotents (toDivisionInvolution s).anti.toRingEquiv
      s.involutive z e hz he₀ he hse
  refine ⟨p, torus s p hp hsp hps, hp₀, hp, hsp, hps, fun R => ⟨?_, fun t => rfl⟩⟩
  intro t v h
  exact torusValue_injective s hp₀ hp hsp
    (congrArg (fun g : (isometryPoints s).obj R => (g.val : R ⊗[k] A)) h)

open private involutionTraceOne from LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels

theorem symplecticIsotropicIdempotentSplitTorus : SymplecticIsotropicIdempotentSplitTorus.{u} := by
  intro k A K _ _ _ _ _ s n c
  obtain ⟨z, hz⟩ := involutionTraceOne s c
  exact ⟨z, hz, fun e => isotropicIdempotentSplitTorus s z e hz⟩

end Torus

section Corner

open private antiValue_add antiValue_mul antiValue_zero antiValue_one antiValue_smul transportAnti
  from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

variable {k C : Type*} [Field k] [Ring C] [Algebra k C]

private def conjugate (U : Cˣ) : C ≃ₐ[k] C where
  toFun x := U.inv * x * U.val
  invFun x := U.val * x * U.inv
  left_inv x := by
    change U.val * (U.inv * x * U.val) * U.inv = x
    simp only [mul_assoc, U.val_inv, mul_one]
    rw [← mul_assoc, U.val_inv, one_mul]
  right_inv x := by
    change U.inv * (U.val * x * U.inv) * U.val = x
    simp only [mul_assoc, U.inv_val, mul_one]
    rw [← mul_assoc, U.inv_val, one_mul]
  map_mul' x y := by
    simp only [mul_assoc, ← mul_assoc U.val U.inv, U.val_inv, one_mul]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' a := by
    rw [(Algebra.commutes a U.inv).symm, mul_assoc, U.inv_val, mul_one]

variable {D I : Type*} [Ring D] [Fintype I] [DecidableEq I]

private def columnMatrix (i : I) (v : I → D) : Matrix I I D :=
  Matrix.of fun j l => if l = i then v j else 0

private theorem mul_single_eq_column (X : Matrix I I D) (i j : I) (a : D) :
    X * Matrix.single i j a = columnMatrix j (fun l => X l i * a) := by
  ext l m
  by_cases h : m = j
  · subst m
    simp [columnMatrix]
  · simp [columnMatrix, h]

private theorem columnMatrix_mul (i j : I) (v w : I → D) :
    columnMatrix i v * columnMatrix j w = columnMatrix j (fun l => v l * w i) := by
  ext l m
  by_cases h : m = j
  · subst m
    simp [Matrix.mul_apply, columnMatrix, ite_mul]
  · simp [Matrix.mul_apply, columnMatrix, h]

omit [Fintype I] in
private theorem single_column (i : I) (a : D) :
    Matrix.single i i a = columnMatrix i (Pi.single i a) := by
  ext j l
  by_cases h : l = i <;> by_cases hj : j = i <;> simp [Matrix.single, columnMatrix, h, hj, eq_comm (a := i) (b := j), eq_comm (a := i) (b := l)]

private theorem corner_eq_single {i : I} {X : Matrix I I D}
    (hl : Matrix.single i i 1 * X = X) (hr : X * Matrix.single i i 1 = X) :
    X = Matrix.single i i (X i i) := by
  ext j l
  by_cases hj : j = i
  · subst j
    by_cases hl' : l = i
    · subst l
      simp
    · rw [← congrArg (fun M : Matrix I I D => M i l) hr]
      rw [Matrix.mul_single_apply_of_ne (c := (1 : D)) i i i l hl' X]
      simp [Matrix.single, Ne.symm hl']
  · rw [← congrArg (fun M : Matrix I I D => M j l) hl]
    rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hj]
    simp [Matrix.single, Ne.symm hj]

private def cornerInvolution [Algebra k D]
    (s : Involution k (Matrix I I D)) (i : I)
    (hs : antiValue s.anti (Matrix.single i i 1) = Matrix.single i i 1) :
    Involution k D := by
  let b (x : D) := (antiValue s.anti (Matrix.single i i x)) i i
  have h (x : D) : antiValue s.anti (Matrix.single i i x) = Matrix.single i i (b x) := by
    apply corner_eq_single
    · rw [← hs, ← antiValue_mul, Matrix.single_mul_single_same, mul_one]
    · rw [← hs, ← antiValue_mul, Matrix.single_mul_single_same, one_mul]
  have hb (x : D) : b (b x) = x := by
    dsimp only [b] at ⊢
    rw [← h, s.square]
    simp
  refine ⟨
    { toFun := fun x => op (b x)
      invFun := fun x => b (unop x)
      left_inv := hb
      right_inv := fun x => unop_injective (hb (unop x))
      map_add' := ?_
      map_mul' := ?_
      commutes' := ?_ }, hb⟩
  · intro x y
    apply unop_injective
    change b (x * y) = b y * b x
    have hxy : Matrix.single i i (x * y) = Matrix.single i i x * Matrix.single i i y :=
      (Matrix.single_mul_single_same (c := x) i i i y).symm
    change antiValue s.anti (Matrix.single i i (x * y)) i i = b y * b x
    rw [hxy, antiValue_mul, h y, h x, Matrix.single_mul_single_same]
    simp
  · intro x y
    apply unop_injective
    change b (x + y) = b x + b y
    dsimp only [b]
    rw [Matrix.single_add, antiValue_add]
    rfl
  · intro a
    apply unop_injective
    change b (algebraMap k D a) = algebraMap k D a
    have ha : Matrix.single i i (algebraMap k D a) = a • (Matrix.single i i 1 : Matrix I I D) := by
      ext j l
      by_cases hj : j = i <;> by_cases hl : l = i <;>
        simp [Matrix.single, hj, hl, Matrix.smul_apply, Algebra.smul_def]
    dsimp only [b]
    rw [ha, antiValue_smul, hs, Matrix.smul_apply, Matrix.single_apply_same,
      Algebra.smul_def, mul_one]

private theorem matrixSelfAdjointCorner {D : Type*} [DivisionRing D] [Algebra k D]
    (s : Involution k (Matrix I I D)) (i : I)
    (hanis : ∀ p : Matrix I I D, p ≠ 0 → p * p = p → antiValue s.anti p * p ≠ 0) :
    ∃ U : (Matrix I I D)ˣ, antiValue s.anti
      ((conjugate (k := k) U).symm (Matrix.single i i 1)) =
        (conjugate (k := k) U).symm (Matrix.single i i 1) := by
  let E : Matrix I I D := Matrix.single i i 1
  let star := antiValue s.anti
  have hE : E * E = E := by simp [E]
  have hE₀ : E ≠ 0 := by
    intro h
    have h' := congrArg (fun M : Matrix I I D => M i i) h
    simp [E] at h'
  let B := star E * E
  have hB₀ : B ≠ 0 := hanis E hE₀ hE
  have hB : star B = B := by
    change antiValue s.anti (antiValue s.anti E * E) = B
    rw [antiValue_mul, s.square]
  let v (j : I) := star E j i
  have hv : B = columnMatrix i v := by
    change star E * Matrix.single i i 1 = columnMatrix i v
    rw [mul_single_eq_column]
    simp [v]
  have hdiag : v i ≠ 0 := by
    intro hz
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra! h
      exact hB₀ (by ext j l; simp [hv, columnMatrix, h])
    let X : Matrix I I D := Matrix.single i j (v j)⁻¹
    let Q := B * X
    have hQ : Q = columnMatrix j (fun l => v l * (v j)⁻¹) := by
      rw [show Q = B * Matrix.single i j (v j)⁻¹ from rfl, mul_single_eq_column, hv]
      simp [columnMatrix]
    have hQ₀ : Q ≠ 0 := by
      intro h
      have heq := congrArg (fun M : Matrix I I D => M j j) h
      simp [hQ, columnMatrix, hj] at heq
    have hQQ : Q * Q = Q := by rw [hQ, columnMatrix_mul]; simp [hj]
    have hBB : B * B = 0 := by
      rw [hv, columnMatrix_mul]
      ext l m
      simp [columnMatrix, hz]
    apply hanis Q hQ₀ hQQ
    change antiValue s.anti (B * X) * (B * X) = 0
    rw [antiValue_mul, show antiValue s.anti B = B from hB,
      mul_assoc (antiValue s.anti X), ← mul_assoc B B, hBB, zero_mul, mul_zero]
  let X : Matrix I I D := Matrix.single i i (v i)⁻¹
  let P := B * X
  have hP : P = columnMatrix i (fun j => v j * (v i)⁻¹) := by
    rw [show P = B * Matrix.single i i (v i)⁻¹ from rfl, mul_single_eq_column, hv]
    simp [columnMatrix]
  have hPP : P * P = P := by rw [hP, columnMatrix_mul]; simp [hdiag]
  have hPB : P * B = B := by
    rw [hP, hv, columnMatrix_mul]
    simp [hdiag]
  have hBP : B * P = B := by rw [hP, hv, columnMatrix_mul]; simp [hdiag]
  have hsPB : star P * B = B := by
    rw [← hB, ← antiValue_mul, hBP]
  have hsPP : star P * P = P := by
    change star P * (B * X) = B * X
    rw [← mul_assoc, hsPB]
  have hself : star P = P := by
    have hh := congrArg star hsPP
    change antiValue s.anti (antiValue s.anti P * P) = star P at hh
    rw [antiValue_mul, s.square, hsPP] at hh
    exact hh.symm
  have hPE : P * E = P := by
    rw [hP, show E = _ from single_column i (1 : D), columnMatrix_mul]
    simp
  have hEP : E * P = E := by
    rw [hP, show E = _ from single_column i (1 : D), columnMatrix_mul]
    simp [hdiag]
  let N := P - E
  have hN : N * N = 0 := by
    simp [N, mul_sub, sub_mul, hPP, hE, hPE, hEP]
  let U : (Matrix I I D)ˣ :=
    ⟨1 + N, 1 - N,
      by simp only [add_mul, mul_sub, one_mul, mul_one, hN]; abel,
      by simp only [sub_mul, mul_add, one_mul, mul_one, hN]; abel⟩
  have hc : (conjugate (k := k) U).symm E = P := by
    change (1 + (P - E)) * E * (1 - (P - E)) = P
    simp only [add_mul, sub_mul, mul_sub, one_mul, mul_one, hPE, hE, hPP]
    abel
  refine ⟨U, ?_⟩
  change antiValue s.anti ((conjugate (k := k) U).symm E) = _
  rw [hc]
  exact hself

theorem involutoryDivisionCorner : InvolutoryDivisionCorner.{u} := by
  intro k A D _ _ _ _ _ s r e i hanis
  let t : Involution k (Matrix (Fin r) (Fin r) D) :=
    ⟨transportAnti e s.anti, fun X => by
      change e (antiValue s.anti (e.symm (e (antiValue s.anti (e.symm X))))) = X
      rw [e.symm_apply_apply, s.square, e.apply_symm_apply]⟩
  have ht (X : Matrix (Fin r) (Fin r) D) : antiValue t.anti X = e (antiValue s.anti (e.symm X)) := rfl
  have ha (X : Matrix (Fin r) (Fin r) D) (hX₀ : X ≠ 0) (hX : X * X = X) :
      antiValue t.anti X * X ≠ 0 := by
    intro h
    apply hanis (e.symm X)
    · intro hz
      apply hX₀
      simpa using congrArg e hz
    · rw [← map_mul, hX]
    · apply e.injective
      simpa [ht] using h
  obtain ⟨U, hU⟩ := matrixSelfAdjointCorner t i ha
  let f : A ≃ₐ[k] Matrix (Fin r) (Fin r) D := e.trans (conjugate U)
  let a : Involution k (Matrix (Fin r) (Fin r) D) :=
    ⟨transportAnti f s.anti, fun X => by
      change f (antiValue s.anti (f.symm (f (antiValue s.anti (f.symm X))))) = X
      rw [f.symm_apply_apply, s.square, f.apply_symm_apply]⟩
  have hE : antiValue a.anti (Matrix.single i i 1) = Matrix.single i i 1 := by
    exact ((conjugate (k := k) U).eq_symm_apply).mp hU
  let σ := cornerInvolution a i hE
  refine ⟨f, σ, fun d => ?_⟩
  change antiValue a.anti (Matrix.single i i d) = Matrix.single i i (antiValue σ.anti d)
  exact corner_eq_single (by rw [← hE, ← antiValue_mul, Matrix.single_mul_single_same, mul_one])
    (by rw [← hE, ← antiValue_mul, Matrix.single_mul_single_same, one_mul])

end Corner

section HermitianForm

open private anti_gram matrixAnti transportAnti antiValue_mul antiValue_one antiValue_zero
  hermitianValue_laws hermitianValue_nondegenerate hermitianValue_congr hermitianValue_single
  extendEquiv matrixBaseChange matrixCoordinates_pure matrixBaseChange_natural
  extendAnti_square extendAnti_tmul quaternion_point_compare
  from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

variable {k D I : Type*} [Field k] [DivisionRing D] [Algebra k D]
  [Fintype I] [DecidableEq I]

private theorem cornerGramHermitian
    (hC : _root_.Specs.RM03.CSA.isCentralSimple k (Matrix I I D))
    (hD : _root_.Specs.RM03.CSA.isCentralDivision k D)
    (s : Involution k (Matrix I I D)) (σ : Involution k D)
    (i : I) (H : (Matrix I I D)ˣ)
    (h : ∀ X, antiValue s.anti X = H.inv * dagger σ.anti X * H.val)
    (hc : ∀ a, antiValue s.anti (Matrix.single i i a) =
      Matrix.single i i (antiValue σ.anti a)) :
    dagger σ.anti H.val = H.val := by
  let d := dagger (I := I) σ.anti
  have hd (X : Matrix I I D) : d (d X) = X := by
    ext j l
    exact σ.square (X j l)
  have hm (X Y : Matrix I I D) : d (X * Y) = d Y * d X :=
    QuaternionHermitianCocharacters.adjoint_mul σ.anti.toAlgHom X Y
  have hone : d 1 = 1 := QuaternionHermitianCocharacters.adjoint_one σ.anti.toAlgHom
  let U := H.inv * d H.val
  let V := d H.inv * H.val
  have hUXV (X : Matrix I I D) : U * X * V = X := by
    have hh := s.square X
    rw [h (antiValue s.anti X), h X] at hh
    change H.inv * d (H.inv * d X * H.val) * H.val = X at hh
    rw [hm, hm, hd] at hh
    simpa only [U, V, mul_assoc] using hh
  have hcomm (X : Matrix I I D) : X * U = U * X := by
    have hVU : V * U = 1 := by
      change (d H.inv * H.val) * (H.inv * d H.val) = 1
      rw [mul_assoc, ← mul_assoc H.val, H.val_inv, one_mul, ← hm, H.val_inv, hone]
    have hh := congrArg (fun Y => Y * U) (hUXV X)
    simpa only [mul_assoc, hVU, mul_one] using hh.symm
  let : Algebra.IsCentral k (Matrix I I D) := hC.2.1
  have hcU : U ∈ Subalgebra.center k (Matrix I I D) := Subalgebra.mem_center_iff.mpr hcomm
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hcU)
  have hH : d H.val = H.val * algebraMap k (Matrix I I D) a := by
    rw [ha]
    change d H.val = H.val * (H.inv * d H.val)
    rw [← mul_assoc, H.val_inv, one_mul]
  have hsingle (b : D) : dagger σ.anti (Matrix.single i i b) = Matrix.single i i (antiValue σ.anti b) := by
    ext j l
    by_cases hj : j = i
    · subst j
      by_cases hl : l = i <;> simp [dagger, Matrix.single, hl, Ne.symm]
    · by_cases hl : l = i <;> simp [dagger, Matrix.single, hj, hl, Ne.symm]
  have hM (b : D) : Matrix.single i i b * H.val = H.val * Matrix.single i i b := by
    have h' := h (Matrix.single i i (antiValue σ.anti b))
    rw [hc, hsingle, σ.square] at h'
    have h'' := congrArg (fun Y : Matrix I I D => H.val * Y) h'
    simpa only [← mul_assoc, H.val_inv, one_mul] using h''.symm
  have hDii (b : D) : b * H.val i i = H.val i i * b := by
    simpa only [Matrix.single_mul_apply_same, Matrix.mul_single_apply_same] using
      congrArg (fun X : Matrix I I D => X i i) (hM b)
  let : Algebra.IsCentral k D := hD.1
  have hZ := Algebra.IsCentral.out (Subalgebra.mem_center_iff.mpr hDii :
      H.val i i ∈ Subalgebra.center k D)
  obtain ⟨b, hb⟩ := Algebra.mem_bot.mp hZ
  have hfix : antiValue σ.anti (H.val i i) = H.val i i := by
    rw [← hb]
    simp [antiValue]
  have hrow (j : I) (hj : j ≠ i) : H.val i j = 0 := by
    have heq := congrArg (fun X : Matrix I I D => X i j) (hM 1)
    simpa [hj] using heq
  have hne : H.val i i ≠ 0 := by
    have heq := congrArg (fun X : Matrix I I D => X i i) H.val_inv
    change (∑ j, H.val i j * H.inv j i) = (1 : Matrix I I D) i i at heq
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [hrow j hj, zero_mul])
      (fun hi => (hi (Finset.mem_univ _)).elim), Matrix.one_apply_eq] at heq
    intro hzero
    rw [hzero, zero_mul] at heq
    exact zero_ne_one heq
  have heq := congrArg (fun X : Matrix I I D => X i i) hH
  change antiValue σ.anti (H.val i i) = (H.val * algebraMap k (Matrix I I D) a) i i at heq
  rw [hfix, (Algebra.commutes a H.val).symm, ← Algebra.smul_def, Matrix.smul_apply, Algebra.smul_def] at heq
  have haD : algebraMap k D a = 1 :=
    mul_right_cancel₀ hne (heq.symm.trans (one_mul (H.val i i)).symm)
  have ha1 : a = 1 := (algebraMap k D).injective (haD.trans (map_one _).symm)
  simpa [ha1] using hH

private theorem matrixFormAnisotropic
    (s : Involution k (Matrix I I D)) (σ : Involution k D) (H : (Matrix I I D)ˣ)
    (hH : dagger σ.anti H.val = H.val)
    (h : ∀ X, antiValue s.anti X = H.inv * dagger σ.anti X * H.val)
    (hanis : ∀ p : Matrix I I D, p ≠ 0 → p * p = p → antiValue s.anti p * p ≠ 0) :
    ∀ x : I → D, x ≠ 0 → hermitianValue σ.anti H.val x x ≠ 0 := by
  classical
  let b := hermitianValue σ.anti H.val
  have hb := hermitianValue_laws σ.anti σ.square H.val hH
  intro x hx hx0
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! hzero
    exact hx (funext hzero)
  let p := columnMatrix i (fun j => x j * (x i)⁻¹)
  have hp : p * p = p := by dsimp only [p]; rw [columnMatrix_mul]; simp [hi]
  have hp₀ : p ≠ 0 := by
    intro hz
    have hh := congrArg (fun X : Matrix I I D => X i i) hz
    simp [p, columnMatrix, hi] at hh
  have hpv (v : I → D) : p *ᵥ v = fun j => x j * ((x i)⁻¹ * v i) := by
    funext j
    simp [p, columnMatrix, Matrix.mulVec, dotProduct, ite_mul, mul_assoc]
  have hline (a c : D) : b (fun j => x j * a) (fun j => x j * c) = 0 := by
    dsimp only [b]
    rw [hb.mul_right, hb.symmetric x (fun j => x j * a),
      hb.mul_right, hx0, zero_mul, antiValue_zero, zero_mul]
  have hzero : dagger σ.anti p * H.val * p = 0 := by
    ext j l
    have h' := hermitianValue_congr σ.anti H.val p (Pi.single j 1) (Pi.single l 1)
    rw [hpv, hpv, hermitianValue_single] at h'
    rw [← h', Matrix.zero_apply]
    exact hline _ _
  apply hanis p hp₀ hp
  rw [h, mul_assoc H.inv, mul_assoc H.inv, hzero, mul_zero]

theorem globalHermitianModel : GlobalHermitianModel.{u} := by
  intro k A K _ _ _ _ _ hA s n t c hs
  obtain ⟨_, _, torusOf⟩ := symplecticIsotropicIdempotentSplitTorus s c
  have hanis (p : A) : p ≠ 0 → p * p = p → antiValue t.anti p * p ≠ 0 := by
    intro hp₀ hp h
    obtain ⟨_, c', _, _, _, _, hc⟩ := torusOf p hp₀ hp h
    exact hs ⟨c', fun R => (hc R).1⟩
  obtain ⟨r, D, δ, α, hD, hr, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation k A hA
  let i : Fin r := ⟨0, hr⟩
  obtain ⟨f, σ, hf⟩ := involutoryDivisionCorner t e i hanis
  let a : Involution k (Matrix (Fin r) (Fin r) D) :=
    ⟨transportAnti f t.anti, fun X => by
      change f (antiValue t.anti (f.symm (f (antiValue t.anti (f.symm X))))) = X
      rw [f.symm_apply_apply, t.square, f.apply_symm_apply]⟩
  have ha (X : Matrix (Fin r) (Fin r) D) : antiValue a.anti X = f (antiValue t.anti (f.symm X)) :=
    rfl
  let : Nonempty (Fin r) := ⟨i⟩
  let : Algebra.IsCentral k D := hD.1
  let : FiniteDimensional k D := hD.2
  have hC : _root_.Specs.RM03.CSA.isCentralSimple k (Matrix (Fin r) (Fin r) D) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨H, hH⟩ := anti_gram hC a.anti (matrixAnti σ.anti)
  have h' (X : Matrix (Fin r) (Fin r) D) :
      antiValue a.anti X = H.inv * dagger σ.anti X * H.val := hH X
  have hd := cornerGramHermitian hC hD a σ i H h' hf
  have hanis' (p : Matrix (Fin r) (Fin r) D) (hp₀ : p ≠ 0) (hp : p * p = p) :
      antiValue a.anti p * p ≠ 0 := by
    intro hzero
    apply hanis (f.symm p)
    · intro hzero'
      apply hp₀
      simpa using congrArg f hzero'
    · rw [← map_mul, hp]
    · apply f.injective
      simpa [ha] using hzero
  refine ⟨r, D, δ, α, hD, ⟨
    ⟨i, f, σ, H, hf, hd, fun x => ?_, hermitianValue_laws σ.anti σ.square H.val hd,
      hermitianValue_nondegenerate σ.anti H, matrixFormAnisotropic a σ H hd h' hanis'⟩⟩⟩
  simpa only [ha, f.symm_apply_apply] using h' (f x)

theorem hermitianModelBaseChange : HermitianModelBaseChange.{u} := by
  intro k A D _ _ _ _ _ s r m
  let E (R : Type u) [CommRing R] [Algebra k R] :=
    (extendEquiv (R := R) m.equiv).trans (matrixBaseChange (Fin r))
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro R _ _ x
    exact matrixCoordinates_pure (F := k) (R := R) m.equiv x
  · intro R _ _
    let bR := extendAnti m.involution.anti R
    let HR := m.gram.val.map (intoTensor (F := k) R D)
    have hHR : dagger bR HR = HR := by
      ext i j
      change antiValue bR (1 ⊗ₜ[k] m.gram.val j i) = 1 ⊗ₜ[k] m.gram.val i j
      rw [extendAnti_tmul]
      congr 1
      exact congrArg (fun X : Matrix (Fin r) (Fin r) D => X i j) m.hermitian
    exact hermitianValue_laws bR (extendAnti_square m.involution.anti m.involution.square) HR hHR
  · intro R _ _ g
    exact quaternion_point_compare (F := k) (R := R) s.anti m.involution.anti m.gram m.equiv
      m.adjoint g
  · intro R S _ _ _ _ f x
    exact matrixBaseChange_natural f m.equiv x

end HermitianForm

section Coordinates

open private antiValue_add antiValue_zero antiValue_smul extendAnti_tmul
  from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

variable {k R C D I J : Type*} [Field k] [Field R] [Ring C] [Algebra R C]
  [Ring D] [Algebra k D] [Fintype I] [DecidableEq I] [Fintype J]

private def formLinear (s : AntiEquiv R C) (H : Matrix I I C) :
    (I → C) →ₗ[R] (I → C) →ₗ[R] C :=
  LinearMap.mk₂ R (hermitianValue s H)
    (fun x y z => by
      have h : (fun i => antiValue s ((x + y) i)) =
          (fun i => antiValue s (x i)) + (fun i => antiValue s (y i)) :=
        funext fun i => antiValue_add s (x i) (y i)
      simp only [hermitianValue, h, add_dotProduct])
    (fun a x y => by
      have h : (fun i => antiValue s ((a • x) i)) = a • (fun i => antiValue s (x i)) :=
        funext fun i => antiValue_smul s a (x i)
      simp only [hermitianValue, h, smul_dotProduct])
    (fun x y z => by simp only [hermitianValue, Matrix.mulVec_add, dotProduct_add])
    (fun a x y => by simp only [hermitianValue, Matrix.mulVec_smul, dotProduct_smul])

private theorem sum_column_basis (b : Module.Basis J R C) (x : I → C) :
    (∑ p : I × J, b.repr (x p.1) p.2 • Pi.single p.1 (b p.2)) = x := by
  funext i
  simp only [Fintype.sum_prod_type, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
    smul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hli
    simp [Ne.symm hli]
  · simp

private def diagonalPolynomials (c : (I × J) → (I × J) → J → k)
    (j : J) : MvPolynomial (I × J) k :=
  ∑ p, ∑ q, MvPolynomial.C (c q p j) * (MvPolynomial.X p * MvPolynomial.X q)

omit [DecidableEq I] in
private theorem diagonalPolynomials_homogeneous (c : (I × J) → (I × J) → J → k)
    (j : J) : (diagonalPolynomials c j).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro p _
  apply MvPolynomial.IsHomogeneous.sum
  intro q _
  exact ((MvPolynomial.isHomogeneous_X k p).mul (MvPolynomial.isHomogeneous_X k q)).C_mul _

private theorem diagonalPolynomials_eval (c : (I × J) → (I × J) → J → k)
    (a : k →+* R) (b : Module.Basis J R C) (h : (I → C) →ₗ[R] (I → C) →ₗ[R] C)
    (hc : ∀ (p q : I × J) j, a (c p q j) =
      b.repr (h (Pi.single p.1 (b p.2)) (Pi.single q.1 (b q.2))) j)
    (x : I → C) (j : J) :
    (diagonalPolynomials c j).eval₂ a (fun p => b.repr (x p.1) p.2) = b.repr (h x x) j := by
  let u (p : I × J) := b.repr (x p.1) p.2
  let basis (p : I × J) : I → C := Pi.single p.1 (b p.2)
  have hx : (∑ p, u p • basis p) = x := sum_column_basis b x
  conv_rhs => rw [← hx]
  simp only [diagonalPolynomials, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, hc, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [u, basis]
  ac_rfl

omit [DecidableEq I] in
private theorem form_pure [Algebra k R] (s : AntiEquiv k D) (H : Matrix I I D) (x y : I → D) :
    hermitianValue (extendAnti s R) (H.map (intoTensor R D))
        (fun i => (1 : R) ⊗ₜ[k] x i) (fun i => (1 : R) ⊗ₜ[k] y i) =
      (1 : R) ⊗ₜ[k] hermitianValue s H x y := by
  let f : D →+* (R ⊗[k] D) := (intoTensor R D).toRingHom
  have hf (a : D) : f a = (1 : R) ⊗ₜ[k] a := rfl
  change hermitianValue (extendAnti s R) (H.map f) (f ∘ x) (f ∘ y) = f (hermitianValue s H x y)
  simp only [hermitianValue, RingHom.map_dotProduct]
  have h (i : I) : antiValue (extendAnti s R) (f (x i)) = f (antiValue s (x i)) := by
    simp only [hf, extendAnti_tmul]
  have hy : f ∘ (H *ᵥ y) = H.map f *ᵥ (f ∘ y) := funext (RingHom.map_mulVec f H y)
  rw [hy]
  congr 1

omit [Fintype I] [DecidableEq I] [Fintype J] in
private theorem right_linear_of_basis (b : Module.Basis J R C)
    (f : (I → C) →ₗ[R] (I → C))
    (hf : ∀ j x, f (fun i => x i * b j) = fun i => f x i * b j)
    (a : C) (x : I → C) :
    f (fun i => x i * a) = fun i => f x i * a := by
  let right (x : I → C) : C →ₗ[R] (I → C) := LinearMap.pi fun i => LinearMap.mul R C (x i)
  have h : f.comp (right x) = right (f x) := by
    apply b.ext
    exact fun j => hf j x
  exact congrArg (fun l : C →ₗ[R] (I → C) => l a) h

private theorem right_linear_matrix (f : (I → C) →ₗ[R] (I → C))
    (hf : ∀ a x, f (fun i => x i * a) = fun i => f x i * a) :
    ∃ g : Matrix I I C, ∀ x, f x = g *ᵥ x := by
  refine ⟨Matrix.of (fun i j => f (Pi.single j 1) i), ?_⟩
  intro x
  have hx : (∑ j, Pi.single j (x j)) = x := Finset.univ_sum_single x
  have hs (j : I) : (fun i => (Pi.single j (1 : C) : I → C) i * x j) = Pi.single j (x j) := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  have hm (j : I) := hf (x j) (Pi.single j 1)
  simp_rw [hs] at hm
  conv_lhs => rw [← hx, map_sum]
  funext i
  simp only [Finset.sum_apply, hm, Matrix.mulVec, dotProduct, Matrix.of_apply]

omit [Fintype J] in
private theorem matrix_of_right_linear_equiv (b : Module.Basis J R C)
    (f : (I → C) ≃ₗ[R] (I → C)) (hf : ∀ j x, f (fun i => x i * b j) = fun i => f x i * b j) :
    ∃ g : (Matrix I I C)ˣ, ∀ x, f x = g.val *ᵥ x := by
  have h := right_linear_of_basis b f.toLinearMap hf
  have h' (a : C) (x : I → C) : f.symm (fun i => x i * a) = fun i => f.symm x i * a := by
    apply f.injective
    change f (f.symm (fun i => x i * a)) = f (fun i => f.symm x i * a)
    have hh := h a (f.symm x)
    change f (fun i => f.symm x i * a) = (fun i => f (f.symm x) i * a) at hh
    rw [f.apply_symm_apply, hh]
    simp
  obtain ⟨g, hg⟩ := right_linear_matrix f.toLinearMap h
  obtain ⟨g', hg'⟩ := right_linear_matrix f.symm.toLinearMap h'
  have hgg (x : I → C) : (g * g') *ᵥ x = 1 *ᵥ x := by
    rw [← Matrix.mulVec_mulVec, ← hg', ← hg]
    simp
  have hgg' (x : I → C) : (g' * g) *ᵥ x = 1 *ᵥ x := by
    rw [← Matrix.mulVec_mulVec, ← hg, ← hg']
    simp
  refine ⟨⟨g, g', ?_, ?_⟩, hg⟩ <;> ext i j
  · simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (hgg (Pi.single j 1)) i
  · simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (hgg' (Pi.single j 1)) i

theorem diagonalCoordinatesAndStabilizer : DiagonalCoordinatesAndStabilizer.{u,v,w} := by
  classical
  intro k D I J _ _ _ _ _ _ _ σ H b hanis
  let h := formLinear σ.anti H.val
  let c (p q : I × J) (j : J) :=
    b.repr (h (Pi.single p.1 (b p.2)) (Pi.single q.1 (b q.2))) j
  refine ⟨diagonalPolynomials c, diagonalPolynomials_homogeneous c, ?_, ?_⟩
  · intro x hx
    let y (i : I) := b.equivFun.symm (fun j => x (i, j))
    have hy (p : I × J) : b.repr (y p.1) p.2 = x p := by
      change b.equivFun (b.equivFun.symm (fun j => x (p.1, j))) p.2 = _
      rw [LinearEquiv.apply_symm_apply]
    have hy₀ : y ≠ 0 := by
      intro hz
      apply hx
      funext p
      simp [← hy, hz]
    have hz : h y y ≠ 0 := hanis y hy₀
    obtain ⟨j, hj⟩ : ∃ j, b.repr (h y y) j ≠ 0 := by
      by_contra! hh
      exact hz (b.repr.injective (Finsupp.ext fun j => by simpa only [map_zero, Finsupp.zero_apply] using hh j))
    refine ⟨j, ?_⟩
    have he := diagonalPolynomials_eval c (RingHom.id k) b h (fun _ _ _ => rfl) y j
    have hev := he.trans_ne hj
    simpa only [hy, MvPolynomial.eval₂_id] using hev
  · intro R _ _ bR hR coords
    let hL := formLinear (extendAnti σ.anti R) (H.val.map (intoTensor R D))
    change (∀ x j, (diagonalPolynomials c j).eval₂ (algebraMap k R) (coords x) =
      bR.repr (hL x x) j) ∧ _
    have hbase (p : I × J) :
        (Pi.single p.1 (bR p.2) : I → R ⊗[k] D) =
          fun i => (1 : R) ⊗ₜ[k] (Pi.single p.1 (b p.2) : I → D) i := by
      funext i
      change (Pi.single p.1 ((b.baseChange R) p.2) : I → R ⊗[k] D) i = _
      by_cases hi : i = p.1 <;> simp [hi]
    have hc (p q : I × J) (j : J) : algebraMap k R (c p q j) =
        bR.repr (hL (Pi.single p.1 (bR p.2)) (Pi.single q.1 (bR q.2))) j := by
      rw [hbase p, hbase q]
      change _ = (b.baseChange R).repr
        (hermitianValue (extendAnti σ.anti R) (H.val.map (intoTensor R D)) _ _) j
      rw [form_pure, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
      rfl
    refine ⟨fun x j => diagonalPolynomials_eval c (algebraMap k R) bR hL hc x j, ?_⟩
    intro f
    constructor
    · rintro ⟨hcomm, hform⟩
      obtain ⟨g, hg⟩ := matrix_of_right_linear_equiv bR f hcomm
      exact ⟨g, hg, fun x y => by rw [← hg, ← hg]; exact hform x y⟩
    · rintro ⟨g, hg, hform⟩
      refine ⟨?_, fun x y => by rw [hg, hg]; exact hform x y⟩
      intro j x
      funext i
      simp only [hg, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

end Coordinates

section Determinant

open private matrixBaseChange matrixBaseChange_tmul extendEquiv extendEquiv_tmul matrix_card_eq
  from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
open private splitComparisonBaseChange
  from LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels

private theorem columnAction_baseChange {R L C I : Type*} [Field R] [Field L]
    [Algebra R L] [Ring C] [Algebra R C] [FiniteDimensional R C] [Fintype I] [DecidableEq I]
    (X : Matrix I I C) :
    LinearMap.det (columnAction (R := L) (X.map (intoTensor (F := R) L C))) =
      algebraMap R L (LinearMap.det (columnAction (R := R) X)) := by
  let f := columnAction (R := R) X
  let E := TensorProduct.piRight R L L (fun _ : I => C)
  let G := columnAction (R := L) (X.map (intoTensor (F := R) L C))
  have h (z : L ⊗[R] (I → C)) : E (f.baseChange L z) = G (E z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      funext i
      change a ⊗ₜ[R] (X *ᵥ x) i =
        ((X.map (intoTensor (F := R) L C)) *ᵥ (fun j => a ⊗ₜ[R] x j)) i
      simp only [Matrix.mulVec, dotProduct, TensorProduct.tmul_sum, Matrix.map_apply]
      apply Finset.sum_congr rfl
      intro j _
      change a ⊗ₜ[R] (X i j * x j) = ((1 : L) ⊗ₜ[R] X i j) * (a ⊗ₜ[R] x j)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hh : E.toLinearMap ∘ₗ f.baseChange L ∘ₗ E.symm.toLinearMap = G := by
    apply LinearMap.ext
    intro x
    exact (h (E.symm x)).trans (congrArg G (E.apply_symm_apply x))
  change G.det = algebraMap R L f.det
  rw [← hh, LinearMap.det_conj, LinearMap.det_baseChange]

private def splitColumnCoordinates {L C I J : Type*} [Field L] [Ring C] [Algebra L C]
    [Fintype J] [DecidableEq J] (e : C ≃ₐ[L] Matrix J J L) :
    (I → C) ≃ₗ[L] (J → (I × J → L)) where
  toFun x j p := e (x p.1) p.2 j
  invFun y i := e.symm (Matrix.of (fun a j => y j (i, a)))
  left_inv x := by
    funext i
    exact e.symm_apply_apply (x i)
  right_inv y := by
    funext j p
    exact congrArg (fun M : Matrix J J L => M p.2 j)
      (e.apply_symm_apply (Matrix.of (fun a l => y l (p.1, a))))
  map_add' x y := by
    funext j p
    simp [map_add]
  map_smul' a x := by
    funext j p
    simp [Matrix.smul_apply]

private theorem splitColumnDeterminant {L C I J : Type*} [Field L] [Ring C] [Algebra L C]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : C ≃ₐ[L] Matrix J J L) (X : Matrix I I C) :
    LinearMap.det (columnAction (R := L) X) =
      (Matrix.compAlgEquiv I J L L (e.mapMatrix X)).det ^ Fintype.card J := by
  let t := splitColumnCoordinates (I := I) e
  let Y := Matrix.compAlgEquiv I J L L (e.mapMatrix X)
  let f := columnAction (R := L) X
  have h (x : I → C) (j : J) : t (f x) j = Y *ᵥ (t x j) := by
    funext p
    change e ((X *ᵥ x) p.1) p.2 j =
      ∑ q : I × J, e (X p.1 q.1) p.2 q.2 * e (x q.1) q.2 j
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.sum_apply,
      Matrix.mul_apply, Fintype.sum_prod_type]
  have hh : t.toLinearMap ∘ₗ f ∘ₗ t.symm.toLinearMap =
      LinearMap.pi (fun j : J => Y.mulVecLin ∘ₗ LinearMap.proj j) := by
    apply LinearMap.ext
    intro x
    funext j
    change t (f (t.symm x)) j = Y *ᵥ x j
    rw [h, t.apply_symm_apply]
  rw [← LinearMap.det_conj f t, hh, LinearMap.det_pi]
  simp [Y, ← Matrix.toLin'_apply', LinearMap.det_toLin']

private theorem matrixAlgEquiv_det {L I J : Type*} [Field L] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Nonempty I]
    (f : Matrix I I L ≃ₐ[L] Matrix J J L) (X : Matrix I I L) : (f X).det = X.det := by
  let re := Matrix.reindexAlgEquiv L L (Fintype.equivOfCardEq (matrix_card_eq f.toLinearEquiv))
  let a := f.trans re.symm
  have hC : RM03.CSA.IsCentralSimple L (Matrix I I L) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨U, hU⟩ := RM03.CSA.algEquiv_isInner hC a
  have h : (a X).det = X.det := by
    rw [hU, Matrix.det_mul, Matrix.det_mul, mul_comm U.val.det X.det, mul_assoc, ← Matrix.det_mul,
      U.mul_inv, Matrix.det_one, mul_one]
  calc
    (f X).det = (re (a X)).det := by simp [a]
    _ = (a X).det := Matrix.det_reindexAlgEquiv L L _ (a X)
    _ = X.det := h

private theorem symplecticImage_det {k A L : Type u} [Field k] [Ring A] [Algebra k A]
    [Field L] [Algebra k L] (s : SymplecticIsometryDescent.Involution k A) {n : ℕ}
    (c : SplitComparison (toDivisionInvolution s) L n)
    (g : A) (hg : s.toLinearMap g * g = 1) : (c.equiv (1 ⊗ₜ[k] g)).det = 1 := by
  let M := c.equiv ((1 : L) ⊗ₜ[k] g)
  let J := Matrix.J (Fin n) L
  have h : (-J) * M.transpose * J * M = 1 := by
    have he := c.adjoint g
    change c.equiv ((1 : L) ⊗ₜ[k] s.toLinearMap g) = (-J) * M.transpose * J at he
    rw [← he, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hg,
      ← Algebra.TensorProduct.one_def, map_one]
  have hJ : J * -J = 1 := by simp [J, Matrix.J_squared]
  have hm : M.transpose * J * M = J := by
    have ht := congrArg (fun X => J * X) h
    simpa only [← mul_assoc, hJ, one_mul, mul_one] using ht
  apply SymplecticGroup.det_eq_one
  apply SymplecticGroup.transpose_mem_iff.mp
  exact SymplecticGroup.mem_iff.mpr (by simpa only [Matrix.transpose_transpose] using hm)

theorem symplecticColumnDeterminant : SymplecticColumnDeterminant.{u} := by
  classical
  intro k A D K _ _ _ _ _ _ _ _ hD s n r c R _ _ e g
  let L := AlgebraicClosure R
  let C := R ⊗[k] D
  have hC : RM03.CSA.IsCentralSimple R C :=
    RM03.CSA.isCentralSimple_baseChange (L := R) (RM03.CSA.isCentralSimple_of_isCentralDivision k D hD)
  let : FiniteDimensional R C := hC.2.2
  obtain ⟨d⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hC
  let I := Fin r
  let J := Fin (_root_.Specs.RM03.CSA.degree R C)
  let c' := splitComparisonBaseChange (F := R) s c
  let E : (L ⊗[R] (R ⊗[k] A)) ≃ₐ[L] Matrix (I × J) (I × J) L :=
    (extendEquiv e).trans
      ((matrixBaseChange I).trans (d.mapMatrix.trans (Matrix.compAlgEquiv I J L L)))
  have hE : E ((1 : L) ⊗ₜ[R] g.val.val) =
      Matrix.compAlgEquiv I J L L (d.mapMatrix ((e g.val.val).map (intoTensor L C))) := by
    simp only [E, AlgEquiv.trans_apply, extendEquiv_tmul, matrixBaseChange_tmul]
    rfl
  have detE : (E ((1 : L) ⊗ₜ[R] g.val.val)).det = 1 := by
    have hc := symplecticImage_det (s.baseChange R) c' g.val.val g.property
    by_cases hI : Nonempty (I × J)
    · let := hI
      have he := matrixAlgEquiv_det (E.symm.trans c'.equiv) (E ((1 : L) ⊗ₜ[R] g.val.val))
      rw [AlgEquiv.trans_apply, E.symm_apply_apply, hc] at he
      exact he.symm
    · let : IsEmpty (I × J) := not_nonempty_iff.mp hI
      exact Matrix.det_isEmpty
  apply (algebraMap R L).injective
  rw [← columnAction_baseChange (L := L), map_one]
  calc
    _ = (Matrix.compAlgEquiv I J L L
        (d.mapMatrix ((e g.val.val).map (intoTensor L C)))).det ^ Fintype.card J :=
      splitColumnDeterminant d _
    _ = 1 := by rw [← hE, detE, one_pow]

end Determinant

open private extendAnti_involution
  from LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels

theorem symplecticTensorModel : SymplecticTensorModel.{u} := by
  intro k A D K J _ _ _ _ _ _ _ _ _ _ hD s n r t c m b
  obtain ⟨P, hP, hanis, hdiag⟩ :=
    diagonalCoordinatesAndStabilizer.{u,0,u} (I := Fin r) (J := J) m.involution m.gram b m.anisotropic
  obtain ⟨E, hpure, _, hForm, hnatural⟩ := hermitianModelBaseChange m
  refine ⟨P, E, hP, hanis, hpure, hnatural, ?_⟩
  intro R _ _ bR h coords
  obtain ⟨hEval, hMatrix⟩ := hdiag R
  have hiso (g : (R ⊗[k] A)ˣ) :
      g ∈ (s.baseChange R).isometries ↔
        ∀ x y, h (E R g.val *ᵥ x) (E R g.val *ᵥ y) = h x y := by
    rw [(s.baseChange R).mem_isometries]
    have hf := hForm R g
    change antiValue (extendAnti (toDivisionInvolution s).anti R) g.val * g.val = 1 ↔ _ at hf
    rwa [extendAnti_involution] at hf
  refine ⟨hEval, ?_, ?_⟩
  · intro g M
    refine ⟨symplecticColumnDeterminant hD s c R (E R) g, ?_⟩
    intro x j
    rw [hEval, hEval]
    exact congrArg (fun z => bR.repr z j) ((hiso g.val).mp g.property x x)
  · intro f
    rw [hMatrix]
    constructor
    · rintro ⟨g, hg, hform⟩
      let g' : (R ⊗[k] A)ˣ := Units.map (E R).symm.toMonoidHom g
      have he : E R g'.val = g.val := (E R).apply_symm_apply g.val
      have hh : g' ∈ (s.baseChange R).isometries := by
        apply (hiso g').mpr
        rw [he]
        exact hform
      exact ⟨⟨g', hh⟩, fun x => by rw [he]; exact hg x⟩
    · rintro ⟨g, hg⟩
      exact ⟨Units.map (E R).toMonoidHom g.val, hg, (hiso g.val).mp g.property⟩

end

end LinearAlgebraicGroups.Arithmetic.AnisotropicSymplecticInvolutionTensors
