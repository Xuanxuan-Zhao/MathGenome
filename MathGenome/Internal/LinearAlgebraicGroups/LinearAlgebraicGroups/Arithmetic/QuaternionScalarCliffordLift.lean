import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuaternionScalarCliffordLift
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinScaleCover
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SymplecticDatumRankOneAndPinning
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OddSpinModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Degree
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

open AlgebraicGeometry
open scoped Matrix TensorProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.QuaternionScalarCliffordLift

open CliffordAlgebra Matrix

noncomputable section

section CliffordPlane

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  (q : QuadraticForm R V)

/-- Four isotropic Clifford vectors coming from a hyperbolic plane of rank two.
The last two vectors are the polar duals of the first two in the same order. -/
structure HyperbolicFrame where
  x : V
  y : V
  u : V
  v : V
  qx : q x = 0
  qy : q y = 0
  qu : q u = 0
  qv : q v = 0
  xy : QuadraticMap.polar q x y = 0
  uv : QuadraticMap.polar q u v = 0
  xu : QuadraticMap.polar q x u = 1
  yv : QuadraticMap.polar q y v = 1
  xv : QuadraticMap.polar q x v = 0
  yu : QuadraticMap.polar q y u = 0

namespace HyperbolicFrame

variable {q} (h : HyperbolicFrame q)

def creation : CliffordAlgebra q := ι q h.x * ι q h.y

def contraction : CliffordAlgebra q := ι q h.v * ι q h.u

private theorem ι_sq_zero {a : V} (ha : q a = 0) : ι q a * ι q a = 0 := by
  rw [ι_sq_scalar, ha, map_zero]

private theorem ι_swap_of_polar_zero {a b : V} (hab : QuadraticMap.polar q a b = 0) :
    ι q b * ι q a = -(ι q a * ι q b) := by
  apply eq_neg_of_add_eq_zero_left
  rw [add_comm, ι_mul_ι_add_swap, hab, map_zero]

private theorem ι_swap_of_polar_one {a b : V} (hab : QuadraticMap.polar q a b = 1) :
    ι q b * ι q a = 1 - ι q a * ι q b := by
  apply eq_sub_of_add_eq
  rw [add_comm, ι_mul_ι_add_swap, hab, map_one]

private theorem nilpotent_product {A : Type*} [Ring A] {x y : A}
    (hx : x * x = 0) (hyx : y * x = -(x * y)) : (x * y) * (x * y) = 0 := by
  calc
    (x * y) * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
    _ = 0 := by rw [hyx, mul_neg, ← mul_assoc x x, hx, zero_mul, neg_zero, zero_mul]

theorem creation_sq : h.creation * h.creation = 0 :=
  nilpotent_product (ι_sq_zero h.qx) (ι_swap_of_polar_zero h.xy)

theorem contraction_sq : h.contraction * h.contraction = 0 :=
  nilpotent_product (ι_sq_zero h.qv) (ι_swap_of_polar_zero
    ((QuadraticMap.polar_comm q h.v h.u).trans h.uv))

private theorem sandwich {A : Type*} [Ring A] {x y u v : A}
    (hx : x * x = 0) (hy : y * y = 0)
    (hyx : y * x = -(x * y)) (hvx : v * x = -(x * v))
    (hux : u * x = 1 - x * u) (hyv : y * v = 1 - v * y) :
    (x * y) * (v * u) * (x * y) = x * y := by
  have hcomm : (y * v) * x = x * (y * v) := by
    calc
      (y * v) * x = y * (v * x) := mul_assoc ..
      _ = x * (y * v) := by rw [hvx, mul_neg, ← mul_assoc, hyx, neg_mul, neg_neg, mul_assoc]
  have hyvy : (y * v) * y = y := by rw [hyv, sub_mul, one_mul, mul_assoc, hy, mul_zero, sub_zero]
  calc
    (x * y) * (v * u) * (x * y) = x * (y * v) * (u * x) * y := by simp only [mul_assoc]
    _ = x * ((y * v) * y) - x * ((y * v) * x) * u * y := by
      rw [hux]
      noncomm_ring
    _ = x * y := by rw [hyvy, hcomm, ← mul_assoc x x, hx]; simp

theorem creation_contraction_creation :
    h.creation * h.contraction * h.creation = h.creation :=
  sandwich (ι_sq_zero h.qx) (ι_sq_zero h.qy)
    (ι_swap_of_polar_zero h.xy) (ι_swap_of_polar_zero h.xv)
    (ι_swap_of_polar_one h.xu)
    (ι_swap_of_polar_one ((QuadraticMap.polar_comm q h.v h.y).trans h.yv))

theorem contraction_creation_contraction :
    h.contraction * h.creation * h.contraction = h.contraction :=
  sandwich (ι_sq_zero h.qv) (ι_sq_zero h.qu)
    (ι_swap_of_polar_zero ((QuadraticMap.polar_comm q h.v h.u).trans h.uv))
    (ι_swap_of_polar_zero ((QuadraticMap.polar_comm q h.v h.x).trans h.xv))
    (ι_swap_of_polar_one ((QuadraticMap.polar_comm q h.v h.y).trans h.yv))
    (ι_swap_of_polar_one h.xu)

/-- The determinant-one matrix acts in the corner generated by the two Clifford
products and by the identity on the complementary idempotent. -/
def matrixAction (A : Matrix (Fin 2) (Fin 2) R) : CliffordAlgebra q :=
  1 + (A 0 0 - 1) • (h.creation * h.contraction)
    + A 0 1 • h.creation + A 1 0 • h.contraction
    + (A 1 1 - 1) • (h.contraction * h.creation)

theorem matrixAction_one : h.matrixAction 1 = 1 := by
  simp [matrixAction]

private theorem cornerProduct (A B : Matrix (Fin 2) (Fin 2) R) :
    h.matrixAction (A * B) = h.matrixAction A * h.matrixAction B := by
  let E := h.creation
  let L := h.contraction
  let P := E * L
  let Q := L * E
  have ee : E * E = 0 := h.creation_sq
  have ll : L * L = 0 := h.contraction_sq
  have pe : P * E = E := h.creation_contraction_creation
  have ql : Q * L = L := h.contraction_creation_contraction
  have pp : P * P = P := by change (E * L) * (E * L) = _; rw [← mul_assoc, show E * L * E = E from pe]
  have qq : Q * Q = Q := by change (L * E) * (L * E) = _; rw [← mul_assoc, show L * E * L = L from ql]
  have pq : P * Q = 0 := by change (E * L) * (L * E) = _; rw [mul_assoc, ← mul_assoc L, ll, zero_mul, mul_zero]
  have qp : Q * P = 0 := by change (L * E) * (E * L) = _; rw [mul_assoc, ← mul_assoc E, ee, zero_mul, mul_zero]
  have ep : E * P = 0 := by change E * (E * L) = _; rw [← mul_assoc, ee, zero_mul]
  have pl : P * L = 0 := by change (E * L) * L = _; rw [mul_assoc, ll, mul_zero]
  have eq : E * Q = E := by change E * (L * E) = _; rw [← mul_assoc]; exact pe
  have qe : Q * E = 0 := by change (L * E) * E = _; rw [mul_assoc, ee, mul_zero]
  have lp : L * P = L := by change L * (E * L) = _; rw [← mul_assoc]; exact ql
  have lq : L * Q = 0 := by change L * (L * E) = _; rw [← mul_assoc, ll, zero_mul]
  change 1 + ((A * B) 0 0 - 1) • P + (A * B) 0 1 • E + (A * B) 1 0 • L +
      ((A * B) 1 1 - 1) • Q =
    (1 + (A 0 0 - 1) • P + A 0 1 • E + A 1 0 • L + (A 1 1 - 1) • Q) *
      (1 + (B 0 0 - 1) • P + B 0 1 • E + B 1 0 • L + (B 1 1 - 1) • Q)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, ee, ll, pp, qq, pq, qp, pe, pl, ep, eq, qe, ql, lp, lq,
    show E * L = P from rfl, show L * E = Q from rfl, smul_zero, add_zero]
  module

/-- The all-ring Clifford formula, with inverse induced by the inverse matrix. -/
def matrixUnitsAction : Matrix.SpecialLinearGroup (Fin 2) R →* (CliffordAlgebra q)ˣ where
  toFun A :=
    { val := h.matrixAction A.val
      inv := h.matrixAction (A⁻¹).val
      val_inv := by rw [← h.cornerProduct]; exact congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) R =>
        h.matrixAction g.val) (mul_inv_cancel A) |>.trans h.matrixAction_one
      inv_val := by rw [← h.cornerProduct]; exact congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) R =>
        h.matrixAction g.val) (inv_mul_cancel A) |>.trans h.matrixAction_one }
  map_one' := Units.ext h.matrixAction_one
  map_mul' A B := Units.ext (h.cornerProduct A.val B.val)

theorem matrixAction_even (A : Matrix (Fin 2) (Fin 2) R) :
    h.matrixAction A ∈ evenOdd q 0 := by
  have he : h.creation ∈ evenOdd q 0 := ι_mul_ι_mem_evenOdd_zero q _ _
  have hl : h.contraction ∈ evenOdd q 0 := ι_mul_ι_mem_evenOdd_zero q _ _
  have hm {x y : CliffordAlgebra q} (hx : x ∈ evenOdd q 0) (hy : y ∈ evenOdd q 0) :
      x * y ∈ evenOdd q 0 := by simpa using SetLike.mul_mem_graded hx hy
  exact (evenOdd q 0).add_mem
    ((evenOdd q 0).add_mem
      ((evenOdd q 0).add_mem
        ((evenOdd q 0).add_mem (SetLike.one_mem_graded _)
          ((evenOdd q 0).smul_mem _ (hm he hl)))
        ((evenOdd q 0).smul_mem _ he))
      ((evenOdd q 0).smul_mem _ hl))
    ((evenOdd q 0).smul_mem _ (hm hl he))

theorem matrixAction_reverse (A : Matrix (Fin 2) (Fin 2) R) :
    reverse (h.matrixAction A) = h.matrixAction (Matrix.adjugate A) := by
  have he : reverse h.creation = -h.creation := by
    rw [creation, reverse.map_mul, reverse_ι, reverse_ι, ι_swap_of_polar_zero h.xy]
  have hl : reverse h.contraction = -h.contraction := by
    rw [contraction, reverse.map_mul, reverse_ι, reverse_ι,
      ι_swap_of_polar_zero ((QuadraticMap.polar_comm q h.v h.u).trans h.uv)]
  simp [matrixAction, reverse.map_mul, he, hl, Matrix.adjugate_fin_two]
  abel

theorem matrixAction_norm (A : Matrix.SpecialLinearGroup (Fin 2) R) :
    reverse (h.matrixAction A.val) * h.matrixAction A.val = 1 := by
  rw [matrixAction_reverse, ← Matrix.SpecialLinearGroup.coe_inv, ← h.cornerProduct]
  exact ((congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) R => h.matrixAction g.val)
    (inv_mul_cancel A))).trans h.matrixAction_one

theorem matrixAction_upper (t : R) :
    (h.matrixUnitsAction
      (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t)).val =
      1 + t • h.creation := by
  change h.matrixAction (Matrix.transvection 0 1 t) = _
  simp [matrixAction, Matrix.transvection]

theorem matrixAction_lower (t : R) :
    (h.matrixUnitsAction
      (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t)).val =
      1 + t • h.contraction := by
  change h.matrixAction (Matrix.transvection 1 0 t) = _
  simp [matrixAction, Matrix.transvection]

theorem matrixAction_diagonal (t : Rˣ) :
    (h.matrixUnitsAction (Specs.Arithmetic.QuaternionScalarCliffordLift.scalarDiagonal t)).val =
      1 + ((t : R) - 1) • (h.creation * h.contraction)
        + ((↑t⁻¹ : R) - 1) • (h.contraction * h.creation) := by
  simp [matrixUnitsAction, matrixAction, Specs.Arithmetic.QuaternionScalarCliffordLift.scalarDiagonal]

private theorem mul_cliffordVector (a b z : V) :
    (ι q a * ι q b) * ι q z =
      ι q z * (ι q a * ι q b) +
        QuadraticMap.polar q b z • ι q a - QuadraticMap.polar q a z • ι q b := by
  have swap (w : V) : ι q w * ι q z =
      algebraMap R (CliffordAlgebra q) (QuadraticMap.polar q w z) - ι q z * ι q w :=
    ι_mul_ι_comm w z
  calc
    _ = ι q a * (ι q b * ι q z) := mul_assoc ..
    _ = _ := by
      rw [swap b, mul_sub, ← mul_assoc, swap a, sub_mul, mul_assoc (ι q z),
        Algebra.smul_def, Algebra.smul_def, ← Algebra.commutes (QuadraticMap.polar q b z) (ι q a)]
      abel

private theorem mul_vector_first {C : Type*} [Ring C] [Algebra R C]
    (E L X Y : C) (a b c d : R) (hdet : a * d - b * c = 1)
    (hEX : E * X = 0) (hXE : X * E = 0) (_hLY : L * Y = 0) (hYL : Y * L = 0)
    (hLX : L * X = X * L + Y) (hEY : E * Y = Y * E + X) :
    let M := 1 + (a - 1) • (E * L) + b • E + c • L + (d - 1) • (L * E)
    M * X = (a • X + c • Y) * M := by
  have hPX : (E * L) * X = Y * E + X := by
    rw [mul_assoc, hLX, mul_add, ← mul_assoc, hEX, zero_mul, zero_add, hEY]
  have hQX : (L * E) * X = 0 := by rw [mul_assoc, hEX, mul_zero]
  have hXP : X * (E * L) = 0 := by rw [← mul_assoc, hXE, zero_mul]
  have hXQ : X * (L * E) = -(Y * E) := by
    rw [← mul_assoc, show X * L = L * X - Y by rw [hLX, add_sub_cancel_right],
      sub_mul, mul_assoc L, hXE, mul_zero, zero_sub]
  have hYP : Y * (E * L) = -(X * L) := by
    rw [← mul_assoc, show Y * E = E * Y - X by rw [hEY, add_sub_cancel_right],
      sub_mul, mul_assoc E, hYL, mul_zero, zero_sub]
  have hYQ : Y * (L * E) = 0 := by rw [← mul_assoc, hYL, zero_mul]
  have hd : c * b - a * (d - 1) = a - 1 := by linear_combination -hdet
  intro M
  dsimp [M]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    hEX, hXE, hYL, hLX, hPX, hQX, hXP, hXQ, hYP, hYQ, smul_zero, add_zero]
  simp only [smul_add, smul_smul, smul_neg]
  calc
    _ = a • X + c • Y + c • (X * L) + (a - 1) • (Y * E) := by module
    _ = a • X + c • Y + c • (X * L) + (c * b - a * (d - 1)) • (Y * E) := by rw [hd]
    _ = _ := by module

private theorem mul_vector_second {C : Type*} [Ring C] [Algebra R C]
    (E L X Y : C) (a b c d : R) (hdet : a * d - b * c = 1)
    (hEX : E * X = 0) (hXE : X * E = 0) (hLY : L * Y = 0) (hYL : Y * L = 0)
    (hLX : L * X = X * L + Y) (hEY : E * Y = Y * E + X) :
    let M := 1 + (a - 1) • (E * L) + b • E + c • L + (d - 1) • (L * E)
    M * Y = (b • X + d • Y) * M := by
  have hdet' : d * a - c * b = 1 := by simpa only [mul_comm] using hdet
  have he := mul_vector_first L E Y X d c b a hdet' hLY hYL hEX hXE hEY hLX
  have hm : 1 + (d - 1) • (L * E) + c • L + b • E + (a - 1) • (E * L) =
      1 + (a - 1) • (E * L) + b • E + c • L + (d - 1) • (L * E) := by abel
  dsimp only at he ⊢
  rw [hm, add_comm (d • Y)] at he
  exact he

private theorem creation_mul_left_zero : h.creation * ι q h.x = 0 := by
  rw [creation, mul_assoc, ι_swap_of_polar_zero h.xy, mul_neg, ← mul_assoc,
    ι_sq_zero h.qx, zero_mul, neg_zero]

private theorem creation_mul_right_zero : h.creation * ι q h.y = 0 := by
  rw [creation, mul_assoc, ι_sq_zero h.qy, mul_zero]

private theorem left_mul_creation_zero : ι q h.x * h.creation = 0 := by
  rw [creation, ← mul_assoc, ι_sq_zero h.qx, zero_mul]

private theorem right_mul_creation_zero : ι q h.y * h.creation = 0 := by
  rw [creation, ← mul_assoc, ι_swap_of_polar_zero h.xy, neg_mul, mul_assoc,
    ι_sq_zero h.qy, mul_zero, neg_zero]

private theorem contraction_mul_left_zero : h.contraction * ι q h.v = 0 := by
  rw [contraction, mul_assoc,
    ι_swap_of_polar_zero ((QuadraticMap.polar_comm q h.v h.u).trans h.uv),
    mul_neg, ← mul_assoc, ι_sq_zero h.qv, zero_mul, neg_zero]

private theorem contraction_mul_right_zero : h.contraction * ι q h.u = 0 := by
  rw [contraction, mul_assoc, ι_sq_zero h.qu, mul_zero]

private theorem left_mul_contraction_zero : ι q h.v * h.contraction = 0 := by
  rw [contraction, ← mul_assoc, ι_sq_zero h.qv, zero_mul]

private theorem right_mul_contraction_zero : ι q h.u * h.contraction = 0 := by
  rw [contraction, ← mul_assoc,
    ι_swap_of_polar_zero ((QuadraticMap.polar_comm q h.v h.u).trans h.uv), neg_mul,
    mul_assoc, ι_sq_zero h.qu, mul_zero, neg_zero]

private theorem contraction_mul_x :
    h.contraction * ι q h.x = ι q h.x * h.contraction + ι q h.v := by
  simpa [contraction, QuadraticMap.polar_comm q h.u h.x, QuadraticMap.polar_comm q h.v h.x,
    h.xu, h.xv] using mul_cliffordVector (q := q) h.v h.u h.x

private theorem creation_mul_v :
    h.creation * ι q h.v = ι q h.v * h.creation + ι q h.x := by
  simpa [creation, h.yv, h.xv] using mul_cliffordVector (q := q) h.x h.y h.v

private theorem contraction_mul_y :
    h.contraction * ι q h.y = ι q h.y * h.contraction + -ι q h.u := by
  simpa [contraction, QuadraticMap.polar_comm q h.u h.y, QuadraticMap.polar_comm q h.v h.y,
    h.yu, h.yv, sub_eq_add_neg] using mul_cliffordVector (q := q) h.v h.u h.y

private theorem creation_mul_neg_u :
    h.creation * (-ι q h.u) = (-ι q h.u) * h.creation + ι q h.y := by
  rw [mul_neg, neg_mul]
  have he := mul_cliffordVector (q := q) h.x h.y h.u
  change h.creation * ι q h.u = ι q h.u * h.creation + _ - _ at he
  rw [h.yu, h.xu, zero_smul, one_smul, add_zero] at he
  rw [he, neg_sub, sub_eq_neg_add]

/-- The vector action in the two ordered pairs of coordinates
`(x,v)` and `(y,-u)`. Both pairs carry the defining rank-two action. -/
theorem matrixAction_intertwine_frame (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    let A := h.matrixAction g.val
    (A * ι q h.x = ι q (g.val 0 0 • h.x + g.val 1 0 • h.v) * A) ∧
    (A * ι q h.v = ι q (g.val 0 1 • h.x + g.val 1 1 • h.v) * A) ∧
    (A * ι q h.y = ι q (g.val 0 0 • h.y - g.val 1 0 • h.u) * A) ∧
    (A * ι q h.u = ι q (-(g.val 0 1 • h.y) + g.val 1 1 • h.u) * A) := by
  have hdet := g.property
  rw [Matrix.det_fin_two] at hdet
  have hx := mul_vector_first h.creation h.contraction (ι q h.x) (ι q h.v) _ _ _ _ hdet
    h.creation_mul_left_zero h.left_mul_creation_zero h.contraction_mul_left_zero
    h.left_mul_contraction_zero h.contraction_mul_x h.creation_mul_v
  have hv := mul_vector_second h.creation h.contraction (ι q h.x) (ι q h.v) _ _ _ _ hdet
    h.creation_mul_left_zero h.left_mul_creation_zero h.contraction_mul_left_zero
    h.left_mul_contraction_zero h.contraction_mul_x h.creation_mul_v
  have hy := mul_vector_first h.creation h.contraction (ι q h.y) (-ι q h.u) _ _ _ _ hdet
    h.creation_mul_right_zero h.right_mul_creation_zero (by simp [h.contraction_mul_right_zero])
    (by simp [h.right_mul_contraction_zero]) h.contraction_mul_y h.creation_mul_neg_u
  have hu := mul_vector_second h.creation h.contraction (ι q h.y) (-ι q h.u) _ _ _ _ hdet
    h.creation_mul_right_zero h.right_mul_creation_zero (by simp [h.contraction_mul_right_zero])
    (by simp [h.right_mul_contraction_zero]) h.contraction_mul_y h.creation_mul_neg_u
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [matrixAction, map_add, map_smul] using hx
  · simpa only [matrixAction, map_add, map_smul] using hv
  · simpa only [matrixAction, map_sub, map_add, map_neg, map_smul, smul_neg, sub_eq_add_neg] using hy
  · have hn := congrArg Neg.neg hu
    simpa only [matrixAction, map_add, map_neg, map_smul, smul_neg, mul_neg, neg_neg,
      ← neg_mul, neg_add] using hn

/-- The lifted Clifford action fixes every vector polar-orthogonal to the frame. -/
theorem matrixAction_commute_of_orthogonal (A : Matrix (Fin 2) (Fin 2) R) (z : V)
    (hx : QuadraticMap.polar q h.x z = 0) (hy : QuadraticMap.polar q h.y z = 0)
    (hu : QuadraticMap.polar q h.u z = 0) (hv : QuadraticMap.polar q h.v z = 0) :
    Commute (h.matrixAction A) (ι q z) := by
  have he : Commute h.creation (ι q z) := by
    simpa [Commute, SemiconjBy, creation, hx, hy] using mul_cliffordVector (q := q) h.x h.y z
  have hl : Commute h.contraction (ι q z) := by
    simpa [Commute, SemiconjBy, contraction, hu, hv] using mul_cliffordVector (q := q) h.v h.u z
  exact (((((Commute.one_left _).add_left ((he.mul_left hl).smul_left _)).add_left
    (he.smul_left _)).add_left (hl.smul_left _)).add_left ((hl.mul_left he).smul_left _))

/-- The frame component of a vector, recovered from its polar pairings with the frame. -/
def frameComponent (z : V) : V :=
  QuadraticMap.polar q h.u z • h.x + QuadraticMap.polar q h.y z • h.v +
  QuadraticMap.polar q h.v z • h.y + QuadraticMap.polar q h.x z • h.u

private theorem frameRemainder_orthogonal (z : V) :
    let z₀ := z - h.frameComponent z
    QuadraticMap.polar q h.x z₀ = 0 ∧ QuadraticMap.polar q h.y z₀ = 0 ∧
    QuadraticMap.polar q h.u z₀ = 0 ∧ QuadraticMap.polar q h.v z₀ = 0 := by
  have hyx := (QuadraticMap.polar_comm q h.y h.x).trans h.xy
  have hux := (QuadraticMap.polar_comm q h.u h.x).trans h.xu
  have hxu := (QuadraticMap.polar_comm q h.u h.y).trans h.yu
  have huv := (QuadraticMap.polar_comm q h.v h.u).trans h.uv
  have hvx := (QuadraticMap.polar_comm q h.v h.x).trans h.xv
  have hvy := (QuadraticMap.polar_comm q h.v h.y).trans h.yv
  simp only [frameComponent, QuadraticMap.polar_sub_right, QuadraticMap.polar_add_right,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_self, h.qx, h.qy, h.qu, h.qv,
    smul_zero, h.xy, h.xu, h.xv, h.yv, h.uv, h.yu, hyx, hux, hxu, huv, hvx, hvy,
    smul_eq_mul, mul_zero, mul_one, add_zero, zero_add, sub_self, and_self]

/-- The matrix acts by the standard two-dimensional representation on each of
the frame's two ordered pairs and fixes their orthogonal complement. -/
def vectorTransform (g : Matrix.SpecialLinearGroup (Fin 2) R) (z : V) : V :=
  QuadraticMap.polar q h.u z • (g.val 0 0 • h.x + g.val 1 0 • h.v) +
  QuadraticMap.polar q h.y z • (g.val 0 1 • h.x + g.val 1 1 • h.v) +
  QuadraticMap.polar q h.v z • (g.val 0 0 • h.y - g.val 1 0 • h.u) +
  QuadraticMap.polar q h.x z • (-(g.val 0 1 • h.y) + g.val 1 1 • h.u) +
  (z - h.frameComponent z)

theorem matrixAction_intertwine (g : Matrix.SpecialLinearGroup (Fin 2) R) (z : V) :
    h.matrixAction g.val * ι q z = ι q (h.vectorTransform g z) * h.matrixAction g.val := by
  let A := h.matrixAction g.val
  let z₀ := z - h.frameComponent z
  obtain ⟨hx, hy, hu, hv⟩ := h.frameRemainder_orthogonal z
  have hz₀ : A * ι q z₀ = ι q z₀ * A :=
    (h.matrixAction_commute_of_orthogonal g.val z₀ hx hy hu hv).eq
  obtain ⟨hx', hv', hy', hu'⟩ := h.matrixAction_intertwine_frame g
  simp only [← show A = h.matrixAction g.val from rfl] at hx' hv' hy' hu'
  conv_lhs =>
    rw [show z = h.frameComponent z + z₀ from (add_sub_cancel _ _).symm]
  change A * ι q (h.frameComponent z + z₀) = ι q (h.vectorTransform g z) * A
  simp only [frameComponent, vectorTransform,
    map_add, map_smul, mul_add, mul_smul_comm, smul_mul_assoc, add_mul, hx', hv', hy', hu', hz₀]
  rfl

theorem matrixUnitsAction_conjugate (g : Matrix.SpecialLinearGroup (Fin 2) R) (z : V) :
    (h.matrixUnitsAction g).val * ι q z * (h.matrixUnitsAction g).inv =
      ι q (h.vectorTransform g z) := by
  change (h.matrixAction g.val * ι q z) * (h.matrixUnitsAction g).inv = _
  rw [h.matrixAction_intertwine, mul_assoc]
  change ι q (h.vectorTransform g z) * ((h.matrixUnitsAction g).val *
    (h.matrixUnitsAction g).inv) = _
  rw [Units.val_inv, mul_one]

section ScalarExtension

open LinearAlgebraicGroups.Albert.CliffordModel
open LinearAlgebraicGroups.Albert.SpinSpecification
open Module

variable {J : Type*} [LinearOrder J] (b : Basis J R V)
variable (S : Type*) [CommRing S] [Algebra R S]

private theorem coefficientForm_polar_one_tmul (x y : V) :
    QuadraticMap.polar (coefficientForm S q b) (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) =
      algebraMap R S (QuadraticMap.polar q x y) := by
  simp only [QuadraticMap.polar, ← TensorProduct.tmul_add, coefficientForm_tmul, one_mul, map_sub]

/-- A hyperbolic frame remains a hyperbolic frame under arbitrary scalar extension. -/
def baseChange : HyperbolicFrame (coefficientForm S q b) where
  x := 1 ⊗ₜ[R] h.x
  y := 1 ⊗ₜ[R] h.y
  u := 1 ⊗ₜ[R] h.u
  v := 1 ⊗ₜ[R] h.v
  qx := by simp [coefficientForm_tmul, h.qx]
  qy := by simp [coefficientForm_tmul, h.qy]
  qu := by simp [coefficientForm_tmul, h.qu]
  qv := by simp [coefficientForm_tmul, h.qv]
  xy := by simp [coefficientForm_polar_one_tmul b S, h.xy]
  uv := by simp [coefficientForm_polar_one_tmul b S, h.uv]
  xu := by simp [coefficientForm_polar_one_tmul b S, h.xu]
  yv := by simp [coefficientForm_polar_one_tmul b S, h.yv]
  xv := by simp [coefficientForm_polar_one_tmul b S, h.xv]
  yu := by simp [coefficientForm_polar_one_tmul b S, h.yu]

/-- The determinant-one action in the scalar extension of the original Clifford algebra. -/
def scalarMatrixUnitsAction : Matrix.SpecialLinearGroup (Fin 2) S →* (ScalarClifford q S)ˣ :=
  (Units.map (baseChangeEquiv S q b).symm.toMonoidHom).comp (h.baseChange b S).matrixUnitsAction

theorem scalarMatrixUnitsAction_val (g : Matrix.SpecialLinearGroup (Fin 2) S) :
    let E := (1 : S) ⊗ₜ[R] h.creation
    let L := (1 : S) ⊗ₜ[R] h.contraction
    (h.scalarMatrixUnitsAction b S g).val =
      1 + (g.val 0 0 - 1) • (E * L) + g.val 0 1 • E + g.val 1 0 • L +
        (g.val 1 1 - 1) • (L * E) := by
  apply (baseChangeEquiv S q b).injective
  change baseChangeEquiv S q b ((baseChangeEquiv S q b).symm
    ((h.baseChange b S).matrixAction g.val)) = _
  rw [AlgEquiv.apply_symm_apply]
  have he : baseChangeEquiv S q b ((1 : S) ⊗ₜ[R] h.creation) = (h.baseChange b S).creation := by
    rw [creation, ← one_mul (1 : S), ← Algebra.TensorProduct.tmul_mul_tmul]
    simp only [map_mul, baseChangeEquiv_ι, creation, baseChange]
  have hl : baseChangeEquiv S q b ((1 : S) ⊗ₜ[R] h.contraction) = (h.baseChange b S).contraction := by
    rw [contraction, ← one_mul (1 : S), ← Algebra.TensorProduct.tmul_mul_tmul]
    simp only [map_mul, baseChangeEquiv_ι, contraction, baseChange]
  simp only [matrixAction, map_add, map_mul, map_one, map_smul, he, hl]

theorem scalarMatrixUnitsAction_natural {T : Type*} [CommRing T] [Algebra R T]
    (f : S →ₐ[R] T) (g : Matrix.SpecialLinearGroup (Fin 2) S) :
    h.scalarMatrixUnitsAction b T (Matrix.SpecialLinearGroup.map f.toRingHom g) =
      Units.map (coefficientMap q S f).toMonoidHom (h.scalarMatrixUnitsAction b S g) := by
  apply Units.ext
  change (h.scalarMatrixUnitsAction b T (Matrix.SpecialLinearGroup.map f.toRingHom g)).val =
    coefficientMap q S f (h.scalarMatrixUnitsAction b S g).val
  rw [h.scalarMatrixUnitsAction_val, h.scalarMatrixUnitsAction_val]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe,
    coefficientMap, map_add, map_one, Algebra.smul_def, map_mul,
    Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, map_sub, Algebra.algebraMap_self_apply]
  rfl

open private baseChangeEquiv_evenOdd baseChangeEquiv_reverse
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel

private theorem baseChangeEquiv_vectors (z : S ⊗[R] V) :
    baseChangeEquiv S q b (vectors q S z) = ι (coefficientForm S q b) z := by
  induction z using TensorProduct.inductionOn with
  | tmul s z => rw [LinearMap.baseChange_tmul, baseChangeEquiv_ι]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem scalarMatrixUnitsAction_mem (g : Matrix.SpecialLinearGroup (Fin 2) S) :
    h.scalarMatrixUnitsAction b S g ∈ spinUnits q S := by
  let e := baseChangeEquiv S q b
  let frame := h.baseChange b S
  have he (g' : Matrix.SpecialLinearGroup (Fin 2) S) :
      e (h.scalarMatrixUnitsAction b S g').val = frame.matrixAction g'.val :=
    e.apply_symm_apply _
  have hvec (g' : Matrix.SpecialLinearGroup (Fin 2) S) :
      Set.MapsTo (conjugate q S (h.scalarMatrixUnitsAction b S g'))
        (LinearMap.range (vectors q S)) (LinearMap.range (vectors q S)) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨frame.vectorTransform g' z, e.injective ?_⟩
    have hv (w : S ⊗[R] V) : e (vectors q S w) = ι (coefficientForm S q b) w :=
      baseChangeEquiv_vectors b S w
    simp only [conjugate, map_mul, hv, he, ← map_inv (h.scalarMatrixUnitsAction b S)]
    exact (frame.matrixUnitsAction_conjugate g' z).symm
  refine ⟨?_, ?_, hvec g, ?_⟩
  · change (h.scalarMatrixUnitsAction b S g).val ∈ (evenOdd q 0).baseChange S
    have hmem : e (h.scalarMatrixUnitsAction b S g).val ∈ evenOdd (coefficientForm S q b) 0 := by
      rw [he]
      exact frame.matrixAction_even _
    rw [← baseChangeEquiv_evenOdd S q b 0] at hmem
    obtain ⟨x, hx, hxy⟩ := hmem
    exact (e.injective hxy) ▸ hx
  · apply e.injective
    rw [map_mul, map_one, baseChangeEquiv_reverse S q b, he]
    exact frame.matrixAction_norm g
  · rw [← map_inv (h.scalarMatrixUnitsAction b S)]
    exact hvec g⁻¹

theorem scalarMatrixUnitsAction_vector (g : Matrix.SpecialLinearGroup (Fin 2) S) (z : S ⊗[R] V) :
    vectors q S ((h.baseChange b S).vectorTransform g z) =
      conjugate q S (h.scalarMatrixUnitsAction b S g) (vectors q S z) := by
  let e := baseChangeEquiv S q b
  let h' := h.baseChange b S
  apply e.injective
  have hv (w : S ⊗[R] V) : e (vectors q S w) = ι (coefficientForm S q b) w :=
    baseChangeEquiv_vectors b S w
  have he (g' : Matrix.SpecialLinearGroup (Fin 2) S) :
      e (h.scalarMatrixUnitsAction b S g').val = h'.matrixAction g'.val := e.apply_symm_apply _
  simp only [conjugate, map_mul, hv, he, ← map_inv (h.scalarMatrixUnitsAction b S)]
  exact (h'.matrixUnitsAction_conjugate g z).symm

end ScalarExtension

section RepresentedSpin
open scoped CategoryTheory.MonObj

open CategoryTheory
open Module
open LinearAlgebraicGroups.Albert.SpinSpecification
open LinearAlgebraicGroups.Specs.SymplecticDatumRankOneAndPinning (determinantOnePoints)

variable {k W J : Type u} [Field k] [AddCommGroup W] [Module k W] [LinearOrder J]
variable {q : QuadraticForm k W} (h : HyperbolicFrame q) (b : Basis J k W)
variable {G : LinearAlgebraicGroups.Specs.GroupScheme k}
variable (e : ∀ S : TestAlgebra k, Points G.X S →* (ScalarClifford q S)ˣ)

private theorem exists_rankOne_point (rep : IsSpinPointRepresentation q G e)
    (S : TestAlgebra k) (g : Matrix.SpecialLinearGroup (Fin 2) S) :
    ∃ p : Points G.X S, e S p = h.scalarMatrixUnitsAction b S g := by
  rw [← Set.mem_range, (rep.1 S).2]
  exact h.scalarMatrixUnitsAction_mem b S g

/-- The formula for a hyperbolic frame defines a natural group homomorphism
into the represented spin group. -/
def representedRankOne (rep : IsSpinPointRepresentation q G e) :
    determinantOnePoints k ⟶ (groupPointsFunctor k).obj G where
  app S := GrpCat.ofHom
    { toFun := fun g => (h.exists_rankOne_point b e rep S g).choose
      map_one' := by
        apply (rep.1 S).1
        rw [(h.exists_rankOne_point b e rep S 1).choose_spec, map_one, map_one]
      map_mul' := by
        intro g g'
        apply (rep.1 S).1
        have hp (x : Matrix.SpecialLinearGroup (Fin 2) S) :=
          (h.exists_rankOne_point b e rep S x).choose_spec
        rw [hp (g * g'), (e S).map_mul, hp g, hp g', map_mul] }
  naturality S T f := by
    apply GrpCat.ext
    intro g
    change Matrix.SpecialLinearGroup (Fin 2) S at g
    apply (rep.1 T).1
    change e T (Classical.choose (h.exists_rankOne_point b e rep T
        (Matrix.SpecialLinearGroup.map f.hom.toRingHom g))) =
      e T (mapPoints f (Classical.choose (h.exists_rankOne_point b e rep S g)))
    calc
      _ = h.scalarMatrixUnitsAction b T (Matrix.SpecialLinearGroup.map f.hom.toRingHom g) :=
        (h.exists_rankOne_point b e rep T _).choose_spec
      _ = Units.map (coefficientMap q S f.hom).toMonoidHom (h.scalarMatrixUnitsAction b S g) :=
        h.scalarMatrixUnitsAction_natural b S f.hom g
      _ = _ := ((rep.2 f _).trans (congrArg
        (Units.map (coefficientMap q S f.hom).toMonoidHom)
        (h.exists_rankOne_point b e rep S g).choose_spec)).symm

theorem representedRankOne_apply (rep : IsSpinPointRepresentation q G e)
    (S : TestAlgebra k) (g : Matrix.SpecialLinearGroup (Fin 2) S) :
    e S ((h.representedRankOne b e rep).app S g) = h.scalarMatrixUnitsAction b S g :=
  (h.exists_rankOne_point b e rep S g).choose_spec

private theorem scalar_creation_eq (S : Type*) [CommRing S] [Algebra k S] :
    (1 : S) ⊗ₜ[k] h.creation =
      vectors q S (1 ⊗ₜ[k] h.x) *
      vectors q S (1 ⊗ₜ[k] h.y) := by
  rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, creation]

private theorem scalar_contraction_eq (S : Type*) [CommRing S] [Algebra k S] :
    (1 : S) ⊗ₜ[k] h.contraction =
      vectors q S (1 ⊗ₜ[k] h.v) *
      vectors q S (1 ⊗ₜ[k] h.u) := by
  rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, contraction]

theorem representedRankOne_values (rep : IsSpinPointRepresentation q G e)
    (S : TestAlgebra k) (g : Matrix.SpecialLinearGroup (Fin 2) S) :
    let z := (e S ((h.representedRankOne b e rep).app S g)).val
    let E := vectors q S (1 ⊗ₜ[k] h.x) * vectors q S (1 ⊗ₜ[k] h.y)
    let L := vectors q S (1 ⊗ₜ[k] h.v) * vectors q S (1 ⊗ₜ[k] h.u)
    (∀ t : S, g = Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) t → z = 1 + t • E) ∧
    (∀ t : S, g = Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 by decide) t → z = 1 + t • L) ∧
    (∀ t : Sˣ, g = Specs.Arithmetic.QuaternionScalarCliffordLift.scalarDiagonal t →
      z = 1 + ((t : S) - 1) • (E * L) + ((↑t⁻¹ : S) - 1) • (L * E)) := by
  dsimp only
  rw [representedRankOne_apply, scalarMatrixUnitsAction_val, scalar_creation_eq, scalar_contraction_eq]
  refine ⟨?_, ?_, ?_⟩
  · rintro t rfl
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection]
  · rintro t rfl
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection]
  · rintro t rfl
    simp [Specs.Arithmetic.QuaternionScalarCliffordLift.scalarDiagonal]

end RepresentedSpin

end HyperbolicFrame

end CliffordPlane

section HyperbolicCoordinates

open QuadraticMap

variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W] (q : QuadraticForm k W)

private theorem isometry_polar (s : q.IsometryEquiv q) (x y : W) :
    polar q (s x) (s y) = polar q x y := by
  simp only [polar, ← map_add, IsometryEquiv.map_app]

private def quadraticReflection (a : W) (ha : q a ≠ 0) : q.IsometryEquiv q := by
  let f : W →ₗ[k] W := LinearMap.id - (q.polarBilin a).smulRight ((q a)⁻¹ • a)
  have hf (z : W) : f z = z - (polar q a z / q a) • a := by
    simp [f, div_eq_mul_inv, smul_smul]
  have hmul (z : W) : polar q a z / q a * q a = polar q a z := div_mul_cancel₀ _ ha
  refine ⟨LinearEquiv.ofInvolutive f (fun z => ?_), fun z => ?_⟩
  · rw [hf, hf, polar_sub_right, polar_smul_right, polar_self, smul_eq_mul]
    have h : (polar q a z - polar q a z / q a * (2 • q a)) / q a = -(polar q a z / q a) := by
      rw [two_smul, mul_add, hmul]
      ring
    rw [h, neg_smul]
    abel
  · change q (f z) = q z
    rw [hf, sub_eq_add_neg, QuadraticMap.map_add q, q.map_neg, q.map_smul, polar_neg_right,
      polar_smul_right, polar_comm q z a]
    simp only [smul_eq_mul]
    rw [mul_assoc, hmul]
    ring

private theorem quadraticReflection_apply (a : W) (ha : q a ≠ 0) (z : W) :
    quadraticReflection q a ha z = z - (polar q a z / q a) • a := by
  change z - polar q a z • ((q a)⁻¹ • a) = _
  rw [smul_smul, div_eq_mul_inv]

private def eichlerLinear (e w : W) : W →ₗ[k] W :=
  LinearMap.id + (q.polarBilin e).smulRight w -
    (q.polarBilin w + q w • q.polarBilin e).smulRight e

private theorem eichlerLinear_apply (e w z : W) :
    eichlerLinear q e w z = z + polar q e z • w - (polar q w z + q w * polar q e z) • e := rfl

/-- The isometry fixing an isotropic vector and translating a polar partner. -/
private def eichlerIsometry (e w : W) (he : q e = 0) (hew : polar q e w = 0) :
    q.IsometryEquiv q := by
  have hwe := (polar_comm q w e).trans hew
  have hee : polar q e e = 0 := by simp [he]
  have hcancel (w : W) (hew : polar q e w = 0) :
      (eichlerLinear q e (-w)).comp (eichlerLinear q e w) = LinearMap.id := by
    have hwe := (polar_comm q w e).trans hew
    ext z
    change eichlerLinear q e (-w) (eichlerLinear q e w z) = z
    rw [eichlerLinear_apply]
    have hez : polar q e (eichlerLinear q e w z) = polar q e z := by
      simp [eichlerLinear_apply, hew, hee]
    have hwz : polar q w (eichlerLinear q e w z) = polar q w z + 2 * q w * polar q e z := by
      simp [eichlerLinear_apply, hwe, two_smul, smul_eq_mul]
      ring
    rw [hez, polar_neg_left, hwz, q.map_neg, eichlerLinear_apply]
    module
  have hcancel' : (eichlerLinear q e w).comp (eichlerLinear q e (-w)) = LinearMap.id := by
    simpa using hcancel (-w) (by simp [hew])
  refine ⟨LinearEquiv.ofLinearMap _ _ hcancel' (hcancel w hew), fun z => ?_⟩
  change q (eichlerLinear q e w z) = q z
  rw [eichlerLinear_apply, sub_eq_add_neg, QuadraticMap.map_add q, q.map_neg, q.map_smul, he,
    polar_neg_right, polar_smul_right, polar_add_left, polar_smul_left, hwe,
    QuadraticMap.map_add q, q.map_smul, polar_smul_right, polar_comm q z w, polar_comm q z e]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring

private theorem eichlerIsometry_apply (e w : W) (he : q e = 0) (hew : polar q e w = 0)
    (z : W) : eichlerIsometry q e w he hew z =
      z + polar q e z • w - (polar q w z + q w * polar q e z) • e := rfl

/-- Pair isometries in a nondegenerate subspace are obtained by reflections
and a translation fixing the first member of the target pair. -/
private theorem move_hyperbolicPair (U : Submodule k W)
    (hU : ∀ x ∈ U, x ≠ 0 → ∃ z ∈ U, polar q x z ≠ 0)
    {x y x' y' : W} (hx : x ∈ U) (hy : y ∈ U) (hx' : x' ∈ U) (hy' : y' ∈ U)
    (hqx : q x = 0) (hqy : q y = 0) (hqx' : q x' = 0) (hqy' : q y' = 0)
    (hxy : polar q x y = 1) (hxy' : polar q x' y' = 1) :
    ∃ s : q.IsometryEquiv q, s x = x' ∧ s y = y' ∧
      Set.MapsTo s U U ∧ ∀ z, (∀ a ∈ U, polar q a z = 0) → s z = z := by
  let Good (s : q.IsometryEquiv q) :=
    Set.MapsTo s U U ∧ ∀ z, (∀ a ∈ U, polar q a z = 0) → s z = z
  have htrans {s t : q.IsometryEquiv q} (hs : Good s) (ht : Good t) : Good (s.trans t) :=
    ⟨fun _ hu => ht.1 (hs.1 hu), fun z hz => by
      change t (s z) = z
      rw [hs.2 z hz, ht.2 z hz]⟩
  have hr {a b : W} (ha : a ∈ U) (hb : b ∈ U) (hqa : q a = 0) (hqb : q b = 0)
      (hab : polar q a b ≠ 0) : ∃ s : q.IsometryEquiv q, s a = b ∧ Good s := by
    have hq : q (a - b) = -polar q a b := by
      rw [sub_eq_add_neg, QuadraticMap.map_add q, q.map_neg, hqa, hqb, polar_neg_right, zero_add, zero_add]
    have hq₀ : q (a - b) ≠ 0 := hq ▸ neg_ne_zero.mpr hab
    have hs : polar q (a - b) a = q (a - b) := by
      rw [polar_sub_left, polar_self, hqa, smul_zero, zero_sub, polar_comm q b a, hq]
    refine ⟨quadraticReflection q (a - b) hq₀, ?_, ?_⟩
    · rw [quadraticReflection_apply, hs, div_self hq₀, one_smul, sub_sub_cancel]
    · refine ⟨fun z hz => ?_, fun z hz => ?_⟩
      · rw [quadraticReflection_apply]
        exact U.sub_mem hz (U.smul_mem _ (U.sub_mem ha hb))
      · rw [quadraticReflection_apply, hz _ (U.sub_mem ha hb), zero_div, zero_smul, sub_zero]
  have hfirst : ∃ s : q.IsometryEquiv q, s x = x' ∧ Good s := by
    by_cases hp : polar q x x' = 0
    · have hx₀ : x ≠ 0 := fun h => by simp [h] at hxy
      have hx'₀ : x' ≠ 0 := fun h => by simp [h] at hxy'
      obtain ⟨v, hv, hv₀⟩ := hU x hx hx₀
      have hboth : ∃ z ∈ U, polar q x z ≠ 0 ∧ polar q x' z ≠ 0 := by
        by_cases h : polar q x' v = 0
        · obtain ⟨w, hw, hw₀⟩ := hU x' hx' hx'₀
          by_cases h' : polar q x w = 0
          · exact ⟨v + w, U.add_mem hv hw, by simpa [h'] using hv₀, by simpa [h] using hw₀⟩
          · exact ⟨w, hw, h', hw₀⟩
        · exact ⟨v, hv, hv₀, h⟩
      obtain ⟨z, hz, hzx, hzx'⟩ := hboth
      let t := z - (q z / polar q x z) • x
      have ht : t ∈ U := U.sub_mem hz (U.smul_mem _ hx)
      have hqt : q t = 0 := by
        simp only [t, sub_eq_add_neg, QuadraticMap.map_add q, q.map_neg, q.map_smul, hqx,
          add_zero, polar_neg_right, polar_smul_right, polar_comm q z x, smul_eq_mul, mul_zero,
          div_mul_cancel₀ _ hzx, add_neg_cancel]
      have hxt : polar q x t ≠ 0 := by simpa [t, hqx] using hzx
      have htx' : polar q t x' ≠ 0 := by
        rw [polar_comm]
        simpa [t, (polar_comm q x' x).trans hp] using hzx'
      obtain ⟨s, hs, hsg⟩ := hr hx ht hqx hqt hxt
      obtain ⟨r, hr', hrg⟩ := hr ht hx' hqt hqx' htx'
      exact ⟨s.trans r, by change r (s x) = x'; rw [hs, hr'], htrans hsg hrg⟩
    · exact hr hx hx' hqx hqx' hp
  obtain ⟨s, hs, hsg⟩ := hfirst
  let b := s y
  have hb : b ∈ U := hsg.1 hy
  have hqb : q b = 0 := (s.map_app y).trans hqy
  have hxb : polar q x' b = 1 := by
    rw [← hs]
    exact (isometry_polar q s x y).trans hxy
  let c := polar q b y'
  let w := y' - b - c • x'
  have hw : w ∈ U := U.sub_mem (U.sub_mem hy' hb) (U.smul_mem _ hx')
  have hxw : polar q x' w = 0 := by simp [w, hxy', hxb, hqx']
  have hbw : polar q b w = 0 := by simp [w, c, hqb, (polar_comm q b x').trans hxb]
  have hsum : b + w + c • x' = y' := by dsimp [w]; abel
  have hqw : q w + c = 0 := by
    have h := congrArg q hsum
    rwa [QuadraticMap.map_add q, QuadraticMap.map_add q, q.map_smul, hqx', hqb, hbw, zero_add, add_zero, smul_zero,
      add_zero, polar_smul_right, polar_add_left, polar_comm q w x', hxw,
      (polar_comm q b x').trans hxb, add_zero, smul_eq_mul, mul_one, hqy'] at h
  let t := eichlerIsometry q x' w hqx' hxw
  have ht : Good t := by
    constructor
    · intro z hz
      rw [show t z = _ from eichlerIsometry_apply q x' w hqx' hxw z]
      exact U.sub_mem (U.add_mem hz (U.smul_mem _ hw)) (U.smul_mem _ hx')
    · intro z hz
      simp [t, eichlerIsometry_apply, hz _ hx', hz _ hw]
  refine ⟨s.trans t, ?_, ?_, htrans hsg ht⟩
  · change t (s x) = x'
    rw [hs, show t x' = _ from eichlerIsometry_apply q x' w hqx' hxw x']
    simp [hqx', polar_comm q w x', hxw]
  · change t b = y'
    rw [show t b = _ from eichlerIsometry_apply q x' w hqx' hxw b]
    rw [hxb, one_smul, (polar_comm q w b).trans hbw, mul_one, zero_add,
      (eq_neg_of_add_eq_zero_left hqw : q w = -c), neg_smul, sub_neg_eq_add]
    exact hsum

private theorem move_hyperbolicFrame
    (hnd : ∀ x : W, x ≠ 0 → ∃ z, polar q x z ≠ 0)
    (h h' : HyperbolicFrame q) :
    ∃ s : q.IsometryEquiv q, s h.x = h'.x ∧ s h.y = h'.y ∧ s h.u = h'.u ∧ s h.v = h'.v := by
  obtain ⟨s, hsx, hsu, _⟩ := move_hyperbolicPair q ⊤
    (fun x _ hx => let ⟨z, hz⟩ := hnd x hx; ⟨z, Submodule.mem_top, hz⟩)
    (x := h.x) (y := h.u) (x' := h'.x) (y' := h'.u)
    Submodule.mem_top Submodule.mem_top Submodule.mem_top Submodule.mem_top
    h.qx h.qu h'.qx h'.qu h.xu h'.xu
  let U := (q.polarBilin h'.x).ker ⊓ (q.polarBilin h'.u).ker
  have hx'u' : polar q h'.u h'.x = 1 := (polar_comm q _ _).trans h'.xu
  have hyu : polar q h.u h.y = 0 := (polar_comm q _ _).trans h.yu
  have hyu' : polar q h'.u h'.y = 0 := (polar_comm q _ _).trans h'.yu
  have hnd' (x : W) (hx : x ∈ U) (hx₀ : x ≠ 0) : ∃ z ∈ U, polar q x z ≠ 0 := by
    obtain ⟨z, hz⟩ := hnd x hx₀
    let z' := z - polar q h'.x z • h'.u - polar q h'.u z • h'.x
    change polar q h'.x x = 0 ∧ polar q h'.u x = 0 at hx
    refine ⟨z', ?_, ?_⟩
    · change polar q h'.x z' = 0 ∧ polar q h'.u z' = 0
      simp [z', h'.xu, hx'u', h'.qx, h'.qu]
    · simpa [z', polar_comm q x h'.x, polar_comm q x h'.u, hx.1, hx.2] using hz
  have hsy : s h.y ∈ U := by
    change polar q h'.x (s h.y) = 0 ∧ polar q h'.u (s h.y) = 0
    rw [← hsx, ← hsu, isometry_polar, isometry_polar, h.xy, hyu]
    exact ⟨rfl, rfl⟩
  have hsv : s h.v ∈ U := by
    change polar q h'.x (s h.v) = 0 ∧ polar q h'.u (s h.v) = 0
    rw [← hsx, ← hsu, isometry_polar, isometry_polar, h.xv, h.uv]
    exact ⟨rfl, rfl⟩
  have hy' : h'.y ∈ U := ⟨h'.xy, hyu'⟩
  have hv' : h'.v ∈ U := ⟨h'.xv, h'.uv⟩
  obtain ⟨t, hty, htv, _, hfix⟩ := move_hyperbolicPair q U hnd' hsy hsv hy' hv'
    ((s.map_app h.y).trans h.qy) ((s.map_app h.v).trans h.qv) h'.qy h'.qv
    ((isometry_polar q s h.y h.v).trans h.yv) h'.yv
  refine ⟨s.trans t, ?_, hty, ?_, htv⟩
  · change t (s h.x) = h'.x
    rw [hsx]
    exact hfix h'.x fun z hz => (polar_comm q _ _).trans hz.1
  · change t (s h.u) = h'.u
    rw [hsu]
    exact hfix h'.u fun z hz => (polar_comm q _ _).trans hz.2

end HyperbolicCoordinates

section CliffordIsometry

open CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Albert.SpinSpecification
open LinearAlgebraicGroups.Specs (GroupScheme)

open private map_isometry_reverse map_isometry_evenOdd
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
  {q : QuadraticForm k V} (s : q.IsometryEquiv q)
  {G : GroupScheme k} (e : ∀ R : TestAlgebra k, Points G.X R →* (ScalarClifford q R)ˣ)

private def cliffordIsometry (R : TestAlgebra k) : ScalarClifford q R ≃ₐ[k] ScalarClifford q R :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R) (CliffordAlgebra.equivOfIsometry s)

private theorem cliffordIsometry_vectors (R : TestAlgebra k) (z : R ⊗[k] V) :
    cliffordIsometry s R (vectors q R z) =
      vectors q R (TensorProduct.congr (LinearEquiv.refl k R) s.toLinearEquiv z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r z =>
    change r ⊗ₜ[k] CliffordAlgebra.map s.toIsometry (CliffordAlgebra.ι q z) =
      r ⊗ₜ[k] CliffordAlgebra.ι q (s z)
    rw [map_apply_ι]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem cliffordIsometry_reversion (R : TestAlgebra k) (z : ScalarClifford q R) :
    cliffordIsometry s R (reversion q R z) = reversion q R (cliffordIsometry s R z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r z =>
    change r ⊗ₜ[k] CliffordAlgebra.map s.toIsometry (reverse z) =
      r ⊗ₜ[k] reverse (CliffordAlgebra.map s.toIsometry z)
    rw [map_isometry_reverse]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem cliffordIsometry_smul (R : TestAlgebra k) (t : R) (z : ScalarClifford q R) :
    cliffordIsometry s R (t • z) = t • cliffordIsometry s R z := by
  induction z using TensorProduct.inductionOn with
  | tmul r z => rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem cliffordIsometry_even (R : TestAlgebra k) {z : ScalarClifford q R}
    (hz : z ∈ evenPart q R) : cliffordIsometry s R z ∈ evenPart q R := by
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.inductionOn with
  | tmul r z =>
    change (r ⊗ₜ[k] (CliffordAlgebra.map s.toIsometry z.val)) ∈ (evenOdd q 0).baseChange R
    exact Submodule.tmul_mem_baseChange_of_mem r (map_isometry_evenOdd s.toIsometry z.property)
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

private def cliffordUnits (R : TestAlgebra k) : (ScalarClifford q R)ˣ →* (ScalarClifford q R)ˣ :=
  Units.map (cliffordIsometry s R).toMonoidHom

private theorem cliffordUnits_inverse (R : TestAlgebra k) (a : (ScalarClifford q R)ˣ) :
    cliffordUnits s.symm R (cliffordUnits s R a) = a := by
  apply Units.ext
  exact (cliffordIsometry s R).symm_apply_apply a.val

private theorem cliffordUnits_preservesSpin (R : TestAlgebra k) {a : (ScalarClifford q R)ˣ}
    (ha : a ∈ spinUnits q R) : cliffordUnits s R a ∈ spinUnits q R := by
  have hv {b : (ScalarClifford q R)ˣ}
      (hb : Set.MapsTo (conjugate q R b) (LinearMap.range (vectors q R))
        (LinearMap.range (vectors q R))) :
      Set.MapsTo (conjugate q R (cliffordUnits s R b)) (LinearMap.range (vectors q R))
        (LinearMap.range (vectors q R)) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (TensorProduct.congr (LinearEquiv.refl k R) s.toLinearEquiv).surjective x
    obtain ⟨z, hz⟩ := hb (LinearMap.mem_range_self (vectors q R) y)
    refine ⟨TensorProduct.congr (LinearEquiv.refl k R) s.toLinearEquiv z, ?_⟩
    rw [← cliffordIsometry_vectors s R z, hz, ← hy, ← cliffordIsometry_vectors s R y]
    rw [conjugate, conjugate, ← map_inv (cliffordUnits s R), map_mul, map_mul]
    rfl
  refine ⟨cliffordIsometry_even s R ha.1, ?_, hv ha.2.2.1, ?_⟩
  · change reversion q R (cliffordIsometry s R a.val) * cliffordIsometry s R a.val = 1
    rw [← cliffordIsometry_reversion, ← map_mul, ha.2.1, map_one]
  · rw [← map_inv (cliffordUnits s R)]
    exact hv ha.2.2.2

private theorem cliffordUnits_naturality {R S : TestAlgebra k} (a : R ⟶ S)
    (x : (ScalarClifford q R)ˣ) :
    Units.map (coefficientMap q R a.hom).toMonoidHom (cliffordUnits s R x) =
      cliffordUnits s S (Units.map (coefficientMap q R a.hom).toMonoidHom x) := by
  apply Units.ext
  change coefficientMap q R a.hom (cliffordIsometry s R x.val) =
    cliffordIsometry s S (coefficientMap q R a.hom x.val)
  induction x.val using TensorProduct.inductionOn with
  | tmul r y => rfl
  | add y z hy hz => simp only [map_add, hy, hz]

private theorem exists_spinIsometry_point (rep : IsSpinPointRepresentation q G e)
    (R : TestAlgebra k) (p : Points G.X R) : ∃ y, e R y = cliffordUnits s R (e R p) := by
  rw [← Set.mem_range, (rep.1 R).2]
  exact cliffordUnits_preservesSpin s R ((rep.1 R).2 ▸ Set.mem_range_self p)

private def spinIsometryPoints (rep : IsSpinPointRepresentation q G e)
    (R : TestAlgebra k) : Points G.X R →* Points G.X R where
  toFun p := (exists_spinIsometry_point s e rep R p).choose
  map_one' := (rep.1 R).1 (by
    rw [(exists_spinIsometry_point s e rep R 1).choose_spec, map_one, map_one])
  map_mul' p x := (rep.1 R).1 (by
    rw [(exists_spinIsometry_point s e rep R (p * x)).choose_spec, map_mul, map_mul, map_mul,
      (exists_spinIsometry_point s e rep R p).choose_spec,
      (exists_spinIsometry_point s e rep R x).choose_spec])

private theorem spinIsometryPoints_apply (rep : IsSpinPointRepresentation q G e)
    (R : TestAlgebra k) (p : Points G.X R) :
    e R (spinIsometryPoints s e rep R p) = cliffordUnits s R (e R p) :=
  (exists_spinIsometry_point s e rep R p).choose_spec

/-- A quadratic isometry acts on the represented spin group through its
induced automorphism of the Clifford algebra. -/
private def spinIsometry (rep : IsSpinPointRepresentation q G e) :
    (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj G :=
  NatIso.ofComponents (fun R =>
    let j : Points G.X R ≃* Points G.X R :=
      { toFun := spinIsometryPoints s e rep R
        invFun := spinIsometryPoints s.symm e rep R
        left_inv p := (rep.1 R).1 (by simp only [spinIsometryPoints_apply, cliffordUnits_inverse])
        right_inv p := (rep.1 R).1 (by
          rw [spinIsometryPoints_apply, spinIsometryPoints_apply]
          apply Units.ext
          exact (cliffordIsometry s R).apply_symm_apply (e R p).val)
        map_mul' := (spinIsometryPoints s e rep R).map_mul }
    j.toGrpIso) (by
    intro R S a
    apply GrpCat.ext
    intro p
    change Points G.X R at p
    apply (rep.1 S).1
    change e S (spinIsometryPoints s e rep S (mapPoints a p)) =
      e S (mapPoints a (spinIsometryPoints s e rep R p))
    have h (p : Points G.X R) : e S (mapPoints a p) =
        Units.map (coefficientMap q R a.hom).toMonoidHom (e R p) := rep.2 a p
    rw [spinIsometryPoints_apply, h, h, spinIsometryPoints_apply, cliffordUnits_naturality])

private def representedSpinIsometry (hG : IsAffine G.X.left) (rep : IsSpinPointRepresentation q G e) : G ≅ G := by
  let d := spinIsometry s e rep
  let c := groupHomEquiv G G hG
  let f := c.symm d.hom
  let g := c.symm d.inv
  have hf : (groupPointsFunctor k).map f = d.hom := c.apply_symm_apply _
  have hg : (groupPointsFunctor k).map g = d.inv := c.apply_symm_apply _
  refine ⟨f, g, ?_, ?_⟩
  · apply c.injective
    change (groupPointsFunctor k).map (f ≫ g) = (groupPointsFunctor k).map (𝟙 G)
    rw [Functor.map_comp, CategoryTheory.Functor.map_id (groupPointsFunctor k) G, hf, hg, d.hom_inv_id]
  · apply c.injective
    change (groupPointsFunctor k).map (g ≫ f) = (groupPointsFunctor k).map (𝟙 G)
    rw [Functor.map_comp, CategoryTheory.Functor.map_id (groupPointsFunctor k) G, hf, hg, d.inv_hom_id]

private theorem representedSpinIsometry_apply (hG : IsAffine G.X.left) (rep : IsSpinPointRepresentation q G e)
    (R : TestAlgebra k) (p : Points G.X R) :
    (e R (p ≫ (representedSpinIsometry s e hG rep).hom.hom.hom)).val = cliffordIsometry s R (e R p).val := by
  have h : (groupPointsFunctor k).map (representedSpinIsometry s e hG rep).hom = (spinIsometry s e rep).hom :=
    (groupHomEquiv G G hG).apply_symm_apply _
  have hh := congrArg (fun m => m.app R p) h
  change p ≫ (representedSpinIsometry s e hG rep).hom.hom.hom = spinIsometryPoints s e rep R p at hh
  rw [hh, spinIsometryPoints_apply]
  rfl

end CliffordIsometry
section Lifts

open CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair SpinModel)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
  (QuaternionHyperbolicPresentation spinVectorProjection)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionScalarCliffordLift
  (LiftsScalarPair scalarPairMatrix)
open LinearAlgebraicGroups.Specs.SymplecticDatumRankOneAndPinning (determinantOnePoints)
open _root_.Specs.RM03.CSA (isCentralSimple)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G A : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ}

private theorem testAlgebra_scalar_injective (R : TestAlgebra F) :
    Function.Injective (algebraMap R (R ⊗[F] B)) :=
  Algebra.TensorProduct.includeLeft_injective (S := R) (A := R) (algebraMap F B).injective

private theorem scalarPairMatrix_injective (R : TestAlgebra F) :
    Function.Injective (scalarPairMatrix (B := B) (d := d) R) := by
  intro x y hxy
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply testAlgebra_scalar_injective (B := B) R
  simpa only [scalarPairMatrix, Matrix.fromBlocks_apply₁₁, Matrix.map_apply] using
    congrFun (congrFun hxy (Sum.inl i)) (Sum.inl j)

/-- Any lift of the scalar matrix action is a closed immersion. -/
theorem scalarLift_isClosedImmersion (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d)
    (e : (groupPointsFunctor F).obj A.val ≅ determinantOnePoints F) (f : A.val ⟶ G.val)
    (hf : LiftsScalarPair M Q e f) : IsClosedImmersion f.hom.hom.left := by
  apply RootData.RootGroups.isClosedImmersion_of_injectivePoints A G f
  intro R p p' he
  change Points A.val.X R at p p'
  change p ≫ f.hom.hom = p' ≫ f.hom.hom at he
  have hmat : scalarPairMatrix (B := B) (d := d) R (e.hom.app R p) =
      scalarPairMatrix (B := B) (d := d) R (e.hom.app R p') := by
    rw [← hf R p, ← hf R p', he]
  have hpp := scalarPairMatrix_injective (B := B) (d := d) R hmat
  change p = p'
  have hinv (z : Points A.val.X R) : e.inv.app R (e.hom.app R z) = z :=
    congrArg (fun t => t.app R z) e.hom_inv_id
  rw [← hinv p, ← hinv p', hpp]

/-- The vector projection is injective on reduced characteristic-two test
algebras. Its scheme kernel is still the full square-one unit scheme. -/
theorem spinVectorProjection_injective_of_reduced [CharP F 2]
    (M : SpinModel G D) (R : TestAlgebra F) [_root_.IsReduced R] :
    Function.Injective (spinVectorProjection M R) := by
  intro x y hxy
  let π : Points G.val.X R →* Points M.neutral.val.X R :=
    (((groupPointsFunctor F).map M.projection).app R).hom
  have hπ : π x = π y := by
    let : IsOpenImmersion M.inclusion.hom.hom.left := M.openImmersion
    let : Mono M.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono M.inclusion.hom.hom).mp
    apply M.fullFaithful R
    change M.fullPoints R ((x ≫ M.projection.hom.hom) ≫ M.inclusion.hom.hom) =
      M.fullPoints R ((y ≫ M.projection.hom.hom) ≫ M.inclusion.hom.hom)
    rw [Category.assoc, Category.assoc]
    exact hxy
  have hker : π (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hπ, mul_inv_cancel]
  let p : Points M.kernel.group.X R := M.isKernel.lift (x * y⁻¹) (toUnit _) hker
  have hp : p ≫ M.kernel.inclusion.hom.hom = x * y⁻¹ := M.isKernel.lift_fst _ _ _
  let a := (M.kernelPoints R p).val
  have ha : (a : R) ^ 2 = 1 := (mem_rootsOfUnity' 2 a).mp (M.kernelPoints R p).property
  have htwo : (2 : R) = 0 := by
    rw [← map_ofNat (algebraMap F R) 2, CharP.ofNat_eq_zero F 2, map_zero]
  have ha₁ : (a : R) = 1 := by
    apply sub_eq_zero.mp
    apply IsNilpotent.eq_zero
    refine ⟨2, ?_⟩
    rw [sub_sq, ha, htwo, zero_mul, zero_mul, sub_zero, one_pow, one_add_one_eq_two, htwo]
  have hp₁ : p = 1 := by
    apply (M.kernelPoints R).injective
    rw [map_one]
    exact Subtype.ext (Units.ext ha₁)
  apply mul_inv_eq_one.mp
  rw [← hp, hp₁]
  exact map_one (((groupPointsFunctor F).map M.kernel.inclusion).app R).hom

open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

/-- Two lifts from a smooth affine source agree on its universal point. -/
theorem scalarLift_unique [CharP F 2] (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d)
    (hA : Smooth A.val.X.hom)
    (e : (groupPointsFunctor F).obj A.val ≅ determinantOnePoints F)
    {f f' : A.val ⟶ G.val} (hf : LiftsScalarPair M Q e f) (hf' : LiftsScalarPair M Q e f') :
    f' = f := by
  obtain ⟨C, _, ⟨a⟩⟩ := groupPresentation A
  let R := CommAlgCat.of F C
  let p : Points A.val.X R := a.hom.hom.hom
  let : Smooth A.val.X.hom := hA
  let : AlgebraicGeometry.IsReduced A.val.X.left := isReduced_of_smooth_over_field A.val.X.hom
  have ha : IsIso a.hom.hom.hom.left :=
    (Grp.forget (SchemeOver F) ⋙ Over.forget (Spec (CommRingCat.of F))).map_isIso a.hom
  have hi := @IsOpenImmersion.of_isIso _ _ a.hom.hom.hom.left ha
  have hred : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of C)) :=
    @isReduced_of_isOpenImmersion _ _ a.hom.hom.hom.left hi inferInstance
  let : _root_.IsReduced R := (affine_isReduced_iff (CommRingCat.of C)).mp hred
  have he : p ≫ f'.hom.hom = p ≫ f.hom.hom :=
    spinVectorProjection_injective_of_reduced M R (Units.ext
      ((Q.matrixAt R).injective ((hf' R p).trans (hf R p).symm)))
  apply Grp.hom_ext
  let : IsIso p := inferInstanceAs (IsIso (((Grp.forget (SchemeOver F)).map a.hom)))
  exact (cancel_epi p).mp he

end Lifts
section Contractions

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (GroupScheme)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionScalarCliffordLift (scalarDiagonal)
open LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.Specs.SymplecticDatumRankOneAndPinning (determinantOnePoints)
open LinearAlgebraicGroups.CocharacterDynamics

private abbrev upper {R : Type u} [CommRing R] :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (F := R)

private abbrev lower {R : Type u} [CommRing R] :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (F := R)

private theorem scalarDiagonal_mul {R : Type u} [CommRing R] (s t : Rˣ) :
    scalarDiagonal (s * t) = scalarDiagonal s * scalarDiagonal t := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (scalarDiagonal (s * t)).val i j = ((scalarDiagonal s).val * (scalarDiagonal t).val) i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarDiagonal, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem scalarDiagonal_inv {R : Type u} [CommRing R] (t : Rˣ) :
    (scalarDiagonal t)⁻¹ = scalarDiagonal t⁻¹ := by
  have ho : scalarDiagonal (1 : Rˣ) = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [scalarDiagonal]
  apply inv_eq_of_mul_eq_one_right
  rw [← scalarDiagonal_mul, mul_inv_cancel, ho]

theorem scalarDiagonal_conjugate_upper {R : Type u} [CommRing R] (s : Rˣ) (t : R) :
    scalarDiagonal s * upper t * (scalarDiagonal s)⁻¹ = upper (t * (s : R) ^ 2) := by
  rw [scalarDiagonal_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((scalarDiagonal s).val * (upper t).val * (scalarDiagonal s⁻¹).val) i j =
    (upper (t * (s : R) ^ 2)).val i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [scalarDiagonal, Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply, pow_two] <;> ring

theorem scalarDiagonal_conjugate_lower {R : Type u} [CommRing R] (s : Rˣ) (t : R) :
    scalarDiagonal s⁻¹ * lower t * (scalarDiagonal s⁻¹)⁻¹ = lower (t * (s : R) ^ 2) := by
  rw [scalarDiagonal_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((scalarDiagonal s⁻¹).val * (lower t).val * (scalarDiagonal s).val) i j =
    (lower (t * (s : R) ^ 2)).val i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [scalarDiagonal, Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply, pow_two] <;> ring

private theorem map_transvection {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {i j : Fin 2} (hij : i ≠ j) (t : R) :
    Matrix.SpecialLinearGroup.map f (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij (f t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  change f (Matrix.transvection i j t a b) = Matrix.transvection i j (f t) a b
  simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, apply_ite f]

variable {k : Type u} [Field k] {A G : GroupScheme k}

private abbrev pointHom (f : A ⟶ G) (R : TestAlgebra k) :
    Points A.X R →* Points G.X R :=
  (((groupPointsFunctor k).map f).app R).hom

private theorem hasLimit_postcompose (f : A ⟶ G) {c : Cocharacter A}
    {R : TestAlgebra k} {p q : Points A.X R} (h : HasLimit c p q) :
    HasLimit (c ≫ f) (pointHom f R p) (pointHom f R q) := by
  rcases h with ⟨x, hx, hq⟩
  have hn {S T : TestAlgebra k} (v : S ⟶ T) (x : Points A.X S) :
      mapPoints v (pointHom f S x) = pointHom f T (mapPoints v x) :=
    (Category.assoc _ _ _).symm
  refine ⟨pointHom f _ x, ?_, ?_⟩
  · rw [hn, hx]
    simp only [orbit, map_mul, map_inv, hn]
    rfl
  · rw [hn, hq]

open private opposite_point unitEquiv unitEquiv_unitPoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private def diagonalPoints :
    (groupPointsFunctor k).obj (specGroup (Specs.DiagonalizableGroups.groupAlgebra k
      Specs.DiagonalizableGroups.IntegerCharacters)) ⟶ determinantOnePoints k where
  app R :=
    let d : Rˣ →* Matrix.SpecialLinearGroup (Fin 2) R :=
      { toFun := scalarDiagonal
        map_one' := by
          apply Matrix.SpecialLinearGroup.ext
          intro i j
          fin_cases i <;> fin_cases j <;> simp [scalarDiagonal]
        map_mul' := scalarDiagonal_mul }
    GrpCat.ofHom (d.comp (unitEquiv R).toMonoidHom)
  naturality R S a := by
    apply GrpCat.ext
    intro p
    let s := unitEquiv R p
    have hp : unitPoint R s = p := (unitEquiv R).injective (unitEquiv_unitPoint R s)
    change scalarDiagonal (unitEquiv S (mapPoints a p)) =
      Matrix.SpecialLinearGroup.map a.hom.toRingHom (scalarDiagonal s)
    symm
    rw [← hp, mapPoints_unitPoint, unitEquiv_unitPoint]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change a.hom ((scalarDiagonal s).val i j) =
      (scalarDiagonal (Units.map a.hom.toMonoidHom s)).val i j
    fin_cases i <;> fin_cases j <;> simp [scalarDiagonal, ← map_inv]

/-- The diagonal of the represented determinant-one group is a cocharacter. -/
theorem determinantOne_diagonal (e : (groupPointsFunctor k).obj A ≅ determinantOnePoints k) :
    ∃ c : Cocharacter A, ∀ (R : TestAlgebra k) (s : Rˣ),
      e.hom.app R (cocharacterPoint c R s) = scalarDiagonal s := by
  let H : GroupScheme k := specGroup (Specs.DiagonalizableGroups.groupAlgebra k
    Specs.DiagonalizableGroups.IntegerCharacters)
  have hH : IsAffine H.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of _)))
  let c := (groupHomEquiv H A hH).symm (diagonalPoints ≫ e.inv)
  have hc : (groupPointsFunctor k).map c = diagonalPoints ≫ e.inv :=
    (groupHomEquiv H A hH).apply_symm_apply _
  refine ⟨c, fun R s => ?_⟩
  have h := congrArg (fun m => (m.app R) (unitPoint R s)) hc
  change cocharacterPoint c R s = e.inv.app R (scalarDiagonal (unitEquiv R (unitPoint R s))) at h
  rw [h, unitEquiv_unitPoint]
  exact congrArg (fun m => (m.app R) (scalarDiagonal s)) e.inv_hom_id

theorem determinantOne_contracts
    (e : (groupPointsFunctor k).obj A ≅ determinantOnePoints k)
    (c : Cocharacter A)
    (hc : ∀ (R : TestAlgebra k) (s : Rˣ),
      e.hom.app R (cocharacterPoint c R s) = scalarDiagonal s)
    (f : A ⟶ G) (R : TestAlgebra k) (p : Points A.X R) (r : R) :
    (e.hom.app R p = upper r → HasLimit (c ≫ f) (p ≫ f.hom.hom) 1) ∧
    (e.hom.app R p = lower r → HasLimit (oppositeCocharacter (c ≫ f)) (p ≫ f.hom.hom) 1) := by
  have hn {S T : TestAlgebra k} (v : S ⟶ T) (p : Points A.X S) :
      e.hom.app T (mapPoints v p) =
        Matrix.SpecialLinearGroup.map v.hom.toRingHom (e.hom.app S p) :=
    congrArg (fun t => t p) (e.hom.naturality v)
  have hi (S : TestAlgebra k) (g : Matrix.SpecialLinearGroup (Fin 2) S) :
      e.hom.app S (e.inv.app S g) = g :=
    congrArg (fun t => t.app S g) e.inv_hom_id
  have hinj (S : TestAlgebra k) : Function.Injective (e.hom.app S) :=
    (e.app S).groupIsoToMulEquiv.injective
  let a := Polynomial.C r * (Polynomial.X : Polynomial R) ^ 2
  have ha : (polynomialToLaurent R).hom.toRingHom a =
      (laurentConstants R).hom.toRingHom r * (↑(laurentParameter R) : LaurentPolynomial R) ^ 2 := by
    change Polynomial.toLaurent a = LaurentPolynomial.C r * LaurentPolynomial.T 1 ^ 2
    simp only [a, map_mul, map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X]
  have ha₀ : (polynomialEvaluate R 0).hom.toRingHom a = 0 := by
    change (polynomialEvaluate R 0).hom a = 0
    simp [a, polynomialEvaluate, Polynomial.aevalTower]
  have hpointOne : pointHom f R (1 : Points A.X R) = 1 := (pointHom f R).map_one
  constructor
  · intro hp
    suffices h : HasLimit c p 1 by
      change HasLimit (c ≫ f) (pointHom f R p) 1
      rw [← hpointOne]
      exact hasLimit_postcompose f h
    let x : Points A.X (polynomialAlgebra R) := e.inv.app _ (upper a)
    refine ⟨x, ?_, ?_⟩
    · apply hinj (laurentAlgebra R)
      rw [hn, show e.hom.app _ x = upper a from hi _ _, map_transvection, ha]
      simp only [orbit, map_mul, map_inv, hc, hn, hp, map_transvection]
      exact (scalarDiagonal_conjugate_upper _ _).symm
    · apply hinj R
      rw [hn, show e.hom.app _ x = upper a from hi _ _, map_transvection, ha₀]
      exact (Matrix.SpecialLinearGroup.transvection_coeff_zero _).trans ((e.hom.app R).hom.map_one).symm
  · intro hp
    suffices h : HasLimit (oppositeCocharacter c) p 1 by
      have hpost := hasLimit_postcompose f h
      change HasLimit (oppositeCocharacter (c ≫ f)) (pointHom f R p) 1
      rw [← hpointOne]
      simpa only [oppositeCocharacter, Category.assoc] using hpost
    let x : Points A.X (polynomialAlgebra R) := e.inv.app _ (lower a)
    refine ⟨x, ?_, ?_⟩
    · apply hinj (laurentAlgebra R)
      rw [hn, show e.hom.app _ x = lower a from hi _ _, map_transvection, ha]
      simp only [orbit, map_mul, map_inv, opposite_point, hc, hn, hp, map_transvection]
      exact (scalarDiagonal_conjugate_lower _ _).symm
    · apply hinj R
      rw [hn, show e.hom.app _ x = lower a from hi _ _, map_transvection, ha₀]
      exact (Matrix.SpecialLinearGroup.transvection_coeff_zero _).trans ((e.hom.app R).hom.map_one).symm

end Contractions

section DeterminantOneGeometry

open CategoryTheory
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.StandardGroups (GLCoordinates SLCoordinates genericDeterminant
  determinantOneIdeal universalMatrix)
open LinearAlgebraicGroups.Specs.SymplecticDatumRankOneAndPinning (determinantOnePoints)

open private sl_coordinates_smooth diagonalAt diagonalAt_val det_diagonalAt
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
open private glCoordinates_ext quotient_det slEvaluation slEvaluation_entry universalGeneralLinear
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private standardRankOnePoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SymplecticDatumRankOneAndPinning

variable (k : Type u) [Field k]

private abbrev rankOneIndex := ULift.{u} (Fin 2)

private abbrev determinantOneGroup : AffineAlgebraicGroup k :=
  StandardGroups.specialLinearGroup k rankOneIndex

private def determinantOneGroupPoints :
    (groupPointsFunctor k).obj (determinantOneGroup k).val ≅ determinantOnePoints k :=
  StandardGroups.specialLinearGroupPointsIso k rankOneIndex ≪≫ standardRankOnePoints k

private theorem determinantOneGroup_smooth : Smooth (determinantOneGroup k).val.X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (SLCoordinates k rankOneIndex))))
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr (sl_coordinates_smooth (k := k) rankOneIndex))

private theorem splitDeterminantOneCoordinates_areDomain (K : Type u) [Field K] [Algebra k K] :
    IsDomain (K ⊗[k] SLCoordinates k rankOneIndex) := by
  classical
  let A := GLCoordinates k rankOneIndex
  let S := SLCoordinates k rankOneIndex
  let q : A →ₐ[k] S := Ideal.Quotient.mkₐ k (determinantOneIdeal k rankOneIndex)
  let M : Matrix.GeneralLinearGroup rankOneIndex A := universalGeneralLinear
  let t := Matrix.GeneralLinearGroup.det M
  let i : rankOneIndex := ⟨0⟩
  let D := diagonalAt i t⁻¹
  have hD : Matrix.GeneralLinearGroup.det (D * M) = 1 := by
    rw [map_mul, det_diagonalAt, inv_mul_cancel]
  let w : Matrix.SpecialLinearGroup rankOneIndex A := ⟨(D * M).val, congrArg Units.val hD⟩
  let l : S →ₐ[k] A := slEvaluation w
  have hq : q.comp l = AlgHom.id k S := by
    apply Ideal.Quotient.algHom_ext k
    apply glCoordinates_ext
    intro a b
    change q (l (q (universalMatrix k rankOneIndex a b))) = q (universalMatrix k rankOneIndex a b)
    rw [slEvaluation_entry]
    change q ((D.val * M.val) a b) = q (M.val a b)
    rw [diagonalAt_val, diagonal_mul, map_mul]
    have hqt : q (t : A) = 1 := quotient_det
    have hqi : q ((t⁻¹ : Aˣ) : A) = 1 := by
      change q t.inv = 1
      have hh := congrArg q t.val_inv
      simpa only [map_mul, hqt, one_mul, map_one] using hh
    by_cases ha : a = i <;> simp [ha, hqi]
  let P := MvPolynomial (rankOneIndex × rankOneIndex) k
  let d := genericDeterminant k rankOneIndex
  let e : K ⊗[k] P ≃ₐ[K] MvPolynomial (rankOneIndex × rankOneIndex) K :=
    MvPolynomial.algebraTensorAlgEquiv k K
  letI : IsDomain (K ⊗[k] P) := MulEquiv.isDomain _ e.toRingEquiv.toMulEquiv
  have hd : d ≠ 0 := by
    intro he
    let f := MvPolynomial.eval (fun ij : rankOneIndex × rankOneIndex =>
      if ij.1 = ij.2 then (1 : k) else 0)
    have h : ((Specs.StandardGroups.genericMatrix k rankOneIndex).map f).det = 0 := by
      exact (f.map_det _).symm.trans ((congrArg f he).trans (map_zero f))
    have hf : (Specs.StandardGroups.genericMatrix k rankOneIndex).map f = 1 := by
      ext i j
      simp [Specs.StandardGroups.genericMatrix, f, Matrix.one_apply]
    rw [hf, Matrix.det_one] at h
    exact one_ne_zero h
  have hd' : ((1 : K) ⊗ₜ[k] d) ≠ 0 := by
    intro he
    apply hd
    apply MvPolynomial.map_injective _ (algebraMap k K).injective
    have he' : e (1 ⊗ₜ[k] d) = MvPolynomial.map (algebraMap k K) d := by
      rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    rw [← he', he, map_zero, map_zero]
  let f : K ⊗[k] A ≃ₐ[K] Localization.Away ((1 : K) ⊗ₜ[k] d) :=
    IsLocalization.Away.tensorProductEquivTMulRight k K d A
  letI : IsDomain (Localization.Away ((1 : K) ⊗ₜ[k] d)) := Localization.Away.isDomain hd'
  letI : IsDomain (K ⊗[k] A) := MulEquiv.isDomain _ f.toRingEquiv.toMulEquiv
  let lK := Algebra.TensorProduct.map (AlgHom.id K K) l
  let qK := Algebra.TensorProduct.map (AlgHom.id K K) q
  have hK : qK.comp lK = AlgHom.id K (K ⊗[k] S) := by
    rw [← Algebra.TensorProduct.map_id_comp, hq, Algebra.TensorProduct.map_id]
  exact Function.Injective.isDomain lK (fun a b hab =>
    (DFunLike.congr_fun hK a).symm.trans ((congrArg qK hab).trans (DFunLike.congr_fun hK b)))

private theorem determinantOneGroup_geometricallyConnected :
    GeometricallyConnected (determinantOneGroup k).val.X.hom := by
  let A := SLCoordinates k rankOneIndex
  change GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} => ConnectedSpace X)).mpr
  intro K _ _
  letI : IsDomain (K ⊗[k] A) := splitDeterminantOneCoordinates_areDomain k K
  let h := (CommRingCat.isPushout_tensorProduct k K A).op.map Scheme.Spec
  exact (h.isoPullback.hom.homeomorph.connectedSpace_iff).mp
    (inferInstance : ConnectedSpace (Spec (CommRingCat.of (K ⊗[k] A))))

end DeterminantOneGeometry

section GaloisDescent

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair SpinModel)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
  (QuaternionHyperbolicPresentation spinVectorProjection)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionScalarCliffordLift
  (LiftsScalarPair scalarPairMatrix)
open LinearAlgebraicGroups.Specs.SymplecticDatumRankOneAndPinning (determinantOnePoints)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (tensorMap)
open _root_.Specs.RM03.CSA (isCentralSimple)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)

set_option backward.isDefEq.respectTransparency false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

open private extendedTest extendedBase includeTest galoisTest includeTest_galois extendMap
  includeTest_natural pointsInclusion_fixed tensorInclusion_fixed multiplyTest multiplyTest_include
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent

variable {I B : Type u} [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ}

private theorem matrixAt_naturality (Q : QuaternionHyperbolicPresentation D hB d)
    {R S : TestAlgebra F} (a : R ⟶ S) (x : R ⊗[F] ρ.fixedSubalgebra) :
    Q.matrixAt S (tensorMap ρ.fixedSubalgebra a.hom x) =
      (Q.matrixAt R x).map (tensorMap B a.hom) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    change Q.matrixAt S (a.hom r ⊗ₜ[F] x) = _
    simp only [Q.matrixAtFormula]
    ext i j
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    ext i j
    exact (map_add (tensorMap B a.hom) _ _).symm

private theorem spinVectorProjection_naturality (M : SpinModel G D)
    {R S : TestAlgebra F} (a : R ⟶ S) (p : Points G.val.X R) :
    spinVectorProjection M S (mapPoints a p) =
      Units.map (tensorMap ρ.fixedSubalgebra a.hom).toMonoidHom (spinVectorProjection M R p) := by
  change M.fullPoints S ((mapPoints a p) ≫ (M.projection ≫ M.inclusion).hom.hom) = _
  exact M.fullNatural R S a (p ≫ (M.projection ≫ M.inclusion).hom.hom)

private theorem scalarPairMatrix_naturality {R S : TestAlgebra F} (a : R ⟶ S)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    scalarPairMatrix (B := B) (d := d) S (Matrix.SpecialLinearGroup.map a.hom.toRingHom g) =
      (scalarPairMatrix R g).map (tensorMap B a.hom) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [scalarPairMatrix, Matrix.one_apply, apply_ite (tensorMap B a.hom)]
  rfl

open LinearAlgebraicGroups.Specs.StandardGroups (SLCoordinates)

/-- The split scalar lift descends from its value at the determinant-one
universal point. The comparison after descent applies to every test algebra. -/
private theorem scalarLift_descends [CharP F 2] [FiniteDimensional F K] [IsGalois F K]
    (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    (l : determinantOnePoints K ⟶ restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj G.val)
    (hl : ∀ (S : TestAlgebra K) (g : Matrix.SpecialLinearGroup (Fin 2) S),
      let R := (restrictTestAlgebra F K).obj S
      Q.matrixAt R (spinVectorProjection M R (l.app S g)).val = scalarPairMatrix R g) :
    let A := determinantOneGroup F
    let e := determinantOneGroupPoints F
    ∃ f : A.val ⟶ G.val, LiftsScalarPair M Q e f ∧
      ∀ (S : TestAlgebra K) (p : Points ((groupBaseChange F K).obj A.val).X S),
        baseChangePoint F K G.val.X S (p ≫ ((groupBaseChange F K).map f).hom.hom) =
          l.app S (e.hom.app _ (baseChangePoint F K A.val.X S p)) := by
  let A := determinantOneGroup F
  let e := determinantOneGroupPoints F
  let P := (groupPointsFunctor F).obj A.val
  let H := determinantOnePoints F
  let J := (groupPointsFunctor F).obj G.val
  let U : TestAlgebra F := CommAlgCat.of F (SLCoordinates F rankOneIndex)
  let p₀ : P.obj U := 𝟙 _
  let g₀ := e.hom.app U p₀
  let i (R : TestAlgebra F) := includeTest (K := K) R
  let z := l.app (extendedTest (K := K) U) (H.map (i U) g₀)
  have hfix (σ : Gal(K/F)) : J.map (galoisTest U σ) z = z := by
    let S := extendedBase (K := K) U
    let : IsDomain S := splitDeterminantOneCoordinates_areDomain F K
    apply spinVectorProjection_injective_of_reduced M S
    apply Units.ext
    apply (Q.matrixAt S).injective
    change Q.matrixAt S (spinVectorProjection M S (mapPoints (galoisTest U σ) z)).val = _
    rw [spinVectorProjection_naturality, Units.coe_map]
    let b := galoisTest U σ
    change Q.matrixAt S (tensorMap ρ.fixedSubalgebra b.hom (spinVectorProjection M S z).val) = _
    rw [matrixAt_naturality Q b]
    have hv : Q.matrixAt S (spinVectorProjection M S z).val = scalarPairMatrix S (H.map (i U) g₀) :=
      hl (extendedTest (K := K) U) _
    rw [hv, ← scalarPairMatrix_naturality]
    congr 1
    exact ConcreteCategory.congr_hom
      ((H.map_comp (i U) (galoisTest U σ)).symm.trans (congrArg H.map (includeTest_galois U σ))) g₀
  obtain ⟨z₀, hz₀⟩ := ((pointsInclusion_fixed (K := K) G U).2 z).mpr hfix
  have hcomp (L : TestAlgebra F ⥤ GrpCat.{u}) {R S : TestAlgebra F} (a : R ⟶ S)
      (x : L.obj R) : L.map (i S) (L.map a x) =
        L.map ((restrictTestAlgebra F K).map (extendMap (K := K) a)) (L.map (i R) x) :=
    ConcreteCategory.congr_hom
      (((L.map_comp a _).symm.trans (congrArg L.map (includeTest_natural (K := K) a))).trans
        (L.map_comp _ _)) x
  have hex (R : TestAlgebra F) (g : H.obj R) :
      ∃ y : J.obj R, J.map (i R) y = l.app (extendedTest (K := K) R) (H.map (i R) g) := by
    let p := e.inv.app R g
    let a : U ⟶ R := ((algSpec.fullyFaithful (R := CommRingCat.of F)).preimage
      (show (testSpec F).obj (op R) ⟶ (testSpec F).obj (op U) from p)).unop
    have ha : P.map a p₀ = p := by
      change (testSpec F).map a.op ≫ 𝟙 _ = p
      rw [Category.comp_id]
      exact (algSpec.fullyFaithful (R := CommRingCat.of F)).map_preimage _
    have hg : H.map a g₀ = g := by
      have h := ConcreteCategory.congr_hom (e.hom.naturality a) p₀
      change e.hom.app R (P.map a p₀) = H.map a g₀ at h
      rw [ha] at h
      exact h.symm.trans (congrArg (fun m => m.app R g) e.inv_hom_id)
    refine ⟨J.map a z₀, ?_⟩
    rw [hcomp J a, hz₀, ← hg, hcomp H a]
    exact (ConcreteCategory.congr_hom (l.naturality (extendMap (K := K) a)) _).symm
  let m (R : TestAlgebra F) : H.obj R →* J.obj R :=
    { toFun := fun g => (hex R g).choose
      map_one' := (pointsInclusion_fixed (K := K) G R).1 (by
        change J.map (i R) ((hex R 1).choose) = J.map (i R) 1
        rw [(hex R 1).choose_spec, map_one, map_one, map_one])
      map_mul' := fun x y => (pointsInclusion_fixed (K := K) G R).1 (by
        change J.map (i R) ((hex R (x * y)).choose) =
          J.map (i R) ((hex R x).choose * (hex R y).choose)
        rw [(hex R (x * y)).choose_spec, map_mul, map_mul, map_mul,
          (hex R x).choose_spec, (hex R y).choose_spec]) }
  have hm (R : TestAlgebra F) (g : H.obj R) :
      J.map (i R) (m R g) = l.app (extendedTest (K := K) R) (H.map (i R) g) :=
    (hex R g).choose_spec
  let n : H ⟶ J :=
    { app := fun R => GrpCat.ofHom (m R)
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro g
        apply (pointsInclusion_fixed (K := K) G S).1
        change J.map (i S) (m S (H.map a g)) = J.map (i S) (J.map a (m R g))
        rw [hm, hcomp H a, hcomp J a, hm]
        exact ConcreteCategory.congr_hom (l.naturality (extendMap (K := K) a)) _ }
  let f := (A.groupHomEquiv G).symm (e.hom ≫ n)
  have hf (R : TestAlgebra F) (p : P.obj R) : p ≫ f.hom.hom = m R (e.hom.app R p) :=
    ConcreteCategory.congr_hom (congrArg (fun a => a.app R)
      ((A.groupHomEquiv G).apply_symm_apply (e.hom ≫ n))) p
  refine ⟨f, ?_, ?_⟩
  · intro R p
    apply Matrix.map_injective (tensorInclusion_fixed (K := K) (A := B) R).1
    change (Q.matrixAt R (spinVectorProjection M R (p ≫ f.hom.hom)).val).map
      (tensorMap B (i R).hom) = (scalarPairMatrix R (e.hom.app R p)).map (tensorMap B (i R).hom)
    rw [← matrixAt_naturality, ← scalarPairMatrix_naturality]
    have hp := congrArg Units.val (spinVectorProjection_naturality M (i R) (p ≫ f.hom.hom))
    change (spinVectorProjection M _ (J.map (i R) (p ≫ f.hom.hom))).val =
      tensorMap ρ.fixedSubalgebra (i R).hom (spinVectorProjection M R (p ≫ f.hom.hom)).val at hp
    rw [← hp, hf]
    change Q.matrixAt (extendedBase (K := K) R)
      (spinVectorProjection M _ (J.map (i R) (m R (e.hom.app R p)))).val = _
    rw [hm]
    exact hl (extendedTest (K := K) R) _
  · intro S p
    let R := (restrictTestAlgebra F K).obj S
    let a := (restrictTestAlgebra F K).map (multiplyTest (k := F) S)
    have hra (L : TestAlgebra F ⥤ GrpCat.{u}) (x : L.obj R) :
        L.map a (L.map (i R) x) = x :=
      ConcreteCategory.congr_hom
        (((L.map_comp (i R) a).symm.trans (congrArg L.map (multiplyTest_include S))).trans
          (L.map_id _)) x
    change baseChangePoint F K G.val.X S (p ≫ (baseChange F K).map f.hom.hom) = _
    rw [baseChangePointsSchemeNaturality F K f.hom.hom S p, hf]
    let g := e.hom.app R (baseChangePoint F K A.val.X S p)
    change m R g = l.app S g
    rw [← hra J (m R g), hm]
    exact (ConcreteCategory.congr_hom (l.naturality (multiplyTest (k := F) S))
      (H.map (i R) g)).symm.trans (congrArg (l.app S) (hra H g))

end GaloisDescent

section SplitQuaternionCoordinates

open CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair SpinModel orthogonalMatrices hyperbolicGram adjoint)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
  (QuaternionHyperbolicPresentation QuaternionPairIndex spinVectorProjection SpinScaleCover
    quaternionScale diagonalQuaternionScale inverseConjugateUnit quaternionHyperbolicGram)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionScalarCliffordLift
  (scalarPairMatrix scalarDiagonal)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (antiValue extendAnti dagger)
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)

set_option backward.isDefEq.respectTransparency false

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ}

local notation "𝓐" => ρ.fixedSubalgebra

private def pairEntry (Q : QuaternionHyperbolicPresentation D hB d)
    (i j : Fin 2) (b : B) : 𝓐 :=
  Q.matrixModel.symm (Matrix.single (Sum.inl i) (Sum.inl j) b)

private def pairMatrixUnit (Q : QuaternionHyperbolicPresentation D hB d)
    (i j : Fin 2) : Matrix (I ⊕ I) (I ⊕ I) K := (pairEntry Q i j 1).val

private theorem matrixAt_pairEntry (Q : QuaternionHyperbolicPresentation D hB d)
    (R : TestAlgebra F) (r : R) (i j : Fin 2) (b : B) :
    Q.matrixAt R (r ⊗ₜ[F] pairEntry Q i j b) =
      Matrix.single (Sum.inl i) (Sum.inl j) (r ⊗ₜ[F] b) := by
  rw [Q.matrixAtFormula, pairEntry, AlgEquiv.apply_symm_apply]
  ext a c
  simp only [Matrix.map_apply, Matrix.single_apply]
  split <;> simp_all

private theorem pairMatrixUnit_mul (Q : QuaternionHyperbolicPresentation D hB d)
    (i j k l : Fin 2) :
    pairMatrixUnit Q i j * pairMatrixUnit Q k l = if j = k then pairMatrixUnit Q i l else 0 := by
  classical
  have h : pairEntry Q i j 1 * pairEntry Q k l 1 =
      if j = k then pairEntry Q i l 1 else 0 := by
    apply Q.matrixModel.injective
    simp only [map_mul, pairEntry, AlgEquiv.apply_symm_apply]
    by_cases h : j = k
    · subst k
      simp [Matrix.single_mul_single_same]
    · rw [if_neg h, map_zero, Matrix.single_mul_single_of_ne _ _ _ _ (fun e => h (Sum.inl.inj e))]
  simpa only [pairMatrixUnit, Subalgebra.coe_mul, Subalgebra.coe_zero,
    apply_ite (fun x : 𝓐 => x.val)] using congrArg (fun x : 𝓐 => x.val) h

private theorem scalarPairMatrix_preimage (Q : QuaternionHyperbolicPresentation D hB d)
    (R : TestAlgebra F) (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    (Q.matrixAt R).symm (scalarPairMatrix R g) =
      1 + ((g.val 0 0 - 1) ⊗ₜ[F] pairEntry Q 0 0 1) +
        (g.val 0 1 ⊗ₜ[F] pairEntry Q 0 1 1) + (g.val 1 0 ⊗ₜ[F] pairEntry Q 1 0 1) +
        ((g.val 1 1 - 1) ⊗ₜ[F] pairEntry Q 1 1 1) := by
  apply (Q.matrixAt R).injective
  simp only [AlgEquiv.apply_symm_apply, map_add, map_one, matrixAt_pairEntry]
  ext (i | i) (j | j)
  · fin_cases i <;> fin_cases j <;>
      simp [scalarPairMatrix, Matrix.single_apply, Matrix.one_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.one_def,
        TensorProduct.sub_tmul]
  · simp [scalarPairMatrix, Matrix.single_apply, Matrix.one_apply]
  · simp [scalarPairMatrix, Matrix.single_apply, Matrix.one_apply]
  · simp [scalarPairMatrix, Matrix.single_apply, Matrix.one_apply]

private def splitMatrix (M : SpinModel G D) (S : TestAlgebra K) :
    let R := (restrictTestAlgebra F K).obj S
    (R ⊗[F] 𝓐) ≃ₐ[S] Matrix (I ⊕ I) (I ⊕ I) S :=
  (M.matrixComparison S).choose

private theorem splitMatrix_tmul (M : SpinModel G D) (S : TestAlgebra K) (s : S) (a : 𝓐) :
    splitMatrix M S (s ⊗ₜ[F] a) = s • a.val.map (algebraMap K S) :=
  (M.matrixComparison S).choose_spec.1 s a

private theorem splitMatrix_scalarPair (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (S : TestAlgebra K)
    (g : Matrix.SpecialLinearGroup (Fin 2) S) :
    let R := (restrictTestAlgebra F K).obj S
    splitMatrix M S ((Q.matrixAt R).symm (scalarPairMatrix R g)) =
      1 + (g.val 0 0 - 1) • (pairMatrixUnit Q 0 0).map (algebraMap K S) +
        g.val 0 1 • (pairMatrixUnit Q 0 1).map (algebraMap K S) +
        g.val 1 0 • (pairMatrixUnit Q 1 0).map (algebraMap K S) +
        (g.val 1 1 - 1) • (pairMatrixUnit Q 1 1).map (algebraMap K S) := by
  let R := (restrictTestAlgebra F K).obj S
  change splitMatrix M S ((Q.matrixAt R).symm (scalarPairMatrix R g)) = _
  rw [scalarPairMatrix_preimage Q R g, map_add, map_add, map_add, map_add, map_one]
  change 1 + splitMatrix M S ((g.val 0 0 - 1) ⊗ₜ[F] pairEntry Q 0 0 1) +
    splitMatrix M S (g.val 0 1 ⊗ₜ[F] pairEntry Q 0 1 1) +
    splitMatrix M S (g.val 1 0 ⊗ₜ[F] pairEntry Q 1 0 1) +
    splitMatrix M S ((g.val 1 1 - 1) ⊗ₜ[F] pairEntry Q 1 1 1) = _
  rw [splitMatrix_tmul M S, splitMatrix_tmul M S, splitMatrix_tmul M S, splitMatrix_tmul M S]
  rfl

private theorem splitMatrix_scalarDiagonal (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (S : TestAlgebra K) (s : Sˣ) :
    let R := (restrictTestAlgebra F K).obj S
    splitMatrix M S ((Q.matrixAt R).symm (scalarPairMatrix R (scalarDiagonal s))) =
      1 + ((s : S) - 1) • (pairMatrixUnit Q 0 0).map (algebraMap K S) +
        ((↑s⁻¹ : S) - 1) • (pairMatrixUnit Q 1 1).map (algebraMap K S) := by
  have h := splitMatrix_scalarPair M Q S (scalarDiagonal s)
  simpa [scalarDiagonal] using h

private theorem splitMatrix_fullPoint (M : SpinModel G D) (S : TestAlgebra K)
    (p : Points ((groupBaseChange F K).obj M.full.val).X S) :
    splitMatrix M S (M.fullPoints _ (baseChangePoint F K M.full.val.X S p)).val =
      (M.splitCover.orthogonal.points S (p ≫ M.splitFull.hom.hom.hom)).val.val :=
  (M.matrixComparison S).choose_spec.2 p

set_option maxHeartbeats 450000 in
private theorem splitMatrix_spinPoint (M : SpinModel G D) (S : TestAlgebra K)
    (p : Points ((groupBaseChange F K).obj G.val).X S) :
    splitMatrix M S (spinVectorProjection M _ (baseChangePoint F K G.val.X S p)).val =
      (M.splitCover.orthogonal.points S (p ≫ M.splitSource.hom.hom.hom ≫
        (M.splitCover.projection ≫ M.splitCover.inclusion).hom.hom)).val.val := by
  let k := groupBaseChange F K
  let m := M.projection ≫ M.inclusion
  change splitMatrix M S (M.fullPoints _ (baseChangePoint F K G.val.X S p ≫ m.hom.hom)).val = _
  have h : baseChangePoint F K M.full.val.X S (p ≫ (k.map m).hom.hom) =
      baseChangePoint F K G.val.X S p ≫ m.hom.hom :=
    baseChangePointsSchemeNaturality F K m.hom.hom S p
  rw [← h, splitMatrix_fullPoint, Category.assoc]
  have hc : k.map m ≫ M.splitFull.hom = M.splitSource.hom ≫
      (M.splitCover.projection ≫ M.splitCover.inclusion) := by
    change (groupBaseChange F K).map (M.projection ≫ M.inclusion) ≫ M.splitFull.hom = _
    rw [Functor.map_comp, Category.assoc, M.inclusionComparison, ← Category.assoc,
      M.projectionComparison, Category.assoc]
  exact congrArg (fun a => (M.splitCover.orthogonal.points S (p ≫ a.hom.hom)).val.val) hc

/-- The corner of a split full endomorphism algebra is the endomorphism
algebra of the image of the corresponding idempotent. -/
private theorem finrank_matrixCorner {k V C : Type u} {J : Type v} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [Ring C] [Algebra k C] [Fintype J] [DecidableEq J]
    (e : Matrix J J C ≃ₐ[k] Module.End k V) (j : J) :
    Module.finrank k C = (Module.finrank k (LinearMap.range (e (Matrix.single j j 1)))) ^ 2 := by
  let p := e (Matrix.single j j 1)
  let W := LinearMap.range p
  have hp : p * p = p := by rw [← map_mul]; simp [p]
  let pr : V →ₗ[k] W := p.rangeRestrict
  have hpr (w : W) : pr w.val = w := by
    obtain ⟨v, hv⟩ := w.property
    apply Subtype.ext
    change p w.val = w.val
    rw [← hv]
    exact DFunLike.congr_fun hp v
  let a : C →ₗ[k] Module.End k V := e.toLinearMap.comp (Matrix.singleLinearMap k j j)
  let b : Module.End k W →ₗ[k] Module.End k V :=
    { toFun := fun t => W.subtype.comp (t.comp pr)
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  have ha : Function.Injective a := by
    intro x y h
    have h' := e.injective h
    simpa using congrFun (congrFun h' j) j
  have hb : Function.Injective b := by
    intro f g h
    ext w
    have h' := DFunLike.congr_fun h w.val
    change (f (pr w.val)).val = (g (pr w.val)).val at h'
    simpa only [hpr] using h'
  have hcorner (t : Module.End k V) : t ∈ a.range ↔ p * t * p = t := by
    constructor
    · rintro ⟨x, rfl⟩
      change e (Matrix.single j j 1) * e (Matrix.single j j x) * e (Matrix.single j j 1) = _
      rw [← map_mul, ← map_mul, Matrix.single_mul_mul_single, one_mul, mul_one]
      simp [a]
    · intro ht
      refine ⟨(e.symm t) j j, ?_⟩
      change e (Matrix.single j j ((e.symm t) j j)) = t
      rw [← one_mul ((e.symm t) j j), ← mul_one (1 * (e.symm t) j j),
        ← Matrix.single_mul_mul_single, map_mul, map_mul, e.apply_symm_apply]
      exact ht
  have hba : b.range = a.range := by
    ext t
    rw [hcorner]
    constructor
    · rintro ⟨s, rfl⟩
      ext v
      change p (s (pr (p v))).val = (s (pr v)).val
      rw [show pr (p v) = pr v from hpr (pr v)]
      exact congrArg Subtype.val (hpr (s (pr v)))
    · intro ht
      have ht' (v : V) : p (t (p v)) = t v := DFunLike.congr_fun ht v
      refine ⟨(t.comp W.subtype).codRestrict W (fun w => ?_), ?_⟩
      · exact ⟨t (p w.val), ht' w.val⟩
      · ext v
        change t (p v) = t v
        have hh : p (p v) = p v := DFunLike.congr_fun hp v
        rw [← ht' (p v), hh, ht']
  rw [← LinearMap.finrank_range_of_inj ha, ← hba, LinearMap.finrank_range_of_inj hb,
    Module.finrank_linearMap, pow_two]

private theorem pairMatrixUnit_rank (Q : QuaternionHyperbolicPresentation D hB d)
    (hdegree : degree F B = 2) :
    Module.finrank K (LinearMap.range (Matrix.mulVecLin (pairMatrixUnit Q 0 0))) = 2 := by
  let R := CommAlgCat.of F K
  let e : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (K ⊗[F] B) ≃ₐ[K]
      Module.End K (I ⊕ I → K) := ((Q.matrixAt R).symm.trans D.splitting).trans Matrix.toLinAlgEquiv'
  let j : QuaternionPairIndex d := Sum.inl 0
  have hp : e (Matrix.single j j 1) = Matrix.mulVecLin (pairMatrixUnit Q 0 0) := by
    have h := matrixAt_pairEntry Q R 1 0 0 1
    change Q.matrixAt R (1 ⊗ₜ[F] pairEntry Q 0 0 1) = Matrix.single j j 1 at h
    change Matrix.toLinAlgEquiv' (D.splitting ((Q.matrixAt R).symm (Matrix.single j j 1))) = _
    rw [← h, AlgEquiv.symm_apply_apply, D.splittingFormula, one_smul]
    rfl
  have h := finrank_matrixCorner e j
  rw [hp, Module.finrank_baseChange, _root_.RM03.CSA.finrank_eq_degree_sq hB] at h
  change (degree F B) ^ 2 = _ at h
  rw [hdegree] at h
  have hpow := Nat.pow_left_injective (show 2 ≠ 0 by decide) h
  exact hpow.symm

private theorem two_eq_zero_of_algebra [CharP F 2] (C : Type*) [Ring C] [Algebra F C] :
    (2 : C) = 0 := by
  rw [← map_ofNat (algebraMap F C) 2, CharP.ofNat_eq_zero F 2, map_zero]

private theorem neg_one_of_two_zero {C : Type*} [Ring C] (h : (2 : C) = 0) : (-1 : C) = 1 :=
  neg_eq_of_add_eq_zero_left (by simpa only [one_add_one_eq_two] using h)

private theorem polar_hyperbolicGram {R : Type u} [CommRing R] (h : (2 : R) = 0) (x y : I ⊕ I → R) :
    QuadraticMap.polar (hyperbolicForm I R) x y = x ⬝ᵥ (hyperbolicGram I R *ᵥ y) := by
  have hf := LinearAlgebraicGroups.Arithmetic.OddSpinModels.hyperbolicPolar I R h
  change (hyperbolicForm I R).polarBilin = Matrix.toLinearMap₂' R (Matrix.J I R) at hf
  change (hyperbolicForm I R).polarBilin x y = _
  rw [hf, Matrix.toLinearMap₂'_apply']
  congr 2
  ext (a | a) (b | b) <;> simp [Matrix.J, hyperbolicGram, Matrix.one_apply]
  split <;> simp [neg_one_of_two_zero h, *]

private theorem hyperbolicGram_sq (R : Type u) [CommRing R] :
    hyperbolicGram I R * hyperbolicGram I R = 1 := by
  simp [hyperbolicGram, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

private theorem hyperbolic_adjoint (h₂ : (2 : K) = 0) (a : Matrix (I ⊕ I) (I ⊕ I) K)
    (x y : I ⊕ I → K) :
    QuadraticMap.polar (hyperbolicForm I K) (a *ᵥ x) y =
      QuadraticMap.polar (hyperbolicForm I K) x (adjoint (hyperbolicGram I K) a *ᵥ y) := by
  rw [polar_hyperbolicGram h₂, polar_hyperbolicGram h₂]
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, adjoint, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hyperbolicGram_sq, one_mul]

private theorem hyperbolic_nondegenerate (h₂ : (2 : K) = 0) :
    ∀ (x : I ⊕ I → K), x ≠ 0 → ∃ y, QuadraticMap.polar (hyperbolicForm I K) x y ≠ 0 := by
  intro x hx
  by_contra! h
  apply hx
  funext j
  have he := h (hyperbolicGram I K *ᵥ Pi.single j 1)
  rw [polar_hyperbolicGram h₂, Matrix.mulVec_mulVec,
    hyperbolicGram_sq, Matrix.one_mulVec, dotProduct_single_one] at he
  exact he

private def standardFrame (h₂ : (2 : K) = 0) (i j : I) (hij : i ≠ j) :
    HyperbolicFrame (hyperbolicForm I K) := by
  let x : I ⊕ I → K := Pi.single (Sum.inl i) 1
  let y : I ⊕ I → K := Pi.single (Sum.inl j) 1
  let u : I ⊕ I → K := Pi.single (Sum.inr i) 1
  let v : I ⊕ I → K := Pi.single (Sum.inr j) 1
  have hp (a b : I ⊕ I) : QuadraticMap.polar (hyperbolicForm I K)
      (Pi.single a 1) (Pi.single b 1) = hyperbolicGram I K a b := by
    rw [polar_hyperbolicGram h₂, Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply]
  refine ⟨x, y, u, v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | exact LinearAlgebraicGroups.Arithmetic.OddSpinModels.hyperbolicForm_standardVector _
  | simp [x, y, u, v, hp, hyperbolicGram, Matrix.one_apply, hij, Ne.symm hij]

private def pairScalarUnit (R : TestAlgebra F) (s : Rˣ) : (R ⊗[F] B)ˣ :=
  Units.map (algebraMap R (R ⊗[F] B)).toMonoidHom s

private theorem quaternionScale_scalar (Q : QuaternionHyperbolicPresentation D hB d)
    (R : TestAlgebra F) (s : Rˣ) :
    Q.matrixAt R (quaternionScale Q R (pairScalarUnit R s)).val =
      scalarPairMatrix R (scalarDiagonal s) := by
  have hinv : inverseConjugateUnit (extendAnti Q.conjugation.anti R).toMonoidHom
      (pairScalarUnit R s) = pairScalarUnit R s⁻¹ := by
    change (Units.opEquiv (Units.map (extendAnti Q.conjugation.anti R).toMonoidHom
      (pairScalarUnit R s))).unop⁻¹ = (pairScalarUnit R s)⁻¹
    apply congrArg Inv.inv
    apply Units.ext
    change MulOpposite.unop (extendAnti Q.conjugation.anti R (algebraMap R (R ⊗[F] B) (s : R))) = _
    rw [AlgEquiv.commutes]
    rfl
  change (Q.matrixAt R) ((Q.matrixAt R).symm _) = _
  rw [AlgEquiv.apply_symm_apply]
  let diag : QuaternionPairIndex d → (R ⊗[F] B)ˣ :=
    Sum.elim ![pairScalarUnit R s,
      inverseConjugateUnit (extendAnti Q.conjugation.anti R).toMonoidHom (pairScalarUnit R s)]
      (fun _ => 1)
  change Matrix.diagonal (fun j => (diag j : R ⊗[F] B)) = _
  dsimp only [diag]
  rw [hinv]
  ext (i | i) (j | j)
  · fin_cases i <;> fin_cases j <;> simp [scalarPairMatrix, scalarDiagonal, pairScalarUnit]
  · simp [scalarPairMatrix]
  · simp [scalarPairMatrix]
  · simp [scalarPairMatrix, Matrix.diagonal_apply, Matrix.one_apply]

private theorem splitScalarDiagonal_isometry [FiniteDimensional F K] [IsGalois F K]
    (cover : SpinScaleCover.{u}) (M : SpinModel G D) (hrank : 4 ≤ Fintype.card I)
    (hdegree : degree F B = 2) (Q : QuaternionHyperbolicPresentation D hB d)
    (S : TestAlgebra K) (s : Sˣ) (x : I ⊕ I → S) :
    let R := (restrictTestAlgebra F K).obj S
    hyperbolicForm I S (splitMatrix M S ((Q.matrixAt R).symm (scalarPairMatrix R (scalarDiagonal s))) *ᵥ x) =
      hyperbolicForm I S x := by
  let R := (restrictTestAlgebra F K).obj S
  let : Module.Finite F B := hB.2.2
  let b := (Module.finBasis F B).reindex (Equiv.ulift.{u}.symm)
  obtain ⟨a, ha⟩ := (cover M hrank hB hdegree d Q b).1 R (pairScalarUnit R s)
  let p := (baseChangePointsEquiv K M.full.val.X S).symm (a ≫ M.inclusion.hom.hom)
  have hp : baseChangePoint F K M.full.val.X S p = a ≫ M.inclusion.hom.hom :=
    (baseChangePointsEquiv K M.full.val.X S).apply_symm_apply _
  have he := splitMatrix_fullPoint M S p
  rw [hp, ha] at he
  have hq : (Q.matrixAt R).symm (scalarPairMatrix R (scalarDiagonal s)) =
      (quaternionScale Q R (pairScalarUnit R s)).val :=
    (congrArg (Q.matrixAt R).symm (quaternionScale_scalar Q R s).symm).trans
      ((Q.matrixAt R).symm_apply_apply _)
  change hyperbolicForm I S (splitMatrix M S ((Q.matrixAt R).symm
    (scalarPairMatrix R (scalarDiagonal s))) *ᵥ x) = _
  rw [hq, he]
  exact (M.splitCover.orthogonal.points S (p ≫ M.splitFull.hom.hom.hom)).property x

open LinearAlgebraicGroups.CocharacterDynamics (laurentParameter laurentAlgebra)

private theorem laurentParameter_sq_ne_one {k : Type u} [Field k] :
    (↑(laurentParameter (CommAlgCat.of k k)) : LaurentPolynomial k) ^ 2 ≠ 1 := by
  intro he
  change (LaurentPolynomial.T 1 : LaurentPolynomial k) ^ 2 = LaurentPolynomial.T 0 at he
  have hh := congrArg (fun f : LaurentPolynomial k => f.coeff 2) he
  simp only [LaurentPolynomial.T_pow, LaurentPolynomial.T_apply] at hh
  norm_num at hh

set_option maxHeartbeats 450000 in
private theorem quaternionPair_isotropic_of_scale [FiniteDimensional F K] [IsGalois F K]
    (cover : SpinScaleCover.{u}) (M : SpinModel G D) (hrank : 4 ≤ Fintype.card I)
    (hdegree : degree F B = 2) (Q : QuaternionHyperbolicPresentation D hB d)
    (S : TestAlgebra K) [IsDomain S] (s : Sˣ) (hs₂ : (s : S) ^ 2 ≠ 1)
    (i : Fin 2) (x : I ⊕ I → K) : hyperbolicForm I K (pairMatrixUnit Q i i *ᵥ x) = 0 := by
  let R := (restrictTestAlgebra F K).obj S
  let a := algebraMap K S
  let p := pairMatrixUnit Q i i *ᵥ x
  let pS : I ⊕ I → S := a ∘ p
  have hP (j : Fin 2) : (pairMatrixUnit Q j j).map a *ᵥ pS = if j = i then pS else 0 := by
    have h (j : Fin 2) : pairMatrixUnit Q j j *ᵥ p = if j = i then p else 0 := by
      dsimp only [p]
      rw [Matrix.mulVec_mulVec, pairMatrixUnit_mul]
      by_cases hj : j = i
      · subst j
        simp only [eq_self, ite_true]
      · simp only [ite_eq_right hj, Matrix.zero_mulVec]
    have he : (pairMatrixUnit Q j j).map a *ᵥ pS = a ∘ (pairMatrixUnit Q j j *ᵥ p) :=
      funext fun k => (a.map_mulVec (pairMatrixUnit Q j j) p k).symm
    rw [he, h j]
    split
    · rfl
    · funext k
      simp only [Function.comp_apply, Pi.zero_apply, map_zero]
  let t : Sˣ := if i = 0 then s else s⁻¹
  have hT : splitMatrix M S ((Q.matrixAt R).symm (scalarPairMatrix R (scalarDiagonal t))) *ᵥ pS =
      (s : S) • pS := by
    have hD := splitMatrix_scalarDiagonal M Q S t
    change splitMatrix M S ((Q.matrixAt R).symm (scalarPairMatrix R (scalarDiagonal t))) = _ at hD
    rw [hD, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Matrix.smul_mulVec, hP 0, hP 1]
    have hs : pS + ((s : S) - 1) • pS = (s : S) • pS := by
      rw [sub_smul, one_smul, add_comm pS, sub_add_cancel]
    by_cases hi : i = 0
    · have hi' : (1 : Fin 2) ≠ i := by rw [hi]; decide
      simpa only [t, ite_eq_left hi, ite_eq_left hi.symm, ite_eq_right hi', smul_zero, add_zero] using hs
    · have hi' : i = 1 := Fin.eq_one_of_ne_zero i hi
      have h0 : (0 : Fin 2) ≠ i := hi ∘ Eq.symm
      simpa only [t, ite_eq_right hi, ite_eq_right h0, ite_eq_left hi'.symm, inv_inv,
        smul_zero, add_zero] using hs
  have hq := splitScalarDiagonal_isometry cover M hrank hdegree Q S t pS
  change hyperbolicForm I S
    (splitMatrix M S ((Q.matrixAt R).symm (scalarPairMatrix R (scalarDiagonal t))) *ᵥ pS) = _ at hq
  rw [hT, QuadraticMap.map_smul, smul_eq_mul, ← pow_two] at hq
  have hq' : ((s : S) ^ 2 - 1) * hyperbolicForm I S pS = 0 := by
    rw [sub_mul, one_mul, hq, sub_self]
  have hpS := (mul_eq_zero.mp hq').resolve_left
    (fun hs => hs₂ (sub_eq_zero.mp hs))
  apply a.injective
  rw [map_zero]
  simpa only [LinearAlgebraicGroups.Arithmetic.OddSpinModels.hyperbolicForm_apply,
    pS, Function.comp_apply, map_sum, map_mul] using hpS

private theorem quaternionPair_isotropic [FiniteDimensional F K] [IsGalois F K]
    (cover : SpinScaleCover.{u}) (M : SpinModel G D) (hrank : 4 ≤ Fintype.card I)
    (hdegree : degree F B = 2) (Q : QuaternionHyperbolicPresentation D hB d)
    (i : Fin 2) (x : I ⊕ I → K) : hyperbolicForm I K (pairMatrixUnit Q i i *ᵥ x) = 0 :=
  quaternionPair_isotropic_of_scale cover M hrank hdegree Q (laurentAlgebra (CommAlgCat.of K K))
    (laurentParameter (CommAlgCat.of K K)) laurentParameter_sq_ne_one i x

private abbrev flipPair (i : Fin 2) : Fin 2 := 1 - i

private theorem pairEntry_involution [CharP F 2] (Q : QuaternionHyperbolicPresentation D hB d)
    (i j : Fin 2) (b : B) :
    D.involution.toLinearMap (pairEntry Q i j b) =
      pairEntry Q (flipPair j) (flipPair i) (antiValue Q.conjugation.anti b) := by
  let H₀ : Matrix (Fin 2) (Fin 2) B := !![0, 1; -1, 0]
  let H := quaternionHyperbolicGram Q.complement.val
  let t := Q.conjugation.anti
  let N := Matrix.single i j b
  let P := Matrix.single (flipPair j) (flipPair i) (antiValue t b)
  have hn : (-1 : B) = 1 := neg_one_of_two_zero (two_eq_zero_of_algebra (F := F) B)
  have hs (i j : Fin 2) (c : B) : Q.matrixModel (pairEntry Q i j c) =
      Matrix.fromBlocks (Matrix.single i j c) 0 0 0 := by
    rw [pairEntry, AlgEquiv.apply_symm_apply]
    ext (a | a) (b' | b') <;> simp [Matrix.single_apply]
  have had : dagger t (Matrix.fromBlocks N 0 0 (0 : Matrix (Fin d) (Fin d) B)) =
      Matrix.fromBlocks (dagger t N) 0 0 0 := by
    ext (a | a) (b' | b') <;> simp [dagger, antiValue]
  have hP : H₀ * P = dagger t N * H₀ := by
    ext a c
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases c <;>
      simp [H₀, P, N, dagger, antiValue, Matrix.mul_apply, Fin.sum_univ_two, hn, flipPair]
  have h₀ : H₀ * H₀ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [H₀, Matrix.mul_apply, Fin.sum_univ_two, hn]
  let H' := Matrix.fromBlocks H₀ 0 0 Q.complement.inv
  have hH : H' * H = 1 := by
    change Matrix.fromBlocks H₀ 0 0 Q.complement.inv *
      Matrix.fromBlocks H₀ 0 0 Q.complement.val = _
    rw [Matrix.fromBlocks_multiply]
    simp [h₀, Q.complement.inv_val, Matrix.fromBlocks_one]
  have he := Q.adjoint (pairEntry Q i j b)
  rw [hs, had] at he
  have he' : H * Q.matrixModel (D.involution.toLinearMap (pairEntry Q i j b)) =
      H * Q.matrixModel (pairEntry Q (flipPair j) (flipPair i) (antiValue t b)) := by
    rw [show H * Q.matrixModel _ = _ from he, hs]
    change Matrix.fromBlocks (dagger t N) 0 0 (0 : Matrix (Fin d) (Fin d) B) *
      Matrix.fromBlocks H₀ 0 0 Q.complement.val =
        Matrix.fromBlocks H₀ 0 0 Q.complement.val * Matrix.fromBlocks P 0 0 0
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hP]
  apply Q.matrixModel.injective
  have hh := congrArg (H' * ·) he'
  simpa only [← mul_assoc, hH, one_mul] using hh

private theorem pairEntry_splitAdjoint [CharP F 2] (Q : QuaternionHyperbolicPresentation D hB d)
    (i j : Fin 2) (b : B) :
    adjoint (hyperbolicGram I K) (pairEntry Q i j b).val =
      (pairEntry Q (flipPair j) (flipPair i) (antiValue Q.conjugation.anti b)).val := by
  rw [← D.involutionFormula, pairEntry_involution]

private theorem pairMatrixUnit_adjoint [CharP F 2] (Q : QuaternionHyperbolicPresentation D hB d)
    (i j : Fin 2) : adjoint (hyperbolicGram I K) (pairMatrixUnit Q i j) =
      pairMatrixUnit Q (flipPair j) (flipPair i) := by
  rw [pairMatrixUnit, pairEntry_splitAdjoint]
  simp only [antiValue, map_one, MulOpposite.unop_one, pairMatrixUnit]

private theorem quaternionLower_alternating [CharP F 2] (Q : QuaternionHyperbolicPresentation D hB d)
    (hdegree : degree F B = 2) (x : I ⊕ I → K) :
    QuadraticMap.polar (hyperbolicForm I K) x (pairMatrixUnit Q 1 0 *ᵥ x) = 0 := by
  obtain ⟨_, _, _, _, htrace⟩ :=
    LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels.quaternionConjugation.{u,u,u} hB hdegree
  obtain ⟨b, hb⟩ := htrace 1
  have hb' : b + antiValue Q.conjugation.anti b = 1 := by
    rw [Q.canonical, Specs.SymplecticInvolutionModels.quaternionConjugate, hb, map_one]
    abel
  let X := (pairEntry Q 1 0 b).val
  have hX : X + adjoint (hyperbolicGram I K) X = pairMatrixUnit Q 1 0 := by
    change (pairEntry Q 1 0 b).val + adjoint (hyperbolicGram I K) (pairEntry Q 1 0 b).val = _
    rw [pairEntry_splitAdjoint]
    have h : pairEntry Q 1 0 b + pairEntry Q 1 0 (antiValue Q.conjugation.anti b) = pairEntry Q 1 0 1 := by
      apply Q.matrixModel.injective
      rw [map_add]
      simp only [pairEntry, AlgEquiv.apply_symm_apply, ← Matrix.single_add, hb']
    exact congrArg Subtype.val h
  let q := hyperbolicForm I K
  have h₂ := two_eq_zero_of_algebra (F := F) K
  rw [← hX, Matrix.add_mulVec, QuadraticMap.polar_add_right,
    ← hyperbolic_adjoint h₂ X, QuadraticMap.polar_comm q (X *ᵥ x) x, ← two_mul, h₂, zero_mul]

local notation "𝓥" => (I ⊕ I → K)
local notation "q₀" => (hyperbolicForm I K)
local notation "⟪" x ", " y "⟫" => QuadraticMap.polar q₀ x y

/-- A hyperbolic frame in the actual split comparison, normalized so that
the scalar matrix acts in the ordered pairs `(x,v)` and `(y,u)`. -/
private structure ScalarPairFrame (Q : QuaternionHyperbolicPresentation D hB d) where
  frame : HyperbolicFrame q₀
  diagonal₀ (z : 𝓥) : pairMatrixUnit Q 0 0 *ᵥ z = ⟪frame.u, z⟫ • frame.x + ⟪frame.v, z⟫ • frame.y
  upper (z : 𝓥) : pairMatrixUnit Q 0 1 *ᵥ z = ⟪frame.y, z⟫ • frame.x + ⟪frame.x, z⟫ • frame.y
  lower (z : 𝓥) : pairMatrixUnit Q 1 0 *ᵥ z = ⟪frame.u, z⟫ • frame.v + ⟪frame.v, z⟫ • frame.u
  diagonal₁ (z : 𝓥) : pairMatrixUnit Q 1 1 *ᵥ z = ⟪frame.y, z⟫ • frame.v + ⟪frame.x, z⟫ • frame.u

set_option maxHeartbeats 600000 in
private theorem scalarPairFrame_exists [CharP F 2] [FiniteDimensional F K] [IsGalois F K]
    (cover : SpinScaleCover.{u}) (M : SpinModel G D) (hrank : 4 ≤ Fintype.card I)
    (hdegree : degree F B = 2) (Q : QuaternionHyperbolicPresentation D hB d) :
    Nonempty (ScalarPairFrame Q) := by
  let T (i j : Fin 2) : 𝓥 →ₗ[K] 𝓥 := (pairMatrixUnit Q i j).mulVecLin
  have hT (i j k l : Fin 2) (z : 𝓥) : T i j (T k l z) = if j = k then T i l z else 0 := by
    change pairMatrixUnit Q i j *ᵥ (pairMatrixUnit Q k l *ᵥ z) = _
    rw [Matrix.mulVec_mulVec, pairMatrixUnit_mul]
    split <;> simp [T, *]
  let U := (T 0 0).range
  let W := (T 1 1).range
  have hdim : Module.finrank K U = 2 := pairMatrixUnit_rank Q hdegree
  let : Nontrivial U := Module.nontrivial_of_finrank_pos (by rw [hdim]; decide : 0 < Module.finrank K U)
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : U)
  let x : 𝓥 := x₀.val
  have hxU : x ∈ U := x₀.property
  have hx : x ≠ 0 := fun h => hx₀ (Subtype.ext h)
  have h₂ := two_eq_zero_of_algebra (F := F) K
  obtain ⟨z₀, hz₀⟩ := hyperbolic_nondegenerate h₂ x hx
  let y := (⟪x, z₀⟫)⁻¹ • T 0 1 z₀
  let u := T 1 0 y
  let v := T 1 0 x
  have hId (i : Fin 2) (z : 𝓥) (hz : z ∈ (T i i).range) : T i i z = z := by
    obtain ⟨w, rfl⟩ := hz
    simp [hT]
  have hyU : y ∈ U := by
    apply U.smul_mem
    exact ⟨T 0 1 z₀, by simp [hT]⟩
  have huW : u ∈ W := ⟨u, by simp [u, hT]⟩
  have hvW : v ∈ W := ⟨v, by simp [v, hT]⟩
  have hq (i : Fin 2) {z : 𝓥} (hz : z ∈ (T i i).range) : q₀ z = 0 := by
    obtain ⟨w, rfl⟩ := hz
    exact quaternionPair_isotropic cover M hrank hdegree Q i w
  have hzero (i : Fin 2) {z w : 𝓥} (hz : z ∈ (T i i).range) (hw : w ∈ (T i i).range) :
      ⟪z, w⟫ = 0 := by
    simp [QuadraticMap.polar, hq i hz, hq i hw, hq i ((T i i).range.add_mem hz hw)]
  have hAdj (i j : Fin 2) (z w : 𝓥) :
      ⟪T i j z, w⟫ = ⟪z, T (flipPair j) (flipPair i) w⟫ := by
    change ⟪pairMatrixUnit Q i j *ᵥ z, w⟫ = _
    rw [hyperbolic_adjoint h₂, pairMatrixUnit_adjoint]
    rfl
  have hadj₀ (z w : 𝓥) : ⟪T 0 0 z, w⟫ = ⟪z, T 1 1 w⟫ := hAdj 0 0 z w
  have hadjᵤ (z w : 𝓥) : ⟪T 0 1 z, w⟫ = ⟪z, T 0 1 w⟫ := hAdj 0 1 z w
  have hadjₗ (z w : 𝓥) : ⟪T 1 0 z, w⟫ = ⟪z, T 1 0 w⟫ := hAdj 1 0 z w
  have hxu : ⟪x, u⟫ = 1 := by
    have h : ⟪x, T 1 1 z₀⟫ = ⟪x, z₀⟫ := (hadj₀ x z₀).symm.trans (by rw [hId 0 x hxU])
    dsimp only [u, y]
    rw [map_smul, QuadraticMap.polar_smul_right, hT, if_pos rfl, h, smul_eq_mul, inv_mul_cancel₀ hz₀]
  have hyv : ⟪y, v⟫ = 1 := by
    rw [QuadraticMap.polar_comm q₀ y v]
    exact (hadjₗ x y).trans hxu
  have hxv : ⟪x, v⟫ = 0 := quaternionLower_alternating Q hdegree x
  have hyu : ⟪y, u⟫ = 0 := quaternionLower_alternating Q hdegree y
  let frame : HyperbolicFrame q₀ := ⟨x, y, u, v, hq 0 hxU, hq 0 hyU, hq 1 huW, hq 1 hvW,
    hzero 0 hxU hyU, hzero 1 huW hvW, hxu, hyv, hxv, hyu⟩
  let ev : U →ₗ[K] K × K := (((q₀).polarBilin u).comp U.subtype).prod (((q₀).polarBilin v).comp U.subtype)
  have hus : ⟪u, x⟫ = 1 := (QuadraticMap.polar_comm q₀ _ _).trans hxu
  have hvs : ⟪v, y⟫ = 1 := (QuadraticMap.polar_comm q₀ _ _).trans hyv
  have huz : ⟪u, y⟫ = 0 := (QuadraticMap.polar_comm q₀ _ _).trans hyu
  have hvz : ⟪v, x⟫ = 0 := (QuadraticMap.polar_comm q₀ _ _).trans hxv
  have hev (a b : K) : ev ⟨a • x + b • y, U.add_mem (U.smul_mem a hxU) (U.smul_mem b hyU)⟩ = (a,b) := by
    change (⟪u, a • x + b • y⟫, ⟪v, a • x + b • y⟫) = _
    simp [hus, hvs, huz, hvz, smul_eq_mul]
  have hei : Function.Injective ev := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hdim, Module.finrank_prod])).mpr
    rintro ⟨a,b⟩
    exact ⟨_, hev a b⟩
  have hp (z : 𝓥) : T 0 0 z = ⟪u, z⟫ • x + ⟪v, z⟫ • y := by
    have hleft : ev ⟨T 0 0 z, ⟨z, rfl⟩⟩ = (⟪u, z⟫, ⟪v, z⟫) := by
      change (⟪u, T 0 0 z⟫, ⟪v, T 0 0 z⟫) = _
      simp only [QuadraticMap.polar_comm q₀ u (T 0 0 z), QuadraticMap.polar_comm q₀ v (T 0 0 z),
        hadj₀, hId 1 u huW, hId 1 v hvW, QuadraticMap.polar_comm q₀ z u, QuadraticMap.polar_comm q₀ z v]
    exact congrArg Subtype.val (hei (hleft.trans (hev _ _).symm))
  have hUu : T 0 1 u = y := by simp [u, hT, hId 0 y hyU]
  have hUv : T 0 1 v = x := by simp [v, hT, hId 0 x hxU]
  have hur (z : 𝓥) : T 0 1 z = ⟪y, z⟫ • x + ⟪x, z⟫ • y := by
    have hh := hp (T 0 1 z)
    simpa only [hT, eq_self, ite_true, ← hadjᵤ, hUu, hUv] using hh
  have hlr (z : 𝓥) : T 1 0 z = ⟪u, z⟫ • v + ⟪v, z⟫ • u := by
    have hh := congrArg (T 1 0) (hp z)
    simpa only [hT, eq_self, ite_true, map_add, map_smul, u, v] using hh
  have hq₁ (z : 𝓥) : T 1 1 z = ⟪y, z⟫ • v + ⟪x, z⟫ • u := by
    have hh := congrArg (T 1 0) (hur z)
    simpa only [hT, eq_self, ite_true, map_add, map_smul, u, v] using hh
  exact ⟨⟨frame, hp, hur, hlr, hq₁⟩⟩

open LinearAlgebraicGroups.Albert.CliffordSpecification (coefficientForm)
open LinearAlgebraicGroups.Albert.SpinSpecification (vectors conjugate IsVectorAction)
open LinearAlgebraicGroups.Specs.SymplecticDatumRankOneAndPinning (determinantOnePoints)

open private vectors_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

private theorem pairOperator_extension [LinearOrder (I ⊕ I)] (S : TestAlgebra K)
    (L : 𝓥 →ₗ[K] 𝓥) (a b c d : 𝓥)
    (h : ∀ z, L z = ⟪a, z⟫ • b + ⟪c, z⟫ • d) (z : S ⊗[K] 𝓥) :
    let q := coefficientForm S q₀ (Pi.basisFun K (I ⊕ I))
    L.baseChange S z = QuadraticMap.polar q (1 ⊗ₜ[K] a) z • (1 ⊗ₜ[K] b) +
      QuadraticMap.polar q (1 ⊗ₜ[K] c) z • (1 ⊗ₜ[K] d) := by
  let B := Pi.basisFun K (I ⊕ I)
  let q := coefficientForm S q₀ B
  let P : S ⊗[K] 𝓥 →ₗ[S] S ⊗[K] 𝓥 := (q.polarBilin (1 ⊗ₜ[K] a)).smulRight (1 ⊗ₜ[K] b) +
    (q.polarBilin (1 ⊗ₜ[K] c)).smulRight (1 ⊗ₜ[K] d)
  have hL : L.baseChange S = P := by
    apply (TensorProduct.isBaseChange K 𝓥 S).algHom_ext
    intro w
    change (1 : S) ⊗ₜ[K] (L w) = QuadraticMap.polar q (1 ⊗ₜ[K] a) (1 ⊗ₜ[K] w) • (1 ⊗ₜ[K] b) +
      QuadraticMap.polar q (1 ⊗ₜ[K] c) (1 ⊗ₜ[K] w) • (1 ⊗ₜ[K] d)
    rw [h, TensorProduct.tmul_add, HyperbolicFrame.coefficientForm_polar_one_tmul B S,
      HyperbolicFrame.coefficientForm_polar_one_tmul B S]
    simp only [TensorProduct.tmul_smul, ← Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
  exact DFunLike.congr_fun hL z

set_option maxHeartbeats 550000 in
private theorem splitScalarPair_vector [CharP F 2] [LinearOrder (I ⊕ I)] (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (P : ScalarPairFrame Q) (S : TestAlgebra K)
    (g : Matrix.SpecialLinearGroup (Fin 2) S) :
    let p := (P.frame.representedRankOne (Pi.basisFun K (I ⊕ I)) M.splitCover.spinPoints
      M.splitCover.spinRepresents).app S g
    (M.splitCover.orthogonal.points S (p ≫ (M.splitCover.projection ≫ M.splitCover.inclusion).hom.hom)).val.val =
      splitMatrix M S ((Q.matrixAt ((restrictTestAlgebra F K).obj S)).symm
        (scalarPairMatrix ((restrictTestAlgebra F K).obj S) g)) := by
  let b := Pi.basisFun K (I ⊕ I)
  let bS := b.baseChange S
  let p := (P.frame.representedRankOne b M.splitCover.spinPoints M.splitCover.spinRepresents).app S g
  let T (i j : Fin 2) := ((pairMatrixUnit Q i j).mulVecLin).baseChange S
  let W := S ⊗[K] 𝓥
  let k : W →ₗ[S] W := LinearMap.id + (g.val 0 0 - 1) • T 0 0 + g.val 0 1 • T 0 1 +
    g.val 1 0 • T 1 0 + (g.val 1 1 - 1) • T 1 1
  have ht (i j : Fin 2) : LinearMap.toMatrix bS bS (T i j) = (pairMatrixUnit Q i j).map (algebraMap K S) := by
    ext x y
    simp [bS, b, T, LinearMap.toMatrix_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      Matrix.col_apply, ← Algebra.algebraMap_eq_smul_one]
  have hk : LinearMap.toMatrix bS bS k = splitMatrix M S ((Q.matrixAt ((restrictTestAlgebra F K).obj S)).symm
      (scalarPairMatrix ((restrictTestAlgebra F K).obj S) g)) := by
    have h := splitMatrix_scalarPair M Q S g
    change splitMatrix M S ((Q.matrixAt ((restrictTestAlgebra F K).obj S)).symm
      (scalarPairMatrix ((restrictTestAlgebra F K).obj S) g)) = _ at h
    rw [h]
    simp only [k, map_add, map_smul, LinearMap.toMatrix_id, ht]
  let h := P.frame.baseChange b S
  have htransform (z : W) : h.vectorTransform g z = k z := by
    let q := coefficientForm S q₀ b
    have he₀ : T 0 0 z = QuadraticMap.polar q h.u z • h.x + QuadraticMap.polar q h.v z • h.y :=
      pairOperator_extension S _ P.frame.u P.frame.x P.frame.v P.frame.y P.diagonal₀ z
    have heᵤ : T 0 1 z = QuadraticMap.polar q h.y z • h.x + QuadraticMap.polar q h.x z • h.y :=
      pairOperator_extension S _ P.frame.y P.frame.x P.frame.x P.frame.y P.upper z
    have heₗ : T 1 0 z = QuadraticMap.polar q h.u z • h.v + QuadraticMap.polar q h.v z • h.u :=
      pairOperator_extension S _ P.frame.u P.frame.v P.frame.v P.frame.u P.lower z
    have he₁ : T 1 1 z = QuadraticMap.polar q h.y z • h.v + QuadraticMap.polar q h.x z • h.u :=
      pairOperator_extension S _ P.frame.y P.frame.v P.frame.x P.frame.u P.diagonal₁ z
    have h₂ : (2 : S) = 0 := by
      rw [← map_ofNat (algebraMap K S) 2, two_eq_zero_of_algebra (F := F) K, map_zero]
    have hneg (w : W) : -w = w := neg_eq_of_add_eq_zero_left (by rw [← two_smul S w, h₂, zero_smul])
    change h.vectorTransform g z = z + (g.val 0 0 - 1) • T 0 0 z + g.val 0 1 • T 0 1 z +
      g.val 1 0 • T 1 0 z + (g.val 1 1 - 1) • T 1 1 z
    rw [he₀, heᵤ, heₗ, he₁]
    unfold HyperbolicFrame.vectorTransform HyperbolicFrame.frameComponent
    rw [sub_eq_add_neg (g.val 0 0 • h.y) (g.val 1 0 • h.u),
      hneg (g.val 1 0 • h.u), hneg (g.val 0 1 • h.y)]
    module
  obtain ⟨v, hv, hm⟩ := M.splitCover.vector S p
  have he : v.toLinearMap = k := by
    apply LinearMap.ext
    intro z
    change v z = k z
    apply vectors_injective q₀ S b
    rw [← htransform, hv z, P.frame.representedRankOne_apply]
    exact (P.frame.scalarMatrixUnitsAction_vector b S g z).symm
  exact hm.symm.trans ((congrArg (LinearMap.toMatrix bS bS) he).trans hk)

open private groupBaseChangePointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

private def scalarSplitLift [LinearOrder (I ⊕ I)] (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (P : ScalarPairFrame Q) :
    determinantOnePoints K ⟶ restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj G.val :=
  P.frame.representedRankOne (Pi.basisFun K (I ⊕ I)) M.splitCover.spinPoints M.splitCover.spinRepresents ≫
    (groupPointsFunctor K).map M.splitSource.inv ≫ (groupBaseChangePointIso K G.val).hom

private theorem scalarSplitLift_projects [CharP F 2] [LinearOrder (I ⊕ I)] (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (P : ScalarPairFrame Q)
    (S : TestAlgebra K) (g : Matrix.SpecialLinearGroup (Fin 2) S) :
    let R := (restrictTestAlgebra F K).obj S
    Q.matrixAt R (spinVectorProjection M R ((scalarSplitLift M Q P).app S g)).val = scalarPairMatrix R g := by
  let R := (restrictTestAlgebra F K).obj S
  let p := (P.frame.representedRankOne (Pi.basisFun K (I ⊕ I)) M.splitCover.spinPoints
    M.splitCover.spinRepresents).app S g
  let z := p ≫ M.splitSource.inv.hom.hom
  change Q.matrixAt R (spinVectorProjection M R (baseChangePoint F K G.val.X S z)).val = _
  apply (Q.matrixAt R).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  apply (splitMatrix M S).injective
  rw [splitMatrix_spinPoint]
  have h : z ≫ M.splitSource.hom.hom.hom = p := by
    have he := congrArg (fun a => a.hom.hom) M.splitSource.inv_hom_id
    change M.splitSource.inv.hom.hom ≫ M.splitSource.hom.hom.hom = 𝟙 _ at he
    change (p ≫ M.splitSource.inv.hom.hom) ≫ M.splitSource.hom.hom.hom = _
    rw [Category.assoc, he, Category.comp_id]
  rw [← Category.assoc, h]
  exact splitScalarPair_vector M Q P S g

end SplitQuaternionCoordinates

section Assembly

open CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open LinearAlgebraicGroups.Specs.StandardGroups (SLCoordinates)
open LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint laurentParameter laurentAlgebra)
open LinearAlgebraicGroups.Albert.SpinSpecification (vectors)
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair SpinModel)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionScalarCliffordLift
  (ScalarCliffordLift scalarPairMatrix scalarDiagonal IsAdaptedSplitComparison LiftsScalarPair IsPairDiagonal)
open LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
open LinearAlgebraicGroups.Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open LinearAlgebraicGroups.Specs.SymplecticDatumRankOneAndPinning (determinantOnePoints)
open LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)

open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

set_option backward.isDefEq.respectTransparency false

private theorem cocharacterPoint_postcompose {k : Type u} [Field k] {G H : GroupScheme k}
    (c : Cocharacter G) (f : G ⟶ H) (R : TestAlgebra k) (r : Rˣ) :
    cocharacterPoint (c ≫ f) R r = cocharacterPoint c R r ≫ f.hom.hom := by
  unfold cocharacterPoint
  rw [Functor.map_comp]
  rfl

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ}

private theorem scalarDiagonal_noncentral (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    {A : AffineAlgebraicGroup F} (e : (groupPointsFunctor F).obj A.val ≅ determinantOnePoints F)
    (f : A.val ⟶ G.val) (hf : LiftsScalarPair M Q e f) (c : Cocharacter A.val)
    (hc : ∀ (R : TestAlgebra F) (s : Rˣ), e.hom.app R (cocharacterPoint c R s) = scalarDiagonal s) :
    IsNoncentral (c ≫ f) := by
  let R := laurentAlgebra (CommAlgCat.of F F)
  let t := laurentParameter (CommAlgCat.of F F)
  let p : Points A.val.X R := e.inv.app R (upper 1)
  let fR := pointHom f R
  let a := cocharacterPoint c R t
  have hpi : Function.Injective fR := by
    intro x y h
    apply (e.app R).groupIsoToMulEquiv.injective
    apply scalarPairMatrix_injective (B := B) (d := d) R
    change x ≫ f.hom.hom = y ≫ f.hom.hom at h
    change scalarPairMatrix R (e.hom.app R x) = scalarPairMatrix R (e.hom.app R y)
    rw [← hf R x, ← hf R y, h]
  refine ⟨(testSpec F).obj (Opposite.op R), fR p, ?_⟩
  intro h
  have h' := (centralizes_iff (c ≫ f) (fR p)).mp h _ (𝟙 _) (unitPoint R t)
  have hpa : Commute (fR p) (fR a) := by
    rw [Category.id_comp] at h'
    change Commute (fR p) (cocharacterPoint (c ≫ f) R t) at h'
    rwa [cocharacterPoint_postcompose] at h'
  have hpa' : Commute p a := by
    apply hpi
    rw [map_mul, map_mul]
    exact hpa.eq
  have hpp : e.hom.app R p = upper 1 := congrArg (fun m => m.app R (upper 1)) e.inv_hom_id
  have hcomm := hpa'.map (e.hom.app R).hom
  change Commute (e.hom.app R p) (e.hom.app R a) at hcomm
  rw [hpp, show e.hom.app R a = _ from hc R t] at hcomm
  have hconj : scalarDiagonal t * upper 1 * (scalarDiagonal t)⁻¹ = upper 1 := by
    rw [hcomm.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [scalarDiagonal_conjugate_upper, one_mul] at hconj
  have hv := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) R => g.val 0 1) hconj
  apply laurentParameter_sq_ne_one (k := F)
  simpa [upper, Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection, Matrix.one_apply] using hv

private theorem scalarCliffordLift_fromScaleCover (hcover : SpinScaleCover.{u}) : ScalarCliffordLift.{u} := by
  intro F K I B _ _ _ _ _ _ _ _ _ _ ρ G D M hrank hB hdegree d Q
  let ord := Fintype.equivFin (I ⊕ I)
  letI : LinearOrder (I ⊕ I) := LinearOrder.lift' ord ord.injective
  let A := determinantOneGroup F
  let e := determinantOneGroupPoints F
  obtain ⟨P⟩ := scalarPairFrame_exists hcover M hrank hdegree Q
  let l := scalarSplitLift M Q P
  obtain ⟨f, hf, hfK⟩ := scalarLift_descends M Q l (scalarSplitLift_projects M Q P)
  have hsm := determinantOneGroup_smooth F
  refine ⟨A, e, f, hsm, determinantOneGroup_geometricallyConnected F,
    scalarLift_isClosedImmersion M Q e f hf, hf, fun f' hf' => scalarLift_unique M Q hsm e hf hf', ?_, ?_⟩
  · obtain ⟨c, hc⟩ := determinantOne_diagonal e
    refine ⟨c, hc, ?_, scalarDiagonal_noncentral M Q e f hf c hc,
      determinantOne_contracts e c hc f⟩
    intro R r
    rw [cocharacterPoint_postcompose, hf, hc]
  · have hcard : 1 < Fintype.card I := by omega
    obtain ⟨i, j, hij⟩ := Fintype.one_lt_card_iff.mp hcard
    let q := hyperbolicForm I K
    let b := Pi.basisFun K (I ⊕ I)
    have h₂ := two_eq_zero_of_algebra (F := F) K
    let h := standardFrame h₂ i j hij
    obtain ⟨s, hsx, hsy, hsu, hsv⟩ := move_hyperbolicFrame q (hyperbolic_nondegenerate h₂) P.frame h
    let S₀ := M.splitCover.spin
    let e₀ := M.splitCover.spinPoints
    let rep := M.splitCover.spinRepresents
    let a₀ := representedSpinIsometry s e₀ S₀.property.1 rep
    let a := M.splitSource ≪≫ a₀
    refine ⟨i, j, hij, a, ?_, ?_⟩
    · refine ⟨s.toIsometry, s.toLinearEquiv.bijective, fun R p => ?_⟩
      change (e₀ R ((p ≫ M.splitSource.hom.hom.hom) ≫ a₀.hom.hom.hom)).val =
        cliffordIsometry s R (e₀ R (p ≫ M.splitSource.hom.hom.hom)).val
      exact representedSpinIsometry_apply s e₀ S₀.property.1 rep R _
    · intro R p
      let g := e.hom.app _ (baseChangePoint F K A.val.X R p)
      let z := (P.frame.representedRankOne b e₀ rep).app R g
      have hpt : p ≫ ((groupBaseChange F K).map f).hom.hom = z ≫ M.splitSource.inv.hom.hom :=
        (baseChangePointsEquiv K G.val.X R).injective (hfK R p)
      have hpa : p ≫ ((groupBaseChange F K).map f ≫ a.hom).hom.hom = z ≫ a₀.hom.hom.hom := by
        change p ≫ ((groupBaseChange F K).map f).hom.hom ≫
          M.splitSource.hom.hom.hom ≫ a₀.hom.hom.hom = _
        rw [← Category.assoc, ← Category.assoc, hpt]
        have he := congrArg (fun f => f.hom.hom) M.splitSource.inv_hom_id
        change M.splitSource.inv.hom.hom ≫ M.splitSource.hom.hom.hom = 𝟙 _ at he
        have hc : (z ≫ M.splitSource.inv.hom.hom) ≫ M.splitSource.hom.hom.hom = z := by
          rw [Category.assoc, he, Category.comp_id]
        rw [hc]
      have hv (w : I ⊕ I → K) : cliffordIsometry s R (vectors q R (1 ⊗ₜ[K] w)) =
          vectors q R (1 ⊗ₜ[K] s w) := cliffordIsometry_vectors s R _
      obtain ⟨hu, hl, hd⟩ := P.frame.representedRankOne_values b e₀ rep R g
      have hp := representedSpinIsometry_apply s e₀ S₀.property.1 rep R z
      dsimp only
      rw [hpa, hp]
      refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
      · rw [hu r hr, map_add, map_one, cliffordIsometry_smul, map_mul, hv, hv, hsx, hsy]
        rfl
      · rw [hl r hr, map_add, map_one, cliffordIsometry_smul, map_mul, hv, hv, hsv, hsu]
        rfl
      · rw [hd r hr]
        simp only [map_add, map_one, cliffordIsometry_smul, map_mul]
        rw [hv P.frame.x, hv P.frame.y, hv P.frame.v, hv P.frame.u, hsx, hsy, hsv, hsu]
        rfl

/-- The scalar determinant-one action on the quaternionic pair lifts to the
original spin group and becomes the indicated Clifford root group after splitting. -/
theorem scalarCliffordLift : ScalarCliffordLift.{u} :=
  scalarCliffordLift_fromScaleCover QuaternionSpinScaleCover.spinScaleCover

end Assembly


end

end LinearAlgebraicGroups.Arithmetic.QuaternionScalarCliffordLift
