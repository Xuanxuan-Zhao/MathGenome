import Specs.LinearAlgebraicGroups.Albert.QuadraticOperators
import LinearAlgebraicGroups.Albert.CubicIdentities
import LinearAlgebraicGroups.Albert.QuadraticJordan
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Albert

open LinearAlgebraicGroups.Composition Polynomial TensorProduct
open scoped BigOperators

universe u v w z

noncomputable section

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
variable {n : QuadraticForm R A} (γ : Fin 3 → Rˣ)

abbrev applyCubicOperator := @QuadraticOperatorSpecification.applyOperator

local notation "V" => Coordinates R A
local notation "N" => cubicNorm n γ
local notation "Q" => cubicAdjoint n γ
local notation "T" => tracePairing n γ
local notation "B" => adjointCross n γ
local notation "e" => (cubicUnit : V)
local notation "U" => applyCubicOperator n γ
local notation "tr" => linearTrace n γ

variable [IsScalarTower R A A] [SMulCommClass R A A]

private def adjointMap : QuadraticMap R V V :=
  (cubicAdjoint_isQuadratic (n := n) γ).choose

private theorem adjointMap_apply (x : V) : adjointMap (n := n) γ x = Q x :=
  (cubicAdjoint_isQuadratic (n := n) γ).choose_spec.1 x

private theorem adjointMap_polar (x y : V) : (adjointMap (n := n) γ).polarBilin x y = B x y :=
  (cubicAdjoint_isQuadratic (n := n) γ).choose_spec.2 x y

open private adjointCross_comm from LinearAlgebraicGroups.Albert.CubicIdentities

private theorem cross_add (x y z : V) : B x (y + z) = B x y + B x z := by
  simp only [← adjointMap_polar, map_add]

private theorem cross_smul (x y : V) (r : R) : B x (r • y) = r • B x y := by
  simp only [← adjointMap_polar, map_smul]

private theorem cross_add_left (x y z : V) : B (x + y) z = B x z + B y z := by
  simp only [← adjointMap_polar, LinearMap.map_add₂]

private theorem cross_smul_left (x y : V) (r : R) : B (r • x) y = r • B x y := by
  simp only [← adjointMap_polar, LinearMap.map_smul₂]

private theorem cross_sub (x y z : V) : B x (y - z) = B x y - B x z := by
  simp only [← adjointMap_polar, map_sub]

private theorem adj_smul (x : V) (r : R) : Q (r • x) = (r * r) • Q x := by
  simp only [← adjointMap_apply, QuadraticMap.map_smul]

private theorem cross_self (x : V) : B x x = (2 : R) • Q x := by
  simp only [← adjointMap_polar, ← adjointMap_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul]

private def opEnd (x : V) : Module.End R V :=
  (T x).smulRight x - (adjointMap (n := n) γ).polarBilin (Q x)

private theorem opEnd_apply (x y : V) : opEnd (n := n) γ x y = U x y := by
  simp only [opEnd, LinearMap.sub_apply, LinearMap.smulRight_apply, adjointMap_polar]
  rfl

private theorem op_smul (r : R) (x y : V) : U (r • x) y = (r * r) • U x y := by
  simp only [QuadraticOperatorSpecification.applyOperator, adj_smul, cross_smul_left,
    LinearMap.map_smul₂, smul_eq_mul, smul_sub, smul_smul]
  congr 1
  rw [mul_right_comm, mul_assoc, mul_comm r]

private theorem triple_formula (x y z : V) :
    QuadraticOperatorSpecification.triple n γ x y z =
      T x y • z + T z y • x - B (B x z) y := by
  have h : Q (x + z) = Q x + Q z + B x z := by
    unfold adjointCross CubicSpecification.adjointCross
    abel
  simp only [QuadraticOperatorSpecification.triple, QuadraticOperatorSpecification.applyOperator,
    h, cross_add_left, LinearMap.map_add₂, add_smul, smul_add]
  abel

private def opPolar : LinearMap.BilinMap R V (Module.End R V) :=
  LinearMap.mk₂ R (fun x z =>
    (T x).smulRight z + (T z).smulRight x - (adjointMap (n := n) γ).polarBilin (B x z))
    (fun x x' z => LinearMap.ext fun y => by
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
        LinearMap.map_add₂, adjointMap_polar, cross_add_left, add_smul, smul_add]
      abel)
    (fun r x z => LinearMap.ext fun y => by
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
        LinearMap.map_smul₂, LinearMap.smul_apply, adjointMap_polar, cross_smul_left,
        smul_eq_mul, smul_add, smul_sub, smul_smul, mul_comm])
    (fun x z z' => LinearMap.ext fun y => by
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
        LinearMap.map_add₂, adjointMap_polar, cross_add, add_smul, smul_add]
      abel)
    (fun r x z => LinearMap.ext fun y => by
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
        LinearMap.map_smul₂, LinearMap.smul_apply, adjointMap_polar, cross_smul,
        smul_eq_mul, smul_add, smul_sub, smul_smul, mul_comm])

private def opQuadratic : QuadraticMap R V (Module.End R V) where
  toFun := opEnd (n := n) γ
  toFun_smul r x := LinearMap.ext fun y => by
    simp only [LinearMap.smul_apply, opEnd_apply, op_smul]
  exists_companion' := ⟨opPolar (n := n) γ, fun x z => LinearMap.ext fun y => by
    have h := triple_formula (n := n) γ x y z
    unfold QuadraticOperatorSpecification.triple at h
    change opEnd (n := n) γ (x + z) y =
      opEnd (n := n) γ x y + opEnd (n := n) γ z y +
        ((T x).smulRight z + (T z).smulRight x - (adjointMap (n := n) γ).polarBilin (B x z)) y
    simp only [opEnd_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
      adjointMap_polar]
    rw [← h]
    abel⟩

private theorem opQuadratic_apply (x y : V) : opQuadratic (n := n) γ x y = U x y :=
  opEnd_apply γ x y

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem opUnit (y : V) : U e y = y := by
  have h := cubic_unit_identities (n := n) γ
  simp only [QuadraticOperatorSpecification.applyOperator, h.2.1, h.2.2,
    tracePairing_comm γ e y]
  change tr y • e - (tr y • e - y) = y
  abel

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem opSquare (x : V) : U x e = Q x + tr x • x - quadraticTrace n γ x • e := by
  have h := (cubic_unit_identities (n := n) γ).2.2 (Q x)
  change T x e • x - B (Q x) e = _
  change B e (Q x) = tr (Q x) • e - Q x at h
  rw [adjointCross_comm γ (Q x) e, h]
  change tr x • x - (tr (Q x) • e - Q x) = _
  change _ = Q x + tr x • x - tr (Q x) • e
  abel

section PolynomialCoefficients

local notation "P" => Polynomial R
local notation "Vₚ" => Coordinates P (P ⊗[R] A)
local notation "Xₚ" => (X : P)

private def coefficient (k : ℕ) : Vₚ →ₗ[R] V :=
  (TensorProduct.lid R V).toLinearMap ∘ₗ (Polynomial.lcoeff R k).rTensor V ∘ₗ
    (coordinatesBaseChange (R := R) (A := A) P).symm.toLinearMap.restrictScalars R

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem coefficient_smul_extend (k : ℕ) (p : P) (x : V) :
    coefficient (R := R) (A := A) k (p • extendCoordinates P x) = p.coeff k • x := by
  change (TensorProduct.lid R V) ((Polynomial.lcoeff R k).rTensor V
    ((coordinatesBaseChange (R := R) (A := A) P).symm
    (p • coordinatesBaseChange P (1 ⊗ₜ[R] x)))) = _
  rw [map_smul, LinearEquiv.symm_apply_apply, smul_tmul', smul_eq_mul, mul_one,
    LinearMap.rTensor_tmul, Polynomial.lcoeff_apply, TensorProduct.lid_tmul]

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem coefficient_extend (k : ℕ) (x : V) :
    coefficient (R := R) (A := A) k (extendCoordinates P x) = (1 : P).coeff k • x := by
  simpa only [one_smul] using coefficient_smul_extend k (1 : P) x

variable (h : IsOctonionNorm n)

include h

set_option maxHeartbeats 1200000 in
/-- The first two coefficients of the iterated adjoint on a line. -/
private theorem adjoint_coefficients (x y : V) :
    B (Q x) (B x y) = N x • y + T (Q x) y • x ∧
    Q (B x y) + B (Q x) (Q y) = T (Q y) x • x + T (Q x) y • y := by
  let := h.projective
  let q := normBaseChange P n
  let δ := baseChangedWeights P γ
  let ι := extendCoordinates (R := R) (A := A) P
  have hq : IsOctonionNorm q := octonion_norm_baseChange h P
  have adj (x : V) : cubicAdjoint q δ (ι x) = ι (Q x) :=
    cubicAdjoint_extend γ P x
  have cross (x y : V) : adjointCross q δ (ι x) (ι y) = ι (B x y) := by
    change cubicAdjoint q δ (ι x + ι y) - cubicAdjoint q δ (ι x) - cubicAdjoint q δ (ι y) = _
    rw [← extendCoordinates_add, adj, adj, adj, ← extendCoordinates_sub, ← extendCoordinates_sub]
    rfl
  have line (a b : Vₚ) (s : P) :
      cubicAdjoint q δ (a + s • b) =
        cubicAdjoint q δ a + s • adjointCross q δ a b + (s * s) • cubicAdjoint q δ b :=
    cubicAdjoint_add_smul δ a b s
  have expansion : cubicAdjoint q δ (ι x + Xₚ • ι y) =
      ι (Q x) + Xₚ • ι (B x y) + Xₚ ^ 2 • ι (Q y) := by
    rw [line, adj, adj, cross, pow_two]
  have id : cubicAdjoint q δ (cubicAdjoint q δ (ι x + Xₚ • ι y)) =
      cubicLinePolynomial n γ x y • (ι x + Xₚ • ι y) :=
    cubic_adjoint_identity δ hq (ι x + Xₚ • ι y)
  rw [expansion] at id
  rw [cubic_line_polynomial γ h x y] at id
  have left :
      cubicAdjoint q δ (ι (Q x) + Xₚ • ι (B x y) + Xₚ ^ 2 • ι (Q y)) =
        ι (Q (Q x)) + Xₚ • ι (B (Q x) (B x y)) +
        Xₚ ^ 2 • ι (Q (B x y)) + Xₚ ^ 2 • ι (B (Q x) (Q y)) +
        Xₚ ^ 3 • ι (B (B x y) (Q y)) + Xₚ ^ 4 • ι (Q (Q y)) := by
    rw [line (ι (Q x) + Xₚ • ι (B x y)),
      line (ι (Q x)), cross_add_left, cross_smul_left]
    simp only [adj, cross, smul_add, smul_smul]
    rw [← pow_two, ← pow_succ, ← pow_add]
    norm_num
    abel
  rw [left] at id
  have right :
      (C (N x) + Xₚ * C (T (Q x) y) + Xₚ ^ 2 * C (T (Q y) x) + Xₚ ^ 3 * C (N y)) •
        (ι x + Xₚ • ι y) =
      C (N x) • ι x + (Xₚ * C (T (Q x) y)) • ι x +
        (Xₚ ^ 2 * C (T (Q y) x)) • ι x + (Xₚ ^ 3 * C (N y)) • ι x +
        (Xₚ * C (N x)) • ι y + (Xₚ ^ 2 * C (T (Q x) y)) • ι y +
        (Xₚ ^ 3 * C (T (Q y) x)) • ι y + (Xₚ ^ 4 * C (N y)) • ι y := by
    simp only [smul_add, add_smul, smul_smul]
    module
  rw [right] at id
  constructor
  · have c := congrArg (coefficient (R := R) (A := A) 1) id
    simp only [map_add, ι, coefficient_extend, coefficient_smul_extend, Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_C, Polynomial.coeff_X, Polynomial.coeff_one] at c
    norm_num at c
    exact c.trans (add_comm _ _)
  · have c := congrArg (coefficient (R := R) (A := A) 2) id
    simp only [map_add, ι, coefficient_extend, coefficient_smul_extend, Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_C, Polynomial.coeff_X, Polynomial.coeff_one] at c
    norm_num at c
    exact c

private theorem trace_adjoint_self (x : V) : T x (Q x) = 3 * N x := by
  let := h.projective
  let q := normBaseChange P n
  let δ := baseChangedWeights P γ
  let ι := extendCoordinates (R := R) (A := A) P
  have hh : cubicLinePolynomial n γ x x = (1 + X : P) ^ 3 * C (N x) := by
    change cubicNorm q δ (ι x + (X : P) • ι x) = _
    have add : ι x + Xₚ • ι x = (1 + Xₚ) • ι x := by simp [add_smul]
    rw [add, show cubicNorm q δ ((1 + Xₚ) • ι x) = (1 + Xₚ)^3 * cubicNorm q δ (ι x)
      from cubicNorm_smul δ (1 + Xₚ) (ι x), cubicNorm_extend]
    rfl
  have hh' := congrArg (fun p : P => p.coeff 1) hh
  rw [cubic_line_polynomial γ h x x] at hh'
  rw [show (1 + X : P)^3 = 1 + X * C 3 + X^2 * C 3 + X^3 by
    simp only [map_ofNat]; ring] at hh'
  have hc : T (Q x) x = 3 * N x := by
    simpa [Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      add_mul, mul_assoc] using hh'
  rw [tracePairing_comm γ, hc]

end PolynomialCoefficients

section Identities

variable (h : IsOctonionNorm n)

include h

private theorem trace_cross_cycle (x y z : V) : T (B x y) z = T (B y z) x := by
  have norm_add (a b : V) : N (a + b) = N a + T (Q a) b + T (Q b) a + N b := by
    simpa only [one_smul, one_mul, one_pow] using cubicNorm_add_smul γ h.toNormLaws a b (1 : R)
  have mixed (a b c : V) :
      T (B a b) c = N (a + b + c) - N (a + b) - N (b + c) - N (c + a) + N a + N b + N c := by
    change T (Q (a + b) - Q a - Q b) c = _
    rw [norm_add (a + b) c, norm_add b c, add_comm c a, norm_add a c]
    simp only [LinearMap.map_sub₂, map_add]
    abel
  rw [mixed, mixed, show y + z + x = x + y + z by ac_rfl]
  abel

private theorem trace_cross_symm (a y z : V) : T (B a y) z = T (B a z) y := by
  rw [trace_cross_cycle γ h a y z, adjointCross_comm γ y z, ← trace_cross_cycle γ h a z y]

private theorem self_adjoint (x y z : V) : T (U x y) z = T y (U x z) := by
  rw [tracePairing_comm γ y (U x z)]
  change T (T x y • x - B (Q x) y) z = T (T x z • x - B (Q x) z) y
  simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smul₂, smul_eq_mul,
    trace_cross_symm γ h (Q x) y z, mul_comm (T x y)]

private theorem trace_cross_pair (a b c : V) : T (B a b) c = T a (B b c) :=
  (trace_cross_cycle γ h a b c).trans (tracePairing_comm γ _ _)

/-- Transpose the first coefficient identity using the perfect trace pairing. -/
private theorem reverse_cross (x y : V) :
    B x (B (Q x) y) = N x • y + T x y • Q x := by
  apply (tracePairing_perfect γ h.perfect).bijective_left.injective
  apply LinearMap.ext
  intro z
  change T (B x (B (Q x) y)) z = T (N x • y + T x y • Q x) z
  rw [adjointCross_comm γ x, trace_cross_pair γ h, adjointCross_comm γ (Q x),
    trace_cross_pair γ h, (adjoint_coefficients γ h x z).1]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, tracePairing_comm γ y x]
  ring

private theorem covariance (x y : V) : Q (U x y) = U (Q x) (Q y) := by
  let a := Q x
  let b := N x
  let r := T x y
  have id : Q a = b • x := cubic_adjoint_identity γ h x
  have second := (adjoint_coefficients γ h a y).2
  change Q (B a y) + B (Q a) (Q y) = T (Q y) a • a + T (Q a) y • y at second
  rw [id, LinearMap.map_smul₂, smul_eq_mul] at second
  have expand : Q (r • x - B a y) =
      (r * r) • a - r • B x (B a y) + Q (B a y) := by
    have hh : Q (r • x + (-1 : R) • B a y) =
        Q (r • x) + (-1 : R) • B (r • x) (B a y) + ((-1 : R) * (-1)) • Q (B a y) :=
      cubicAdjoint_add_smul γ (r • x) (B a y) (-1)
    simpa only [a, neg_one_smul, ← sub_eq_add_neg, neg_mul_neg, one_mul, one_smul,
      adj_smul, cross_smul_left] using hh
  change Q (r • x - B a y) = T a (Q y) • a - B (Q a) (Q y)
  rw [expand, reverse_cross γ h x y, tracePairing_comm γ a (Q y), id]
  change (r * r) • a - r • (b • y + r • a) + Q (B a y) =
    T (Q y) a • a - B (b • x) (Q y)
  rw [eq_sub_of_add_eq second]
  module

private theorem op_adjoint (x : V) : U x (Q x) = N x • x := by
  have id : Q (Q x) = N x • x := cubic_adjoint_identity γ h x
  change T x (Q x) • x - B (Q x) (Q x) = _
  rw [trace_adjoint_self γ h, cross_self, id]
  module

private theorem op_cross (x y : V) : U x (B x y) = T (Q x) y • x - N x • y := by
  change T x (B x y) • x - B (Q x) (B x y) = _
  have ht : T x (B x y) = 2 * T (Q x) y := by
    rw [tracePairing_comm γ x, trace_cross_symm γ h x y x, cross_self,
      LinearMap.map_smul₂, smul_eq_mul]
  rw [(adjoint_coefficients γ h x y).1, ht]
  module

private theorem cross_op (x y : V) : B x (U x y) = T x y • Q x - N x • y := by
  change B x (T x y • x - B (Q x) y) = _
  rw [cross_sub, cross_smul, cross_self, reverse_cross γ h]
  module

omit h in
private theorem op_add_right (x y z : V) : U x (y + z) = U x y + U x z := by
  simp only [← opEnd_apply, map_add]

omit h in
private theorem op_sub_right (x y z : V) : U x (y - z) = U x y - U x z := by
  simp only [← opEnd_apply, map_sub]

omit h in
private theorem op_smul_right (r : R) (x y : V) : U x (r • y) = r • U x y := by
  simp only [← opEnd_apply, map_smul]

private theorem op_inverse (x y : V) :
    U x (U (Q x) y) = N x ^ 2 • y ∧ U (Q x) (U x y) = N x ^ 2 • y := by
  have id : Q (Q x) = N x • x := cubic_adjoint_identity γ h x
  have formula (z : V) : U (Q x) z = T (Q x) z • Q x - N x • B x z := by
    change T (Q x) z • Q x - B (Q (Q x)) z = _
    rw [id, cross_smul_left]
  constructor
  · rw [formula, op_sub_right, op_smul_right, op_smul_right, op_adjoint γ h, op_cross γ h]
    module
  · have ht : T (Q x) (U x y) = N x * T x y := by
      rw [← self_adjoint γ h, op_adjoint γ h, LinearMap.map_smul₂, smul_eq_mul]
    rw [formula, ht, cross_op γ h]
    module

private theorem covariance_cross (x y z : V) :
    B (U x y) (U x z) = U (Q x) (B y z) := by
  change Q (U x y + U x z) - Q (U x y) - Q (U x z) = U (Q x) (Q (y + z) - Q y - Q z)
  rw [← op_add_right, covariance γ h, covariance γ h, covariance γ h, op_sub_right, op_sub_right]

/-- Transfer the polarized covariance across the trace pairing. -/
private theorem fundamental_cross (x y z : V) :
    B (U (Q x) (Q y)) z = U x (B (Q y) (U x z)) := by
  apply (tracePairing_perfect γ h.perfect).bijective_left.injective
  apply LinearMap.ext
  intro w
  change T (B (U (Q x) (Q y)) z) w = T (U x (B (Q y) (U x z))) w
  rw [trace_cross_pair γ h, self_adjoint γ h (Q x), ← covariance_cross γ h x z w,
    ← trace_cross_pair γ h, ← self_adjoint γ h]

private theorem fundamental (x y z : V) : U (U x y) z = U x (U y (U x z)) := by
  change T (U x y) z • U x y - B (Q (U x y)) z = _
  rw [self_adjoint γ h, covariance γ h, fundamental_cross γ h]
  change _ = U x (T y (U x z) • y - B (Q y) (U x z))
  rw [op_sub_right, op_smul_right]

private theorem commuting (x y z : V) :
    U x (QuadraticOperatorSpecification.triple n γ y x z) =
      QuadraticOperatorSpecification.triple n γ (U x y) z x := by
  rw [triple_formula, triple_formula, op_sub_right, op_add_right, op_smul_right, op_smul_right,
    adjointCross_comm γ (B y z) x, op_cross γ h, adjointCross_comm γ (U x y) x, cross_op γ h]
  have ht : T (U x y) z = T x y * T x z - T (Q x) (B y z) := by
    change T (T x y • x - B (Q x) y) z = _
    simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smul₂, smul_eq_mul,
      trace_cross_cycle γ h (Q x) y z, tracePairing_comm γ (B y z)]
  rw [ht]
  have hc (r s : R) (a b c : V) : B (r • a - s • b) c = r • B a c - s • B b c := by
    simp only [← adjointMap_polar, map_sub, LinearMap.sub_apply, LinearMap.map_smul₂]
  rw [hc]
  change T y x • (T x z • x - B (Q x) z) + T z x • U x y -
    (T (Q x) (B y z) • x - N x • B y z) =
    (T x y * T x z - T (Q x) (B y z)) • x + T x z • U x y -
      (T x y • B (Q x) z - N x • B y z)
  rw [tracePairing_comm γ y x, tracePairing_comm γ z x]
  module

omit h in
theorem cubic_operator_identities : QuadraticOperatorSpecification.identitiesType.{u, v} := by
  intro R A _ _ _ _ _ n γ h
  refine ⟨opUnit γ, triple_formula γ, self_adjoint γ h, covariance γ h,
    op_adjoint γ h, op_inverse γ h, fundamental γ h, commuting γ h, opSquare γ, ?_⟩
  intro x y
  exact self_adjoint γ h x y cubicUnit

end Identities

section MatrixSquare

open private next_zero next_one next_two prev_zero prev_one prev_two from LinearAlgebraicGroups.Albert.CubicIdentities

private theorem matrix_square (h : IsOctonionNorm n) (x : V) :
    assemble n γ (U x e) = assemble n γ x * assemble n γ x := by
  rw [opSquare]
  have norm_rel (a : A) : a * conjugate n a = n a • (1 : A) :=
    (mul_conjugate h.toNormLaws a).1
  have norm_rel' (a : A) : conjugate n a * a = n a • (1 : A) :=
    (mul_conjugate h.toNormLaws a).2
  have invol (a : A) : conjugate n (conjugate n a) = a := conjugate_involutive h.toNormLaws a
  have conjmul (a b : A) : conjugate n (a * b) = conjugate n b * conjugate n a :=
    conjugate_mul h.toNormLaws a b
  have qtr : quadraticTrace n γ x = ∑ i, (Q x).1 i := linearTrace_apply γ (Q x)
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [HermitianSpecification.assemble, Matrix.mul_apply, Fin.sum_univ_three,
      CubicSpecification.cubicAdjoint, qtr, linearTrace_apply,
      CubicSpecification.blockWeight, CubicSpecification.cubicUnit,
      next_zero, next_one, next_two, prev_zero, prev_one, prev_two,
      smul_mul_assoc, mul_smul_comm, norm_rel, norm_rel', conjmul, invol,
      map_add, map_smul, smul_add, smul_smul]
     module)

theorem cubic_operator_matrix_square : QuadraticOperatorSpecification.matrixSquareType.{u, v} := by
  intro R A _ _ _ _ _ n γ h x
  exact matrix_square γ h x

theorem cubic_operator_after_extension : QuadraticOperatorSpecification.scalarExtensionType.{u, v, w} := by
  intro R A _ _ _ _ _ n γ S _ _ h
  let := h.projective
  have hS := octonion_norm_baseChange h S
  exact ⟨cubic_operator_identities (baseChangedWeights S γ) hS,
    matrix_square (baseChangedWeights S γ) hS, opQuadratic (baseChangedWeights S γ),
    opQuadratic_apply (baseChangedWeights S γ)⟩

end MatrixSquare

theorem cubic_operator_inverse : QuadraticOperatorSpecification.inverseType.{u, v} := by
  intro R A _ _ _ _ _ n γ h x d hd
  change (↑d : R) = cubicNorm n γ x at hd
  let f := opEnd (n := n) γ x
  let g := ((↑d⁻¹ : R) ^ 2) • opEnd (n := n) γ (cubicAdjoint n γ x)
  have cancel : ((↑d⁻¹ : R) ^ 2) * cubicNorm n γ x ^ 2 = 1 := by
    rw [← mul_pow, ← hd, Units.inv_mul, one_pow]
  have fg : f * g = 1 := by
    apply LinearMap.ext
    intro y
    change opEnd (n := n) γ x (((↑d⁻¹ : R) ^ 2) • opEnd (n := n) γ (cubicAdjoint n γ x) y) = y
    rw [map_smul, opEnd_apply, opEnd_apply, (op_inverse γ h x y).1, smul_smul, cancel, one_smul]
  have gf : g * f = 1 := by
    apply LinearMap.ext
    intro y
    change ((↑d⁻¹ : R) ^ 2) • opEnd (n := n) γ (cubicAdjoint n γ x) (opEnd (n := n) γ x y) = y
    rw [opEnd_apply, opEnd_apply, (op_inverse γ h x y).2, smul_smul, cancel, one_smul]
  refine ⟨⟨f, g, fg, gf⟩, opEnd_apply γ x, ?_⟩
  change g x = (↑d⁻¹ : R) • cubicAdjoint n γ x
  have eq : f ((↑d⁻¹ : R) • cubicAdjoint n γ x) = x := by
    change opEnd (n := n) γ x ((↑d⁻¹ : R) • cubicAdjoint n γ x) = x
    rw [map_smul, opEnd_apply, op_adjoint γ h, smul_smul, ← hd, Units.inv_mul, one_smul]
  calc
    g x = g (f ((↑d⁻¹ : R) • cubicAdjoint n γ x)) := congrArg g eq.symm
    _ = _ := by
      change (g * f) ((↑d⁻¹ : R) • cubicAdjoint n γ x) = _
      rw [gf, Module.End.one_apply]

section JordanStructure

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem extend_self_apply (x : V) :
    extendCoordinates R x = coordinatesBaseChange R ((TensorProduct.lid R V).symm x) := rfl

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem extend_self_injective :
    Function.Injective (extendCoordinates (R := R) (A := A) R) :=
  fun _ _ hh => (TensorProduct.lid R V).symm.injective ((coordinatesBaseChange R).injective hh)

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem extend_self_smul (r : R) (x : V) :
    extendCoordinates R (r • x) = r • extendCoordinates R x := by
  simp only [extend_self_apply, map_smul]

open private tensor_map_smul coordinate_ext from LinearAlgebraicGroups.Albert.CubicIdentities

variable (h : IsOctonionNorm n)

private def tensorOperator (S : Type u) [CommRing S] [Algebra R S] :
    QuadraticMap S (S ⊗[R] V) (Module.End S (S ⊗[R] V)) :=
  letI := h.projective
  let f : S ⊗[R] V ≃ₗ[S] Coordinates S (S ⊗[R] A) := coordinatesBaseChange S
  f.symm.conj.toLinearMap.compQuadraticMap
    ((opQuadratic (n := normBaseChange S n) (baseChangedWeights S γ)).comp f.toLinearMap)

private theorem tensorOperator_apply (S : Type u) [CommRing S] [Algebra R S]
    (x y : S ⊗[R] V) :
    letI := h.projective
    coordinatesBaseChange S (tensorOperator γ h S x y) =
      applyCubicOperator (normBaseChange S n) (baseChangedWeights S γ)
        (coordinatesBaseChange S x) (coordinatesBaseChange S y) := by
  let := h.projective
  change coordinatesBaseChange S ((coordinatesBaseChange S).symm
    (opQuadratic (n := normBaseChange S n) (baseChangedWeights S γ)
      (coordinatesBaseChange S x) (coordinatesBaseChange S y))) = _
  rw [LinearEquiv.apply_symm_apply, opQuadratic_apply]

private theorem coordinate_operator_natural
    (S : Type w) [CommRing S] [Algebra R S] (D : Type z) [CommRing D] [Algebra R D]
    (f : S →ₐ[R] D) (x y : Coordinates S (S ⊗[R] A)) :
    letI := h.projective
    let F := mapExtendedCoordinates S f
    F (applyCubicOperator (normBaseChange S n) (baseChangedWeights S γ) x y) =
      applyCubicOperator (normBaseChange D n) (baseChangedWeights D γ) (F x) (F y) := by
  let := h.projective
  let qS := normBaseChange S n
  let qD := normBaseChange D n
  let δS := baseChangedWeights S γ
  let δD := baseChangedWeights D γ
  let m := mapExtendedCoordinates S (A := A) f
  have map_smul (r : S) (z : Coordinates S (S ⊗[R] A)) : m (r • z) = f r • m z := by
    apply coordinate_ext
    · intro i
      simp only [m, CubicSpecification.mapExtendedCoordinates, Prod.smul_fst, Pi.smul_apply,
        smul_eq_mul, map_mul]
    · intro i
      exact tensor_map_smul S f r (z.2 i)
  have map_add (a b : Coordinates S (S ⊗[R] A)) : m (a + b) = m a + m b := by
    apply coordinate_ext <;> intro i <;>
      simp only [m, CubicSpecification.mapExtendedCoordinates, Prod.fst_add, Prod.snd_add,
        Pi.add_apply, _root_.map_add]
  have map_sub (a b : Coordinates S (S ⊗[R] A)) : m (a - b) = m a - m b := by
    apply coordinate_ext <;> intro i <;>
      simp only [m, CubicSpecification.mapExtendedCoordinates, Prod.fst_sub, Prod.snd_sub,
        Pi.sub_apply, _root_.map_sub]
  have adj (a : Coordinates S (S ⊗[R] A)) :
      cubicAdjoint qD δD (m a) = m (cubicAdjoint qS δS a) :=
    (cubic_extension_naturality γ S (D := D) h f a a).2.1
  have trace (a b : Coordinates S (S ⊗[R] A)) :
      tracePairing qD δD (m a) (m b) = f (tracePairing qS δS a b) :=
    (cubic_extension_naturality γ S (D := D) h f a b).2.2
  have cross (a b : Coordinates S (S ⊗[R] A)) :
      m (adjointCross qS δS a b) = adjointCross qD δD (m a) (m b) := by
    change m (cubicAdjoint qS δS (a + b) - cubicAdjoint qS δS a - cubicAdjoint qS δS b) =
      cubicAdjoint qD δD (m a + m b) - cubicAdjoint qD δD (m a) - cubicAdjoint qD δD (m b)
    simp only [map_sub, ← adj, map_add]
  change m (tracePairing qS δS x y • x - adjointCross qS δS (cubicAdjoint qS δS x) y) = _
  simp only [map_sub, map_smul, cross, ← adj, ← trace]
  rfl

theorem cubic_operator_naturality : QuadraticOperatorSpecification.naturalityType.{u, v, w, z} := by
  intro R A _ _ _ _ _ n γ h S _ _ D _ _ f x y
  exact coordinate_operator_natural γ h S D f x y

private theorem extended_operator_natural {S D : Type u} [CommRing S] [CommRing D]
    [Algebra R S] [Algebra R D] (f : S →ₐ[R] D)
    (x y : S ⊗[R] V) :
    f.toLinearMap.rTensor V (tensorOperator γ h S x y) =
      tensorOperator γ h D (f.toLinearMap.rTensor V x) (f.toLinearMap.rTensor V y) := by
  let := h.projective
  let m := mapExtendedCoordinates S (A := A) f
  have natural (z : S ⊗[R] V) :
      coordinatesBaseChange D (f.toLinearMap.rTensor V z) = m (coordinatesBaseChange S z) :=
    (coordinates_extension_naturality S f z).symm
  apply (coordinatesBaseChange D).injective
  rw [natural, tensorOperator_apply, tensorOperator_apply, natural x, natural y]
  exact coordinate_operator_natural γ h S D f _ _

private def hermitianOperatorLaw : QuadraticOperatorLaw R V where
  op S := tensorOperator γ h S
  natural f x y := extended_operator_natural γ h f x y

private theorem tensorTriple_apply (S : Type u) [CommRing S] [Algebra R S]
    (x y z : S ⊗[R] V) :
    letI := h.projective
    coordinatesBaseChange S ((hermitianOperatorLaw γ h).triple S x y z) =
      QuadraticOperatorSpecification.triple (normBaseChange S n) (baseChangedWeights S γ)
        (coordinatesBaseChange S x) (coordinatesBaseChange S y) (coordinatesBaseChange S z) := by
  let := h.projective
  change coordinatesBaseChange S
    (QuadraticMap.polarBilin (R := S) («N» := Module.End S (S ⊗[R] V))
      (tensorOperator γ h S) x z y) = _
  rw [QuadraticMap.polarBilin_apply_apply]
  change coordinatesBaseChange S
    (tensorOperator γ h S (x + z) y - tensorOperator γ h S x y - tensorOperator γ h S z y) = _
  simp only [map_sub, tensorOperator_apply, map_add]
  rfl

set_option maxHeartbeats 1000000 in
/-- The weighted Hermitian quadratic Jordan algebra in its 27 coordinates. -/
def weightedHermitianJordan : QuadraticJordan R V where
  toQuadraticOperatorLaw := hermitianOperatorLaw γ h
  unit := e
  op_unit S _ _ := by
    let := h.projective
    apply LinearMap.ext
    intro y
    change tensorOperator γ h S (1 ⊗ₜ[R] e) y = y
    apply (coordinatesBaseChange S).injective
    rw [tensorOperator_apply]
    change applyCubicOperator _ _ (extendCoordinates S e) (coordinatesBaseChange S y) = _
    rw [extendCoordinates_unit, opUnit]
  fundamental S _ _ x y := by
    let := h.projective
    apply LinearMap.ext
    intro z
    change tensorOperator γ h S (tensorOperator γ h S x y) z =
      tensorOperator γ h S x (tensorOperator γ h S y (tensorOperator γ h S x z))
    apply (coordinatesBaseChange S).injective
    simp only [tensorOperator_apply]
    exact fundamental (baseChangedWeights S γ) (octonion_norm_baseChange h S) _ _ _
  commuting S _ _ x y z := by
    let := h.projective
    change tensorOperator γ h S x ((hermitianOperatorLaw γ h).triple S y x z) =
      (hermitianOperatorLaw γ h).triple S (tensorOperator γ h S x y) z x
    apply (coordinatesBaseChange S).injective
    simp only [tensorOperator_apply, tensorTriple_apply]
    exact commuting (baseChangedWeights S γ) (octonion_norm_baseChange h S) _ _ _

private theorem extended_constant_operator (S : Type u) [CommRing S] [Algebra R S] (x y : V) :
    letI := h.projective
    applyCubicOperator (normBaseChange S n) (baseChangedWeights S γ)
      (extendCoordinates S x) (extendCoordinates S y) = extendCoordinates S (U x y) := by
  let := h.projective
  let q := normBaseChange S n
  let δ := baseChangedWeights S γ
  let ι := extendCoordinates (R := R) (A := A) S
  have cross (x y : V) : adjointCross q δ (ι x) (ι y) = ι (B x y) := by
    change cubicAdjoint q δ (ι x + ι y) - cubicAdjoint q δ (ι x) - cubicAdjoint q δ (ι y) = _
    rw [← extendCoordinates_add, cubicAdjoint_extend, cubicAdjoint_extend,
      cubicAdjoint_extend, ← extendCoordinates_sub, ← extendCoordinates_sub]
    rfl
  have smul (r : R) (x : V) : ι (r • x) = algebraMap R S r • ι x := by
    change coordinatesBaseChange S (1 ⊗ₜ[R] (r • x)) = _
    rw [← TensorProduct.smul_tmul, ← algebraMap_smul S r (1 : S), ← TensorProduct.smul_tmul', map_smul]
    rfl
  change tracePairing q δ (ι x) (ι y) • ι x - adjointCross q δ (cubicAdjoint q δ (ι x)) (ι y) =
    ι (T x y • x - B (Q x) y)
  rw [cubicAdjoint_extend, tracePairing_extend, cross, ← smul, ← extendCoordinates_sub]

private theorem ground_operator (x y : V) : (weightedHermitianJordan γ h).groundOp x y = U x y := by
  let := h.projective
  apply extend_self_injective
  change coordinatesBaseChange R ((TensorProduct.lid R V).symm
    ((TensorProduct.lid R V) (tensorOperator γ h R (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)))) = _
  rw [LinearEquiv.symm_apply_apply, tensorOperator_apply]
  exact extended_constant_operator γ h R x y

open private groundProduct_at from LinearAlgebraicGroups.Albert.QuadraticJordan

set_option maxHeartbeats 1000000 in
private theorem ground_product (d : Rˣ) (x y : V) :
    assemble n γ ((weightedHermitianJordan γ h).groundProduct d x y) =
      (↑d⁻¹ : R) • (assemble n γ x * assemble n γ y + assemble n γ y * assemble n γ x) := by
  let := h.projective
  let J := weightedHermitianJordan γ h
  let invTwo := (↑d⁻¹ : R)
  have point (x y : V) : extendCoordinates R (U x y) =
      coordinatesBaseChange R (tensorOperator γ h R (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)) := by
    rw [tensorOperator_apply]
    exact (extended_constant_operator γ h R x y).symm
  have form : J.groundProduct d x y = invTwo •
      (U (x + y) e - U x e - U y e) := by
    apply extend_self_injective
    have add : (1 : R) ⊗ₜ[R] (x + y) = 1 ⊗ₜ[R] x + 1 ⊗ₜ[R] y := TensorProduct.tmul_add _ _ _
    rw [extend_self_apply, groundProduct_at, QuadraticJordan.linearProduct_apply, map_smul,
      Algebra.algebraMap_self, RingHom.id_apply, extend_self_smul]
    congr 1
    change coordinatesBaseChange R
      ((hermitianOperatorLaw γ h).triple R (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] e) (1 ⊗ₜ[R] y)) = _
    rw [extendCoordinates_sub, extendCoordinates_sub, point, point, point]
    change coordinatesBaseChange R
       (tensorOperator γ h R (1 ⊗ₜ[R] x + 1 ⊗ₜ[R] y) (1 ⊗ₜ[R] e) -
         tensorOperator γ h R (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] e) -
         tensorOperator γ h R (1 ⊗ₜ[R] y) (1 ⊗ₜ[R] e)) = _
    rw [add, map_sub, map_sub]
  let f : V →ₗ[R] Mat A := (hermitian n γ).subtype.comp (coordinateMap h.toNormLaws γ)
  have sq (x : V) : f (U x e) = f x * f x := matrix_square γ h x
  change f (J.groundProduct d x y) = invTwo • (f x * f y + f y * f x)
  rw [form, map_smul, map_sub, map_sub, sq, sq, sq, map_add, add_mul, mul_add, mul_add]
  congr 1
  abel

end JordanStructure

theorem weighted_hermitian_quadratic_jordan :
    QuadraticOperatorSpecification.jordanStructureType.{u, v} := by
  intro R A _ _ _ _ _ n γ h
  let := h.projective
  exact ⟨weightedHermitianJordan γ h, rfl, ground_operator γ h, tensorOperator_apply γ h,
    fun d _ x y => ground_product γ h d x y⟩

end

end LinearAlgebraicGroups.Albert
