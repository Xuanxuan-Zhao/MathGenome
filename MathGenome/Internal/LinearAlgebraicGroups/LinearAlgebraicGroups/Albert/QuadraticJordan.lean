import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.QuadraticJordan
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff

import Mathlib.Tactic.LinearCombination

namespace LinearAlgebraicGroups.Albert

universe u v w

open TensorProduct
abbrev operatorOfProduct {S : Type u} [CommRing S]
    {P : Type v} [AddCommGroup P] [Module S P]
    (p : LinearMap.BilinMap S P P) :=
  Specs.LinearAlgebraicGroups.Albert.operatorOfProduct p

abbrev QuadraticOperatorLaw := Specs.LinearAlgebraicGroups.Albert.QuadraticOperatorLaw
abbrev QuadraticJordan := Specs.LinearAlgebraicGroups.Albert.QuadraticJordan
abbrev LinearJordan := Specs.LinearAlgebraicGroups.Albert.LinearJordan

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

namespace QuadraticOperatorLaw

abbrev triple (Q : QuadraticOperatorLaw R M) (S : Type u) [CommRing S] [Algebra R S] :=
  Specs.LinearAlgebraicGroups.Albert.QuadraticOperatorLaw.triple Q S

end QuadraticOperatorLaw

namespace QuadraticJordan

abbrev Hom (J : QuadraticJordan R M) (K : QuadraticJordan R N) :=
  Specs.LinearAlgebraicGroups.Albert.QuadraticJordan.Hom J K

abbrev square (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S] :=
  Specs.LinearAlgebraicGroups.Albert.QuadraticJordan.square J S

abbrev groundOp (J : QuadraticJordan R M) :=
  Specs.LinearAlgebraicGroups.Albert.QuadraticJordan.groundOp J

abbrev groundSquare (J : QuadraticJordan R M) :=
  Specs.LinearAlgebraicGroups.Albert.QuadraticJordan.groundSquare J

abbrev linearProduct (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S] :=
  Specs.LinearAlgebraicGroups.Albert.QuadraticJordan.linearProduct J S

abbrev groundProduct (J : QuadraticJordan R M) :=
  Specs.LinearAlgebraicGroups.Albert.QuadraticJordan.groundProduct J

noncomputable abbrev baseChange (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S] :=
  Specs.LinearAlgebraicGroups.Albert.QuadraticJordan.baseChange J S

variable (J : QuadraticJordan R M)
variable (S : Type u) [CommRing S] [Algebra R S]

local notation "Jₛ" => S ⊗[R] M

/-- Polarization with both outer slots exposed as linear maps. -/
abbrev polar := Specs.LinearAlgebraicGroups.Albert.QuadraticJordan.polar J S

private theorem polar_apply (x z y : Jₛ) :
    J.polar S x z y = J.op S (x + z) y - J.op S x y - J.op S z y := rfl

theorem polar_symm (x z : Jₛ) : J.polar S x z = J.polar S z x :=
  QuadraticMap.polar_comm (J.op S) x z

private theorem op_add (x z : Jₛ) :
    J.op S (x + z) = J.op S x + J.op S z + J.polar S x z :=
  QuadraticMap.map_add (J.op S) x z

variable {S}

private theorem natural_polar {T : Type u} [CommRing T] [Algebra R T]
    (f : S →ₐ[R] T) (x z y : Jₛ) :
    f.toLinearMap.rTensor M (J.polar S x z y) =
      J.polar T (f.toLinearMap.rTensor M x) (f.toLinearMap.rTensor M z)
        (f.toLinearMap.rTensor M y) := by
  simp only [polar_apply, map_sub, J.natural, map_add]

variable (S)

local notation "e" => (1 ⊗ₜ[R] J.unit : Jₛ)
local notation "U" => J.op S
local notation "B" => J.polar S

private theorem commuting' (x y z : Jₛ) : U x (B y z x) = B (U x y) x z :=
  J.commuting S x y z

private theorem polar_unit (x z : Jₛ) : B x z e = B x e z := by
  simpa only [J.op_unit, Module.End.one_apply] using J.commuting' S e x z

private theorem polar_diag (x : Jₛ) : B x x = (2 : ℕ) • U x := by
  simpa only [polar, Specs.LinearAlgebraicGroups.Albert.QuadraticJordan.polar,
    QuadraticMap.polarBilin_apply_apply] using
    (@QuadraticMap.polar_self S Jₛ (Module.End S Jₛ) _ _ _ _ _ U x)

private theorem polar_unit_flip (x z : Jₛ) : B x e z = B z e x := by
  rw [← J.polar_unit S x z, J.polar_symm S x z, J.polar_unit S z x]

private theorem polar_unit_unit (x : Jₛ) : B x e e = (2 : S) • x := by
  have h := J.polar_unit S e x
  rw [J.polar_symm S e x] at h
  rw [h]
  rw [J.polar_diag, J.op_unit]
  simp [two_smul]

private theorem op_unit_add_smul (a : Jₛ) (t : S) :
    U (e + t • a) = 1 + (t * t) • U a + t • B a e := by
  rw [J.op_add, J.op_unit, (J.op S).map_smul, J.polar_symm S e (t • a), LinearMap.map_smul₂]

private theorem op_unit_add_smul_apply_unit (a : Jₛ) (t : S) :
    U (e + t • a) e = e + (t * t) • U a e + t • ((2 : S) • a) := by
  rw [J.op_unit_add_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, J.polar_unit_unit]

private noncomputable abbrev polynomialInclusion : S →ₐ[R] Polynomial S :=
  IsScalarTower.toAlgHom R S (Polynomial S)

private theorem polynomialInclusion_apply (s : S) :
    (polynomialInclusion (R := R) (S := S)) s = Polynomial.C s := rfl

/-- Coefficient extraction works even when the module of coefficients is not free. -/
private noncomputable def coefficient (n : ℕ) : Polynomial S ⊗[R] M →ₗ[R] Jₛ :=
  ((Polynomial.lcoeff S n).restrictScalars R).rTensor M

private theorem coefficient_smul_image (n : ℕ) (p : Polynomial S) (x : Jₛ) :
    coefficient (R := R) (M := M) S n
      (p • (polynomialInclusion (R := R) (S := S)).toLinearMap.rTensor M x) =
      p.coeff n • x := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, polynomialInclusion_apply, smul_tmul', coefficient,
      LinearMap.rTensor_tmul, LinearMap.restrictScalars_apply, Polynomial.lcoeff_apply,
      smul_eq_mul, Polynomial.coeff_mul_C, ← smul_eq_mul, ← smul_tmul']
  | add x y hx hy =>
    simp only [map_add, smul_add, hx, hy]

private theorem coefficient_image (n : ℕ) (x : Jₛ) :
    coefficient (R := R) (M := M) S n
      ((polynomialInclusion (R := R) (S := S)).toLinearMap.rTensor M x) =
      (1 : Polynomial S).coeff n • x := by
  simpa only [one_smul] using coefficient_smul_image S n (1 : Polynomial S) x

private theorem two_smul_op (a z : Jₛ) :
    (2 : S) • U a z = B a e (B a e z) - B (U a e) e z := by
  let T := Polynomial S
  let f := (polynomialInclusion (R := R) (S := S)).toLinearMap.rTensor M
  let t : T := Polynomial.X
  let et : T ⊗[R] M := 1 ⊗ₜ[R] J.unit
  have he : f e = et := by simp [f, et]
  have hop (x y : Jₛ) : J.op T (f x) (f y) = f (U x y) :=
    (J.natural (polynomialInclusion (R := R) (S := S)) x y).symm
  have hpolar (x z y : Jₛ) : J.polar T (f x) (f z) (f y) = f (B x z y) :=
    (J.natural_polar (polynomialInclusion (R := R) (S := S)) x z y).symm
  have h := J.commuting' T (et + t • f a) et (f z)
  rw [J.op_unit_add_smul_apply_unit, J.op_unit_add_smul] at h
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_add, map_smul, smul_add, smul_smul] at h
  simp only [show (1 ⊗ₜ[R] J.unit : T ⊗[R] M) = f e from he.symm,
    show et = f e from he.symm, hop, hpolar] at h
  have hp := congrArg (coefficient (R := R) (M := M) S 2) h
  change coefficient S 2 _ = coefficient S 2 _ at hp
  dsimp only [f, t, T] at hp
  simp [coefficient_smul_image, coefficient_image, Polynomial.coeff_X_mul,
    Polynomial.coeff_one, Polynomial.coeff_X] at hp
  rw [J.polar_symm S e z, J.polar_unit_unit S z, J.polar_unit_flip S z a,
    J.polar_diag S a, map_smul] at hp
  simp only [two_smul, LinearMap.add_apply] at hp ⊢
  apply eq_sub_of_add_eq
  -- At degree two, the same term occurs twice on the left and four times on the right.
  apply add_right_cancel (b := U a z + U a z)
  calc
    (U a z + U a z + B (U a e) e z) + (U a z + U a z) =
        B (U a e) e z + ((U a z + U a z) + (U a z + U a z)) := by abel
    _ = (U a z + U a z) + B a e (B a e z) := hp.symm
    _ = B a e (B a e z) + (U a z + U a z) := add_comm _ _

variable (d : Rˣ) (hd : (↑d : R) = 2)

local notation "c" => algebraMap R S (Units.val (d⁻¹))
local notation "p" => J.linearProduct S d

theorem linearProduct_apply (x y : Jₛ) :
    p x y = c • J.toQuadraticOperatorLaw.triple S x e y := rfl

private theorem half_mul_two (hd : (↑d : R) = 2) : c * (2 : S) = 1 := by
  simpa only [map_mul, map_one, hd, map_ofNat] using
    congrArg (algebraMap R S) (Units.inv_mul d)

private theorem product_apply (x y : Jₛ) : p x y = c • B x e y := by
  rw [J.linearProduct_apply]
  congr 1
  exact J.polar_unit S x y

theorem linearProduct_comm (x y : Jₛ) : p x y = p y x := by
  rw [J.product_apply, J.product_apply, J.polar_unit_flip]

include hd

theorem linearProduct_unit (x : Jₛ) : p e x = x := by
  rw [J.product_apply, J.polar_unit_flip S e x, J.polar_unit_unit, smul_smul,
    half_mul_two S d hd, one_smul]

theorem linearProduct_square (x : Jₛ) : p x x = J.square S x := by
  rw [J.linearProduct_apply]
  change c • B x x e = U x e
  rw [J.polar_diag]
  simp only [two_nsmul, LinearMap.add_apply]
  rw [← two_smul S, smul_smul, half_mul_two S d hd, one_smul]

theorem op_eq_operatorOfProduct (x : Jₛ) : U x = operatorOfProduct p x := by
  apply LinearMap.ext
  intro y
  change U x y = (2 : S) • p x (p x y) - p (p x x) y
  rw [J.linearProduct_square S d hd, J.product_apply, J.product_apply, J.product_apply,
    map_smul, smul_smul, smul_smul]
  have hh : (2 : S) * c * c = c := by
    rw [mul_comm (2 : S) c, half_mul_two S d hd, one_mul]
  rw [hh]
  change U x y = c • (B x e (B x e y)) - c • (B (U x e) e y)
  rw [← smul_sub c (B x e (B x e y)) (B (U x e) e y), ← J.two_smul_op,
    smul_smul, half_mul_two S d hd, one_smul]

theorem linearProduct_jordan (x y : Jₛ) : p (p x y) (p x x) = p x (p y (p x x)) := by
  have h := J.commuting' S x y e
  rw [J.polar_unit S (U x y) x, J.polar_unit_flip S y x,
    J.polar_unit_flip S (U x y) x] at h
  have hcomm : U x (p x y) = p x (U x y) := by
    rw [J.product_apply, J.product_apply, map_smul, h]
  rw [J.op_eq_operatorOfProduct S d hd x] at hcomm
  change (2 : S) • p x (p x (p x y)) - p (p x x) (p x y) =
    p x ((2 : S) • p x (p x y) - p (p x x) y) at hcomm
  rw [map_sub, map_smul] at hcomm
  rw [J.linearProduct_comm S d (p x y) (p x x), J.linearProduct_comm S d y (p x x)]
  exact sub_right_inj.mp hcomm
omit hd

private theorem linearProduct_natural {T : Type u} [CommRing T] [Algebra R T]
    (f : S →ₐ[R] T) (x y : Jₛ) :
    let F := f.toLinearMap.rTensor M
    F (p x y) = J.linearProduct T d (F x) (F y) := by
  dsimp
  rw [J.linearProduct_apply, J.linearProduct_apply]
  change f.toLinearMap.rTensor M (c • B x y e) =
    algebraMap R T (↑d⁻¹ : R) • J.polar T (f.toLinearMap.rTensor M x)
      (f.toLinearMap.rTensor M y) (1 ⊗ₜ[R] J.unit)
  rw [IsScalarTower.algebraMap_smul S, map_smul, J.natural_polar,
    IsScalarTower.algebraMap_smul T]
  simp

private theorem groundProduct_at (x y : M) :
    (TensorProduct.lid R M).symm (J.groundProduct d x y) =
      J.linearProduct R d (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) := by
  change (TensorProduct.lid R M).symm
    ((TensorProduct.lid R M) (J.linearProduct R d
      ((TensorProduct.lid R M).symm x) ((TensorProduct.lid R M).symm y))) = _
  rw [LinearEquiv.symm_apply_apply, lid_symm_apply, lid_symm_apply]

theorem groundProduct_baseChange : (J.groundProduct d).baseChange S = p := by
  apply AlgebraTensorModule.ext
  intro s x
  apply AlgebraTensorModule.ext
  intro t y
  have h := J.linearProduct_natural R d (Algebra.ofId R S) (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)
  dsimp at h
  rw [← J.groundProduct_at] at h
  simp only [lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one] at h
  rw [LinearMap.BilinMap.baseChange_tmul, ← mul_one (s * t), ← smul_eq_mul,
    ← smul_tmul', h]
  have hst (a : S) (z : M) : a • (1 ⊗ₜ[R] z) = a ⊗ₜ[R] z := by
    simp [smul_tmul']
  rw [← hst s x, ← hst t y, LinearMap.map_smul₂, map_smul, smul_smul]

/-- The linear Jordan algebra obtained when two is invertible. -/
noncomputable def toLinearJordan (hd : (↑d : R) = 2) : LinearJordan R M where
  unit := J.unit
  product := J.groundProduct d
  comm x y := by
    apply (TensorProduct.lid R M).symm.injective
    rw [J.groundProduct_at, J.groundProduct_at, J.linearProduct_comm]
  unit_mul x := by
    apply (TensorProduct.lid R M).symm.injective
    rw [J.groundProduct_at, J.linearProduct_unit R d hd, lid_symm_apply]
  jordan S _ _ x y := by
    dsimp
    rw [J.groundProduct_baseChange S d]
    exact J.linearProduct_jordan S d hd x y


end QuadraticJordan

section LinearIdentities

variable {A : Type*} [CommRing A] {P : Type*} [AddCommGroup P] [Module A P]
variable (p : LinearMap.BilinMap A P P)

private def associator (x y z : P) : P := p (p x y) z - p x (p y z)

private theorem cancel_two (d : Aˣ) (hd : (↑d : A) = 2) {z : P} (h : z + z = 0) :
    z = 0 := by
  apply smul_left_cancel d
  simpa only [Units.smul_def, hd, two_smul, smul_zero] using h

private theorem operatorOfProduct_apply (x y : P) :
    operatorOfProduct p x y = (2 : A) • p x (p x y) - p (p x x) y := rfl

macro "expand_jordan" hc:term : tactic => do
  let rule ← `(Lean.Parser.Tactic.simpLemma| $hc:term)
  `(tactic|
    (simp only [associator, operatorOfProduct_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.neg_apply, LinearMap.zero_apply, two_smul, LinearMap.map_add₂, LinearMap.map_sub₂,
      LinearMap.map_neg₂, LinearMap.map_zero₂, map_add, map_sub, map_neg, map_zero,
      sub_zero, zero_sub, add_zero, zero_add]
     try simp only [$rule]
     abel))

variable (hc : ∀ x y, p x y = p y x)
variable (hj : ∀ x y, p (p x y) (p x x) = p x (p y (p x x)))

include hj in
private theorem jordanAssoc (x t : P) :
    associator p x t (p x x) = 0 :=
  sub_eq_zero.mpr (hj x t)

include hc hj

private theorem jordanPartial (x y t : P) (d : Aˣ) (hd : (↑d : A) = 2) :
    associator p y t (p x x) + (2 : A) • associator p x t (p x y) = 0 := by
  apply cancel_two d hd
  linear_combination (norm := expand_jordan hc)
    jordanAssoc p hj (x + y) t - jordanAssoc p hj (x - y) t -
      (2 : ℤ) • jordanAssoc p hj y t

private theorem jordanFull (x y z t : P) (d : Aˣ) (hd : (↑d : A) = 2) :
    associator p x t (p y z) + associator p y t (p z x) +
      associator p z t (p x y) = 0 := by
  apply cancel_two d hd
  linear_combination (norm := expand_jordan hc)
    jordanPartial p hc hj (x + y) z t d hd - jordanPartial p hc hj x z t d hd -
      jordanPartial p hc hj y z t d hd

private theorem linear_commuting (d : Aˣ) (hd : (↑d : A) = 2) (x y z : P) :
    let U := operatorOfProduct p
    let B := fun x z y => U (x + z) y - U x y - U z y
    U x (B y z x) = B (U x y) x z := by
  dsimp
  have h1 := jordanAssoc p hj x (p y z)
  have h2 := jordanPartial p hc hj x (p x y) z d hd
  have h3 := jordanPartial p hc hj x (p y z) x d hd
  have h4 := jordanPartial p hc hj x z (p x y) d hd
  have h5 := jordanFull p hc hj z x (p x x) y d hd
  have h6 := congrArg (fun v => p v x) (jordanPartial p hc hj x y z d hd)
  have h7 := congrArg (fun v => p v x) (jordanPartial p hc hj x z y d hd)
  have h8 := congrArg (fun v => p v z) (jordanAssoc p hj x y)
  have h9 := congrArg (fun v => p v z) (jordanPartial p hc hj x y x d hd)
  linear_combination (norm := expand_jordan hc)
    (-4 : ℤ) • h1 + (2 : ℤ) • h2 + (2 : ℤ) • h3 + (-4 : ℤ) • h4 + (2 : ℤ) • h5 +
      (-2 : ℤ) • h6 + (-2 : ℤ) • h7 + (2 : ℤ) • h8 + (-2 : ℤ) • h9


omit hc hj in
private theorem cancel_two_eq (d : Aˣ) (hd : (↑d : A) = 2) {z w : P}
    (h : z + z = w + w) : z = w := by
  apply smul_left_cancel d
  simpa only [Units.smul_def, hd, two_smul] using h

-- The degree-(4,2,1) dyadic certificate uses substitutions in the Jordan
-- identity and its two polarizations, followed by bilinearity.
set_option maxHeartbeats 6000000 in
private theorem linear_fundamental (d : Aˣ) (hd : (↑d : A) = 2) (x y z : P) :
    operatorOfProduct p (operatorOfProduct p x y) z =
      operatorOfProduct p x (operatorOfProduct p y (operatorOfProduct p x z)) := by
  apply cancel_two_eq d hd
  apply cancel_two_eq d hd
  have h1 := jordanPartial p hc hj y (p x x) (p x (p x z)) d hd
  have h2 := jordanPartial p hc hj y (p x x) (p z (p x x)) d hd
  have h3 := jordanAssoc p hj x (p x (p y (p y z)))
  have h4 := jordanAssoc p hj x (p z (p y (p x y)))
  have h5 := jordanAssoc p hj x (p (p x z) (p y y))
  have h6 := jordanPartial p hc hj x (p x (p y (p x z))) y d hd
  have h7 := jordanPartial p hc hj x (p z (p x (p x y))) y d hd
  have h8 := jordanPartial p hc hj x (p z (p y (p x x))) y d hd
  have h9 := jordanPartial p hc hj x (p y (p y (p x z))) x d hd
  have h10 := jordanPartial p hc hj x (p y (p x z)) (p x y) d hd
  have h11 := jordanPartial p hc hj x (p x y) (p x (p y z)) d hd
  have h12 := jordanPartial p hc hj x (p x y) (p y (p x z)) d hd
  have h13 := jordanPartial p hc hj x x (p x (p y (p y z))) d hd
  have h14 := jordanPartial p hc hj x (p y z) (p x (p x y)) d hd
  have h15 := jordanPartial p hc hj x (p y z) (p y (p x x)) d hd
  have h16 := jordanPartial p hc hj x y (p x (p y (p x z))) d hd
  have h17 := jordanPartial p hc hj (p x y) x (p x z) d hd
  have h18 := jordanFull p hc hj z y (p x x) (p x (p x y)) d hd
  have h19 := jordanFull p hc hj z y (p x x) (p y (p x x)) d hd
  have h20 := jordanFull p hc hj z x (p x y) (p x (p x y)) d hd
  have h21 := jordanFull p hc hj z x (p x y) (p y (p x x)) d hd
  have h22 := jordanFull p hc hj y x (p x y) (p z (p x x)) d hd
  have h23 := jordanFull p hc hj y x (p z (p x y)) (p x x) d hd
  have h24 := jordanFull p hc hj y x (p y (p x (p x z))) x d hd
  have h25 := jordanFull p hc hj y x (p y (p z (p x x))) x d hd
  have h26 := jordanFull p hc hj y x (p z (p x (p x y))) x d hd
  have h27 := jordanFull p hc hj y x (p z (p y (p x x))) x d hd
  have h28 := jordanFull p hc hj y x (p x (p z (p x x))) y d hd
  have h29 := jordanFull p hc hj y x (p (p x x) (p x y)) z d hd
  have h30 := jordanFull p hc hj y (p x z) (p x x) (p x y) d hd
  have h31 := jordanFull p hc hj y (p x y) (p x x) (p x z) d hd
  have h32 := jordanFull p hc hj y (p y (p x z)) (p x x) x d hd
  have h33 := jordanFull p hc hj y (p x x) (p z (p x x)) y d hd
  have h34 := jordanFull p hc hj y (p x x) (p y (p x x)) z d hd
  have h35 := jordanFull p hc hj (p y z) x (p y (p x x)) x d hd
  have h36 := jordanFull p hc hj (p y y) (p x z) (p x x) x d hd
  have h37 := jordanFull p hc hj x (p x z) (p x y) (p x y) d hd
  have h38 := jordanFull p hc hj x (p x z) (p x x) (p y y) d hd
  have h39 := jordanFull p hc hj x (p x y) (p x (p y z)) x d hd
  have h40 := jordanFull p hc hj x (p x y) (p z (p x x)) y d hd
  have h41 := jordanFull p hc hj x (p x y) (p x (p x y)) z d hd
  have h42 := jordanFull p hc hj x (p x y) (p y (p x x)) z d hd
  have h43 := jordanFull p hc hj x (p z (p x y)) (p x x) y d hd
  have h44 := congrArg (fun v => p v (p x (p x y))) (jordanPartial p hc hj x z y d hd)
  simp only [LinearMap.map_zero₂] at h44
  have h45 := congrArg (fun v => p v (p y (p x x))) (jordanPartial p hc hj x z y d hd)
  simp only [LinearMap.map_zero₂] at h45
  have h46 := congrArg (fun v => p v (p x (p x y))) (jordanFull p hc hj z y x x d hd)
  simp only [LinearMap.map_zero₂] at h46
  have h47 := congrArg (fun v => p v (p y (p x x))) (jordanFull p hc hj z y x x d hd)
  simp only [LinearMap.map_zero₂] at h47
  have h48 := congrArg (fun v => p v (p x x)) (jordanFull p hc hj z y (p x x) y d hd)
  simp only [LinearMap.map_zero₂] at h48
  have h49 := congrArg (fun v => p v (p x x)) (jordanFull p hc hj y (p y z) x x d hd)
  simp only [LinearMap.map_zero₂] at h49
  have h50 := congrArg (fun v => p v (p x x)) (jordanFull p hc hj y x (p x z) y d hd)
  simp only [LinearMap.map_zero₂] at h50
  have h51 := congrArg (fun v => p v (p x x)) (jordanFull p hc hj y x (p x y) z d hd)
  simp only [LinearMap.map_zero₂] at h51
  have h52 := congrArg (fun v => p v (p x x)) (congrArg (fun v => p v y) (jordanPartial p hc hj x y z d hd))
  simp only [LinearMap.map_zero₂] at h52
  have h53 := congrArg (fun v => p v (p x x)) (congrArg (fun v => p v y) (jordanFull p hc hj z y x x d hd))
  simp only [LinearMap.map_zero₂] at h53
  have h54 := congrArg (fun v => p v (p y (p x z))) (jordanPartial p hc hj x x y d hd)
  simp only [LinearMap.map_zero₂] at h54
  have h55 := congrArg (fun v => p v (p z (p x y))) (jordanPartial p hc hj x x y d hd)
  simp only [LinearMap.map_zero₂] at h55
  have h56 := congrArg (fun v => p v (p z (p x y))) (jordanPartial p hc hj x y x d hd)
  simp only [LinearMap.map_zero₂] at h56
  have h57 := congrArg (fun v => p v (p x y)) (jordanAssoc p hj x (p y z))
  simp only [LinearMap.map_zero₂] at h57
  have h58 := congrArg (fun v => p v (p x y)) (jordanPartial p hc hj x (p x y) z d hd)
  simp only [LinearMap.map_zero₂] at h58
  have h59 := congrArg (fun v => p v (p x y)) (jordanPartial p hc hj x (p x z) y d hd)
  simp only [LinearMap.map_zero₂] at h59
  have h60 := congrArg (fun v => p v (p x y)) (jordanPartial p hc hj x z (p x y) d hd)
  simp only [LinearMap.map_zero₂] at h60
  have h61 := congrArg (fun v => p v (p x y)) (jordanFull p hc hj z y (p x x) x d hd)
  simp only [LinearMap.map_zero₂] at h61
  have h62 := congrArg (fun v => p v (p x y)) (jordanFull p hc hj z x (p x y) x d hd)
  simp only [LinearMap.map_zero₂] at h62
  have h63 := congrArg (fun v => p v (p x y)) (jordanFull p hc hj z x (p x x) y d hd)
  simp only [LinearMap.map_zero₂] at h63
  have h64 := congrArg (fun v => p v (p x y)) (congrArg (fun v => p v x) (jordanPartial p hc hj x y z d hd))
  simp only [LinearMap.map_zero₂] at h64
  have h65 := congrArg (fun v => p v (p x y)) (congrArg (fun v => p v x) (jordanFull p hc hj z y x x d hd))
  simp only [LinearMap.map_zero₂] at h65
  have h66 := congrArg (fun v => p v (p x y)) (congrArg (fun v => p v z) (jordanPartial p hc hj x x y d hd))
  simp only [LinearMap.map_zero₂] at h66
  have h67 := congrArg (fun v => p v (p x y)) (congrArg (fun v => p v z) (jordanPartial p hc hj x y x d hd))
  simp only [LinearMap.map_zero₂] at h67
  have h68 := congrArg (fun v => p v (p x z)) (jordanPartial p hc hj y x (p x x) d hd)
  simp only [LinearMap.map_zero₂] at h68
  have h69 := congrArg (fun v => p v x) (jordanPartial p hc hj y (p x x) (p x z) d hd)
  simp only [LinearMap.map_zero₂] at h69
  have h70 := congrArg (fun v => p v x) (jordanPartial p hc hj y (p x z) (p x x) d hd)
  simp only [LinearMap.map_zero₂] at h70
  have h71 := congrArg (fun v => p v x) (jordanPartial p hc hj y x (p x (p x z)) d hd)
  simp only [LinearMap.map_zero₂] at h71
  have h72 := congrArg (fun v => p v x) (jordanPartial p hc hj y x (p z (p x x)) d hd)
  simp only [LinearMap.map_zero₂] at h72
  have h73 := congrArg (fun v => p v x) (jordanAssoc p hj x (p y (p y z)))
  simp only [LinearMap.map_zero₂] at h73
  have h74 := congrArg (fun v => p v x) (jordanPartial p hc hj x (p x (p y z)) y d hd)
  simp only [LinearMap.map_zero₂] at h74
  have h75 := congrArg (fun v => p v x) (jordanPartial p hc hj x (p y (p x z)) y d hd)
  simp only [LinearMap.map_zero₂] at h75
  have h76 := congrArg (fun v => p v x) (jordanPartial p hc hj x (p z (p x y)) y d hd)
  simp only [LinearMap.map_zero₂] at h76
  have h77 := congrArg (fun v => p v x) (jordanPartial p hc hj x (p y z) (p x y) d hd)
  simp only [LinearMap.map_zero₂] at h77
  have h78 := congrArg (fun v => p v x) (jordanPartial p hc hj x y (p x (p y z)) d hd)
  simp only [LinearMap.map_zero₂] at h78
  have h79 := congrArg (fun v => p v x) (jordanPartial p hc hj x y (p y (p x z)) d hd)
  simp only [LinearMap.map_zero₂] at h79
  have h80 := congrArg (fun v => p v x) (jordanPartial p hc hj x y (p z (p x y)) d hd)
  simp only [LinearMap.map_zero₂] at h80
  have h81 := congrArg (fun v => p v x) (jordanPartial p hc hj x z (p y (p x y)) d hd)
  simp only [LinearMap.map_zero₂] at h81
  have h82 := congrArg (fun v => p v x) (jordanPartial p hc hj (p x y) z x d hd)
  simp only [LinearMap.map_zero₂] at h82
  have h83 := congrArg (fun v => p v x) (jordanFull p hc hj z y x (p y (p x x)) d hd)
  simp only [LinearMap.map_zero₂] at h83
  have h84 := congrArg (fun v => p v x) (jordanFull p hc hj z y (p x x) (p x y) d hd)
  simp only [LinearMap.map_zero₂] at h84
  have h85 := congrArg (fun v => p v x) (jordanFull p hc hj z x (p x y) (p x y) d hd)
  simp only [LinearMap.map_zero₂] at h85
  have h86 := congrArg (fun v => p v x) (jordanFull p hc hj y x (p x z) (p x y) d hd)
  simp only [LinearMap.map_zero₂] at h86
  have h87 := congrArg (fun v => p v x) (jordanFull p hc hj y x (p x y) (p x z) d hd)
  simp only [LinearMap.map_zero₂] at h87
  have h88 := congrArg (fun v => p v x) (jordanFull p hc hj y x (p y (p x z)) x d hd)
  simp only [LinearMap.map_zero₂] at h88
  have h89 := congrArg (fun v => p v x) (jordanFull p hc hj y x (p x (p x z)) y d hd)
  simp only [LinearMap.map_zero₂] at h89
  have h90 := congrArg (fun v => p v x) (jordanFull p hc hj y x (p z (p x x)) y d hd)
  simp only [LinearMap.map_zero₂] at h90
  have h91 := congrArg (fun v => p v x) (jordanFull p hc hj y x (p y (p x x)) z d hd)
  simp only [LinearMap.map_zero₂] at h91
  have h92 := congrArg (fun v => p v x) (jordanFull p hc hj y (p x z) (p x x) y d hd)
  simp only [LinearMap.map_zero₂] at h92
  have h93 := congrArg (fun v => p v x) (congrArg (fun v => p v (p x z)) (jordanPartial p hc hj x y y d hd))
  simp only [LinearMap.map_zero₂] at h93
  have h94 := congrArg (fun v => p v x) (congrArg (fun v => p v x) (jordanFull p hc hj z y (p x x) y d hd))
  simp only [LinearMap.map_zero₂] at h94
  have h95 := congrArg (fun v => p v x) (congrArg (fun v => p v x) (jordanFull p hc hj y x (p x z) y d hd))
  simp only [LinearMap.map_zero₂] at h95
  have h96 := congrArg (fun v => p v x) (congrArg (fun v => p v x) (congrArg (fun v => p v y) (jordanPartial p hc hj x y z d hd)))
  simp only [LinearMap.map_zero₂] at h96
  have h97 := congrArg (fun v => p v x) (congrArg (fun v => p v x) (congrArg (fun v => p v y) (jordanPartial p hc hj x z y d hd)))
  simp only [LinearMap.map_zero₂] at h97
  have h98 := congrArg (fun v => p v x) (congrArg (fun v => p v x) (congrArg (fun v => p v y) (jordanFull p hc hj z y x x d hd)))
  simp only [LinearMap.map_zero₂] at h98
  have h99 := congrArg (fun v => p v x) (congrArg (fun v => p v y) (jordanPartial p hc hj x (p x y) z d hd))
  simp only [LinearMap.map_zero₂] at h99
  have h100 := congrArg (fun v => p v x) (congrArg (fun v => p v y) (jordanPartial p hc hj x x (p y z) d hd))
  simp only [LinearMap.map_zero₂] at h100
  have h101 := congrArg (fun v => p v x) (congrArg (fun v => p v y) (jordanPartial p hc hj x z (p x y) d hd))
  simp only [LinearMap.map_zero₂] at h101
  have h102 := congrArg (fun v => p v x) (congrArg (fun v => p v y) (jordanFull p hc hj z y x (p x x) d hd))
  simp only [LinearMap.map_zero₂] at h102
  have h103 := congrArg (fun v => p v x) (congrArg (fun v => p v y) (jordanFull p hc hj z y (p x x) x d hd))
  simp only [LinearMap.map_zero₂] at h103
  have h104 := congrArg (fun v => p v x) (congrArg (fun v => p v y) (jordanFull p hc hj y x (p x z) x d hd))
  simp only [LinearMap.map_zero₂] at h104
  have h105 := congrArg (fun v => p v x) (congrArg (fun v => p v y) (jordanFull p hc hj y x (p x x) z d hd))
  simp only [LinearMap.map_zero₂] at h105
  have h106 := congrArg (fun v => p v x) (congrArg (fun v => p v y) (congrArg (fun v => p v x) (jordanPartial p hc hj x z y d hd)))
  simp only [LinearMap.map_zero₂] at h106
  have h107 := congrArg (fun v => p v x) (congrArg (fun v => p v y) (congrArg (fun v => p v y) (jordanPartial p hc hj x x z d hd)))
  simp only [LinearMap.map_zero₂] at h107
  have h108 := congrArg (fun v => p v x) (congrArg (fun v => p v y) (congrArg (fun v => p v y) (jordanPartial p hc hj x z x d hd)))
  simp only [LinearMap.map_zero₂] at h108
  have h109 := congrArg (fun v => p v x) (congrArg (fun v => p v y) (congrArg (fun v => p v z) (jordanAssoc p hj x y)))
  simp only [LinearMap.map_zero₂] at h109
  have h110 := congrArg (fun v => p v x) (congrArg (fun v => p v z) (jordanPartial p hc hj x y (p x y) d hd))
  simp only [LinearMap.map_zero₂] at h110
  have h111 := congrArg (fun v => p v (p y y)) (jordanAssoc p hj x (p x z))
  simp only [LinearMap.map_zero₂] at h111
  have h112 := congrArg (fun v => p v (p y y)) (congrArg (fun v => p v x) (jordanAssoc p hj x z))
  simp only [LinearMap.map_zero₂] at h112
  have h113 := congrArg (fun v => p v (p y z)) (jordanAssoc p hj x (p x y))
  simp only [LinearMap.map_zero₂] at h113
  have h114 := congrArg (fun v => p v (p y z)) (jordanPartial p hc hj x x (p x y) d hd)
  simp only [LinearMap.map_zero₂] at h114
  have h115 := congrArg (fun v => p v (p y z)) (congrArg (fun v => p v x) (jordanAssoc p hj x y))
  simp only [LinearMap.map_zero₂] at h115
  have h116 := congrArg (fun v => p v (p y z)) (congrArg (fun v => p v x) (jordanPartial p hc hj x x y d hd))
  simp only [LinearMap.map_zero₂] at h116
  have h117 := congrArg (fun v => p v y) (jordanAssoc p hj x (p y (p x z)))
  simp only [LinearMap.map_zero₂] at h117
  have h118 := congrArg (fun v => p v y) (jordanAssoc p hj x (p z (p x y)))
  simp only [LinearMap.map_zero₂] at h118
  have h119 := congrArg (fun v => p v y) (jordanPartial p hc hj x (p x y) (p x z) d hd)
  simp only [LinearMap.map_zero₂] at h119
  have h120 := congrArg (fun v => p v y) (jordanPartial p hc hj x (p x z) (p x y) d hd)
  simp only [LinearMap.map_zero₂] at h120
  have h121 := congrArg (fun v => p v y) (jordanPartial p hc hj x x (p z (p x y)) d hd)
  simp only [LinearMap.map_zero₂] at h121
  have h122 := congrArg (fun v => p v y) (jordanPartial p hc hj x y (p z (p x x)) d hd)
  simp only [LinearMap.map_zero₂] at h122
  have h123 := congrArg (fun v => p v y) (jordanPartial p hc hj x z (p y (p x x)) d hd)
  simp only [LinearMap.map_zero₂] at h123
  have h124 := congrArg (fun v => p v y) (jordanFull p hc hj z x (p y (p x x)) x d hd)
  simp only [LinearMap.map_zero₂] at h124
  have h125 := congrArg (fun v => p v y) (jordanFull p hc hj y x (p z (p x x)) x d hd)
  simp only [LinearMap.map_zero₂] at h125
  have h126 := congrArg (fun v => p v y) (congrArg (fun v => p v x) (jordanPartial p hc hj x (p x y) z d hd))
  simp only [LinearMap.map_zero₂] at h126
  have h127 := congrArg (fun v => p v y) (congrArg (fun v => p v x) (jordanPartial p hc hj x (p x z) y d hd))
  simp only [LinearMap.map_zero₂] at h127
  have h128 := congrArg (fun v => p v y) (congrArg (fun v => p v z) (congrArg (fun v => p v x) (jordanAssoc p hj x y)))
  simp only [LinearMap.map_zero₂] at h128
  linear_combination (norm := expand_jordan hc)
    (1 : ℤ) • h1 +
    (-2 : ℤ) • h2 +
    (-1 : ℤ) • h3 +
    (-2 : ℤ) • h4 +
    (-1 : ℤ) • h5 +
    (1 : ℤ) • h6 +
    (4 : ℤ) • h7 +
    (-2 : ℤ) • h8 +
    (-3 : ℤ) • h9 +
    (3 : ℤ) • h10 +
    (-2 : ℤ) • h11 +
    (5 : ℤ) • h12 +
    (1 : ℤ) • h13 +
    (-1 : ℤ) • h14 +
    (2 : ℤ) • h15 +
    (-1 : ℤ) • h16 +
    (-8 : ℤ) • h17 +
    (-5 : ℤ) • h18 +
    (4 : ℤ) • h19 +
    (16 : ℤ) • h20 +
    (-11 : ℤ) • h21 +
    (3 : ℤ) • h22 +
    (4 : ℤ) • h23 +
    (8 : ℤ) • h24 +
    (-2 : ℤ) • h25 +
    (-8 : ℤ) • h26 +
    (2 : ℤ) • h27 +
    (-2 : ℤ) • h28 +
    (2 : ℤ) • h29 +
    (-4 : ℤ) • h30 +
    (4 : ℤ) • h31 +
    (-3 : ℤ) • h32 +
    (2 : ℤ) • h33 +
    (-2 : ℤ) • h34 +
    (-2 : ℤ) • h35 +
    (-1 : ℤ) • h36 +
    (8 : ℤ) • h37 +
    (1 : ℤ) • h38 +
    (-2 : ℤ) • h39 +
    (-5 : ℤ) • h40 +
    (-8 : ℤ) • h41 +
    (5 : ℤ) • h42 +
    (-4 : ℤ) • h43 +
    (8 : ℤ) • h44 +
    (-2 : ℤ) • h45 +
    (-8 : ℤ) • h46 +
    (2 : ℤ) • h47 +
    (2 : ℤ) • h48 +
    (2 : ℤ) • h49 +
    (-6 : ℤ) • h50 +
    (-2 : ℤ) • h51 +
    (2 : ℤ) • h52 +
    (-2 : ℤ) • h53 +
    (1 : ℤ) • h54 +
    (-2 : ℤ) • h55 +
    (4 : ℤ) • h56 +
    (-1 : ℤ) • h57 +
    (-5 : ℤ) • h58 +
    (7 : ℤ) • h59 +
    (-1 : ℤ) • h60 +
    (1 : ℤ) • h61 +
    (6 : ℤ) • h62 +
    (-1 : ℤ) • h63 +
    (-3 : ℤ) • h64 +
    (2 : ℤ) • h65 +
    (-2 : ℤ) • h66 +
    (1 : ℤ) • h67 +
    (1 : ℤ) • h68 +
    (1 : ℤ) • h69 +
    (-2 : ℤ) • h70 +
    (-9 : ℤ) • h71 +
    (6 : ℤ) • h72 +
    (2 : ℤ) • h73 +
    (-4 : ℤ) • h74 +
    (2 : ℤ) • h75 +
    (6 : ℤ) • h76 +
    (-3 : ℤ) • h77 +
    (4 : ℤ) • h78 +
    (1 : ℤ) • h79 +
    (-2 : ℤ) • h80 +
    (-2 : ℤ) • h81 +
    (4 : ℤ) • h82 +
    (-2 : ℤ) • h83 +
    (-3 : ℤ) • h84 +
    (4 : ℤ) • h85 +
    (12 : ℤ) • h86 +
    (-3 : ℤ) • h87 +
    (-1 : ℤ) • h88 +
    (9 : ℤ) • h89 +
    (-6 : ℤ) • h90 +
    (2 : ℤ) • h91 +
    (2 : ℤ) • h92 +
    (-2 : ℤ) • h93 +
    (-2 : ℤ) • h94 +
    (7 : ℤ) • h95 +
    (-6 : ℤ) • h96 +
    (-2 : ℤ) • h97 +
    (8 : ℤ) • h98 +
    (-4 : ℤ) • h99 +
    (1 : ℤ) • h100 +
    (1 : ℤ) • h101 +
    (-2 : ℤ) • h102 +
    (-1 : ℤ) • h103 +
    (-3 : ℤ) • h104 +
    (3 : ℤ) • h105 +
    (1 : ℤ) • h106 +
    (3 : ℤ) • h107 +
    (-3 : ℤ) • h108 +
    (-1 : ℤ) • h109 +
    (-2 : ℤ) • h110 +
    (-1 : ℤ) • h111 +
    (-2 : ℤ) • h112 +
    (1 : ℤ) • h113 +
    (1 : ℤ) • h114 +
    (-1 : ℤ) • h115 +
    (1 : ℤ) • h116 +
    (-1 : ℤ) • h117 +
    (1 : ℤ) • h118 +
    (4 : ℤ) • h119 +
    (-4 : ℤ) • h120 +
    (1 : ℤ) • h121 +
    (-2 : ℤ) • h122 +
    (2 : ℤ) • h123 +
    (-2 : ℤ) • h124 +
    (2 : ℤ) • h125 +
    (4 : ℤ) • h126 +
    (-4 : ℤ) • h127 +
    (2 : ℤ) • h128

end LinearIdentities

section ScalarExtensionIdentity

variable (p : LinearMap.BilinMap R M M)
variable (hc : ∀ x y, p x y = p y x)
variable (hj : ∀ x y, p (p x y) (p x x) = p x (p y (p x x)))
variable (d : Rˣ) (hd : (↑d : R) = 2)
variable (S : Type u) [CommRing S] [Algebra R S]
include hc hj hd

set_option maxHeartbeats 800000 in
/-- The pointwise linear Jordan identity extends to all scalar algebras when
two is invertible. The polarizations keep this valid in characteristic three. -/
theorem linearJordanIdentity_baseChange (x t : S ⊗[R] M) :
    let q := p.baseChange S
    q (q x t) (q x x) = q x (q t (q x x)) := by
  let q := p.baseChange S
  have hq (x y : S ⊗[R] M) : q x y = q y x := p.baseChange_isSymm hc x y
  let full (x y z t : S ⊗[R] M) :=
    associator q x t (q y z) + associator q y t (q z x) + associator q z t (q x y)
  let part (x y t : S ⊗[R] M) :=
    associator q y t (q x x) + (2 : S) • associator q x t (q x y)
  have hfull : ∀ x y z t, full x y z t = 0 := by
    intro x y z t
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
        induction z using TensorProduct.inductionOn with
        | tmul c z =>
          induction t using TensorProduct.inductionOn with
          | tmul r t =>
            simp only [full, associator, q, LinearMap.BilinMap.baseChange_tmul,
              mul_left_comm, mul_comm, ← tmul_sub, ← tmul_add]
            change _ ⊗ₜ[R] (associator p x t (p y z) + associator p y t (p z x) +
              associator p z t (p x y)) = _
            rw [jordanFull p hc hj x y z t d hd, tmul_zero]
          | add t t' h₁ h₂ =>
            dsimp only [full] at h₁ h₂ ⊢
            linear_combination (norm := expand_jordan hq) h₁ + h₂
        | add z z' h₁ h₂ =>
          dsimp only [full] at h₁ h₂ ⊢
          linear_combination (norm := expand_jordan hq) h₁ + h₂
      | add y y' h₁ h₂ =>
        dsimp only [full] at h₁ h₂ ⊢
        linear_combination (norm := expand_jordan hq) h₁ + h₂
    | add x x' h₁ h₂ =>
      dsimp only [full] at h₁ h₂ ⊢
      linear_combination (norm := expand_jordan hq) h₁ + h₂
  have hpart : ∀ x y t, part x y t = 0 := by
    intro x y t
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
        induction t using TensorProduct.inductionOn with
        | tmul r t =>
          simp only [part, associator, two_smul, q, LinearMap.BilinMap.baseChange_tmul,
            mul_left_comm, mul_comm, ← tmul_sub, ← tmul_add]
          have h := jordanPartial p hc hj x y t d hd
          rw [two_smul] at h
          change _ ⊗ₜ[R] (associator p y t (p x x) +
            (associator p x t (p x y) + associator p x t (p x y))) = _
          rw [h, tmul_zero]
        | add t t' h₁ h₂ =>
          dsimp only [part] at h₁ h₂ ⊢
          linear_combination (norm := expand_jordan hq) h₁ + h₂
      | add y y' h₁ h₂ =>
        dsimp only [part] at h₁ h₂ ⊢
        linear_combination (norm := expand_jordan hq) h₁ + h₂
    | add x x' h₁ h₂ =>
      have h := hfull x x' y t
      dsimp only [part, full] at h₁ h₂ h ⊢
      linear_combination (norm := expand_jordan hq) h₁ + h₂ + (2 : ℤ) • h
  change q (q x t) (q x x) = q x (q t (q x x))
  apply sub_eq_zero.mp
  change associator q x t (q x x) = 0
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction t using TensorProduct.inductionOn with
    | tmul r t =>
      simp only [associator, q, LinearMap.BilinMap.baseChange_tmul,
        mul_left_comm, mul_comm, hj x t, sub_self]
    | add t t' h₁ h₂ =>
      linear_combination (norm := expand_jordan hq) h₁ + h₂
  | add x x' h₁ h₂ =>
    have h₃ := hpart x x' t
    have h₄ := hpart x' x t
    dsimp only [part] at h₃ h₄
    linear_combination (norm := expand_jordan hq) h₁ + h₂ + h₃ + h₄

end ScalarExtensionIdentity

section QuadraticOfProduct

variable {A : Type*} [CommRing A] {P : Type*} [AddCommGroup P] [Module A P]
variable (p : LinearMap.BilinMap A P P)

private theorem operatorPolar_apply (x z y : P) :
    QuadraticMap.polar (operatorOfProduct p) x z y =
      (2 : A) • p x (p z y) + (2 : A) • p z (p x y) -
        p (p x z) y - p (p z x) y := by
  simp only [QuadraticMap.polar, LinearMap.sub_apply, operatorOfProduct_apply, two_smul,
    LinearMap.add_apply, map_add]
  abel

private def quadraticOfProduct : QuadraticMap A P (Module.End A P) :=
  QuadraticMap.ofPolar (operatorOfProduct p)
    (fun a x => by
      apply LinearMap.ext
      intro y
      simp only [operatorOfProduct_apply, LinearMap.smul_apply, map_smul,
        smul_smul, smul_sub, mul_assoc, mul_left_comm (2 : A)]
      rw [mul_comm (2 : A) a])
    (fun x z y => by
      apply LinearMap.ext
      intro t
      simp only [LinearMap.add_apply, operatorPolar_apply, map_add, smul_add]
      abel)
    (fun a x z => by
      apply LinearMap.ext
      intro t
      simp only [LinearMap.smul_apply, operatorPolar_apply,
        map_smul, smul_add, smul_sub, smul_smul, mul_comm (2 : A) a])

end QuadraticOfProduct

namespace LinearJordan

variable (L : LinearJordan R M)
variable (S : Type u) [CommRing S] [Algebra R S]

private theorem baseChange_bilin_natural (p : LinearMap.BilinMap R M M)
    {T : Type u} [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
    (x y : S ⊗[R] M) :
    let F := f.toLinearMap.rTensor M
    F (p.baseChange S x y) = p.baseChange T (F x) (F y) := by
  dsimp
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | tmul t b =>
      simp only [LinearMap.BilinMap.baseChange_tmul, LinearMap.rTensor_tmul,
        AlgHom.toLinearMap_apply, map_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [LinearMap.add_apply, map_add, hx, hy]

private theorem baseChange_unit_mul (x : S ⊗[R] M) :
    L.product.baseChange S (1 ⊗ₜ[R] L.unit) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul s x => simp [L.unit_mul]
  | add x y hx hy => simp [map_add, hx, hy]

private def operatorLaw : QuadraticOperatorLaw R M where
  op S := quadraticOfProduct (L.product.baseChange S)
  natural {S T} _ _ _ _ f x y := by
    change f.toLinearMap.rTensor M (operatorOfProduct (L.product.baseChange S) x y) =
      operatorOfProduct (L.product.baseChange T) (f.toLinearMap.rTensor M x)
        (f.toLinearMap.rTensor M y)
    simp only [operatorOfProduct_apply, two_smul, map_sub, map_add, baseChange_bilin_natural]

/-- The quadratic structure associated with a scalar-extended linear Jordan identity. -/
noncomputable def toQuadraticJordan (d : Rˣ) (hd : (↑d : R) = 2) : QuadraticJordan R M where
  toQuadraticOperatorLaw := L.operatorLaw
  unit := L.unit
  op_unit S _ _ := by
    apply LinearMap.ext
    intro y
    change operatorOfProduct (L.product.baseChange S) (1 ⊗ₜ[R] L.unit) y =
      (1 : Module.End S (S ⊗[R] M)) y
    simp only [operatorOfProduct_apply, L.baseChange_unit_mul, two_smul,
      add_sub_cancel_right, Module.End.one_apply]
  fundamental S _ _ x y := by
    apply LinearMap.ext
    intro z
    let dS := Units.map (algebraMap R S).toMonoidHom d
    have hdS : (↑dS : S) = 2 := by simp [dS, hd, map_ofNat]
    exact linear_fundamental (L.product.baseChange S)
      (L.product.baseChange_isSymm L.comm) (L.jordan S) dS hdS x y z
  commuting S _ _ x y z := by
    let dS := Units.map (algebraMap R S).toMonoidHom d
    have hdS : (↑dS : S) = 2 := by simp [dS, hd, map_ofNat]
    exact linear_commuting (L.product.baseChange S)
      (L.product.baseChange_isSymm L.comm) (L.jordan S) dS hdS x y z

theorem toQuadraticJordan_op (d : Rˣ) (hd : (↑d : R) = 2) (x : S ⊗[R] M) :
    (L.toQuadraticJordan d hd).op S x = operatorOfProduct (L.product.baseChange S) x := rfl

end LinearJordan

section Presentations

open Specs.LinearAlgebraicGroups.Albert (Presents)

private theorem quadraticJordan_ext {J K : QuadraticJordan R M}
    (hunit : J.unit = K.unit)
    (hop : ∀ (S : Type u) [CommRing S] [Algebra R S] (x : S ⊗[R] M), J.op S x = K.op S x) :
    J = K := by
  cases J with
  | mk JL uj huj hfj hcj =>
    cases K with
    | mk KL uk huk hfk hck =>
      rw [Specs.LinearAlgebraicGroups.Albert.QuadraticJordan.mk.injEq]
      refine ⟨?_, hunit⟩
      cases JL
      cases KL
      rw [Specs.LinearAlgebraicGroups.Albert.QuadraticOperatorLaw.mk.injEq]
      funext S _ _
      exact QuadraticMap.ext fun x => hop S x

private theorem linearJordan_ext {J K : LinearJordan R M}
    (hunit : J.unit = K.unit) (hprod : J.product = K.product) : J = K := by
  cases J
  cases K
  rw [Specs.LinearAlgebraicGroups.Albert.LinearJordan.mk.injEq]
  exact ⟨hunit, hprod⟩

private theorem operatorPolar_unit {A : Type*} [CommRing A] {P : Type*}
    [AddCommGroup P] [Module A P] (p : LinearMap.BilinMap A P P) (e : P)
    (hc : ∀ x y, p x y = p y x) (he : ∀ x, p e x = x) (x y : P) :
    QuadraticMap.polar (operatorOfProduct p) x y e = (2 : A) • p x y := by
  have hr (x : P) : p x e = x := (hc x e).trans (he x)
  simp only [operatorPolar_apply, hr, hc y x, two_smul]
  abel

private theorem product_eq_of_presents (d : Rˣ) (hd : (↑d : R) = 2)
    (L : LinearJordan R M) (J : QuadraticJordan R M) (h : Presents L J) :
    J.groundProduct d = L.product := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply (TensorProduct.lid R M).symm.injective
  rw [QuadraticJordan.groundProduct_at J d, QuadraticJordan.linearProduct_apply J R d, h.1]
  let p := L.product.baseChange R
  let e : R ⊗[R] M := 1 ⊗ₜ[R] L.unit
  have hop : (fun a => J.op R a) = operatorOfProduct p := funext fun a => h.2 R a
  change algebraMap R R (↑d⁻¹ : R) •
    QuadraticMap.polar (fun a => J.op R a) (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) e =
      (TensorProduct.lid R M).symm (L.product x y)
  rw [hop, operatorPolar_unit p e (L.product.baseChange_isSymm L.comm)
      (LinearJordan.baseChange_unit_mul L R), smul_smul, QuadraticJordan.half_mul_two R d hd, one_smul]
  simp [p, lid_symm_apply]

/-- With two invertible, each presentation has a unique matching structure of
the other kind on the same module. -/
theorem presentation_equivalence :
    Specs.LinearAlgebraicGroups.Albert.Types.PresentationEquivalenceType.{u, v} := by
  intro R _ M _ _ d hd
  constructor
  · intro J
    refine ⟨QuadraticJordan.toLinearJordan J d hd, ⟨rfl, ?_⟩, ?_⟩
    · intro S _ _ x
      change J.op S x = operatorOfProduct ((J.groundProduct d).baseChange S) x
      rw [QuadraticJordan.groundProduct_baseChange J S d, QuadraticJordan.op_eq_operatorOfProduct J S d hd]
    · intro L h
      exact linearJordan_ext h.1.symm (product_eq_of_presents d hd L J h).symm
  · intro L
    refine ⟨LinearJordan.toQuadraticJordan L d hd, ⟨rfl, fun S _ _ x => LinearJordan.toQuadraticJordan_op L S d hd x⟩, ?_⟩
    intro J h
    apply quadraticJordan_ext h.1
    intro S _ _ x
    rw [LinearJordan.toQuadraticJordan_op L S d hd, h.2 S x]

end Presentations

namespace QuadraticJordan

open Specs.LinearAlgebraicGroups.Albert (towerAlgebra iteratedTensorEquiv)

theorem baseChange_op (J : QuadraticJordan R M)
    (S : Type u) [CommRing S] [Algebra R S] (T : Type u) [CommRing T] [Algebra S T]
    (x y : T ⊗[S] (S ⊗[R] M)) :
    letI := towerAlgebra R S T
    let e := iteratedTensorEquiv (R := R) (S := S) (M := M) T
    e ((J.baseChange S).op T x y) = J.op T (e x) (e y) := by
  let e := iteratedTensorEquiv (R := R) (S := S) (M := M) T
  exact e.apply_symm_apply _

end QuadraticJordan

abbrev associativeJordan (R : Type u) [CommRing R]
    (C : Type w) [Ring C] [Algebra R C] :=
  Specs.LinearAlgebraicGroups.Albert.associativeJordan R C

theorem associative_formula (R : Type u) [CommRing R] (C : Type w) [Ring C] [Algebra R C]
    (S : Type u) [CommRing S] [Algebra R S] (x y z : S ⊗[R] C) :
    let J := associativeJordan R C
    J.op S x y = x * y * x ∧ J.toQuadraticOperatorLaw.triple S x y z = x * y * z + z * y * x := by
  constructor
  · rfl
  · change (x + z) * y * (x + z) - x * y * x - z * y * z = _
    simp only [add_mul, mul_add]
    abel

theorem characteristic_two_example : Specs.LinearAlgebraicGroups.Albert.Types.CharacteristicTwoType := by
  let F := ZMod 2
  let e : F ⊗[F] F := 1 ⊗ₜ[F] 1
  have h := associative_formula F F F e e e
  change _ ∧ _ ∧ e ≠ 0
  change (associativeJordan F F).toQuadraticOperatorLaw.triple F e e e = 0 ∧
    (associativeJordan F F).op F e e = e ∧ e ≠ 0
  have he : e = 1 := rfl
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  refine ⟨?_, ?_, ?_⟩
  · rw [h.2, he, one_mul, one_mul, ← two_smul F, htwo, zero_smul]
  · rw [h.1, he, one_mul, one_mul]
  · intro hz
    have hzero := congrArg (TensorProduct.lid F F) hz
    simp [e] at hzero

end LinearAlgebraicGroups.Albert
