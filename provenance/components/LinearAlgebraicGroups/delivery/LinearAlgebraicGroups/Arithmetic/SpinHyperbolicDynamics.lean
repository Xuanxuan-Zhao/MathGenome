import Specs.LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics
import LinearAlgebraicGroups.Albert.SpinFunctor
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.Tactic.NoncommRing
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics

open AlgebraicGeometry CategoryTheory CliffordAlgebra Module
open LinearAlgebraicGroups.Albert
open SpinSpecification
open Specs.Arithmetic.SpinHyperbolicDynamics
open CocharacterDynamics
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open scoped TensorProduct CategoryTheory.MonObj LaurentPolynomial

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

open private cliffordEquiv cliffordEquiv_vector cliffordEquiv_even reversion_mul
  even_one conjugationLinear changeModule changeModule_smul changeModule_coord changeCoefficients_vector
  changeCoefficients_apply vectors_injective scalar_tensor_injective orderedBasis
  from LinearAlgebraicGroups.Albert.SpinFunctor

open private unitEquiv unitEquiv_unitPoint unitPointHom unitPointHom_apply opposite_point
  centralizes_onAlgebras polynomialConstants polynomialConstants_laurent polynomialConstants_zero
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

open private baseChangeEquiv_reverse from LinearAlgebraicGroups.Albert.CliffordModel

section Ring

variable {S A : Type u} [CommRing S] [Ring A] [Algebra S A]

private structure PlaneRelations (E L : A) : Prop where
  ee : E * E = 0
  ll : L * L = 0
  sum : E * L + L * E = 1

private theorem PlaneRelations.swap {E L : A} (r : PlaneRelations E L) :
    PlaneRelations L E :=
  ⟨r.ll, r.ee, (add_comm _ _).trans r.sum⟩

private theorem PlaneRelations.ele {E L : A} (r : PlaneRelations E L) :
    E * L * E = E := by
  calc
    _ = E * (E * L + L * E) - (E * E) * L := by noncomm_ring
    _ = E := by rw [r.sum, r.ee, mul_one, zero_mul, sub_zero]

private theorem PlaneRelations.cross {E L : A} (r : PlaneRelations E L) :
    (E * L) * (L * E) = 0 := by
  rw [← mul_assoc, mul_assoc E L L, r.ll, mul_zero, zero_mul]

private def plane (E L : A) (a b : S) : A := a • (E * L) + b • (L * E)

private theorem PlaneRelations.plane_mul {E L : A} (r : PlaneRelations E L)
    (a b c d : S) :
    plane E L a b * plane E L c d = plane E L (a * c) (b * d) := by
  have h₁ : (E * L) * (E * L) = E * L := by rw [← mul_assoc, r.ele]
  have h₂ : (L * E) * (L * E) = L * E := by rw [← mul_assoc, r.swap.ele]
  simp only [plane, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
    h₁, h₂, r.cross, r.swap.cross, smul_zero, add_zero, zero_add, mul_comm c a, mul_comm d b]

private theorem PlaneRelations.plane_mul_left {E L : A} (r : PlaneRelations E L)
    (a b : S) : plane E L a b * E = a • E := by
  have h : (L * E) * E = 0 := by rw [mul_assoc, r.ee, mul_zero]
  simp [plane, add_mul, r.ele, h]

private theorem PlaneRelations.plane_mul_right {E L : A} (r : PlaneRelations E L)
    (a b : S) : E * plane E L a b = b • E := by
  have h : E * (E * L) = 0 := by rw [← mul_assoc, r.ee, zero_mul]
  simp [plane, mul_add, ← mul_assoc E L E, r.ele, h]

private theorem plane_swap (E L : A) (a b : S) :
    plane L E a b = plane E L b a := add_comm _ _

private theorem PlaneRelations.plane_one {E L : A} (r : PlaneRelations E L) :
    plane E L (1 : S) 1 = 1 := by simpa [plane] using r.sum

private theorem commute_product_of_anticommute {E L X : A}
    (he : X * E = -(E * X)) (hf : X * L = -(L * X)) :
    Commute (E * L) X := by
  change (E * L) * X = X * (E * L)
  rw [mul_assoc, ← mul_assoc X, he, neg_mul, mul_assoc E, hf, mul_neg, neg_neg]

end Ring

section IntrinsicShear

variable {R : Type u} [CommRing R] {V : Type u} [AddCommGroup V] [Module R V]
variable (q : QuadraticForm R V) (e w : V)

private def intrinsicShearAction (x : V) : V :=
  x + q.polarBilin w x • e - q.polarBilin e x • w -
    (q.polarBilin e x * q w) • e

private theorem swap (x y : V) :
    CliffordAlgebra.ι q x * CliffordAlgebra.ι q y + CliffordAlgebra.ι q y * CliffordAlgebra.ι q x = algebraMap R _ (q.polarBilin x y) := by
  exact ι_mul_ι_add_swap x y

private theorem orthogonal_swap (h : q.polarBilin e w = 0) :
    CliffordAlgebra.ι q w * CliffordAlgebra.ι q e = -(CliffordAlgebra.ι q e * CliffordAlgebra.ι q w) := by
  have hv := swap q w e
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
    ← QuadraticMap.polarBilin_apply_apply, h, map_zero] at hv
  exact eq_neg_of_add_eq_zero_left hv

private theorem shear_nilpotent (he : q e = 0) (hew : q.polarBilin e w = 0) :
    (CliffordAlgebra.ι q e * CliffordAlgebra.ι q w) * (CliffordAlgebra.ι q e * CliffordAlgebra.ι q w) = 0 := by
  have hee : CliffordAlgebra.ι q e * CliffordAlgebra.ι q e = 0 := by rw [ι_sq_scalar, he, map_zero]
  calc
    _ = CliffordAlgebra.ι q e * (CliffordAlgebra.ι q w * CliffordAlgebra.ι q e) * CliffordAlgebra.ι q w := by noncomm_ring
    _ = -(CliffordAlgebra.ι q e * CliffordAlgebra.ι q e) * (CliffordAlgebra.ι q w * CliffordAlgebra.ι q w) := by rw [orthogonal_swap q e w hew]; noncomm_ring
    _ = _ := by rw [hee, neg_zero, zero_mul]

private def shear (he : q e = 0) (hew : q.polarBilin e w = 0) :
    (CliffordAlgebra q)ˣ where
  val := 1 + CliffordAlgebra.ι q e * CliffordAlgebra.ι q w
  inv := 1 - CliffordAlgebra.ι q e * CliffordAlgebra.ι q w
  val_inv := by
    calc
      _ = 1 - (CliffordAlgebra.ι q e * CliffordAlgebra.ι q w) * (CliffordAlgebra.ι q e * CliffordAlgebra.ι q w) := by noncomm_ring
      _ = 1 := by rw [shear_nilpotent q e w he hew, sub_zero]
  inv_val := by
    calc
      _ = 1 - (CliffordAlgebra.ι q e * CliffordAlgebra.ι q w) * (CliffordAlgebra.ι q e * CliffordAlgebra.ι q w) := by noncomm_ring
      _ = 1 := by rw [shear_nilpotent q e w he hew, sub_zero]

private theorem vector_even_product (x y : V) :
    CliffordAlgebra.ι q x * CliffordAlgebra.ι q y ∈ evenOdd q 0 := by
  have h := SetLike.mul_mem_graded (ι_mem_evenOdd_one q x) (ι_mem_evenOdd_one q y)
  simpa only [show (1 + 1 : ZMod 2) = 0 by decide] using h

private theorem shear_conjugation (he : q e = 0) (hew : q.polarBilin e w = 0) (x : V) :
    (1 + CliffordAlgebra.ι q e * CliffordAlgebra.ι q w) * CliffordAlgebra.ι q x * (1 - CliffordAlgebra.ι q e * CliffordAlgebra.ι q w) =
      CliffordAlgebra.ι q (intrinsicShearAction q e w x) := by
  let E := CliffordAlgebra.ι q e
  let Z := CliffordAlgebra.ι q w
  let X := CliffordAlgebra.ι q x
  let P := algebraMap R (CliffordAlgebra q) (q.polarBilin w x)
  let Q := algebraMap R (CliffordAlgebra q) (q.polarBilin e x)
  let C := algebraMap R (CliffordAlgebra q) (q w)
  have e2 : E * E = 0 := by dsimp [E]; rw [ι_sq_scalar, he, map_zero]
  have z2 : Z * Z = C := ι_sq_scalar q w
  have zx : Z * X = P - X * Z := eq_sub_of_add_eq (swap q w x)
  have xe : X * E = Q - E * X := eq_sub_of_add_eq (by rw [add_comm]; exact swap q e x)
  have ze : Z * E = -(E * Z) := orthogonal_swap q e w hew
  have ep : E * P = P * E := (Algebra.commutes _ E).symm
  have n2 : (E * Z) * (E * Z) = 0 := shear_nilpotent q e w he hew
  have ene : E * (E * Z) = 0 := by rw [← mul_assoc, e2, zero_mul]
  have zne : Z * (E * Z) = -(E * C) := by rw [← mul_assoc, ze, neg_mul, mul_assoc, z2]
  have comm : E * Z * X - X * (E * Z) = P * E - Q * Z := by
    rw [mul_assoc E, zx, ← mul_assoc X, xe, mul_sub, sub_mul, ep]
    noncomm_ring
  have quad : E * Z * X * (E * Z) = Q * C * E := by
    calc
      _ = (X * (E * Z) + (P * E - Q * Z)) * (E * Z) := by
        congr 1
        exact eq_add_of_sub_eq' comm
      _ = X * ((E * Z) * (E * Z)) + P * (E * (E * Z)) - Q * (Z * (E * Z)) := by noncomm_ring
      _ = Q * (E * C) := by rw [n2, ene, zne, mul_zero, mul_zero, add_zero, zero_sub, mul_neg, neg_neg]
      _ = _ := by rw [← Algebra.commutes (q w) E, ← mul_assoc]
  calc
    _ = X + (E * Z * X - X * (E * Z)) - E * Z * X * (E * Z) := by
      change (1 + E * Z) * X * (1 - E * Z) = _
      noncomm_ring
    _ = X + P * E - Q * Z - Q * C * E := by rw [comm, quad]; noncomm_ring
    _ = _ := by
      simp only [intrinsicShearAction, map_add, map_sub, map_smul, Algebra.smul_def, map_mul,
        E, Z, X, P, Q, C]

end IntrinsicShear

section Field

variable {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
variable (q : QuadraticForm F V) (h : HyperbolicPair q)
  {I : Type u} [LinearOrder I] (b : Basis I F V)

private theorem polar_self_zero {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
    (Q : QuadraticForm S M) {x : M} (hx : Q x = 0) : Q.polarBilin x x = 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hx, smul_zero]

private theorem decompose {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
    (Q : QuadraticForm S M) {e f : M} (he : Q e = 0) (hf : Q f = 0)
    (hef : Q.polarBilin e f = 1) (x : M) :
    ∃ w, Q.polarBilin e w = 0 ∧ Q.polarBilin f w = 0 ∧
      x = Q.polarBilin f x • e + Q.polarBilin e x • f + w := by
  let a := Q.polarBilin f x
  let c := Q.polarBilin e x
  have hfe : Q.polarBilin f e = 1 := (QuadraticMap.polar_comm Q _ _).trans hef
  refine ⟨x - a • e - c • f, ?_, ?_, by abel⟩
  · rw [map_sub, map_sub, map_smul, map_smul, polar_self_zero Q he, hef,
      smul_zero, sub_zero, smul_eq_mul, mul_one, sub_self]
  · rw [map_sub, map_sub, map_smul, map_smul, polar_self_zero Q hf, hfe,
      smul_zero, sub_zero, smul_eq_mul, mul_one, sub_self]

private theorem form_over (R : TestAlgebra F) (v : V) :
    ExtendedForm q R b (vectorOver R v) = algebraMap F R (q v) := by
  simpa using CliffordModel.coefficientForm_tmul R q b (1 : R) v

private theorem polar_over (R : TestAlgebra F) (x y : V) :
    (ExtendedForm q R b).polarBilin (vectorOver R x) (vectorOver R y) =
      algebraMap F R (q.polarBilin x y) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [← TensorProduct.tmul_add, form_over, form_over, form_over, map_sub, map_sub]

private abbrev E (R : TestAlgebra F) := vectors q R (vectorOver R h.e)
private abbrev L (R : TestAlgebra F) := vectors q R (vectorOver R h.f)

private theorem vector_square (R : TestAlgebra F) (x : R ⊗[F] V) :
    vectors q R x * vectors q R x = algebraMap R _ (ExtendedForm q R b x) := by
  apply (cliffordEquiv q R b).injective
  rw [map_mul, cliffordEquiv_vector, (cliffordEquiv q R b).commutes, ι_sq_scalar]

private theorem vector_swap (R : TestAlgebra F) (x y : R ⊗[F] V) :
    vectors q R x * vectors q R y + vectors q R y * vectors q R x =
      algebraMap R _ ((ExtendedForm q R b).polarBilin x y) := by
  apply (cliffordEquiv q R b).injective
  rw [map_add, map_mul, map_mul, cliffordEquiv_vector, cliffordEquiv_vector,
    (cliffordEquiv q R b).commutes]
  exact ι_mul_ι_add_swap _ _

private theorem orthogonal_vector_swap (R : TestAlgebra F) (x y : R ⊗[F] V)
    (hy : (ExtendedForm q R b).polarBilin x y = 0) :
    vectors q R y * vectors q R x = -(vectors q R x * vectors q R y) := by
  have hz := vector_swap q b R x y
  rw [hy, map_zero] at hz
  exact eq_neg_of_add_eq_zero_right hz

include b in
private theorem plane_relations (R : TestAlgebra F) :
    PlaneRelations (E q h R) (L q h R) := by
  constructor
  · rw [E, vector_square q b, form_over, h.q_e, map_zero, map_zero]
  · rw [L, vector_square q b, form_over, h.q_f, map_zero, map_zero]
  · rw [E, L, vector_swap q b, polar_over, h.polar_ef, map_one, map_one]

private theorem over_decompose (R : TestAlgebra F) (x : R ⊗[F] V) :
    ∃ w : perpendicularOver q h b R,
      x = (ExtendedForm q R b).polarBilin (vectorOver R h.f) x • vectorOver R h.e +
        (ExtendedForm q R b).polarBilin (vectorOver R h.e) x • vectorOver R h.f + w.val := by
  obtain ⟨w, he, hf, hx⟩ := decompose (ExtendedForm q R b)
    (by rw [form_over, h.q_e, map_zero]) (by rw [form_over, h.q_f, map_zero])
    (by rw [polar_over, h.polar_ef, map_one]) x
  exact ⟨⟨w, he, hf⟩, hx⟩

private theorem diagonal_formula (R : TestAlgebra F) (s : Rˣ) :
    diagonal q h R s = plane (E q h R) (L q h R) (s : R) (↑s⁻¹ : R) := rfl

include b in
private theorem diagonal_product (R : TestAlgebra F) (s t : Rˣ) :
    diagonal q h R s * diagonal q h R t = diagonal q h R (s * t) := by
  rw [diagonal_formula, diagonal_formula, (plane_relations q h b R).plane_mul, diagonal_formula]
  congr 1
  change (↑s⁻¹ : R) * ↑t⁻¹ = ↑(t⁻¹ * s⁻¹)
  rw [Units.val_mul, mul_comm]

include b in
private theorem diagonal_one (R : TestAlgebra F) : diagonal q h R 1 = 1 :=
  (plane_relations q h b R).plane_one

include b in
private def diagonalUnit (R : TestAlgebra F) (s : Rˣ) : (ScalarClifford q R)ˣ where
  val := diagonal q h R s
  inv := diagonal q h R s⁻¹
  val_inv := by rw [diagonal_product q h b, mul_inv_cancel, diagonal_one q h b]
  inv_val := by rw [diagonal_product q h b, inv_mul_cancel, diagonal_one q h b]

private theorem diagonal_commutes_perpendicular (R : TestAlgebra F) (s : Rˣ)
    (w : perpendicularOver q h b R) : Commute (diagonal q h R s) (vectors q R w.val) := by
  have he := orthogonal_vector_swap q b R (vectorOver R h.e) w.val w.property.1
  have hf := orthogonal_vector_swap q b R (vectorOver R h.f) w.val w.property.2
  exact ((commute_product_of_anticommute he hf).smul_left (s : R)).add_left
    ((commute_product_of_anticommute hf he).smul_left (↑s⁻¹ : R))

private theorem diagonal_conjugates_e (R : TestAlgebra F) (s : Rˣ) :
    conjugate q R (diagonalUnit q h b R s) (E q h R) = (s : R) ^ 2 • E q h R := by
  change diagonal q h R s * E q h R * diagonal q h R s⁻¹ = _
  have r := plane_relations q h b R
  rw [diagonal_formula, diagonal_formula, r.plane_mul_left, smul_mul_assoc,
    r.plane_mul_right, inv_inv, smul_smul, pow_two]

private theorem diagonal_swap (R : TestAlgebra F) (s : Rˣ) :
    diagonal q h.swap R s = diagonal q h R s⁻¹ := by
  simp only [diagonal_formula, inv_inv]
  exact plane_swap _ _ _ _

private theorem diagonalUnit_swap (R : TestAlgebra F) (s : Rˣ) :
    diagonalUnit q h.swap b R s = diagonalUnit q h b R s⁻¹ :=
  Units.ext (diagonal_swap q h R s)

private theorem diagonal_conjugates_f (R : TestAlgebra F) (s : Rˣ) :
    conjugate q R (diagonalUnit q h b R s) (L q h R) = (↑s⁻¹ : R) ^ 2 • L q h R := by
  have H := diagonal_conjugates_e q h.swap b R s⁻¹
  rw [diagonalUnit_swap, inv_inv] at H
  exact H

private theorem diagonal_conjugates_w (R : TestAlgebra F) (s : Rˣ)
    (w : perpendicularOver q h b R) :
    conjugate q R (diagonalUnit q h b R s) (vectors q R w.val) = vectors q R w.val := by
  change diagonal q h R s * vectors q R w.val * diagonal q h R s⁻¹ = _
  rw [(diagonal_commutes_perpendicular q h b R s w).eq, mul_assoc,
    diagonal_product q h b, mul_inv_cancel, diagonal_one q h b, mul_one]

private theorem diagonal_spin (R : TestAlgebra F) (s : Rˣ) :
    diagonalUnit q h b R s ∈ spinUnits q R := by
  have normalizes (t : Rˣ) :
      Set.MapsTo (conjugate q R (diagonalUnit q h b R t))
        (LinearMap.range (vectors q R)) (LinearMap.range (vectors q R)) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨w, hx⟩ := over_decompose q h b R x
    let a := (ExtendedForm q R b).polarBilin (vectorOver R h.f) x
    let c := (ExtendedForm q R b).polarBilin (vectorOver R h.e) x
    refine ⟨(a * (t : R) ^ 2) • vectorOver R h.e +
      (c * (↑t⁻¹ : R) ^ 2) • vectorOver R h.f + w.val, ?_⟩
    conv_rhs => rw [hx]
    change _ = conjugationLinear q R (diagonalUnit q h b R t) (vectors q R (_ + _ + _))
    simp only [map_add, map_smul]
    change _ = a • conjugate q R (diagonalUnit q h b R t) (E q h R) +
      c • conjugate q R (diagonalUnit q h b R t) (L q h R) +
        conjugate q R (diagonalUnit q h b R t) (vectors q R w.val)
    rw [diagonal_conjugates_e, diagonal_conjugates_f, diagonal_conjugates_w, smul_smul, smul_smul]
  refine ⟨?_, ?_, normalizes s, ?_⟩
  · change diagonal q h R s ∈ evenPart q R
    rw [← cliffordEquiv_even q R b]
    unfold diagonal
    simp only [map_add, map_smul, map_mul, cliffordEquiv_vector]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (vector_even_product _ _ _))
      (Submodule.smul_mem _ _ (vector_even_product _ _ _))
  · change reversion q R (diagonal q h R s) * diagonal q h R s = 1
    have hv (x : V) : reversion q R (vectors q R (vectorOver R x)) =
        vectors q R (vectorOver R x) := by
      simp [vectorOver]
    have hr : reversion q R (diagonal q h R s) = diagonal q h R s⁻¹ := by
      simp only [diagonal, map_add, map_smul, reversion_mul q R b, hv, inv_inv, add_comm]
    rw [hr, diagonal_product q h b, inv_mul_cancel, diagonal_one q h b]
  · exact normalizes s⁻¹

private theorem change_vectorOver {R S : TestAlgebra F} (a : R ⟶ S) (v : V) :
    changeModule a.hom (vectorOver R v) = vectorOver S v := by
  simp [changeModule, vectorOver]

private theorem change_vector {R S : TestAlgebra F} (a : R ⟶ S) (x : R ⊗[F] V) :
    coefficientMap q R a.hom (vectors q R x) =
      vectors q S (changeModule a.hom x) :=
  changeCoefficients_vector q a.hom x

private theorem change_diagonal {R S : TestAlgebra F} (a : R ⟶ S) (s : Rˣ) :
    coefficientMap q R a.hom (diagonal q h R s) =
      diagonal q h S (Units.map a.hom.toMonoidHom s) := by
  have hs (t : R) (x : ScalarClifford q R) :
      coefficientMap q R a.hom (t • x) =
        a.hom t • coefficientMap q R a.hom x :=
    changeModule_smul a.hom t x
  simp only [diagonal, map_add, hs, map_mul, change_vector, change_vectorOver,
    ← map_inv (Units.map a.hom.toMonoidHom)]
  rfl

private theorem change_shear {R S : TestAlgebra F} (a : R ⟶ S) (w : R ⊗[F] V) :
    coefficientMap q R a.hom (shearValue q h R w) =
      shearValue q h S (changeModule a.hom w) := by
  simp only [shearValue, map_add, map_one, map_mul, change_vector, change_vectorOver]

variable {G : LinearAlgebraicGroups.Specs.GroupScheme F}
  (rep : ∀ R : TestAlgebra F, GroupPoints G R →* (ScalarClifford q R)ˣ)

private theorem rep_value_natural (hr : IsSpinPointRepresentation q G rep)
    {R S : TestAlgebra F} (a : R ⟶ S) (g : GroupPoints G R) :
    (rep S (mapPoints a g)).val = coefficientMap q R a.hom (rep R g).val :=
  congrArg Units.val (hr.2 a g)

private theorem rep_val_injective (hr : IsSpinPointRepresentation q G rep) (R : TestAlgebra F) :
    Function.Injective (fun g : GroupPoints G R => (rep R g).val) :=
  Units.val_injective.comp (hr.1 R).1

private theorem point_from_unit (hr : IsSpinPointRepresentation q G rep)
    {R : TestAlgebra F} {a : (ScalarClifford q R)ˣ} (ha : a ∈ spinUnits q R) :
    ∃ g : GroupPoints G R, (rep R g).val = a.val := by
  obtain ⟨g, hg⟩ := (hr.1 R).2.symm ▸ ha
  exact ⟨g, congrArg Units.val hg⟩

theorem cocharacterExists : CocharacterExists.{u} := by
  intro F _ V _ _ I _ q b h G rep hr
  classical
  have existsPoint (R : TestAlgebra F) (s : Rˣ) :
      ∃ g : GroupPoints G R, (rep R g).val = diagonal q h R s :=
    point_from_unit q rep hr (diagonal_spin q h b R s)
  let point (R : TestAlgebra F) (s : Rˣ) := (existsPoint R s).choose
  have point_formula (R : TestAlgebra F) (s : Rˣ) :
      (rep R (point R s)).val = diagonal q h R s := (existsPoint R s).choose_spec
  let gm := specGroup (groupAlgebra F IntegerCharacters)
  let α : (groupPointsFunctor F).obj gm ⟶ (groupPointsFunctor F).obj G :=
    { app := fun R => GrpCat.ofHom
        ({ toFun := fun p => point R (unitEquiv R p)
           map_one' := by
             apply rep_val_injective q rep hr R
             dsimp only
             rw [map_one, point_formula, diagonal_one q h b, map_one]
             rfl
           map_mul' := by
             intro x y
             apply rep_val_injective q rep hr R
             dsimp only
             rw [map_mul (unitEquiv R), point_formula, map_mul, Units.val_mul,
               point_formula, point_formula, diagonal_product q h b] } :
           GroupPoints gm R →* GroupPoints G R)
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro p
        have hp : unitPoint R (unitEquiv R p) = p := by
          apply (unitEquiv R).injective
          exact unitEquiv_unitPoint R _
        obtain ⟨s, rfl⟩ : ∃ s, unitPoint R s = p := ⟨_, hp⟩
        apply rep_val_injective q rep hr S
        change (rep S (point S (unitEquiv S (mapPoints a (unitPoint R s))))).val =
          (rep S (mapPoints a (point R (unitEquiv R (unitPoint R s))))).val
        rw [mapPoints_unitPoint, unitEquiv_unitPoint, unitEquiv_unitPoint,
          point_formula, rep_value_natural q rep hr, point_formula, change_diagonal q h] }
  have hgm : IsAffine gm.X.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra F IntegerCharacters))))
  obtain ⟨cochar, hc⟩ := (groupHomComparison F gm G hgm).surjective α
  refine ⟨cochar, ?_⟩
  intro R s
  change (rep R (((groupPointsFunctor F).map cochar).app R (unitPoint R s))).val = _
  change (groupPointsFunctor F).map cochar = α at hc
  rw [hc]
  change (rep R (point R (unitEquiv R (unitPoint R s)))).val = _
  rw [unitEquiv_unitPoint, point_formula]

theorem cocharacterWeights : CocharacterWeights.{u} := by
  intro F _ V _ _ I _ q b h G rep cochar _ hd R s
  let d : SpinFunctor.Spin q R b := ⟨diagonalUnit q h b R s, diagonal_spin q h b R s⟩
  let A := SpinFunctor.vectorAction q R b d
  have hval : rep R (cocharacterPoint cochar R s) = d.val := Units.ext (hd R s)
  have hact := SpinFunctor.vectorAction_characterization q R b d
  refine ⟨A, hval.symm ▸ hact, ?_, ?_, ?_⟩
  · apply vectors_injective q R b
    rw [hact, map_smul]
    exact diagonal_conjugates_e q h b R s
  · apply vectors_injective q R b
    rw [hact, map_smul]
    exact diagonal_conjugates_f q h b R s
  · intro w
    apply vectors_injective q R b
    rw [hact]
    exact diagonal_conjugates_w q h b R s w

private theorem opposite_diagonal {cochar : Cocharacter G} (hd : IsDiagonal q h rep cochar) :
    IsDiagonal q h.swap rep (oppositeCocharacter cochar) := by
  intro R s
  rw [opposite_point, hd, diagonal_swap]

private theorem shear_spin (R : TestAlgebra F) (w : perpendicularOver q h b R) :
    ∃ a ∈ spinUnits q R,
      a.val = shearValue q h R w ∧
      ∀ x, conjugate q R a (vectors q R x) = vectors q R (shearAction q h b w x) := by
  let Q := ExtendedForm q R b
  let e := vectorOver R h.e
  have he : Q e = 0 := by
    change ExtendedForm q R b (vectorOver R h.e) = _
    rw [form_over, h.q_e, map_zero]
  have hw : Q.polarBilin e w.val = 0 := w.property.1
  let φ := cliffordEquiv q R b
  let c := shear Q e w.val he hw
  let a := Units.map φ.symm.toMonoidHom c
  have ha : φ a.val = c.val := φ.apply_symm_apply _
  have hi : φ a⁻¹.val = c⁻¹.val := by
    change φ ((Units.map φ.symm.toMonoidHom c)⁻¹.val) = _
    rw [← map_inv]
    exact φ.apply_symm_apply _
  have hval : a.val = shearValue q h R w := by
    apply φ.injective
    rw [ha, shearValue, map_add, map_one, map_mul, cliffordEquiv_vector, cliffordEquiv_vector]
    rfl
  have hconj (x : R ⊗[F] V) :
      conjugate q R a (vectors q R x) = vectors q R (shearAction q h b w x) := by
    apply φ.injective
    rw [conjugate, map_mul, map_mul, ha, hi, cliffordEquiv_vector, cliffordEquiv_vector]
    exact shear_conjugation Q e w.val he hw x
  refine ⟨a, ⟨?_, ?_, ?_, ?_⟩, hval, hconj⟩
  · rw [← cliffordEquiv_even q R b, ha]
    exact Submodule.add_mem _ (SetLike.one_mem_graded (evenOdd Q)) (vector_even_product Q e w)
  · apply φ.injective
    rw [map_mul, show φ (reversion q R a.val) = reverse (φ a.val) from
      baseChangeEquiv_reverse R q b _, ha, map_one]
    change reverse (1 + CliffordAlgebra.ι Q e * CliffordAlgebra.ι Q w.val) * (1 + CliffordAlgebra.ι Q e * CliffordAlgebra.ι Q w.val) = 1
    rw [map_add, reverse.map_one, reverse.map_mul, reverse_ι, reverse_ι,
      orthogonal_swap Q e w.val hw, ← sub_eq_add_neg]
    exact c.inv_val
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, (hconj x).symm⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨intrinsicShearAction Q e (-w.val) x, φ.injective ?_⟩
    rw [conjugate, inv_inv, map_mul, map_mul, hi, ha, cliffordEquiv_vector, cliffordEquiv_vector]
    have neg_mem : Q.polarBilin e (-w.val) = 0 := by rw [map_neg, hw, neg_zero]
    change CliffordAlgebra.ι Q _ =
      (1 - CliffordAlgebra.ι Q e * CliffordAlgebra.ι Q w.val) * CliffordAlgebra.ι Q x *
        (1 + CliffordAlgebra.ι Q e * CliffordAlgebra.ι Q w.val)
    simpa only [map_neg, mul_neg, ← sub_eq_add_neg, sub_neg_eq_add] using
      (shear_conjugation Q e (-w.val) he neg_mem x).symm

private theorem exists_shear_point (hr : IsSpinPointRepresentation q G rep)
    (R : TestAlgebra F) (w : perpendicularOver q h b R) :
    ∃ g : GroupPoints G R, (rep R g).val = shearValue q h R w ∧
      ∀ x, conjugate q R (rep R g) (vectors q R x) = vectors q R (shearAction q h b w x) := by
  obtain ⟨a, ha, hv, hc⟩ := shear_spin q h b R w
  obtain ⟨g, hg⟩ := point_from_unit q rep hr ha
  refine ⟨g, hg.trans hv, ?_⟩
  rw [Units.ext hg]
  exact hc

private theorem change_polarOver {R S : TestAlgebra F} (a : R ⟶ S) (v : V)
    (w : R ⊗[F] V) :
    (ExtendedForm q S b).polarBilin (vectorOver S v) (changeModule a.hom w) =
      a.hom ((ExtendedForm q R b).polarBilin (vectorOver R v) w) := by
  induction w with
  | tmul c x =>
    rw [show c ⊗ₜ[F] x = c • vectorOver R x by rw [vectorOver, TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      changeModule_smul, change_vectorOver, map_smul, map_smul, smul_eq_mul,
      smul_eq_mul, map_mul, polar_over, polar_over, a.hom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem change_perpendicular {R S : TestAlgebra F} (a : R ⟶ S)
    (w : perpendicularOver q h b R) : changeModule a.hom w.val ∈ perpendicularOver q h b S := by
  have he := w.property.1
  have hf := w.property.2
  constructor <;> change (ExtendedForm q S b).polarBilin _ (changeModule a.hom w.val) = 0
  · rw [change_polarOver, he, map_zero]
  · rw [change_polarOver, hf, map_zero]

private theorem diagonal_conjugates_shear (R : TestAlgebra F) (s : Rˣ)
    (w : perpendicularOver q h b R) :
    conjugate q R (diagonalUnit q h b R s) (shearValue q h R w) =
      shearValue q h R ((s : R) ^ 2 • w.val) := by
  let d := diagonalUnit q h b R s
  have hz := diagonal_conjugates_w q h b R s w
  have he := diagonal_conjugates_e q h b R s
  have hmul (x y : ScalarClifford q R) :
      conjugate q R d (x * y) = conjugate q R d x * conjugate q R d y := by
    simp only [conjugate, mul_assoc, ← mul_assoc (↑d⁻¹ : ScalarClifford q R) (↑d), Units.inv_mul, one_mul]
  simp only [shearValue]
  change conjugate q R d (1 + E q h R * vectors q R w.val) = _
  have hAdd (x : ScalarClifford q R) : conjugate q R d (1 + x) = 1 + conjugate q R d x := by
    simp [conjugate, mul_add, add_mul]
  rw [hAdd, hmul, he, hz, map_smul, smul_mul_assoc, mul_smul_comm]

include b in
private theorem represented_orbit (hr : IsSpinPointRepresentation q G rep)
    {cochar : Cocharacter G} (hd : IsDiagonal q h rep cochar)
    {R : TestAlgebra F} (g : GroupPoints G R) :
    (rep (laurentAlgebra R) (orbit cochar g)).val =
      conjugate q (laurentAlgebra R) (diagonalUnit q h b _ (laurentParameter R))
        (coefficientMap q R (laurentConstants R).hom (rep R g).val) := by
  let S := laurentAlgebra R
  have ht : rep S (cocharacterPoint cochar S (laurentParameter R)) =
      diagonalUnit q h b S (laurentParameter R) := Units.ext (hd S _)
  change (rep S (cocharacterPoint cochar S (laurentParameter R) *
    (show GroupPoints G S from mapPoints (laurentConstants R) g) *
      (cocharacterPoint cochar S (laurentParameter R))⁻¹)).val = _
  rw [map_mul, map_mul, map_inv, ht, Units.val_mul, Units.val_mul,
    rep_value_natural q rep hr]
  rfl

private theorem shear_contracts (hr : IsSpinPointRepresentation q G rep)
    {cochar : Cocharacter G} (hd : IsDiagonal q h rep cochar)
    (R : TestAlgebra F) (w : perpendicularOver q h b R) (g : GroupPoints G R)
    (hg : (rep R g).val = shearValue q h R w) : HasLimit cochar g 1 := by
  let S := polynomialAlgebra R
  let T := laurentAlgebra R
  let wp : perpendicularOver q h b S :=
    ⟨(Polynomial.X : S) ^ 2 • changeModule (polynomialConstants R).hom w.val,
      Submodule.smul_mem _ _ (change_perpendicular q h b (polynomialConstants R) w)⟩
  obtain ⟨p, hp, _⟩ := exists_shear_point q h b rep hr S wp
  have hparam : (polynomialToLaurent R).hom (Polynomial.X : S) =
      (laurentParameter R : Tˣ).val := Polynomial.toLaurent_X
  have hzero : (polynomialEvaluate R 0).hom (Polynomial.X : S) = 0 := by
    exact Polynomial.eval₂_X _ _
  have hcomp {A B C : TestAlgebra F} (a : A ⟶ B) (f : B ⟶ C) (x : A ⊗[F] V) :
      changeModule f.hom (changeModule a.hom x) = changeModule (a ≫ f).hom x := by
    induction x with
    | tmul c z => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨p, rep_val_injective q rep hr T ?_, rep_val_injective q rep hr R ?_⟩
  · dsimp only
    rw [rep_value_natural q rep hr, hp, change_shear, represented_orbit q h b rep hr hd,
      hg, change_shear]
    change _ = conjugate q T (diagonalUnit q h b T (laurentParameter R))
      (shearValue q h T (⟨_, change_perpendicular q h b (laurentConstants R) w⟩ :
        perpendicularOver q h b T).val)
    rw [diagonal_conjugates_shear]
    congr 1
    change changeModule (polynomialToLaurent R).hom
      ((Polynomial.X : S) ^ 2 • changeModule (polynomialConstants R).hom w.val) = _
    rw [changeModule_smul, map_pow, hparam, hcomp, polynomialConstants_laurent]
  · dsimp only
    rw [rep_value_natural q rep hr, hp, change_shear, map_one, Units.val_one]
    change shearValue q h R (changeModule (polynomialEvaluate R 0).hom
      ((Polynomial.X : S) ^ 2 • changeModule (polynomialConstants R).hom w.val)) = 1
    rw [changeModule_smul, map_pow, hzero, zero_pow (by decide), zero_smul]
    simp [shearValue]

theorem shearsContract : ShearsContract.{u} := by
  intro F _ V _ _ I _ q b h G rep cochar hr hd
  have aux (p : HyperbolicPair q) (c : Cocharacter G) (hc : IsDiagonal q p rep c)
      (R : TestAlgebra F) (w : perpendicularOver q p b R) :
      ∃ g : GroupPoints G R, (rep R g).val = shearValue q p R w ∧ HasLimit c g 1 ∧
        ∀ x, conjugate q R (rep R g) (vectors q R x) =
          vectors q R (shearAction q p b w x) := by
    obtain ⟨g, hg, hact⟩ := exists_shear_point q p b rep hr R w
    exact ⟨g, hg, shear_contracts q p b rep hr hc R w g hg, hact⟩
  exact ⟨aux h cochar hd, aux h.swap (oppositeCocharacter cochar) (opposite_diagonal q h rep hd)⟩

private theorem plane_conjugation {S A : Type u} [CommRing S] [Ring A] [Algebra S A]
    {e f : A} (s : Sˣ) (x : A) :
    plane e f (s : S) (↑s⁻¹ : S) * x * plane e f (↑s⁻¹ : S) (s : S) =
      ((e * f) * x * (e * f) + (f * e) * x * (f * e)) +
        (s : S) ^ 2 • ((e * f) * x * (f * e)) +
        (↑s⁻¹ : S) ^ 2 • ((f * e) * x * (e * f)) := by
  simp only [plane, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
    Units.inv_mul, Units.mul_inv, one_smul, pow_two]
  abel

/-- Conjugation weights on the four corners cut out by the two plane idempotents. -/
private theorem laurent_orbit (R : TestAlgebra F) (x : ScalarClifford q R) :
    let p := E q h R * L q h R
    let r := L q h R * E q h R
    let j := coefficientMap q R (laurentConstants R).hom
    conjugate q (laurentAlgebra R) (diagonalUnit q h b _ (laurentParameter R)) (j x) =
      j (p * x * p + r * x * r) + (LaurentPolynomial.T 2 : LaurentPolynomial R) • j (p * x * r) +
        (LaurentPolynomial.T (-2) : LaurentPolynomial R) • j (r * x * p) := by
  dsimp only
  change diagonal q h _ (laurentParameter R) * _ *
    diagonal q h _ (laurentParameter R)⁻¹ = _
  rw [diagonal_formula, diagonal_formula, inv_inv, plane_conjugation]
  have hE := change_vector q (laurentConstants R) (vectorOver R h.e)
  have hL := change_vector q (laurentConstants R) (vectorOver R h.f)
  rw [change_vectorOver] at hE hL
  change coefficientMap q R (laurentConstants R).hom (E q h R) = E q h _ at hE
  change coefficientMap q R (laurentConstants R).hom (L q h R) = L q h _ at hL
  have hp := (map_mul (coefficientMap q R (laurentConstants R).hom)
    (E q h R) (L q h R)).trans (congrArg₂ (· * ·) hE hL)
  have hq := (map_mul (coefficientMap q R (laurentConstants R).hom)
    (L q h R) (E q h R)).trans (congrArg₂ (· * ·) hL hE)
  simp only [map_add, map_mul (coefficientMap q R (laurentConstants R).hom) (_ * _) _,
    hp, hq]
  change _ + (LaurentPolynomial.T 1 : LaurentPolynomial R) ^ 2 • _ +
    (LaurentPolynomial.T (-1) : LaurentPolynomial R) ^ 2 • _ = _
  rw [LaurentPolynomial.T_pow, LaurentPolynomial.T_pow]
  norm_num

include b in
/-- The negative corner vanishes for a polynomial family. Its diagonal corner
is the evaluation at zero. -/
private theorem laurent_coeff_corners [Fintype I] (R : TestAlgebra F)
    (y : ScalarClifford q (polynomialAlgebra R)) (d k n : ScalarClifford q R)
    (hy : coefficientMap q (polynomialAlgebra R) (polynomialToLaurent R).hom y =
      coefficientMap q R (laurentConstants R).hom d +
        (LaurentPolynomial.T 2 : LaurentPolynomial R) •
          coefficientMap q R (laurentConstants R).hom k +
        (LaurentPolynomial.T (-2) : LaurentPolynomial R) •
          coefficientMap q R (laurentConstants R).hom n) :
    n = 0 ∧ d = coefficientMap q (polynomialAlgebra R) (polynomialEvaluate R 0).hom y := by
  classical
  let B := orderedBasis q b
  have extract (i : Finset I) :
      ((B.baseChange (Polynomial R)).coord i y).toLaurent =
        LaurentPolynomial.C ((B.baseChange R).coord i d) +
          LaurentPolynomial.T 2 * LaurentPolynomial.C ((B.baseChange R).coord i k) +
          LaurentPolynomial.T (-2) * LaurentPolynomial.C ((B.baseChange R).coord i n) := by
    have he := congrArg ((B.baseChange (LaurentPolynomial R)).coord i) hy
    let j := (polynomialToLaurent R).hom
    let c := (laurentConstants R).hom
    change (B.baseChange (LaurentPolynomial R)).coord i (changeModule j y) =
      (B.baseChange (LaurentPolynomial R)).coord i
        (changeModule c d + (LaurentPolynomial.T 2 : LaurentPolynomial R) • changeModule c k +
          (LaurentPolynomial.T (-2) : LaurentPolynomial R) • changeModule c n) at he
    simp only [map_add, map_smul, smul_eq_mul, changeModule_coord] at he
    exact he
  have he0 (i : Finset I) :
      (B.baseChange R).coord i n = 0 := by
    have ev := congrArg (fun p : LaurentPolynomial R => p.coeff (-2)) (extract i)
    change _ = _ at ev
    simp only [coeff_toLaurent_neg _ (by decide : (-2 : ℤ) < 0),
      LaurentPolynomial.T_mul, ← LaurentPolynomial.single_eq_C_mul_T] at ev
    change 0 = (LaurentPolynomial.C _).coeff (-2) +
      (Finsupp.single (2 : ℤ) ((B.baseChange R).coord i k)) (-2) +
      (Finsupp.single (-2 : ℤ) ((B.baseChange R).coord i n)) (-2) at ev
    simpa [LaurentPolynomial.C_apply, Finsupp.single_apply] using ev.symm
  have he1 (i : Finset I) :
      (B.baseChange R).coord i d =
        (B.baseChange R).coord i (coefficientMap q (polynomialAlgebra R)
          (polynomialEvaluate R 0).hom y) := by
    have ev := congrArg (fun p : LaurentPolynomial R => p.coeff 0) (extract i)
    simp only [LaurentPolynomial.T_mul, ← LaurentPolynomial.single_eq_C_mul_T] at ev
    have hs : (↑(0 : ℕ) : ℤ) = 0 := rfl
    rw [← hs, coeff_toLaurent_nat] at ev
    change ((B.baseChange (Polynomial R)).coord i y).coeff 0 =
      (LaurentPolynomial.C _).coeff 0 +
      (Finsupp.single (2 : ℤ) ((B.baseChange R).coord i k)) 0 +
      (Finsupp.single (-2 : ℤ) ((B.baseChange R).coord i n)) 0 at ev
    have ep : ((B.baseChange (Polynomial R)).coord i y).coeff 0 =
        (B.baseChange R).coord i d := by
      simpa [LaurentPolynomial.C_apply, Finsupp.single_apply] using ev
    rw [show coefficientMap q (polynomialAlgebra R) (polynomialEvaluate R 0).hom y =
      changeModule (polynomialEvaluate R 0).hom y from rfl, changeModule_coord, ← ep]
    exact Polynomial.coeff_zero_eq_eval_zero _
  constructor
  · apply (B.baseChange R).repr.injective
    ext i
    exact (he0 i).trans (by simp)
  · apply (B.baseChange R).repr.injective
    ext i
    exact he1 i

private theorem shear_parameter_injective (R : TestAlgebra F) :
    Function.Injective (fun w : perpendicularOver q h b R => shearValue q h R w.val) := by
  intro x y hxy
  have xy := add_left_cancel hxy
  let e := E q h R
  let f := L q h R
  let X := vectors q R x.val
  let Y := vectors q R y.val
  have r := plane_relations q h b R
  have hx := orthogonal_vector_swap q b R (vectorOver R h.f) x.val x.property.2
  have hy := orthogonal_vector_swap q b R (vectorOver R h.f) y.val y.property.2
  have hx' := orthogonal_vector_swap q b R (vectorOver R h.e) x.val x.property.1
  have hy' := orthogonal_vector_swap q b R (vectorOver R h.e) y.val y.property.1
  change e * X = e * Y at xy
  change X * f = -(f * X) at hx
  change Y * f = -(f * Y) at hy
  change X * e = -(e * X) at hx'
  change Y * e = -(e * Y) at hy'
  apply Subtype.ext
  apply vectors_injective q R b
  change X = Y
  calc
    X = (e * f + f * e) * X := by rw [r.sum, one_mul]
    _ = -(e * X) * f + f * (e * X) := by
      simp only [add_mul, mul_assoc, hx, neg_mul, mul_neg, neg_neg]
    _ = (e * f + f * e) * Y := by
      rw [xy]; simp only [add_mul, mul_assoc, hy, neg_mul, mul_neg, neg_neg]
    _ = Y := by rw [r.sum, one_mul]

private theorem contracting_shear [Fintype I] (hr : IsSpinPointRepresentation q G rep)
    {cochar : Cocharacter G} (hd : IsDiagonal q h rep cochar)
    (R : TestAlgebra F) (g : GroupPoints G R) (hg : HasLimit cochar g 1) :
    ∃! w : perpendicularOver q h b R, (rep R g).val = shearValue q h R w := by
  obtain ⟨y, hy, hy0⟩ := hg
  let a := rep R g
  let e := E q h R
  let f := L q h R
  let P := e * f
  let Q := f * e
  let n := P * a.val * Q
  have r := plane_relations q h b R
  have orbit_eq := congrArg (fun p => (rep (laurentAlgebra R) p).val) hy
  rw [rep_value_natural q rep hr, represented_orbit q h b rep hr hd,
    laurent_orbit q h b] at orbit_eq
  have eval_eq := congrArg (fun p => (rep R p).val) hy0
  rw [rep_value_natural q rep hr, map_one, Units.val_one] at eval_eq
  obtain ⟨hneg, hzero⟩ := laurent_coeff_corners q b R _ _ _ _ orbit_eq
  rw [eval_eq] at hzero
  have ha : a.val = 1 + n := by
    change Q * a.val * P = 0 at hneg
    change P * a.val * P + Q * a.val * Q = 1 at hzero
    calc
      a.val = (P + Q) * a.val * (P + Q) := by rw [r.sum, one_mul, mul_one]
      _ = (P * a.val * P + Q * a.val * Q) + n + Q * a.val * P := by dsimp [n]; noncomm_ring
      _ = 1 + n := by rw [hneg, hzero, add_zero]
  have nen : n * e = 0 := by
    have hz : Q * e = 0 := by change (f * e) * e = _; rw [mul_assoc, r.ee, mul_zero]
    change (P * a.val * Q) * e = 0
    rw [mul_assoc, hz, mul_zero]
  have enn : e * n = 0 := by
    have hz : e * P = 0 := by change e * (e * f) = _; rw [← mul_assoc, r.ee, zero_mul]
    change e * (P * a.val * Q) = 0
    calc
      _ = (e * P) * a.val * Q := by noncomm_ring
      _ = 0 := by rw [hz, zero_mul, zero_mul]
  have aE : a.val * e = e := by rw [ha, add_mul, nen, one_mul, add_zero]
  have Ea : e * a.val = e := by rw [ha, mul_add, enn, mul_one, add_zero]
  have iaE : a.inv * e = e := by
    calc
      a.inv * e = a.inv * (a.val * e) := by rw [aE]
      _ = e := by rw [← mul_assoc, a.inv_val, one_mul]
  have nfE : n * f * e = n := by
    have hQQ : Q * Q = Q := by change _ * (f * e) = _; rw [← mul_assoc, r.swap.ele]
    change n * f * e = n
    rw [mul_assoc, show f * e = Q from rfl]
    change (P * a.val * Q) * Q = _
    rw [mul_assoc, hQQ]
  have amem : a ∈ spinUnits q R := (hr.1 R).2 ▸ Set.mem_range_self g
  let A : SpinFunctor.Spin q R b := ⟨a, amem⟩
  let act := SpinFunctor.vectorAction q R b A
  have act_e : act (vectorOver R h.e) = vectorOver R h.e := by
    apply vectors_injective q R b
    rw [SpinFunctor.vectorAction_characterization q R b A]
    change a.val * e * a.inv = e
    rw [aE]
    calc
      e * a.inv = (e * a.val) * a.inv := by rw [Ea]
      _ = e := by rw [mul_assoc, a.val_inv, mul_one]
  let x := act (vectorOver R h.f) - vectorOver R h.f
  have hx : (ExtendedForm q R b).polarBilin (vectorOver R h.e) x = 0 := by
    have H := SpinFunctor.vectorAction_preserves q R b A
    have H' : (ExtendedForm q R b).polarBilin (act (vectorOver R h.e)) (act (vectorOver R h.f)) =
        (ExtendedForm q R b).polarBilin (vectorOver R h.e) (vectorOver R h.f) := by
      change ∀ y, (ExtendedForm q R b) (act y) = (ExtendedForm q R b) y at H
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, H]
    dsimp [x]
    rw [map_sub, ← act_e, H', act_e, sub_self]
  -- The image of the opposite null vector recovers the surviving corner.
  have nx : vectors q R x * e = n := by
    dsimp [x]
    rw [map_sub, SpinFunctor.vectorAction_characterization q R b A]
    change (a.val * f * a.inv - f) * e = n
    rw [sub_mul, mul_assoc (a.val * f), iaE, ha, add_mul, one_mul, add_mul, nfE]
    abel
  obtain ⟨w, hw⟩ := over_decompose q h b R x
  have nn : n = -(e * vectors q R w.val) := by
    have hs := orthogonal_vector_swap q b R (vectorOver R h.e) w.val w.property.1
    rw [← nx]
    have hw' : x = (ExtendedForm q R b).polarBilin (vectorOver R h.f) x • vectorOver R h.e + w.val := by
      simpa [hx] using hw
    rw [hw', map_add, map_smul, add_mul, smul_mul_assoc, r.ee, smul_zero, zero_add]
    exact hs
  have hresult : a.val = shearValue q h R (-w).val := by
    rw [ha, nn]
    change 1 + -(e * vectors q R w.val) = 1 + e * vectors q R (-w.val)
    rw [map_neg, mul_neg]
  refine ⟨-w, hresult, ?_⟩
  intro z hz
  exact shear_parameter_injective q h b R (hz.symm.trans hresult)

theorem contractingPoints : ContractingPoints.{u} := by
  intro F _ _ V _ _ I _ _ q b h _ G rep cochar hr hd
  exact ⟨contracting_shear q h b rep hr hd,
    contracting_shear q h.swap b rep hr (opposite_diagonal q h rep hd)⟩

private theorem exists_distinct_weights (F : Type u) [Field F] [Infinite F] :
    ∃ s : Fˣ, (s : F) ^ 2 ≠ (↑s⁻¹ : F) ^ 2 ∧
      (s : F) ^ 2 ≠ 1 ∧ (↑s⁻¹ : F) ^ 2 ≠ 1 := by
  let p : Polynomial F := Polynomial.X * (Polynomial.X ^ 4 - 1)
  have hp : p ≠ 0 := by
    intro H
    have hh := congrArg (fun r : Polynomial F => r.coeff 5) H
    simp [p, mul_sub, ← pow_succ', Polynomial.coeff_X_pow, Polynomial.coeff_X] at hh
  obtain ⟨s, hs⟩ := (Polynomial.eventually_eval_ne_zero_cofinite hp).exists
  have H : s * (s ^ 4 - 1) ≠ 0 := by simpa [p] using hs
  have hs0 : s ≠ 0 := (mul_ne_zero_iff.mp H).1
  have hs4 : s ^ 4 ≠ 1 := sub_ne_zero.mp (mul_ne_zero_iff.mp H).2
  let t := Units.mk0 s hs0
  have hmul : (t : F) ^ 2 * (↑t⁻¹ : F) ^ 2 = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  refine ⟨t, ?_, ?_, ?_⟩
  · intro he
    apply hs4
    change (t : F) ^ 4 = 1
    rw [← he] at hmul
    rw [show (4 : ℕ) = 2 + 2 by decide, pow_add]
    exact hmul 
  · intro he
    exact hs4 (by change (t : F) ^ 4 = 1; rw [show (4 : ℕ) = 2 + 2 by decide, pow_add, he, one_mul])
  · intro he
    rw [he, mul_one] at hmul
    exact hs4 (by change (t : F) ^ 4 = 1; rw [show (4 : ℕ) = 2 + 2 by decide, pow_add, hmul, one_mul])

private theorem action_preserves_polar (R : TestAlgebra F)
    (A : SpinFunctor.Spin q R b) (x y : R ⊗[F] V) :
    (ExtendedForm q R b).polarBilin (SpinFunctor.vectorAction q R b A x)
      (SpinFunctor.vectorAction q R b A y) = (ExtendedForm q R b).polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add,
    SpinFunctor.vectorAction_preserves]

set_option maxHeartbeats 600000 in
theorem centralizerAction : CentralizerAction.{u} := by
  intro F _ _ V _ _ I _ q b h G rep cochar hr hd R g hg
  obtain ⟨s, h12, h10, h20⟩ := exists_distinct_weights F
  let a : SpinFunctor.Spin q R b := ⟨rep R g, show rep R g ∈ spinUnits q R from
    (hr.1 R).2 ▸ Set.mem_range_self g⟩
  let d : SpinFunctor.Spin q R b := ⟨diagonalUnit q h b R s, diagonal_spin q h b R s⟩
  let act := SpinFunctor.vectorAction q R b
  let A := act a
  let D := act d
  let e := vectorOver R h.e
  let f := vectorOver R h.f
  let B := (ExtendedForm q R b).polarBilin
  have hef : B e f = 1 := by
    change (ExtendedForm q R b).polarBilin (vectorOver R h.e) (vectorOver R h.f) = 1
    rw [polar_over, h.polar_ef, map_one]
  have hfe : B f e = 1 := (QuadraticMap.polar_comm _ _ _).trans hef
  have hee : B e e = 0 := polar_self_zero _ (by
    change ExtendedForm q R b (vectorOver R h.e) = 0
    rw [form_over, h.q_e, map_zero])
  have hff : B f f = 0 := polar_self_zero _ (by
    change ExtendedForm q R b (vectorOver R h.f) = 0
    rw [form_over, h.q_f, map_zero])
  have hac : ∀ x, D (A x) = A (D x) := by
    have hc := (centralizes_onAlgebras cochar g).mp hg R (𝟙 R) s
    have hi : (mapPoints (𝟙 R) g : GroupPoints G R) = g := by
      simp [mapPoints]
    rw [hi] at hc
    have hs : rep R (cocharacterPoint cochar R s) = d.val := Units.ext (hd R s)
    have hac : Commute a d := by
      apply Subtype.ext
      change rep R g * d.val = d.val * rep R g
      rw [← hs]
      exact (hc.map (rep R)).eq
    exact fun x => congrArg (fun m : (R ⊗[F] V) ≃ₗ[R] (R ⊗[F] V) => m x) (hac.symm.map act).eq
  have he : D e = (s : F) ^ 2 • e := by
    apply vectors_injective q R b
    rw [SpinFunctor.vectorAction_characterization q R b d, map_smul]
    exact diagonal_conjugates_e q h b R s
  have hf : D f = (↑s⁻¹ : F) ^ 2 • f := by
    apply vectors_injective q R b
    rw [SpinFunctor.vectorAction_characterization q R b d, map_smul]
    exact diagonal_conjugates_f q h b R s
  have hw (w : perpendicularOver q h b R) : D w.val = w.val := by
    apply vectors_injective q R b
    rw [SpinFunctor.vectorAction_characterization q R b d]
    exact diagonal_conjugates_w q h b R s w
  have weight (x : R ⊗[F] V) :
      D x = (B f x * (s : F) ^ 2) • e + (B e x * (↑s⁻¹ : F) ^ 2) • f +
        (x - B f x • e - B e x • f) := by
    obtain ⟨w, hx⟩ := over_decompose q h b R x
    change x = B f x • e + B e x • f + w.val at hx
    have H : x - B f x • e - B e x • f = w.val := by
      exact (eq_sub_iff_add_eq.mpr (eq_sub_iff_add_eq.mpr (by simpa [add_comm, add_left_comm,
        add_assoc] using hx.symm))).symm
    rw [H]
    conv_lhs => rw [hx]
    rw [map_add, map_add, map_smul, map_smul, he, hf, hw, smul_smul, smul_smul]
  have eqs (x : R ⊗[F] V) (c : F) (hx : D x = c • x) :
      B f x * ((s : F) ^ 2 - c) = 0 ∧ B e x * ((↑s⁻¹ : F) ^ 2 - c) = 0 := by
    have H1 := congrArg (B f) ((weight x).symm.trans hx)
    have H2 := congrArg (B e) ((weight x).symm.trans hx)
    simp only [map_add, map_sub, map_smul, hfe, hff, hee, hef, smul_eq_mul, mul_one, mul_zero,
      add_zero, zero_add, sub_self, sub_zero] at H1 H2
    constructor <;> rw [mul_sub, sub_eq_zero]
    · exact H1.trans (mul_comm _ _)
    · exact H2.trans (mul_comm _ _)
  have line_e (x : R ⊗[F] V) (hx : D x = (s : F) ^ 2 • x) :
      x = B f x • e := by
    have hz := (mul_eq_zero.mp (eqs x _ hx).2).resolve_right (sub_ne_zero.mpr h12.symm)
    obtain ⟨w, hwx⟩ := over_decompose q h b R x
    change x = B f x • e + B e x • f + w.val at hwx
    simp only [hz, zero_smul, add_zero] at hwx
    have hh := hx
    rw [hwx, map_add, map_smul, he, hw, smul_add, smul_smul, smul_smul, mul_comm (B f x),
      add_right_inj] at hh
    have hz' : (1 - (s : F) ^ 2) • w.val = 0 :=
      calc
        _ = (1 : F) • w.val - (s : F) ^ 2 • w.val := sub_smul _ _ _
        _ = 0 := sub_eq_zero.mpr ((one_smul _ _).trans hh)
    have h0 := (smul_eq_zero.mp hz').resolve_left (sub_ne_zero.mpr h10.symm)
    simpa [h0] using hwx
  have line_f (x : R ⊗[F] V) (hx : D x = (↑s⁻¹ : F) ^ 2 • x) :
      x = B e x • f := by
    have hz := (mul_eq_zero.mp (eqs x _ hx).1).resolve_right (sub_ne_zero.mpr h12)
    obtain ⟨w, hwx⟩ := over_decompose q h b R x
    change x = B f x • e + B e x • f + w.val at hwx
    simp only [hz, zero_smul, zero_add] at hwx
    have hh := hx
    rw [hwx, map_add, map_smul, hf, hw, smul_add, smul_smul, smul_smul, mul_comm (B e x),
      add_right_inj] at hh
    have hz' : (1 - (↑s⁻¹ : F) ^ 2) • w.val = 0 :=
      calc
        _ = (1 : F) • w.val - (↑s⁻¹ : F) ^ 2 • w.val := sub_smul _ _ _
        _ = 0 := sub_eq_zero.mpr ((one_smul _ _).trans hh)
    have h0 := (smul_eq_zero.mp hz').resolve_left (sub_ne_zero.mpr h20.symm)
    simpa [h0] using hwx
  have haE : A e = B f (A e) • e := line_e _ (by rw [hac, he, map_smul])
  have haF : A f = B e (A f) • f := line_f _ (by rw [hac, hf, map_smul])
  let t := B f (A e)
  let z := B e (A f)
  have htz : t * z = 1 := by
    have h := action_preserves_polar q b R a e f
    change B (A e) (A f) = B e f at h
    rw [haE, haF, map_smul, map_smul, LinearMap.smul_apply, hef] at h
    change z * (t * 1) = 1 at h
    rw [mul_one, mul_comm] at h
    exact h
  let u : Fˣ := ⟨t, z, htz, (mul_comm _ _).trans htz⟩
  refine ⟨A, u, SpinFunctor.vectorAction_characterization q R b a, haE, haF, ?_⟩
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hwy := hw ⟨y, hy⟩
    have hex : D (A y) = (1 : F) • A y := by rw [hac, hwy, one_smul]
    obtain ⟨h1, h2⟩ := eqs _ 1 hex
    exact ⟨(mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr h20),
      (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr h10)⟩
  · intro x hx
    refine ⟨A.symm x, ?_, A.apply_symm_apply x⟩
    have H : D (A.symm x) = (1 : F) • A.symm x := by
      apply A.injective
      rw [← hac, A.apply_symm_apply, hw ⟨x, hx⟩, one_smul, A.apply_symm_apply]
    obtain ⟨h1, h2⟩ := eqs _ 1 H
    exact ⟨(mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr h20),
      (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr h10)⟩

private theorem perpendicular_eq_zero_of_zero_norm (hq : IsRegular q)
    (hz : ∀ w : perpendicular q h, q w.val = 0) :
    ∀ w : perpendicular q h, w.val = 0 := by
  intro w
  have hrad : w.val ∈ LinearMap.ker q.polarBilin := by
    apply LinearMap.mem_ker.mpr
    ext x
    obtain ⟨v, hve, hvf, hv⟩ := decompose q h.q_e h.q_f h.polar_ef x
    let v' : perpendicular q h := ⟨v, hve, hvf⟩
    have hp : q.polarBilin w.val v = 0 := by
      have ha := hz (w + v')
      change q (w.val + v) = 0 at ha
      rw [QuadraticMap.map_add q, hz w, show q v = 0 from hz v', zero_add, zero_add] at ha
      exact ha
    have he : q.polarBilin w.val h.e = 0 :=
      (QuadraticMap.polar_comm q _ _).trans w.property.1
    have hf : q.polarBilin w.val h.f = 0 :=
      (QuadraticMap.polar_comm q _ _).trans w.property.2
    conv_lhs => rw [hv]
    simp only [map_add, map_smul, he, hf, hp, smul_zero, add_zero, LinearMap.zero_apply]
  rcases hq with hq | ⟨r, hr, hq⟩
  · rwa [hq, Submodule.mem_bot] at hrad
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hq ▸ hrad)
    have hqa := hz w
    rw [← ha, q.map_smul, smul_eq_mul] at hqa
    have h0 := mul_self_eq_zero.mp ((mul_eq_zero.mp hqa).resolve_right hr)
    rw [← ha, h0, zero_smul]

private theorem scalar_plane_spans (hz : ∀ w : perpendicular q h, w.val = 0)
    (R : TestAlgebra F) (x : R ⊗[F] V) :
    ∃ a c : R, x = a • vectorOver R h.e + c • vectorOver R h.f := by
  induction x with
  | tmul r v =>
    obtain ⟨w, he, hf, hv⟩ := decompose q h.q_e h.q_f h.polar_ef v
    have hw := hz ⟨w, he, hf⟩
    change w = 0 at hw
    rw [hw, add_zero] at hv
    refine ⟨r * algebraMap F R (q.polarBilin h.f v),
      r * algebraMap F R (q.polarBilin h.e v), ?_⟩
    conv_lhs => rw [hv]
    simp only [TensorProduct.tmul_add, TensorProduct.tmul_smul, vectorOver,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.smul_def, mul_comm r]
  | add x y hx hy =>
    obtain ⟨a, c, hx⟩ := hx
    obtain ⟨a', c', hy⟩ := hy
    refine ⟨a + a', c + c', ?_⟩
    rw [hx, hy, add_smul, add_smul]
    abel

include b in
/-- In dimension two the even part is generated as a module by the two plane
idempotents, over every test algebra. -/
private theorem even_plane (hz : ∀ w : perpendicular q h, w.val = 0)
    (R : TestAlgebra F) (x : ScalarClifford q R) (hx : x ∈ evenPart q R) :
    ∃ a c : R, x = plane (E q h R) (L q h R) a c := by
  let Q := ExtendedForm q R b
  let φ := cliffordEquiv q R b
  let E' := CliffordAlgebra.ι Q (vectorOver R h.e)
  let L' := CliffordAlgebra.ι Q (vectorOver R h.f)
  have he : φ (E q h R) = E' := cliffordEquiv_vector q R b _
  have hf : φ (L q h R) = L' := cliffordEquiv_vector q R b _
  have r := plane_relations q h b R
  have r' : PlaneRelations E' L' := by
    constructor
    · rw [← he, ← map_mul φ, r.ee, map_zero]
    · rw [← hf, ← map_mul φ, r.ll, map_zero]
    · rw [← he, ← hf, ← map_mul φ, ← map_mul φ, ← map_add φ, r.sum, map_one]
  have hw : φ x ∈ evenOdd Q 0 := (cliffordEquiv_even q R b x).mpr hx
  have hh (y : CliffordAlgebra Q) (hy : y ∈ evenOdd Q 0) :
      ∃ a c : R, y = plane E' L' a c := by
    induction y, hy using even_induction with
    | algebraMap t =>
      refine ⟨t, t, ?_⟩
      change _ = t • (E' * L') + t • (L' * E')
      rw [← smul_add, r'.sum, Algebra.smul_def, mul_one]
    | add x y _ _ hx hy =>
      obtain ⟨a, c, rfl⟩ := hx
      obtain ⟨d, j, rfl⟩ := hy
      refine ⟨a + d, c + j, ?_⟩
      simp only [plane, add_smul]
      abel
    | ι_mul_ι_mul x y z _ hz' =>
      obtain ⟨a, c, hx⟩ := scalar_plane_spans q h hz R x
      obtain ⟨d, j, hy⟩ := scalar_plane_spans q h hz R y
      obtain ⟨s, t, rfl⟩ := hz'
      have hprod : CliffordAlgebra.ι Q x * CliffordAlgebra.ι Q y =
          plane E' L' (a * j) (c * d) := by
        rw [hx, hy, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
        change (a • E' + c • L') * (d • E' + j • L') = _
        simp only [plane, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
          r'.ee, r'.ll, smul_zero, zero_add, add_zero, mul_comm d c, mul_comm j a]
        apply add_comm
      rw [hprod, r'.plane_mul]
      exact ⟨_, _, rfl⟩
  obtain ⟨a, c, ha⟩ := hh (φ x) hw
  refine ⟨a, c, φ.injective ?_⟩
  rw [ha, plane, plane, map_add, map_smul, map_smul, map_mul, map_mul, he, hf]

theorem hyperbolicPlaneTorus : HyperbolicPlaneTorus.{u} := by
  intro F _ V _ _ I _ q b h hW G hG rep cochar hr hd
  let gm := specGroup (groupAlgebra F IntegerCharacters)
  let H := groupPointsFunctor F
  let α := H.map cochar
  have hzero : ∀ x : V, x ∈ perpendicular q h → x = 0 := by
    rw [hW]
    intro x hx
    rwa [Submodule.mem_bot] at hx
  have hz (w : perpendicular q h) : w.val = 0 := hzero w.val w.property
  have bij (R : TestAlgebra F) : Function.Bijective ((α.app R).hom) := by
    constructor
    · intro p₁ p₂ hp
      have hpoint (p : GroupPoints gm R) : unitPoint R (unitEquiv R p) = p :=
        (unitEquiv R).injective (unitEquiv_unitPoint R _)
      rw [← hpoint p₁, ← hpoint p₂] at hp
      change cocharacterPoint cochar R (unitEquiv R p₁) =
        cocharacterPoint cochar R (unitEquiv R p₂) at hp
      have heq := congrArg (fun g : GroupPoints G R => (rep R g).val) hp
      change (rep R (cocharacterPoint cochar R (unitEquiv R p₁))).val =
        (rep R (cocharacterPoint cochar R (unitEquiv R p₂))).val at heq
      rw [hd, hd, diagonal_formula, diagonal_formula] at heq
      have heq' := congrArg (fun z => z * E q h R) heq
      change _ * E q h R = _ * E q h R at heq'
      rw [(plane_relations q h b R).plane_mul_left,
        (plane_relations q h b R).plane_mul_left] at heq'
      have heq'' : ((unitEquiv R p₁ : Rˣ) : R) • vectorOver R h.e =
          ((unitEquiv R p₂ : Rˣ) : R) • vectorOver R h.e := by
        apply vectors_injective q R b
        rw [map_smul, map_smul]
        exact heq'
      apply (unitEquiv R).injective
      apply Units.ext
      let B := (ExtendedForm q R b).polarBilin (vectorOver R h.f)
      have hpair : B (vectorOver R h.e) = 1 := by
        change (ExtendedForm q R b).polarBilin (vectorOver R h.f) (vectorOver R h.e) = 1
        rw [polar_over, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm q,
          ← QuadraticMap.polarBilin_apply_apply, h.polar_ef, map_one]
      have H := congrArg B heq''
      change B (_ • _) = B (_ • _) at H
      simpa only [map_smul, hpair, smul_eq_mul, mul_one] using H
    · intro g
      have hg : rep R g ∈ spinUnits q R := (hr.1 R).2 ▸ Set.mem_range_self g
      obtain ⟨a, c, ha⟩ := even_plane q h b hz R _ hg.1
      let e := E q h R
      let f := L q h R
      have r := plane_relations q h b R
      have revE : reversion q R e = e := by simp [e]
      have revF : reversion q R f = f := by simp [f]
      have hrev : reversion q R (plane e f a c) = plane e f c a := by
        simp only [plane, map_add, map_smul, reversion_mul q R b, revE, revF, add_comm]
      have hn := hg.2.1
      change reversion q R (rep R g).val * (rep R g).val = 1 at hn
      rw [ha] at hn
      change reversion q R (plane e f a c) * plane e f a c = 1 at hn
      rw [hrev, r.plane_mul, mul_comm c a] at hn
      have hnorm : a * c = 1 := by
        have H : algebraMap R (ScalarClifford q R) (a * c) = algebraMap R _ 1 := by
          rw [map_one, Algebra.algebraMap_eq_smul_one]
          calc
            _ = plane e f (a * c) (a * c) := by
              conv_lhs => rw [← r.sum, smul_add]
              rfl
            _ = _ := hn
        exact scalar_tensor_injective q R b H
      let s : Rˣ := ⟨a, c, hnorm, (mul_comm _ _).trans hnorm⟩
      refine ⟨unitPoint R s, rep_val_injective q rep hr R ?_⟩
      change (rep R (cocharacterPoint cochar R s)).val = (rep R g).val
      rw [hd]
      exact ha.symm
  let β : H.obj gm ≅ H.obj G :=
    NatIso.ofComponents (fun R => (MulEquiv.ofBijective (α.app R).hom (bij R)).toGrpIso)
      (fun a => α.naturality a)
  obtain ⟨inv, hinv⟩ := (groupHomComparison F G gm hG).surjective β.inv
  change H.map inv = β.inv at hinv
  have hgm : IsAffine gm.X.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra F IntegerCharacters))))
  have hα : H.map cochar = β.hom := rfl
  refine ⟨⟨inv, ?_, ?_⟩⟩
  · apply (groupHomComparison F gm gm hgm).injective
    change H.map (cochar ≫ inv) = H.map (𝟙 gm)
    rw [Functor.map_comp, hα, hinv, β.hom_inv_id]
    exact (H.map_id gm).symm
  · apply (groupHomComparison F G G hG).injective
    change H.map (inv ≫ cochar) = H.map (𝟙 G)
    rw [Functor.map_comp, hα, hinv, β.inv_hom_id]
    exact (H.map_id G).symm

include b in
private theorem plane_spin_points_commute (hz : ∀ w : perpendicular q h, w.val = 0)
    (hr : IsSpinPointRepresentation q G rep) (R : TestAlgebra F) (g g' : GroupPoints G R) :
    g * g' = g' * g := by
  apply rep_val_injective q rep hr R
  dsimp only
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  have hg : rep R g ∈ spinUnits q R := (hr.1 R).2 ▸ Set.mem_range_self g
  have hg' : rep R g' ∈ spinUnits q R := (hr.1 R).2 ▸ Set.mem_range_self g'
  obtain ⟨a, c, ha⟩ := even_plane q h b hz R _ hg.1
  obtain ⟨d, j, hd⟩ := even_plane q h b hz R _ hg'.1
  rw [ha, hd, (plane_relations q h b R).plane_mul, (plane_relations q h b R).plane_mul,
    mul_comm a d, mul_comm c j]

open Specs.GeometricRadicals
open CategoryTheory.MonoidalCategory
open Opposite
open private rationalSections solvable_iff_sections
  from LinearAlgebraicGroups.Reductive.GeometricRadicals

include b in
private theorem plane_not_absolutely_almost_simple
    (hz : ∀ w : perpendicular q h, w.val = 0) (H : Specs.AffineAlgebraicGroup F)
    (rep : ∀ R : TestAlgebra F, GroupPoints H.val R →* (ScalarClifford q R)ˣ)
    (hr : IsSpinPointRepresentation q H.val rep) :
    ¬ Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple H := by
  intro hs
  let K := AlgebraicClosure F
  let A := GeometricGroup H
  let R := CommAlgCat.of K K
  have i : (testSpec K).obj (op R) ≅ 𝟙_ (SchemeOver K) :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of K))) (by
      change (𝟙 _) ≫ (𝟙 _) = Spec.map (𝟙 (CommRingCat.of K))
      rw [Spec.map_id, Category.comp_id])
  let m : rationalSections A.val →* Points A.val.X R :=
    { toFun := fun p => i.hom ≫ p
      map_one' := MonObj.comp_one _
      map_mul' := fun _ _ => MonObj.comp_mul _ _ _ }
  have hm : Function.Injective m := by
    intro x y hxy
    exact (cancel_epi i.hom).mp hxy
  let φ := baseChangePointGroupEquiv K H.val R
  have hsol : Group.IsSolvable (rationalSections A.val) := by
    apply Group.isSolvable_of_comm
    intro a c
    apply hm
    apply φ.injective
    rw [map_mul, map_mul, map_mul, map_mul]
    exact plane_spin_points_commute q h b rep hz hr _ _ _
  have hsm : Smooth A.val.X.hom :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback H.val.X.hom (fieldSpecMap F K)) hs.1.1
  have hcon : ConnectedSpace A.val.X.left := by
    let := hs.1.2.1
    exact pullback_of_geometrically
      (GeometricallyConnected.geometrically_connectedSpace (f := H.val.X.hom))
      K (fieldSpecMap F K)
  let N : Specs.ClosedSubgroup A.val :=
    ⟨A.val, 𝟙 _, by change IsClosedImmersion (𝟙 A.val.X.left); infer_instance⟩
  have hnormal : IsSmoothConnectedNormal (G := A) N := by
    refine ⟨hsm, hcon, Specs.subgroupConjugation (𝟙 A.val), ?_⟩
    change _ ≫ 𝟙 _ = _
    rw [Category.comp_id]
  have hrad : IsSolvableRadical A N := by
    refine ⟨hnormal, (solvable_iff_sections A hsm hcon).mpr hsol, ?_⟩
    intro U _ _
    exact ⟨U.inclusion, Category.comp_id _⟩
  obtain ⟨e, _, _⟩ := GeometricRadicals.radicalUnique A
    (fun T => Specs.SchemeDerivedGroup.IsSolvable T.val) hrad
    (GeometricRadicals.geometricSolvableRadicalLargest H)
  obtain ⟨j⟩ := hs.1.2.2
  exact hs.2.1 ⟨e.trans j⟩

theorem noncentrality : Noncentrality.{u} := by
  intro F _ _ V _ _ I _ _ q b h hq G rep cochar hr hd hs
  have hw : ∃ w : perpendicular q h, q w.val ≠ 0 := by
    by_contra! hz
    exact plane_not_absolutely_almost_simple q h b
      (perpendicular_eq_zero_of_zero_norm q h hq hz) G rep hr hs
  obtain ⟨w, hw⟩ := hw
  let R := CommAlgCat.of F F
  let v : perpendicularOver q h b R := ⟨vectorOver R w.val, by
    constructor
    · change (ExtendedForm q R b).polarBilin (vectorOver R h.e) (vectorOver R w.val) = 0
      rw [polar_over, show q.polarBilin h.e w.val = 0 from w.property.1, map_zero]
    · change (ExtendedForm q R b).polarBilin (vectorOver R h.f) (vectorOver R w.val) = 0
      rw [polar_over, show q.polarBilin h.f w.val = 0 from w.property.2, map_zero]⟩
  obtain ⟨g, hg, _⟩ := exists_shear_point q h b rep hr R v
  refine ⟨⟨w, hw⟩, g, ?_⟩
  intro hc
  obtain ⟨s, _, hs, _⟩ := exists_distinct_weights F
  have hcomm := (centralizes_onAlgebras cochar g).mp hc R (𝟙 R) s
  have hi : (mapPoints (𝟙 R) g : GroupPoints G.val R) = g := by simp [mapPoints]
  rw [hi] at hcomm
  have hdu : rep R (cocharacterPoint cochar R s) = diagonalUnit q h b R s := Units.ext (hd R s)
  have huc : Commute (rep R g) (diagonalUnit q h b R s) := by
    have he : Commute (rep R g) (rep R (cocharacterPoint cochar R s)) := hcomm.map (rep R)
    exact hdu ▸ he
  have hv : conjugate q R (diagonalUnit q h b R s) (shearValue q h R v.val) =
      shearValue q h R v.val := by
    rw [← hg]
    have H := congrArg Units.val huc.symm.eq
    change (diagonalUnit q h b R s).val * (rep R g).val =
      (rep R g).val * (diagonalUnit q h b R s).val at H
    rw [conjugate, H, mul_assoc, Units.mul_inv, mul_one]
  rw [diagonal_conjugates_shear] at hv
  have he := shear_parameter_injective q h b R
    (show shearValue q h R (((s : F) ^ 2) • v : perpendicularOver q h b R).val =
      shearValue q h R v.val from hv)
  have hz : ((s : F) ^ 2 - 1) • v.val = 0 := by
    have hh := congrArg Subtype.val he
    exact (sub_smul ((s : F) ^ 2) 1 v.val).trans
      (sub_eq_zero.mpr (hh.trans (one_smul _ _).symm))
  have hv0 := (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hs)
  have hnorm := form_over q b R w.val
  change ExtendedForm q R b v.val = q w.val at hnorm
  rw [hv0, map_zero] at hnorm
  exact hw hnorm.symm

end Field

end
end LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics
