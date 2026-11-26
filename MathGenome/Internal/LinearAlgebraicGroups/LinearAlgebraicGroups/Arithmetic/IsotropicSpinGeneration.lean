import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import Mathlib.Tactic.NoncommRing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinOrthogonalWords
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinScalarExtension
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

namespace LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration

open CliffordAlgebra
open Specs.Arithmetic.IsotropicSpinGeneration

universe u v

section Shear

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable (q : QuadraticForm R V) (e w : V)

private theorem swap (x y : V) :
    ι q x * ι q y + ι q y * ι q x = algebraMap R _ (q.polarBilin x y) := by
  exact ι_mul_ι_add_swap x y

private theorem orthogonal_swap (h : q.polarBilin e w = 0) :
    ι q w * ι q e = -(ι q e * ι q w) := by
  have hv := swap q w e
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
    ← QuadraticMap.polarBilin_apply_apply, h, map_zero] at hv
  exact eq_neg_of_add_eq_zero_left hv

private theorem shear_nilpotent (he : q e = 0) (hew : q.polarBilin e w = 0) :
    (ι q e * ι q w) * (ι q e * ι q w) = 0 := by
  have hee : ι q e * ι q e = 0 := by rw [ι_sq_scalar, he, map_zero]
  calc
    _ = ι q e * (ι q w * ι q e) * ι q w := by noncomm_ring
    _ = -(ι q e * ι q e) * (ι q w * ι q w) := by rw [orthogonal_swap q e w hew]; noncomm_ring
    _ = _ := by rw [hee, neg_zero, zero_mul]

private def shear (he : q e = 0) (hew : q.polarBilin e w = 0) :
    (CliffordAlgebra q)ˣ where
  val := 1 + ι q e * ι q w
  inv := 1 - ι q e * ι q w
  val_inv := by
    calc
      _ = 1 - (ι q e * ι q w) * (ι q e * ι q w) := by noncomm_ring
      _ = 1 := by rw [shear_nilpotent q e w he hew, sub_zero]
  inv_val := by
    calc
      _ = 1 - (ι q e * ι q w) * (ι q e * ι q w) := by noncomm_ring
      _ = 1 := by rw [shear_nilpotent q e w he hew, sub_zero]

private theorem vector_even_product (x y : V) :
    ι q x * ι q y ∈ evenOdd q 0 := by
  have h := SetLike.mul_mem_graded (ι_mem_evenOdd_one q x) (ι_mem_evenOdd_one q y)
  simpa only [show (1 + 1 : ZMod 2) = 0 by decide] using h

private theorem shear_conjugation (he : q e = 0) (hew : q.polarBilin e w = 0) (x : V) :
    (1 + ι q e * ι q w) * ι q x * (1 - ι q e * ι q w) =
      ι q (shearAction q e w x) := by
  let E := ι q e
  let Z := ι q w
  let X := ι q x
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
      simp only [shearAction, map_add, map_sub, map_smul, Algebra.smul_def, map_mul,
        E, Z, X, P, Q, C]

theorem shearCalculation : ShearCalculation.{u,v} := by
  intro R _ V _ _ q e w he hew
  refine ⟨shear q e w he hew, rfl, rfl, ?_, ?_, shear_conjugation q e w he hew⟩
  · exact Submodule.add_mem _ (SetLike.one_mem_graded (evenOdd q)) (vector_even_product q e w)
  · change reverse (1 + ι q e * ι q w) * (1 + ι q e * ι q w) = 1
    rw [map_add, reverse.map_one, reverse.map_mul, reverse_ι, reverse_ι,
      orthogonal_swap q e w hew, ← sub_eq_add_neg]
    exact (shear q e w he hew).inv_val

end Shear

section ScalarShears

open LinearAlgebraicGroups.Albert
open SpinSpecification
open scoped TensorProduct

open private baseChangeEquiv_evenOdd baseChangeEquiv_reverse
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel

universe z j

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

private theorem inverse_shear (q : QuadraticForm R V) (e w : V) (he : q e = 0)
    (hew : q.polarBilin e w = 0) :
    (shear q e w he hew)⁻¹ =
      shear q e (-w) he (by rw [map_neg, hew, neg_zero]) := by
  apply Units.ext
  change 1 - ι q e * ι q w = 1 + ι q e * ι q (-w)
  rw [map_neg, mul_neg, sub_eq_add_neg]

theorem scalarShears : ScalarShears.{u,v,j,z} := by
  intro R _ V _ _ I _ q b S _ _ Q e w he hew
  let φ := CliffordModel.baseChangeEquiv S q b
  let c := shear Q e w he hew
  let a := Units.map φ.symm.toMonoidHom c
  have hv (x : S ⊗[R] V) : φ (vectors q S x) = ι Q x := by
    induction x with
    | tmul t v => exact CliffordModel.baseChangeEquiv_ι S q b t v
    | add x y hx hy => simp only [map_add, hx, hy]
  have ha : φ a.val = c.val := φ.apply_symm_apply _
  have hi : φ a⁻¹.val = c⁻¹.val := by
    change φ ((Units.map φ.symm.toMonoidHom c)⁻¹.val) = _
    rw [← map_inv]
    exact φ.apply_symm_apply _
  have hval : a.val = 1 + vectors q S e * vectors q S w := by
    apply φ.injective
    rw [ha, map_add, map_one, map_mul, hv, hv]
    rfl
  have hinv : a⁻¹.val = 1 - vectors q S e * vectors q S w := by
    apply φ.injective
    rw [hi, map_sub, map_one, map_mul, hv, hv]
    rfl
  have hconj (x : S ⊗[R] V) : conjugate q S a (vectors q S x) =
      vectors q S (shearAction Q e w x) := by
    apply φ.injective
    rw [conjugate, map_mul, map_mul, ha, hi, hv, hv]
    exact shear_conjugation Q e w he hew x
  refine ⟨a, ?_, hval, hinv, hconj⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm : c.val ∈ evenOdd Q 0 :=
      Submodule.add_mem _ (SetLike.one_mem_graded (evenOdd Q)) (vector_even_product Q e w)
    have hm' : φ a.val ∈ (evenPart q S).map φ.toLinearEquiv.toLinearMap := by
      rw [baseChangeEquiv_evenOdd S q b 0, ha]
      exact hm
    obtain ⟨y, hy, hya⟩ := hm'
    exact φ.injective hya ▸ hy
  · apply φ.injective
    rw [map_mul, baseChangeEquiv_reverse S q b, ha, map_one]
    change reverse (1 + ι Q e * ι Q w) * (1 + ι Q e * ι Q w) = 1
    rw [map_add, reverse.map_one, reverse.map_mul, reverse_ι, reverse_ι,
      orthogonal_swap Q e w hew, ← sub_eq_add_neg]
    exact c.inv_val
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, (hconj x).symm⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨shearAction Q e (-w) x, φ.injective ?_⟩
    rw [conjugate, inv_inv, hv, map_mul, map_mul, hi, ha, hv]
    have hci := inverse_shear Q e w he hew
    have hc : c = (shear Q e (-w) he (by rw [map_neg, hew, neg_zero]))⁻¹ :=
      (inv_inv c).symm.trans (congrArg Inv.inv hci)
    rw [hci, hc]
    exact (shear_conjugation Q e (-w) he (by rw [map_neg, hew, neg_zero]) x).symm

end ScalarShears

section Plane

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

private theorem perpendicular_left {q : QuadraticForm R V} (h : HyperbolicPair q)
    (w : h.perpendicular) : q.polarBilin h.e w = 0 :=
  w.property.1

private theorem perpendicular_right {q : QuadraticForm R V} (h : HyperbolicPair q)
    (w : h.perpendicular) : q.polarBilin h.f w = 0 :=
  w.property.2

private theorem polar_symmetric (q : QuadraticForm R V) (x y : V) :
    q.polarBilin x y = q.polarBilin y x := QuadraticMap.polar_comm q x y

private theorem isotropic_self_polar (q : QuadraticForm R V) {e : V} (he : q e = 0) :
    q.polarBilin e e = 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, he, smul_zero]

private def perpendicularComponent (q : QuadraticForm R V) (h : HyperbolicPair q) (z : V) :
    h.perpendicular := by
  let α := q.polarBilin h.f z
  let β := q.polarBilin h.e z
  let z' := z - α • h.e - β • h.f
  refine ⟨z', ?_, ?_⟩
  · change q.polarBilin h.e (z - α • h.e - β • h.f) = 0
    rw [map_sub, map_sub, map_smul, map_smul, isotropic_self_polar q h.q_e,
      h.polar_ef, smul_zero, sub_zero, smul_eq_mul, mul_one]
    exact sub_self _
  · have bfe : q.polarBilin h.f h.e = 1 := (polar_symmetric q _ _).trans h.polar_ef
    change q.polarBilin h.f (z - α • h.e - β • h.f) = 0
    rw [map_sub, map_sub, map_smul, map_smul, isotropic_self_polar q h.q_f,
      bfe, smul_zero, sub_zero, smul_eq_mul, mul_one]
    exact sub_self _

private theorem perpendicular_decomposition (q : QuadraticForm R V)
    (h : HyperbolicPair q) (z : V) :
    z = q.polarBilin h.f z • h.e + q.polarBilin h.e z • h.f +
      (perpendicularComponent q h z).val := by
  dsimp [perpendicularComponent]
  abel

private theorem complementary_products (q : QuadraticForm R V) (h : HyperbolicPair q) :
    ι q h.e * ι q h.f + ι q h.f * ι q h.e = 1 := by
  rw [swap, h.polar_ef, map_one]

private theorem hyperbolic_triple (q : QuadraticForm R V) (h : HyperbolicPair q) :
    ι q h.e * ι q h.f * ι q h.e = ι q h.e := by
  let E := ι q h.e
  let L := ι q h.f
  have e2 : E * E = 0 := by dsimp [E]; rw [ι_sq_scalar, h.q_e, map_zero]
  calc
    _ = E * (E * L + L * E) - (E * E) * L := by
      change E * L * E = _
      noncomm_ring
    _ = E := by rw [complementary_products q h, e2, mul_one, zero_mul, sub_zero]

private def swappedPair {q : QuadraticForm R V} (h : HyperbolicPair q) : HyperbolicPair q :=
  ⟨h.f, h.e, h.q_f, h.q_e, (polar_symmetric q _ _).trans h.polar_ef⟩

theorem planeDiagonalCalculation : PlaneDiagonalCalculation.{u,v} := by
  intro R _ V _ _ q h
  dsimp only
  let E := ι q h.e
  let L := ι q h.f
  let P := E * L
  let Q := L * E
  have e2 : E * E = 0 := by dsimp [E]; rw [ι_sq_scalar, h.q_e, map_zero]
  have l2 : L * L = 0 := by dsimp [L]; rw [ι_sq_scalar, h.q_f, map_zero]
  have pe : P * E = E := hyperbolic_triple q h
  have ql : Q * L = L := hyperbolic_triple q (swappedPair h)
  have eq' : E * Q = E := (mul_assoc E L E).symm.trans pe
  have lp : L * P = L := (mul_assoc L E L).symm.trans ql
  have ep : E * P = 0 := by change E * (E * L) = _; rw [← mul_assoc, e2, zero_mul]
  have lq : L * Q = 0 := by change L * (L * E) = _; rw [← mul_assoc, l2, zero_mul]
  have pl : P * L = 0 := by change (E * L) * L = _; rw [mul_assoc, l2, mul_zero]
  have qe : Q * E = 0 := by change (L * E) * E = _; rw [mul_assoc, e2, mul_zero]
  have pp : P * P = P := by change P * (E * L) = _; rw [← mul_assoc, pe]
  have qq : Q * Q = Q := by change Q * (L * E) = _; rw [← mul_assoc, ql]
  have pq : P * Q = 0 := by change P * (L * E) = _; rw [← mul_assoc, pl, zero_mul]
  have qp : Q * P = 0 := by change Q * (E * L) = _; rw [← mul_assoc, qe, zero_mul]
  have rp : reverse P = Q := by simp [P,Q,E,L,reverse.map_mul,reverse_ι]
  have rq : reverse Q = P := by simp [P,Q,E,L,reverse.map_mul,reverse_ι]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [planeDiagonal, one_smul] using complementary_products q h
  · intro a b c d
    change (a • P + b • Q) * (c • P + d • Q) = (a * c) • P + (b * d) • Q
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      pp, qq, pq, qp, smul_zero, add_zero, zero_add, mul_comm c a, mul_comm d b]
  · intro a b
    change reverse (a • P + b • Q) = b • P + a • Q
    rw [map_add, map_smul, map_smul, rp, rq, add_comm]
  · intro a b
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (vector_even_product q h.e h.f))
      (Submodule.smul_mem _ _ (vector_even_product q h.f h.e))
  · intro a b
    change (a • P + b • Q) * E = a • E ∧ E * (a • P + b • Q) = b • E ∧
      (a • P + b • Q) * L = b • L ∧ L * (a • P + b • Q) = a • L ∧ _
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, pe, qe, ep, eq',
      pl, ql, lp, lq, smul_zero, add_zero, zero_add, true_and]
    intro w
    let Z := ι q w.val
    have ze : Z * E = -(E * Z) := orthogonal_swap q h.e w.val (perpendicular_left h w)
    have zl : Z * L = -(L * Z) := orthogonal_swap q h.f w.val (perpendicular_right h w)
    have comm (x y : CliffordAlgebra q) (hx : Z * x = -(x * Z)) (hy : Z * y = -(y * Z)) :
        Commute (x * y) Z := by
      change (x * y) * Z = Z * (x * y)
      rw [mul_assoc, ← mul_assoc Z, hx, neg_mul, mul_assoc x, hy, mul_neg, neg_neg]
    exact ((comm E L ze zl).smul_left a).add_left ((comm L E zl ze).smul_left b)

theorem planeScalingCalculation : PlaneScalingCalculation.{u,v} := by
  intro R _ V _ _ q h s w
  let a : R := s
  let b : R := ↑s⁻¹
  let D := planeDiagonal q h
  let d := D a b
  let d' := D b a
  let Z := ι q w.val
  obtain ⟨done, dmul, _, _, dvec⟩ := planeDiagonalCalculation q h
  have dd : d * d' = 1 := by
    change D a b * D b a = 1
    rw [dmul, show a * b = 1 from s.val_inv, show b * a = 1 from s.inv_val, done]
  have hz : Commute d' Z := (dvec b a).2.2.2.2 w
  have move (e : V) (t : R)
      (he : d * ι q e = t • ι q e) (he' : ι q e * d' = t • ι q e) :
      d * (1 + ι q e * Z) * d' = 1 + ι q e * ι q (t ^ 2 • w.val) := by
    have hm : d * (ι q e * Z) * d' = (d * ι q e) * d' * Z := by
      rw [← mul_assoc d, mul_assoc (d * ι q e), ← hz.eq, ← mul_assoc]
    have hs : (d * ι q e) * d' = (t ^ 2) • ι q e := by
      rw [he, smul_mul_assoc, he', smul_smul, pow_two]
    rw [mul_add, mul_one, add_mul, dd, hm, hs, map_smul, smul_mul_assoc, mul_smul_comm]
  exact ⟨move h.e a (dvec a b).1 (dvec b a).2.1,
    move h.f b (dvec a b).2.2.1 (dvec b a).2.2.2.1⟩

end Plane

section WeylWord

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]

theorem hyperbolicPairExistence : HyperbolicPairExistence.{u,v} := by
  classical
  intro F _ V _ _ q hq e he hqe
  have hn : e ∉ LinearMap.ker q.polarBilin := by
    rcases hq with h | ⟨r, hr, h⟩
    · rwa [h, Submodule.mem_bot]
    · rw [h]
      intro hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      apply he
      rw [q.map_smul, smul_eq_mul] at hqe
      have ha : a = 0 := by
        rcases mul_eq_zero.mp hqe with ha | hz
        · exact (mul_self_eq_zero.mp ha)
        · exact (hr hz).elim
      rw [ha, zero_smul]
  have hn' : q.polarBilin e ≠ 0 := hn
  obtain ⟨y, hy⟩ : ∃ y, q.polarBilin e y ≠ 0 := by
    by_contra! h
    exact hn' (LinearMap.ext h)
  let z := (q.polarBilin e y)⁻¹ • y
  have hz : q.polarBilin e z = 1 := by
    change q.polarBilin e ((q.polarBilin e y)⁻¹ • y) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]
  have hee : q.polarBilin e e = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hqe, smul_zero]
  let f := z + (-q z) • e
  have hf : q f = 0 := by
    change q (z + (-q z) • e) = _
    rw [QuadraticMap.map_add q z, q.map_smul (-q z) e, hqe, smul_zero, add_zero,
      QuadraticMap.polar_smul_right]
    change q z + (-q z) • q.polarBilin z e = 0
    rw [polar_symmetric q z e, hz, smul_eq_mul, mul_one, add_neg_cancel]
  have hef : q.polarBilin e f = 1 := by
    change q.polarBilin e (z + (-q z) • e) = 1
    rw [map_add, hz, map_smul, hee, smul_zero, add_zero]
  exact ⟨⟨e, f, hqe, hf, hef⟩, rfl⟩

theorem perpendicularRegularity : PerpendicularRegularity.{u,v} := by
  intro F _ V _ _ q h hq
  let Q := q.comp h.perpendicular.subtype
  have polar_restrict (x y : h.perpendicular) : Q.polarBilin x y = q.polarBilin x.val y.val := by
    simp only [Q, QuadraticMap.polarBilin_apply_apply]
    rfl
  have radical_iff (w : h.perpendicular) :
      w ∈ LinearMap.ker Q.polarBilin ↔ w.val ∈ LinearMap.ker q.polarBilin := by
    simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply]
    constructor
    · intro hw z
      conv_lhs => rw [perpendicular_decomposition q h z]
      rw [map_add, map_add, map_smul, map_smul,
        polar_symmetric q w.val h.e, polar_symmetric q w.val h.f,
        perpendicular_left h w, perpendicular_right h w,
        ← polar_restrict w (perpendicularComponent q h z), hw, smul_zero, smul_zero,
        add_zero, add_zero]
    · intro hw z
      rw [polar_restrict, hw]
  change IsRegular Q
  rcases hq with hq | ⟨r, hr, hq⟩
  · left
    ext w
    rw [radical_iff, hq, Submodule.mem_bot, Submodule.mem_bot]
    exact ⟨fun hw => Subtype.ext hw, fun hw => congrArg Subtype.val hw⟩
  · have hrker : r ∈ LinearMap.ker q.polarBilin := hq.symm ▸ Submodule.mem_span_singleton_self r
    have hrmem : r ∈ h.perpendicular := by
      have hrker' : q.polarBilin r = 0 := hrker
      constructor
      · change q.polarBilin h.e r = 0
        rw [polar_symmetric q h.e r, hrker', LinearMap.zero_apply]
      · change q.polarBilin h.f r = 0
        rw [polar_symmetric q h.f r, hrker', LinearMap.zero_apply]
    let r' : h.perpendicular := ⟨r, hrmem⟩
    refine Or.inr ⟨r', hr, ?_⟩
    ext w
    rw [radical_iff, hq, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, Subtype.ext ha⟩,
      fun ⟨a, ha⟩ => ⟨a, congrArg Subtype.val ha⟩⟩

private theorem normalized_shear_product (q : QuadraticForm F V) (x y w : V)
    (hy : q.polarBilin y w = 0) (hw : q w ≠ 0) :
    (q w)⁻¹ • (ι q x * ι q w * (ι q y * ι q w)) = -(ι q x * ι q y) := by
  calc
    _ = (q w)⁻¹ • (ι q x * (ι q w * ι q y) * ι q w) := by
      congr 1
      noncomm_ring
    _ = (q w)⁻¹ • (-(ι q x * ι q y) * (ι q w * ι q w)) := by
      rw [orthogonal_swap q y w hy]
      congr 1
      noncomm_ring
    _ = _ := by
      rw [ι_sq_scalar, ← Algebra.commutes (q w), ← Algebra.smul_def,
        smul_smul, inv_mul_cancel₀ hw, one_smul]

theorem weylWordCalculation : WeylWordCalculation.{u,v} := by
  intro F _ V _ _ q h w hw
  dsimp only
  let E := ι q h.e
  let L := ι q h.f
  let Z := ι q w.val
  let A := E * Z
  let B := (q w.val)⁻¹ • (L * Z)
  have aa : A * A = 0 :=
    shear_nilpotent q h.e w.val h.q_e (perpendicular_left h w)
  have ab : A * B = -(E * L) := by
    change (E * Z) * ((q w.val)⁻¹ • (L * Z)) = _
    rw [mul_smul_comm]
    exact normalized_shear_product q h.e h.f w.val (perpendicular_right h w) hw
  have ba : B * A = -(L * E) := by
    change ((q w.val)⁻¹ • (L * Z)) * (E * Z) = _
    rw [smul_mul_assoc]
    exact normalized_shear_product q h.f h.e w.val (perpendicular_left h w) hw
  have aba : (A * B) * A = -A := by
    rw [ab]
    change -(E * L) * (E * Z) = -(E * Z)
    rw [← mul_assoc, neg_mul, hyperbolic_triple q h, neg_mul]
  have abba : A * B + B * A = -1 := by
    rw [ab, ba, ← neg_add, complementary_products q h]
  have hB : ι q h.f * ι q ((q w.val)⁻¹ • w.val) = B := by
    simp only [map_smul, mul_smul_comm, B, L, Z]
  rw [hB]
  change (1 + A) * (1 + B) * (1 + A) = _
  calc
    _ = 1 + (A * B + B * A) + A + A + B + A * A + (A * B) * A := by noncomm_ring
    _ = A + B := by rw [abba, aa, aba]; abel
    _ = _ := by simp only [A, B, E, L, Z, add_mul, map_smul, smul_mul_assoc]

private theorem reflection_mul_vector (q : QuadraticForm F V) (w x : V) (hw : q w ≠ 0) :
    ι q (reflection q w x) * ι q w = -(ι q w * ι q x) := by
  calc
    _ = ι q x * ι q w - (q.polarBilin w x / q w) • (ι q w * ι q w) := by
      rw [reflection, map_sub, map_smul, sub_mul, smul_mul_assoc]
    _ = ι q x * ι q w - algebraMap F _ (q.polarBilin w x) := by
      rw [ι_sq_scalar, Algebra.smul_def, ← map_mul (algebraMap F (CliffordAlgebra q)), div_mul_cancel₀ _ hw]
    _ = _ := by rw [← swap q w x]; abel

private theorem product_reflections (q : QuadraticForm F V) (a w x : V)
    (ha : q a ≠ 0) (hw : q w ≠ 0) :
    (ι q a * ι q w) * ι q x =
      ι q (reflection q a (reflection q w x)) * (ι q a * ι q w) := by
  rw [mul_assoc, ← neg_eq_iff_eq_neg.mpr (reflection_mul_vector q w x hw), mul_neg, ← mul_assoc,
    ← neg_eq_iff_eq_neg.mpr (reflection_mul_vector q a (reflection q w x) ha), neg_mul,
    neg_neg, mul_assoc]

theorem weylActionCalculation : WeylActionCalculation.{u,v} := by
  intro F _ V _ _ q h w hw
  dsimp only
  let d := q w.val
  let a := h.e + d⁻¹ • h.f
  let n := ι q a * ι q w.val
  have hfe : q.polarBilin h.f h.e = 1 := (polar_symmetric q _ _).trans h.polar_ef
  have bee : q.polarBilin h.e h.e = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, h.q_e, smul_zero]
  have bff : q.polarBilin h.f h.f = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, h.q_f, smul_zero]
  have qa : q a = d⁻¹ := by
    change q (h.e + d⁻¹ • h.f) = _
    rw [QuadraticMap.map_add q h.e (d⁻¹ • h.f), q.map_smul, h.q_e, h.q_f, smul_zero,
      zero_add, zero_add, QuadraticMap.polar_smul_right]
    change d⁻¹ • q.polarBilin h.e h.f = d⁻¹
    rw [h.polar_ef, smul_eq_mul, mul_one]
  have ae : q.polarBilin a h.e = d⁻¹ := by
    change q.polarBilin (h.e + d⁻¹ • h.f) h.e = _
    simp [bee, hfe]
  have af : q.polarBilin a h.f = 1 := by
    change q.polarBilin (h.e + d⁻¹ • h.f) h.f = _
    simp [bff, h.polar_ef]
  have rae : reflection q a h.e = -d⁻¹ • h.f := by
    rw [reflection, ae, qa, div_self (inv_ne_zero hw), one_smul]
    change h.e - (h.e + d⁻¹ • h.f) = _
    rw [neg_smul]
    abel
  have raf : reflection q a h.f = -d • h.e := by
    rw [reflection, af, qa, one_div, inv_inv]
    change h.f - d • (h.e + d⁻¹ • h.f) = _
    rw [smul_add, smul_smul, mul_inv_cancel₀ hw, one_smul, neg_smul]
    abel
  have rwe : reflection q w.val h.e = h.e := by
    rw [reflection, polar_symmetric q w.val h.e, perpendicular_left h w, zero_div,
      zero_smul, sub_zero]
  have rwf : reflection q w.val h.f = h.f := by
    rw [reflection, polar_symmetric q w.val h.f, perpendicular_right h w, zero_div,
      zero_smul, sub_zero]
  have raw (x : h.perpendicular) : q.polarBilin a x.val = 0 := by
    change q.polarBilin (h.e + d⁻¹ • h.f) x.val = _
    simp [perpendicular_left h x, perpendicular_right h x]
  have rwperp (x : h.perpendicular) :
      reflection q w.val x.val ∈ h.perpendicular := by
    rw [reflection]
    exact Submodule.sub_mem _ x.property (Submodule.smul_mem _ _ w.property)
  have plane (x : h.perpendicular) :
      reflection q a (reflection q w.val x.val) = reflection q w.val x.val := by
    have hh := raw ⟨_, rwperp x⟩
    change q.polarBilin a (reflection q w.val x.val) = 0 at hh
    let y := reflection q w.val x.val
    change y - (q.polarBilin a y / q a) • a = y
    rw [hh, zero_div, zero_smul, sub_zero]
  have act (x : V) := product_reflections q a w.val x (qa ▸ inv_ne_zero hw) hw
  change n * ι q h.e = _ ∧ n * ι q h.f = _ ∧ _
  refine ⟨?_, ?_, fun x => ?_⟩
  · simpa only [rwe, rae] using act h.e
  · simpa only [rwf, raf] using act h.f
  · simpa only [plane x] using act x.val

theorem weylScaleCalculation : WeylScaleCalculation.{u,v} := by
  intro F _ V _ _ q h w hw
  have hdiag := (planeDiagonalCalculation q h).2.2.2.2
  refine ⟨?_, ?_⟩
  · intro s hs
    have hs' : ((s * s) * q w.val)⁻¹ * s = s⁻¹ * (q w.val)⁻¹ := by
      rw [mul_inv, mul_inv]
      calc
        _ = (s⁻¹ * s) * (s⁻¹ * (q w.val)⁻¹) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hs, one_mul]
    calc
      weylElement q h (s • w.val) =
          (s • ι q h.e + (s⁻¹ * (q w.val)⁻¹) • ι q h.f) * ι q w.val := by
        rw [weylElement, q.map_smul, smul_eq_mul, map_add, map_smul, map_smul, mul_smul_comm,
          ← smul_mul_assoc, smul_add, smul_smul]
        rw [mul_comm s _, hs']
      _ = planeDiagonal q h s s⁻¹ * weylElement q h w.val := by
        rw [weylElement, map_add, map_smul, ← mul_assoc, mul_add, mul_smul_comm,
          (hdiag s s⁻¹).1, (hdiag s s⁻¹).2.2.1, smul_smul, mul_comm]
  · have hq : q (-w.val) = q w.val := by
      rw [← neg_one_smul F w.val, q.map_smul, neg_mul_neg, one_mul, one_smul]
    rw [weylElement, hq, map_neg, mul_neg]
    rfl

end WeylWord

section ScaleLift

open LinearAlgebraicGroups.Albert
open SpinSpecification
open scoped TensorProduct

open private scalar_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
variable {I : Type j} [LinearOrder I] [Fintype I]

open private contract_polar contract_coord polar_range orderedBasis orderedBasis_empty
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

theorem gradedCentralizerCalculation : GradedCentralizerCalculation.{u,v,j} := by
  classical
  intro F _ V _ _ I _ _ q b hb a ha
  let B := orderedBasis q b
  have hcoord (i : I) : ∃ v, q.polarBilin v = b.coord i := by
    change b.coord i ∈ LinearMap.range q.polarBilin
    rw [polar_range q b, hb, Submodule.dualAnnihilator_bot]
    trivial
  have hzero (s : Finset I) (hs : s ≠ ∅) : B.coord s a = 0 := by
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨v, hv⟩ := hcoord i
    apply contract_coord q b a i _ s hi
    rw [← hv, contract_polar, ha, sub_self]
  refine ⟨B.coord ∅ a, ?_⟩
  conv_lhs => rw [← B.sum_repr a]
  rw [Finset.sum_eq_single ∅]
  · rw [← Module.Basis.coord_apply]
    change (B.coord ∅ a) • orderedBasis q b ∅ = _
    rw [orderedBasis_empty, Algebra.smul_def, mul_one]
  · intro s _ hs
    rw [← Module.Basis.coord_apply, hzero s hs, zero_smul]
  · simp

private theorem regularIntrinsicCentralizer
    (q : QuadraticForm F V) (b : Module.Basis I F V) (hq : IsRegular q)
    (a : CliffordAlgebra q) (ha : a ∈ evenOdd q 0) (hc : ∀ x, Commute a (ι q x)) :
    ∃ t : F, a = algebraMap F _ t := by
  let φ := Algebra.TensorProduct.lid F (CliffordAlgebra q)
  have he : φ.symm a ∈ evenPart q F := Submodule.tmul_mem_baseChange_of_mem 1 ha
  have hv (x : F ⊗[F] V) : φ (vectors q F x) = ι q (TensorProduct.lid F V x) := by
    induction x with
    | tmul c x =>
      simp only [vectors, LinearMap.baseChange_tmul, φ, Algebra.TensorProduct.lid_tmul,
        TensorProduct.lid_tmul, map_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hc' (x : F ⊗[F] V) : Commute (φ.symm a) (vectors q F x) := by
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply, hv]
    exact hc _
  obtain ⟨t, ht⟩ := SpinFunctor.regular_scalarCentralizer q F b hq he hc'
  exact ⟨t, by simpa only [φ.apply_symm_apply, AlgEquiv.commutes] using congrArg φ ht⟩

theorem scaleLiftCalculation : ScaleLiftCalculation.{u,v,j} := by
  intro F _ V _ _ I _ _ q b h hq t g hg hn hge hgf hgw
  let E := ι q h.e
  let L := ι q h.f
  let D := planeDiagonal q h
  let a : F := t
  let a' : F := ↑t⁻¹
  let x := D a 1
  let y := D a' 1
  have aa' : a * a' = 1 := t.val_inv
  obtain ⟨done, dmul, drev, deven, dvec⟩ := planeDiagonalCalculation q h
  change D 1 1 = 1 at done
  change ∀ a b c d, D a b * D c d = D (a * c) (b * d) at dmul
  change ∀ a b, reverse (D a b) = D b a at drev
  change ∀ a b, D a b ∈ evenOdd q 0 at deven
  change ∀ a b, D a b * E = a • E ∧ E * D a b = b • E ∧
    D a b * L = b • L ∧ L * D a b = a • L ∧
    ∀ w : h.perpendicular, Commute (D a b) (ι q w.val) at dvec
  change g * E = a • (E * g) at hge
  change g * L = a' • (L * g) at hgf
  have xy : x * y = 1 := by
    change D a 1 * D a' 1 = 1
    rw [dmul, aa', one_mul, done]
  obtain ⟨ye, ey, yf, fy, yw⟩ := dvec a' 1
  change y * E = a' • E at ye
  change E * y = (1 : F) • E at ey
  change y * L = (1 : F) • L at yf
  change L * y = a' • L at fy
  have ce : Commute (y * g) E := by
    change (y * g) * E = E * (y * g)
    rw [mul_assoc y, hge, mul_smul_comm, ← mul_assoc y, ye, smul_mul_assoc,
      smul_smul, aa', one_smul, ← mul_assoc E, ey, one_smul]
  have cf : Commute (y * g) L := by
    change (y * g) * L = L * (y * g)
    rw [mul_assoc y, hgf, mul_smul_comm, ← mul_assoc y, yf, one_smul,
      ← mul_assoc L, fy, smul_mul_assoc]
  have hB (z : V) : Commute (y * g) (ι q z) := by
    let α := q.polarBilin h.f z
    let β := q.polarBilin h.e z
    let w := perpendicularComponent q h z
    have hz : z = α • h.e + β • h.f + w.val := perpendicular_decomposition q h z
    have cw : Commute (y * g) (ι q w.val) := (yw w).mul_left (hgw w)
    have hv := congrArg (ι q) hz
    simp only [map_add, map_smul] at hv
    change ι q z = α • E + β • L + ι q w.val at hv
    rw [hv]
    exact ((ce.smul_right α).add_right (cf.smul_right β)).add_right cw
  have hgy : y * g ∈ evenOdd q 0 := by
    simpa only [add_zero] using SetLike.mul_mem_graded (deven a' 1) hg
  obtain ⟨r, hr⟩ := regularIntrinsicCentralizer q b hq (y * g) hgy hB
  have hd : g = D (r * a) r := by
    calc
      g = x * (y * g) := by rw [← mul_assoc, xy, one_mul]
      _ = r • x := by rw [hr, Algebra.smul_def, Algebra.commutes]
      _ = _ := by
        change r • (a • (E * L) + (1 : F) • (L * E)) = _
        rw [smul_add, smul_smul, smul_smul, mul_one]
        rfl
  have hna : r * r * a = 1 := by
    rw [hd, drev, dmul, mul_comm (r * a) r, ← mul_assoc] at hn
    change (r * r * a) • (E * L) + (r * r * a) • (L * E) = 1 at hn
    rw [← smul_add, complementary_products q h, Algebra.smul_def, mul_one,
      ← (algebraMap F (CliffordAlgebra q)).map_one] at hn
    exact scalar_injective q b hn
  have hr0 : r ≠ 0 := by intro hr0; simp [hr0] at hna
  have hra : r * a = r⁻¹ := by
    apply mul_left_cancel₀ hr0
    rw [← mul_assoc, hna, mul_inv_cancel₀ hr0]
  let s : Fˣ := (Units.mk0 r hr0)⁻¹
  refine ⟨s, ?_, ?_⟩
  · change g = D r⁻¹ r
    rw [hd, hra]
  · change a = r⁻¹ ^ 2
    apply mul_left_cancel₀ (mul_ne_zero hr0 hr0 : r * r ≠ 0)
    rw [hna, ← pow_two, ← mul_pow, mul_inv_cancel₀ hr0, one_pow]

end ScaleLift

section ReflectionParity

open private scalar_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
variable {q : QuadraticForm F V} (h : HyperbolicPair q)

private def reflectWord (l : List h.perpendicular) (x : V) : V :=
  l.foldr (fun w z => reflection q w.val z) x

private def cliffordWord (l : List h.perpendicular) : CliffordAlgebra q :=
  (l.map fun w => ι q w.val).prod

private theorem vector_isUnit {w : V} (hw : q w ≠ 0) : IsUnit (ι q w) := by
  let r := algebraMap F (CliffordAlgebra q) (q w)⁻¹
  have hmul : ι q w * (r * ι q w) = 1 := by
    rw [← mul_assoc, ← (Algebra.commutes (R := F) (q w)⁻¹ (ι q w)), mul_assoc,
      ι_sq_scalar, ← map_mul, inv_mul_cancel₀ hw, map_one]
  have hinv : (r * ι q w) * ι q w = 1 := by
    rw [mul_assoc, ι_sq_scalar, ← map_mul, inv_mul_cancel₀ hw, map_one]
  exact ⟨⟨ι q w, r * ι q w, hmul, hinv⟩, rfl⟩

private theorem cliffordWord_isUnit (l : List h.perpendicular)
    (hl : ∀ w ∈ l, q w.val ≠ 0) : IsUnit (cliffordWord h l) := by
  induction l with
  | nil => exact isUnit_one
  | cons w l ih =>
    exact (vector_isUnit (hl w (List.mem_cons_self ..))).mul
      (ih fun z hz => hl z (List.mem_cons_of_mem _ hz))

private theorem cliffordWord_grade (l : List h.perpendicular) :
    cliffordWord h l ∈ evenOdd q (l.length : ZMod 2) := by
  induction l with
  | nil => exact SetLike.one_mem_graded (evenOdd q)
  | cons w l ih =>
    change ι q w.val * cliffordWord h l ∈ evenOdd q ((l.length + 1 : ℕ) : ZMod 2)
    rw [Nat.cast_add, Nat.cast_one, add_comm]
    exact SetLike.mul_mem_graded (ι_mem_evenOdd_one q w.val) ih

private theorem cliffordWord_action (l : List h.perpendicular)
    (hl : ∀ w ∈ l, q w.val ≠ 0) (x : V) :
    cliffordWord h l * ι q x = ι q (reflectWord h l x) * involute (cliffordWord h l) := by
  induction l with
  | nil => simp [cliffordWord, reflectWord]
  | cons w l ih =>
    have hw := hl w (List.mem_cons_self ..)
    change (ι q w.val * cliffordWord h l) * ι q x =
      ι q (reflection q w.val (reflectWord h l x)) * involute (ι q w.val * cliffordWord h l)
    rw [mul_assoc, ih (fun z hz => hl z (List.mem_cons_of_mem _ hz)), ← mul_assoc,
      map_mul, involute_ι, ← mul_assoc, mul_neg, reflection_mul_vector q _ _ hw, neg_neg]

private theorem reflectWord_fixes_pair (l : List h.perpendicular) :
    reflectWord h l h.e = h.e ∧ reflectWord h l h.f = h.f := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons w l ih =>
    constructor
    · change reflection q w.val (reflectWord h l h.e) = h.e
      simp [ih.1, reflection, polar_symmetric q w.val h.e, perpendicular_left h w]
    · change reflection q w.val (reflectWord h l h.f) = h.f
      simp [ih.2, reflection, polar_symmetric q w.val h.f, perpendicular_right h w]

/-- Intertwining equations can be tested on the pair and its perpendicular. -/
private theorem intertwines_of_pair (A : V ≃ₗ[F] V) (a d : CliffordAlgebra q)
    (he : a * ι q h.e = ι q (A h.e) * d) (hf : a * ι q h.f = ι q (A h.f) * d)
    (hw : ∀ w : h.perpendicular, a * ι q w.val = ι q (A w.val) * d)
    (x : V) : a * ι q x = ι q (A x) * d := by
  rw [perpendicular_decomposition q h x]
  simp only [map_add, map_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, he, hf, hw]

private theorem nonsingular_word_even
    {I : Type j} [LinearOrder I] [Fintype I] (b : Module.Basis I F V)
    (hq : LinearMap.ker q.polarBilin = ⊥)
    (a : (CliffordAlgebra q)ˣ) (ha : a.val ∈ evenOdd q 0)
    (A : V ≃ₗ[F] V) (haA : ∀ x, a.val * ι q x = ι q (A x) * a.val)
    (t : Fˣ) (he : A h.e = (t : F) • h.e) (hf : A h.f = (↑t⁻¹ : F) • h.f)
    (l : List h.perpendicular) (hl : ∀ w ∈ l, q w.val ≠ 0)
    (hA : ∀ w : h.perpendicular, A w.val = reflectWord h l w.val)
    (hAw : ∀ w : h.perpendicular, A w.val ∈ h.perpendicular) :
    l.length % 2 = 0 := by
  let U := cliffordWord h l
  let X := planeDiagonal q h (t : F) 1
  let c := a⁻¹.val * (X * U)
  obtain ⟨hone, hmul, _, hgrade, hvec⟩ := planeDiagonalCalculation q h
  obtain ⟨Xe, eX, Xf, fX, Xw⟩ := hvec (t : F) 1
  have hX : involute X = X := involute_eq_of_mem_even (hgrade _ _)
  have hXi : IsUnit X := by
    let Y := planeDiagonal q h (↑t⁻¹ : F) 1
    have hxy : X * Y = 1 := by
      calc
        _ = planeDiagonal q h ((t : F) * ↑t⁻¹) (1 * 1) := hmul _ _ _ _
        _ = 1 := by rw [Units.mul_inv, one_mul]; exact hone
    have hyx : Y * X = 1 := by
      calc
        _ = planeDiagonal q h ((↑t⁻¹ : F) * t) (1 * 1) := hmul _ _ _ _
        _ = 1 := by rw [Units.inv_mul, one_mul]; exact hone
    exact ⟨⟨X, Y, hxy, hyx⟩, rfl⟩
  have hae : involute a.val = a.val := involute_eq_of_mem_even ha
  have hai : involute a⁻¹.val = a⁻¹.val := by
    have H : Units.map (involute (Q := q)).toMonoidHom a = a := Units.ext hae
    exact congrArg Units.val ((map_inv (Units.map (involute (Q := q)).toMonoidHom) a).trans
      (congrArg Inv.inv H))
  have hXU (x : V) : (X * U) * ι q x = ι q (A x) * involute (X * U) := by
    have hword := cliffordWord_action h l hl
    have hpair := reflectWord_fixes_pair h l
    apply intertwines_of_pair h A
    · have h₁ : X * ι q h.e = (t : F) • ι q h.e := Xe
      have h₂ : ι q h.e * X = ι q h.e := (eX.trans (one_smul _ _))
      rw [mul_assoc, hword, hpair.1, ← mul_assoc, h₁,
        map_mul, hX, he, map_smul]
      simp only [smul_mul_assoc, ← mul_assoc (ι q h.e) X, h₂, U]
    · have h₁ : X * ι q h.f = ι q h.f := Xf.trans (one_smul _ _)
      have h₂ : ι q h.f * X = (t : F) • ι q h.f := fX
      rw [mul_assoc, hword, hpair.2, ← mul_assoc, h₁, map_mul, hX, hf, map_smul]
      simp only [smul_mul_assoc, ← mul_assoc (ι q h.f) X, h₂, smul_smul,
        Units.inv_mul, one_smul, U]
    · intro w
      have H : Commute X (ι q (A w.val)) := Xw ⟨A w.val, hAw w⟩
      rw [mul_assoc, hword, ← hA, ← mul_assoc, H.eq, mul_assoc, map_mul, hX]
  have hc (x : V) : ι q x * c = involute c * ι q x := by
    have hax : ι q x * a⁻¹.val = a⁻¹.val * ι q (A x) := by
      calc
        _ = a⁻¹.val * (a.val * ι q x) * a⁻¹.val := by
          rw [← mul_assoc a⁻¹.val, Units.inv_mul, one_mul]
        _ = _ := by rw [haA, mul_assoc a⁻¹.val, mul_assoc (ι q (A x)), Units.mul_inv, mul_one]
    change ι q x * (a⁻¹.val * (X * U)) = involute (a⁻¹.val * (X * U)) * ι q x
    have H : involute (X * U) * ι q x = ι q (A x) * (X * U) := by
      simpa only [map_mul, involute_ι, involute_involute, mul_neg, neg_mul, neg_inj]
        using congrArg (involute (Q := q)) (hXU x)
    calc
      _ = a⁻¹.val * (ι q (A x) * (X * U)) := by rw [← mul_assoc (ι q x), hax, mul_assoc]
      _ = involute (a⁻¹.val * (X * U)) * ι q x := by
        have hm : involute (a⁻¹.val * (X * U)) =
            involute a⁻¹.val * involute (X * U) := map_mul involute _ _
        rw [← H, hm, hai, mul_assoc]
  obtain ⟨r, hr⟩ := gradedCentralizerCalculation q b hq c hc
  have heq : X * U = a.val * algebraMap F _ r := by
    rw [← hr]
    change _ = a.val * (a⁻¹.val * (X * U))
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have h₀ : X * U ∈ evenOdd q 0 := by
    rw [heq, ← Algebra.commutes, ← Algebra.smul_def r]
    exact Submodule.smul_mem _ _ ha
  have h₁ : X * U ∈ evenOdd q (l.length : ZMod 2) := by
    simpa only [zero_add] using SetLike.mul_mem_graded (hgrade (t : F) 1) (cliffordWord_grade h l)
  let : Nontrivial (CliffordAlgebra q) :=
    Function.Injective.nontrivial (scalar_injective q b)
  have hne : X * U ≠ 0 := (hXi.mul (cliffordWord_isUnit h l hl)).ne_zero
  have hpar : (l.length : ZMod 2) = 0 :=
    DirectSum.degree_eq_of_mem_mem (evenOdd q) h₁ h₀ hne
  exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hpar)

private theorem even_perpendicular_word
    [Infinite F] {I : Type j} [LinearOrder I] [Fintype I] (b : Module.Basis I F V)
    (hq : IsRegular q) (a : (CliffordAlgebra q)ˣ) (ha : a.val ∈ evenOdd q 0)
    (A : V ≃ₗ[F] V) (haA : ∀ x, a.val * ι q x = ι q (A x) * a.val)
    (hqA : ∀ x, q (A x) = q x)
    (t : Fˣ) (he : A h.e = (t : F) • h.e) (hf : A h.f = (↑t⁻¹ : F) • h.f) :
    ∃ l : List h.perpendicular, l.length % 2 = 0 ∧
      (∀ w ∈ l, q w.val ≠ 0) ∧ ∀ w : h.perpendicular, A w.val = reflectWord h l w.val := by
  let W := h.perpendicular
  have hB (x y : V) : q.polarBilin (A x) (A y) = q.polarBilin x y := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hqA]
  have hmem (x : V) : A x ∈ W ↔ x ∈ W := by
    have ht := t.ne_zero
    have hti := (t⁻¹).ne_zero
    have h₁ := hB h.e x
    have h₂ := hB h.f x
    rw [he, map_smul, LinearMap.smul_apply, smul_eq_mul] at h₁
    rw [hf, map_smul, LinearMap.smul_apply, smul_eq_mul] at h₂
    change (_ = 0 ∧ _ = 0) ↔ (_ = 0 ∧ _ = 0)
    rw [← h₁, ← h₂, mul_eq_zero, mul_eq_zero, or_iff_right ht, or_iff_right hti]
  have hmap : W.map A.toLinearMap = W := by
    ext x
    change (∃ y ∈ W, A y = x) ↔ x ∈ W
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).mpr hy
    · intro hx
      exact ⟨A.symm x, (hmem _).mp (by simpa only [A.apply_symm_apply] using hx),
        A.apply_symm_apply x⟩
  let A' := A.ofSubmodules W W hmap
  let Q := q.comp W.subtype
  let := Module.Finite.of_basis b
  have hQ := perpendicularRegularity q h hq
  obtain ⟨l, hl, hA⟩ := SpinOrthogonalWords.orthogonalWords Q hQ A' (fun w => hqA w.val)
  have hfold (m : List W) (w : W) :
      (m.foldr (fun z x => x - (Q.polarBilin z x / Q z) • z) w).val =
        reflectWord h m w.val := by
    induction m with
    | nil => rfl
    | cons z m ih =>
      change reflection q z.val
        ((m.foldr (fun z x => x - (Q.polarBilin z x / Q z) • z) w).val) =
          reflection q z.val (reflectWord h m w.val)
      rw [ih]
  have hact (w : W) : A w.val = reflectWord h l w.val :=
    (congrArg Subtype.val (hA w)).trans (hfold l w)
  by_cases hn : l.length % 2 = 0
  · exact ⟨l, hn, hl, hact⟩
  rcases hq with hnq | ⟨r, hr, hrad⟩
  · exact False.elim (hn (nonsingular_word_even h b hnq a ha A haA t he hf l hl hact (fun w => (hmem _).mpr w.property)))
  · have hzero : q.polarBilin r = 0 := by
      have H : r ∈ LinearMap.ker q.polarBilin := hrad.symm ▸ Submodule.mem_span_singleton_self r
      exact H
    have hrW : r ∈ W := by
      constructor
      · change q.polarBilin h.e r = 0
        rw [polar_symmetric q h.e r, hzero, LinearMap.zero_apply]
      · change q.polarBilin h.f r = 0
        rw [polar_symmetric q h.f r, hzero, LinearMap.zero_apply]
    let z : W := ⟨r, hrW⟩
    refine ⟨z :: l, by simp only [List.length_cons]; omega, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hr
      · exact hl w hw
    · intro w
      change A w.val = reflection q r (reflectWord h l w.val)
      rw [reflection, hzero, LinearMap.zero_apply, zero_div, zero_smul, sub_zero, hact]

end ReflectionParity

section RationalPoints

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Albert
open SpinSpecification (ScalarClifford vectors reversion IsSpinPointRepresentation)
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open CocharacterDynamics

open private polar_over
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SpinHyperbolicDynamics
open private scalar_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private reductive_of_semisimple
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private testPointSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
variable {q : QuadraticForm F V} {G : AffineAlgebraicGroup F}
variable {I : Type u} [LinearOrder I] (b : Module.Basis I F V)
variable (h : HyperbolicPair q)
variable (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ)

private abbrev fieldAlgebra (F : Type u) [Field F] := CommAlgCat.of F F

private abbrev FieldPoints (G : Specs.GroupScheme F) := GroupPoints G (fieldAlgebra F)

private def dynamicsPair : Specs.Arithmetic.SpinHyperbolicDynamics.HyperbolicPair q :=
  ⟨h.e, h.f, h.q_e, h.q_f, h.polar_ef⟩

private def intrinsicPoint : FieldPoints G.val →* (CliffordAlgebra q)ˣ :=
  (Units.map (Algebra.TensorProduct.lid F (CliffordAlgebra q)).toMonoidHom).comp
    (ρ (fieldAlgebra F))

private theorem intrinsicPoint_injective (hr : IsSpinPointRepresentation q G.val ρ) :
    Function.Injective (intrinsicPoint ρ) := by
  intro x y hxy
  apply (hr.1 (fieldAlgebra F)).1
  apply Units.ext
  exact (Algebra.TensorProduct.lid F _).injective (congrArg Units.val hxy)

private theorem fieldVector (x : V) :
    Algebra.TensorProduct.lid F (CliffordAlgebra q) (vectors q F (1 ⊗ₜ[F] x)) = CliffordAlgebra.ι q x := by
  simp [vectors, LinearMap.baseChange_tmul]

private theorem fieldReversion (x : ScalarClifford q F) :
    Algebra.TensorProduct.lid F (CliffordAlgebra q) (reversion q F x) =
      reverse (Algebra.TensorProduct.lid F (CliffordAlgebra q) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => simp only [reversion, LinearMap.baseChange_tmul, Algebra.TensorProduct.lid_tmul,
      map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem intrinsicPoint_even_norm (hr : IsSpinPointRepresentation q G.val ρ)
    (p : FieldPoints G.val) :
    (intrinsicPoint ρ p).val ∈ evenOdd q 0 ∧
      reverse (intrinsicPoint ρ p).val * (intrinsicPoint ρ p).val = 1 := by
  have hp : ρ (fieldAlgebra F) p ∈ SpinSpecification.spinUnits q (fieldAlgebra F) :=
    (hr.1 (fieldAlgebra F)).2 ▸ Set.mem_range_self p
  let φ := Algebra.TensorProduct.lid F (CliffordAlgebra q)
  change φ (ρ _ p).val ∈ evenOdd q 0 ∧
    reverse (φ (ρ _ p).val) * φ (ρ _ p).val = 1
  refine ⟨?_, ?_⟩
  · have hφ : (SpinSpecification.evenPart q F) ≤ (evenOdd q 0).comap φ.toLinearMap := by
      change (evenOdd q 0).baseChange F ≤ _
      rw [Submodule.baseChange_eq_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, rfl⟩
      change x ∈ evenOdd q 0 at hx
      change φ (1 ⊗ₜ[F] x) ∈ evenOdd q 0
      simpa only [φ, Algebra.TensorProduct.lid_tmul, one_smul] using hx
    exact hφ hp.1
  · rw [← fieldReversion, ← map_mul, hp.2.1, map_one]

include b in
private theorem field_perpendicular (w : h.perpendicular) :
    (1 ⊗ₜ[F] w.val) ∈ Specs.Arithmetic.SpinHyperbolicDynamics.perpendicularOver
      q (dynamicsPair h) b (fieldAlgebra F) := by
  constructor
  · change (SpinSpecification.ExtendedForm q (fieldAlgebra F) b).polarBilin
      (1 ⊗ₜ[F] h.e) (1 ⊗ₜ[F] w.val) = 0
    rw [polar_over, perpendicular_left h w, map_zero]
  · change (SpinSpecification.ExtendedForm q (fieldAlgebra F) b).polarBilin
      (1 ⊗ₜ[F] h.f) (1 ⊗ₜ[F] w.val) = 0
    rw [polar_over, perpendicular_right h w, map_zero]

include b in
private theorem centralizer_intrinsic_action [Infinite F] [Fintype I]
    (hr : IsSpinPointRepresentation q G.val ρ) (c : Cocharacter G.val)
    (hc : HasSpinCocharacterFormula h ρ c) (p : FieldPoints G.val) (hp : Centralizes c p) :
    ∃ (A : V ≃ₗ[F] V) (t : Fˣ), (∀ x, q (A x) = q x) ∧
      (∀ x, (intrinsicPoint ρ p).val * CliffordAlgebra.ι q x = CliffordAlgebra.ι q (A x) * (intrinsicPoint ρ p).val) ∧
      A h.e = (t : F) • h.e ∧ A h.f = (↑t⁻¹ : F) • h.f := by
  obtain ⟨B, t, hB, he, hf, _⟩ :=
    SpinHyperbolicDynamics.centralizerAction q b (dynamicsPair h) ρ c hr hc p hp
  let L := TensorProduct.lid F V
  let A := (L.symm.trans B).trans L
  let a := intrinsicPoint ρ p
  have hA (x : V) : a.val * CliffordAlgebra.ι q x = CliffordAlgebra.ι q (A x) * a.val := by
    have hx := hB (L.symm x)
    have hL : L.symm (A x) = B (L.symm x) := L.symm_apply_apply _
    rw [← hL, TensorProduct.lid_symm_apply, TensorProduct.lid_symm_apply] at hx
    have H := congrArg (Algebra.TensorProduct.lid F (CliffordAlgebra q)) hx
    simp only [SpinSpecification.conjugate, map_mul, fieldVector] at H
    change CliffordAlgebra.ι q (A x) = a.val * CliffordAlgebra.ι q x * a⁻¹.val at H
    rw [H, mul_assoc (a.val * _), Units.inv_mul, mul_one]
  have hqA (x : V) : q (A x) = q x := by
    apply scalar_injective q b
    have H : CliffordAlgebra.ι q (A x) * CliffordAlgebra.ι q (A x) * a.val = a.val * (CliffordAlgebra.ι q x * CliffordAlgebra.ι q x) := by
      rw [mul_assoc, ← hA, ← mul_assoc, ← hA, mul_assoc]
    rw [ι_sq_scalar, ι_sq_scalar, ← Algebra.commutes] at H
    have HH := congrArg (· * a⁻¹.val) H
    simpa only [mul_assoc, Units.mul_inv, mul_one] using HH
  refine ⟨A, t, hqA, hA, ?_, ?_⟩
  · change B (1 ⊗ₜ[F] h.e) = (t : F) • (1 ⊗ₜ[F] h.e) at he
    change L (B (L.symm h.e)) = _
    rw [TensorProduct.lid_symm_apply, he, map_smul, TensorProduct.lid_tmul, one_smul]
  · change B (1 ⊗ₜ[F] h.f) = (↑t⁻¹ : F) • (1 ⊗ₜ[F] h.f) at hf
    change L (B (L.symm h.f)) = _
    rw [TensorProduct.lid_symm_apply, hf, map_smul, TensorProduct.lid_tmul, one_smul]

include b in
private theorem centralizer_even_word [Infinite F] [Fintype I]
    (hr : IsSpinPointRepresentation q G.val ρ) (hq : IsRegular q) (c : Cocharacter G.val)
    (hc : HasSpinCocharacterFormula h ρ c) : HasEvenPerpendicularAction h ρ c := by
  intro p hp
  obtain ⟨A, t, hqA, haA, he, hf⟩ := centralizer_intrinsic_action b h ρ hr c hc p hp
  have ha := (intrinsicPoint_even_norm ρ hr p).1
  obtain ⟨l, hlen, hl, hact⟩ := even_perpendicular_word h b hq _ ha A haA hqA t he hf
  refine ⟨l, hlen, hl, fun w => ?_⟩
  apply (Algebra.TensorProduct.lid F (CliffordAlgebra q)).injective
  simp only [map_mul, fieldVector]
  change (intrinsicPoint ρ p).val * CliffordAlgebra.ι q w.val =
    CliffordAlgebra.ι q (reflectWord h l w.val) * (intrinsicPoint ρ p).val
  rw [← hact, haA]

private theorem contracts_mem_sections {c : Cocharacter G.val} (D : LimitDecomposition c)
    {p : FieldPoints G.val} (hp : HasLimit c p 1) :
    testPointSections G.val p ∈ SubgroupSections D.contracting (𝟙_ (SchemeOver F)) := by
  obtain ⟨s, hs⟩ := (D.contracting_points (fieldAlgebra F) p).mp hp
  change s ≫ D.contracting.inclusion.hom.hom = p at hs
  refine ⟨testPointSections D.contracting.group s, ?_⟩
  change ((rationalSourceIso F).hom ≫ s) ≫ D.contracting.inclusion.hom.hom =
    (rationalSourceIso F).hom ≫ p
  rw [Category.assoc, hs]

include b in
private theorem weyl_mem_radicals
    (c : Cocharacter G.val) (hr : IsSpinPointRepresentation q G.val ρ)
    (hc : HasSpinCocharacterFormula h ρ c)
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (w : h.perpendicular) (hw : q w.val ≠ 0) :
    ∃ p : FieldPoints G.val,
      testPointSections G.val p ∈ SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
        SubgroupSections E.contracting (𝟙_ (SchemeOver F)) ∧
      (intrinsicPoint ρ p).val = weylElement q h w.val := by
  let R := fieldAlgebra F
  let h' := dynamicsPair h
  let w' : h.perpendicular := (q w.val)⁻¹ • w
  have hw' := field_perpendicular b h w'
  have hw's : (1 ⊗ₜ[F] w'.val) ∈
      Specs.Arithmetic.SpinHyperbolicDynamics.perpendicularOver q h'.swap b R :=
    ⟨hw'.2, hw'.1⟩
  obtain ⟨hex, hfx⟩ := SpinHyperbolicDynamics.shearsContract q b h' ρ c hr hc
  obtain ⟨p, hp, hc₁, _⟩ := hex R ⟨_, field_perpendicular b h w⟩
  obtain ⟨r, hr', hc₂, _⟩ := hfx R ⟨_, hw's⟩
  let B := SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
    SubgroupSections E.contracting (𝟙_ (SchemeOver F))
  have hpB : testPointSections G.val p ∈ B := Subgroup.mem_sup_left (contracts_mem_sections D hc₁)
  have hrB : testPointSections G.val r ∈ B := Subgroup.mem_sup_right (contracts_mem_sections E hc₂)
  refine ⟨p * r * p, ?_, ?_⟩
  · change testPointSections G.val (p * r * p) ∈ B
    rw [map_mul, map_mul]
    exact B.mul_mem (B.mul_mem hpB hrB) hpB
  · change (ρ (fieldAlgebra F) p).val =
      1 + vectors q F (1 ⊗ₜ[F] h.e) * vectors q F (1 ⊗ₜ[F] w.val) at hp
    change (ρ (fieldAlgebra F) r).val =
      1 + vectors q F (1 ⊗ₜ[F] h.f) * vectors q F (1 ⊗ₜ[F] w'.val) at hr'
    have hp' := congrArg (Algebra.TensorProduct.lid F (CliffordAlgebra q)) hp
    have hf' := congrArg (Algebra.TensorProduct.lid F (CliffordAlgebra q)) hr'
    simp only [map_add, map_one, map_mul, fieldVector] at hp' hf'
    change (intrinsicPoint ρ p).val = 1 + CliffordAlgebra.ι q h.e * CliffordAlgebra.ι q w.val at hp'
    change (intrinsicPoint ρ r).val =
      1 + CliffordAlgebra.ι q h.f * CliffordAlgebra.ι q ((q w.val)⁻¹ • w.val) at hf'
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hp', hf']
    simpa only [weylElement, map_add, map_smul] using weylWordCalculation q h w hw

/-- Even words in the Weyl lifts fix each isotropic line. Odd words
exchange the lines. In either case the two factors are reciprocal. -/
private theorem weyl_word_mem
    (B : Subgroup (FieldPoints G.val))
    (H : ∀ w : h.perpendicular, q w.val ≠ 0 →
      ∃ p ∈ B, (intrinsicPoint ρ p).val = weylElement q h w.val)
    (l : List h.perpendicular) (hl : ∀ w ∈ l, q w.val ≠ 0) :
    ∃ p ∈ B, ∃ s : Fˣ,
      let a := (intrinsicPoint ρ p).val
      let x := if l.length % 2 = 0 then h.e else h.f
      let y := if l.length % 2 = 0 then h.f else h.e
      a * CliffordAlgebra.ι q h.e = (s : F) • (CliffordAlgebra.ι q x * a) ∧
      a * CliffordAlgebra.ι q h.f = (↑s⁻¹ : F) • (CliffordAlgebra.ι q y * a) ∧
      ∀ w : h.perpendicular, a * CliffordAlgebra.ι q w.val =
        CliffordAlgebra.ι q (reflectWord h l w.val) * a := by
  induction l with
  | nil =>
    refine ⟨1, B.one_mem, 1, ?_⟩
    simp [reflectWord]
  | cons w l ih =>
    have hw := hl w (List.mem_cons_self ..)
    obtain ⟨r, hrB, hr⟩ := H w hw
    obtain ⟨p, hpB, s, he, hf, hW⟩ := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    let a := (intrinsicPoint ρ r).val
    let d := (intrinsicPoint ρ p).val
    let t : Fˣ := -(Units.mk0 (q w.val) hw)⁻¹
    obtain ⟨ra, rb, rW⟩ := weylActionCalculation q h w hw
    change a = weylElement q h w.val at hr
    have re : a * CliffordAlgebra.ι q h.e =
        (t : F) • (CliffordAlgebra.ι q h.f * a) := by
      have ht : (t : F) = -(q w.val)⁻¹ := by simp [t]
      rw [hr, ht]
      simpa only [weylElement, map_smul, smul_mul_assoc] using ra
    have rf : a * CliffordAlgebra.ι q h.f =
        (↑t⁻¹ : F) • (CliffordAlgebra.ι q h.e * a) := by
      have ht : (↑t⁻¹ : F) = -q w.val := by simp [t]
      rw [hr, ht]
      simpa only [weylElement, map_smul, smul_mul_assoc] using rb
    have hW' (x : h.perpendicular) :
        (a * d) * CliffordAlgebra.ι q x.val =
          CliffordAlgebra.ι q (reflectWord h (w :: l) x.val) * (a * d) := by
      have hmem : ∀ m : List h.perpendicular, reflectWord h m x.val ∈ h.perpendicular := by
        intro m
        induction m with
        | nil => exact x.property
        | cons z m ih =>
          exact Submodule.sub_mem _ ih (Submodule.smul_mem _ _ z.property)
      have rr : a * CliffordAlgebra.ι q (reflectWord h l x.val) =
          CliffordAlgebra.ι q (reflection q w.val (reflectWord h l x.val)) * a := by
        rw [hr]
        exact rW ⟨_, hmem l⟩
      rw [mul_assoc, hW x, ← mul_assoc, rr, mul_assoc]
      rfl
    have hval : (intrinsicPoint ρ (r * p)).val = a * d := by simp [a, d]
    refine ⟨r * p, B.mul_mem hrB hpB, ?_⟩
    by_cases hlen : l.length % 2 = 0
    · have hn : (w :: l).length % 2 ≠ 0 := by simp only [List.length_cons]; omega
      refine ⟨s * t, ?_⟩
      simp only [hlen, ite_true] at he hf
      simp only [hval, hn, ite_false]
      change d * CliffordAlgebra.ι q h.e = _ at he
      change d * CliffordAlgebra.ι q h.f = _ at hf
      refine ⟨?_, ?_, hW'⟩
      · rw [mul_assoc, he, mul_smul_comm, ← mul_assoc a, re, smul_mul_assoc, smul_smul,
          mul_assoc, Units.val_mul]
      · rw [mul_assoc, hf, mul_smul_comm, ← mul_assoc a, rf, smul_mul_assoc, smul_smul,
          mul_assoc, mul_inv_rev, Units.val_mul, mul_comm (↑s⁻¹ : F)]
    · have hn : (w :: l).length % 2 = 0 := by simp only [List.length_cons]; omega
      refine ⟨s * t⁻¹, ?_⟩
      simp only [hlen, ite_false] at he hf
      simp only [hval, hn, ite_true]
      change d * CliffordAlgebra.ι q h.e = _ at he
      change d * CliffordAlgebra.ι q h.f = _ at hf
      refine ⟨?_, ?_, hW'⟩
      · rw [mul_assoc, he, mul_smul_comm, ← mul_assoc a, rf, smul_mul_assoc, smul_smul,
          mul_assoc, Units.val_mul]
      · rw [mul_assoc, hf, mul_smul_comm, ← mul_assoc a, re, smul_mul_assoc, smul_smul,
          mul_assoc, mul_inv_rev, inv_inv, Units.val_mul, mul_comm (↑s⁻¹ : F)]

private theorem inverse_intertwining {M : Type*} [Monoid M] (a : Mˣ) {x y : M}
    (h : a.val * x = y * a.val) : a⁻¹.val * y = x * a⁻¹.val := by
  calc
    _ = (a⁻¹.val * (y * a.val)) * a⁻¹.val := by
      simp only [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [← h, ← mul_assoc a⁻¹.val, Units.inv_mul, one_mul]

private theorem quotient_scale (a d : (CliffordAlgebra q)ˣ) (x : CliffordAlgebra q)
    (t r : Fˣ)
    (ha : a.val * x = (t : F) • (x * a.val))
    (hd : d.val * x = (r : F) • (x * d.val)) :
    (d⁻¹.val * a.val) * x = (↑(t * r⁻¹) : F) • (x * (d⁻¹.val * a.val)) := by
  have hd' : d.val * ((↑r⁻¹ : F) • x) = x * d.val := by
    rw [mul_smul_comm, hd, smul_smul, Units.inv_mul, one_smul]
  have hi := inverse_intertwining d hd'
  rw [mul_assoc, ha, mul_smul_comm, ← mul_assoc d⁻¹.val, hi, smul_mul_assoc,
    smul_mul_assoc, smul_smul, mul_assoc, Units.val_mul]

private theorem spin_diagonal_mem
    (B : Subgroup (FieldPoints G.val))
    (H : ∀ w : h.perpendicular, q w.val ≠ 0 →
      ∃ g ∈ B, (intrinsicPoint ρ g).val = weylElement q h w.val)
    (w : h.perpendicular) (hw : q w.val ≠ 0) (s : Fˣ) :
    ∃ g ∈ B, (intrinsicPoint ρ g).val = planeDiagonal q h (s : F) (↑s⁻¹ : F) := by
  have hsw : q (((s : F) • w : h.perpendicular).val) ≠ 0 := by
    change q ((s : F) • w.val) ≠ 0
    rw [q.map_smul, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero s.ne_zero s.ne_zero) hw
  obtain ⟨g, hgB, hg⟩ := H w hw
  obtain ⟨g', hg'B, hg'⟩ := H ((s : F) • w) hsw
  change (intrinsicPoint ρ g').val = weylElement q h ((s : F) • w.val) at hg'
  refine ⟨g' * g⁻¹, B.mul_mem hg'B (B.inv_mem hgB), ?_⟩
  rw [map_mul, map_inv, Units.val_mul, hg', (weylScaleCalculation q h w hw).1 _ s.ne_zero,
    ← hg, mul_assoc, Units.mul_inv, mul_one, Units.val_inv_eq_inv_val]

include b in
private theorem centralizer_mem_of_weyl_lifts [Infinite F] [Fintype I]
    (hr : IsSpinPointRepresentation q G.val ρ) (hq : IsRegular q)
    (B : Subgroup (FieldPoints G.val))
    (H : ∀ w : h.perpendicular, q w.val ≠ 0 →
      ∃ g ∈ B, (intrinsicPoint ρ g).val = weylElement q h w.val)
    (w₀ : h.perpendicular) (hw₀ : q w₀.val ≠ 0) (p : FieldPoints G.val)
    (A : V ≃ₗ[F] V) (t : Fˣ) (hqA : ∀ x, q (A x) = q x)
    (haA : ∀ x, (intrinsicPoint ρ p).val * CliffordAlgebra.ι q x =
      CliffordAlgebra.ι q (A x) * (intrinsicPoint ρ p).val)
    (he : A h.e = (t : F) • h.e) (hf : A h.f = (↑t⁻¹ : F) • h.f) :
    p ∈ B := by
  have ha := (intrinsicPoint_even_norm ρ hr p).1
  obtain ⟨l, hpar, hl, hact⟩ := even_perpendicular_word h b hq _ ha A haA hqA t he hf
  obtain ⟨v, hv, r, hve, hvf, hvW⟩ := weyl_word_mem h ρ B H l hl
  simp only [hpar, ite_true] at hve hvf
  let z := v⁻¹ * p
  let a := intrinsicPoint ρ p
  let d := intrinsicPoint ρ v
  let k := (intrinsicPoint ρ z).val
  have hk : k = d⁻¹.val * a.val := by
    change (intrinsicPoint ρ (v⁻¹ * p)).val = _
    rw [map_mul, map_inv, Units.val_mul]
  have hke : k * CliffordAlgebra.ι q h.e =
      (↑(t * r⁻¹) : F) • (CliffordAlgebra.ι q h.e * k) := by
    rw [hk]
    exact quotient_scale a d _ t r (by rw [haA, he, map_smul, smul_mul_assoc]) hve
  have hkf : k * CliffordAlgebra.ι q h.f =
      (↑(t * r⁻¹)⁻¹ : F) • (CliffordAlgebra.ι q h.f * k) := by
    rw [hk, mul_inv_rev, mul_comm, inv_inv]
    exact quotient_scale a d _ t⁻¹ r⁻¹ (by rw [haA, hf, map_smul, smul_mul_assoc]) hvf
  have hkW (w : h.perpendicular) : Commute k (CliffordAlgebra.ι q w.val) := by
    change k * CliffordAlgebra.ι q w.val = CliffordAlgebra.ι q w.val * k
    rw [hk, mul_assoc, haA, hact, ← mul_assoc,
      inverse_intertwining d (hvW w), mul_assoc]
  obtain ⟨hEven, hNorm⟩ := intrinsicPoint_even_norm ρ hr z
  obtain ⟨s, hs, _⟩ := scaleLiftCalculation q b h hq (t * r⁻¹) k hEven hNorm hke hkf hkW
  obtain ⟨g, hgB, hg⟩ := spin_diagonal_mem h ρ B H w₀ hw₀ s
  have hz : z = g := intrinsicPoint_injective ρ hr (Units.ext (hs.trans hg.symm))
  have hzB : z ∈ B := by rw [hz]; exact hgB
  have hpz : v * z = p := mul_inv_cancel_left _ _
  rw [← hpz]
  exact B.mul_mem hv hzB

private theorem field_point_centralizes {c : Cocharacter G.val} (D : LimitDecomposition c)
    {p : 𝟙_ (SchemeOver F) ⟶ G.val.X}
    (hp : p ∈ SubgroupSections D.centralizer (𝟙_ (SchemeOver F))) :
    Centralizes c ((testPointSections G.val).symm p) := by
  obtain ⟨v, hv⟩ := hp
  change v ≫ D.centralizer.inclusion.hom.hom = p at hv
  apply (D.centralizer_points _ _).mpr
  refine ⟨(testPointSections D.centralizer.group).symm v, ?_⟩
  change ((rationalSourceIso F).inv ≫ v) ≫ D.centralizer.inclusion.hom.hom =
    (rationalSourceIso F).inv ≫ p
  rw [Category.assoc, hv]

private theorem mem_of_symm_mem_comap {M N : Type*} [Group M] [Group N]
    (e : M ≃* N) (L : Subgroup N) {p : N} (hp : e.symm p ∈ L.comap e.toMonoidHom) :
    p ∈ L := by
  change e (e.symm p) ∈ L at hp
  rwa [e.apply_symm_apply] at hp

include b in
private theorem centralizing_point_mem [Infinite F] [Fintype I]
    (hr : IsSpinPointRepresentation q G.val ρ) (hq : IsRegular q)
    (c : Cocharacter G.val) (hc : HasSpinCocharacterFormula h ρ c)
    (B : Subgroup (FieldPoints G.val))
    (H : ∀ x : h.perpendicular, q x.val ≠ 0 →
      ∃ a ∈ B, (intrinsicPoint ρ a).val = weylElement q h x.val)
    (w : h.perpendicular) (hw : q w.val ≠ 0) (g : FieldPoints G.val) (hg : Centralizes c g) :
    g ∈ B := by
  obtain ⟨A, t, hqA, haA, he, hf⟩ := centralizer_intrinsic_action b h ρ hr c hc g hg
  exact centralizer_mem_of_weyl_lifts b h ρ hr hq B H w hw g A t hqA haA he hf

include b in
private theorem centralizer_sections_le [Infinite F] [Fintype I]
    (hr : IsSpinPointRepresentation q G.val ρ) (hq : IsRegular q)
    (c : Cocharacter G.val) (hc : HasSpinCocharacterFormula h ρ c)
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (w : h.perpendicular) (hw : q w.val ≠ 0) :
    SubgroupSections D.centralizer (𝟙_ (SchemeOver F)) ≤
      SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
        SubgroupSections E.contracting (𝟙_ (SchemeOver F)) := by
  let L := SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
    SubgroupSections E.contracting (𝟙_ (SchemeOver F))
  let e := testPointSections G.val
  let B := L.comap e.toMonoidHom
  have H (x : h.perpendicular) (hx : q x.val ≠ 0) :
      ∃ a ∈ B, (intrinsicPoint ρ a).val = weylElement q h x.val := by
    obtain ⟨a, ha, hvalue⟩ := weyl_mem_radicals b h ρ c hr hc D E x hx
    exact ⟨a, Subgroup.mem_comap.mpr ha, hvalue⟩
  intro p hp
  have hmem : e.symm p ∈ B :=
    centralizing_point_mem b h ρ hr hq c hc B H w hw (e.symm p)
      (field_point_centralizes D (p := p) hp)
  exact mem_of_symm_mem_comap e L (p := p) hmem

include b in
private theorem radicals_generate [Infinite F] [Fintype I]
    (hr : IsSpinPointRepresentation q G.val ρ) (hq : IsRegular q)
    (hG : IsAbsolutelyAlmostSimple G) (c : Cocharacter G.val) (hc : HasSpinCocharacterFormula h ρ c)
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c)) :
    SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
      SubgroupSections E.contracting (𝟙_ (SchemeOver F)) = ⊤ := by
  obtain ⟨⟨w, hw⟩, _⟩ :=
    SpinHyperbolicDynamics.noncentrality q b (dynamicsPair h) hq G ρ c hr hc hG
  have hL := centralizer_sections_le b h ρ hr hq c hc D E w hw
  have H := RelativeRayGeneration.twoRadicals_sup_centralizer
    (reductive_of_semisimple G hG.1) D E
  change (SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
    SubgroupSections E.contracting (𝟙_ (SchemeOver F))) ⊔
      SubgroupSections D.centralizer (𝟙_ (SchemeOver F)) = ⊤ at H
  exact (sup_eq_left.mpr hL).symm.trans H

/-- Local generation for the represented spin group and the marked opposite radicals. -/
theorem localSpinGeneration : LocalSpinGeneration.{u} := by
  intro F _ _ V _ _ I _ _ q b G ρ hr hq hG h
  let h' := dynamicsPair h
  obtain ⟨c, hc⟩ := SpinHyperbolicDynamics.cocharacterExists q b h' ρ hr
  obtain ⟨_, p, hp⟩ := SpinHyperbolicDynamics.noncentrality q b h' hq G ρ c hr hc hG
  refine ⟨c, hc, ⟨_, p, hp⟩, centralizer_even_word b h ρ hr hq c hc, ?_⟩
  intro D E
  refine ⟨?_, ?_, radicals_generate b h ρ hr hq hG c hc D E⟩
  · obtain ⟨h₁, h₂⟩ := SpinHyperbolicDynamics.shearsContract q b h' ρ c hr hc
    intro R g
    constructor
    · rintro ⟨w, he, hf, hw⟩
      obtain ⟨g', hg', hlimit, _⟩ := h₁ R ⟨w, he, hf⟩
      have eq : g' = g := (hr.1 R).1 (Units.ext (hg'.trans hw.symm))
      exact eq ▸ hlimit
    · rintro ⟨w, he, hf, hw⟩
      obtain ⟨g', hg', hlimit, _⟩ := h₂ R ⟨w, hf, he⟩
      have eq : g' = g := (hr.1 R).1 (Units.ext (hg'.trans hw.symm))
      exact eq ▸ hlimit
  · intro charZero R g
    let : CharZero F := charZero
    obtain ⟨h₁, h₂⟩ := SpinHyperbolicDynamics.contractingPoints q b h' hq ρ c hr hc
    constructor
    · intro hlimit
      obtain ⟨w, hw, _⟩ := h₁ R g hlimit
      exact ⟨w.val, w.property.1, w.property.2, hw⟩
    · intro hlimit
      obtain ⟨w, hw, _⟩ := h₂ R g hlimit
      exact ⟨w.val, w.property.2, w.property.1, hw⟩

end
end RationalPoints

section GlobalApproximation

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open CocharacterDynamics
open LinearAlgebraicGroups.Albert
open LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open SpinSpecification (ScalarClifford IsSpinPointRepresentation)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.Arithmetic.OppositeRadicals (localPlus IsNoncentral)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)

open private globalField_infinite completionPointEquiv completionPointEquiv_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

noncomputable section

set_option backward.isDefEq.respectTransparency false

private theorem localPlus_eq_univ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (w : D.Place)
    (htop : unipotentGenerated (baseChangedAlgebraicGroup (D.Completion w) G) = ⊤) :
    localPlus D i w = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨p, hp⟩ := (completionPointEquiv D i w).surjective g
  have hmem : p ∈ unipotentGenerated (baseChangedAlgebraicGroup (D.Completion w) G) := by
    rw [htop]
    exact Subgroup.mem_top p
  have hpoint := (completionPointEquiv_apply D i w p).symm.trans hp
  unfold localPlus
  rw [Set.mem_ofPred_eq]
  exact ⟨p, hmem, hpoint⟩

private theorem spin_localPlus_eq_univ
    {K : Type u} [Field K] {V : Type u} [AddCommGroup V] [Module K V] [Module.Finite K V]
    {I : Type u} [LinearOrder I] [Fintype I] {q : QuadraticForm K V}
    (D : GlobalFieldData.{u, v} K) (b : Module.Basis I K V) (h : HyperbolicPair q)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (ρ : ∀ R : TestAlgebra K, GroupPoints G.val R →* (ScalarClifford q R)ˣ)
    (hr : IsSpinPointRepresentation q G.val ρ) (hq : IsRegular q) (hG : IsAbsolutelyAlmostSimple G)
    (c : Cocharacter G.val) (hc : HasSpinCocharacterFormula h ρ c) (hnc : IsNoncentral c)
    (P : LimitDecomposition c) (N : LimitDecomposition (oppositeCocharacter c))
    (w : D.Place) : localPlus D i w = Set.univ := by
  let F := D.Completion w
  let GF := baseChangedAlgebraicGroup F G
  let Q := CliffordSpecification.coefficientForm F q b
  let : Infinite K := globalField_infinite D
  let : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  have hGF := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := F) G hG
  obtain ⟨m, hm, hncF, PF, NF, _⟩ := OppositeRadicals.localGeneration D G i hG c hnc P N w
  let cF : Cocharacter GF.val := m.hom ≫ (groupBaseChange K F).map c
  obtain ⟨_, ρF, _, _, _, _, _, _, hrF, hmark⟩ :=
    SpinScalarExtension.spinRepresentationExtension (F := F) q b G ρ hr
  obtain ⟨heF, hfF, hpair⟩ :=
    SpinScalarExtension.hyperbolicPairExtension (F := F) q b h.e h.f h.q_e h.q_f h.polar_ef
  let hF : HyperbolicPair Q := ⟨1 ⊗ₜ[K] h.e, 1 ⊗ₜ[K] h.f, heF, hfF, hpair⟩
  have hcF : HasSpinCocharacterFormula hF ρF cF :=
    (hmark h.e h.f h.q_e h.q_f h.polar_ef c hc m hm).2.1
  obtain ⟨_, hrad₀, hrad₁⟩ := SpinScalarExtension.polarRadicalExtension (F := F) q b
  have hQ : IsRegular Q := by
    rcases hq with hn | ⟨r, hr, heq⟩
    · exact Or.inl (hrad₀ hn)
    · exact Or.inr ⟨1 ⊗ₜ[K] r, hrad₁ r hr heq⟩
  have htop : unipotentGenerated GF = ⊤ :=
    (RelativeRayGeneration.twoRadicalsGenerate GF hGF cF hncF PF NF).symm.trans
      (radicals_generate (b.baseChange F) hF ρF hrF hQ hGF cF hcF PF NF)
  exact localPlus_eq_univ D i w htop

/-- The local generation of the same spin group at every completion gives strong
approximation for the global isotropic form. -/
theorem globalSpinApproximation : GlobalSpinApproximation.{u, v} := by
  intro K _ D V _ _ _ q G ρ hr hq hiso hG i S hS
  let : Infinite K := globalField_infinite D
  let b : Module.Basis (ULift.{u} (Fin (Module.finrank K V))) K V :=
    (Module.finBasis K V).reindex Equiv.ulift.symm
  obtain ⟨e, he, heq⟩ := hiso
  obtain ⟨h, _⟩ := hyperbolicPairExistence q hq e he heq
  obtain ⟨c, hc⟩ := SpinHyperbolicDynamics.cocharacterExists q b (dynamicsPair h) ρ hr
  obtain ⟨_, g, hg⟩ := SpinHyperbolicDynamics.noncentrality q b (dynamicsPair h) hq G ρ c hr hc hG
  have hnc : IsNoncentral c := ⟨_, g, hg⟩
  obtain ⟨P⟩ := existsLimitDecomposition G c
  obtain ⟨N⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  apply ((OppositeRadicals.approximation D G i hG c hnc P N).2.2.2.2 S hS).2
  intro w
  have hw := spin_localPlus_eq_univ D b h G i ρ hr hq hG c hc hnc P N w.1
  rw [hw]
  exact dense_univ

end
end GlobalApproximation

end LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
