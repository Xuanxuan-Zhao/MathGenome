import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.MoritaEvaluations
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.P103.Ch02.DualBasis
import Mathlib.Algebra.Module.ULift

noncomputable section
universe u v w
namespace P103.Ch03.MoritaEvaluations
open MulOpposite P103.Morita P103.BalancedTensor
variable {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module Rᵐᵒᵖ P]

/-- Finite right dual basis with functionals valued in the actual regular R-module. -/
theorem finite_dual_basis [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] :
    ∃ (n : ℕ) (p : Fin n → P) (q : Fin n → Q R P),
      ∀ x, x = ∑ i, op (q i x) • p i := by
  obtain ⟨n, p, q, _, h⟩ := P103.Ch02.DualBasis.right_finite_dualBasis R P
  let q' : Fin n → Q R P := fun i =>
    { toFun := fun x => unop (q i x)
      map_add' := by intros; simp
      map_smul' := by intros; simp [map_smul, smul_eq_mul] }
  exact ⟨n, p, q', h⟩

/-- A finite trace identity extracted from a preimage of 1 in a sum of copies of P. -/
theorem finite_trace (h : IsGenerator R P) :
    ∃ (J : Type (max u v)) (t : Finset J) (a : J → P) (b : J → Q R P),
      ∑ j ∈ t, b j (a j) = 1 := by
  classical
  obtain ⟨J, f, hf⟩ := h (ULift.{max u v} R)
  let g : (J →₀ P) →ₗ[Rᵐᵒᵖ] R := (ULift.moduleEquiv.toLinearMap).comp f
  obtain ⟨z, hz⟩ := hf (ULift.up 1)
  let b : J → Q R P := fun j => g.comp (Finsupp.lsingle j)
  refine ⟨J, z.support, fun j => z j, b, ?_⟩
  change ∑ j ∈ z.support, g (Finsupp.single j (z j)) = 1
  rw [← map_sum]
  rw [show (∑ j ∈ z.support, Finsupp.single j (z j)) = z from z.sum_single]
  exact congrArg ULift.down hz

/-- The generator convention gives quotients in every universe, with no size
restriction on the module or the indexing set of its elements. -/
theorem generator_quotients : P103.Morita.generatorQuotientsType.{u,v,w} := by
  intro R _ P _ _ hG M _ _
  classical
  obtain ⟨J, t, a, b, ht⟩ := finite_trace hG
  let k : M × J → P →ₗ[Rᵐᵒᵖ] M := fun c =>
    { toFun := fun p => op (b c.2 p) • c.1
      map_add' := by intros; simp [map_add, add_smul]
      map_smul' := by intros; simp [map_smul, smul_smul] }
  let f : ((M × J) →₀ P) →ₗ[Rᵐᵒᵖ] M := Finsupp.lsum ℤ k
  refine ⟨M × J, f, ?_⟩
  intro x
  refine ⟨∑ j ∈ t, Finsupp.single (x, j) (a j), ?_⟩
  calc
    _ = ∑ j ∈ t, op (b j (a j)) • x := by
      simp only [map_sum, f, Finsupp.lsum_single, k, LinearMap.coe_mk, AddHom.coe_mk]
    _ = op (∑ j ∈ t, b j (a j)) • x := by simp [Finset.sum_smul]
    _ = x := by rw [ht]; simp

@[simp] theorem theta_add_left (p p' : P) (q : Q R P) :
    theta R P (p + p') q = theta R P p q + theta R P p' q := by
  ext x; simp [smul_add]
@[simp] theorem theta_add_right (p : P) (q q' : Q R P) :
    theta R P p (q + q') = theta R P p q + theta R P p q' := by
  ext x; simp [add_smul]

def endPairing : Pairing R (A := P) (B := Q R P) (S R P) :=
  Pairing.ofFun (theta R P) theta_add_left theta_add_right (by
    intro r p q
    ext x
    simp [smul_smul])

def endMap : Tensor R P (Q R P) →+ S R P := lift endPairing
@[simp] theorem endMap_tmul (p : P) (q : Q R P) :
    endMap (tmul R p q) = theta R P p q := rfl

def evalPairing : Pairing (S R P) (A := Q R P) (B := P) R :=
  Pairing.ofFun (fun q p => q p)
    (by intros; rfl) (by intros; exact map_add _ _ _) (by intros; rfl)

def evalMap : Tensor (S R P) (Q R P) P →+ R := lift evalPairing
@[simp] theorem evalMap_tmul (q : Q R P) (p : P) :
    evalMap (tmul (S R P) q p) = q p := rfl

/-- The expansion of a functional obtained by applying it to the dual-basis identity. -/
theorem functional_expansion {n : ℕ} (p : Fin n → P) (q : Fin n → Q R P)
    (h : ∀ x, x = ∑ i, op (q i x) • p i) (v : Q R P) :
    v = ∑ i, (v (p i)) • q i := by
  ext x
  have hx := congrArg v (h x)
  simpa [map_sum, map_smul] using hx

/-- Explicit inverse of the endomorphism evaluation, from a finite dual basis. -/
def endInverse {n : ℕ} (p : Fin n → P) (q : Fin n → Q R P) :
    S R P →+ Tensor R P (Q R P) :=
  AddMonoidHom.mk' (fun s => ∑ i, tmul R (s (p i)) (q i)) (by
    intro s t
    simp [add_tmul, Finset.sum_add_distrib])

theorem endMap_inverse {n : ℕ} (p : Fin n → P) (q : Fin n → Q R P)
    (h : ∀ x, x = ∑ i, op (q i x) • p i) (s : S R P) :
    endMap (endInverse p q s) = s := by
  ext x
  change (endMap (∑ i, tmul R (s (p i)) (q i))) x = s x
  simp only [map_sum, endMap_tmul, LinearMap.sum_apply, theta_apply]
  simpa only [map_sum, map_smul] using (congrArg s (h x)).symm

theorem endInverse_map {n : ℕ} (p : Fin n → P) (q : Fin n → Q R P)
    (h : ∀ x, x = ∑ i, op (q i x) • p i) (z : Tensor R P (Q R P)) :
    endInverse p q (endMap z) = z := by
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ha z z' hz hz' => simp [hz, hz']
  | ht a b =>
    change (∑ i, tmul R (op (b (p i)) • a) (q i)) = tmul R a b
    simp_rw [balance]
    change (∑ i, (pairing (R := R)).toBiadditive a (b (p i) • q i)) = _
    rw [← map_sum, ← functional_expansion p q h b]
    rfl

/-- Both inverse formulas are part of the constructed additive isomorphism. -/
def endEquiv {n : ℕ} (p : Fin n → P) (q : Fin n → Q R P)
    (h : ∀ x, x = ∑ i, op (q i x) • p i) : Tensor R P (Q R P) ≃+ S R P :=
  { endMap with
    invFun := endInverse p q
    left_inv := endInverse_map p q h
    right_inv := endMap_inverse p q h }

/-- Explicit inverse of evaluation, from a finite trace identity. -/
def evalInverse {J : Type*} (t : Finset J) (a : J → P) (b : J → Q R P) :
    R →+ Tensor (S R P) (Q R P) P :=
  AddMonoidHom.mk' (fun r => ∑ j ∈ t, tmul (S R P) (b j) (op r • a j)) (by
    intro r s
    simp [add_smul, tmul_add, Finset.sum_add_distrib])

theorem evalMap_inverse {J : Type*} (t : Finset J) (a : J → P) (b : J → Q R P)
    (h : ∑ j ∈ t, b j (a j) = 1) (r : R) :
    evalMap (evalInverse t a b r) = r := by
  change evalMap (∑ j ∈ t, tmul (S R P) (b j) (op r • a j)) = r
  simp only [map_sum, evalMap_tmul, map_smul, MulOpposite.smul_eq_mul_unop,
    unop_op]
  rw [← Finset.sum_mul, h, one_mul]

theorem functional_theta (b q : Q R P) (a : P) :
    op (theta R P a q) • b = b a • q := by
  ext x
  simp [map_smul]

theorem evalInverse_map {J : Type*} (t : Finset J) (a : J → P) (b : J → Q R P)
    (h : ∑ j ∈ t, b j (a j) = 1) (z : Tensor (S R P) (Q R P) P) :
    evalInverse t a b (evalMap z) = z := by
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ha z z' hz hz' => simp [hz, hz']
  | ht q p =>
    change (∑ j ∈ t, tmul (S R P) (b j) (op (q p) • a j)) = tmul (S R P) q p
    calc
      _ = ∑ j ∈ t, tmul (S R P) (op (theta R P (a j) q) • b j) p := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (balance (theta R P (a j) q) (b j) p).symm
      _ = tmul (S R P) (∑ j ∈ t, b j (a j) • q) p := by
        simp_rw [functional_theta]
        exact (map_sum ((pairing (R := S R P) (A := Q R P) (B := P)).toBiadditive.flip p) _ _).symm
      _ = _ := by rw [← Finset.sum_smul, h, one_smul]

def evalEquiv {J : Type*} (t : Finset J) (a : J → P) (b : J → Q R P)
    (h : ∑ j ∈ t, b j (a j) = 1) : Tensor (S R P) (Q R P) P ≃+ R :=
  { evalMap with
    invFun := evalInverse t a b
    left_inv := evalInverse_map t a b h
    right_inv := evalMap_inverse t a b h }

theorem endMap_leftScale (s : S R P) (z : Tensor R P (Q R P)) :
    endMap (leftScale s z) = s * endMap z := by
  apply lift_leftScale endPairing _ s z
  intro s a b
  ext x
  exact (s.map_smul (op (b x)) a).symm

theorem endMap_rightScale (s : (S R P)ᵐᵒᵖ) (z : Tensor R P (Q R P)) :
    endMap (rightScale s z) = endMap z * s.unop := by
  exact lift_rightScale endPairing (fun _ _ _ => rfl) s z

theorem evalMap_leftScale (r : R) (z : Tensor (S R P) (Q R P) P) :
    evalMap (leftScale r z) = r * evalMap z := by
  exact lift_leftScale evalPairing (fun _ _ _ => rfl) r z

theorem evalMap_rightScale (r : Rᵐᵒᵖ) (z : Tensor (S R P) (Q R P) P) :
    evalMap (rightScale r z) = evalMap z * r.unop := by
  apply lift_rightScale evalPairing _ r z
  intro r q p
  exact q.map_smul r p

/-- The two canonical balanced evaluations are isomorphisms of bimodules. -/
theorem evaluations : P103.Morita.evaluationsType.{u,v} := by
  intro R _ P _ _ _ _ hG
  let lS : Module (S R P) (Tensor R P (Q R P)) := leftModule
  let rS : Module (S R P)ᵐᵒᵖ (Tensor R P (Q R P)) := rightModule
  let lR : Module R (Tensor (S R P) (Q R P) P) := leftModule
  let rR : Module Rᵐᵒᵖ (Tensor (S R P) (Q R P) P) := rightModule
  refine ⟨lS, rS, lR, rR, ?_⟩
  let := lS
  let := rS
  let := lR
  let := rR
  refine ⟨⟨fun s t z => outer_commute s t z⟩,
    ⟨fun r t z => outer_commute r t z⟩,
    (fun _ _ _ => rfl), (fun _ _ _ => rfl),
    (fun _ _ _ => rfl), (fun _ _ _ => rfl), ?_⟩
  obtain ⟨n, p, q, h⟩ := finite_dual_basis (R := R) (P := P)
  obtain ⟨J, t, a, b, ht⟩ := finite_trace hG
  refine ⟨endEquiv p q h, evalEquiv t a b ht,
    (fun _ _ => rfl), (fun _ _ => rfl), ?_, ?_, ?_, ?_⟩
  · exact endMap_leftScale
  · exact endMap_rightScale
  · exact evalMap_leftScale
  · exact evalMap_rightScale

end P103.Ch03.MoritaEvaluations
