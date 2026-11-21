import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.Coordinates
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Alg01SymmetricWitt.Witt.Coordinates

universe u v w

/-- The hyperbolic plane with quadratic value `x * y`. -/
def hyperbolicPlane (k : Type u) [Field k] : QuadraticForm k (k × k) :=
  Specs.Alg01SymmetricWitt.Witt.Coordinates.hyperbolicPlane k

/-- The coordinatewise orthogonal sum of `r` hyperbolic planes. -/
def hyperbolicSum (k : Type u) [Field k] (r : ℕ) : QuadraticForm k (Fin r → k × k) :=
  Specs.Alg01SymmetricWitt.Witt.Coordinates.hyperbolicSum k r

/-- The subspace of the hyperbolic sum with all second coordinates zero. -/
def firstCoordinates (k : Type u) [Field k] (r : ℕ) : Submodule k (Fin r → k × k) :=
  Specs.Alg01SymmetricWitt.Witt.Coordinates.firstCoordinates k r

/-- A subspace is totally isotropic if its restricted quadratic form vanishes. -/
def totallyIsotropic {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    (q : QuadraticForm k V) (T : Submodule k V) : Prop :=
  Specs.Alg01SymmetricWitt.Witt.Coordinates.totallyIsotropic q T

variable {k : Type u} [Field k]

@[simp] theorem hyperbolicPlane_apply (z : k × k) :
    hyperbolicPlane k z = z.1 * z.2 :=
  rfl

@[simp] theorem hyperbolicSum_apply {r : ℕ} (x : Fin r → k × k) :
    hyperbolicSum k r x = ∑ i, (x i).1 * (x i).2 :=
  QuadraticMap.pi_apply (fun _ => hyperbolicPlane k) x

@[simp] theorem mem_firstCoordinates {r : ℕ} {x : Fin r → k × k} :
    x ∈ firstCoordinates k r ↔ ∀ i, (x i).2 = 0 :=
  Iff.rfl

theorem firstCoordinates_totallyIsotropic (r : ℕ) :
    totallyIsotropic (hyperbolicSum k r) (firstCoordinates k r) := by
  intro x hx
  simp [hyperbolicSum_apply, mem_firstCoordinates.mp hx]

theorem anisotropic_of_subsingleton {V : Type v} [AddCommGroup V] [Module k V]
    [Subsingleton V] (q : QuadraticForm k V) : q.Anisotropic :=
  fun x _ => Subsingleton.elim x 0

theorem hyperbolicSum_zero : hyperbolicSum k 0 = 0 := by
  ext x
  simp

theorem associated_apply_div_two [Invertible (2 : k)] {V : Type v}
    [AddCommGroup V] [Module k V] (q : QuadraticForm k V) (x y : V) :
    QuadraticMap.associated q x y = (q (x + y) - q x - q y) / 2 := by
  rw [QuadraticMap.associated_apply]
  change (⅟(2 : k)) * (q (x + y) - q x - q y) = _
  rw [invOf_eq_inv, div_eq_mul_inv, mul_comm]

theorem nondegenerate_iff_associated_separatingLeft [Invertible (2 : k)] {V : Type v}
    [AddCommGroup V] [Module k V] (q : QuadraticForm k V) :
    q.Nondegenerate ↔ (QuadraticMap.associated q).SeparatingLeft := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticMap.radical_eq_ker_associated,
    LinearMap.separatingLeft_iff_ker_eq_bot]

theorem polarization {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] (q : QuadraticForm k V) :
    let B := QuadraticMap.associated q
    (∀ x y, B x y = (q (x + y) - q x - q y) / 2) ∧
      B.IsSymm ∧
      (∀ x, B x x = q x) ∧
      (q.Nondegenerate ↔ ∀ x, (∀ y, B x y = 0) → x = 0) ∧
      (∀ T : Submodule k V, totallyIsotropic q T ↔ ∀ x ∈ T, ∀ y ∈ T, B x y = 0) := by
  refine ⟨associated_apply_div_two q, QuadraticForm.associated_isSymm k q,
    QuadraticMap.associated_eq_self_apply k q, nondegenerate_iff_associated_separatingLeft q, ?_⟩
  intro T
  constructor
  · intro h x hx y hy
    rw [associated_apply_div_two, h _ (T.add_mem hx hy), h x hx, h y hy]
    simp
  · intro h x hx
    rw [← QuadraticMap.associated_eq_self_apply k q x]
    exact h x hx x hx

theorem preservesQuadraticIffBilinear {k : Type u} {V : Type v} {W : Type w}
    [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (q : QuadraticForm k V) (q' : QuadraticForm k W) (e : V ≃ₗ[k] W) :
    (∀ x, q' (e x) = q x) ↔
      ∀ x y, QuadraticMap.associated q' (e x) (e y) = QuadraticMap.associated q x y := by
  constructor
  · intro h x y
    rw [associated_apply_div_two, associated_apply_div_two, ← map_add, h, h, h]
  · intro h x
    simpa only [QuadraticMap.associated_eq_self_apply] using h x x

theorem hyperbolicDiagonal (k : Type u) [Field k] [Invertible (2 : k)] :
    ∃ e : ((QuadraticMap.sq (R := k)).prod
      ((-1 : k) • (QuadraticMap.sq (R := k) : QuadraticForm k k))).IsometryEquiv (hyperbolicPlane k),
      ∀ z : k × k, e z = (z.1 + z.2, z.1 - z.2) := by
  have two_ne : (2 : k) ≠ 0 := Invertible.ne_zero _
  let e : (k × k) ≃ₗ[k] (k × k) :=
    { toFun := fun z => (z.1 + z.2, z.1 - z.2)
      invFun := fun z => ((z.1 + z.2) / 2, (z.1 - z.2) / 2)
      left_inv := by
        intro z
        apply Prod.ext <;> dsimp <;> field_simp <;> ring
      right_inv := by
        intro z
        apply Prod.ext <;> dsimp <;> field_simp <;> ring
      map_add' := by
        intro x y
        apply Prod.ext <;> dsimp <;> ring
      map_smul' := by
        intro a z
        apply Prod.ext <;> simp [mul_add, mul_sub] }
  refine ⟨{ toLinearEquiv := e, map_app' := ?_ }, fun _ => rfl⟩
  intro z
  change (z.1 + z.2) * (z.1 - z.2) = z.1 * z.1 + (-1 : k) * (z.2 * z.2)
  ring

theorem hyperbolicNondegenerate (k : Type u) [Field k] [Invertible (2 : k)] :
    (hyperbolicPlane k).Nondegenerate ∧ ∀ r, (hyperbolicSum k r).Nondegenerate := by
  have plane : (QuadraticMap.associated (hyperbolicPlane k)).SeparatingLeft := by
    intro x hx
    have h₁ := hx (0, 1)
    have h₂ := hx (1, 0)
    have two_ne : (2 : k) ≠ 0 := Invertible.ne_zero _
    simp [associated_apply_div_two, div_eq_zero_iff, two_ne, mul_add, add_mul, add_sub_cancel_left] at h₁ h₂
    exact Prod.ext h₁ h₂
  refine ⟨(nondegenerate_iff_associated_separatingLeft _).2 plane, fun r => ?_⟩
  apply (nondegenerate_iff_associated_separatingLeft _).2
  intro x hx
  funext i
  apply plane
  intro y
  have h := hx (Pi.single i y)
  change QuadraticMap.associated (QuadraticMap.pi (fun _ : Fin r => hyperbolicPlane k))
    x (Pi.single i y) = 0 at h
  simp only [QuadraticMap.Ring.associated_pi, LinearMap.sum_apply, LinearMap.compl₁₂_apply,
    LinearMap.proj_apply] at h
  rw [Fintype.sum_eq_single i, Pi.single_eq_same] at h
  · exact h
  · intro j hj
    simp [Pi.single_eq_of_ne hj]

end Alg01SymmetricWitt.Witt.Coordinates
