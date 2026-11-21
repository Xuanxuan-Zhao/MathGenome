import MathGenome.Internal.Specs.D05.M15.TensorDerivation.LieDuality
import MathGenome.Internal.D05.M15.TensorDerivation
import MathGenome.Internal.D05.M15.ExteriorDerivation
import MathGenome.Internal.D05.M15.SymmetricDerivation
import MathGenome.Internal.D05.M15.ExteriorPairing
import MathGenome.Internal.D05.M15.SymmetricBasis.PerfectPairing
import MathGenome.Internal.D05.M15.TensorPairing

noncomputable section
namespace D05.M15.TensorDerivation.LieDuality
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

theorem tensor_add : Specs.D05.M15.TensorDerivation.LieDuality.tensor_add :=
  @D05.M15.TensorDerivation.induced_add

theorem tensor_smul : Specs.D05.M15.TensorDerivation.LieDuality.tensor_smul :=
  @D05.M15.TensorDerivation.induced_smul

theorem tensor_commutator : Specs.D05.M15.TensorDerivation.LieDuality.tensor_commutator :=
  @D05.M15.TensorDerivation.induced_commutator

theorem tensor_power_commutator : Specs.D05.M15.TensorDerivation.LieDuality.tensor_power_commutator :=
  @D05.M15.TensorDerivation.onPower_commutator

theorem tensor_duality : Specs.D05.M15.TensorDerivation.LieDuality.tensor_duality :=
  @D05.M15.TensorDerivation.tensor_duality

theorem tensor_degree_zero : Specs.D05.M15.TensorDerivation.LieDuality.tensor_degree_zero :=
  @D05.M15.TensorDerivation.onPower_zero

/-- The two mixed Leibniz terms cancel in an arbitrary associative algebra. -/
theorem commutator_rule {R : Type*} [Ring R] [Algebra K R]
    (D E : R →ₗ[K] R)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hE : ∀ x y, E (x * y) = E x * y + x * E y) (x y : R) :
    (D.comp E - E.comp D) (x * y) =
      (D.comp E - E.comp D) x * y + x * (D.comp E - E.comp D) y := by
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, hD, hE,
    map_add, sub_mul, mul_sub]
  abel

theorem exterior_add : Specs.D05.M15.TensorDerivation.LieDuality.exterior_add := by
  intro K V _ _ _ A B
  apply D05.M15.ExteriorDerivation.derivation_ext
  · exact D05.M15.ExteriorDerivation.induced_leibniz _
  · intro x y
    simp only [LinearMap.add_apply, D05.M15.ExteriorDerivation.induced_mul, add_mul, mul_add]
    abel
  · intro v
    simp [D05.M15.ExteriorDerivation.induced_generator]

theorem exterior_smul : Specs.D05.M15.TensorDerivation.LieDuality.exterior_smul := by
  intro K V _ _ _ a A
  apply D05.M15.ExteriorDerivation.derivation_ext
  · exact D05.M15.ExteriorDerivation.induced_leibniz _
  · intro x y
    simp only [LinearMap.smul_apply, D05.M15.ExteriorDerivation.induced_mul,
      smul_add, smul_mul_assoc, mul_smul_comm]
  · intro v
    simp [D05.M15.ExteriorDerivation.induced_generator]

theorem exterior_commutator : Specs.D05.M15.TensorDerivation.LieDuality.exterior_commutator := by
  intro K V _ _ _ A B
  apply D05.M15.ExteriorDerivation.derivation_ext
  · exact commutator_rule _ _ (D05.M15.ExteriorDerivation.induced_mul A)
      (D05.M15.ExteriorDerivation.induced_mul B)
  · exact D05.M15.ExteriorDerivation.induced_leibniz _
  · intro v
    simp [D05.M15.ExteriorDerivation.induced_generator]

theorem symmetric_add : Specs.D05.M15.TensorDerivation.LieDuality.symmetric_add := by
  intro K V _ _ _ A B
  apply D05.M15.SymmetricDerivation.derivation_ext
  · exact D05.M15.SymmetricDerivation.induced_mul _
  · intro x y
    simp only [LinearMap.add_apply, D05.M15.SymmetricDerivation.induced_mul, add_mul, mul_add]
    abel
  · intro v
    simp [D05.M15.SymmetricDerivation.induced_generator]

theorem symmetric_smul : Specs.D05.M15.TensorDerivation.LieDuality.symmetric_smul := by
  intro K V _ _ _ a A
  apply D05.M15.SymmetricDerivation.derivation_ext
  · exact D05.M15.SymmetricDerivation.induced_mul _
  · intro x y
    simp only [LinearMap.smul_apply, D05.M15.SymmetricDerivation.induced_mul,
      smul_add, smul_mul_assoc, mul_smul_comm]
  · intro v
    simp [D05.M15.SymmetricDerivation.induced_generator]

theorem symmetric_commutator : Specs.D05.M15.TensorDerivation.LieDuality.symmetric_commutator := by
  intro K V _ _ _ A B
  apply D05.M15.SymmetricDerivation.derivation_ext
  · exact commutator_rule _ _ (D05.M15.SymmetricDerivation.induced_mul A)
      (D05.M15.SymmetricDerivation.induced_mul B)
  · exact D05.M15.SymmetricDerivation.induced_mul _
  · intro v
    simp [D05.M15.SymmetricDerivation.induced_generator]

/-- For each permutation the changed row and changed column correspond under
that permutation. The weight can be either its sign or 1. -/
theorem weighted_slot_duality (A : V →ₗ[K] V) (p : ℕ)
    (w : Equiv.Perm (Fin p) → K) (φ : Fin p → Module.Dual K V) (x : Fin p → V) :
    (∑ j : Fin p, ∑ σ : Equiv.Perm (Fin p), w σ *
      ∏ i, (Function.update φ j (A.dualMap (φ j))) i (x (σ i))) =
    ∑ j : Fin p, ∑ σ : Equiv.Perm (Fin p), w σ *
      ∏ i, φ i ((Function.update x j (A (x j))) (σ i)) := by
  classical
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Fintype.sum_equiv σ
  intro j
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : i = j
  · subst i
    simp [LinearMap.dualMap_apply]
  · simp [Function.update_of_ne h, Function.update_of_ne (σ.injective.ne h)]

set_option maxHeartbeats 800000 in
/-- Determinant version of the slot calculation. -/
theorem determinant_slot_duality (A : V →ₗ[K] V) (p : ℕ)
    (φ : Fin p → Module.Dual K V) (x : Fin p → V) :
    (∑ j : Fin p, Matrix.det (fun i k => (Function.update φ j (A.dualMap (φ j))) i (x k))) =
    ∑ j : Fin p, Matrix.det (fun i k => φ i ((Function.update x j (A (x j))) k)) := by
  have hdet (M : Matrix (Fin p) (Fin p) K) :
      M.det = ∑ σ : Equiv.Perm (Fin p), ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, M i (σ i) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  calc
    _ = ∑ j : Fin p, ∑ σ : Equiv.Perm (Fin p), ((Equiv.Perm.sign σ : ℤ) : K) *
        ∏ i, (Function.update φ j (A.dualMap (φ j))) i (x (σ i)) :=
      Finset.sum_congr rfl (fun j _ => hdet (Matrix.of (fun i k =>
        (Function.update φ j (A.dualMap (φ j))) i (x k))))
    _ = ∑ j : Fin p, ∑ σ : Equiv.Perm (Fin p), ((Equiv.Perm.sign σ : ℤ) : K) *
        ∏ i, φ i ((Function.update x j (A (x j))) (σ i)) :=
      weighted_slot_duality A p _ φ x
    _ = _ := Finset.sum_congr rfl (fun j _ => (hdet (Matrix.of (fun i k =>
        φ i ((Function.update x j (A (x j))) k)))).symm)

/-- Restricting the established algebra derivation gives the same slot sum
in the actual degree-p exterior submodule. -/
theorem exterior_restriction_slots (A : V →ₗ[K] V) (p : ℕ)
    (D : (⋀[K]^p V) →ₗ[K] (⋀[K]^p V))
    (hD : ∀ x, (D x : _root_.ExteriorAlgebra K V) = D05.M15.ExteriorDerivation.induced A x)
    (x : Fin p → V) :
    D (exteriorPower.ιMulti K p x) =
      ∑ j : Fin p, exteriorPower.ιMulti K p (Function.update x j (A (x j))) := by
  apply Subtype.ext
  rw [hD]
  change D05.M15.ExteriorDerivation.induced A (_root_.ExteriorAlgebra.ιMulti K p x) = _
  rw [D05.M15.ExteriorDerivation.induced_word, Submodule.coe_sum]
  rfl

theorem exterior_duality : Specs.D05.M15.TensorDerivation.LieDuality.exterior_duality := by
  intro K V _ _ _ A p
  obtain ⟨D, hD, _⟩ := D05.M15.ExteriorDerivation.power_restriction A p
  obtain ⟨E, hE, _⟩ := D05.M15.ExteriorDerivation.power_restriction A.dualMap p
  refine ⟨D, E, hD, hE, ?_⟩
  have h : (D05.M15.ExteriorPairing.pairing K V p).comp E =
      D.dualMap.comp (D05.M15.ExteriorPairing.pairing K V p) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro φ
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    change D05.M15.ExteriorPairing.pairing K V p (E (exteriorPower.ιMulti K p φ))
      (exteriorPower.ιMulti K p x) =
      D05.M15.ExteriorPairing.pairing K V p (exteriorPower.ιMulti K p φ)
        (D (exteriorPower.ιMulti K p x))
    rw [exterior_restriction_slots _ _ E hE, exterior_restriction_slots _ _ D hD]
    simp only [map_sum, LinearMap.sum_apply]
    calc
      _ = ∑ j : Fin p, Matrix.det (fun i k =>
          (Function.update φ j (A.dualMap (φ j))) i (x k)) :=
        Finset.sum_congr rfl (fun j _ => D05.M15.ExteriorPairing.elementary p _ _)
      _ = ∑ j : Fin p, Matrix.det (fun i k =>
          φ i ((Function.update x j (A (x j))) k)) := determinant_slot_duality A p φ x
      _ = _ := Finset.sum_congr rfl (fun j _ => (D05.M15.ExteriorPairing.elementary p _ _).symm)
  exact fun α x => LinearMap.congr_fun (LinearMap.congr_fun h α) x

open Specs.D05.M15.Symmetric
open Specs.D05.M15.SymmetricBasis
open Specs.D05.M15.SymmetricBasis.PerfectPairing

/-- Conjugate the restricted algebra operator through the already proved
identification of the quotient power with the homogeneous submodule. -/
theorem symmetric_restriction_exists (A : V →ₗ[K] V) (p : ℕ) :
    ∃ D : symmetricPower K V p →ₗ[K] symmetricPower K V p,
      ∀ x, powerInclusion (K := K) (V := V) p (D x) =
        D05.M15.SymmetricDerivation.induced A (powerInclusion (K := K) (V := V) p x) := by
  obtain ⟨F, hF⟩ := D05.M15.Symmetric.power_equiv_homogeneous (K := K) (V := V) p
  have hinc : (LinearMap.range (homogeneousMap K V p)).subtype.comp F.toLinearMap =
      powerInclusion (K := K) (V := V) p := by
    apply D05.M15.SymmetricBasis.PerfectPairing.power_ext
    intro x
    exact (hF x).trans ((D05.M15.Symmetric.homogeneousMap_tprod p x).trans
      (D05.M15.SymmetricBasis.inclusion_elementary p x).symm)
  let dRange := ((D05.M15.SymmetricDerivation.induced A).comp
    (LinearMap.range (homogeneousMap K V p)).subtype).codRestrict
      (LinearMap.range (homogeneousMap K V p))
      (fun x => D05.M15.SymmetricDerivation.induced_degree A p x x.property)
  let D := F.symm.toLinearMap.comp (dRange.comp F.toLinearMap)
  refine ⟨D, ?_⟩
  intro x
  rw [← LinearMap.congr_fun hinc (D x), ← LinearMap.congr_fun hinc x]
  change (F (F.symm (dRange (F x))) : _root_.SymmetricAlgebra K V) =
    D05.M15.SymmetricDerivation.induced A (F x)
  rw [F.apply_symm_apply]
  rfl

theorem symmetric_restriction_slots (A : V →ₗ[K] V) (p : ℕ)
    (D : symmetricPower K V p →ₗ[K] symmetricPower K V p)
    (hD : ∀ x, powerInclusion (K := K) (V := V) p (D x) =
      D05.M15.SymmetricDerivation.induced A (powerInclusion (K := K) (V := V) p x))
    (x : Fin p → V) :
    D (elementary K V p x) =
      ∑ j : Fin p, elementary K V p (Function.update x j (A (x j))) := by
  apply D05.M15.SymmetricBasis.inclusion_injective p
  rw [hD, map_sum]
  have he (y : Fin p → V) : powerInclusion (K := K) (V := V) p (elementary K V p y) =
      D05.M15.SymmetricDerivation.word p y :=
    D05.M15.SymmetricBasis.inclusion_elementary p y
  simp only [he]
  exact D05.M15.SymmetricDerivation.induced_word A p x

theorem symmetric_duality : Specs.D05.M15.TensorDerivation.LieDuality.symmetric_duality := by
  intro K V _ _ _ A p
  obtain ⟨D, hD⟩ := symmetric_restriction_exists A p
  obtain ⟨E, hE⟩ := symmetric_restriction_exists A.dualMap p
  refine ⟨D, E, hD, hE, ?_⟩
  intro P hP
  have h : P.comp E = D.dualMap.comp P := by
    apply D05.M15.SymmetricBasis.PerfectPairing.power_ext
    intro φ
    apply D05.M15.SymmetricBasis.PerfectPairing.power_ext
    intro x
    change P (E (elementary K (Module.Dual K V) p φ)) (elementary K V p x) =
      P (elementary K (Module.Dual K V) p φ) (D (elementary K V p x))
    rw [symmetric_restriction_slots _ _ E hE, symmetric_restriction_slots _ _ D hD]
    simp only [map_sum, LinearMap.sum_apply]
    calc
      _ = ∑ j : Fin p, permanent (Function.update φ j (A.dualMap (φ j))) x :=
        Finset.sum_congr rfl (fun j _ => hP _ _)
      _ = ∑ j : Fin p, permanent φ (Function.update x j (A (x j))) := by
        simpa only [one_mul, permanent] using weighted_slot_duality A p (fun _ => 1) φ x
      _ = _ := Finset.sum_congr rfl (fun j _ => (hP _ _).symm)
  exact fun α x => LinearMap.congr_fun (LinearMap.congr_fun h α) x

end D05.M15.TensorDerivation.LieDuality
