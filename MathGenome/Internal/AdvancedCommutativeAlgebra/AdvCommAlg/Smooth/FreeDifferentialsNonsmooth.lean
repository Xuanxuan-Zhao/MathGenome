import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Hypersurfaces
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.FreeDifferentialsNonsmooth
import Mathlib.Algebra.CharP.Lemmas

namespace AdvCommAlg.Smooth.FreeDifferentialsNonsmooth
universe u
noncomputable section
open Specs.AdvCommAlg.Smooth.FreeDifferentialsNonsmooth

lemma coordinate_pow (K : Type u) [CommRing K] (n : ℕ) :
    coordinate K n ^ n = 0 := by
  change AdjoinRoot.mk (Polynomial.X ^ n : Polynomial K) Polynomial.X ^ n = 0
  rw [← map_pow, AdjoinRoot.mk_self]

@[simp] lemma reduction_coordinate (K : Type u) [CommRing K] (p : ℕ) :
    reduction K p (coordinate K (p+1)) = coordinate K p := by
  exact AdjoinRoot.algHomOfDvd_root _ _ _

@[simp] lemma reduction_mk (K : Type u) [CommRing K] (p : ℕ) (q : Polynomial K) :
    reduction K p (AdjoinRoot.mk (Polynomial.X ^ (p+1)) q) =
      AdjoinRoot.mk (Polynomial.X ^ p) q := by
  have h : (reduction K p).comp (AdjoinRoot.mkₐ (Polynomial.X ^ (p+1))) =
      AdjoinRoot.mkₐ (Polynomial.X ^ p) := by
    ext
    exact reduction_coordinate K p
  exact DFunLike.congr_fun h q

lemma reduction_surjective (K : Type u) [CommRing K] (p : ℕ) :
    Function.Surjective (reduction K p) := by
  intro b
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
  exact ⟨AdjoinRoot.mk _ q, reduction_mk K p q⟩

/-- Multiplication by the top power only retains the constant coefficient. -/
lemma top_power_mul (K : Type u) [CommRing K] (p : ℕ) (q : Polynomial K) :
    coordinate K (p+1) ^ p * AdjoinRoot.mk (Polynomial.X ^ (p+1)) q =
      algebraMap K (Truncated K (p+1)) (q.coeff 0) * coordinate K (p+1) ^ p := by
  obtain ⟨h, hh⟩ := Polynomial.X_dvd_sub_C (p := q)
  have hq : q = Polynomial.C (q.coeff 0) + Polynomial.X * h := by
    exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)
  rw [hq, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, mul_add]
  have hz : coordinate K (p+1) ^ p * coordinate K (p+1) = 0 := by
    rw [← pow_succ, coordinate_pow]
  change coordinate K (p+1) ^ p * algebraMap K (Truncated K (p+1)) (q.coeff 0) +
    coordinate K (p+1) ^ p * (coordinate K (p+1) * AdjoinRoot.mk _ h) = _
  rw [← mul_assoc, hz, zero_mul, add_zero, mul_comm]
  simp

/-- This elementary description does not require a characteristic assumption. -/
lemma kernel_elements (K : Type u) [CommRing K] (p : ℕ)
    (z : Truncated K (p+1)) (hz : reduction K p z = 0) :
    ∃ c : K, z = algebraMap K (Truncated K (p+1)) c * coordinate K (p+1) ^ p := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [reduction_mk, AdjoinRoot.mk_eq_zero] at hz
  obtain ⟨h, rfl⟩ := hz
  refine ⟨h.coeff 0, ?_⟩
  rw [map_mul, map_pow, AdjoinRoot.mk_X]
  exact top_power_mul K p h

theorem candidate_images : candidateImages.{u} := by
  intro K _ p _ _ z hz
  have h : reduction K p (z - coordinate K (p+1)) = 0 := by
    rw [map_sub, hz, reduction_coordinate, sub_self]
  obtain ⟨c, hc⟩ := kernel_elements K p _ h
  exact ⟨c, (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)⟩

theorem differential_basis : differentialBasis.{u} := by
  intro K _ p _ _
  let B := Truncated K p
  have hd : Polynomial.derivative (Polynomial.X ^ p : Polynomial K) = 0 := by
    rw [Polynomial.derivative_X_pow, CharP.cast_eq_zero, map_zero, zero_mul]
  let I : Submodule B B := Ideal.span {(AdjoinRoot.mk (Polynomial.X ^ p : Polynomial K)
    (Polynomial.derivative (Polynomial.X ^ p)))}
  have hI : I = ⊥ := by simp [I, hd]
  obtain ⟨e, he⟩ := Differentials.univariate_hypersurface K (Polynomial.X ^ p)
  let c : B ≃ₗ[B] KaehlerDifferential K B := (I.quotEquivOfEqBot hI).symm.trans e
  refine ⟨(Module.Basis.singleton Unit B).map c, ?_⟩
  change c ((Module.Basis.singleton Unit B) ()) = _
  rw [Module.Basis.singleton_apply]
  change e (Ideal.Quotient.mk _ 1) = _
  simpa using he 1

/-- The last nonzero power in the larger truncation. -/
lemma top_power_ne_zero (K : Type u) [Field K] (p : ℕ) :
    coordinate K (p+1) ^ p ≠ 0 := by
  change AdjoinRoot.mk (Polynomial.X ^ (p+1) : Polynomial K) Polynomial.X ^ p ≠ 0
  rw [← map_pow]
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt (Polynomial.monic_X.pow (p+1))
    (pow_ne_zero _ Polynomial.X_ne_zero) (by simp)

theorem candidate_powers : candidatePowers.{u} := by
  intro K _ p _ hp z hz
  have hprime := CharP.char_prime_of_ne_zero K (Nat.ne_of_gt hp)
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨c, rfl⟩ := candidate_images K p hp z hz
  refine ⟨?_, top_power_ne_zero K p⟩
  have he : (Polynomial.X + Polynomial.C c * Polynomial.X ^ p : Polynomial K) ^ p =
      Polynomial.X ^ p + Polynomial.C c ^ p * Polynomial.X ^ (p*p) := by
    rw [add_pow_char, mul_pow, ← pow_mul]
  have hm := congrArg (AdjoinRoot.mk (Polynomial.X ^ (p+1) : Polynomial K)) he
  simp only [map_pow, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hm
  change (coordinate K (p+1) + algebraMap K (Truncated K (p+1)) c *
    coordinate K (p+1) ^ p) ^ p = _ at hm
  rw [hm]
  have hh : p+1 ≤ p*p := by
    calc
      p+1 ≤ p*2 := by omega
      _ ≤ p*p := Nat.mul_le_mul_left p hprime.two_le
  rw [pow_eq_zero_of_le hh (coordinate_pow K (p+1)), mul_zero, add_zero]

lemma kernel_square_zero (K : Type u) [CommRing K] (p : ℕ) (hp : 0 < p) :
    (RingHom.ker (reduction K p)) ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro a ha b hb
  obtain ⟨c, rfl⟩ := kernel_elements K p a ha
  obtain ⟨d, rfl⟩ := kernel_elements K p b hb
  have hz : coordinate K (p+1) ^ (p*2) = 0 :=
    pow_eq_zero_of_le (by omega) (coordinate_pow K (p+1))
  change (algebraMap K (Truncated K (p+1)) c * coordinate K (p+1) ^ p) *
    (algebraMap K (Truncated K (p+1)) d * coordinate K (p+1) ^ p) = 0
  calc
    _ = (algebraMap K (Truncated K (p+1)) c * algebraMap K (Truncated K (p+1)) d) *
        (coordinate K (p+1) ^ p * coordinate K (p+1) ^ p) := by ac_rfl
    _ = 0 := by rw [← pow_two, ← pow_mul, hz, mul_zero]

theorem failure_test : failureTest.{u} := by
  intro K _ p _ hp
  refine ⟨reduction_surjective K p, kernel_square_zero K p hp, ?_⟩
  rintro ⟨f, hf⟩
  have hroot : reduction K p (f (coordinate K p)) = coordinate K p :=
    DFunLike.congr_fun hf (coordinate K p)
  obtain ⟨hpow, hne⟩ := candidate_powers K p hp _ hroot
  apply hne
  rw [← hpow, ← map_pow, coordinate_pow, map_zero]

theorem not_formally_smooth_and_not_smooth : nonsmooth.{u} := by
  intro K _ p _ hp
  have hnot : ¬ Specs.AdvCommAlg.FormalLifting.formallySmoothValue K (Truncated K p) := by
    intro h
    let q := reduction K p
    let N := RingHom.ker q
    have hN : N ^ 2 = ⊥ := (failure_test K p hp).2.1
    let e : (Truncated K (p+1) ⧸ N) ≃ₐ[K] Truncated K p :=
      Ideal.quotientKerAlgEquivOfSurjective (reduction_surjective K p)
    obtain ⟨f, hf⟩ := h N hN e.symm.toAlgHom
    apply (failure_test K p hp).2.2
    refine ⟨f, ?_⟩
    apply DFunLike.ext
    intro x
    have hx := DFunLike.congr_fun hf x
    have he := congrArg e hx
    change e (Ideal.Quotient.mk N (f x)) = e (e.symm x) at he
    rw [AlgEquiv.apply_symm_apply] at he
    change q (f x) = x
    exact he
  exact ⟨hnot, fun hs => hnot ((smooth_iff K (Truncated K p)).mp hs).2⟩

end
end AdvCommAlg.Smooth.FreeDifferentialsNonsmooth
