import MathGenome.Internal.Specs.D05.M10.JordanChains
import MathGenome.Internal.D05.M10.Rational
import MathGenome.Internal.D05.Foundations.QuotientBasisUnits
import Mathlib.Data.Fin.Rev

noncomputable section
open Polynomial
open scoped BigOperators

namespace D05.M10.JordanChains
open Specs.D05.M10.Rational

variable {K : Type*} [Field K]

/-- A monic divisor of a power of X has no other irreducible factors. -/
lemma monic_divisor_X_pow (d : K[X]) (hd : d.Monic) {s : ℕ}
    (hdiv : d ∣ X ^ s) : d = X ^ d.natDegree := by
  obtain ⟨a, _, ha⟩ := (dvd_prime_pow (prime_X (R := K)) s).mp hdiv
  have heq : d = X ^ a := Polynomial.eq_of_monic_of_associated hd (monic_X.pow a) ha
  simp only [heq, natDegree_X_pow]

theorem quotient_chain_basis : Specs.D05.M10.JordanChains.quotient_chain_basis := by
  intro K _ a ha
  obtain ⟨b, hb⟩ := Foundations.QuotientBasisUnits.residueBasis K (X ^ a) (monic_X.pow a)
  let e : Fin (X ^ a : K[X]).natDegree ≃ Fin a :=
    (finCongr (natDegree_X_pow a)).trans Fin.revPerm
  have he (j : Fin a) : (e.symm j).val = a - 1 - j.val := by
    simp [e, Nat.sub_sub, Nat.add_comm]
  have hbj (j : Fin a) : (b.reindex e) j =
      AdjoinRoot.mk (X ^ a : K[X]) (X ^ (a - 1 - j.val)) := by
    rw [Module.Basis.reindex_apply, hb, he]
  refine ⟨b.reindex e, hbj, ?_, ?_⟩
  · intro j hj
    rw [hbj]
    change AdjoinRoot.mk (X ^ a : K[X]) X *
      AdjoinRoot.mk (X ^ a : K[X]) (X ^ (a - 1 - j.val)) = 0
    rw [← map_mul, ← pow_succ', hj]
    have he : a - 1 - 0 + 1 = a := by omega
    rw [he]
    exact AdjoinRoot.mk_self
  · intro j k hjk
    rw [hbj, hbj]
    change AdjoinRoot.mk (X ^ a : K[X]) X *
      AdjoinRoot.mk (X ^ a : K[X]) (X ^ (a - 1 - j.val)) =
      AdjoinRoot.mk (X ^ a : K[X]) (X ^ (a - 1 - k.val))
    rw [← map_mul, ← pow_succ']
    congr 2
    have hj := j.isLt
    omega

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Nilpotence forces each actual cyclic quotient modulus to divide a
power of X. Evaluate on a tuple of unit residue classes, using surjectivity
of the module equivalence rather than assuming an annihilator certificate. -/
lemma quotient_modulus_dvd_X_pow (N : Module.End K V) {s r : ℕ}
    (hs : N ^ s = 0) (d : Fin r → K[X])
    (e : Module.AEval' N ≃ₗ[K[X]] (∀ i, Residue (d i))) (i : Fin r) :
    d i ∣ X ^ s := by
  let z : ∀ i, Residue (d i) := fun _ => Submodule.Quotient.mk (1 : K[X])
  have hz : (X ^ s : K[X]) • e.symm z = 0 := by
    apply (Module.AEval'.of N).symm.injective
    simp only [Module.AEval.of_symm_smul, aeval_X_pow, hs, zero_smul, map_zero]
  have h := congrArg (fun y => e y i) hz
  rw [map_smul, e.apply_symm_apply, map_zero] at h
  change (X ^ s : K[X]) • (Submodule.Quotient.mk (1 : K[X]) : Residue (d i)) = 0 at h
  change AdjoinRoot.mk (d i) (X ^ s * 1) = 0 at h
  rw [mul_one] at h
  exact AdjoinRoot.mk_eq_zero.mp h

theorem jordan_chain_basis : Specs.D05.M10.JordanChains.jordan_chain_basis := by
  intro K V _ _ _ _ N hN
  classical
  obtain ⟨s, hs⟩ := hN
  obtain ⟨r, d, hm, hp, _hd, ⟨e⟩, _⟩ := Rational.rational_form N
  have hd (i : Fin r) : d i = X ^ (d i).natDegree :=
    monic_divisor_X_pow (d i) (hm i) (quotient_modulus_dvd_X_pow N hs d e i)
  let a : Fin r → ℕ := fun i => (d i).natDegree
  have heq : d = fun i => (X ^ a i : K[X]) := funext hd
  rw [heq] at e
  choose B hB hzero hstep using fun i => quotient_chain_basis (K := K) (a i) (hp i)
  let E : (∀ i, AdjoinRoot (X ^ a i : K[X])) ≃ₗ[K] V :=
    (e.symm.restrictScalars K).trans (Module.AEval'.of N).symm
  let b := (Pi.basis B).map E
  have hN (z : ∀ i, AdjoinRoot (X ^ a i : K[X])) :
      N (E z) = E (fun i => AdjoinRoot.root (X ^ a i : K[X]) * z i) := by
    have heX := e.symm.map_smul (X : K[X]) z
    change e.symm (fun i => AdjoinRoot.root (X ^ a i : K[X]) * z i) =
      (X : K[X]) • e.symm z at heX
    change N ((Module.AEval'.of N).symm (e.symm z)) =
      (Module.AEval'.of N).symm (e.symm
        (fun i => AdjoinRoot.root (X ^ a i : K[X]) * z i))
    rw [heX, Module.AEval'.of_symm_X_smul]
  refine ⟨r, a, hp, b, ?_, ?_, ?_⟩
  · intro i j hj
    change N (E ((Pi.basis B) ⟨i, j⟩)) = 0
    rw [hN, Pi.basis_apply, ← E.map_zero]
    congr 1
    funext k
    by_cases hk : k = i
    · subst k
      simp only [Pi.single_eq_same, Pi.zero_apply]
      exact hzero i j hj
    · simp [Pi.single_eq_of_ne hk]
  · intro i j k hjk
    change N (E ((Pi.basis B) ⟨i, j⟩)) = E ((Pi.basis B) ⟨i, k⟩)
    rw [hN, Pi.basis_apply, Pi.basis_apply]
    congr 1
    funext l
    by_cases hl : l = i
    · subst l
      simp only [Pi.single_eq_same]
      exact hstep i j k hjk
    · simp [Pi.single_eq_of_ne hl]
  · simpa using (Module.finrank_eq_card_basis b).symm

theorem zero_space : Specs.D05.M10.JordanChains.zero_space := by
  intro K V _ _ _ _ N hV
  refine ⟨basisOfFinrankZero hV, ?_⟩
  rintro ⟨i, _⟩
  exact Fin.elim0 i

end D05.M10.JordanChains
