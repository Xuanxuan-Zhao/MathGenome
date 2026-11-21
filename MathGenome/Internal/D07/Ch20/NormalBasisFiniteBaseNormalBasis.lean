import MathGenome.Internal.Specs.D07.Ch20.NormalBasisFiniteBaseNormalBasis
import Mathlib.FieldTheory.Galois.NormalBasis

/-!
The finite-base branch of K07.20.normal_basis.

Mathlib's `minpoly_frobeniusAlgHom` proves the minimal-polynomial formula
from independence of the first n Frobenius embeddings. Its finite-field
normal-basis argument uses a vector with the same polynomial annihilator
as the operator, over the PID K[X]; it does not divide by n. We transport
its independent orbit along the enumeration by Frobenius powers and give
the actual ordered basis, as well as the cyclic span and characteristic
polynomial asserted in the source proof.
-/

noncomputable section
universe u v
namespace D07.Ch20.NormalBasisFiniteBaseNormalBasis

open Polynomial Module
open Specs.D07.Ch20.NormalBasisFiniteBaseNormalBasis

theorem finite_base_normal_basis : FiniteBaseNormalBasis.{u, v} := by
  intro K L _ _ _ _ _ q n hq hn
  subst q
  subst n
  let := Fintype.ofFinite K
  let T := frobeniusOperator K L
  have hmin : minpoly K T = X ^ finrank K L - 1 := by
    exact FiniteField.minpoly_frobeniusAlgHom K L
  have hchar : T.charpoly = X ^ finrank K L - 1 := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (Polynomial.monic_X_pow_sub_C 1 finrank_pos.ne') T.charpoly_monic
    · rw [Polynomial.C_1, ← hmin]
      exact LinearMap.minpoly_dvd_charpoly T
    · rw [LinearMap.charpoly_natDegree, Polynomial.natDegree_X_pow_sub_C]
  have hpow (j : ℕ) (x : L) : (T ^ j) x = x ^ (Nat.card K ^ j) := by
    rw [Module.End.coe_pow]
    change (fun x : L => x ^ Fintype.card K)^[j] x = _
    rw [pow_iterate, Nat.card_eq_fintype_card]
  obtain ⟨a, ha⟩ := exists_linearIndependent_algEquiv_apply K L
  have hLI : LinearIndependent K (fun i : Fin (finrank K L) => (T ^ (i : ℕ)) a) := by
    have h := ha.comp (fun i : Fin (finrank K L) =>
      FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ (i : ℕ))
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L).injective
    convert h using 1
    ext i
    change (T ^ i.val) a =
      (FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ i.val) a
    rw [hpow, AlgEquiv.coe_pow]
    change _ = (fun x : L => x ^ Fintype.card K)^[i.val] a
    rw [pow_iterate, Nat.card_eq_fintype_card]
  let : Nonempty (Fin (finrank K L)) := ⟨⟨0, finrank_pos⟩⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hLI (by simp)
  have hb (i : Fin (finrank K L)) : b i = (T ^ (i : ℕ)) a := by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hcyc : Submodule.span K (Set.range (fun j : ℕ => (T ^ j) a)) = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.val, (hb i).symm⟩
  refine ⟨finrank_pos, ?_, hmin, hchar, a, b, hcyc, hb, ?_⟩
  · intro x
    exact hpow 1 x |>.trans (by simp)
  · intro i
    exact (hb i).trans (hpow i.val a)

end D07.Ch20.NormalBasisFiniteBaseNormalBasis
