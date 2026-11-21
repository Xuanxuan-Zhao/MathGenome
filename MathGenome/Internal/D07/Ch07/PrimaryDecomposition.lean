import MathGenome.Internal.Specs.D07.Ch07.PrimaryDecomposition
import MathGenome.Internal.D07.Ch07.PrimarySubgroups
import Mathlib.GroupTheory.NoncommPiCoprod

namespace D07.Ch07.PrimaryDecomposition

universe u v
open scoped BigOperators
open Specs.D07.Ch07.PrimaryDecomposition

theorem primary_cardinality (A : Type u) [AddCommGroup A] [Finite A]
    (p : ℕ) (hp : p.Prime) :
    Nat.card (Primary A p) = p ^ (Nat.card A).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS, _⟩ := D07.Ch07.PrimarySubgroups.primary_unique_sylow A p hp
  have hcard := S.card_eq_multiplicity
  change Nat.card S.toSubgroup = _ at hcard
  rw [hS] at hcard
  exact hcard

theorem canonical_decomposition : CanonicalDecomposition.{u} := by
  intro A _ _
  classical
  let H : PrimeDivisors A → AddSubgroup A := fun p => Primary A p.val
  let (p : PrimeDivisors A) : Fintype (H p) := Fintype.ofFinite (H p)
  have hcomm : Pairwise fun p q : PrimeDivisors A =>
      ∀ x y : A, x ∈ H p → y ∈ H q → AddCommute x y := by
    intro _ _ _ x y _ _
    exact AddCommute.all x y
  have hind : iSupIndep H := by
    apply AddSubgroup.independent_of_coprime_order hcomm
    intro p q hpq
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rw [primary_cardinality A p.val (Nat.prime_of_mem_primeFactors p.prop),
      primary_cardinality A q.val (Nat.prime_of_mem_primeFactors q.prop)]
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors p.prop)
      (Nat.prime_of_mem_primeFactors q.prop) (fun h => hpq (Subtype.ext h))
  have hcard : Nat.card ((p : PrimeDivisors A) → H p) = Nat.card A := by
    rw [Nat.card_pi]
    calc
      (∏ p : PrimeDivisors A, Nat.card (H p)) =
          ∏ p : PrimeDivisors A, p.val ^ (Nat.card A).factorization p.val := by
        apply Finset.prod_congr rfl
        intro p _
        exact primary_cardinality A p.val (Nat.prime_of_mem_primeFactors p.prop)
      _ = Nat.card A := by
        simpa only [PrimeDivisors, Finset.univ_eq_attach, Finsupp.prod_attach_index] using
          (Nat.prod_primeFactors_pow_factorization (Nat.card_pos (α := A)).ne').symm
  have hbij : Function.Bijective (AddSubgroup.noncommPiCoprod hcomm) :=
    (Nat.bijective_iff_injective_and_card _).mpr
      ⟨AddSubgroup.injective_noncommPiCoprod_of_iSupIndep hind, hcard⟩
  refine ⟨AddEquiv.ofBijective (AddSubgroup.noncommPiCoprod hcomm) hbij, ?_⟩
  intro x
  change AddSubgroup.noncommPiCoprod hcomm x = _
  rw [AddSubgroup.noncommPiCoprod_apply, Finset.noncommSum_eq_sum]

theorem primary_intrinsic : PrimaryIntrinsic.{u, v} := by
  intro A B _ _ e p _hp
  ext b
  constructor
  · rintro ⟨a, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  · rintro ⟨k, hk⟩
    refine ⟨e.symm b, ⟨k, ?_⟩, e.apply_symm_apply b⟩
    rw [← map_nsmul, hk, map_zero]

end D07.Ch07.PrimaryDecomposition
