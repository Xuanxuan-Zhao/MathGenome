import MathGenome.Internal.Specs.D07.Ch07.PrimaryCyclicExistence
import MathGenome.Internal.D07.Ch07.PrimaryDecomposition
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Index
import Batteries.Tactic.OpenPrivate

/-!
Existence of cyclic prime-power factors. The library's PID-based finite
abelian structure theorem initially permits zero exponents. Delete those
coordinates, identify finite sums with finite products, and reindex by Fin.
For a p-group, Lagrange forces the prime of each remaining factor to be p.
Finally use the canonical primary decomposition to combine the factors.
-/
noncomputable section
namespace D07.Ch07.PrimaryCyclicExistence

universe u
open Specs.D07.Ch07.PrimaryCyclicExistence
open Specs.D07.Ch07.PrimaryDecomposition
open scoped DirectSum
open private directSumNeZeroMulEquiv from Mathlib.GroupTheory.FiniteAbelian.Basic

theorem finite_cyclic_existence : FiniteCyclicExistence.{u} := by
  intro A _ _
  classical
  obtain ⟨ι, fι, p, hp, e, ⟨E⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite A
  let J := {i : ι // e i ≠ 0}
  let q : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let F := (directSumNeZeroMulEquiv ι p e).symm
  let G := DirectSum.addEquivProd (fun i : J => ZMod (p i.val ^ e i.val))
  let H := (RingEquiv.piCongrLeft (fun i : J => ZMod (p i.val ^ e i.val)) q).symm
  refine ⟨Fintype.card J, fun i => p (q i).val, fun i => e (q i).val, ?_,
    ⟨E.trans (F.trans (G.trans H.toAddEquiv))⟩⟩
  intro i
  exact ⟨hp _, Nat.pos_of_ne_zero (q i).property⟩

theorem primary_cyclic_existence : PGroupDecomposition.{u} := by
  intro A _ _ p hp ⟨a, ha⟩
  classical
  obtain ⟨r, q, e, hqe, ⟨E⟩⟩ := finite_cyclic_existence A
  have hprime : ∀ i, q i = p := by
    intro i
    have hsurj : Function.Surjective
        ((Pi.evalAddMonoidHom (fun j : Fin r => ZMod (q j ^ e j)) i).comp
          E.toAddMonoidHom) := by
      intro x
      exact ⟨E.symm (Pi.single i x), by simp⟩
    have hd := AddSubgroup.card_dvd_of_surjective hsurj
    have hq0 : q i ^ e i ≠ 0 := pow_ne_zero _ (hqe i).1.ne_zero
    have : NeZero (q i ^ e i) := ⟨hq0⟩
    rw [Nat.card_eq_fintype_card, ZMod.card, ha] at hd
    exact Nat.prime_eq_prime_of_dvd_pow (hqe i).1 hp
      ((dvd_pow_self _ (Nat.ne_of_gt (hqe i).2)).trans hd)
  refine ⟨r, e, fun i => (hqe i).2, ?_⟩
  exact ⟨E.trans (AddEquiv.piCongrRight (fun i =>
    (ZMod.ringEquivCongr (congrArg (fun n => n ^ e i) (hprime i))).toAddEquiv))⟩

theorem combined_primary_cyclic_existence : CombinedPrimaryCyclicExistence.{u} := by
  intro A _ _
  classical
  have hex : ∀ p : PrimeDivisors A,
      ∃ (r : ℕ) (e : Fin r → ℕ), (∀ i, 0 < e i) ∧
        Nonempty (Primary A p.val ≃+ ((i : Fin r) → ZMod (p.val ^ e i))) := by
    intro p
    exact primary_cyclic_existence (Primary A p.val) p.val
      (Nat.prime_of_mem_primeFactors p.property)
      ⟨(Nat.card A).factorization p.val,
        D07.Ch07.PrimaryDecomposition.primary_cardinality A p.val
          (Nat.prime_of_mem_primeFactors p.property)⟩
  choose r e he E using hex
  obtain ⟨F, _⟩ := D07.Ch07.PrimaryDecomposition.canonical_decomposition A
  exact ⟨r, e, he, E, ⟨F.symm.trans (AddEquiv.piCongrRight (fun p => (E p).some))⟩⟩

theorem trivial_empty_product : TrivialEmptyProduct.{u} := by
  intro A _ _ p _
  exact ⟨{ toFun := fun _ i => Fin.elim0 i
           invFun := fun _ => 0
           left_inv := fun _ => Subsingleton.elim _ _
           right_inv := fun _ => Subsingleton.elim _ _
           map_add' := fun _ _ => Subsingleton.elim _ _ }⟩

end D07.Ch07.PrimaryCyclicExistence
