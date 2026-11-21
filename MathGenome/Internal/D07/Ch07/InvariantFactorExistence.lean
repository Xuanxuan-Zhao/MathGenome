import MathGenome.Internal.Specs.D07.Ch07.InvariantFactorExistence
import MathGenome.Internal.D07.Ch07.ClassificationDataConversion
import MathGenome.Internal.D07.Ch07.PrimaryCyclicExistence
import Mathlib.Data.Fin.Tuple.Sort

/-!
Invariant factors are obtained from the proved primary cyclic decomposition.
We retain each prime label and every positive exponent, sort each primary
row by an explicit permutation, and bridge its finite product to the
canonical elementary-data model. The upstream recombination theorem then
supplies both the increasing divisibility chain and the CRT isomorphism.
-/
noncomputable section
namespace D07.Ch07.InvariantFactorExistence

universe u
open D07.Ch07.ClassificationDataConversion
open Specs.D07.Ch07.PrimaryDecomposition

/-- Sorting an exponent tuple only reorders its cyclic factors. -/
def sortedFactorsEquiv {n : ℕ} (p : ℕ) (e : Fin n → ℕ) :
    ((i : Fin n) → ZMod (p ^ e i)) ≃+
      ((i : Fin n) → ZMod (p ^ (e ∘ Tuple.sort e) i)) :=
  (RingEquiv.piCongrLeft (fun i => ZMod (p ^ e i)) (Tuple.sort e)).symm.toAddEquiv

/-- The sorted multiset row is exactly the sorted tuple, with multiplicities. -/
theorem sorted_row {n : ℕ} (e : Fin n → ℕ) :
    ((List.ofFn e : Multiset ℕ).sort (· ≤ ·)) =
      List.ofFn (e ∘ Tuple.sort e) := by
  have hp := (Tuple.sort e).ofFn_comp_perm e
  rw [← Multiset.coe_eq_coe.mpr hp, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (Tuple.monotone_sort e).sortedLE_ofFn.pairwise

/-- Present a tuple of cyclic factors using the corresponding list. -/
def ofFnFactorsEquiv {n : ℕ} (p : ℕ) (e : Fin n → ℕ) :
    ((i : Fin n) → ZMod (p ^ e i)) ≃+
      ((i : Fin (List.ofFn e).length) → ZMod (p ^ (List.ofFn e).getD i 0)) := by
  let hlen : (List.ofFn e).length = n := List.length_ofFn
  refine (AddEquiv.piCongrRight (fun i : Fin n =>
    (ZMod.ringEquivCongr ?_).toAddEquiv)).trans
      (finPiCongr (fun i => ZMod (p ^ (List.ofFn e).getD i 0)) hlen).symm
  congr 1
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- Assemble the primary cyclic decompositions in the canonical elementary-data model. -/
theorem elementary_model (A : Type u) [AddCommGroup A] [Finite A] :
    ∃ E : ElementaryData, IsElementary E ∧ Nonempty (A ≃+ ElementaryGroup E) := by
  classical
  obtain ⟨r, e, he, hprimary, ⟨F⟩⟩ :=
    D07.Ch07.PrimaryCyclicExistence.combined_primary_cyclic_existence A
  have hr : ∀ p : PrimeDivisors A, r p ≠ 0 := by
    intro p hz
    have hc : Nat.card (Primary A p.val) = 1 := by
      rw [Nat.card_congr (hprimary p).some.toEquiv]
      have : IsEmpty (Fin (r p)) := ⟨fun i => by have := i.isLt; omega⟩
      exact Nat.card_unique
    have hp := Nat.prime_of_mem_primeFactors p.property
    rw [D07.Ch07.PrimaryDecomposition.primary_cardinality A p.val hp] at hc
    have ha : (Nat.card A).factorization p.val ≠ 0 :=
      Finsupp.mem_support_iff.mp p.property
    exact (Nat.one_lt_pow ha hp.one_lt).ne' hc
  let E : ElementaryData := Finsupp.onFinset (PrimeDivisors A)
    (fun p => if h : p ∈ PrimeDivisors A then
      (List.ofFn (e ⟨p, h⟩) : Multiset ℕ) else 0)
    (by intro p hp; by_contra hn; simp [hn] at hp)
  have hEp (p : PrimeDivisors A) : E p.val = (List.ofFn (e p) : Multiset ℕ) := by
    simp only [E, Finsupp.onFinset_apply, dite_eq_left p.property]
  have hsupport : E.support = PrimeDivisors A := by
    ext p
    rw [Finsupp.mem_support_iff]
    by_cases hp : p ∈ PrimeDivisors A
    · simp only [hp, iff_true]
      have hh := congrArg Multiset.card (hEp ⟨p, hp⟩)
      intro hz
      rw [hz] at hh
      simp only [Multiset.card_zero, Multiset.coe_card, List.length_ofFn] at hh
      exact hr ⟨p, hp⟩ hh.symm
    · have hz : E p = 0 := by
        change (if h : p ∈ PrimeDivisors A then
          (List.ofFn (e ⟨p, h⟩) : Multiset ℕ) else 0) = 0
        exact dite_eq_right hp
      rw [hz]
      simp only [ne_self_iff_false, hp]
  have hnorm : IsElementary E := by
    intro p a ha
    have hp : p ∈ PrimeDivisors A := by
      rw [← hsupport, Finsupp.mem_support_iff]
      intro hz
      simp [hz] at ha
    rw [hEp ⟨p, hp⟩] at ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp ha)
    exact ⟨Nat.prime_of_mem_primeFactors hp, he ⟨p, hp⟩ i⟩
  have hrow (p : PrimeDivisors A) :
      row E p.val = List.ofFn (e p ∘ Tuple.sort (e p)) := by
    unfold row
    rw [hEp p, sorted_row]
  let q : E.support ≃ PrimeDivisors A :=
    { toFun := fun p => ⟨p.val, hsupport ▸ p.property⟩
      invFun := fun p => ⟨p.val, hsupport.symm ▸ p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let G := AddEquiv.piCongrRight (fun p : PrimeDivisors A =>
    sortedFactorsEquiv p.val (e p))
  have H : Nonempty (((p : PrimeDivisors A) →
      (i : Fin (r p)) → ZMod (p.val ^ (e p ∘ Tuple.sort (e p)) i)) ≃+
        ElementaryGroup E) := by
    let H₁ := (RingEquiv.piCongrLeft
      (fun p : PrimeDivisors A =>
        (i : Fin (r p)) → ZMod (p.val ^ (e p ∘ Tuple.sort (e p)) i)) q).symm.toAddEquiv
    refine ⟨H₁.trans (AddEquiv.piCongrRight (fun p => ?_))⟩
    change ((i : Fin (r (q p))) →
      ZMod (p.val ^ (e (q p) ∘ Tuple.sort (e (q p))) i)) ≃+
      ((i : Fin (row E p.val).length) → ZMod (p.val ^ (row E p.val).getD i 0))
    have hrowp : row E p.val = List.ofFn (e (q p) ∘ Tuple.sort (e (q p))) := hrow (q p)
    rw [hrowp]
    exact ofFnFactorsEquiv p.val _
  exact ⟨E, hnorm, ⟨F.trans (G.trans H.some)⟩⟩

theorem invariant_factor_existence :
    Specs.D07.Ch07.InvariantFactorExistence.Existence.{u} := by
  intro A _ _
  obtain ⟨E, hE, ⟨F⟩⟩ := elementary_model A
  exact ⟨recombine E, recombine_normalized E hE,
    ⟨F.trans (group_preservation E hE).some.symm⟩⟩

theorem zero_group_empty_factors :
    Specs.D07.Ch07.InvariantFactorExistence.ZeroGroupEmptyFactors.{u} := by
  intro A _ _
  refine ⟨⟨by simp, by simp⟩, ⟨?_⟩⟩
  exact
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => by funext i; exact Fin.elim0 i
      map_add' := fun _ _ => by funext i; exact Fin.elim0 i }

end D07.Ch07.InvariantFactorExistence
