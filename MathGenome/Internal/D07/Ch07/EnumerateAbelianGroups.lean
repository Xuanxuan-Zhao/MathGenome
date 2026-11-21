import MathGenome.Internal.Specs.D07.Ch07.EnumerateAbelianGroups
import MathGenome.Internal.D07.Ch07.PrimaryCyclicExistence
import MathGenome.Internal.D07.Ch07.PrimaryCyclicUniqueness
import Mathlib.Algebra.Group.TransferInstance

noncomputable section
namespace D07.Ch07.EnumerateAbelianGroups

open Specs.D07.Ch07.EnumerateAbelianGroups
open Specs.D07.Ch07.PrimaryDecomposition
open Specs.D07.Ch07.TorsionCountInvariants
open scoped BigOperators

/-- A permutation of a list reindexes its positions while preserving entries. -/
theorem perm_get_equiv {α : Type*} {l m : List α} (h : l.Perm m) :
    ∃ q : Fin l.length ≃ Fin m.length, ∀ i, l.get i = m.get (q i) := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun i => Fin.elim0 i⟩
  | @cons a l m h ih =>
    obtain ⟨q, hq⟩ := ih
    let q' : Fin (l.length + 1) ≃ Fin (m.length + 1) :=
      { toFun := Fin.cases 0 (fun i => (q i).succ)
        invFun := Fin.cases 0 (fun i => (q.symm i).succ)
        left_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
        right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    refine ⟨q', ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa [q'] using hq j
  | @swap a b l =>
    let q : Fin (l.length + 2) ≃ Fin (l.length + 2) :=
      { toFun := Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ))
        invFun := Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ))
        left_inv := by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · rfl
          · refine Fin.cases ?_ (fun k => ?_) j <;> rfl
        right_inv := by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · rfl
          · refine Fin.cases ?_ (fun k => ?_) j <;> rfl }
    refine ⟨q, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨q, hq⟩ := ih₁
    obtain ⟨r, hr⟩ := ih₂
    exact ⟨q.trans r, fun i => (hq i).trans (hr (q i))⟩

/-- Reordering cyclic factors gives an additive isomorphism of actual products. -/
def primePowerPermEquiv (p : ℕ) {l m : List ℕ} (h : l.Perm m) :
    PrimePowerProduct p l ≃+ PrimePowerProduct p m := by
  let q := (perm_get_equiv h).choose
  have hq := (perm_get_equiv h).choose_spec
  let e := AddEquiv.piCongrRight (fun i : Fin l.length =>
    (ZMod.ringEquivCongr (congrArg (p ^ ·) (hq i))).toAddEquiv)
  exact e.trans (RingEquiv.piCongrLeft (fun j : Fin m.length => ZMod (p ^ m.get j)) q).toAddEquiv

/-- Product cardinalities are powers of the sum of exponents. -/
theorem primePowerProduct_card (p : ℕ) (l : List ℕ) :
    Nat.card (PrimePowerProduct p l) = p ^ l.sum := by
  rw [Nat.card_pi]
  simp only [Nat.card_zmod]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simpa only [List.get_eq_getElem, id_eq, List.map_id] using
    Fin.sum_univ_fun_getElem l id

abbrev Model (n : ℕ) (d : PartitionData n) :=
  (p : n.primeFactors) → PrimePowerProduct p.val (d p).parts.toList

instance modelFinite (n : ℕ) (d : PartitionData n) : Finite (Model n d) := by
  let (p : n.primeFactors) (i : Fin (d p).parts.toList.length) :
      NeZero (p.val ^ (d p).parts.toList.get i) :=
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  infer_instance

/-- Every choice of partitions realizes a finite group of order n. -/
theorem model_card (n : ℕ) (hn : 0 < n) (d : PartitionData n) :
    Nat.card (Model n d) = n := by
  rw [Nat.card_pi]
  calc
    (∏ p : n.primeFactors, Nat.card (PrimePowerProduct p.val (d p).parts.toList)) =
        ∏ p : n.primeFactors, p.val ^ n.factorization p.val := by
      apply Finset.prod_congr rfl
      intro p _
      rw [primePowerProduct_card]
      congr 1
      simpa only [← Multiset.sum_coe, Multiset.coe_toList] using (d p).parts_sum
    _ = n := by
      simpa only [Finset.univ_eq_attach, Finsupp.prod_attach_index] using
        (Nat.prod_primeFactors_pow_factorization hn.ne').symm

/-- The function-indexed and list-indexed product presentations agree. -/
def ofFnProductEquiv (p r : ℕ) (e : Fin r → ℕ) :
    ((i : Fin r) → ZMod (p ^ e i)) ≃+
      PrimePowerProduct p (List.ofFn e) := by
  let q : Fin r ≃ Fin (List.ofFn e).length :=
    finCongr (List.length_ofFn (f := e)).symm
  have hq (i : Fin r) : e i = (List.ofFn e).get (q i) := by simp [q]
  let E := AddEquiv.piCongrRight (fun i : Fin r =>
    (ZMod.ringEquivCongr (congrArg (p ^ ·) (hq i))).toAddEquiv)
  exact E.trans (RingEquiv.piCongrLeft
    (fun j : Fin (List.ofFn e).length => ZMod (p ^ (List.ofFn e).get j)) q).toAddEquiv

/-- Existence of primary cyclic splittings gives a partition at each prime. -/
theorem exists_model (A : Type) [AddCommGroup A] [Finite A] :
    ∃ d : PartitionData (Nat.card A), Nonempty (A ≃+ Model (Nat.card A) d) := by
  classical
  obtain ⟨r, e, he, E, ⟨F⟩⟩ :=
    D07.Ch07.PrimaryCyclicExistence.combined_primary_cyclic_existence A
  have hs (p : (Nat.card A).primeFactors) :
      (List.ofFn (e p)).sum = (Nat.card A).factorization p.val := by
    apply Nat.pow_right_injective (Nat.prime_of_mem_primeFactors p.property).two_le
    calc
      p.val ^ (List.ofFn (e p)).sum =
          Nat.card (PrimePowerProduct p.val (List.ofFn (e p))) :=
        (primePowerProduct_card _ _).symm
      _ = Nat.card (Primary A p.val) :=
        (Nat.card_congr (((E p).some).trans (ofFnProductEquiv p.val (r p) (e p))).toEquiv).symm
      _ = p.val ^ (Nat.card A).factorization p.val :=
        D07.Ch07.PrimaryDecomposition.primary_cardinality A p.val
          (Nat.prime_of_mem_primeFactors p.property)
  let d : PartitionData (Nat.card A) := fun p =>
    { parts := (List.ofFn (e p) : Multiset ℕ)
      parts_pos := by
        intro k hk
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
        exact he p i
      parts_sum := by simpa only [Multiset.sum_coe] using hs p }
  refine ⟨d, ⟨F.trans (AddEquiv.piCongrRight (fun p => ?_))⟩⟩
  refine (ofFnProductEquiv p.val (r p) (e p)).trans (primePowerPermEquiv p.val ?_)
  apply Multiset.coe_eq_coe.mp
  simp only [Multiset.coe_toList]
  rfl

/-- Counts for a product with a different prime label are all one. -/
theorem primaryProduct_mixed_torsion_card (p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) (l : List ℕ) (k : ℕ) :
    Nat.card (torsionSubgroup (PrimePowerProduct q l) p k) =
      if q = p then p ^ torsionExponent l k else 1 := by
  classical
  rw [Nat.card_congr (D07.Ch07.TorsionCountInvariants.torsionPiEquiv _ _ p k),
    Nat.card_pi]
  simp only [D07.Ch07.PrimaryCyclicUniqueness.cyclic_mixed_torsion_card p q _ k hp hq]
  by_cases h : q = p
  · simp only [h, ite_true]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    exact Fin.sum_univ_fun_getElem l (fun e => min k e)
  · simp [h]

/-- At a fixed prime only the corresponding primary factor contributes. -/
theorem model_torsion_card (n : ℕ) (d : PartitionData n)
    (p : n.primeFactors) (k : ℕ) :
    Nat.card (torsionSubgroup (Model n d) p.val k) =
      p.val ^ torsionExponent (d p).parts.toList k := by
  classical
  rw [Nat.card_congr (D07.Ch07.TorsionCountInvariants.torsionPiEquiv _ _ p.val k),
    Nat.card_pi]
  calc
    (∏ q : n.primeFactors,
      Nat.card (torsionSubgroup (PrimePowerProduct q.val (d q).parts.toList) p.val k)) =
        ∏ q : n.primeFactors,
          if q = p then p.val ^ torsionExponent (d q).parts.toList k else 1 := by
      apply Finset.prod_congr rfl
      intro q _
      rw [primaryProduct_mixed_torsion_card _ _
        (Nat.prime_of_mem_primeFactors p.property)
        (Nat.prime_of_mem_primeFactors q.property)]
      simp only [Subtype.ext_iff]
    _ = _ := by simp

/-- Isomorphic models have the same partition at every prime. -/
theorem model_unique {n : ℕ} (d e : PartitionData n)
    (f : Model n d ≃+ Model n e) : d = e := by
  funext p
  apply Nat.Partition.ext
  have hperm := D07.Ch07.TorsionCountInvariants.counts_recover_exponents
    p.val (Nat.prime_of_mem_primeFactors p.property)
    (d p).parts.toList (e p).parts.toList
    (fun a ha => (d p).parts_pos (Multiset.mem_toList.mp ha))
    (fun a ha => (e p).parts_pos (Multiset.mem_toList.mp ha))
  have h : (d p).parts.toList.Perm (e p).parts.toList := by
    apply hperm
    intro k
    rw [D07.Ch07.TorsionCountInvariants.torsion_cardinality _
        (Nat.prime_of_mem_primeFactors p.property) _
        (fun a ha => (d p).parts_pos (Multiset.mem_toList.mp ha)),
      D07.Ch07.TorsionCountInvariants.torsion_cardinality _
        (Nat.prime_of_mem_primeFactors p.property) _
        (fun a ha => (e p).parts_pos (Multiset.mem_toList.mp ha)),
      ← model_torsion_card n d p k, ← model_torsion_card n e p k]
    exact Nat.card_congr (D07.Ch07.PrimaryCyclicUniqueness.torsionEquiv f p.val k)
  simpa only [Multiset.coe_toList] using Multiset.coe_eq_coe.mpr h

/-- The bundled realization has the exact prescribed group order. -/
def modelGroup (n : ℕ) (hn : 0 < n) (d : PartitionData n) : AbelianGroupOfOrder n where
  Carrier := Model n d
  card_eq := model_card n hn d

/-- Send a partition choice to its abstract group isomorphism class. -/
def modelClass (n : ℕ) (hn : 0 < n) (d : PartitionData n) : IsomorphismTypes n :=
  Quotient.mk (groupSetoid n) (modelGroup n hn d)

theorem modelClass_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective (modelClass n hn) := by
  constructor
  · intro d e h
    obtain ⟨f⟩ := Quotient.exact h
    exact model_unique d e f
  · intro x
    refine Quotient.inductionOn x ?_
    intro G
    rcases G with @⟨A, g, hf, hcard⟩
    subst n
    obtain ⟨d, ⟨F⟩⟩ := exists_model A
    exact ⟨d, Quotient.sound ⟨F.symm⟩⟩

theorem partition_classification : PartitionClassification := by
  intro n hn
  exact ⟨(Equiv.ofBijective (modelClass n hn) (modelClass_bijective n hn)).symm⟩

theorem finite_types : FiniteTypes := by
  intro n hn
  obtain ⟨e⟩ := partition_classification n hn
  exact Finite.of_equiv (PartitionData n) e.symm

theorem enumeration_formula : EnumerationFormula := by
  intro n hn
  obtain ⟨e⟩ := partition_classification n hn
  rw [Nat.card_congr e, Nat.card_pi]
  exact Finset.prod_attach n.primeFactors (fun p => partitionNumber (n.factorization p))

theorem boundary_cases : BoundaryCases := by
  constructor
  · exact Nat.card_unique
  · rw [enumeration_formula 1 (by decide)]
    simp

/-- Finiteness permits relabelling into a fixed small universe without changing
any operations up to additive equivalence. -/
theorem represents_all : RepresentsAll.{u} := by
  intro A _ _ n hcard
  obtain ⟨B, bg, bf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_addEquiv.{u, 0} A
  let := bg
  let := bf
  let cg : AddCommGroup B :=
    { bg with add_comm := fun x y => e.symm.injective (by simp only [map_add, add_comm]) }
  refine ⟨{ Carrier := B
            group := cg
            card_eq := (Nat.card_congr e.toEquiv).symm.trans hcard }, ⟨e⟩⟩

end D07.Ch07.EnumerateAbelianGroups
