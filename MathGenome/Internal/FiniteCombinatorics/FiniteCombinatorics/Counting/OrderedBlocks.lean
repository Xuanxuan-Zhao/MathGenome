import Mathlib.Data.Fintype.Perm
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.OrderedBlocks

/-!
Ordered-block counting, paper.tex W04 (the ordered-block assertion).

First identify a function together with bijections on its fibers with a
bijection to a dependent sum. For fibers of sizes `k i`, these bijections
have cardinality `∏ i, (k i)!`. If the sizes sum to the size of the ground
set, the bijections to the dependent sum number `n!`. Finally identify
assignments with actual disjoint finite block families, without assuming
any block is nonempty.
-/

namespace FiniteCombinatorics.Counting.OrderedBlocks
universe u v w
variable {X : Type u} {I : Type v} {β : I → Type w}

private def assemble (p : Σ f : X → I, ∀ i, {a // f a = i} ≃ β i) : X ≃ Sigma β :=
  (Equiv.sigmaFiberEquiv p.1).symm.trans (Equiv.sigmaCongrRight p.2)

@[simp] private theorem assemble_apply (p : Σ f : X → I, ∀ i, {a // f a = i} ≃ β i) (a : X) :
    assemble p a = ⟨p.1 a, p.2 (p.1 a) ⟨a, rfl⟩⟩ := rfl

private def splitFiber (e : X ≃ Sigma β) (i : I) : {a // (e a).1 = i} ≃ β i where
  toFun a := a.property ▸ (e a.val).2
  invFun b := ⟨e.symm ⟨i, b⟩, by simp⟩
  left_inv a := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    rcases a with ⟨a, h⟩
    dsimp
    cases h
    rfl
  right_inv b := by
    apply eq_of_heq
    exact (eqRec_heq _ _).trans (Sigma.mk.inj (e.apply_symm_apply ⟨i, b⟩)).2

private theorem assemble_injective : Function.Injective (assemble (X := X) (β := β)) := by
  rintro ⟨f, d⟩ ⟨g, c⟩ h
  have hf : f = g := funext fun a => congrArg Sigma.fst (Equiv.congr_fun h a)
  subst g
  congr 1
  funext i
  apply Equiv.ext
  rintro ⟨a, ha⟩
  subst i
  have hh := Equiv.congr_fun h a
  simpa only [assemble_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh

private theorem assemble_surjective : Function.Surjective (assemble (X := X) (β := β)) := by
  intro e
  refine ⟨⟨fun a => (e a).1, splitFiber e⟩, ?_⟩
  apply Equiv.ext
  intro a
  rfl

private def Assignments (X : Type u) [Fintype X] {r : ℕ} (k : Fin r → ℕ) :=
  {f : X → Fin r // ∀ i, Fintype.card {a // f a = i} = k i}

private noncomputable instance (X : Type u) [Fintype X] {r : ℕ} (k : Fin r → ℕ) :
    Fintype (Assignments X k) := by
  classical
  unfold Assignments
  infer_instance

private noncomputable def ordersEquiv (X : Type u) [Fintype X] {r : ℕ} (k : Fin r → ℕ) :
    (Σ p : Assignments X k, ∀ i, {a // p.val a = i} ≃ Fin (k i)) ≃
      (X ≃ Σ i, Fin (k i)) := by
  refine (Equiv.sigmaSubtypeEquivOfSubset
    (fun f : X → Fin r => ∀ i, {a // f a = i} ≃ Fin (k i))
    (fun f => ∀ i, Fintype.card {a // f a = i} = k i) ?_).trans
    (Equiv.ofBijective assemble ⟨assemble_injective, assemble_surjective⟩)
  intro f e i
  simpa using Fintype.card_congr (e i)

private theorem assignment_card_factorial (X : Type u) [Fintype X] {r : ℕ}
    (k : Fin r → ℕ) (hsum : (∑ i, k i) = Fintype.card X) :
    Fintype.card (Assignments X k) * (∏ i, (k i).factorial) =
      (Fintype.card X).factorial := by
  classical
  let e : X ≃ Σ i, Fin (k i) := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hsum.symm)
  have hc := Fintype.card_congr (ordersEquiv X k)
  have ho (p : Assignments X k) :
      Fintype.card (∀ i, {a // p.val a = i} ≃ Fin (k i)) = ∏ i, (k i).factorial := by
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    rw [Fintype.card_equiv (Fintype.equivFinOfCardEq (p.property i)), p.property i]
  simpa only [Fintype.card_sigma, ho, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Fintype.card_equiv e] using hc

/-- Ordered finite block families on a finite ground set, allowing empty blocks. -/
abbrev OrderedBlocks {α : Type u} (A : Finset α) {r : ℕ} (k : Fin r → ℕ) :=
  Specs.FiniteCombinatorics.Counting.OrderedBlocks.OrderedBlocks A k

private def assignmentsToBlocks {α : Type u} (A : Finset α) {r : ℕ} (k : Fin r → ℕ)
    (p : Assignments A k) : OrderedBlocks A k := by
  refine ⟨fun i => Finset.univ.filter (fun a => p.val a = i), ?_, ?_⟩
  · intro i
    rw [← Fintype.card_subtype]
    exact p.property i
  · intro a
    refine ⟨p.val a, by simp, ?_⟩
    intro j hj
    simpa using (Finset.mem_filter.mp hj).2.symm

private theorem assignmentsToBlocks_injective {α : Type u} (A : Finset α) {r : ℕ}
    (k : Fin r → ℕ) : Function.Injective (assignmentsToBlocks A k) := by
  intro p q h
  apply Subtype.ext
  funext a
  have hh := congrArg (fun B : OrderedBlocks A k => B.val (p.val a)) h
  have hp : a ∈ (assignmentsToBlocks A k p).val (p.val a) := by
    simp [assignmentsToBlocks]
  rw [hh] at hp
  exact (Finset.mem_filter.mp hp).2.symm

private theorem assignmentsToBlocks_surjective {α : Type u} (A : Finset α) {r : ℕ}
    (k : Fin r → ℕ) : Function.Surjective (assignmentsToBlocks A k) := by
  classical
  intro B
  choose f hf hu using B.property.2
  have hm (a : A) (i : Fin r) : f a = i ↔ a ∈ B.val i := by
    constructor
    · intro h
      simpa only [← h] using hf a
    · intro h
      exact (hu a i h).symm
  have hc (i : Fin r) : Fintype.card {a : A // f a = i} = k i := by
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun a => hm a i)),
      Fintype.card_coe]
    exact B.property.1 i
  refine ⟨⟨f, hc⟩, ?_⟩
  apply Subtype.ext
  funext i
  apply Finset.ext
  intro a
  simpa [assignmentsToBlocks] using hm a i

private noncomputable def assignmentsEquivBlocks {α : Type u} (A : Finset α) {r : ℕ}
    (k : Fin r → ℕ) : Assignments A k ≃ OrderedBlocks A k :=
  Equiv.ofBijective (assignmentsToBlocks A k)
    ⟨assignmentsToBlocks_injective A k, assignmentsToBlocks_surjective A k⟩

/-- The specified cardinality of every block. -/
theorem block_card {α : Type u} (A : Finset α) {r : ℕ} (k : Fin r → ℕ)
    (B : OrderedBlocks A k) (i : Fin r) : (B.val i).card = k i :=
  B.property.1 i

/-- Distinct indexed blocks are disjoint, even if their sizes coincide. -/
theorem block_disjoint {α : Type u} (A : Finset α) {r : ℕ} (k : Fin r → ℕ)
    (B : OrderedBlocks A k) (i j : Fin r) (hij : i ≠ j) :
    Disjoint (B.val i) (B.val j) := by
  apply Finset.disjoint_left.mpr
  intro a hai haj
  obtain ⟨b, _, hu⟩ := B.property.2 a
  exact hij ((hu i hai).trans (hu j haj).symm)

/-- The indexed blocks cover the entire given ground set. -/
theorem block_cover {α : Type u} (A : Finset α) {r : ℕ} (k : Fin r → ℕ)
    (B : OrderedBlocks A k) (a : A) : ∃ i, a ∈ B.val i :=
  (B.property.2 a).exists

/-- Zero sizes give empty blocks; they are not excluded. -/
theorem block_zero {α : Type u} (A : Finset α) {r : ℕ} (k : Fin r → ℕ)
    (B : OrderedBlocks A k) (i : Fin r) (hi : k i = 0) : B.val i = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [block_card A k B i, hi]

/-- Ordering inside each block gives exactly `∏ i, (k i)!` enumerations.
The count also applies to empty ground sets and empty indexed families. -/
theorem factorial_identity {α : Type u} (A : Finset α) (n r : ℕ) (k : Fin r → ℕ)
    (hA : A.card = n) (hsum : (∑ i, k i) = n) :
    Fintype.card (OrderedBlocks A k) * (∏ i, (k i).factorial) = n.factorial := by
  classical
  have h := assignment_card_factorial A k (by simpa only [Fintype.card_coe, hA] using hsum)
  rw [Fintype.card_congr (assignmentsEquivBlocks A k)] at h
  simpa only [Fintype.card_coe, hA] using h

/-- The number of ordered blocks of the prescribed sizes is the exact
natural factorial quotient. -/
theorem count {α : Type u} (A : Finset α) (n r : ℕ) (k : Fin r → ℕ)
    (hA : A.card = n) (hsum : (∑ i, k i) = n) :
    Fintype.card (OrderedBlocks A k) = n.factorial / ∏ i, (k i).factorial := by
  have hpos : 0 < ∏ i, (k i).factorial :=
    Finset.prod_pos fun i _ => Nat.factorial_pos (k i)
  calc
    Fintype.card (OrderedBlocks A k) =
        (Fintype.card (OrderedBlocks A k) * (∏ i, (k i).factorial)) /
          (∏ i, (k i).factorial) := (Nat.mul_div_cancel _ hpos).symm
    _ = n.factorial / ∏ i, (k i).factorial := by
      rw [factorial_identity A n r k hA hsum]

/-- The same count expressed as Mathlib's natural multinomial coefficient. -/
theorem multinomial_count {α : Type u} (A : Finset α) (n r : ℕ) (k : Fin r → ℕ)
    (hA : A.card = n) (hsum : (∑ i, k i) = n) :
    Fintype.card (OrderedBlocks A k) = Nat.multinomial Finset.univ k := by
  rw [count A n r k hA hsum, Nat.multinomial, hsum]

/-- There is exactly one all-empty block family on an empty ground set,
for every number of blocks, including zero. -/
theorem empty_count {α : Type u} (r : ℕ) :
    Fintype.card (OrderedBlocks (∅ : Finset α) (fun _ : Fin r => 0)) = 1 := by
  rw [count (∅ : Finset α) 0 r (fun _ => 0) (by simp) (by simp)]
  simp

end FiniteCombinatorics.Counting.OrderedBlocks
