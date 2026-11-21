import MathGenome.Internal.Specs.D07.Ch07.InvariantFactorUniqueness
import MathGenome.Internal.D07.Ch07.ClassificationDataConversion
import MathGenome.Internal.D07.Ch07.PrimaryCyclicUniqueness

/-!
The prime-power annihilator counts recover each row of elementary data.
The proved inverse conversion then recovers the original invariant list.
-/
namespace D07.Ch07.InvariantFactorUniqueness

open D07.Ch07.ClassificationDataConversion
open Specs.D07.Ch07.TorsionCountInvariants
open D07.Ch07.TorsionCountInvariants
open D07.Ch07.PrimaryCyclicUniqueness

/-- Count annihilated elements in one row, including a row at another prime. -/
theorem row_torsion_card (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (l : List ℕ) (k : ℕ) :
    Nat.card (torsionSubgroup
      ((i : Fin l.length) → ZMod (q ^ l.getD i 0)) p k) =
      if q = p then p ^ torsionExponent l k else 1 := by
  calc
    _ = Nat.card ((i : Fin l.length) →
        torsionSubgroup (ZMod (q ^ l.getD i 0)) p k) :=
      Nat.card_congr (torsionPiEquiv _ _ p k)
    _ = ∏ i : Fin l.length,
        Nat.card (torsionSubgroup (ZMod (q ^ l.getD i 0)) p k) := Nat.card_pi
    _ = ∏ i : Fin l.length,
        if q = p then p ^ min k (l.get i) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [List.getD_eq_getElem _ _ i.isLt]
      exact cyclic_mixed_torsion_card p q (l.get i) k hp hq
    _ = if q = p then p ^ torsionExponent l k else 1 := by
      by_cases h : q = p
      · simp only [h, ↓reduceIte, Finset.prod_pow_eq_pow_sum]
        congr 1
        exact Fin.sum_univ_fun_getElem l (fun n => min k n)
      · simp [h]

/-- Counts at `p` depend only on the row carrying the actual prime `p`. -/
theorem elementary_torsion_card (E : ElementaryData) (hE : IsElementary E)
    (p : ℕ) (hp : p.Prime) (k : ℕ) :
    Nat.card (torsionSubgroup (ElementaryGroup E) p k) =
      p ^ torsionExponent (row E p) k := by
  classical
  calc
    _ = Nat.card ((q : E.support) → torsionSubgroup
        ((i : Fin (row E q.val).length) →
          ZMod (q.val ^ (row E q.val).getD i 0)) p k) :=
      Nat.card_congr (torsionPiEquiv _ _ p k)
    _ = ∏ q : E.support, Nat.card (torsionSubgroup
        ((i : Fin (row E q.val).length) →
          ZMod (q.val ^ (row E q.val).getD i 0)) p k) := Nat.card_pi
    _ = ∏ q : E.support,
        if q.val = p then p ^ torsionExponent (row E q.val) k else 1 := by
      apply Finset.prod_congr rfl
      intro q _
      exact row_torsion_card p q.val hp (prime_of_support hE q.property) _ k
    _ = p ^ torsionExponent (row E p) k := by
      by_cases h : p ∈ E.support
      · rw [Finset.prod_eq_single (⟨p, h⟩ : E.support)]
        · simp
        · intro q _ hq
          have hqp : q.val ≠ p := fun heq => hq (Subtype.ext heq)
          simp [hqp]
        · simp
      · have hz : E p = 0 := Finsupp.notMem_support_iff.mp h
        have hqp : ∀ q : E.support, q.val ≠ p := by
          intro q heq
          exact h (heq ▸ q.property)
        simp [hqp, row, hz, torsionExponent]

/-- Isomorphic elementary products have identical prime-labelled data. -/
theorem elementary_data_unique (E F : ElementaryData)
    (hE : IsElementary E) (hF : IsElementary F)
    (f : ElementaryGroup E ≃+ ElementaryGroup F) : E = F := by
  apply Finsupp.ext
  intro p
  by_cases hp : p.Prime
  · have hperm : (row E p).Perm (row F p) := by
      apply counts_recover_exponents p hp _ _ (row_positive hE p) (row_positive hF p)
      intro k
      rw [torsion_cardinality p hp _ (row_positive hE p),
        torsion_cardinality p hp _ (row_positive hF p),
        ← elementary_torsion_card E hE p hp k,
        ← elementary_torsion_card F hF p hp k]
      exact Nat.card_congr (torsionEquiv f p k)
    simpa only [row_multiset] using (Multiset.coe_eq_coe.mpr hperm)
  · have hzero (G : ElementaryData) (hG : IsElementary G) : G p = 0 := by
      apply Multiset.eq_zero_iff_forall_notMem.mpr
      intro a ha
      exact hp (hG p a ha).1
    rw [hzero E hE, hzero F hF]

theorem invariant_factor_uniqueness :
    Specs.D07.Ch07.InvariantFactorUniqueness.Uniqueness := by
  intro d e hd he f
  obtain ⟨fd⟩ := split_group_preservation d hd
  obtain ⟨fe⟩ := split_group_preservation e he
  have h := elementary_data_unique (split d) (split e)
    (split_normalized d hd) (split_normalized e he) (fd.symm.trans (f.trans fe))
  calc
    d = recombine (split d) := (recombine_split d hd).symm
    _ = recombine (split e) := congrArg recombine h
    _ = e := recombine_split e he

end D07.Ch07.InvariantFactorUniqueness
