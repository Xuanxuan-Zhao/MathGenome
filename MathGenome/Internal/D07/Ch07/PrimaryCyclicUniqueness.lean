import MathGenome.Internal.Specs.D07.Ch07.PrimaryCyclicUniqueness
import MathGenome.Internal.D07.Ch07.TorsionCountInvariants

/-!
Uniqueness of elementary divisors (K07.07.primary_cyclic_uniqueness).
The intrinsic cardinalities of annihilator subgroups are preserved by
additive isomorphisms. At a fixed prime, the upstream difference formulas
recover the exponent multiset. For mixed prime labels, coprimality makes
all other cyclic factors contribute exactly one annihilated element.
-/

namespace D07.Ch07.PrimaryCyclicUniqueness

open Specs.D07.Ch07.PrimaryCyclicUniqueness
open Specs.D07.Ch07.TorsionCountInvariants

/-- An additive isomorphism restricts to a bijection on each annihilator. -/
def torsionEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A ≃+ B) (p k : ℕ) :
    torsionSubgroup A p k ≃ torsionSubgroup B p k where
  toFun x := ⟨f x, by
    change (p ^ k) • f (x : A) = 0
    rw [← map_nsmul, show (p ^ k) • (x : A) = 0 from x.property, map_zero]⟩
  invFun x := ⟨f.symm x, by
    change (p ^ k) • f.symm (x : B) = 0
    rw [← map_nsmul, show (p ^ k) • (x : B) = 0 from x.property, map_zero]⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x)
  right_inv x := Subtype.ext (f.apply_symm_apply x)

theorem primary_cyclic_uniqueness : PrimaryUniqueness := by
  intro p hp e f he hf h
  apply D07.Ch07.TorsionCountInvariants.counts_recover_exponents p hp e f he hf
  intro k
  exact Nat.card_congr (torsionEquiv h p k)

/-- Extract the positive exponents carrying a specified prime label. -/
def primeExponents (d : List (ℕ × ℕ)) (p : ℕ) : List ℕ :=
  (d.filter fun a => a.1 = p).map Prod.snd

theorem primeExponents_positive (d : List (ℕ × ℕ))
    (hd : ValidElementaryDivisors d) (p : ℕ) :
    ∀ n ∈ primeExponents d p, 0 < n := by
  intro n hn
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
  exact (hd a (List.mem_filter.mp ha).1).2

/-- Other prime-power factors contribute only the zero element. -/
theorem cyclic_mixed_torsion_card (p q e k : ℕ) (hp : p.Prime) (hq : q.Prime) :
    Nat.card (torsionSubgroup (ZMod (q ^ e)) p k) =
      if q = p then p ^ min k e else 1 := by
  by_cases h : q = p
  · subst q
    simpa using D07.Ch07.TorsionCountInvariants.cyclic_torsion_card p hp e k
  · have : NeZero (q ^ e) := ⟨pow_ne_zero e hq.ne_zero⟩
    rw [ite_eq_right h, torsionSubgroup, IsAddCyclic.card_nsmulAddMonoidHom_ker,
      Nat.card_zmod]
    exact ((Nat.coprime_primes hq hp).mpr h).pow e k

theorem primeExponents_prod (d : List (ℕ × ℕ)) (p k : ℕ) :
    (d.map fun a => if a.1 = p then p ^ min k a.2 else 1).prod =
      p ^ torsionExponent (primeExponents d p) k := by
  induction d with
  | nil => simp [primeExponents, torsionExponent]
  | cons a d ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih]
    by_cases h : a.1 = p <;> simp [primeExponents, torsionExponent, h, pow_add]

/-- Counts at p ignore every factor with a different prime label. -/
theorem mixed_torsion_card (d : List (ℕ × ℕ)) (hd : ValidElementaryDivisors d)
    (p : ℕ) (hp : p.Prime) (k : ℕ) :
    Nat.card (torsionSubgroup (ElementaryProduct d) p k) =
      p ^ torsionExponent (primeExponents d p) k := by
  calc
    Nat.card (torsionSubgroup (ElementaryProduct d) p k) =
        Nat.card (∀ i : Fin d.length,
          torsionSubgroup (ZMod ((d.get i).1 ^ (d.get i).2)) p k) :=
      Nat.card_congr (D07.Ch07.TorsionCountInvariants.torsionPiEquiv _ _ p k)
    _ = ∏ i : Fin d.length,
        Nat.card (torsionSubgroup (ZMod ((d.get i).1 ^ (d.get i).2)) p k) :=
      Nat.card_pi
    _ = ∏ i : Fin d.length,
        if (d.get i).1 = p then p ^ min k (d.get i).2 else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      exact cyclic_mixed_torsion_card p _ _ k hp (hd _ (List.get_mem d i)).1
    _ = (d.map fun a => if a.1 = p then p ^ min k a.2 else 1).prod :=
      Fin.prod_univ_fun_getElem d (fun a => if a.1 = p then p ^ min k a.2 else 1)
    _ = p ^ torsionExponent (primeExponents d p) k := primeExponents_prod d p k

theorem count_primeExponents (d : List (ℕ × ℕ)) (p k : ℕ) :
    (primeExponents d p).count k = d.count (p, k) := by
  induction d with
  | nil => simp [primeExponents]
  | cons a d ih =>
    rcases a with ⟨q, e⟩
    by_cases hq : q = p
    · subst q
      simpa [primeExponents, List.count_cons, beq_iff_eq] using ih
    · simpa [primeExponents, List.count_cons, beq_iff_eq, hq] using ih

theorem elementary_divisor_uniqueness : ElementaryDivisorUniqueness := by
  intro d e hd he f
  have hpperm : ∀ p : ℕ, p.Prime → (primeExponents d p).Perm (primeExponents e p) := by
    intro p hp
    apply D07.Ch07.TorsionCountInvariants.counts_recover_exponents p hp
      _ _ (primeExponents_positive d hd p) (primeExponents_positive e he p)
    intro k
    rw [D07.Ch07.TorsionCountInvariants.torsion_cardinality p hp _
      (primeExponents_positive d hd p),
      D07.Ch07.TorsionCountInvariants.torsion_cardinality p hp _
      (primeExponents_positive e he p),
      ← mixed_torsion_card d hd p hp, ← mixed_torsion_card e he p hp]
    exact Nat.card_congr (torsionEquiv f p k)
  apply List.perm_iff_count.mpr
  rintro ⟨p, k⟩
  by_cases hp : p.Prime
  · simpa only [count_primeExponents] using (hpperm p hp).count_eq k
  · have hdnot : (p, k) ∉ d := fun h => hp (hd _ h).1
    have henot : (p, k) ∉ e := fun h => hp (he _ h).1
    rw [List.count_eq_zero.mpr hdnot, List.count_eq_zero.mpr henot]

theorem finite_abelian_uniqueness : FiniteAbelianUniqueness := by
  intro A _ _ d e hd he f g
  have h := elementary_divisor_uniqueness d e hd he (f.symm.trans g)
  exact ⟨h, h.map (fun a => a.1 ^ a.2)⟩

end D07.Ch07.PrimaryCyclicUniqueness
