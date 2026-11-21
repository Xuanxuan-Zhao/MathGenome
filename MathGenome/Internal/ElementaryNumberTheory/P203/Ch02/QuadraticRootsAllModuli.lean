import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.QuadraticRootsAllModuli
import Mathlib.Data.ZMod.QuotientRing
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch02.QuadraticRootReduction
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch02.QuadraticUnitRoots

noncomputable section
namespace P203.Ch02
open P203Specs.Ch01 P203Specs.Ch02
open scoped BigOperators

/-- Root counts in the two upstream representations agree. -/
theorem quadraticRootCount_eq_residue (m : ℕ) (hm : 0 < m) (a : ℤ) :
    quadraticRootCount m a = UnitQuadratic.quadraticRootCount m a :=
  (quadraticRootsResidueBridge m hm a).2

/-- Ring isomorphisms transport the equation, including its right hand side. -/
theorem quadraticRootsCRT : QuadraticRootsCRT := by
  intro m hm a
  let e := ZMod.equivPi m hm.ne'
  have he : ∀ x : ZMod m, x^2 = (a : ZMod m) ↔
      ∀ p : m.primeFactors, (e x p)^2 = (a : ZMod ((p : ℕ)^m.factorization p)) := by
    intro x
    rw [← e.injective.eq_iff, map_pow, map_intCast]
    exact funext_iff
  let er : UnitQuadratic.QuadraticRoots m a ≃
      {y : (p : m.primeFactors) → ZMod ((p : ℕ)^m.factorization p) //
        ∀ p, (y p)^2 = (a : ZMod ((p : ℕ)^m.factorization p))} :=
    e.toEquiv.subtypeEquiv he
  refine ⟨er.trans (Equiv.subtypePiEquivPi
    (p := fun (p : m.primeFactors) (y : ZMod ((p : ℕ)^m.factorization p)) =>
      y^2 = (a : ZMod ((p : ℕ)^m.factorization p)))), ?_⟩
  intro x p
  change e x.val p = _
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective x.val
  rw [← hz]
  simp only [map_intCast]
  rfl

theorem quadraticRootCountProduct : QuadraticRootCountProduct := by
  intro m hm a
  obtain ⟨e, _⟩ := quadraticRootsCRT m hm a
  rw [quadraticRootCount_eq_residue m hm a]
  unfold UnitQuadratic.quadraticRootCount
  rw [Nat.card_congr e, Nat.card_pi]
  apply Finset.prod_congr rfl
  intro p _
  exact (quadraticRootCount_eq_residue _
    (pow_pos (Nat.pos_of_mem_primeFactors p.property) _) a).symm

/-- All four unit-count results, in one explicit expression. -/
theorem unitRootCount_explicit (p : ℕ) (hp : p.Prime) (j : ℕ) (hj : 1 ≤ j)
    (b : ℤ) (hb : ¬(p : ℤ) ∣ b) :
    quadraticRootCount (p^j) b = unitRootFactor p j b := by
  rw [quadraticRootCount_eq_residue _ (pow_pos hp.pos _) b]
  by_cases hp2 : p = 2
  · subst p
    by_cases hj1 : j = 1
    · subst j
      simpa [unitRootFactor] using twoUnitRootCount b hb
    · by_cases hj2 : j = 2
      · subst j
        simpa [unitRootFactor] using fourUnitRootCount b hb
      · simpa [unitRootFactor, hj1, hj2] using
          twoPowerUnitRootCount j (by omega) b hb
  · simpa [unitRootFactor, hp2] using oddPrimeUnitRootCount p hp hp2 j hj b hb

theorem primePowerRootCountExplicit : PrimePowerRootCountExplicit := by
  intro p hp k hk a
  unfold primePowerRootFactor
  by_cases hz : (p : ℤ)^k ∣ a
  · rw [ite_eq_left hz]
    exact (zeroResidueRoots p hp k hk a hz).2
  · rw [ite_eq_right hz]
    obtain ⟨_, s, hs, hsk, _⟩ := nonzeroResidueValuation p hp k hk a hz
    rw [hs, ENat.toNat_natCast]
    by_cases ho : Odd s
    · rw [ite_eq_left ho]
      exact (oddValuationNoRoots p hp k s a hs hsk ho).2
    · rw [ite_eq_right ho]
      have hs_eq : s = 2*(s/2) := by
        have := Nat.even_or_odd s
        rcases this with ⟨r, hr⟩ | hodd
        · omega
        · exact False.elim (ho hodd)
      have hst : primeValuation p a = ((2*(s/2) : ℕ) : ℕ∞) := by
        simpa only [← hs_eq] using hs
      obtain ⟨hj, _, hb, _, _, hc⟩ :=
        evenValuationReduction p hp k (s/2) a hst (by omega)
      rw [hc, unitRootCount_explicit p hp _ hj _ hb]
      simp only [← hs_eq]

theorem quadraticRootCountExplicit : QuadraticRootCountExplicit := by
  intro m hm a
  rw [quadraticRootCountProduct m hm a]
  apply Finset.prod_congr rfl
  intro p _
  have hp := Nat.prime_of_mem_primeFactors p.property
  exact primePowerRootCountExplicit p hp (m.factorization p)
    (hp.factorization_pos_of_dvd hm.ne' (Nat.dvd_of_mem_primeFactors p.property)) a

theorem quadraticRootsModulusOne : QuadraticRootsModulusOne := by
  intro a
  refine ⟨?_, ?_, ?_⟩
  · rw [quadraticRootCountExplicit 1 (by decide) a]
    simp
  · exact ⟨0, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  · simp

end P203.Ch02
