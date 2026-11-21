import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.HenselFactorLimit
import Mathlib.Tactic.Choose
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

universe u
namespace P103.Ch07.HenselFactorLimit
open Polynomial
variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Consecutive congruences telescope at the specified shifted rate. -/
lemma sequence_congruence (a : ℕ → R)
    (ha : ∀ n, a (n+1) - a n ∈ I ^ (n+1))
    {m n : ℕ} (hmn : m ≤ n) : a n - a m ∈ I ^ (m+1) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have hn : a (n+1) - a n ∈ I ^ (m+1) :=
      (Ideal.pow_le_pow_right (by omega)) (ha n)
    convert (I ^ (m+1)).add_mem hn ih using 1; ring

/-- Completeness gives a limit with the full shifted congruence, not just
one power less. -/
lemma sequence_limit [IsAdicComplete I R] (a : ℕ → R)
    (ha : ∀ n, a (n+1) - a n ∈ I ^ (n+1)) :
    ∃ L : R, ∀ n, L - a n ∈ I ^ (n+1) := by
  have hc : ∀ {m n}, m ≤ n → a m ≡ a n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    simpa only [neg_sub] using (I ^ m).neg_mem
      ((Ideal.pow_le_pow_right (by omega)) (sequence_congruence I a ha hmn))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I R) hc
  refine ⟨L, fun n => ?_⟩
  have hn : L - a (n+1) ∈ I ^ (n+1) := by
    have := (hL (n+1)).symm
    simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using this
  convert (I ^ (n+1)).add_mem hn (ha n) using 1; ring

/-- Membership in every ideal power is equality, in the ring itself. -/
lemma eq_of_sub_mem [IsHausdorff I R] {a b : R}
    (h : ∀ n : ℕ, a - b ∈ I ^ n) : a = b := by
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using h

/-- Fixed degree bounds make the coefficient limits into a polynomial. -/
lemma monic_sequence_limit [IsAdicComplete I R] (r : ℕ) (g : ℕ → R[X])
    (hg : ∀ n, (g n).Monic) (hd : ∀ n, (g n).natDegree = r)
    (hc : ∀ n k, (g (n+1) - g n).coeff k ∈ I ^ (n+1)) :
    ∃ G : R[X], G.Monic ∧ G.natDegree = r ∧
      ∀ n k, (G - g n).coeff k ∈ I ^ (n+1) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨g 0, hg 0, hd 0, ?_⟩
    intro n k
    have : (g 0 - g n).coeff k = 0 := Subsingleton.elim _ _
    rw [this]
    exact Ideal.zero_mem _
  have hlim (k : ℕ) : ∃ L : R, ∀ n, L - (g n).coeff k ∈ I ^ (n+1) := by
    apply sequence_limit I
    simpa only [coeff_sub] using fun n => hc n k
  choose a ha using hlim
  have az (k : ℕ) (hk : r < k) : a k = 0 := by
    apply eq_of_sub_mem I
    intro n
    have hz : (g n).coeff k = 0 := coeff_eq_zero_of_natDegree_lt ((hd n).trans_lt hk)
    have hn := ha k n
    rw [hz] at hn
    exact (Ideal.pow_le_pow_right (by omega)) hn
  let G : R[X] := ∑ k ∈ Finset.range (r+1), monomial k (a k)
  have hGa (k : ℕ) : G.coeff k = a k := by
    dsimp [G]
    simp only [finsetSum_coeff, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hk
    · rfl
    · symm
      exact az k (by simp only [Finset.mem_range] at hk; omega)
  have har : a r = 1 := by
    apply eq_of_sub_mem I
    intro n
    have hn := ha r n
    have hr : (g n).coeff r = 1 := by rw [← hd n]; exact (hg n).coeff_natDegree
    rw [hr] at hn
    exact (Ideal.pow_le_pow_right (by omega)) hn
  have hbound : G.natDegree ≤ r := natDegree_le_iff_coeff_eq_zero.mpr fun k hk => by
    rw [hGa, az k hk]
  have htop : G.coeff r = 1 := (hGa r).trans har
  refine ⟨G, monic_of_natDegree_le_of_coeff_eq_one r hbound htop,
    natDegree_eq_of_le_of_coeff_ne_zero hbound (htop ▸ one_ne_zero), ?_⟩
  intro n k
  simpa only [coeff_sub, hGa] using ha k n

/-- Coefficient congruences are polynomial equalities over the quotient ring. -/
lemma map_eq_of_coeff_sub_mem (J : Ideal R) {p q : R[X]}
    (h : ∀ k, (p - q).coeff k ∈ J) :
    p.map (Ideal.Quotient.mk J) = q.map (Ideal.Quotient.mk J) := by
  ext k
  simp only [coeff_map]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := J) _ _).mpr
  simpa only [coeff_sub] using h k

/-- Coefficientwise adic limits of bounded monic factor approximations.
This is the limit passage in the factorization proof of Theorem 7.8. -/
theorem factor_limit (R : Type u) [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (r s : ℕ) (f : R[X]) (g h : ℕ → R[X])
    (hg : ∀ n, (g n).Monic) (hh : ∀ n, (h n).Monic)
    (hdg : ∀ n, (g n).natDegree = r) (hdh : ∀ n, (h n).natDegree = s)
    (hcg : ∀ n k, (g (n+1) - g n).coeff k ∈ I ^ (n+1))
    (hch : ∀ n k, (h (n+1) - h n).coeff k ∈ I ^ (n+1))
    (herr : ∀ n k, (f - g n * h n).coeff k ∈ I ^ (n+1)) :
    ∃ G H : R[X], G.Monic ∧ H.Monic ∧ G.natDegree = r ∧ H.natDegree = s ∧
      f = G * H ∧ (∀ n k, (G - g n).coeff k ∈ I ^ (n+1)) ∧
      (∀ n k, (H - h n).coeff k ∈ I ^ (n+1)) := by
  obtain ⟨G, hGm, hGd, hGc⟩ := monic_sequence_limit I r g hg hdg hcg
  obtain ⟨H, hHm, hHd, hHc⟩ := monic_sequence_limit I s h hh hdh hch
  refine ⟨G, H, hGm, hHm, hGd, hHd, ?_, hGc, hHc⟩
  have heq (n : ℕ) : f.map (Ideal.Quotient.mk (I ^ (n+1))) =
      (G * H).map (Ideal.Quotient.mk (I ^ (n+1))) := by
    have hfn := map_eq_of_coeff_sub_mem (I ^ (n+1)) (herr n)
    have hgn := map_eq_of_coeff_sub_mem (I ^ (n+1)) (hGc n)
    have hhn := map_eq_of_coeff_sub_mem (I ^ (n+1)) (hHc n)
    rw [hfn, Polynomial.map_mul, Polynomial.map_mul, hgn, hhn]
  ext k
  apply eq_of_sub_mem I
  intro n
  have hn := congrArg (fun p => p.coeff k) (heq n)
  simp only [coeff_map] at hn
  exact (Ideal.pow_le_pow_right (by omega))
    ((Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := I ^ (n+1)) _ _).mp hn)

end P103.Ch07.HenselFactorLimit
