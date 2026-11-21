import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.HermiteRemainder
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.IntervalCalculus
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.HermiteAlgebra
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.RepeatedRolle
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NumAnalysis206.Approximation
open Polynomial Set
open scoped BigOperators
open HermiteRemainderSpec

/-- Real polynomial Taylor coefficients are ordinary derivatives divided by
factorials. No such division was used in the field-valued residue theorem. -/
theorem polynomial_taylor_coeff (p : ℝ[X]) (z : ℝ) (j : ℕ) :
    (p.taylor z).coeff j = polynomialJet p j z / (j.factorial : ℝ) := by
  have h := congrFun (factorial_smul_hasseDeriv (R := ℝ) (k := j)) p
  have he := congrArg (fun q : ℝ[X] => q.eval z) h
  simp only [nsmul_eq_mul] at he
  rw [taylor_coeff]
  apply (eq_div_iff (by exact_mod_cast j.factorial_ne_zero)).mpr
  simpa [polynomialJet, mul_comm] using he

theorem taylor_residue_coeff (z : ℝ) (m : ℕ) (d : ℕ → ℝ) (j : ℕ) (hj : j < m) :
    ((taylorResidue z m d).taylor z).coeff j = d j / (j.factorial : ℝ) := by
  simp only [taylorResidue, map_sum, taylor_mul, taylor_C, taylor_pow,
    map_sub, taylor_X, add_sub_cancel_right]
  simp [coeff_C_mul, coeff_X_pow, Finset.mem_range.mpr hj]

/-- The local equivalence between real Taylor residues and derivative data. -/
theorem taylor_residue_equivalence : TaylorResidueEquivalence := by
  intro p z m d
  rw [X_sub_C_pow_dvd_iff, ← taylor_apply, X_pow_dvd_iff]
  simp only [map_sub, coeff_sub]
  constructor
  · intro h j hj
    have := h j hj
    rw [sub_eq_zero, polynomial_taylor_coeff, taylor_residue_coeff _ _ _ _ hj] at this
    exact (div_left_inj' (by exact_mod_cast j.factorial_ne_zero)).mp this
  · intro h j hj
    rw [polynomial_taylor_coeff, taylor_residue_coeff _ _ _ _ hj, h j hj, sub_self]

/-- Arbitrary real derivative data have a unique Hermite interpolant. -/
theorem real_hermite_interpolation : RealHermiteInterpolation := by
  intro s hs z hz m hm d
  obtain ⟨p, hp, huniq⟩ := hermite_residue_interpolation ℝ s hs z hz m hm
    (fun i => taylorResidue (z i) (m i) (d i))
  refine ⟨p, ⟨hp.1, ?_⟩, ?_⟩
  · intro i
    exact (taylor_residue_equivalence p (z i) (m i) (d i)).mp (hp.2 i)
  · intro q hq
    exact huniq q ⟨hq.1, fun i =>
      (taylor_residue_equivalence q (z i) (m i) (d i)).mpr (hq.2 i)⟩

/-- The algebraic polynomial jet has the ordinary analytic derivatives. -/
theorem polynomialJet_hasDerivAt (p : ℝ[X]) (j : ℕ) (t : ℝ) :
    HasDerivAt (polynomialJet p j) (polynomialJet p (j + 1) t) t := by
  change HasDerivAt (fun x => (derivative^[j] p).eval x)
    ((derivative^[j + 1] p).eval t) t
  rw [Function.iterate_succ_apply']
  exact (derivative^[j] p).hasDerivAt t

theorem polynomialJet_eq_iteratedDeriv (p : ℝ[X]) (j : ℕ) :
    polynomialJet p j = iteratedDeriv j (fun t => p.eval t) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, ← ih]
    funext t
    exact (polynomialJet_hasDerivAt p j t).deriv.symm

theorem polynomial_interval_jet (p : ℝ[X]) (a b : ℝ) (r : ℕ) :
    IntervalJet a b r (fun t => p.eval t) (polynomialJet p) := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro j _
    exact (continuous_iff_continuousAt.mpr
      (fun t => (polynomialJet_hasDerivAt p j t).continuousAt)).continuousOn
  · intro j _ t _
    exact (polynomialJet_hasDerivAt p j t).hasDerivWithinAt

theorem polynomialJet_eq_zero_of_degree_lt {p : ℝ[X]} {n : ℕ}
    (hp : p.degree < (n : WithBot ℕ)) (t : ℝ) : polynomialJet p n t = 0 := by
  simp [polynomialJet, iterate_derivative_eq_zero_of_degree_lt hp]

/-- The top derivative of a monic polynomial is its degree factorial. -/
theorem polynomialJet_monic_top {p : ℝ[X]} (hp : p.Monic) (t : ℝ) :
    polynomialJet p p.natDegree t = (p.natDegree.factorial : ℝ) := by
  have heq : derivative^[p.natDegree] p = C (p.natDegree.factorial : ℝ) := by
    ext k
    cases k with
    | zero =>
      simp [coeff_iterate_derivative, Nat.descFactorial_self,
        show p.coeff p.natDegree = 1 from hp]
    | succ k =>
      rw [coeff_iterate_derivative, coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  simp [polynomialJet, heq]

/-- A factor of multiplicity `m` forces the first `m` polynomial jet entries
to vanish, including order zero. -/
theorem polynomialJet_vanish_of_pow_dvd {p : ℝ[X]} {z : ℝ} {m : ℕ}
    (hp : (X - C z) ^ m ∣ p) (j : ℕ) (hj : j < m) :
    polynomialJet p j z = 0 := by
  have h : (X - C z) ^ m ∣ p - taylorResidue z m (fun _ => 0) := by
    simpa [taylorResidue] using hp
  exact (taylor_residue_equivalence p z m (fun _ => 0)).mp h j hj

/-- An indexed-family version of the accepted marked-zero Rolle theorem.
Sorting uses the order pulled back along the injective node map. -/
theorem repeated_rolle_fintype {ι : Type*} [Fintype ι] [Nonempty ι]
    {a b : ℝ} {g : ℝ → ℝ} {D : ℕ → ℝ → ℝ}
    (z : ι → ℝ) (hz : Function.Injective z) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hmem : ∀ i, z i ∈ Icc a b)
    (hD : IntervalJet a b ((∑ i, m i) - 1) g D)
    (hzero : ∀ i j, j < m i → D j (z i) = 0) :
    ∃ ξ ∈ convexHull ℝ (Set.range z), D ((∑ i, m i) - 1) ξ = 0 := by
  classical
  let : LinearOrder ι := LinearOrder.lift' z hz
  let l : List (ℝ × ℕ) := (Finset.univ.sort).map (fun i => (z i, m i))
  have hne : l ≠ [] := by
    intro he
    have : l.length = 0 := by rw [he]; rfl
    have hcard : 0 < Fintype.card ι := Fintype.card_pos
    simp [l] at this
  have hlist : ∀ p ∈ l, ∃ i, p = (z i, m i) := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact ⟨i, rfl⟩
  have hord : l.Pairwise (fun p q => p.1 < q.1) := by
    apply List.pairwise_map.mpr
    exact (Finset.sortedLT_sort (Finset.univ : Finset ι)).pairwise
  have hsum : (l.map Prod.snd).sum = ∑ i, m i := by
    dsimp only [l]
    rw [List.map_map]
    change (((Finset.univ : Finset ι).sort).map m).sum = _
    rw [((Finset.sort_perm_toList (Finset.univ : Finset ι) (· ≤ ·)).map m).sum_eq]
    exact Finset.sum_map_toList _ _
  have hN : 1 ≤ ∑ i, m i := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (hm i).trans_le (Finset.single_le_sum (fun j _ => Nat.zero_le (m j))
      (Finset.mem_univ i))
  have hab : a ≤ b := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (hmem i).1.trans (hmem i).2
  obtain ⟨ξ, hξ, hzξ⟩ := repeated_rolle l hne hab hN hD hord
    (fun p hp => by obtain ⟨i, rfl⟩ := hlist p hp; exact hm i)
    (fun p hp => by obtain ⟨i, rfl⟩ := hlist p hp; exact hmem i)
    hsum
    (fun p hp => by obtain ⟨i, rfl⟩ := hlist p hp; exact hzero i)
  refine ⟨ξ, ?_, hzξ⟩
  have hleft : (l.head hne).1 ∈ Set.range z := by
    obtain ⟨i, hi⟩ := hlist _ (List.head_mem hne)
    exact ⟨i, by rw [hi]⟩
  have hright : (l.getLast hne).1 ∈ Set.range z := by
    obtain ⟨i, hi⟩ := hlist _ (List.getLast_mem hne)
    exact ⟨i, by rw [hi]⟩
  exact segment_subset_convexHull hleft hright (Icc_subset_segment hξ)

/-- The repeated-node remainder, using only the closed-interval derivative
data and the degree and matching properties of the interpolant. -/
theorem hermite_error_formula : HermiteErrorFormula := by
  intro a b f D s hs z hz hmem m hm hD p hp hmatch x hx
  classical
  let N := ∑ i, m i
  let q : ℝ[X] := ∏ i, (X - C (z i)) ^ m i
  have hqmon : q.Monic :=
    monic_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (z i)).pow (m i))
  have hqdeg : q.natDegree = N := by
    dsimp [q, N]
    rw [natDegree_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (z i)).pow (m i))]
    simp
  have hqeval (t : ℝ) : q.eval t = ∏ i, (t - z i) ^ m i := by
    simp [q, eval_prod]
  have hqzero (i : Fin s) (j : ℕ) (hj : j < m i) : polynomialJet q j (z i) = 0 := by
    apply polynomialJet_vanish_of_pow_dvd _ j hj
    exact Finset.dvd_prod_of_mem (fun i => (X - C (z i)) ^ m i) (Finset.mem_univ i)
  by_cases hnode : ∃ i, z i = x
  · obtain ⟨i, hi⟩ := hnode
    have hpx : p.eval x = f x := by
      calc
        p.eval x = polynomialJet p 0 (z i) := by rw [hi]; rfl
        _ = D 0 (z i) := hmatch i 0 (hm i)
        _ = f x := by rw [hi]; exact hD.1 hx
    have hprod : ∏ i, (x - z i) ^ m i = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, (hm i).ne'])
    exact ⟨x, subset_convexHull ℝ _ (Set.mem_insert x _), by rw [hpx, hprod]; ring⟩
  have hqnonzero : q.eval x ≠ 0 := by
    rw [hqeval]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun hi => hnode ⟨i, hi.symm⟩))
  let c : ℝ := (f x - p.eval x) / q.eval x
  let g : ℝ → ℝ := fun t => f t - p.eval t - c * q.eval t
  let E : ℕ → ℝ → ℝ := fun j t =>
    D j t - polynomialJet p j t - c * polynomialJet q j t
  have hE : IntervalJet a b N g E := by
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      dsimp [E, g, polynomialJet]
      rw [hD.1 ht]
    · intro j hj
      exact ((hD.2.1 j hj).sub ((polynomial_interval_jet p a b N).2.1 j hj)).sub
        (((polynomial_interval_jet q a b N).2.1 j hj).const_mul c)
    · intro j hj t ht
      exact ((hD.2.2 j hj t ht).sub
        ((polynomialJet_hasDerivAt p j t).hasDerivWithinAt)).sub
        ((polynomialJet_hasDerivAt q j t).hasDerivWithinAt.const_mul c)
  let w : Option (Fin s) → ℝ := fun o => o.elim x z
  let k : Option (Fin s) → ℕ := fun o => o.elim 1 m
  have hw : Function.Injective w := by
    intro u v huv
    cases u with
    | none =>
      cases v with
      | none => rfl
      | some i => exact (hnode ⟨i, huv.symm⟩).elim
    | some i =>
      cases v with
      | none => exact (hnode ⟨i, huv⟩).elim
      | some j => exact congrArg some (hz huv)
  have hk : ∀ o, 0 < k o := by
    intro o
    cases o with
    | none => exact Nat.zero_lt_one
    | some i => exact hm i
  have hwmem : ∀ o, w o ∈ Icc a b := by
    intro o
    cases o with
    | none => exact hx
    | some i => exact hmem i
  have hsum : ∑ o, k o = N + 1 := by
    simp [k, Fintype.sum_option, N, Nat.add_comm]
  have hwzero : ∀ o j, j < k o → E j (w o) = 0 := by
    intro o j hj
    cases o with
    | none =>
      have hj0 : j = 0 := by change j < 1 at hj; omega
      subst j
      change D 0 x - p.eval x - c * q.eval x = 0
      rw [hD.1 hx]
      dsimp [c]
      rw [div_mul_cancel₀ _ hqnonzero, sub_self]
    | some i =>
      change D j (z i) - polynomialJet p j (z i) - c * polynomialJet q j (z i) = 0
      rw [hmatch i j hj, hqzero i j hj]
      ring
  obtain ⟨ξ, hξ, hzero⟩ := repeated_rolle_fintype w hw k hk hwmem
    (by simpa only [hsum, Nat.add_sub_cancel] using hE) hwzero
  have hrange : Set.range w = insert x (Set.range z) := by
    ext t
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Set.mem_insert _ _
      | some i => exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
    · intro ht
      rcases ht with rfl | ⟨i, rfl⟩
      · exact ⟨none, rfl⟩
      · exact ⟨some i, rfl⟩
  refine ⟨ξ, by rwa [hrange] at hξ, ?_⟩
  have hpzero : polynomialJet p N ξ = 0 := polynomialJet_eq_zero_of_degree_lt hp ξ
  have hqtop : polynomialJet q N ξ = (N.factorial : ℝ) := by
    rw [← hqdeg]
    exact polynomialJet_monic_top hqmon ξ
  have hc : c = D N ξ / (N.factorial : ℝ) := by
    rw [hsum, Nat.add_sub_cancel] at hzero
    change D N ξ - polynomialJet p N ξ - c * polynomialJet q N ξ = 0 at hzero
    rw [hpzero, hqtop] at hzero
    apply (eq_div_iff (by exact_mod_cast N.factorial_ne_zero)).mpr
    linarith
  calc
    f x - p.eval x = c * q.eval x := (div_mul_cancel₀ _ hqnonzero).symm
    _ = D N ξ / (N.factorial : ℝ) * ∏ i, (x - z i) ^ m i := by rw [hc, hqeval]

/-- The full real Hermite theorem: residues, derivative conditions, unique
degree-bounded interpolant, and the pointwise remainder on the closed hull. -/
theorem real_hermite_with_remainder : RealHermiteWithRemainder := by
  intro a b f D s hs z hz hmem m hm hD
  obtain ⟨p, hp, huniq⟩ := real_hermite_interpolation s hs z hz m hm
    (fun i j => D j (z i))
  refine ⟨p, ⟨hp.1, ?_, hp.2, ?_⟩, ?_⟩
  · intro i
    exact (taylor_residue_equivalence p (z i) (m i) (fun j => D j (z i))).mpr (hp.2 i)
  · exact hermite_error_formula s hs z hz hmem m hm hD p hp.1 hp.2
  · intro q hq
    exact huniq q ⟨hq.1, hq.2.2.1⟩

end NumAnalysis206.Approximation
