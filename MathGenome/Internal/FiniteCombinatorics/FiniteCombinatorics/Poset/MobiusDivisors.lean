import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Poset.MobiusInversion
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Poset.MobiusDivisors

/-! Divisor-poset specialization of `paper.tex`, p204:W09.
We identify a row of the incidence inverse using arithmetic inversion on the
(divisor-closed) set of divisors of `N`, then apply the integer coefficient map.
The arithmetic inversion theorem itself is the independent Dirichlet-convolution
result in Mathlib, rewritten with the source's single divisor index. -/

noncomputable section
open Classical
open scoped FiniteCombinatorics.Poset

namespace FiniteCombinatorics.Poset.IncidenceFunction

/-- Arithmetic inversion written with a single divisor index. -/
theorem divisor_inversion (R : Type*) [CommRing R] (f g : ℕ → R) :
    (∀ n > 0, g n = ∑ d ∈ n.divisors, f d) ↔
    (∀ n > 0, f n = ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius (n / d) : R) * g d) := by
  have h := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := f) (g := g)
  simp_rw [Nat.sum_divisorsAntidiagonal'
    (f := fun x y => (ArithmeticFunction.moebius x : R) * g y)] at h
  simpa only [eq_comm] using h

/-- Changing from the lower set of a divisor to its ordinary natural divisors. -/
lemma sum_divisor_lower {R : Type*} [AddCommMonoid R] {N : ℕ}
    (b : DivisorPoset N) (F : ℕ → R) :
    (∑ y ∈ Finset.univ.filter (fun y : DivisorPoset N => y ≤ b), F y.val) =
      ∑ d ∈ b.val.divisors, F d := by
  apply Finset.sum_bij (fun y _ => y.val)
  · intro y hy
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hy).2,
      (Nat.pos_of_mem_divisors b.property).ne'⟩
  · intro y _ z _ h
    exact Subtype.ext h
  · intro d hd
    have hdN : d ∈ N.divisors := Nat.mem_divisors.mpr
      ⟨dvd_trans (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors b.property),
        Nat.ne_zero_of_mem_divisors b.property⟩
    exact ⟨⟨d, hdN⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Nat.dvd_of_mem_divisors hd⟩, rfl⟩
  · intro _ _
    rfl

/-- Möbius values on positive divisors agree with the arithmetic Möbius function. -/
theorem mobius_divisors_int (N : ℕ) (_hN : 0 < N)
    (a b : DivisorPoset N) (hab : a ≤ b) :
    mobius ℤ (DivisorPoset N) a b =
      ArithmeticFunction.moebius (b.val / a.val) := by
  let F : ℕ → ℤ := fun d =>
    if h : d ∈ N.divisors then mobius ℤ (DivisorPoset N) a ⟨d, h⟩ else 0
  let G : ℕ → ℤ := fun d => if d = a.val then 1 else 0
  have hFy (y : DivisorPoset N) : F y.val = mobius ℤ (DivisorPoset N) a y := by
    dsimp only [F]
    rw [dite_eq_left y.property]
    congr 1
  have hsum : ∀ n > 0, n ∈ N.divisors → (∑ d ∈ n.divisors, F d) = G n := by
    intro n _ hn
    let c : DivisorPoset N := ⟨n, hn⟩
    rw [← sum_divisor_lower c F]
    have h := congrArg (fun v : IncidenceFunction ℤ (DivisorPoset N) => v a c)
      (mobius_inverse ℤ (DivisorPoset N)).2
    rw [convolution_univ, delta_apply] at h
    have heq : a = c ↔ n = a.val := by
      constructor
      · intro he
        exact (congrArg Subtype.val he).symm
      · intro he
        exact Subtype.ext he.symm
    simp_rw [hFy]
    simp_rw [zeta_apply ℤ (DivisorPoset N)] at h
    simpa only [G, c, Finset.sum_filter, mul_ite, mul_one, mul_zero, heq] using h
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
    (R := ℤ) (f := F) (g := G) {d | d ∈ N.divisors}
    (by
      intro m n hmn hn
      exact Nat.mem_divisors.mpr
        ⟨dvd_trans hmn (Nat.dvd_of_mem_divisors hn),
          Nat.ne_zero_of_mem_divisors hn⟩)).mp hsum
  have h := hinv b.val (Nat.pos_of_mem_divisors b.property) b.property
  simp only [Int.cast_id] at h
  rw [Nat.sum_divisorsAntidiagonal' (f := fun x y =>
    ArithmeticFunction.moebius x * G y)] at h
  have ha : a.val ∈ b.val.divisors := Nat.mem_divisors.mpr
    ⟨hab, (Nat.pos_of_mem_divisors b.property).ne'⟩
  rw [hFy] at h
  simpa [G, mul_ite, ha] using h.symm

/-- Specialization to arbitrary commutative coefficient rings. -/
theorem mobius_divisors (R : Type*) [CommRing R] (N : ℕ) (hN : 0 < N)
    (a b : DivisorPoset N) (hab : a ≤ b) :
    mobius R (DivisorPoset N) a b =
      (ArithmeticFunction.moebius (b.val / a.val) : R) := by
  rw [← mobius_intCast, mobius_divisors_int N hN a b hab]

end FiniteCombinatorics.Poset.IncidenceFunction
