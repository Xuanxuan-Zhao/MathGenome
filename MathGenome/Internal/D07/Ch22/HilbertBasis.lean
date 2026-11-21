import MathGenome.Internal.Specs.D07.Ch22.HilbertBasis

/-!
K07.22.hilbert_basis. The library Hilbert basis theorem is valid for
commutative unital rings with zero divisors, including the zero ring.
The finite-type presentation uses unital algebra maps; Noetherianity
passes along their surjective underlying ring maps.

For the countably many variables example, evaluation kills the first n
variables and sends the next variable to the nonzero polynomial X.
This witnesses every strict inclusion in the displayed ideal chain.
-/

universe u v

namespace D07.Ch22.HilbertBasis

open Specs.D07.Ch22.HilbertBasis

theorem oneVariableNoetherian : OneVariableNoetherian.{u} := by
  intro R _ _
  exact Polynomial.isNoetherianRing

theorem finiteVariablesNoetherian : FiniteVariablesNoetherian.{u} := by
  intro R _ _ n
  exact MvPolynomial.isNoetherianRing_fin

theorem finiteTypePresentation : FiniteTypePresentation.{u, v} := by
  intro R _ A _ _
  exact Algebra.FiniteType.iff_quotient_mvPolynomial''

theorem finiteTypeNoetherian : FiniteTypeNoetherian.{u, v} := by
  intro R _ _ A _ _ _
  obtain ⟨n, f, hf⟩ := (finiteTypePresentation R A).mp inferInstance
  let := finiteVariablesNoetherian R n
  exact isNoetherianRing_of_surjective (MvPolynomial (Fin n) R) A f.toRingHom hf

/-- Each stage contains all earlier generators, even when the coefficient
ring has zero divisors or is the zero ring. -/
theorem initialVariableIdeal_mono (R : Type u) [CommRing R] :
    Monotone (initialVariableIdeal R) := by
  intro m n hmn
  apply Ideal.span_mono
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi hmn, rfl⟩

/-- Setting the earlier variables to zero leaves the next one nonzero. -/
theorem nextVariable_not_mem (k : Type u) [Field k] (n : ℕ) :
    MvPolynomial.X n ∉ initialVariableIdeal k n := by
  let e : MvPolynomial ℕ k →+* Polynomial k :=
    MvPolynomial.eval₂Hom Polynomial.C (fun i => if i < n then 0 else Polynomial.X)
  have hker : initialVariableIdeal k n ≤ RingHom.ker e := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hi : i < n := hi
    simp [RingHom.mem_ker, e, hi]
  intro h
  have he := RingHom.mem_ker.mp (hker h)
  exact Polynomial.X_ne_zero (R := k) (by simpa [e] using he)

theorem infiniteVariableChain : InfiniteVariableChain.{u} := by
  intro k _ n
  have hmem : MvPolynomial.X n ∈ initialVariableIdeal k (n + 1) :=
    Ideal.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
  have hnot := nextVariable_not_mem k n
  refine ⟨lt_of_le_of_ne (initialVariableIdeal_mono k (Nat.le_succ n)) ?_, hnot, hmem⟩
  intro heq
  exact hnot (heq ▸ hmem)

theorem infiniteVariablesNotNoetherian : InfiniteVariablesNotNoetherian.{u} := by
  intro k _ h
  let := h
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (isNoetherianRing_iff.mp h)
    (⟨initialVariableIdeal k, initialVariableIdeal_mono k⟩ :
      ℕ →o Submodule (MvPolynomial ℕ k) (MvPolynomial ℕ k))
  exact (infiniteVariableChain k n).1.ne (hn (n + 1) (Nat.le_succ n))

theorem algebraFiniteNotModuleFinite : AlgebraFiniteNotModuleFinite.{u} := by
  intro k _
  refine ⟨Polynomial.adjoin_X, inferInstance, ?_, Polynomial.not_finite⟩
  simpa only [Polynomial.coe_basisMonomials, ← Polynomial.C_mul_X_pow_eq_monomial,
    map_one, one_mul] using (Polynomial.basisMonomials k).linearIndependent

end D07.Ch22.HilbertBasis
