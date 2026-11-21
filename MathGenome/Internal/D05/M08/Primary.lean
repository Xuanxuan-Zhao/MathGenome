import MathGenome.Internal.Specs.D05.M08.Primary
import MathGenome.Internal.D05.M08.BezoutDecomposition
import MathGenome.Internal.D05.M08.Minpoly
import MathGenome.Internal.D05.M06.InvariantDecomposition
import MathGenome.Internal.D05.Foundations.Factorization
import Mathlib.RingTheory.Coprime.Lemmas

/-! Primary decomposition by polynomial Chinese-remainder projectors.
The finite-family lemma only needs a coprime annihilating product; it does
not assume the desired decomposition or the existence of projections. -/

noncomputable section

namespace D05.M08.Primary

open Specs.D05.M06.DirectSum (UniqueDecomposition)
open Specs.D05.M06.InvariantDecomposition (componentProjection)

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- CRT polynomials give maps into each kernel, whose sum is the identity.
The last assertion says they extract exactly the indicated summand. -/
theorem coprime_projector_polynomials [DecidableEq ι] (T : Module.End K V) (f : ι → Polynomial K)
    (hc : Pairwise (fun i j => IsCoprime (f i) (f j)))
    (hz : Polynomial.aeval T (∏ i, f i) = 0) :
    ∃ e : ι → Polynomial K,
      (∑ i, Polynomial.aeval T (e i)) = 1 ∧
      (∀ i v, Polynomial.aeval T (e i) v ∈ LinearMap.ker (Polynomial.aeval T (f i))) ∧
      ∀ i j v, v ∈ LinearMap.ker (Polynomial.aeval T (f j)) →
        Polynomial.aeval T (e i) v = if i = j then v else 0 := by
  classical
  by_cases hn : Nonempty ι
  · let := hn
    obtain ⟨μ, hμ⟩ := exists_sum_eq_one_iff_pairwise_coprime'.mpr hc
    let Q : ι → Polynomial K := fun i => ∏ j ∈ ({i}ᶜ : Finset ι), f j
    let e : ι → Polynomial K := fun i => μ i * Q i
    have hsum : (∑ i, Polynomial.aeval T (e i)) = 1 := by
      rw [← map_sum]
      simpa only [e, Q, map_one] using congrArg (Polynomial.aeval T) hμ
    have hQ (i : ι) : f i * Q i = ∏ j, f j := by
      simpa using Finset.prod_mul_prod_compl ({i} : Finset ι) f
    have hdiv (i j : ι) (hij : i ≠ j) : f j ∣ e i := by
      apply dvd_mul_of_dvd_right
      apply Finset.dvd_prod_of_mem
      simpa using hij.symm
    have hkill (i j : ι) (hij : i ≠ j) (v : V)
        (hv : v ∈ LinearMap.ker (Polynomial.aeval T (f j))) :
        Polynomial.aeval T (e i) v = 0 := by
      obtain ⟨r, hr⟩ := hdiv i j hij
      rw [hr, mul_comm, map_mul, Module.End.mul_apply, LinearMap.mem_ker.mp hv, map_zero]
    refine ⟨e, hsum, ?_, ?_⟩
    · intro i v
      simpa only [e, map_mul, Module.End.mul_apply] using
        (BezoutDecomposition.component_membership T (f i) (Q i)
        (by rw [hQ]; exact hz) 0 (μ i) v).1
    · intro i j v hv
      by_cases hij : i = j
      · subst j
        rw [ite_eq_left rfl]
        have hs := congrArg (fun A : Module.End K V => A v) hsum
        change (∑ j, Polynomial.aeval T (e j)) v = v at hs
        rw [LinearMap.sum_apply, Finset.sum_eq_single i] at hs
        · exact hs
        · intro j _ hji
          exact hkill j i hji v hv
        · simp
      · rw [ite_eq_right hij]
        exact hkill i j hij v hv
  · have : IsEmpty ι := not_nonempty_iff.mp hn
    have hone : (1 : Module.End K V) = 0 := by simpa using hz
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · simpa using hone.symm
    · intro i; exact isEmptyElim i
    · intro i; exact isEmptyElim i

/-- An annihilating pairwise coprime family has a unique kernel expansion;
its canonical component maps are the CRT polynomial maps. -/
theorem coprime_kernel_decomposition (T : Module.End K V) (f : ι → Polynomial K)
    (hc : Pairwise (fun i j => IsCoprime (f i) (f j)))
    (hz : Polynomial.aeval T (∏ i, f i) = 0) :
    let U := fun i => LinearMap.ker (Polynomial.aeval T (f i))
    ∃ h : Function.Bijective (Specs.D05.M06.ExternalSum.summationMap U),
      UniqueDecomposition U ∧
      ∀ i, ∃ e : Polynomial K, Polynomial.aeval T e = componentProjection U h i := by
  classical
  let U := fun i => LinearMap.ker (Polynomial.aeval T (f i))
  obtain ⟨e, hsum, hmem, hact⟩ := coprime_projector_polynomials T f hc hz
  have hextract (c : ∀ i, U i) (i : ι) :
      Polynomial.aeval T (e i) (∑ j, (c j : V)) = (c i : V) := by
    rw [map_sum]
    simp only [hact i _ _ (c _).property]
    simp
  have hU : UniqueDecomposition U := by
    intro v
    refine ⟨fun i => ⟨Polynomial.aeval T (e i) v, hmem i v⟩, ?_, ?_⟩
    · have hs := congrArg (fun A : Module.End K V => A v) hsum
      simpa only [LinearMap.sum_apply, Module.End.one_apply] using hs
    · intro c hc
      funext i
      apply Subtype.ext
      exact (hextract c i).symm.trans (congrArg (Polynomial.aeval T (e i)) hc)
  obtain ⟨h⟩ : Nonempty (Function.Bijective (Specs.D05.M06.ExternalSum.summationMap U)) :=
    ⟨(D05.M06.InvariantDecomposition.finite_internal_iff_bijective U).mp hU⟩
  refine ⟨h, hU, ?_⟩
  intro i
  refine ⟨e i, ?_⟩
  ext v
  obtain ⟨x, rfl⟩ := h.2 v
  calc
    Polynomial.aeval T (e i) (Specs.D05.M06.ExternalSum.summationMap U x) = (x i : V) := by
      rw [D05.M06.ExternalSum.summation_apply U x]
      exact hextract (fun j => x j) i
    _ = componentProjection U h i (Specs.D05.M06.ExternalSum.summationMap U x) :=
      (D05.M06.InvariantDecomposition.componentProjection_on_sum U h x i).symm

omit [Fintype ι] in
/-- Distinct monic irreducibles are coprime; positive powers remain coprime.
The polynomial Bézout coefficients come from the accepted factorization
foundation, rather than any operator decomposition assumption. -/
theorem primary_factors_pairwise_coprime (p : ι → Polynomial K) (a : ι → ℕ)
    (hm : ∀ i, (p i).Monic) (hi : ∀ i, Irreducible (p i))
    (hinj : Function.Injective p) :
    Pairwise (fun i j => IsCoprime (p i ^ a i) (p j ^ a j)) := by
  intro i j hij
  apply IsCoprime.pow
  apply Foundations.Factorization.irreducibleBezout K (p i) (p j) (hi i)
  intro hd
  apply hij
  apply hinj
  exact Polynomial.eq_of_monic_of_associated (hm i) (hm j)
    ((hi i).associated_of_dvd (hi j) hd)

theorem primary_decomposition : Specs.D05.M08.Primary.primary_decomposition := by
  intro K V ι _ _ _ _ _ T p a hm hi hinj _ha hfac
  classical
  let f := fun i => p i ^ a i
  have hz : Polynomial.aeval T (∏ i, f i) = 0 := by
    rw [← hfac]
    exact Minpoly.annihilates T
  obtain ⟨h, hU, he⟩ := coprime_kernel_decomposition T f
    (primary_factors_pairwise_coprime p a hm hi hinj) hz
  refine ⟨hU, ?_, ?_, h, ?_⟩
  · intro i
    simp only [map_pow]
  · intro i v hv
    exact BezoutDecomposition.kernel_invariant T (p i ^ a i) v hv
  · intro i
    obtain ⟨e, he⟩ := he i
    exact ⟨e, he, D05.M06.InvariantDecomposition.componentProjection_properties _ h i⟩

theorem minimalPolynomial_eq_one_iff_zero :
    Specs.D05.M08.Primary.minimalPolynomial_eq_one_iff_zero := by
  intro K V _ _ _ _ T
  constructor
  · intro hm v
    have hz := Minpoly.annihilates T
    rw [hm, map_one] at hz
    exact congrArg (fun A : Module.End K V => A v) hz
  · intro hv
    let : Subsingleton V := ⟨fun x y => (hv x).trans (hv y).symm⟩
    exact Minpoly.zero_space T

end D05.M08.Primary
