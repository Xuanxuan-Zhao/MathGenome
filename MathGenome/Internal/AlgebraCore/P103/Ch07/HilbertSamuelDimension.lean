import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.HilbertSamuelDimension
import MathGenome.Internal.AlgebraCore.P103.Ch06.SystemsParameters
import MathGenome.Internal.AlgebraCore.P103.Ch07.ArtinRees
import MathGenome.Internal.AlgebraCore.P103.Ch05.AssociatedFiniteness
import MathGenome.Internal.AlgebraCore.P103.Ch05.SupportGeometry
import MathGenome.Internal.AlgebraCore.P103.Ch05.PrimeAvoidance
import MathGenome.Internal.AlgebraCore.P103.Ch07.HilbertSamuelPolynomial
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The Hilbert–Samuel dimension formula. Polynomial existence comes from
the preceding polynomial stage; both degree bounds are proved here using
dimension induction, with Artin–Rees supplying the lower bound. -/
namespace P103.HilbertSamuelDimension

universe u v
open P103.HilbertSamuelPolynomial
open P103.Specs.Ch06.DimensionConventions
open Specs.P103.HilbertSamuelDimension

/-- A finite-length module over a local ring is killed by a power of every
ideal contained in the maximal ideal. This includes Q=0. -/
theorem powerSubmodule_eventually_zero (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (Q : Ideal R)
    (hQ : Q ≤ IsLocalRing.maximalIdeal R) (hM : IsFiniteLength R M) :
    ∃ N : ℕ, ∀ n ≥ N, powerSubmodule Q M n = ⊥ := by
  obtain ⟨N, hN⟩ := P103.Ch06.FiniteColength.finite_length_power R M hM
  refine ⟨N, fun n hn => ?_⟩
  have hle : Q ^ n ≤ Module.annihilator R M :=
    (Ideal.pow_le_pow_right hn).trans ((pow_le_pow_left' hQ N).trans hN)
  rw [← Submodule.annihilator_top, Submodule.le_annihilator_iff] at hle
  exact hle

/-- Once the power submodules vanish, the layers vanish and the quotients
identify with the original module, with their actual module lengths. -/
theorem lengths_of_powerSubmodule_zero (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (Q : Ideal R) (n : ℕ)
    (hn : powerSubmodule Q M n = ⊥) (hs : powerSubmodule Q M (n + 1) = ⊥) :
    layerLength Q M n = 0 ∧ quotientLength Q M n = (Module.length R M).toNat := by
  have : Subsingleton (powerSubmodule Q M n) := by rw [hn]; infer_instance
  constructor
  · simp [layerLength]
  · have he := (Submodule.quotEquivOfEqBot _ hs).length_eq
    exact congrArg ENat.toNat he

/-- In dimension zero, the layers vanish and the cumulative lengths become
a strictly positive constant. -/
theorem zero_dimension : zeroDimensionType.{u,v} := by
  intro R _ _ _ M _ _ _ _ Q hQ _ hd
  have hM := (P103.Ch06.SystemsParameters.dimension_zero_iff R M).mp hd
  obtain ⟨N, hN⟩ := powerSubmodule_eventually_zero R M Q hQ hM
  refine ⟨(Module.length R M).toNat,
    ENat.toNat_pos (Module.length_pos.ne') (Module.length_ne_top_iff.mpr hM), N, ?_⟩
  intro n hn
  exact lengths_of_powerSubmodule_zero R M Q n (hN n hn)
    (hN (n + 1) (by omega))

open Polynomial

/-- The backward difference keeps the original index n: p(n)-p(n-1). -/
noncomputable def backwardDifference (p : Polynomial ℚ) : Polynomial ℚ :=
  p - Polynomial.taylor (-1) p

/-- The top surviving coefficient in a backward difference. -/
theorem backwardDifference_coeff (p : Polynomial ℚ) (hp : 0 < p.natDegree) :
    (backwardDifference p).coeff (p.natDegree - 1) =
      (p.natDegree : ℚ) * p.leadingCoeff := by
  have hi : 1 + (p.natDegree - 1) = p.natDegree := by omega
  have hchoose : p.natDegree.choose (p.natDegree - 1) = p.natDegree := by
    conv_lhs => rw [← hi]
    simpa only [Nat.add_comm _ 1, hi] using Nat.choose_succ_self_right (p.natDegree - 1)
  have hder : (hasseDeriv (p.natDegree - 1) p).natDegree ≤ 1 :=
    (natDegree_hasseDeriv_le _ _).trans (by omega)
  rw [backwardDifference, coeff_sub, taylor_coeff,
    eq_X_add_C_of_natDegree_le_one hder]
  simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff,
    zero_add, Nat.choose_self, Nat.cast_one, one_mul, hi, hchoose, coeff_natDegree]
  ring

/-- In characteristic zero a nonconstant polynomial loses exactly one degree
under a backward difference, including the linear-to-constant boundary. -/
theorem backwardDifference_degree (p : Polynomial ℚ) (hp : 0 < p.natDegree) :
    backwardDifference p ≠ 0 ∧
      (backwardDifference p).natDegree = p.natDegree - 1 := by
  have hc : (backwardDifference p).coeff (p.natDegree - 1) ≠ 0 := by
    rw [backwardDifference_coeff p hp]
    exact mul_ne_zero (by exact_mod_cast hp.ne') (leadingCoeff_ne_zero.mpr
      (ne_zero_of_natDegree_gt hp))
  refine ⟨fun hz => hc (by simp [hz]), natDegree_eq_of_le_of_coeff_ne_zero ?_ hc⟩
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have hbound : (backwardDifference p).natDegree ≤ p.natDegree := by
    simpa only [backwardDifference, natDegree_taylor, max_self] using
      natDegree_sub_le p (taylor (-1) p)
  by_cases heq : k = p.natDegree
  · subst k
    simp only [backwardDifference, coeff_sub, coeff_taylor_natDegree,
      coeff_natDegree, sub_self]
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The backward difference of an eventual cumulative polynomial gives the
layer polynomial, using only the actual summation identity. -/
theorem layers_of_cumulative (a b : ℕ → ℕ)
    (hs : ∀ n, b n = ∑ j ∈ Finset.range (n + 1), a j)
    (p : Polynomial ℚ) (hp : EventuallyPolynomial b p) :
    EventuallyPolynomial a (backwardDifference p) := by
  obtain ⟨N, hN⟩ := hp
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hsum : b n = b (n - 1) + a n := by
    rw [hs n, hs (n - 1), Nat.sub_add_cancel (by omega : 1 ≤ n)]
    simpa using Finset.sum_range_succ a n
  have heval := hN n (by omega)
  have heval' := hN (n - 1) (by omega)
  have hcast : (n - 1 : ℕ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  simp only [backwardDifference, eval_sub, taylor_apply, eval_comp,
    eval_add, eval_X, eval_C, ← sub_eq_add_neg]
  rw [← hcast, ← heval, ← heval', hsum, Nat.cast_add]
  ring

/-- After the dimension computation, the layer assertion is a formal
consequence of taking a first difference. -/
theorem positive_layers_of_quotient_degree
    (hs : Specs.P103.HilbertSamuelPolynomial.sumLayersType.{u,v})
    (hdegree : quotientDegreeType.{u,v}) : positiveLayersType.{u,v} := by
  intro R _ _ _ M _ _ _ _ Q hQ hlen d hd hdpos
  obtain ⟨p, hp, _, hpd⟩ := hdegree R M Q hQ hlen d hd
  have hpos : 0 < p.natDegree := by omega
  obtain ⟨hnonzero, hnat⟩ := backwardDifference_degree p hpos
  exact ⟨backwardDifference p,
    layers_of_cumulative _ _ (hs R M Q hQ hlen) p hp,
    hnonzero, hnat.trans (congrArg (· - 1) hpd)⟩

/-- Eventual agreement on the original natural-number indices uniquely
determines the rational polynomial. -/
theorem eventuallyPolynomial_unique (f : ℕ → ℕ) (p q : Polynomial ℚ)
    (hp : EventuallyPolynomial f p) (hq : EventuallyPolynomial f q) : p = q := by
  obtain ⟨Np, hNp⟩ := hp
  obtain ⟨Nq, hNq⟩ := hq
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun n : ℕ => ((n + (Np + Nq) : ℕ) : ℚ)) := by
    intro a b hab
    dsimp only at hab
    have hab' : a + (Np + Nq) = b + (Np + Nq) := by exact_mod_cast hab
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro x ⟨n, rfl⟩
  exact (hNp _ (by omega)).symm.trans (hNq _ (by omega))

/-- A zero layer forces equality of consecutive powers; Nakayama then
annihilates that power. No faithfulness hypothesis on M is used. -/
theorem powerSubmodule_zero_of_layer_zero (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (Q : Ideal R) (hQ : Q ≤ IsLocalRing.maximalIdeal R) (n : ℕ)
    (hfinite : IsFiniteLength R (Layer Q M n)) (hz : layerLength Q M n = 0) :
    powerSubmodule Q M n = ⊥ := by
  have hlen : Module.length R (Layer Q M n) = 0 := by
    exact (ENat.toNat_eq_zero.mp hz).resolve_right (Module.length_ne_top_iff.mpr hfinite)
  have hsub : Subsingleton (Layer Q M n) := Module.length_eq_zero_iff.mp hlen
  have htop : successorSubmodule Q M n = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hsub
  have hle : powerSubmodule Q M n ≤ powerSubmodule Q M (n + 1) := by
    intro m hm
    have hmem : (⟨m, hm⟩ : powerSubmodule Q M n) ∈ successorSubmodule Q M n := by
      rw [htop]; trivial
    exact hmem
  have hsmul : powerSubmodule Q M (n + 1) = Q • powerSubmodule Q M n := by
    simp only [powerSubmodule, pow_succ', Submodule.mul_smul]
  rw [hsmul] at hle
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot Q _
    (IsNoetherian.noetherian _) hle
    (hQ.trans (IsLocalRing.maximalIdeal_le_jacobson _))

/-- An eventual constant cumulative length forces dimension zero, by the
summation formula and Nakayama on a power submodule. -/
theorem dimension_zero_of_eventually_constant
    (hf : Specs.P103.HilbertSamuelPolynomial.finiteLengthsType.{u,v})
    (hs : Specs.P103.HilbertSamuelPolynomial.sumLayersType.{u,v})
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R) (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (hlen : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))))
    (c : ℚ) (hc : EventuallyPolynomial (quotientLength Q M) (C c)) :
    moduleDimensionValue R M = 0 := by
  obtain ⟨N, hN⟩ := layers_of_cumulative _ _ (hs R M Q hQ hlen) (C c) hc
  have hzero : layerLength Q M N = 0 := by
    have h := hN N le_rfl
    simpa [backwardDifference] using h
  have hpower := powerSubmodule_zero_of_layer_zero R M Q hQ N
    (hf R M Q hQ hlen N).1 hzero
  have hnext : powerSubmodule Q M (N + 1) = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← hpower]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ N))
  have hM : IsFiniteLength R M :=
    (hf R M Q hQ hlen N).2.of_surjective (Submodule.quotEquivOfEqBot _ hnext).surjective
  exact (P103.Ch06.SystemsParameters.dimension_zero_iff R M).mpr hM

/-- Consequently every cumulative polynomial in positive dimension is
nonconstant. This is the first step of the source's lower-bound induction. -/
theorem polynomial_degree_pos_of_dimension_ne_zero
    (hf : Specs.P103.HilbertSamuelPolynomial.finiteLengthsType.{u,v})
    (hs : Specs.P103.HilbertSamuelPolynomial.sumLayersType.{u,v})
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R) (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (hlen : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))))
    (hd : moduleDimensionValue R M ≠ 0)
    (p : Polynomial ℚ) (hp : EventuallyPolynomial (quotientLength Q M) p) :
    0 < p.natDegree := by
  by_contra! h
  have hpc : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero h
  rw [hpc] at hp
  exact hd (dimension_zero_of_eventually_constant hf hs R M Q hQ hlen _ hp)

/-- An inclusion on the action of two ideals can be iterated on M. This
formulation also works when M has a nonzero annihilator. -/
theorem powerSubmodule_mul_le (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (I J : Ideal R) (s : ℕ)
    (h : powerSubmodule J M s ≤ powerSubmodule I M 1) :
    ∀ k : ℕ, powerSubmodule J M (s * k) ≤ powerSubmodule I M k := by
  intro k
  induction k with
  | zero => simp [powerSubmodule]
  | succ k ih =>
    calc
      powerSubmodule J M (s * (k + 1)) =
          J ^ (s * k) • (J ^ s • (⊤ : Submodule R M)) := by
        simp only [powerSubmodule, Nat.mul_add, Nat.mul_one, pow_add, Submodule.mul_smul]
      _ ≤ J ^ (s * k) • (I • (⊤ : Submodule R M)) :=
        smul_mono_right _ (by simpa [powerSubmodule] using h)
      _ = I • powerSubmodule J M (s * k) := by
        simp only [powerSubmodule, ← Submodule.mul_smul, mul_comm]
      _ ≤ I • powerSubmodule I M k := smul_mono_right _ ih
      _ = powerSubmodule I M (k + 1) := by
        simp only [powerSubmodule, pow_succ', Submodule.mul_smul]

/-- Finite colength gives the required power inclusion on M itself. It does
not require a power of the maximal ideal to lie in Q as ideals of R. -/
theorem maximal_power_le_of_finite_colength (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (Q : Ideal R)
    (hlen : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M)))) :
    ∃ s : ℕ, 0 < s ∧
      powerSubmodule (IsLocalRing.maximalIdeal R) M s ≤ powerSubmodule Q M 1 := by
  obtain ⟨s, hs⟩ := P103.Ch06.FiniteColength.finite_length_power R
    (M ⧸ (Q • (⊤ : Submodule R M))) hlen
  refine ⟨s + 1, by omega, ?_⟩
  have hkill : (IsLocalRing.maximalIdeal R) ^ (s + 1) ≤
      Module.annihilator R (M ⧸ (Q • (⊤ : Submodule R M))) :=
    (Ideal.pow_le_pow_right (Nat.le_succ s)).trans hs
  change (IsLocalRing.maximalIdeal R) ^ (s + 1) • (⊤ : Submodule R M) ≤ _
  apply Submodule.smul_le.mpr
  intro r hr m _
  have hz := Module.mem_annihilator.mp (hkill hr)
    ((Q • (⊤ : Submodule R M)).mkQ m)
  change r • m ∈ Q ^ 1 • (⊤ : Submodule R M)
  rw [pow_one]
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change (Q • (⊤ : Submodule R M)).mkQ (r • m) = 0
  simpa only [map_smul] using hz

/-- Monotonicity of the actual lengths of finite quotients. -/
theorem quotientLength_le_of_powerSubmodule_le (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (I J : Ideal R) (a b : ℕ)
    (h : powerSubmodule J M (b + 1) ≤ powerSubmodule I M (a + 1))
    (hfinite : IsFiniteLength R (Quotient J M b)) :
    quotientLength I M a ≤ quotientLength J M b := by
  let f := (powerSubmodule J M (b + 1)).mapQ (powerSubmodule I M (a + 1))
    (LinearMap.id : M →ₗ[R] M) (by simpa using h)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨m, rfl⟩ := (powerSubmodule I M (a + 1)).mkQ_surjective z
    exact ⟨(powerSubmodule J M (b + 1)).mkQ m, rfl⟩
  exact ENat.toNat_le_toNat (Module.length_le_of_surjective f hf)
    (Module.length_ne_top_iff.mpr hfinite)

/-- Finite colength passes to any larger ideal. -/
theorem finite_colength_mono (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (I J : Ideal R) (hIJ : I ≤ J)
    (hlen : IsFiniteLength R (M ⧸ (I • (⊤ : Submodule R M)))) :
    IsFiniteLength R (M ⧸ (J • (⊤ : Submodule R M))) := by
  let f := (I • (⊤ : Submodule R M)).mapQ (J • (⊤ : Submodule R M))
    (LinearMap.id : M →ₗ[R] M) (by simpa using Submodule.smul_mono_left hIJ)
  apply hlen.of_surjective (f := f)
  intro z
  obtain ⟨a, rfl⟩ := (J • (⊤ : Submodule R M)).mkQ_surjective z
  exact ⟨(I • (⊤ : Submodule R M)).mkQ a, rfl⟩

/-- The source's two comparisons, with the original shifted indices and
without passing to a faithful scalar action. -/
theorem quotientLength_comparison
    (hf : Specs.P103.HilbertSamuelPolynomial.finiteLengthsType.{u,v})
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R) (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (hlen : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M)))) :
    ∃ s : ℕ, 0 < s ∧ ∀ n : ℕ,
      quotientLength (IsLocalRing.maximalIdeal R) M n ≤ quotientLength Q M n ∧
      quotientLength Q M n ≤
        quotientLength (IsLocalRing.maximalIdeal R) M (s * (n + 1) - 1) := by
  let m := IsLocalRing.maximalIdeal R
  have hlenm : IsFiniteLength R (M ⧸ (m • (⊤ : Submodule R M))) :=
    finite_colength_mono R M Q m hQ hlen
  obtain ⟨s, hs, hpower⟩ := maximal_power_le_of_finite_colength R M Q hlen
  refine ⟨s, hs, fun n => ⟨?_, ?_⟩⟩
  · exact quotientLength_le_of_powerSubmodule_le R M m Q n n
      (Submodule.smul_mono_left (pow_le_pow_left' hQ (n + 1)))
      (hf R M Q hQ hlen n).2
  · apply quotientLength_le_of_powerSubmodule_le R M Q m n (s * (n + 1) - 1) _
      (hf R M m le_rfl hlenm _).2
    have hindex : s * (n + 1) - 1 + 1 = s * (n + 1) := by
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hs (by omega)))
    rw [hindex]
    exact powerSubmodule_mul_le R M Q m s hpower (n + 1)

/-- Eventual order bounds the degree of a polynomial with positive leading
coefficient. This version applies to rational polynomials on natural indices. -/
theorem natDegree_le_of_eventually_eval_le (p q : Polynomial ℚ)
    (hp : 0 < p.leadingCoeff) (h : ∃ N : ℕ, ∀ n ≥ N, p.eval (n : ℚ) ≤ q.eval (n : ℚ)) :
    p.natDegree ≤ q.natDegree := by
  by_contra! hdeg
  have hdiff : (p - q).natDegree = p.natDegree :=
    natDegree_sub_eq_left_of_natDegree_lt hdeg
  have hlc : (p - q).leadingCoeff = p.leadingCoeff :=
    leadingCoeff_sub_of_degree_lt (degree_lt_degree hdeg)
  have hpos : 0 < (p - q).degree :=
    natDegree_pos_iff_degree_pos.mp (by rw [hdiff]; omega)
  have ht := (p - q).tendsto_atTop_of_leadingCoeff_nonneg hpos (by rw [hlc]; exact hp.le)
  have ht' := ht.comp (tendsto_natCast_atTop_atTop (R := ℚ))
  obtain ⟨N, hN⟩ := h
  have he := ht'.eventually_gt_atTop 0
  obtain ⟨n, hn, hgt⟩ := (Filter.eventually_atTop.2 ⟨N, hN⟩).and he |>.exists
  dsimp only [Function.comp_apply] at hgt
  rw [eval_sub] at hgt
  linarith

/-- The comparison with an affine reindexing preserves polynomial degree. -/
theorem degrees_eq_of_sandwich (f g : ℕ → ℕ) (p q : Polynomial ℚ)
    (hf : EventuallyPolynomial f p) (hg : EventuallyPolynomial g q)
    (hp : 0 < p.natDegree → 0 < p.leadingCoeff)
    (hq : 0 < q.natDegree → 0 < q.leadingCoeff)
    (s : ℕ) (hs : 0 < s)
    (h : ∀ n, f n ≤ g n ∧ g n ≤ f (s * (n + 1) - 1)) :
    p.natDegree = q.natDegree := by
  obtain ⟨Np, hNp⟩ := hf
  obtain ⟨Nq, hNq⟩ := hg
  apply le_antisymm
  · by_cases hp0 : p.natDegree = 0
    · omega
    apply natDegree_le_of_eventually_eval_le p q (hp (by omega))
    refine ⟨Np + Nq, fun n hn => ?_⟩
    rw [← hNp n (by omega), ← hNq n (by omega)]
    exact_mod_cast (h n).1
  · by_cases hq0 : q.natDegree = 0
    · omega
    let a : Polynomial ℚ := C (s : ℚ) * (X + C 1) - C 1
    have ha : a.natDegree = 1 := by
      dsimp only [a]
      rw [natDegree_sub_C,
        natDegree_C_mul (show (s : ℚ) ≠ 0 by exact_mod_cast hs.ne'), natDegree_X_add_C]
    have hcomp : (p.comp a).natDegree = p.natDegree := by
      rw [natDegree_comp, ha, Nat.mul_one]
    rw [← hcomp]
    apply natDegree_le_of_eventually_eval_le q (p.comp a) (hq (by omega))
    refine ⟨Np + Nq, fun n hn => ?_⟩
    have hind : n ≤ s * (n + 1) - 1 := by
      have hmul : n + 1 ≤ s * (n + 1) := by
        simpa using Nat.mul_le_mul_right (n + 1) (show 1 ≤ s by omega)
      omega
    have hcast : ((s * (n + 1) - 1 : ℕ) : ℚ) = (s : ℚ) * ((n : ℚ) + 1) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt (Nat.mul_pos hs (show 0 < n + 1 by omega)))]
      push_cast
      ring
    simp only [eval_comp, a, eval_sub, eval_mul, eval_add, eval_C, eval_X]
    rw [← hcast, ← hNp _ (by omega), ← hNq n (by omega)]
    exact_mod_cast (h n).2

/-- Any cumulative polynomial supplied by the quotient-polynomial
interface has the same degree as one for the maximal ideal. -/
theorem quotient_polynomial_degree_eq_maximal
    (hf : Specs.P103.HilbertSamuelPolynomial.finiteLengthsType.{u,v})
    (hq : Specs.P103.HilbertSamuelPolynomial.quotientPolynomialType.{u,v})
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R) (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (hlen : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M)))) :
    ∃ p q : Polynomial ℚ,
      EventuallyPolynomial (quotientLength Q M) p ∧ p ≠ 0 ∧
      EventuallyPolynomial (quotientLength (IsLocalRing.maximalIdeal R) M) q ∧ q ≠ 0 ∧
      p.natDegree = q.natDegree := by
  obtain ⟨p, hp, hp0, hppos⟩ := hq R M Q hQ hlen
  have hlenm := finite_colength_mono R M Q (IsLocalRing.maximalIdeal R) hQ hlen
  obtain ⟨q, hq', hq0, hqpos⟩ := hq R M (IsLocalRing.maximalIdeal R) le_rfl hlenm
  obtain ⟨s, hs, hcmp⟩ := quotientLength_comparison hf R M Q hQ hlen
  exact ⟨p, q, hp, hp0, hq', hq0,
    (degrees_eq_of_sandwich _ _ q p hq' hp hqpos hppos s hs hcmp).symm⟩

/-- Quotient length decreases with the submodule being divided out. -/
theorem length_quotient_antitone (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (A B : Submodule R M) (hAB : A ≤ B) :
    Module.length R (M ⧸ B) ≤ Module.length R (M ⧸ A) := by
  let f := A.mapQ B (LinearMap.id : M →ₗ[R] M) (by simpa using hAB)
  apply Module.length_le_of_surjective f
  intro z
  obtain ⟨m, rfl⟩ := B.mkQ_surjective z
  exact ⟨A.mkQ m, rfl⟩

/-- Length decomposition by the image of a submodule in a quotient. -/
theorem length_quotient_eq_image_add (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (A S : Submodule R M) :
    Module.length R (M ⧸ A) = Module.length R (S.map A.mkQ) +
      Module.length R (M ⧸ (A ⊔ S)) := by
  rw [Module.length_eq_add_of_exact (S.map A.mkQ).subtype (S.map A.mkQ).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _),
    (Submodule.quotientQuotientEquivQuotientSup A S).length_eq]

/-- The kernel contribution is at most the length of the original submodule. -/
theorem length_quotient_le_sup_add (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (A K : Submodule R M) :
    Module.length R (M ⧸ A) ≤ Module.length R K +
      Module.length R (M ⧸ (A ⊔ K)) := by
  rw [length_quotient_eq_image_add R M A K]
  apply add_le_add_left
  let f : K →ₗ[R] K.map A.mkQ :=
    { toFun := fun k => ⟨A.mkQ k, ⟨k, k.property, rfl⟩⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply Module.length_le_of_surjective f
  rintro ⟨z, m, hm, rfl⟩
  exact ⟨⟨m, hm⟩, rfl⟩

/-- The algebraic length inequality behind the source's Artin–Rees estimate.
It is valid for extended lengths, without finiteness or injectivity assumptions. -/
theorem length_estimate_of_range_inf_le (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (f : M →ₗ[R] M)
    (A B : Submodule R M) (h : LinearMap.range f ⊓ A ≤ B.map f) :
    Module.length R (M ⧸ (A ⊔ LinearMap.range f)) + Module.length R (M ⧸ B) ≤
      Module.length R (M ⧸ A) + Module.length R (LinearMap.ker f) := by
  let g : M →ₗ[R] M ⧸ A := A.mkQ.comp f
  have hker : LinearMap.ker g ≤ B ⊔ LinearMap.ker f := by
    intro m hm
    have hmA : f m ∈ A := (Submodule.Quotient.mk_eq_zero A).mp hm
    obtain ⟨b, hb, hbm⟩ := h ⟨LinearMap.mem_range_self f m, hmA⟩
    have hmk : m - b ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, hbm, sub_self]
    exact Submodule.mem_sup.mpr ⟨b, hb, m - b, hmk, by abel⟩
  have hbound : Module.length R (M ⧸ B) ≤
      Module.length R (LinearMap.ker f) + Module.length R (LinearMap.range g) := by
    calc
      Module.length R (M ⧸ B) ≤ Module.length R (LinearMap.ker f) +
          Module.length R (M ⧸ (B ⊔ LinearMap.ker f)) :=
        length_quotient_le_sup_add R M B (LinearMap.ker f)
      _ ≤ Module.length R (LinearMap.ker f) + Module.length R (M ⧸ LinearMap.ker g) :=
        add_le_add_right (length_quotient_antitone R M _ _ hker) _
      _ = _ := by rw [g.quotKerEquivRange.length_eq]
  have hrange : LinearMap.range g = (LinearMap.range f).map A.mkQ := by
    exact LinearMap.range_comp f A.mkQ
  have hdecomp : Module.length R (M ⧸ A) = Module.length R (LinearMap.range g) +
      Module.length R (M ⧸ (A ⊔ LinearMap.range f)) := by
    rw [hrange]
    exact length_quotient_eq_image_add R M A (LinearMap.range f)
  calc
    _ ≤ Module.length R (M ⧸ (A ⊔ LinearMap.range f)) +
        (Module.length R (LinearMap.ker f) + Module.length R (LinearMap.range g)) :=
      add_le_add_right hbound _
    _ = _ := by rw [hdecomp]; ac_rfl

/-- Applying Artin–Rees to the image of an endomorphism gives the precise
submodule inclusion used in the length estimate, with a positive shift. -/
theorem range_inf_powerSubmodule_le (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (Q : Ideal R) (f : M →ₗ[R] M) :
    ∃ c : ℕ, 0 < c ∧ ∀ n ≥ c,
      LinearMap.range f ⊓ powerSubmodule Q M (n + 1) ≤
        (powerSubmodule Q M (n - c + 1)).map f := by
  obtain ⟨c, hc⟩ := P103.Ch07.ArtinRees.artin_rees R Q M (LinearMap.range f)
  refine ⟨c + 1, by omega, fun n hn => ?_⟩
  rw [inf_comm, powerSubmodule, hc (n + 1) (by omega)]
  calc
    Q ^ (n + 1 - c) • (Q ^ c • ⊤ ⊓ LinearMap.range f) ≤
        Q ^ (n + 1 - c) • LinearMap.range f := smul_mono_right _ inf_le_right
    _ ≤ Q ^ (n - (c + 1) + 1) • LinearMap.range f :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
    _ = _ := by simp only [powerSubmodule, Submodule.map_smul'', Submodule.map_top]

/-- The Artin–Rees lower-bound estimate in additive form, avoiding truncated
subtraction. The source specializes f to multiplication by a selected scalar. -/
theorem artin_rees_length_estimate (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (Q : Ideal R) (f : M →ₗ[R] M) :
    ∃ c : ℕ, 0 < c ∧ ∀ n ≥ c,
      Module.length R (M ⧸ (powerSubmodule Q M (n + 1) ⊔ LinearMap.range f)) +
        Module.length R (Quotient Q M (n - c)) ≤
      Module.length R (Quotient Q M n) + Module.length R (LinearMap.ker f) := by
  obtain ⟨c, hc, hAR⟩ := range_inf_powerSubmodule_le R M Q f
  exact ⟨c, hc, fun n hn => length_estimate_of_range_inf_le R M f _ _ (hAR n hn)⟩

/-- Quotienting M first commutes with ideal powers, and the resulting
subquotient length is that of M/(Q^(n+1)M+S). -/
theorem length_quotient_of_quotient (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (Q : Ideal R)
    (S : Submodule R M) (n : ℕ) :
    Module.length R (Quotient Q (M ⧸ S) n) =
      Module.length R (M ⧸ (powerSubmodule Q M (n + 1) ⊔ S)) := by
  have hmap : (powerSubmodule Q M (n + 1)).map S.mkQ =
      powerSubmodule Q (M ⧸ S) (n + 1) := by
    simp only [powerSubmodule, Submodule.map_smul'', Submodule.map_top, S.range_mkQ]
  change Module.length R ((M ⧸ S) ⧸ powerSubmodule Q (M ⧸ S) (n + 1)) = _
  rw [← hmap, sup_comm (powerSubmodule Q M (n + 1)) S]
  exact (Submodule.quotientQuotientEquivQuotientSup S _).length_eq

/-- Natural-length form of the Artin–Rees estimate, valid for arbitrary
endomorphisms with a finite-length kernel, including zero quotient modules. -/
theorem artin_rees_quotientLength_estimate
    (hf : Specs.P103.HilbertSamuelPolynomial.finiteLengthsType.{u,v})
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R) (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (hlen : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))))
    (f : M →ₗ[R] M) (hK : IsFiniteLength R (LinearMap.ker f)) :
    ∃ c : ℕ, 0 < c ∧ ∀ n ≥ c,
      quotientLength Q (M ⧸ LinearMap.range f) n + quotientLength Q M (n - c) ≤
        quotientLength Q M n + (Module.length R (LinearMap.ker f)).toNat := by
  obtain ⟨c, hc, hAR⟩ := artin_rees_length_estimate R M Q f
  refine ⟨c, hc, fun n hn => ?_⟩
  have hMn := Module.length_ne_top_iff.mpr (hf R M Q hQ hlen n).2
  have hMnc := Module.length_ne_top_iff.mpr (hf R M Q hQ hlen (n - c)).2
  have hK' := Module.length_ne_top_iff.mpr hK
  have hNn : Module.length R (M ⧸ (powerSubmodule Q M (n + 1) ⊔ LinearMap.range f)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (length_quotient_antitone R M _ _ le_sup_left) hMn.lt_top)
  have hnat := ENat.toNat_le_toNat (hAR n hn) (by
    simpa only [ne_eq, ENat.add_eq_top, not_or] using And.intro hMn hK')
  rw [ENat.toNat_add hNn hMnc, ENat.toNat_add hMn hK'] at hnat
  simpa only [quotientLength, length_quotient_of_quotient] using hnat

/-- Cancellation of the top coefficient bounds the degree of every shifted
difference, even before proving that the shift is nonzero. -/
theorem natDegree_sub_taylor_le (p : Polynomial ℚ) (a : ℚ) :
    (p - taylor a p).natDegree ≤ p.natDegree - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have hbound : (p - taylor a p).natDegree ≤ p.natDegree := by
    simpa only [natDegree_taylor, max_self] using natDegree_sub_le p (taylor a p)
  by_cases heq : k = p.natDegree
  · subst k
    simp only [coeff_sub, coeff_taylor_natDegree, coeff_natDegree, sub_self]
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The nonzero cumulative polynomials in the polynomial-stage interface have
positive leading coefficient also in the constant case. -/
theorem leadingCoeff_pos_of_eventuallyPolynomial (f : ℕ → ℕ) (p : Polynomial ℚ)
    (hp : EventuallyPolynomial f p) (hp0 : p ≠ 0)
    (hpos : 0 < p.natDegree → 0 < p.leadingCoeff) : 0 < p.leadingCoeff := by
  by_cases hd : p.natDegree = 0
  · obtain ⟨N, hN⟩ := hp
    have hC : p = C p.leadingCoeff := by
      simpa only [leadingCoeff, hd] using eq_C_of_natDegree_eq_zero hd
    have hnonneg : 0 ≤ p.leadingCoeff := by
      have he := hN N le_rfl
      rw [hC, eval_C] at he
      exact he ▸ Nat.cast_nonneg (f N)
    exact lt_of_le_of_ne hnonneg (leadingCoeff_ne_zero.mpr hp0).symm
  · exact hpos (by omega)

/-- An Artin–Rees comparison forces a strict degree drop after quotienting
by an endomorphism with finite-length kernel. The dimension induction still
has to supply the scalar and identify the dimension of this quotient. -/
theorem quotient_polynomial_degree_drop
    (hf : Specs.P103.HilbertSamuelPolynomial.finiteLengthsType.{u,v})
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R) (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (hlen : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))))
    (f : M →ₗ[R] M) (hK : IsFiniteLength R (LinearMap.ker f))
    (p q : Polynomial ℚ) (hp : EventuallyPolynomial (quotientLength Q M) p)
    (hq : EventuallyPolynomial (quotientLength Q (M ⧸ LinearMap.range f)) q)
    (hqlc : 0 < q.leadingCoeff) :
    q.natDegree ≤ p.natDegree - 1 := by
  obtain ⟨c, hc, hAR⟩ := artin_rees_quotientLength_estimate hf R M Q hQ hlen f hK
  obtain ⟨Np, hNp⟩ := hp
  obtain ⟨Nq, hNq⟩ := hq
  let r : Polynomial ℚ := p - taylor (-(c : ℚ)) p +
    C ((Module.length R (LinearMap.ker f)).toNat : ℚ)
  have hr : r.natDegree ≤ p.natDegree - 1 := by
    simpa only [r, natDegree_add_C] using natDegree_sub_taylor_le p (-(c : ℚ))
  apply le_trans (natDegree_le_of_eventually_eval_le q r hqlc ?_) hr
  refine ⟨Np + Nq + c, fun n hn => ?_⟩
  have hcast : ((n - c : ℕ) : ℚ) = (n : ℚ) - (c : ℚ) := Nat.cast_sub (by omega)
  have hnat := hAR n (by omega)
  have hrat : (quotientLength Q (M ⧸ LinearMap.range f) n : ℚ) +
      (quotientLength Q M (n - c) : ℚ) ≤
      (quotientLength Q M n : ℚ) + (Module.length R (LinearMap.ker f)).toNat := by
    exact_mod_cast hnat
  rw [hNq n (by omega), hNp n (by omega), hNp (n - c) (by omega), hcast] at hrat
  simp only [r, eval_add, eval_sub, taylor_apply, eval_comp, eval_add, eval_X, eval_C,
    ← sub_eq_add_neg]
  linarith

/-- Prime avoidance selects a scalar which is regular away from the closed
point. The formulation retains an arbitrary finite-length kernel. -/
theorem exists_scalar_finite_length_kernel (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R)
    (hI : ∀ P ∈ associatedPrimes R M, P ≠ IsLocalRing.maximalIdeal R → ¬ I ≤ P) :
    ∃ x : R, x ∈ I ∧
      (∀ P ∈ associatedPrimes R M, P ≠ IsLocalRing.maximalIdeal R → x ∉ P) ∧
      IsFiniteLength R (LinearMap.ker (LinearMap.lsmul R M x)) := by
  classical
  let m := IsLocalRing.maximalIdeal R
  let s : Set (Ideal R) := associatedPrimes R M \ {m}
  have hs : s.Finite := (associatedPrimes.finite R M).sdiff
  have hnotcover : ¬ (I : Set R) ⊆ ⋃ P ∈ s, (P : Set R) := by
    intro hcover
    obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime_finite hs m m
      (fun P hP _ _ => hP.1.isPrime)).mp hcover
    exact hI P hP.1 (by simpa only [Set.mem_singleton_iff] using hP.2) hle
  obtain ⟨x, hxm, hx⟩ := Set.not_subset.mp hnotcover
  have havoid : ∀ P ∈ associatedPrimes R M, P ≠ m → x ∉ P := by
    intro P hP hPm hxP
    exact hx (Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr
      ⟨⟨hP, by simpa only [Set.mem_singleton_iff] using hPm⟩, hxP⟩⟩)
  refine ⟨x, hxm, havoid, ?_⟩
  let f : M →ₗ[R] M := LinearMap.lsmul R M x
  let K := LinearMap.ker f
  by_cases hK : Subsingleton K
  · exact IsFiniteLength.of_subsingleton
  · have : Nontrivial K := not_subsingleton_iff_nontrivial.mp hK
    have hxK : x ∈ Module.annihilator R K := by
      apply Module.mem_annihilator.mpr
      intro k
      apply Subtype.ext
      exact k.property
    apply P103.Ch06.FiniteColength.finite_length_of_support_singleton R K
    ext p
    constructor
    · intro hp
      obtain ⟨P, hP, hPp⟩ := Ideal.exists_minimalPrimes_le (Module.mem_support_iff_of_finite.mp hp)
      have hPa := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R K hP
      have hPM := associatedPrimes.subset_of_injective K.subtype_injective hPa
      have hxP : x ∈ P := IsAssociatedPrime.annihilator_le hPa
        (by simpa only [Submodule.annihilator_top] using hxK)
      have hPm : P = m := by
        by_contra hPm
        exact havoid P hPM hPm hxP
      have hpEq : p = IsLocalRing.closedPoint R := by
        apply PrimeSpectrum.ext
        change p.asIdeal = IsLocalRing.maximalIdeal R
        exact le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
          (by simpa only [hPm, m] using hPp)
      exact Set.mem_singleton_iff.mpr hpEq
    · intro hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      exact IsLocalRing.closedPoint_mem_support R K

/-- In positive dimension the same scalar can be chosen to lower module
dimension by exactly one. This supplies the geometric step of the induction. -/
theorem exists_scalar_dimension_drop (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] (Q : Ideal R) (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (hlen : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))))
    (hd : moduleDimensionValue R M ≠ 0) :
    ∃ x : R, x ∈ Q ∧
      IsFiniteLength R (LinearMap.ker (LinearMap.lsmul R M x)) ∧
      Nontrivial (M ⧸ LinearMap.range (LinearMap.lsmul R M x)) ∧
      moduleDimensionValue R (M ⧸ LinearMap.range (LinearMap.lsmul R M x)) + 1 =
        moduleDimensionValue R M := by
  have hrad := (P103.Ch06.FiniteColength.finite_colength_iff R M Q hQ).mp hlen
  have hI : ∀ P ∈ associatedPrimes R M, P ≠ IsLocalRing.maximalIdeal R → ¬ Q ≤ P := by
    intro P hP hPm hQP
    have hAnn : Module.annihilator R M ≤ P := by
      simpa only [Submodule.annihilator_top] using IsAssociatedPrime.annihilator_le hP
    have hmP : IsLocalRing.maximalIdeal R ≤ P := by
      rw [← hrad]
      exact hP.isPrime.radical_le_iff.mpr (sup_le hQP hAnn)
    exact hPm (le_antisymm (IsLocalRing.le_maximalIdeal hP.isPrime.ne_top) hmP)
  obtain ⟨x, hxQ, havoid, hK⟩ := exists_scalar_finite_length_kernel R M Q hI
  have hxm := hQ hxQ
  have hn : ∀ P ∈ (Module.annihilator R M).minimalPrimes, x ∉ P := by
    intro P hP
    apply havoid P
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hP)
    intro hPm
    have hrad := (P103.Ch06.SystemsParameters.maximal_mem_minimalPrimes_iff R
      (Module.annihilator R M)).mp (hPm ▸ hP)
    have hsupp : Module.support R M = {IsLocalRing.closedPoint R} := by
      rw [Module.support_eq_zeroLocus,
        P103.Ch06.FiniteColength.zeroLocus_eq_closedPoint_iff]
      exact hrad
    exact hd ((P103.Ch06.SystemsParameters.dimension_zero_iff R M).mpr
      (P103.Ch06.FiniteColength.finite_length_of_support_singleton R M hsupp))
  open scoped Pointwise in
  have hrange : LinearMap.range (LinearMap.lsmul R M x) = x • (⊤ : Submodule R M) := by
    ext z
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      LinearMap.mem_range, LinearMap.lsmul_apply]
  have hd' := Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal hn hxm
  rw [← P103.Ch06.SystemsParameters.moduleDimension_eq_supportDim R M,
    ← P103.Ch06.SystemsParameters.moduleDimension_eq_supportDim R _] at hd'
  have hN : Nontrivial (M ⧸ LinearMap.range (LinearMap.lsmul R M x)) := by
    rw [hrange, ← Submodule.ideal_span_singleton_smul]
    exact P103.Ch06.FiniteColength.quotient_nontrivial R M _
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxm))
  exact ⟨x, hxQ, hK, hN, hrange ▸ hd'⟩

/-- Finite colength survives taking an arbitrary module quotient. -/
theorem finite_colength_module_quotient (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (Q : Ideal R) (S : Submodule R M)
    (h : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M)))) :
    IsFiniteLength R ((M ⧸ S) ⧸ (Q • (⊤ : Submodule R (M ⧸ S)))) := by
  have hlen : Module.length R (Quotient Q (M ⧸ S) 0) ≠ ⊤ := by
    rw [length_quotient_of_quotient]
    have hbound := length_quotient_antitone R M (Q • (⊤ : Submodule R M))
      (powerSubmodule Q M (0 + 1) ⊔ S) (by simp [powerSubmodule])
    exact ne_of_lt (lt_of_le_of_lt hbound (Module.length_ne_top_iff.mpr h).lt_top)
  apply Module.length_ne_top_iff.mp
  change Module.length R ((M ⧸ S) ⧸ (Q ^ (0 + 1) • (⊤ : Submodule R (M ⧸ S)))) ≠ ⊤ at hlen
  rw [pow_one] at hlen
  exact hlen

/-- The full dimension lower bound. The proof uses the finite-length-kernel
scalar, induction on dimension, and the Artin–Rees degree-drop estimate. -/
theorem dimension_le_polynomial_degree
    (hf : Specs.P103.HilbertSamuelPolynomial.finiteLengthsType.{u,v})
    (hs : Specs.P103.HilbertSamuelPolynomial.sumLayersType.{u,v})
    (hq : Specs.P103.HilbertSamuelPolynomial.quotientPolynomialType.{u,v}) :
    ∀ (d : ℕ) (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
      (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
      (Q : Ideal R), Q ≤ IsLocalRing.maximalIdeal R →
      IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))) →
      moduleDimensionValue R M = (d : WithBot ℕ∞) →
      ∀ p : Polynomial ℚ, EventuallyPolynomial (quotientLength Q M) p → d ≤ p.natDegree := by
  intro d
  induction d with
  | zero => intros; exact Nat.zero_le _
  | succ d ih =>
    intro R _ _ _ M _ _ _ _ Q hQ hlen hd p hp
    have hd0 : moduleDimensionValue R M ≠ 0 := by
      rw [hd]
      exact_mod_cast Nat.succ_ne_zero d
    obtain ⟨x, _hxm, hK, hN, hdim⟩ := exists_scalar_dimension_drop R M Q hQ hlen hd0
    let f : M →ₗ[R] M := LinearMap.lsmul R M x
    let N := M ⧸ LinearMap.range f
    have : Nontrivial N := hN
    obtain ⟨e, he, _⟩ := P103.Ch06.SystemsParameters.parameter_count R N
    have heq : e = d := by
      change moduleDimensionValue R N + 1 = moduleDimensionValue R M at hdim
      rw [he, hd] at hdim
      have hh : e + 1 = d + 1 := by exact_mod_cast hdim
      omega
    subst e
    have hlenN := finite_colength_module_quotient R M Q (LinearMap.range f) hlen
    obtain ⟨q, hq', hq0, hqpos⟩ := hq R N Q hQ hlenN
    have hind : d ≤ q.natDegree := ih R N Q hQ hlenN he q hq'
    have hdrop := quotient_polynomial_degree_drop hf R M Q hQ hlen f hK p q hp hq'
      (leadingCoeff_pos_of_eventuallyPolynomial _ _ hq' hq0 hqpos)
    have hpos := polynomial_degree_pos_of_dimension_ne_zero hf hs R M Q hQ hlen hd0 p hp
    omega


/-- The image of an induced quotient map has length at most that of its source. -/
theorem length_upper_estimate_of_le_ker (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (f : M →ₗ[R] M)
    (A B : Submodule R M) (h : B ≤ LinearMap.ker (A.mkQ.comp f)) :
    Module.length R (M ⧸ A) ≤ Module.length R (M ⧸ B) +
      Module.length R (M ⧸ (A ⊔ LinearMap.range f)) := by
  let g : M →ₗ[R] M ⧸ A := A.mkQ.comp f
  have hbound : Module.length R (LinearMap.range g) ≤ Module.length R (M ⧸ B) := by
    rw [← g.quotKerEquivRange.length_eq]
    exact length_quotient_antitone R M _ _ h
  have hrange : LinearMap.range g = (LinearMap.range f).map A.mkQ :=
    LinearMap.range_comp f A.mkQ
  rw [length_quotient_eq_image_add R M A (LinearMap.range f), ← hrange]
  exact add_le_add hbound le_rfl

/-- Multiplication by a scalar in Q bounds the increase in cumulative length
by the cumulative length after quotienting by that scalar. -/
theorem scalar_quotientLength_recurrence
    (hf : Specs.P103.HilbertSamuelPolynomial.finiteLengthsType.{u,v})
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R) (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (hlen : IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))))
    (x : R) (hx : x ∈ Q) (n : ℕ) :
    quotientLength Q M (n + 1) ≤ quotientLength Q M n +
      quotientLength Q (M ⧸ LinearMap.range (LinearMap.lsmul R M x)) (n + 1) := by
  let f : M →ₗ[R] M := LinearMap.lsmul R M x
  let A := powerSubmodule Q M (n + 1 + 1)
  let B := powerSubmodule Q M (n + 1)
  have hBA : B ≤ LinearMap.ker (A.mkQ.comp f) := by
    intro m hm
    apply (Submodule.Quotient.mk_eq_zero A).mpr
    change x • m ∈ Q ^ (n + 1 + 1) • (⊤ : Submodule R M)
    rw [pow_succ', Submodule.mul_smul]
    exact Submodule.smul_mem_smul hx hm
  have hle := length_upper_estimate_of_le_ker R M f A B hBA
  have hMn := Module.length_ne_top_iff.mpr (hf R M Q hQ hlen n).2
  have hNn : Module.length R (M ⧸ (A ⊔ LinearMap.range f)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (length_quotient_antitone R M A _ le_sup_left)
      (Module.length_ne_top_iff.mpr (hf R M Q hQ hlen (n + 1)).2).lt_top)
  have hnat := ENat.toNat_le_toNat hle (by
    simpa only [ne_eq, ENat.add_eq_top, not_or] using And.intro hMn hNn)
  rw [ENat.toNat_add hMn hNn] at hnat
  simpa only [quotientLength, length_quotient_of_quotient] using hnat


/-- A cumulative recurrence gives a polynomial degree bound by taking a
backward difference with positive leading coefficient. -/
theorem polynomial_degree_le_succ_of_recurrence
    (f g : ℕ → ℕ) (p q : Polynomial ℚ)
    (hf : EventuallyPolynomial f p) (hg : EventuallyPolynomial g q)
    (hp : 0 < p.natDegree → 0 < p.leadingCoeff)
    (hrec : ∀ n : ℕ, f (n + 1) ≤ f n + g (n + 1)) :
    p.natDegree ≤ q.natDegree + 1 := by
  by_cases hp0 : p.natDegree = 0
  · omega
  have hpdeg : 0 < p.natDegree := by omega
  obtain ⟨hbd0, hbd⟩ := backwardDifference_degree p hpdeg
  have hcoeff : 0 < (backwardDifference p).leadingCoeff := by
    rw [← coeff_natDegree, hbd, backwardDifference_coeff p hpdeg]
    exact mul_pos (by exact_mod_cast hpdeg) (hp hpdeg)
  have hbound : (backwardDifference p).natDegree ≤ q.natDegree := by
    apply natDegree_le_of_eventually_eval_le _ _ hcoeff
    obtain ⟨Np, hNp⟩ := hf
    obtain ⟨Nq, hNq⟩ := hg
    refine ⟨Np + Nq + 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := by omega
    have hcast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) + (-1) := by
      rw [Nat.cast_sub hn1]
      push_cast
      ring
    have hr := hrec (n - 1)
    rw [Nat.sub_add_cancel hn1] at hr
    have hr' : (f n : ℚ) ≤ (f (n - 1) : ℚ) + (g n : ℚ) := by exact_mod_cast hr
    rw [hNp n (by omega), hNp (n - 1) (by omega), hNq n (by omega)] at hr'
    simpa only [backwardDifference, eval_sub, taylor_eval, hcast] using
      (sub_le_iff_le_add'.mpr hr')
  omega

/-- The upper bound follows by induction using a scalar in the original
finite-colength ideal. No faithfulness or residue-field assumption is needed. -/
theorem polynomial_degree_le_dimension
    (hf : Specs.P103.HilbertSamuelPolynomial.finiteLengthsType.{u,v})
    (hq : Specs.P103.HilbertSamuelPolynomial.quotientPolynomialType.{u,v}) :
    ∀ (d : ℕ) (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
      (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
      (Q : Ideal R), Q ≤ IsLocalRing.maximalIdeal R →
      IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))) →
      moduleDimensionValue R M = (d : WithBot ℕ∞) →
      ∀ p : Polynomial ℚ, EventuallyPolynomial (quotientLength Q M) p →
        (0 < p.natDegree → 0 < p.leadingCoeff) → p.natDegree ≤ d := by
  intro d
  induction d with
  | zero =>
    intro R _ _ _ M _ _ _ _ Q hQ hlen hd p hp hpos
    have hM := (P103.Ch06.SystemsParameters.dimension_zero_iff R M).mp (by simpa using hd)
    obtain ⟨N, hN⟩ := powerSubmodule_eventually_zero R M Q hQ hM
    have hconst : EventuallyPolynomial (quotientLength Q M)
        (C ((Module.length R M).toNat : ℚ)) := by
      refine ⟨N, fun n hn => ?_⟩
      rw [(lengths_of_powerSubmodule_zero R M Q n (hN n hn)
        (hN (n + 1) (by omega))).2, eval_C]
    have heq := eventuallyPolynomial_unique _ _ _ hp hconst
    rw [heq, natDegree_C]
  | succ d ih =>
    intro R _ _ _ M _ _ _ _ Q hQ hlen hd p hp hpos
    have hd0 : moduleDimensionValue R M ≠ 0 := by
      rw [hd]
      exact_mod_cast Nat.succ_ne_zero d
    obtain ⟨x, hxQ, _hK, hN, hdim⟩ := exists_scalar_dimension_drop R M Q hQ hlen hd0
    let f : M →ₗ[R] M := LinearMap.lsmul R M x
    let N := M ⧸ LinearMap.range f
    have : Nontrivial N := hN
    obtain ⟨e, he, _⟩ := P103.Ch06.SystemsParameters.parameter_count R N
    have heq : e = d := by
      change moduleDimensionValue R N + 1 = moduleDimensionValue R M at hdim
      rw [he, hd] at hdim
      have hh : e + 1 = d + 1 := by exact_mod_cast hdim
      omega
    subst e
    have hlenN := finite_colength_module_quotient R M Q (LinearMap.range f) hlen
    obtain ⟨q, hq', hq0, hqpos⟩ := hq R N Q hQ hlenN
    have hind : q.natDegree ≤ d := ih R N Q hQ hlenN he q hq' hqpos
    have hbound := polynomial_degree_le_succ_of_recurrence _ _ p q hp hq' hpos
      (scalar_quotientLength_recurrence hf R M Q hQ hlen x hxQ)
    omega


/-- The exact cumulative degree follows from the two proved dimension bounds. -/
theorem quotient_degree : quotientDegreeType.{u,v} := by
  intro R _ _ _ M _ _ _ _ Q hQ hlen d hd
  obtain ⟨p, hp, hp0, hpos⟩ := quotient_polynomial R M Q hQ hlen
  exact ⟨p, hp, hp0, le_antisymm
    (polynomial_degree_le_dimension finite_lengths quotient_polynomial
      d R M Q hQ hlen hd p hp hpos)
    (dimension_le_polynomial_degree finite_lengths sum_layers quotient_polynomial
      d R M Q hQ hlen hd p hp)⟩

/-- First differences give the exact layer degree in positive dimension. -/
theorem positive_layers : positiveLayersType.{u,v} :=
  positive_layers_of_quotient_degree sum_layers quotient_degree

end P103.HilbertSamuelDimension
