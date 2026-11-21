import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.AssociatedPrimeBound
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! The associated-prime depth bound, DP-10. -/

universe u v
open scoped Pointwise
open RingTheory.Sequence
namespace AdvCommAlg.Depth

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- An associated prime can be extended strictly after quotienting by a
regular element in the maximal ideal. Krull intersection supplies an
associated-prime witness divisible by a maximal power of that element. -/
lemma exists_associatedPrime_quotSMulTop_gt
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) (hp : p ∈ associatedPrimes R M)
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) :
    ∃ q ∈ associatedPrimes R (QuotSMulTop x M), p < q := by
  obtain ⟨hprime, m, hpm⟩ := isAssociatedPrime_iff.mp hp
  have hm : m ≠ 0 := by
    intro hm
    apply hprime.ne_top
    apply top_unique
    intro a _
    rw [hpm]
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, hm, smul_zero]
  let I : Ideal R := Ideal.span {x}
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (Ideal.span_le.mpr (by simpa using hx))
  have hcap := I.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) hI
  have hex : ∃ n : ℕ, m ∉ I ^ n • (⊤ : Submodule R M) := by
    by_contra! h
    have hm' : m ∈ ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) :=
      (Submodule.mem_iInf _).mpr h
    rw [hcap] at hm'
    exact hm (by simpa using hm')
  obtain ⟨n, hn⟩ := hex
  have hboundary : ∃ n : ℕ, m ∈ I ^ n • (⊤ : Submodule R M) ∧
      m ∉ I ^ (n + 1) • (⊤ : Submodule R M) := by
    induction n with
    | zero => simp at hn
    | succ n ih =>
      by_cases hn' : m ∈ I ^ n • (⊤ : Submodule R M)
      · exact ⟨n, hn', hn⟩
      · exact ih hn'
  obtain ⟨n, hn, hn'⟩ := hboundary
  rw [show I = Ideal.span {x} from rfl, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul] at hn
  obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists m (x ^ n) ⊤).mp hn
  have hyp : ∀ a ∈ p, a • y = 0 := by
    intro a ha
    apply (hreg.pow n).right_eq_zero_of_smul
    rw [smul_comm, hy]
    simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot] using
      (show a ∈ (⊥ : Submodule R M).colon {m} from hpm ▸ ha)
  have hyx : y ∉ x • (⊤ : Submodule R M) := by
    intro hyx
    obtain ⟨z, _, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists y x ⊤).mp hyx
    apply hn'
    rw [show I = Ideal.span {x} from rfl, Ideal.span_singleton_pow,
      Submodule.ideal_span_singleton_smul]
    apply (Submodule.mem_smul_pointwise_iff_exists m (x ^ (n + 1)) ⊤).mpr
    exact ⟨z, trivial, by rw [pow_succ, mul_smul, hz, hy]⟩
  let ybar : QuotSMulTop x M := Submodule.Quotient.mk y
  have hybar : ybar ≠ 0 := by
    exact fun h => hyx ((Submodule.Quotient.mk_eq_zero _).mp h)
  obtain ⟨q, hq, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R ybar hybar
  have hpq : p ≤ q := by
    intro a ha
    apply hle
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Submodule.Quotient.mk (a • y) = 0
    rw [hyp a ha]
    rfl
  have hxq : x ∈ q := by
    apply hle
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Submodule.Quotient.mk (x • y) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.smul_mem_pointwise_smul y x ⊤ trivial)
  refine ⟨q, hq, lt_of_le_of_ne hpq ?_⟩
  intro he
  have hxm : x • m = 0 := by
    simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot] using
      (show x ∈ (⊥ : Submodule R M).colon {m} from
        hpm ▸ (show x ∈ p from he.symm ▸ hxq))
  exact hm (hreg.right_eq_zero_of_smul hxm)

/-- Each element of a regular sequence gives one strict step above any
associated prime. -/
lemma regular_length_le_coheight_of_associatedPrime
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (xs : List R) (hxs : IsRegular M xs)
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    (xs.length : ℕ∞) ≤ Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R) := by
  induction xs generalizing M p with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hreg, htail⟩ := (isRegular_cons_iff M x xs).mp hxs
    have hx : x ∈ IsLocalRing.maximalIdeal R := by
      by_contra hx
      have hu : IsUnit x := by simpa using hx
      exact RegularSequence.not_regular_unit_cons M x xs hu hxs
    obtain ⟨q, hq, hpq⟩ := exists_associatedPrime_quotSMulTop_gt M p hp x hx hreg
    calc
      ((x :: xs).length : ℕ∞) = (xs.length : ℕ∞) + 1 := by simp
      _ ≤ Order.coheight (⟨q, hq.isPrime⟩ : PrimeSpectrum R) + 1 :=
        add_le_add (ih (QuotSMulTop x M) htail q hq) le_rfl
      _ ≤ Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R) :=
        Order.coheight_add_one_le hpq

/-- The depth is bounded by dim(R/p) for every associated prime p. -/
theorem depth_le_dim_quotient_of_associatedPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    (depth R M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  have hproper : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  have hdim : (Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R) : WithBot ℕ∞) =
      ringKrullDim (R ⧸ p) := by
    rw [Order.coheight_eq_krullDim_Ici, ringKrullDim_quotient]
    rfl
  rw [← hdim]
  apply WithBot.coe_le_coe.mpr
  rw [depth_eq_grade, grade_of_smul_ne_top _ _ hproper]
  apply sSup_le
  rintro _ ⟨xs, hxs, _, rfl⟩
  exact regular_length_le_coheight_of_associatedPrime M xs hxs p hp

end AdvCommAlg.Depth
