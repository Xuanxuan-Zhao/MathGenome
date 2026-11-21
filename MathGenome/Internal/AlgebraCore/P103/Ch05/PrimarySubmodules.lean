import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.PrimarySubmodules
import MathGenome.Internal.AlgebraCore.P103.Ch05.AssociatedPrimesInterface

namespace P103.Ch05.PrimarySubmodules
universe u v
open P103.Specs.Ch05.PrimarySubmodules
open P103.Specs.Ch05.AssociatedPrimesInterface

def IsPrimary : PrimaryType.{u,v} := primaryValue

def radical : RadicalType.{u,v} := radicalValue

def zeroDivisors : ZeroDivisorsType.{u,v} := zeroDivisorsValue

theorem quotient_nontrivial : quotient_nontrivialType.{u,v} := by
  intro R _ M _ _ N hN
  exact Submodule.Quotient.nontrivial_iff.mpr hN.1

theorem primary_iff_quotient : primary_iff_quotientType.{u,v} := by
  intro R _ M _ _ N
  constructor
  · intro hN
    refine ⟨hN.1, ?_⟩
    intro r x hx hne
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N x
    have hrm : r • m ∈ N := by
      exact (Submodule.Quotient.mk_eq_zero N).mp hx
    have hm : m ∉ N := fun h => hne ((Submodule.Quotient.mk_eq_zero N).mpr h)
    obtain ⟨n, hn, hall⟩ := hN.2 r m hrm hm
    refine ⟨n, hn, ?_⟩
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective N y
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hall z)
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro r m hrm hm
    obtain ⟨n, hn, hall⟩ := h r (Submodule.Quotient.mk m)
      ((Submodule.Quotient.mk_eq_zero N).mpr hrm)
      (fun he => hm ((Submodule.Quotient.mk_eq_zero N).mp he))
    exact ⟨n, hn, fun y => (Submodule.Quotient.mk_eq_zero N).mp (hall (Submodule.Quotient.mk y))⟩

theorem mem_radical_iff_nilpotent : mem_radical_iff_nilpotentType.{u,v} := by
  intro R _ M _ _ N r
  change (∃ n : ℕ, r ^ n ∈ Module.annihilator R (M ⧸ N)) ↔ _
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, Nat.le_add_left 1 n, fun y => ?_⟩
    rw [pow_succ', mul_smul, Module.mem_annihilator.mp hn y, smul_zero]
  · rintro ⟨n, _, hn⟩
    exact ⟨n, Module.mem_annihilator.mpr hn⟩

/-- A scalar that kills no nonzero vector acts injectively. -/
lemma smul_injective_of_no_zeroDivisor {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (r : R)
    (h : ∀ x : M, r • x = 0 → x = 0) :
    Function.Injective (fun x : M => r • x) := by
  intro x y he
  apply sub_eq_zero.mp
  apply h
  change r • x = r • y at he
  rw [smul_sub, he, sub_self]

/-- A nilpotent scalar on a nonzero module must kill a nonzero vector. -/
lemma zeroDivisor_of_annihilating_power {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Nontrivial M] (r : R)
    (n : ℕ) (hn : ∀ x : M, r ^ n • x = 0) :
    ∃ x : M, x ≠ 0 ∧ r • x = 0 := by
  classical
  by_contra h
  have hk : ∀ x : M, r • x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    exact h ⟨x, hne, hx⟩
  have hp : ∀ k : ℕ, ∀ x : M, r ^ k • x = 0 → x = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro x hx
      apply ih x
      apply hk
      simpa only [pow_succ', mul_smul] using hx
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  exact hx (hp n x (hn x))

theorem radical_eq_zeroDivisors : radical_eq_zeroDivisorsType.{u,v} := by
  intro R _ M _ _ N hN
  haveI := quotient_nontrivial R M N hN
  ext r
  constructor
  · intro hr
    obtain ⟨n, _, hn⟩ := (mem_radical_iff_nilpotent R M N r).mp hr
    exact zeroDivisor_of_annihilating_power r n hn
  · rintro ⟨x, hx, hrx⟩
    exact (mem_radical_iff_nilpotent R M N r).mpr
      (((primary_iff_quotient R M N).mp hN).2 r x hrx hx)

theorem injective_of_not_mem_radical : injective_of_not_mem_radicalType.{u,v} := by
  intro R _ M _ _ N hN r hr
  apply smul_injective_of_no_zeroDivisor r
  intro x hx
  by_contra hne
  apply hr
  rw [← SetLike.mem_coe, radical_eq_zeroDivisors R M N hN]
  exact ⟨x, hne, hx⟩

theorem radical_isPrime : radical_isPrimeType.{u,v} := by
  intro R _ M _ _ N hN
  haveI := quotient_nontrivial R M N hN
  have hproper : radicalValue R M N ≠ ⊤ := by
    intro he
    have h1 : (1 : R) ∈ radicalValue R M N := he.symm ▸ Submodule.mem_top
    obtain ⟨n, _, hn⟩ := (mem_radical_iff_nilpotent R M N 1).mp h1
    obtain ⟨x, hx⟩ := exists_ne (0 : M ⧸ N)
    exact hx (by simpa using hn x)
  refine ⟨hproper, ?_⟩
  intro a b hab
  by_cases hb : b ∈ radicalValue R M N
  · exact Or.inr hb
  · left
    obtain ⟨n, _, hn⟩ := (mem_radical_iff_nilpotent R M N (a * b)).mp hab
    by_cases hbn : ∀ x : M ⧸ N, b ^ n • x = 0
    · exact (hb ⟨n, Module.mem_annihilator.mpr hbn⟩).elim
    · push Not at hbn
      obtain ⟨x, hx⟩ := hbn
      have ha : a ^ n ∈ radicalValue R M N := by
        rw [← SetLike.mem_coe, radical_eq_zeroDivisors R M N hN]
        refine ⟨b ^ n • x, hx, ?_⟩
        simpa only [mul_pow, mul_smul] using hn x
      exact Ideal.mem_radical_of_pow_mem ha

theorem associatedPrimes_singleton : associatedPrimes_singletonType.{u,v} := by
  intro R _ _ M _ _ N hN
  haveI := quotient_nontrivial R M N hN
  have unique : ∀ p ∈ associatedPrimesValue R (M ⧸ N), p = radicalValue R M N := by
    rintro p ⟨hp, x, hpx⟩
    have hx : x ≠ 0 :=
      AssociatedPrimesInterface.annihilator_witness_ne_zero R (M ⧸ N) p x hp hpx
    apply le_antisymm
    · intro r hr
      rw [← SetLike.mem_coe, radical_eq_zeroDivisors R M N hN]
      exact ⟨x, hx, (AssociatedPrimesInterface.mem_elementAnnihilator R (M ⧸ N) x r).mp
        (hpx ▸ hr)⟩
    · apply hp.radical_le_iff.mpr
      intro r hr
      rw [hpx]
      exact (AssociatedPrimesInterface.mem_elementAnnihilator R (M ⧸ N) x r).mpr
        (Module.mem_annihilator.mp hr x)
  obtain ⟨p, hp⟩ := AssociatedPrimesInterface.associatedPrimes_nonempty R (M ⧸ N)
  apply Set.ext
  intro q
  constructor
  · intro hq
    exact Set.mem_singleton_iff.mpr (unique q hq)
  · intro hq
    have hqeq : q = radicalValue R M N := Set.mem_singleton_iff.mp hq
    rw [hqeq, ← unique p hp]
    exact hp

end P103.Ch05.PrimarySubmodules
