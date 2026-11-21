import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.DimensionBounds
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.UnmixednessCriterion
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-! Converse unmixedness criterion (CM-09).
We work at an arbitrary prime p. A longest global regular sequence in p
exists by DP-02. Prime avoidance gives an associated prime q of its quotient
with p ≤ q. The hypothesis implies ht(q) = length, and the localized regular
sequence forces the reverse inequality at p.
-/

universe u
open scoped Pointwise
open RingTheory.Sequence
namespace AdvCommAlg.CohenMacaulay

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- A weakly regular sequence contained in a proper ideal is proper on the ring. -/
lemma ringRegular_of_weaklyRegular_of_le {xs : List R}
    (hx : IsWeaklyRegular R xs) {I : Ideal R} (hI : I ≠ ⊤)
    (hxs : Ideal.ofList xs ≤ I) : IsRegular R xs := by
  refine ⟨hx, ?_⟩
  change (⊤ : Ideal R) ≠ Ideal.ofList xs • ⊤
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact (ne_top_of_le_ne_top hI hxs).symm

/-- A regular sequence in a Noetherian ring has height equal to its length. -/
lemma height_ofList_eq_length_of_regular {xs : List R} (hx : IsRegular R xs) :
    (Ideal.ofList xs).height = (xs.length : ℕ∞) := by
  classical
  have hproper : Ideal.ofList xs ≠ ⊤ := by
    intro h
    apply hx.top_ne_smul
    simp [h]
  apply le_antisymm
  · have heq : Ideal.ofList xs = Ideal.span (xs.toFinset : Set R) := by
      simp [Ideal.ofList]
    rw [heq]
    exact (Ideal.height_span_le_card_of_span_ne_top (heq ▸ hproper)).trans
      (by exact_mod_cast List.toFinset_card_le xs)
  · rw [Ideal.height_eq_inf_minimalPrimes]
    apply le_iInf₂
    intro p hp
    have := hp.isPrime
    let S := Localization.AtPrime p
    have hreg : IsRegular S (xs.map (algebraMap R S)) :=
      hx.toIsWeaklyRegular.isRegular_of_isLocalization_of_mem S p
        (fun a ha => hp.le (Ideal.subset_span ha))
    have hbound := (Depth.regular_length_le_supportDim S _ hreg).trans
      (Module.supportDim_le_ringKrullDim S S)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S] at hbound
    simp only [List.length_map] at hbound
    exact_mod_cast hbound

/-- Choose a regular sequence of greatest length inside a prime. -/
lemma exists_longest_regular_in_prime (p : Ideal R) [p.IsPrime] :
    ∃ xs : List R, IsRegular R xs ∧ (∀ a ∈ xs, a ∈ p) ∧
      ∀ ys : List R, IsRegular R ys → (∀ a ∈ ys, a ∈ p) → ys.length ≤ xs.length := by
  classical
  have hproper : p • (⊤ : Submodule R R) ≠ ⊤ := by
    change p • (⊤ : Ideal R) ≠ ⊤
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using (Ideal.IsPrime.ne_top' (I := p))
  obtain ⟨n, hn⟩ := Depth.regular_lengths_bounded R p hproper
  let L : Set ℕ := {n | ∃ xs : List R,
    IsRegular R xs ∧ (∀ a ∈ xs, a ∈ p) ∧ xs.length = n}
  have hfin : L.Finite := (Set.finite_Iic n).subset (by
    rintro k ⟨xs, hx, hxp, rfl⟩
    exact hn xs hx hxp)
  have hnonempty : L.Nonempty := by
    exact ⟨0, [], ringRegular_of_weaklyRegular_of_le (.nil R R)
      (Ideal.IsPrime.ne_top' (I := p)) (by simp), by simp, rfl⟩
  obtain ⟨e, he, hmax⟩ := hfin.exists_maximal hnonempty
  obtain ⟨xs, hx, hxp, rfl⟩ := he
  refine ⟨xs, hx, hxp, ?_⟩
  intro ys hy hyp
  by_contra h
  have hlt : xs.length < ys.length := Nat.lt_of_not_ge h
  exact hlt.not_ge (hmax ⟨ys, hy, hyp, rfl⟩ hlt.le)

/-- Failure to extend a longest sequence is detected by an associated prime. -/
lemma exists_associatedPrime_over_of_longest (p : Ideal R) [p.IsPrime]
    (xs : List R) (hx : IsRegular R xs) (hxp : ∀ a ∈ xs, a ∈ p)
    (hmax : ∀ ys : List R, IsRegular R ys →
      (∀ a ∈ ys, a ∈ p) → ys.length ≤ xs.length) :
    ∃ q ∈ associatedPrimes R (R ⧸ Ideal.ofList xs), p ≤ q := by
  have hsubset : (p : Set R) ⊆
      ⋃ q ∈ associatedPrimes R (R ⧸ Ideal.ofList xs), (q : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    intro a ha hreg
    have hquot : IsSMulRegular
        (R ⧸ (Ideal.ofList xs • ⊤ : Submodule R R)) a := by
      change IsSMulRegular (R ⧸ (Ideal.ofList xs • (⊤ : Ideal R))) a
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
      exact hreg
    have hweak : IsWeaklyRegular R (xs ++ [a]) :=
      (isWeaklyRegular_append_iff R xs [a]).mpr
        ⟨hx.toIsWeaklyRegular, (isWeaklyRegular_singleton_iff _ a).mpr hquot⟩
    have hmem : ∀ b ∈ xs ++ [a], b ∈ p := by
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hxp b hb
      · obtain rfl := List.mem_singleton.mp hb
        exact ha
    have hproper := ringRegular_of_weaklyRegular_of_le hweak
      (Ideal.IsPrime.ne_top' (I := p)) (Ideal.span_le.mpr hmem)
    have hlen := hmax _ hproper hmem
    simp only [List.length_append, List.length_singleton] at hlen
    exact Nat.not_succ_le_self _ hlen
  exact (p.subset_union_prime_finite (associatedPrimes.finite R (R ⧸ Ideal.ofList xs))
    (f := id) 0 0 (fun _ h _ _ => h.isPrime)).mp hsubset

/-- A Noetherian ring satisfying the source unmixedness condition is Cohen–Macaulay. -/
theorem unmixednessCriterion (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ xs : List R, Ideal.ofList xs ≠ ⊤ →
      (Ideal.ofList xs).height = (xs.length : ℕ∞) →
      ∀ p : Ideal R, p ∈ associatedPrimes R (R ⧸ Ideal.ofList xs) →
        p.height = (xs.length : ℕ∞)) : CohenMacaulayRing R := by
  intro p
  obtain ⟨xs, hx, hxp, hmax⟩ := exists_longest_regular_in_prime p.asIdeal
  obtain ⟨q, hq, hpq⟩ := exists_associatedPrime_over_of_longest p.asIdeal xs hx hxp hmax
  have hproper : Ideal.ofList xs ≠ ⊤ :=
    ne_top_of_le_ne_top p.isPrime.ne_top (Ideal.span_le.mpr hxp)
  have hheight := h xs hproper (height_ofList_eq_length_of_regular hx) q hq
  have hle : p.asIdeal.height ≤ (xs.length : ℕ∞) :=
    (Ideal.height_mono hpq).trans_eq hheight
  let S := Localization.AtPrime p.asIdeal
  have hreg : IsRegular S (xs.map (algebraMap R S)) :=
    hx.toIsWeaklyRegular.isRegular_of_isLocalization_of_mem S p.asIdeal hxp
  have hmem : ∀ a ∈ xs.map (algebraMap R S), a ∈ IsLocalRing.maximalIdeal S := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p.asIdeal b).mpr (hxp b hb)
  have hdepth : (xs.length : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of S S) := by
    rw [IsLocalRing.depth_eq_sSup_length_isRegular]
    apply le_sSup
    exact ⟨xs.map (algebraMap R S), hreg, hmem, by simp⟩
  apply (cohenMacaulayAt_iff_depth_eq R p).mpr
  apply le_antisymm
  · rw [← Depth.depth_eq_libraryDepth (ModuleCat.of S S)]
    exact (Depth.depth_le_supportDim S).trans (Module.supportDim_le_ringKrullDim S S)
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal S]
    exact WithBot.coe_le_coe.mpr (hle.trans hdepth)

end AdvCommAlg.CohenMacaulay
