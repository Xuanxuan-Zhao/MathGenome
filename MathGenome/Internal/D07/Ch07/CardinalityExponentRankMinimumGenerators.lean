import MathGenome.Internal.Specs.D07.Ch07.CardinalityExponentRankMinimumGenerators
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Convert

namespace D07.Ch07.CardinalityExponentRankMinimumGenerators

open Specs.D07.Ch07.CardinalityExponentRankMinimumGenerators

/-- The coordinate elements generate, even without the normalization conditions. -/
theorem coordinate_generators_span {r : ℕ} (d : Fin r → ℕ) :
    AddSubgroup.closure (Set.range (coordinateGenerator d)) = ⊤ := by
  apply top_unique
  intro x hx
  have hsingle (i : Fin r) :
      Pi.single i (x i) ∈ AddSubgroup.closure (Set.range (coordinateGenerator d)) := by
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective (x i)
    have hm := (AddSubgroup.closure (Set.range (coordinateGenerator d))).zsmul_mem
      (AddSubgroup.subset_closure (Set.mem_range_self i)) z
    convert hm using 1
    rw [← hz]
    ext j
    by_cases h : j = i
    · subst j; simp [coordinateGenerator]
    · simp [coordinateGenerator, h]
  have hsum := (AddSubgroup.closure (Set.range (coordinateGenerator d))).sum_mem
    (fun i (_ : i ∈ Finset.univ) => hsingle i)
  simpa only [Finset.univ_sum_single] using hsum

theorem coordinate_generators :
    CoordinateGenerators := by
  intro r d hd
  refine ⟨coordinate_generators_span d, ?_⟩
  intro i j hij
  by_contra hne
  have : NeZero (d i) := ⟨by have := hd.1 i; omega⟩
  have hi := congrFun hij i
  have hji : i ≠ j := hne
  have h10 : (1 : ZMod (d i)) ≠ 0 := by
    have : Fact (1 < d i) := ⟨hd.1 i⟩
    exact one_ne_zero
  exact h10 (by simpa [coordinateGenerator, Pi.single_apply, hji] using hi)

/-- A residue vanishes modulo `p` precisely when it is a `p`-multiple. -/
theorem residue_zero_iff {n p : ℕ} (h : p ∣ n) (x : ZMod n) :
    ZMod.castHom h (ZMod p) x = 0 ↔ ∃ y : ZMod n, p • y = x := by
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    have hz : (z : ZMod p) = 0 := by simpa using hx
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hz
    refine ⟨(t : ZMod n), ?_⟩
    rw [ht]
    simp [nsmul_eq_mul]
  · rintro ⟨y, rfl⟩
    rw [map_nsmul]
    simp [nsmul_eq_mul]

theorem residue_surjective {r : ℕ} (d : Fin r → ℕ) (p : ℕ)
    (h : ∀ i, p ∣ d i) : Function.Surjective (residueHom d p h) := by
  intro x
  choose y hy using fun i => ZMod.castHom_surjective (h i) (x i)
  exact ⟨y, funext hy⟩

theorem residue_kernel {r : ℕ} (d : Fin r → ℕ) (p : ℕ)
    (h : ∀ i, p ∣ d i) : (residueHom d p h).ker = multiples d p := by
  ext x
  change (residueHom d p h x = 0) ↔ ∃ y : CyclicProduct d, p • y = x
  constructor
  · intro hx
    have hx' (i : Fin r) : ZMod.castHom (h i) (ZMod p) (x i) = 0 := congrFun hx i
    choose y hy using fun i => (residue_zero_iff (h i) (x i)).mp (hx' i)
    exact ⟨y, funext hy⟩
  · rintro ⟨y, rfl⟩
    ext i
    exact (residue_zero_iff (h i) (p • y i)).mpr ⟨y i, rfl⟩

theorem residue_quotient : ResidueQuotient := by
  intro r d p hp h
  have hk := residue_kernel d p h
  refine ⟨residue_surjective d p h, hk, ?_⟩
  let e := (QuotientAddGroup.quotientAddEquivOfEq hk.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (residueHom d p h)
      (residue_surjective d p h))
  exact ⟨e, fun x => rfl⟩

theorem normalized_residue_quotient : NormalizedResidueQuotient := by
  intro r d hd hr p hp hpd
  have h : ∀ i, p ∣ d i := fun i =>
    hpd.trans (hd.2 ⟨0, hr⟩ i (by change (0 : ℕ) ≤ i.val; exact Nat.zero_le _))
  exact ⟨h, (residue_quotient r d p hp h).2.2⟩

/-- Reduction modulo a common prime turns any additive generating family into
    a spanning family in the `r`-dimensional vector space over `ZMod p`. -/
theorem generating_family_lower_bound {r : ℕ} (d : Fin r → ℕ)
    (hd : Normalized d) {ι : Type*} [Fintype ι] (g : ι → CyclicProduct d)
    (hg : AddSubgroup.closure (Set.range g) = ⊤) : r ≤ Fintype.card ι := by
  classical
  by_cases hr : r = 0
  · simp [hr]
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  let i₀ : Fin r := ⟨0, hrpos⟩
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (show d i₀ ≠ 1 by have := hd.1 i₀; omega)
  have h : ∀ i, p ∣ d i := fun i =>
    hpd.trans (hd.2 i₀ i (by change (0 : ℕ) ≤ i.val; exact Nat.zero_le _))
  let : Fact p.Prime := ⟨hp⟩
  let f := residueHom d p h
  have himage : AddSubgroup.closure (Set.range (fun i => f (g i))) = ⊤ := by
    change AddSubgroup.closure (Set.range (f ∘ g)) = ⊤
    rw [Set.range_comp, ← AddMonoidHom.map_closure, hg,
      AddSubgroup.map_top_of_surjective f (residue_surjective d p h)]
  have hc : AddSubgroup.closure (Set.range (fun i => f (g i))) ≤
      (Submodule.span (ZMod p) (Set.range (fun i => f (g i)))).toAddSubgroup :=
    (AddSubgroup.closure_le _).mpr Submodule.subset_span
  rw [himage] at hc
  have hs : Submodule.span (ZMod p) (Set.range (fun i => f (g i))) = ⊤ := by
    apply top_unique
    intro x hx
    exact hc hx
  simpa only [Module.finrank_pi, Fintype.card_fin] using
    (finrank_le_of_span_eq_top hs)

theorem generator_lower_bound : GeneratorLowerBound := by
  intro r d hd k g hg
  simpa only [Fintype.card_fin] using generating_family_lower_bound d hd g hg

theorem minimum_generators : MinimumGenerators := by
  classical
  intro r d hd
  let s := Finset.univ.image (coordinateGenerator d)
  have hs : (s : Set (CyclicProduct d)) = Set.range (coordinateGenerator d) := by
    ext x; simp [s]
  refine ⟨s, ?_, ?_, ?_⟩
  · rw [hs]; exact coordinate_generators_span d
  · exact (Finset.card_image_of_injective _ (coordinate_generators r d hd).2).trans
      (Fintype.card_fin r)
  · intro t ht
    have hrange : Set.range (fun x : t => (x : CyclicProduct d)) =
        (t : Set (CyclicProduct d)) := by
      ext x; simp
    have hgen : AddSubgroup.closure (Set.range (fun x : t => (x : CyclicProduct d))) = ⊤ := by
      rw [hrange]; exact ht
    simpa only [Fintype.card_coe] using
      generating_family_lower_bound d hd (fun x : t => (x : CyclicProduct d)) hgen

theorem empty_product : EmptyProduct := by
  intro d
  apply top_unique
  intro x hx
  have hx0 : x = 0 := funext fun i => Fin.elim0 i
  rw [hx0]
  exact AddSubgroup.zero_mem _

end D07.Ch07.CardinalityExponentRankMinimumGenerators
