import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.FiniteFieldArtinSchreier
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.ArtinSchreierConnecting
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.FiniteFrobenius
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace GaloisFormalization.GH.FiniteFieldArtinSchreier

open ArtinSchreierCoefficients
open Specs.GaloisFormalization.GH.FiniteFieldArtinSchreier

universe u v

noncomputable section

attribute [local instance] ZMod.algebra

theorem traceFormula : TraceFormula.{u} := by
  intro p k _ _ _ _
  dsimp only
  constructor
  · rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  · intro a
    rw [FiniteField.algebraMap_trace_eq_sum_pow, Nat.card_zmod]

private theorem sum_wp_pow (p : ℕ) {F : Type*} [Field F] [Fact p.Prime] [CharP F p]
    (x : F) (r : ℕ) :
    ∑ i ∈ Finset.range r, (wp p F x) ^ (p ^ i) = x ^ (p ^ r) - x := by
  simp only [wp_apply]
  calc
    _ = ∑ i ∈ Finset.range r, (x ^ (p ^ (i + 1)) - x ^ (p ^ i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [sub_pow_char_pow, pow_succ', pow_mul]
    _ = _ := by
      simpa only [pow_zero, pow_one] using Finset.sum_range_sub (fun i => x ^ (p ^ i)) r

theorem traceQuotient : TraceQuotient.{u} := by
  intro p k _ _ _ _
  let := Fintype.ofFinite k
  let tr := Algebra.trace (ZMod p) k
  obtain ⟨hcard, htrace⟩ := traceFormula p k
  have hsurj : Function.Surjective tr := Algebra.trace_surjective (ZMod p) k
  have hle : LinearMap.range (wp p k) ≤ LinearMap.ker tr := by
    rintro a ⟨x, rfl⟩
    change tr (wp p k x) = 0
    apply (algebraMap (ZMod p) k).injective
    change algebraMap (ZMod p) k (Algebra.trace (ZMod p) k (wp p k x)) = _
    rw [map_zero, htrace, sum_wp_pow, ← hcard, FiniteField.pow_card, sub_self]
  have hwp := (wp p k).finrank_range_add_finrank_ker
  rw [(exact_wp p k).linearMap_ker_eq,
    LinearMap.finrank_range_of_inj (primeFieldInclusion_injective p k), Module.finrank_self] at hwp
  have htr := tr.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at htr
  have hexact : Function.Exact (wp p k) tr :=
    LinearMap.exact_iff.mpr (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  refine ⟨hexact.linearEquivOfSurjective hsurj, ?_⟩
  intro a
  rfl

theorem characterAtFrobenius : CharacterAtFrobenius.{u,v} := by
  intro p k S _ _ _ _ _ _ _ _ _
  dsimp only
  let : CharP S p := charP_of_injective_algebraMap' k p
  obtain ⟨connect, toCharacter, hclass, hroot⟩ :=
    ArtinSchreierConnecting.artinSchreierConnecting p k S
  refine ⟨connect, toCharacter, hclass, hroot, ?_⟩
  intro a
  obtain ⟨_, _, hsurj⟩ := shortExact p k S
  obtain ⟨α, hα⟩ := hsurj (algebraMap k S a)
  obtain ⟨hcard, htrace⟩ := traceFormula p k
  apply primeFieldInclusion_injective p S
  refine (hroot a α hα (FiniteFrobenius.arithmeticFrobenius k S)).trans ?_
  change FiniteFrobenius.arithmeticFrobenius k S α - α =
    primeFieldInclusion p S (Algebra.trace (ZMod p) k a)
  rw [FiniteFrobenius.arithmeticFrobenius_apply, hcard, ← sum_wp_pow,
    hα, ← primeFieldInclusion_natural p (algebraMap k S),
    primeFieldInclusion_apply, htrace, map_sum]
  simp only [map_pow]

end

end GaloisFormalization.GH.FiniteFieldArtinSchreier
