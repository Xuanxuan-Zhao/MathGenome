import Mathlib.Analysis.Complex.Exponential
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Multiset.Filter
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
Independent specification of the subset-sum construction in paper.tex:7784–7819.
Subsets index the sums, so different subsets giving the same number retain
separate occurrences. Conjugates are the distinct complex roots of the minimal
polynomial over Q. The output list explicitly begins with the given element.
Rationality concerns the coefficients of the product, not its individual roots.
-/

namespace Specs.D07.Appendix.PiTranscendentalSubsetSumRelation

open Polynomial
open scoped BigOperators

noncomputable def distinctRoots (p : ℚ[X]) (L : Type*) [Field L] [Algebra ℚ L] : Finset L :=
  by classical exact (p.aroots L).toFinset

noncomputable def conjugates (α : ℂ) : Finset ℂ :=
  distinctRoots (minpoly ℚ α) ℂ

noncomputable def subsetSums {R : Type*} [AddCommMonoid R] (s : Finset R) : Multiset R :=
  s.powerset.val.map (fun t => ∑ x ∈ t, x)

noncomputable def nonzeroSums {R : Type*} [AddCommMonoid R] (s : Finset R) : Multiset R :=
  by classical exact (subsetSums s).filter (· ≠ 0)

noncomputable def zeroCount {R : Type*} [AddCommMonoid R] (s : Finset R) : ℕ :=
  by classical exact (subsetSums s).count 0

noncomputable def rootProduct {R : Type*} [CommRing R] (b : Multiset R) : R[X] :=
  (b.map (fun z => X - C z)).prod

/-- Automorphisms permute the entire multiset, and also its nonzero part. -/
def GaloisSubsetSums : Prop :=
  ∀ (L : Type) [Field L] [Algebra ℚ L] (p : ℚ[X]) (σ : L ≃ₐ[ℚ] L),
    let s := distinctRoots p L
    (subsetSums s).map σ = subsetSums s ∧
    (nonzeroSums s).map σ = nonzeroSums s ∧
    (rootProduct (nonzeroSums s)).map σ.toRingHom = rootProduct (nonzeroSums s)

/-- A complete construction from exactly the source hypotheses. The equation
for `subsetSums` records all multiplicities in the zero/nonzero separation. -/
def SubsetSumRelation : Prop :=
  ∀ α : ℂ, α ≠ 0 → IsAlgebraic ℚ α → Complex.exp α = -1 →
    ∃ tail : List ℂ,
      (α :: tail).Nodup ∧ (α :: tail).toFinset = conjugates α ∧
      0 < zeroCount (conjugates α) ∧
      0 < (nonzeroSums (conjugates α)).card ∧
      (∀ β ∈ nonzeroSums (conjugates α), β ≠ 0) ∧
      subsetSums (conjugates α) =
        Multiset.replicate (zeroCount (conjugates α)) 0 + nonzeroSums (conjugates α) ∧
      (zeroCount (conjugates α) : ℂ) +
        ((nonzeroSums (conjugates α)).map Complex.exp).sum = 0 ∧
      ∃ P : ℚ[X], P.map (algebraMap ℚ ℂ) = rootProduct (nonzeroSums (conjugates α))

end Specs.D07.Appendix.PiTranscendentalSubsetSumRelation
