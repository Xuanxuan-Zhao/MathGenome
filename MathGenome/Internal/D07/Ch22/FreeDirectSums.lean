import MathGenome.Internal.Specs.D07.Ch22.FreeDirectSums

/-!
# Free modules and arbitrary direct sums

K07.22.free_direct_sums, paper.tex:6706–6725. We use the actual finite-support
models `Finsupp` and `DirectSum` (dependent `DFinsupp`). No nontriviality,
finite index set, basis of a summand, or finite generation is required.
The extension constructions are linear maps; their formulas and uniqueness
are proved separately, with the coefficients recovered by coordinates.
-/

universe u v w t

namespace D07.Ch22.FreeDirectSums

open Specs.D07.Ch22.FreeDirectSums
open scoped BigOperators

/-- Precisely the finite-support functions, with no condition on the index set. -/
theorem freeFunctions : FreeFunctions.{u, v} := by
  intro R _ E f
  constructor
  · rintro ⟨a, ha⟩
    simpa only [ha] using (show Set.Finite {i | a i ≠ 0} from a.hasFiniteSupport)
  · intro hf
    exact ⟨Finsupp.ofSupportFinite f hf, fun _ => rfl⟩

theorem freePointwise : FreePointwise.{u, v} := by
  intro R _ E a b r i
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem deltaCoordinates : DeltaCoordinates.{u, v} := by
  classical
  intro R _ E e i
  exact Finsupp.single_apply

/-- Scalar multiplication of a delta function puts the scalar in its coordinate. -/
theorem freeExpansion : FreeExpansion.{u, v} := by
  intro R _ E a
  simpa only [Finsupp.smul_single_one, Finsupp.sum] using a.sum_single

theorem freeCoefficientsUnique : FreeCoefficientsUnique.{u, v} := by
  intro R _ E a
  refine ⟨a, freeExpansion R E a, ?_⟩
  intro c hc
  rwa [freeExpansion R E c] at hc

/-- `linearCombination` is the finite-sum extension, already bundled as a linear map. -/
theorem freeUniversalProperty : FreeUniversalProperty.{u, v, w} := by
  intro R _ E N _ _ h
  refine ⟨Finsupp.linearCombination R h, ?_, ?_⟩
  · intro e
    simp
  · intro F hF
    apply Finsupp.lhom_ext
    intro e r
    rw [← Finsupp.smul_single_one e r, F.map_smul, hF]
    simp

/-- The formula holds for every extension, so is independent of its construction. -/
theorem freeMapFormula : FreeMapFormula.{u, v, w} := by
  intro R _ E N _ _ h F hF a
  calc
    F a = F (∑ e ∈ a.support, a e • Finsupp.single e (1 : R)) :=
      congrArg F (freeExpansion R E a).symm
    _ = ∑ e ∈ a.support, a e • h e := by simp only [map_sum, map_smul, hF]

theorem directSumFunctions : DirectSumFunctions.{u, v, w} := by
  classical
  intro R _ E M _ _ f
  constructor
  · rintro ⟨a, ha⟩
    simpa only [ha] using DFinsupp.finite_support a
  · intro hf
    refine ⟨DFinsupp.mk hf.toFinset (fun i => f i), ?_⟩
    intro i
    by_cases hi : i ∈ hf.toFinset
    · exact DFinsupp.mk_of_mem hi
    · rw [DFinsupp.mk_of_notMem hi]
      exact (not_not.mp (fun hn => hi (hf.mem_toFinset.mpr hn))).symm

theorem directSumPointwise : DirectSumPointwise.{u, v, w} := by
  intro R _ E M _ _ a b r i
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem coordinateInclusions : CoordinateInclusions.{u, v, w} := by
  classical
  intro R _ E M _ _ i x
  refine ⟨DirectSum.lof_apply R i x, ?_⟩
  intro j hj
  exact DFinsupp.single_eq_of_ne hj

theorem directSumExpansion : DirectSumExpansion.{u, v, w} := by
  classical
  intro R _ E M _ _ a
  exact DirectSum.sum_support_of a

/-- The family of maps extends by the direct sum's canonical finite-sum map. -/
theorem directSumUniversalProperty : DirectSumUniversalProperty.{u, v, w, t} := by
  classical
  intro R _ E M _ _ N _ _ h
  refine ⟨DirectSum.toModule R E N h, ?_, ?_⟩
  · intro i x
    exact DirectSum.toModule_lof R i x
  · intro F hF
    apply DirectSum.linearMap_ext R
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, hF, DirectSum.toModule_lof]

theorem directSumMapFormula : DirectSumMapFormula.{u, v, w, t} := by
  classical
  intro R _ E M _ _ N _ _ h F hF a
  calc
    F a = F (∑ i ∈ a.support, DirectSum.lof R E M i (a i)) :=
      congrArg F (directSumExpansion R E M a).symm
    _ = ∑ i ∈ a.support, h i (a i) := by simp only [map_sum, hF]

theorem emptyFree : EmptyFree.{u, v} := by
  intro R _ E _ a
  ext e
  exact isEmptyElim e

theorem emptyDirectSum : EmptyDirectSum.{u, v, w} := by
  intro R _ E _ M _ _ a
  apply DirectSum.ext
  intro e
  exact isEmptyElim e

/-- Infinite products have tuples that cannot be finite-support sums.
The core construction above still covers zero rings; this particular
counterexample necessarily uses `1 ≠ 0`. -/
theorem infiniteProduct : InfiniteProduct.{u, v} := by
  intro R _ _ E _ h
  obtain ⟨a, ha⟩ := h
  have hone (i : E) : a i = 1 := congrFun ha i
  have hfin : Set.Finite (Set.univ : Set E) := by
    simpa only [hone, ne_eq, one_ne_zero, not_false_eq_true, Set.ofPred_true] using DFinsupp.finite_support a
  exact Set.infinite_univ hfin

/-- The quotient by finite-support tuples detects the failure of uniqueness
for the product. This avoids any assertion that every product tuple can be
summed, and applies over every nonzero commutative ring. -/
theorem productNotCoproduct : ProductNotCoproduct.{u, v} := by
  classical
  intro R _ _ E _
  let P : Submodule R (E → R) := LinearMap.range
    (DirectSum.coeFnLinearMap R : DirectSum E (fun _ => R) →ₗ[R] (E → R))
  refine ⟨P.mkQ, 0, ?_, ?_⟩
  · intro heq
    have hz : P.mkQ (fun _ : E => (1 : R)) = 0 :=
      LinearMap.congr_fun heq (fun _ => 1)
    have hm : (fun _ : E => (1 : R)) ∈ P := Submodule.Quotient.mk_eq_zero P |>.mp hz
    exact infiniteProduct R E hm
  · intro i x
    change (Submodule.Quotient.mk (Pi.single i x) : (E → R) ⧸ P) = 0
    apply (Submodule.Quotient.mk_eq_zero P).mpr
    refine ⟨DirectSum.lof R E (fun _ => R) i x, ?_⟩
    rfl

end D07.Ch22.FreeDirectSums
