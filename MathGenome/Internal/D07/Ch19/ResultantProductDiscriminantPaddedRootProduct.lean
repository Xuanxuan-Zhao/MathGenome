import MathGenome.Internal.Specs.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct
import MathGenome.Internal.D07.Ch19.ResultantDefinition

/-!
The upstream bridge identifies the literal notes determinant with Mathlib's
fixed-bound resultant. The library product-of-evaluations theorem allows
arbitrary padding in g, g = 0, and root multiplicities. Mapping the determinant
to the chosen splitting extension preserves its two bounds. Separate scaling
and normalization results verify the passage from monic to general f.
-/

universe u v
namespace D07.Ch19.ResultantProductDiscriminantPaddedRootProduct
open Polynomial
open Specs.D07.Ch19.ResultantDefinition
open Specs.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct

theorem paddedRootProduct : PaddedRootProduct.{u, v} := by
  intro F L _ _ _ f g n m hf hn hnpos hg hs
  rw [ResultantDefinition.resultantBridge F f g n m hn.le hg,
    ← Polynomial.resultant_map_map]
  have hd : (f.map (algebraMap F L)).natDegree = n := by
    rw [natDegree_map, hn]
  rw [← hd, Polynomial.resultant_eq_prod_eval _ _ m
    (natDegree_map_le.trans hg) hs, leadingCoeff_map_of_injective
    (algebraMap F L).injective]
  congr 1
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  simp [aeval_def]

theorem rootMultiplicityCount : RootMultiplicityCount.{u, v} := by
  intro F L _ _ _ f n hf hn hnpos hs
  rw [← hs.natDegree_eq_card_roots, natDegree_map, hn]

theorem indexedRootProduct : IndexedRootProduct.{u, v} := by
  intro F L _ _ _ f g n m α hf hn hnpos hg hs hα
  rw [paddedRootProduct F L f g n m hf hn hnpos hg hs, ← hα]
  simp [Multiset.map_coe, List.map_ofFn, List.prod_ofFn, Function.comp_def]

theorem monicRootProduct : MonicRootProduct.{u, v} := by
  intro F L _ _ _ f g n m hf hn hnpos hg hs
  simpa [hf.leadingCoeff] using paddedRootProduct F L f g n m hf.ne_zero hn hnpos hg hs

theorem fixedResultantScaling : FixedResultantScaling.{u} := by
  intro R _ f g c n m hf hg
  rw [ResultantDefinition.resultantBridge R (C c * f) g n m
    ((natDegree_C_mul_le c f).trans hf) hg,
    ResultantDefinition.resultantBridge R f g n m hf hg,
    Polynomial.resultant_C_mul_left]

theorem monicNormalization : MonicNormalization.{u} := by
  intro F _ f g n m hf hn hnpos hg
  dsimp only
  have ha : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hback : f = C f.leadingCoeff * (C f.leadingCoeff⁻¹ * f) := by
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  refine ⟨monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ ha), ?_, hback, ?_⟩
  · rw [natDegree_C_mul (inv_ne_zero ha), hn]
  · conv_lhs => rw [hback]
    exact fixedResultantScaling F (C f.leadingCoeff⁻¹ * f) g f.leadingCoeff n m
      (by rw [natDegree_C_mul (inv_ne_zero ha), hn]) hg

end D07.Ch19.ResultantProductDiscriminantPaddedRootProduct
