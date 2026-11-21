import MathGenome.Internal.Specs.D05.M06.InvariantDecomposition
import MathGenome.Internal.D05.M06.ExternalSum

/-! Invariant summands and commuting component projections, without dimension assumptions. -/
namespace D05.M06.InvariantDecomposition

open Specs.D05.M06.InvariantDecomposition
open Specs.D05.M06.ExternalSum (summationMap)
open Specs.D05.M06.Invariant (invariant_value restriction_value)

theorem finite_internal_iff_bijective :
    Specs.D05.M06.InvariantDecomposition.finite_internal_iff_bijective := by
  intro K V ι _ _ _ _ U
  exact (D05.M06.ExternalSum.bijective_iff_internal U).symm

theorem summationEquiv_apply :
    Specs.D05.M06.InvariantDecomposition.summationEquiv_apply := by
  intro K V ι _ _ _ U h x
  rfl

theorem componentProjection_on_sum :
    Specs.D05.M06.InvariantDecomposition.componentProjection_on_sum := by
  intro K V ι _ _ _ U h x i
  change (((summationEquiv U h).symm (summationEquiv U h x)) i : V) = _
  rw [LinearEquiv.symm_apply_apply]

theorem componentProjection_on_summand :
    Specs.D05.M06.InvariantDecomposition.componentProjection_on_summand := by
  intro K V ι _ _ _ U h i u
  classical
  have hs : summationMap U (_root_.DirectSum.lof K ι (fun j => U j) i u) = (u : V) := by
    exact _root_.DirectSum.coeLinearMap_lof U i u
  have heq := componentProjection_on_sum U h
    (_root_.DirectSum.lof K ι (fun j => U j) i u) i
  rw [hs] at heq
  simpa using heq

theorem componentProjection_properties :
    Specs.D05.M06.InvariantDecomposition.componentProjection_properties := by
  intro K V ι _ _ _ U h i
  have hm (v : V) : componentProjection U h i v ∈ U i :=
    (((summationEquiv U h).symm v) i).property
  have hf (v : V) (hv : v ∈ U i) : componentProjection U h i v = v :=
    componentProjection_on_summand U h i ⟨v, hv⟩
  refine ⟨?_, ?_, ?_⟩
  · ext v
    exact hf _ (hm v)
  · apply le_antisymm
    · rintro v ⟨x, rfl⟩
      exact hm x
    · intro v hv
      exact ⟨v, hf v hv⟩
  · intro v
    exact ⟨fun hv => hv ▸ hm v, hf v⟩

theorem direct_sum_intertwines :
    Specs.D05.M06.InvariantDecomposition.direct_sum_intertwines := by
  intro K V ι _ _ _ U T hT
  classical
  -- Equality on each summand extends to every finitely supported sum.
  apply _root_.DirectSum.linearMap_ext
  intro i
  ext u
  simp only [LinearMap.comp_apply, summationMap, _root_.DirectSum.coeLinearMap_lof,
    restrictedSum, _root_.DirectSum.lmap_lof]
  rfl

private theorem decomposition_natural {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] (U : ι → Submodule K V) (h : Function.Bijective (summationMap U))
    (T : Module.End K V) (hT : ∀ i, invariant_value K V (U i) T) (v : V) :
    (summationEquiv U h).symm (T v) =
      restrictedSum U T hT ((summationEquiv U h).symm v) := by
  apply (summationEquiv U h).injective
  rw [LinearEquiv.apply_symm_apply]
  have heq := congrArg (fun f => f ((summationEquiv U h).symm v))
    (direct_sum_intertwines U T hT)
  change T (summationEquiv U h ((summationEquiv U h).symm v)) =
    summationEquiv U h (restrictedSum U T hT ((summationEquiv U h).symm v)) at heq
  simpa only [LinearEquiv.apply_symm_apply] using heq

theorem transformed_component :
    Specs.D05.M06.InvariantDecomposition.transformed_component := by
  intro K V ι _ _ _ U h T hT v i
  exact congrArg (fun x => x i) (decomposition_natural U h T hT v)

theorem invariant_iff_commuting :
    Specs.D05.M06.InvariantDecomposition.invariant_iff_commuting := by
  intro K V ι _ _ _ U h T
  constructor
  · intro hT i
    ext v
    exact congrArg (fun x : U i => (x : V)) (transformed_component U h T hT v i)
  · intro hc i u hu
    -- Commutation carries a fixed vector to a fixed vector of the same projection.
    have hfix := (componentProjection_properties U h i).2.2
    apply (hfix (T u)).mp
    have heq := congrArg (fun f : Module.End K V => f u) (hc i)
    change componentProjection U h i (T u) = T (componentProjection U h i u) at heq
    rw [(hfix u).mpr hu] at heq
    exact heq

theorem direct_sum_conjugacy :
    Specs.D05.M06.InvariantDecomposition.direct_sum_conjugacy := by
  intro K V ι _ _ _ U h T hT
  apply LinearMap.ext
  intro x
  apply _root_.DirectSum.ext
  intro i
  change ((summationEquiv U h).symm (T (summationEquiv U h x))) i =
    restriction_value K V (U i) T (hT i) (x i)
  simpa only [LinearEquiv.symm_apply_apply] using
    transformed_component U h T hT (summationEquiv U h x) i

theorem finite_invariant_decomposition :
    Specs.D05.M06.InvariantDecomposition.finite_invariant_decomposition := by
  intro K V ι _ _ _ _ U hU T
  let h := (finite_internal_iff_bijective U).mp hU
  exact ⟨h, invariant_iff_commuting U h T, direct_sum_conjugacy U h T⟩

end D05.M06.InvariantDecomposition
