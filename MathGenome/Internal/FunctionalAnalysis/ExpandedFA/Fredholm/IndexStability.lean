import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.IndexStability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.AtkinsonCalkin
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.AlgebraicIndexAdditivity
import Mathlib.Analysis.Normed.Operator.Fredholm.Open
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Int
import Mathlib.Tactic.Ring

/-!
Banach-space index calculus for `fa2:p2:index`. The upstream equivalence with
Mathlib's topological Fredholm maps allows using its block-decomposition proof
of openness and local constancy. Compact perturbations are handled by actual
bounded parametrices and a real affine path; no endomorphism restriction is
imposed on the original operator.
-/

noncomputable section
namespace ExpandedFA.Fredholm
open scoped Topology
universe u v w z t

section Banach
variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
  [CompleteSpace X] [CompleteSpace Y]

/-- The native index is exactly the manuscript's integer subtraction. -/
theorem fredholmIndex_eq_native (T : X →L[𝕜] Y) (hT : IsFredholm T) :
    fredholmIndex T hT = T.toLinearMap.index := rfl

/-- The source predicate and the native one agree on Banach spaces. -/
theorem isFredholm_iff_native (T : X →L[𝕜] Y) :
    IsFredholm T ↔ T.IsFredholm := ⟨IsFredholm.to_native, isFredholm_of_native⟩

/-- Operator norm openness, for the original closed-range predicate. -/
theorem isOpen_isFredholm : IsOpen {T : X →L[𝕜] Y | IsFredholm T} := by
  simp_rw [isFredholm_iff_native]
  exact ContinuousLinearMap.isOpen_setOfPred_isFredholm

/-- Both Fredholmness and equality of the integer index hold throughout a
neighborhood of any Fredholm operator. -/
theorem fredholmIndex_eventually_eq (T : X →L[𝕜] Y) (hT : IsFredholm T) :
    ∀ᶠ S in 𝓝 T, ∃ hS : IsFredholm S,
      fredholmIndex S hS = fredholmIndex T hT := by
  filter_upwards [hT.to_native.eventually_nhds,
    hT.to_native.eventually_nhds_index_eq] with S hS hindex
  exact ⟨isFredholm_of_native hS, hindex⟩

/-- Compact perturbations preserve Fredholmness for maps between arbitrary
Banach spaces, by adding compact errors to the same bounded parametrix. -/
theorem IsFredholm.add_compact {T K : X →L[𝕜] Y} (hT : IsFredholm T)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) : IsFredholm (T + K) := by
  obtain ⟨S, hST, hTS⟩ := (atkinson_compact T).mp hT
  apply isFredholm_of_compact_parametrix (T + K) S
  · have heq : S.comp (T + K) - ContinuousLinearMap.id 𝕜 X =
        (S.comp T - ContinuousLinearMap.id 𝕜 X) + S.comp K := by
      ext x
      simp only [sub_apply, add_apply,
        ContinuousLinearMap.comp_apply, map_add]
      abel
    rw [heq]
    exact Compactness.compact_add _ _ hST (Compactness.compact_postcomp _ S hK)
  · have heq : (T + K).comp S - ContinuousLinearMap.id 𝕜 Y =
        (T.comp S - ContinuousLinearMap.id 𝕜 Y) + K.comp S := by
      ext y
      simp only [sub_apply, add_apply,
        ContinuousLinearMap.comp_apply]
      abel
    rw [heq]
    exact Compactness.compact_add _ _ hTS (Compactness.compact_precomp _ S hK)

/-- The equivalence includes preservation of non-Fredholmness. -/
theorem isFredholm_add_compact_iff (T K : X →L[𝕜] Y)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    IsFredholm (T + K) ↔ IsFredholm T := by
  constructor
  · intro h
    have hneg : Compactness.IsCompactLinearMap (-K).toLinearMap := by
      simpa only [neg_one_smul, ContinuousLinearMap.toLinearMap_neg] using
        Compactness.compact_smul (-1 : 𝕜) K.toLinearMap hK
    simpa using h.add_compact hneg
  · exact fun h => h.add_compact hK

end Banach

section Composition
variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w} {Z : Type z}
  [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [NormedSpace 𝕜 Z]
  [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]

/-- Products are Fredholm as actual continuous linear maps. -/
theorem isFredholm_comp (T : X →L[𝕜] Y) (S : Y →L[𝕜] Z)
    (hT : IsFredholm T) (hS : IsFredholm S) : IsFredholm (S.comp T) :=
  isFredholm_of_native (hS.to_native.comp hT.to_native)

/-- The accepted algebraic kernel–cokernel calculation applies to the same
underlying maps and gives the Fredholm product formula. -/
theorem fredholmIndex_comp (T : X →L[𝕜] Y) (S : Y →L[𝕜] Z)
    (hT : IsFredholm T) (hS : IsFredholm S) (hST : IsFredholm (S.comp T)) :
    fredholmIndex (S.comp T) hST = fredholmIndex S hS + fredholmIndex T hT :=
  algebraicIndex_comp T.toLinearMap S.toLinearMap hT.2 hS.2 hST.2

end Composition

section CompactIndex
variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
  [CompleteSpace X] [CompleteSpace Y]

/-- The index is constant along the real affine line of compact perturbations.
This treats operators between distinct spaces as well as endomorphisms. -/
theorem fredholmIndex_add_compact (T K : X →L[𝕜] Y)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap)
    (hT : IsFredholm T) (hTK : IsFredholm (T + K)) :
    fredholmIndex (T + K) hTK = fredholmIndex T hT := by
  let p : ℝ → (X →L[𝕜] Y) := fun t => T + (RCLike.ofReal t : 𝕜) • K
  have hp : Continuous p :=
    continuous_const.add ((RCLike.continuous_ofReal : Continuous (RCLike.ofReal : ℝ → 𝕜)).smul continuous_const)
  have hfp (t : ℝ) : IsFredholm (p t) :=
    hT.add_compact (Compactness.compact_smul (RCLike.ofReal t : 𝕜) K.toLinearMap hK)
  have hi : Continuous (fun t : ℝ => (p t).toLinearMap.index) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hfp t).to_native.index_continuousAt.comp hp.continuousAt
  have hconst := isPreconnected_univ.constant hi.continuousOn
    (x := (1 : ℝ)) (y := (0 : ℝ)) (Set.mem_univ _) (Set.mem_univ _)
  rw [fredholmIndex_eq_native, fredholmIndex_eq_native]
  simpa only [p, RCLike.ofReal_one, RCLike.ofReal_zero, one_smul, zero_smul, add_zero]
    using hconst

end CompactIndex

namespace IndexStability
section AlgebraicProducts
variable {𝕜 : Type u} [Field 𝕜]
  {E : Type v} {F : Type w} [AddCommGroup E] [AddCommGroup F]
  [Module 𝕜 E] [Module 𝕜 F]

/-- The actual quotient of a binary product is the product of the two
quotients. The map is induced by the two canonical quotient maps. -/
def quotientProdEquiv (p : Submodule 𝕜 E) (q : Submodule 𝕜 F) :
    ((E × F) ⧸ p.prod q) ≃ₗ[𝕜] (E ⧸ p) × (F ⧸ q) := by
  let f := p.mkQ.prodMap q.mkQ
  have hk : f.ker = p.prod q := by
    simp only [f, LinearMap.ker_prodMap, Submodule.ker_mkQ]
  have hs : Function.Surjective f := by
    rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := p.mkQ_surjective x
    obtain ⟨b, rfl⟩ := q.mkQ_surjective y
    exact ⟨(a, b), rfl⟩
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs)

end AlgebraicProducts
end IndexStability

section DirectSums
variable {𝕜 : Type u} [RCLike 𝕜]
  {X : Type v} {Y : Type w} {X' : Type z} {Y' : Type t}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedAddCommGroup X'] [NormedAddCommGroup Y']
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
  [NormedSpace 𝕜 X'] [NormedSpace 𝕜 Y']
  [CompleteSpace X] [CompleteSpace Y] [CompleteSpace X'] [CompleteSpace Y']

/-- Binary direct sums are Fredholm; kernels and actual cokernels split. -/
theorem isFredholm_prodMap (S : X →L[𝕜] Y) (T : X' →L[𝕜] Y')
    (hS : IsFredholm S) (hT : IsFredholm T) : IsFredholm (S.prodMap T) := by
  have hk : (S.prodMap T).ker = S.ker.prod T.ker :=
    LinearMap.ker_prodMap S.toLinearMap T.toLinearMap
  have hr : (S.prodMap T).range = S.range.prod T.range :=
    LinearMap.range_prodMap S.toLinearMap T.toLinearMap
  let := hS.2.1
  let := hT.2.1
  let := hS.2.2
  let := hT.2.2
  refine ⟨?_, ?_, ?_⟩
  · change IsClosed ((S.prodMap T).range : Set (Y × Y'))
    rw [hr]
    exact hS.1.prod hT.1
  · rw [hk]
    exact Module.Finite.equiv (Submodule.prodEquiv S.ker T.ker).symm
  · rw [hr]
    exact Module.Finite.equiv (IndexStability.quotientProdEquiv S.range T.range).symm

/-- The integer index of the binary direct sum is the sum of the indices. -/
theorem fredholmIndex_prodMap (S : X →L[𝕜] Y) (T : X' →L[𝕜] Y')
    (hS : IsFredholm S) (hT : IsFredholm T) (hST : IsFredholm (S.prodMap T)) :
    fredholmIndex (S.prodMap T) hST = fredholmIndex S hS + fredholmIndex T hT := by
  have hk : (S.prodMap T).ker = S.ker.prod T.ker :=
    LinearMap.ker_prodMap S.toLinearMap T.toLinearMap
  have hr : (S.prodMap T).range = S.range.prod T.range :=
    LinearMap.range_prodMap S.toLinearMap T.toLinearMap
  let := hS.2.1
  let := hT.2.1
  let := hS.2.2
  let := hT.2.2
  unfold fredholmIndex
  rw [hk, hr, (Submodule.prodEquiv S.ker T.ker).finrank_eq,
    (IndexStability.quotientProdEquiv S.range T.range).finrank_eq,
    Module.finrank_prod, Module.finrank_prod]
  push_cast
  ring

end DirectSums

end ExpandedFA.Fredholm
