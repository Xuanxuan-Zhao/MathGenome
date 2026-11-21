import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.DimensionBounds
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.RegularLocalStructure
import MathGenome.Internal.AlgebraCore.P103.Ch07.RegularSequence

/-! CM-08a: regular generators, the field boundary, and Cohen–Macaulayness.
The mounted P103 regular-generator theorem is a proved library result, not
an assumed historical interface. Its hypothesis `regularLocalValue` is
bridged below to Mathlib's `IsRegularLocalRing` by the cotangent-space theorem.
Its ideal-quotient injectivity is then transported to the canonical regular
sequence predicate, which uses module quotients. Cohen–Macaulayness follows
from a regular generating list of dimension length and the depth bound.
-/

universe u
namespace AdvCommAlg.CohenMacaulay

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- Every generating list of dimension length is regular, in any order.
This is stronger than requiring the list to be minimal. -/
theorem regular_generatingList (d : ℕ) (x : List R)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (hlen : x.length = d)
    (hgen : Ideal.ofList x = IsLocalRing.maximalIdeal R) :
    RegularSequence.RingRegular x := by
  have hreg : P103.Specs.Ch07.EmbeddingDimension.regularLocalValue R :=
    (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  obtain ⟨_, hinj, hproper⟩ :=
    P103.Ch07.RegularSequence.generatingList R d x hreg hd hlen hgen
  have hsmul (I : Ideal R) : I • (⊤ : Submodule R R) = I := by
    change I * ⊤ = I
    exact Ideal.mul_top _
  constructor
  · constructor
    intro i hi
    unfold IsSMulRegular
    rw [hsmul]
    exact hinj i hi
  · simpa only [hsmul, ne_comm] using hproper

/-- A regular generating list exists with length exactly the dimension. -/
theorem exists_regular_generators :
    ∃ x : List R, Ideal.ofList x = IsLocalRing.maximalIdeal R ∧
      ringKrullDim R = (x.length : WithBot ℕ∞) ∧ RegularSequence.RingRegular x := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  have hgen : Ideal.ofList s.toList = IsLocalRing.maximalIdeal R := by
    change Submodule.span R {r | r ∈ s.toList} = _
    simpa using hspan
  have hdim : ringKrullDim R = (s.toList.length : WithBot ℕ∞) := by
    rw [Finset.length_toList, hcard]
    exact IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  exact ⟨s.toList, hgen, hdim, regular_generatingList R _ _ hdim rfl hgen⟩

/-- In dimension zero the cotangent space vanishes, so the ring is a field. -/
theorem regularLocal_dimension_zero_isField (hd : ringKrullDim R = 0) : IsField R := by
  apply IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mp
  have h := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  rw [hd] at h
  exact_mod_cast h

/-- A regular local ring has depth equal to its dimension. -/
theorem regularLocal_cohenMacaulay : LocalCohenMacaulay R R := by
  obtain ⟨x, hgen, hdim, hreg⟩ := exists_regular_generators R
  apply (localCohenMacaulay_iff_sourceDepth R R).mpr
  apply le_antisymm (Depth.depth_le_supportDim R)
  change Module.supportDim R R ≤ _
  rw [Module.supportDim_self_eq_ringKrullDim, hdim]
  apply WithBot.coe_le_coe.mpr
  have hm : IsLocalRing.maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ := by
    change IsLocalRing.maximalIdeal R * ⊤ ≠ ⊤
    rw [Ideal.mul_top]
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  rw [Depth.depth_eq_grade, Depth.grade_of_smul_ne_top _ _ hm]
  apply le_sSup
  exact ⟨x, hreg, fun a ha => hgen ▸ Ideal.subset_span ha, rfl⟩

end AdvCommAlg.CohenMacaulay
