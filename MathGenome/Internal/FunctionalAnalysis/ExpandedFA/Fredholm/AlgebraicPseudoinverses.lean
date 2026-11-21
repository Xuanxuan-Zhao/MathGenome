import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.AlgebraicPseudoinverses
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.AlgebraicIndexAdditivity
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Complement-based generalized inverses and algebraic finite-index stability.
The ambient vector spaces may have arbitrary dimension and carry no topology.
The product law is reused from the accepted algebraic exact-sequence theorem. -/

noncomputable section
namespace ExpandedFA.Fredholm.AlgebraicPseudoinverses
universe u v w z
variable {𝕜 : Type u} [Field 𝕜] {X : Type v} {Y : Type w}
  [AddCommGroup X] [AddCommGroup Y] [Module 𝕜 X] [Module 𝕜 Y]

/-- Invert the quotient-to-range isomorphism, choose the representative in the
specified kernel complement, and extend by zero on the range complement. -/
def inverseOfComplements (T : X →ₗ[𝕜] Y) (X₀ : Submodule 𝕜 X) (C : Submodule 𝕜 Y)
    (hX : IsCompl T.ker X₀) (hY : IsCompl T.range C) : Y →ₗ[𝕜] X :=
  X₀.subtype.comp (((T.ker.quotientEquivOfIsCompl X₀ hX).toLinearMap.comp
    T.quotKerEquivRange.symm.toLinearMap).comp (T.range.projectionOnto C hY))

theorem inverseOfComplements_comp (T : X →ₗ[𝕜] Y)
    (X₀ : Submodule 𝕜 X) (C : Submodule 𝕜 Y)
    (hX : IsCompl T.ker X₀) (hY : IsCompl T.range C) :
    (inverseOfComplements T X₀ C hX hY).comp T = X₀.projection T.ker hX.symm := by
  ext x
  change (T.ker.quotientEquivOfIsCompl X₀ hX
    (T.quotKerEquivRange.symm (T.range.projectionOnto C hY (T x))) : X) = _
  rw [Submodule.projectionOnto_apply_of_mem_left hY (show T x ∈ T.range from ⟨x, rfl⟩)]
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

theorem comp_inverseOfComplements (T : X →ₗ[𝕜] Y)
    (X₀ : Submodule 𝕜 X) (C : Submodule 𝕜 Y)
    (hX : IsCompl T.ker X₀) (hY : IsCompl T.range C) :
    T.comp (inverseOfComplements T X₀ C hX hY) = T.range.projection C hY := by
  ext y
  let q := T.quotKerEquivRange.symm (T.range.projectionOnto C hY y)
  have hq := Submodule.mk_quotientEquivOfIsCompl_apply hX q
  change T (T.ker.quotientEquivOfIsCompl X₀ hX q) =
    (T.range.projectionOnto C hY y : Y)
  calc
    _ = (T.quotKerEquivRange (T.ker.mkQ (T.ker.quotientEquivOfIsCompl X₀ hX q)) : Y) := rfl
    _ = (T.quotKerEquivRange q : Y) := congrArg (fun q => (T.quotKerEquivRange q : Y)) hq
    _ = _ := congrArg Subtype.val (T.quotKerEquivRange.apply_symm_apply _)

/-- The chosen complements give both reflexive inverse identities and the exact
defect projections. -/
theorem complement_construction :
    AlgebraicPseudoinversesSpec.ComplementConstruction := by
  intro 𝕜 _ X Y _ _ _ _ T X₀ C hX hY
  let S := inverseOfComplements T X₀ C hX hY
  have hST : S.comp T = X₀.projection T.ker hX.symm :=
    inverseOfComplements_comp T X₀ C hX hY
  have hTS : T.comp S = T.range.projection C hY :=
    comp_inverseOfComplements T X₀ C hX hY
  refine ⟨S, ?_, ?_, hST, hTS, ?_, ?_⟩
  · rw [hTS]
    ext x
    exact Submodule.projection_apply_of_mem_left hY ⟨x, rfl⟩
  · rw [hST]
    ext y
    apply Submodule.projection_apply_of_mem_left hX.symm
    exact Submodule.coe_mem _
  · rw [hST, ← Submodule.projection_eq_id_sub_projection hX.symm]
  · rw [hTS, ← Submodule.projection_eq_id_sub_projection hY]

/-- Existence of complements is the only use of vector-space choice. -/
theorem exists_generalizedInverse :
    AlgebraicPseudoinversesSpec.GeneralizedInverseExistence := by
  intro 𝕜 _ X Y _ _ _ _ T
  obtain ⟨X₀, hX⟩ := T.ker.exists_isCompl
  obtain ⟨C, hY⟩ := T.range.exists_isCompl
  obtain ⟨S, hTST, hSTS, _, _, hP, hQ⟩ := complement_construction T X₀ C hX hY
  refine ⟨S, hTST, hSTS, ?_, ?_, ?_, ?_⟩
  · rw [hP]; exact Submodule.isIdempotentElem_projection hX
  · rw [hQ]; exact Submodule.isIdempotentElem_projection hY.symm
  · rw [hP, Submodule.range_projection]
  · rw [hQ, Submodule.range_projection]; exact hY

/-- An inner inverse already makes the left defect project onto the kernel. -/
theorem left_defect_range (T : X →ₗ[𝕜] Y) (S : Y →ₗ[𝕜] X)
    (h : (T.comp S).comp T = T) :
    (LinearMap.id - S.comp T).range = T.ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change T (y - S (T y)) = 0
    rw [map_sub, show T (S (T y)) = T y from LinearMap.congr_fun h y, sub_self]
  · intro hx
    refine ⟨x, ?_⟩
    change x - S (T x) = x
    rw [show T x = 0 from hx, map_zero, sub_zero]

/-- The right defect has range complementary to the actual range, without any
closedness or finite-dimensionality hypothesis. -/
theorem right_defect_isCompl (T : X →ₗ[𝕜] Y) (S : Y →ₗ[𝕜] X)
    (h : (T.comp S).comp T = T) :
    IsCompl T.range (LinearMap.id - T.comp S).range := by
  have hp : LinearMap.IsProj T.range (T.comp S) :=
    ⟨fun y => ⟨S y, rfl⟩, by
      rintro y ⟨x, rfl⟩
      exact LinearMap.congr_fun h x⟩
  rw [← LinearMap.IsIdempotentElem.ker_eq_range hp.isIdempotentElem]
  exact hp.isCompl

theorem defect_index_formula :
    AlgebraicPseudoinversesSpec.DefectIndexFormula := by
  intro 𝕜 _ X Y _ _ _ _ T S hTST _ hT
  have : FiniteDimensional 𝕜 T.ker := hT.1
  have : FiniteDimensional 𝕜 (Y ⧸ T.range) := hT.2
  have hP := left_defect_range T S hTST
  let e := T.range.quotientEquivOfIsCompl (LinearMap.id - T.comp S).range
    (right_defect_isCompl T S hTST)
  refine ⟨?_, Module.Finite.equiv e, ?_⟩
  · rw [hP]; infer_instance
  · change (Module.finrank 𝕜 T.ker : ℤ) - (Module.finrank 𝕜 (Y ⧸ T.range) : ℤ) = _
    rw [hP, ← e.finrank_eq]

/-- The converse does not require the putative inverse to satisfy either
reflexive identity: finite-rank errors alone suffice. -/
theorem finite_index_of_finite_defects (T : X →ₗ[𝕜] Y) (S : Y →ₗ[𝕜] X)
    (hP : FiniteDimensional 𝕜 (LinearMap.id - S.comp T).range)
    (hQ : FiniteDimensional 𝕜 (LinearMap.id - T.comp S).range) :
    IsAlgebraicFiniteIndex T := by
  let P := LinearMap.id - S.comp T
  let Q := LinearMap.id - T.comp S
  have : FiniteDimensional 𝕜 P.range := hP
  have : FiniteDimensional 𝕜 Q.range := hQ
  constructor
  · apply Submodule.finiteDimensional_of_le (S₂ := P.range)
    intro x hx
    refine ⟨x, ?_⟩
    change x - S (T x) = x
    rw [show T x = 0 from hx, map_zero, sub_zero]
  · let f : Q.range →ₗ[𝕜] Y ⧸ T.range := T.range.mkQ.comp Q.range.subtype
    apply FiniteDimensional.of_surjective f
    intro q
    obtain ⟨y, rfl⟩ := T.range.mkQ_surjective q
    refine ⟨⟨Q y, ⟨y, rfl⟩⟩, ?_⟩
    change T.range.mkQ (y - T (S y)) = T.range.mkQ y
    have hz : T.range.mkQ (T (S y)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨S y, rfl⟩
    rw [map_sub, hz, sub_zero]

theorem finite_defect_characterization :
    AlgebraicPseudoinversesSpec.FiniteDefectCharacterization := by
  intro 𝕜 _ X Y _ _ _ _ T
  constructor
  · intro hT
    obtain ⟨S, hTST, hSTS, _⟩ := exists_generalizedInverse T
    exact ⟨S, (defect_index_formula T S hTST hSTS hT).1,
      (defect_index_formula T S hTST hSTS hT).2.1⟩
  · rintro ⟨S, hP, hQ⟩
    exact finite_index_of_finite_defects T S hP hQ

/-- Finite rank is an algebraic ideal: composing on either side and adding or
subtracting finite-rank maps preserves finite rank. -/
theorem finite_range_comp_left {Z : Type*} [AddCommGroup Z] [Module 𝕜 Z]
    (D : X →ₗ[𝕜] Y) (U : Y →ₗ[𝕜] Z) [FiniteDimensional 𝕜 D.range] :
    FiniteDimensional 𝕜 (U.comp D).range := by
  rw [LinearMap.range_comp]
  infer_instance

theorem finite_range_comp_right {Z : Type*} [AddCommGroup Z] [Module 𝕜 Z]
    (D : X →ₗ[𝕜] Y) (U : Z →ₗ[𝕜] X) [FiniteDimensional 𝕜 D.range] :
    FiniteDimensional 𝕜 (D.comp U).range :=
  Submodule.finiteDimensional_of_le (LinearMap.range_comp_le_range U D)

theorem finite_range_sub (D F : X →ₗ[𝕜] Y)
    [FiniteDimensional 𝕜 D.range] [FiniteDimensional 𝕜 F.range] :
    FiniteDimensional 𝕜 (D - F).range := by
  have : FiniteDimensional 𝕜 (-F).range := by rw [LinearMap.range_neg]; infer_instance
  rw [sub_eq_add_neg]
  exact Submodule.finiteDimensional_of_le (LinearMap.range_add_le D (-F))

/-- A parametrix for `T` is still a parametrix after any finite-rank change. -/
theorem finite_index_add (T D : X →ₗ[𝕜] Y)
    (hD : FiniteDimensional 𝕜 D.range) (hT : IsAlgebraicFiniteIndex T) :
    IsAlgebraicFiniteIndex (T + D) := by
  have : FiniteDimensional 𝕜 D.range := hD
  obtain ⟨S, hP, hQ⟩ := (finite_defect_characterization T).mp hT
  have : FiniteDimensional 𝕜 (LinearMap.id - S.comp T).range := hP
  have : FiniteDimensional 𝕜 (LinearMap.id - T.comp S).range := hQ
  have : FiniteDimensional 𝕜 (S.comp D).range := finite_range_comp_left D S
  have : FiniteDimensional 𝕜 (D.comp S).range := finite_range_comp_right D S
  apply finite_index_of_finite_defects (T + D) S
  · rw [LinearMap.comp_add, ← sub_sub]
    exact finite_range_sub _ _
  · rw [LinearMap.add_comp, ← sub_sub]
    exact finite_range_sub _ _

theorem finite_rank_perturbation_finiteness :
    AlgebraicPseudoinversesSpec.FiniteRankPerturbationFiniteness := by
  intro 𝕜 _ X Y _ _ _ _ T D hD
  constructor
  · intro hTD
    have hnD : FiniteDimensional 𝕜 (-D).range := by rw [LinearMap.range_neg]; exact hD
    have h := finite_index_add (T + D) (-D) hnD hTD
    rw [add_assoc, add_neg_cancel, add_zero] at h
    exact h
  · exact finite_index_add T D hD

/-- Restrict both maps to the cofinite subspace `ker D`. The restrictions agree,
so product additivity cancels the common index of its inclusion. -/
theorem finite_rank_perturbation_index :
    AlgebraicPseudoinversesSpec.FiniteRankPerturbationIndex := by
  intro 𝕜 _ X Y _ _ _ _ T D hD hT hTD
  have : FiniteDimensional 𝕜 D.range := hD
  have : FiniteDimensional 𝕜 (X ⧸ D.ker) := Module.Finite.equiv D.quotKerEquivRange.symm
  have hE : IsAlgebraicFiniteIndex D.ker.subtype := by
    constructor
    · rw [Submodule.ker_subtype]; infer_instance
    · rw [Submodule.range_subtype]; infer_instance
  have hR := isAlgebraicFiniteIndex_comp D.ker.subtype T hE hT
  have hR' := isAlgebraicFiniteIndex_comp D.ker.subtype (T + D) hE hTD
  have hsame : (T + D).comp D.ker.subtype = T.comp D.ker.subtype := by
    ext x
    change T x + D x = T x
    rw [show D x = 0 from x.property, add_zero]
  have hi := algebraicIndex_comp D.ker.subtype T hE hT hR
  have hi' := algebraicIndex_comp D.ker.subtype (T + D) hE hTD hR'
  change algebraicIndex (T + D) hTD = algebraicIndex T hT
  unfold algebraicIndex at hi hi' ⊢
  rw [hsame] at hi'
  omega

/-- Product additivity applies to these same purely algebraic finite-index maps. -/
theorem composition_index : AlgebraicPseudoinversesSpec.CompositionIndex := by
  intro 𝕜 _ X Y Z _ _ _ _ _ _ T U hT hU
  have hUT := isAlgebraicFiniteIndex_comp T U hT hU
  exact ⟨hUT, algebraicIndex_comp T U hT hU hUT⟩

end ExpandedFA.Fredholm.AlgebraicPseudoinverses
