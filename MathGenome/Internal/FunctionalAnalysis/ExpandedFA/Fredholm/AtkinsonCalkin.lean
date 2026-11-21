import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.AtkinsonCalkin
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.AtkinsonParametrices
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section
namespace ExpandedFA.Fredholm
universe u v w
open scoped Topology LinearMap.FiniteRangeSetoid

/-- The full Banach-space compact parametrix characterization. -/
theorem atkinson_compact : AtkinsonCalkinSpec.TwoSidedCompactCharacterization.{u, v, w} :=
  atkinson_compact_parametrix

/-- The equivalent characterization by two finite-rank defects. -/
theorem atkinson_finite_rank : AtkinsonCalkinSpec.TwoSidedFiniteRankCharacterization.{u, v, w} :=
  atkinson_finite_rank_parametrix

/-- Invertibility in the genuine Calkin ring, including its zero-ring case. -/
theorem atkinson_calkin : AtkinsonCalkinSpec.CalkinCharacterization := by
  intro 𝕜 _ X _ _ _ T
  rw [atkinson_compact_parametrix]
  constructor
  · rintro ⟨S, hST, hTS⟩
    have hl : calkinProjection 𝕜 X S * calkinProjection 𝕜 X T = 1 := by
      rw [← map_mul, ← map_one (calkinProjection 𝕜 X)]
      exact (calkinProjection_eq_iff _ _).mpr hST
    have hr : calkinProjection 𝕜 X T * calkinProjection 𝕜 X S = 1 := by
      rw [← map_mul, ← map_one (calkinProjection 𝕜 X)]
      exact (calkinProjection_eq_iff _ _).mpr hTS
    exact ⟨⟨calkinProjection 𝕜 X T, calkinProjection 𝕜 X S, hr, hl⟩, rfl⟩
  · rintro ⟨a, ha⟩
    change (a : Calkin 𝕜 X) = calkinProjection 𝕜 X T at ha
    obtain ⟨S, hS⟩ := calkinProjection_surjective (a.inv : Calkin 𝕜 X)
    refine ⟨S, ?_, ?_⟩
    · apply (calkinProjection_eq_iff _ _).mp
      change calkinProjection 𝕜 X (S * T) = calkinProjection 𝕜 X 1
      rw [map_mul, map_one, hS, ← ha]
      exact a.inv_val
    · apply (calkinProjection_eq_iff _ _).mp
      change calkinProjection 𝕜 X (T * S) = calkinProjection 𝕜 X 1
      rw [map_mul, map_one, hS, ← ha]
      exact a.val_inv

section Banach
variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
  [CompleteSpace X] [CompleteSpace Y]

/-- A continuous left inverse modulo finite rank forces closed range.
On the finite-codimension equalizer it gives a norm lower bound. -/
theorem closed_range_of_left_quasiInverse (T : X →L[𝕜] Y) (U : Y →L[𝕜] X)
    (hU : U.toLinearMap.IsLeftQuasiInverse T.toLinearMap) :
    IsClosed (T.range : Set Y) := by
  let M := (ContinuousLinearMap.id 𝕜 X).eqLocus (U.comp T)
  have hM : M.CoFG :=
    LinearMap.FiniteRangeSetoid.equiv_iff_eqLocus_coFG.mp (Setoid.symm hU.equiv)
  let := hM
  let : CompleteSpace M := (ContinuousLinearMap.isClosed_eqLocus _ _).completeSpace_coe
  have hb : ∀ x : M, ‖x‖ ≤ ‖U‖₊ * ‖T.domRestrict M x‖ := by
    intro x
    have hx : (x : X) = U (T x) := x.property
    calc
      ‖x‖ = ‖U (T x)‖ := congrArg norm hx
      _ ≤ ‖U‖₊ * ‖T.domRestrict M x‖ := U.le_opNorm _
  have hc := ((T.domRestrict M).antilipschitz_of_bound hb).isClosed_range
    (T.domRestrict M).uniformContinuous
  exact T.toLinearMap.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient
    (s := M) (by
      have heq : (M.map T.toLinearMap : Set Y) = Set.range (T.domRestrict M) := by
        ext y
        exact ⟨fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩,
          fun ⟨x, hx⟩ => ⟨x, x.property, hx⟩⟩
      rwa [heq])

/-- A compact left defect forces the closed-range/finite-kernel conditions,
even for Banach spaces. No converse for general Banach spaces is asserted. -/
theorem closed_finite_kernel_of_left_compact (T : X →L[𝕜] Y) (S : Y →L[𝕜] X)
    (h : Compactness.IsCompactLinearMap
      (S.comp T - ContinuousLinearMap.id 𝕜 X).toLinearMap) :
    IsClosed (T.range : Set Y) ∧ FiniteDimensional 𝕜 T.ker := by
  have hn : Compactness.IsCompactLinearMap
      (ContinuousLinearMap.id 𝕜 X - S.comp T).toLinearMap := by
    simpa only [neg_one_smul, ContinuousLinearMap.toLinearMap_sub, neg_sub] using
      Compactness.compact_smul (-1 : 𝕜) _ h
  have hprod := identity_sub_compact_isFredholm _ hn
  rw [sub_sub_cancel] at hprod
  obtain ⟨A, hA⟩ := hprod.to_native.exists_isQuasiInverse
  have hleft : (A.comp S).toLinearMap.IsLeftQuasiInverse T.toLinearMap := hA.1
  let := hprod.2.1
  exact ⟨closed_range_of_left_quasiInverse T (A.comp S) hleft,
    Submodule.finiteDimensional_of_le (show T.ker ≤ (S.comp T).ker from
      fun x hx => by change S (T x) = 0; change T x = 0 at hx; rw [hx, map_zero])⟩

/-- A right compact defect forces closed range and finite cokernel:
the range contains the closed finite-codimension range of `TS`. -/
theorem closed_finite_cokernel_of_right_compact (T : X →L[𝕜] Y) (S : Y →L[𝕜] X)
    (h : Compactness.IsCompactLinearMap
      (T.comp S - ContinuousLinearMap.id 𝕜 Y).toLinearMap) :
    IsClosed (T.range : Set Y) ∧ FiniteDimensional 𝕜 (Y ⧸ T.range) := by
  have hn : Compactness.IsCompactLinearMap
      (ContinuousLinearMap.id 𝕜 Y - T.comp S).toLinearMap := by
    simpa only [neg_one_smul, ContinuousLinearMap.toLinearMap_sub, neg_sub] using
      Compactness.compact_smul (-1 : 𝕜) _ h
  have hprod := identity_sub_compact_isFredholm _ hn
  rw [sub_sub_cancel] at hprod
  let := hprod.2.2
  have hle : (T.comp S).range ≤ T.range := by
    rintro y ⟨x, rfl⟩
    exact ⟨S x, rfl⟩
  exact ⟨Submodule.isClosed_mono_of_finiteDimensional_quotient hprod.1 hle,
    Module.Finite.of_surjective
      (Submodule.mapQ _ _ LinearMap.id hle) (by
        intro z
        obtain ⟨y, rfl⟩ := T.range.mkQ_surjective z
        exact ⟨Submodule.Quotient.mk y, rfl⟩)⟩
end Banach

section Hilbert
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

/-- The bounded generalized inverse of a closed-range Hilbert operator.
Its two errors are exactly the orthogonal kernel and cokernel projections. -/
theorem closed_range_generalized_inverse (T : H →L[𝕜] K)
    (hc : IsClosed (T.range : Set K)) :
    ∃ S : K →L[𝕜] H,
      S.comp T = ContinuousLinearMap.id 𝕜 H - T.ker.starProjection ∧
      T.comp S = T.range.starProjection := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  let : CompleteSpace T.range := hc.completeSpace_coe
  let f : T.kerᗮ →L[𝕜] T.range := T.rangeRestrict.comp T.kerᗮ.subtypeL
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro x hx
      have hxk : (x : H) ∈ T.ker := congrArg Subtype.val hx
      have hz : (x : H) = 0 :=
        Submodule.disjoint_def.mp T.ker.orthogonal_disjoint (x : H) hxk x.property
      exact Subtype.ext hz
    · exact bot_le
  have hs : Function.Surjective f := by
    rintro ⟨y, x, rfl⟩
    refine ⟨⟨x - T.ker.starProjection x,
      T.ker.sub_starProjection_mem_orthogonal x⟩, ?_⟩
    apply Subtype.ext
    change T (x - T.ker.starProjection x) = T x
    rw [map_sub, show T (T.ker.starProjection x) = 0 from
      (T.ker.orthogonalProjectionOnto x).property, sub_zero]
  let e : T.kerᗮ ≃L[𝕜] T.range :=
    (LinearEquiv.ofBijective f.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquivOfContinuous
      f.continuous
  let S : K →L[𝕜] H := T.kerᗮ.subtypeL.comp
    (e.symm.toContinuousLinearMap.comp T.range.orthogonalProjectionOnto)
  have hf (x : T.kerᗮ) : T x = (e x : K) := rfl
  refine ⟨S, ?_, ?_⟩
  · rw [← T.ker.starProjection_orthogonal]
    ext x
    change (e.symm (T.range.orthogonalProjectionOnto (T x)) : H) =
      (T.kerᗮ.orthogonalProjectionOnto x : H)
    apply congrArg Subtype.val
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rw [← hf]
    change T.range.starProjection (T x) = T (T.kerᗮ.starProjection x)
    calc
      T.range.starProjection (T x) = T x :=
        T.range.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
      _ = T (T.kerᗮ.starProjection x) := by
        rw [T.ker.starProjection_orthogonal_val, map_sub,
          show T (T.ker.starProjection x) = 0 from
            (T.ker.orthogonalProjectionOnto x).property, sub_zero]
  · ext y
    change T (e.symm (T.range.orthogonalProjectionOnto y)) =
      (T.range.orthogonalProjectionOnto y : K)
    rw [hf, e.apply_symm_apply]

/-- Left finite-rank parametrix on Hilbert spaces. -/
theorem hilbert_left_finite_rank : AtkinsonCalkinSpec.LeftFiniteRankCharacterization := by
  intro 𝕜 _ H K _ _ _ _ _ _ T
  constructor
  · intro hT
    obtain ⟨S, hST, _⟩ := closed_range_generalized_inverse T hT.1
    let := hT.2
    refine ⟨S, ?_⟩
    rw [hST, sub_sub_cancel_left]
    have heq : (-T.ker.starProjection).range = T.ker := by
      rw [ContinuousLinearMap.toLinearMap_neg, LinearMap.range_neg,
        Submodule.range_starProjection]
    rw [heq]
    infer_instance
  · rintro ⟨S, hS⟩
    let := hS
    exact closed_finite_kernel_of_left_compact T S (compact_of_finiteDimensional_range _)

/-- Right finite-rank parametrix on Hilbert spaces. -/
theorem hilbert_right_finite_rank : AtkinsonCalkinSpec.RightFiniteRankCharacterization := by
  intro 𝕜 _ H K _ _ _ _ _ _ T
  constructor
  · intro hT
    obtain ⟨S, _, hTS⟩ := closed_range_generalized_inverse T hT.1
    let : CompleteSpace T.range := hT.1.completeSpace_coe
    let := hT.2
    let : FiniteDimensional 𝕜 T.rangeᗮ :=
      (T.range.quotientEquivOrthogonal.toLinearEquiv).finiteDimensional
    refine ⟨S, ?_⟩
    rw [hTS]
    have heq : (T.range.starProjection - ContinuousLinearMap.id 𝕜 K).range =
        T.rangeᗮ := by
      rw [show T.range.starProjection - ContinuousLinearMap.id 𝕜 K =
        -T.rangeᗮ.starProjection by rw [T.range.starProjection_orthogonal]; abel]
      rw [ContinuousLinearMap.toLinearMap_neg, LinearMap.range_neg,
        Submodule.range_starProjection]
    rw [heq]
    infer_instance
  · rintro ⟨S, hS⟩
    let := hS
    exact closed_finite_cokernel_of_right_compact T S (compact_of_finiteDimensional_range _)

/-- Left inverse modulo compact maps iff closed range and finite kernel. -/
theorem hilbert_left_compact : AtkinsonCalkinSpec.LeftCompactCharacterization := by
  intro 𝕜 _ H K _ _ _ _ _ _ T
  constructor
  · intro hT
    obtain ⟨S, hS⟩ := (hilbert_left_finite_rank T).mp hT
    let := hS
    exact ⟨S, compact_of_finiteDimensional_range _⟩
  · rintro ⟨S, hS⟩
    exact closed_finite_kernel_of_left_compact T S hS

/-- Right inverse modulo compact maps iff closed range and finite cokernel. -/
theorem hilbert_right_compact : AtkinsonCalkinSpec.RightCompactCharacterization := by
  intro 𝕜 _ H K _ _ _ _ _ _ T
  constructor
  · intro hT
    obtain ⟨S, hS⟩ := (hilbert_right_finite_rank T).mp hT
    let := hS
    exact ⟨S, compact_of_finiteDimensional_range _⟩
  · rintro ⟨S, hS⟩
    exact closed_finite_cokernel_of_right_compact T S hS
open scoped InnerProduct

/-- Closed range passes to the Hilbert adjoint. The generalized inverse
shows that its range contains the entire orthogonal complement of the kernel. -/
theorem closed_range_adjoint (T : H →L[𝕜] K) (hc : IsClosed (T.range : Set K)) :
    IsClosed (T.adjoint.range : Set H) := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  obtain ⟨S, hST, _⟩ := closed_range_generalized_inverse T hc
  rw [← T.ker.starProjection_orthogonal] at hST
  have heq : T.adjoint.comp S.adjoint = T.kerᗮ.starProjection := by
    have h := congrArg ContinuousLinearMap.adjoint hST
    simpa only [ContinuousLinearMap.adjoint_comp,
      T.kerᗮ.starProjection_isSymmetric.clm_adjoint_eq] using h
  have hr : T.adjoint.range = T.kerᗮ := by
    apply le_antisymm
    · rw [T.orthogonal_ker]
      exact Submodule.le_topologicalClosure _
    · rw [← Submodule.range_starProjection T.kerᗮ, ← heq]
      rintro x ⟨y, rfl⟩
      exact ⟨S.adjoint y, rfl⟩
  rw [hr]
  exact T.ker.isClosed_orthogonal

/-- Right semi-Fredholmness equals left semi-Fredholmness of the genuine
Hilbert adjoint (rather than the Banach transpose). -/
theorem hilbert_right_iff_left_adjoint : AtkinsonCalkinSpec.RightAdjointCharacterization := by
  intro 𝕜 _ H K _ _ _ _ _ _ T
  constructor
  · intro hT
    let : CompleteSpace T.range := hT.1.completeSpace_coe
    let := hT.2
    have hf : FiniteDimensional 𝕜 T.rangeᗮ :=
      T.range.quotientEquivOrthogonal.toLinearEquiv.finiteDimensional
    refine ⟨closed_range_adjoint T hT.1, ?_⟩
    rw [← T.orthogonal_range]
    exact hf
  · intro hT
    have hc : IsClosed (T.range : Set K) := by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using
        closed_range_adjoint T.adjoint hT.1
    let : CompleteSpace T.range := hc.completeSpace_coe
    have hf : FiniteDimensional 𝕜 T.rangeᗮ := by
      rw [T.orthogonal_range]
      exact hT.2
    let := hf
    exact ⟨hc, T.range.quotientEquivOrthogonal.symm.toLinearEquiv.finiteDimensional⟩
end Hilbert
end ExpandedFA.Fredholm
