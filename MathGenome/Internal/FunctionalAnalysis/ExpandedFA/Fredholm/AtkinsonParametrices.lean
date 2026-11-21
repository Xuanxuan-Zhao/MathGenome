import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.AtkinsonParametrices
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactDefectClosedRange
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.SchauderAdjoints
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.LocallyConvex.HahnBanach

noncomputable section
namespace ExpandedFA.Fredholm
open scoped Topology LinearMap.FiniteRangeSetoid
universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
  {X : Type v} {Y : Type w}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]

/-- The source's closed-range definition implies the native topological
Fredholm definition. Strictness is supplied by the Banach open mapping theorem. -/
theorem IsFredholm.to_native [CompleteSpace X] [CompleteSpace Y]
    {T : X →L[𝕜] Y} (h : IsFredholm T) : T.IsFredholm := by
  let : IsClosed (T.range : Set Y) := h.1
  let : CompleteSpace T.range := h.1.completeSpace_coe
  let : FiniteDimensional 𝕜 T.ker := h.2.1
  let : FiniteDimensional 𝕜 (Y ⧸ T.range) := h.2.2
  refine ⟨?_, h.1, h.2.1, inferInstance,
    Submodule.ClosedComplemented.of_finiteDimensional T.ker⟩
  exact T.rangeRestrict.isQuotientMap (fun y => by
    obtain ⟨x, hx⟩ := y.property
    exact ⟨x, Subtype.ext hx⟩)

/-- Conversely the native definition explicitly contains the three source conditions. -/
theorem isFredholm_of_native {T : X →L[𝕜] Y} (h : T.IsFredholm) :
    IsFredholm T := by
  let := h.finite_coker
  exact ⟨h.isClosed_range, h.finite_ker, inferInstance⟩

/-- Finite-dimensional continuous dual forces finite-dimensional original space,
by the injective canonical map into its continuous bidual (Hahn--Banach). -/
theorem finiteDimensional_of_finiteDimensional_strongDual
    [FiniteDimensional 𝕜 (StrongDual 𝕜 X)] : FiniteDimensional 𝕜 X :=
  FiniteDimensional.of_injective (V₂ := StrongDual 𝕜 (StrongDual 𝕜 X)) (NormedSpace.inclusionInDoubleDualLi (E := X) 𝕜).toLinearMap
    (NormedSpace.inclusionInDoubleDualLi (E := X) 𝕜).injective

/-- The actual continuous dual of the closed cokernel embeds in the kernel
of the transpose. This never uses the algebraic dual of a non-Hausdorff quotient. -/
theorem finiteDimensional_cokernel_of_transpose_kernel
    (T : X →L[𝕜] Y) (hclosed : IsClosed (T.range : Set Y))
    [FiniteDimensional 𝕜
      (P1.C04Annihilators.banachTranspose 𝕜 X Y T).ker] :
    FiniteDimensional 𝕜 (Y ⧸ T.range) := by
  let : IsClosed (T.range : Set Y) := hclosed
  let j : StrongDual 𝕜 (Y ⧸ T.range) →ₗ[𝕜]
      (P1.C04Annihilators.banachTranspose 𝕜 X Y T).ker :=
    { toFun := fun f => ⟨f.comp T.range.mkQL, by
        apply ContinuousLinearMap.ext
        intro x
        change f (Submodule.Quotient.mk (T x)) = 0
        have hz : (Submodule.Quotient.mk (T x) : Y ⧸ T.range) = 0 :=
          (Submodule.Quotient.mk_eq_zero T.range).mpr ⟨x, rfl⟩
        exact hz ▸ f.map_zero⟩
      map_add' := by intro f g; rfl
      map_smul' := by intro a f; rfl }
  have hj : Function.Injective j := by
    intro f g hfg
    apply ContinuousLinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := T.range.mkQ_surjective z
    exact congrArg (fun f => (f.val : StrongDual 𝕜 Y) y) hfg
  let : FiniteDimensional 𝕜 (StrongDual 𝕜 (Y ⧸ T.range)) :=
    FiniteDimensional.of_injective
      (V₂ := (P1.C04Annihilators.banachTranspose 𝕜 X Y T).ker) j hj
  exact finiteDimensional_of_finiteDimensional_strongDual

/-- Identity minus compact is Fredholm. Closed range is proved upstream;
the cokernel is handled through its continuous dual and Schauder's theorem. -/
theorem identity_sub_compact_isFredholm
    (K : X →L[𝕜] X) (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    IsFredholm (ContinuousLinearMap.id 𝕜 X - K) := by
  let A := ContinuousLinearMap.id 𝕜 X - K
  let K' := P1.C04Annihilators.banachTranspose 𝕜 X X K
  have hK' := Compactness.SchauderAdjoints.compact_banachTranspose 𝕜 X X K hK
  have hker := identity_sub_compact_kernel_closed_finite_dimensional K hK
  have hclosed := identity_sub_compact_closed_range K hK
  have hdual := identity_sub_compact_kernel_closed_finite_dimensional K' hK'
  have heq : P1.C04Annihilators.banachTranspose 𝕜 X X A =
      ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X) - K' := by
    ext f x
    change f (x - K x) = f x - f (K x)
    exact map_sub f x (K x)
  have hd : FiniteDimensional 𝕜
      (P1.C04Annihilators.banachTranspose 𝕜 X X A).ker := by
    rw [heq]
    exact hdual.2
  let := hd
  exact ⟨hclosed, hker.2, finiteDimensional_cokernel_of_transpose_kernel A hclosed⟩


/-- A continuous finite-rank map is compact in the original codomain. -/
theorem compact_of_finiteDimensional_range (T : X →L[𝕜] Y)
    [FiniteDimensional 𝕜 T.range] : Compactness.IsCompactLinearMap T.toLinearMap := by
  have hc : IsCompactOperator T.rangeRestrict :=
    isCompactOperator_of_locallyCompactSpace_dom T.rangeRestrict
  have h := hc.clm_comp T.range.subtypeL
  exact (Compactness.compact_iff_isCompactOperator _).mpr h

/-- Both Fredholm products suffice. The two finite-rank quasi-inverses
are combined in the quotient of linear maps by finite-rank maps. -/
theorem isFredholm_of_fredholm_products
    (T : X →L[𝕜] Y) (S : Y →L[𝕜] X)
    (hST : (S.comp T).IsFredholm) (hTS : (T.comp S).IsFredholm) :
    T.IsFredholm := by
  obtain ⟨A, hA⟩ := hST.exists_isQuasiInverse
  obtain ⟨B, hB⟩ := hTS.exists_isQuasiInverse
  let U := A.comp S
  let V := S.comp B
  have hleft : U.toLinearMap.IsLeftQuasiInverse T.toLinearMap := hA.1
  have hright : V.toLinearMap.IsRightQuasiInverse T.toLinearMap := hB.2
  have hUV : U.toLinearMap ≈ V.toLinearMap := by
    calc
      U.toLinearMap = U.toLinearMap.comp LinearMap.id := by simp
      _ ≈ U.toLinearMap.comp (T.toLinearMap.comp V.toLinearMap) :=
        LinearMap.FiniteRangeSetoid.equiv_comp_left (Setoid.symm hright.equiv)
      _ = (U.toLinearMap.comp T.toLinearMap).comp V.toLinearMap := rfl
      _ ≈ LinearMap.id.comp V.toLinearMap := LinearMap.FiniteRangeSetoid.equiv_comp_right hleft.equiv
      _ = V.toLinearMap := by simp
  have hrightU : U.toLinearMap.IsRightQuasiInverse T.toLinearMap :=
    hright.congr hUV (Setoid.refl _)
  exact ContinuousLinearMap.IsFredholm.of_isQuasiInverse ⟨hleft, hrightU⟩

/-- Fredholmness supplies one bounded map with both finite-rank defects. -/
theorem finite_rank_parametrix_of_isFredholm [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[𝕜] Y) (hT : IsFredholm T) :
    ∃ S : Y →L[𝕜] X,
      FiniteDimensional 𝕜 (S.comp T - ContinuousLinearMap.id 𝕜 X).range ∧
      FiniteDimensional 𝕜 (T.comp S - ContinuousLinearMap.id 𝕜 Y).range := by
  obtain ⟨S, hS⟩ := hT.to_native.exists_isQuasiInverse
  have hleft := LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hS.1.equiv
  have hright := LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hS.2.equiv
  refine ⟨S, Module.Finite.of_fg ?_, Module.Finite.of_fg ?_⟩
  · simpa only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.coe_id, LinearMap.HasFiniteRange] using hleft.hasFiniteRange
  · simpa only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.coe_id, LinearMap.HasFiniteRange] using hright.hasFiniteRange

/-- Reverse Atkinson implication: neither closed range nor finite cokernel
is assumed. Both follow by reducing the two products to identity minus compact. -/
theorem isFredholm_of_compact_parametrix [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[𝕜] Y) (S : Y →L[𝕜] X)
    (hST : Compactness.IsCompactLinearMap
      (S.comp T - ContinuousLinearMap.id 𝕜 X).toLinearMap)
    (hTS : Compactness.IsCompactLinearMap
      (T.comp S - ContinuousLinearMap.id 𝕜 Y).toLinearMap) : IsFredholm T := by
  have hnegST : Compactness.IsCompactLinearMap
      (ContinuousLinearMap.id 𝕜 X - S.comp T).toLinearMap := by
    simpa only [neg_one_smul, ContinuousLinearMap.toLinearMap_sub, neg_sub] using
      Compactness.compact_smul (-1 : 𝕜) _ hST
  have hnegTS : Compactness.IsCompactLinearMap
      (ContinuousLinearMap.id 𝕜 Y - T.comp S).toLinearMap := by
    simpa only [neg_one_smul, ContinuousLinearMap.toLinearMap_sub, neg_sub] using
      Compactness.compact_smul (-1 : 𝕜) _ hTS
  have h1 := identity_sub_compact_isFredholm _ hnegST
  have h2 := identity_sub_compact_isFredholm _ hnegTS
  rw [sub_sub_cancel] at h1 h2
  exact isFredholm_of_native (isFredholm_of_fredholm_products T S h1.to_native h2.to_native)

/-- Atkinson's theorem with compact defects. -/
theorem atkinson_compact_parametrix :
    AtkinsonParametricesSpec.CompactParametrixCharacterization := by
  intro 𝕜 _ X Y _ _ _ _ _ _ T
  constructor
  · intro hT
    obtain ⟨S, h1, h2⟩ := finite_rank_parametrix_of_isFredholm T hT
    let := h1
    let := h2
    exact ⟨S, compact_of_finiteDimensional_range _, compact_of_finiteDimensional_range _⟩
  · rintro ⟨S, h1, h2⟩
    exact isFredholm_of_compact_parametrix T S h1 h2

/-- The equivalent finite-rank formulation, using the same bounded
parametrix for its two defects. -/
theorem atkinson_finite_rank_parametrix :
    AtkinsonParametricesSpec.FiniteRankParametrixCharacterization := by
  intro 𝕜 _ X Y _ _ _ _ _ _ T
  constructor
  · exact finite_rank_parametrix_of_isFredholm T
  · rintro ⟨S, h1, h2⟩
    let := h1
    let := h2
    exact isFredholm_of_compact_parametrix T S
      (compact_of_finiteDimensional_range _) (compact_of_finiteDimensional_range _)

end ExpandedFA.Fredholm
