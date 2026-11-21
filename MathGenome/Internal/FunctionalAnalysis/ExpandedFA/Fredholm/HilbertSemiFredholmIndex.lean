import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.HilbertSemiFredholmIndex
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.IndexStability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.ClosedRangeEquivalences

/-!
Residual Hilbert assertions of `fa2:p2:index`.
A closed-range cokernel is the adjoint kernel. For the infinite-defect
stability assertion we use a fixed one-sided parametrix: LT is Fredholm,
so LS stays Fredholm nearby. Such S have closed range and finite kernel.
If one of these S were Fredholm, cancellation would make L, and then T,
Fredholm. Thus infinite deficiency persists. The right case follows by
the continuous Hilbert adjoint. The finite case is the accepted integer
index stability theorem.
-/

noncomputable section
namespace ExpandedFA.Fredholm
open scoped Topology
universe u v w

section Hilbert
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

/-- The actual cokernel, rather than the quotient by the closure of the range. -/
def cokernelEquivAdjointKer (T : H →L[𝕜] K) (hc : IsClosed (T.range : Set K)) :
    (K ⧸ T.range) ≃ₗ[𝕜] T.adjoint.ker := by
  let : CompleteSpace T.range := hc.completeSpace_coe
  rw [← T.orthogonal_range]
  exact T.range.quotientEquivOrthogonal.toLinearEquiv

/-- Closed range and finite defects pass to the Hilbert adjoint. -/
theorem IsFredholm.adjoint {T : H →L[𝕜] K} (hT : IsFredholm T) :
    IsFredholm T.adjoint := by
  have hc := Hilbert.ClosedRangeEquivalences.isClosed_adjoint_range_of_isClosed_range T hT.1
  let := hT.2.1
  let := hT.2.2
  have hk : FiniteDimensional 𝕜 T.adjoint.ker :=
    (cokernelEquivAdjointKer T hT.1).finiteDimensional
  have he := cokernelEquivAdjointKer T.adjoint hc
  rw [ContinuousLinearMap.adjoint_adjoint] at he
  exact ⟨hc, hk, he.symm.finiteDimensional⟩

theorem isFredholm_adjoint_iff : HilbertSemiFredholmIndexSpec.AdjointFredholm.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T
  change IsFredholm T ↔ IsFredholm T.adjoint
  exact ⟨fun h => IsFredholm.adjoint h, fun h => by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using IsFredholm.adjoint h⟩

theorem fredholmIndex_adjoint : HilbertSemiFredholmIndexSpec.AdjointIndex.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T hT hstar
  have h₁ := (cokernelEquivAdjointKer T hT.1).finrank_eq
  have h₂ := (cokernelEquivAdjointKer T.adjoint hstar.1).finrank_eq
  rw [ContinuousLinearMap.adjoint_adjoint] at h₂
  change (Module.finrank 𝕜 T.adjoint.ker : ℤ) -
    (Module.finrank 𝕜 (H ⧸ T.adjoint.range) : ℤ) =
    -((Module.finrank 𝕜 T.ker : ℤ) - (Module.finrank 𝕜 (K ⧸ T.range) : ℤ))
  rw [h₁, h₂]
  ring

/-- A Fredholm product LS forces S to have closed range and finite kernel. -/
theorem isLeftSemiFredholm_of_comp (S : H →L[𝕜] K) (L : K →L[𝕜] H)
    (hLS : IsFredholm (L.comp S)) : IsLeftSemiFredholm S := by
  obtain ⟨R, hR, _⟩ := (atkinson_compact (L.comp S)).mp hLS
  change Compactness.IsCompactLinearMap
    (R.comp (L.comp S) - ContinuousLinearMap.id 𝕜 H).toLinearMap at hR
  apply closed_finite_kernel_of_left_compact S (R.comp L)
  simpa only [ContinuousLinearMap.comp_assoc] using hR

/-- A fixed left parametrix gives a neighborhood preserving the left condition
and whether the cokernel is infinite. -/
theorem IsLeftSemiFredholm.eventually_nhds (T : H →L[𝕜] K)
    (hT : IsLeftSemiFredholm T) :
    ∀ᶠ S in 𝓝 T, IsLeftSemiFredholm S ∧ (IsFredholm S ↔ IsFredholm T) := by
  obtain ⟨L, hL⟩ := (hilbert_left_compact T).mp hT
  have hLT : IsFredholm (L.comp T) := by
    have hneg : Compactness.IsCompactLinearMap
        (ContinuousLinearMap.id 𝕜 H - L.comp T).toLinearMap := by
      simpa only [neg_one_smul, ContinuousLinearMap.toLinearMap_sub, neg_sub] using
        Compactness.compact_smul (-1 : 𝕜) _ hL
    have h := identity_sub_compact_isFredholm _ hneg
    simpa only [sub_sub_cancel] using h
  have hc : Continuous (fun S : H →L[𝕜] K => L.comp S) := by fun_prop
  have hev := (hc.tendsto T).eventually (hLT.to_native.eventually_nhds)
  filter_upwards [hev] with S hLS
  refine ⟨isLeftSemiFredholm_of_comp S L (isFredholm_of_native hLS), ?_⟩
  constructor
  · intro hS
    have hLf : L.IsFredholm := hS.to_native.comp_iff_left.mp hLS
    exact isFredholm_of_native (hLf.comp_iff_right.mp hLT.to_native)
  · intro hTf
    have hLf : L.IsFredholm := hTf.to_native.comp_iff_left.mp hLT.to_native
    exact isFredholm_of_native (hLf.comp_iff_right.mp hLS)

/-- The right condition and infinite nullity are preserved near a right
semi-Fredholm map. -/
theorem IsRightSemiFredholm.eventually_nhds (T : H →L[𝕜] K)
    (hT : IsRightSemiFredholm T) :
    ∀ᶠ S in 𝓝 T, IsRightSemiFredholm S ∧ (IsFredholm S ↔ IsFredholm T) := by
  have hstar : IsLeftSemiFredholm T.adjoint :=
    (hilbert_right_iff_left_adjoint T).mp hT
  have hc : Continuous (fun S : H →L[𝕜] K => S.adjoint) :=
    ContinuousLinearMap.adjoint.continuous
  have hev := (hc.tendsto T).eventually (IsLeftSemiFredholm.eventually_nhds T.adjoint hstar)
  filter_upwards [hev] with S hS
  refine ⟨(hilbert_right_iff_left_adjoint S).mpr hS.1, ?_⟩
  exact (isFredholm_adjoint_iff S).trans (hS.2.trans (isFredholm_adjoint_iff T).symm)

/-- Full local constancy, including the two infinite-defect cases. -/
theorem semiFredholmIndex_eventually_eq :
    HilbertSemiFredholmIndexSpec.SemiFredholmIndexLocallyConstant.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T hT
  change IsSemiFredholm T at hT
  change ∀ᶠ S in 𝓝 T, ∃ hS : IsSemiFredholm S,
    semiFredholmIndex S hS = semiFredholmIndex T hT
  classical
  by_cases hf : IsFredholm T
  · filter_upwards [fredholmIndex_eventually_eq T hf] with S hS
    obtain ⟨hSf, hi⟩ := hS
    have hs : IsSemiFredholm S := Or.inl ⟨hSf.1, hSf.2.1⟩
    refine ⟨hs, ?_⟩
    rw [semiFredholmIndex_of_fredholm S hSf hs,
      semiFredholmIndex_of_fredholm T hf hT, hi]
  · rcases hT with hl | hr
    · filter_upwards [IsLeftSemiFredholm.eventually_nhds T hl] with S hS
      have hnS : ¬ IsFredholm S := fun h => hf (hS.2.mp h)
      have hcT : ¬ FiniteDimensional 𝕜 (K ⧸ T.range) := fun h => hf ⟨hl.1, hl.2, h⟩
      have hcS : ¬ FiniteDimensional 𝕜 (K ⧸ S.range) := fun h => hnS ⟨hS.1.1, hS.1.2, h⟩
      refine ⟨Or.inl hS.1, ?_⟩
      exact (semiFredholmIndex_eq_bot S (Or.inl hS.1) hcS).trans
        (semiFredholmIndex_eq_bot T (Or.inl hl) hcT).symm
    · filter_upwards [IsRightSemiFredholm.eventually_nhds T hr] with S hS
      have hnS : ¬ IsFredholm S := fun h => hf (hS.2.mp h)
      have hkT : ¬ FiniteDimensional 𝕜 T.ker := fun h => hf ⟨hr.1, h, hr.2⟩
      have hkS : ¬ FiniteDimensional 𝕜 S.ker := fun h => hnS ⟨hS.1.1, h, hS.1.2⟩
      refine ⟨Or.inr hS.1, ?_⟩
      exact (semiFredholmIndex_eq_top S (Or.inr hS.1) hkS).trans
        (semiFredholmIndex_eq_top T (Or.inr hr) hkT).symm

end Hilbert
end ExpandedFA.Fredholm
