import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FiniteCodimensionalComplements
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01FiniteDimension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02QuotientMap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02TopologicalSum

/-!
Closed subspaces of finite codimension in real or complex normed spaces.
An algebraic section is continuous because its domain is finite-dimensional
and the closedness assumption makes the distance quotient Hausdorff. Its
range and the original subspace give the two bounded coordinates.
Neither ambient completeness nor Hahn–Banach is used; codimension zero and
the zero ambient space are included in the same construction.
-/

namespace ExpandedFA.P1.FiniteCodimensionalComplements

theorem finite_codimensional_section_and_complement :
    Spec.SectionAndComplement := by
  intro 𝕜 E _ _ _ M hM _
  let : IsClosed (M : Set E) := hM
  -- Split the algebraic quotient, then apply finite-dimensional continuity
  -- in its native distance quotient norm.
  obtain ⟨t, ht⟩ := M.mkQ.exists_rightInverse_of_surjective M.range_mkQ
  let s : (E ⧸ M) →L[𝕜] E := t.toContinuousLinearMap
  have hs : ∀ z, M.mkQ (s z) = z := fun z => LinearMap.congr_fun ht z
  have hleft : Function.LeftInverse M.mkQL s := hs
  have hkerQ : M.mkQL.ker = M := M.ker_mkQ
  have htop : Submodule.IsTopCompl M s.range := by
    simpa only [hkerQ] using
      (s.isTopCompl_range_ker_of_leftInverse M.mkQL hleft).symm
  let : FiniteDimensional 𝕜 s.range :=
    LinearMap.finiteDimensional_range s.toLinearMap
  refine ⟨s, hs, inferInstance,
    C01FiniteDimension.finite_dimensional_subspace_closed 𝕜 E s.range, htop, ?_⟩
  let P := s.comp M.mkQL
  let Q := ContinuousLinearMap.id 𝕜 E - P
  have hP : P.comp P = P := by
    ext x
    exact congrArg s (hs (M.mkQ x))
  have hPker : P.ker = M := by
    ext x
    change s (M.mkQ x) = 0 ↔ x ∈ M
    rw [← s.map_zero, hleft.injective.eq_iff]
    exact Submodule.Quotient.mk_eq_zero M
  have hPrange : P.range = s.range :=
    LinearMap.range_comp_of_range_eq_top s.toLinearMap M.range_mkQ
  have hPid : IsIdempotentElem P := hP
  have hPidLinear : IsIdempotentElem P.toLinearMap :=
    ContinuousLinearMap.IsIdempotentElem.toLinearMap hPid
  have hQ : Q.comp Q = Q := hPid.one_sub
  have hQrange : Q.range = M := by
    calc
      Q.range = P.ker := (LinearMap.IsIdempotentElem.ker_eq_range hPidLinear).symm
      _ = M := hPker
  have hQker : Q.ker = s.range := by
    calc
      Q.ker = P.range := (LinearMap.IsIdempotentElem.range_eq_ker hPidLinear).symm
      _ = s.range := hPrange
  exact ⟨hP, hPker, hPrange, hQ, hQrange, hQker,
    sub_add_cancel _ _, fun x => sub_add_cancel x (P x)⟩

theorem finite_codimensional_complemented :
    Spec.FiniteDimensionalComplement := by
  intro 𝕜 E _ _ _ M hM _
  obtain ⟨s, _, hfinite, hclosed, htop, _⟩ :=
    finite_codimensional_section_and_complement 𝕜 E M hM
  exact ⟨s.range, hfinite, hclosed, htop⟩

end ExpandedFA.P1.FiniteCodimensionalComplements
