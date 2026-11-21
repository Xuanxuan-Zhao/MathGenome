import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FinitePresentation

/-! Finite presentation, paper.tex 331–355. The proof uses the library kernel
criterion over arbitrary rings. In particular no Noetherian hypothesis is used.
The quotient statement explicitly identifies the source's cokernel definition.
-/

namespace P103.Ch02.FinitePresentation

open P103.Specs.Ch02.FinitePresentation

/-- Finite presentation is equivalent to a finite free cover with finite relations. -/
theorem finite_free_cover_iff : finite_free_cover_iffType := by
  intro R _ M _ _
  constructor
  · intro h
    have := h
    obtain ⟨n, m, f, g, hf, _⟩ := Module.FinitePresentation.exists_fin' R M
    exact ⟨n, f, hf, Module.FinitePresentation.fg_ker f hf⟩
  · rintro ⟨n, f, hf, hk⟩
    exact Module.finitePresentation_of_free_of_surjective f hf hk

/-- A finite free right exact presentation is equivalent to the library predicate. -/
theorem finite_free_presentation_iff : finite_free_presentation_iffType := by
  intro R _ M _ _
  constructor
  · intro h
    have := h
    exact Module.FinitePresentation.exists_fin' R M
  · rintro ⟨n, m, f, g, hf, he⟩
    apply Module.finitePresentation_of_free_of_surjective f hf
    rw [LinearMap.exact_iff.mp he]
    exact Submodule.fg_range g

/-- Cokernels of maps between finite free modules are exactly the finitely
presented modules, with the cokernel realized as the quotient by the image. -/
theorem finite_free_cokernel_iff : finite_free_cokernel_iffType := by
  intro R _ M _ _
  constructor
  · intro h
    obtain ⟨n, m, f, g, hf, he⟩ := (finite_free_presentation_iff R M).mp h
    refine ⟨n, m, g, ⟨?_⟩⟩
    exact (Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp he).symm).trans
      (LinearMap.quotKerEquivOfSurjective f hf)
  · rintro ⟨n, m, g, ⟨e⟩⟩
    have hq : Module.FinitePresentation R ((Fin n → R) ⧸ LinearMap.range g) := by
      apply Module.finitePresentation_of_free_of_surjective (LinearMap.range g).mkQ
        (Submodule.mkQ_surjective _)
      rw [Submodule.ker_mkQ]
      exact Submodule.fg_range g
    have := hq
    exact Module.FinitePresentation.of_equiv e

/-- Every surjective map from a finitely generated module to a finitely
presented one has finitely generated kernel. This includes every finite free cover. -/
theorem kernel_finitely_generated : kernel_finitely_generatedType := by
  intro R _ M _ _ h P _ _ _ f hf
  have := h
  exact Module.FinitePresentation.fg_ker f hf

theorem right_finite_free_cover_iff : right_finite_free_cover_iffType := by
  intro R _ M _ _
  exact finite_free_cover_iff Rᵐᵒᵖ M

theorem right_finite_free_presentation_iff : right_finite_free_presentation_iffType := by
  intro R _ M _ _
  exact finite_free_presentation_iff Rᵐᵒᵖ M

theorem right_finite_free_cokernel_iff : right_finite_free_cokernel_iffType := by
  intro R _ M _ _
  exact finite_free_cokernel_iff Rᵐᵒᵖ M

theorem right_kernel_finitely_generated : right_kernel_finitely_generatedType := by
  intro R _ M _ _
  exact kernel_finitely_generated Rᵐᵒᵖ M

/-- Rank zero and zero targets are included, even over the zero ring. -/
theorem boundary_cases : boundary_casesType := by
  constructor
  · intro R _ M _ _ _
    infer_instance
  · intro R _ M _ _ f
    constructor
    · intro hf
      refine ⟨?_⟩
      intro x y
      obtain ⟨a, rfl⟩ := hf x
      obtain ⟨b, rfl⟩ := hf y
      exact congrArg f (Subsingleton.elim a b)
    · intro h
      have := h
      intro x
      exact ⟨0, Subsingleton.elim _ _⟩

end P103.Ch02.FinitePresentation
