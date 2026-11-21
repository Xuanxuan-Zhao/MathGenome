import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.FreeModules

noncomputable section

namespace P103.Ch01.FreeModules

open P103.Ch01

universe u v w

theorem standard_basis : Specs.P103.Ch01.FreeModules.standardBasis.{u, v} := by
  intro R X _
  exact ⟨Module.Basis.ofRepr (LinearEquiv.refl R (FreeModule R X)), fun _ => rfl⟩

theorem unique_extension : Specs.P103.Ch01.FreeModules.uniqueExtension.{u, v, w} := by
  intro R X M _ _ _ f
  refine ⟨Finsupp.lift M R X f, ?_, ?_⟩
  · intro x
    simp [freeGenerator]
  · intro L hL
    apply (Finsupp.lift M R X).symm.injective
    funext x
    simpa [freeGenerator] using hL x

theorem extension_formula : Specs.P103.Ch01.FreeModules.extensionFormula.{u, v, w} := by
  intro R X M _ _ _ f L hL c
  have h : L = Finsupp.lift M R X f := by
    apply (Finsupp.lift M R X).symm.injective
    funext x
    simpa [freeGenerator] using hL x
  rw [h]
  rfl

theorem product_inclusion : Specs.P103.Ch01.FreeModules.productInclusion.{u, v} := by
  intro R X _
  refine ⟨fun _ _ h => Finsupp.ext (congrFun h), ?_⟩
  intro g
  constructor
  · rintro ⟨c, rfl⟩
    exact c.hasFiniteSupport
  · intro hg
    exact ⟨Finsupp.ofSupportFinite g hg, rfl⟩

theorem finite_product : Specs.P103.Ch01.FreeModules.finiteProduct.{u, v} := by
  intro R X _ _
  exact ⟨Finsupp.linearEquivFunOnFinite R R X, fun _ => rfl⟩

theorem infinite_product : Specs.P103.Ch01.FreeModules.infiniteProduct.{u, v} := by
  intro R X _ _ _ h
  obtain ⟨c, hc⟩ := h
  have hf := c.hasFiniteSupport
  rw [hc] at hf
  have hs : Function.support (fun _ : X => (1 : R)) = Set.univ := by
    ext x
    simp
  rw [Function.HasFiniteSupport, hs] at hf
  exact Set.infinite_univ hf

theorem boundary_cases : Specs.P103.Ch01.FreeModules.boundaryCases.{u, v} := by
  constructor
  · intro R X _ _ c
    ext x
    exact isEmptyElim x
  · intro R X _ _ c
    ext x
    exact Subsingleton.elim _ _

theorem right_module : Specs.P103.Ch01.FreeModules.rightModule.{u, v, w} := by
  intro R X M _ _ _
  refine ⟨standard_basis Rᵐᵒᵖ X, ?_⟩
  intro f
  obtain ⟨L, hL, huniq⟩ := unique_extension Rᵐᵒᵖ X M f
  refine ⟨L, ⟨hL, ?_⟩, ?_⟩
  · exact extension_formula Rᵐᵒᵖ X M f L hL
  · intro K hK
    exact huniq K hK.1

end P103.Ch01.FreeModules
