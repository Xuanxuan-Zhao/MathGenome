import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.DifferentialCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.FiniteProducts
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.FiniteProducts
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.FiniteProducts

/-! ET-17: finite products of étale algebras, including the empty product. -/
namespace AdvCommAlg.Etale

universe u v w

/-- Étaleness of a finite product is equivalent to étaleness of all factors. -/
theorem etale_finite_products :
    Specs.AdvCommAlg.Etale.etaleFiniteProducts.{u,v,w} := by
  intro A ι B _ _ _ _
  obtain ⟨e, _⟩ := Differentials.finite_products A ι B
  constructor
  · intro h i
    obtain ⟨hs, hΩ⟩ := (etale_iff_smooth_and_subsingleton_omega A (∀ i, B i)).mp h
    let := hΩ
    let : Subsingleton (∀ i, KaehlerDifferential A (B i)) :=
      e.symm.injective.subsingleton
    exact (etale_iff_smooth_and_subsingleton_omega A (B i)).mpr
      ⟨(Smooth.smooth_finite_products A ι B).mp hs i,
        (show Function.Surjective
          (fun x : ∀ j, KaehlerDifferential A (B j) => x i) from
          Function.surjective_eval i).subsingleton⟩
  · intro h
    have hs := (Smooth.smooth_finite_products A ι B).mpr
      (fun i => ((etale_iff_smooth_and_subsingleton_omega A (B i)).mp (h i)).1)
    let (i : ι) : Subsingleton (KaehlerDifferential A (B i)) :=
      ((etale_iff_smooth_and_subsingleton_omega A (B i)).mp (h i)).2
    exact (etale_iff_smooth_and_subsingleton_omega A (∀ i, B i)).mpr
      ⟨hs, e.injective.subsingleton⟩

/-- In particular, the empty product is étale. -/
theorem etale_empty_product :
    Specs.AdvCommAlg.Etale.etaleEmptyProduct.{u,v,w} := by
  intro A ι B _ _ _ _
  exact (etale_finite_products A ι B).mpr (fun i => isEmptyElim i)

/-- Every zero algebra is étale over its given base algebra. -/
theorem etale_zero_algebra :
    Specs.AdvCommAlg.Etale.etaleZeroAlgebra.{u,v} := by
  intro A B _ _ _ _
  exact (etale_iff_smooth_and_subsingleton_omega A B).mpr
    ⟨Smooth.smooth_zero_algebra A B,
      KaehlerDifferential.subsingleton_of_surjective A B
        (fun b => ⟨0, Subsingleton.elim _ _⟩)⟩

end AdvCommAlg.Etale
