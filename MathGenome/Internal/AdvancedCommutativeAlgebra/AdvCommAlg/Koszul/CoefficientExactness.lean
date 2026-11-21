import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.CoefficientExactness
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Construction
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v
namespace AdvCommAlg.Koszul
open CoefficientSequences

theorem exteriorTerms_finiteFree : Specs.AdvCommAlg.Koszul.exteriorTermsFiniteFree.{u} := by
  intro R _ x q
  exact ⟨Module.Free.of_basis (listBasis x q), Module.Finite.of_basis (listBasis x q)⟩

theorem chainCoefficient_shortExact : Specs.AdvCommAlg.Koszul.chainCoefficientShortExact.{u,v} := by
  intro R _ x S hS
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let P := ⋀[R]^n (Fin x.length → R)
  have : Module.Free R P := Module.Free.of_basis (listBasis x n)
  apply ModuleCat.shortComplex_shortExact
  · exact Module.Flat.lTensor_exact (M := P)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
  · exact Module.Flat.lTensor_preserves_injective_linearMap S.f.hom hS.moduleCat_injective_f
  · exact LinearMap.lTensor_surjective P hS.moduleCat_surjective_g

theorem cochainCoefficient_shortExact : Specs.AdvCommAlg.Koszul.cochainCoefficientShortExact.{u,v} := by
  intro R _ x S hS
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let P := ⋀[R]^n (Fin x.length → R)
  have : Module.Projective R P := Module.Projective.of_basis (listBasis x n)
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    change ∀ h : P →ₗ[R] S.X₂, S.g.hom.comp h = 0 →
      ∃ f : P →ₗ[R] S.X₁, S.f.hom.comp f = h
    intro h hh
    have hex := (ShortComplex.moduleCat_exact_iff S).mp hS.exact
    have hp : ∀ i : Set.powersetCard (Fin x.length) n,
        ∃ a : S.X₁, S.f a = h (listBasis x n i) := by
      intro i
      apply hex
      exact DFunLike.congr_fun hh (listBasis x n i)
    choose a ha using hp
    refine ⟨(listBasis x n).constr R a, ?_⟩
    change S.f.hom.comp ((listBasis x n).constr R a) = h
    apply (listBasis x n).ext
    intro i
    simpa using ha i
  · apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (fun f : P →ₗ[R] S.X₁ => S.f.hom.comp f)
    intro f g hfg
    apply LinearMap.ext
    intro a
    apply hS.moduleCat_injective_f
    exact DFunLike.congr_fun hfg a
  · apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective (fun f : P →ₗ[R] S.X₂ => S.g.hom.comp f)
    intro f
    exact Module.projective_lifting_property S.g.hom f hS.moduleCat_surjective_g

/-- The natural homology sequence ... → Hₙ₊₁(N) → Hₙ(L) → Hₙ(M) → Hₙ(N) → ... . -/
theorem chainCoefficient_longExact : Specs.AdvCommAlg.Koszul.chainCoefficientLongExact.{u,v} := by
  intro R _ x S hS
  let h := chainCoefficient_shortExact x S hS
  refine ⟨h, fun n => HomologicalComplex.HomologySequence.composableArrows₅_exact h (n+1) n rfl, ?_⟩
  have := h.epi_g
  apply HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
  intro j hj
  change j+1 = 0 at hj
  exact Nat.noConfusion hj

/-- The natural cohomology sequence 0 → H⁰(L) → H⁰(M) → H⁰(N) → H¹(L) → ... . -/
theorem cochainCoefficient_longExact : Specs.AdvCommAlg.Koszul.cochainCoefficientLongExact.{u,v} := by
  intro R _ x S hS
  let h := cochainCoefficient_shortExact x S hS
  refine ⟨h, fun n => HomologicalComplex.HomologySequence.composableArrows₅_exact h n (n+1) rfl, ?_⟩
  have := h.mono_f
  apply HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
  intro i hi
  change i+1 = 0 at hi
  exact Nat.noConfusion hi

theorem chainConnecting_natural : Specs.AdvCommAlg.Koszul.chainConnectingNatural.{u,v} := by
  intro R _ x S T hS hT φ n
  exact HomologicalComplex.HomologySequence.δ_naturality
    ((coefficientChainFunctor x).mapShortComplex.map φ) hS hT (n+1) n rfl

theorem cochainConnecting_natural : Specs.AdvCommAlg.Koszul.cochainConnectingNatural.{u,v} := by
  intro R _ x S T hS hT φ n
  exact HomologicalComplex.HomologySequence.δ_naturality
    ((coefficientCochainFunctor x).mapShortComplex.map φ) hS hT n (n+1) rfl

/-- Public construction exports, reducing to the independent canonical definitions. -/
def koszulChainCoefficientFunctor := @coefficientChainFunctor.{u,v}
def koszulCochainCoefficientFunctor := @coefficientCochainFunctor.{u,v}

end AdvCommAlg.Koszul
