import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.KModelMorphisms
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.BoundedKModels
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
HA-R04. The shared K-model predicates agree with Mathlib's unbounded
null-homotopy classes. Mathlib identifies these with the right and left
orthogonals of the acyclic triangulated subcategory. Its localization lemmas
then prove bijectivity by the two fraction calculi, without bounds or enough
injectives/projectives. Naturality is functoriality of this very localization
map. The quasi-isomorphism lemmas lift the inverse in D to a two-sided inverse
in K; we expose its cochain representative and the two homotopies explicitly.
-/

set_option linter.checkUnivs false
open CategoryTheory

namespace AdvancedHomologicalAlgebra.KModelMorphisms

theorem kInjective_map_bijective :
    Specs.AdvancedHomologicalAlgebra.KModelMorphisms.kInjective_map_bijectiveType := by
  intro A _ _ _ X I hI
  let : I.IsKInjective := (BoundedKModels.kInjective_iff A I).mp hI
  exact CochainComplex.IsKInjective.Qh_map_bijective X I

theorem kProjective_map_bijective :
    Specs.AdvancedHomologicalAlgebra.KModelMorphisms.kProjective_map_bijectiveType := by
  intro A _ _ _ P X hP
  let : P.IsKProjective := (BoundedKModels.kProjective_iff A P).mp hP
  exact CochainComplex.IsKProjective.Qh_map_bijective P X

theorem kInjective_map_natural :
    Specs.AdvancedHomologicalAlgebra.KModelMorphisms.kInjective_map_naturalType := by
  intro A _ _ _ X₁ X₂ I₁ I₂ _ _ a f b
  simp only [Functor.map_comp]

theorem kProjective_map_natural :
    Specs.AdvancedHomologicalAlgebra.KModelMorphisms.kProjective_map_naturalType := by
  intro A _ _ _ P₁ P₂ X₁ X₂ _ _ a f b
  simp only [Functor.map_comp]

theorem kInjective_homotopyInverse :
    Specs.AdvancedHomologicalAlgebra.KModelMorphisms.kInjective_homotopyInverseType := by
  intro A _ _ I J f hI hJ hf
  let : I.IsKInjective := (BoundedKModels.kInjective_iff A I).mp hI
  let : J.IsKInjective := (BoundedKModels.kInjective_iff A J).mp hJ
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f).mp hf
  exact ⟨e.inv, ⟨he ▸ e.homotopyHomInvId⟩, ⟨he ▸ e.homotopyInvHomId⟩⟩

theorem kProjective_homotopyInverse :
    Specs.AdvancedHomologicalAlgebra.KModelMorphisms.kProjective_homotopyInverseType := by
  intro A _ _ P R f hP hR hf
  let : P.IsKProjective := (BoundedKModels.kProjective_iff A P).mp hP
  let : R.IsKProjective := (BoundedKModels.kProjective_iff A R).mp hR
  obtain ⟨e, he⟩ := (CochainComplex.IsKProjective.quasiIso_iff f).mp hf
  exact ⟨e.inv, ⟨he ▸ e.homotopyHomInvId⟩, ⟨he ▸ e.homotopyInvHomId⟩⟩

end AdvancedHomologicalAlgebra.KModelMorphisms
