import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.EquationalCriterion

open scoped TensorProduct

namespace DerivedFormalization.Descent

universe u v w

/-- Finite projectivity descends along a faithfully flat map of commutative rings. -/
theorem finiteProjectiveDescent (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    [AddCommGroup M] [Module A M]
    [Module.Finite B (B ⊗[A] M)] [Module.Projective B (B ⊗[A] M)] :
    Module.Finite A M ∧ Module.Projective A M := by
  have hFinite : Module.Finite A M :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  let fB := f.baseChange B
  have hfB : Function.Surjective fB := LinearMap.lTensor_surjective B hf
  obtain ⟨s, hs⟩ := fB.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hfB)
  have hKerB : Module.Finite B (LinearMap.ker fB) := by
    apply Module.Finite.of_fg
    rw [LinearMap.ker_eq_range_of_comp_eq_id hs]
    exact Submodule.fg_range _
  have hTensorKer : Module.Finite B (B ⊗[A] LinearMap.ker f) := by
    let e : (B ⊗[A] LinearMap.ker f) ≃ₗ[B] LinearMap.ker fB :=
      LinearMap.tensorKerEquiv B B f
    exact Module.Finite.equiv e.symm
  have hKer : Module.Finite A (LinearMap.ker f) :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  have hPresented : Module.FinitePresentation A M :=
    Module.finitePresentation_of_surjective f hf (Module.Finite.iff_fg.mp hKer)
  have hFlat : Module.Flat A M := Module.Flat.of_flat_tensorProduct A M B
  exact ⟨hFinite, Module.Flat.projective_of_finitePresentation⟩

end DerivedFormalization.Descent
