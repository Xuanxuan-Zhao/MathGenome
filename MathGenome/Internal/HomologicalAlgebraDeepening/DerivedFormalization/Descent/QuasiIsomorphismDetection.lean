import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.QuasiIsomorphismDetection
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory

universe uA uB v

namespace DerivedFormalization.Descent

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
  (ι : A →+* B)

/-- Flat scalar extension preserves homology, in the actual universe of the
tensor product. -/
theorem extendScalars_preservesHomology_of_flat (hι : ι.Flat) :
    (ModuleCat.extendScalars.{uA, uB, v} ι).PreservesHomology := by
  let : Algebra A B := ι.toAlgebra
  let : Module.Flat A B := hι
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact B (f := S.f.hom) (g := S.g.hom) hS

private theorem extendScalars_reflectsIsomorphisms_of_faithfullyFlat (hι : ι.FaithfullyFlat) :
    (ModuleCat.extendScalars.{uA, uB, v} ι).ReflectsIsomorphisms := by
  let : Algebra A B := ι.toAlgebra
  let : Module.FaithfullyFlat A B := hι
  refine ⟨fun {M N} g hg ↦ ?_⟩
  rw [ConcreteCategory.isIso_iff_bijective] at hg ⊢
  have hTensor : Function.Bijective (g.hom.lTensor B) := hg
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B g.hom).mp hTensor

/-- A cochain map is a quasi-isomorphism if and only if its termwise scalar
extension along a faithfully flat ring map is a quasi-isomorphism. -/
theorem quasiIso_iff_extendScalars (hι : ι.FaithfullyFlat)
    {X Y : CochainComplex (ModuleCat.{v} A) ℤ} (f : X ⟶ Y) :
    QuasiIso f ↔ QuasiIso (((ModuleCat.extendScalars.{uA, uB, v} ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by
  have := extendScalars_preservesHomology_of_flat.{uA, uB, v} ι hι.flat
  have := extendScalars_reflectsIsomorphisms_of_faithfullyFlat.{uA, uB, v} ι hι
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f
    (ModuleCat.extendScalars ι)).symm

end DerivedFormalization.Descent
