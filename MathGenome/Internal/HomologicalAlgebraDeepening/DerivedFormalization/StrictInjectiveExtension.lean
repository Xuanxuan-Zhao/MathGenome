import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ModelCategory.Lifting

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open CochainComplex

universe u v

/-- A termwise monic quasi-isomorphism admits strict extensions of cochain maps
into a K-injective complex whose terms are injective. -/
theorem strictInjectiveExtension {R : Type u} [CommRing R] {X J I : Comp.{v} R}
    (i : X ⟶ J) (hi : ∀ n : ℤ, Mono (i.f n)) (hqi : QuasiIso i)
    (hI : IsKInjective I) (hInj : ∀ n : ℤ, Injective (I.X n))
    (f : X ⟶ I) : ∃ g : J ⟶ I, i ≫ g = f := by
  have : Mono i := HomologicalComplex.mono_of_mono_f i hi
  let sq : CommSq f i (0 : I ⟶ (0 : Comp.{v} R)) (0 : J ⟶ (0 : Comp.{v} R)) :=
    ⟨by simp⟩
  let degreewiseLift (n : ℤ) : (sq.map (HomologicalComplex.eval _ _ n)).LiftStruct := by
    haveI : Mono (i.f n) := hi n
    haveI : Injective (I.X n) := hInj n
    exact {
      l := (Injective.factorThru (f.f n) (i.f n) : J.X n ⟶ I.X n)
      fac_left := Injective.comp_factorThru (f.f n) (i.f n)
      fac_right := by simp }
  have hExact : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  have hAcyclic : (cokernel i).Acyclic := hExact.acyclic_X₃ hqi
  -- The obstruction is a degree-one cocycle from the quotient to I.
  let hKernel := KernelFork.IsLimit.ofId (0 : I ⟶ (0 : Comp.{v} R)) rfl
  let obstruction :=
    Lifting.cocycle₁ sq degreewiseLift (hπ := cokernel.condition i) (cokernelIsCokernel i) hKernel
  obtain ⟨correction, hCorrection⟩ :=
    CochainComplex.IsKInjective.eq_δ_of_cocycle obstruction hAcyclic 0 (by simp)
  have : sq.HasLift :=
    Lifting.hasLift sq degreewiseLift (hπ := cokernel.condition i) (cokernelIsCokernel i)
      hKernel correction hCorrection
  exact ⟨sq.lift, sq.fac_left⟩

end DerivedFormalization
