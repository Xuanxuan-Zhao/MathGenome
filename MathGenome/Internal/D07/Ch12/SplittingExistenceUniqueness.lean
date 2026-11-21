import MathGenome.Internal.Specs.D07.Ch12.SplittingExistenceUniqueness
import MathGenome.Internal.D07.Ch12.SplittingDefinition
import MathGenome.Internal.D07.Ch12.DegreeDefinition
import Mathlib.FieldTheory.SplittingField.Construction

/-!
Finite splitting fields, uniqueness, and transport of the base isomorphism.
The library construction recursively adjoins roots of irreducible factors;
it does not use an algebraically closed ambient field. For transport along σ,
give L' the K-action obtained by composing σ with its K'-structure map. The
inverse base isomorphism makes K'/K/L' a compatible tower, so the library's
base-change theorem realizes L' as a splitting field of f over K. Fixed-base
uniqueness then supplies an isomorphism whose scalar identity is precisely
extension of σ. This argument allows constants and inseparable polynomials.
-/

universe u v w z

namespace D07.Ch12.SplittingExistenceUniqueness

open Polynomial Specs.D07.Ch12.SplittingExistenceUniqueness

theorem finiteSplittingField : FiniteSplittingField.{u, v} := by
  intro K L _ _ _ f hf
  let : Polynomial.IsSplittingField K L f :=
    (SplittingDefinition.library_characterization K L f hf.1).mp hf
  let : FiniteDimensional K L := Polynomial.IsSplittingField.finiteDimensional L f
  exact (DegreeDefinition.finite_iff_finiteDimensional K L).mpr inferInstance

theorem finiteExistence : FiniteExistence.{u} := by
  intro K _ f hf
  refine ⟨f.SplittingField, inferInstance, inferInstance, ?_, ?_⟩
  · exact (SplittingDefinition.library_characterization K f.SplittingField f hf).mpr
      inferInstance
  · exact (DegreeDefinition.finite_iff_finiteDimensional K f.SplittingField).mpr
      inferInstance

theorem uniqueness : Uniqueness.{u, v, w} := by
  intro K L E _ _ _ _ _ f hL hE
  let : Polynomial.IsSplittingField K L f :=
    (SplittingDefinition.library_characterization K L f hL.1).mp hL
  let : Polynomial.IsSplittingField K E f :=
    (SplittingDefinition.library_characterization K E f hE.1).mp hE
  exact ⟨(Polynomial.IsSplittingField.algEquiv L f).trans
    (Polynomial.IsSplittingField.algEquiv E f).symm⟩

theorem baseIsomorphismExtension : BaseIsomorphismExtension.{u, v, w, z} := by
  intro K K' L L' _ _ _ _ _ _ σ f hL hL'
  let : Polynomial.IsSplittingField K L f :=
    (SplittingDefinition.library_characterization K L f hL.1).mp hL
  let : Polynomial.IsSplittingField K' L' (f.map σ.toRingHom) :=
    (SplittingDefinition.library_characterization K' L' _ hL'.1).mp hL'
  let : Algebra K L' := ((algebraMap K' L').comp σ.toRingHom).toAlgebra
  let : Algebra K' K := σ.symm.toRingHom.toAlgebra
  let : IsScalarTower K' K L' := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K' L' a = algebraMap K' L' (σ (σ.symm a))
    rw [σ.apply_symm_apply]
  have hmap : (f.map σ.toRingHom).map (algebraMap K' K) = f := by
    change (f.map σ.toRingHom).map σ.symm.toRingHom = f
    rw [Polynomial.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Polynomial.map_id]
  let : Polynomial.IsSplittingField K L' f := by
    rw [← hmap]
    infer_instance
  let e : L ≃ₐ[K] L' := (Polynomial.IsSplittingField.algEquiv L f).trans
    (Polynomial.IsSplittingField.algEquiv L' f).symm
  exact ⟨e.toRingEquiv, fun a => e.commutes a⟩

end D07.Ch12.SplittingExistenceUniqueness
