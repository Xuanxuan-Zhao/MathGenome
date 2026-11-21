import MathGenome.Internal.Specs.D05.M07.DualBasis
import MathGenome.Internal.D05.M03.BasisExtension
import MathGenome.Internal.D05.M07.Dual
import MathGenome.Internal.D05.M02.Dimension
import Mathlib.LinearAlgebra.Dual.Basis

/-! K05.07.dual_basis: finite dual bases, coordinates, and dimension. -/

namespace D05.M07.DualBasis

/-- Prescribing a row of the Kronecker delta uniquely specifies a functional.
The existing coordinate maps supply these rows. Equality on the original basis
then proves uniqueness of the whole family. -/
theorem exists_unique_dual_family : Specs.D05.M07.DualBasis.exists_unique_dual_family := by
  intro K V I _ _ _ _ b
  classical
  refine ⟨b.coord, ⟨?_, ?_⟩, ?_⟩
  · intro i
    simp [Module.Basis.coord_apply]
  · intro i j hij
    simp [Module.Basis.coord_apply, hij]
  · rintro φ ⟨hdiag, hoff⟩
    funext i
    apply b.ext
    intro j
    by_cases hij : i = j
    · subst j
      simpa [Module.Basis.coord_apply] using hdiag i
    · simpa [Module.Basis.coord_apply, hij, Ne.symm hij] using hoff i j hij

/-- Mathlib's dual basis is obtained from the same coordinate functionals;
its construction transports the original basis by the coordinate isomorphism. -/
theorem coordinate_family_basis : Specs.D05.M07.DualBasis.coordinate_family_basis := by
  intro K V I _ _ _ _ b
  classical
  exact ⟨b.dualBasis, fun i => congrFun b.coe_dualBasis i⟩

theorem coordinate_apply : Specs.D05.M07.DualBasis.coordinate_apply := by
  intro K V I _ _ _ _ b i x
  exact b.coord_apply i x

theorem coordinate_of_expansion : Specs.D05.M07.DualBasis.coordinate_of_expansion := by
  intro K V I _ _ _ _ b a x hx i
  rw [hx, Module.Basis.coord_apply, b.repr_sum_self]

/-- Agreement on the basis proves spanning, with the coefficients f(b_i). -/
theorem functional_expansion : Specs.D05.M07.DualBasis.functional_expansion := by
  intro K V I _ _ _ _ b f
  exact (b.sum_dual_apply_smul_coord f).symm

/-- Evaluating a relation at each original basis vector extracts its coefficient. -/
theorem dual_relation_coefficients : Specs.D05.M07.DualBasis.dual_relation_coefficients := by
  intro K V I _ _ _ _ b c hc j
  classical
  have hj := congrArg (fun f : Module.Dual K V => f (b j)) hc
  simpa [LinearMap.sum_apply, Module.Basis.coord_apply, Finsupp.single_apply,
    mul_ite] using hj

theorem evaluation_expansion : Specs.D05.M07.DualBasis.evaluation_expansion := by
  intro K V I _ _ _ _ b f x
  have hx := congrArg (fun g : Module.Dual K V => g x) (functional_expansion b f)
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using hx

/-- Count both finite bases using the same index type; no independent finiteness
assumption on the dual is needed. -/
theorem dual_dimension : Specs.D05.M07.DualBasis.dual_dimension := by
  intro K V _ _ _ _
  classical
  let b := Module.finBasis K V
  obtain ⟨d, _⟩ := coordinate_family_basis b
  refine ⟨d.finiteDimensional_of_finite, ?_⟩
  exact (Module.finrank_eq_card_basis d).trans (Module.finrank_eq_card_basis b).symm

/-- With no nonzero inputs, every functional vanishes. The empty basis is
therefore available directly, including without an assumed finite dimension. -/
theorem zero_space_dual : Specs.D05.M07.DualBasis.zero_space_dual := by
  intro K V _ _ _ hzero
  have hf : ∀ f : Module.Dual K V, f = 0 := by
    intro f
    ext x
    rw [hzero x, map_zero, LinearMap.zero_apply]
  let : Subsingleton (Module.Dual K V) :=
    ⟨fun f g => (hf f).trans (hf g).symm⟩
  let d : Module.Basis (Fin 0) K (Module.Dual K V) := Module.Basis.empty _
  exact ⟨hf, ⟨d⟩, by simpa using Module.finrank_eq_card_basis d⟩

end D05.M07.DualBasis
