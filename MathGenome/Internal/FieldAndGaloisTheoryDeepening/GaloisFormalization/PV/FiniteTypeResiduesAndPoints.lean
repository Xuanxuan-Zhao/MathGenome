import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

namespace GaloisFormalization.PV

universe u v

/-- A field of finite type as an algebra over an infinite field is finite and algebraic. -/
theorem finiteAlgebraicOfFiniteType (F : Type u) (E : Type v) [Field F] [Infinite F]
    [Field E] [Algebra F E] [Algebra.FiniteType F E] :
    Module.Finite F E ∧ Algebra.IsAlgebraic F E := by
  let : Module.Finite F E := finite_of_finite_type_of_isJacobsonRing F E
  exact ⟨inferInstance, inferInstance⟩

/-- The residue field at a maximal ideal of a finite-type algebra is finite over the base. -/
theorem maximalQuotientFinite (F : Type u) (B : Type v) [Field F] [Infinite F]
    [CommRing B] [Nontrivial B] [Algebra F B] [Algebra.FiniteType F B]
    (m : Ideal B) (hm : m.IsMaximal) : Module.Finite F (B ⧸ m) := by
  let := hm
  let := Ideal.Quotient.field m
  exact (finiteAlgebraicOfFiniteType F (B ⧸ m)).1

/-- Every maximal quotient of a finite-type algebra over an algebraically closed field is
isomorphic to the base as an algebra. -/
theorem maximalQuotientAlgEquiv (F : Type u) (B : Type v) [Field F] [IsAlgClosed F]
    [CommRing B] [Nontrivial B] [Algebra F B] [Algebra.FiniteType F B]
    (m : Ideal B) (hm : m.IsMaximal) : Nonempty ((B ⧸ m) ≃ₐ[F] F) := by
  let := hm
  let := Ideal.Quotient.field m
  let := maximalQuotientFinite F B m hm
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId F (B ⧸ m))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F))).symm⟩

/-- Every nonzero finite-type algebra over an algebraically closed field has a rational point. -/
theorem existsAlgHom (F : Type u) (B : Type v) [Field F] [IsAlgClosed F]
    [CommRing B] [Nontrivial B] [Algebra F B] [Algebra.FiniteType F B] :
    Nonempty (B →ₐ[F] F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  obtain ⟨e⟩ := maximalQuotientAlgEquiv F B m hm
  exact ⟨e.toAlgHom.comp (Ideal.Quotient.mkₐ F m)⟩

/-- Every nonzero element of a reduced finite-type algebra survives at a rational point
over an algebraically closed base field. -/
theorem existsAlgHomOfNeZero (F : Type u) (B : Type v) [Field F] [IsAlgClosed F]
    [CommRing B] [Nontrivial B] [Algebra F B] [Algebra.FiniteType F B] [IsReduced B]
    (b : B) (hb : b ≠ 0) : ∃ f : B →ₐ[F] F, f b ≠ 0 := by
  let : Nontrivial (Localization.Away b) := nontrivial_of_ne 1 0 fun h => by
    have heq : algebraMap B (Localization.Away b) 1 = algebraMap B (Localization.Away b) 0 := by
      simpa only [map_one, map_zero] using h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq b heq
    exact hb (IsReduced.eq_zero (x := b) ⟨n, by simpa only [mul_one, mul_zero] using hn⟩)
  obtain ⟨g⟩ := existsAlgHom F (Localization.Away b)
  refine ⟨g.comp (IsScalarTower.toAlgHom F B (Localization.Away b)), ?_⟩
  exact ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b) b).map g).ne_zero

end GaloisFormalization.PV
