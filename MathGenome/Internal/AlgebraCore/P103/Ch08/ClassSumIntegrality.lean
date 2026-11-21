import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.ClassSumIntegrality
import MathGenome.Internal.AlgebraCore.P103.Ch08.Schur
import MathGenome.Internal.AlgebraCore.P103.Ch08.CharacterConstructions
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Batteries.Tactic.OpenPrivate

noncomputable section
universe u v
namespace P103.Ch08.ClassSumIntegrality
open scoped MonoidAlgebra Classical
variable {G : Type u} [Group G] [Fintype G]

@[simp] theorem mem_classMembers (D : ConjClasses G) (g : G) :
    g ∈ classMembers D ↔ ConjClasses.mk g = D := by
  classical
  simp [classMembers]

@[simp] theorem classSum_coeff (R : Type*) [CommRing R] (D : ConjClasses G) (g : G) :
    (classSum R D).coeff g = if ConjClasses.mk g = D then 1 else 0 := by
  classical
  simp [classSum, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]

/-- The entire integer group algebra is a finite free lattice, so this proof
can use it instead of restricting multiplication to its central sublattice. -/
theorem classSum_integral_int (D : ConjClasses G) : IsIntegral ℤ (classSum ℤ D) := by
  exact IsIntegral.of_finite ℤ _

theorem classSum_integral_complex (D : ConjClasses G) : IsIntegral ℤ (classSum ℂ D) := by
  have h := (classSum_integral_int D).map
    (MonoidAlgebra.mapAlgHom G (Algebra.ofId ℤ ℂ))
  simpa [classSum, map_sum] using h

/-- Conjugacy invariance of the coefficients makes the class sum central. -/
theorem classSum_commutes_single (R : Type*) [CommRing R]
    (D : ConjClasses G) (h : G) :
    classSum R D * MonoidAlgebra.single h 1 =
      MonoidAlgebra.single h 1 * classSum R D := by
  classical
  ext x
  have hc : ConjClasses.mk (h⁻¹ * x) = ConjClasses.mk (x * h⁻¹) := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    exact isConj_iff.mpr ⟨h, by simp⟩
  simp [hc]

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- The linear action of a central class sum is an intertwiner. -/
def classSumIntertwiner (ρ : Representation ℂ G V) (D : ConjClasses G) :
    ρ.IntertwiningMap ρ where
  toLinearMap := ρ.asAlgebraHom (classSum ℂ D)
  isIntertwining' h := by
    change ρ.asAlgebraHom (classSum ℂ D) * ρ h =
      ρ h * ρ.asAlgebraHom (classSum ℂ D)
    rw [← ρ.asAlgebraHom_single_one h, ← map_mul, ← map_mul,
      classSum_commutes_single]

open private libraryIrreducible from MathGenome.Internal.AlgebraCore.P103.Ch08.Schur

/-- A nonzero vector generates a simple group algebra module. The group
algebra is finite dimensional when the group is finite. -/
theorem finiteDimensional_of_irreducible (ρ : Representation ℂ G V)
    (hρ : Irreducible ℂ G V ρ) : FiniteDimensional ℂ V := by
  have := libraryIrreducible ρ hρ
  have : Module.Finite ℂ[G] ρ.asModule := inferInstance
  have : Module.Finite ℂ ρ.asModule := Module.Finite.trans ℂ[G] ρ.asModule
  exact Module.Finite.equiv ρ.asModuleEquiv

variable [FiniteDimensional ℂ V]

theorem trace_classSum (ρ : Representation ℂ G V) (D : ConjClasses G)
    (g : G) (hg : ConjClasses.mk g = D) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ D)) =
      (classMembers D).card * CharacterSpecs.characterValue ρ g := by
  classical
  have ht (x : G) (hx : x ∈ classMembers D) :
      CharacterSpecs.characterValue ρ x = CharacterSpecs.characterValue ρ g := by
    have hc : IsConj g x := ConjClasses.mk_eq_mk_iff_isConj.mp
      (hg.trans (mem_classMembers D x |>.mp hx).symm)
    obtain ⟨h, rfl⟩ := isConj_iff.mp hc
    exact character_conjugate ρ g h
  calc
    _ = ∑ x ∈ classMembers D, CharacterSpecs.characterValue ρ x := by
      simp [classSum, CharacterSpecs.characterValue]
    _ = ∑ _x ∈ classMembers D, CharacterSpecs.characterValue ρ g := by
      exact Finset.sum_congr rfl ht
    _ = _ := by simp

/-- Schur gives a scalar, and taking the trace identifies it without choosing
an eigenvector or assuming anything about its integrality. -/
theorem classSum_asAlgebraHom (ρ : Representation ℂ G V)
    (hρ : Irreducible ℂ G V ρ) (D : ConjClasses G) (g : G)
    (hg : ConjClasses.mk g = D) :
    ρ.asAlgebraHom (classSum ℂ D) = classScalar ρ D g • LinearMap.id := by
  have : Nontrivial V := hρ.1
  obtain ⟨c, hc, _⟩ := Schur.uniqueScalar ρ hρ (classSumIntertwiner ρ D)
  have he : ρ.asAlgebraHom (classSum ℂ D) = c • LinearMap.id :=
    congrArg Representation.IntertwiningMap.toLinearMap hc
  have hn : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have ht := congrArg (LinearMap.trace ℂ V) he
  rw [trace_classSum ρ D g hg, map_smul, LinearMap.trace_id] at ht
  have hscalar : c = classScalar ρ D g := by
    apply (eq_div_iff hn).mpr
    exact ht.symm
  simpa [hscalar] using he

theorem scalarAction : Specs.scalarActionType := by
  intro G _ _ V _ _ ρ hρ D g hg v
  have := finiteDimensional_of_irreducible ρ hρ
  rw [representationModule_act, classSum_asAlgebraHom ρ hρ D g hg]
  rfl

theorem scalarIntegral : Specs.scalarIntegralType := by
  intro G _ _ V _ _ ρ hρ D g hg
  have := finiteDimensional_of_irreducible ρ hρ
  have : Nontrivial V := hρ.1
  have hi := (classSum_integral_complex D).map ρ.asAlgebraHom
  rw [classSum_asAlgebraHom ρ hρ D g hg] at hi
  change IsIntegral ℤ (algebraMap ℂ (Module.End ℂ V) (classScalar ρ D g)) at hi
  exact (isIntegral_algebraMap_iff (R := ℤ) (A := ℂ) (B := Module.End ℂ V)).mp hi

end P103.Ch08.ClassSumIntegrality
