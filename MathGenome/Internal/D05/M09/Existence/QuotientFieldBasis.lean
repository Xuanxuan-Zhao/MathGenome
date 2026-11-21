import MathGenome.Internal.Specs.D05.M09.Existence.QuotientFieldBasis
import MathGenome.Internal.D05.M08.Evaluation
import MathGenome.Internal.D05.M06.Invariant
import MathGenome.Internal.D05.Foundations.QuotientBasisUnits
import MathGenome.Internal.D05.M02.BasisExtension
import Mathlib.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.Dimension.Free

noncomputable section
namespace D05.M09.Existence.QuotientFieldBasis
open Polynomial
open Specs.D05.M09.Existence.QuotientFieldBasis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Polynomial operators preserve the kernel because their products commute. -/
theorem eval_preserves (T : Module.End K V) (p q : K[X]) :
    ∀ x ∈ Kernel T p, aeval T q x ∈ Kernel T p := by
  intro x hx
  change aeval T p x = 0 at hx
  change aeval T p (aeval T q x) = 0
  calc
    _ = aeval T (p * q) x := congrArg (fun f : Module.End K V => f x) (map_mul (aeval T) p q).symm
    _ = aeval T (q * p) x := by rw [mul_comm p q]
    _ = aeval T q (aeval T p x) := congrArg (fun f : Module.End K V => f x) (map_mul (aeval T) q p)
    _ = 0 := by rw [hx, map_zero]

/-- Evaluation restricted to the actual kernel, before quotienting scalars. -/
def restrictedEvaluation (T : Module.End K V) (p : K[X]) :
    K[X] →ₐ[K] Module.End K (Kernel T p) where
  toFun q := (aeval T q).restrict (eval_preserves T p q)
  map_one' := by ext x; simp
  map_mul' q r := by ext x; simp
  map_zero' := by ext x; simp
  map_add' q r := by ext x; simp
  commutes' a := by ext x; simp

@[simp] theorem restrictedEvaluation_apply (T : Module.End K V) (p q : K[X])
    (w : Kernel T p) : (restrictedEvaluation T p q w : V) = aeval T q (w : V) := rfl

/-- Every multiple of the modulus annihilates W. This is the descent check. -/
theorem restrictedEvaluation_kills (T : Module.End K V) (p : K[X]) :
    ∀ q ∈ Ideal.span ({p} : Set K[X]), restrictedEvaluation T p q = 0 := by
  intro q hq
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
  ext w
  change aeval T (p * r) (w : V) = 0
  rw [mul_comm p r, map_mul]
  change aeval T r (aeval T p (w : V)) = 0
  rw [w.property, map_zero]

/-- A unital algebra homomorphism into the endomorphisms of W. Its existence
establishes the module laws without any nontriviality assumption on W. -/
def quotientRepresentation (T : Module.End K V) (p : K[X]) :
    AdjoinRoot p →ₐ[K] Module.End K (Kernel T p) :=
  Ideal.Quotient.liftₐ _ (restrictedEvaluation T p) (restrictedEvaluation_kills T p)

theorem quotient_module : Specs.D05.M09.Existence.QuotientFieldBasis.quotient_module := by
  intro K V _ _ _ T p
  let m := Module.compHom (Kernel T p) (quotientRepresentation T p).toRingHom
  refine ⟨m, ?_⟩
  intro q w
  rfl

theorem representative_independence :
    Specs.D05.M09.Existence.QuotientFieldBasis.representative_independence := by
  intro K V _ _ _ T p q r h w
  obtain ⟨m, hm⟩ := quotient_module T p
  let := m
  have he : AdjoinRoot.mk p q = AdjoinRoot.mk p r := by
    apply sub_eq_zero.mp
    rw [← map_sub, AdjoinRoot.mk_eq_zero]
    exact h
  rw [← hm q w, ← hm r w, he]

/-- The evaluation formula forces the scalar tower to extend the inherited
K-action; no additional compatibility hypothesis is required. -/
theorem scalarTower (T : Module.End K V) (p : K[X])
    [Module (AdjoinRoot p) (Kernel T p)] (h : ActionAgrees T p) :
    IsScalarTower K (AdjoinRoot p) (Kernel T p) := by
  apply IsScalarTower.of_algebraMap_smul
  intro a w
  apply Subtype.ext
  simpa only [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, aeval_C,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
    Submodule.coe_smul_of_tower] using h (C a) w

theorem spanning_over_quotient :
    Specs.D05.M09.Existence.QuotientFieldBasis.spanning_over_quotient := by
  intro K V _ _ _ T p _ _ h s w hw
  haveI := scalarTower T p h
  apply eq_top_iff.mpr
  intro x _
  have hx : x ∈ Submodule.span K (Set.range w) := by rw [hw]; trivial
  exact Submodule.span_le_restrictScalars K (AdjoinRoot p) (Set.range w) hx

theorem finite_basis_of_spanning :
    Specs.D05.M09.Existence.QuotientFieldBasis.finite_basis_of_spanning := by
  intro K V _ _ _ T p _ _ h s w hw
  have hF := spanning_over_quotient T p h s w hw
  obtain ⟨t, b, _⟩ := D05.M02.BasisExtension.finite_spanning_contains_basis s w hF
  letI := Module.Finite.of_basis b
  exact ⟨inferInstance, Module.finrank (AdjoinRoot p) (Kernel T p),
    ⟨Module.finBasis (AdjoinRoot p) (Kernel T p)⟩⟩

theorem finite_dimensional :
    Specs.D05.M09.Existence.QuotientFieldBasis.finite_dimensional := by
  intro K V _ _ _ _ T p _ _ h
  haveI := scalarTower T p h
  exact Module.Finite.of_restrictScalars_finite K (AdjoinRoot p) (Kernel T p)

theorem expanded_basis : Specs.D05.M09.Existence.QuotientFieldBasis.expanded_basis := by
  intro K V I _ _ _ T p hp _ h b
  haveI := scalarTower T p h
  let a : Module.Basis (Fin p.natDegree) K (AdjoinRoot p) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible p).ne_zero).basis
  refine ⟨a.smulTower' b, ?_⟩
  intro i j
  have hab := a.smulTower'_apply b (i, j)
  rw [hab]
  have ha : a j = AdjoinRoot.mk p (X ^ (j : ℕ)) := by
    rw [map_pow]
    exact (AdjoinRoot.powerBasis (Fact.out : Irreducible p).ne_zero).basis_eq_pow j
  rw [ha, h]
  simp

theorem dimension_formula : Specs.D05.M09.Existence.QuotientFieldBasis.dimension_formula := by
  intro K V _ _ _ _ T p _ _ h
  haveI := scalarTower T p h
  rw [← Module.finrank_mul_finrank K (AdjoinRoot p) (Kernel T p)]
  rw [show Module.finrank K (AdjoinRoot p) = p.natDegree from
    finrank_quotient_span_eq_natDegree]

end D05.M09.Existence.QuotientFieldBasis
