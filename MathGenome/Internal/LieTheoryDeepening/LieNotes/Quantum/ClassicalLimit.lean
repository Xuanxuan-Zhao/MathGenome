import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.Completion
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.MatrixSpecialization
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.ClassicalLimit

noncomputable section

open Specs.LieNotes.Quantum
open scoped TensorProduct Specs.LieNotes.Quantum.ClassicalLimit

namespace LieNotes.Quantum.ClassicalLimit

open Specs.LieNotes.Quantum.ClassicalLimit
open Specs.LieNotes.Quantum.Completion (AtLevel Level Limit TensorPower project)

universe u

section Reduction

variable {k : Type u} [Field k] [CharZero k]

/-- Regard the first projection as a map over the constant scalars. -/
private def firstProjection (p : TensorPower) : Limit k p →ₐ[k] AtLevel k p firstLevel :=
  { (project k p firstLevel).toRingHom with
    commutes' := fun a =>
      ((project k p firstLevel).commutes (PowerSeries.C a)).trans
        (congrArg (algebraMap (Completion.A k firstLevel) (AtLevel k p firstLevel))
          ((Truncations.truncate (R := k) firstLevel).commutes a)) }

private theorem parameterIdeal_eq_ker (h : Completion.ReductionProp.{u}) (p : TensorPower) :
    parameterIdeal k p = RingHom.ker (firstProjection (k := k) p) := by
  ext x
  rw [RingHom.mem_ker]
  change x ∈ parameterIdeal k p ↔ project k p firstLevel x = 0
  have hx := ((h k p).2.1 firstLevel).2 x
  rw [hx, parameterIdeal, Ideal.mem_span_singleton']
  change (∃ y, y * algebraMap (PowerSeries k) (Limit k p) PowerSeries.X = x) ↔
    ∃ y, (PowerSeries.X : PowerSeries k) ^ 1 • y = x
  simp only [pow_one, Algebra.smul_def, Algebra.commutes (A := Limit k p)]

private theorem exists_levelEquivs (h : Completion.ReductionProp.{u}) :
    ∃ r : ∀ p : TensorPower, ModParameter k p ≃ₐ[k] AtLevel k p firstLevel,
      ∀ p (x : Limit k p), r p (modParameter k p x) = project k p firstLevel x := by
  have hs (p : TensorPower) : Function.Surjective (firstProjection (k := k) p) :=
    ((h k p).2.1 firstLevel).1
  refine ⟨fun p => (Ideal.quotientEquivAlgOfEq k (parameterIdeal_eq_ker h p)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (hs p)), ?_⟩
  intro p x
  change (Ideal.quotientKerAlgEquivOfSurjective (hs p))
    (Ideal.quotientEquivAlgOfEq k (parameterIdeal_eq_ker h p)
      (Ideal.Quotient.mk (parameterIdeal k p) x)) = firstProjection p x
  rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

end Reduction

section GeneratorImages

variable {k : Type u} [Field k] [CharZero k] {D : Completion.HopfMaps k}

theorem equiv_modParameter (r : ClassicalReduction D) (x : Completion.Uh k) :
    r.equiv (modParameter k .single x) = r.comparison (project k .single firstLevel x) :=
  congrArg r.comparison (r.levelEquiv_mk .single x)

theorem equiv_formalE (r : ClassicalReduction D) (i : Presentation.Root) :
    r.equiv (modParameter k .single (formalE k i)) =
      UniversalEnvelopingAlgebra.ι k (MatrixSpecialization.matrixE k i) :=
  (equiv_modParameter r _).trans (r.generators.map_E i)

theorem equiv_formalF (r : ClassicalReduction D) (i : Presentation.Root) :
    r.equiv (modParameter k .single (formalF k i)) =
      UniversalEnvelopingAlgebra.ι k (MatrixSpecialization.matrixF k i) :=
  (equiv_modParameter r _).trans (r.generators.map_F i)

theorem equiv_formalH (r : ClassicalReduction D) (i : Presentation.Root) :
    r.equiv (modParameter k .single (formalH k i)) =
      UniversalEnvelopingAlgebra.ι k (MatrixSpecialization.matrixH k i) :=
  (equiv_modParameter r _).trans (r.generators.map_H i)

end GeneratorImages

private theorem coefficientEquiv_truncate {k : Type u} [Field k] (f : PowerSeries k) :
    MatrixSpecialization.coefficientEquiv k (Truncations.truncate 1 f) =
      PowerSeries.constantCoeff f := by
  change MatrixSpecialization.coefficientEquiv k (Truncations.mk k 1 (PowerSeries.trunc 1 f)) = _
  rw [PowerSeries.trunc_one_left, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact (MatrixSpecialization.coefficientEquiv k).commutes (PowerSeries.constantCoeff f)

/-- Reduce the completed Hopf structure at level one and identify its reduction
with the enveloping Hopf algebra of the traceless three-by-three matrices. -/
theorem classical_limit : ClassicalLimitProp.{u} := by
  refine ⟨Completion.series_description, Completion.reduction, Completion.topological_algebras, ?_⟩
  intro k _ _
  refine ⟨fun p => Completion.series_coefficients k (Completion.Index p), ?_⟩
  obtain ⟨d, s, D, projects, identities, continuous⟩ := Completion.completed_hopf k
  obtain ⟨r, hr⟩ := exists_levelEquivs (k := k) Completion.reduction
  obtain ⟨e, images, _, c, preserves⟩ := MatrixSpecialization.specialization k
  obtain ⟨t, ht, intertwines⟩ := preserves (d firstLevel) (s firstLevel)
  refine ⟨d, s, D, projects, identities, continuous, ⟨
    { levelEquiv := r
      levelEquiv_mk := hr
      comparison := e
      generators := images
      hopf := c
      tensorComparison := t
      tensorComparison_tmul := ht
      comul := ?_
      counit := ?_
      antipode := ?_ }⟩⟩
  · intro x
    rw [hr, hr, projects.comul]
    exact (intertwines (project k .single firstLevel x)).1
  · intro x
    rw [hr]
    have hc : Truncations.truncate 1 (D.counit x) =
        (d firstLevel).counit (project k .single firstLevel x) := projects.counit firstLevel x
    calc
      PowerSeries.constantCoeff (D.counit x) =
        MatrixSpecialization.coefficientEquiv k (Truncations.truncate 1 (D.counit x)) :=
          (coefficientEquiv_truncate (D.counit x)).symm
      _ = MatrixSpecialization.coefficientEquiv k
          ((d firstLevel).counit (project k .single firstLevel x)) :=
            congrArg (MatrixSpecialization.coefficientEquiv k) hc
      _ = _ := (intertwines (project k .single firstLevel x)).2.1
  · intro x
    rw [hr, hr, projects.antipode]
    exact (intertwines (project k .single firstLevel x)).2.2

end LieNotes.Quantum.ClassicalLimit
