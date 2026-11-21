import MathGenome.Internal.Specs.D07.Ch20.TracePairing
import MathGenome.Internal.D07.Ch20.TracePairingTraceDualReconstruction
import Mathlib.RingTheory.Trace.Basic

/-!
Nondegenerate trace and trace-dual bases, K07.20.trace_pairing.

Mathlib's nondegeneracy equivalence concerns the multiplication trace,
including the inseparable case. Surjectivity uses the nonzero trace map,
not the value at 1. The accepted reconstruction dependency supplies the
linear equivalence and the unique trace-dual basis. The finite-field
examples below explicitly have zero trace at 1 and nonzero, onto trace.
-/

universe u v w
namespace D07.Ch20.TracePairing

open Specs.D07.Ch20.TracePairing

theorem nondegenerate_iff_separable : NondegenerateIffSeparable.{u,v} := by
  intro K L _ _ _ _
  exact (traceForm_nondegenerate_tfae K L).out 3 1

theorem trace_nonzero : TraceNonzero.{u,v} := by
  intro K L _ _ _ _ _
  exact Algebra.trace_ne_zero K L

theorem trace_surjective : TraceSurjective.{u,v} := by
  intro K L _ _ _ _ _
  exact Algebra.trace_surjective K L

theorem trace_linear_equivalence : TraceLinearEquivalence.{u,v} :=
  TracePairingTraceDualReconstruction.trace_linear_equivalence

theorem unique_functional_representation : UniqueFunctionalRepresentation.{u,v} :=
  TracePairingTraceDualReconstruction.unique_functional_representation

theorem trace_dual_basis_reconstruction : TraceDualBasisReconstruction.{u,v,w} :=
  TracePairingTraceDualReconstruction.trace_dual_basis_reconstruction

theorem finite_field_trace_one_zero : FiniteFieldTraceOneZero.{u,v} := by
  intro p _ K L _ _ _ _ _ _ hcard
  classical
  let : Fintype K := Fintype.ofFinite K
  have hd : Module.finrank K L = p := by
    apply Nat.pow_right_injective (show 1 < Nat.card K by
      simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card (α := K)))
    exact (Module.natCard_eq_pow_finrank (K := K) (V := L)).symm.trans hcard
  refine ⟨hd, inferInstance, ?_, trace_surjective K L, trace_nonzero K L⟩
  simpa only [map_one, hd, nsmul_eq_mul, mul_one, CharP.cast_eq_zero] using
    (Algebra.trace_algebraMap (R := K) (S := L) (1 : K))

theorem prime_field_example : PrimeFieldExample := by
  intro p hp
  have hcard := GaloisField.card p p hp.out.ne_zero
  have h := finite_field_trace_one_zero p (ZMod p) (GaloisField p p) (by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using hcard)
  exact ⟨hcard, h⟩

end D07.Ch20.TracePairing
