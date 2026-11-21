import MathGenome.Internal.Specs.D07.Ch20.TracePairingTraceDualReconstruction
import Mathlib.RingTheory.Trace.Basic

/-!
Trace-dual reconstruction, K07.20.trace_pairing (paper.tex:5936–5963).

The only input about separability needed below is that the trace map is
nonzero. Nondegeneracy follows by pairing a nonzero b with z/b, where
Tr(z) ≠ 0. Finite-dimensional duality then gives the linear equivalence.
Transporting the coordinate dual basis through its inverse constructs an
actual basis; the dual-basis identities give uniqueness and reconstruction.
None of these steps uses Tr(1) ≠ 0 or divides by the extension degree.
-/

universe u v w
namespace D07.Ch20.TracePairingTraceDualReconstruction

open Module

noncomputable section

/-- A nonzero field trace already suffices for nondegeneracy, without
assuming separability or imposing a characteristic restriction. -/
theorem trace_pairing_nondegenerate_of_nonzero
    (K : Type*) (L : Type*) [Field K] [Field L] [Algebra K L]
    (h : Algebra.trace K L ≠ 0) : (Algebra.traceForm K L).Nondegenerate := by
  obtain ⟨z, hz⟩ : ∃ z : L, Algebra.trace K L z ≠ 0 := by
    by_contra! hn
    exact h (LinearMap.ext hn)
  constructor
  · intro b hb
    by_contra hbn
    apply hz
    simpa [Algebra.traceForm_apply, ← mul_assoc, hbn] using hb (b⁻¹ * z)
  · intro b hb
    by_contra hbn
    apply hz
    simpa [Algebra.traceForm_apply, mul_assoc, hbn] using hb (z * b⁻¹)

/-- This construction is valid for any finite field extension with nonzero
trace, which is the precise input used in the separable case. -/
theorem trace_linear_equivalence_of_nonzero
    (K : Type*) (L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (h : Algebra.trace K L ≠ 0) :
    ∃ e : L ≃ₗ[K] Module.Dual K L,
      ∀ b x : L, e b x = Algebra.trace K L (b * x) := by
  exact ⟨(Algebra.traceForm K L).toDual
    (trace_pairing_nondegenerate_of_nonzero K L h), fun _ _ => rfl⟩

theorem trace_linear_equivalence :
    Specs.D07.Ch20.TracePairingTraceDualReconstruction.TraceLinearEquivalence.{u,v} := by
  intro K L _ _ _ _ _
  exact trace_linear_equivalence_of_nonzero K L (Algebra.trace_ne_zero K L)

theorem unique_functional_representation :
    Specs.D07.Ch20.TracePairingTraceDualReconstruction.UniqueFunctionalRepresentation.{u,v} := by
  intro K L _ _ _ _ _ f
  obtain ⟨e, he⟩ := trace_linear_equivalence K L
  refine ⟨e.symm f, ?_, ?_⟩
  · intro x
    rw [← he, e.apply_symm_apply]
  · intro b hb
    apply e.injective
    ext x
    rw [e.apply_symm_apply, he, ← hb x]

theorem trace_dual_basis_reconstruction :
    Specs.D07.Ch20.TracePairingTraceDualReconstruction.TraceDualBasisReconstruction.{u,v,w} := by
  intro K L _ _ _ _ _ ι _ _ a
  let B := Algebra.traceForm K L
  have hB : B.Nondegenerate :=
    trace_pairing_nondegenerate_of_nonzero K L (Algebra.trace_ne_zero K L)
  have hsym : B.IsSymm := Algebra.traceForm_isSymm K
  let b := B.dualBasis hB a
  refine ⟨b, ?_, ?_, ?_⟩
  · intro i j
    exact B.apply_dualBasis_right hB hsym a i j
  · intro c hc
    apply Eq.symm
    apply (B.dualBasis_eq_iff hB a c).mpr
    intro i j
    simpa only [B, Algebra.traceForm_apply, mul_comm] using hc j i
  · intro x
    have hrepr (i : ι) : a.repr x i = Algebra.trace K L (x * b i) := by
      have hr := B.dualBasis_repr_apply hB b x i
      rw [show B.dualBasis hB b = a from B.dualBasis_dualBasis hB hsym a] at hr
      exact hr
    calc
      x = ∑ i, a.repr x i • a i := (a.sum_repr x).symm
      _ = ∑ i, Algebra.trace K L (x * b i) • a i := by simp_rw [hrepr]

end
end D07.Ch20.TracePairingTraceDualReconstruction
