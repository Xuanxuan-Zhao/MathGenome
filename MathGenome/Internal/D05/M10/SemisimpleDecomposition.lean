import MathGenome.Internal.Specs.D05.M10.SemisimpleDecomposition
import MathGenome.Internal.D05.M10.Semisimple
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.FieldTheory.Perfect

/-! The semisimple–nilpotent decomposition over the original scalar field.
Mathlib's Jordan–Chevalley theorem constructs both parts in K[T] by finite
Newton iteration. Characteristic zero follows from the given inclusion into
ℂ, so its perfect-field hypotheses introduce no additional assumption.
The upstream bridge identifies Mathlib semisimplicity with the paper's
invariant-complement definition. Uniqueness is among all admissible pairs.
-/

noncomputable section
namespace D05.M10.SemisimpleDecomposition

open Polynomial Algebra

theorem decomposition : Specs.D05.M10.SemisimpleDecomposition.decomposition := by
  intro K V _ _ _ _ ι T
  have : CharZero K := RingHom.charZero ι
  obtain ⟨N, hNT, S, hST, hN, hS, hT⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := T)
  obtain ⟨p, hp⟩ := (Algebra.adjoin_singleton_eq_range_aeval K T ▸ hST)
  obtain ⟨q, hq⟩ := (Algebra.adjoin_singleton_eq_range_aeval K T ▸ hNT)
  have hSN : Commute S N := by
    rw [← hp, ← hq]
    show aeval T p * aeval T q = aeval T q * aeval T p
    rw [← map_mul, ← map_mul, mul_comm p q]
  refine ⟨S, N, ?_, (Semisimple.semisimple_iff_isSemisimple S).mpr hS,
    hN, hSN, ⟨p, hp⟩, ⟨q, hq⟩, ?_⟩
  · exact hT.trans (add_comm N S)
  · intro S' N' hT' hS' hN' hc'
    have hu := Module.End.isNilpotent_isSemisimple_unique hN'
      ((Semisimple.semisimple_iff_isSemisimple S').mp hS')
      hN hS hc'.symm hSN.symm ((add_comm N' S').trans (hT'.symm.trans hT))
    exact ⟨hu.2, hu.1⟩

end D05.M10.SemisimpleDecomposition
