import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Profinite.Integers
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Profinite.FiniteFieldGalois
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteFields.AbsoluteGaloisGroup

/-! The Krull group of an algebraic closure of a finite field, compared
with the completion of the integers through their common residue model. -/

namespace ALG02GroupTheory.Profinite

open Specs.ALG02GroupTheory.Profinite (FiniteFieldGaloisCompletion)

universe u v

/-- The arithmetic Frobenius corresponds to the canonical image of 1 in
the completion, with each quotient coordinate given by the Frobenius
exponent of the finite-field restriction. -/
theorem finite_field_galois_completion : FiniteFieldGaloisCompletion.{u, v} := by
  intro k Ω _ _ _ _ _
  obtain ⟨coords, hcoords, e, he, _⟩ :=
    AdvancedFieldTheory.AbsoluteGalois.absoluteGaloisGroup k Ω
  obtain ⟨i, hi, hiη⟩ := integer_completion
  refine ⟨e.trans i.symm, ?_, coords, hcoords, ?_⟩
  · change i.symm (e (Specs.AdvancedFieldTheory.globalFrobenius_value k Ω)) = _
    apply i.injective
    rw [i.apply_symm_apply, he.2, hiη]
  · intro σ n x
    have h := hi (i.symm (e σ)) n
    rw [i.apply_symm_apply] at h
    exact (congrArg (fun a : ZMod (n : ℕ) =>
      (coords n (Multiplicative.ofAdd a) x : Ω)) h.symm).trans (he.1 σ n x)

end ALG02GroupTheory.Profinite
