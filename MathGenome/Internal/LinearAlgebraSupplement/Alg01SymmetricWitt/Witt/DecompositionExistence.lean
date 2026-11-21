import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.HyperbolicSplitting
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Alg01SymmetricWitt.Witt.DecompositionExistence

open Coordinates (hyperbolicPlane hyperbolicSum hyperbolicSum_apply)
open HyperbolicSplitting (hyperbolicSplitting)
open OrthogonalSplitting (orthogonalComplement)

universe u v

section

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

/-- Separate the first hyperbolic coordinate from the remaining coordinates. -/
private def splitHyperbolicSum (r : ℕ) :
    (hyperbolicSum k (r + 1)).IsometryEquiv
      ((hyperbolicPlane k).prod (hyperbolicSum k r)) where
  toLinearEquiv :=
    { (Fin.consEquiv (fun _ : Fin (r + 1) => k × k)).symm with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_app' x := by
    change hyperbolicPlane k (x 0) + hyperbolicSum k r (Fin.tail x) = _
    simp only [Coordinates.hyperbolicPlane_apply, hyperbolicSum_apply, Fin.tail]
    exact (Fin.sum_univ_succ (fun i => (x i).1 * (x i).2)).symm

/-- The zero-fold hyperbolic sum adds no coordinates to the quadratic space. -/
private def zeroHyperbolicSum (q : QuadraticForm k V) :
    ((hyperbolicSum k 0).prod q).IsometryEquiv q where
  toLinearEquiv := LinearEquiv.uniqueProd
  map_app' x := by simp

end

/-- Repeated hyperbolic splitting produces an anisotropic subspace of the original space. -/
theorem wittDecompositionExists {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (q : QuadraticForm k V) (hq : q.Nondegenerate) :
    ∃ (r : ℕ) (A : Submodule k V),
      (q.comp A.subtype).Anisotropic ∧ (q.comp A.subtype).Nondegenerate ∧
      Nonempty (q.IsometryEquiv ((hyperbolicSum k r).prod (q.comp A.subtype))) ∧
      (q.Anisotropic → r = 0) := by
  classical
  generalize hn : Module.finrank k V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hAniso : q.Anisotropic
    · let A : Submodule k V := ⊤
      let i : (q.comp A.subtype).IsometryEquiv q :=
        { Submodule.topEquiv with map_app' := fun _ => rfl }
      have hA : (q.comp A.subtype).Anisotropic := by
        intro x hx
        apply i.injective
        rw [map_zero]
        exact hAniso (i x) ((i.map_app x).trans hx)
      have hANondegenerate : (q.comp A.subtype).Nondegenerate := by
        rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, ← i.symm.map_radical,
          hq.radical_eq_bot, Submodule.map_bot]
      exact ⟨0, A, hA, hANondegenerate, ⟨i.symm.trans (zeroHyperbolicSum _).symm⟩, fun _ => rfl⟩
    · obtain ⟨e, he, heq⟩ := (q.not_anisotropic_iff_exists).mp hAniso
      obtain ⟨f, _, _, _, ⟨i, _⟩, hCompl, ⟨a, _⟩, hW⟩ :=
        hyperbolicSplitting q hq e he heq
      let P := Submodule.span k ({e, f} : Set V)
      let W := orthogonalComplement q P
      have hWProper : W ≠ ⊤ := by
        intro h
        have hinf : P ⊓ W = ⊥ := hCompl.inf_eq_bot
        have hPBot : P = ⊥ := by simpa only [h, inf_top_eq] using hinf
        have heP : e ∈ P := Submodule.subset_span (by simp)
        exact he (by simpa [hPBot] using heP)
      have hDim : Module.finrank k W < n := hn ▸ Submodule.finrank_lt hWProper
      obtain ⟨r, A, hA, hANondegenerate, ⟨b⟩, _⟩ := ih (Module.finrank k W) hDim
        (q.comp W.subtype) hW rfl
      -- View the complement’s anisotropic subspace inside the original space.
      let A' := A.map W.subtype
      let j : ((q.comp W.subtype).comp A.subtype).IsometryEquiv (q.comp A'.subtype) :=
        { A.equivMapOfInjective W.subtype W.subtype_injective with map_app' := fun _ => rfl }
      have hA' : (q.comp A'.subtype).Anisotropic := by
        intro x hx
        apply j.symm.injective
        rw [map_zero]
        exact hA (j.symm x) ((j.symm.map_app x).trans hx)
      have hANondegenerate' : (q.comp A'.subtype).Nondegenerate := by
        rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, ← j.map_radical,
          hANondegenerate.radical_eq_bot, Submodule.map_bot]
      let reassociate : (((hyperbolicPlane k).prod (hyperbolicSum k r)).prod
          (q.comp A'.subtype)).IsometryEquiv
          ((hyperbolicPlane k).prod ((hyperbolicSum k r).prod (q.comp A'.subtype))) :=
        { LinearEquiv.prodAssoc k _ _ _ with map_app' := fun _ => (add_assoc _ _ _).symm }
      let decomposeComplement := b.trans ((QuadraticMap.IsometryEquiv.refl (hyperbolicSum k r)).prod j)
      let split := (splitHyperbolicSum (k := k) r).prod
        (QuadraticMap.IsometryEquiv.refl (q.comp A'.subtype))
      exact ⟨r + 1, A', hA', hANondegenerate',
        ⟨a.symm.trans ((i.symm.prod decomposeComplement).trans (reassociate.symm.trans split.symm))⟩,
        fun h => (hAniso h).elim⟩

end Alg01SymmetricWitt.Witt.DecompositionExistence
