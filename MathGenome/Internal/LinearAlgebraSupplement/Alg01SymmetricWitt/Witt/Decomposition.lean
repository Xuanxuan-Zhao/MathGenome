import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.DecompositionExistence
import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.DecompositionUniqueness
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.Decomposition
import Batteries.Tactic.OpenPrivate

namespace Alg01SymmetricWitt.Witt.Decomposition

open Coordinates (hyperbolicSum)
open DecompositionExistence (wittDecompositionExists)
open DecompositionUniqueness (decompositionUnique)

universe u v w

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]

/-- The hyperbolic count of a Witt decomposition of the quadratic form. -/
abbrev IsWittIndex (q : QuadraticForm k V) (r : ℕ) : Prop :=
  Specs.Alg01SymmetricWitt.Witt.Decomposition.IsWittIndex q r

variable [Invertible (2 : k)] [FiniteDimensional k V]

/-- Existence of a Witt decomposition and uniqueness against any anisotropic remainder. -/
theorem wittDecomposition (q : QuadraticForm k V) (hq : q.Nondegenerate) :
    ∃ (r : ℕ) (A : Submodule k V),
      (q.comp A.subtype).Anisotropic ∧ (q.comp A.subtype).Nondegenerate ∧
      q.Equivalent ((hyperbolicSum k r).prod (q.comp A.subtype)) ∧
      ∀ {A' : Type w} [AddCommGroup A'] [Module k A'] [FiniteDimensional k A']
        (qA' : QuadraticForm k A') (s : ℕ), qA'.Anisotropic →
        q.Equivalent ((hyperbolicSum k s).prod qA') →
        r = s ∧ (q.comp A.subtype).Equivalent qA' := by
  obtain ⟨r, A, hA, hA_nd, e, _⟩ := wittDecompositionExists q hq
  exact ⟨r, A, hA, hA_nd, e, fun qA' s hA' e' =>
    decompositionUnique q (q.comp A.subtype) qA' r s hq hA hA' e e'⟩

theorem existsUnique_wittIndex (q : QuadraticForm k V) (hq : q.Nondegenerate) :
    ∃! r, IsWittIndex q r := by
  obtain ⟨r, A, hA, _, e, h_unique⟩ := wittDecomposition q hq
  refine ⟨r, ⟨A, hA, e⟩, ?_⟩
  rintro s ⟨B, hB, f⟩
  exact (h_unique (q.comp B.subtype) s hB f).1.symm

theorem isWittIndex_iff {A : Type w} [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    (q : QuadraticForm k V) (qA : QuadraticForm k A) (r s : ℕ)
    (hq : q.Nondegenerate) (hA : qA.Anisotropic)
    (e : q.Equivalent ((hyperbolicSum k r).prod qA)) :
    IsWittIndex q s ↔ s = r := by
  constructor
  · rintro ⟨B, hB, f⟩
    exact (decompositionUnique q (q.comp B.subtype) qA s r hq hB hA f e).1
  · intro hs
    subst s
    obtain ⟨t, B, hB, _, f, _⟩ := wittDecompositionExists q hq
    have htr := (decompositionUnique q (q.comp B.subtype) qA t r hq hB hA f e).1
    subst t
    exact ⟨B, hB, f⟩

theorem isWittIndex_equivalent {W : Type w} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (q : QuadraticForm k V) (q' : QuadraticForm k W) (r : ℕ)
    (hq : q.Nondegenerate) (hq' : q'.Nondegenerate) (e : q.Equivalent q') :
    IsWittIndex q r ↔ IsWittIndex q' r := by
  constructor
  · rintro ⟨A, hA, f⟩
    exact (isWittIndex_iff q' (q.comp A.subtype) r r hq' hA (e.symm.trans f)).2 rfl
  · rintro ⟨A, hA, f⟩
    exact (isWittIndex_iff q (q'.comp A.subtype) r r hq hA (e.trans f)).2 rfl

open private zeroHyperbolicSum from MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.DecompositionExistence in
theorem isWittIndex_zero_iff (q : QuadraticForm k V) (hq : q.Nondegenerate) :
    IsWittIndex q 0 ↔ q.Anisotropic := by
  constructor
  · rintro ⟨A, hA, ⟨e⟩⟩
    let f := e.trans (zeroHyperbolicSum (q.comp A.subtype))
    intro x hx
    apply f.injective
    rw [map_zero]
    exact hA (f x) ((f.map_app x).trans hx)
  · intro h
    obtain ⟨r, A, hA, _, e, h_zero⟩ := wittDecompositionExists q hq
    exact (h_zero h) ▸ (show IsWittIndex q r from ⟨A, hA, e⟩)

/-- The empty hyperbolic sum is the zero form on a one-element vector space. -/
theorem hyperbolicSumZero (k : Type u) [Field k] :
    Subsingleton (Fin 0 → k × k) ∧ hyperbolicSum k 0 = 0 :=
  ⟨inferInstance, Coordinates.hyperbolicSum_zero⟩

end Alg01SymmetricWitt.Witt.Decomposition
