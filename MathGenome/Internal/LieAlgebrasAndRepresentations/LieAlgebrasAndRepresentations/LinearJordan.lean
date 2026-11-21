import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.LinearJordan
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Polynomial.Tower

open Polynomial Algebra

universe u v w

namespace LieAlgebrasAndRepresentations

variable {k : Type u} [Field k] [CharZero k]
  {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A separable annihilating polynomial stays separable after scalar extension. -/
theorem semisimple_baseChange {K : Type w} [Field K] [Algebra k K]
    {s : Module.End k V} (hs : s.IsSemisimple) : Module.End.IsSemisimple (s.baseChange K) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (minpoly k s).map (algebraMap k K))
  · exact (PerfectField.separable_iff_squarefree.mpr hs.minpoly_squarefree).map.squarefree
  · rw [aeval_map_algebraMap K]
    change aeval ((Module.End.baseChangeHom k K V) s) (minpoly k s) = 0
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]

omit [CharZero k] [FiniteDimensional k V] in
/-- Base extension is faithful also for the zero-dimensional space. -/
theorem end_baseChange_injective {K : Type w} [Field K] [Algebra k K] :
    Function.Injective (fun f : Module.End k V => f.baseChange K) :=
  LinearMap.baseChangeHom_injective k V K

/-- Full uniqueness can be checked over the algebraic closure and then descended. -/
theorem jordan_decomposition_unique {A s₁ n₁ s₂ n₂ : Module.End k V}
    (h₁ : IsJordanDecomposition A s₁ n₁) (h₂ : IsJordanDecomposition A s₂ n₂) :
    s₁ = s₂ ∧ n₁ = n₂ := by
  rcases h₁ with ⟨he₁, hc₁, hs₁, hn₁⟩
  rcases h₂ with ⟨he₂, hc₂, hs₂, hn₂⟩
  let φ := Module.End.baseChangeHom k (AlgebraicClosure k) V
  have h := Module.End.isNilpotent_isSemisimple_unique
    (hn₁.map φ) hs₁ (hn₂.map φ) hs₂ (hc₁.symm.map φ) (hc₂.symm.map φ)
    (show φ n₁ + φ s₁ = φ n₂ + φ s₂ by
      rw [← map_add, ← map_add, add_comm n₁, ← he₁, add_comm n₂, ← he₂])
  exact ⟨end_baseChange_injective h.2, end_baseChange_injective h.1⟩

omit [CharZero k] [FiniteDimensional k V] in
/-- Polynomials in an operator preserve each of its invariant subspaces. -/
theorem polynomial_preserves_subspace (A : Module.End k V) (p : Polynomial k)
    (W : Submodule k V) (hW : ∀ x ∈ W, A x ∈ W) :
    ∀ x ∈ W, (aeval A p) x ∈ W := by
  intro x hx
  exact aeval_apply_smul_mem_of_le_comap hx p A hW

/-- LA-B03: linear Jordan decomposition over the original characteristic-zero field. -/
theorem linear_jordan_decomposition :
    Specs.LieAlgebrasAndRepresentations.LinearJordan.linear_jordan_decomposition_type := by
  intro k _ _ V _ _ _ A
  obtain ⟨n, hn, s, hs, hn_nil, hs_ss, he⟩ := A.exists_isNilpotent_isSemisimple
  have hc : Commute s n :=
    commute_of_mem_adjoin_singleton_of_commute hn (commute_of_mem_adjoin_self hs).symm
  have hdec : IsJordanDecomposition A s n :=
    ⟨he.trans (add_comm n s), hc, semisimple_baseChange hs_ss, hn_nil⟩
  rw [adjoin_singleton_eq_range_aeval] at hs hn
  obtain ⟨p, hp⟩ := hs
  obtain ⟨q, hq⟩ := hn
  refine ⟨s, n, hdec, ⟨p, q, hp, hq⟩, ?_, ?_⟩
  · intro W hW
    constructor
    · rw [← hp]
      exact polynomial_preserves_subspace A p W hW
    · rw [← hq]
      exact polynomial_preserves_subspace A q W hW
  · intro s' n' h'
    exact jordan_decomposition_unique h' hdec

/-- On perfect fields, semisimplicity is the geometric notion in LA-B03. -/
theorem absolutely_semisimple_iff :
    Specs.LieAlgebrasAndRepresentations.LinearJordan.absolutely_semisimple_iff_type := by
  intro k _ _ V _ _ _ s
  refine ⟨fun hs => ?_, semisimple_baseChange⟩
  obtain ⟨n, hnmem, t, htmem, hn, ht, he⟩ := s.exists_isNilpotent_isSemisimple
  have h₁ : IsJordanDecomposition s s 0 := ⟨by simp, Commute.zero_right _, hs, IsNilpotent.zero⟩
  have h₂ : IsJordanDecomposition s t n := by
    refine ⟨he.trans (add_comm n t), ?_, semisimple_baseChange ht, hn⟩
    have hc : Commute n t :=
      commute_of_mem_adjoin_singleton_of_commute htmem
        (commute_of_mem_adjoin_self hnmem).symm
    exact hc.symm
  have hst := (jordan_decomposition_unique h₁ h₂).1
  exact hst ▸ ht

/-- In the algebraic closure the semisimple operator is diagonalizable. -/
theorem absolutely_semisimple_eigenspaces :
    Specs.LieAlgebrasAndRepresentations.LinearJordan.absolutely_semisimple_eigenspaces_type := by
  intro k _ V _ _ _ s hs
  exact hs.iSup_eigenspace_eq_top

end LieAlgebrasAndRepresentations
