import MathGenome.Internal.Specs.D07.Ch16.PidPrimitiveBasis
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.RingTheory.Ideal.Operations

/-! A primitive vector splits off a free rank-one summand. A finite basis
of the kernel of its Bézout functional completes it to a basis. -/

universe u

namespace D07.Ch16.PidPrimitiveBasis

open Module
open Specs.D07.Ch16.PidPrimitiveBasis

theorem primitiveExtendsToBasis : PrimitiveExtendsToBasis.{u} := by
  intro R _ _ _ n e he
  classical
  have hone : (1 : R) ∈ Ideal.span (Set.range e) := by
    rw [he]
    trivial
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
  let f : (Fin n → R) →ₗ[R] R :=
    ∑ i : Fin n, c i • LinearMap.proj i
  have hfe : f e = 1 := by
    simpa [f] using hc
  obtain ⟨m, ⟨bk⟩⟩ :=
    (LinearMap.ker f).nonempty_basis_of_pid (Pi.basisFun R (Fin n))
  have hind : ∀ (a : R) (x : Fin n → R), x ∈ LinearMap.ker f →
      a • e + x = 0 → a = 0 := by
    intro a x hx hax
    have h := congrArg f hax
    simpa [map_add, map_smul, hfe, LinearMap.mem_ker.mp hx] using h
  have hspan : ∀ x : Fin n → R, ∃ a : R, x + a • e ∈ LinearMap.ker f := by
    intro x
    refine ⟨-f x, ?_⟩
    simp [LinearMap.mem_ker, map_add, map_smul, hfe]
  let b : Basis (Fin (m + 1)) R (Fin n → R) := Basis.mkFinCons e bk hind hspan
  let re : Fin (m + 1) ≃ Fin n := b.indexEquiv (Pi.basisFun R (Fin n))
  refine ⟨b.reindex re, re 0, ?_⟩
  simp [Basis.reindex_apply, b, Basis.coe_mkFinCons]

end D07.Ch16.PidPrimitiveBasis
