import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.IrreduciblePrimary
import MathGenome.Internal.AlgebraCore.P103.Ch05.NoetherianFiniteness
import MathGenome.Internal.AlgebraCore.P103.Ch05.IrreducibleIntersections
import MathGenome.Internal.AlgebraCore.P103.Ch05.PrimarySubmodules
import Mathlib.RingTheory.Lasker

/-!
Theorem 5.5, primary stages. `InfIrred.isPrimary` is the kernel-stabilization
argument, not an application of primary decomposition: the ascending chain
of inverse images under scalar powers stabilizes, and irreducibility forces
one of the kernel or image terms to vanish in the quotient.
The finite-intersection lemma uses only primary conditions and finite infima.
The colon-ideal identity identifies the library radical with the source's
radical of the quotient annihilator.
-/

namespace P103.Ch05.IrreduciblePrimary

open P103.Specs.Ch05.IrreduciblePrimary
open P103.Specs.Ch05.PrimarySubmodules

open scoped Pointwise

theorem primary_iff_mathlib : primary_iff_mathlibType := by
  intro R _ M _ _ N
  constructor
  · rintro ⟨hproper, h⟩
    refine ⟨hproper, ?_⟩
    intro r x hrx
    by_cases hx : x ∈ N
    · exact Or.inl hx
    · obtain ⟨n, _, hn⟩ := h r x hrx hx
      right
      refine ⟨n, ?_⟩
      apply Submodule.mem_colon_iff_le.mp
      exact Submodule.mem_colon.mpr (fun y _ => hn y)
  · intro h
    refine ⟨h.ne_top, ?_⟩
    intro r x hrx hx
    have hr : r ∈ (N.colon Set.univ).radical := (h.mem_or_mem hrx).resolve_left hx
    obtain ⟨n, hn⟩ := hr
    have hall : ∀ y : M, r ^ n • y ∈ N :=
      fun y => Submodule.mem_colon.mp hn y (Set.mem_univ y)
    refine ⟨n + 1, Nat.le_add_left 1 n, fun y => ?_⟩
    simpa only [pow_succ', mul_smul] using N.smul_mem r (hall y)

theorem irreducible_primary : irreducible_primaryType := by
  intro R _ _ M _ _ _ N hN
  letI : IsNoetherian R M := (NoetherianFiniteness.finite_module R M).1
  exact (primary_iff_mathlib R M N).mpr
    ((IrreducibleIntersections.irreducible_iff_infIrred R M N).mp hN).isPrimary

theorem irreducible_quotient_nilpotent : irreducible_quotient_nilpotentType := by
  intro R _ _ M _ _ _ N hN
  have hp := irreducible_primary R M N hN
  exact ⟨PrimarySubmodules.quotient_nontrivial R M N hp,
    ((PrimarySubmodules.primary_iff_quotient R M N).mp hp).2⟩

theorem finite_intersection_primary : finite_intersection_primaryType := by
  intro R _ M _ _ ι s Q p hs _ hQ
  obtain ⟨i, hi⟩ := hs
  have hrad (j) (hj : j ∈ s) : ((Q j).colon Set.univ).radical = p := by
    simpa only [radicalValue, Submodule.annihilator_quotient] using (hQ j hj).2
  have hp : (s.inf Q).IsPrimary := Submodule.isPrimary_finsetInf hi
    (fun j hj => (primary_iff_mathlib R M (Q j)).mp (hQ j hj).1)
    (fun j hj => (hrad j hj).trans (hrad i hi).symm)
  have heq : (⨅ j ∈ s, Q j) = s.inf Q := (Finset.inf_eq_iInf s Q).symm
  rw [heq]
  refine ⟨(primary_iff_mathlib R M (s.inf Q)).mpr hp, ?_⟩
  change (Module.annihilator R (M ⧸ s.inf Q)).radical = p
  rw [Submodule.annihilator_quotient, Submodule.colon_finsetInf,
    Ideal.radical_finset_inf hi (fun j hj => (hrad j hj).trans (hrad i hi).symm)]
  exact hrad i hi

end P103.Ch05.IrreduciblePrimary
