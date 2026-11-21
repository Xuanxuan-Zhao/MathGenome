import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.IrreducibleIntersections
import MathGenome.Internal.AlgebraCore.P103.Ch05.NoetherianFiniteness

/-!
Finite irreducible intersections, the first step of Theorem 5.5.
The upstream finiteness result makes M Noetherian, hence its submodule
lattice has well-founded strict reverse order. The library's general
irreducible decomposition theorem uses induction in that order: a reducible
element splits into two larger elements, whose finite decompositions combine.
Thus the argument uses ACC alone, without primary decomposition.
-/

namespace P103.Ch05.IrreducibleIntersections

open P103.Specs.Ch05.IrreducibleIntersections

theorem irreducible_iff_infIrred : irreducible_iff_infIrredType := by
  intro R _ M _ _ N
  constructor
  · rintro ⟨hproper, h⟩
    refine ⟨?_, ?_⟩
    · simpa only [isMax_iff_eq_top] using hproper
    · intro A B hAB
      exact (h A B hAB.symm).imp Eq.symm Eq.symm
  · intro h
    refine ⟨h.ne_top, ?_⟩
    intro A B hAB
    exact (h.2 hAB.symm).imp Eq.symm Eq.symm

theorem finite_intersection : finite_intersectionType := by
  intro R _ _ M _ _ _ N
  classical
  let : IsNoetherian R M := (P103.Ch05.NoetherianFiniteness.finite_module R M).1
  obtain ⟨s, hs, hirred⟩ := exists_infIrred_decomposition N
  have hN : N = ⨅ Q ∈ s, Q := by
    simpa only [Finset.inf_eq_iInf, id_eq] using hs.symm
  refine ⟨s, ?_, hN, ?_⟩
  · intro Q hQ
    exact (irreducible_iff_infIrred R M Q).mpr (hirred hQ)
  · constructor
    · intro hs0
      simpa only [hs0, Finset.notMem_empty, iInf_false, iInf_top] using hN
    · intro htop
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro Q hQ
      have hle : N ≤ Q := hN ▸ iInf_le_of_le Q (iInf_le_of_le hQ le_rfl)
      exact (hirred hQ).ne_top (top_unique (htop ▸ hle))

theorem proper_finite_intersection : proper_finite_intersectionType := by
  intro R _ _ M _ _ _ N hproper
  obtain ⟨s, hirred, hN, hempty⟩ := finite_intersection R M N
  exact ⟨s, Finset.nonempty_iff_ne_empty.mpr (fun hs => hproper (hempty.mp hs)),
    hirred, hN⟩

end P103.Ch05.IrreducibleIntersections
