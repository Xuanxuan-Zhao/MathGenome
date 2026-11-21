import MathGenome.Internal.Specs.D07.Ch12.SplittingDegreeBound
import MathGenome.Internal.D07.Ch12.SplittingDegreeBoundFactorialInequality
import MathGenome.Internal.D07.Ch14.PolynomialRootAction
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fintype.Perm

/-!
Factorial bounds, K07.12.splitting_degree_bound.
The upstream root-adjunction induction gives the bound without separability.
For separable f, its splitting field is finite Galois; the faithful action on
the n roots embeds its automorphism group in S_n. Lagrange and the Galois
automorphism count give divisibility. When n = 0 the upper bound and positive
field degree give degree one, so this case does not need a nonempty root set.
-/

universe u v

namespace D07.Ch12.SplittingDegreeBound

theorem factorial_bound : Specs.D07.Ch12.SplittingDegreeBound.FactorialBound.{u, v} :=
  SplittingDegreeBoundFactorialInequality.factorial_inequality

theorem factorial_divisibility :
    Specs.D07.Ch12.SplittingDegreeBound.FactorialDivisibility.{u, v} := by
  intro K L _ _ _ f hsplit hsep
  obtain ⟨d, hrank, hle⟩ := factorial_bound K L f hsplit
  obtain ⟨hfinite, hd⟩ := (DegreeDefinition.degree_eq_nat_iff K L d).mp hrank
  let : FiniteDimensional K L := hfinite
  refine ⟨d, hrank, ?_⟩
  by_cases hzero : f.natDegree = 0
  · have hpos : 0 < d := by
      rw [← hd]
      exact (Module.finrank_pos_iff_of_free K L).mpr inferInstance
    have hd1 : d = 1 := by
      simp only [hzero, Nat.factorial_zero] at hle
      omega
    simp [hd1]
  · obtain ⟨_halg, hnormal, hseparable⟩ :=
      Ch14.SplittingCriterion.separableSplittingFieldGalois K L f hsep hsplit
    let : Normal K L := hnormal
    let : Algebra.IsSeparable K L := hseparable
    let : IsGalois K L := ⟨⟩
    obtain ⟨_b, ρ, hρ, _haction⟩ :=
      Ch14.PolynomialRootAction.numberedEmbedding K L f f.natDegree
        (Nat.pos_of_ne_zero hzero) hsep hsplit rfl
    have hdiv := Subgroup.card_dvd_of_injective ρ hρ
    rw [IsGalois.card_aut_eq_finrank K L, hd, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin] at hdiv
    exact hdiv

end D07.Ch12.SplittingDegreeBound
