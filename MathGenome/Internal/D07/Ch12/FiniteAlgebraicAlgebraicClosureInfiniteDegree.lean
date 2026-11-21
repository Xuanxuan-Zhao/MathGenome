import MathGenome.Internal.Specs.D07.Ch12.FiniteAlgebraicAlgebraicClosureInfiniteDegree
import MathGenome.Internal.D07.Ch11.Eisenstein
import MathGenome.Internal.D07.Ch12.AlgebraicClosure
import MathGenome.Internal.D07.Ch12.DegreeDivisibility
import MathGenome.Internal.D07.Ch12.SimpleDegree

/-!
For every m ≥ 1, Eisenstein at 2 proves that X^m - 2 is irreducible over ℚ.
A root therefore has minimal polynomial X^m - 2 and simple degree m.
Closedness supplies such a root inside any given algebraic closure. If that
closure had finite degree d, its degree-(d+1) intermediate field would have
positive degree dividing d, which is impossible. Finally, a single algebraic
generator would generate a finite extension, so the closure cannot be simple.
-/

universe u

namespace D07.Ch12.FiniteAlgebraicAlgebraicClosureInfiniteDegree

open Polynomial
open Specs.D07.Ch12.FiniteAlgebraicAlgebraicClosureInfiniteDegree

theorem root_degree : RootDegree.{u} := by
  intro L _ _ m hm α hα
  have hm0 : m ≠ 0 := Nat.ne_zero_of_lt hm
  have hirr : Irreducible (X ^ m - C (2 : ℚ)) :=
    (Ch11.Eisenstein.xPowSubPrime 2 m (by decide) hm).2
  have hmon : (X ^ m - C (2 : ℚ)).Monic := monic_X_pow_sub_C _ hm0
  have heval : aeval α (X ^ m - C (2 : ℚ)) = 0 := by
    simpa only [map_sub, map_pow, aeval_X, aeval_C, map_ofNat, sub_eq_zero] using hα
  have hmin : minpoly ℚ α = X ^ m - C (2 : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr heval hmon).symm
  have halg : IsAlgebraic ℚ α := ⟨_, hmon.ne_zero, heval⟩
  refine ⟨hmin, ?_⟩
  rw [SimpleDegree.simple_degree ℚ L α halg, hmin, natDegree_X_pow_sub_C]

theorem roots_of_every_degree : RootsOfEveryDegree.{u} := by
  intro Ω _ _ _ m hm
  have hirr : Irreducible (X ^ m - C (2 : ℚ)) :=
    (Ch11.Eisenstein.xPowSubPrime 2 m (by decide) hm).2
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero Ω
    (X ^ m - C (2 : ℚ)) (degree_pos_of_irreducible hirr).ne'
  have hpow : α ^ m = (2 : Ω) := by
    simpa only [map_sub, map_pow, aeval_X, aeval_C, map_ofNat, sub_eq_zero] using hα
  exact ⟨α, hpow, root_degree Ω m hm α hpow⟩

private theorem closed_not_finite (Ω : Type u) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosed Ω] : ¬ FiniteDimensional ℚ Ω := by
  intro hfinite
  let := hfinite
  let d := Module.finrank ℚ Ω
  obtain ⟨α, _, _, hdegree⟩ := roots_of_every_degree Ω (d + 1) (Nat.succ_pos d)
  let E := IntermediateField.adjoin ℚ {α}
  -- Keep the scalar action inherited from Ω when applying the tower theorem.
  let : Algebra ℚ E := E.algebra'
  obtain ⟨hE, _, _, _, hdiv, _⟩ := DegreeDivisibility.intermediate_degrees ℚ E Ω
  let := hE
  have hdim : Module.finrank ℚ E = d + 1 :=
    ((DegreeDefinition.degree_eq_nat_iff ℚ E (d + 1)).mp hdegree).2
  have hpos : 0 < d := Module.finrank_pos
  rw [hdim] at hdiv
  exact Nat.not_succ_le_self d (Nat.le_of_dvd hpos hdiv)

theorem closure_infinite_and_not_simple : ClosureInfiniteAndNotSimple.{u} := by
  intro Ω _ _ _ _
  have hfinite : ¬ ∃ n : ℕ, Module.rank ℚ Ω = (n : Cardinal.{u}) := by
    intro h
    exact closed_not_finite Ω ((DegreeDefinition.finite_iff_finiteDimensional ℚ Ω).mp h)
  refine ⟨inferInstance, hfinite, ?_, ?_⟩
  · exact le_of_not_gt (fun h => hfinite (Cardinal.lt_aleph0.mp h))
  · intro α htop
    have halg : IsAlgebraic ℚ α := Algebra.IsAlgebraic.isAlgebraic α
    obtain ⟨n, hn⟩ := (SimpleDegree.algebraic_iff_finite_simple_extension ℚ Ω α).mp halg
    rw [htop, IntermediateField.rank_top'] at hn
    exact hfinite ⟨n, hn⟩

theorem counterexample_exists : CounterexampleExists := by
  obtain ⟨L, hL, hQ, _, halg, hclosed⟩ := AlgebraicClosure.existence ℚ
  let := hL
  let := hQ
  let := halg
  let := hclosed
  obtain ⟨_, hinfinite, _, hnonsimple⟩ := closure_infinite_and_not_simple L
  exact ⟨L, hL, hQ, hclosed, halg, hinfinite, hnonsimple⟩

end D07.Ch12.FiniteAlgebraicAlgebraicClosureInfiniteDegree
