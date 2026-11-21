import MathGenome.Internal.Specs.D07.Ch16.FreeGenerators
import Mathlib.LinearAlgebra.InvariantBasisNumber

/-! K07.16.free_generators: finite expansions, generation, and finite rank.
The general module statements retain arbitrary associative unital scalar
rings. Only rank invariance specializes to commutative domains. -/

universe u v w z

namespace D07.Ch16.FreeGenerators

open Module Specs.D07.Ch16.FreeGenerators

theorem basisCharacterization : BasisCharacterization.{u, v, w} := by
  intro R _ M _ _ ι e
  classical
  constructor
  · rintro ⟨b, rfl⟩ x
    refine ⟨b.repr x, ?_, ?_⟩
    · exact b.linearCombination_repr x
    · intro c hc
      have hc' : Finsupp.linearCombination R b c = x := hc
      rw [← b.coe_repr_symm] at hc'
      exact b.repr.symm.injective (hc'.trans (b.repr.symm_apply_apply x).symm)
  · intro h
    let f : (ι →₀ R) →ₗ[R] M := Finsupp.linearCombination R e
    have hf : Function.Bijective f := by
      constructor
      · intro c d hcd
        obtain ⟨a, ha, hu⟩ := h (f c)
        exact (hu c rfl).trans (hu d hcd.symm).symm
      · intro x
        obtain ⟨c, hc, _⟩ := h x
        exact ⟨c, hc⟩
    refine ⟨Basis.ofRepr (LinearEquiv.ofBijective f hf).symm, ?_⟩
    ext i
    simp [Basis.coe_ofRepr, f]

theorem freeCharacterization : FreeCharacterization.{u, v} := by
  intro R _ M _ _
  exact Module.free_def R M

theorem finiteGenerationCharacterization : FiniteGenerationCharacterization.{u, v} := by
  intro R _ M _ _
  exact Module.finite_def.trans Submodule.fg_def

/-- Comparing basis coefficients reduces the assertion to cancellation in ℤ. -/
theorem integerFreeTwoTorsion : IntegerFreeTwoTorsion.{v} := by
  intro M _ _ _ x hx
  let b := Module.Free.chooseBasis ℤ M
  apply b.repr.injective
  ext i
  have hi : (2 : ℤ) * b.repr x i = 0 := by
    simpa using congrArg (fun y => b.repr y i) hx
  simpa using (mul_eq_zero.mp hi).resolve_left (by decide : (2 : ℤ) ≠ 0)

theorem cyclicTwoCounterexample : CyclicTwoCounterexample := by
  have hspan : Submodule.span ℤ ({1} : Set (ZMod 2)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    exact Submodule.mem_span_singleton.mpr ⟨z, by simp⟩
  have hfinite : Module.Finite ℤ (ZMod 2) :=
    (finiteGenerationCharacterization ℤ (ZMod 2)).mpr
      ⟨{1}, Set.finite_singleton 1, hspan⟩
  have htwo : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
  refine ⟨hspan, hfinite, one_ne_zero, htwo, ?_⟩
  intro hf
  let := hf
  exact one_ne_zero (integerFreeTwoTorsion (ZMod 2) 1 htwo)

/-- The library invariant-basis-number theorem even applies to all
nontrivial commutative rings; here it is used with the source domain hypotheses. -/
theorem finiteFreeRankInvariant : FiniteFreeRankInvariant.{u} := by
  intro R _ _ m n e
  exact eq_of_fin_equiv R e

theorem finiteBasisCardinality : FiniteBasisCardinality.{u, v, w, z} := by
  intro R _ _ M _ _ ι κ _ _ b c
  exact card_eq_of_linearEquiv R (b.equivFun.symm.trans c.equivFun)

theorem emptyBasis : EmptyBasis.{u, v} := by
  intro R _ M _ _ _
  exact ⟨Basis.empty (R := R) (M := M) (ι := Fin 0)⟩

end D07.Ch16.FreeGenerators
