import MathGenome.Internal.D07.Ch17.SchurNonscalar
import MathGenome.Internal.Specs.D07.Ch17.SchurScalar

/-! Scalar Schur lemma for an arbitrary group over an algebraically closed field.
We transport Mathlib's scalar endomorphism result from bundled intertwiners to
the concrete centralizer algebra used by the upstream source formalization.
-/
namespace D07.Ch17.SchurScalar

universe u v w
noncomputable section

open Specs.D07.Ch17.SchurScalar

variable {K : Type u} {G : Type v} {V : Type w}
  [Field K] [Group G] [AddCommGroup V] [Module K V]
  [IsAlgClosed K] [FiniteDimensional K V]

/-- Scalar surjectivity in the canonical centralizer model of End_G(V). -/
theorem scalar_map_bijective (ρ : Representation K G V)
    (hρ : Representation.IsIrreducible ρ) :
    Function.Bijective (algebraMap K (SchurNonscalar.endomorphismAlgebra K G V ρ)) := by
  haveI : Representation.IsIrreducible ρ := hρ
  haveI : Nontrivial (SchurNonscalar.endomorphismAlgebra K G V ρ) :=
    (SchurNonscalar.division_algebra K G V ρ hρ).1
  refine ⟨RingHom.injective _, fun T => ?_⟩
  let S : Representation.IntertwiningMap ρ ρ :=
    (T : Module.End K V).intertwiningMap_of_isIntertwiningMap ρ ρ
      ((SchurNonscalar.endomorphism_algebra_characterization K G V ρ T).mp
        T.property).isIntertwining
  obtain ⟨a, ha⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 S
  refine ⟨a, Subtype.ext ?_⟩
  exact congrArg Representation.IntertwiningMap.toLinearMap ha

theorem unique_scalar : UniqueScalar.{u,v,w} := by
  intro K G V _ _ _ _ _ _ ρ hρ T
  obtain ⟨a, ha⟩ := (scalar_map_bijective ρ hρ).2 T
  refine ⟨a, (congrArg Subtype.val ha).symm, ?_⟩
  intro b hb
  apply (scalar_map_bijective ρ hρ).1
  apply Subtype.ext
  exact hb.symm.trans (congrArg Subtype.val ha).symm

theorem scalar_map_isomorphism : ScalarMapIsomorphism.{u,v,w} := by
  intro K G V _ _ _ _ _ _ ρ hρ
  exact ⟨AlgEquiv.ofBijective (Algebra.ofId K _)
    (scalar_map_bijective ρ hρ), rfl⟩

theorem endomorphism_finrank : EndomorphismFinrank.{u,v,w} := by
  intro K G V _ _ _ _ _ _ ρ hρ
  obtain ⟨e, _⟩ := scalar_map_isomorphism K G V ρ hρ
  rw [← e.toLinearEquiv.finrank_eq]
  exact Module.finrank_self K

end
end D07.Ch17.SchurScalar
