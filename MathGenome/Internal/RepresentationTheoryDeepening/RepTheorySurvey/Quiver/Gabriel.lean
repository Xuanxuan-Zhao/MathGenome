import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.Gabriel
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.DynkinClassification
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.EulerExt
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.IndecomposableVectors
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.InfiniteRepresentationType
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.PositiveRoots

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

universe u v w d

namespace RepTheorySurvey.Quiver.Gabriel

open FormsSpec DynkinClassificationSpec PositiveRootsSpec PathResolutionSpec
open scoped EulerExtSpec

/-- The linear path-module equivalence transports the endomorphism
algebra by mapping each endomorphism. -/
private noncomputable def pathModuleEndEquiv {k : Type w} {Q : Type u}
    [Field k] [Quiver.{v} Q] [Fintype Q]
    (V : RM03.QuiverRepresentation.{u, v, w, d} k Q) :
    End V ≃ₐ[k] End (Target V) := by
  let F := RM03.QuiverModuleEquivalence.inverse.{u, v, w, d} k Q
  letI : F.IsEquivalence := (RM03.QuiverModuleEquivalence.equivalence k Q).isEquivalence_inverse
  letI : F.Additive := RM03.QuiverModuleEquivalence.inverseAdditive
  letI : F.Linear k := RM03.QuiverModuleEquivalence.inverseLinear
  let e := (Functor.FullyFaithful.ofFullyFaithful F).mulEquivEnd V
  refine { e with map_add' := ?_, commutes' := ?_ }
  · intro f g
    apply End.ext
    exact F.map_add
  · intro a
    simp only [Algebra.algebraMap_eq_smul_one]
    apply End.ext
    change F.map (a • 𝟙 V) = a • 𝟙 (F.obj V)
    rw [F.map_smul, F.map_id]

theorem gabrielsTheorem : GabrielSpec.GabrielsTheorem.{u, v, w, d} := by
  intro k Q _ _ _ _ _ hacyclic
  have hDynkin := DynkinClassification.positiveDefiniteIffDynkin hacyclic
  constructor
  · constructor
    · intro hfinite
      apply hDynkin.mp
      by_contra hnot
      have hinfinite : Infinite (IndecomposableClass.{u, v, w, max w d} k Q) :=
        InfiniteRepresentationType.infinite_indecomposableClasses.{u, v, w, d} k hacyclic hnot
      exact (not_finite_iff_infinite.mpr hinfinite) hfinite
    · intro hgraph
      have hpos := hDynkin.mpr hgraph
      obtain ⟨e, _⟩ :=
        IndecomposableVectors.dimensionVector_bijection.{u, v, w, d} k Q hacyclic hpos
      have : Finite ↥(positiveRoots Q) :=
        ((PositiveRoots.finite_roots hacyclic hpos).subset (fun _ h => h.1)).to_subtype
      have hroots := PositiveRoots.positiveRoots_characterization hacyclic hpos
      exact Finite.of_equiv ↥(positiveRoots Q) ((Set.equivOfEq hroots).trans e.symm)
  · intro hgraph
    have hpos := hDynkin.mpr hgraph
    have hroots := PositiveRoots.positiveRoots_characterization hacyclic hpos
    obtain ⟨e, he⟩ :=
      IndecomposableVectors.dimensionVector_bijection.{u, v, w, d} k Q hacyclic hpos
    refine ⟨hroots, ⟨e.trans (Set.equivOfEq hroots.symm), he⟩, ?_⟩
    intro V
    obtain ⟨a⟩ :=
      IndecomposableVectors.endomorphismAlgebra.{u, v, w, d} k Q hacyclic hpos V
    let a' : End (Target V.val.obj) ≃ₐ[k] k :=
      (pathModuleEndEquiv V.val.obj).symm.trans a
    have hHom : Module.finrank k (Target V.val.obj ⟶ Target V.val.obj) = 1 := by
      simpa only [Module.finrank_self] using
        (End.linearEquiv (R := k)).symm.trans a'.toLinearEquiv |>.finrank_eq
    have hq : titsForm (dimensionVector V.val) = 1 := by
      rw [← he V]
      exact (e (Quotient.mk _ V)).property.2
    obtain ⟨_, hExt, hEuler⟩ :=
      ((EulerExt.two_term_projective_resolution k hacyclic V.val).2 V.val).1
    refine ⟨⟨a'⟩, hExt, ?_⟩
    apply (Module.finrank_zero_iff (R := k)).mp
    change _ - _ = titsForm (dimensionVector V.val) at hEuler
    rw [hHom, hq] at hEuler
    omega

end RepTheorySurvey.Quiver.Gabriel
