import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleCoefficientVanishing
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CentralActionHomotopy
import MathGenome.Internal.AlgebraCore.P103.Ch10.HomotopyAndContraction

/-! LA-C03. Invertible coefficient multiplication is nullhomotopic by the
Casimir comparison homotopy. Composing with its inverse contracts the identity.
Evaluation transfers vanishing to exterior cochains, and comparison transfers
it to every projective resolution. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory CategoryTheory.Limits
open AdvancedHomologicalAlgebra.CE AdvancedHomologicalAlgebra.CE.Ext
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions
open LieAlgebrasAndRepresentations.CentralActionHomotopy
universe u v w

namespace LieAlgebrasAndRepresentations.SimpleCoefficientVanishing

/-- An invertible coefficient map which is nullhomotopic contracts Hom. -/
theorem homComplex_contractible {R : Type u} [Ring R]
    (P : ChainComplex (ModuleCat.{v} R) ℕ)
    (N : Type w) [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] N) (hf : Function.Bijective f)
    (H : Homotopy (homPostMap P f) 0) :
    Nonempty (Homotopy (𝟙 (homComplex P N)) 0) := by
  let e := LinearEquiv.ofBijective f hf
  have he : homPostMap P f ≫ homPostMap P e.symm.toLinearMap = 𝟙 _ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro F
    change P.X n →ₗ[R] N at F
    apply LinearMap.ext
    intro z
    exact e.symm_apply_apply (F z)
  have hh := H.compRight (homPostMap P e.symm.toLinearMap)
  rw [he, zero_comp] at hh
  exact ⟨hh⟩

variable (k : Type u) (g : Type v) (M : Type w)
  [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
  [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [LieRingModule g M] [LieModule k g M] [LieModule.IsIrreducible k g M]

attribute [local instance] LieAlgebrasAndRepresentations.CentralActionHomotopy.coefficientModule

/-- The identity contraction is obtained from the actual module Casimir. -/
theorem casimir_contracts
    (hg : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value k g)
    (hM : ¬ LieModule.IsTrivial g M) :
    Nonempty (Homotopy
      (𝟙 (homComplex (chain k g (boundaryData k g).differential
        (boundaryData k g).augmented) M)) 0) := by
  obtain ⟨C, hC, _, _, _, _, ⟨H⟩⟩ := module_casimir_nullhomotopy k g M hg hM
  exact homComplex_contractible _ M (centralLinear k g C hC.1 M) hC.2.2.2 H

theorem cohomology_vanishes :
    Specs.LieAlgebrasAndRepresentations.SimpleCoefficientVanishing.cohomology_vanishes_type.{u,v,w} := by
  intro k g M _ _ _ _ _ _ _ _ _ _ _ hg hM q
  let D := boundaryData k g
  let E := cochainData k g M D
  have he := (free_resolution k g D).1
  have h : Subsingleton
      (Homology (homComplex (chain k g D.differential D.augmented) M) q) :=
    P103.Ch10.HomotopyAndContraction.contractible_acyclic _ (casimir_contracts k g M hg hM) q
  obtain ⟨_, _, comparison⟩ := cohomology k g D he M E
  obtain ⟨e, _⟩ := comparison q
  exact @Equiv.subsingleton _ _ e.toEquiv h

theorem ext_vanishes :
    Specs.LieAlgebrasAndRepresentations.SimpleCoefficientVanishing.ext_vanishes_type.{u,v,w} := by
  intro k g M _ _ _ _ _ _ _ _ _ _ _ hg hM
  let := coefficientModule k g M
  let := trivialModule k g
  intro Q hQ q
  let D := boundaryData k g
  let E := cochainData k g M D
  have he := (free_resolution k g D).1
  obtain ⟨e, heval, _⟩ := cohomology k g D he M E
  obtain ⟨comparison, _⟩ := resolution_comparison k g D.differential D.formula
    D.augmented he M E.differential E.squared e
    (fun n F z => by rw [heval n F, E.evaluate_tmul]) Q hQ q
  exact @Equiv.subsingleton _ _ comparison.symm.toEquiv (cohomology_vanishes k g M hg hM q)

end LieAlgebrasAndRepresentations.SimpleCoefficientVanishing
