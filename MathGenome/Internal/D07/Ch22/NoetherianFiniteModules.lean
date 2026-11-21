import MathGenome.Internal.Specs.D07.Ch22.NoetherianFiniteModules
import MathGenome.Internal.D07.Ch16.FinitePresentation
import MathGenome.Internal.D07.Ch16.QuotientsIsomorphism
import MathGenome.Internal.D07.Ch22.NoetherianEquivalences

/-!
K07.22.noetherian_finite_modules (paper.tex:6969–6995).
Noetherianity passes to submodules and quotients, and from the ends of
a short exact sequence to its middle. Over a Noetherian ring a finite
free cover of a finitely generated module has finitely generated kernel,
so the upstream finite-presentation criterion applies. Neither submodules
nor relation kernels are assumed free.
-/

universe u v w z

namespace D07.Ch22.NoetherianFiniteModules

open Specs.D07.Ch22.NoetherianFiniteModules

theorem submoduleNoetherian : SubmoduleNoetherian.{u, v} := by
  intro R _ M _ _ _ N
  exact isNoetherian_submodule' N

theorem quotientNoetherian : QuotientNoetherian.{u, v} := by
  intro R _ M _ _ _ N
  exact isNoetherian_quotient N

theorem exactSequenceNoetherian : ExactSequenceNoetherian.{u, v, w, z} := by
  intro R _ U _ _ M _ _ V _ _ f g _hf hex _hg hU hV
  let := hU
  let := hV
  exact isNoetherian_of_range_eq_ker f g (LinearMap.exact_iff.mp hex).symm

theorem finiteModuleNoetherian : FiniteModuleNoetherian.{u, v} := by
  intro R _ _ M _ _ _
  exact isNoetherian_of_isNoetherianRing_of_finite R M

theorem finiteModuleFinitelyPresented : FiniteModuleFinitelyPresented.{u, v} := by
  intro R _ _ M _ _ _
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  have hker : (LinearMap.ker π).FG := IsNoetherian.noetherian _
  exact (D07.Ch16.FinitePresentation.finitePresentationCriterion R M).mpr
    ⟨n, π, hπ, hker⟩

theorem finiteFreePresentation : FiniteFreePresentation.{u, v} := by
  intro R _ _ M _ _ _
  let := finiteModuleFinitelyPresented R M
  obtain ⟨n, s, π, A, hπ, hex⟩ := Module.FinitePresentation.exists_fin' R M
  exact ⟨n, s, π, A, hπ, hex, IsNoetherian.noetherian _⟩

end D07.Ch22.NoetherianFiniteModules
