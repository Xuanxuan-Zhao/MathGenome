import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.NoetherianFiniteness
import MathGenome.Internal.AlgebraCore.P103.Ch02.ChainConditions
import MathGenome.Internal.AlgebraCore.P103.Ch02.FinitePresentation

/-!
Hilbert's basis theorem and finite modules (paper.tex, Theorem 5.1).
The polynomial and finite-type results use the library Hilbert basis theorem
and its quotient-algebra consequence. For modules, a finite free cover has
finitely generated kernel because its source is Noetherian. Chapter 2's
kernel criterion then yields finite presentation. Submodules inherit the
Noetherian property, hence are finite, and the same argument applies to them.
All results allow zero rings, empty sets of variables, and zero modules.
-/

namespace P103.Ch05.NoetherianFiniteness

open P103.Specs.Ch05.NoetherianFiniteness

theorem ring_characterizations : ring_characterizationsType := by
  intro R _
  exact ⟨P103.Ch02.ChainConditions.noetherian_iff_ascending R R,
    P103.Ch02.ChainConditions.noetherian_iff_fg R R⟩

theorem module_characterizations : module_characterizationsType := by
  intro R _ M _ _
  exact ⟨P103.Ch02.ChainConditions.noetherian_iff_ascending R M,
    P103.Ch02.ChainConditions.noetherian_iff_fg R M⟩

theorem polynomial_noetherian : polynomial_noetherianType := by
  intro R _ _
  exact Polynomial.isNoetherianRing

theorem mvPolynomial_noetherian : mvPolynomial_noetherianType := by
  intro R _ _ ι _
  exact MvPolynomial.isNoetherianRing

theorem finiteType_noetherian : finiteType_noetherianType := by
  intro R _ _ A _ _ _
  exact Algebra.FiniteType.isNoetherianRing R A

theorem finite_module : finite_moduleType := by
  intro R _ _ M _ _ _
  refine ⟨inferInstance, ?_⟩
  apply (P103.Ch02.FinitePresentation.finite_free_cover_iff R M).mpr
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact ⟨n, f, hf, IsNoetherian.noetherian (LinearMap.ker f)⟩

theorem submodule_finiteness : submodule_finitenessType := by
  intro R _ _ M _ _ _ N
  have hM : IsNoetherian R M := (finite_module R M).1
  have : IsNoetherian R N :=
    P103.Ch02.ChainConditions.noetherian_submodule R M N hM
  have : Module.Finite R N := inferInstance
  exact ⟨(P103.Ch02.ChainConditions.noetherian_iff_fg R M).mp hM N,
    (finite_module R N).1, (finite_module R N).2⟩

end P103.Ch05.NoetherianFiniteness
