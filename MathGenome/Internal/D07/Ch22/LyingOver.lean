import MathGenome.Internal.Specs.D07.Ch22.LyingOver
import MathGenome.Internal.D07.Ch22.LyingOverIntegralDomainFieldCriterion
import MathGenome.Internal.D07.Ch22.LyingOverIntegralLocalizationInclusion
import MathGenome.Internal.D07.Ch09.MaximalExistence
import Mathlib.RingTheory.Ideal.GoingUp

/-!
K07.22.lying_over (paper.tex:7286–7333).

The main proof follows the source's localization argument, using the
assigned field-criterion and localization prerequisites. For the
noninjective formulation, Mathlib's general integral going-up theorem
applied to the zero ideal gives exactly the kernel condition. The local
algebra structure is induced by the specified homomorphism, so its
algebra map and integral-element predicate are the specified ones.
-/

universe u v

namespace D07.Ch22.LyingOver

open Specs.D07.Ch22.LyingOver
open Specs.D07.Ch22.LyingOverIntegralLocalizationInclusion

theorem lyingOver : PrimeLyingOver.{u, v} := by
  intro R B _ _ f hf hint P hP
  let := hP
  let T := Localization (P.primeCompl.map f)
  let g : Localization.AtPrime P →+* T := localizationMap f P.primeCompl
  have hg : Function.Injective g :=
    LyingOverIntegralLocalizationInclusion.mapInjective R B f P.primeCompl hf
  have hi : g.IsIntegral :=
    LyingOverIntegralLocalizationInclusion.mapIntegral R B f P.primeCompl hint
  let : Nontrivial T :=
    (LyingOverIntegralLocalizationInclusion.nonzeroAtPrime R B f P hf).2
  obtain ⟨M, _, hM⟩ := D07.Ch09.MaximalExistence.existsMaximal T ⊥ bot_ne_top
  have hMc : (M.comap g).IsMaximal :=
    LyingOverIntegralDomainFieldCriterion.maximalContraction
      (Localization.AtPrime P) T g hg hi M hM
  have heq : M.comap g = Ideal.map (algebraMap R (Localization.AtPrime P)) P :=
    (LocalRings.uniqueMaximalIdeal R P).2 _ hMc
  refine ⟨M.comap (algebraMap B T),
    D07.Ch09.Contraction.prime_contraction B T (algebraMap B T) M hM.isPrime, ?_⟩
  have hcomm : (algebraMap B T).comp f = g.comp (algebraMap R (Localization.AtPrime P)) := by
    ext r
    exact (IsLocalization.map_eq (S := Localization.AtPrime P) (Q := T) (g := f)
      P.primeCompl.le_comap_map r).symm
  rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap, heq]
  exact LocalizationIdeals.contractionExtension R P.primeCompl P hP
    (Set.disjoint_left.mpr (fun _ hs hp => hs hp))

theorem lyingOverIffKernelLe : LyingOverIffKernelLe.{u, v} := by
  intro R B _ _ f hint P hP
  constructor
  · rintro ⟨Q, _hQ, hQP⟩
    rw [← hQP]
    intro r hr
    change f r ∈ Q
    change f r = 0 at hr
    rw [hr]
    exact Q.zero_mem
  · intro hker
    let : Algebra R B := f.toAlgebra
    let : Algebra.IsIntegral R B := ⟨hint⟩
    let := hP
    obtain ⟨Q, _, hQ, hQP⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (S := B) P ⊥ hker
    exact ⟨Q, hQ, hQP⟩

theorem zeroRingNoPrimes : ZeroRingNoPrimes.{u} := by
  intro R _ _ P hP
  exact hP.ne_top (Subsingleton.elim _ _)

end D07.Ch22.LyingOver
