import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.LocalDetection
import Mathlib.RingTheory.Ideal.GoingUp

/-! DP-08, finite changes of rings (paper.tex:2894–2898, 2908–2923).
The action of R on N is restriction of its S-action along the structural map.
The infimum runs over every maximal ideal of S, without a support restriction;
its value is infinity if S is the zero ring. The last statement records attainment
when S has maximal ideals, so this infimum is indeed a minimum. -/
universe u
namespace AdvCommAlg.Depth.Specs

def grade_finite_algebraType : Prop :=
  ∀ {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S] [Module.Finite R S]
    (N : Type u) [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.Finite S N] (I : Ideal R),
    gradeValue I N = gradeValue (I.map (algebraMap R S)) N

def depth_eq_iInf_maximal_localDepthType : Prop :=
  ∀ {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] [Module.Finite R S]
    (N : Type u) [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.Finite S N] [IsLocalRing R],
    depthValue R N = ⨅ (p : PrimeSpectrum S) (_ : p.asIdeal.IsMaximal),
      depthValue (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N)

def exists_maximal_localDepth_eq_depthType : Prop :=
  ∀ {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] [Module.Finite R S]
    (N : Type u) [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.Finite S N] [IsLocalRing R] [Nontrivial S],
    ∃ p : PrimeSpectrum S, p.asIdeal.IsMaximal ∧
      depthValue (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) =
        depthValue R N

end AdvCommAlg.Depth.Specs
