import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! Independent statements of DP-06 (paper.tex:2817–2830).
The support restriction is explicit; the infimum in `ℕ∞` of an empty set is `⊤`.
No nonzero or properness assumptions are imposed on the detection formula or
its radical, product and intersection consequences. -/
universe u
namespace AdvCommAlg.Depth.Specs

def grade_eq_iInf_localDepthType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (I : Ideal R),
    gradeValue I M = ⨅ (p : PrimeSpectrum R)
      (_ : I ≤ p.asIdeal) (_ : p ∈ Module.support R M),
      depthValue (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M)

def grade_radicalType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (I : Ideal R),
    gradeValue I.radical M = gradeValue I M

def grade_mulType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (I J : Ideal R),
    gradeValue (I * J) M = min (gradeValue I M) (gradeValue J M)

def grade_infType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (I J : Ideal R),
    gradeValue (I ⊓ J) M = min (gradeValue I M) (gradeValue J M)

def grade_le_heightType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R), I ≠ ⊤ → gradeValue I R ≤ I.height

end AdvCommAlg.Depth.Specs
