import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Homological.ExtProjectivityTest
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-! Independent statements for paper.tex, Proposition DP-12, lines 3067–3107.
The projective resolution includes its augmentation and quasi-isomorphism;
minimality is the actual image inclusion, not an assumed Tor comparison.
All degrees include degree zero, and existence allows the zero module. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AdvCommAlg

/-- A projective resolution which is finite free in every degree and whose
differentials have image in the maximal ideal times their target. -/
structure IsMinimalFreeResolution {R : Type u} [CommRing R] [IsLocalRing R]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) : Prop where
  finite : ∀ i, Module.Finite R (P.complex.X i)
  free : ∀ i, Module.Free R (P.complex.X i)
  minimal : ∀ i, LinearMap.range (P.complex.d (i + 1) i).hom ≤
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R (P.complex.X i))

end AdvCommAlg

namespace Specs.AdvCommAlg

def finite_projective_free : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (M : ModuleCat.{u} R),
    Module.Finite R M → Module.Projective R M → Module.Free R M

def exists_minimalFreeResolution : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R), Module.Finite R M →
      ∃ P : ProjectiveResolution M, _root_.AdvCommAlg.IsMinimalFreeResolution P

/-- The actual left derived tensor functor, computed in the resolved variable M.
The comparison is an R-linear isomorphism. The Tor object is defined independently
of P. No nonzero hypothesis on M is imposed. -/
def minimalFreeResolution_torIso : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (P : ProjectiveResolution M),
    _root_.AdvCommAlg.IsMinimalFreeResolution P → ∀ i : ℕ,
      Nonempty (ModuleCat.of R (IsLocalRing.ResidueField R ⊗[R] P.complex.X i) ≅
        ((CategoryTheory.Tor (ModuleCat.{u} R) i).obj
          (ModuleCat.of R (IsLocalRing.ResidueField R))).obj M)

def minimalFreeResolution_lastNonzero : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (P : ProjectiveResolution M), _root_.AdvCommAlg.IsMinimalFreeResolution P →
    ∀ e : ℕ, projectiveDimension M = (e : WithBot ℕ∞) →
      (∀ i : ℕ, e < i → Subsingleton (P.complex.X i)) ∧
        Nontrivial (P.complex.X e)

end Specs.AdvCommAlg
