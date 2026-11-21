import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Homological.MinimalFreeResolution
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Basic

/-! Independent statements of the last assertions of CM-12
(paper.tex:3664–3667, 3697–3700). A finite free resolution is represented by
an augmented projective resolution with finite free terms, all of whose
terms above the stated length are zero. Thus length zero, early termination,
and the field case are included. The uniform dimension bound admits zero
modules; the sharper depth bound requires a nonzero module, as in the source.
-/

universe u
open CategoryTheory CategoryTheory.Abelian
namespace AdvCommAlg.CohenMacaulay.Specs

def regularLocal_projectiveDimension_le_sub_depthType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M] (d e : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) → Depth.Specs.depthValue R M = (e : ℕ∞) →
    projectiveDimension M ≤ ((d - e : ℕ) : WithBot ℕ∞)

def regularLocal_exists_finiteFreeResolutionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M] (d e : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) → Depth.Specs.depthValue R M = (e : ℕ∞) →
    ∃ P : ProjectiveResolution M,
      (∀ i, Module.Finite R (P.complex.X i)) ∧
      (∀ i, Module.Free R (P.complex.X i)) ∧
      (∀ i : ℕ, d - e < i → Subsingleton (P.complex.X i))

def regularLocal_projectiveDimension_leType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) → projectiveDimension M ≤ (d : WithBot ℕ∞)

def regularLocal_residueField_projectiveDimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (d : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) →
    projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) = (d : WithBot ℕ∞)

end AdvCommAlg.CohenMacaulay.Specs
