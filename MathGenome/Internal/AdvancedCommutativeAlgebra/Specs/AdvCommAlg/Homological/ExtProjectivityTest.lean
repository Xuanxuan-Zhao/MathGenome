import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-! The general projectivity criterion used in paper.tex, DP-12 (and DP-11).
No local, Noetherian, finite generation, or nonzero assumptions are imposed. -/

open CategoryTheory CategoryTheory.Abelian

universe u v

namespace AdvCommAlg

/-- The bth syzygy of an augmented projective resolution, represented as
`coker(P_{b+1} → P_b)`. Exactness identifies this with the usual image in
`P_{b-1}` for positive b; in degree zero the augmentation identifies it with M.
In particular this is not Mathlib's `Projective.syzygies`, which is a projective
cover of a kernel rather than the kernel itself. -/
noncomputable def resolutionSyzygy {R : Type u} [CommRing R]
    {M : ModuleCat.{v} R} (P : ProjectiveResolution M) (b : ℕ) : ModuleCat.{v} R :=
  P.complex.opcycles b

end AdvCommAlg

namespace Specs.AdvCommAlg

/-- Vanishing of the actual derived Ext group in degree one detects projectivity. -/
def projective_of_ext_one_vanishes : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (T : ModuleCat.{v} R),
    (∀ V : ModuleCat.{v} R, Subsingleton (Ext T V 1)) → Module.Projective R T

/-- Vanishing in the single degree b+1 bounds projective dimension, including b=0. -/
def projectiveDimension_le_of_ext_vanishes : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (M : ModuleCat.{v} R) (b : ℕ),
    (∀ V : ModuleCat.{v} R, Subsingleton (Ext M V (b + 1))) →
      projectiveDimension M ≤ (b : WithBot ℕ∞)

/-- The bth syzygy in every projective resolution is projective under the same
single-degree vanishing hypothesis. -/
def syzygy_projective_of_ext_vanishes : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (M : ModuleCat.{v} R) (b : ℕ)
    (P : ProjectiveResolution M),
    (∀ V : ModuleCat.{v} R, Subsingleton (Ext M V (b + 1))) →
      Module.Projective R (_root_.AdvCommAlg.resolutionSyzygy P b)

end Specs.AdvCommAlg
