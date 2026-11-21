import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! Independent statement of the finite-projective-dimension criterion in
paper.tex, CM-12 (3656–3661). The ring is Cohen–Macaulay as a local module
over itself. For a nonzero module, projective dimension different from top
means finite projective dimension. The grade is evaluated on the ring. -/

universe u
open CategoryTheory
namespace AdvCommAlg.CohenMacaulay.Specs

def localCohenMacaulay_iff_projectiveDimension_eq_gradeType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    LocalCohenMacaulayValue R R →
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M],
      projectiveDimension M ≠ ⊤ →
      (LocalCohenMacaulayValue R M ↔
        projectiveDimension M =
          (AdvCommAlg.Depth.Specs.gradeValue (Module.annihilator R M) R : WithBot ℕ∞))

end AdvCommAlg.CohenMacaulay.Specs
