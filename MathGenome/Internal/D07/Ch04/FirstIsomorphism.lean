import MathGenome.Internal.D07.Ch01.InjectiveKernel
import MathGenome.Internal.D07.Ch04.QuotientUniversalProperty
import MathGenome.Internal.Specs.D07.Ch04.FirstIsomorphism
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
The group first isomorphism theorem (`K07.04.first_isomorphism`,
paper.tex:691–700), including the prescribed map on every left coset
and the surjective case. Mathlib's equivalences have exactly these
canonical kernels, images, and quotient groups. Their forward maps
are the quotient lifts, so both representative formulas are definitional.
-/

namespace D07.Ch04.FirstIsomorphism

universe u v

theorem first_isomorphism (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) :
    ∃ e : G ⧸ f.ker ≃* f.range,
      ∀ g : G, (e (QuotientGroup.mk' f.ker g) : H) = f g := by
  exact ⟨QuotientGroup.quotientKerEquivRange f, fun _ => rfl⟩

theorem first_isomorphism_of_surjective (G : Type u) (H : Type v)
    [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) :
    ∃ e : G ⧸ f.ker ≃* H,
      ∀ g : G, e (QuotientGroup.mk' f.ker g) = f g := by
  exact ⟨QuotientGroup.quotientKerEquivOfSurjective f hf, fun _ => rfl⟩

end D07.Ch04.FirstIsomorphism
