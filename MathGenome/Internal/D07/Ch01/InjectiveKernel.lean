import MathGenome.Internal.D07.Ch01.IsomorphismDefinition
import MathGenome.Internal.D07.Ch01.KernelImage
import MathGenome.Internal.Specs.D07.Ch01.InjectiveKernel

/-!
Injectivity, surjectivity, and isomorphisms (`K07.01.injective_kernel`).
The kernel and image are the canonical subgroups with carriers established
upstream. No commutativity or nontriviality is required. The finite statements
use natural cardinalities only under explicit finiteness hypotheses.
-/

namespace D07.Ch01.InjectiveKernel

universe u v

theorem injective_iff_kernel_singleton (G : Type u) (H : Type v)
    [Group G] [Group H] (f : G →* H) :
    Function.Injective f ↔ (f.ker : Set G) = {1} := by
  constructor
  · intro hf
    rw [f.ker_eq_bot hf, Subgroup.coe_bot]
  · intro hker
    apply f.ker_eq_bot_iff.mp
    apply SetLike.coe_injective
    exact hker.trans Subgroup.coe_bot.symm

theorem surjective_iff_image_univ (G : Type u) (H : Type v)
    [Group G] [Group H] (f : G →* H) :
    Function.Surjective f ↔ (f.range : Set H) = Set.univ := by
  change Function.Surjective f ↔ Set.range f = Set.univ
  exact Set.range_eq_univ.symm

theorem isomorphism_of_finite_injective (G : Type u) (H : Type v)
    [Group G] [Group H] [Finite G] [Finite H] (f : G →* H)
    (hcard : Nat.card G = Nat.card H) (hf : Function.Injective f) :
    IsomorphismDefinition.IsIsomorphism G H f :=
  (Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩

theorem isomorphism_of_finite_surjective (G : Type u) (H : Type v)
    [Group G] [Group H] [Finite G] [Finite H] (f : G →* H)
    (hcard : Nat.card G = Nat.card H) (hf : Function.Surjective f) :
    IsomorphismDefinition.IsIsomorphism G H f :=
  (Nat.bijective_iff_surjective_and_card f).mpr ⟨hf, hcard⟩

theorem finite_isomorphism_bundled (G : Type u) (H : Type v)
    [Group G] [Group H] [Finite G] [Finite H] (f : G →* H)
    (hcard : Nat.card G = Nat.card H)
    (hf : Function.Injective f ∨ Function.Surjective f) :
    ∃ e : G ≃* H, e.toMonoidHom = f := by
  apply (IsomorphismDefinition.isomorphism_iff_bundled G H f).mp
  rcases hf with hinj | hsurj
  · exact isomorphism_of_finite_injective G H f hcard hinj
  · exact isomorphism_of_finite_surjective G H f hcard hsurj

end D07.Ch01.InjectiveKernel
