import MathGenome.Internal.Specs.D05.M03.Kernel
import MathGenome.Internal.Specs.D05.M03.Image

/-!
Independent statements for K05.03.injective_surjective (paper.tex:553–559).

The kernel and image are the canonical submodules used by the upstream Specs.
The bottom submodule has carrier `{0}`, and the top submodule has carrier the
whole codomain. Both equivalences quantify over arbitrary vector spaces over
the same field, including zero spaces, without a dimension hypothesis.
-/

namespace Specs.D05.M03.InjectiveSurjective

/-- Injectivity is equivalent to the kernel being the zero subspace. -/
def injective_iff_kernel_eq_bot : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    Function.Injective T ↔ LinearMap.ker T = ⊥

/-- Surjectivity is equivalent to the image being the entire codomain. -/
def surjective_iff_image_eq_top : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    Function.Surjective T ↔ LinearMap.range T = ⊤

end Specs.D05.M03.InjectiveSurjective
