import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.DenseUniformExtension
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformConventions
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! Extension from a dense uniform subspace (`d10:12:dense-extension`).

Mathlib's `Dense.uniformContinuous_extend` proves the extension theorem using
the proper filter `(nhds z).comap Subtype.val`, its Cauchy image under `f`,
and target completeness. Its proof does not invoke uniform completion.
`Dense.extend` supplies its own nonemptiness witness at each input by density
and the given map, so no global `Nonempty Y` assumption is needed. This also
handles empty spaces. The accepted bridges below identify the manuscript's
entourage definitions with precisely the library hypotheses and conclusions.
-/

universe u v

namespace D10Topology.Ch12

theorem dense_uniform_extension
    {Z : Type u} {Y : Type v} [UniformSpace Z] [UniformSpace Y]
    (A : Set Z) (hA : Dense A) (hY : Complete Y) (hsep : Separated (X := Y))
    (f : A → Y) (hf : EntourageContinuous f) :
    ∃! g : Z → Y, EntourageContinuous g ∧ ∀ a : A, g a.val = f a := by
  letI : CompleteSpace Y := complete_iff_mathlib.mp hY
  letI : T0Space Y := separated_iff_mathlib.mp hsep
  have hfu : UniformContinuous f := (entourageContinuous_iff_mathlib f).mp hf
  refine ⟨hA.extend f, ⟨?_, ?_⟩, ?_⟩
  · exact (entourageContinuous_iff_mathlib _).mpr (hA.uniformContinuous_extend hfu)
  · exact hA.extend_of_ind hfu
  · intro g hg
    exact (hA.extend_unique hg.2
      ((entourageContinuous_iff_mathlib g).mp hg.1).continuous).symm

theorem continuous_extension_unique
    {Z : Type u} {Y : Type v} [UniformSpace Z] [UniformSpace Y]
    (A : Set Z) (hA : Dense A) (hsep : Separated (X := Y))
    (f : A → Y) (g h : Z → Y) (hg : Continuous g) (hh : Continuous h)
    (hgf : ∀ a : A, g a.val = f a) (hhf : ∀ a : A, h a.val = f a) : g = h := by
  letI : T0Space Y := separated_iff_mathlib.mp hsep
  exact (hA.extend_unique hgf hg).symm.trans (hA.extend_unique hhf hh)

end D10Topology.Ch12
