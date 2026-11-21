import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.CompositionCoordinates
import MathGenome.Internal.RealAnalysis.D11.Ch04.MeasurableMapTests
import MathGenome.Internal.RealAnalysis.D11.Ch03.BorelGenerators

/-! Composition and coordinate tests, with exactly specified Borel targets.
The coordinate proof uses the coordinate homeomorphism from Euclidean ℓ²
space to the finite product. Only the topology, not an equality of norms,
is used. All statements also allow an empty source. -/

open Set MeasurableSpace
open scoped MeasureTheory
universe u v w
namespace D11.Ch04.CompositionCoordinates

open D11.Ch03.BorelGenerators

theorem composition : Specs.D11.Ch04.CompositionCoordinates.composition := by
  intro X Y Z m n p f g hf hg
  exact hg.comp hf

theorem continuous_borel : Specs.D11.Ch04.CompositionCoordinates.continuous_borel := by
  intro Y Z _ _ g hg
  exact hg.borel_measurable

theorem continuous_after_measurable :
    Specs.D11.Ch04.CompositionCoordinates.continuous_after_measurable := by
  intro X Y Z _ _ m f g hf hg
  exact hg.borel_measurable.comp hf

theorem euclidean_coordinates :
    Specs.D11.Ch04.CompositionCoordinates.euclidean_coordinates := by
  intro X m d f
  let : MeasurableSpace X := m
  constructor
  · intro hf i
    exact (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).borel_measurable.comp hf
  · intro hf
    have hpi : Measurable (fun x i => f x i) := measurable_pi_iff.mpr hf
    have hpi' : @Measurable X (Fin d → ℝ) m (borel (Fin d → ℝ))
        (fun x i => f x i) := by
      rwa [← BorelSpace.measurable_eq]
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).borel_measurable.comp hpi'

theorem complex_coordinates :
    Specs.D11.Ch04.CompositionCoordinates.complex_coordinates := by
  intro X m f
  let : MeasurableSpace X := m
  constructor
  · intro hf
    exact ⟨Complex.continuous_re.borel_measurable.comp hf,
      Complex.continuous_im.borel_measurable.comp hf⟩
  · rintro ⟨hre, him⟩
    have hp : Measurable (fun x => ((f x).re, (f x).im)) := hre.prodMk him
    have hp' : @Measurable X (ℝ × ℝ) m (borel (ℝ × ℝ))
        (fun x => ((f x).re, (f x).im)) := by
      rwa [← BorelSpace.measurable_eq]
    exact Complex.equivRealProdCLM.symm.continuous.borel_measurable.comp hp'

theorem finite_real_tuple : Specs.D11.Ch04.CompositionCoordinates.finite_real_tuple := by
  intro X m d f hf
  exact (euclidean_coordinates m d _).mpr hf

theorem finite_complex_tuple : Specs.D11.Ch04.CompositionCoordinates.finite_complex_tuple := by
  intro X m d f hf
  let : MeasurableSpace X := m
  rw [← BorelSpace.measurable_eq]
  exact measurable_pi_iff.mpr hf

theorem real_modulus : Specs.D11.Ch04.CompositionCoordinates.real_modulus := by
  intro X m f hf
  exact continuous_abs.borel_measurable.comp hf

theorem complex_modulus : Specs.D11.Ch04.CompositionCoordinates.complex_modulus := by
  intro X m f hf
  exact continuous_norm.borel_measurable.comp hf

theorem complex_conjugation : Specs.D11.Ch04.CompositionCoordinates.complex_conjugation := by
  intro X m f hf
  exact Complex.continuous_conj.borel_measurable.comp hf

theorem indicator_test : Specs.D11.Ch04.CompositionCoordinates.indicator_test := by
  intro X Y m n f
  let : MeasurableSpace X := m
  let : MeasurableSpace Y := n
  constructor
  · intro h A hA
    have hcomp := h A hA
    have heq : ((A.indicator (fun _ => (1 : ℝ))) ∘ f) ⁻¹' {1} = f ⁻¹' A := by
      ext x
      simp [Function.comp_def]
    rw [← heq]
    exact hcomp (measurableSet_singleton 1)
  · intro h A hA
    have hf : @Measurable X Y m n f := fun _ hB => h _ hB
    exact (measurable_const.indicator hA).comp hf

end D11.Ch04.CompositionCoordinates
