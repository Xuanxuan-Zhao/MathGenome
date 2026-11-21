import MathGenome.Internal.Specs.D07.Ch12.NormalCharacterizations
import MathGenome.Internal.D07.Ch12.NormalDefinition
import MathGenome.Internal.D07.Ch12.SplittingExistenceUniqueness
import Mathlib.FieldTheory.Normal.Basic

/-!
Normality, splitting fields, and embeddings (K07.12.normal_characterizations).

For a normal algebraic extension, every embedding into an overfield factors
as the original inclusion after an automorphism. Surjectivity of this
automorphism gives equality of images even in infinite degree. Conversely,
any root of an element's minimal polynomial in Ω is the image of that element
under a full embedding of L. Image invariance therefore puts all these roots
back in L, and splitting descends along the inclusion.

The finite splitting-field theorem uses the library's product-of-minimal-
polynomials construction. Its existential API allows the zero polynomial;
in that case the roots generate only the base, and the nonzero constant 1
has the same splitting field. Change of intermediate base follows because
the new minimal polynomial divides the old one after coefficient extension.
-/

universe u v w

namespace D07.Ch12.NormalCharacterizations

open Polynomial Specs.D07.Ch12.NormalCharacterizations

theorem normalIffEmbeddingImage : NormalIffEmbeddingImage.{u, v, w} := by
  intro K L Ω _ _ _ _ _ _ _ hAlg _
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  constructor
  · intro hNormal
    let : Normal K L := hNormal
    intro σ
    obtain ⟨e, rfl⟩ := (Normal.algHomEquivAut K Ω L).symm.surjective σ
    change Set.range (fun x : L => algebraMap L Ω (e x)) = _
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, by simp⟩
  · intro hImage
    apply (NormalDefinition.normalIffMinimalPolynomialSplits K L hAlg).mpr
    intro a
    apply Splits.of_splits_map (algebraMap L Ω)
    · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      exact IsAlgClosed.splits _
    · intro b hb
      have hb' : aeval b (minpoly K a) = 0 := by
        rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at hb
        exact (mem_aroots.mp hb).2
      obtain ⟨σ, hσ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
        (fun x : L => ⟨(hAlg.isAlgebraic x).isIntegral, IsAlgClosed.splits _⟩) hb'
      change b ∈ Set.range (algebraMap L Ω)
      rw [← hImage σ]
      exact ⟨a, hσ⟩

theorem finiteNormalIffSplittingField : FiniteNormalIffSplittingField.{u, v} := by
  intro K L _ _ _ hFinite
  let : FiniteDimensional K L :=
    (DegreeDefinition.finite_iff_finiteDimensional K L).mp hFinite
  constructor
  · intro hNormal
    let : Normal K L := hNormal
    obtain ⟨f, hf⟩ := Normal.exists_isSplittingField K L
    rcases eq_or_ne f 0 with rfl | hf0
    · have hOne : Polynomial.IsSplittingField K L (C 1) :=
        { splits' := by simp
          adjoin_rootSet' := by
            simpa only [rootSet_zero, rootSet_C] using hf.adjoin_rootSet' }
      exact ⟨C 1, (SplittingDefinition.library_characterization K L (C 1)
        (C_ne_zero.mpr one_ne_zero)).mpr hOne⟩
    · exact ⟨f, (SplittingDefinition.library_characterization K L f hf0).mpr hf⟩
  · rintro ⟨f, hf⟩
    let : Polynomial.IsSplittingField K L f :=
      (SplittingDefinition.library_characterization K L f hf.1).mp hf
    exact Normal.of_isSplittingField f

theorem normalOverIntermediateBase : NormalOverIntermediateBase.{u, v, w} := by
  intro K M L _ _ _ _ _ _ _ hNormal
  let : Normal K L := hNormal
  exact Normal.tower_top_of_normal K M L

end D07.Ch12.NormalCharacterizations
