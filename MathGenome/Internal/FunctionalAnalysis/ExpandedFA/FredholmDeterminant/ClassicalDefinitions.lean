import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalDefinitions

/-!
The classical continuous-kernel Fredholm series and their zero-size conventions.
The operator is the shared continuous-kernel operator on C(Q). The scalar series
use the ordinary finite determinants and n-fold product measures; neither
trace-class membership nor a determinant on an operator ideal is assumed.
-/

open MeasureTheory
universe u
namespace ExpandedFA.FredholmDeterminant.ClassicalDefinitions

noncomputable def kernelOperator : Spec.KernelOperatorType.{u} := @Spec.KernelOperatorValue.{u}

noncomputable def measureMass : Spec.MeasureMassType.{u} := @Spec.MeasureMassValue.{u}

noncomputable def kernelBound : Spec.KernelBoundType.{u} := @Spec.KernelBoundValue.{u}

noncomputable def measurePower : Spec.MeasurePowerType.{u} := @Spec.MeasurePowerValue.{u}

noncomputable def kernelMatrix : Spec.KernelMatrixType.{u} := @Spec.KernelMatrixValue.{u}

noncomputable def augmentedMatrix : Spec.AugmentedMatrixType.{u} := @Spec.AugmentedMatrixValue.{u}

noncomputable def determinantIntegral : Spec.DeterminantIntegralType.{u} := @Spec.DeterminantIntegralValue.{u}

noncomputable def minorIntegral : Spec.MinorIntegralType.{u} := @Spec.MinorIntegralValue.{u}

noncomputable def determinantTerm : Spec.DeterminantTermType.{u} := @Spec.DeterminantTermValue.{u}

noncomputable def minorTerm : Spec.MinorTermType.{u} := @Spec.MinorTermValue.{u}

noncomputable def fredholmDeterminant : Spec.FredholmDeterminantType.{u} := @Spec.FredholmDeterminantValue.{u}

noncomputable def fredholmMinor : Spec.FredholmMinorType.{u} := @Spec.FredholmMinorValue.{u}

theorem augmented_matrix_entries : Spec.AugmentedMatrixEntries.{u} := by
  intro Q _ k n x y t
  simp [Spec.AugmentedMatrixValue]

theorem product_mass : Spec.ProductMass.{u} := by
  intro Q _ μ _ n
  simp [Spec.MeasurePowerValue, Measure.pi_univ]

/-- An empty product of measures is a unit mass on the unique empty tuple.
This remains true if Q has no points and if μ is zero. -/
private lemma measurePower_zero_real {Q : Type u} [MeasurableSpace Q] (μ : Measure Q) :
    (Spec.MeasurePowerValue μ 0).real Set.univ = 1 := by
  simp [Spec.MeasurePowerValue, measureReal_def]

theorem zeroth_terms : Spec.ZerothTerms.{u} := by
  intro Q _ _ μ k
  have hd : Spec.DeterminantIntegralValue μ k 0 = 1 := by
    simp [Spec.DeterminantIntegralValue, Matrix.det_isEmpty, integral_const,
      measurePower_zero_real]
  have hm (x y : Q) : Spec.MinorIntegralValue μ k 0 x y = k (x, y) := by
    simp [Spec.MinorIntegralValue, Spec.AugmentedMatrixValue,
      integral_const, measurePower_zero_real]
  exact ⟨fun _ => Matrix.det_isEmpty, hd,
    fun z => by simp [Spec.DeterminantTermValue, hd],
    fun x y t => by simp [Spec.AugmentedMatrixValue],
    hm, fun x y z => by simp [Spec.MinorTermValue, hm]⟩

/-- Continuity is checked on the matrix entries before taking the determinant. -/
lemma continuous_kernel_determinant {Q : Type u} [TopologicalSpace Q]
    (k : C(Q × Q, ℂ)) (n : ℕ) :
    Continuous (fun t : Fin n → Q => (kernelMatrix k n t).det) := by
  apply Continuous.matrix_det
  exact continuous_pi fun i => continuous_pi fun j =>
    k.continuous.comp ((continuous_apply i).prodMk (continuous_apply j))

lemma continuous_augmented_determinant {Q : Type u} [TopologicalSpace Q]
    (k : C(Q × Q, ℂ)) (n : ℕ) (x y : Q) :
    Continuous (fun t : Fin n → Q => (augmentedMatrix k n x y t).det) := by
  have hx : Continuous (fun t : Fin n → Q => Fin.cons (α := fun _ => Q) x t) :=
    continuous_const.finCons continuous_id
  have hy : Continuous (fun t : Fin n → Q => Fin.cons (α := fun _ => Q) y t) :=
    continuous_const.finCons continuous_id
  apply Continuous.matrix_det
  exact continuous_pi fun i => continuous_pi fun j =>
    k.continuous.comp (((continuous_apply i).comp hx).prodMk ((continuous_apply j).comp hy))

theorem integrable_determinants : Spec.IntegrableDeterminants.{u} := by
  intro Q _ _ _ _ μ _ k n
  have : IsFiniteMeasure (Spec.MeasurePowerValue μ n) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Fin n => μ)))
  constructor
  · exact (continuous_kernel_determinant k n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro x y
    exact (continuous_augmented_determinant k n x y).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem data_identification : Spec.DataIdentification.{u} := by
  intro Q _ _ _ _ μ _ k
  exact ⟨ExpandedFA.PartV.ContinuousKernel.Spec.KernelOperatorValue_apply μ k, rfl, rfl⟩

end ExpandedFA.FredholmDeterminant.ClassicalDefinitions
