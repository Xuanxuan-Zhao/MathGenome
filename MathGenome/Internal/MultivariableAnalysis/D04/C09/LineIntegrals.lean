import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.LineIntegrals
import MathGenome.Internal.MultivariableAnalysis.D04.C09.PathsLength
import MathGenome.Internal.MultivariableAnalysis.D04.C01.OperatorEstimates
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.GraphLength
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.FiniteChanges

noncomputable section
open Set
open scoped BigOperators
namespace D04.C09
open Specs.D04.C01.EuclideanInterfaces.Model
open SingleVariableAnalysis.Riemann

abbrev PieceIntegrable := @Specs.D04.C09.LineIntegrals.Model.PieceIntegrable
abbrev pieceIntegral := @Specs.D04.C09.LineIntegrals.Model.pieceIntegral
abbrev ScalarIntegrable := @Specs.D04.C09.LineIntegrals.Model.ScalarIntegrable
abbrev scalarLineIntegral := @Specs.D04.C09.LineIntegrals.Model.scalarLineIntegral
abbrev CovectorIntegrable := @Specs.D04.C09.LineIntegrals.Model.CovectorIntegrable
abbrev covectorLineIntegral := @Specs.D04.C09.LineIntegrals.Model.covectorLineIntegral
abbrev workCovector := @Specs.D04.C09.LineIntegrals.Model.workCovector
abbrev WorkIntegrable := @Specs.D04.C09.LineIntegrals.Model.WorkIntegrable
abbrev covectorVector := @Specs.D04.C09.LineIntegrals.Model.covectorVector
abbrev workLineIntegral := @Specs.D04.C09.LineIntegrals.Model.workLineIntegral

lemma riemann_integrable_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) : RealIntegrable f a b := by
  apply real_continuous_integrable _ hab
  intro t ht
  exact (SingleVariableAnalysis.relativeContinuousAt_within_iff _ _ _).mpr (hf t ht)

theorem scalar_integrable {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (f : E n → ℝ) (hf : ContinuousOn f (trace γ)) :
    ScalarIntegrable d f := by
  intro i
  apply riemann_integrable_of_continuousOn
    (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))).le
  exact (hf.comp (γ.continuousOn.mono (cell_subset_interval d.partition i))
    (fun t ht => ⟨t, cell_subset_interval d.partition i ht, rfl⟩)).mul (d.smooth i).1.norm

theorem covector_integrable {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (α : E n → E n →L[ℝ] ℝ)
    (hα : ContinuousOn α (trace γ)) : CovectorIntegrable d α := by
  intro i
  apply riemann_integrable_of_continuousOn
    (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))).le
  exact (hα.comp (γ.continuousOn.mono (cell_subset_interval d.partition i))
    (fun t ht => ⟨t, cell_subset_interval d.partition i ht, rfl⟩)).clm_apply (d.smooth i).1

theorem work_integrable {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (F : E n → E n) (hF : ContinuousOn F (trace γ)) :
    WorkIntegrable d F := by
  intro i
  apply riemann_integrable_of_continuousOn
    (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))).le
  exact (hF.comp (γ.continuousOn.mono (cell_subset_interval d.partition i))
    (fun t ht => ⟨t, cell_subset_interval d.partition i ht, rfl⟩)).inner (d.smooth i).1

lemma riemann_congr {f g : ℝ → ℝ} {a b : ℝ} (hf : RealIntegrable f a b)
    (heq : EqOn f g (Icc a b)) :
    ∃ hg : RealIntegrable g a b, realIntegral g hg = realIntegral f hf := by
  have himg : g '' Icc a b = f '' Icc a b := image_congr (fun x hx => (heq hx).symm)
  have hbg : BoundedOnInterval g a b := by
    change BddBelow (g '' Icc a b) ∧ BddAbove (g '' Icc a b)
    rw [himg]
    exact hf.bounded
  apply real_finite_changes f g hf.bounded hbg _ hf
  have hempty : {x | x ∈ Icc a b ∧ f x ≠ g x} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hx
    exact not_not.mpr (heq hx)
  rw [hempty]
  exact finite_empty

lemma velocities_agree_on_cell {n a b} {γ : IntervalPath n a b}
    (d e : PiecewiseC1Data γ) (R : Partition a b)
    (j : Fin R.n) (i : Fin d.partition.n) (k : Fin e.partition.n)
    (hd : cell R j ⊆ cell d.partition i) (he : cell R j ⊆ cell e.partition k) :
    EqOn (d.velocity i) (e.velocity k) (cell R j) := by
  intro t ht
  have h₁ := ((d.smooth i).2 t (hd ht)).mono hd
  have h₂ := ((e.smooth k).2 t (he ht)).mono he
  have hu := uniqueDiffOn_Icc (R.strictMono (Fin.castSucc_lt_succ (i := j))) t ht
  exact (h₁.derivWithin hu).symm.trans (h₂.derivWithin hu)

open D04.Darboux.Subdivision

/-- A fine cell's unique coarse parent, for a common refinement. -/
def parentCell {a b : ℝ} {P R : Partition a b} (h : Refines R P) (j : Fin R.n) : Fin P.n :=
  ((cellEquiv h).symm j).1

lemma parentCell_subset {a b : ℝ} {P R : Partition a b} (h : Refines R P) (j : Fin R.n) :
    cell R j ⊆ cell P (parentCell h j) := by
  have hh := embed_cell_subset h ((cellEquiv h).symm j).1 ((cellEquiv h).symm j).2
  have he : embedCell h ((cellEquiv h).symm j).1 ((cellEquiv h).symm j).2 = j :=
    (cellEquiv h).apply_symm_apply j
  rw [he] at hh
  exact hh

/-- Riemann additivity and a bijective enumeration of the refined cells. -/
lemma sum_integrals_refinement {a b : ℝ} {P R : Partition a b} (h : Refines R P)
    (f : Fin P.n → ℝ → ℝ) (g : Fin R.n → ℝ → ℝ)
    (hf : ∀ i, RealIntegrable (f i) (P.point i.castSucc) (P.point i.succ))
    (heq : ∀ j, EqOn (f (parentCell h j)) (g j) (cell R j)) :
    ∃ hg : ∀ j, RealIntegrable (g j) (R.point j.castSucc) (R.point j.succ),
      (∑ i, realIntegral (f i) (hf i)) = ∑ j, realIntegral (g j) (hg j) := by
  have hsub (j : Fin R.n) : RealIntegrable (f (parentCell h j))
      (R.point j.castSucc) (R.point j.succ) := by
    have hs := parentCell_subset h j
    have hl := hs (left_mem_Icc.mpr (R.strictMono (Fin.castSucc_lt_succ (i := j))).le)
    have hr := hs (right_mem_Icc.mpr (R.strictMono (Fin.castSucc_lt_succ (i := j))).le)
    exact (hf _).subinterval hl.1 (R.strictMono (Fin.castSucc_lt_succ (i := j))).le hr.2
  choose hg hval using fun j => riemann_congr (hsub j) (heq j)
  refine ⟨hg, ?_⟩
  rw [← (cellEquiv h).sum_comp (fun j => realIntegral (g j) (hg j)), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  have he (k : Fin (restrictPartition h i).n) :
      realIntegral (g (embedCell h i k)) (hg _) =
        realIntegral (f i) ((hf i).subinterval (graph_point_mem (restrictPartition h i) k.castSucc).1
          ((restrictPartition h i).strictMono (Fin.castSucc_lt_succ (i := k))).le
          (graph_point_mem (restrictPartition h i) k.succ).2) := by
    have hv := hval (embedCell h i k)
    have hp : parentCell h (embedCell h i k) = i :=
      congrArg Sigma.fst ((cellEquiv h).symm_apply_apply ⟨i, k⟩)
    simp only [hp] at hv
    simpa only [restrict_left, restrict_right] using hv
  change realIntegral (f i) (hf i) = ∑ k, realIntegral (g (embedCell h i k)) (hg _)
  simp_rw [he]
  exact (graph_sum_cell_integrals (hf i) (restrictPartition h i)).symm

theorem pieceIntegral_independent {n a b} {γ : IntervalPath n a b}
    (d e : PiecewiseC1Data γ) (H : E n → E n → ℝ)
    (hd : PieceIntegrable d H) (he : PieceIntegrable e H) :
    pieceIntegral d H hd = pieceIntegral e H he := by
  obtain ⟨R, _, hRd, hRe⟩ := common_refinement d.partition e.partition
  let g (j : Fin R.n) (t : ℝ) := H (γ t) (d.velocity (parentCell hRd j) t)
  obtain ⟨hg, hds⟩ := sum_integrals_refinement hRd
    (fun i t => H (γ t) (d.velocity i t)) g hd (fun _ _ _ => rfl)
  obtain ⟨hg', hes⟩ := sum_integrals_refinement hRe
    (fun i t => H (γ t) (e.velocity i t)) g he (by
      intro j t ht
      dsimp [g]
      rw [velocities_agree_on_cell e d R j (parentCell hRe j) (parentCell hRd j)
        (parentCell_subset hRe j) (parentCell_subset hRd j) ht])
  exact hds.trans hes.symm

theorem scalarLineIntegral_independent {n a b} {γ : IntervalPath n a b}
    (d e : PiecewiseC1Data γ) (f : E n → ℝ)
    (hd : ScalarIntegrable d f) (he : ScalarIntegrable e f) :
    scalarLineIntegral d f hd = scalarLineIntegral e f he :=
  pieceIntegral_independent d e _ hd he

theorem covectorLineIntegral_independent {n a b} {γ : IntervalPath n a b}
    (d e : PiecewiseC1Data γ) (α : E n → E n →L[ℝ] ℝ)
    (hd : CovectorIntegrable d α) (he : CovectorIntegrable e α) :
    covectorLineIntegral d α hd = covectorLineIntegral e α he :=
  pieceIntegral_independent d e _ hd he

theorem pieceIntegral_degenerate {n a} {γ : IntervalPath n a a}
    (d : PiecewiseC1Data γ) (H : E n → E n → ℝ) (h : PieceIntegrable d H) :
    pieceIntegral d H h = 0 := by
  have : IsEmpty (Fin d.partition.n) :=
    Fin.isEmpty_iff.mpr (n_eq_zero_of_degenerate a d.partition)
  exact Finset.sum_of_isEmpty _

theorem workCovector_apply {n} (F : E n → E n) (x v : E n) :
    workCovector F x v = inner ℝ (F x) v := rfl

theorem workCovector_coordinates {n} (F : E n → E n) (x v : E n) :
    workCovector F x v = ∑ i, F x i * v i := by
  rw [workCovector_apply, D04.inner_coordinates]

theorem covector_eq_work {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (F : E n → E n)
    (hc : CovectorIntegrable d (workCovector F)) (hw : WorkIntegrable d F) :
    covectorLineIntegral d (workCovector F) hc = workLineIntegral d F hw := rfl

theorem covector_coordinates {n} (α : E n → E n →L[ℝ] ℝ) (x v : E n) :
    α x v = ∑ i, α x (D04.standardBasis n i) * v i := by
  have hv : v = ∑ i : Fin n, v i • D04.standardBasis n i := by
    simpa [D04.standardBasis, EuclideanSpace.basisFun_repr] using
      ((D04.standardBasis n).sum_repr v).symm
  calc
    α x v = α x (∑ i : Fin n, v i • D04.standardBasis n i) := congrArg (α x) hv
    _ = ∑ i, α x (D04.standardBasis n i) * v i := by simp [mul_comm]

theorem workCovector_covectorVector {n} (α : E n → E n →L[ℝ] ℝ) (x : E n) :
    workCovector (covectorVector α) x = α x := by
  ext v
  rw [workCovector_coordinates, covector_coordinates]
  rfl

theorem covectorLineIntegral_eq_coordinates {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (α : E n → E n →L[ℝ] ℝ)
    (hc : CovectorIntegrable d α) (hw : WorkIntegrable d (covectorVector α)) :
    covectorLineIntegral d α hc = workLineIntegral d (covectorVector α) hw := by
  change (∑ i, realIntegral _ (hc i)) = ∑ i, realIntegral _ (hw i)
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨hg, he⟩ := riemann_congr (hc i) (g := fun t => inner ℝ (covectorVector α (γ t)) (d.velocity i t)) (by
    intro t _
    exact (congrArg (fun L : E n →L[ℝ] ℝ => L (d.velocity i t))
      (workCovector_covectorVector α (γ t))).symm)
  exact he.symm

theorem pieceIntegrable_degenerate {n a} {γ : IntervalPath n a a}
    (d : PiecewiseC1Data γ) (H : E n → E n → ℝ) : PieceIntegrable d H := by
  have : IsEmpty (Fin d.partition.n) :=
    Fin.isEmpty_iff.mpr (n_eq_zero_of_degenerate a d.partition)
  intro i
  exact isEmptyElim i

theorem scalarLineIntegral_degenerate {n a} {γ : IntervalPath n a a}
    (d : PiecewiseC1Data γ) (f : E n → ℝ) (h : ScalarIntegrable d f) :
    scalarLineIntegral d f h = 0 := pieceIntegral_degenerate d _ h

theorem covectorLineIntegral_degenerate {n a} {γ : IntervalPath n a a}
    (d : PiecewiseC1Data γ) (α : E n → E n →L[ℝ] ℝ) (h : CovectorIntegrable d α) :
    covectorLineIntegral d α h = 0 := pieceIntegral_degenerate d _ h

end D04.C09
