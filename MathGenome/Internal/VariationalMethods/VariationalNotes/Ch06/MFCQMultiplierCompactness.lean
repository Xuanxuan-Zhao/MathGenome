import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.MFCQMultiplierCompactness
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.LICQMultiplierUniqueness
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

noncomputable section
universe u v w
namespace VariationalNotes.Ch06
open ContinuousLinearMap

def kktMultiplierSet : MFCQMultiplierCompactnessSpecs.kktMultiplierSetType :=
  @MFCQMultiplierCompactnessSpecs.kktMultiplierSet

/-- The multiplier equations and nonnegativity conditions are closed. -/
theorem kktMultiplierSet_isClosed
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X) :
    IsClosed (kktMultiplierSet U f g h x) := by
  classical
  change IsClosed {p : (I → ℝ) × (J → ℝ) |
    x ∈ feasibleSet U g h ∧ (∀ i, 0 ≤ p.1 i) ∧
    (∀ i, p.1 i * g i x = 0) ∧
    fderiv ℝ f x + (∑ i, p.1 i • fderiv ℝ (g i) x) +
      (∑ j, p.2 j • fderiv ℝ (h j) x) = 0}
  apply IsClosed.inter isClosed_const
  apply IsClosed.inter
  · change IsClosed {p : (I → ℝ) × (J → ℝ) | ∀ i, 0 ≤ p.1 i}
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (by fun_prop)
  apply IsClosed.inter
  · change IsClosed {p : (I → ℝ) × (J → ℝ) | ∀ i, p.1 i * g i x = 0}
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) continuous_const

/-- MFCQ bounds every coefficient of every normalized KKT pair. Evaluate
stationarity on its strict inward vector to bound the nonnegative coefficients,
then on preimages of equality coordinate vectors to bound the free coefficients. -/
theorem kktMultiplierSet_coordinate_bounds
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X)
    (hm : MFCQ U g h x) :
    ∃ (A : I → ℝ) (B : J → ℝ), ∀ p ∈ kktMultiplierSet U f g h x,
      (∀ i, |p.1 i| ≤ A i) ∧ (∀ j, |p.2 j| ≤ B j) := by
  classical
  obtain ⟨hx, hsurj, w, hw, hstrict⟩ := hm
  let A : I → ℝ := fun i =>
    if i ∈ activeSet g x then |fderiv ℝ f x w| / (-fderiv ℝ (g i) x w) else 0
  choose d hd using fun j : J => hsurj (Pi.single j 1)
  let B : J → ℝ := fun j => |fderiv ℝ f x (d j)| +
    ∑ i, A i * |fderiv ℝ (g i) x (d j)|
  refine ⟨A, B, ?_⟩
  intro p hp
  have hk : KKT U f g h x p.1 p.2 := hp
  have heval (v : X) : fderiv ℝ f x v +
      (∑ i, p.1 i * fderiv ℝ (g i) x v) +
      (∑ j, p.2 j * fderiv ℝ (h j) x v) = 0 := by
    simpa only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply] using
      congrArg (fun L : X →L[ℝ] ℝ => L v) hk.2.2.2
  have hinactive (i : I) (hi : i ∉ activeSet g x) : p.1 i = 0 :=
    kkt_inactive_multiplier U f g h x p.1 p.2 hk i hi
  have heqw (j : J) : fderiv ℝ (h j) x w = 0 := congrFun hw j
  have hsum : ∑ i, p.1 i * (-fderiv ℝ (g i) x w) = fderiv ℝ f x w := by
    have he := heval w
    simp only [heqw, mul_zero, Finset.sum_const_zero, add_zero] at he
    simp only [mul_neg, Finset.sum_neg_distrib]
    linarith
  have hnonneg (i : I) : 0 ≤ p.1 i * (-fderiv ℝ (g i) x w) := by
    by_cases hi : i ∈ activeSet g x
    · exact mul_nonneg (hk.2.1 i) (neg_pos.mpr (hstrict i hi)).le
    · simp [hinactive i hi]
  have hlam (i : I) : |p.1 i| ≤ A i := by
    rw [abs_of_nonneg (hk.2.1 i)]
    by_cases hi : i ∈ activeSet g x
    · dsimp [A]
      rw [ite_eq_left hi, le_div_iff₀ (neg_pos.mpr (hstrict i hi))]
      calc
        p.1 i * (-fderiv ℝ (g i) x w) ≤
            ∑ k, p.1 k * (-fderiv ℝ (g k) x w) :=
          Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i)
        _ = fderiv ℝ f x w := hsum
        _ ≤ |fderiv ℝ f x w| := le_abs_self _
    · simp [A, hi, hinactive i hi]
  refine ⟨hlam, ?_⟩
  intro j
  have hdj (k : J) : fderiv ℝ (h k) x (d j) = (Pi.single j 1 : J → ℝ) k :=
    congrFun (hd j) k
  have he : fderiv ℝ f x (d j) +
      (∑ i, p.1 i * fderiv ℝ (g i) x (d j)) + p.2 j = 0 := by
    simpa [hdj, Pi.single_apply] using heval (d j)
  have hnu : p.2 j = -(fderiv ℝ f x (d j) +
      ∑ i, p.1 i * fderiv ℝ (g i) x (d j)) := by linarith
  rw [hnu, abs_neg]
  calc
    |fderiv ℝ f x (d j) + ∑ i, p.1 i * fderiv ℝ (g i) x (d j)| ≤
        |fderiv ℝ f x (d j)| + |∑ i, p.1 i * fderiv ℝ (g i) x (d j)| :=
      abs_add_le _ _
    _ ≤ |fderiv ℝ f x (d j)| + ∑ i, |p.1 i * fderiv ℝ (g i) x (d j)| :=
      add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ B j := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hlam i) (abs_nonneg _)

theorem kktMultiplierSet_isCompact_of_mfcq :
    MFCQMultiplierCompactnessSpecs.kktMultiplierSet_isCompact_of_mfcq.{u,v,w} := by
  intro X _ _ I J _ _ U f g h x hm
  obtain ⟨A, B, hb⟩ := kktMultiplierSet_coordinate_bounds U f g h x hm
  have hc : IsCompact
      ((Set.pi Set.univ (fun i => Set.Icc (-A i) (A i))) ×ˢ
        (Set.pi Set.univ (fun j => Set.Icc (-B j) (B j)))) :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).prod
      (isCompact_univ_pi (fun _ => isCompact_Icc))
  apply hc.of_isClosed_subset (kktMultiplierSet_isClosed U f g h x)
  intro p hp
  obtain ⟨ha, hb⟩ := hb p hp
  constructor
  · intro i _
    exact abs_le.mp (ha i)
  · intro j _
    exact abs_le.mp (hb j)

theorem kktMultiplierSet_nonempty_isCompact_of_mfcq :
    MFCQMultiplierCompactnessSpecs.kktMultiplierSet_nonempty_isCompact_of_mfcq.{u,v,w} := by
  intro X _ _ _ I J _ _ U f g h x hs hmin hm
  obtain ⟨lam, nu, hk⟩ := kkt_of_mfcq U f g h x hs hmin hm
  exact ⟨⟨(lam, nu), hk⟩, kktMultiplierSet_isCompact_of_mfcq U f g h x hm⟩

theorem qualified_multiplier_sets :
    MFCQMultiplierCompactnessSpecs.qualified_multiplier_sets.{u,v,w} := by
  intro X _ _ _ I J _ _ U f g h x hs hmin
  constructor
  · intro hl
    obtain ⟨p, hp, _, hunique⟩ := existsUnique_kkt_of_licq U f g h x hs hmin hl
    exact ⟨p, hp, hunique⟩
  · exact kktMultiplierSet_nonempty_isCompact_of_mfcq U f g h x hs hmin

end VariationalNotes.Ch06
