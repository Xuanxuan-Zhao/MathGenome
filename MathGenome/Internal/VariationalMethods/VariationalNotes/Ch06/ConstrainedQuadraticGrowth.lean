import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.ConstrainedQuadraticGrowth
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.SmoothConstraintModels
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.TangentInclusion
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.UnconstrainedTests
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Push

noncomputable section
open Set Filter Asymptotics
open scoped Topology
universe u v w
namespace VariationalNotes.Ch06

/-- The stationary Taylor expansion along convergent normalized secants. -/
lemma normalizedSecondOrder
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {L : X → ℝ} {a d : X} {B : X →L[ℝ] X →L[ℝ] ℝ} {z : ℕ → X}
    (htwo : _root_.Specs.VariationalNotes.Ch06.TwiceFrechetAt L a B)
    (hzero : fderiv ℝ L a = 0)
    (hz : Tendsto z atTop (𝓝 a))
    (hd : Tendsto (fun n => ‖z n - a‖⁻¹ • (z n - a)) atTop (𝓝 d)) :
    Tendsto (fun n => (L (z n) - L a) / ‖z n - a‖ ^ 2) atTop
      (𝓝 ((1/2 : ℝ) * B d d)) := by
  have hr := ((secondOrderRemainder htwo).comp_tendsto hz).tendsto_div_nhds_zero
  have hc : Continuous (fun v : X => B v v) := by fun_prop
  have hb := (hc.tendsto d).comp hd
  have H := (hb.const_mul (1/2 : ℝ)).add hr
  simp only [add_zero] at H
  convert H using 1
  funext n
  simp only [Function.comp_apply, hzero, zero_apply, sub_zero,
    map_smul, smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- A compactness argument for an objective with a stationary lower support
function. Positivity is needed only on tangent directions with nonpositive
objective differential. This includes an empty unit tangent set. -/
lemma quadraticGrowth_of_tangent_hessian
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {S : Set X} {f L : X → ℝ} {a : X}
    {A : X →L[ℝ] ℝ} {B : X →L[ℝ] X →L[ℝ] ℝ}
    (hf : HasFDerivAt f A a)
    (htwo : _root_.Specs.VariationalNotes.Ch06.TwiceFrechetAt L a B)
    (hzero : fderiv ℝ L a = 0) (heq : L a = f a)
    (hle : ∀ x ∈ S, L x ≤ f x)
    (hpos : ∀ d ∈ VariationalNotes.ConvexGeometry.Specs.contingentTangent S a,
      A d ≤ 0 → d ≠ 0 → 0 < B d d) :
    ∃ c > 0, ∃ ρ > 0, ∀ x ∈ S,
      ‖x-a‖ < ρ → f a + c * ‖x-a‖ ^ 2 ≤ f x := by
  classical
  by_contra H
  push Not at H
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hbad (n : ℕ) := H (ε n) (hεpos n) (ε n) (hεpos n)
  choose z hz hsmall hbad using hbad
  have hne (n : ℕ) : z n ≠ a := by
    intro he
    have hh := hbad n
    simp [he] at hh
  have hrpos (n : ℕ) : 0 < ‖z n - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne n))
  have hr0 : Tendsto (fun n => ‖z n - a‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => (hsmall n).le) hε
  have hz0 : Tendsto z atTop (𝓝 a) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [dist_eq_norm] using hr0
  have hunit (n : ℕ) : ‖z n - a‖⁻¹ • (z n - a) ∈ Metric.sphere (0 : X) 1 := by
    simp [norm_smul, ne_of_gt (hrpos n)]
  obtain ⟨d, hdunit, σ, hσ, hd⟩ := (isCompact_sphere (0 : X) 1).tendsto_subseq hunit
  have hdne : d ≠ 0 := by intro he; simp [he] at hdunit
  have hzσ := hz0.comp hσ.tendsto_atTop
  have hrσ := hr0.comp hσ.tendsto_atTop
  have hd' : Tendsto (fun n => ‖z (σ n)-a‖⁻¹ • (z (σ n)-a)) atTop (𝓝 d) := hd
  have htan : d ∈ VariationalNotes.ConvexGeometry.Specs.contingentTangent S a :=
    ⟨z ∘ σ, (fun n => ‖z (σ n)-a‖), fun n => hz (σ n),
      fun n => hrpos (σ n), hrσ, hd'⟩
  have hfirst := tangent_difference_quotient_tendsto hf (fun n => hrpos (σ n)) hrσ hd'
  have hA : A d ≤ 0 := by
    have hb : Tendsto (fun n => ε (σ n) * ‖z (σ n)-a‖) atTop (𝓝 (0 : ℝ)) := by
      simpa using (hε.comp hσ.tendsto_atTop).mul hrσ
    apply le_of_tendsto_of_tendsto' hfirst hb
    intro n
    have hp := hrpos (σ n)
    have hh := hbad (σ n)
    rw [← div_eq_inv_mul]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hp := hpos d htan hA hdne
  have ht := normalizedSecondOrder htwo hzero hzσ hd'
  have hn : (1/2 : ℝ) * B d d ≤ 0 := by
    apply le_of_tendsto_of_tendsto' ht (hε.comp hσ.tendsto_atTop)
    intro n
    apply (div_le_iff₀ (sq_pos_of_pos (hrpos (σ n)))).mpr
    have hh := hbad (σ n)
    have hl := hle (z (σ n)) (hz (σ n))
    change L (z (σ n)) - L a ≤ ε (σ n) * ‖z (σ n)-a‖ ^ 2
    rw [heq]
    linarith
  linarith

/-- C² at a point supplies exactly the pointwise twice Fréchet
hypothesis used by the upstream Taylor remainder theorem. -/
lemma twiceFrechetAt_of_contDiffAt
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {L : X → ℝ} {a : X} (hL : ContDiffAt ℝ 2 L a) :
    _root_.Specs.VariationalNotes.Ch06.TwiceFrechetAt L a
      (fderiv ℝ (fderiv ℝ L) a) := by
  constructor
  · exact (hL.eventually (by norm_num)).mono fun x hx => hx.differentiableAt (by norm_num)
  · exact (hL.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt

/-- A scalar function bounded above by its base value on a set has a
nonpositive differential on every feasible-sequence tangent direction. -/
lemma tangent_differential_nonpos
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {S : Set X} {F : X → ℝ} {A : X →L[ℝ] ℝ} {a d : X}
    (hF : HasFDerivAt F A a) (hbound : ∀ x ∈ S, F x ≤ F a)
    (hd : d ∈ VariationalNotes.ConvexGeometry.Specs.contingentTangent S a) :
    A d ≤ 0 := by
  obtain ⟨z, t, hz, ht, ht0, hd⟩ := hd
  apply le_of_tendsto (tangent_difference_quotient_tendsto hF ht ht0 hd)
  exact Eventually.of_forall fun n => mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.mpr (ht n).le) (sub_nonpos.mpr (hbound (z n) (hz n)))

/-- Pointwise derivatives suffice for the linearized inequalities; the two
signs of each equality give its zero differential. -/
lemma tangent_linearized_of_differentiableAt
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    {U : Set X} {g : I → X → ℝ} {h : J → X → ℝ} {a d : X}
    (ha : a ∈ feasibleSet U g h)
    (hg : ∀ i, DifferentiableAt ℝ (g i) a)
    (hh : ∀ j, DifferentiableAt ℝ (h j) a)
    (hd : d ∈ constraintTangentCone U g h a) :
    d ∈ linearizedCone g h a := by
  constructor
  · funext j
    have hup := tangent_differential_nonpos (hh j).hasFDerivAt
      (fun x (hx : x ∈ feasibleSet U g h) => by rw [hx.2.2 j, ha.2.2 j]) hd
    have hlo := tangent_differential_nonpos (hh j).hasFDerivAt.neg
      (fun x (hx : x ∈ feasibleSet U g h) => by
        change -(h j x) ≤ -(h j a)
        rw [hx.2.2 j, ha.2.2 j]) hd
    change fderiv ℝ (h j) a d = 0
    simpa using le_antisymm hup (neg_nonpos.mp hlo)
  · intro i hi
    apply tangent_differential_nonpos (hg i).hasFDerivAt _ hd
    intro x hx
    change g i a = 0 at hi
    rw [hi]
    exact hx.2.1 i

theorem constrainedQuadraticGrowth : Specs.constrainedQuadraticGrowth.{u,v,w} := by
  intro X _ _ _ I J _ _ U f g h a lam nu hU hf hg hh hk hpos
  classical
  let L := lagrangian f g h lam nu
  have hL : ContDiffAt ℝ 2 L a :=
    (hf.add (ContDiffAt.sum (fun i (_ : i ∈ Finset.univ) => (hg i).const_smul (lam i)))).add
      (ContDiffAt.sum (fun j (_ : j ∈ Finset.univ) => (hh j).const_smul (nu j)))
  have hdf := (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hdg (i : I) := ((hg i).differentiableAt (by norm_num)).hasFDerivAt
  have hdh (j : J) := ((hh j).differentiableAt (by norm_num)).hasFDerivAt
  have hdL : fderiv ℝ L a = 0 := by
    have H := (hdf.add (HasFDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (hdg i).const_mul (lam i)))).add
      (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hdh j).const_mul (nu j)))
    change HasFDerivAt L _ a at H
    rw [H.fderiv]
    exact hk.2.2.2
  have heq : L a = f a := by
    have hsg : (∑ i, lam i * g i a) = 0 :=
      Finset.sum_eq_zero (fun i _ => hk.2.2.1 i)
    have hsh : (∑ j, nu j * h j a) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hk.1.2.2 j, mul_zero]
    change f a + (∑ i, lam i * g i a) + (∑ j, nu j * h j a) = f a
    rw [hsg, hsh, add_zero, add_zero]
  have hle (x : X) (hx : x ∈ feasibleSet U g h) : L x ≤ f x := by
    have hsg : (∑ i, lam i * g i x) ≤ 0 :=
      Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hk.2.1 i) (hx.2.1 i))
    have hsh : (∑ j, nu j * h j x) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hx.2.2 j, mul_zero]
    change f x + (∑ i, lam i * g i x) + (∑ j, nu j * h j x) ≤ f x
    rw [hsh, add_zero]
    linarith
  have hgrowth := quadraticGrowth_of_tangent_hessian hdf (twiceFrechetAt_of_contDiffAt hL)
    hdL heq hle (fun d hd hA hdne => hpos d
      ⟨tangent_linearized_of_differentiableAt hk.1
        (fun i => (hdg i).differentiableAt) (fun j => (hdh j).differentiableAt) hd, hA⟩ hdne)
  refine ⟨hgrowth, ?_⟩
  obtain ⟨c, hc, ρ, hρ, hbound⟩ := hgrowth
  refine ⟨ρ, hρ, fun x hx hxr hxa => ?_⟩
  have hb := hbound x hx hxr
  have hp : 0 < c * ‖x-a‖ ^ 2 :=
    mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxa)))
  linarith

end VariationalNotes.Ch06
