import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.SecondOrderNecessity
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.LICQMultiplierUniqueness
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.EqualityChart
import MathGenome.Internal.MultivariableAnalysis.D04.C05.CriticalConeNecessity
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Tactic.Linarith

open Set Filter
open scoped Topology ContDiff
noncomputable section
universe u v w
namespace VariationalNotes.Ch06

/-- Impose only the active constraints whose differential vanishes on `d`.
LICQ makes their joint equality map a submersion. The resulting two-sided C²
curve is feasible on the right; the remaining active derivatives are negative. -/
lemma critical_direction_feasible_curve
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ) (x d : X)
    (hU : IsOpen U) (hg : ∀ i, ContDiffOn ℝ 2 (g i) U)
    (hh : ∀ j, ContDiffOn ℝ 2 (h j) U) (hl : LICQ U g h x)
    (hd : d ∈ linearizedCone g h x) :
    ∃ γ : ℝ → X, γ 0 = x ∧ ContDiffAt ℝ 2 γ 0 ∧ HasDerivAt γ d 0 ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ feasibleSet U g h) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), (∀ j, h j (γ t) = 0) ∧
        ∀ i ∈ activeSet g x, fderiv ℝ (g i) x d = 0 → g i (γ t) = 0) := by
  classical
  let : CompleteSpace X := FiniteDimensional.complete ℝ X
  let A := {i : I // i ∈ activeSet g x ∧ fderiv ℝ (g i) x d = 0}
  let c : (A ⊕ J) → X → ℝ := Sum.elim (fun i : A => g i.val) h
  let l : (A ⊕ J) → X →L[ℝ] ℝ :=
    Sum.elim (fun i : A => fderiv ℝ (g i.val) x) (fun j => fderiv ℝ (h j) x)
  let B : X →L[ℝ] ((A ⊕ J) → ℝ) := ContinuousLinearMap.pi l
  let e : (A ⊕ J) → ({i // i ∈ activeSet g x} ⊕ J) :=
    Sum.map (fun i => ⟨i.val, i.property.1⟩) id
  have he : Function.Injective e := by
    apply Sum.map_injective.mpr
    constructor
    · intro a b hab
      exact Subtype.ext (congrArg (fun i : {i // i ∈ activeSet g x} => (i : I)) hab)
    · exact Function.injective_id
  have hli : LinearIndependent ℝ l := by
    have hfamily : l = (Sum.elim
        (fun i : {i // i ∈ activeSet g x} => fderiv ℝ (g i.val) x)
        (fun j : J => fderiv ℝ (h j) x)) ∘ e := by
      funext k
      cases k <;> rfl
    rw [hfamily]
    exact hl.2.comp e he
  have hsurj : Function.Surjective B := coordinateMap_surjective_of_linearIndependent l hli
  have hc : ContDiffOn ℝ 2 (fun y k => c k y) U := by
    apply contDiffOn_pi.mpr
    intro k
    cases k with
    | inl i => exact hg i.val
    | inr j => exact hh j
  have hc0 : (fun k => c k x) = 0 := by
    funext k
    cases k with
    | inl i => exact i.property.1
    | inr j => exact hl.1.2.2 j
  have hcD : HasFDerivAt (fun y k => c k y) B x := by
    apply hasFDerivAt_pi.mpr
    intro k
    cases k with
    | inl i =>
      exact (((hg i.val).contDiffAt (hU.mem_nhds hl.1.1)).differentiableAt
        (by norm_num)).hasFDerivAt
    | inr j =>
      exact (((hh j).contDiffAt (hU.mem_nhds hl.1.1)).differentiableAt
        (by norm_num)).hasFDerivAt
  have hBd : B d = 0 := by
    funext k
    cases k with
    | inl i => exact i.property.2
    | inr j => exact congrFun hd.1 j
  obtain ⟨R, hR, hgraph, hambient, hcurves⟩ :=
    EqualityChart.finiteTargetEqualityChart X ((A ⊕ J) → ℝ) 2 (by norm_num)
      U hU (fun y k => c k y) hc x hl.1.1 hc0 B hcD hsurj
  obtain ⟨ε, γ, hε, hγ0, hγC, hγD, hγF⟩ := hcurves ⟨d, hBd⟩
  have hinterval : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨by linarith, hε⟩
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ U ∧ (∀ k, c k (γ t) = 0) := by
    filter_upwards [hinterval] with t ht
    exact ⟨(hγF t ht).1, fun k => congrFun (hγF t ht).2 k⟩
  have hinequalities : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), g i (γ t) ≤ 0 := by
    intro i
    have hgi : HasFDerivAt (g i) (fderiv ℝ (g i) x) (γ 0) := by
      rw [hγ0]
      exact (((hg i).contDiffAt (hU.mem_nhds hl.1.1)).differentiableAt
        (by norm_num)).hasFDerivAt
    have hcomp : HasDerivAt (fun t => g i (γ t)) (fderiv ℝ (g i) x d) 0 :=
      hgi.comp_hasDerivAt 0 hγD
    by_cases hi : i ∈ activeSet g x
    · by_cases hz : fderiv ℝ (g i) x d = 0
      · exact (hnear.mono (fun t ht => (ht.2 (Sum.inl ⟨i, hi, hz⟩)).le)).filter_mono
          nhdsWithin_le_nhds
      · exact (eventually_neg_of_hasDerivAt hcomp
          (lt_of_le_of_ne (hd.2 i hi) hz) (by rw [hγ0]; exact hi)).mono
          (fun _ ht => ht.le)
    · have hslack : g i (γ 0) < 0 := by
        rw [hγ0]
        exact lt_of_le_of_ne (hl.1.2.1 i) hi
      exact ((hcomp.continuousAt.eventually (gt_mem_nhds hslack)).mono
        (fun _ ht => ht.le)).filter_mono nhdsWithin_le_nhds
  refine ⟨γ, hγ0, hγC.contDiffAt hinterval, hγD, ?_, ?_⟩
  · filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      eventually_all.mpr hinequalities] with t ht hgt
    exact ⟨ht.1, hgt, fun j => ht.2 (Sum.inr j)⟩
  · filter_upwards [hnear] with t ht
    exact ⟨(fun j => ht.2 (Sum.inr j)), fun i hi hz => ht.2 (Sum.inl ⟨i, hi, hz⟩)⟩

/-- Theorem `thm:licq-second-order-necessity`. No strict complementarity is
assumed, and active constraints with negative directional derivative are allowed. -/
theorem secondOrderNecessary_of_licq :
    SecondOrderNecessitySpecs.secondOrderNecessary_of_licq.{u,v,w} := by
  classical
  intro X _ _ _ I J _ _ U f g h x lam nu hU hf hg hh hmin hl hk d hd
  let L := Specs.lagrangian f g h lam nu
  have hL : ContDiffOn ℝ 2 L U :=
    (hf.add (ContDiffOn.sum (fun i (_ : i ∈ Finset.univ) =>
      (hg i).const_smul (lam i)))).add
        (ContDiffOn.sum (fun j (_ : j ∈ Finset.univ) => (hh j).const_smul (nu j)))
  have hdf := (hf.contDiffAt (hU.mem_nhds hl.1.1)).differentiableAt (by norm_num)
    |>.hasFDerivAt
  have hdg (i : I) := (hg i |>.contDiffAt (hU.mem_nhds hl.1.1)).differentiableAt
    (by norm_num) |>.hasFDerivAt
  have hdh (j : J) := (hh j |>.contDiffAt (hU.mem_nhds hl.1.1)).differentiableAt
    (by norm_num) |>.hasFDerivAt
  have hdL : HasFDerivAt L (0 : X →L[ℝ] ℝ) x := by
    have H := (hdf.add (HasFDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (hdg i).const_mul (lam i)))).add
        (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hdh j).const_mul (nu j)))
    rw [hk.2.2.2] at H
    exact H
  obtain ⟨γ, hγ0, hγ, hdγ, hfeas, hcoords⟩ :=
    critical_direction_feasible_curve U g h x d hU hg hh hl hd.1
  have hpositive : ∀ i, 0 < lam i → fderiv ℝ (g i) x d = 0 := by
    have heq := criticalCone_eq_positive_multipliers U f g h x lam nu hk
    exact (show d ∈ {d | d ∈ Specs.linearizedCone g h x ∧
        ∀ i, 0 < lam i → fderiv ℝ (g i) x d = 0} from heq ▸ hd).2
  have hLx : L x = f x := by
    have heq : (∑ j, nu j * h j x) = 0 :=
      Finset.sum_eq_zero (fun j _ => by rw [hl.1.2.2 j, mul_zero])
    simp only [L, Specs.lagrangian, Finset.sum_eq_zero (fun i _ => hk.2.2.1 i),
      heq, add_zero]
  have hvalues : ∀ᶠ t in 𝓝 (0 : ℝ), L (γ t) = f (γ t) := by
    filter_upwards [hcoords] with t ht
    have hineq : (∑ i, lam i * g i (γ t)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : lam i = 0
      · rw [hi, zero_mul]
      · have hp : 0 < lam i := lt_of_le_of_ne (hk.2.1 i) (Ne.symm hi)
        have ha : i ∈ activeSet g x := by
          change g i x = 0
          exact (mul_eq_zero.mp (hk.2.2.1 i)).resolve_left hi
        rw [ht.2 i ha (hpositive i hp), mul_zero]
    have heq : (∑ j, nu j * h j (γ t)) = 0 :=
      Finset.sum_eq_zero (fun j _ => by rw [ht.1 j, mul_zero])
    simp only [L, Specs.lagrangian, hineq, heq, add_zero]
  have htend : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝[Specs.feasibleSet U g h] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hfeas⟩
    simpa [hγ0] using hdγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hminL : ∀ᶠ t in 𝓝[>] (0 : ℝ), L (γ 0) ≤ L (γ t) := by
    filter_upwards [htend.eventually hmin, hvalues.filter_mono nhdsWithin_le_nhds]
      with t ht heq
    simpa only [hγ0, hLx, heq] using ht
  have hLat : ContDiffAt ℝ 2 L (γ 0) := by
    rw [hγ0]
    exact hL.contDiffAt (hU.mem_nhds hl.1.1)
  have hdLγ : deriv (L ∘ γ) 0 = 0 := by
    have H := (by rw [hγ0]; exact hdL : HasFDerivAt L 0 (γ 0)).comp_hasDerivAt 0 hdγ
    simpa using H.deriv
  have hnonneg := D04.CriticalCone.right_second_nonneg (hLat.comp 0 hγ) hdLγ hminL
  have hsecond := iteratedDeriv_vcomp_two hLat hγ
  rw [hγ0, hdγ.deriv, hdL.fderiv, zero_apply, add_zero] at hsecond
  rw [hsecond, iteratedFDeriv_two_apply] at hnonneg
  exact hnonneg

/-- Existence and uniqueness are supplied by the first-order LICQ theorem;
the preceding result applies to its unique pair. -/
theorem existsUnique_secondOrder_kkt_of_licq :
    SecondOrderNecessitySpecs.existsUnique_secondOrder_kkt_of_licq.{u,v,w} := by
  intro X _ _ _ I J _ _ U f g h x hU hf hg hh hmin hl
  have hs : Specs.SmoothConstraintData U f g h :=
    ⟨hU, hf.of_le (by norm_num), (fun i => (hg i).of_le (by norm_num)),
      fun j => (hh j).of_le (by norm_num)⟩
  obtain ⟨p, hp, _, hunique⟩ := existsUnique_kkt_of_licq U f g h x hs hmin hl
  exact ⟨p, hp, hunique,
    secondOrderNecessary_of_licq U f g h x p.1 p.2 hU hf hg hh hmin hl hp⟩

end VariationalNotes.Ch06
