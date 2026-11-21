import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.PoissonSchauder
import MathGenome.Internal.LinearPDE.P201.Elliptic.NewtonHessian
import MathGenome.Internal.LinearPDE.P201.Potential.DerivativesLiouville
import Mathlib.Basic.Real.Pointwise

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff Pointwise

namespace P201.Elliptic.PoissonSchauder
open P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation

/-- The ordinary bounded Hölder norm splits into its supremum and seminorm. -/
lemma holderNormOn_eq {n : ℕ} (α : ℝ) (g : Space n → ℝ) (s : Set (Space n)) :
    holderNormOn α g s = supNormOn g s + holderSeminormOn α g s := rfl

/-- The upstream C²,α norm uses exactly the derivative sums in the scaled norm. -/
lemma c2HolderNormOn_eq {n : ℕ} (α : ℝ) (u : Space n → ℝ) (s : Set (Space n)) :
    c2HolderNormOn α u s = supNormOn u s + firstDerivativeNormOn u s +
      secondDerivativeNormOn u s + secondDerivativeSeminormOn α u s := by
  simp only [c2HolderNormOn, firstDerivativeNormOn, secondDerivativeNormOn,
    secondDerivativeSeminormOn, holderNormOn_eq, Finset.sum_add_distrib,
    supNormOn, add_assoc]

/-- Distributional Laplacian of a C² function is its classical Laplacian. -/
lemma distributionLaplacian_regular {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ 2 u) :
    distributionLaplacian (regularDistribution (⊤ : Domain n) u) =
      regularDistribution (⊤ : Domain n) (laplacian u) := by
  have hd (i : Fin n) : Continuous (multiPartial u {i, i}) := by
    exact continuousOn_univ.mp
      (P102.U4.partialWord_contDiffOn (⊤ : Domain n) hu.contDiffOn
        (({i, i} : MultiIndex n).sort (· ≤ ·)) 0 (by simp)).continuousOn
  have he (i : Fin n) : distributionDerivative {i, i}
      (regularDistribution (⊤ : Domain n) u) =
      regularDistribution (⊤ : Domain n) (multiPartial u {i, i}) :=
    P102.U4.derivative_classicalCompatibility n ℝ ⊤ {i, i} u (by simpa using hu.contDiffOn)
  change (∑ i : Fin n, distributionDerivative {i, i}
    (regularDistribution (⊤ : Domain n) u)) = _
  simp_rw [he]
  ext φ
  simp only [sum_apply]
  rw [P102.U4.regular_pairing n ℝ ⊤ _
    ((continuous_finsetSum _ (fun i _ => hd i)).locallyIntegrable.locallyIntegrableOn _)]
  simp_rw [P102.U4.regular_pairing n ℝ ⊤ _ ((hd _).locallyIntegrable.locallyIntegrableOn _)]
  simp only [TopologicalSpace.Opens.coe_top, setIntegral_univ]
  simp_rw [Finset.sum_mul]
  exact (integral_finsetSum _ fun i _ =>
    (hd i).locallyIntegrable.integrable_smul_right_of_hasCompactSupport
      φ.continuous φ.hasCompactSupport).symm

/-- The Newtonian potential of compact Hölder data solves the Poisson equation
pointwise, including in dimension one and for the logarithmic kernel. -/
theorem potential_equation : PotentialEquationStatement := by
  intro n hn α hα hα1 F hc hF
  have hcont := P201.Elliptic.HolderCancellation.holder_continuous hα hF
  have hS := P201.Elliptic.NewtonHessian.regularDistribution_compactSupport_of_continuous hc hcont
  obtain ⟨R, hR, hsupp⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Space n)
  obtain ⟨C, hC, hest⟩ := P201.Elliptic.NewtonHessian.potentialEstimate hn α hα hα1
    (∅ : Set (Space n)) Bornology.isBounded_empty 0 R hR
  have hw := hest F hc hsupp hF
  have hw2 : ContDiff ℝ 2 (holderPotential F) := hw.1.1
  have hL : Continuous (laplacian (holderPotential F)) := by
    apply continuous_finsetSum
    intro i _
    exact continuousOn_univ.mp
      (P102.U4.partialWord_contDiffOn (⊤ : Domain n) hw2.contDiffOn
        (({i, i} : MultiIndex n).sort (· ≤ ·)) 0 (by simp)).continuousOn
  have heq : -(distributionLaplacian
      (regularDistribution (⊤ : Domain n) (holderPotential F))) =
      regularDistribution (⊤ : Domain n) F := by
    rw [P201.Elliptic.NewtonHessian.regular_holderPotential_eq_rightCompactConvolution hn hc hcont hS]
    exact P201.newtonDistributionEquation n hn (regularDistribution (⊤ : Domain n) F) hS
  rw [distributionLaplacian_regular hw2] at heq
  have hneg : -(regularDistribution (⊤ : Domain n) (laplacian (holderPotential F))) =
      regularDistribution (⊤ : Domain n) (fun x => -laplacian (holderPotential F) x) := by
    ext φ
    simp only [neg_apply]
    rw [P102.U4.regular_pairing n ℝ ⊤ _ (hL.locallyIntegrable.locallyIntegrableOn _),
      P102.U4.regular_pairing n ℝ ⊤ (fun x => -laplacian (holderPotential F) x)
        (hL.neg.locallyIntegrable.locallyIntegrableOn _)]
    simp only [neg_mul, integral_neg]
  rw [hneg] at heq
  have hae := (P102.U4.regular_injectivity n ℝ ⊤ _ _
    (hL.neg.locallyIntegrable.locallyIntegrableOn _)
    (hcont.locallyIntegrable.locallyIntegrableOn _)).mp heq
  have hp := MeasureTheory.Measure.eq_of_ae_eq (μ := volume)
    (by simpa using hae) hL.neg hcont
  intro x
  exact congrFun hp x


lemma isHolderOn_mono {n : ℕ} {α : ℝ} {f : Space n → ℝ} {s t : Set (Space n)}
    (h : IsHolderOn α f t) (hst : s ⊆ t) : IsHolderOn α f s := by
  rcases h with ⟨M, H, hM, hH, hb, hh⟩
  exact ⟨M, H, hM, hH, fun x hx => hb x (hst hx),
    fun x hx y hy => hh x (hst hx) y (hst hy)⟩

lemma isHolderOn_congr {n : ℕ} {α : ℝ} {f g : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) (heq : EqOn g f s) : IsHolderOn α g s := by
  rcases hf with ⟨M, H, hM, hH, hb, hh⟩
  exact ⟨M, H, hM, hH, fun x hx => by rw [heq hx]; exact hb x hx,
    fun x hx y hy => by rw [heq hx, heq hy]; exact hh x hx y hy⟩

lemma isHolderOn_add {n : ℕ} {α : ℝ} {f g : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) (hg : IsHolderOn α g s) : IsHolderOn α (f + g) s := by
  rcases hf with ⟨M, H, hM, hH, hb, hh⟩
  rcases hg with ⟨N, J, hN, hJ, hc, hj⟩
  refine ⟨M + N, H + J, add_nonneg hM hN, add_nonneg hH hJ, ?_, ?_⟩
  · intro x hx
    exact (norm_add_le _ _).trans (add_le_add (hb x hx) (hc x hx))
  · intro x hx y hy
    calc
      ‖(f + g) x - (f + g) y‖ = ‖(f x - f y) + (g x - g y)‖ := by congr 1; simp; ring
      _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
      _ ≤ H * dist x y ^ α + J * dist x y ^ α := add_le_add (hh x hx y hy) (hj x hx y hy)
      _ = _ := by ring

/-- Bounded Lipschitz functions on any set are bounded Hölder for 0 ≤ α ≤ 1. -/
lemma isHolderOn_of_bounded_lipschitz {n : ℕ} {α : ℝ} {g : Space n → ℝ}
    {s : Set (Space n)} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hg : IsBoundedOn g s)
    {L : NNReal} (hL : LipschitzOnWith L g s) : IsHolderOn α g s := by
  rcases hg with ⟨M, hM, hbound⟩
  refine ⟨M, max (L : ℝ) (2 * M), hM,
    le_trans L.coe_nonneg (le_max_left _ _), hbound, ?_⟩
  intro x hx y hy
  by_cases hd : dist x y ≤ 1
  · calc
      ‖g x - g y‖ ≤ (L : ℝ) * dist x y := by simpa only [dist_eq_norm] using hL.dist_le_mul x hx y hy
      _ ≤ (L : ℝ) * dist x y ^ α :=
        mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one dist_nonneg hd hα1) L.coe_nonneg
      _ ≤ max (L : ℝ) (2 * M) * dist x y ^ α :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
  · calc
      ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hbound x hx, hbound y hy]
      _ ≤ (2 * M) * dist x y ^ α :=
        le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (not_le.mp hd).le hα)
      _ ≤ max (L : ℝ) (2 * M) * dist x y ^ α :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)

/-- The cutoff product is globally Hölder even if f has no regularity outside s.
The cutoff vanishes on the complement; no zero extension certificate is assumed. -/
lemma cutoff_product_holder {n : ℕ} {α : ℝ} {χ f : Space n → ℝ} {s : Set (Space n)}
    (hχ : IsHolder α χ) (hf : IsHolderOn α f s) (hz : ∀ x ∉ s, χ x = 0) :
    IsHolder α (fun x => χ x * f x) := by
  rcases hχ with ⟨P, Q, hP, hQ, hbχ, hhχ⟩
  rcases hf with ⟨M, H, hM, hH, hbf, hhf⟩
  have hbound (x : Space n) : ‖χ x * f x‖ ≤ P * M := by
    by_cases hx : x ∈ s
    · rw [norm_mul]
      exact mul_le_mul (hbχ x) (hbf x hx) (norm_nonneg _) hP
    · simp [hz x hx, mul_nonneg hP hM]
  have hin (x : Space n) (hx : x ∈ s) (y : Space n) :
      ‖χ x * f x - χ y * f y‖ ≤ (P * H + Q * M) * dist x y ^ α := by
    by_cases hy : y ∈ s
    · calc
        _ = ‖χ x * (f x - f y) + (χ x - χ y) * f y‖ := by congr 1; ring
        _ ≤ ‖χ x‖ * ‖f x - f y‖ + ‖χ x - χ y‖ * ‖f y‖ := by
          simpa only [norm_mul] using norm_add_le (χ x * (f x - f y)) ((χ x - χ y) * f y)
        _ ≤ P * (H * dist x y ^ α) + (Q * dist x y ^ α) * M :=
          add_le_add (mul_le_mul (hbχ x) (hhf x hx y hy) (norm_nonneg _) hP)
            (mul_le_mul (hhχ x y) (hbf y hy) (norm_nonneg _) (by positivity))
        _ = _ := by ring
    · have hcx : ‖χ x‖ ≤ Q * dist x y ^ α := by simpa [hz y hy] using hhχ x y
      calc
        _ = ‖χ x‖ * ‖f x‖ := by simp [hz y hy, norm_mul]
        _ ≤ (Q * dist x y ^ α) * M := mul_le_mul hcx (hbf x hx) (norm_nonneg _) (by positivity)
        _ ≤ (P * H + Q * M) * dist x y ^ α := by
          have hp := mul_nonneg (mul_nonneg hP hH)
            (Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α)
          nlinarith
  refine ⟨P * M, P * H + Q * M, mul_nonneg hP hM,
    add_nonneg (mul_nonneg hP hH) (mul_nonneg hQ hM), hbound, ?_⟩
  intro x y
  by_cases hx : x ∈ s
  · exact hin x hx y
  by_cases hy : y ∈ s
  · simpa only [norm_sub_rev, dist_comm] using hin y hy x
  · simp only [hz x hx, hz y hy, zero_mul, sub_self, norm_zero]
    exact mul_nonneg (add_nonneg (mul_nonneg hP hH) (mul_nonneg hQ hM))
      (Real.rpow_nonneg dist_nonneg α)

/-- The source equation makes the localized remainder harmonic wherever F=f. -/
lemma harmonic_remainder {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (V : Domain n) {u f F : Space n → ℝ} (hu : ContDiffOn ℝ 2 u V)
    (heq : ∀ x ∈ V, -laplacian u x = f x)
    (hc : HasCompactSupport F) (hF : IsHolder α F) (hagree : EqOn F f V) :
    P201.MeanValues.IsHarmonic V (u - holderPotential F) := by
  obtain ⟨R, hR, hsupp⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Space n)
  obtain ⟨C, hC, hest⟩ := P201.Elliptic.NewtonHessian.potentialEstimate hn α hα hα1
    (∅ : Set (Space n)) Bornology.isBounded_empty 0 R hR
  have hw := (hest F hc hsupp hF).1.1
  refine ⟨hu.sub hw.contDiffOn, ?_⟩
  intro x hx
  have hux : ContDiffAt ℝ 2 u x := (hu x hx).contDiffAt (V.isOpen.mem_nhds hx)
  have hwx : ContDiffAt ℝ 2 (holderPotential F) x := hw.contDiffAt
  rw [P201.MeanValues.laplacian_bridge (u - holderPotential F) x (hux.sub hwx),
    hux.laplacian_sub hwx, ← P201.MeanValues.laplacian_bridge _ _ hux,
    ← P201.MeanValues.laplacian_bridge _ _ hwx]
  have hpot := potential_equation hn α hα hα1 F hc hF x
  have huq := heq x hx
  have hFq := hagree hx
  linarith


/-- Coordinate differentiation is additive up to the available finite order,
locally on the open domain. This does not assume global smoothness. -/
lemma partialWord_add_on {n N : ℕ} (Ω : Domain n) {u v : Space n → ℝ}
    (hu : ContDiffOn ℝ (N : ℕ) u Ω) (hv : ContDiffOn ℝ (N : ℕ) v Ω)
    (l : List (Fin n)) (hl : l.length ≤ N) :
    EqOn (P102.U4.partialWord (u + v) l)
      (P102.U4.partialWord u l + P102.U4.partialWord v l) Ω := by
  induction l with
  | nil => intro x hx; rfl
  | cons i l ih =>
    intro x hx
    have hlen : 1 + l.length ≤ N := by simpa [List.length_cons, Nat.add_comm] using hl
    have hu1 := P102.U4.partialWord_contDiffOn Ω hu l 1 hlen
    have hv1 := P102.U4.partialWord_contDiffOn Ω hv l 1 hlen
    have heu : DifferentiableAt ℝ (P102.U4.partialWord u l) x :=
      ((hu1 x hx).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by norm_num)
    have hev : DifferentiableAt ℝ (P102.U4.partialWord v l) x :=
      ((hv1 x hx).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by norm_num)
    have heq : P102.U4.partialWord (u + v) l =ᶠ[𝓝 x]
        P102.U4.partialWord u l + P102.U4.partialWord v l :=
      mem_of_superset (Ω.isOpen.mem_nhds hx) fun y hy => ih (by omega) hy
    change fderiv ℝ (P102.U4.partialWord (u + v) l) x _ = _
    rw [heq.fderiv_eq, fderiv_add heu hev]
    rfl

lemma smooth_holder_on_compact_convex {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (Ω : Domain n) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ (3 : ℕ) u Ω) {s : Set (Space n)}
    (hs : IsCompact s) (hconv : Convex ℝ s) (hsub : s ⊆ (Ω : Set _)) :
    ∀ i j : Fin n, IsHolderOn α (multiPartial u {i, j}) s := by
  intro i j
  have hd : ContDiffOn ℝ 1 (multiPartial u {i, j}) Ω :=
    P102.U4.partialWord_contDiffOn Ω hu (({i, j} : MultiIndex n).sort (· ≤ ·)) 1 (by simp)
  obtain ⟨L, hL⟩ := (hd.mono hsub).exists_lipschitzOnWith (by norm_num) hconv hs
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn (hd.continuousOn.mono hsub)
  apply isHolderOn_of_bounded_lipschitz hα hα1 _ hL
  exact ⟨max M 0, le_max_right _ _, fun x hx => (hM x hx).trans (le_max_left _ _)⟩

/-- The qualitative conclusion, with no boundedness assumption on all of Ω. -/
theorem local_regularity : LocalRegularityStatement := by
  intro n hn α hα hα1 Ω u f hu hf heq
  refine ⟨hu, ?_⟩
  intro x hx
  obtain ⟨R, hR, hRΩ, hfR⟩ := hf x hx
  let χ : ContDiffBump x :=
    { rIn := R / 4
      rOut := R / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let F : Space n → ℝ := fun y => χ y * f y
  have hχsupp : tsupport χ ⊆ ball x R := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by dsimp [χ]; linarith)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    χ.hasCompactSupport (χ.contDiff : ContDiff ℝ (1 : ℕ) (χ : Space n → ℝ)) (by norm_num)
  have hχ : IsHolder α (χ : Space n → ℝ) :=
    P201.Elliptic.NewtonHessian.isHolder_of_bounded_lipschitz hα.le hα1.le
      (χ.contDiff : ContDiff ℝ (1 : ℕ) (χ : Space n → ℝ)).continuous χ.hasCompactSupport hL
  have hF : IsHolder α F := cutoff_product_holder hχ hfR (fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hχsupp h)))
  have hFc : HasCompactSupport F := χ.hasCompactSupport.mul_right
  let V : Domain n := ⟨ball x (R / 4), isOpen_ball⟩
  have hVΩ : (V : Set (Space n)) ⊆ (Ω : Set _) :=
    (ball_subset_ball (by linarith : R / 4 ≤ R)).trans hRΩ
  have hagree : EqOn F f V := by
    intro y hy
    change χ y * f y = f y
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
  have hv := harmonic_remainder hn hα hα1 V (hu.mono hVΩ)
    (fun y hy => heq y (hVΩ hy)) hFc hF hagree
  have hvSmooth : ContDiffOn ℝ (⊤ : ℕ∞) (u - holderPotential F) V :=
    P201.MeanValues.sphere_mean_implies_contDiffOn hn V _ hv.1.continuousOn
      (fun a r hr hball => (P201.MeanValues.mean_values hn V _ hv a r hr hball).1)
  have hsmall : closedBall x (R / 8) ⊆ (V : Set (Space n)) :=
    closedBall_subset_ball (by linarith)
  have hvHolder := smooth_holder_on_compact_convex hα.le hα1.le V
    (hvSmooth.of_le (by simp) : ContDiffOn ℝ (3 : ℕ) (u - holderPotential F) V)
    (isCompact_closedBall x (R / 8)) (convex_closedBall x (R / 8)) hsmall
  obtain ⟨S, hS, hsupp⟩ := hFc.isBounded.subset_closedBall_lt 0 (0 : Space n)
  obtain ⟨C, hC, hest⟩ := P201.Elliptic.NewtonHessian.potentialEstimate hn α hα hα1
    (closedBall x (R / 8)) isBounded_closedBall 0 S hS
  have hw := (hest F hFc hsupp hF).1
  have hpartial (i j : Fin n) : EqOn (multiPartial u {i, j})
      (multiPartial (u - holderPotential F) {i, j} + multiPartial (holderPotential F) {i, j}) V := by
    have ha := partialWord_add_on V hv.1 hw.1.contDiffOn
      (({i, j} : MultiIndex n).sort (· ≤ ·)) (by simp)
    have hfunc : (u - holderPotential F) + holderPotential F = u := by ext y; simp
    rw [hfunc] at ha
    exact ha
  refine ⟨R / 8, by positivity, (ball_subset_closedBall.trans hsmall).trans hVΩ, ?_⟩
  intro i j
  apply isHolderOn_congr (isHolderOn_mono
    (isHolderOn_add (hvHolder i j) (hw.2 _ isBounded_closedBall i j)) ball_subset_closedBall)
  intro y hy
  exact hpartial i j (hsmall (ball_subset_closedBall hy))


/-- A real supremum of nonnegative values is nonnegative, including the empty case. -/
lemma sSup_nonneg_of_nonneg {s : Set ℝ} (h : ∀ x ∈ s, 0 ≤ x) : 0 ≤ sSup s := by
  by_cases hb : BddAbove s
  · rcases s.eq_empty_or_nonempty with he | he
    · simp [he]
    · obtain ⟨x, hx⟩ := he
      exact (h x hx).trans (le_csSup hb hx)
  · rw [Real.sSup_of_not_bddAbove hb]

lemma supNormOn_nonneg {n : ℕ} (g : Space n → ℝ) (s : Set (Space n)) :
    0 ≤ supNormOn g s := by
  apply sSup_nonneg_of_nonneg
  rintro r ⟨x, hx, rfl⟩
  exact norm_nonneg _

lemma holderSeminormOn_nonneg {n : ℕ} (α : ℝ) (g : Space n → ℝ)
    (s : Set (Space n)) : 0 ≤ holderSeminormOn α g s := by
  apply sSup_nonneg_of_nonneg
  rintro r ⟨x, hx, y, hy, hxy, rfl⟩
  exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _)

lemma norm_le_supNormOn {n : ℕ} {g : Space n → ℝ} {s : Set (Space n)}
    (hg : IsBoundedOn g s) {x : Space n} (hx : x ∈ s) : ‖g x‖ ≤ supNormOn g s := by
  rcases hg with ⟨M, hM, hb⟩
  exact le_csSup ⟨M, by rintro r ⟨y, hy, rfl⟩; exact hb y hy⟩ ⟨x, hx, rfl⟩

lemma holder_bounds_by_normOn {n : ℕ} {α : ℝ} {g : Space n → ℝ}
    {s : Set (Space n)} (hg : IsHolderOn α g s) :
    0 ≤ holderNormOn α g s ∧
    (∀ x ∈ s, ‖g x‖ ≤ holderNormOn α g s) ∧
    ∀ x ∈ s, ∀ y ∈ s, ‖g x - g y‖ ≤ holderNormOn α g s * dist x y ^ α := by
  rcases hg with ⟨M, H, hM, hH, hb, hh⟩
  have hS := supNormOn_nonneg g s
  have hQ := holderSeminormOn_nonneg α g s
  rw [holderNormOn_eq]
  refine ⟨add_nonneg hS hQ, fun x hx =>
    (norm_le_supNormOn ⟨M, hM, hb⟩ hx).trans (le_add_of_nonneg_right hQ), ?_⟩
  intro x hx y hy
  by_cases hxy : x = y
  · subst y; simp; positivity
  have hd : 0 < dist x y ^ α := Real.rpow_pos_of_pos (dist_pos.mpr hxy) _
  have hq : ‖g x - g y‖ / dist x y ^ α ≤ holderSeminormOn α g s := by
    unfold holderSeminormOn
    have hbd : BddAbove {q : ℝ | ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ q = ‖g a - g b‖ / dist a b ^ α} := by
      refine ⟨H, ?_⟩
      rintro q ⟨a, ha, b, hb', hab, rfl⟩
      exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hab) _)).mpr (hh a ha b hb')
    exact le_csSup hbd ⟨x, hx, y, hy, hxy, rfl⟩
  exact ((div_le_iff₀ hd).mp hq).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hS) hd.le)

/-- Coordinate bounds control the actual operator norm in the Euclidean space. -/
lemma norm_linearMap_le_sum_coordinates {n : ℕ} (A : Space n →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ i : Fin n, ‖A (coordinate n i)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (s := Finset.univ) fun i _ => norm_nonneg _)
  intro x
  have he : ∑ i : Fin n, x i • coordinate n i = x :=
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  calc
    ‖A x‖ = ‖A (∑ i : Fin n, x i • coordinate n i)‖ := congrArg (fun z => ‖A z‖) he.symm
    _ = ‖∑ i : Fin n, x i • A (coordinate n i)‖ := by simp only [map_sum, map_smul]
    _ ≤ ∑ i : Fin n, ‖x i • A (coordinate n i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ‖x‖ * ‖A (coordinate n i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = (∑ i : Fin n, ‖A (coordinate n i)‖) * ‖x‖ := by simp only [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

/-- Interior derivative estimates give uniform supremum bounds on any set with
one fixed interior radius. The constant is chosen before the harmonic function. -/
lemma harmonic_word_bound {n : ℕ} (hn : 1 ≤ n) (l : List (Fin n))
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Domain n) (u : Space n → ℝ),
      P201.MeanValues.IsHarmonic V u → ∀ M : ℝ, 0 ≤ M →
      (∀ x ∈ V, ‖u x‖ ≤ M) → ∀ x : Space n,
      closedBall x r ⊆ (V : Set _) → ‖P102.U4.partialWord u l x‖ ≤ C * M := by
  obtain ⟨D, hD, hest⟩ := P201.DerivativesLiouville.interior_word_estimate hn l
  refine ⟨D / r ^ (n + l.length) * volume.real (ball (0 : Space n) r), by positivity, ?_⟩
  intro V u hu M hM hb x hball
  have hi : (∫ y in ball x r, ‖u y‖) ≤ volume.real (ball x r) * M := by
    have hnrm := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun y => ‖u y‖)
      (measure_ball_lt_top (x := x) (r := r))
      (fun y hy => by simpa only [norm_norm] using hb y (hball (ball_subset_closedBall hy)))
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, mul_comm] using hnrm)
  have hv : volume.real (ball x r) = volume.real (ball (0 : Space n) r) := by
    rw [P201.ballVolumeNormalization hn x r hr.le,
      P201.ballVolumeNormalization hn 0 r hr.le]
  calc
    _ ≤ D / r ^ (n + l.length) * ∫ y in ball x r, ‖u y‖ := hest V u hu x r hr hball
    _ ≤ D / r ^ (n + l.length) * (volume.real (ball x r) * M) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [hv]; ring


/-- Uniform bounds and all-pairs Hölder bounds for any coordinate derivative
of a harmonic function on a compact subset of its domain. -/
lemma harmonic_word_holder_bound {n : ℕ} (hn : 1 ≤ n) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (V : Domain n) (K : Set (Space n))
    (hK : IsCompact K) (hKV : K ⊆ (V : Set _)) (l : List (Fin n)) :
    ∃ A H : ℝ, 0 ≤ A ∧ 0 ≤ H ∧ ∀ (u : Space n → ℝ),
      P201.MeanValues.IsHarmonic V u → ∀ M : ℝ, 0 ≤ M →
      (∀ x ∈ V, ‖u x‖ ≤ M) →
      (∀ x ∈ K, ‖P102.U4.partialWord u l x‖ ≤ A * M) ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖P102.U4.partialWord u l x - P102.U4.partialWord u l y‖ ≤
          H * M * dist x y ^ α := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_thickening_subset_open V.isOpen hKV
  let T := thickening (δ / 2) K
  have hTV : T ⊆ (V : Set _) :=
    (thickening_mono (by linarith : δ / 2 ≤ δ) K).trans hδV
  have hKT : K ⊆ T := self_subset_thickening (by positivity) K
  have hball (x : Space n) (hx : x ∈ T) : closedBall x (δ / 4) ⊆ (V : Set _) := by
    obtain ⟨a, ha, hax⟩ := mem_thickening_iff.mp hx
    intro z hz
    apply hδV
    apply mem_thickening_iff.mpr
    refine ⟨a, ha, ?_⟩
    have hz' : dist z x ≤ δ / 4 := hz
    exact (dist_triangle z x a).trans_lt (by change dist x a < δ / 2 at hax; linarith)
  obtain ⟨A, hA, hAb⟩ := harmonic_word_bound hn l (δ / 4) (by positivity)
  choose B hB hBb using fun i : Fin n =>
    harmonic_word_bound hn (i :: l) (δ / 4) (by positivity)
  let L := ∑ i : Fin n, B i
  have hL : 0 ≤ L := Finset.sum_nonneg (s := Finset.univ) fun i _ => hB i
  let H := L * (δ / 2) ^ (1 - α) + (2 * A) / (δ / 2) ^ α
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨A, H, hA, hH, ?_⟩
  intro u hu M hM hb
  have hsup : ∀ x ∈ T, ‖P102.U4.partialWord u l x‖ ≤ A * M :=
    fun x hx => hAb V u hu M hM hb x (hball x hx)
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) u V :=
    P201.MeanValues.sphere_mean_implies_contDiffOn hn V u hu.1.continuousOn
      (fun a r hr hball => (P201.MeanValues.mean_values hn V u hu a r hr hball).1)
  have hd : ContDiffOn ℝ (1 : ℕ) (P102.U4.partialWord u l) V :=
    P102.U4.partialWord_contDiffOn V
      (hsmooth.of_le (by simp) : ContDiffOn ℝ (1 + l.length : ℕ) u V) l 1 le_rfl
  have hfder : ∀ x ∈ T, ‖fderiv ℝ (P102.U4.partialWord u l) x‖ ≤ L * M := by
    intro x hx
    calc
      _ ≤ ∑ i : Fin n, ‖fderiv ℝ (P102.U4.partialWord u l) x (coordinate n i)‖ :=
        norm_linearMap_le_sum_coordinates _
      _ ≤ ∑ i : Fin n, B i * M := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
        hBb i V u hu M hM hb x (hball x hx)
      _ = L * M := by simp only [L, Finset.sum_mul]
  refine ⟨fun x hx => hsup x (hKT hx), ?_⟩
  intro x hx y hy
  by_cases hnear : dist x y < δ / 2
  · have hsmall : ball x (δ / 2) ⊆ T := ball_subset_thickening hx _
    have hdiff : ‖P102.U4.partialWord u l x - P102.U4.partialWord u l y‖ ≤
        (L * M) * dist x y := by
      have hm := (convex_ball x (δ / 2)).norm_image_sub_le_of_norm_fderiv_le
        (fun z hz => ((hd z (hTV (hsmall hz))).contDiffAt
          (V.isOpen.mem_nhds (hTV (hsmall hz)))).differentiableAt (by norm_num))
        (fun z hz => hfder z (hsmall hz))
        (mem_ball_self (by positivity : 0 < δ / 2))
        (by simpa only [mem_ball, dist_comm] using hnear : y ∈ ball x (δ / 2))
      simpa only [norm_sub_rev, dist_eq_norm] using hm
    have hp : dist x y ≤ (δ / 2) ^ (1 - α) * dist x y ^ α := by
      calc
        dist x y = dist x y ^ (1 - α) * dist x y ^ α := by
          rw [← Real.rpow_add' dist_nonneg (by linarith : 0 < 1 - α + α).ne']; simp
        _ ≤ (δ / 2) ^ (1 - α) * dist x y ^ α :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow dist_nonneg hnear.le (by linarith))
            (Real.rpow_nonneg dist_nonneg _)
    calc
      _ ≤ (L * M) * dist x y := hdiff
      _ ≤ (L * M) * ((δ / 2) ^ (1 - α) * dist x y ^ α) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hL hM)
      _ ≤ H * M * dist x y ^ α := by
        have hz : 0 ≤ (2 * A / (δ / 2) ^ α) * M * dist x y ^ α := by positivity
        dsimp [H]; nlinarith
  · have hp : (δ / 2) ^ α ≤ dist x y ^ α :=
      Real.rpow_le_rpow (by positivity) (not_lt.mp hnear) hα.le
    have hpos : 0 < (δ / 2) ^ α := Real.rpow_pos_of_pos (by positivity) _
    calc
      _ ≤ ‖P102.U4.partialWord u l x‖ + ‖P102.U4.partialWord u l y‖ := norm_sub_le _ _
      _ ≤ (2 * A) * M := by linarith [hsup x (hKT hx), hsup y (hKT hy)]
      _ ≤ ((2 * A) / (δ / 2) ^ α) * M * dist x y ^ α := by
        have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (2 * A) * M / (δ / 2) ^ α)
        calc
          _ = ((2 * A) * M / (δ / 2) ^ α) * (δ / 2) ^ α := by field_simp
          _ ≤ ((2 * A) * M / (δ / 2) ^ α) * dist x y ^ α := hh
          _ = _ := by ring
      _ ≤ H * M * dist x y ^ α := by
        have hz := mul_nonneg (mul_nonneg hL (Real.rpow_nonneg (by positivity : 0 ≤ δ / 2) (1 - α)))
          (mul_nonneg hM (Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α))
        dsimp [H]; nlinarith


lemma boundedOn_of_continuousOn_compact {n : ℕ} {g : Space n → ℝ}
    {s : Set (Space n)} (hs : IsCompact s) (hg : ContinuousOn g s) : IsBoundedOn g s := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hg
  exact ⟨max M 0, le_max_right _ _, fun x hx => (hM x hx).trans (le_max_left _ _)⟩

lemma boundedOn_mono {n : ℕ} {g : Space n → ℝ} {s t : Set (Space n)}
    (hg : IsBoundedOn g t) (hst : s ⊆ t) : IsBoundedOn g s := by
  rcases hg with ⟨M, hM, hb⟩
  exact ⟨M, hM, fun x hx => hb x (hst hx)⟩

lemma c2HolderOn_of_global {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    (hu : IsC2HolderLoc α u) {s : Set (Space n)} (hs : Bornology.IsBounded s) :
    IsC2HolderOn α u s := by
  have hc : IsCompact (closure s) := isCompact_of_isClosed_isBounded isClosed_closure hs.closure
  refine ⟨hu.1.contDiffOn,
    boundedOn_mono (boundedOn_of_continuousOn_compact hc hu.1.continuous.continuousOn) subset_closure,
    ?_, hu.2 s hs⟩
  intro i
  have hd : Continuous (multiPartial u {i}) := continuousOn_univ.mp
    (P102.U4.partialWord_contDiffOn (⊤ : Domain n) hu.1.contDiffOn
      (({i} : MultiIndex n).sort (· ≤ ·)) 0 (by simp)).continuousOn
  exact boundedOn_mono (boundedOn_of_continuousOn_compact hc hd.continuousOn) subset_closure

lemma c2HolderNormOn_nonneg {n : ℕ} (α : ℝ) (u : Space n → ℝ)
    (s : Set (Space n)) : 0 ≤ c2HolderNormOn α u s := by
  unfold c2HolderNormOn
  exact add_nonneg (add_nonneg (supNormOn_nonneg u s)
    (Finset.sum_nonneg (s := Finset.univ) fun i _ => supNormOn_nonneg _ _))
    (Finset.sum_nonneg (s := Finset.univ) fun i _ => Finset.sum_nonneg (s := Finset.univ) fun j _ =>
      add_nonneg (supNormOn_nonneg _ _) (holderSeminormOn_nonneg _ _ _))

/-- Each component of the ordinary norm is controlled by the norm itself. -/
lemma c2HolderNormOn_components {n : ℕ} (α : ℝ) (u : Space n → ℝ)
    (s : Set (Space n)) :
    supNormOn u s ≤ c2HolderNormOn α u s ∧
    (∀ i : Fin n, supNormOn (multiPartial u {i}) s ≤ c2HolderNormOn α u s) ∧
    ∀ i j : Fin n, holderNormOn α (multiPartial u {i, j}) s ≤ c2HolderNormOn α u s := by
  have h1 : ∀ i : Fin n, 0 ≤ supNormOn (multiPartial u {i}) s := fun i => supNormOn_nonneg _ _
  have h2 : ∀ i j : Fin n, 0 ≤ holderNormOn α (multiPartial u {i, j}) s :=
    fun i j => add_nonneg (supNormOn_nonneg _ _) (holderSeminormOn_nonneg _ _ _)
  have hS1 : 0 ≤ ∑ i : Fin n, supNormOn (multiPartial u {i}) s := Finset.sum_nonneg (s := Finset.univ) fun i _ => h1 i
  have hS2 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (multiPartial u {i,j}) s :=
    Finset.sum_nonneg (s := Finset.univ) fun i _ => Finset.sum_nonneg (s := Finset.univ) fun j _ => h2 i j
  have heq : c2HolderNormOn α u s = supNormOn u s +
      (∑ i : Fin n, supNormOn (multiPartial u {i}) s) +
      ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (multiPartial u {i,j}) s := rfl
  rw [heq]
  refine ⟨by linarith, ?_, ?_⟩
  · intro i
    have hi := Finset.single_le_sum (fun i _ => h1 i) (Finset.mem_univ i)
    linarith [supNormOn_nonneg u s]
  · intro i j
    have hij := Finset.single_le_sum (fun j _ => h2 i j) (Finset.mem_univ j)
    have hi := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (s := Finset.univ) fun j _ => h2 i j) (Finset.mem_univ i)
    linarith [supNormOn_nonneg u s]

/-- Quantitative zero extension: the cutoff is fixed before the data. -/
lemma cutoff_product_norm {n : ℕ} (hn : 1 ≤ n) {α : ℝ} {χ : Space n → ℝ}
    (hχ : IsHolder α χ) (s : Set (Space n)) (hz : ∀ x ∉ s, χ x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Space n → ℝ, IsHolderOn α f s →
      IsHolder α (fun x => χ x * f x) ∧
      holderNorm α (fun x => χ x * f x) ≤ C * holderNormOn α f s := by
  obtain ⟨P, Q, hP, hQ, hbχ, hhχ⟩ := hχ
  refine ⟨2 * P + Q, by positivity, ?_⟩
  intro f hf
  have hN := holder_bounds_by_normOn hf
  let N := holderNormOn α f s
  have hN0 : 0 ≤ N := hN.1
  have hnew : IsHolderOn α f s := ⟨N, N, hN.1, hN.1, hN.2.1, hN.2.2⟩
  have hprod := cutoff_product_holder ⟨P, Q, hP, hQ, hbχ, hhχ⟩ hnew hz
  refine ⟨hprod, ?_⟩
  have hb : HolderBounds α (fun x => χ x * f x) (P * N) ((P + Q) * N) := by
    have hh := cutoff_product_holder ⟨P, Q, hP, hQ, hbχ, hhχ⟩ hnew hz
    -- Retain the explicit constants of the product proof via rescaling f.
    refine ⟨mul_nonneg hP hN.1, mul_nonneg (add_nonneg hP hQ) hN.1, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ s
      · rw [norm_mul]; exact mul_le_mul (hbχ x) (hN.2.1 x hx) (norm_nonneg _) hP
      · simp [hz x hx]; positivity
    · intro x y
      have hin (x y : Space n) (hx : x ∈ s) :
          ‖χ x * f x - χ y * f y‖ ≤ ((P + Q) * N) * dist x y ^ α := by
        by_cases hy : y ∈ s
        · calc
            _ = ‖χ y * (f x - f y) + (χ x - χ y) * f x‖ := by congr 1; ring
            _ ≤ ‖χ y‖ * ‖f x - f y‖ + ‖χ x - χ y‖ * ‖f x‖ := by
              simpa only [norm_mul] using norm_add_le (χ y * (f x - f y)) ((χ x - χ y) * f x)
            _ ≤ P * (N * dist x y ^ α) + (Q * dist x y ^ α) * N :=
              add_le_add (mul_le_mul (hbχ y) (hN.2.2 x hx y hy) (norm_nonneg _) hP)
                (mul_le_mul (hhχ x y) (hN.2.1 x hx) (norm_nonneg _) (by positivity))
            _ = _ := by ring
        · have hcx : ‖χ x‖ ≤ Q * dist x y ^ α := by simpa [hz y hy] using hhχ x y
          calc
            _ = ‖χ x‖ * ‖f x‖ := by simp [hz y hy, norm_mul]
            _ ≤ (Q * dist x y ^ α) * N := mul_le_mul hcx (hN.2.1 x hx) (norm_nonneg _) (by positivity)
            _ ≤ _ := by
              have hpos : 0 ≤ P * N * dist x y ^ α := by positivity
              nlinarith
      by_cases hx : x ∈ s
      · exact hin x y hx
      by_cases hy : y ∈ s
      · simpa only [norm_sub_rev, dist_comm] using hin y x hy
      · simp only [hz x hx, hz y hy, zero_mul, sub_self, norm_zero]; positivity
  calc
    _ ≤ P * N + (P + Q) * N := P201.Elliptic.HolderCancellation.holderNorm_le hn hb
    _ = _ := by dsimp [N]; ring


/-- Quantitative harmonic C²,α control on arbitrary compact sets, including
all pairs when the compact set or domain is disconnected. -/
lemma harmonic_c2_estimate {n : ℕ} (hn : 1 ≤ n) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (V : Domain n) (K : Set (Space n))
    (hK : IsCompact K) (hKV : K ⊆ (V : Set _)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Space n → ℝ,
      P201.MeanValues.IsHarmonic V u → ∀ M : ℝ, 0 ≤ M →
      (∀ x ∈ V, ‖u x‖ ≤ M) → ∀ s : Set (Space n), s ⊆ K →
      IsC2HolderOn α u s ∧ c2HolderNormOn α u s ≤ C * M := by
  choose A H hA hH hAb using fun i : Fin n =>
    harmonic_word_holder_bound hn hα hα1 V K hK hKV
      (({i} : MultiIndex n).sort (· ≤ ·))
  choose B J hB hJ hBb using fun i j : Fin n =>
    harmonic_word_holder_bound hn hα hα1 V K hK hKV
      (({i,j} : MultiIndex n).sort (· ≤ ·))
  let C := 1 + (∑ i : Fin n, A i) + ∑ i : Fin n, ∑ j : Fin n, (B i j + J i j)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg (s := Finset.univ) fun i _ => hA i))
      (Finset.sum_nonneg (s := Finset.univ) fun i _ => Finset.sum_nonneg (s := Finset.univ) fun j _ => add_nonneg (hB i j) (hJ i j))
  refine ⟨C, hC, ?_⟩
  intro u hu M hM hb s hs
  have hu0 : ∀ x ∈ s, ‖u x‖ ≤ M := fun x hx => hb x (hKV (hs hx))
  have hu1 (i : Fin n) : ∀ x ∈ s, ‖multiPartial u {i} x‖ ≤ A i * M :=
    fun x hx => (hAb i u hu M hM hb).1 x (hs hx)
  have hu2 (i j : Fin n) : IsHolderOn α (multiPartial u {i,j}) s :=
    ⟨B i j * M, J i j * M, mul_nonneg (hB i j) hM, mul_nonneg (hJ i j) hM,
      fun x hx => (hBb i j u hu M hM hb).1 x (hs hx),
      fun x hx y hy => (hBb i j u hu M hM hb).2 x (hs hx) y (hs hy)⟩
  refine ⟨⟨hu.1.mono (hs.trans hKV), ⟨M, hM, hu0⟩,
    fun i => ⟨A i * M, mul_nonneg (hA i) hM, hu1 i⟩, hu2⟩, ?_⟩
  have hzero : supNormOn u s ≤ M := P201.Elliptic.NewtonHessian.supNormOn_le hM hu0
  have hone (i : Fin n) : supNormOn (multiPartial u {i}) s ≤ A i * M :=
    P201.Elliptic.NewtonHessian.supNormOn_le (mul_nonneg (hA i) hM) (hu1 i)
  have htwo (i j : Fin n) : holderNormOn α (multiPartial u {i,j}) s ≤ (B i j + J i j) * M := by
    have hh := P201.Elliptic.NewtonHessian.holderNormOn_le
      (mul_nonneg (hB i j) hM) (mul_nonneg (hJ i j) hM)
      (fun x hx => (hBb i j u hu M hM hb).1 x (hs hx))
      (fun x hx y hy => (hBb i j u hu M hM hb).2 x (hs hx) y (hs hy))
    exact hh.trans_eq (by ring)
  calc
    _ ≤ M + (∑ i : Fin n, A i * M) + ∑ i : Fin n, ∑ j : Fin n, (B i j + J i j) * M :=
      add_le_add (add_le_add hzero (Finset.sum_le_sum (s := Finset.univ) fun i _ => hone i))
        (Finset.sum_le_sum (s := Finset.univ) fun i _ => Finset.sum_le_sum (s := Finset.univ) fun j _ => htwo i j)
    _ = C * M := by simp only [C, add_mul, one_mul, Finset.sum_mul]

/-- Finite supremum norms satisfy the triangle inequality on an arbitrary set. -/
lemma supNormOn_add_le {n : ℕ} {f g h : Space n → ℝ} {s : Set (Space n)}
    (hf : IsBoundedOn f s) (hg : IsBoundedOn g s) (hh : EqOn h (f + g) s) :
    supNormOn h s ≤ supNormOn f s + supNormOn g s := by
  apply P201.Elliptic.NewtonHessian.supNormOn_le
    (add_nonneg (supNormOn_nonneg _ _) (supNormOn_nonneg _ _))
  intro x hx
  rw [hh hx]
  exact (norm_add_le _ _).trans (add_le_add (norm_le_supNormOn hf hx) (norm_le_supNormOn hg hx))

lemma holderSeminormOn_le_of_bound {n : ℕ} {α : ℝ} {g : Space n → ℝ}
    {s : Set (Space n)} {H : ℝ} (hH : 0 ≤ H)
    (hh : ∀ x ∈ s, ∀ y ∈ s, ‖g x - g y‖ ≤ H * dist x y ^ α) :
    holderSeminormOn α g s ≤ H := by
  apply P201.Elliptic.NewtonHessian.real_sSup_le_of_nonneg hH
  rintro q ⟨x, hx, y, hy, hxy, rfl⟩
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) _)).mpr (hh x hx y hy)

lemma holder_diff_le_seminorm {n : ℕ} {α : ℝ} {g : Space n → ℝ}
    {s : Set (Space n)} (hg : IsHolderOn α g s) {x y : Space n}
    (hx : x ∈ s) (hy : y ∈ s) :
    ‖g x - g y‖ ≤ holderSeminormOn α g s * dist x y ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero]
    exact mul_nonneg (holderSeminormOn_nonneg _ _ _) (Real.rpow_nonneg dist_nonneg _)
  rcases hg with ⟨M, H, hM, hH, hb, hh⟩
  have hbd : BddAbove {q : ℝ | ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ q = ‖g a - g b‖ / dist a b ^ α} := by
    refine ⟨H, ?_⟩
    rintro q ⟨a, ha, b, hb', hab, rfl⟩
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hab) _)).mpr (hh a ha b hb')
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) _)).mp
    (le_csSup hbd ⟨x, hx, y, hy, hxy, rfl⟩)

lemma holderNormOn_add_le {n : ℕ} {α : ℝ} {f g h : Space n → ℝ}
    {s : Set (Space n)} (hf : IsHolderOn α f s) (hg : IsHolderOn α g s)
    (hh : EqOn h (f + g) s) :
    holderNormOn α h s ≤ holderNormOn α f s + holderNormOn α g s := by
  have hf0 : IsBoundedOn f s := by rcases hf with ⟨M,H,hM,hH,hb,hh⟩; exact ⟨M,hM,hb⟩
  have hg0 : IsBoundedOn g s := by rcases hg with ⟨M,H,hM,hH,hb,hh⟩; exact ⟨M,hM,hb⟩
  rw [holderNormOn_eq, holderNormOn_eq, holderNormOn_eq]
  have hzero := supNormOn_add_le hf0 hg0 hh
  have hsemi : holderSeminormOn α h s ≤ holderSeminormOn α f s + holderSeminormOn α g s := by
    apply holderSeminormOn_le_of_bound
      (add_nonneg (holderSeminormOn_nonneg _ _ _) (holderSeminormOn_nonneg _ _ _))
    intro x hx y hy
    rw [hh hx, hh hy]
    calc
      _ = ‖(f x - f y) + (g x - g y)‖ := by congr 1; simp; ring
      _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
      _ ≤ _ := by
        have := add_le_add (holder_diff_le_seminorm hf hx hy) (holder_diff_le_seminorm hg hx hy)
        nlinarith
  linarith

/-- Addition on an open domain uses genuine local classical derivatives. -/
lemma c2HolderOn_add {n : ℕ} {α : ℝ} (V : Domain n) {u v : Space n → ℝ}
    (hu : IsC2HolderOn α u V) (hv : IsC2HolderOn α v V) :
    IsC2HolderOn α (u + v) V ∧
    c2HolderNormOn α (u + v) V ≤ c2HolderNormOn α u V + c2HolderNormOn α v V := by
  have h1 (i : Fin n) : EqOn (multiPartial (u + v) {i})
      (multiPartial u {i} + multiPartial v {i}) V :=
    partialWord_add_on V hu.1 hv.1 (({i} : MultiIndex n).sort (· ≤ ·)) (by simp)
  have h2 (i j : Fin n) : EqOn (multiPartial (u + v) {i,j})
      (multiPartial u {i,j} + multiPartial v {i,j}) V :=
    partialWord_add_on V hu.1 hv.1 (({i,j} : MultiIndex n).sort (· ≤ ·)) (by simp)
  have hzero : IsBoundedOn (u + v) V := by
    refine ⟨supNormOn u V + supNormOn v V,
      add_nonneg (supNormOn_nonneg _ _) (supNormOn_nonneg _ _), ?_⟩
    intro x hx
    exact (norm_add_le _ _).trans
      (add_le_add (norm_le_supNormOn hu.2.1 hx) (norm_le_supNormOn hv.2.1 hx))
  have hone (i : Fin n) : IsBoundedOn (multiPartial (u + v) {i}) V := by
    refine ⟨supNormOn (multiPartial u {i}) V + supNormOn (multiPartial v {i}) V,
      add_nonneg (supNormOn_nonneg _ _) (supNormOn_nonneg _ _), ?_⟩
    intro x hx
    rw [h1 i hx]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_le_supNormOn (hu.2.2.1 i) hx) (norm_le_supNormOn (hv.2.2.1 i) hx))
  refine ⟨⟨hu.1.add hv.1, hzero, hone, fun i j =>
    isHolderOn_congr (isHolderOn_add (hu.2.2.2 i j) (hv.2.2.2 i j)) (h2 i j)⟩, ?_⟩
  have hsum := add_le_add
    (add_le_add (supNormOn_add_le hu.2.1 hv.2.1 (fun _ _ => rfl))
      (Finset.sum_le_sum (s := Finset.univ) fun i _ => supNormOn_add_le (hu.2.2.1 i) (hv.2.2.1 i) (h1 i)))
    (Finset.sum_le_sum (s := Finset.univ) fun i _ => Finset.sum_le_sum (s := Finset.univ) fun j _ =>
      holderNormOn_add_le (hu.2.2.2 i j) (hv.2.2.2 i j) (h2 i j))
  change c2HolderNormOn α (u + v) V ≤ _ at hsum
  exact hsum.trans_eq (by simp only [c2HolderNormOn, Finset.sum_add_distrib, supNormOn]; ring)


lemma c2HolderOn_mono {n : ℕ} {α : ℝ} {u : Space n → ℝ} {s t : Set (Space n)}
    (hu : IsC2HolderOn α u t) (hst : s ⊆ t) : IsC2HolderOn α u s :=
  ⟨hu.1.mono hst, boundedOn_mono hu.2.1 hst,
    fun i => boundedOn_mono (hu.2.2.1 i) hst,
    fun i j => isHolderOn_mono (hu.2.2.2 i j) hst⟩

lemma supNormOn_mono {n : ℕ} {g : Space n → ℝ} {s t : Set (Space n)}
    (hg : IsBoundedOn g t) (hst : s ⊆ t) : supNormOn g s ≤ supNormOn g t :=
  P201.Elliptic.NewtonHessian.supNormOn_le (supNormOn_nonneg _ _)
    (fun x hx => norm_le_supNormOn hg (hst hx))

lemma holderNormOn_mono {n : ℕ} {α : ℝ} {g : Space n → ℝ} {s t : Set (Space n)}
    (hg : IsHolderOn α g t) (hst : s ⊆ t) : holderNormOn α g s ≤ holderNormOn α g t := by
  rcases hg with ⟨M,H,hM,hH,hb,hh⟩
  exact add_le_add (supNormOn_mono ⟨M,hM,hb⟩ hst)
    (holderSeminormOn_le_of_bound (holderSeminormOn_nonneg _ _ _)
      (fun x hx y hy => holder_diff_le_seminorm ⟨M,H,hM,hH,hb,hh⟩ (hst hx) (hst hy)))

lemma c2HolderNormOn_mono {n : ℕ} {α : ℝ} {u : Space n → ℝ} {s t : Set (Space n)}
    (hu : IsC2HolderOn α u t) (hst : s ⊆ t) : c2HolderNormOn α u s ≤ c2HolderNormOn α u t :=
  add_le_add (add_le_add (supNormOn_mono hu.2.1 hst)
    (Finset.sum_le_sum (s := Finset.univ) fun i _ => supNormOn_mono (hu.2.2.1 i) hst))
    (Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) fun j _ => holderNormOn_mono (hu.2.2.2 i j) hst)

/-- The interior estimate with the constant chosen before the solution and data. -/
theorem interior_estimate : InteriorEstimateStatement := by
  intro n hn α hα hα1 Ω Ω' Ω'' hbounded hclosure hΩ
  let K := closure (Ω' : Set (Space n))
  have hK : IsCompact K := isCompact_of_isClosed_isBounded isClosed_closure hbounded.closure
  obtain ⟨χ, hχrange, V, hKV, hVΩ'', hχone⟩ :=
    P102.U4.cutoff n Ω'' ⟨K, hK⟩ hclosure
  have hVb : Bornology.IsBounded (V : Set (Space n)) :=
    χ.hasCompactSupport.isBounded.subset (fun x hx =>
      subset_tsupport _ (by rw [Function.mem_support, hχone x hx]; norm_num))
  obtain ⟨R, hR, hχR⟩ := χ.hasCompactSupport.isBounded.subset_closedBall_lt 0 (0 : Space n)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport χ.hasCompactSupport
    (χ.contDiff.of_le (by simp) : ContDiff ℝ (1 : ℕ) (χ : Space n → ℝ)) (by norm_num)
  have hχH : IsHolder α (χ : Space n → ℝ) :=
    P201.Elliptic.NewtonHessian.isHolder_of_bounded_lipschitz hα.le hα1.le
      χ.continuous χ.hasCompactSupport hL
  obtain ⟨D, hD, hcut⟩ := cutoff_product_norm hn hχH (Ω'' : Set (Space n))
    (fun x hx => χ.zero_on_compl hx)
  obtain ⟨P, hP, hpot⟩ := P201.Elliptic.NewtonHessian.potentialEstimate hn α hα hα1
    (V : Set (Space n)) hVb 0 R hR
  obtain ⟨A, hA, hharm⟩ := harmonic_c2_estimate hn hα hα1 V K hK hKV
  let Q := P * D
  have hQ : 0 ≤ Q := mul_nonneg hP hD
  refine ⟨A * (1 + Q) + Q + 1, by positivity, ?_⟩
  intro u f hu hf heq hub hfb
  let F : Space n → ℝ := fun x => χ x * f x
  have hFH : IsHolder α F := (hcut f hfb).1
  have hFc : HasCompactSupport F := χ.hasCompactSupport.mul_right
  have hFR : tsupport F ⊆ closedBall (0 : Space n) R := tsupport_mul_subset_left.trans hχR
  have hw := hpot F hFc hFR hFH
  have hwclass : IsC2HolderOn α (holderPotential F) V := c2HolderOn_of_global hw.1 hVb
  let N := holderNormOn α f Ω''
  let U := supNormOn u Ω''
  have hN : 0 ≤ N := (holder_bounds_by_normOn hfb).1
  have hU : 0 ≤ U := supNormOn_nonneg _ _
  have hwbound : c2HolderNormOn α (holderPotential F) V ≤ Q * N := by
    calc
      _ ≤ P * holderNorm α F := hw.2
      _ ≤ P * (D * N) := mul_le_mul_of_nonneg_left (hcut f hfb).2 hP
      _ = _ := by dsimp [Q]; ring
  have hwzero : ∀ x ∈ V, ‖holderPotential F x‖ ≤ Q * N := by
    intro x hx
    exact (norm_le_supNormOn hwclass.2.1 hx).trans
      ((c2HolderNormOn_components α (holderPotential F) V).1.trans hwbound)
  have hh : P201.MeanValues.IsHarmonic V (u - holderPotential F) :=
    harmonic_remainder hn hα hα1 V (hu.mono (hVΩ''.trans hΩ))
      (fun x hx => heq x (hΩ (hVΩ'' hx))) hFc hFH
      (fun x hx => by change χ x * f x = f x; rw [hχone x hx, one_mul])
  have hhbound : ∀ x ∈ V, ‖(u - holderPotential F) x‖ ≤ U + Q * N := by
    intro x hx
    exact (norm_sub_le _ _).trans
      (add_le_add (norm_le_supNormOn hub (hVΩ'' hx)) (hwzero x hx))
  have hsV : (Ω' : Set (Space n)) ⊆ (V : Set _) := subset_closure.trans hKV
  have hhest := hharm (u - holderPotential F) hh (U + Q * N)
    (by positivity) hhbound Ω' subset_closure
  have hwest : c2HolderNormOn α (holderPotential F) Ω' ≤ Q * N :=
    (c2HolderNormOn_mono hwclass hsV).trans hwbound
  have hadd := c2HolderOn_add Ω' hhest.1 (c2HolderOn_mono hwclass hsV)
  have hsum : (u - holderPotential F) + holderPotential F = u := by ext x; simp
  rw [hsum] at hadd
  refine ⟨hadd.1, ?_⟩
  calc
    c2HolderNormOn α u Ω' ≤ A * (U + Q * N) + Q * N :=
      hadd.2.trans (add_le_add hhest.2 hwest)
    _ ≤ (A * (1 + Q) + Q + 1) * (U + N) := by nlinarith [mul_nonneg hA hU, mul_nonneg hQ hU]


lemma supNormOn_bijOn_mul {n : ℕ} {s t : Set (Space n)}
    {φ : Space n → Space n} (hφ : Set.BijOn φ s t)
    {g h : Space n → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (heq : ∀ x ∈ s, h x = c * g (φ x)) :
    supNormOn h s = c * supNormOn g t := by
  unfold supNormOn
  have hs : {q : ℝ | ∃ x ∈ s, q = ‖h x‖} =
      c • {q : ℝ | ∃ x ∈ t, q = ‖g x‖} := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨‖g (φ x)‖, ⟨φ x, hφ.mapsTo hx, rfl⟩, ?_⟩
      simp [heq x hx, norm_mul, Real.norm_of_nonneg hc]
    · rintro ⟨q, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hφ.surjOn hy
      exact ⟨x, hx, by simp [heq x hx, norm_mul, Real.norm_of_nonneg hc]⟩
  rw [hs, Real.sSup_smul_of_nonneg hc]
  rfl

lemma holderSeminormOn_bijOn_mul {n : ℕ} {s t : Set (Space n)}
    {φ : Space n → Space n} (hφ : Set.BijOn φ s t)
    {g h : Space n → ℝ} {c r α : ℝ} (hc : 0 ≤ c) (hr : 0 < r)
    (hdist : ∀ x ∈ s, ∀ y ∈ s, dist (φ x) (φ y) = r * dist x y)
    (heq : ∀ x ∈ s, h x = c * g (φ x)) :
    holderSeminormOn α h s = (c * r ^ α) * holderSeminormOn α g t := by
  have hquot (x : Space n) (hx : x ∈ s) (y : Space n) (hy : y ∈ s)
      (hxy : x ≠ y) :
      ‖h x - h y‖ / dist x y ^ α =
        (c * r ^ α) * (‖g (φ x) - g (φ y)‖ / dist (φ x) (φ y) ^ α) := by
    rw [heq x hx, heq y hy, ← mul_sub, norm_mul, Real.norm_of_nonneg hc,
      hdist x hx y hy, Real.mul_rpow hr.le dist_nonneg]
    have hd : dist x y ^ α ≠ 0 := (Real.rpow_pos_of_pos (dist_pos.mpr hxy) _).ne'
    have hp : r ^ α ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
    field_simp
  unfold holderSeminormOn
  have hs : {q : ℝ | ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ q = ‖h x - h y‖ / dist x y ^ α} =
      (c * r ^ α) • {q : ℝ | ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧
        q = ‖g x - g y‖ / dist x y ^ α} := by
    ext q
    constructor
    · rintro ⟨x, hx, y, hy, hxy, rfl⟩
      refine ⟨‖g (φ x) - g (φ y)‖ / dist (φ x) (φ y) ^ α,
        ⟨φ x, hφ.mapsTo hx, φ y, hφ.mapsTo hy, fun h => hxy (hφ.injOn hx hy h), rfl⟩, ?_⟩
      exact (hquot x hx y hy hxy).symm
    · rintro ⟨q, ⟨x, hx, y, hy, hxy, rfl⟩, rfl⟩
      obtain ⟨u, hu, heu⟩ := hφ.surjOn hx
      obtain ⟨v, hv, hev⟩ := hφ.surjOn hy
      have huv : u ≠ v := by intro h; apply hxy; rw [← heu, ← hev, h]
      refine ⟨u, hu, v, hv, huv, ?_⟩
      simpa [heu, hev] using (hquot u hu v hv huv).symm
  rw [hs, Real.sSup_smul_of_nonneg (mul_nonneg hc (Real.rpow_nonneg hr.le _))]
  rfl
lemma isBoundedOn_mapsTo_mul {n : ℕ} {s t : Set (Space n)}
    {φ : Space n → Space n} (hφ : Set.MapsTo φ s t)
    {g h : Space n → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hg : IsBoundedOn g t) (heq : ∀ x ∈ s, h x = c * g (φ x)) :
    IsBoundedOn h s := by
  rcases hg with ⟨M, hM, hbound⟩
  refine ⟨c * M, mul_nonneg hc hM, ?_⟩
  intro x hx
  rw [heq x hx, norm_mul, Real.norm_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (hbound (φ x) (hφ hx)) hc

lemma isHolderOn_mapsTo_mul {n : ℕ} {s t : Set (Space n)}
    {φ : Space n → Space n} (hφ : Set.MapsTo φ s t)
    {g h : Space n → ℝ} {c r α : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hg : IsHolderOn α g t)
    (hdist : ∀ x ∈ s, ∀ y ∈ s, dist (φ x) (φ y) = r * dist x y)
    (heq : ∀ x ∈ s, h x = c * g (φ x)) :
    IsHolderOn α h s := by
  rcases hg with ⟨M, H, hM, hH, hbound, hholder⟩
  refine ⟨c * M, c * r ^ α * H, mul_nonneg hc hM,
    mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hr _)) hH, ?_, ?_⟩
  · intro x hx
    rw [heq x hx, norm_mul, Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (hbound (φ x) (hφ hx)) hc
  · intro x hx y hy
    calc
      ‖h x - h y‖ = c * ‖g (φ x) - g (φ y)‖ := by
        rw [heq x hx, heq y hy, ← mul_sub, norm_mul, Real.norm_of_nonneg hc]
      _ ≤ c * (H * dist (φ x) (φ y) ^ α) :=
        mul_le_mul_of_nonneg_left (hholder (φ x) (hφ hx) (φ y) (hφ hy)) hc
      _ = (c * r ^ α * H) * dist x y ^ α := by
        rw [hdist x hx y hy, Real.mul_rpow hr dist_nonneg]
        ring

lemma isHolderOn_of_bijOn_mul {n : ℕ} {s t : Set (Space n)}
    {φ : Space n → Space n} (hφ : Set.BijOn φ s t)
    {g h : Space n → ℝ} {c r α : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hh : IsHolderOn α h s)
    (hdist : ∀ x ∈ s, ∀ y ∈ s, dist (φ x) (φ y) = r * dist x y)
    (heq : ∀ x ∈ s, h x = c * g (φ x)) :
    IsHolderOn α g t := by
  rcases hh with ⟨M, H, hM, hH, hbound, hholder⟩
  have hra : 0 < r ^ α := Real.rpow_pos_of_pos hr _
  refine ⟨M / c, H / (c * r ^ α), div_nonneg hM hc.le,
    div_nonneg hH (mul_pos hc hra).le, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, hu, heu⟩ := hφ.surjOn hx
    rw [← heu, le_div_iff₀ hc]
    simpa [heq u hu, norm_mul, Real.norm_of_nonneg hc.le, mul_comm] using hbound u hu
  · intro x hx y hy
    obtain ⟨u, hu, heu⟩ := hφ.surjOn hx
    obtain ⟨v, hv, hev⟩ := hφ.surjOn hy
    rw [← heu, ← hev]
    apply (mul_le_mul_iff_right₀ hc).mp
    calc
      c * ‖g (φ u) - g (φ v)‖ = ‖h u - h v‖ := by
        rw [heq u hu, heq v hv, ← mul_sub, norm_mul, Real.norm_of_nonneg hc.le]
      _ ≤ H * dist u v ^ α := hholder u hu v hv
      _ = c * (H / (c * r ^ α) * dist (φ u) (φ v) ^ α) := by
        rw [hdist u hu v hv, Real.mul_rpow hr.le dist_nonneg]
        field_simp

lemma isHolderOn_bijOn_mul_iff {n : ℕ} {s t : Set (Space n)}
    {φ : Space n → Space n} (hφ : Set.BijOn φ s t)
    {g h : Space n → ℝ} {c r α : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hdist : ∀ x ∈ s, ∀ y ∈ s, dist (φ x) (φ y) = r * dist x y)
    (heq : ∀ x ∈ s, h x = c * g (φ x)) :
    IsHolderOn α h s ↔ IsHolderOn α g t :=
  ⟨fun hh => isHolderOn_of_bijOn_mul hφ hc hr hh hdist heq,
    fun hg => isHolderOn_mapsTo_mul hφ.mapsTo hc.le hr.le hg hdist heq⟩


lemma partialWord_affine_on {n N : ℕ} (Ω : Domain n) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ (N : ℕ) u Ω) (a : Space n) (r : ℝ)
    (l : List (Fin n)) (hl : l.length ≤ N) :
    EqOn (P102.U4.partialWord (fun y => u (a + r • y)) l)
      (fun y => r ^ l.length * P102.U4.partialWord u l (a + r • y))
      ((fun y => a + r • y) ⁻¹' Ω) := by
  induction l with
  | nil => intro x hx; simp [P102.U4.partialWord]
  | cons i l ih =>
    intro x hx
    have hlen : 1 + l.length ≤ N := by simpa [List.length_cons, Nat.add_comm] using hl
    have hu1 := P102.U4.partialWord_contDiffOn Ω hu l 1 hlen
    have heu : DifferentiableAt ℝ (P102.U4.partialWord u l) (a + r • x) :=
      ((hu1 _ hx).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by norm_num)
    have hA : HasFDerivAt (fun y : Space n => a + r • y)
        (r • ContinuousLinearMap.id ℝ (Space n)) x := by
      simpa using ((hasFDerivAt_id x).const_smul r).const_add a
    have hd := (heu.hasFDerivAt.comp x hA).const_mul (r ^ l.length)
    simp only [Function.comp_def] at hd
    have hopen : IsOpen ((fun y : Space n => a + r • y) ⁻¹' (Ω : Set _)) :=
      Ω.isOpen.preimage ((continuous_id.const_smul r).const_add a)
    have heq : P102.U4.partialWord (fun y => u (a + r • y)) l =ᶠ[𝓝 x]
        (fun y => r ^ l.length * P102.U4.partialWord u l (a + r • y)) :=
      mem_of_superset (hopen.mem_nhds hx) fun y hy => ih (by omega) hy
    change fderiv ℝ (P102.U4.partialWord (fun y => u (a + r • y)) l) x _ = _
    rw [heq.fderiv_eq, hd.fderiv]
    simp [List.length_cons, pow_succ, P102.U4.partialWord]
    ring

lemma multiPartial_affine_on {n N : ℕ} (Ω : Domain n) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ (N : ℕ) u Ω) (a : Space n) (r : ℝ)
    (m : MultiIndex n) (hm : m.card ≤ N) {y : Space n} (hy : a + r • y ∈ Ω) :
    multiPartial (fun z => u (a + r • z)) m y =
      r ^ m.card * multiPartial u m (a + r • y) := by
  simpa only [multiPartial, P102.U4.multiPartial, Multiset.length_sort] using
    partialWord_affine_on Ω hu a r (m.sort (· ≤ ·)) (by simpa using hm) hy

lemma laplacian_affine_on {n : ℕ} (Ω : Domain n) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) (a : Space n) (r : ℝ)
    {y : Space n} (hy : a + r • y ∈ Ω) :
    laplacian (fun z => u (a + r • z)) y = r ^ 2 * laplacian u (a + r • y) := by
  change (∑ i : Fin n, multiPartial (fun z => u (a + r • z)) {i,i} y) =
    r ^ 2 * ∑ i : Fin n, multiPartial u {i,i} (a + r • y)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact multiPartial_affine_on Ω hu a r {i,i} (by simp) hy

lemma isBoundedOn_bijOn_mul_iff {n : ℕ} {s t : Set (Space n)}
    {φ : Space n → Space n} (hφ : Set.BijOn φ s t)
    {g h : Space n → ℝ} {c : ℝ} (hc : 0 < c)
    (heq : ∀ x ∈ s, h x = c * g (φ x)) :
    IsBoundedOn h s ↔ IsBoundedOn g t := by
  constructor
  · rintro ⟨M,hM,hb⟩
    refine ⟨M / c, div_nonneg hM hc.le, ?_⟩
    intro y hy
    obtain ⟨x,hx,rfl⟩ := hφ.surjOn hy
    have hh := hb x hx
    rw [heq x hx, norm_mul, Real.norm_of_nonneg hc.le] at hh
    exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hh)
  · rintro ⟨M,hM,hb⟩
    refine ⟨c * M, mul_nonneg hc.le hM, ?_⟩
    intro x hx
    rw [heq x hx, norm_mul, Real.norm_of_nonneg hc.le]
    exact mul_le_mul_of_nonneg_left (hb _ (hφ.mapsTo hx)) hc.le

lemma c2HolderOn_affine_transfer {n : ℕ} {α r : ℝ} (hr : 0 < r)
    (Ω : Domain n) {u : Space n → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (a : Space n) {s t : Set (Space n)}
    (hφ : Set.BijOn (fun y : Space n => a + r • y) s t)
    (htΩ : t ⊆ (Ω : Set _))
    (hv : IsC2HolderOn α (fun y => u (a + r • y)) s) :
    IsC2HolderOn α u t := by
  have hd : ∀ x ∈ s, ∀ y ∈ s,
      dist (a + r • x) (a + r • y) = r * dist x y := by
    intro x hx y hy
    simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
      norm_smul, Real.norm_of_nonneg hr.le]
  have h0 := (isBoundedOn_bijOn_mul_iff hφ (g := u) (by norm_num : (0:ℝ) < 1)
    (fun x hx => by simp)).mp hv.2.1
  have h1 (i : Fin n) (x : Space n) (hx : x ∈ s) :
      multiPartial (fun y => u (a + r • y)) {i} x =
      r * multiPartial u {i} (a + r • x) := by
    simpa using multiPartial_affine_on Ω hu a r {i} (by simp) (htΩ (hφ.mapsTo hx))
  have h2 (i j : Fin n) (x : Space n) (hx : x ∈ s) :
      multiPartial (fun y => u (a + r • y)) {i,j} x =
      r ^ 2 * multiPartial u {i,j} (a + r • x) := by
    simpa using multiPartial_affine_on Ω hu a r {i,j} (by simp) (htΩ (hφ.mapsTo hx))
  refine ⟨hu.mono htΩ, h0, ?_, ?_⟩
  · intro i
    exact (isBoundedOn_bijOn_mul_iff hφ hr (h1 i)).mp (hv.2.2.1 i)
  · intro i j
    exact isHolderOn_of_bijOn_mul hφ (sq_pos_of_pos hr) hr (hv.2.2.2 i j) hd (h2 i j)


lemma affine_mem_ball_iff {n : ℕ} (a : Space n) {r : ℝ} (hr : 0 < r)
    (R : ℝ) (y : Space n) :
    a + r • y ∈ ball a (r * R) ↔ y ∈ ball (0 : Space n) R := by
  simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, sub_zero]
  exact mul_lt_mul_iff_right₀ hr

lemma affine_mem_closedBall_iff {n : ℕ} (a : Space n) {r : ℝ} (hr : 0 < r)
    (R : ℝ) (y : Space n) :
    a + r • y ∈ closedBall a (r * R) ↔ y ∈ closedBall (0 : Space n) R := by
  simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, sub_zero]
  exact mul_le_mul_iff_right₀ hr

lemma affine_inverse_right {n : ℕ} (a : Space n) {r : ℝ} (hr : r ≠ 0)
    (x : Space n) : a + r • (r⁻¹ • (x-a)) = x := by
  rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
  exact add_sub_cancel a x

lemma affine_inverse_left {n : ℕ} (a : Space n) {r : ℝ} (hr : r ≠ 0)
    (y : Space n) : r⁻¹ • ((a + r • y)-a) = y := by
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]

lemma inverse_affine_mem_ball_iff {n : ℕ} (a : Space n) {r : ℝ} (hr : 0 < r)
    (R : ℝ) (x : Space n) :
    r⁻¹ • (x-a) ∈ ball (0 : Space n) R ↔ x ∈ ball a (r * R) := by
  rw [← affine_mem_ball_iff a hr R, affine_inverse_right a hr.ne']

lemma affine_image_ball {n : ℕ} (a : Space n) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (fun y : Space n => a + r • y) '' ball 0 R = ball a (r * R) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (affine_mem_ball_iff a hr R y).mpr hy
  · intro hx
    exact ⟨r⁻¹ • (x-a), (inverse_affine_mem_ball_iff a hr R x).mpr hx,
      affine_inverse_right a hr.ne' x⟩

lemma contDiffOn_affine_pullback {n : ℕ} {m : ℕ∞ω} {u : Space n → ℝ}
    (a : Space n) (r : ℝ) (s : Set (Space n)) (t : Set (Space n))
    (hu : ContDiffOn ℝ m u t) (hst : MapsTo (fun y : Space n => a + r • y) s t) :
    ContDiffOn ℝ m (fun y : Space n => u (a + r • y)) s := by
  exact hu.comp (contDiff_const.add (contDiff_id.const_smul r)).contDiffOn hst

lemma contDiffOn_inverse_affine_pullback {n : ℕ} {m : ℕ∞ω} {u : Space n → ℝ}
    (a : Space n) {r : ℝ} (hr : r ≠ 0) (s : Set (Space n)) (t : Set (Space n))
    (hu : ContDiffOn ℝ m (fun y : Space n => u (a + r • y)) t)
    (hst : MapsTo (fun x : Space n => r⁻¹ • (x-a)) s t) :
    ContDiffOn ℝ m u s := by
  have hcomp := hu.comp
    (((contDiff_id.sub contDiff_const).const_smul r⁻¹).contDiffOn) hst
  simpa only [Function.comp_def, affine_inverse_right a hr, id_eq] using hcomp

lemma contDiffOn_affine_ball {n : ℕ} {m : ℕ∞ω} {u : Space n → ℝ}
    (a : Space n) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (hu : ContDiffOn ℝ m u (ball a (r * R))) :
    ContDiffOn ℝ m (fun y : Space n => u (a + r • y)) (ball 0 R) :=
  contDiffOn_affine_pullback a r _ _ hu
    (fun y hy => (affine_mem_ball_iff a hr R y).mpr hy)

lemma contDiffOn_inverse_affine_ball {n : ℕ} {m : ℕ∞ω} {u : Space n → ℝ}
    (a : Space n) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (hu : ContDiffOn ℝ m (fun y : Space n => u (a + r • y)) (ball 0 R)) :
    ContDiffOn ℝ m u (ball a (r * R)) :=
  contDiffOn_inverse_affine_pullback a hr.ne' _ _ hu
    (fun x hx => (inverse_affine_mem_ball_iff a hr R x).mpr hx)


lemma isHolderLoc_of_isHolderOn {n : ℕ} {α : ℝ} {f : Space n → ℝ}
    {Ω : Domain n} (hf : IsHolderOn α f Ω) : IsHolderLoc α f Ω := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  exact ⟨r, hr, hball, isHolderOn_mono hf hball⟩

lemma unit_ball_estimate {n : ℕ} (hn : 1 ≤ n) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u f : Space n → ℝ,
      ContDiffOn ℝ 2 u (ball (0 : Space n) 2) →
      IsBoundedOn u (ball (0 : Space n) 2) →
      IsHolderOn α f (ball (0 : Space n) 2) →
      (∀ x ∈ ball (0 : Space n) 2, -laplacian u x = f x) →
      IsC2HolderOn α u (ball (0 : Space n) 1) ∧
      c2HolderNormOn α u (ball (0 : Space n) 1) ≤
        C * (supNormOn u (ball (0 : Space n) 2) +
          holderNormOn α f (ball (0 : Space n) 2)) := by
  let B₂ : Domain n := ⟨ball 0 2, isOpen_ball⟩
  let B₁ : Domain n := ⟨ball 0 1, isOpen_ball⟩
  have hclosure : closure (B₁ : Set (Space n)) ⊆ (B₂ : Set _) := by
    exact (closure_minimal ball_subset_closedBall isClosed_closedBall).trans
      (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
  obtain ⟨C, hC, hest⟩ := interior_estimate hn α hα hα1 B₂ B₁ B₂
    isBounded_ball hclosure le_rfl
  refine ⟨C, hC, ?_⟩
  intro u f hu hub hf heq
  exact hest u f hu (isHolderLoc_of_isHolderOn (Ω := B₂) hf) heq hub hf


lemma c2HolderNormOn_rescale {n : ℕ} {s t : Set (Space n)}
    {φ : Space n → Space n} (hφ : Set.BijOn φ s t)
    {u v : Space n → ℝ} {r α : ℝ} (hr : 0 < r)
    (hdist : ∀ x ∈ s, ∀ y ∈ s, dist (φ x) (φ y) = r * dist x y)
    (hzero : ∀ x ∈ s, v x = u (φ x))
    (hone : ∀ i : Fin n, ∀ x ∈ s,
      multiPartial v {i} x = r * multiPartial u {i} (φ x))
    (htwo : ∀ i j : Fin n, ∀ x ∈ s,
      multiPartial v {i,j} x = r ^ 2 * multiPartial u {i,j} (φ x)) :
    c2HolderNormOn α v s = scaledSolutionNorm α r u t := by
  have h0 : supNormOn v s = supNormOn u t := by
    simpa using supNormOn_bijOn_mul hφ zero_le_one
      (fun x hx => (hzero x hx).trans (one_mul _).symm)
  have h1 (i : Fin n) : supNormOn (multiPartial v {i}) s =
      r * supNormOn (multiPartial u {i}) t :=
    supNormOn_bijOn_mul hφ hr.le (hone i)
  have h2 (i j : Fin n) : supNormOn (multiPartial v {i,j}) s =
      r ^ 2 * supNormOn (multiPartial u {i,j}) t :=
    supNormOn_bijOn_mul hφ (sq_nonneg _) (htwo i j)
  have hH (i j : Fin n) : holderSeminormOn α (multiPartial v {i,j}) s =
      r ^ (2 + α) * holderSeminormOn α (multiPartial u {i,j}) t := by
    rw [holderSeminormOn_bijOn_mul hφ (sq_nonneg _) hr hdist (htwo i j)]
    rw [Real.rpow_add hr, Real.rpow_two]
  rw [c2HolderNormOn_eq, scaledSolutionNorm]
  simp only [firstDerivativeNormOn, secondDerivativeNormOn,
    secondDerivativeSeminormOn, h0, h1, h2, hH, Finset.mul_sum]

lemma scaledDataNorm_rescale {n : ℕ} {s t : Set (Space n)}
    {φ : Space n → Space n} (hφ : Set.BijOn φ s t)
    {u f v g : Space n → ℝ} {r α : ℝ} (hr : 0 < r)
    (hdist : ∀ x ∈ s, ∀ y ∈ s, dist (φ x) (φ y) = r * dist x y)
    (hzero : ∀ x ∈ s, v x = u (φ x))
    (hg : ∀ x ∈ s, g x = r ^ 2 * f (φ x)) :
    supNormOn v s + holderNormOn α g s = scaledDataNorm α r u f t := by
  have h0 : supNormOn v s = supNormOn u t := by
    simpa using supNormOn_bijOn_mul hφ zero_le_one
      (fun x hx => (hzero x hx).trans (one_mul _).symm)
  rw [holderNormOn_eq, h0, supNormOn_bijOn_mul hφ (sq_nonneg _) hg,
    holderSeminormOn_bijOn_mul hφ (sq_nonneg _) hr hdist hg,
    scaledDataNorm, Real.rpow_add hr, Real.rpow_two]
  ring


/-- The unit estimate rescales through the equation itself, so this also
covers the logarithmic fundamental solution without an additive term. -/
theorem scaled_ball_estimate : ScaledBallEstimateStatement := by
  intro n hn α hα hα1
  obtain ⟨C, hC, hest⟩ := unit_ball_estimate hn hα hα1
  refine ⟨C, hC, ?_⟩
  intro a r hr u f hu hub hf heq
  let Ω : Domain n := ⟨ball a (2 * r), isOpen_ball⟩
  let φ : Space n → Space n := fun y => a + r • y
  let v : Space n → ℝ := fun y => u (φ y)
  let g : Space n → ℝ := fun y => r ^ 2 * f (φ y)
  have hbij (R : ℝ) : Set.BijOn φ (ball (0 : Space n) R) (ball a (r * R)) := by
    refine ⟨fun y hy => (affine_mem_ball_iff a hr R y).mpr hy, ?_, ?_⟩
    · intro x hx y hy h
      have he := congrArg (fun z => r⁻¹ • (z - a)) h
      simpa only [φ, affine_inverse_left a hr.ne'] using he
    · intro x hx
      exact ⟨r⁻¹ • (x - a), (inverse_affine_mem_ball_iff a hr R x).mpr hx,
        affine_inverse_right a hr.ne' x⟩
  have hb₁ : Set.BijOn φ (ball (0 : Space n) 1) (ball a r) := by
    simpa only [mul_one] using hbij 1
  have hb₂ : Set.BijOn φ (ball (0 : Space n) 2) (ball a (2 * r)) := by
    simpa only [mul_comm r 2] using hbij 2
  have hdist (x y : Space n) : dist (φ x) (φ y) = r * dist x y := by
    dsimp [φ]
    simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
      norm_smul, Real.norm_of_nonneg hr.le]
  have hv : ContDiffOn ℝ 2 v (ball (0 : Space n) 2) :=
    contDiffOn_affine_ball a hr 2 (by simpa only [mul_comm r 2] using hu)
  have hvb : IsBoundedOn v (ball (0 : Space n) 2) :=
    isBoundedOn_mapsTo_mul hb₂.mapsTo zero_le_one hub (fun x hx => by simp [v])
  have hg : IsHolderOn α g (ball (0 : Space n) 2) :=
    isHolderOn_mapsTo_mul hb₂.mapsTo (sq_nonneg r) hr.le hf
      (fun x hx y hy => hdist x y) (fun x hx => rfl)
  have heqv : ∀ y ∈ ball (0 : Space n) 2, -laplacian v y = g y := by
    intro y hy
    have hm : a + r • y ∈ Ω := hb₂.mapsTo hy
    change -laplacian (fun z => u (a + r • z)) y = r ^ 2 * f (a + r • y)
    rw [laplacian_affine_on Ω hu a r hm, ← mul_neg, heq _ hm]
  have hunit := hest v g hv hvb hg heqv
  have htΩ : ball a r ⊆ (Ω : Set (Space n)) :=
    ball_subset_ball (by linarith)
  have hclass := c2HolderOn_affine_transfer hr Ω hu a hb₁ htΩ hunit.1
  have hone (i : Fin n) (y : Space n) (hy : y ∈ ball (0 : Space n) 1) :
      multiPartial v {i} y = r * multiPartial u {i} (φ y) := by
    simpa only [Multiset.card_singleton, pow_one] using
      multiPartial_affine_on Ω hu a r {i} (by simp) (htΩ (hb₁.mapsTo hy))
  have htwo (i j : Fin n) (y : Space n) (hy : y ∈ ball (0 : Space n) 1) :
      multiPartial v {i,j} y = r ^ 2 * multiPartial u {i,j} (φ y) := by
    simpa using multiPartial_affine_on Ω hu a r {i,j} (by simp) (htΩ (hb₁.mapsTo hy))
  have hnorm := c2HolderNormOn_rescale (α := α) hb₁ hr
    (fun x hx y hy => hdist x y) (fun x hx => rfl) hone htwo
  have hdata := scaledDataNorm_rescale (α := α) (u := u) (v := v) (f := f) (g := g) hb₂ hr
    (fun x hx y hy => hdist x y) (fun x hx => rfl) (fun x hx => rfl : ∀ x ∈ ball (0 : Space n) 2,
      g x = r ^ 2 * f (φ x))
  refine ⟨hclass, ?_⟩
  rw [← hnorm, ← hdata]
  exact hunit.2

end P201.Elliptic.PoissonSchauder
