import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ProperOrder
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ProperContinuity

/-!
Interchange of proper Riemann integrations on a compact rectangle.
The proof uses uniform continuity, one-dimensional Darboux bounds, tagged
convergence, and finite linearity. No multiple or measure integral is used.
-/
namespace SingleVariableAnalysis.ParameterIntegral
open Riemann
open scoped BigOperators
namespace O
export Specs.SingleVariableAnalysis.Ch14.ProperOrder (intervalExtension)
end O

@[simp] theorem intervalExtension_on {E : Type*} [Zero E] {a b : ℝ}
    (g : Set.Icc a b → E) (x : Set.Icc a b) : O.intervalExtension g x = g x := by
  classical
  exact dite_eq_left x.property

/-- A common bound on the oscillation in each cell bounds the tagged error. -/
theorem real_tagged_error_of_oscillation {g : ℝ → ℝ} {a b η : ℝ}
    (hg : RealIntegrable g a b) (P : Partition a b) (ξ : Tagging P)
    (hosc : ∀ i : Fin P.n, ∀ u ∈ cell P i, ∀ v ∈ cell P i,
      g u - g v ≤ η) :
    |realIntegral g hg - taggedSum P ξ g| ≤ η * (b - a) := by
  have hgap : upperSum g P hg.bounded - lowerSum g P hg.bounded ≤ η * (b - a) := by
    calc
      _ = ∑ i : Fin P.n,
          (cellSupremum g P hg.bounded i - cellInfimum g P hg.bounded i) *
            cellLength P i := by
        simp only [sub_mul, Finset.sum_sub_distrib]
        rfl
      _ ≤ ∑ i : Fin P.n, η * cellLength P i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
          (cell_oscillation_le_of_sub_le g P hg.bounded i η (hosc i)) (cell_positive P i).le
      _ = η * (b - a) := by rw [← Finset.mul_sum, sum_cellLength]
  have hI := realIntegral_bounds g hg P
  have hS := tagged_bounds g P hg.bounded ξ
  exact (abs_le.mpr ⟨by linarith [hI.1, hI.2, hS.1, hS.2],
    by linarith [hI.1, hI.2, hS.1, hS.2]⟩).trans hgap

/-- Uniform error estimates pass through a proper integral. -/
theorem real_integral_difference_le {g h : ℝ → ℝ} {a b M : ℝ}
    (hg : RealIntegrable g a b) (hh : RealIntegrable h a b)
    (hb : ∀ x ∈ Set.Icc a b, |g x - h x| ≤ M) :
    |realIntegral g hg - realIntegral h hh| ≤ (b - a) * M := by
  obtain ⟨hd, hv⟩ := real_difference_value hg hh
  obtain ⟨hn, hnI, _⟩ := real_norm_estimate _ hd
  rw [← hv, ← Real.norm_eq_abs]
  exact hnI.trans (realIntegral_le_mul_bound hn (by simpa only [Real.norm_eq_abs] using hb))

/-- The real interchange argument permits any ambient representatives agreeing
on the closed intervals. This also allows its use for complex components. -/
theorem real_order_of_representatives {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (f : Set.Icc a b → Set.Icc c d → ℝ)
    (hf : Continuous (Function.uncurry f))
    (sx : Set.Icc c d → ℝ → ℝ) (st : Set.Icc a b → ℝ → ℝ)
    (hsx : ∀ t (x : Set.Icc a b), sx t x = f x t)
    (hst : ∀ x (t : Set.Icc c d), st x t = f x t)
    (hx : ∀ t, RealIntegrable (sx t) a b)
    (ht : ∀ x, RealIntegrable (st x) c d)
    (F G : ℝ → ℝ) (hF : RealIntegrable F c d) (hG : RealIntegrable G a b)
    (hFval : ∀ t : Set.Icc c d, F t = realIntegral (sx t) (hx t))
    (hGval : ∀ x : Set.Icc a b, G x = realIntegral (st x) (ht x)) :
    realIntegral F hF = realIntegral G hG := by
  apply eq_of_forall_dist_le
  intro ε hε
  let A := (b - a) * (d - c)
  have hA : 0 ≤ A := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hcd)
  let η := ε / (2 * (A + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηeq : η * (2 * (A + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) η hη
  obtain ⟨δF, hδF, hcF⟩ :=
    ((real_tagged_equivalence F hcd hF.bounded _).mp ⟨hF, rfl⟩) (ε / 2) (half_pos hε)
  obtain ⟨Q, hQ⟩ := exists_fine_partition hcd (min δ δF) (lt_min hδ hδF)
  obtain ⟨τ⟩ := tags_exist Q
  let tags : Fin Q.n → Set.Icc c d := fun j => ⟨τ j, cell_subset_interval Q j (τ j).property⟩
  obtain ⟨hH, hHval⟩ := real_finite_linearity Q.n (cellLength Q)
    (fun j => sx (tags j)) hab (fun j => hx (tags j))
  let H := fun x : ℝ => ∑ j : Fin Q.n, cellLength Q j * sx (tags j) x
  have huniform (x : Set.Icc a b) : |G x - H x| ≤ η * (d - c) := by
    have ho (j : Fin Q.n) (u : ℝ) (hu : u ∈ cell Q j)
        (v : ℝ) (hv : v ∈ cell Q j) : st x u - st x v ≤ η := by
      let u' : Set.Icc c d := ⟨u, cell_subset_interval Q j hu⟩
      let v' : Set.Icc c d := ⟨v, cell_subset_interval Q j hv⟩
      have hdist : dist (x, u') (x, v') < δ := by
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        change dist u v < δ
        rw [Real.dist_eq]
        have hl := cellLength_le_mesh Q j
        have hm := hQ.trans_le (min_le_left δ δF)
        change Q.point j.succ - Q.point j.castSucc ≤ mesh Q at hl
        exact abs_lt.mpr ⟨by linarith [hu.1, hu.2, hv.1, hv.2],
          by linarith [hu.1, hu.2, hv.1, hv.2]⟩
      have he := hc hdist
      change dist (f x u') (f x v') < η at he
      rw [Real.dist_eq] at he
      rw [hst x u', hst x v']
      exact (le_abs_self _).trans he.le
    have he := real_tagged_error_of_oscillation (ht x) Q τ ho
    rw [hGval x]
    convert he using 2
    dsimp [H, taggedSum, Riemann.S.sumValue]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hsx (tags j) x, hst x (tags j)]
  have hbound : |realIntegral G hG - realIntegral H hH| ≤ (b - a) * (η * (d - c)) :=
    real_integral_difference_le hG hH (fun x hx => huniform ⟨x, hx⟩)
  have hsum : realIntegral H hH = taggedSum Q τ F := by
    calc
      realIntegral H hH = ∑ j : Fin Q.n,
          cellLength Q j * realIntegral (sx (tags j)) (hx (tags j)) := hHval
      _ = taggedSum Q τ F := by
        simp only [taggedSum, Riemann.S.sumValue, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [hFval (tags j)]
  have happrox := hcF Q τ (hQ.trans_le (min_le_right δ δF))
  rw [Real.norm_eq_abs] at happrox
  change |taggedSum Q τ F - realIntegral F hF| < ε / 2 at happrox
  rw [abs_sub_comm] at happrox
  rw [hsum] at hbound
  rw [Real.dist_eq]
  have htriangle := abs_sub_le (realIntegral F hF) (taggedSum Q τ F) (realIntegral G hG)
  rw [abs_sub_comm (taggedSum Q τ F)] at htriangle
  have hsmall : (b - a) * (η * (d - c)) < ε / 2 := by
    have he : (b - a) * (η * (d - c)) = η * A := by dsimp [A]; ring
    rw [he]
    nlinarith
  linarith

/-- Both iterated real proper integrals exist and have the same value. -/
theorem real_proper_order : Specs.SingleVariableAnalysis.Ch14.ProperOrder.realOrder := by
  intro a b c d hab hcd f hf
  obtain ⟨hx, hFc⟩ := real_rectangle_continuity hab hcd f hf
  have hflip : Continuous (Function.uncurry (fun t x => f x t)) :=
    hf.comp continuous_swap
  obtain ⟨ht, hGc⟩ := real_rectangle_continuity hcd hab (fun t x => f x t) hflip
  refine ⟨hx, ht, ?_⟩
  let F := fun t => realIntegral (parameterSection .real f t) (hx t)
  let G := fun x => realIntegral (parameterSection .real (fun t x => f x t) x) (ht x)
  change ∃ (hF : RealIntegrable (O.intervalExtension F) c d)
    (hG : RealIntegrable (O.intervalExtension G) a b),
    realIntegral _ hF = realIntegral _ hG
  have hF : RealIntegrable (O.intervalExtension F) c d :=
    real_integrable_of_continuousOn hcd
      (continuousOn_of_section_agreement hFc (intervalExtension_on F))
  have hG : RealIntegrable (O.intervalExtension G) a b :=
    real_integrable_of_continuousOn hab
      (continuousOn_of_section_agreement hGc (intervalExtension_on G))
  refine ⟨hF, hG, ?_⟩
  exact real_order_of_representatives hab hcd f hf
    (parameterSection .real f) (parameterSection .real (fun t x => f x t))
    (fun t x => section_on_interval .real f t x)
    (fun x t => section_on_interval .real (fun t x => f x t) x t)
    hx ht _ _ hF hG (intervalExtension_on F) (intervalExtension_on G)

/-- A continuous complex interval function has an integrable representative. -/
theorem complex_intervalExtension_integrable {a b : ℝ} (hab : a ≤ b)
    {g : Set.Icc a b → ℂ} (hg : Continuous g) :
    ComplexIntegrable (O.intervalExtension g) a b := by
  constructor
  · apply real_integrable_of_continuousOn hab
    exact continuousOn_of_section_agreement (Complex.continuous_re.comp hg)
      (fun x => congrArg Complex.re (intervalExtension_on g x))
  · apply real_integrable_of_continuousOn hab
    exact continuousOn_of_section_agreement (Complex.continuous_im.comp hg)
      (fun x => congrArg Complex.im (intervalExtension_on g x))

/-- The complex assertion follows by applying the real finite-sum argument to
the two real components of the same inner and outer Darboux integrals. -/
theorem complex_proper_order : Specs.SingleVariableAnalysis.Ch14.ProperOrder.complexOrder := by
  intro a b c d hab hcd f hf
  obtain ⟨hx, hFc⟩ := complex_rectangle_continuity hab hcd f hf
  have hflip : Continuous (Function.uncurry (fun t x => f x t)) :=
    hf.comp continuous_swap
  obtain ⟨ht, hGc⟩ := complex_rectangle_continuity hcd hab (fun t x => f x t) hflip
  refine ⟨hx, ht, ?_⟩
  let F := fun t => complexIntegral (parameterSection .complex f t) (hx t)
  let G := fun x => complexIntegral (parameterSection .complex (fun t x => f x t) x) (ht x)
  change ∃ (hF : ComplexIntegrable (O.intervalExtension F) c d)
    (hG : ComplexIntegrable (O.intervalExtension G) a b),
    complexIntegral _ hF = complexIntegral _ hG
  have hF : ComplexIntegrable (O.intervalExtension F) c d :=
    complex_intervalExtension_integrable hcd hFc
  have hG : ComplexIntegrable (O.intervalExtension G) a b :=
    complex_intervalExtension_integrable hab hGc
  refine ⟨hF, hG, ?_⟩
  apply Complex.ext
  · rw [(complexIntegral_components _ hF).1, (complexIntegral_components _ hG).1]
    apply real_order_of_representatives hab hcd (fun x t => (f x t).re)
      (Complex.continuous_re.comp hf)
      (fun t x => (parameterSection .complex f t x).re)
      (fun x t => (parameterSection .complex (fun t x => f x t) x t).re)
      (fun t x => congrArg Complex.re (section_on_interval .complex f t x))
      (fun x t => congrArg Complex.re (section_on_interval .complex (fun t x => f x t) x t))
      (fun t => (hx t).1) (fun x => (ht x).1)
    · intro t
      rw [intervalExtension_on]
      exact (complexIntegral_components _ (hx t)).1
    · intro x
      rw [intervalExtension_on]
      exact (complexIntegral_components _ (ht x)).1
  · rw [(complexIntegral_components _ hF).2, (complexIntegral_components _ hG).2]
    apply real_order_of_representatives hab hcd (fun x t => (f x t).im)
      (Complex.continuous_im.comp hf)
      (fun t x => (parameterSection .complex f t x).im)
      (fun x t => (parameterSection .complex (fun t x => f x t) x t).im)
      (fun t x => congrArg Complex.im (section_on_interval .complex f t x))
      (fun x t => congrArg Complex.im (section_on_interval .complex (fun t x => f x t) x t))
      (fun t => (hx t).2) (fun x => (ht x).2)
    · intro t
      rw [intervalExtension_on]
      exact (complexIntegral_components _ (hx t)).2
    · intro x
      rw [intervalExtension_on]
      exact (complexIntegral_components _ (ht x)).2

end SingleVariableAnalysis.ParameterIntegral
