import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.FritzJohn
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.SmoothConstraintModels
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.EqualityChart
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Gordan
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Linarith

open Set Filter
open scoped Topology ContDiff

noncomputable section
universe u v w
namespace VariationalNotes.Ch06

/-- A strictly negative derivative implies strict decrease for sufficiently
small positive time. No differentiability away from zero is needed. -/
private lemma eventually_lt_of_hasDerivAt_neg {p : ℝ → ℝ} {a : ℝ}
    (hp : HasDerivAt p a 0) (ha : a < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), p t < p 0 := by
  have hs := hp.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  filter_upwards [hs.eventually (gt_mem_nhds ha), self_mem_nhdsWithin] with t ht hpos
  have ht' : 0 < t := hpos
  have hslope : (p t - p 0) / t < 0 := by simpa [slope_def_field] using ht
  have := (div_lt_iff₀ ht').mp hslope
  linarith

/-- Coordinate expression of a linear functional on a finite real coordinate space. -/
private lemma dual_pi_apply {J : Type w} [Fintype J] [DecidableEq J]
    (l : (J → ℝ) →ₗ[ℝ] ℝ) (y : J → ℝ) :
    l y = ∑ j, l (Pi.single j 1) * y j := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show Pi.single j (y j) = y j • Pi.single j (1 : ℝ) by
    ext k
    by_cases hk : k = j <;> simp [hk]]
  simp [mul_comm]

/-- Strict simultaneous objective/active descent in the equality kernel is
impossible at a local minimum: the equality chart realizes the direction. -/
private lemma no_strict_descent
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    {U : Set X} {f : X → ℝ} {g : I → X → ℝ} {h : J → X → ℝ} {x : X}
    (hs : SmoothConstraintData U f g h) (hx : x ∈ feasibleSet U g h)
    (hm : IsLocalMinOn f (feasibleSet U g h) x)
    (hc : EqualityChart.Specs.FeasibleCurves (equalityDerivative h x) 1 U
      (fun y j => h j y) x) :
    ¬ ∃ d : (equalityDerivative h x).ker,
      fderiv ℝ f x d < 0 ∧ ∀ i ∈ activeSet g x, fderiv ℝ (g i) x d < 0 := by
  classical
  rintro ⟨d, hdf, hdg⟩
  obtain ⟨ε, γ, hε, hγ0, _, hγd, hγ⟩ := hc d
  obtain ⟨hf, hg, _⟩ := smoothConstraintData_hasFDerivAt U f g h x hs hx.1
  have hfd := hf.comp_hasDerivAt_of_eq 0 hγd hγ0.symm
  have hfall : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (γ t) < f x := by
    simpa only [Function.comp_apply, hγ0] using
      eventually_lt_of_hasDerivAt_neg hfd hdf
  have hgall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, g i (γ t) ≤ 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ∈ activeSet g x
    · have hgd := (hg i).comp_hasDerivAt_of_eq 0 hγd hγ0.symm
      have hlt := eventually_lt_of_hasDerivAt_neg hgd (hdg i hi)
      filter_upwards [hlt] with t ht
      have hi0 : g i x = 0 := hi
      simpa only [Function.comp_apply, hγ0, hi0] using ht.le
    · have hi0 : g i x < 0 := lt_of_le_of_ne (hx.2.1 i) hi
      have hgcont : ContinuousAt (fun t => g i (γ t)) 0 := by
        exact ((hg i).continuousAt.comp_of_eq hγd.continuousAt hγ0)
      have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), g i (γ t) < 0 :=
        hgcont.eventually (gt_mem_nhds (by simpa [hγ0] using hi0))
      exact (hnear.filter_mono nhdsWithin_le_nhds).mono (fun _ ht => ht.le)
  have hinterval : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (-ε) ε := by
    have hn : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-ε) ε :=
      Ioo_mem_nhds (by linarith : -ε < 0) hε
    exact hn.filter_mono nhdsWithin_le_nhds
  have hfeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ feasibleSet U g h := by
    filter_upwards [hinterval, hgall] with t ht hgt
    exact ⟨(hγ t ht).1, hgt, fun j => congrFun (hγ t ht).2 j⟩
  have htend : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝[feasibleSet U g h] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨by
      simpa only [hγ0] using hγd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      hfeas⟩
  have hmin : ∀ᶠ t in 𝓝[>] (0 : ℝ), f x ≤ f (γ t) := htend.eventually hm
  obtain ⟨t, ht, htf⟩ := (hmin.and hfall).exists
  exact (not_lt_of_ge ht) htf

/-- Translating a functional on the equality target to scalar multipliers. -/
private lemma equality_sum_apply
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {J : Type w} [Fintype J] [DecidableEq J]
    (h : J → X → ℝ) (x : X) (l : (J → ℝ) →ₗ[ℝ] ℝ) (d : X) :
    (∑ j, l (Pi.single j 1) • fderiv ℝ (h j) x) d = l (equalityDerivative h x d) := by
  simp only [sum_apply, smul_apply, smul_eq_mul]
  exact (dual_pi_apply l (equalityDerivative h x d)).symm

/-- A nonzero functional has a nonzero coordinate coefficient, even when the
index type is allowed to be empty. -/
private lemma exists_nonzero_coordinate {J : Type w} [Fintype J] [DecidableEq J]
    (l : (J → ℝ) →ₗ[ℝ] ℝ) (hl : l ≠ 0) : ∃ j, l (Pi.single j 1) ≠ 0 := by
  by_contra! hz
  apply hl
  apply LinearMap.ext
  intro y
  change l y = 0
  rw [dual_pi_apply]
  simp [hz]

/-- Singular equality derivatives supply abnormal multipliers directly. -/
private lemma abnormal_of_not_surjective
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X)
    (hx : x ∈ feasibleSet U g h)
    (hns : ¬ Function.Surjective (equalityDerivative h x)) :
    ∃ (lam0 : ℝ) (lam : I → ℝ) (nu : J → ℝ), FritzJohn U f g h x lam0 lam nu := by
  classical
  let B := equalityDerivative h x
  have hproper : LinearMap.range B.toLinearMap < ⊤ :=
    lt_top_iff_ne_top.mpr (fun ht => hns (LinearMap.range_eq_top.mp ht))
  obtain ⟨l, hl, hvan⟩ := Submodule.exists_le_ker_of_lt_top _ hproper
  refine ⟨0, fun _ => 0, fun j => l (Pi.single j 1), hx, le_rfl,
    fun _ => le_rfl, fun _ => zero_mul _,
    Or.inr (Or.inr (exists_nonzero_coordinate l hl)), ?_⟩
  simp only [zero_smul, Finset.sum_const_zero, add_zero, zero_add]
  ext d
  rw [equality_sum_apply]
  exact hvan ⟨d, rfl⟩

/-- If the equality derivative is onto, Gordan on its kernel supplies the
nonnegative objective/active coefficients. A right inverse supplies the free
coefficients of the equality differentials. -/
private lemma fritzJohn_of_surjective
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X)
    (hs : SmoothConstraintData U f g h) (hx : x ∈ feasibleSet U g h)
    (hm : IsLocalMinOn f (feasibleSet U g h) x)
    (honto : Function.Surjective (equalityDerivative h x)) :
    ∃ (lam0 : ℝ) (lam : I → ℝ) (nu : J → ℝ), FritzJohn U f g h x lam0 lam nu := by
  classical
  let B := equalityDerivative h x
  have hhC : ContDiffOn ℝ 1 (fun y j => h j y) U := contDiffOn_pi.mpr hs.2.2.2
  have hB : HasFDerivAt (fun y j => h j y) B x :=
    equalityDerivative_hasFDerivAt h x (fun j =>
      ((smoothConstraintData_hasFDerivAt U f g h x hs hx.1).2.2 j).differentiableAt)
  obtain ⟨R, hBR, _, _, hc⟩ := EqualityChart.finiteTargetEqualityChart X (J → ℝ)
    1 le_rfl U hs.1 (fun y j => h j y) hhC x hx.1 (funext hx.2.2) B hB honto
  have hnd := no_strict_descent hs hx hm hc
  let A := {i // i ∈ activeSet g x}
  let a : Option A → X →L[ℝ] ℝ :=
    Option.elim' (fderiv ℝ f x) (fun i => fderiv ℝ (g i.val) x)
  let T : B.ker →ₗ[ℝ] (Option A → ℝ) :=
    LinearMap.pi (fun o => (a o).toLinearMap.comp B.ker.subtype)
  obtain ⟨μ, hμ, hμne, hμzero⟩ : ∃ μ : Option A → ℝ,
      (∀ o, 0 ≤ μ o) ∧ μ ≠ 0 ∧ ∀ d : B.ker, ∑ o, μ o * T d o = 0 := by
    rcases (VariationalNotes.ConvexGeometry.gordan_linearMap T).1 with hd | hcert
    · obtain ⟨d, hd⟩ := hd
      exact False.elim (hnd ⟨d, hd none, fun i hi => hd (some ⟨i, hi⟩)⟩)
    · exact hcert
  let L : X →L[ℝ] ℝ := μ none • fderiv ℝ f x +
    ∑ i : A, μ (some i) • fderiv ℝ (g i.val) x
  have hLker (d : B.ker) : L d = 0 := by
    simpa [L, T, a, Fintype.sum_option, add_comm] using hμzero d
  let l : (J → ℝ) →ₗ[ℝ] ℝ := (-(L.comp R)).toLinearMap
  let nu : J → ℝ := fun j => l (Pi.single j 1)
  have hstation : L + (∑ j, nu j • fderiv ℝ (h j) x) = 0 := by
    ext d
    rw [add_apply, equality_sum_apply]
    change L d + -(L (R (B d))) = 0
    have hBRd : B (R (B d)) = B d :=
      congrArg (fun F : (J → ℝ) →L[ℝ] (J → ℝ) => F (B d)) hBR
    have hk : d - R (B d) ∈ B.ker := by
      change B (d - R (B d)) = 0
      rw [map_sub, hBRd, sub_self]
    have hz := hLker ⟨d - R (B d), hk⟩
    change L (d - R (B d)) = 0 at hz
    rw [map_sub] at hz
    linarith only [hz]
  let lam : I → ℝ := fun i => if hi : i ∈ activeSet g x then μ (some ⟨i, hi⟩) else 0
  have hlam (i : I) : 0 ≤ lam i := by
    dsimp [lam]
    split
    · exact hμ _
    · exact le_rfl
  have hcomp (i : I) : lam i * g i x = 0 := by
    by_cases hi : i ∈ activeSet g x
    · have hi0 : g i x = 0 := hi
      rw [hi0, mul_zero]
    · simp [lam, hi]
  have hsum : (∑ i, lam i • fderiv ℝ (g i) x) =
      ∑ i : A, μ (some i) • fderiv ℝ (g i.val) x := by
    have hinactive : (∑ i : {i // i ∉ activeSet g x},
        lam i.val • fderiv ℝ (g i.val) x) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [lam, i.property]
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun i => i ∈ activeSet g x) (fun i => lam i • fderiv ℝ (g i) x)
    rw [hinactive, add_zero] at hsplit
    rw [← hsplit]
    apply Finset.sum_congr rfl
    intro i _
    simp [lam, i.property]
  refine ⟨μ none, lam, nu, hx, hμ none, hlam, hcomp, ?_, ?_⟩
  · by_cases h0 : μ none = 0
    · right
      left
      by_contra! hall
      apply hμne
      funext o
      cases o with
      | none => exact h0
      | some i =>
        have hi := hall i.val
        simpa [lam, i.property] using hi
    · exact Or.inl h0
  · rw [hsum]
    exact hstation

/-- The unconditional Fritz John rule, including abnormal multipliers and
empty constraint families (`paper.tex`, Theorem `thm:fritz-john`). -/
theorem fritzJohn : FritzJohnSpecs.fritzJohn.{u,v,w} := by
  intro X _ _ _ I J _ _ U f g h x hs hx hm
  have : CompleteSpace X := FiniteDimensional.complete ℝ X
  by_cases honto : Function.Surjective (equalityDerivative h x)
  · exact fritzJohn_of_surjective U f g h x hs hx hm honto
  · exact abnormal_of_not_surjective U f g h x hx honto

end VariationalNotes.Ch06
