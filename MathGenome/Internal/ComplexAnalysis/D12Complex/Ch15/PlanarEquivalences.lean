import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.PlanarEquivalences
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch15.ComplementPeriods
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PrimitivePeriodCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.HomotopyIntegrals
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.GlobalLogarithmCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch12.ExtremalOnto
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.TFAE

/-! The seven simultaneous equivalences of D12.15.07.
The square-root implication uses the earlier extremal construction with its
universal square-root hypothesis. The whole plane is handled by convexity.
All contours and holomorphic functions are the shared canonical objects. -/

noncomputable section
open Set
open scoped unitInterval

namespace D12Complex.PlanarEquivalences

/-- A contraction of an arbitrary-interval closed contour, expressed in the
continuous-square format used by the homotopy Cauchy theorem. -/
theorem closed_piecewise_has_nullhomotopy
    {Ω : Set ℂ} (hsc : SimplyConnectedSpace Ω) (γ : PiecewiseC1Path)
    (hγ : γ.trace ⊆ Ω) (hc : γ.IsClosed) :
    ∃ (z : ℂ) (H : C(I × I, ℂ)), (∀ p, H p ∈ Ω) ∧
      (∀ t : I, H (0, t) = γ (γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ))) ∧
      (∀ t : I, H (1, t) = z) ∧ (∀ s : I, H (s, 0) = H (s, 1)) := by
  have hmem (t : I) : γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ) ∈
      Icc γ.path.a γ.path.b := by
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hab := γ.path.ordered
    constructor <;> nlinarith
  let p : Path γ.path.source γ.path.source := {
    toFun := fun t => γ (γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ))
    continuous_toFun := γ.path.continuousOn.comp_continuous
      (continuous_const.add (continuous_const.mul continuous_subtype_val)) hmem
    source' := by simp [ComplexPath.source]
    target' := by simpa [ComplexPath.source, ComplexPath.target, PiecewiseC1Path.IsClosed,
      ComplexPath.IsClosed] using hc
  }
  obtain ⟨F, hF⟩ :=
    (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hsc).2 _ p
      (fun t => hγ ⟨_, hmem t, rfl⟩)
  refine ⟨γ.path.source, F.toHomotopy.toContinuousMap, hF, ?_, ?_, ?_⟩
  · intro t
    exact F.toHomotopy.map_zero_left t
  · intro t
    exact F.toHomotopy.map_one_left t
  · intro s
    exact (F.source s).trans (F.target s).symm

/-- The underlying homeomorphism of a pair of holomorphic inverse maps. -/
def biholomorphicPairHomeomorph {Ω V : Set ℂ} {f g : ℂ → ℂ}
    (h : BiholomorphicPair Ω V f g) : Ω ≃ₜ V where
  toFun z := ⟨f z, h.2.2.1 z.property⟩
  invFun w := ⟨g w, h.2.2.2.1 w.property⟩
  left_inv z := Subtype.ext (h.2.2.2.2.1 z.property)
  right_inv w := Subtype.ext (h.2.2.2.2.2 w.property)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (show ContinuousOn f Ω from fun z hz =>
      (h.1.2 z hz).continuousAt.continuousWithinAt).domRestrict
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (show ContinuousOn g V from fun z hz =>
      (h.2.1.2 z hz).continuousAt.continuousWithinAt).domRestrict

/-- Universal square roots give a disk biholomorphism on a proper domain;
transporting the disk contraction gives simple connectivity. -/
theorem simplyConnected_of_squareRoots (Ω : Set ℂ) (hΩ : IsDomain Ω)
    (hroot : ∀ f : ℂ → ℂ, HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
      ∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧ ∀ z ∈ Ω, g z ^ 2 = f z) :
    SimplyConnectedSpace Ω := by
  by_cases hfull : Ω = Set.univ
  · subst Ω
    letI : ContractibleSpace (Set.univ : Set ℂ) :=
      (convex_univ : Convex ℝ (Set.univ : Set ℂ)).contractibleSpace Set.univ_nonempty
    infer_instance
  · obtain ⟨z₀, hz₀⟩ := hΩ.1
    obtain ⟨F, G, hpair, _, _⟩ :=
      ExtremalOnto.normalized_biholomorphism Ω hΩ hfull hroot z₀ hz₀
    letI : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
      (convex_ball (0 : ℂ) 1).contractibleSpace (Metric.nonempty_ball.mpr zero_lt_one)
    letI : ContractibleSpace Ω := (biholomorphicPairHomeomorph hpair).contractibleSpace
    infer_instance

theorem periods_iff_primitives (Ω : Set ℂ) (hΩ : IsDomain Ω) :
    (∀ f : ℂ → ℂ, HolomorphicOn Ω f →
      ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.IsClosed → γ.integral f = 0) ↔
    (∀ f : ℂ → ℂ, HolomorphicOn Ω f →
      ∃ F : ℂ → ℂ, HolomorphicOn Ω F ∧ ∀ z ∈ Ω, deriv F z = f z) := by
  constructor
  · intro hz f hf
    have hc : ContinuousOn f Ω :=
      fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt
    have hp := Primitives.primitive_criterion Ω f hΩ hc
    exact hp.1.mpr (hp.2.mpr (hz f hf))
  · intro hp f hf
    have hc : ContinuousOn f Ω :=
      fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt
    have hi := Primitives.primitive_criterion Ω f hΩ hc
    exact hi.2.mp (hi.1.mp (hp f hf))

theorem logarithms_of_primitives (Ω : Set ℂ) (hΩ : IsDomain Ω)
    (hp : ∀ f : ℂ → ℂ, HolomorphicOn Ω f →
      ∃ F : ℂ → ℂ, HolomorphicOn Ω F ∧ ∀ z ∈ Ω, deriv F z = f z) :
    ∀ f : ℂ → ℂ, HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
      ∃ L : ℂ → ℂ, HolomorphicOn Ω L ∧ ∀ z ∈ Ω, E (L z) = f z := by
  intro f hf hn
  apply (GlobalLogarithmCriterion.global_logarithm_criterion Ω f hΩ hf hn).mpr
  have hd := GlobalLogarithmCriterion.holomorphicOn_logarithmicDerivative Ω f hf hn
  have hc : ContinuousOn (fun z => deriv f z / f z) Ω :=
    fun z hz => (hd.2 z hz).continuousAt.continuousWithinAt
  have hi := Primitives.primitive_criterion Ω (fun z => deriv f z / f z) hΩ hc
  exact hi.2.mp (hi.1.mp (hp _ hd))

theorem nthRoots_of_logarithms (Ω : Set ℂ)
    (hl : ∀ f : ℂ → ℂ, HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
      ∃ L : ℂ → ℂ, HolomorphicOn Ω L ∧ ∀ z ∈ Ω, E (L z) = f z) :
    ∀ f : ℂ → ℂ, HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
      ∀ n : ℕ, 0 < n →
        ∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧ ∀ z ∈ Ω, g z ^ n = f z := by
  intro f hf hn n hpos
  obtain ⟨L, hL, he⟩ := hl f hf hn
  refine ⟨fun z => E (L z / (n : ℂ)), ⟨hL.1, ?_⟩, ?_⟩
  · intro z hz
    exact ((Exponential.hasDerivAt_E _).differentiableAt).comp z
      ((hL.2 z hz).div_const _)
  · intro z hz
    rw [Exponential.E_eq_exp, ← Complex.exp_nat_mul,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos))]
    exact (congrFun Exponential.E_eq_exp (L z)).symm.trans (he z hz)

theorem squareRoots_of_nthRoots (Ω : Set ℂ)
    (hn : ∀ f : ℂ → ℂ, HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
      ∀ n : ℕ, 0 < n →
        ∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧ ∀ z ∈ Ω, g z ^ n = f z) :
    ∀ f : ℂ → ℂ, HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
      ∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧ ∀ z ∈ Ω, g z ^ 2 = f z := by
  intro f hf hz
  exact hn f hf hz 2 (by norm_num)

/-- All seven source properties are equivalent, simultaneously, on every
plane domain, including the whole plane. -/
theorem planar_equivalences :
    Specs.D12Complex.Ch15.PlanarEquivalences.planar_equivalences_type := by
  intro Ω hΩ
  tfae_have 1 → 3 := by
    intro hsc f hf γ htrace hclosed
    exact HomotopyIntegrals.null_homotopic_integral Ω f hf γ htrace hclosed
      (closed_piecewise_has_nullhomotopy hsc γ htrace hclosed)
  tfae_have 2 ↔ 3 := ComplementPeriods.connected_complement_iff_zero_periods Ω hΩ
  tfae_have 3 ↔ 4 := periods_iff_primitives Ω hΩ
  tfae_have 4 → 5 := logarithms_of_primitives Ω hΩ
  tfae_have 5 → 7 := nthRoots_of_logarithms Ω
  tfae_have 7 → 6 := squareRoots_of_nthRoots Ω
  tfae_have 6 → 1 := simplyConnected_of_squareRoots Ω hΩ
  tfae_finish

end D12Complex.PlanarEquivalences
