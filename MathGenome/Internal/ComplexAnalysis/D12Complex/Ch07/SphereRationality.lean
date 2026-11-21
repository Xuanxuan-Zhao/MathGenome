import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SphereRationality
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereTopology
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.LocalQuotientsArithmetic
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.InfinityClassification
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
open Set Filter Metric
open scoped Topology
namespace D12Complex.SphereRationality

/-- A closed discrete plane pole set has a pole-free punctured neighborhood
at every point, whether the center itself is a pole or is regular. -/
theorem eventually_no_poles {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn univ F) (a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, F z ≠ sphereInfty := by
  have hc : IsClosed {z | F z = sphereInfty} := by
    exact hF.2.1.preimage (continuous_id.subtype_mk (fun _ => mem_univ _))
  have hd : IsDiscrete {z | F z = sphereInfty} := by
    simpa only [scalarPoleSet, mem_univ, true_and] using hF.2.2.1
  exact disjoint_principal_right.mp ((isClosed_and_discrete_iff.mp ⟨hc, hd⟩) a)

/-- No finite pole can escape towards source infinity. -/
theorem finite_poles_bounded {F : RiemannSphere → RiemannSphere}
    (hF : ScalarMeromorphicOnSphere univ F) :
    ∃ R : ℝ, ∀ z : ℂ, F (sphereFinite z) = sphereInfty → ‖z‖ ≤ R := by
  have hI : ScalarMeromorphicOn univ (F ∘ infinityParametrization) := by
    simpa using hF.2.2
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp (eventually_no_poles hI 0)
  refine ⟨r⁻¹, fun z hz => ?_⟩
  by_contra! hnorm
  have hpos : 0 < ‖z‖ := lt_trans (inv_pos.mpr hr) hnorm
  have hzi : z⁻¹ ≠ 0 := inv_ne_zero (norm_pos_iff.mp hpos)
  have hmem : z⁻¹ ∈ ball (0 : ℂ) r ∩ ({0}ᶜ : Set ℂ) := by
    refine ⟨?_, hzi⟩
    simp only [mem_ball, dist_zero_right, norm_inv]
    exact (inv_lt_comm₀ hr hpos).mp hnorm
  have hn := hball hmem
  change F (infinityParametrization z⁻¹) ≠ sphereInfty at hn
  rw [infinityParametrization_ne_zero _ hzi, inv_inv] at hn
  exact hn hz

/-- Compactness of a disk and local discreteness make the finite pole set finite. -/
theorem finite_plane_poles {F : RiemannSphere → RiemannSphere}
    (hF : ScalarMeromorphicOnSphere univ F) :
    Set.Finite {z : ℂ | F (sphereFinite z) = sphereInfty} := by
  have hP : ScalarMeromorphicOn univ (F ∘ sphereFinite) := by simpa using hF.2.1
  have hc : IsClosed {z : ℂ | F (sphereFinite z) = sphereInfty} :=
    hP.2.1.preimage (continuous_id.subtype_mk (fun _ => mem_univ _))
  have hd : IsDiscrete {z : ℂ | F (sphereFinite z) = sphereInfty} := by
    simpa only [scalarPoleSet, mem_univ, true_and, Function.comp_apply] using hP.2.2.1
  obtain ⟨R, hR⟩ := finite_poles_bounded hF
  exact (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hc
    (fun z hz => by simpa using hR z hz) |>.finite hd

theorem finite_poles : Specs.D12Complex.Ch07.SphereRationality.finite_poles_type := by
  intro F hF
  apply ((finite_plane_poles hF).image sphereFinite |>.union (finite_singleton sphereInfty)).subset
  intro p hp
  rcases sphere_eq_infty_or_finite p with hi | ⟨z, rfl⟩
  · exact Or.inr hi
  · exact Or.inl ⟨z, hp, rfl⟩

/-- Polynomial evaluation is analytic in the finite coordinate. -/
theorem polynomial_analytic (P : Polynomial ℂ) (a : ℂ) : AnalyticAt ℂ P.eval a :=
  AnalyticOnNhd.eval_polynomial P a (mem_univ _)

/-- A polynomial in a reciprocal variable is a meromorphic germ at zero. -/
theorem polynomial_reciprocal_meromorphic (P : Polynomial ℂ) :
    MeromorphicAt (fun w : ℂ => P.eval w⁻¹) 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [Polynomial.eval_add] using hP.fun_add hQ
  | monomial n c =>
    simpa only [Polynomial.eval_monomial, Pi.inv_apply, id_eq] using
      (MeromorphicAt.const c 0).fun_mul ((MeromorphicAt.id 0).inv.fun_pow n)

/-- Clearing finitely many poles gives an actual entire product. The exponents
may exceed the exact pole orders, which causes no loss in the quotient. -/
theorem clear_finite_poles (F : ℂ → RiemannSphere)
    (hF : ScalarMeromorphicOn univ F) (hS : Set.Finite {a | F a = sphereInfty}) :
    ∃ Q : Polynomial ℂ, Q ≠ 0 ∧
      HolomorphicOn univ (fun z => Q.eval z * scalarFinitePart F z) := by
  classical
  have hm (a : ℂ) := LocalQuotientsArithmetic.scalar_meromorphicAt univ F hF a (mem_univ _)
  choose n hn using hm
  let S := hS.toFinset
  let Q : Polynomial ℂ := ∏ a ∈ S, (Polynomial.X - Polynomial.C a) ^ n a
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun a _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a))
  refine ⟨Q, hQ, isOpen_univ, fun a _ => ?_⟩
  apply AnalyticAt.differentiableAt
  by_cases ha : a ∈ S
  · let R : Polynomial ℂ := ∏ b ∈ S.erase a, (Polynomial.X - Polynomial.C b) ^ n b
    have heq (z : ℂ) : Q.eval z * scalarFinitePart F z =
        R.eval z * ((z-a)^n a * scalarFinitePart F z) := by
      dsimp [Q, R]
      rw [← Finset.prod_erase_mul S _ ha]
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, mul_assoc]
    have han : AnalyticAt ℂ (fun z => (z-a)^n a * scalarFinitePart F z) a := by
      simpa only [smul_eq_mul] using hn a
    convert! (polynomial_analytic R a).mul han using 1
    exact funext heq
  · have hfa : F a ≠ sphereInfty := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using ha
    exact (polynomial_analytic Q a).mul
      (scalarMeromorphicOn_finite_analytic univ F hF a (mem_univ _) hfa)

/-- The entire product retains meromorphy at infinity. This uses only the
punctured reciprocal germ, so the representative's filler at zero is irrelevant. -/
theorem cleared_reciprocal_meromorphic {F : RiemannSphere → RiemannSphere}
    (hF : ScalarMeromorphicOnSphere univ F) (Q : Polynomial ℂ) :
    MeromorphicAt (reciprocalPullback
      (fun z => Q.eval z * scalarFinitePart (F ∘ sphereFinite) z)) 0 := by
  have hI : ScalarMeromorphicOn univ (F ∘ infinityParametrization) := by
    simpa using hF.2.2
  have hm := LocalQuotientsArithmetic.scalar_meromorphicAt univ
    (F ∘ infinityParametrization) hI 0 (mem_univ _)
  apply ((polynomial_reciprocal_meromorphic Q).fun_mul hm).congr
  filter_upwards [self_mem_nhdsWithin] with w hw
  change w ≠ 0 at hw
  simp only [scalarFinitePart, Function.comp_apply,
    infinityParametrization_ne_zero _ hw, reciprocalPullback]

/-- An ordinary nonnegative meromorphic order gives the source's removable
singularity, including an extension on a whole disk. -/
theorem removable_of_meromorphic_nonneg {f : ℂ → ℂ} {a : ℂ}
    (hi : IsolatedSingularityAt f a) (hm : MeromorphicAt f a)
    (ho : 0 ≤ meromorphicOrderAt f a) : RemovableSingularityAt f a := by
  obtain ⟨g, hg, he⟩ := hm.meromorphicOrderAt_nonneg_iff.mp ho
  have he' : ∀ᶠ z in 𝓝 a, z ≠ a → f z = g z :=
    eventually_nhdsWithin_iff.mp he
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp (hg.eventually_analyticAt.and he')
  refine ⟨hi, r, hr, g, ⟨isOpen_ball, fun z hz => (h (mem_ball.mp hz)).1.differentiableAt⟩,
    fun z hz => (h ?_).2 ?_⟩
  · simpa only [dist_eq_norm] using hz.2
  · exact fun heq => by simpa [heq] using hz.1

/-- The accepted classification at infinity applies to an entire function
as soon as its reciprocal germ is meromorphic. -/
theorem polynomial_of_entire_reciprocal_meromorphic (f : ℂ → ℂ)
    (hf : HolomorphicOn univ f) (hm : MeromorphicAt (reciprocalPullback f) 0) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, f z = P.eval z := by
  have hi : IsolatedSingularityAtInfinity f :=
    (isolatedSingularityAtInfinity_iff_exterior f).mpr
      ⟨1, zero_lt_one, isOpen_lt continuous_const continuous_norm,
        fun z _ => hf.2 z (mem_univ _)⟩
  by_cases ho : 0 ≤ meromorphicOrderAt (reciprocalPullback f) 0
  · have hr : RemovableSingularityAtInfinity f := removable_of_meromorphic_nonneg hi hm ho
    obtain ⟨c, hc⟩ := (InfinityClassification.removable_iff_constant f hf).mp hr
    exact ⟨Polynomial.C c, fun z => by simpa using hc z⟩
  · have hneg := lt_of_not_ge ho
    cases he : meromorphicOrderAt (reciprocalPullback f) 0 with
    | top => simp [he] at hneg
    | coe k =>
      have hk : k < 0 := by simpa [he] using hneg
      let m := (-k).toNat
      have hmpos : 1 ≤ m := by omega
      have hcast : -(m : ℤ) = k := by dsimp [m]; omega
      have hp : PoleOfOrderAtInfinity f m :=
        LocalQuotientsArithmetic.poleOfOrder_of_order hm m hmpos (by
          exact he.trans (congrArg (fun i : ℤ => (i : WithTop ℤ)) hcast.symm))
      obtain ⟨P, _, hP⟩ := (InfinityClassification.pole_iff_polynomial_degree f hf m hmpos).mp hp
      exact ⟨P, hP⟩

/-- Every scalar meromorphic function on the whole sphere is a quotient of
complex polynomials, with all values restored in both source coordinates. -/
theorem rationality : Specs.D12Complex.Ch07.SphereRationality.rationality_type := by
  intro F hF
  have hP : ScalarMeromorphicOn univ (F ∘ sphereFinite) := by simpa using hF.2.1
  have hI : ScalarMeromorphicOn univ (F ∘ infinityParametrization) := by simpa using hF.2.2
  obtain ⟨Q, hQ, hg⟩ := clear_finite_poles (F ∘ sphereFinite) hP (finite_plane_poles hF)
  obtain ⟨P, hPQ⟩ := polynomial_of_entire_reciprocal_meromorphic _ hg
    (cleared_reciprocal_meromorphic hF Q)
  have heq (z : ℂ) (hz : Q.eval z ≠ 0) :
      scalarFinitePart (F ∘ sphereFinite) z = P.eval z / Q.eval z := by
    apply (eq_div_iff hz).mpr
    rw [mul_comm]
    exact hPQ z
  refine ⟨P, Q, hQ, ?_, ?_⟩
  · intro a
    calc
      F (sphereFinite a) = LocalQuotientsArithmetic.fill
          (scalarFinitePart (F ∘ sphereFinite)) a :=
        LocalQuotientsArithmetic.scalar_eq_fill univ _ hP (mem_univ a)
      _ = _ := LocalQuotientsArithmetic.fill_congr _ _ a (by
        filter_upwards [(Polynomial.eventually_eval_ne_zero_cofinite hQ).filter_mono
          (nhdsNE_le_cofinite a)] with z hz
        exact heq z hz)
  · calc
      F sphereInfty = LocalQuotientsArithmetic.fill
          (scalarFinitePart (F ∘ infinityParametrization)) 0 := by
        simpa only [Function.comp_apply, infinityParametrization_zero,
          LocalQuotientsArithmetic.fill,
          Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects.fill] using
          LocalQuotientsArithmetic.scalar_eq_fill univ _ hI (mem_univ (0 : ℂ))
      _ = _ := LocalQuotientsArithmetic.fill_congr _ _ 0 (by
        have hne : ∀ᶠ w in (cofinite : Filter ℂ), Q.eval w⁻¹ ≠ 0 :=
          inv_injective.tendsto_cofinite.eventually
            (Polynomial.eventually_eval_ne_zero_cofinite hQ)
        filter_upwards [hne.filter_mono (nhdsNE_le_cofinite (0 : ℂ)),
          self_mem_nhdsWithin] with w hw hw0
        change w ≠ 0 at hw0
        have h := heq w⁻¹ hw
        simpa only [scalarFinitePart, Function.comp_apply,
          infinityParametrization_ne_zero _ hw0] using h)

end D12Complex.SphereRationality
