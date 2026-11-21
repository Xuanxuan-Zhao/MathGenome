import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.LocalAndStarShapedPotentials
import MathGenome.Internal.MultivariableAnalysis.D04.C11.PotentialPathIndependencePeriods
import MathGenome.Internal.MultivariableAnalysis.D04.C13.EuclideanPoincareLemma
import MathGenome.Internal.MultivariableAnalysis.D04.C13.OrientedEuclideanDictionary
import Mathlib.Analysis.Convex.PathConnected

noncomputable section
open Set Filter Topology
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace D04.C11
open D04
open D04.Dictionary
open D04.Homotopy

abbrev SymmetricPartials := @Specs.D04.C11.LocalAndStarShapedPotentials.Model.SymmetricPartials
abbrev radialPotential := @Specs.D04.C11.LocalAndStarShapedPotentials.Model.radialPotential

theorem symmetry_iff_jacobian {n} (U : Set (E n)) (F : E n → E n)
    (_hU : IsOpen U) (hF : CrOn 1 U F) :
    SymmetricPartials U F ↔ ∀ x ∈ U, (jacobian F x).IsSymm := by
  constructor
  · intro h x hx
    apply Matrix.IsSymm.ext
    intro i j
    rw [jacobian_apply U F x (hF.1 x hx) j i, jacobian_apply U F x (hF.1 x hx) i j]
    exact h x hx i j
  · intro h x hx i j
    have he := (h x hx).apply i j
    rw [jacobian_apply U F x (hF.1 x hx) j i, jacobian_apply U F x (hF.1 x hx) i j] at he
    exact he

theorem potential_C2 {n} (U : Set (E n)) (F : E n → E n) (f : E n → ℝ)
    (hU : IsOpen U) (hF : CrOn 1 U F) (hf : IsPotential U F f) : CrOn 2 U f :=
  potential_regular 1 U F f hU hf hF

theorem potential_necessary {n} (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hF : CrOn 1 U F) (hf : HasPotential U F) :
    SymmetricPartials U F := by
  obtain ⟨f, hf⟩ := hf
  have hf2 := potential_C2 U F f hU hF hf
  have he (i : Fin n) : EqOn (fun y => F y i) (fun y => scalarPartialDerivative f y i) U := by
    intro y hy
    change F y i = scalarPartialDerivative f y i
    rw [← hf.2 hy]
    exact gradient_coordinates U f y hU hf.1 hy i
  intro x hx i j
  change scalarPartialDerivative (fun y => F y j) x i = scalarPartialDerivative (fun y => F y i) x j
  rw [scalarPartialDerivative_congr U _ _ hU (he j) x hx i,
    scalarPartialDerivative_congr U _ _ hU (he i) x hx j]
  exact scalarPartialDerivative_comm U f hU hf2 x hx i j

/-- Agreement on an open domain transfers the potential property. -/
lemma potential_congr {n} (U : Set (E n)) (F : E n → E n) (f g : E n → ℝ)
    (hU : IsOpen U) (hf : IsPotential U F f) (he : EqOn f g U) : IsPotential U F g := by
  refine ⟨(crOn_iff_contDiffOn 1 U g hU).mpr
    (((crOn_iff_contDiffOn 1 U f hU).mp hf.1).congr he.symm), ?_⟩
  intro x hx
  have hd : fderiv ℝ f x = fderiv ℝ g x :=
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) he).fderiv_eq
  have hg : scalarGradient g x = scalarGradient f x := by
    change (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ g x) =
      (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ f x)
    rw [hd]
  exact hg.trans (hf.2 hx)

/-- The degree-one homotopy integrand has weight t^0 = 1. -/
lemma homotopy_alpha_integrand {n} (a : E n) (F : E n → E n) (x : E n)
    (v : Fin 0 → E n) :
    homotopyIntegrand a (alpha F) x v =
      fun t => inner ℝ (F (a + t • (x-a))) (x-a) := by
  funext t
  simp only [homotopyIntegrand, Specs.D04.C13.HomotopyOperatorRegularity.Model.homotopyIntegrand,
    pow_zero, one_mul]
  rfl

theorem radialPotential_integrable {n} (U : Set (E n)) (F : E n → E n) (a : E n)
    (hU : IsOpen U) (hF : CrOn 1 U F) (ha : a ∈ U) (hstar : StarConvex ℝ a U) :
    ∀ x ∈ U, ScalarIntegrable (fun t => inner ℝ (F (a + t • (x-a))) (x-a)) := by
  have hcF : CrOn 0 U F := ((crOn_iff_contDiffOn 1 U F hU).mp hF).continuousOn
  have hα := (alpha_isCr 0 U F hU hcF).2
  intro x hx
  have hi := homotopy_integrable (k := 0) (alpha F) hU ha hstar hα x hx (0 : Fin 0 → E n)
  change ScalarIntegrable (homotopyIntegrand a (alpha F) x (0 : Fin 0 → E n)) at hi
  rwa [homotopy_alpha_integrand] at hi

/-- The scalar corresponding to the zero-form Hα is the stated Riemann integral. -/
lemma homotopy_alpha_scalar {n} (U : Set (E n)) (F : E n → E n) (a : E n)
    (hU : IsOpen U) (hF : CrOn 1 U F) (ha : a ∈ U) (hstar : StarConvex ℝ a U) :
    EqOn (fun x => scalarCovector.symm (homotopyOperator (k := 0) a (alpha F) x))
      (radialPotential a F) U := by
  have hcF : CrOn 0 U F := ((crOn_iff_contDiffOn 1 U F hU).mp hF).continuousOn
  have hα := (alpha_isCr 0 U F hU hcF).2
  intro x hx
  change homotopyOperator a (alpha F) x (0 : Fin 0 → E n) = radialPotential a F x
  rw [homotopy_apply (alpha F) hU ha hstar hα x hx]
  change scalarIntegral (homotopyIntegrand a (alpha F) x (0 : Fin 0 → E n)) = _
  rw [homotopy_alpha_integrand]
  rfl

theorem star_shaped_potential {n} (U : Set (E n)) (F : E n → E n) (a : E n)
    (hU : IsOpen U) (hF : CrOn 1 U F) (ha : a ∈ U) (hstar : StarConvex ℝ a U)
    (hs : SymmetricPartials U F) :
    IsPotential U F (radialPotential a F) ∧ CrOn 2 U (radialPotential a F) ∧
      ∀ g, IsPotential U F g → ∃ c : ℝ, ∀ x ∈ U, g x = radialPotential a F x + c := by
  have hclosed : Specs.D04.C13.ClosedAndExactForms.Model.IsClosedForm U (alpha F) := ⟨alpha_isCr 1 U F hU hF,
    (exterior_alpha_closed_iff U F hU hF).mpr ((symmetry_iff_jacobian U F hU hF).mp hs)⟩
  obtain ⟨hη, hdη, _⟩ := Poincare.poincare_primitive (alpha F) hU ha hstar hclosed
  let η : FormField n 0 := homotopyOperator a (alpha F)
  let f : E n → ℝ := fun x => scalarCovector.symm (η x)
  have hrepr : (fun x => scalarCovector (V := E n) (f x)) = η := by
    funext x
    exact scalarCovector.apply_symm_apply (η x)
  have hf : CrOn 1 U f :=
    ((isCrForm_zero_iff (some 1) U f).mp (hrepr ▸ hη)).2
  have hpot : IsPotential U F f := by
    refine ⟨hf, ?_⟩
    intro x hx
    apply ext_inner_right ℝ
    intro v
    have he : alpha (scalarGradient f) x = alpha F x := by
      rw [← differential_alpha_gradient U f hU hf x hx, hrepr]
      exact hdη hx
    exact congrArg (fun A : Covector (E n) 1 => A (fun _ => v)) he
  have hrad : IsPotential U F (radialPotential a F) :=
    potential_congr U F f (radialPotential a F) hU hpot
      (homotopy_alpha_scalar U F a hU hF ha hstar)
  refine ⟨hrad, potential_C2 U F _ hU hF hrad, ?_⟩
  intro g hg
  exact potential_unique U F _ g hU (hstar.isPathConnected ha).isConnected.isPreconnected hrad hg

theorem ball_potential {n} (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hF : CrOn 1 U F) (hs : SymmetricPartials U F)
    (b : E n) (r : ℝ) (hr : 0 < r) (hball : Metric.ball b r ⊆ U) :
    IsPotential (Metric.ball b r) F (radialPotential b F) ∧
      CrOn 2 (Metric.ball b r) (radialPotential b F) := by
  have hFb : CrOn 1 (Metric.ball b r) F :=
    (crOn_iff_contDiffOn 1 _ F Metric.isOpen_ball).mpr
      (((crOn_iff_contDiffOn 1 U F hU).mp hF).mono hball)
  have hs' : SymmetricPartials (Metric.ball b r) F := fun x hx => hs x (hball hx)
  have hh := star_shaped_potential (Metric.ball b r) F b Metric.isOpen_ball hFb
    (Metric.mem_ball_self hr) ((convex_ball b r) (Metric.mem_ball_self hr)) hs'
  exact ⟨hh.1, hh.2.1⟩

theorem local_potential {n} (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hF : CrOn 1 U F) (hs : SymmetricPartials U F) :
    ∀ x ∈ U, ∃ r > 0, Metric.ball x r ⊆ U ∧ HasPotential (Metric.ball x r) F := by
  intro x hx
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
  exact ⟨r, hr, hsub, radialPotential x F, (ball_potential U F hU hF hs x r hr hsub).1⟩

theorem symmetry_iff_curl_zero (U : Set (E 3)) (F : E 3 → E 3)
    (hU : IsOpen U) (hF : CrOn 1 U F) :
    SymmetricPartials U F ↔ ∀ x ∈ U, curl F x = 0 := by
  constructor
  · intro hs x hx
    rw [curl_coordinates U F x hU hF hx]
    ext i
    fin_cases i
    · exact sub_eq_zero.mpr (hs x hx 1 2)
    · exact sub_eq_zero.mpr (hs x hx 2 0)
    · exact sub_eq_zero.mpr (hs x hx 0 1)
  · intro hz x hx i j
    have he := hz x hx
    rw [curl_coordinates U F x hU hF hx] at he
    have h0 := congrArg (fun v : E 3 => v 0) he
    have h1 := congrArg (fun v : E 3 => v 1) he
    have h2 := congrArg (fun v : E 3 => v 2) he
    change scalarPartialDerivative (fun y => F y 2) x 1 - scalarPartialDerivative (fun y => F y 1) x 2 = 0 at h0
    change scalarPartialDerivative (fun y => F y 0) x 2 - scalarPartialDerivative (fun y => F y 2) x 0 = 0 at h1
    change scalarPartialDerivative (fun y => F y 1) x 0 - scalarPartialDerivative (fun y => F y 0) x 1 = 0 at h2
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact sub_eq_zero.mp h0 | exact (sub_eq_zero.mp h0).symm |
        exact sub_eq_zero.mp h1 | exact (sub_eq_zero.mp h1).symm |
        exact sub_eq_zero.mp h2 | exact (sub_eq_zero.mp h2).symm

end D04.C11
