import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.OrientedEuclideanDictionary
import MathGenome.Internal.MultivariableAnalysis.D04.C13.ExteriorDerivative
import MathGenome.Internal.MultivariableAnalysis.D04.C11.EuclideanVectorOperators
import MathGenome.Internal.MultivariableAnalysis.D04.C09.GradientIntegral
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace D04.Dictionary
open D04
open D04.C09
open Specs.D04.C14.OrientationsAndChartSigns.Model
abbrev alpha := @Specs.D04.C13.OrientedEuclideanDictionary.Model.alpha
abbrev coordinateOne := @Specs.D04.C13.OrientedEuclideanDictionary.Model.coordinateOne
abbrev omega := Specs.D04.C13.OrientedEuclideanDictionary.Model.omega
abbrev coordinateWithout := @Specs.D04.C13.OrientedEuclideanDictionary.Model.coordinateWithout
abbrev fluxForm := @Specs.D04.C13.OrientedEuclideanDictionary.Model.fluxForm
abbrev beta := Specs.D04.C13.OrientedEuclideanDictionary.Model.beta
abbrev euclideanCross := Specs.D04.C13.OrientedEuclideanDictionary.Model.euclideanCross
abbrev metricTopForm := @Specs.D04.C13.OrientedEuclideanDictionary.Model.metricTopForm
abbrev gramDensity := @Specs.D04.C13.OrientedEuclideanDictionary.Model.gramDensity
abbrev OneFormIntegrable := @Specs.D04.C13.OrientedEuclideanDictionary.Model.OneFormIntegrable
abbrev oneFormIntegral := @Specs.D04.C13.OrientedEuclideanDictionary.Model.oneFormIntegral

theorem alpha_apply {n} (F : E n → E n) (x : E n) (v : Fin 1 → E n) :
    alpha F x v = inner ℝ (F x) (v 0) := rfl

theorem alpha_workCovector {n} (F : E n → E n) (x v : E n) :
    alpha F x (fun _ => v) = workCovector F x v := rfl

@[simp] theorem coordinateOne_apply {n} (i : Fin n) (v : Fin 1 → E n) :
    coordinateOne i v = v 0 i := rfl

theorem alpha_coordinates {n} (F : E n → E n) (x : E n) :
    alpha F x = ∑ i : Fin n, F x i • coordinateOne i := by
  ext v
  simp only [alpha_apply, sum_apply, smul_apply, smul_eq_mul, coordinateOne_apply]
  exact workCovector_coordinates F x (v 0)

theorem differential_alpha_gradient {n} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 1 U f) (x : E n) (hx : x ∈ U) :
    exteriorDerivative (fun y => scalarCovector (V := E n) (f y)) x = alpha (scalarGradient f) x := by
  rw [exteriorDerivative_function U f hU hf x hx]
  ext v
  exact scalarGradient_represents f x (v 0)

theorem alpha_integrable_iff {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (F : E n → E n) :
    OneFormIntegrable d (alpha F) ↔ WorkIntegrable d F := Iff.rfl

theorem alpha_integral_work {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (F : E n → E n) (ha : OneFormIntegrable d (alpha F))
    (hw : WorkIntegrable d F) : oneFormIntegral d (alpha F) ha = workLineIntegral d F hw := rfl

theorem alpha_gradient_endpoint {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (U : Set (E n)) (f : E n → ℝ) (hU : IsOpen U)
    (hf : CrOn 1 U f) (hγ : trace γ ⊆ U) :
    ∃ h : OneFormIntegrable d (alpha (scalarGradient f)),
      oneFormIntegral d (alpha (scalarGradient f)) h = f (γ b) - f (γ a) := by
  obtain ⟨hc, hw, _, he⟩ := gradient_integral d U f hU hf hγ
  exact ⟨hw, he⟩

theorem omega_wedge (n : ℕ) : omega n = wedgeList n (fun i => (standardBasis n).coord i) := by
  ext v
  rw [wedgeList_apply]
  rfl

section Metric
universe u
variable {k : ℕ} {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [hdim : Fact (Module.finrank ℝ V = k)]

theorem metricTopForm_normalized (o : SpaceOrientation k V)
    (b : OrthonormalBasis (Fin k) ℝ V) (hb : b.toBasis.orientation = o) :
    metricTopForm o b = 1 := by
  change o.volumeForm b = 1
  rw [o.volumeForm_robust b hb]
  simpa using b.toBasis.det_self

theorem metricTopForm_exists_unique (hk : 0 < k) (o : SpaceOrientation k V) :
    ∃! ω : Covector V k, ∀ b : OrthonormalBasis (Fin k) ℝ V, b.toBasis.orientation = o → ω b = 1 := by
  refine ⟨metricTopForm o, metricTopForm_normalized o, ?_⟩
  intro ω hω
  let b := o.finOrthonormalBasis hk hdim.out
  have hb : b.toBasis.orientation = o := o.finOrthonormalBasis_orientation hk hdim.out
  rw [ω.eq_smul_basis_det b.toBasis]
  have he : ω b.toBasis = 1 := by simpa using hω b hb
  rw [he, one_smul]
  exact (o.volumeForm_robust b hb).symm

theorem metricTopForm_reverse (o : SpaceOrientation k V) :
    metricTopForm (-o) = -metricTopForm o := o.volumeForm_neg_orientation

theorem metricTopForm_reverse_density (o : SpaceOrientation k V) (v : Fin k → V) :
    |metricTopForm (-o) v| = |metricTopForm o v| := by
  rw [metricTopForm_reverse]
  simp

theorem metricTopForm_gram (o : SpaceOrientation k V) (v : Fin k → V) :
    |metricTopForm o v| = gramDensity v := by
  cases k with
  | zero =>
    have hv : Pairwise (fun i j : Fin 0 => inner ℝ (v i) (v j) = 0) :=
      fun i => Fin.elim0 i
    simpa [gramDensity, Specs.D04.C13.OrientedEuclideanDictionary.Model.gramDensity,
      metricTopForm, Specs.D04.C13.OrientedEuclideanDictionary.Model.metricTopForm] using
      o.abs_volumeForm_apply_of_pairwise_orthogonal hv
  | succ k =>
    let b := o.finOrthonormalBasis (Nat.succ_pos k) hdim.out
    have hb := o.finOrthonormalBasis_orientation (Nat.succ_pos k) hdim.out
    change |o.volumeForm v| = Real.sqrt (Matrix.gram ℝ v).det
    rw [o.volumeForm_robust b hb, Matrix.gram_eq_conjTranspose_mul b v,
      Matrix.det_mul, Matrix.det_conjTranspose]
    change |b.toBasis.det v| = Real.sqrt ((b.toBasis.det v) * (b.toBasis.det v))
    rw [← pow_two, Real.sqrt_sq_eq_abs]

end Metric

@[simp] theorem indexTuple_singleton {n : ℕ} (i : Fin n) (j : Fin 1) :
    indexTuple (Set.powersetCard.ofSingleton i) j = i := by
  have h := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
    (Set.powersetCard.ofSingleton i) (indexTuple (Set.powersetCard.ofSingleton i) j)).mp
      ⟨j, rfl⟩
  exact Finset.mem_singleton.mp h

@[simp] theorem dx_singleton {n : ℕ} (i : Fin n) :
    dx (standardBasis n) (Set.powersetCard.ofSingleton i) = coordinateOne i := by
  ext v
  simp only [dx_apply, indexTuple_singleton, Matrix.det_fin_one, coordinateOne_apply]
  rfl

@[simp] theorem alpha_coefficient_singleton {n : ℕ} (F : E n → E n)
    (x : E n) (i : Fin n) :
    coefficient (standardBasis n) (alpha F x) (Set.powersetCard.ofSingleton i) = F x i := by
  change inner ℝ (F x) (standardBasis n (indexTuple (Set.powersetCard.ofSingleton i) 0)) = _
  rw [indexTuple_singleton]
  exact EuclideanSpace.inner_basisFun_real (Fin n) _ i

theorem exterior_alpha_double_sum {n : ℕ} (F : E n → E n) (x : E n) :
    exteriorDerivative (alpha F) x = ∑ j : Fin n, ∑ i : Fin n,
      scalarPartialDerivative (fun y => F y j) x i • wedge (coordinateOne i) (coordinateOne j) := by
  rw [exteriorDerivative_formula, ← (Set.powersetCard.ofSingleton (α := Fin n)).sum_comp]
  simp_rw [alpha_coefficient_singleton, dx_singleton]
  rfl


/-- The normalized wedge has no extra factor of two. -/
theorem wedge_linear_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (f g : Module.Dual ℝ V) (v : Fin 2 → V) :
    wedge (linearCovector f) (linearCovector g) v =
      f (v 0) * g (v 1) - f (v 1) * g (v 0) := by
  have h1 : wedgeList 1 (fun _ => f) = linearCovector f := by
    change wedge (scalarCovector 1) (linearCovector f) = _
    simpa only [castCovector, Specs.D04.C13.NormalizedFormsAndWedge.Model.castCovector, one_smul] using wedge_scalar_left (q := 1) (V := V) 1 (linearCovector f)
  have h2 := wedgeList_apply (V := V) 2 ![f,g] v
  change wedge (wedgeList 1 (fun _ => f)) (linearCovector g) v = _ at h2
  rw [h1] at h2
  simpa [Matrix.det_fin_two] using h2

@[simp] theorem coordinateOne_wedge_apply {n} (i j : Fin n) (v : Fin 2 → E n) :
    wedge (coordinateOne i) (coordinateOne j) v =
      v 0 i * v 1 j - v 1 i * v 0 j :=
  wedge_linear_apply _ _ v

@[simp] theorem coordinateOne_wedge_self {n} (i : Fin n) :
    wedge (coordinateOne i) (coordinateOne i) = 0 := by
  ext v
  simp [mul_comm]

theorem coordinateOne_wedge_swap {n} (i j : Fin n) :
    wedge (coordinateOne j) (coordinateOne i) = -wedge (coordinateOne i) (coordinateOne j) := by
  ext v
  simp only [coordinateOne_wedge_apply, neg_apply]
  ring

/-- Collect the two orders of each distinct pair of coordinate indices. -/
theorem exterior_alpha_formula {n} (F : E n → E n) (x : E n) :
    exteriorDerivative (alpha F) x = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then
        (scalarPartialDerivative (fun y => F y j) x i -
         scalarPartialDerivative (fun y => F y i) x j) • wedge (coordinateOne i) (coordinateOne j)
      else 0 := by
  let t (i j : Fin n) := scalarPartialDerivative (fun y => F y j) x i •
    wedge (coordinateOne i) (coordinateOne j)
  have ht (i : Fin n) : t i i = 0 := by simp [t]
  have split (i j : Fin n) : t i j =
      (if i < j then t i j else 0) + (if j < i then t i j else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [ht]
    · simp [h, not_lt.mpr h.le]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, t i j) =
      (∑ i : Fin n, ∑ j : Fin n, if i < j then t i j else 0) +
      (∑ i : Fin n, ∑ j : Fin n, if j < i then t i j else 0) := by
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [split]
    simp only [Finset.sum_add_distrib]
  rw [exterior_alpha_double_sum, Finset.sum_comm]
  change (∑ i : Fin n, ∑ j : Fin n, t i j) = _
  rw [hsum]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j
  · simp only [h, ite_true, t, coordinateOne_wedge_swap i j, smul_neg]
    ext v
    simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
    ring
  · simp [h]

theorem exterior_alpha_basis {n} (F : E n → E n) (x : E n) (i j : Fin n) :
    exteriorDerivative (alpha F) x ![standardBasis n i, standardBasis n j] =
      scalarPartialDerivative (fun y => F y j) x i -
      scalarPartialDerivative (fun y => F y i) x j := by
  rw [exterior_alpha_double_sum]
  simp [sum_apply, smul_apply, coordinateOne_wedge_apply, standardBasis_apply,
    Finset.sum_sub_distrib, mul_sub]

theorem exterior_alpha_closed_iff {n} (U : Set (E n)) (F : E n → E n)
    (_hU : IsOpen U) (hF : CrOn 1 U F) :
    ((∀ x ∈ U, exteriorDerivative (alpha F) x = 0) ↔
      ∀ x ∈ U, (jacobian F x).IsSymm) := by
  constructor
  · intro h x hx
    apply Matrix.IsSymm.ext
    intro i j
    rw [jacobian_apply U F x (hF.1 x hx) j i, jacobian_apply U F x (hF.1 x hx) i j]
    have he := exterior_alpha_basis F x i j
    rw [h x hx] at he
    exact (sub_eq_zero.mp he.symm)
  · intro h x hx
    rw [exterior_alpha_formula]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    split_ifs
    · have he := (h x hx).apply i j
      rw [jacobian_apply U F x (hF.1 x hx) j i,
        jacobian_apply U F x (hF.1 x hx) i j] at he
      rw [he, sub_self, zero_smul]
    · rfl

theorem beta_cross (F : E 3 → E 3) (x v w : E 3) :
    beta F x ![v,w] = inner ℝ (F x) (euclideanCross v w) := by
  simp only [beta, Specs.D04.C13.OrientedEuclideanDictionary.Model.beta,
    add_apply, smul_apply, smul_eq_mul, coordinateOne_wedge_apply]
  rw [← workCovector_apply, workCovector_coordinates]
  simp [euclideanCross, Specs.D04.C13.OrientedEuclideanDictionary.Model.euclideanCross,
    cross_apply, Fin.sum_univ_succ]
  ring


theorem coordinateOne_wedge_omega_two :
    wedge (coordinateOne (n := 2) 0) (coordinateOne 1) = omega 2 := by
  ext v
  rw [coordinateOne_wedge_apply]
  change _ = Matrix.det (fun i j : Fin 2 => v j i)
  rw [Matrix.det_fin_two]

theorem planar_derivative (U : Set (E 2)) (P Q : E 2 → ℝ)
    (_hU : IsOpen U) (_hP : CrOn 1 U P) (_hQ : CrOn 1 U Q) (x : E 2) (_hx : x ∈ U) :
    exteriorDerivative (fun y => P y • coordinateOne 0 + Q y • coordinateOne 1) x =
      (scalarPartialDerivative Q x 0 - scalarPartialDerivative P x 1) • omega 2 := by
  let F : E 2 → E 2 := fun y => WithLp.toLp 2 ![P y, Q y]
  have ha : (fun y => P y • coordinateOne 0 + Q y • coordinateOne 1) = alpha F := by
    funext y
    rw [alpha_coordinates]
    simp [F, Fin.sum_univ_two]
  rw [ha, exterior_alpha_formula]
  simp [F, Fin.sum_univ_two, coordinateOne_wedge_omega_two]

theorem exterior_alpha_curl (U : Set (E 3)) (F : E 3 → E 3)
    (hU : IsOpen U) (hF : CrOn 1 U F) (x : E 3) (hx : x ∈ U) :
    exteriorDerivative (alpha F) x = beta (curl F) x := by
  rw [exterior_alpha_double_sum]
  ext v
  simp only [sum_apply, smul_apply, smul_eq_mul, coordinateOne_wedge_apply,
    beta, Specs.D04.C13.OrientedEuclideanDictionary.Model.beta, add_apply]
  rw [curl_coordinates U F x hU hF hx]
  simp [Fin.sum_univ_succ]
  ring

theorem beta_neg (F : E 3 → E 3) (x : E 3) : beta (fun y => -F y) x = -beta F x := by
  ext v
  simp only [beta, Specs.D04.C13.OrientedEuclideanDictionary.Model.beta,
    add_apply, smul_apply, neg_apply, smul_eq_mul]
  change -F x 0 * _ + -F x 1 * _ + -F x 2 * _ = _
  ring

theorem curl_orientation_reverse (U : Set (E 3)) (F : E 3 → E 3)
    (hU : IsOpen U) (hF : CrOn 1 U F) (x : E 3) (hx : x ∈ U) :
    exteriorDerivative (alpha F) x = -beta (fun y => -curl F y) x := by
  rw [beta_neg, neg_neg]
  exact exterior_alpha_curl U F hU hF x hx

theorem curl_identification_unique (U : Set (E 3)) (F : E 3 → E 3)
    (hU : IsOpen U) (hF : CrOn 1 U F) (x : E 3) (hx : x ∈ U) (c : E 3)
    (hc : ∀ v w, exteriorDerivative (alpha F) x ![v,w] = inner ℝ c (euclideanCross v w)) :
    c = curl F x := by
  have he (v w : E 3) : inner ℝ c (euclideanCross v w) =
      inner ℝ (curl F x) (euclideanCross v w) := by
    rw [← hc v w, exterior_alpha_curl U F hU hF x hx, beta_cross]
  simp_rw [inner_coordinates] at he
  ext i
  fin_cases i
  all_goals
    first
    | simpa [euclideanCross, Specs.D04.C13.OrientedEuclideanDictionary.Model.euclideanCross,
        cross_apply, standardBasis_apply, Fin.sum_univ_succ] using he (standardBasis 3 1) (standardBasis 3 2)
    | simpa [euclideanCross, Specs.D04.C13.OrientedEuclideanDictionary.Model.euclideanCross,
        cross_apply, standardBasis_apply, Fin.sum_univ_succ] using he (standardBasis 3 2) (standardBasis 3 0)
    | simpa [euclideanCross, Specs.D04.C13.OrientedEuclideanDictionary.Model.euclideanCross,
        cross_apply, standardBasis_apply, Fin.sum_univ_succ] using he (standardBasis 3 0) (standardBasis 3 1)


theorem wedgeList_append {V : Type*} [AddCommGroup V] [Module ℝ V] (p q : ℕ)
    (f : Fin p → Module.Dual ℝ V) (g : Fin q → Module.Dual ℝ V) :
    wedge (wedgeList p f) (wedgeList q g) = wedgeList (p+q) (Fin.append f g) := by
  rw [wedgeList_eq_toForm, wedgeList_eq_toForm, wedgeList_eq_toForm, wedge_eq_library,
    ← D05.M15.ExteriorPairing.AlternatingForms.multiplication_elementary]
  congr 1
  apply Subtype.ext
  exact _root_.ExteriorAlgebra.ιMulti_mul_ιMulti f g

theorem cast_wedgeList {V : Type*} [AddCommGroup V] [Module ℝ V] {p q : ℕ}
    (h : p = q) (f : Fin p → Module.Dual ℝ V) :
    castCovector h (wedgeList p f) = wedgeList q (f ∘ (finCongr h).symm) := by
  subst q
  rfl

theorem wedgeList_cons {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (f : Module.Dual ℝ V) (g : Fin n → Module.Dual ℝ V) :
    castCovector (Nat.add_comm 1 n) (wedge (linearCovector f) (wedgeList n g)) =
      wedgeList (n+1) (Fin.cons f g) := by
  have h1 : wedgeList 1 (fun _ => f) = linearCovector f := by
    change wedge (scalarCovector 1) (linearCovector f) = _
    simpa only [castCovector, Specs.D04.C13.NormalizedFormsAndWedge.Model.castCovector, one_smul]
      using wedge_scalar_left (q := 1) (V := V) 1 (linearCovector f)
  rw [← h1, wedgeList_append, cast_wedgeList, Fin.append_left_eq_cons]
  congr 1

/-- Deleting a coordinate is the complement of its singleton multi-index. -/
def missingIndexEquiv (n : ℕ) : Fin (n+1) ≃ MultiIndex (n+1) n :=
  Set.powersetCard.ofSingleton.trans (Set.powersetCard.compl (by simp))

@[simp] theorem indexTuple_missing {n} (i : Fin (n+1)) (j : Fin n) :
    indexTuple (missingIndexEquiv n i) j = i.succAbove j := by
  change (({i}ᶜ : Finset (Fin (n+1))).orderEmbOfFin _) j = _
  rw [Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb]
  rfl

theorem coordinateWithout_dx {n} (i : Fin (n+1)) :
    coordinateWithout i = dx (standardBasis (n+1)) (missingIndexEquiv n i) := by
  rw [← coordinate_wedge]
  unfold coordinateWithout Specs.D04.C13.OrientedEuclideanDictionary.Model.coordinateWithout
  congr 1
  ext j
  rw [indexTuple_missing]
  rfl

theorem fluxForm_coefficient {n} (F : E (n+1) → E (n+1)) (x : E (n+1)) (i : Fin (n+1)) :
    coefficient (standardBasis (n+1)) (fluxForm F x) (missingIndexEquiv n i) =
      (-1 : ℝ) ^ i.val * F x i := by
  change coefficient _ (∑ j : Fin (n+1), _ • coordinateWithout j) _ = _
  simp_rw [coordinateWithout_dx]
  rw [coefficient_eq_repr]
  simp [dx, Specs.D04.C13.NormalizedFormsAndWedge.Model.dx, Finsupp.single_apply,
    (missingIndexEquiv n).injective.eq_iff]

/-- Evaluation of dx_j ∧ dx_without_i on the standard ordered basis. -/
theorem coordinateExteriorTerm_missing {n} (i j : Fin (n+1)) :
    Specs.D04.C13.ExteriorDerivative.Model.coordinateExteriorTerm j (missingIndexEquiv n i)
      (standardBasis (n+1)) = if j = i then (-1 : ℝ) ^ i.val else 0 := by
  change (castCovector (Nat.add_comm 1 n)
    (wedge (coordinateOne j) (dx (standardBasis (n+1)) (missingIndexEquiv n i)))) _ = _
  rw [← coordinateWithout_dx]
  change (castCovector (Nat.add_comm 1 n)
    (wedge (linearCovector ((standardBasis (n+1)).coord j))
      (wedgeList n (fun a => (standardBasis (n+1)).coord (i.succAbove a))))) _ = _
  rw [wedgeList_cons, wedgeList_apply]
  let r : Fin (n+1) → Fin (n+1) := Fin.cons j i.succAbove
  have hh : Fin.cons ((standardBasis (n+1)).coord j)
      (fun a => (standardBasis (n+1)).coord (i.succAbove a)) =
      (fun a => (standardBasis (n+1)).coord (r a)) := by
    funext a
    cases a using Fin.cases <;> rfl
  rw [hh]
  change Matrix.det (fun a b => (standardBasis (n+1)).coord (r a) (standardBasis (n+1) b)) = _
  by_cases h : j = i
  · subst j
    have hr : r = i.cycleRange.symm := by
      ext a
      cases a using Fin.cases <;> simp [r]
    have hm : (fun a b => (standardBasis (n+1)).coord (r a) (standardBasis (n+1) b)) =
        (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ).submatrix i.cycleRange.symm id := by
      ext a b
      simp [hr, Module.Basis.coord_apply, Matrix.one_apply, eq_comm, Finsupp.single_apply]
    rw [hm, Matrix.det_permute]
    simp [Fin.sign_cycleRange]
  · obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq h
    rw [ite_eq_right h]
    apply Matrix.det_zero_of_row_eq (i := 0) (j := a.succ) (Fin.succ_ne_zero a).symm
    ext b
    simp [r, ha]


/-- Scalar multiplication commutes with an actual directional derivative. -/
theorem scalarPartialDerivative_const_mul {n} (U : Set (E n)) (f : E n → ℝ)
    (x : E n) (hf : TotalDifferentiableAt U f x) (c : ℝ) (j : Fin n) :
    scalarPartialDerivative (fun y => c * f y) x j = c * scalarPartialDerivative f x j := by
  obtain ⟨A, hA⟩ := hf
  have hB : HasTotalDerivative U (fun y => c * f y) (c • A) x := by
    apply (hasTotalDerivative_iff_hasFDerivAt U _ _ x hA.1 hA.2.1).mpr
    exact ((hasTotalDerivative_iff_hasFDerivAt U _ A x hA.1 hA.2.1).mp hA).const_smul c
  rw [scalarPartialDerivative_eq U _ x (c • A) hB,
    scalarPartialDerivative_eq U f x A hA]
  rfl

theorem exterior_flux_coefficient {n} (U : Set (E (n+1))) (F : E (n+1) → E (n+1))
    (hU : IsOpen U) (hF : CrOn 1 U F) (x : E (n+1)) (hx : x ∈ U) :
    exteriorDerivative (fluxForm F) x =
      (∑ i, scalarPartialDerivative (fun y => F y i) x i) • omega (n+1) := by
  have hc (i : Fin (n+1)) : TotalDifferentiableAt U (fun y => F y i) x :=
    (totalDifferentiableAt_iff_components U F x hU hx).mp (hF.1 x hx) i
  rw [(exteriorDerivative (fluxForm F) x).eq_smul_basis_det (standardBasis (n+1))]
  change _ • omega (n+1) = _
  congr 1
  change (exteriorDerivative (fluxForm F) x) (standardBasis (n+1)) = _
  rw [exteriorDerivative_formula, ← (missingIndexEquiv n).sum_comp]
  simp_rw [fluxForm_coefficient]
  change (∑ i : Fin (n+1), ∑ j : Fin (n+1),
    scalarPartialDerivative (fun y => (-1 : ℝ)^i.val * F y i) x j •
      Specs.D04.C13.ExteriorDerivative.Model.coordinateExteriorTerm j (missingIndexEquiv n i))
        (standardBasis (n+1)) = _
  simp only [sum_apply, smul_apply, smul_eq_mul, coordinateExteriorTerm_missing,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarPartialDerivative_const_mul U _ x (hc i)]
  calc
    ((-1 : ℝ) ^ i.val * scalarPartialDerivative (fun y => F y i) x i) * (-1 : ℝ) ^ i.val =
        ((-1 : ℝ)^i.val * (-1 : ℝ)^i.val) * scalarPartialDerivative (fun y => F y i) x i := by ring
    _ = scalarPartialDerivative (fun y => F y i) x i := by
      rw [← mul_pow]
      simp

theorem exterior_flux_divergence {n} (U : Set (E (n+1))) (F : E (n+1) → E (n+1))
    (hU : IsOpen U) (hF : CrOn 1 U F) (x : E (n+1)) (hx : x ∈ U) :
    exteriorDerivative (fluxForm F) x = divergence F x • omega (n+1) := by
  rw [exterior_flux_coefficient U F hU hF x hx, divergence_coordinates U F x hU hF hx]

theorem fluxForm_three (F : E 3 → E 3) : fluxForm F = beta F := by
  funext x
  ext v
  simp only [fluxForm, Specs.D04.C13.OrientedEuclideanDictionary.Model.fluxForm,
    beta, Specs.D04.C13.OrientedEuclideanDictionary.Model.beta,
    sum_apply, smul_apply, smul_eq_mul, add_apply, coordinateOne_wedge_apply,
    coordinateWithout, Specs.D04.C13.OrientedEuclideanDictionary.Model.coordinateWithout,
    wedgeList_apply]
  simp [Fin.sum_univ_succ, Matrix.det_fin_two, Fin.succAbove,
    Specs.D04.C01.EuclideanInterfaces.Model.standardBasis]
  ring

theorem exterior_beta_divergence (U : Set (E 3)) (F : E 3 → E 3)
    (hU : IsOpen U) (hF : CrOn 1 U F) (x : E 3) (hx : x ∈ U) :
    exteriorDerivative (beta F) x = divergence F x • omega 3 := by
  rw [← fluxForm_three]
  exact exterior_flux_divergence U F hU hF x hx

/-- Laplace expansion identifies flux with insertion into the oriented volume. -/
theorem fluxForm_volume {n} (F : E (n+1) → E (n+1)) (x : E (n+1)) (v : Fin n → E (n+1)) :
    fluxForm F x v = omega (n+1) (Fin.cons (F x) v) := by
  simp only [fluxForm, Specs.D04.C13.OrientedEuclideanDictionary.Model.fluxForm,
    sum_apply, smul_apply, smul_eq_mul, coordinateWithout,
    Specs.D04.C13.OrientedEuclideanDictionary.Model.coordinateWithout, wedgeList_apply]
  change (∑ i : Fin (n+1), ((-1 : ℝ)^i.val * F x i) *
    Matrix.det (fun a b => v b (i.succAbove a))) =
      Matrix.det (fun (a b : Fin (n+1)) => (Fin.cons (F x) v : Fin (n+1) → E (n+1)) b a)
  rw [Matrix.det_succ_column_zero]
  rfl

theorem omega_metricTopForm (n : ℕ) :
    letI : Fact (Module.finrank ℝ (E n) = n) := ⟨by simp [E, Specs.D04.C01.EuclideanInterfaces.Model.E]⟩
    omega n = metricTopForm (standardBasis n).orientation := by
  letI : Fact (Module.finrank ℝ (E n) = n) := ⟨by simp [E]⟩
  exact ((standardBasis n).orientation.volumeForm_robust (EuclideanSpace.basisFun (Fin n) ℝ) rfl).symm

theorem beta_volume (F : E 3 → E 3) (x v w : E 3) :
    beta F x ![v,w] = omega 3 ![F x,v,w] := by
  rw [← fluxForm_three]
  exact fluxForm_volume F x ![v,w]


theorem alpha_isCr {n} (r : ℕ) (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hF : CrOn r U F) : IsCrForm (some r) U (alpha F) := by
  refine ⟨hU, ?_⟩
  intro I
  obtain ⟨i, rfl⟩ := (Set.powersetCard.ofSingleton (α := Fin n)).surjective I
  change CrOn r U (fun x => coefficient (standardBasis n) (alpha F x) _) 
  simp_rw [alpha_coefficient_singleton]
  apply (crOn_iff_contDiffOn r U _ hU).mpr
  exact (PiLp.proj 2 (fun _ : Fin n => ℝ) i).contDiff.comp_contDiffOn
    ((crOn_iff_contDiffOn r U F hU).mp hF)

theorem fluxForm_isCr {n} (r : ℕ) (U : Set (E (n+1))) (F : E (n+1) → E (n+1))
    (hU : IsOpen U) (hF : CrOn r U F) : IsCrForm (some r) U (fluxForm F) := by
  refine ⟨hU, ?_⟩
  intro I
  obtain ⟨i, rfl⟩ := (missingIndexEquiv n).surjective I
  change CrOn r U (fun x => coefficient (standardBasis (n+1)) (fluxForm F x) _)
  simp_rw [fluxForm_coefficient]
  apply (crOn_iff_contDiffOn r U _ hU).mpr
  let L : E (n+1) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin (n+1) => ℝ) i
  have hi : ContDiffOn ℝ (r : WithTop ℕ∞) (fun x => F x i) U :=
    L.contDiff.comp_contDiffOn ((crOn_iff_contDiffOn r U F hU).mp hF)
  exact contDiffOn_const.mul hi

theorem beta_isCr (r : ℕ) (U : Set (E 3)) (F : E 3 → E 3)
    (hU : IsOpen U) (hF : CrOn r U F) : IsCrForm (some r) U (beta F) := by
  rw [← fluxForm_three]
  exact fluxForm_isCr r U F hU hF

end D04.Dictionary
