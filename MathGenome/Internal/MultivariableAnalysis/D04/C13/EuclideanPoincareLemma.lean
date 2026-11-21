import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.EuclideanPoincareLemma
import MathGenome.Internal.MultivariableAnalysis.D04.C13.HomotopyOperatorRegularity
import MathGenome.Internal.MultivariableAnalysis.D04.C13.DifferentialIdentities
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import MathGenome.SingleVariableAnalysis.IntegrationFormulas

noncomputable section
open Set Filter Topology
open scoped BigOperators Classical
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace D04.Poincare
open Homotopy

/-- The regularity assertion uses the same radial proper-integral primitive. -/
theorem homotopy_C1 {n k : ℕ} {U : Set (E n)} {a : E n}
    (ω : FormField n (k+1)) (hU : IsOpen U) (ha : a ∈ U)
    (hstar : StarConvex ℝ a U) (hω : IsCrForm (some 1) U ω) :
    IsCrForm (some 1) U (homotopyOperator a ω) :=
  homotopy_isCr ω (some 1) hU ha hstar hω

theorem homotopy_regularity : Specs.D04.C13.EuclideanPoincareLemma.homotopy_regularityType := by
  intro n k U a ω r hU ha hstar hω
  exact homotopy_isCr ω r hU ha hstar hω

open JordanRegions Darboux

/-- The proper integral used by H agrees with the admitted scalar Darboux
integral. The enclosing-box convention contributes only two zero outer cells. -/
lemma scalarIntegral_eq_realIntegral (f : ℝ → ℝ) (hf : ScalarIntegrable f) :
    ∃ h : SingleVariableAnalysis.Riemann.RealIntegrable f 0 1,
      scalarIntegral f = SingleVariableAnalysis.Riemann.realIntegral f h := by
  let Q := enclosingBox Homotopy.unitInterval
  have hQ : Encloses Homotopy.unitInterval Q := enclosingBox_encloses (jordan_bounded unitInterval_jordan)
  let g : E 1 → ℝ := zeroExtension (fun t : Homotopy.unitInterval => f (t.val 0))
  have hg : Darboux.Integrable g Q := (region_integrable_iff_box _ hQ).mp hf
  have hl : Q.lower 0 < 0 := (encloses_open hQ
    (subset_closure (show (0 : E 1) ∈ Homotopy.unitInterval from ⟨le_rfl, zero_le_one⟩)) 0).1
  have hu : 1 < Q.upper 0 := (encloses_open hQ
    (subset_closure (show scalarPoint 1 ∈ Homotopy.unitInterval from ⟨zero_le_one, le_rfl⟩)) 0).2
  let P : Grid Q := fun i => threePartition (Q.lower i) 0 1 (Q.upper i)
    (by fin_cases i; exact hl) zero_lt_one (by fin_cases i; exact hu)
  let c₀ : CellIndex P := fun _ => (1 : Fin 3)
  have hmid : cellBox P c₀ = intervalBox 0 1 zero_le_one := by
    apply Subdivision.box_ext <;> apply PiLp.ext <;> intro i <;> fin_cases i <;> rfl
  have hcells := (subdivision_integrable g Q hg.1 P).mp hg
  have he : EqOn g (fun x : E 1 => f (x 0)) (carrier (intervalBox 0 1 zero_le_one)) := by
    intro x hx
    exact zeroExtension_apply _ (⟨x, unitInterval_eq_carrier ▸ hx⟩ : Homotopy.unitInterval)
  have hm : Darboux.Integrable g (intervalBox 0 1 zero_le_one) := hmid ▸ hcells c₀
  have hfm : Darboux.Integrable (fun x : E 1 => f (x 0)) (intervalBox 0 1 zero_le_one) :=
    (integrable_congr he).mp hm
  obtain ⟨hreal, hval⟩ := (Darboux.scalar_integral (fun x : E 1 => f (x 0)) 0 1 zero_le_one).2 hfm
  refine ⟨hreal, ?_⟩
  change regionIntegral (fun t : Homotopy.unitInterval => f (t.val 0)) = _
  rw [integral_eq_on_enclosing_box _ hf hQ hg,
    subdivision_integral g Q P hg hcells]
  rw [Finset.sum_eq_single c₀]
  · change lowerIntegral g _ = _
    rw [hmid]
    exact (lowerIntegral_congr he).trans hval
  · intro c _ hc
    have hzero : ∀ x ∈ carrier (cellBox P c),
        x ∉ ({0} ∪ {scalarPoint 1} : Set (E 1)) → g x = 0 := by
      intro x hx hn
      apply zeroExtension_of_not_mem
      intro hxu
      have hci : c 0 ≠ (1 : Fin 3) := by
        intro h
        apply hc
        funext i
        fin_cases i
        exact h
      have hxc := hx (0 : Fin 1)
      change ![Q.lower 0, 0, 1, Q.upper 0] (c 0).castSucc ≤ x 0 ∧
        x 0 ≤ ![Q.lower 0, 0, 1, Q.upper 0] (c 0).succ at hxc
      have hxt : 0 ≤ x 0 ∧ x 0 ≤ 1 := hxu
      generalize hd : c 0 = j at hxc hci
      fin_cases j
      · have hz : x = 0 := by
          apply PiLp.ext
          intro i
          fin_cases i
          have : x 0 ≤ 0 := by simpa using hxc.2
          exact le_antisymm this hxt.1
        exact hn (Or.inl hz)
      · exact hci rfl
      · have hz : x = scalarPoint 1 := by
          apply PiLp.ext
          intro i
          fin_cases i
          have : 1 ≤ x 0 := by simpa using hxc.1
          exact le_antisymm hxt.2 this
        exact hn (Or.inr hz)
    exact (ExceptionalSets.zero_off_contentZero (by decide) (hcells c).1
      (contentZero_union (NullCovers.singleton_contentZero (by decide) _)
        (NullCovers.singleton_contentZero (by decide) _)) hzero).2
  · simp

lemma scalarIntegral_ftc (F g : ℝ → ℝ) (hc : ContinuousOn F (Icc 0 1))
    (hd : ∀ t ∈ Ioo 0 1, HasDerivAt F (g t) t) (hg : ScalarIntegrable g) :
    scalarIntegral g = F 1 - F 0 := by
  obtain ⟨hr, he⟩ := scalarIntegral_eq_realIntegral g hg
  exact he.trans (SingleVariableAnalysis.Riemann.real_ftc_second F g 0 1 zero_le_one hc hd hr)

lemma scalarIntegrable_of_continuous (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 1)) : ScalarIntegrable f := by
  have hc : Continuous (fun t : Homotopy.unitInterval => f (t.val 0)) :=
    hf.comp_continuous
      ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_subtype_val)
      (fun t => t.property)
  exact (scalar_integral_continuous (P := (univ : Set (E 0))) (fun t _ => f t)
    (hc.comp continuous_fst)).1 0 (mem_univ _)

lemma scalarIntegral_congr {f g : ℝ → ℝ} (he : EqOn f g (Icc 0 1)) :
    scalarIntegral f = scalarIntegral g := by
  change regionIntegral (fun t : Homotopy.unitInterval => f (t.val 0)) =
    regionIntegral (fun t : Homotopy.unitInterval => g (t.val 0))
  congr 1
  funext t
  exact he t.property

lemma scalarIntegral_pow (m : ℕ) :
    scalarIntegral (fun t : ℝ => t ^ m) = 1 / (m+1 : ℕ) := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => s ^ (m+1) / (m+1 : ℕ)) (t^m) t := by
    convert ((hasDerivAt_id t).pow (m+1)).div_const (m+1 : ℕ) using 1 <;>
      simp [Nat.cast_add, Nat.cast_one]
    field_simp
  have h := scalarIntegral_ftc (fun t : ℝ => t ^ (m+1) / (m+1 : ℕ))
    (fun t => t^m) (by fun_prop) (fun t _ => hd t)
    (scalarIntegrable_of_continuous _ (by fun_prop))
  simpa using h

open private integral Integrable integral_linear integral_hasFDerivAt integral_continuous
  from MathGenome.Internal.MultivariableAnalysis.D04.C08.FiniteRepeated
open private integral_eq_scalar from MathGenome.Internal.MultivariableAnalysis.D04.C13.HomotopyOperatorRegularity

/-- Differentiate the shared proper scalar integral with jointly continuous
parameter derivatives. No extension outside the original parameter domain is assumed. -/
lemma scalarIntegral_fderiv {n : ℕ} {P : Set (E n)} (hP : IsOpen P)
    (f : ℝ → E n → ℝ) (A : ℝ → E n → E n →L[ℝ] ℝ)
    (hf : Continuous (fun z : Homotopy.unitInterval × P => f (z.1.val 0) z.2))
    (hA : Continuous (fun z : Homotopy.unitInterval × P => A (z.1.val 0) z.2))
    (hd : ∀ t ∈ Icc 0 1, ∀ p ∈ P, HasFDerivAt (f t) (A t p) p)
    (p : E n) (hp : p ∈ P) (v : E n) :
    fderiv ℝ (fun q => scalarIntegral (fun t => f t q)) p v =
      scalarIntegral (fun t => A t p v) := by
  let g : closure Homotopy.unitInterval → E n → ℝ := fun t q => f (t.val 0) q
  let B : closure Homotopy.unitInterval → E n → E n →L[ℝ] ℝ := fun t q => A (t.val 0) q
  have hclosed := unitInterval_closed.closure_eq
  let q : closure Homotopy.unitInterval × P → Homotopy.unitInterval × P := fun z =>
    (⟨z.1.val, by simpa only [hclosed] using z.1.property⟩, z.2)
  have hq : Continuous q := by fun_prop
  have hgc : Continuous (fun z : closure Homotopy.unitInterval × P => g z.1 z.2) := hf.comp hq
  have hBc : Continuous (fun z : closure Homotopy.unitInterval × P => B z.1 z.2) := hA.comp hq
  have H := integral_hasFDerivAt unitInterval_jordan hP g B hgc hBc
    (fun t r hr => hd _ t.property r hr) p hp
  have he (r : E n) (hr : r ∈ P) :
      integral (fun t : Homotopy.unitInterval => f (t.val 0) r) =
        scalarIntegral (fun t => f t r) :=
    integral_eq_scalar _ ((integral_continuous unitInterval_jordan g hgc).1 r hr)
  have hlocal : (fun r => integral (fun t : Homotopy.unitInterval => f (t.val 0) r)) =ᶠ[𝓝 p]
      (fun r => scalarIntegral (fun t => f t r)) :=
    Filter.eventuallyEq_of_mem (hP.mem_nhds hp) he
  rw [← hlocal.fderiv_eq, H.fderiv]
  have hi := (integral_continuous unitInterval_jordan B hBc).1 p hp
  have hv := integral_linear (fun t : Homotopy.unitInterval => A (t.val 0) p)
    (ContinuousLinearMap.apply ℝ ℝ v) hi
  have heval : integral (fun t : Homotopy.unitInterval => A (t.val 0) p v) =
      scalarIntegral (fun t => A t p v) := integral_eq_scalar _ hv.1
  exact hv.2.symm.trans heval

/-- The scalar endpoint identity, including the zero-dimensional ambient space. -/
theorem homotopy_function : Specs.D04.C13.EuclideanPoincareLemma.homotopy_functionType := by
  intro n U a f hU ha hstar hf x hx
  let ω : FormField n 0 := fun y => scalarCovector (V := E n) (f y)
  have hω : IsCrForm (some 1) U ω :=
    (isCrForm_zero_iff (some 1) U f).mpr ⟨hU, hf⟩
  have hdω := exteriorDerivative_continuous U ω hω
  have hc : IsContinuousForm U (exteriorDerivative ω) := hdω.2
  let F : ℝ → ℝ := fun t => f (radialPoint a x t)
  let g : ℝ → ℝ := fun t => totalDerivative f (radialPoint a x t) (x-a)
  have hline : Continuous (fun t : ℝ => radialPoint a x t) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : MapsTo (radialPoint a x) (Icc 0 1) U := fun _ ht => radialPoint_mem hstar hx ht
  have hF : ContinuousOn F (Icc 0 1) := by
    apply ((crOn_iff_contDiffOn 1 U f hU).mp hf).continuousOn.comp hline.continuousOn hmem
  have hg : ContinuousOn g (Icc 0 1) :=
    (hf.2.comp hline.continuousOn hmem).clm_apply continuousOn_const
  have hD (t : ℝ) (ht : t ∈ Ioo 0 1) : HasDerivAt F (g t) t := by
    obtain ⟨A, hA⟩ := hf.1 _ (hmem ⟨ht.1.le, ht.2.le⟩)
    have hda := (hasTotalDerivative_iff_hasFDerivAt U f A _ hU
      (hmem ⟨ht.1.le, ht.2.le⟩)).mp hA
    have hl : HasDerivAt (fun s : ℝ => radialPoint a x s) (x-a) t := by
      simpa only [radialPoint, Specs.D04.C13.HomotopyOperatorRegularity.Model.radialPoint, one_smul, id_eq]
        using ((hasDerivAt_id t).smul_const (x-a)).const_add a
    have hh := hda.comp_hasDerivAt t hl
    rw [show g t = A (x-a) from by simp only [g, totalDerivative_eq U f A _ hA]]
    convert hh using 1
    rfl
  have hFTC := scalarIntegral_ftc F g hF hD (scalarIntegrable_of_continuous g hg)
  ext v
  rw [homotopy_apply (exteriorDerivative ω) hU ha hstar hc x hx v]
  have he : EqOn (homotopyIntegrand a (exteriorDerivative ω) x v) g (Icc 0 1) := by
    intro t ht
    rw [show homotopyIntegrand a (exteriorDerivative ω) x v t =
      exteriorDerivative ω (radialPoint a x t) (Fin.cons (x-a) v) from by
        simp [homotopyIntegrand, Specs.D04.C13.HomotopyOperatorRegularity.Model.homotopyIntegrand]]
    rw [exteriorDerivative_function U f hU hf _ (hmem ht)]
    rfl
  change scalarIntegral (homotopyIntegrand a (exteriorDerivative ω) x v) = f x - f a
  rw [scalarIntegral_congr he, hFTC]
  simp [F, radialPoint, Specs.D04.C13.HomotopyOperatorRegularity.Model.radialPoint]

abbrev exampleForm := Specs.D04.C13.EuclideanPoincareLemma.Model.exampleForm
abbrev examplePrimitive := Specs.D04.C13.EuclideanPoincareLemma.Model.examplePrimitive

/-- Evaluation of the normalized wedge in degree two. -/
lemma wedge_two_apply {n : ℕ} (l m : Module.Dual ℝ (E n)) (v : Fin 2 → E n) :
    wedge (linearCovector l) (linearCovector m) v =
      l (v 0) * m (v 1) - l (v 1) * m (v 0) := by
  have h1 (f : Fin 1 → Module.Dual ℝ (E n)) : wedgeList 1 f = linearCovector (f 0) := by
    ext w
    rw [wedgeList_apply, Matrix.det_fin_one]
    rfl
  have h := wedgeList_apply 2 (![l,m] : Fin 2 → Module.Dual ℝ (E n)) v
  change wedge (wedgeList 1 (Fin.init ![l,m])) (linearCovector m) v = _ at h
  rw [h1] at h
  exact h.trans (Matrix.det_fin_two _)

lemma exampleForm_apply (x : E 3) (v : Fin 2 → E 3) :
    exampleForm x v = x 2 * (v 0 0 * v 1 2 - v 1 0 * v 0 2) := by
  change x 2 * wedge (linearCovector ((standardBasis 3).coord 0))
    (linearCovector ((standardBasis 3).coord 2)) v = _
  rw [wedge_two_apply]
  rfl

lemma exampleForm_isCr (r : ℕ) : IsCrForm (some r) univ exampleForm := by
  refine ⟨isOpen_univ, fun I => (crOn_iff_contDiffOn r univ _ isOpen_univ).mpr ?_⟩
  change ContDiffOn ℝ (r : WithTop ℕ∞) (fun x : E 3 => x 2 *
    wedge (coordinateOneForm 3 0) (coordinateOneForm 3 2)
      (fun j => standardBasis 3 (indexTuple I j))) univ
  fun_prop

lemma examplePrimitive_isCr (r : ℕ) : IsCrForm (some r) univ examplePrimitive := by
  refine ⟨isOpen_univ, fun I => (crOn_iff_contDiffOn r univ _ isOpen_univ).mpr ?_⟩
  change ContDiffOn ℝ (r : WithTop ℕ∞) (fun x : E 3 =>
    (-(x 2)^2 / 3) * coordinateOneForm 3 0 (fun j => standardBasis 3 (indexTuple I j)) +
    (x 0 * x 2 / 3) * coordinateOneForm 3 2 (fun j => standardBasis 3 (indexTuple I j))) univ
  fun_prop

lemma scalarIntegral_const_mul_pow (c : ℝ) (m : ℕ) :
    scalarIntegral (fun t : ℝ => c * t^m) = c / (m+1 : ℕ) := by
  have h := scalarIntegral_linearCombination (ι := Fin 1) (fun _ => c)
    (fun _ t => t^m) (fun _ => by fun_prop)
  simpa only [Fin.sum_univ_one, scalarIntegral_pow, mul_one_div] using h

/-- The integral calculation in d04:13:homotopy-example. -/
theorem homotopy_example_operator : homotopyOperator (0 : E 3) exampleForm = examplePrimitive := by
  funext x
  ext v
  have hc : IsContinuousForm univ exampleForm := (exampleForm_isCr 0).2
  rw [homotopy_apply exampleForm isOpen_univ (mem_univ _) (convex_univ.starConvex (mem_univ _)) hc x (mem_univ _) v]
  have he : homotopyIntegrand (0 : E 3) exampleForm x v =
      fun t : ℝ => (x 2 * (x 0 * v 0 2 - v 0 0 * x 2)) * t^2 := by
    funext t
    rw [show homotopyIntegrand (0 : E 3) exampleForm x v t =
        t * exampleForm (t • x) (Fin.cons x v) from by
          simp [homotopyIntegrand, Specs.D04.C13.HomotopyOperatorRegularity.Model.homotopyIntegrand,
            Specs.D04.C13.HomotopyOperatorRegularity.Model.radialPoint]]
    rw [exampleForm_apply]
    simp only [Fin.cons_zero, Fin.cons_one, PiLp.smul_apply, smul_eq_mul]
    ring
  change scalarIntegral (homotopyIntegrand (0 : E 3) exampleForm x v) = _
  rw [he, scalarIntegral_const_mul_pow]
  change _ = (-(x 2)^2 / 3) * v 0 0 + (x 0 * x 2 / 3) * v 0 2
  norm_num
  ring

/-- Prepending a one-covector agrees with the determinant normalization. -/
lemma prependCovector_wedgeList {n k : ℕ} (l : Module.Dual ℝ (E n))
    (f : Fin k → Module.Dual ℝ (E n)) :
    prependCovector (linearCovector l) (wedgeList k f) =
      wedgeList (k+1) (Fin.cons l f) := by
  induction k with
  | zero =>
    ext v
    change wedge (linearCovector l) (scalarCovector 1) v = _
    rw [wedge_scalar_right, one_smul, wedgeList_apply, Matrix.det_fin_one]
    rfl
  | succ k ih =>
    change prependCovector (linearCovector l)
      (wedge (wedgeList k (Fin.init f)) (linearCovector (f (Fin.last k)))) = _
    rw [prependCovector_wedge, ih, castCovector_rfl]
    conv_rhs => unfold wedgeList Specs.D04.C13.NormalizedFormsAndWedge.Model.wedgeList
    have he : (Fin.cons l (Fin.init f) : Fin (k+1) → Module.Dual ℝ (E n)) =
        Fin.init (Fin.cons l f : Fin (k+2) → Module.Dual ℝ (E n)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [he]
    rfl

lemma prependCovector_apply {n k : ℕ} (l : Module.Dual ℝ (E n))
    (A : Covector (E n) k) (v : Fin (k+1) → E n) :
    prependCovector (linearCovector l) A v =
      ∑ i : Fin (k+1), (-1 : ℝ)^i.val * l (v i) * A (i.removeNth v) := by
  conv_lhs => rw [covector_expansion (standardBasis n) A]
  simp only [prependCovector_sum, prependCovector_smul, sum_apply, smul_apply, smul_eq_mul]
  have he (I : MultiIndex n k) :
      prependCovector (linearCovector l) (dx (standardBasis n) I) v =
        ∑ i : Fin (k+1), (-1 : ℝ)^i.val * l (v i) * dx (standardBasis n) I (i.removeNth v) := by
    rw [← coordinate_wedge, prependCovector_wedgeList, wedgeList_apply, Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [wedgeList_apply]
    rfl
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  conv_rhs => rw [covector_expansion (standardBasis n) A]
  simp only [sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  ring

/-- Insertion in a wedge with a one-covector: the cancellation used by Cartan's formula. -/
lemma curryLeft_prependCovector {n k : ℕ} (l : Module.Dual ℝ (E n))
    (A : Covector (E n) (k+1)) (u : E n) :
    (prependCovector (linearCovector l) A).curryLeft u =
      l u • A - prependCovector (linearCovector l) (A.curryLeft u) := by
  ext v
  rw [AlternatingMap.curryLeft_apply_apply, prependCovector_apply, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Matrix.vecCons, Fin.cons_zero,
    Fin.removeNth_zero, Fin.tail_cons, Fin.val_succ, pow_succ, Fin.cons_succ,
    smul_apply, sub_apply, smul_eq_mul]
  rw [prependCovector_apply]
  have he (i : Fin (k+1)) :
      A (i.succ.removeNth (Fin.cons u v : Fin (k+2) → E n)) = A.curryLeft u (i.removeNth v) := by
    rw [AlternatingMap.curryLeft_apply_apply]
    congr 1
    funext j
    refine Fin.cases ?_ (fun r => ?_) j <;> simp [Fin.removeNth]
  simp_rw [he]
  simp only [mul_neg_one, neg_mul, Finset.sum_neg_distrib]
  rfl

/-- Degree counts arise from alternating uncurry/curry, with no factorial. -/
lemma prepend_curry_sum {n k : ℕ} (A : Covector (E n) (k+1)) :
    (∑ j : Fin n, prependCovector (coordinateOneForm n j)
      (A.curryLeft (standardBasis n j))) = (k+1) • A := by
  ext v
  simp only [sum_apply, coordinateOneForm, Specs.D04.C13.PullbackCalculus.Model.coordinateOneForm]
  simp_rw [prependCovector_apply]
  rw [Finset.sum_comm]
  have he (i : Fin (k+1)) :
      (∑ j : Fin n, (-1 : ℝ)^i.val *
        ((standardBasis n).coord j) (v i) * (A.curryLeft (standardBasis n j)) (i.removeNth v)) =
        (-1 : ℝ)^i.val * (A.curryLeft (v i)) (i.removeNth v) := by
    conv_rhs => rw [← (standardBasis n).sum_repr (v i)]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (-1 : ℝ)^i.val * ((standardBasis n).repr (v i)) j * _ = _
    ring
  have heq := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => he i)
  change (∑ i : Fin (k+1), ∑ j : Fin n, (-1 : ℝ)^i.val *
    ((standardBasis n).coord j) (v i) * (A.curryLeft (standardBasis n j)) (i.removeNth v)) = _
  rw [heq]
  have H := congrArg (fun B : Covector (E n) (k+1) => B v)
    (AlternatingMap.alternatizeUncurryFin_curryLeft A)
  simpa only [AlternatingMap.alternatizeUncurryFin_apply, smul_apply, smul_eq_mul,
    zsmul_eq_mul, Int.cast_neg, Int.cast_one, Int.cast_pow] using H

lemma exteriorDerivative_single {n k : ℕ} (b : E n → ℝ) (A : Covector (E n) k)
    (x : E n) (hb : DifferentiableAt ℝ b x) :
    exteriorDerivative (fun y => b y • A) x =
      prependCovector (linearCovector (fderiv ℝ b x).toLinearMap) A := by
  let a : Fin 1 → E n → ℝ := fun _ => b
  let B : Fin 1 → Covector (E n) k := fun _ => A
  have he : (fun y => b y • A) = fun y => ∑ i : Fin 1, a i y • B i := by
    funext y
    simp [a, B]
  rw [he, exteriorDerivative_sum_smul_const a B x (fun _ => hb)]
  simp only [Fin.sum_univ_one, a, B]
  have hl : linearCovector (fderiv ℝ b x).toLinearMap =
      ∑ j : Fin n, scalarPartialDerivative b x j • coordinateOneForm n j := by
    ext v
    simp only [linearCovector_apply, sum_apply, smul_apply, coordinateOneForm_apply,
      scalarPartialDerivative_eq_fderiv b x hb, smul_eq_mul]
    conv_lhs => rw [← (standardBasis n).sum_repr (v 0)]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
    rfl
  rw [hl]
  simp only [prependCovector, wedge_sum_left, wedge_smul_left,
    castCovector_sum, castCovector_smul]

/-- Direct differentiation of the displayed polynomial primitive. -/
theorem exteriorDerivative_examplePrimitive : exteriorDerivative examplePrimitive = exampleForm := by
  let b : Fin 2 → E 3 → ℝ := ![fun x => -(x 2)^2 / 3, fun x => x 0 * x 2 / 3]
  let A : Fin 2 → Covector (E 3) 1 := ![coordinateOneForm 3 0, coordinateOneForm 3 2]
  let η : Fin 2 → FormField 3 1 := fun i x => b i x • A i
  have he : examplePrimitive = fun x => ∑ i : Fin 2, η i x := by
    funext x
    simp only [Fin.sum_univ_two]
    rfl
  have hb : ∀ i, IsCrForm (some 1) univ (η i) := by
    intro i
    refine ⟨isOpen_univ, fun I => (crOn_iff_contDiffOn 1 univ _ isOpen_univ).mpr ?_⟩
    change ContDiffOn ℝ 1 (fun x : E 3 => b i x * A i (fun j => standardBasis 3 (indexTuple I j))) univ
    fin_cases i <;> dsimp [b] <;> fun_prop
  funext x
  rw [he, exteriorDerivative_sum univ η isOpen_univ hb x (mem_univ _)]
  have hd : ∀ i : Fin 2, DifferentiableAt ℝ (b i) x := by
    intro i
    fin_cases i <;> dsimp [b] <;> fun_prop
  simp_rw [η, exteriorDerivative_single _ _ x (hd _)]
  rw [Fin.sum_univ_two]
  let L (i : Fin 3) : E 3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
  have h0 : HasFDerivAt (b 0) ((-(2 * x 2) / 3) • L 2) x := by
    have H := (((L 2).hasFDerivAt (x := x)).pow 2).neg.const_smul (1/3 : ℝ)
    convert H using 1
    · funext y
      simp only [b, Matrix.cons_val_zero, Pi.smul_apply, Pi.neg_apply,
        smul_eq_mul, L, PiLp.proj_apply]
      ring
    · ext y
      simp [L, smul_smul]
      ring
  have h1 : HasFDerivAt (b 1) ((x 2 / 3) • L 0 + (x 0 / 3) • L 2) x := by
    have H := ((L 0).hasFDerivAt (x := x)).mul (L 2).hasFDerivAt |>.const_smul (1/3 : ℝ)
    convert H using 1
    · funext y
      simp only [b, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.smul_apply, Pi.mul_apply,
        smul_eq_mul, L, PiLp.proj_apply]
      ring
    · ext y
      simp [L, smul_add, smul_smul]
      ring
  rw [h0.fderiv, h1.fderiv]
  ext v
  change wedge (linearCovector _) (linearCovector ((standardBasis 3).coord 0)) v +
    wedge (linearCovector _) (linearCovector ((standardBasis 3).coord 2)) v = exampleForm x v
  rw [wedge_two_apply, wedge_two_apply, exampleForm_apply]
  simp only [ContinuousLinearMap.coe_coe, add_apply,
    smul_apply, smul_eq_mul, L, PiLp.proj_apply]
  have hcoord (i : Fin 3) (w : E 3) : (standardBasis 3).coord i w = w i := rfl
  simp_rw [hcoord]
  ring

lemma exteriorDerivative_exampleForm : exteriorDerivative exampleForm = 0 := by
  rw [← exteriorDerivative_examplePrimitive]
  funext x
  exact exteriorDerivative_squared univ examplePrimitive (examplePrimitive_isCr 2) x (mem_univ _)

theorem homotopy_example : Specs.D04.C13.EuclideanPoincareLemma.homotopy_exampleType :=
  ⟨⟨isOpen_univ, fun I r => (exampleForm_isCr r).2 I⟩,
    ⟨isOpen_univ, fun I r => (examplePrimitive_isCr r).2 I⟩,
    homotopy_example_operator, exteriorDerivative_exampleForm, exteriorDerivative_examplePrimitive⟩


/-- A covector with a variable first argument expands linearly in that argument. -/
lemma curryLeft_coordinates {n k : ℕ} (A : Covector (E n) (k+1)) (u : E n) :
    A.curryLeft u = ∑ j : Fin n, u j • A.curryLeft (standardBasis n j) := by
  conv_lhs => rw [← (standardBasis n).sum_repr u]
  simp only [map_sum, map_smul]
  rfl

lemma linearCovector_coordinates {n : ℕ} (L : E n →L[ℝ] ℝ) :
    linearCovector L.toLinearMap =
      ∑ j : Fin n, L (standardBasis n j) • coordinateOneForm n j := by
  ext v
  simp only [linearCovector_apply, sum_apply, smul_apply, coordinateOneForm_apply, smul_eq_mul]
  conv_lhs => rw [← (standardBasis n).sum_repr (v 0)]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  rfl

/-- The differential of insertion of the displacement vector into a constant form. -/
lemma exteriorDerivative_contraction {n k : ℕ} (A : Covector (E n) (k+1))
    (a x : E n) (c : E n → ℝ) (hc : DifferentiableAt ℝ c x) :
    exteriorDerivative (fun q => c q • A.curryLeft (q-a)) x =
      prependCovector (linearCovector (fderiv ℝ c x).toLinearMap) (A.curryLeft (x-a)) +
      c x • ((k+1) • A) := by
  have he : (fun q => c q • A.curryLeft (q-a)) =
      fun q => ∑ j : Fin n, (c q * (q-a) j) • A.curryLeft (standardBasis n j) := by
    funext q
    rw [curryLeft_coordinates]
    simp only [Finset.smul_sum, smul_smul]
  have hd (j : Fin n) : HasFDerivAt (fun q : E n => (q-a) j)
      (PiLp.proj 2 (fun _ : Fin n => ℝ) j : E n →L[ℝ] ℝ) x := by
    convert ((PiLp.proj 2 (fun _ : Fin n => ℝ) j : E n →L[ℝ] ℝ).hasFDerivAt
      (x := x)).sub_const (a j) using 1
    funext q
    rfl
  rw [he, exteriorDerivative_sum_smul_const (fun j q => c q * (q-a) j)
    (fun j => A.curryLeft (standardBasis n j)) x
    (fun j => hc.mul (hd j).differentiableAt)]
  have hp (j l : Fin n) : scalarPartialDerivative (fun q => c q * (q-a) j) x l =
      (x-a) j * fderiv ℝ c x (standardBasis n l) + c x * standardBasis n l j := by
    rw [scalarPartialDerivative_eq_fderiv (fun q => c q * (q-a) j) x (hc.mul (hd j).differentiableAt),
      show fderiv ℝ (fun q => c q * (q-a) j) x =
        (x-a) j • fderiv ℝ c x + c x • (PiLp.proj 2 (fun _ : Fin n => ℝ) j) from by
          apply HasFDerivAt.fderiv
          convert hc.hasFDerivAt.mul (hd j) using 1
          exact add_comm _ _]
    rfl
  simp_rw [hp, add_smul]
  simp only [Finset.sum_add_distrib]
  conv_rhs => rw [linearCovector_coordinates, curryLeft_coordinates]
  simp only [prependCovector, wedge_sum_left, wedge_smul_left, wedge_sum_right, wedge_smul_right,
    castCovector_sum, castCovector_smul, Finset.smul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    simp only [smul_smul]
  · have hcoord (l j : Fin n) : standardBasis n l j = if l = j then 1 else 0 := by
      simp [standardBasis, eq_comm]
    simp_rw [hcoord]
    simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    rw [← Finset.smul_sum]
    simpa only [prependCovector, add_smul] using
      congrArg (fun B => c x • B) (prepend_curry_sum A)

/-- Joint C¹ regularity supplies the continuous parameter derivative needed for
our proper integral differentiation theorem. -/
lemma scalarIntegral_fderiv_of_contDiff {n : ℕ} {P : Set (E n)} (hP : IsOpen P)
    (f : ℝ × E n → ℝ)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ∀ p ∈ P, ContDiffAt ℝ 1 f (t,p))
    (p : E n) (hp : p ∈ P) (v : E n) :
    fderiv ℝ (fun q => scalarIntegral (fun t => f (t,q))) p v =
      scalarIntegral (fun t => fderiv ℝ (fun q => f (t,q)) p v) := by
  let q : Homotopy.unitInterval × P → ℝ × E n := fun z => (z.1.val 0,z.2.val)
  have hq : Continuous q := by fun_prop
  apply scalarIntegral_fderiv hP (fun t q => f (t,q))
    (fun t p => fderiv ℝ (fun q => f (t,q)) p)
  · exact continuous_iff_continuousAt.mpr fun z =>
      (hf _ z.1.property _ z.2.property).continuousAt.comp (f := q) hq.continuousAt
  · apply continuous_iff_continuousAt.mpr
    intro z
    have hh := (hf _ z.1.property _ z.2.property).comp
      ((z.1.val 0,z.2.val),z.2.val)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hD := ContDiffAt.fderiv (f := fun (w : ℝ × E n) (y : E n) => f (w.1,y))
      (g := fun w => w.2) hh (contDiffAt_snd (n := (0 : WithTop ℕ∞)))
      (m := (0 : WithTop ℕ∞)) (by norm_num)
    exact hD.continuousAt.comp (f := q) hq.continuousAt
  · intro t ht p hp
    exact ((hf t ht p hp).comp p (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  · exact hp

/-- Exterior differentiation commutes with integration of jointly C¹
coefficients, for the actual proper integral in the radial operator. -/
lemma exteriorDerivative_integral {n k : ℕ} {U : Set (E n)} (hU : IsOpen U)
    (F : ℝ → FormField n k)
    (hF : ∀ I : MultiIndex n k, ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
      ContDiffAt ℝ 1 (fun z : ℝ × E n => coefficient (standardBasis n) (F z.1 z.2) I) (t,x))
    (x : E n) (hx : x ∈ U) (v : Fin (k+1) → E n) :
    exteriorDerivative (fun q => ∑ I : MultiIndex n k,
      scalarIntegral (fun t => coefficient (standardBasis n) (F t q) I) • dx (standardBasis n) I) x v =
      scalarIntegral (fun t => exteriorDerivative (F t) x v) := by
  let b (I : MultiIndex n k) (z : ℝ × E n) := coefficient (standardBasis n) (F z.1 z.2) I
  have hd (I : MultiIndex n k) : DifferentiableAt ℝ
      (fun q => scalarIntegral (fun t => b I (t,q))) x := by
    have hc := scalar_integral_cr hU 1 (b I) (hF I)
    exact (totalDifferentiableAt_iff_differentiableAt U _ x hU hx).mp (hc.1 x hx)
  rw [exteriorDerivative_sum_smul_const _ _ x hd]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  have hpart (I : MultiIndex n k) (j : Fin n) :
      scalarPartialDerivative (fun q => scalarIntegral (fun t => b I (t,q))) x j =
        scalarIntegral (fun t => fderiv ℝ (fun q => b I (t,q)) x (standardBasis n j)) := by
    rw [scalarPartialDerivative_eq_fderiv _ x (hd I)]
    exact scalarIntegral_fderiv_of_contDiff hU (b I) (hF I) x hx _
  simp_rw [hpart]
  have hc (I : MultiIndex n k) (j : Fin n) : Continuous
      (fun t : Homotopy.unitInterval => fderiv ℝ (fun q => b I (t.val 0,q)) x (standardBasis n j)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hh := (hF I _ t.property x hx).comp ((t.val 0,x),x)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hD := ContDiffAt.fderiv (f := fun (w : ℝ × E n) (y : E n) => b I (w.1,y))
      (g := fun w => w.2) hh (contDiffAt_snd (n := (0 : WithTop ℕ∞)))
      (m := (0 : WithTop ℕ∞)) (by norm_num)
    exact (hD.continuousAt.clm_apply continuousAt_const).comp
      (f := fun t : Homotopy.unitInterval => (t.val 0,x))
      (show ContinuousAt (fun t : Homotopy.unitInterval => (t.val 0,x)) t from by fun_prop)
  have he (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      exteriorDerivative (F t) x v = ∑ I : MultiIndex n k, ∑ j : Fin n,
        prependCovector (coordinateOneForm n j) (dx (standardBasis n) I) v *
          fderiv ℝ (fun q => b I (t,q)) x (standardBasis n j) := by
    rw [exteriorDerivative_expansion]
    simp only [sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro j _
    rw [scalarPartialDerivative_eq_fderiv (fun y => coefficient (standardBasis n) (F t y) I) x
      (((hF I t ht x hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num))]
    exact mul_comm _ _
  rw [scalarIntegral_congr he]
  have hs := scalarIntegral_linearCombination (fun _ => 1)
    (fun I t => ∑ j : Fin n,
      prependCovector (coordinateOneForm n j) (dx (standardBasis n) I) v *
        fderiv ℝ (fun q => b I (t,q)) x (standardBasis n j))
    (fun I => by exact continuous_finsetSum _ fun j _ => continuous_const.mul (hc I j))
  simp only [one_mul] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro I _
  rw [scalarIntegral_linearCombination _ _ (hc I)]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

lemma insertion_isCr {n k : ℕ} (r : ℕ) (U : Set (E n)) (hU : IsOpen U)
    (a : E n) (A : Covector (E n) (k+1)) :
    IsCrForm (some r) U (fun x => A.curryLeft (x-a)) := by
  refine ⟨hU, fun I => (crOn_iff_contDiffOn r U _ hU).mpr ?_⟩
  change ContDiffOn ℝ (r : WithTop ℕ∞)
    (fun x => coefficient (standardBasis n) (A.curryLeft (x-a)) I) U
  have he (x : E n) : coefficient (standardBasis n) (A.curryLeft (x-a)) I =
      ∑ j : Fin n, (x-a) j * (A.curryLeft (standardBasis n j))
        (fun l => standardBasis n (indexTuple I l)) := by
    rw [curryLeft_coordinates]
    simp only [coefficient, Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient,
      sum_apply, smul_apply, smul_eq_mul]
  simp_rw [he]
  fun_prop

lemma exteriorDerivative_fderiv {n k : ℕ} (U : Set (E n)) (ω : FormField n k)
    (hω : IsCrForm (some 1) U ω) (x : E n) (hx : x ∈ U) :
    exteriorDerivative ω x = ∑ I : MultiIndex n k,
      prependCovector (linearCovector
        (fderiv ℝ (fun q => coefficient (standardBasis n) (ω q) I) x).toLinearMap)
        (dx (standardBasis n) I) := by
  rw [exteriorDerivative_expansion]
  apply Finset.sum_congr rfl
  intro I _
  rw [linearCovector_coordinates]
  simp only [prependCovector, wedge_sum_left, wedge_smul_left, castCovector_sum, castCovector_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [scalarPartialDerivative_eq_fderiv _ x
    (isCrForm_coefficient_differentiableAt U ω hω x hx I)]

/-- The integrand as an alternating covector, before coefficient integration. -/
def radialForm {n k : ℕ} (a : E n) (ω : FormField n (k+1))
    (t : ℝ) (x : E n) : Covector (E n) k :=
  t^k • (ω (radialPoint a x t)).curryLeft (x-a)

lemma radial_coefficient {n k : ℕ} (a : E n) (ω : FormField n (k+1))
    (I : MultiIndex n k) (t : ℝ) (x : E n) :
    coefficient (standardBasis n) (radialForm a ω t x) I =
      homotopyIntegrand a ω x (fun j => standardBasis n (indexTuple I j)) t := rfl

lemma radial_scalar_derivative {n : ℕ} (a x : E n) (t : ℝ) (m : ℕ)
    (b : E n → ℝ) (hb : DifferentiableAt ℝ b (radialPoint a x t)) :
    HasFDerivAt (fun q => t^m * b (radialPoint a q t))
      (t^(m+1) • fderiv ℝ b (radialPoint a x t)) x := by
  have hl : HasFDerivAt (fun q => radialPoint a q t)
      (t • ContinuousLinearMap.id ℝ (E n)) x := by
    convert (((hasFDerivAt_id x).sub_const a).const_smul t).const_add a using 1
    funext q
    rfl
  have hh := (hb.hasFDerivAt.comp x hl).const_mul (t^m)
  convert hh using 1
  · funext q
    rfl
  · ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, pow_succ]
    ring

/-- The finite-dimensional Cartan calculation at the radial integrand.
Only first derivatives of the coefficients are used. -/
lemma radial_homotopy_calculation {n k : ℕ} {U : Set (E n)} {a : E n}
    (ω : FormField n (k+1)) (hU : IsOpen U) (hstar : StarConvex ℝ a U)
    (hω : IsCrForm (some 1) U ω) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
    (x : E n) (hx : x ∈ U) :
    exteriorDerivative (radialForm a ω t) x +
      t^(k+1) • (exteriorDerivative ω (radialPoint a x t)).curryLeft (x-a) =
    ∑ I : MultiIndex n (k+1),
      ((k+1 : ℕ) * t^k * coefficient (standardBasis n) (ω (radialPoint a x t)) I +
        t^(k+1) * fderiv ℝ (fun q => coefficient (standardBasis n) (ω q) I)
          (radialPoint a x t) (x-a)) • dx (standardBasis n) I := by
  let b (I : MultiIndex n (k+1)) (q : E n) := coefficient (standardBasis n) (ω q) I
  let A (I : MultiIndex n (k+1)) := dx (standardBasis n) I
  let c (I : MultiIndex n (k+1)) (q : E n) := t^k * b I (radialPoint a q t)
  have hc (I : MultiIndex n (k+1)) : CrOn 1 U (c I) := by
    apply (crOn_iff_contDiffOn 1 U _ hU).mpr
    intro q hq
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_const.mul
    exact (((crOn_iff_contDiffOn 1 U (b I) hU).mp (hω.2 I)).contDiffAt
      (hU.mem_nhds (radialPoint_mem hstar hq ht))).comp q
      (contDiffAt_const.add ((contDiffAt_id.sub contDiffAt_const).const_smul t))
  have hd (I : MultiIndex n (k+1)) : HasFDerivAt (c I)
      (t^(k+1) • fderiv ℝ (b I) (radialPoint a x t)) x :=
    radial_scalar_derivative a x t k (b I)
      (isCrForm_coefficient_differentiableAt U ω hω _ (radialPoint_mem hstar hx ht) I)
  have hex : radialForm a ω t = fun q => ∑ I : MultiIndex n (k+1), c I q • (A I).curryLeft (q-a) := by
    funext q
    ext v
    change t^k * ω (radialPoint a q t) (Fin.cons (q-a) v) = _
    conv_lhs => rw [covector_expansion (standardBasis n) (ω (radialPoint a q t))]
    simp only [sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum,
      AlternatingMap.curryLeft_apply_apply, Matrix.vecCons, c, b, A]
    apply Finset.sum_congr rfl
    intro I _
    ring
  rw [hex, exteriorDerivative_sum U _ hU
    (fun I => isCrForm_function_smul 1 U (c I) _ hU (hc I)
      (insertion_isCr 1 U hU a (A I))) x hx]
  simp_rw [exteriorDerivative_contraction _ a x _ (hd _).differentiableAt]
  have he (I : MultiIndex n (k+1)) :
      linearCovector (fderiv ℝ (c I) x).toLinearMap =
        t^(k+1) • linearCovector (fderiv ℝ (b I) (radialPoint a x t)).toLinearMap := by
    rw [(hd I).fderiv]
    ext v
    rfl
  simp_rw [he]
  rw [exteriorDerivative_fderiv U ω hω _ (radialPoint_mem hstar hx ht)]
  have hcur : (∑ I : MultiIndex n (k+1),
      prependCovector (linearCovector (fderiv ℝ (b I) (radialPoint a x t)).toLinearMap) (A I)).curryLeft (x-a) =
      ∑ I : MultiIndex n (k+1),
        (fderiv ℝ (b I) (radialPoint a x t) (x-a) • A I -
          prependCovector (linearCovector (fderiv ℝ (b I) (radialPoint a x t)).toLinearMap)
            ((A I).curryLeft (x-a))) := by
    ext v
    simp only [AlternatingMap.curryLeft_apply_apply, sum_apply]
    apply Finset.sum_congr rfl
    intro I _
    exact congrArg (fun B : Covector (E n) (k+1) => B v)
      (curryLeft_prependCovector _ (A I) (x-a))
  change _ + t^(k+1) • (∑ I : MultiIndex n (k+1),
      prependCovector (linearCovector (fderiv ℝ (b I) (radialPoint a x t)).toLinearMap) (A I)).curryLeft (x-a) = _
  rw [hcur, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _
  simp only [prependCovector, wedge_smul_left, castCovector_smul, smul_sub, smul_smul,
    c, b, A, ← Nat.cast_smul_eq_nsmul ℝ, add_smul]
  module

lemma continuous_unitInterval {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0:ℝ) 1)) :
    Continuous (fun t : Homotopy.unitInterval => f (t.val 0)) :=
  hf.comp_continuous
    ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_subtype_val)
    (fun t => t.property)

lemma scalarIntegral_add (f g : ℝ → ℝ)
    (hf : Continuous (fun t : Homotopy.unitInterval => f (t.val 0)))
    (hg : Continuous (fun t : Homotopy.unitInterval => g (t.val 0))) :
    scalarIntegral (fun t => f t + g t) = scalarIntegral f + scalarIntegral g := by
  have h := scalarIntegral_linearCombination (ι := Fin 2) (fun _ => 1) ![f,g]
    (fun i => by fin_cases i; exact hf; exact hg)
  simpa only [Fin.sum_univ_two, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using h

lemma radial_scalar_continuous {n : ℕ} {U : Set (E n)} {a : E n}
    (hU : IsOpen U) (hstar : StarConvex ℝ a U) (b : E n → ℝ) (hb : CrOn 1 U b)
    (k : ℕ) (x : E n) (hx : x ∈ U) :
    ContinuousOn (fun t : ℝ => (k+1 : ℕ) * t^k * b (radialPoint a x t) +
      t^(k+1) * fderiv ℝ b (radialPoint a x t) (x-a)) (Icc 0 1) := by
  have hline : Continuous (fun t : ℝ => radialPoint a x t) := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hm : MapsTo (radialPoint a x) (Icc (0:ℝ) 1) U := fun _ ht => radialPoint_mem hstar hx ht
  have hbc := (crOn_iff_contDiffOn 1 U b hU).mp hb
  have h0 : ContinuousOn (fun t => b (radialPoint a x t)) (Icc (0:ℝ) 1) :=
    hbc.continuousOn.comp hline.continuousOn hm
  have h1 : ContinuousOn (fun t => fderiv ℝ b (radialPoint a x t) (x-a)) (Icc (0:ℝ) 1) :=
    ((hbc.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp hline.continuousOn hm).clm_apply
      continuousOn_const
  exact ((continuousOn_const.mul (continuousOn_id.pow k)).mul h0).add
    ((continuousOn_id.pow (k+1)).mul h1)

lemma radial_scalar_ftc {n : ℕ} {U : Set (E n)} {a : E n}
    (hU : IsOpen U) (hstar : StarConvex ℝ a U) (b : E n → ℝ) (hb : CrOn 1 U b)
    (k : ℕ) (x : E n) (hx : x ∈ U) :
    scalarIntegral (fun t : ℝ => (k+1 : ℕ) * t^k * b (radialPoint a x t) +
      t^(k+1) * fderiv ℝ b (radialPoint a x t) (x-a)) = b x := by
  let F (t : ℝ) := t^(k+1) * b (radialPoint a x t)
  let g (t : ℝ) := (k+1 : ℕ) * t^k * b (radialPoint a x t) +
      t^(k+1) * fderiv ℝ b (radialPoint a x t) (x-a)
  have hline : Continuous (fun t : ℝ => radialPoint a x t) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hm : MapsTo (radialPoint a x) (Icc (0:ℝ) 1) U := fun _ ht => radialPoint_mem hstar hx ht
  have hbc := (crOn_iff_contDiffOn 1 U b hU).mp hb
  have hF : ContinuousOn F (Icc 0 1) :=
    (continuousOn_id.pow (k+1)).mul (hbc.continuousOn.comp hline.continuousOn hm)
  have hd (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt F (g t) t := by
    have hb' := (hbc.contDiffAt (hU.mem_nhds (hm ⟨ht.1.le, ht.2.le⟩))).differentiableAt
      (by norm_num)
    have hl : HasDerivAt (fun s : ℝ => radialPoint a x s) (x-a) t := by
      convert ((hasDerivAt_id t).smul_const (x-a)).const_add a using 1
      · funext s
        rfl
      · simp
    have hh := ((hasDerivAt_id t).pow (k+1)).mul (hb'.hasFDerivAt.comp_hasDerivAt t hl)
    convert hh using 1 <;> first | rfl | (dsimp [g]; simp only [mul_one])
  have he := scalarIntegral_ftc F g hF hd
    (scalarIntegrable_of_continuous _ (radial_scalar_continuous hU hstar b hb k x hx))
  simpa only [g, F, zero_pow (Nat.succ_ne_zero k), zero_mul, sub_zero, one_pow, one_mul,
    radialPoint, Specs.D04.C13.HomotopyOperatorRegularity.Model.radialPoint,
    one_smul, add_sub_cancel] using he

/-- The positive-degree homotopy identity for the specified radial proper integral. -/
theorem homotopy_identity : Specs.D04.C13.EuclideanPoincareLemma.homotopy_identityType := by
  intro n k U a ω hU ha hstar hω
  refine ⟨homotopy_C1 ω hU ha hstar hω, ?_⟩
  intro x hx
  let b (I : MultiIndex n (k+1)) (q : E n) := coefficient (standardBasis n) (ω q) I
  let g (I : MultiIndex n (k+1)) (t : ℝ) :=
    (k+1 : ℕ) * t^k * b I (radialPoint a x t) +
      t^(k+1) * fderiv ℝ (b I) (radialPoint a x t) (x-a)
  have hg (I : MultiIndex n (k+1)) : Continuous
      (fun t : Homotopy.unitInterval => g I (t.val 0)) :=
    continuous_unitInterval (radial_scalar_continuous hU hstar (b I) (hω.2 I) k x hx)
  have hgi (I : MultiIndex n (k+1)) : scalarIntegral (g I) = b I x :=
    radial_scalar_ftc hU hstar (b I) (hω.2 I) k x hx
  have hrad (I : MultiIndex n k) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (q : E n) (hq : q ∈ U) :
      ContDiffAt ℝ 1 (fun z : ℝ × E n =>
        coefficient (standardBasis n) (radialForm a ω z.1 z.2) I) (t,q) := by
    simp_rw [radial_coefficient]
    exact homotopy_integrand_contDiffAt hU hstar 1
      ((isCrForm_finite_contDiffOn 1 U ω hU).mp hω) _ t ht q hq
  have hdH (v : Fin (k+1) → E n) :
      exteriorDerivative (homotopyOperator a ω) x v =
        scalarIntegral (fun t => exteriorDerivative (radialForm a ω t) x v) := by
    exact exteriorDerivative_integral hU (radialForm a ω) hrad x hx v
  have hdω : IsContinuousForm U (exteriorDerivative ω) :=
    (exteriorDerivative_continuous U ω hω).2
  ext v
  change exteriorDerivative (homotopyOperator a ω) x v +
    homotopyOperator a (exteriorDerivative ω) x v = ω x v
  rw [hdH, homotopy_apply (exteriorDerivative ω) hU ha hstar hdω x hx v]
  let D (t : ℝ) := exteriorDerivative (radialForm a ω t) x v
  let B (t : ℝ) := homotopyIntegrand a (exteriorDerivative ω) x v t
  let S (t : ℝ) := ∑ I : MultiIndex n (k+1), dx (standardBasis n) I v * g I t
  have he (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : D t + B t = S t := by
    have hh := congrArg (fun C : Covector (E n) (k+1) => C v)
      (radial_homotopy_calculation ω hU hstar hω t ht x hx)
    simpa only [D, B, S, g, b, add_apply, smul_apply, sum_apply,
      AlternatingMap.curryLeft_apply_apply, Matrix.vecCons, smul_eq_mul,
      homotopyIntegrand, Specs.D04.C13.HomotopyOperatorRegularity.Model.homotopyIntegrand,
      mul_comm] using hh
  have hB : Continuous (fun t : Homotopy.unitInterval => B (t.val 0)) :=
    (homotopy_integrand_continuous hstar hdω v).comp
      (show Continuous (fun t : Homotopy.unitInterval => (t, (⟨x,hx⟩ : U))) from
        continuous_id.prodMk continuous_const)
  have hS : Continuous (fun t : Homotopy.unitInterval => S (t.val 0)) :=
    continuous_finsetSum _ fun I _ => continuous_const.mul (hg I)
  have hD : Continuous (fun t : Homotopy.unitInterval => D (t.val 0)) := by
    apply (hS.sub hB).congr
    intro t
    exact (eq_sub_iff_add_eq.mpr (he _ t.property)).symm
  change scalarIntegral D + scalarIntegral B = _
  rw [← scalarIntegral_add D B hD hB, scalarIntegral_congr he,
    scalarIntegral_linearCombination _ _ hg]
  simp_rw [hgi]
  conv_rhs => rw [covector_expansion (standardBasis n) (ω x)]
  simp only [sum_apply, smul_apply, smul_eq_mul, b]
  apply Finset.sum_congr rfl
  intro I _
  exact mul_comm _ _


/-- Closedness is used only along radial segments in U. -/
theorem poincare_primitive : Specs.D04.C13.EuclideanPoincareLemma.poincare_primitiveType := by
  intro n k U a ω hU ha hstar hclosed
  have hid := homotopy_identity ω hU ha hstar hclosed.1
  have hz (x : E n) (hx : x ∈ U) :
      homotopyOperator a (exteriorDerivative ω) x = 0 := by
    ext v
    rw [homotopy_apply (exteriorDerivative ω) hU ha hstar
      (exteriorDerivative_continuous U ω hclosed.1).2 x hx v]
    change scalarIntegral (homotopyIntegrand a (exteriorDerivative ω) x v) = 0
    rw [scalarIntegral_congr (g := fun _ => 0) (by
      intro t ht
      change t^(k+1) * exteriorDerivative ω (radialPoint a x t) (Fin.cons (x-a) v) = 0
      have hez : exteriorDerivative ω (radialPoint a x t) = 0 :=
        hclosed.2 _ (radialPoint_mem hstar hx ht)
      rw [hez]
      simp), scalarIntegral_zero]
  have hd : EqOn (exteriorDerivative (homotopyOperator a ω)) ω U := by
    intro x hx
    simpa only [hz x hx, add_zero] using hid.2 x hx
  exact ⟨hid.1, hd, homotopyOperator a ω, hid.1, hd.symm⟩

/-- The displayed primitive retains every allowed finite or infinite order. -/
theorem poincare_primitive_isCr : Specs.D04.C13.EuclideanPoincareLemma.poincare_primitive_isCrType := by
  intro n k U a ω r _hr hU ha hstar hclosed hω
  exact ⟨homotopy_regularity ω r hU ha hstar hω,
    (poincare_primitive ω hU ha hstar hclosed).2.1⟩

end D04.Poincare
