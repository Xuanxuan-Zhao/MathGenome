import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.HomotopyOperatorRegularity
import MathGenome.Internal.MultivariableAnalysis.D04.C13.NormalizedFormsAndWedge
import MathGenome.Internal.MultivariableAnalysis.D04.C08.FiniteRepeated
import MathGenome.Internal.MultivariableAnalysis.D04.C01.DistanceFunction
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Filter Topology
open scoped BigOperators Classical ENNReal
namespace D04.Homotopy
abbrev unitInterval := Specs.D04.C13.HomotopyOperatorRegularity.Model.unitInterval
abbrev scalarIntegral := Specs.D04.C13.HomotopyOperatorRegularity.Model.scalarIntegral
abbrev ScalarIntegrable := Specs.D04.C13.HomotopyOperatorRegularity.Model.ScalarIntegrable
abbrev IsContinuousForm := @Specs.D04.C13.HomotopyOperatorRegularity.Model.IsContinuousForm
abbrev radialPoint := @Specs.D04.C13.HomotopyOperatorRegularity.Model.radialPoint
abbrev homotopyIntegrand := @Specs.D04.C13.HomotopyOperatorRegularity.Model.homotopyIntegrand
abbrev homotopyOperator := @Specs.D04.C13.HomotopyOperatorRegularity.Model.homotopyOperator
open JordanRegions

lemma unitInterval_closed : IsClosed unitInterval :=
  isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0)

lemma unitInterval_eq_carrier : unitInterval = Darboux.carrier (Darboux.intervalBox 0 1 zero_le_one) := by
  ext t
  simp [unitInterval, Specs.D04.C13.HomotopyOperatorRegularity.Model.unitInterval,
    Darboux.carrier, Specs.D04.C06.DarbouxIntegral.Model.carrier,
    Darboux.intervalBox, Specs.D04.C06.DarbouxIntegral.Model.intervalBox,
    Specs.D04.C06.DarbouxIntegral.Model.scalarPoint, Fin.forall_fin_one]

lemma unitInterval_jordan : Jordan unitInterval := by
  apply (jordan_iff_boundary (by decide) _ (unitInterval_eq_carrier ▸
    Darboux.carrier_isBounded (Darboux.intervalBox 0 1 zero_le_one))).mpr
  apply NullCovers.contentZero_mono (T := ({0} ∪ {Darboux.scalarPoint 1} : Set (E 1)))
  · intro t ht
    have htS := unitInterval_closed.closure_eq ▸ frontier_subset_closure ht
    have hb : 0 ≤ t 0 ∧ t 0 ≤ 1 := htS
    by_cases h0 : t 0 = 0
    · left
      apply PiLp.ext
      intro i
      fin_cases i
      exact h0
    · by_cases h1 : t 0 = 1
      · right
        apply PiLp.ext
        intro i
        fin_cases i
        exact h1
      · have hi : t ∈ interior unitInterval := by
          apply mem_interior_iff_mem_nhds.mpr
          exact Filter.mem_of_superset
            ((isOpen_Ioo.preimage (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0)).mem_nhds
              (show t 0 ∈ Ioo (0:ℝ) 1 from ⟨lt_of_le_of_ne hb.1 (Ne.symm h0), lt_of_le_of_ne hb.2 h1⟩))
            (fun _ h => ⟨h.1.le, h.2.le⟩)
        exact (ht.2 hi).elim
  · exact contentZero_union (NullCovers.singleton_contentZero (by decide) _)
      (NullCovers.singleton_contentZero (by decide) _)

lemma homotopy_coefficient {n k : ℕ} (a : E n) (ω : FormField n (k+1))
    (x : E n) (I : MultiIndex n k) :
    coefficient (standardBasis n) (homotopyOperator a ω x) I =
      scalarIntegral (homotopyIntegrand a ω x (fun j => standardBasis n (indexTuple I j))) := by
  rw [coefficient_eq_repr]
  change ((covectorBasis (standardBasis n) k).repr
    (∑ J, scalarIntegral (homotopyIntegrand a ω x
      (fun j => standardBasis n (indexTuple J j))) • (covectorBasis (standardBasis n) k) J)) I = _
  simp [Finsupp.single_apply]

open private integral Integrable integral_linear integral_euclidean integral_continuous
  from MathGenome.Internal.MultivariableAnalysis.D04.C08.FiniteRepeated

private def scalarPointCLM : ℝ →L[ℝ] E 1 :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (standardBasis 1 0)

@[simp] private lemma scalarPointCLM_apply (t : ℝ) : scalarPointCLM t 0 = t := by
  simp [scalarPointCLM, standardBasis_apply]

private lemma integral_eq_scalar {d : ℕ} {S : Set (E d)} (f : S → ℝ)
    (hf : Integrable f) : integral f = regionIntegral f := by
  have hp := integral_linear f scalarPointCLM hf
  have he := integral_euclidean (fun t => scalarPointCLM (f t)) hp.1
  have h := congrArg (fun v : E 1 => v 0) (hp.2.symm.trans he.2)
  simpa [vectorRegionIntegral, Specs.D04.C06.JordanRegions.Model.vectorRegionIntegral] using h

lemma scalar_integral_continuous {m : ℕ} {P : Set (E m)}
    (f : ℝ → E m → ℝ)
    (hf : Continuous (fun z : unitInterval × P => f (z.1.val 0) z.2)) :
    (∀ p ∈ P, ScalarIntegrable (fun t => f t p)) ∧
    ContinuousOn (fun p => scalarIntegral (fun t => f t p)) P := by
  have hclosed : closure unitInterval = unitInterval := unitInterval_closed.closure_eq
  let g : closure unitInterval → E m → ℝ := fun t p => f (t.val 0) p
  have hc : Continuous (fun z : closure unitInterval × P =>
      ((⟨z.1.val, by simpa only [hclosed] using z.1.property⟩ : unitInterval), z.2)) := by
    fun_prop
  have hg : Continuous (fun z : closure unitInterval × P => g z.1 z.2) := by
    exact hf.comp hc
  have h := integral_continuous unitInterval_jordan g hg
  have he (p : E m) (hp : p ∈ P) :
      integral (fun t : unitInterval => f (t.val 0) p) = scalarIntegral (fun t => f t p) :=
    integral_eq_scalar _ (h.1 p hp)
  refine ⟨?_, h.2.congr (fun p hp => (he p hp).symm)⟩
  intro p hp
  have hp' := integral_linear (fun t : unitInterval => f (t.val 0) p) scalarPointCLM (h.1 p hp)
  have hi := (integral_euclidean _ hp'.1).1.2 (0 : Fin 1)
  simpa only [scalarPointCLM_apply, ScalarIntegrable,
    Specs.D04.C13.HomotopyOperatorRegularity.Model.ScalarIntegrable] using hi

lemma radialPoint_mem {n : ℕ} {U : Set (E n)} {a x : E n}
    (hstar : StarConvex ℝ a U) (hx : x ∈ U) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    radialPoint a x t ∈ U := by
  have h := hstar hx (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  convert h using 1
  simp only [radialPoint, Specs.D04.C13.HomotopyOperatorRegularity.Model.radialPoint,
    sub_smul, one_smul, smul_sub]
  abel

lemma continuous_radialPoint {n : ℕ} (a : E n) :
    Continuous (fun z : ℝ × E n => radialPoint a z.2 z.1) :=
  continuous_const.add (continuous_fst.smul (continuous_snd.sub continuous_const))

/-- Evaluation at varying vectors is a finite sum of coefficient functions
multiplied by polynomial functions of those vectors. -/
lemma continuous_form_eval {n k : ℕ} {X : Type} [TopologicalSpace X]
    {U : Set (E n)} {ω : FormField n k} (hω : IsContinuousForm U ω)
    (p : X → E n) (hp : Continuous p) (hmem : ∀ z, p z ∈ U)
    (v : X → Fin k → E n) (hv : ∀ j, Continuous (fun z => v z j)) :
    Continuous (fun z => ω (p z) (v z)) := by
  have hrepr (z : X) := congrArg (fun A : Covector (E n) k => A (v z))
    (covector_expansion (standardBasis n) (ω (p z)))
  simp only [sum_apply, smul_apply, smul_eq_mul] at hrepr
  refine Continuous.congr (f := fun z => ∑ I : MultiIndex n k,
    coefficient (standardBasis n) (ω (p z)) I * dx (standardBasis n) I (v z)) ?_ ?_
  · apply continuous_finsetSum
    intro I _
    apply ((hω I).comp_continuous hp hmem).mul
    simp_rw [dx_apply]
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact ((standardBasis n).coord (indexTuple I i)).continuous_of_finiteDimensional.comp (hv j)
  · intro z
    exact (hrepr z).symm

lemma homotopy_integrand_continuous {n k : ℕ} {U : Set (E n)} {a : E n}
    {ω : FormField n (k+1)} (hstar : StarConvex ℝ a U) (hω : IsContinuousForm U ω)
    (v : Fin k → E n) :
    Continuous (fun z : unitInterval × U => homotopyIntegrand a ω z.2 v (z.1.val 0)) := by
  apply (show Continuous (fun z : unitInterval × U => (z.1.val 0) ^ k) from
    ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
      (continuous_subtype_val.comp continuous_fst)).pow k).mul
  apply continuous_form_eval hω
    (fun z : unitInterval × U => radialPoint a z.2 (z.1.val 0))
  · exact (continuous_radialPoint a).comp
      (((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
        (continuous_subtype_val.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd))
  · intro z
    exact radialPoint_mem hstar z.2.property z.1.property
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact (continuous_subtype_val.comp continuous_snd).sub continuous_const
    · exact continuous_const

theorem homotopy_integrable : Specs.D04.C13.HomotopyOperatorRegularity.homotopy_integrableType := by
  intro n k U a ω hU ha hstar hω x hx v
  exact (scalar_integral_continuous (fun t p => homotopyIntegrand a ω p v t)
    (homotopy_integrand_continuous hstar hω v)).1 x hx

theorem homotopy_continuous : Specs.D04.C13.HomotopyOperatorRegularity.homotopy_continuousType := by
  intro n k U a ω hU ha hstar hω I
  change ContinuousOn (fun x => coefficient (standardBasis n) (homotopyOperator a ω x) I) U
  simp_rw [homotopy_coefficient]
  exact (scalar_integral_continuous (fun t p => homotopyIntegrand a ω p _ t)
    (homotopy_integrand_continuous hstar hω _)).2

/-- Joint continuity of partial iterated derivatives is proved locally on
an open set, so endpoints of the integration interval cause no loss of order. -/
lemma partial_iterated_contDiffAt {X Y Z : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : X × Y → Z) (r j : ℕ) (z : X × Y)
    (hf : ContDiffAt ℝ ((r+j : ℕ) : WithTop ℕ∞) f z) :
    ContDiffAt ℝ (r : WithTop ℕ∞)
      (fun w : X × Y => iteratedFDeriv ℝ j (fun y => f (w.1,y)) w.2) z := by
  induction j generalizing r with
  | zero =>
    simp only [Nat.add_zero] at hf
    convert hf.continuousLinearMap_comp
        (continuousMultilinearCurryFin0 ℝ Y Z).symm.toContinuousLinearEquiv.toContinuousLinearMap using 1
    funext w
    rfl
  | succ j ih =>
    have hf' : ContDiffAt ℝ (((r+1)+j : ℕ) : WithTop ℕ∞) f z := by
      convert hf using 1; congr 1; omega
    have hh := ih (r+1) hf'
    have hcomp : ContDiffAt ℝ ((r+1 : ℕ) : WithTop ℕ∞)
        (fun w : (X × Y) × Y => iteratedFDeriv ℝ j (fun y => f (w.1.1,y)) w.2)
        (z,z.2) := hh.comp (z,z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd := ContDiffAt.fderiv
      (f := fun (w : X × Y) (y : Y) => iteratedFDeriv ℝ j (fun y => f (w.1,y)) y)
      (g := fun w : X × Y => w.2) hcomp contDiffAt_snd
      (m := (r : WithTop ℕ∞)) (by simp only [Nat.cast_add, Nat.cast_one]; rfl)
    convert hd.continuousLinearMap_comp
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => Y) Z).symm.toContinuousLinearEquiv.toContinuousLinearMap using 1
    funext w
    rfl

lemma scalar_integral_cr {m : ℕ} {P : Set (E m)} (hP : IsOpen P) (r : ℕ)
    (f : ℝ × E m → ℝ)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ∀ p ∈ P,
      ContDiffAt ℝ (r : WithTop ℕ∞) f (t,p)) :
    CrOn r P (fun p => scalarIntegral (fun t => f (t,p))) := by
  let g : unitInterval → E m → E 1 := fun t p => scalarPointCLM (f (t.val 0,p))
  let T (j : ℕ) (t : closure unitInterval) (p : E m) :=
    iteratedFDeriv ℝ j (fun q => scalarPointCLM (f (t.val 0,q))) p
  have ht (t : closure unitInterval) : t.val 0 ∈ Icc (0:ℝ) 1 := by
    exact (show t.val ∈ unitInterval from by
      simpa only [unitInterval_closed.closure_eq] using t.property)
  have hgd (t : unitInterval) : ContDiffOn ℝ (r : WithTop ℕ∞) (g t) P := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    exact scalarPointCLM.contDiff.contDiffAt.comp p
      ((hf _ t.property p hp).comp p (contDiffAt_const.prodMk contDiffAt_id))
  have hTc (j : ℕ) (hj : j ≤ r) :
      Continuous (fun z : closure unitInterval × P => T j z.1 z.2) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hh : ContDiffAt ℝ (j : WithTop ℕ∞) (fun w : ℝ × E m => scalarPointCLM (f w))
        (z.1.val 0,z.2.val) :=
      scalarPointCLM.contDiff.contDiffAt.comp _ ((hf _ (ht z.1) _ z.2.property).of_le
        (by exact_mod_cast hj))
    have h := partial_iterated_contDiffAt (fun w : ℝ × E m => scalarPointCLM (f w)) 0 j
      (z.1.val 0,z.2.val) (by simpa using hh)
    let q : closure unitInterval × P → ℝ × E m := fun w => (w.1.val 0,w.2.val)
    have hq : Continuous q :=
      ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
        (continuous_subtype_val.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd)
    exact h.continuousAt.comp (f := q) hq.continuousAt
  have H := FiniteRepeated.finite_repeated unitInterval_jordan hP r g T
    (fun t p hp => crOn_timesDifferentiableAt r P (g t) hP
      ((crOn_iff_contDiffOn r P _ hP).mpr (hgd t)) p hp)
    hTc (fun j hj t p hp => rfl)
  have hc := (PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (β := fun _ : Fin 1 => ℝ) 0).contDiff.comp_contDiffOn
    ((crOn_iff_contDiffOn r P _ hP).mp H.2.1)
  apply (crOn_iff_contDiffOn r P _ hP).mpr
  convert hc using 1
  funext p
  simp only [g, Function.comp_def,
    Specs.D04.C06.JordanRegions.Model.vectorRegionIntegral,
    PiLp.proj_apply, scalarPointCLM_apply]
  rfl


lemma contDiffAt_form_eval {n k : ℕ} {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {U : Set (E n)} (hU : IsOpen U) {ω : FormField n k} (r : ℕ)
    (hω : ∀ I : MultiIndex n k,
      ContDiffOn ℝ (r : WithTop ℕ∞) (fun x => coefficient (standardBasis n) (ω x) I) U)
    (p : X → E n) (z : X) (hp : ContDiffAt ℝ (r : WithTop ℕ∞) p z) (hmem : p z ∈ U)
    (v : X → Fin k → E n) (hv : ∀ j, ContDiffAt ℝ (r : WithTop ℕ∞) (fun w => v w j) z) :
    ContDiffAt ℝ (r : WithTop ℕ∞) (fun w => ω (p w) (v w)) z := by
  have hrepr (w : X) := congrArg (fun A : Covector (E n) k => A (v w))
    (covector_expansion (standardBasis n) (ω (p w)))
  simp only [sum_apply, smul_apply, smul_eq_mul] at hrepr
  have he : (fun w => ω (p w) (v w)) = (fun w => ∑ I : MultiIndex n k,
      coefficient (standardBasis n) (ω (p w)) I * dx (standardBasis n) I (v w)) := funext hrepr
  rw [he]
  apply ContDiffAt.sum
  intro I _
  apply (((hω I).contDiffAt (hU.mem_nhds hmem)).comp z hp).mul
  simp_rw [dx_apply, Matrix.det_apply]
  apply ContDiffAt.sum
  intro σ _
  apply ContDiffAt.const_smul
  apply contDiffAt_prod
  intro j _
  exact ((standardBasis n).coord (indexTuple I (σ j))).toContinuousLinearMap.contDiff.contDiffAt.comp z (hv j)

lemma homotopy_integrand_contDiffAt {n k : ℕ} {U : Set (E n)} {a : E n}
    {ω : FormField n (k+1)} (hU : IsOpen U) (hstar : StarConvex ℝ a U)
    (r : ℕ) (hω : ∀ I : MultiIndex n (k+1),
      ContDiffOn ℝ (r : WithTop ℕ∞) (fun x => coefficient (standardBasis n) (ω x) I) U)
    (v : Fin k → E n) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : E n) (hx : x ∈ U) :
    ContDiffAt ℝ (r : WithTop ℕ∞) (fun z : ℝ × E n => homotopyIntegrand a ω z.2 v z.1) (t,x) := by
  apply (contDiffAt_fst.pow k).mul
  apply contDiffAt_form_eval hU r hω (fun z : ℝ × E n => radialPoint a z.2 z.1) (t,x)
  · exact contDiffAt_const.add (contDiffAt_fst.smul (contDiffAt_snd.sub contDiffAt_const))
  · exact radialPoint_mem hstar hx ht
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact contDiffAt_snd.sub contDiffAt_const
    · exact contDiffAt_const

theorem homotopy_isCr : Specs.D04.C13.HomotopyOperatorRegularity.homotopy_isCrType := by
  intro n k U a ω r hU ha hstar hω
  have hfinite (s : ℕ) (hs : IsCrForm (some s) U ω) :
      IsCrForm (some s) U (homotopyOperator a ω) := by
    refine ⟨hU, fun I => ?_⟩
    change CrOn s U (fun x => coefficient (standardBasis n) (homotopyOperator a ω x) I)
    simp_rw [homotopy_coefficient]
    apply scalar_integral_cr hU s
      (fun z : ℝ × E n => homotopyIntegrand a ω z.2
        (fun j => standardBasis n (indexTuple I j)) z.1)
    intro t ht x hx
    exact homotopy_integrand_contDiffAt hU hstar s
      ((isCrForm_finite_contDiffOn s U ω hU).mp hs) _ t ht x hx
  cases r with
  | some s => exact hfinite s hω
  | none =>
    refine ⟨hU, fun I s => ?_⟩
    exact (hfinite s ⟨hU, fun J => hω.2 J s⟩).2 I

private lemma continuous_interval_integrable {Y : Type} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (f : ℝ → Y)
    (hf : Continuous (fun t : unitInterval => f (t.val 0))) :
    Integrable (fun t : unitInterval => f (t.val 0)) := by
  have hclosed := unitInterval_closed.closure_eq
  let g : closure unitInterval → E 0 → Y := fun t _ => f (t.val 0)
  have hc : Continuous (fun t : closure unitInterval =>
      (⟨t.val, by simpa only [hclosed] using t.property⟩ : unitInterval)) := by fun_prop
  have hg : Continuous (fun z : closure unitInterval × (univ : Set (E 0)) => g z.1 z.2) :=
    (hf.comp hc).comp continuous_fst
  exact (integral_continuous unitInterval_jordan g hg).1 0 (mem_univ _)

lemma scalarIntegral_linearCombination {ι : Type} [Fintype ι] (c : ι → ℝ) (f : ι → ℝ → ℝ)
    (hf : ∀ i, Continuous (fun t : unitInterval => f i (t.val 0))) :
    scalarIntegral (fun t => ∑ i, c i * f i t) = ∑ i, c i * scalarIntegral (f i) := by
  let g : unitInterval → (ι → ℝ) := fun t i => f i (t.val 0)
  have hg : Integrable g := continuous_interval_integrable (fun t i => f i t) (continuous_pi hf)
  let L : (ι → ℝ) →L[ℝ] ℝ := ∑ i, c i • ContinuousLinearMap.proj i
  have h := integral_linear g L hg
  have hi (i : ι) := integral_linear g (ContinuousLinearMap.proj i) hg
  have he (i : ι) : scalarIntegral (f i) = (integral g) i :=
    (integral_eq_scalar _ (hi i).1).symm.trans (hi i).2
  calc
    scalarIntegral (fun t => ∑ i, c i * f i t) = integral (fun t => L (g t)) := by
      rw [integral_eq_scalar _ h.1]
      simp only [scalarIntegral, Specs.D04.C13.HomotopyOperatorRegularity.Model.scalarIntegral,
        L, g, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    _ = L (integral g) := h.2
    _ = ∑ i, c i * scalarIntegral (f i) := by
      simp only [L, sum_apply, smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, he]

theorem homotopy_apply : Specs.D04.C13.HomotopyOperatorRegularity.homotopy_applyType := by
  intro n k U a ω hU ha hstar hω x hx v
  let b (I : MultiIndex n k) : Fin k → E n := fun j => standardBasis n (indexTuple I j)
  have hf (I : MultiIndex n k) :
      Continuous (fun t : unitInterval => homotopyIntegrand a ω x (b I) (t.val 0)) :=
    (homotopy_integrand_continuous hstar hω (b I)).comp
      (show Continuous (fun t : unitInterval => (t, (⟨x,hx⟩ : U))) from
        continuous_id.prodMk continuous_const)
  have hex (t : ℝ) : homotopyIntegrand a ω x v t =
      ∑ I : MultiIndex n k, dx (standardBasis n) I v * homotopyIntegrand a ω x (b I) t := by
    let A : Covector (E n) k := t ^ k • (ω (radialPoint a x t)).curryLeft (x-a)
    have h := congrArg (fun B : Covector (E n) k => B v)
      (covector_expansion (standardBasis n) A)
    simpa only [A, coefficient, Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient,
      sum_apply, smul_apply, smul_eq_mul, AlternatingMap.curryLeft_apply_apply, mul_comm,
      homotopyIntegrand, Specs.D04.C13.HomotopyOperatorRegularity.Model.homotopyIntegrand,
      b, Matrix.vecCons] using h
  calc
    homotopyOperator a ω x v =
        ∑ I : MultiIndex n k, dx (standardBasis n) I v * scalarIntegral (homotopyIntegrand a ω x (b I)) := by
      change (∑ I : MultiIndex n k, scalarIntegral (homotopyIntegrand a ω x (b I)) •
        dx (standardBasis n) I) v = _
      simp only [sum_apply, smul_apply, smul_eq_mul, mul_comm]
    _ = scalarIntegral (fun t => ∑ I : MultiIndex n k,
        dx (standardBasis n) I v * homotopyIntegrand a ω x (b I) t) :=
      (scalarIntegral_linearCombination _ _ hf).symm
    _ = scalarIntegral (homotopyIntegrand a ω x v) := congrArg scalarIntegral (funext hex).symm

lemma scalarIntegral_zero : scalarIntegral (fun _ => 0) = 0 := by
  simpa using (scalarIntegral_linearCombination (ι := Fin 0) (fun _ => 0)
    (fun _ _ => 0) (fun i => Fin.elim0 i))

theorem homotopy_zero {n k : ℕ} (a : E n) :
    homotopyOperator a (0 : FormField n (k+1)) = 0 := by
  funext x
  change (∑ I : MultiIndex n k,
    scalarIntegral (fun t => t ^ k * (0 : ℝ)) • dx (standardBasis n) I) = 0
  simp only [mul_zero, scalarIntegral_zero, zero_smul, Finset.sum_const_zero]

theorem homotopy_above_dimension {n k : ℕ} (a : E n) (ω : FormField n (k+1))
    (hk : n < k+1) : homotopyOperator a ω = 0 := by
  have he : ω = 0 := by
    funext x
    apply covector_eq_zero_above_dimension
    simpa [E, Specs.D04.C01.EuclideanInterfaces.Model.E] using hk
  rw [he, homotopy_zero]

end D04.Homotopy
