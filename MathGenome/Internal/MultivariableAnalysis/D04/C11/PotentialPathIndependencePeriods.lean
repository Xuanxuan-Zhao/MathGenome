import MathGenome.Internal.MultivariableAnalysis.D04.C11.EuclideanVectorOperators
import MathGenome.Internal.MultivariableAnalysis.D04.C09.GradientIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C09.PathAlgebra
import MathGenome.Internal.MultivariableAnalysis.D04.C01.Components
import MathGenome.Internal.MultivariableAnalysis.D04.C02.CrCalculus
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.PotentialPathIndependencePeriods
import Mathlib.Analysis.Calculus.MeanValue
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.UniformStability

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04.C11
open D04.C09 D04.C09.PathAlgebra
open SingleVariableAnalysis.Riemann

abbrev IsPotential := @Specs.D04.C11.PotentialPathIndependencePeriods.Model.IsPotential
abbrev HasPotential := @Specs.D04.C11.PotentialPathIndependencePeriods.Model.HasPotential
abbrev PathIndependent := @Specs.D04.C11.PotentialPathIndependencePeriods.Model.PathIndependent
abbrev ZeroPeriods := @Specs.D04.C11.PotentialPathIndependencePeriods.Model.ZeroPeriods

theorem work_integrable_in_domain {n a b} (U : Set (E n)) (F : E n → E n)
    (γ : IntervalPath n a b) (v : PiecewiseC1Data γ)
    (hF : ContinuousOn F U) (hγ : trace γ ⊆ U) : WorkIntegrable v F :=
  work_integrable v F (hF.mono hγ)

/-- Changing only field values outside the trace does not change work. -/
lemma work_congr {n a b} {γ : IntervalPath n a b} (v : PiecewiseC1Data γ)
    (F G : E n → E n) (h : EqOn F G (trace γ))
    (hF : WorkIntegrable v F) (hG : WorkIntegrable v G) :
    workLineIntegral v F hF = workLineIntegral v G hG := by
  change (∑ i, realIntegral _ (hF i)) = ∑ i, realIntegral _ (hG i)
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨hi, he⟩ := riemann_congr (hF i) (fun t ht =>
    congrArg (fun y => inner ℝ y (v.velocity i t))
      (h ⟨t, cell_subset_interval v.partition i ht, rfl⟩))
  exact he.symm

lemma potential_integral {n a b} (U : Set (E n)) (F : E n → E n)
    (f : E n → ℝ) (hU : IsOpen U) (hf : IsPotential U F f)
    (γ : IntervalPath n a b) (v : PiecewiseC1Data γ) (hγ : trace γ ⊆ U)
    (hv : WorkIntegrable v F) :
    workLineIntegral v F hv = f (γ b) - f (γ a) := by
  obtain ⟨_, hw, _, he⟩ := gradient_integral v U f hU hf.1 hγ
  exact (work_congr v F (scalarGradient f) (fun x hx => (hf.2 (hγ hx)).symm) hv hw).trans he

lemma potential_pathIndependent {n} (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hf : HasPotential U F) : PathIndependent U F := by
  obtain ⟨f,hf⟩ := hf
  intro a b c d γ η v w hγ hη hstart hend hv hw
  change workLineIntegral v F hv = workLineIntegral w F hw
  rw [potential_integral U F f hU hf γ v hγ hv,
    potential_integral U F f hU hf η w hη hw, hstart, hend]

lemma pathIndependent_zeroPeriods {n} (U : Set (E n)) (F : E n → E n)
    (h : PathIndependent U F) : ZeroPeriods U F := by
  intro a b γ v hγ hclosed hv
  let η : IntervalPath n a a := ⟨le_rfl, fun _ => γ a, continuousOn_const⟩
  obtain ⟨w⟩ := constant_piecewiseC1 η (γ a) (by intros; rfl)
  have hw : WorkIntegrable w F := pieceIntegrable_degenerate w _
  have he := h γ η v w hγ (by
    rintro x ⟨t,ht,rfl⟩
    exact hγ ⟨a, ⟨le_rfl,γ.ordered⟩,rfl⟩) rfl hclosed.symm hv hw
  exact he.trans (pieceIntegral_degenerate w _ hw)

/-- A path together with its actual work integrability, retaining arbitrary
parameter intervals. This is only a proof helper, not a new path convention. -/
structure WorkPath {n} (U : Set (E n)) (F : E n → E n) (x y : E n) where
  a : ℝ
  b : ℝ
  path : IntervalPath n a b
  data : PiecewiseC1Data path
  inside : trace path ⊆ U
  start : path a = x
  finish : path b = y
  integrable : WorkIntegrable data F

def WorkPath.work {n U F x y} (p : @WorkPath n U F x y) : ℝ :=
  workLineIntegral p.data F p.integrable

lemma WorkPath.append {n U F x y z} (p : @WorkPath n U F x y)
    (q : WorkPath U F y z) : ∃ r : WorkPath U F x z, r.work = p.work + q.work := by
  obtain ⟨κ,d,_,hκ,hl,hr,_,_,he⟩ := arbitrary_concatenate
    (p.finish.trans q.start.symm) p.data q.data (fun _ => 0) (workCovector F)
    (scalar_integrable _ _ continuousOn_const) (scalar_integrable _ _ continuousOn_const)
    p.integrable q.integrable
  have hstart : κ p.a = x := (hl p.a ⟨le_rfl,p.path.ordered⟩).trans p.start
  have hend : κ (p.b + (q.b-q.a)) = z := by
    rw [hr _ ⟨by linarith [q.path.ordered],le_rfl⟩]
    convert q.finish using 1
    congr 1
    ring
  have hi : trace κ ⊆ U := by
    rintro w ⟨t,ht,rfl⟩
    by_cases h : t ≤ p.b
    · rw [hl t ⟨ht.1,h⟩]
      exact p.inside ⟨t,⟨ht.1,h⟩,rfl⟩
    · rw [hr t ⟨by linarith,ht.2⟩]
      exact q.inside ⟨t+q.a-p.b,⟨by linarith,by linarith [ht.2]⟩,rfl⟩
  exact ⟨⟨p.a,_,κ,d,hi,hstart,hend,hκ⟩,he⟩

lemma WorkPath.reverse {n U F x y} (p : @WorkPath n U F x y) :
    ∃ q : WorkPath U F y x, q.work = -p.work := by
  obtain ⟨d,_,hd,_,he⟩ := reverse_integrable p.data (fun _ => 0) (workCovector F)
    (scalar_integrable _ _ continuousOn_const) p.integrable
  refine ⟨⟨p.a,p.b,PathAlgebra.reverse p.path,d,?_,?_,?_,hd⟩,he⟩
  · rintro w ⟨t,ht,rfl⟩
    exact p.inside ⟨p.a+p.b-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,rfl⟩
  · change p.path (p.a+p.b-p.a) = y
    simpa using p.finish
  · change p.path (p.a+p.b-p.b) = x
    simpa using p.start

lemma zeroPeriods_pathIndependent {n} (U : Set (E n)) (F : E n → E n)
    (h : ZeroPeriods U F) : PathIndependent U F := by
  intro a b c d γ η v w hγ hη hstart hend hv hw
  let p : WorkPath U F (γ a) (γ b) := ⟨a,b,γ,v,hγ,rfl,rfl,hv⟩
  let q : WorkPath U F (γ a) (γ b) := ⟨c,d,η,w,hη,hstart.symm,hend.symm,hw⟩
  obtain ⟨q',hq⟩ := q.reverse
  obtain ⟨r,hr⟩ := p.append q'
  have hz := h r.path r.data r.inside (r.start.trans r.finish.symm) r.integrable
  change r.work = 0 at hz
  change p.work = q.work
  linarith

/-- The affine segment, with a single C¹ piece, including a stationary one. -/
def segmentPath {n} (x y : E n) : IntervalPath n 0 1 :=
  ⟨by norm_num, fun t => x + t • (y-x), by fun_prop⟩

def segmentData {n} (x y : E n) : PiecewiseC1Data (segmentPath x y) where
  partition := uniformPartition (by norm_num : (0:ℝ)<1) 1 (by omega)
  velocity := fun _ _ => y-x
  smooth := by
    intro i
    refine ⟨continuousOn_const, fun t ht => ?_⟩
    simpa [segmentPath] using
      ((hasDerivAt_id t).smul_const (y-x) |>.const_add x).hasDerivWithinAt (s := Icc ((uniformPartition (by norm_num : (0:ℝ)<1) 1 (by omega)).point i.castSucc) ((uniformPartition (by norm_num : (0:ℝ)<1) 1 (by omega)).point i.succ))

lemma segmentPath_inside {n} {U : Set (E n)} {x y : E n}
    (h : segment ℝ x y ⊆ U) : trace (segmentPath x y) ⊆ U := by
  rintro w ⟨t,ht,rfl⟩
  apply h
  rw [segment_eq_image_lineMap]
  exact ⟨t,ht,by simp [segmentPath, AffineMap.lineMap_apply_module, sub_smul, smul_sub]; abel⟩

def segmentWorkPath {n U F x y} (hF : ContinuousOn F U)
    (h : segment ℝ x y ⊆ U) : @WorkPath n U F x y where
  a := 0
  b := 1
  path := segmentPath x y
  data := segmentData x y
  inside := segmentPath_inside h
  start := by simp [segmentPath]
  finish := by simp [segmentPath]
  integrable := work_integrable_in_domain U F _ _ hF (segmentPath_inside h)

/-- Open connected domains supply actual piecewise C¹ work paths. -/
lemma workPath_exists {n} (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hc : IsPreconnected U) (hF : ContinuousOn F U)
    (x y : E n) (hx : x ∈ U) (hy : y ∈ U) : Nonempty (WorkPath U F x y) := by
  classical
  obtain ⟨⟨⟨N,v⟩,hs,he,hseg⟩⟩ := open_connected_polygonallyConnected U
    ((open_iff_isOpen U).mpr hU) hc ⟨x,hx⟩ ⟨y,hy⟩
  dsimp only at hs he hseg
  have reach : ∀ k : Fin (N+1), Nonempty (WorkPath U F x (v k)) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      have hxx : segment ℝ x x ⊆ U := by simpa using hx
      exact ⟨by simpa [hs] using segmentWorkPath hF hxx⟩
    | succ k ih =>
      obtain ⟨p⟩ := ih
      obtain ⟨r,_⟩ := p.append (segmentWorkPath hF (hseg k))
      exact ⟨r⟩
  simpa [he] using reach (Fin.last N)

lemma segment_work_integral {n : ℕ} {U : Set (E n)} {F : E n → E n} {x y : E n} (hF : ContinuousOn F U)
    (h : segment ℝ x y ⊆ U) :
    ∃ hi : RealIntegrable (fun t : ℝ => inner ℝ (F (x+t • (y-x))) (y-x)) 0 1,
      (segmentWorkPath hF h).work = realIntegral _ hi := by
  let p := segmentWorkPath hF h
  have hi := p.integrable (0 : Fin 1)
  dsimp [p,segmentWorkPath,segmentData,segmentPath,uniformPartition] at hi
  norm_num at hi
  refine ⟨hi, ?_⟩
  change (∑ i : Fin 1, realIntegral _ (p.integrable i)) = _
  rw [Fin.sum_univ_one]
  simp [p,segmentWorkPath,segmentData,segmentPath,uniformPartition]

lemma realIntegral_constant_unit (c : ℝ) (hc : RealIntegrable (fun _ => c) 0 1) :
    realIntegral _ hc = c := by
  have h := real_ftc_second (fun t : ℝ => t*c) (fun _ => c) 0 1
    (by norm_num) (by fun_prop)
    (fun t _ => by simpa using (hasDerivAt_id t).mul_const c) hc
  simpa using h

/-- The source's short-segment remainder estimate, for a merely continuous F. -/
lemma segment_work_error {n : ℕ} {U : Set (E n)} {F : E n → E n} {x y : E n} (hF : ContinuousOn F U)
    (h : segment ℝ x y ⊆ U) (ε : ℝ)
    (hε : ∀ t ∈ Icc (0:ℝ) 1, ‖F (x+t • (y-x)) - F x‖ ≤ ε) :
    |(segmentWorkPath hF h).work - inner ℝ (F x) (y-x)| ≤ ε * ‖y-x‖ := by
  obtain ⟨hi,he⟩ := segment_work_integral hF h
  have hc : RealIntegrable (fun _ : ℝ => inner ℝ (F x) (y-x)) 0 1 :=
    riemann_integrable_of_continuousOn (by norm_num) continuousOn_const
  obtain ⟨hd,hde⟩ := real_sub_value hi hc
  obtain ⟨hn,hne,_⟩ := real_norm_estimate _ hd
  rw [he, ← realIntegral_constant_unit _ hc, ← hde]
  apply hne.trans
  have hbound := realIntegral_le_mul_bound hn (M := ε * ‖y-x‖) (fun t ht => ?_)
  · simpa using hbound
  · change |inner ℝ (F (x+t • (y-x))) (y-x) - inner ℝ (F x) (y-x)| ≤ _
    rw [← inner_sub_left]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hε t ht) (norm_nonneg _))

lemma isPotential_of_hasFDerivAt {n} (U : Set (E n)) (F : E n → E n)
    (f : E n → ℝ) (hU : IsOpen U) (hF : ContinuousOn F U)
    (hf : ∀ x ∈ U, HasFDerivAt f (workCovector F x) x) : IsPotential U F f := by
  have he : EqOn (totalDerivative f) (workCovector F) U := fun x hx => (hf x hx).fderiv
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    exact ⟨_,(hasTotalDerivative_iff_hasFDerivAt U f _ x hU hx).mpr (hf x hx)⟩
  · change ContinuousOn (totalDerivative f) U
    exact ((innerSL ℝ).continuous.comp_continuousOn hF).congr (fun x hx => he hx)
  · intro x hx
    apply ext_inner_right ℝ
    intro v
    change inner ℝ (scalarGradient f x) v = inner ℝ (F x) v
    rw [← scalarGradient_represents]
    exact congrArg (fun A : E n →L[ℝ] ℝ => A v) (he hx)

/-- Work from one basepoint is independent of the choice of work path. -/
lemma pathIndependent_hasPotential {n} (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hc : IsPreconnected U) (hF : ContinuousOn F U)
    (h : PathIndependent U F) : HasPotential U F := by
  classical
  by_cases hn : U.Nonempty
  · obtain ⟨a,ha⟩ := hn
    let p (x : E n) (hx : x ∈ U) : WorkPath U F a x :=
      Classical.choice (workPath_exists U F hU hc hF a x ha hx)
    let f : E n → ℝ := fun x => if hx : x ∈ U then (p x hx).work else 0
    have hvalue {x : E n} (hx : x ∈ U) (q : WorkPath U F a x) : f x = q.work := by
      dsimp only [f]; rw [dite_eq_left hx]
      exact h (p x hx).path q.path (p x hx).data q.data (p x hx).inside q.inside
        ((p x hx).start.trans q.start.symm) ((p x hx).finish.trans q.finish.symm)
        (p x hx).integrable q.integrable
    refine ⟨f,isPotential_of_hasFDerivAt U F f hU hF ?_⟩
    intro x hx
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    have hFx : ContinuousAt F x := (hF x hx).continuousAt (hU.mem_nhds hx)
    obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hFx ε hε
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU x hx
    filter_upwards [Metric.ball_mem_nhds (0 : E n) (lt_min hδ hr)] with v hv
    have hvδ : ‖v‖ < δ := (lt_min_iff.mp (by simpa [Metric.mem_ball,dist_zero_right] using hv)).1
    have hvr : ‖v‖ < r := (lt_min_iff.mp (by simpa [Metric.mem_ball,dist_zero_right] using hv)).2
    have hseg : segment ℝ x (x+v) ⊆ U :=
      ((convex_ball x r).segment_subset (Metric.mem_ball_self hr)
        (by simpa [Metric.mem_ball,dist_eq_norm] using hvr)).trans hball
    have hnext : x+v ∈ U := hseg (right_mem_segment ℝ x (x+v))
    let s := segmentWorkPath hF hseg
    obtain ⟨q,hq⟩ := (p x hx).append s
    have hinc : f (x+v) - f x = s.work := by
      rw [hvalue hnext q, hvalue hx (p x hx), hq]; ring
    rw [hinc]
    change |s.work - inner ℝ (F x) v| ≤ ε * ‖v‖
    have herr := segment_work_error hF hseg ε (fun t ht => ?_)
    · simpa only [add_sub_cancel_left] using herr
    · have hn : ‖t • v‖ ≤ ‖v‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2
      have hd : dist (x+t • ((x+v)-x)) x < δ := by
        simpa [dist_eq_norm] using hn.trans_lt hvδ
      simpa [dist_eq_norm] using (hclose hd).le
  · have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    subst U
    refine ⟨fun _ => 0, ?_⟩
    exact ⟨⟨by intro x hx; simp at hx, continuousOn_empty _⟩, fun x hx => False.elim hx⟩

/-- The full potential / endpoints / closed-period equivalence. -/
theorem potential_equivalences {n} (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hc : IsPreconnected U) (hF : ContinuousOn F U) :
    (HasPotential U F ↔ PathIndependent U F) ∧
      (PathIndependent U F ↔ ZeroPeriods U F) :=
  ⟨⟨potential_pathIndependent U F hU,
      pathIndependent_hasPotential U F hU hc hF⟩,
    ⟨pathIndependent_zeroPeriods U F,zeroPeriods_pathIndependent U F⟩⟩

lemma potential_hasFDerivAt {n} {U : Set (E n)} {F : E n → E n}
    {f : E n → ℝ} (hU : IsOpen U) (hf : IsPotential U F f)
    {x : E n} (hx : x ∈ U) : HasFDerivAt f (workCovector F x) x := by
  obtain ⟨A,hA⟩ := hf.1.1 x hx
  have hd := (hasTotalDerivative_iff_hasFDerivAt U f A x hU hx).mp hA
  have he : A = workCovector F x := by
    ext v
    rw [← totalDerivative_eq U f A x hA, scalarGradient_represents]
    exact congrArg (fun y => inner ℝ y v) (hf.2 hx)
  rwa [he] at hd

lemma potential_continuous_field {n} {U : Set (E n)} {F : E n → E n}
    {f : E n → ℝ} (hf : IsPotential U F f) : ContinuousOn F U := by
  have hgrad : ContinuousOn (scalarGradient f) U :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.comp_continuousOn hf.1.2
  exact hgrad.congr (fun x hx => (hf.2 hx).symm)

theorem potential_unique {n} (U : Set (E n)) (F : E n → E n) (f g : E n → ℝ)
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hf : IsPotential U F f) (hg : IsPotential U F g) :
    ∃ c : ℝ, ∀ x ∈ U, g x = f x + c := by
  classical
  by_cases hn : U.Nonempty
  · obtain ⟨a,ha⟩ := hn
    refine ⟨g a - f a, fun x hx => ?_⟩
    obtain ⟨p⟩ := workPath_exists U F hU hc (potential_continuous_field hf) a x ha hx
    have he := potential_integral U F f hU hf p.path p.data p.inside p.integrable
    have he' := potential_integral U F g hU hg p.path p.data p.inside p.integrable
    rw [p.start,p.finish] at he he'
    linarith
  · exact ⟨0,fun x hx => False.elim (hn ⟨x,hx⟩)⟩

/-- The derivative is the continuous-linear metric image of F, so this also
covers r = 0 without requiring any derivative of the field. -/
theorem potential_regular {n} (r : ℕ) (U : Set (E n)) (F : E n → E n)
    (f : E n → ℝ) (hU : IsOpen U) (hf : IsPotential U F f) (hF : CrOn r U F) :
    CrOn (r+1) U f := by
  have he : EqOn (totalDerivative f) (workCovector F) U :=
    fun x hx => (potential_hasFDerivAt hU hf hx).fderiv
  refine ⟨hf.1.1, ?_⟩
  apply (crOn_iff_contDiffOn r U _ hU).mpr
  exact ((innerSL ℝ).contDiff.comp_contDiffOn
    ((crOn_iff_contDiffOn r U F hU).mp hF)).congr (fun x hx => he hx)

theorem potential_smooth {n} (U : Set (E n)) (F : E n → E n)
    (f : E n → ℝ) (hU : IsOpen U) (hf : IsPotential U F f) (hF : SmoothOn U F) :
    SmoothOn U f := by
  intro r
  cases r with
  | zero => exact ((crOn_iff_contDiffOn 1 U f hU).mp hf.1).continuousOn
  | succ r => exact potential_regular r U F f hU hf (hF r)

lemma potential_restrict {n} {U V : Set (E n)} {F : E n → E n} {f : E n → ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) (hf : IsPotential U F f) :
    IsPotential V F f :=
  ⟨(crOn_iff_contDiffOn 1 V f hV).mpr
      (((crOn_iff_contDiffOn 1 U f hU).mp hf.1).mono hVU), hf.2.mono hVU⟩

theorem component_equivalences {n} (U : Set (E n)) (F : E n → E n)
    (hU : IsOpen U) (hF : ContinuousOn F U) (C : Set (E n))
    (hC : C ∈ componentsWithin U) :
    IsOpen C ∧ (HasPotential C F ↔ PathIndependent C F) ∧
      (PathIndependent C F ↔ ZeroPeriods C F) := by
  obtain ⟨a,ha,rfl⟩ := hC
  have ho : IsOpen (componentWithin U a) :=
    (open_iff_isOpen _).mp (open_componentWithin U ((open_iff_isOpen U).mpr hU) a)
  exact ⟨ho,potential_equivalences _ F ho (componentWithin_connected U a)
    (hF.mono (componentWithin_subset U a))⟩

theorem component_unique {n} (U : Set (E n)) (F : E n → E n) (f g : E n → ℝ)
    (hU : IsOpen U) (hf : IsPotential U F f) (hg : IsPotential U F g)
    (C : Set (E n)) (hC : C ∈ componentsWithin U) :
    ∃! c : ℝ, ∀ x ∈ C, g x = f x + c := by
  obtain ⟨hne,hsub,hconn⟩ := (componentsWithin_partition U).2.1 C hC
  have ho := (component_equivalences U F hU (potential_continuous_field hf) C hC).1
  obtain ⟨c,hc⟩ := potential_unique C F f g ho hconn
    (potential_restrict hU ho hsub hf) (potential_restrict hU ho hsub hg)
  refine ⟨c,hc,fun d hd => ?_⟩
  obtain ⟨x,hx⟩ := hne
  linarith [hc x hx,hd x hx]

/-- Any chosen constants on the open components preserve the derivative.
The resulting ambient extension can be discontinuous outside U, which is
irrelevant to its C¹ regularity on U. -/
theorem independent_constants {n} (U : Set (E n)) (F : E n → E n) (f : E n → ℝ)
    (hU : IsOpen U) (hf : IsPotential U F f)
    (c : {C : Set (E n) // C ∈ componentsWithin U} → ℝ) :
    ∃ g : E n → ℝ, IsPotential U F g ∧
      ∀ C (hC : C ∈ componentsWithin U), ∀ x ∈ C, g x = f x + c ⟨C,hC⟩ := by
  classical
  let g : E n → ℝ := fun x => if hx : x ∈ U then
    f x + c ⟨componentWithin U x,⟨x,hx,rfl⟩⟩ else 0
  have hg (C : Set (E n)) (hC : C ∈ componentsWithin U) (x : E n) (hx : x ∈ C) :
      g x = f x + c ⟨C,hC⟩ := by
    obtain ⟨a,ha,he⟩ := hC
    have hxa : x ∈ componentWithin U a := by
      change x ∈ Specs.D04.C01.Components.Model.componentWithin U a
      rwa [he]
    have hxU := componentWithin_subset U a hxa
    have heq : componentWithin U x = C := (componentWithin_eq_of_mem U a x hxa).symm.trans he
    dsimp only [g]
    rw [dite_eq_left hxU]
    congr 2
    exact Subtype.ext heq
  refine ⟨g,isPotential_of_hasFDerivAt U F g hU (potential_continuous_field hf) ?_,hg⟩
  intro x hx
  let C := componentWithin U x
  have hC : C ∈ componentsWithin U := ⟨x,hx,rfl⟩
  have ho := (component_equivalences U F hU (potential_continuous_field hf) C hC).1
  have heq : g =ᶠ[𝓝 x] (fun y => f y + c ⟨C,hC⟩) :=
    Filter.eventuallyEq_of_mem (ho.mem_nhds (mem_componentWithin U x hx)) (hg C hC)
  exact ((potential_hasFDerivAt hU hf hx).add_const (c ⟨C,hC⟩)).congr_of_eventuallyEq heq

end D04.C11
