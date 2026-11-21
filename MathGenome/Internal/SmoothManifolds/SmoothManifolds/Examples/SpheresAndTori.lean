import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.SpheresAndTori
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

namespace SmoothManifolds.SphereTorus
open SphereTorusData Set Filter
open scoped BigOperators Topology ContDiff

lemma squareSum_nonneg {n : ℕ} (x : Euclidean n) : 0 ≤ squareSum x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma squareSum_insert {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (y : Euclidean n) :
    squareSum (i.insertNth t y) = t ^ 2 + squareSum y := by
  unfold squareSum
  rw [Fin.sum_univ_succAbove _ i]
  simp

lemma squareSum_omit {n : ℕ} (i : Fin (n + 1)) (x : Euclidean (n + 1)) :
    squareSum x = (x i) ^ 2 + squareSum (omitCoordinate i x) := by
  unfold squareSum omitCoordinate
  rw [Fin.sum_univ_succAbove _ i]

lemma signedRoot_sq (s : Bool) {r : ℝ} (hr : 0 ≤ r) : signedRoot s r ^ 2 = r := by
  cases s <;> simp [signedRoot, Real.sq_sqrt hr]

lemma squareSum_insertRoot {n : ℕ} (i : Fin (n + 1)) (s : Bool)
    (y : Euclidean n) (hy : squareSum y < 1) : squareSum (insertRoot i s y) = 1 := by
  rw [insertRoot, squareSum_insert, signedRoot_sq s (by linarith)]
  ring

@[simp] lemma omit_insertRoot {n : ℕ} (i : Fin (n + 1)) (s : Bool) (y : Euclidean n) :
    omitCoordinate i (insertRoot i s y) = y := by
  ext j
  simp [omitCoordinate, insertRoot]

lemma insertRoot_omit {n : ℕ} (i : Fin (n + 1)) (s : Bool) (x : Sphere n)
    (hx : x ∈ hemisphere i s) : insertRoot i s (omitCoordinate i x.val) = x.val := by
  have he : 1 - squareSum (omitCoordinate i x.val) = (x.val i) ^ 2 := by
    have := squareSum_omit i x.val
    rw [x.property] at this
    linarith
  have ht : signedRoot s (1 - squareSum (omitCoordinate i x.val)) = x.val i := by
    rw [he]
    cases s <;> simp only [hemisphere, mem_ofPred_eq, Bool.false_eq_true, ↓reduceIte,
      signedRoot, Real.sqrt_sq_eq_abs] at hx ⊢
    · rw [abs_of_neg hx, neg_neg]
    · exact abs_of_pos hx
  rw [insertRoot, ht]
  exact Fin.insertNth_self_removeNth i x.val

lemma hemisphere_omit_mem {n : ℕ} (i : Fin (n + 1)) (s : Bool) (x : Sphere n)
    (hx : x ∈ hemisphere i s) : squareSum (omitCoordinate i x.val) < 1 := by
  have hne : x.val i ≠ 0 := by
    cases s <;> simp [hemisphere] at hx
    · exact ne_of_lt hx
    · exact ne_of_gt hx
  have hpos := sq_pos_of_ne_zero hne
  have := squareSum_omit i x.val
  rw [x.property] at this
  linarith

lemma insertRoot_sign {n : ℕ} (i : Fin (n + 1)) (s : Bool)
    (y : Euclidean n) (hy : squareSum y < 1) :
    (if s then 0 < insertRoot i s y i else insertRoot i s y i < 0) := by
  have hr : 0 < Real.sqrt (1 - squareSum y) := Real.sqrt_pos.mpr (by linarith)
  cases s <;> simpa [insertRoot, signedRoot] using hr

lemma continuous_squareSum (n : ℕ) : Continuous (squareSum : Euclidean n → ℝ) := by
  unfold squareSum
  fun_prop

lemma contDiff_squareSum (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (squareSum : Euclidean n → ℝ) := by
  unfold squareSum
  fun_prop

lemma isOpen_hemisphere {n : ℕ} (i : Fin (n + 1)) (s : Bool) :
    IsOpen (hemisphere i s) := by
  cases s
  · exact isOpen_lt ((continuous_apply i).comp continuous_subtype_val) continuous_const
  · exact isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)

lemma isOpen_unitBall (n : ℕ) : IsOpen (unitBall n) :=
  isOpen_lt ((continuous_squareSum n).comp continuous_subtype_val) continuous_const

lemma hemisphere_cover (n : ℕ) (x : Sphere n) :
    ∃ i s, x ∈ hemisphere i s := by
  have hne : ∃ i, x.val i ≠ 0 := by
    by_contra! h
    have : squareSum x.val = 0 := by simp [squareSum, h]
    rw [x.property] at this
    norm_num at this
  obtain ⟨i, hi⟩ := hne
  rcases lt_or_gt_of_ne hi with h | h
  · exact ⟨i, false, h⟩
  · exact ⟨i, true, h⟩

/-- A default point is needed only to make the inverse chart a total function. -/
def sphereBase (n : ℕ) : Sphere n :=
  ⟨(Fin.last n).insertNth 1 (0 : Euclidean n), by
    rw [squareSum_insert]
    simp [squareSum]⟩

noncomputable def hemisphereInverse {n : ℕ} (i : Fin (n + 1)) (s : Bool)
    (y : ModelSpace n .euclidean) : Sphere n :=
  if hy : squareSum y.val < 1 then ⟨insertRoot i s y.val, squareSum_insertRoot i s y.val hy⟩
  else sphereBase n

lemma hemisphereInverse_val {n : ℕ} (i : Fin (n + 1)) (s : Bool)
    (y : ModelSpace n .euclidean) (hy : y ∈ unitBall n) :
    (hemisphereInverse i s y).val = insertRoot i s y.val := by
  simp [hemisphereInverse, show squareSum y.val < 1 from hy]

lemma continuous_insertRoot {n : ℕ} (i : Fin (n + 1)) (s : Bool) :
    Continuous (insertRoot i s) := by
  apply continuous_pi
  intro j
  obtain rfl | ⟨l, rfl⟩ := i.eq_self_or_eq_succAbove j
  · simp only [insertRoot, Fin.insertNth_apply_same]
    cases s <;> simp only [signedRoot, Bool.false_eq_true, ↓reduceIte]
    · exact (Real.continuous_sqrt.comp (continuous_const.sub (continuous_squareSum n))).neg
    · exact Real.continuous_sqrt.comp (continuous_const.sub (continuous_squareSum n))
  · simpa [insertRoot] using (continuous_apply l : Continuous (fun y : Euclidean n => y l))

/-- The explicit coordinate-omission hemisphere chart. -/
noncomputable def hemisphereChart {n : ℕ} (i : Fin (n + 1)) (s : Bool) :
    ModelChart n .euclidean (Sphere n) where
  toFun x := ⟨omitCoordinate i x.val, mem_univ _⟩
  invFun := hemisphereInverse i s
  source := hemisphere i s
  target := unitBall n
  map_source' x hx := hemisphere_omit_mem i s x hx
  map_target' y hy := by
    change (if s then 0 < (hemisphereInverse i s y).val i
      else (hemisphereInverse i s y).val i < 0)
    rw [hemisphereInverse_val i s y hy]
    exact insertRoot_sign i s y.val hy
  left_inv' x hx := by
    apply Subtype.ext
    rw [hemisphereInverse_val i s _ (hemisphere_omit_mem i s x hx)]
    exact insertRoot_omit i s x hx
  right_inv' y hy := by
    apply Subtype.ext
    change omitCoordinate i (hemisphereInverse i s y).val = y.val
    rw [hemisphereInverse_val i s y hy, omit_insertRoot]
  open_source := isOpen_hemisphere i s
  open_target := isOpen_unitBall n
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact (continuous_apply _).comp continuous_subtype_val
  continuousOn_invFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply ((continuous_insertRoot i s).comp continuous_subtype_val).continuousOn.congr
    intro y hy
    exact hemisphereInverse_val i s y hy

lemma hemisphereChart_spec {n : ℕ} (i : Fin (n + 1)) (s : Bool) :
    IsHemisphereChart i s (hemisphereChart i s) := by
  exact ⟨rfl, rfl, fun _ _ => rfl, fun y hy => hemisphereInverse_val i s y hy⟩

lemma contDiffOn_insertRoot {n : ℕ} (i : Fin (n + 1)) (s : Bool) :
    ContDiffOn ℝ (⊤ : ℕ∞) (insertRoot i s) {y | squareSum y < 1} := by
  apply contDiffOn_pi.mpr
  intro j
  obtain rfl | ⟨l, rfl⟩ := i.eq_self_or_eq_succAbove j
  · simp only [insertRoot, Fin.insertNth_apply_same]
    have hr := (contDiff_const.sub (contDiff_squareSum n)).contDiffOn.sqrt
      (fun y (hy : squareSum y < 1) => ne_of_gt (sub_pos.mpr hy))
    cases s
    · exact hr.neg
    · exact hr
  · simpa [insertRoot] using (contDiff_pi.mp (contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (id : Euclidean n → Euclidean n)) l).contDiffOn

lemma hemisphereChart_germ {n : ℕ} {i j : Fin (n + 1)} {s t : Bool}
    {c d : ModelChart n .euclidean (Sphere n)}
    (hc : IsHemisphereChart i s c) (hd : IsHemisphereChart j t d)
    (p : Sphere n) (hp : p ∈ c.source) (hp' : p ∈ d.source) :
    ChartContDiffAt (⊤ : ℕ∞) c d id p := by
  refine ⟨{y | squareSum y < 1}, isOpen_lt (continuous_squareSum n) continuous_const,
    ?_, fun y => omitCoordinate j (insertRoot i s y), ?_, ?_⟩
  · have h := c.map_source hp
    rwa [hc.2.1] at h
  · apply contDiffOn_pi.mpr
    intro l
    exact (contDiffOn_pi.mp (contDiffOn_insertRoot i s) (j.succAbove l))
  · filter_upwards [c.open_source.mem_nhds hp, d.open_source.mem_nhds hp'] with q hq hq'
    change omitCoordinate j (insertRoot i s (c q).val) = (d q).val
    rw [← hc.2.2.2 (c q) (c.map_source hq), c.left_inv hq, hd.2.2.1 q hq']

lemma hemisphereAtlas_isContDiffAtlas (n : ℕ) :
    IsContDiffAtlas (⊤ : ℕ∞) (hemisphereAtlas n) := by
  constructor
  · intro x
    obtain ⟨i, s, hx⟩ := hemisphere_cover n x
    exact ⟨hemisphereChart i s, ⟨i, s, hemisphereChart_spec i s⟩, hx⟩
  · rintro c ⟨i, s, hc⟩ d ⟨j, t, hd⟩
    exact contDiffCompatible_of_germs (hemisphereChart_germ hc hd) (hemisphereChart_germ hd hc)

/-- The full sphere construction, including S^0 and the exact requested charts. -/
theorem sphereManifold : Specs.SmoothManifolds.Examples.SpheresAndTori.sphereManifoldType := by
  intro n
  have hA := hemisphereAtlas_isContDiffAtlas n
  refine ⟨fun i s => ⟨hemisphereChart i s, hemisphereChart_spec i s⟩, hA, ?_⟩
  exact ⟨⟨⟨inferInstance, inferInstance, _, hA.1⟩,
    ⟨_, maximalExtension_isMaximal hA⟩⟩, rfl, rfl⟩

/-- Identifying the complex unit circle with the real coordinate sphere is a
homeomorphism, before imposing any smooth structure. -/
noncomputable def circleSphereHomeomorph : Circle ≃ₜ Sphere 1 where
  toFun z := ⟨![(z : ℂ).re, (z : ℂ).im], by
    simpa [squareSum, Fin.sum_univ_two, Complex.normSq_apply, pow_two]
      using Circle.normSq_coe z⟩
  invFun x := ⟨⟨x.val 0, x.val 1⟩, by
    apply mem_sphere_zero_iff_norm.mpr
    have hx : (x.val 0) ^ 2 + (x.val 1) ^ 2 = 1 := by
      simpa [squareSum, Fin.sum_univ_two] using x.property
    simp [Complex.norm_def, Complex.normSq_apply, ← pow_two, hx]⟩
  left_inv z := by apply Circle.ext; rfl
  right_inv x := by
    apply Subtype.ext
    ext j
    fin_cases j <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    fin_cases j
    · exact Complex.continuous_re.comp continuous_subtype_val
    · exact Complex.continuous_im.comp continuous_subtype_val
  continuous_invFun := by
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    change Continuous (fun x : Sphere 1 => (⟨x.val 0, x.val 1⟩ : ℂ))
    have he : (fun x : Sphere 1 => (⟨x.val 0, x.val 1⟩ : ℂ)) =
        (fun x => (x.val 0 : ℂ) + (x.val 1 : ℂ) * Complex.I) := by
      funext x
      apply Complex.ext <;> simp
    rw [he]
    exact (Complex.continuous_ofReal.comp ((continuous_apply 0).comp continuous_subtype_val)).add
      ((Complex.continuous_ofReal.comp ((continuous_apply 1).comp continuous_subtype_val)).mul
        continuous_const)

/-- The periodic angle homeomorphism, coordinate by coordinate. -/
noncomputable def periodicAngleHomeomorph (k : ℕ) : FlatTorus k ≃ₜ Torus k :=
  Homeomorph.piCongrRight (fun _ : Fin k =>
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).trans circleSphereHomeomorph)

lemma periodicAngleHomeomorph_apply (k : ℕ) (x : Euclidean k) :
    periodicAngleHomeomorph k (quotientProjection k x) = angleMap k x := by
  funext j
  apply Subtype.ext
  change (circleSphereHomeomorph
    ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) (x j))).val = _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  change ![(Circle.exp (2 * Real.pi / 1 * x j) : ℂ).re,
    (Circle.exp (2 * Real.pi / 1 * x j) : ℂ).im] =
    ![Real.cos (2 * Real.pi * x j), Real.sin (2 * Real.pi * x j)]
  simp only [div_one, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

lemma quotientProjection_isOpenQuotientMap (k : ℕ) :
    IsOpenQuotientMap (quotientProjection k) :=
  IsOpenQuotientMap.piMap (fun _ : Fin k => QuotientAddGroup.isOpenQuotientMap_mk)

lemma quotientProjection_fiber (k : ℕ) (x y : Euclidean k) :
    quotientProjection k x = quotientProjection k y ↔
      ∃ z : Fin k → ℤ, ∀ j, x j = y j + (z j : ℝ) := by
  have he (a b : ℝ) : (a : AddCircle (1 : ℝ)) = b ↔ ∃ z : ℤ, a = b + (z : ℝ) := by
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    simp only [zsmul_eq_mul, mul_one]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, by linarith⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, by linarith⟩
  constructor
  · intro h
    have hh : ∀ j, ∃ z : ℤ, x j = y j + (z : ℝ) :=
      fun j => (he _ _).mp (congrFun h j)
    exact ⟨fun j => Classical.choose (hh j), fun j => Classical.choose_spec (hh j)⟩
  · rintro ⟨z, hz⟩
    funext j
    exact (he _ _).mpr ⟨z j, hz j⟩

/-- Full topological quotient statement: exact integer fibers, quotient topology,
and the homeomorphism induced by periodic angle coordinates. -/
theorem angleQuotient : Specs.SmoothManifolds.Examples.SpheresAndTori.angleQuotientType := by
  intro k
  exact ⟨quotientProjection_isOpenQuotientMap k, quotientProjection_fiber k,
    periodicAngleHomeomorph k, periodicAngleHomeomorph_apply k⟩

/-- Coordinatewise hemisphere charts, with one real coordinate per circle. -/
noncomputable def productHemisphereChart (k : ℕ) (i : Fin k → Fin 2) (s : Fin k → Bool) :
    ModelChart k .euclidean (Torus k) where
  toFun p := ⟨fun j => (p j).val ((i j).succAbove 0), mem_univ _⟩
  invFun y j := hemisphereInverse (i j) (s j) ⟨fun _ : Fin 1 => y.val j, mem_univ _⟩
  source := {p | ∀ j, p j ∈ hemisphere (i j) (s j)}
  target := {y | ∀ j, (y.val j) ^ 2 < 1}
  map_source' p hp j := by
    simpa [omitCoordinate, squareSum] using hemisphere_omit_mem (i j) (s j) (p j) (hp j)
  map_target' y hy j := by
    change (if s j then 0 < (hemisphereInverse (i j) (s j) _).val (i j)
      else (hemisphereInverse (i j) (s j) _).val (i j) < 0)
    have h : (⟨fun _ : Fin 1 => y.val j, mem_univ _⟩ : ModelSpace 1 .euclidean) ∈ unitBall 1 := by
      simpa [unitBall, squareSum] using hy j
    rw [hemisphereInverse_val (i j) (s j) _ h]
    exact insertRoot_sign (i j) (s j) _ h
  left_inv' p hp := by
    funext j
    apply Subtype.ext
    have h : (⟨fun _ : Fin 1 => (p j).val ((i j).succAbove 0), mem_univ _⟩ :
        ModelSpace 1 .euclidean) ∈ unitBall 1 := by
      simpa [unitBall, squareSum, omitCoordinate] using
        hemisphere_omit_mem (i j) (s j) (p j) (hp j)
    rw [hemisphereInverse_val (i j) (s j) _ h]
    convert insertRoot_omit (i j) (s j) (p j) (hp j) using 1
    congr 1
    ext l
    exact congrArg (fun l => (p j).val ((i j).succAbove l)) (Subsingleton.elim _ _)
  right_inv' y hy := by
    apply Subtype.ext
    ext j
    have h : (⟨fun _ : Fin 1 => y.val j, mem_univ _⟩ : ModelSpace 1 .euclidean) ∈ unitBall 1 := by
      simpa [unitBall, squareSum] using hy j
    change (hemisphereInverse (i j) (s j) _).val ((i j).succAbove 0) = y.val j
    rw [hemisphereInverse_val (i j) (s j) _ h]
    simp [insertRoot]
  open_source := by
    have he : {p : Torus k | ∀ j, p j ∈ hemisphere (i j) (s j)} =
        ⋂ j : Fin k, (fun p : Torus k => p j) ⁻¹' hemisphere (i j) (s j) := by
      ext p
      simp
    rw [he]
    exact isOpen_iInter_of_finite (fun j =>
      (isOpen_hemisphere (i j) (s j)).preimage (continuous_apply j))
  open_target := by
    simpa [ofPred_forall] using
      (isOpen_iInter_of_finite (fun j : Fin k => isOpen_lt
        (((continuous_apply j).comp (continuous_subtype_val :
          Continuous (Subtype.val : ModelSpace k .euclidean → Euclidean k))).pow 2)
        (continuous_const : Continuous (fun _ : ModelSpace k .euclidean => (1 : ℝ)))))
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact (continuous_apply _).comp (continuous_subtype_val.comp (continuous_apply j))
  continuousOn_invFun := by
    apply continuousOn_pi.mpr
    intro j
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    have hcont : Continuous (fun y : ModelSpace k .euclidean =>
        insertRoot (i j) (s j) (fun _ : Fin 1 => y.val j)) :=
      (continuous_insertRoot (i j) (s j)).comp
        (continuous_pi (fun _ => (continuous_apply j).comp continuous_subtype_val))
    apply hcont.continuousOn.congr
    intro y hy
    exact hemisphereInverse_val (i j) (s j) _ (by simpa [unitBall, squareSum] using hy j)

lemma productHemisphereChart_spec (k : ℕ) (i : Fin k → Fin 2) (s : Fin k → Bool) :
    IsProductHemisphereChart k i s (productHemisphereChart k i s) := by
  refine ⟨rfl, rfl, fun _ _ _ => rfl, ?_⟩
  intro y hy j
  exact hemisphereInverse_val (i j) (s j) _ (by simpa [unitBall, squareSum] using hy j)

lemma productHemisphereChart_germ {k : ℕ} {i j : Fin k → Fin 2} {s t : Fin k → Bool}
    {c d : ModelChart k .euclidean (Torus k)}
    (hc : IsProductHemisphereChart k i s c) (hd : IsProductHemisphereChart k j t d)
    (p : Torus k) (hp : p ∈ c.source) (hp' : p ∈ d.source) :
    ChartContDiffAt (⊤ : ℕ∞) c d id p := by
  let U : Set (Euclidean k) := {y | ∀ l, (y l) ^ 2 < 1}
  have hU : IsOpen U := by
    simpa [U, ofPred_forall] using
      (isOpen_iInter_of_finite (fun l : Fin k => isOpen_lt
        ((continuous_apply l : Continuous (fun y : Euclidean k => y l)).pow 2)
        (continuous_const : Continuous (fun _ : Euclidean k => (1 : ℝ)))))
  refine ⟨U, hU, ?_, fun y l => insertRoot (i l) (s l) (fun _ : Fin 1 => y l) ((j l).succAbove 0), ?_, ?_⟩
  · have h := c.map_source hp
    rwa [hc.2.1] at h
  · apply contDiffOn_pi.mpr
    intro l
    have hrep : ContDiff ℝ (⊤ : ℕ∞) (fun y : Euclidean k => fun _ : Fin 1 => y l) := by fun_prop
    exact contDiffOn_pi.mp ((contDiffOn_insertRoot (i l) (s l)).comp hrep.contDiffOn
      (fun y hy => by simpa [squareSum] using hy l)) ((j l).succAbove 0)
  · filter_upwards [c.open_source.mem_nhds hp, d.open_source.mem_nhds hp'] with q hq hq'
    funext l
    change insertRoot (i l) (s l) (fun _ : Fin 1 => (c q).val l) ((j l).succAbove 0) = (d q).val l
    rw [← hc.2.2.2 (c q) (c.map_source hq) l, c.left_inv hq, hd.2.2.1 q hq' l]

lemma productHemisphereAtlas_isContDiffAtlas (k : ℕ) :
    IsContDiffAtlas (⊤ : ℕ∞) (productHemisphereAtlas k) := by
  constructor
  · intro p
    choose i s hp using (fun j : Fin k => hemisphere_cover 1 (p j))
    exact ⟨productHemisphereChart k i s, ⟨i, s, productHemisphereChart_spec k i s⟩, hp⟩
  · rintro c ⟨i, s, hc⟩ d ⟨j, t, hd⟩
    exact contDiffCompatible_of_germs
      (productHemisphereChart_germ hc hd) (productHemisphereChart_germ hd hc)

/-- The product atlas equips every finite torus with the stated smooth structure. -/
theorem torusManifold : Specs.SmoothManifolds.Examples.SpheresAndTori.torusManifoldType := by
  intro k
  have hA := productHemisphereAtlas_isContDiffAtlas k
  refine ⟨fun i s => ⟨productHemisphereChart k i s, productHemisphereChart_spec k i s⟩, hA, ?_⟩
  exact ⟨⟨⟨inferInstance, inferInstance, _, hA.1⟩,
    ⟨_, maximalExtension_isMaximal hA⟩⟩, rfl, rfl⟩

lemma isOpen_angleBox {k : ℕ} (a : Euclidean k) (ε : ℝ) : IsOpen (angleBox a ε) := by
  simpa [angleBox, ofPred_forall] using
    (isOpen_iInter_of_finite (fun j : Fin k => isOpen_lt
      (((continuous_apply j : Continuous (fun y : Euclidean k => y j)).sub continuous_const).abs)
      (continuous_const : Continuous (fun _ : Euclidean k => ε))))

lemma mem_angleBox_center {k : ℕ} (a : Euclidean k) {ε : ℝ} (hε : 0 < ε) :
    a ∈ angleBox a ε := by simpa [angleBox] using (fun _ : Fin k => hε)

lemma quotientProjection_injOn_box {k : ℕ} (a : Euclidean k) {ε : ℝ} (hε : ε < 1 / 2) :
    InjOn (quotientProjection k) (angleBox a ε) := by
  intro x hx y hy he
  obtain ⟨z, hz⟩ := (quotientProjection_fiber k x y).mp he
  funext j
  have hxj := abs_lt.mp (hx j)
  have hyj := abs_lt.mp (hy j)
  have hlt : |(z j : ℝ)| < 1 := abs_lt.mpr ⟨by linarith [hz j], by linarith [hz j]⟩
  have hz0 : z j = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
  simpa [hz0] using hz j

noncomputable def boxQuotientHomeomorph {k : ℕ} (a : Euclidean k) (ε : ℝ) (hε : ε < 1 / 2) :
    OpenPartialHomeomorph (Euclidean k) (FlatTorus k) :=
  OpenPartialHomeomorph.ofContinuousOpen
    ((quotientProjection_injOn_box a hε).toPartialEquiv (quotientProjection k) (angleBox a ε))
    (quotientProjection_isOpenQuotientMap k).continuous.continuousOn
    (quotientProjection_isOpenQuotientMap k).isOpenMap (isOpen_angleBox a ε)

noncomputable def euclideanModelHomeomorph (k : ℕ) : Euclidean k ≃ₜ ModelSpace k .euclidean :=
  (Homeomorph.Set.univ (Euclidean k)).symm

noncomputable def angleChart {k : ℕ} (a : Euclidean k) (ε : ℝ) (hε : ε < 1 / 2) :
    ModelChart k .euclidean (FlatTorus k) :=
  (boxQuotientHomeomorph a ε hε).symm.trans
    (euclideanModelHomeomorph k).toOpenPartialHomeomorph

lemma angleChart_spec {k : ℕ} (a : Euclidean k) (ε : ℝ) (hε : ε < 1 / 2) :
    IsAngleChart a ε (angleChart a ε hε) := by
  let e := boxQuotientHomeomorph a ε hε
  have hsource : (angleChart a ε hε).source = quotientProjection k '' angleBox a ε := by
    change e.target ∩ e.symm ⁻¹' univ = _
    simp [e, boxQuotientHomeomorph, OpenPartialHomeomorph.ofContinuousOpen,
      OpenPartialHomeomorph.ofContinuousOpenRestrict,
      PartialHomeomorph.ofContinuousOpenRestrict, InjOn.toPartialEquiv, BijOn.toPartialEquiv]
  have htarget : (angleChart a ε hε).target = {y | y.val ∈ angleBox a ε} := by
    change univ ∩ (euclideanModelHomeomorph k).symm ⁻¹' e.source = _
    simp [e, boxQuotientHomeomorph, euclideanModelHomeomorph,
      OpenPartialHomeomorph.ofContinuousOpen,
      OpenPartialHomeomorph.ofContinuousOpenRestrict,
      PartialHomeomorph.ofContinuousOpenRestrict, InjOn.toPartialEquiv, BijOn.toPartialEquiv]
    rfl
  refine ⟨hsource, htarget, ?_, ?_⟩
  · intro x hx
    change e.symm (e x) = x
    exact e.left_inv hx
  · intro y _
    rfl

lemma angleChart_projection {k : ℕ} {a : Euclidean k} {ε : ℝ}
    {c : ModelChart k .euclidean (FlatTorus k)} (hc : IsAngleChart a ε c)
    {p : FlatTorus k} (hp : p ∈ c.source) : quotientProjection k (c p).val = p := by
  rw [← hc.2.2.2 (c p) (c.map_source hp), c.left_inv hp]

/-- Integer differences between two continuous local lifts are locally constant.
The proof uses injectivity on a fixed small box around the value of the lift. -/
lemma angleChart_germ {k : ℕ} {a b : Euclidean k} {ε δ : ℝ}
    {c d : ModelChart k .euclidean (FlatTorus k)}
    (hc : IsAngleChart a ε c) (hd : IsAngleChart b δ d)
    (p : FlatTorus k) (hp : p ∈ c.source) (hp' : p ∈ d.source) :
    ChartContDiffAt (⊤ : ℕ∞) c d id p := by
  let u := (c p).val
  let v := (d p).val
  let F : Euclidean k → Euclidean k := fun y => y + (v - u)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by dsimp [F]; fun_prop
  have hccont := continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  have hdcont := continuous_subtype_val.continuousAt.comp (d.continuousAt hp')
  have hFcont : ContinuousAt (fun q => F (c q).val) p := hF.continuous.continuousAt.comp hccont
  have hFp : F (c p).val = v := by dsimp [F, u, v]; abel
  have hproj : quotientProjection k (v - u) = 0 := by
    change (fun j => ((v j - u j : ℝ) : AddCircle (1 : ℝ))) = 0
    have hv := angleChart_projection hd hp'
    have hu := angleChart_projection hc hp
    funext j
    change (v j : AddCircle (1 : ℝ)) - (u j : AddCircle (1 : ℝ)) = 0
    exact sub_eq_zero.mpr (by exact congrFun (hv.trans hu.symm) j)
  refine ⟨univ, isOpen_univ, mem_univ _, F, hF.contDiffOn, ?_⟩
  have hbox := (isOpen_angleBox v (1 / 4)).mem_nhds (mem_angleBox_center v (by norm_num))
  have hFbox : ∀ᶠ q in 𝓝 p, F (c q).val ∈ angleBox v (1 / 4) := by
    exact hFcont.preimage_mem_nhds (by simpa [hFp] using hbox)
  have hdbox : ∀ᶠ q in 𝓝 p, (d q).val ∈ angleBox v (1 / 4) := hdcont.preimage_mem_nhds hbox
  filter_upwards [c.open_source.mem_nhds hp, d.open_source.mem_nhds hp', hFbox, hdbox]
    with q hqc hqd hqF hqdv
  apply quotientProjection_injOn_box v (by norm_num : (1 : ℝ) / 4 < 1 / 2) hqF hqdv
  have he : quotientProjection k (F (c q).val) = quotientProjection k (c q).val := by
    funext j
    change ((c q).val j : AddCircle (1 : ℝ)) + ((v j - u j : ℝ) : AddCircle (1 : ℝ)) = _
    have hzero := congrFun hproj j
    change ((v j - u j : ℝ) : AddCircle (1 : ℝ)) = 0 at hzero
    rw [hzero, add_zero]
    rfl
  exact he.trans ((angleChart_projection hc hqc).trans (angleChart_projection hd hqd).symm)

lemma angleAtlas_isContDiffAtlas (k : ℕ) : IsContDiffAtlas (⊤ : ℕ∞) (angleAtlas k) := by
  constructor
  · intro p
    obtain ⟨a, rfl⟩ := (quotientProjection_isOpenQuotientMap k).surjective p
    let c := angleChart a (1 / 8) (by norm_num)
    have hc := angleChart_spec a (1 / 8) (by norm_num)
    refine ⟨c, ⟨a, 1 / 8, by norm_num, by norm_num, hc⟩, ?_⟩
    rw [hc.1]
    exact ⟨a, mem_angleBox_center a (by norm_num), rfl⟩
  · rintro c ⟨a, ε, _, _, hc⟩ d ⟨b, δ, _, _, hd⟩
    exact contDiffCompatible_of_germs (angleChart_germ hc hd) (angleChart_germ hd hc)

theorem angleManifold : Specs.SmoothManifolds.Examples.SpheresAndTori.angleManifoldType := by
  intro k
  have hA := angleAtlas_isContDiffAtlas k
  refine ⟨fun a ε _ hε => ⟨angleChart a ε (by linarith), angleChart_spec a ε (by linarith)⟩,
    hA, ?_⟩
  exact ⟨⟨⟨inferInstance, inferInstance, _, hA.1⟩,
    ⟨_, maximalExtension_isMaximal hA⟩⟩, rfl, rfl⟩

/-- A smooth inverse on one actual neighborhood. Analytic regularity of the
forward trigonometric function supplies one neighborhood for all derivative orders. -/
lemma exists_smooth_local_inverse {f : ℝ → ℝ} {a r : ℝ}
    (hf : ContDiff ℝ ω f) (hder : HasDerivAt f r a) (hr : r ≠ 0) :
    ∃ (g : ℝ → ℝ) (U : Set ℝ), IsOpen U ∧ f a ∈ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) g U ∧ ∀ᶠ x in 𝓝 a, g (f x) = x := by
  let hd := hder.hasFDerivAt_equiv hr
  let g := hf.contDiffAt.localInverse hd (by simp)
  have hg : ContDiffAt ℝ ω g (f a) := hf.contDiffAt.to_localInverse hd (by simp)
  obtain ⟨U, hU, hgU⟩ := hg.contDiffOn (m := (⊤ : ℕ∞)) (by simp) (by simp)
  obtain ⟨V, hVU, hV, haV⟩ := mem_nhds_iff.mp hU
  refine ⟨g, V, hV, haV, hgU.mono hVU, ?_⟩
  exact (hf.contDiffAt.hasStrictFDerivAt' hd (by simp)).eventually_left_inverse

noncomputable def angleCoordinate (i : Fin 2) (t : ℝ) : ℝ :=
  (anglePoint t).val (i.succAbove 0)

noncomputable def angleCoordinateDerivative (i : Fin 2) (t : ℝ) : ℝ :=
  if i = 0 then Real.cos (2 * Real.pi * t) * (2 * Real.pi)
  else -Real.sin (2 * Real.pi * t) * (2 * Real.pi)

lemma contDiff_angleCoordinate (i : Fin 2) : ContDiff ℝ ω (angleCoordinate i) := by
  fin_cases i
  · change ContDiff ℝ ω (fun t => Real.sin (2 * Real.pi * t))
    fun_prop
  · change ContDiff ℝ ω (fun t => Real.cos (2 * Real.pi * t))
    fun_prop

lemma hasDerivAt_angleCoordinate (i : Fin 2) (t : ℝ) :
    HasDerivAt (angleCoordinate i) (angleCoordinateDerivative i t) t := by
  fin_cases i
  · change HasDerivAt (fun x : ℝ => Real.sin (2 * Real.pi * x))
      (Real.cos (2 * Real.pi * t) * (2 * Real.pi)) t
    exact (Real.hasDerivAt_sin (2 * Real.pi * t)).comp t
      (by simpa using (hasDerivAt_id t).const_mul (2 * Real.pi))
  · change HasDerivAt (fun x : ℝ => Real.cos (2 * Real.pi * x))
      (-Real.sin (2 * Real.pi * t) * (2 * Real.pi)) t
    exact (Real.hasDerivAt_cos (2 * Real.pi * t)).comp t
      (by simpa using (hasDerivAt_id t).const_mul (2 * Real.pi))

lemma angleCoordinateDerivative_ne_zero (i : Fin 2) (t : ℝ)
    (h : (anglePoint t).val i ≠ 0) : angleCoordinateDerivative i t ≠ 0 := by
  have hp : 2 * Real.pi ≠ 0 := by positivity
  fin_cases i
  · exact mul_ne_zero h hp
  · exact mul_ne_zero (neg_ne_zero.mpr h) hp

/-- In angle coordinates the product hemisphere map is a component of sine or
cosine. Agreement holds throughout the chart source. -/
lemma angleProduct_coordinates {k : ℕ} {i : Fin k → Fin 2} {s : Fin k → Bool}
    {a : Euclidean k} {ε : ℝ}
    {c : ModelChart k .euclidean (Torus k)} {d : ModelChart k .euclidean (FlatTorus k)}
    (hc : IsProductHemisphereChart k i s c) (hd : IsAngleChart a ε d)
    {q : FlatTorus k} (hqc : periodicAngleHomeomorph k q ∈ c.source) (hqd : q ∈ d.source) :
    (c (periodicAngleHomeomorph k q)).val =
      fun j => angleCoordinate (i j) ((d q).val j) := by
  have he : periodicAngleHomeomorph k q = angleMap k (d q).val := by
    rw [← periodicAngleHomeomorph_apply, angleChart_projection hd hqd]
  funext j
  rw [hc.2.2.1 _ hqc j, he]
  rfl

lemma angle_to_product_germ {k : ℕ} {i : Fin k → Fin 2} {s : Fin k → Bool}
    {a : Euclidean k} {ε : ℝ}
    {c : ModelChart k .euclidean (Torus k)} {d : ModelChart k .euclidean (FlatTorus k)}
    (hc : IsProductHemisphereChart k i s c) (hd : IsAngleChart a ε d)
    (p : FlatTorus k) (hpc : periodicAngleHomeomorph k p ∈ c.source) (hpd : p ∈ d.source) :
    ChartContDiffAt (⊤ : ℕ∞) d c (periodicAngleHomeomorph k) p := by
  refine ⟨univ, isOpen_univ, mem_univ _, fun y j => angleCoordinate (i j) (y j), ?_, ?_⟩
  · apply ContDiff.contDiffOn
    apply contDiff_pi.mpr
    intro j
    exact ((contDiff_angleCoordinate (i j)).of_le (by simp)).comp
      (contDiff_pi.mp contDiff_id j)
  · filter_upwards [((periodicAngleHomeomorph k).continuous.continuousAt.preimage_mem_nhds
      (c.open_source.mem_nhds hpc)), d.open_source.mem_nhds hpd] with q hqc hqd
    exact (angleProduct_coordinates hc hd hqc hqd).symm

lemma product_to_angle_germ {k : ℕ} {i : Fin k → Fin 2} {s : Fin k → Bool}
    {a : Euclidean k} {ε : ℝ}
    {c : ModelChart k .euclidean (Torus k)} {d : ModelChart k .euclidean (FlatTorus k)}
    (hc : IsProductHemisphereChart k i s c) (hd : IsAngleChart a ε d)
    (p : Torus k) (hpc : p ∈ c.source) (hpd : (periodicAngleHomeomorph k).symm p ∈ d.source) :
    ChartContDiffAt (⊤ : ℕ∞) c d (periodicAngleHomeomorph k).symm p := by
  let u := (d ((periodicAngleHomeomorph k).symm p)).val
  have he : p = angleMap k u := by
    rw [← periodicAngleHomeomorph_apply, angleChart_projection hd hpd]
    exact ((periodicAngleHomeomorph k).apply_symm_apply p).symm
  have hne (j : Fin k) : (anglePoint (u j)).val (i j) ≠ 0 := by
    have hh : p j ∈ hemisphere (i j) (s j) := by rw [hc.1] at hpc; exact hpc j
    rw [he] at hh
    change (if s j then 0 < (anglePoint (u j)).val (i j)
      else (anglePoint (u j)).val (i j) < 0) at hh
    cases hs : s j
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hh
      exact ne_of_lt hh
    · simp only [hs, ↓reduceIte] at hh
      exact ne_of_gt hh
  choose g U hU hu hdiff hleft using (fun j => exists_smooth_local_inverse
    (contDiff_angleCoordinate (i j)) (hasDerivAt_angleCoordinate (i j) (u j))
    (angleCoordinateDerivative_ne_zero (i j) (u j) (hne j)))
  let W : Set (Euclidean k) := {y | ∀ j, y j ∈ U j}
  have hW : IsOpen W := by
    have heW : W = ⋂ j : Fin k, (fun y : Euclidean k => y j) ⁻¹' U j := by
      ext y
      simp [W]
    rw [heW]
    exact isOpen_iInter_of_finite (fun j => (hU j).preimage (continuous_apply j))
  have hcoords : (c p).val = fun j => angleCoordinate (i j) (u j) := by
    convert angleProduct_coordinates hc hd (q := (periodicAngleHomeomorph k).symm p)
      (by simpa using hpc) hpd using 1
    simp
  refine ⟨W, hW, ?_, fun y j => g j (y j), ?_, ?_⟩
  · intro j
    change (c p).val j ∈ U j
    rw [congrFun hcoords j]
    exact hu j
  · apply contDiffOn_pi.mpr
    intro j
    exact (hdiff j).comp (contDiff_pi.mp contDiff_id j).contDiffOn (fun y hy => hy j)
  · have hlift : ContinuousAt (fun q => (d ((periodicAngleHomeomorph k).symm q)).val) p :=
      continuous_subtype_val.continuousAt.comp
        ((d.continuousAt hpd).comp (periodicAngleHomeomorph k).symm.continuous.continuousAt)
    have hleft' : ∀ᶠ q in 𝓝 p, ∀ j,
        g j (angleCoordinate (i j) ((d ((periodicAngleHomeomorph k).symm q)).val j)) =
          (d ((periodicAngleHomeomorph k).symm q)).val j := by
      apply (Filter.eventually_all).mpr
      intro j
      exact ((continuous_apply j).continuousAt.comp hlift).eventually (hleft j)
    filter_upwards [c.open_source.mem_nhds hpc,
      ((periodicAngleHomeomorph k).symm.continuous.continuousAt.preimage_mem_nhds
        (d.open_source.mem_nhds hpd)), hleft'] with q hqc hqd hqleft
    have hcoordsq := angleProduct_coordinates hc hd
      (q := (periodicAngleHomeomorph k).symm q) (by simpa using hqc) hqd
    simp only [Homeomorph.apply_symm_apply] at hcoordsq
    funext j
    rw [congrFun hcoordsq j]
    exact hqleft j

/-- The periodic homeomorphism is smooth in both directions for the two
specified maximal structures, and the transported quotient atlas generates
exactly the product smooth structure. -/
theorem angleProductCompatibility :
    Specs.SmoothManifolds.Examples.SpheresAndTori.angleProductCompatibilityType := by
  intro k T Q hT hQ
  let h := periodicAngleHomeomorph k
  have hTA := productHemisphereAtlas_isContDiffAtlas k
  have hQA := angleAtlas_isContDiffAtlas k
  have hTsub : productHemisphereAtlas k ⊆ T.smoothStructure.val := by
    rw [hT]
    exact subset_maximalExtension hTA
  have hQsub : angleAtlas k ⊆ Q.smoothStructure.val := by
    rw [hQ]
    exact subset_maximalExtension hQA
  have hf : IsSmoothMap Q T h := by
    intro p
    obtain ⟨d, hd, hpd⟩ := hQA.1 p
    obtain ⟨c, hc, hpc⟩ := hTA.1 (h p)
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      Q.smoothStructure.property.1 T.smoothStructure.property.1 h p).mpr
    refine ⟨h.continuous.continuousAt, d, hQsub hd, c, hTsub hc, hpd, hpc, ?_⟩
    obtain ⟨a, ε, _, _, hd⟩ := hd
    obtain ⟨i, s, hc⟩ := hc
    exact angle_to_product_germ hc hd p hpc hpd
  have hg : IsSmoothMap T Q h.symm := by
    intro p
    obtain ⟨c, hc, hpc⟩ := hTA.1 p
    obtain ⟨d, hd, hpd⟩ := hQA.1 (h.symm p)
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      T.smoothStructure.property.1 Q.smoothStructure.property.1 h.symm p).mpr
    refine ⟨h.symm.continuous.continuousAt, c, hTsub hc, d, hQsub hd, hpc, hpd, ?_⟩
    obtain ⟨a, ε, _, _, hd⟩ := hd
    obtain ⟨i, s, hc⟩ := hc
    exact product_to_angle_germ hc hd p hpc hpd
  refine ⟨h, periodicAngleHomeomorph_apply k, hf, hg, ?_⟩
  have hf' : ManifoldContDiff (⊤ : ℕ∞) (angleAtlas k) T.smoothStructure.val h := by
    intro p
    exact ⟨(hf p).1, fun e he d hd hp hp' => (hf p).2 e (hQsub he) d hd hp hp'⟩
  have hg' : ManifoldContDiff (⊤ : ℕ∞) T.smoothStructure.val (angleAtlas k) h.symm := by
    intro p
    exact ⟨(hg p).1, fun e he d hd hp hp' => (hg p).2 e he d (hQsub hd) hp hp'⟩
  have hAT : transportAtlas h (angleAtlas k) ⊆ T.smoothStructure.val :=
    transportAtlas_subset_of_maps T.smoothStructure.property h hf' hg'
  have htrans := transportAtlas_isContDiffAtlas (⊤ : ℕ∞) (angleAtlas k) h hQA
  exact (T.smoothStructure.property.2 _ (maximalExtension_isContDiffAtlas htrans)
    (atlas_subset_maximalExtension T.smoothStructure.property.1 hAT)).symm

/-- A homeomorphism from the actual integer-translation quotient, with the
specified periodic formula, rather than merely an abstract torus homeomorphism. -/
theorem latticeAngleHomeomorph :
    Specs.SmoothManifolds.Examples.SpheresAndTori.latticeAngleHomeomorphType := by
  intro k
  let r : LatticeQuotient k ≃ₜ Quotient (Setoid.ker (quotientProjection k)) :=
    Homeomorph.Quotient.congrRight (fun x y => (quotientProjection_fiber k x y).symm)
  let f : C(Euclidean k, FlatTorus k) :=
    ⟨quotientProjection k, (quotientProjection_isOpenQuotientMap k).continuous⟩
  let e : LatticeQuotient k ≃ₜ FlatTorus k :=
    r.trans ((quotientProjection_isOpenQuotientMap k).isQuotientMap.homeomorph (f := f))
  have he (x : Euclidean k) : e (latticeProjection k x) = quotientProjection k x := by
    rfl
  refine ⟨e, he, e.trans (periodicAngleHomeomorph k), ?_⟩
  intro x
  exact (congrArg (periodicAngleHomeomorph k) (he x)).trans
    (periodicAngleHomeomorph_apply k x)

end SmoothManifolds.SphereTorus

namespace SmoothManifolds
/-- Public names for the canonical objects shared with independent Specs. -/
abbrev Sphere := SphereTorusData.Sphere
abbrev Torus := SphereTorusData.Torus
abbrev FlatTorus := SphereTorusData.FlatTorus
abbrev LatticeQuotient := SphereTorusData.LatticeQuotient
abbrev hemisphereAtlas := SphereTorusData.hemisphereAtlas
abbrev productHemisphereAtlas := SphereTorusData.productHemisphereAtlas
abbrev angleAtlas := SphereTorusData.angleAtlas
abbrev quotientProjection := SphereTorusData.quotientProjection
noncomputable abbrev angleMap := SphereTorusData.angleMap
end SmoothManifolds
