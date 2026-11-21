import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.SpheresAndTori
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.RealProjectiveSpace
import Mathlib.Tactic.FieldSimp

namespace SmoothManifolds
/-- Real projective n-space is the antipodal quotient of the shared S^n. -/
abbrev RealProjectiveSpace := ProjectiveData.RealProjectiveSpace
end SmoothManifolds

namespace SmoothManifolds.Projective
open ProjectiveData SphereTorusData SphereTorus Set Filter Topology
open scoped BigOperators Topology ContDiff

lemma projection_fiber {n : ℕ} (x y : Sphere n) :
    projectiveProjection x = projectiveProjection y ↔ x = y ∨ x = antipode y :=
  Quotient.eq

lemma continuous_antipode (n : ℕ) : Continuous (@antipode n) := by
  exact (continuous_subtype_val.neg).subtype_mk _

lemma projection_saturation {n : ℕ} (U : Set (Sphere n)) :
    projectiveProjection ⁻¹' (projectiveProjection '' U) = U ∪ antipode ⁻¹' U := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    rcases (projection_fiber y x).mp heq with h | h
    · exact Or.inl (h ▸ hy)
    · right; change antipode x ∈ U; rwa [← h]
  · rintro (hx | hx)
    · exact ⟨x, hx, rfl⟩
    · exact ⟨antipode x, hx, (projection_fiber _ _).mpr (Or.inr rfl)⟩

lemma projection_isOpenQuotientMap (n : ℕ) :
    IsOpenQuotientMap (@projectiveProjection n) := by
  have hq : IsQuotientMap (@projectiveProjection n) := isQuotientMap_quotient_mk'
  refine ⟨hq.surjective, hq.continuous, ?_⟩
  intro U hU
  apply hq.isOpen_preimage.mp
  rw [projection_saturation]
  exact hU.union (hU.preimage (continuous_antipode n))

instance projective_t2 (n : ℕ) : T2Space (RealProjectiveSpace n) := by
  apply (t2Space_iff_of_isOpenQuotientMap (projection_isOpenQuotientMap n)).mpr
  have heq : {q : Sphere n × Sphere n | projectiveProjection q.1 = projectiveProjection q.2} =
      {q | q.1 = q.2} ∪ {q | q.1 = antipode q.2} := by
    ext q; exact projection_fiber _ _
  rw [heq]
  exact (isClosed_eq continuous_fst continuous_snd).union
    (isClosed_eq continuous_fst ((continuous_antipode n).comp continuous_snd))

instance projective_secondCountable (n : ℕ) : SecondCountableTopology (RealProjectiveSpace n) :=
  (projection_isOpenQuotientMap n).secondCountableTopology

/-- The full topology statement is on the literal quotient, not a replacement space. -/
theorem projectiveTopology :
    Specs.SmoothManifolds.Examples.RealProjectiveSpace.projectiveTopologyType := by
  intro n
  exact ⟨projection_isOpenQuotientMap n, projection_fiber, inferInstance, inferInstance⟩

@[simp] lemma ratios_projection {n : ℕ} (i : Fin (n + 1)) (x : Sphere n) (j : Fin n) :
    projectiveRatios i (projectiveProjection x) j = x.val (i.succAbove j) / x.val i := rfl

@[simp] lemma projection_mem_locus {n : ℕ} (i : Fin (n + 1)) (x : Sphere n) :
    projectiveProjection x ∈ projectiveLocus i ↔ x.val i ≠ 0 := by
  constructor
  · rintro ⟨y, hy, heq⟩
    rcases (projection_fiber y x).mp heq with h | h
    · simpa [h] using hy
    · simpa [h, antipode] using hy
  · intro hx; exact ⟨x, hx, rfl⟩

lemma isOpen_locus {n : ℕ} (i : Fin (n + 1)) : IsOpen (projectiveLocus i) :=
  (projection_isOpenQuotientMap n).isOpenMap _
    (isOpen_ne_fun ((continuous_apply i).comp continuous_subtype_val) continuous_const)

lemma locus_cover {n : ℕ} (p : RealProjectiveSpace n) : ∃ i, p ∈ projectiveLocus i := by
  induction p using Quotient.inductionOn with | _ x =>
  obtain ⟨i, s, hi⟩ := hemisphere_cover n x
  refine ⟨i, (projection_mem_locus i x).mpr ?_⟩
  cases s
  · exact ne_of_lt hi
  · exact ne_of_gt hi

lemma insertOne_ratios {n : ℕ} (i : Fin (n + 1)) (x : Sphere n) (hx : x.val i ≠ 0)
    (j : Fin (n + 1)) :
    insertOne i (projectiveRatios i (projectiveProjection x)) j = x.val j / x.val i := by
  obtain rfl | ⟨k, rfl⟩ := i.eq_self_or_eq_succAbove j
  · simp [insertOne, hx]
  · simp [insertOne]

/-- Equal ratios imply proportional representatives; unit length makes the
proportionality factor +1 or -1, giving exactly the antipodal orbit. -/
lemma ratios_fiber {n : ℕ} (i : Fin (n + 1)) (x y : Sphere n)
    (hx : x.val i ≠ 0) (hy : y.val i ≠ 0)
    (h : projectiveRatios i (projectiveProjection x) =
      projectiveRatios i (projectiveProjection y)) :
    projectiveProjection x = projectiveProjection y := by
  let a := x.val i / y.val i
  have hxy : ∀ j, x.val j = a * y.val j := by
    intro j
    have he := congrArg (fun z => insertOne i z j) h
    rw [insertOne_ratios i x hx, insertOne_ratios i y hy] at he
    dsimp [a]
    apply (div_eq_div_iff hx hy).mp at he
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hy).mpr
    calc
      x.val j * y.val i = y.val j * x.val i := he
      _ = x.val i * y.val j := mul_comm _ _
  have ha : a ^ 2 = 1 := by
    have hs : squareSum x.val = a ^ 2 * squareSum y.val := by
      simp only [squareSum, hxy, mul_pow, Finset.mul_sum]
    simpa [x.property, y.property] using hs.symm
  rcases (sq_eq_one_iff).mp ha with ha | ha
  · apply (projection_fiber x y).mpr
    left; apply Subtype.ext; funext j; simpa [ha] using hxy j
  · apply (projection_fiber x y).mpr
    right; apply Subtype.ext; funext j; simpa [ha, antipode] using hxy j

lemma sqrt_normalizer_pos {n : ℕ} (y : Euclidean n) : 0 < Real.sqrt (1 + squareSum y) := by
  apply Real.sqrt_pos.mpr
  have := squareSum_nonneg y
  positivity

lemma normalized_coordinate {n : ℕ} (i : Fin (n + 1)) (y : Euclidean n) :
    (normalizedRepresentative i y).val i ≠ 0 := by
  simp [normalizedRepresentative, insertOne, (sqrt_normalizer_pos y).ne']

@[simp] lemma ratios_inverse {n : ℕ} (i : Fin (n + 1)) (y : Euclidean n) :
    projectiveRatios i (projectiveInverse i y) = y := by
  funext j
  change (insertOne i y (i.succAbove j) / Real.sqrt (1 + squareSum y)) /
    (insertOne i y i / Real.sqrt (1 + squareSum y)) = y j
  simpa only [insertOne, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same, div_one]
    using div_div_div_cancel_right₀ (sqrt_normalizer_pos y).ne' (y j) 1

lemma inverse_mem_locus {n : ℕ} (i : Fin (n + 1)) (y : Euclidean n) :
    projectiveInverse i y ∈ projectiveLocus i :=
  (projection_mem_locus _ _).mpr (normalized_coordinate i y)

lemma inverse_ratios {n : ℕ} (i : Fin (n + 1)) (p : RealProjectiveSpace n)
    (hp : p ∈ projectiveLocus i) : projectiveInverse i (projectiveRatios i p) = p := by
  induction p using Quotient.inductionOn with | _ x =>
  apply ratios_fiber i _ x (normalized_coordinate i _)
    ((projection_mem_locus i x).mp hp)
  exact ratios_inverse i _

lemma continuous_insertOne {n : ℕ} (i : Fin (n + 1)) : Continuous (insertOne i) := by
  apply continuous_pi
  intro j
  obtain rfl | ⟨k, rfl⟩ := i.eq_self_or_eq_succAbove j
  · simpa [insertOne] using (continuous_const : Continuous (fun _ : Euclidean n => (1 : ℝ)))
  · simpa [insertOne] using (continuous_apply k : Continuous (fun y : Euclidean n => y k))

lemma continuous_normalizedRepresentative {n : ℕ} (i : Fin (n + 1)) :
    Continuous (normalizedRepresentative i) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact ((continuous_apply j).comp (continuous_insertOne i)).div
    (Real.continuous_sqrt.comp (continuous_const.add (continuous_squareSum n)))
    (fun y => (sqrt_normalizer_pos y).ne')

lemma continuous_inverse {n : ℕ} (i : Fin (n + 1)) : Continuous (projectiveInverse i) :=
  (projection_isOpenQuotientMap n).continuous.comp (continuous_normalizedRepresentative i)

lemma continuousOn_ratios {n : ℕ} (i : Fin (n + 1)) :
    ContinuousOn (projectiveRatios i) (projectiveLocus i) := by
  intro p hp
  induction p using Quotient.inductionOn with | _ x =>
  apply ContinuousAt.continuousWithinAt
  apply (projection_isOpenQuotientMap n).continuousAt_comp_iff.mp
  apply continuousAt_pi.mpr
  intro j
  exact (((continuous_apply _).comp continuous_subtype_val).continuousAt).div
    (((continuous_apply _).comp continuous_subtype_val).continuousAt)
    ((projection_mem_locus i x).mp hp)

/-- The actual globally surjective ratio chart onto R^n. -/
noncomputable def projectiveChart {n : ℕ} (i : Fin (n + 1)) :
    ModelChart n .euclidean (RealProjectiveSpace n) where
  toFun p := ⟨projectiveRatios i p, mem_univ _⟩
  invFun y := projectiveInverse i y.val
  source := projectiveLocus i
  target := univ
  map_source' _ _ := mem_univ _
  map_target' y _ := inverse_mem_locus i y.val
  left_inv' p hp := inverse_ratios i p hp
  right_inv' y _ := Subtype.ext (ratios_inverse i y.val)
  open_source := isOpen_locus i
  open_target := isOpen_univ
  continuousOn_toFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr (continuousOn_ratios i)
  continuousOn_invFun := ((continuous_inverse i).comp continuous_subtype_val).continuousOn

lemma projectiveChart_spec {n : ℕ} (i : Fin (n + 1)) :
    IsProjectiveChart i (projectiveChart i) := ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem projectiveCharts :
    Specs.SmoothManifolds.Examples.RealProjectiveSpace.projectiveChartsType :=
  fun _ i => ⟨projectiveChart i, projectiveChart_spec i⟩

lemma contDiff_insertOne {n : ℕ} (i : Fin (n + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (insertOne i) := by
  apply contDiff_pi.mpr
  intro j
  obtain rfl | ⟨k, rfl⟩ := i.eq_self_or_eq_succAbove j
  · simpa [insertOne] using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Euclidean n => (1 : ℝ)))
  · simpa [insertOne] using (contDiff_apply ℝ (fun _ => ℝ) k : ContDiff ℝ (⊤ : ℕ∞) (fun y : Euclidean n => y k))

lemma isOpen_overlap {n : ℕ} (i j : Fin (n + 1)) : IsOpen (projectiveOverlap i j) :=
  isOpen_ne_fun ((continuous_apply j).comp (continuous_insertOne i)) continuous_const

lemma contDiffOn_transition {n : ℕ} (i j : Fin (n + 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (projectiveTransition i j) (projectiveOverlap i j) := by
  apply contDiffOn_pi.mpr
  intro k
  exact ((contDiff_apply ℝ (fun _ => ℝ) (j.succAbove k)).comp (contDiff_insertOne i)).contDiffOn.div
    ((contDiff_apply ℝ (fun _ => ℝ) j).comp (contDiff_insertOne i)).contDiffOn (fun _ hy => hy)

lemma overlap_ratios {n : ℕ} (i j : Fin (n + 1)) (p : RealProjectiveSpace n)
    (hi : p ∈ projectiveLocus i) (hj : p ∈ projectiveLocus j) :
    projectiveRatios i p ∈ projectiveOverlap i j := by
  induction p using Quotient.inductionOn with | _ x =>
  change insertOne i (projectiveRatios i (projectiveProjection x)) j ≠ 0
  rw [insertOne_ratios i x ((projection_mem_locus i x).mp hi)]
  exact div_ne_zero ((projection_mem_locus j x).mp hj) ((projection_mem_locus i x).mp hi)

lemma transition_ratios {n : ℕ} (i j : Fin (n + 1)) (p : RealProjectiveSpace n)
    (hi : p ∈ projectiveLocus i) :
    projectiveRatios j p = projectiveTransition i j (projectiveRatios i p) := by
  induction p using Quotient.inductionOn with | _ x =>
  have hx := (projection_mem_locus i x).mp hi
  funext k
  change x.val (j.succAbove k) / x.val j =
    insertOne i (projectiveRatios i (projectiveProjection x)) (j.succAbove k) /
      insertOne i (projectiveRatios i (projectiveProjection x)) j
  rw [insertOne_ratios i x hx, insertOne_ratios i x hx]
  exact (div_div_div_cancel_right₀ hx _ _).symm

theorem projectiveTransitions :
    Specs.SmoothManifolds.Examples.RealProjectiveSpace.projectiveTransitionsType := by
  intro n i j
  exact ⟨isOpen_overlap i j, contDiffOn_transition i j,
    fun p hi hj => ⟨overlap_ratios i j p hi hj, transition_ratios i j p hi⟩⟩

lemma projectiveChart_germ {n : ℕ} {i j : Fin (n + 1)}
    {c d : ModelChart n .euclidean (RealProjectiveSpace n)}
    (hc : IsProjectiveChart i c) (hd : IsProjectiveChart j d)
    (p : RealProjectiveSpace n) (hp : p ∈ c.source) (hp' : p ∈ d.source) :
    ChartContDiffAt (⊤ : ℕ∞) c d id p := by
  refine ⟨projectiveOverlap i j, isOpen_overlap i j, ?_, projectiveTransition i j,
    contDiffOn_transition i j, ?_⟩
  · change (c p).val ∈ projectiveOverlap i j
    rw [hc.2.2.1 p hp]
    exact overlap_ratios i j p (hc.1 ▸ hp) (hd.1 ▸ hp')
  · filter_upwards [c.open_source.mem_nhds hp, d.open_source.mem_nhds hp'] with q hq hq'
    change projectiveTransition i j (c q).val = (d q).val
    rw [hc.2.2.1 q hq, hd.2.2.1 q hq']
    exact (transition_ratios i j q (hc.1 ▸ hq)).symm

lemma projectiveAtlas_isContDiffAtlas (n : ℕ) :
    IsContDiffAtlas (⊤ : ℕ∞) (projectiveAtlas n) := by
  constructor
  · intro p
    obtain ⟨i, hi⟩ := locus_cover p
    exact ⟨projectiveChart i, ⟨i, projectiveChart_spec i⟩, hi⟩
  · rintro c ⟨i, hc⟩ d ⟨j, hd⟩
    exact contDiffCompatible_of_germs (projectiveChart_germ hc hd) (projectiveChart_germ hd hc)

/-- The canonical maximal smooth atlas on the antipodal quotient. -/
noncomputable def projectiveManifold (n : ℕ) :
    SmoothManifold n .euclidean (RealProjectiveSpace n) :=
  ⟨⟨inferInstance, inferInstance, projectiveAtlas n, (projectiveAtlas_isContDiffAtlas n).1⟩,
    ⟨_, maximalExtension_isMaximal (projectiveAtlas_isContDiffAtlas n)⟩⟩

theorem projectiveManifold_exists :
    Specs.SmoothManifolds.Examples.RealProjectiveSpace.projectiveManifoldType := by
  intro n
  exact ⟨projectiveAtlas_isContDiffAtlas n, projectiveManifold n, rfl, rfl⟩

lemma projectiveZero_subsingleton : Subsingleton (RealProjectiveSpace 0) := by
  have hloc : ∀ p : RealProjectiveSpace 0, p ∈ projectiveLocus (0 : Fin 1) := by
    intro p
    obtain ⟨i, hi⟩ := locus_cover p
    have he : i = (0 : Fin 1) := Fin.eq_zero i
    rwa [he] at hi
  constructor
  intro p q
  rw [← inverse_ratios (0 : Fin 1) p (hloc p), ← inverse_ratios (0 : Fin 1) q (hloc q)]
  congr 1
  exact Subsingleton.elim _ _

theorem projectiveZero :
    Specs.SmoothManifolds.Examples.RealProjectiveSpace.projectiveZeroType := by
  let : Subsingleton (RealProjectiveSpace 0) := projectiveZero_subsingleton
  exact ⟨{
    toFun := fun _ => PUnit.unit
    invFun := fun _ => projectiveInverse (0 : Fin 1) (fun i => Fin.elim0 i)
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _
    continuous_toFun := continuous_const
    continuous_invFun := continuous_const }⟩

end SmoothManifolds.Projective
