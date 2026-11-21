import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.TorusHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.CellularComparison
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
The torus calculation in paper.tex, T21. The maps in this file land in the
actual product of circles. We construct its product cubical CW structure
and verify that opposite faces agree and cancel. Coordinate retractions
and naturality on the genuine skeletal relative homology groups show that
every cellular differential is zero, independently of disk orientations.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Topology Set
universe u v w x y

namespace P202.Homology.TorusHomology
open P202Specs.TorusHomology P202.Cellular
open P202Specs.CellularChains P202Specs.SingularChains
open P202Specs.RelativeSingularChains

@[simp] theorem circleLoop_zero : circleLoop 0 = 1 := by
  simp [circleLoop]

@[simp] theorem circleLoop_one : circleLoop 1 = 1 := by
  simp [circleLoop]

theorem circleLoop_eq_one_iff (t : unitInterval) : circleLoop t = 1 ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro ht
    obtain ⟨k, hk⟩ := Circle.exp_eq_one.mp ht
    have htk : (t : ℝ) = (k : ℝ) := by
      nlinarith [Real.pi_pos]
    have hk0 : (0 : ℤ) ≤ k := by exact_mod_cast (htk ▸ t.property.1)
    have hk1 : k ≤ (1 : ℤ) := by exact_mod_cast (htk ▸ t.property.2)
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with hk' | hk'
    · left
      apply Subtype.ext
      simpa [hk'] using htk
    · right
      apply Subtype.ext
      simpa [hk'] using htk
  · rintro (rfl | rfl) <;> simp [circleLoop]

theorem circleLoop_surjective : Function.Surjective circleLoop := by
  intro z
  let r := z.val.arg
  have hrlo : -Real.pi < r := Complex.neg_pi_lt_arg _
  have hrhi : r ≤ Real.pi := Complex.arg_le_pi _
  have hp : 0 < 2 * Real.pi := by positivity
  by_cases hr : 0 ≤ r
  · let t : unitInterval := ⟨r / (2 * Real.pi), (div_nonneg hr hp.le),
      (div_le_one hp).mpr (by linarith)⟩
    refine ⟨t, ?_⟩
    change Circle.exp (2 * Real.pi * (r / (2 * Real.pi))) = z
    rw [mul_div_cancel₀ _ (ne_of_gt hp)]
    exact Circle.exp_arg z
  · let t : unitInterval := ⟨(r + 2 * Real.pi) / (2 * Real.pi),
        div_nonneg (by linarith) hp.le, (div_le_one hp).mpr (by linarith)⟩
    refine ⟨t, ?_⟩
    change Circle.exp (2 * Real.pi * ((r + 2 * Real.pi) / (2 * Real.pi))) = z
    rw [mul_div_cancel₀ _ (ne_of_gt hp), Circle.exp_add_two_pi]
    exact Circle.exp_arg z

theorem circleLoop_interior_iff (t : unitInterval) :
    circleLoop t ≠ 1 ↔ 0 < (t : ℝ) ∧ (t : ℝ) < 1 := by
  rw [ne_eq, circleLoop_eq_one_iff, not_or]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact lt_of_le_of_ne t.property.1 (fun h => h0 (Subtype.ext h.symm))
    · exact lt_of_le_of_ne t.property.2 (fun h => h1 (Subtype.ext h))
  · rintro ⟨h0, h1⟩
    constructor <;> intro ht <;> subst t <;> norm_num at *

theorem circleLoop_inj_interior {t u : unitInterval}
    (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1)
    (hu : 0 < (u : ℝ) ∧ (u : ℝ) < 1)
    (h : circleLoop t = circleLoop u) : t = u := by
  have hp : 0 < 2 * Real.pi := by positivity
  have ht' : 2 * Real.pi * (t : ℝ) ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    constructor <;> nlinarith
  have hu' : 2 * Real.pi * (u : ℝ) ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    constructor <;> nlinarith
  have heq := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp) ht' hu' h
  apply Subtype.ext
  exact (mul_right_inj' (ne_of_gt hp)).mp heq

theorem image_cubeInterior {m : ℕ} (s : Finset (Fin m)) :
    cubeChart s '' cubeInterior s = coordinateStratum s := by
  classical
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    by_cases hi : i ∈ s
    · simp only [cubeChart, ContinuousMap.coe_mk, hi, iff_true]
      exact (circleLoop_interior_iff _).mpr (hx ⟨i, hi⟩)
    · simp [cubeChart, hi]
  · intro hz
    let x : Cube s := fun i => (circleLoop_surjective (z i.val)).choose
    have hx (i : s) : circleLoop (x i) = z i := (circleLoop_surjective (z i.val)).choose_spec
    refine ⟨x, ?_, ?_⟩
    · intro i
      apply (circleLoop_interior_iff _).mp
      rw [hx]
      exact (hz i).mpr i.property
    · funext i
      by_cases hi : i ∈ s
      · simpa only [cubeChart, ContinuousMap.coe_mk, dite_eq_left hi] using hx ⟨i, hi⟩
      · have hz1 : z i = 1 := Classical.not_not.mp (by simpa only [hi, iff_false] using hz i)
        simp only [cubeChart, ContinuousMap.coe_mk, dite_eq_right hi, hz1]

theorem cubeChart_injOn_interior {m : ℕ} (s : Finset (Fin m)) : Set.InjOn (cubeChart s) (cubeInterior s) := by
  classical
  intro x hx y hy hxy
  funext i
  have h := congrFun hxy i.val
  simp only [cubeChart, ContinuousMap.coe_mk, dite_eq_left i.property] at h
  exact circleLoop_inj_interior (hx i) (hy i) h


namespace CubeParametrization

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
def euclideanCube (n : ℕ) : Set (Ambient n) :=
  (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Set.Icc (0 : Fin n → ℝ) 1

theorem euclideanCube_convex (n : ℕ) : Convex ℝ (euclideanCube n) :=
  (convex_Icc (0 : Fin n → ℝ) 1).linear_preimage
    (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap

theorem euclideanCube_compact (n : ℕ) : IsCompact (euclideanCube n) := by
  exact (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc

theorem euclideanCube_interior (n : ℕ) : interior (euclideanCube n) = {x | ∀ i, 0 < x i ∧ x i < 1} := by
  change interior ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph ⁻¹' Set.Icc (0 : Fin n → ℝ) 1) = _
  rw [← (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.preimage_interior,
    ← pi_univ_Icc, interior_pi_set Set.finite_univ]
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, interior_Icc,
    Set.mem_Ioo, Set.mem_ofPred_eq]
  rfl

def coordinateCubeHomeomorph (n : ℕ) : euclideanCube n ≃ₜ (Fin n → unitInterval) where
  toFun x i := ⟨x.val i, x.property.1 i, x.property.2 i⟩
  invFun x := ⟨(EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => x i),
    ⟨fun i => (x i).property.1, fun i => (x i).property.2⟩⟩
  left_inv x := by ext i; rfl
  right_inv x := by ext i; rfl
  continuous_toFun := continuous_pi fun i =>
    ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp
    (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))).subtype_mk _

theorem diskCubeParametrization (n : ℕ) : ∃ e : Disk n ≃ₜ (Fin n → unitInterval),
    ∀ x, (∀ i, 0 < (e x i : ℝ) ∧ (e x i : ℝ) < 1) ↔ ‖x.val‖ < 1 := by
  have hne : (interior (euclideanCube n)).Nonempty := by
    rw [euclideanCube_interior]
    exact ⟨(EuclideanSpace.equiv (Fin n) ℝ).symm (fun _ => 1/2), fun _ => by norm_num⟩
  obtain ⟨h, hi, hc, _⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (euclideanCube_convex n) hne (euclideanCube_compact n).isBounded
  have hclosed : IsClosed (euclideanCube n) := (euclideanCube_compact n).isClosed
  let f : euclideanCube n ≃ₜ Disk n :=
    (h.image (euclideanCube n)).trans (Homeomorph.setCongr (by simpa [hclosed.closure_eq] using hc))
  refine ⟨f.symm.trans (coordinateCubeHomeomorph n), ?_⟩
  intro x
  have hf : h (f.symm x).val = x.val := by
    exact congrArg Subtype.val (f.apply_symm_apply x)
  change (∀ i, 0 < (f.symm x).val i ∧ (f.symm x).val i < 1) ↔ _
  change (f.symm x).val ∈ {y : Ambient n | ∀ i, 0 < y i ∧ y i < 1} ↔ _
  rw [← euclideanCube_interior]
  constructor
  · intro hx
    have hh : h (f.symm x).val ∈ Metric.ball (0 : Ambient n) 1 := hi ▸ Set.mem_image_of_mem h hx
    simpa only [hf, Metric.mem_ball, dist_zero_right] using hh
  · intro hx
    have hh : x.val ∈ h '' interior (euclideanCube n) := by
      rw [hi]
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    obtain ⟨y, hy, heq⟩ := hh
    have heq' : y = (f.symm x).val := h.injective (heq.trans hf.symm)
    exact heq' ▸ hy

end CubeParametrization

/-- There are precisely binomial(m,n) candidate n-cells, including all
empty-set, full-set, and above-dimension cases. -/
theorem card_activeSet (m n : ℕ) : Fintype.card (ActiveSet m n) = m.choose n := by
  simpa only [Fintype.card_fin] using Fintype.card_finset_len (α := Fin m) n

/-- Integral coordinates on the cells, expressed as the requested finite power. -/
def cellCoordinateEquiv (m n : ℕ) :
    (ActiveSet m n →₀ ℤ) ≃ₗ[ℤ] (Fin (m.choose n) → ℤ) :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ (ActiveSet m n)).trans
    (LinearEquiv.funCongrLeft ℤ ℤ (Fintype.equivFinOfCardEq (card_activeSet m n)).symm)

/-- The i-face of the cube, with i fixed to an endpoint. -/
def cubeFace {m : ℕ} (s : Finset (Fin m)) (i : s) (ε : unitInterval) :
    C(Cube (s.erase i.val), Cube s) where
  toFun x j := if h : j.val = i.val then ε else x ⟨j.val, by
    exact Finset.mem_erase.mpr ⟨h, j.property⟩⟩
  continuous_toFun := by
    classical
    apply continuous_pi
    intro j
    by_cases h : j.val = i.val
    · simp only [dite_eq_left h]
      exact continuous_const
    · simp only [dite_eq_right h]
      exact continuous_apply (⟨j.val, Finset.mem_erase.mpr ⟨h, j.property⟩⟩ : s.erase i.val)

/-- Each endpoint face has exactly the chart of the cell with i deleted. -/
theorem cubeChart_face {m : ℕ} (s : Finset (Fin m)) (i : s)
    (ε : unitInterval) (hε : circleLoop ε = 1) :
    (cubeChart s).comp (cubeFace s i ε) = cubeChart (s.erase i.val) := by
  classical
  apply ContinuousMap.ext
  intro x
  funext j
  by_cases hji : j = i.val
  · subst j
    simp [cubeChart, cubeFace, i.property, hε]
  · by_cases hj : j ∈ s
    · have hje : j ∈ s.erase i.val := Finset.mem_erase.mpr ⟨hji, hj⟩
      simp only [ContinuousMap.comp_apply, cubeChart, ContinuousMap.coe_mk,
        dite_eq_left hj, dite_eq_left hje]
      change circleLoop (if h : j = i.val then ε else x ⟨j, _⟩) = _
      rw [dite_eq_right hji]
    · have hje : j ∉ s.erase i.val := fun h => hj (Finset.mem_of_mem_erase h)
      simp [cubeChart, hj]

/-- Opposite faces agree as continuous maps to the actual torus. -/
theorem cubeChart_opposite_faces {m : ℕ} (s : Finset (Fin m)) (i : s) :
    (cubeChart s).comp (cubeFace s i 1) =
      (cubeChart s).comp (cubeFace s i 0) := by
  rw [cubeChart_face _ _ _ circleLoop_one, cubeChart_face _ _ _ circleLoop_zero]

/-- Opposite-face cancellation holds already in the free module on continuous
maps of the lower cube. No homological identification is used in this lemma. -/
theorem cubeChart_signed_faces {m : ℕ} (s : Finset (Fin m)) (i : s) (a : ℤ) :
    (Finsupp.single ((cubeChart s).comp (cubeFace s i 1)) a -
      Finsupp.single ((cubeChart s).comp (cubeFace s i 0)) a :
        C(Cube (s.erase i.val), Torus m) →₀ ℤ) = 0 := by
  rw [cubeChart_opposite_faces, sub_self]

/-- A coordinate subtorus, including all boundary strata of the selected cube. -/
def coordinateSubtorus {m : ℕ} (s : Finset (Fin m)) : Set (Torus m) :=
  {z | ∀ i, i ∉ s → z i = 1}

theorem range_cubeChart {m : ℕ} (s : Finset (Fin m)) :
    Set.range (cubeChart s) = coordinateSubtorus s := by
  classical
  ext z
  constructor
  · rintro ⟨x, rfl⟩ i hi
    simp [cubeChart, hi]
  · intro hz
    let x : Cube s := fun i => (circleLoop_surjective (z i.val)).choose
    refine ⟨x, ?_⟩
    funext i
    by_cases hi : i ∈ s
    · simp only [cubeChart, ContinuousMap.coe_mk, dite_eq_left hi]
      exact (circleLoop_surjective (z i)).choose_spec
    · simpa only [cubeChart, ContinuousMap.coe_mk, dite_eq_right hi] using (hz i hi).symm

theorem coordinateSubtorus_isClosed {m : ℕ} (s : Finset (Fin m)) :
    IsClosed (coordinateSubtorus s) := by
  simp only [coordinateSubtorus, Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply i) continuous_const

theorem cubeInterior_dense {m : ℕ} (s : Finset (Fin m)) : Dense (cubeInterior s) := by
  have hI : Dense (Set.Ioo (0 : unitInterval) 1) := by
    rw [dense_iff_closure_eq, closure_Ioo (by intro h; have h' := congrArg Subtype.val h; norm_num at h' : (0 : unitInterval) ≠ 1)]
    exact Set.Icc_bot_top
  convert (dense_pi Set.univ (fun (_ : s) _ => hI)) using 1
  ext x
  simp only [cubeInterior, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo]
  rfl

/-- The full cube maps onto the actual product torus, with its given topology. -/
theorem cubeChart_univ_surjective (m : ℕ) :
    Function.Surjective (cubeChart (Finset.univ : Finset (Fin m))) := by
  rw [← Set.range_eq_univ, range_cubeChart]
  ext z
  simp [coordinateSubtorus]

/-- This verifies the topology of the cubical quotient, not just its points. -/
theorem cubeChart_univ_isQuotientMap (m : ℕ) :
    IsQuotientMap (cubeChart (Finset.univ : Finset (Fin m))) :=
  (cubeChart _).continuous.isClosedMap.isQuotientMap (cubeChart _).continuous
    (cubeChart_univ_surjective m)

/-- Every closed cell is the closure of the corresponding open stratum. -/
theorem closure_coordinateStratum {m : ℕ} (s : Finset (Fin m)) :
    closure (coordinateStratum s) = coordinateSubtorus s := by
  rw [← image_cubeInterior,
    (cubeChart s).continuous.isClosedMap.closure_image_eq_of_continuous
      (cubeChart s).continuous, (cubeInterior_dense s).closure_eq, Set.image_univ,
    range_cubeChart]

/-- The cubical charts detect the actual topology on the product torus. -/
theorem cubical_closed_test (m : ℕ) (A : Set (Torus m)) :
    IsClosed A ↔ ∀ s : Finset (Fin m), IsClosed ((cubeChart s) ⁻¹' A) := by
  constructor
  · intro h s
    exact h.preimage (cubeChart s).continuous
  · intro h
    exact (cubeChart_univ_isQuotientMap m).isCoinducing.isClosed_preimage.mp (h Finset.univ)

/-- The active coordinate set of an actual point of the torus. -/
def activeCoordinates {m : ℕ} (z : Torus m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => z i ≠ 1)

@[simp] theorem mem_activeCoordinates {m : ℕ} (z : Torus m) (i : Fin m) :
    i ∈ activeCoordinates z ↔ z i ≠ 1 := by
  classical
  simp [activeCoordinates]

theorem coordinateStratum_unique {m : ℕ} (z : Torus m) :
    ∃! s : Finset (Fin m), z ∈ coordinateStratum s := by
  refine ⟨activeCoordinates z, ?_, ?_⟩
  · intro i
    exact (mem_activeCoordinates z i).symm
  · intro s hs
    ext i
    exact (hs i).symm.trans (mem_activeCoordinates z i).symm

abbrev OpenInterval := Set.Ioo (0 : ℝ) 1

def openCircleLoop : C(OpenInterval, Circle) where
  toFun t := Circle.exp (2 * Real.pi * t.val)
  continuous_toFun := Circle.exp.continuous.comp (by fun_prop)

theorem openCircleLoop_embedding : IsEmbedding openCircleLoop := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  apply IsOpenEmbedding.isEmbedding
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap openCircleLoop.continuous
  · intro t u h
    have heq : (⟨t.val, le_of_lt t.property.1, le_of_lt t.property.2⟩ : unitInterval) =
        ⟨u.val, le_of_lt u.property.1, le_of_lt u.property.2⟩ :=
      circleLoop_inj_interior t.property u.property h
    exact Subtype.ext (congrArg (fun v : unitInterval => (v : ℝ)) heq)
  · exact Circle.isCoveringMap_exp.isOpenMap.comp
      ((Homeomorph.mulLeft₀ (2 * Real.pi) hp).isOpenMap.comp isOpen_Ioo.isOpenMap_subtype_val)

def cubeInteriorHomeomorph {m : ℕ} (s : Finset (Fin m)) :
    cubeInterior s ≃ₜ (s → OpenInterval) where
  toFun x i := ⟨x.val i, x.property i⟩
  invFun x := ⟨fun i => ⟨x i, le_of_lt (x i).property.1, le_of_lt (x i).property.2⟩,
    fun i => (x i).property⟩
  left_inv x := by ext i; rfl
  right_inv x := by ext i; rfl
  continuous_toFun := continuous_pi fun i => by
    have h : Continuous (fun x : cubeInterior s => ((x.val i) : ℝ)) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)
    exact h.subtype_mk _
  continuous_invFun := (continuous_pi fun i =>
    (continuous_subtype_val.comp (continuous_apply i)).subtype_mk _).subtype_mk _

theorem cubeChart_interior_embedding {m : ℕ} (s : Finset (Fin m)) :
    IsEmbedding (fun x : cubeInterior s => cubeChart s x.val) := by
  classical
  let g : Torus m → s → Circle := fun z i => z i.val
  have hg : Continuous g := continuous_pi fun i => continuous_apply i.val
  have hf : Continuous (fun x : cubeInterior s => cubeChart s x.val) :=
    (cubeChart s).continuous.comp continuous_subtype_val
  apply IsEmbedding.of_comp hf hg
  have he := (Topology.IsEmbedding.piMap (fun _ : s => openCircleLoop_embedding)).comp
    (cubeInteriorHomeomorph s).isEmbedding
  convert he using 1
  funext x i
  simp [g, cubeChart, cubeInteriorHomeomorph, openCircleLoop, circleLoop, i.property, Pi.map]

/-- Euclidean disks give the chosen cubical characteristic domains. -/
def diskCubeForSet {m n : ℕ} (c : ActiveSet m n) : Disk n ≃ₜ Cube c.val :=
  (CubeParametrization.diskCubeParametrization n).choose.trans
    (Homeomorph.piCongrLeft (Y := fun _ : c.val => unitInterval)
      (Fintype.equivFinOfCardEq (by simpa using c.property)).symm)

theorem diskCubeForSet_interior {m n : ℕ} (c : ActiveSet m n) (x : Disk n) :
    diskCubeForSet c x ∈ cubeInterior c.val ↔ ‖x.val‖ < 1 := by
  let e : Fin n ≃ c.val := (Fintype.equivFinOfCardEq (by simpa using c.property)).symm
  have hs := (CubeParametrization.diskCubeParametrization n).choose_spec x
  rw [← hs]
  let y := (CubeParametrization.diskCubeParametrization n).choose x
  change (∀ i : c.val, 0 < (Homeomorph.piCongrLeft (Y := fun _ : c.val => unitInterval) e y i : ℝ) ∧
    (Homeomorph.piCongrLeft (Y := fun _ : c.val => unitInterval) e y i : ℝ) < 1) ↔ _
  constructor
  · intro hx i
    simpa only [Homeomorph.piCongrLeft_apply_apply] using hx (e i)
  · intro hx i
    obtain ⟨j, rfl⟩ := e.surjective i
    simpa only [Homeomorph.piCongrLeft_apply_apply] using hx j

def openDiskCube {m n : ℕ} (c : ActiveSet m n) : OpenDisk n ≃ₜ cubeInterior c.val where
  toFun x := ⟨diskCubeForSet c (interiorInclusion n x),
    (diskCubeForSet_interior c _).mpr (by simpa only [interiorInclusion, Metric.mem_ball, dist_zero_right] using x.property)⟩
  invFun y := ⟨((diskCubeForSet c).symm y.val).val, by
    have h := (diskCubeForSet_interior c ((diskCubeForSet c).symm y.val)).mp
      (by simpa using y.property)
    simpa only [Metric.mem_ball, dist_zero_right] using h⟩
  left_inv x := by
    apply Subtype.ext
    change (((diskCubeForSet c).symm (diskCubeForSet c (interiorInclusion n x))).val) = x.val
    rw [Homeomorph.symm_apply_apply]
    rfl
  right_inv y := by
    apply Subtype.ext
    exact (diskCubeForSet c).apply_symm_apply y.val
  continuous_toFun := ((diskCubeForSet c).continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp
    ((diskCubeForSet c).symm.continuous.comp continuous_subtype_val)).subtype_mk _

@[instance_reducible] def cubicalCellStructure (m : ℕ) : CellStructure (Torus m) where
  Cell n := ActiveSet m n
  characteristic n c := (cubeChart c.val).comp ⟨diskCubeForSet c, (diskCubeForSet c).continuous⟩

theorem cubical_openCell (m n : ℕ) (c : ActiveSet m n) :
    letI := cubicalCellStructure m
    openCell (Torus m) n c = coordinateStratum c.val := by
  letI := cubicalCellStructure m
  rw [← image_cubeInterior]
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(openDiskCube c x).val, (openDiskCube c x).property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(openDiskCube c).symm ⟨y, hy⟩, ?_⟩
    change cubeChart c.val (openDiskCube c ((openDiskCube c).symm ⟨y, hy⟩)).val = _
    rw [Homeomorph.apply_symm_apply]

theorem cubical_interior_embedding (m n : ℕ) (c : ActiveSet m n) :
    letI := cubicalCellStructure m
    IsEmbedding (interiorMap (Torus m) n c) :=
  (cubeChart_interior_embedding c.val).comp (openDiskCube c).isEmbedding

theorem cubical_closedCell (m n : ℕ) (c : ActiveSet m n) :
    letI := cubicalCellStructure m
    closedCell (Torus m) n c = coordinateSubtorus c.val := by
  letI := cubicalCellStructure m
  change Set.range ((cubeChart c.val) ∘ (diskCubeForSet c)) = _
  rw [Set.range_comp, (diskCubeForSet c).surjective.range_eq, Set.image_univ, range_cubeChart]

def totalCellEquiv (m : ℕ) : (Σ n, ActiveSet m n) ≃ Finset (Fin m) where
  toFun c := c.2.val
  invFun s := ⟨s.card, ⟨s, rfl⟩⟩
  left_inv := by rintro ⟨n, ⟨s, hs⟩⟩; cases hs; rfl
  right_inv _ := rfl

theorem cubical_cover (m : ℕ) :
    letI := cubicalCellStructure m
    ⋃ (n : ℕ) (c : Cell (Torus m) n), openCell (Torus m) n c = Set.univ := by
  letI := cubicalCellStructure m
  apply Set.eq_univ_of_forall
  intro z
  refine Set.mem_iUnion.mpr ⟨(activeCoordinates z).card, Set.mem_iUnion.mpr
    ⟨⟨activeCoordinates z, rfl⟩, ?_⟩⟩
  rw [cubical_openCell]
  intro i
  exact (mem_activeCoordinates z i).symm

theorem cubical_disjoint (m : ℕ) :
    letI := cubicalCellStructure m
    (Set.univ : Set (Σ n, Cell (Torus m) n)).PairwiseDisjoint
      (fun c => openCell (Torus m) c.1 c.2) := by
  letI := cubicalCellStructure m
  intro a _ b _ hab
  apply Set.disjoint_left.mpr
  intro z hza hzb
  apply hab
  apply (totalCellEquiv m).injective
  dsimp only at hza hzb
  rw [cubical_openCell] at hza hzb
  exact Finset.ext fun i => (hza i).symm.trans (hzb i)

theorem cubical_closure_finite (m n : ℕ) (c : ActiveSet m n) :
    letI := cubicalCellStructure m
    ∃ F : Finset (Σ k, Cell (Torus m) k),
      closedCell (Torus m) n c ⊆ ⋃ d ∈ F, openCell (Torus m) d.1 d.2 := by
  letI := cubicalCellStructure m
  letI : Fintype (Σ k, Cell (Torus m) k) :=
    Fintype.ofEquiv (Finset (Fin m)) (totalCellEquiv m).symm
  refine ⟨Finset.univ, ?_⟩
  intro z _
  have hz : z ∈ ⋃ (n : ℕ) (c : Cell (Torus m) n), openCell (Torus m) n c := by
    rw [cubical_cover]; trivial
  rcases Set.mem_iUnion.mp hz with ⟨k, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨d, hz⟩
  exact Set.mem_iUnion.mpr ⟨⟨k, d⟩, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, hz⟩⟩

theorem cubical_weak_topology (m : ℕ) (A : Set (Torus m)) :
    letI := cubicalCellStructure m
    IsClosed A ↔ ∀ n (c : Cell (Torus m) n), IsClosed (characteristic (Torus m) n c ⁻¹' A) := by
  letI := cubicalCellStructure m
  constructor
  · intro h n c
    exact h.preimage (characteristic (Torus m) n c).continuous
  · intro h
    apply (cubical_closed_test m A).mpr
    intro s
    let c : ActiveSet m s.card := ⟨s, rfl⟩
    exact (diskCubeForSet c).isQuotientMap.isCoinducing.isClosed_preimage.mp (h _ c)

theorem cubical_boundary_lands (m n : ℕ) (c : ActiveSet m n) :
    letI := cubicalCellStructure m
    Set.MapsTo (boundaryMap (Torus m) n c) Set.univ (skeletonLT (Torus m) n) := by
  classical
  letI := cubicalCellStructure m
  intro x _
  let z := boundaryMap (Torus m) n c x
  have hclosed : z ∈ closedCell (Torus m) n c := ⟨boundaryInclusion n x, rfl⟩
  rw [cubical_closedCell] at hclosed
  have hsub : activeCoordinates z ⊆ c.val := by
    intro i hi
    by_contra hi'
    exact (mem_activeCoordinates z i).mp hi (hclosed i hi')
  have hne : activeCoordinates z ≠ c.val := by
    intro heq
    have hint : diskCubeForSet c (boundaryInclusion n x) ∈ cubeInterior c.val := by
      intro i
      apply (circleLoop_interior_iff _).mp
      have hi : z i.val ≠ 1 := (mem_activeCoordinates z i.val).mp (by rw [heq]; exact i.property)
      change cubeChart c.val (diskCubeForSet c (boundaryInclusion n x)) i.val ≠ 1 at hi
      simpa only [ContinuousMap.coe_mk, cubeChart, dite_eq_left i.property] using hi
    have hlt := (diskCubeForSet_interior c _).mp hint
    have hnorm : ‖(boundaryInclusion n x).val‖ = 1 := by
      simpa only [boundaryInclusion, Metric.mem_sphere, dist_zero_right] using x.property
    linarith
  have hcard : (activeCoordinates z).card < n := by
    rw [← c.property]
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  refine Set.mem_iUnion.mpr ⟨(activeCoordinates z).card, Set.mem_iUnion.mpr
    ⟨hcard, Set.mem_iUnion.mpr ⟨⟨activeCoordinates z, rfl⟩, ?_⟩⟩⟩
  rw [cubical_openCell]
  intro i
  exact (mem_activeCoordinates z i).symm

@[instance_reducible] def cubicalCWStructure (m : ℕ) : CWStructure (Torus m) := by
  letI := cubicalCellStructure m
  exact P202.Topology.cwStructureOfWeak
    (cubical_interior_embedding m) (cubical_disjoint m) (cubical_cover m)
    (cubical_boundary_lands m) (cubical_closure_finite m) (cubical_weak_topology m)

theorem cubicalCWStructure_isProduct (m : ℕ) : IsProductCubical (cubicalCWStructure m) := by
  refine ⟨fun n => Equiv.refl (ActiveSet m n), ?_⟩
  intro n c
  exact ⟨cubical_openCell m n c, diskCubeForSet c, diskCubeForSet_interior c, rfl⟩


/-- Any complex with all its differentials zero has its chain module as homology.
This uses the actual categorical cycles and homology, including degree zero. -/
def homologyEquivOfZero {R : Type*} [CommRing R]
    (K : ChainComplex (ModuleCat R) ℕ) (h : ∀ i j, K.d i j = 0) (n : ℕ) :
    K.homology n ≃ₗ[R] K.X n :=
  ((K.isoHomologyπ _ n rfl (h _ _)).symm ≪≫
    K.iCyclesIso n _ rfl (h _ _)).toLinearEquiv

/-- The successor differentials determine all differentials, including the
zero map out of degree zero. -/
theorem cellular_d_zero {X : Type*} [TopologicalSpace X] [CWStructure X]
    (h : ∀ n, differential X ℤ ℤ n = 0) (i j : ℕ) :
    (cellularComplex X ℤ ℤ).d i j = 0 := by
  by_cases hij : i = j + 1
  · subst i
    simpa only [cellularComplex, ChainComplex.of_d] using h j
  · exact ChainComplex.of_d_ne _ _ hij

/-- Algebraic reduction of the singular homology calculation to a genuine CW
structure with the stated cell labels and vanishing skeletal differentials.
The geometric hypotheses here remain obligations, not additional premises of
the independent homology target. -/
theorem homology_of_cubical_geometry (m : ℕ) (C : CWStructure (Torus m))
    (hc : IsProductCubical C)
    (hd : letI : CWStructure (Torus m) := C
      ∀ n, differential (Torus m) ℤ ℤ n = 0) (j : ℕ) :
    Nonempty (homology ℤ ℤ (TopCat.of (Torus m)) (j : ℤ) ≃ₗ[ℤ]
      (Fin (m.choose j) → ℤ)) := by
  letI : CWStructure (Torus m) := C
  obtain ⟨cells, _⟩ := hc
  obtain ⟨e⟩ := P202.Homology.cellularCellGroups (Torus m) ℤ ℤ j
  exact ⟨(P202.Homology.CellularComparison.comparisonIso (Torus m) ℤ ℤ j).symm.toLinearEquiv.trans
    ((homologyEquivOfZero (cellularComplex (Torus m) ℤ ℤ) (cellular_d_zero hd) j).trans
      (e.trans ((Finsupp.mapDomain.linearEquiv ℤ ℤ (cells j)).trans
        (cellCoordinateEquiv m j))))⟩

/-- Degree zero of the actual product of circles, independently of a CW structure. -/
theorem torus_homology_zero (m : ℕ) :
    Nonempty (homology ℤ ℤ (TopCat.of (Torus m)) 0 ≃ₗ[ℤ] ℤ) := by
  obtain ⟨e⟩ := P202.SingularDegreeZero.degreeZero ℤ ℤ (TopCat.of (Torus m))
  exact ⟨e.trans (Finsupp.uniqueLinearEquiv ℤ ℤ (ZerothHomotopy.mk (1 : Torus m)))⟩

/-- The actual product of circles admits the specified cubical CW structure. -/
theorem cubicalStructure : P202Specs.TorusHomology.Expected.cubicalStructure := by
  intro m _
  exact ⟨cubicalCWStructure m, cubicalCWStructure_isProduct m⟩

/-- The geometric dimension bound gives vanishing in every degree above m. -/
theorem torus_homology_above_dimension (m j : ℕ) (hj : m < j) :
    IsZero (homology ℤ ℤ (TopCat.of (Torus m)) (j : ℤ)) := by
  letI := cubicalCWStructure m
  letI : IsEmpty (ActiveSet m j) := ⟨fun c => by
    have hle := Finset.card_le_univ c.val
    rw [Fintype.card_fin, c.property] at hle
    omega⟩
  obtain ⟨e⟩ := P202.Homology.cellularCellGroups (Torus m) ℤ ℤ j
  letI : Subsingleton (chainGroup (Torus m) ℤ ℤ j) := e.injective.subsingleton
  have hz : IsZero ((cellularComplex (Torus m) ℤ ℤ).X j) := by
    change IsZero (chainGroup (Torus m) ℤ ℤ j)
    exact ModuleCat.isZero_of_subsingleton _
  exact (P202.Homology.CellularComparison.comparisonIso (Torus m) ℤ ℤ j).isZero_iff.mp
    (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology

/-- Reset all circle coordinates outside `t` to the vertex. -/
def coordinateReset {m : ℕ} (t : Finset (Fin m)) : C(Torus m, Torus m) where
  toFun z i := if i ∈ t then z i else 1
  continuous_toFun := by
    classical
    apply continuous_pi
    intro i
    by_cases hi : i ∈ t
    · simpa only [ite_eq_left hi] using (continuous_apply i : Continuous (fun z : Torus m => z i))
    · simpa only [ite_eq_right hi] using (continuous_const : Continuous (fun _ : Torus m => (1 : Circle)))

@[simp] theorem activeCoordinates_coordinateReset {m : ℕ} (t : Finset (Fin m)) (z : Torus m) :
    activeCoordinates (coordinateReset t z) = activeCoordinates z ∩ t := by
  classical
  ext i
  by_cases hi : i ∈ t <;> simp [coordinateReset, hi]

theorem coordinateReset_cubeChart {m : ℕ} (t s : Finset (Fin m)) (hst : s ⊆ t) :
    (coordinateReset t).comp (cubeChart s) = cubeChart s := by
  classical
  ext x i
  by_cases hi : i ∈ t
  · simp [coordinateReset, hi]
  · have his : i ∉ s := fun his => hi (hst his)
    simp [coordinateReset, hi, cubeChart, his]

theorem activeCoordinates_cubeChart_subset {m : ℕ} (s : Finset (Fin m)) (x : Cube s) :
    activeCoordinates (cubeChart s x) ⊆ s := by
  classical
  intro i hi
  by_contra his
  have hne := (mem_activeCoordinates _ i).mp hi
  simpa [cubeChart, his] using hne

section ArbitraryProduct
variable {m : ℕ} [CWStructure (Torus m)]
variable (cells : ∀ n, Cell (Torus m) n ≃ ActiveSet m n)
variable (hstrata : ∀ n (c : Cell (Torus m) n),
  openCell (Torus m) n c = coordinateStratum (cells n c).val)

include cells hstrata

theorem skeletonLT_iff_activeCoordinates_card_lt (k : ℕ) (z : Torus m) :
    z ∈ skeletonLT (Torus m) k ↔ (activeCoordinates z).card < k := by
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨n, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hn, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨c, hz⟩
    rw [hstrata] at hz
    have heq : activeCoordinates z = (cells n c).val := by
      ext i
      exact (mem_activeCoordinates z i).trans (hz i)
    rw [heq, (cells n c).property]
    exact hn
  · intro hz
    let c := (cells (activeCoordinates z).card).symm ⟨activeCoordinates z, rfl⟩
    refine Set.mem_iUnion.mpr ⟨(activeCoordinates z).card,
      Set.mem_iUnion.mpr ⟨hz, Set.mem_iUnion.mpr ⟨c, ?_⟩⟩⟩
    rw [hstrata]
    simp only [c, Equiv.apply_symm_apply]
    intro i
    exact (mem_activeCoordinates z i).symm

theorem coordinateReset_preserves_skeletonLT (t : Finset (Fin m)) (k : ℕ) :
    Set.MapsTo (coordinateReset t) (skeletonLT (Torus m) k) (skeletonLT (Torus m) k) := by
  intro z hz
  apply (skeletonLT_iff_activeCoordinates_card_lt cells hstrata k _).mpr
  rw [activeCoordinates_coordinateReset]
  exact lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_left)
    ((skeletonLT_iff_activeCoordinates_card_lt cells hstrata k z).mp hz)

theorem coordinateReset_range_skeletonLT (t : Finset (Fin m)) :
    Set.MapsTo (coordinateReset t) Set.univ (skeletonLT (Torus m) (t.card + 1)) := by
  intro z _
  apply (skeletonLT_iff_activeCoordinates_card_lt cells hstrata _ _).mpr
  rw [activeCoordinates_coordinateReset]
  exact Nat.lt_succ_of_le (Finset.card_le_card Finset.inter_subset_right)

end ArbitraryProduct

section Characteristic
variable {m : ℕ} [CWStructure (Torus m)]
variable (cells : ∀ n, Cell (Torus m) n ≃ ActiveSet m n)
variable (hparam : ∀ n (c : Cell (Torus m) n),
  ∃ h : Disk n ≃ₜ Cube (cells n c).val,
    characteristic (Torus m) n c = (cubeChart (cells n c).val).comp ⟨h, h.continuous⟩)

include cells hparam

theorem activeCoordinates_characteristic_subset (n : ℕ) (c : Cell (Torus m) n) (x : Disk n) :
    activeCoordinates (characteristic (Torus m) n c x) ⊆ (cells n c).val := by
  obtain ⟨h, hh⟩ := hparam n c
  rw [hh]
  exact activeCoordinates_cubeChart_subset _ _

theorem coordinateReset_characteristic_eq (n : ℕ) (c : Cell (Torus m) n) :
    (coordinateReset (cells n c).val).comp (characteristic (Torus m) n c) =
      characteristic (Torus m) n c := by
  obtain ⟨h, hh⟩ := hparam n c
  rw [hh, ← ContinuousMap.comp_assoc,
    coordinateReset_cubeChart _ _ (fun _ hi => hi)]

theorem coordinateReset_other_characteristic_lands
    (hstrata : ∀ n (c : Cell (Torus m) n),
      openCell (Torus m) n c = coordinateStratum (cells n c).val)
    (n : ℕ) (c d : Cell (Torus m) n) (hd : d ≠ c) :
    Set.MapsTo ((coordinateReset (cells n c).val).comp (characteristic (Torus m) n d))
      Set.univ (skeletonLT (Torus m) n) := by
  intro x _
  apply (skeletonLT_iff_activeCoordinates_card_lt cells hstrata _ _).mpr
  rw [ContinuousMap.comp_apply, activeCoordinates_coordinateReset]
  have hsub : activeCoordinates (characteristic (Torus m) n d x) ∩ (cells n c).val ⊆
      (cells n c).val := Finset.inter_subset_right
  have hne : activeCoordinates (characteristic (Torus m) n d x) ∩ (cells n c).val ≠
      (cells n c).val := by
    intro heq
    have hcd : (cells n c).val ⊆ (cells n d).val := by
      rw [← heq]
      exact fun i hi => activeCoordinates_characteristic_subset cells hparam n d x
        (Finset.mem_inter.mp hi).1
    have hval : (cells n c).val = (cells n d).val :=
      Finset.eq_of_subset_of_card_le hcd (by rw [(cells n c).property, (cells n d).property])
    exact hd ((cells n).injective (Subtype.ext hval)).symm
  exact (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)).trans_eq
    (cells n c).property

end Characteristic

lemma relativeMap_eq_zero_of_range_subset
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {P Q : Pair.{w}} (f : P ⟶ Q) (h : ∀ x, f.map x ∈ Q.subspace) :
    relativeMap (ordinaryFunctor R M) f = 0 := by
  let g : P.space ⟶ Q.sub := TopCat.ofHom
    ⟨fun x => ⟨f.map x, h x⟩, f.map.hom.continuous.subtype_mk _⟩
  have hf : f.map = g ≫ Q.inclusion := rfl
  apply (cancel_epi (projection (ordinaryFunctor R M) P)).mp
  rw [projection_map, hf, Functor.map_comp, Category.assoc, cokernel.condition]
  simp

lemma relativeHomologyMap_eq_zero_of_range_subset
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {P Q : Pair.{w}} (f : P ⟶ Q) (h : ∀ x, f.map x ∈ Q.subspace) (j : ℤ) :
    (relativeHomologyFunctor R M j).map f = 0 := by
  change homologyMap (relativeMap (ordinaryFunctor R M) f) j = 0
  rw [relativeMap_eq_zero_of_range_subset R M f h]
  simp

lemma cellularDegreeMap_eq_zero_of_range_subset
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    [CellStructure X] [CellStructure Y]
    (f : CellularMap X Y) (n : ℕ) (h : ∀ x, f.map x ∈ skeletonLT Y n) :
    cellularDegreeMap R M f n = 0 := by
  exact relativeHomologyMap_eq_zero_of_range_subset R M (f.onPair n)
    (fun x => h x.val) (n : ℤ)

namespace CoordinateRetractions
variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {A : Type w} {B : Type x} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] {I : Type y}
lemma projection_coordinates (e : A ≃ₗ[R] (I →₀ M)) (p : A →ₗ[R] A) (c : I)
    (hself : ∀ m, p (e.symm (Finsupp.single c m)) = e.symm (Finsupp.single c m))
    (hother : ∀ d, d ≠ c → ∀ m, p (e.symm (Finsupp.single d m)) = 0)
    (a : A) : (e (p a)) c = (e a) c := by
  classical
  let f : (I →₀ M) →ₗ[R] M := (Finsupp.lapply c).comp (e.toLinearMap.comp (p.comp e.symm.toLinearMap))
  have hf : f = Finsupp.lapply c := by
    ext d m
    dsimp [f]
    by_cases hd : d = c
    · subst d
      rw [hself]
      simp
    · rw [hother d hd]
      simp [hd]
  have hh := congrArg (fun g : (I →₀ M) →ₗ[R] M => g (e a)) hf
  simpa [f] using hh

lemma linearMap_eq_zero_of_coordinate_retractions
    (e : A ≃ₗ[R] (I →₀ M)) (D : B →ₗ[R] A) (p : I → A →ₗ[R] A)
    (hzero : ∀ c, (p c).comp D = 0)
    (hself : ∀ c m, p c (e.symm (Finsupp.single c m)) = e.symm (Finsupp.single c m))
    (hother : ∀ c d, d ≠ c → ∀ m, p c (e.symm (Finsupp.single d m)) = 0) :
    D = 0 := by
  ext b
  apply e.injective
  ext c
  have hcoord := projection_coordinates e (p c) c (hself c) (hother c) (D b)
  have hp : p c (D b) = 0 := congrArg (fun f : B →ₗ[R] A => f b) (hzero c)
  rw [hp] at hcoord
  simpa using hcoord.symm
end CoordinateRetractions

lemma differential_eq_zero_of_cell_retractions
    (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (f : Cell X n → CellularMap X X)
    (hupper : ∀ c, cellularDegreeMap R M (f c) (n+1) = 0)
    (hself : ∀ c, characteristicPairMap n c ≫ (f c).onPair n = characteristicPairMap n c)
    (hother : ∀ c d, d ≠ c → ∀ x,
      (characteristicPairMap n d ≫ (f c).onPair n).map x ∈ (skeletalPair X n).subspace) :
    differential X R M n = 0 := by
  let e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)) :=
    (P202.Homology.cellGroupSumIso X R M n n).symm.toLinearEquiv
  have he (c : Cell X n) (a : relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)) :
      e.symm (Finsupp.single c a) =
        (relativeHomologyFunctor R M (n : ℤ)).map (characteristicPairMap n c) a := by
    exact P202.Homology.cellGroupSumIso_single X R M n n c a
  have hz : (differential X R M n).hom = 0 := by
    apply CoordinateRetractions.linearMap_eq_zero_of_coordinate_retractions e (differential X R M n).hom
      (fun c => (cellularDegreeMap R M (f c) n).hom)
    · intro c
      have hcomm := P202.Homology.cellularDegreeMap_comm R M (f c) n
      rw [hupper c, zero_comp] at hcomm
      exact congrArg ModuleCat.Hom.hom hcomm.symm
    · intro c a
      rw [he]
      change ((relativeHomologyFunctor R M (n : ℤ)).map (characteristicPairMap n c) ≫
        (relativeHomologyFunctor R M (n : ℤ)).map ((f c).onPair n)) a = _
      rw [← Functor.map_comp, hself c]
    · intro c d hdc a
      rw [he]
      change ((relativeHomologyFunctor R M (n : ℤ)).map (characteristicPairMap n d) ≫
        (relativeHomologyFunctor R M (n : ℤ)).map ((f c).onPair n)) a = 0
      rw [← Functor.map_comp,
        relativeHomologyMap_eq_zero_of_range_subset R M _ (hother c d hdc) (n : ℤ)]
      rfl
  exact ModuleCat.hom_ext hz

/-- Coordinate retractions detect every cellular coordinate. They kill the
next chain group, so naturality forces the genuine skeletal differential to
vanish. This proof is independent of the chosen disk orientations. -/
theorem product_cubical_differential_zero (m : ℕ) (C : CWStructure (Torus m))
    (hc : IsProductCubical C) :
    letI : CWStructure (Torus m) := C
    ∀ n, differential (Torus m) ℤ ℤ n = 0 := by
  letI : CWStructure (Torus m) := C
  obtain ⟨cells, hcells⟩ := hc
  have hstrata := fun n c => (hcells n c).1
  have hparam : ∀ n (c : Cell (Torus m) n),
      ∃ h : Disk n ≃ₜ Cube (cells n c).val,
        characteristic (Torus m) n c =
          (cubeChart (cells n c).val).comp ⟨h, h.continuous⟩ := by
    intro n c
    obtain ⟨h, _, hh⟩ := (hcells n c).2
    exact ⟨h, hh⟩
  intro n
  let f : Cell (Torus m) n → CellularMap (Torus m) (Torus m) := fun c =>
    ⟨coordinateReset (cells n c).val,
      coordinateReset_preserves_skeletonLT cells hstrata (cells n c).val⟩
  apply differential_eq_zero_of_cell_retractions (Torus m) ℤ ℤ n f
  · intro c
    apply cellularDegreeMap_eq_zero_of_range_subset
    intro z
    have hz := coordinateReset_range_skeletonLT cells hstrata (cells n c).val
      (x := z) (Set.mem_univ z)
    simpa only [(cells n c).property] using hz
  · intro c
    apply PairMap.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun g : C(Disk n, Torus m) => g z.down)
      (coordinateReset_characteristic_eq cells hparam n c)
  · intro c d hdc z
    exact coordinateReset_other_characteristic_lands cells hparam hstrata n c d hdc
      (x := z.down) (Set.mem_univ _)

/-- Every integral cellular differential vanishes for the product cells. -/
theorem zeroDifferentials : P202Specs.TorusHomology.Expected.zeroDifferentials := by
  intro m _ C hc
  exact product_cubical_differential_zero m C hc

/-- Ordinary integral singular homology of the actual finite product of
circles in every nonnegative degree. -/
theorem homology : P202Specs.TorusHomology.Expected.homology := by
  intro m _ j
  exact homology_of_cubical_geometry m (cubicalCWStructure m)
    (cubicalCWStructure_isProduct m)
    (product_cubical_differential_zero m (cubicalCWStructure m)
      (cubicalCWStructure_isProduct m)) j

end P202.Homology.TorusHomology
