import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.BoundaryGraphDirections
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionCornerCollar
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Two independent sign-correct graph descriptions of the actual planar
region, including reflex corners. The graph heights are continuous through
joins; their smooth parametrized half-arcs retain the original real lifts.
The original left-normal test determines the epigraph side. -/
noncomputable section
open Set Topology Filter
open scoped ContDiff
set_option maxHeartbeats 1200000

namespace P202.BoundaryGraphDirections
open P202Specs.PlanarRegionTopology P202Specs.BoundaryGraphDirections
open P202.PlanarRegionTopology


@[simp] theorem quarterTurn_smul (r : ℝ) (v : Plane) :
    quarterTurn (r • v) = r • quarterTurn v := by
  ext i
  fin_cases i <;> simp [quarterTurn]

@[simp] theorem quarterTurn_twice (v : Plane) : quarterTurn (quarterTurn v) = -v := by
  ext i
  fin_cases i <;> simp [quarterTurn]

@[simp] theorem inner_self_quarterTurn (v : Plane) : inner ℝ v (quarterTurn v) = 0 := by
  simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
  ring

@[simp] theorem norm_quarterTurn (v : Plane) : ‖quarterTurn v‖ = ‖v‖ := by
  have hh := quarterTurn_inner v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (quarterTurn v), norm_nonneg v]

/-- A nonzero oriented cross product detects independence of two planar columns. -/
theorem independent_of_cross {a b : Plane}
    (hcross : inner ℝ b (quarterTurn a) ≠ 0) : LinearIndependent ℝ ![a, b] := by
  apply linearIndependent_fin2.mpr
  change b ≠ 0 ∧ ∀ r : ℝ, r • b ≠ a
  constructor
  · intro hz
    exact hcross (by simp [hz])
  · intro r heq
    have hh := congrArg (fun x => inner ℝ x (quarterTurn a)) heq
    simp only [inner_smul_left, inner_self_quarterTurn, conj_trivial] at hh
    have hr : r = 0 := (mul_eq_zero.mp hh).resolve_right hcross
    have ha : a = 0 := by simpa [hr] using heq.symm
    exact hcross (by simp [ha, quarterTurn, PiLp.inner_apply, Fin.sum_univ_two])

/-- Perturb one strict direction inside its open cone, then normalize both
columns. The perturbation has a nonzero cross product even for equal tangents. -/
theorem twoStrictDirections : Expected.twoStrictDirections := by
  intro u v hu hv hn
  obtain ⟨a, ha, hau, hav⟩ := common_projection_direction hu hv hn
  have hcont : Continuous (fun r : ℝ => a + r • quarterTurn a) := by fun_prop
  have hpos : ∀ᶠ r in 𝓝 (0 : ℝ),
      0 < inner ℝ (a + r • quarterTurn a) u ∧
      0 < inner ℝ (a + r • quarterTurn a) v := by
    apply ((hcont.inner continuous_const).continuousAt.eventually
      (Ioi_mem_nhds (by simpa using hau))).and
    exact (hcont.inner continuous_const).continuousAt.eventually
      (Ioi_mem_nhds (by simpa using hav))
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hpos
  let r := η / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrη : r < η := by dsimp [r]; linarith
  let b := a + r • quarterTurn a
  have hbpos : 0 < inner ℝ b u ∧ 0 < inner ℝ b v := by
    apply hball
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hr] using hrη
  have hb : b ≠ 0 := by intro hz; simpa [hz] using hbpos.1
  have hcross : 0 < inner ℝ b (quarterTurn a) := by
    simp only [b, inner_add_left, inner_self_quarterTurn, inner_smul_left,
      conj_trivial, quarterTurn_inner, zero_add]
    exact mul_pos hr (real_inner_self_pos.mpr ha)
  let e : Fin 2 → Plane := ![NormedSpace.normalize a, NormedSpace.normalize b]
  refine ⟨e, independent_of_cross (ne_of_gt ?_), ?_⟩
  · change 0 < inner ℝ (NormedSpace.normalize b) (quarterTurn (NormedSpace.normalize a))
    simp only [NormedSpace.normalize, quarterTurn_smul, inner_smul_left, inner_smul_right,
      conj_trivial]
    positivity
  · intro k
    fin_cases k
    · exact ⟨NormedSpace.norm_normalize ha,
        by simpa [e, NormedSpace.normalize, inner_smul_left] using
          mul_pos (inv_pos.mpr (norm_pos_iff.mpr ha)) hau,
        by simpa [e, NormedSpace.normalize, inner_smul_left] using
          mul_pos (inv_pos.mpr (norm_pos_iff.mpr ha)) hav⟩
    · exact ⟨NormedSpace.norm_normalize hb,
        by simpa [e, NormedSpace.normalize, inner_smul_left] using
          mul_pos (inv_pos.mpr (norm_pos_iff.mpr hb)) hbpos.1,
        by simpa [e, NormedSpace.normalize, inner_smul_left] using
          mul_pos (inv_pos.mpr (norm_pos_iff.mpr hb)) hbpos.2⟩

/-- Retain both genuine smooth extensions, shrink below a period, and keep
strict signed derivatives on the *closed* half intervals. -/
theorem directedProjectionArc_of_extensions (c : RegularJordanCurve) (σ t δ : ℝ)
    (l r : ℝ → Plane) (e : Plane) (he : ‖e‖ = 1) (hδ : 0 < δ)
    (hl : ContDiffOn ℝ ∞ l (Ioo (t - δ) (t + δ)))
    (hr : ContDiffOn ℝ ∞ r (Ioo (t - δ) (t + δ)))
    (hel : EqOn l (realLift c.parametrization) (Icc (t - δ) t))
    (her : EqOn r (realLift c.parametrization) (Icc t (t + δ)))
    (hpl : 0 < σ * inner ℝ e (deriv l t))
    (hpr : 0 < σ * inner ℝ e (deriv r t)) :
    ∃ A : DirectedProjectionArc c σ t, A.axis = e := by
  have hpl' : 0 < inner ℝ (σ • e) (deriv l t) := by simpa only [inner_smul_left, conj_trivial] using hpl
  have hpr' : 0 < inner ℝ (σ • e) (deriv r t) := by simpa only [inner_smul_left, conj_trivial] using hpr
  obtain ⟨ε₀, hε₀, hmono⟩ := strict_projection_from_extensions hδ hl hr hel her hpl' hpr'
  have hpos := (eventually_positive_projection_deriv hδ hl hpl').and
    (eventually_positive_projection_deriv hδ hr hpr')
  obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp hpos
  let ε := min (min ε₀ δ) (min η 1) / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by
    have := (min_le_left (min ε₀ δ) (min η 1)).trans (min_le_right ε₀ δ)
    dsimp [ε]; linarith
  have hεη : ε < η := by
    have := (min_le_right (min ε₀ δ) (min η 1)).trans (min_le_left η 1)
    dsimp [ε]; linarith
  have hε₀' : ε ≤ ε₀ := by
    have := (min_le_left (min ε₀ δ) (min η 1)).trans (min_le_left ε₀ δ)
    dsimp [ε]; linarith
  have hshort : 2 * ε < 1 := by
    have := (min_le_right (min ε₀ δ) (min η 1)).trans (min_le_right η 1)
    dsimp [ε]; linarith
  have hsmall : ∀ u ∈ Icc (t - ε) (t + ε),
      0 < σ * inner ℝ e (deriv l u) ∧ 0 < σ * inner ℝ e (deriv r u) := by
    intro u hu
    have hmem : u ∈ Metric.ball t η := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2]
    simpa only [Set.mem_ofPred_eq, inner_smul_left, conj_trivial] using hηball hmem
  refine ⟨{
    radius := ε, radius_pos := hε, short := hshort, axis := e, unit_axis := he
    extensionRadius := δ, radius_lt := hεδ
    leftExtension := l, rightExtension := r, left_smooth := hl, right_smooth := hr
    left_eq := hel.mono (by intro u hu; exact ⟨by linarith [hu.1], hu.2⟩)
    right_eq := her.mono (by intro u hu; exact ⟨hu.1, by linarith [hu.2]⟩)
    left_positive := ?_, right_positive := ?_, increasing_signed := ?_ }, rfl⟩
  · intro u hu
    exact (hsmall u ⟨hu.1, by linarith [hu.2]⟩).1
  · intro u hu
    exact (hsmall u ⟨by linarith [hu.1], hu.2⟩).2
  · simpa only [arcProjection, inner_smul_left, conj_trivial] using
      hmono.mono (show Icc (t - ε) (t + ε) ⊆ Icc (t - ε₀) (t + ε₀) by
        intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)


/-- The sign acts on the axis, not on the original parameter or the curve. -/
theorem twoDirectedProjectionArcs : Expected.twoDirectedProjectionArcs := by
  intro c σ t hσ
  obtain ⟨δ, l, r, hδ, hl, hr, hel, her, hnl, hnr, hn⟩ := c.regular_joins t
  obtain ⟨e, hind, he⟩ := twoStrictDirections (deriv l t) (deriv r t) hnl hnr hn
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hArcs : ∀ k : Fin 2, ∃ A : DirectedProjectionArc c σ t, A.axis = σ • e k := by
    intro k
    apply directedProjectionArc_of_extensions c σ t δ l r (σ • e k) _ hδ hl hr hel her
    · simp only [inner_smul_left, conj_trivial, ← mul_assoc, hσσ, one_mul]
      exact (he k).2.1
    · simp only [inner_smul_left, conj_trivial, ← mul_assoc, hσσ, one_mul]
      exact (he k).2.2
    · rcases hσ with rfl | rfl <;> simpa using (he k).1
  choose A hA using hArcs
  refine ⟨A, ?_⟩
  simp only [hA]
  convert hind.units_smul (fun _ => Units.mk0 σ hσ0) using 1
  ext k
  rfl

/-- The signed strict projection gives the two ordinary substitution directions. -/
theorem DirectedProjectionArc.increasing {c : RegularJordanCurve} {σ t : ℝ}
    (A : DirectedProjectionArc c σ t) (hσ : σ = 1) :
    StrictMonoOn (arcProjection c A.axis) (Icc (t - A.radius) (t + A.radius)) := by
  simpa [hσ] using A.increasing_signed

theorem DirectedProjectionArc.decreasing {c : RegularJordanCurve} {σ t : ℝ}
    (A : DirectedProjectionArc c σ t) (hσ : σ = -1) :
    StrictAntiOn (arcProjection c A.axis) (Icc (t - A.radius) (t + A.radius)) := by
  intro x hx y hy hxy
  have hh := A.increasing_signed hx hy hxy
  simp only [hσ, neg_one_mul] at hh
  linarith

/-- Real lifts are periodic even when the chosen short interval crosses zero. -/
theorem realLift_periodic (c : RegularJordanCurve) :
    Function.Periodic (realLift c.parametrization) 1 := by
  intro t
  simp only [realLift, AddCircle.coe_add_period]

/-- No other component or distant part of the same quotient-parametrized curve
can visit this neighborhood. Uniqueness is on an interval shorter than a period. -/
theorem boundary_neighborhood_unique_visits (R : PlanarRegion) (i : Fin R.boundaryCount)
    (t ε : ℝ) (hε : 0 < ε) (hshort : 2 * ε < 1) :
    ∃ O : Set Plane, IsOpen O ∧ realLift (R.curve i).parametrization t ∈ O ∧
      R.boundary ∩ O =
        (realLift (R.curve i).parametrization '' Icc (t - ε) (t + ε)) ∩ O ∧
      ∀ (j : Fin R.boundaryCount) (q : ParameterCircle),
        (R.curve j).parametrization q ∈ O → j = i ∧
          ∃! u : ℝ, u ∈ Ioo (t - ε) (t + ε) ∧ (u : ParameterCircle) = q := by
  obtain ⟨O, hO, hp, heq⟩ := boundary_subarc_neighborhood R i t (ε / 2) (by positivity)
  have hliftinj : Set.InjOn (fun u : ℝ => (u : ParameterCircle)) (Icc (t - ε) (t + ε)) := by
    intro x hx y hy hxy
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show x ∈ Ico (t - ε) (t - ε + 1) from ⟨hx.1, by linarith [hx.2]⟩)
      (show y ∈ Ico (t - ε) (t - ε + 1) from ⟨hy.1, by linarith [hy.2]⟩)).mp hxy
  refine ⟨O, hO, hp, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨hxb, hxO⟩
      obtain ⟨u, hu, hux⟩ := (heq ▸ (show x ∈ O ∩ R.boundary from ⟨hxO, hxb⟩)).2
      exact ⟨⟨u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, hux⟩, hxO⟩
    · rintro x ⟨⟨u, _, rfl⟩, hxO⟩
      refine ⟨?_, hxO⟩
      change _ ∈ frontier R.domain
      rw [R.boundary_eq]
      exact mem_iUnion.mpr ⟨i, (u : ParameterCircle), rfl⟩
  · intro j q hqO
    have hqb : (R.curve j).parametrization q ∈ R.boundary := by
      change _ ∈ frontier R.domain
      rw [R.boundary_eq]
      exact mem_iUnion.mpr ⟨j, q, rfl⟩
    obtain ⟨u, hu, he⟩ := (heq ▸ (show (R.curve j).parametrization q ∈ O ∩ R.boundary
      from ⟨hqO, hqb⟩)).2
    have hji : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (R.disjoint_curves hne)
        (mem_range_self q) ⟨(u : ParameterCircle), he⟩
    subst j
    have hcoe : (u : ParameterCircle) = q := (R.curve i).injective he
    refine ⟨rfl, u, ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, hcoe⟩, ?_⟩
    intro v hv
    exact hliftinj ⟨hv.1.1.le, hv.1.2.le⟩
      ⟨by linarith [hu.1], by linarith [hu.2]⟩ (hv.2.trans hcoe.symm)

theorem orientedFrame_exists (e : Plane) (he : ‖e‖ = 1) : Nonempty (OrientedFrame e) := by
  have hsq : e 0 ^ 2 + e 1 ^ 2 = 1 := by
    have hh := EuclideanSpace.real_norm_sq_eq e
    simpa [he, Fin.sum_univ_two] using hh.symm
  let L : Plane →ₗ[ℝ] Plane :=
    { toFun := fun z => z 0 • e + z 1 • quarterTurn e
      map_add' := by intro x y; simp [add_smul]; abel
      map_smul' := by intro r x; simp [smul_add, smul_smul] }
  have hnorm : ∀ z, ‖L z‖ = ‖z‖ := by
    intro z
    have hh : ‖L z‖ ^ 2 = ‖z‖ ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      change (z 0 * e 0 + z 1 * (-e 1)) ^ 2 + (z 0 * e 1 + z 1 * e 0) ^ 2 = _
      nlinarith [sq_nonneg (z 0), sq_nonneg (z 1),
        mul_nonneg (sq_nonneg (z 0)) (sq_nonneg (e 0)),
        mul_nonneg (sq_nonneg (z 1)) (sq_nonneg (e 1))]
    nlinarith [norm_nonneg (L z), norm_nonneg z]
  let LI : Plane →ₗᵢ[ℝ] Plane := { L with norm_map' := hnorm }
  have hsurj : Function.Surjective LI := by
    intro x
    refine ⟨!₂[inner ℝ e x, inner ℝ (quarterTurn e) x], ?_⟩
    change inner ℝ e x • e + inner ℝ (quarterTurn e) x • quarterTurn e = x
    ext i
    fin_cases i
    · simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
      linear_combination x 0 * hsq
    · simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
      linear_combination x 1 * hsq
  exact ⟨⟨(LinearIsometryEquiv.ofSurjective LI hsurj).toAffineIsometryEquiv,
    fun _ => rfl⟩⟩

theorem frame_reconstruct {e : Plane} (he : ‖e‖ = 1) (v : Plane) :
    inner ℝ e v • e + inner ℝ (quarterTurn e) v • quarterTurn e = v := by
  have hsq : e 0 ^ 2 + e 1 ^ 2 = 1 := by
    have hh := EuclideanSpace.real_norm_sq_eq e
    simpa [he, Fin.sum_univ_two] using hh.symm
  ext i
  fin_cases i
  · simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination v 0 * hsq
  · simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination v 1 * hsq

theorem continuous_graph_of_projectedArcGraph (c : RegularJordanCurve) (σ t ε : ℝ)
    (e : Plane) (he : ‖e‖ = 1) (hσ : σ ≠ 0) (F : OrientedFrame e)
    (G : ProjectedArcGraph c t ε (σ • e))
    (hends : inner ℝ (σ • e) (realLift c.parametrization (t - ε)) ≤
      inner ℝ (σ • e) (realLift c.parametrization (t + ε))) :
    ∃ g : ℝ → ℝ, Continuous g ∧
      (∀ u ∈ Icc (t - ε) (t + ε), realLift c.parametrization u =
        F.map !₂[arcProjection c e u, g (arcProjection c e u)]) ∧
      (∀ x : ℝ,
        σ * x ∈ Icc (inner ℝ (σ • e) (realLift c.parametrization (t - ε)))
          (inner ℝ (σ • e) (realLift c.parametrization (t + ε))) →
        F.map !₂[x, g x] ∈ range G.map) := by
  let L := inner ℝ (σ • e) (realLift c.parametrization (t - ε))
  let U := inner ℝ (σ • e) (realLift c.parametrization (t + ε))
  let clamp : ℝ → Icc L U := projIcc L U hends
  let H : ℝ → Plane := fun x => G.map (clamp (σ * x))
  let g : ℝ → ℝ := fun x => inner ℝ (quarterTurn e) (H x)
  have hH : Continuous H := G.map.continuous.comp
    (continuous_projIcc.comp (continuous_const.mul continuous_id))
  refine ⟨g, continuous_const.inner hH, ?_, ?_⟩
  · intro u hu
    obtain ⟨x, hx⟩ : realLift c.parametrization u ∈ range G.map := by
      rw [G.image_eq]
      exact mem_image_of_mem _ hu
    have hp : σ * arcProjection c e u = x.val := by
      rw [← G.projection x, hx]
      simp [arcProjection, inner_smul_left]
    have hclamp : clamp (σ * arcProjection c e u) = x := by
      rw [hp]
      exact projIcc_of_mem hends x.property
    have hg : g (arcProjection c e u) = inner ℝ (quarterTurn e) (realLift c.parametrization u) := by
      simp only [g, H, hclamp, hx]
    rw [F.formula, hg]
    exact (frame_reconstruct he (realLift c.parametrization u)).symm
  · intro x hx
    have hproj : inner ℝ e (H x) = x := by
      apply mul_left_cancel₀ hσ
      have hh := G.projection (clamp (σ * x))
      calc
        σ * inner ℝ e (H x) = (clamp (σ * x)).val := by
          simpa only [inner_smul_left, conj_trivial, H] using hh
        _ = σ * x := congrArg Subtype.val (projIcc_of_mem hends hx)
    refine ⟨clamp (σ * x), ?_⟩
    change H x = F.map !₂[x, g x]
    rw [F.formula]
    change H x = x • e + inner ℝ (quarterTurn e) (H x) • quarterTurn e
    calc
      H x = inner ℝ e (H x) • e + inner ℝ (quarterTurn e) (H x) • quarterTurn e :=
        (frame_reconstruct he (H x)).symm
      _ = x • e + inner ℝ (quarterTurn e) (H x) • quarterTurn e := by rw [hproj]

/-- The oriented frame reads back the original horizontal scalar projection. -/
theorem frame_horizontal {e : Plane} (he : ‖e‖ = 1) (F : OrientedFrame e) (z : Plane) :
    inner ℝ e (F.map z) = z 0 := by
  rw [F.formula, inner_add_right, inner_smul_right, inner_smul_right,
    inner_self_quarterTurn, real_inner_self_eq_norm_sq, he]
  simp

/-- Full parametrized graph of the original boundary, apart from selecting
which of its sides is the domain. The support neighborhood sees unique lifts. -/
theorem parametrized_boundary_graph (R : PlanarRegion) (s : Fin R.boundaryCount → ℝ)
    (i : Fin R.boundaryCount) (t : ℝ) (hσ : s i ≠ 0)
    (A : DirectedProjectionArc (R.curve i) (s i) t) :
    ∃ (F : OrientedFrame A.axis) (g : ℝ → ℝ) (O : Set Plane),
      Continuous g ∧ IsOpen O ∧ realLift (R.curve i).parametrization t ∈ O ∧
      (∀ u ∈ Icc (t - A.radius) (t + A.radius),
        realLift (R.curve i).parametrization u =
          F.map !₂[arcProjection (R.curve i) A.axis u,
            g (arcProjection (R.curve i) A.axis u)]) ∧
      R.boundary ∩ O = (F.map '' {z : Plane | z 1 = g (z 0)}) ∩ O ∧
      R.boundary ∩ O =
        (realLift (R.curve i).parametrization '' Icc (t - A.radius) (t + A.radius)) ∩ O ∧
      ∀ (j : Fin R.boundaryCount) (q : ParameterCircle),
        (R.curve j).parametrization q ∈ O → j = i ∧
          ∃! u : ℝ, u ∈ Ioo (t - A.radius) (t + A.radius) ∧ (u : ParameterCircle) = q := by
  let c := R.curve i
  let a := s i • A.axis
  have hmono : StrictMonoOn (fun u => inner ℝ a (realLift c.parametrization u))
      (Icc (t - A.radius) (t + A.radius)) := by
    simpa only [a, arcProjection, inner_smul_left, conj_trivial] using A.increasing_signed
  obtain ⟨G⟩ := projectedArcGraph_of_strictMono c t A.radius a A.radius_pos hmono
  let L := inner ℝ a (realLift c.parametrization (t - A.radius))
  let U := inner ℝ a (realLift c.parametrization (t + A.radius))
  have hLt : L < inner ℝ a (realLift c.parametrization t) :=
    hmono ⟨le_rfl, by linarith [A.radius_pos]⟩
      ⟨by linarith [A.radius_pos], by linarith [A.radius_pos]⟩ (by linarith [A.radius_pos])
  have htU : inner ℝ a (realLift c.parametrization t) < U :=
    hmono ⟨by linarith [A.radius_pos], by linarith [A.radius_pos]⟩
      ⟨by linarith [A.radius_pos], le_rfl⟩ (by linarith [A.radius_pos])
  have hLU : L ≤ U := (hLt.trans htU).le
  obtain ⟨F⟩ := orientedFrame_exists A.axis A.unit_axis
  obtain ⟨g, hg, hidentity, hgraph⟩ := continuous_graph_of_projectedArcGraph
    c (s i) t A.radius A.axis A.unit_axis hσ F G hLU
  obtain ⟨N, hN, hpN, hNarc, hNvisits⟩ :=
    boundary_neighborhood_unique_visits R i t A.radius A.radius_pos A.short
  let O := N ∩ {p : Plane | L < inner ℝ a p ∧ inner ℝ a p < U}
  have hpO : realLift c.parametrization t ∈ O := ⟨hpN, hLt, htU⟩
  have hO : IsOpen O := hN.inter (isOpen_Ioo.preimage
    (show Continuous (fun p : Plane => inner ℝ a p) from continuous_const.inner continuous_id))
  have hsub : O ⊆ N := inter_subset_left
  have hOarc : R.boundary ∩ O =
      (realLift c.parametrization '' Icc (t - A.radius) (t + A.radius)) ∩ O := by
    ext p
    constructor
    · rintro ⟨hpb, hpO⟩
      exact ⟨(hNarc ▸ (show p ∈ R.boundary ∩ N from ⟨hpb, hsub hpO⟩)).1, hpO⟩
    · rintro ⟨hpa, hpO⟩
      exact ⟨(hNarc.symm ▸ (show p ∈ _ ∩ N from ⟨hpa, hsub hpO⟩)).1, hpO⟩
  refine ⟨F, g, O, hg, hO, hpO, hidentity, ?_, hOarc, ?_⟩
  · apply Subset.antisymm
    · intro p hp
      obtain ⟨u, hu, hup⟩ := (hOarc ▸ hp).1
      refine ⟨?_, hp.2⟩
      refine ⟨!₂[arcProjection c A.axis u, g (arcProjection c A.axis u)], by simp, ?_⟩
      exact (hidentity u hu).symm.trans hup
    · rintro p ⟨⟨z, hz, hzp⟩, hpO⟩
      have hproj : inner ℝ a p = s i * z 0 := by
        rw [← hzp]
        simp only [a, inner_smul_left, conj_trivial, frame_horizontal A.unit_axis F]
      have hx : s i * z 0 ∈ Icc L U := by
        rw [← hproj]
        exact ⟨hpO.2.1.le, hpO.2.2.le⟩
      have hzpair : z = !₂[z 0, g (z 0)] := by
        ext k
        fin_cases k
        · simp
        · simpa using hz
      have hprange : p ∈ range G.map := by
        rw [← hzp, hzpair]
        exact hgraph (z 0) hx
      obtain ⟨u, hu, hup⟩ := G.image_eq ▸ hprange
      refine ⟨?_, hpO⟩
      change p ∈ frontier R.domain
      rw [R.boundary_eq]
      exact mem_iUnion.mpr ⟨i, (u : ParameterCircle), hup⟩
  · intro j q hq
    exact hNvisits j q (hsub hq)


theorem differentiable_of_smooth_parameter {u v g : ℝ → ℝ} {q : ℝ}
    (hu : ContDiffAt ℝ ∞ u q) (hv : DifferentiableAt ℝ v q)
    (hun : deriv u q ≠ 0) (hgraph : (fun t => g (u t)) =ᶠ[𝓝 q] v) :
    DifferentiableAt ℝ g (u q) := by
  have hsu := hu.hasStrictDerivAt (by simp)
  let inv := hsu.localInverse u (deriv u q) q hun
  have hleft : inv (u q) = q := hsu.eventually_left_inverse hun |>.self_of_nhds
  have hdinv : DifferentiableAt ℝ inv (u q) := (hsu.to_localInverse hun).hasDerivAt.differentiableAt
  have htend : Tendsto inv (𝓝 (u q)) (𝓝 q) := by
    simpa only [hleft] using hdinv.continuousAt.tendsto
  have heq : g =ᶠ[𝓝 (u q)] (fun x => v (inv x)) := by
    filter_upwards [hsu.eventually_right_inverse hun, htend.eventually hgraph] with x hx hg
    change u (inv x) = x at hx
    simpa only [hx] using hg
  have hdv : DifferentiableAt ℝ v (inv (u q)) := hleft.symm ▸ hv
  exact (hdv.comp _ hdinv).congr_of_eventuallyEq heq

@[simp] theorem quarterTurn_neg (v : Plane) : quarterTurn (-v) = -quarterTurn v := by
  simpa using quarterTurn_smul (-1) v

theorem frame_vertical {e : Plane} (he : ‖e‖ = 1) (F : OrientedFrame e) (z : Plane) :
    inner ℝ (quarterTurn e) (F.map z) = z 1 := by
  have horth : inner ℝ (quarterTurn e) e = 0 := by
    rw [real_inner_comm]
    exact inner_self_quarterTurn e
  rw [F.formula, inner_add_right, inner_smul_right, inner_smul_right,
    horth, quarterTurn_inner, real_inner_self_eq_norm_sq, he]
  simp

theorem differentiable_graph_height {γ : ℝ → Plane} {e : Plane} {q : ℝ}
    (he : ‖e‖ = 1) (F : OrientedFrame e) (g : ℝ → ℝ)
    (hγ : ContDiffAt ℝ ∞ γ q) (hproj : inner ℝ e (deriv γ q) ≠ 0)
    (hgraph : ∀ᶠ t in 𝓝 q,
      γ t = F.map !₂[inner ℝ e (γ t), g (inner ℝ e (γ t))]) :
    DifferentiableAt ℝ g (inner ℝ e (γ q)) := by
  apply differentiable_of_smooth_parameter
    (u := fun t => inner ℝ e (γ t)) (v := fun t => inner ℝ (quarterTurn e) (γ t))
    (contDiffAt_const.inner ℝ hγ)
    ((differentiableAt_const _).inner ℝ (hγ.differentiableAt (by simp)))
  · simpa only [deriv_inner_apply ℝ (differentiableAt_const e)
      (hγ.differentiableAt (by simp)), deriv_const, inner_zero_left, zero_add, add_zero] using hproj
  · filter_upwards [hgraph] with t ht
    have hh := congrArg (fun p => inner ℝ (quarterTurn e) p) ht
    simpa only [frame_vertical he F, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] using hh.symm


/-- Smoothness is used only at a nonjoin parameter to test the actual side. -/
theorem graph_left_normal_positive (c : RegularJordanCurve) (σ q : ℝ)
    (hq : (q : ParameterCircle) ∉ c.joins) (e : Plane) (he : ‖e‖ = 1)
    (F : OrientedFrame e) (g : ℝ → ℝ)
    (hp : 0 < σ * inner ℝ e (deriv (realLift c.parametrization) q))
    (hgraph : ∀ᶠ t in 𝓝 q, realLift c.parametrization t =
      F.map !₂[inner ℝ e (realLift c.parametrization t),
        g (inner ℝ e (realLift c.parametrization t))]) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      0 < inner ℝ (quarterTurn e) (realLift c.parametrization q +
          r • (σ • quarterTurn (deriv (realLift c.parametrization) q))) -
        g (inner ℝ e (realLift c.parametrization q +
          r • (σ • quarterTurn (deriv (realLift c.parametrization) q)))) := by
  let γ := realLift c.parametrization
  let p := γ q
  let Z : Plane → ℝ := fun x => inner ℝ (quarterTurn e) x - g (inner ℝ e x)
  have hpn : inner ℝ e (deriv γ q) ≠ 0 := by
    intro hz
    change 0 < σ * inner ℝ e (deriv γ q) at hp
    rw [hz, mul_zero] at hp
    exact (lt_irrefl 0) hp
  have hdg := differentiable_graph_height he F g (c.smooth_off_joins q hq) hpn hgraph
  have hZ : DifferentiableAt ℝ Z p :=
    (innerSL ℝ (quarterTurn e)).differentiableAt.sub
      (hdg.comp p (innerSL ℝ e).differentiableAt)
  have hvan : ∀ᶠ t in 𝓝 q, Z (γ t) = 0 := by
    filter_upwards [hgraph] with t ht
    dsimp [Z]
    have hh := congrArg (fun x => inner ℝ (quarterTurn e) x) ht
    simpa [frame_vertical he F] using sub_eq_zero.mpr hh
  have hzero : Z p = 0 := hvan.self_of_nhds
  have htan : fderiv ℝ Z p (σ • deriv γ q) = 0 := by
    rw [map_smul, defining_function_tangent_zero c q hq Z hZ hvan, smul_zero]
  have hunit : fderiv ℝ Z p (quarterTurn e) = 1 := by
    have hdZ := (innerSL ℝ (quarterTurn e)).hasFDerivAt.sub
      (hdg.hasFDerivAt.comp p (innerSL ℝ e).hasFDerivAt)
    simp only [coe_innerSL_apply, Function.comp_def] at hdZ
    change HasFDerivAt Z _ p at hdZ
    rw [hdZ.fderiv]
    simp [ContinuousLinearMap.comp_apply, inner_self_quarterTurn, he]
  have htrans : 0 < inner ℝ (quarterTurn e) (quarterTurn (σ • deriv γ q)) := by
    simpa only [quarterTurn_smul, inner_smul_right, quarterTurn_inner] using hp
  have hpos := left_normal_covector_positive (fderiv ℝ Z p)
    (σ • deriv γ q) (quarterTurn e) htrans htan hunit
  rw [quarterTurn_smul] at hpos
  obtain ⟨ε, hε, hr⟩ := defining_function_normal_rays Z p _ hZ hzero hpos
  exact ⟨ε, hε, fun r hr0 hrε => (hr r hr0 hrε).1⟩

/-- A continuous height gives a global ambient homeomorphism; it is not
claimed to be differentiable at a corner. -/
theorem graph_flatten (e : Plane) (he : ‖e‖ = 1) (F : OrientedFrame e)
    (g : ℝ → ℝ) (hg : Continuous g) :
    ∃ H : Plane ≃ₜ Plane, ∀ p,
      (H p) 0 = inner ℝ e p ∧
      (H p) 1 = inner ℝ (quarterTurn e) p - g (inner ℝ e p) := by
  let H : Plane ≃ₜ Plane := {
    toFun := fun p => !₂[inner ℝ e p, inner ℝ (quarterTurn e) p - g (inner ℝ e p)]
    invFun := fun z => F.map !₂[z 0, z 1 + g (z 0)]
    left_inv := by
      intro p
      change F.map !₂[inner ℝ e p,
        (inner ℝ (quarterTurn e) p - g (inner ℝ e p)) + g (inner ℝ e p)] = p
      rw [sub_add_cancel, F.formula]
      exact frame_reconstruct he p
    right_inv := by
      intro z
      ext i
      fin_cases i
      · simp [frame_horizontal he F]
      · simp [frame_horizontal he F, frame_vertical he F]
    continuous_toFun := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop
    continuous_invFun := by
      apply F.map.continuous.comp
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop }
  exact ⟨H, fun _ => ⟨rfl, rfl⟩⟩

/-- Local one-sidedness selects one of the two connected sides of the actual
continuous graph. The orientation test subsequently resolves the alternative. -/
theorem local_graph_side_alternative (R : PlanarRegion) (e : Plane) (he : ‖e‖ = 1)
    (F : OrientedFrame e) (g : ℝ → ℝ) (hg : Continuous g) (N : Set Plane)
    (hN : IsOpen N) (p : Plane) (hpN : p ∈ N) (hpb : p ∈ R.boundary)
    (hgraph : R.boundary ∩ N = (F.map '' {z : Plane | z 1 = g (z 0)}) ∩ N) :
    ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧ V ⊆ N ∧
      ((∀ x ∈ V, x ∈ R.domain ↔ g (inner ℝ e x) < inner ℝ (quarterTurn e) x) ∨
       (∀ x ∈ V, x ∈ R.domain ↔ inner ℝ (quarterTurn e) x < g (inner ℝ e x))) := by
  obtain ⟨H, hH⟩ := graph_flatten e he F g hg
  have hzero : ∀ x ∈ N, x ∈ R.boundary ↔ (H x) 1 = 0 := by
    intro x hxN
    constructor
    · intro hxb
      obtain ⟨z, hz, hzx⟩ := (hgraph ▸ (show x ∈ R.boundary ∩ N from ⟨hxb, hxN⟩)).1
      rw [(hH x).2, ← hzx, frame_horizontal he F, frame_vertical he F, hz, sub_self]
    · intro hz
      have hgx : inner ℝ (quarterTurn e) x = g (inner ℝ e x) := by
        rw [(hH x).2] at hz
        exact sub_eq_zero.mp hz
      have hximage : x ∈ F.map '' {z : Plane | z 1 = g (z 0)} := by
        refine ⟨!₂[inner ℝ e x, inner ℝ (quarterTurn e) x], ?_, ?_⟩
        · exact hgx
        · rw [F.formula]
          exact frame_reconstruct he x
      exact (hgraph.symm ▸ (show x ∈ _ ∩ N from ⟨hximage, hxN⟩)).1
  have hopen : IsOpen (H '' N) := H.isOpenMap N hN
  obtain ⟨r, hr, hrN⟩ := Metric.isOpen_iff.mp hopen (H p) ⟨p, hpN, rfl⟩
  let W : Set Plane := Metric.ball (H p) r
  let V : Set Plane := H ⁻¹' W
  let A : Set Plane := H ⁻¹' (W ∩ {z : Plane | 0 < z 1})
  let B : Set Plane := H ⁻¹' (W ∩ {z : Plane | z 1 < 0})
  have hpV : p ∈ V := by
    change dist (H p) (H p) < r
    simpa only [dist_self] using hr
  have hW : IsOpen W := Metric.isOpen_ball
  have hV : IsOpen V := hW.preimage H.continuous
  have hVN : V ⊆ N := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hrN hx
    exact H.injective hyx ▸ hy
  have hA : IsPreconnected A := by
    apply H.isPreconnected_preimage.mpr
    exact ((convex_ball _ _).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage (EuclideanSpace.proj (1 : Fin 2)).toLinearMap)).isPreconnected
  have hB : IsPreconnected B := by
    apply H.isPreconnected_preimage.mpr
    exact ((convex_ball _ _).inter
      ((convex_Iio (0 : ℝ)).linear_preimage (EuclideanSpace.proj (1 : Fin 2)).toLinearMap)).isPreconnected
  have hpartition : V \ R.boundary = A ∪ B := by
    ext x
    constructor
    · rintro ⟨hxV, hxb⟩
      have hne : (H x) 1 ≠ 0 := fun hz => hxb ((hzero x (hVN hxV)).mpr hz)
      rcases lt_or_gt_of_ne hne with hn | hp
      · exact Or.inr ⟨hxV, hn⟩
      · exact Or.inl ⟨hxV, hp⟩
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, fun hxb => (ne_of_gt hx.2) ((hzero x (hVN hx.1)).mp hxb)⟩
      · exact ⟨hx.1, fun hxb => (ne_of_lt hx.2) ((hzero x (hVN hx.1)).mp hxb)⟩
  have hdisj : Disjoint R.domain R.boundary := by
    rw [Set.disjoint_left]
    intro x hxu hxb
    change x ∈ frontier R.domain at hxb
    have hxout : x ∉ R.domain := (R.open_domain.frontier_eq ▸ hxb).2
    exact hxout hxu
  obtain hsel | hsel := select_local_domain_side R.open_domain R.one_sided hpb
    hV hpV hA hB hpartition
  · refine ⟨V, hV, hpV, hVN, Or.inl ?_⟩
    intro x hx
    have hz : 0 < (H x) 1 ↔ g (inner ℝ e x) < inner ℝ (quarterTurn e) x := by
      rw [(hH x).2, sub_pos]
    rw [← hz]
    constructor
    · intro hxu
      have hn : (H x) 1 ≠ 0 := fun hz => Set.disjoint_left.mp hdisj hxu
        ((hzero x (hVN hx)).mpr hz)
      rcases lt_or_gt_of_ne hn with hn | hp
      · exact ((hsel.2 (show x ∈ B from ⟨hx, hn⟩)) (subset_closure hxu)).elim
      · exact hp
    · intro hp
      exact hsel.1 ⟨hx, hp⟩
  · refine ⟨V, hV, hpV, hVN, Or.inr ?_⟩
    intro x hx
    have hz : (H x) 1 < 0 ↔ inner ℝ (quarterTurn e) x < g (inner ℝ e x) := by
      rw [(hH x).2, sub_neg]
    rw [← hz]
    constructor
    · intro hxu
      have hn : (H x) 1 ≠ 0 := fun hz => Set.disjoint_left.mp hdisj hxu
        ((hzero x (hVN hx)).mpr hz)
      rcases lt_or_gt_of_ne hn with hn | hp
      · exact hn
      · exact ((hsel.2 (show x ∈ A from ⟨hx, hp⟩)) (subset_closure hxu)).elim
    · intro hn
      exact hsel.1 ⟨hx, hn⟩

/-- Resolve the local side using the original left-normal test at a nearby
smooth parameter. All extensions and the tested arc are original curve data. -/
theorem local_domain_is_above (R : PlanarRegion) (s : Fin R.boundaryCount → ℝ)
    (i : Fin R.boundaryCount) (t : ℝ)
    (hleft : HasSideOnLeft R.domain (R.curve i) (s i))
    (A : DirectedProjectionArc (R.curve i) (s i) t) (F : OrientedFrame A.axis)
    (g : ℝ → ℝ) (hg : Continuous g) (N : Set Plane) (hN : IsOpen N)
    (hpN : realLift (R.curve i).parametrization t ∈ N)
    (hidentity : ∀ u ∈ Icc (t - A.radius) (t + A.radius),
      realLift (R.curve i).parametrization u =
        F.map !₂[arcProjection (R.curve i) A.axis u,
          g (arcProjection (R.curve i) A.axis u)])
    (hboundary : R.boundary ∩ N = (F.map '' {z : Plane | z 1 = g (z 0)}) ∩ N) :
    ∃ V : Set Plane, IsOpen V ∧ realLift (R.curve i).parametrization t ∈ V ∧ V ⊆ N ∧
      ∀ x ∈ V, x ∈ R.domain ↔ g (inner ℝ A.axis x) < inner ℝ (quarterTurn A.axis) x := by
  let c := R.curve i
  let γ := realLift c.parametrization
  have hγ : Continuous γ := by
    change Continuous (realLift c.parametrization)
    unfold realLift
    fun_prop
  have hpb : γ t ∈ R.boundary := by
    change _ ∈ frontier R.domain
    rw [R.boundary_eq]
    exact mem_iUnion.mpr ⟨i, (t : ParameterCircle), rfl⟩
  obtain ⟨V, hV, hpV, hVN, hsel⟩ := local_graph_side_alternative
    R A.axis A.unit_axis F g hg N hN (γ t) hpN hpb hboundary
  refine ⟨V, hV, hpV, hVN, ?_⟩
  rcases hsel with hpos | hneg
  · exact hpos
  · exfalso
    have hpre : γ ⁻¹' V ∈ 𝓝 t := hγ.continuousAt.preimage_mem_nhds (hV.mem_nhds hpV)
    obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp hpre
    have htupper : t < min (t + A.radius) (t + η) :=
      lt_min (by linarith [A.radius_pos]) (by linarith)
    obtain ⟨q, hq, hqjoin⟩ := exists_nonjoin_in_Ioo c htupper
    have hqt : t < q := hq.1
    have hqr : q < t + A.radius := hq.2.trans_le (min_le_left _ _)
    have hqη : q < t + η := hq.2.trans_le (min_le_right _ _)
    have hqV : γ q ∈ V := by
      apply hηball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hevent : A.rightExtension =ᶠ[𝓝 q] γ := by
      filter_upwards [Ioo_mem_nhds hqt hqr] with u hu
      exact A.right_eq ⟨hu.1.le, hu.2.le⟩
    have hderiv : deriv A.rightExtension q = deriv γ q := hevent.deriv_eq
    have hpderiv : 0 < s i * inner ℝ A.axis (deriv γ q) := by
      rw [← hderiv]
      exact A.right_positive q ⟨hqt.le, hqr.le⟩
    have hgraph : ∀ᶠ u in 𝓝 q, γ u = F.map !₂[inner ℝ A.axis (γ u),
        g (inner ℝ A.axis (γ u))] := by
      filter_upwards [Ioo_mem_nhds hqt hqr] with u hu
      exact hidentity u ⟨by linarith [hu.1, A.radius_pos], hu.2.le⟩
    obtain ⟨ε, hε, hpositive⟩ := graph_left_normal_positive c (s i) q hqjoin
      A.axis A.unit_axis F g hpderiv hgraph
    obtain ⟨δ, hδ, hinside⟩ := hleft q hqjoin
    let n := s i • quarterTurn (deriv γ q)
    have hraycont : Continuous (fun r : ℝ => γ q + r • n) := by fun_prop
    have hrayV : ∀ᶠ r in 𝓝 (0 : ℝ), γ q + r • n ∈ V := by
      apply hraycont.continuousAt.eventually
      simpa using hV.mem_nhds hqV
    obtain ⟨ζ, hζ, hζball⟩ := Metric.mem_nhds_iff.mp hrayV
    let r := min (min ε δ) ζ / 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hrε : r < ε := by
      have := (min_le_left (min ε δ) ζ).trans (min_le_left ε δ)
      dsimp [r]; linarith
    have hrδ : r < δ := by
      have := (min_le_left (min ε δ) ζ).trans (min_le_right ε δ)
      dsimp [r]; linarith
    have hrζ : r < ζ := by have := min_le_right (min ε δ) ζ; dsimp [r]; linarith
    have hxV : γ q + r • n ∈ V := by
      apply hζball
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hr] using hrζ
    have hxin : γ q + r • n ∈ R.domain := hinside r hr hrδ
    have hbelow := (hneg _ hxV).mp hxin
    have habove := hpositive r hr hrε
    change 0 < inner ℝ (quarterTurn A.axis) (γ q + r • n) -
      g (inner ℝ A.axis (γ q + r • n)) at habove
    linarith

/-- Literal epigraph membership in the oriented isometric coordinates. -/
theorem frame_epigraph_iff {e : Plane} (he : ‖e‖ = 1) (F : OrientedFrame e)
    (g : ℝ → ℝ) (p : Plane) :
    p ∈ F.map '' {z : Plane | g (z 0) < z 1} ↔
      g (inner ℝ e p) < inner ℝ (quarterTurn e) p := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    change g (z 0) < z 1 at hz
    simpa only [frame_horizontal he F, frame_vertical he F] using hz
  · intro hp
    refine ⟨!₂[inner ℝ e p, inner ℝ (quarterTurn e) p], hp, ?_⟩
    rw [F.formula]
    exact frame_reconstruct he p

/-- Restriction of a literal local set identity to a smaller neighborhood. -/
theorem inter_eq_on_subset {X : Type*} {A B N V : Set X}
    (h : A ∩ N = B ∩ N) (hVN : V ⊆ N) : A ∩ V = B ∩ V := by
  ext x
  constructor
  · rintro ⟨hx, hxV⟩
    exact ⟨(h ▸ (show x ∈ A ∩ N from ⟨hx, hVN hxV⟩)).1, hxV⟩
  · rintro ⟨hx, hxV⟩
    exact ⟨(h.symm ▸ (show x ∈ B ∩ N from ⟨hx, hVN hxV⟩)).1, hxV⟩

/-- Construct the sign-correct graph from the original geometry. -/
theorem localDirectedBoundaryGraph_of_arc (R : PlanarRegion)
    (s : Fin R.boundaryCount → ℝ) (i : Fin R.boundaryCount) (t : ℝ)
    (hσ : s i ≠ 0) (hleft : HasSideOnLeft R.domain (R.curve i) (s i))
    (A : DirectedProjectionArc (R.curve i) (s i) t) :
    ∃ (O : Set Plane) (G : LocalDirectedBoundaryGraph R s i t O),
      IsOpen O ∧ realLift (R.curve i).parametrization t ∈ O ∧ G.arc = A := by
  obtain ⟨F, g, N, hg, hN, hpN, hid, hb, ha, hv⟩ :=
    parametrized_boundary_graph R s i t hσ A
  obtain ⟨O, hO, hpO, hON, hdomain⟩ :=
    local_domain_is_above R s i t hleft A F g hg N hN hpN hid hb
  refine ⟨O, {
    arc := A, frame := F, height := g, continuous_height := hg, arc_identity := hid
    domain_eq := ?_, boundary_eq := inter_eq_on_subset hb hON
    subarc_eq := inter_eq_on_subset ha hON
    increasing := DirectedProjectionArc.increasing A, decreasing := DirectedProjectionArc.decreasing A
    local_visits := fun j q hq => hv j q (hON hq)
    periodic := realLift_periodic (R.curve i)
    periodic_derivative := curve_derivative_periodic (R.curve i) }, hO, hpO, rfl⟩
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨hxU, hxO⟩
    exact ⟨(frame_epigraph_iff A.unit_axis F g x).mpr ((hdomain x hxO).mp hxU), hxO⟩
  · rintro ⟨hxg, hxO⟩
    exact ⟨(hdomain x hxO).mpr ((frame_epigraph_iff A.unit_axis F g x).mp hxg), hxO⟩

/-- All exact set and visit identities restrict to a common neighborhood. -/
def restrictLocalGraph {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {i : Fin R.boundaryCount} {t : ℝ} {N V : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t N) (hVN : V ⊆ N) :
    LocalDirectedBoundaryGraph R s i t V where
  arc := G.arc
  frame := G.frame
  height := G.height
  continuous_height := G.continuous_height
  arc_identity := G.arc_identity
  domain_eq := inter_eq_on_subset G.domain_eq hVN
  boundary_eq := inter_eq_on_subset G.boundary_eq hVN
  subarc_eq := inter_eq_on_subset G.subarc_eq hVN
  increasing := G.increasing
  decreasing := G.decreasing
  local_visits := fun j q hq => G.local_visits j q (hVN hq)
  periodic := G.periodic
  periodic_derivative := G.periodic_derivative

/-- Quarter turn preserves linear independence. -/
theorem quarterTurn_independent {e : Fin 2 → Plane} (he : LinearIndependent ℝ e) :
    LinearIndependent ℝ (fun k => quarterTurn (e k)) := by
  let J : Plane →ₗ[ℝ] Plane := {
    toFun := quarterTurn
    map_add' := by intro x y; ext k; fin_cases k <;> simp [quarterTurn]; ring
    map_smul' := by intro r x; exact quarterTurn_smul r x }
  have hinj : Function.Injective J := by
    intro x y hxy
    have hh := congrArg quarterTurn hxy
    simpa only [J, LinearMap.coe_mk, AddHom.coe_mk, quarterTurn_twice, neg_inj] using hh
  exact he.map' J (LinearMap.ker_eq_bot.mpr hinj)

/-- The complete two-direction construction at a specified original parameter. -/
theorem twoDirectionGraphs_at_parameter (R : PlanarRegion)
    (s : Fin R.boundaryCount → ℝ) (hs : IsInducedBoundaryOrientation R s)
    (i : Fin R.boundaryCount) (t : ℝ) :
    Nonempty (TwoDirectionBoundaryGraphs R s (realLift (R.curve i).parametrization t)) := by
  obtain ⟨A, hAind⟩ := twoDirectedProjectionArcs (R.curve i) (s i) t (hs i).1
  have hσ : s i ≠ 0 := by rcases (hs i).1 with h | h <;> rw [h] <;> norm_num
  have hex : ∀ k : Fin 2, ∃ (O : Set Plane) (G : LocalDirectedBoundaryGraph R s i t O),
      IsOpen O ∧ realLift (R.curve i).parametrization t ∈ O ∧ G.arc = A k :=
    fun k => localDirectedBoundaryGraph_of_arc R s i t hσ (hs i).2 (A k)
  choose N G hN hpN hGA using hex
  let O := N 0 ∩ N 1
  have hON : ∀ k : Fin 2, O ⊆ N k := by
    intro k
    fin_cases k
    · exact inter_subset_left
    · exact inter_subset_right
  let G' : Fin 2 → LocalDirectedBoundaryGraph R s i t O :=
    fun k => restrictLocalGraph (G k) (hON k)
  have haxis : ∀ k, (G' k).arc.axis = (A k).axis := fun k => congrArg DirectedProjectionArc.axis (hGA k)
  refine ⟨{
    component := i, parameter := t, at_point := rfl
    neighborhood := O, open_neighborhood := (hN 0).inter (hN 1)
    mem_neighborhood := ⟨hpN 0, hpN 1⟩
    graphs := G', independent := ?_, unit_normal := ?_ }⟩
  · simpa only [haxis] using quarterTurn_independent hAind
  · intro k
    rw [norm_quarterTurn]
    exact (G' k).arc.unit_axis

/-- Every actual boundary point is on its original component at a real lift.
The local construction includes joins, inserted smooth cuts and period seams. -/
theorem boundaryGraphDirections : Expected.boundaryGraphDirections := by
  intro R s hs p hp
  change p ∈ frontier R.domain at hp
  rw [R.boundary_eq] at hp
  obtain ⟨i, q, hqp⟩ := Set.mem_iUnion.mp hp
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective q
  have hpt : realLift (R.curve i).parametrization t = p := by
    simpa only [realLift, ht] using hqp
  rw [← hpt]
  exact twoDirectionGraphs_at_parameter R s hs i t

end P202.BoundaryGraphDirections
