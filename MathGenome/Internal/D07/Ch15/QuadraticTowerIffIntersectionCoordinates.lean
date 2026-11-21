import MathGenome.Internal.Specs.D07.Ch15.QuadraticTowerIffIntersectionCoordinates
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

namespace D07.Ch15.QuadraticTowerIffIntersectionCoordinates

open D07.Ch15.StraightedgeCompass
open Specs.D07.Ch15.QuadraticTowerIffIntersectionCoordinates

theorem line_equation : LineEquation := by
  intro M a b ha hb hab
  let ax : M := ⟨a.1, ha.1⟩
  let ay : M := ⟨a.2, ha.2⟩
  let bx : M := ⟨b.1, hb.1⟩
  let by' : M := ⟨b.2, hb.2⟩
  refine ⟨ay - by', bx - ax, ax * by' - bx * ay, ?_, ?_⟩
  · by_contra h
    push Not at h
    have hx : b.1 = a.1 := by
      have := congrArg (fun z : M => (z : ℝ)) h.2
      dsimp [bx, ax] at this
      exact sub_eq_zero.mp this
    have hy : a.2 = b.2 := by
      have := congrArg (fun z : M => (z : ℝ)) h.1
      dsimp [ay, by'] at this
      exact sub_eq_zero.mp this
    exact hab (Prod.ext hx.symm hy)
  · intro p
    change ((b.1 - a.1) * (p.2 - a.2) = (b.2 - a.2) * (p.1 - a.1)) ↔ _
    dsimp [ax, ay, bx, by']
    constructor <;> intro h <;> nlinarith [h]

theorem circle_equation : CircleEquation := by
  intro M c a b hc ha hb
  let x : M := ⟨c.1, hc.1⟩
  let y : M := ⟨c.2, hc.2⟩
  let r : M := (⟨a.1, ha.1⟩ - ⟨b.1, hb.1⟩) ^ 2 +
    (⟨a.2, ha.2⟩ - ⟨b.2, hb.2⟩) ^ 2
  refine ⟨-(x + x), -(y + y), x ^ 2 + y ^ 2 - r, ?_⟩
  intro p
  change squaredDistance p c = squaredDistance a b ↔ _
  dsimp [x, y, r, squaredDistance]
  constructor <;> intro h <;> nlinarith [h]

theorem concentric_circles_disjoint : ConcentricCirclesDisjoint := by
  intro c a b d e h
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact h (hp.symm.trans hq)

theorem zero_radicand : ZeroRadicand := by
  intro M
  simp [sqrtExtension, IntermediateField.adjoin_zero]

/-- The square root is integral over the actual real subfield, with a monic
annihilating polynomial of degree two. -/
theorem sqrt_extension_degree (M : IntermediateField ℚ ℝ) (d : M)
    (hd : 0 ≤ (d : ℝ)) :
    FiniteDimensional M (sqrtExtension M d) ∧
      Module.finrank M (sqrtExtension M d) ≤ 2 := by
  let f : Polynomial M := Polynomial.X ^ 2 - Polynomial.C d
  have hm : f.Monic := Polynomial.monic_X_pow_sub_C d (by decide)
  have hf : Polynomial.aeval (Real.sqrt (d : ℝ)) f = 0 := by
    simp [f, Real.sq_sqrt hd]
  have hi : IsIntegral M (Real.sqrt (d : ℝ)) := ⟨f, hm, hf⟩
  refine ⟨IntermediateField.adjoin.finiteDimensional hi, ?_⟩
  change Module.finrank M (IntermediateField.adjoin M {Real.sqrt (d : ℝ)}) ≤ 2
  rw [IntermediateField.adjoin.finrank hi]
  have hdeg := Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero M
    (Real.sqrt (d : ℝ)) hm.ne_zero hf)
  simpa [f] using hdeg

/-- Either real square root has membership in the same simple extension. -/
theorem mem_sqrt_extension_of_sq (M : IntermediateField ℚ ℝ) (d : M)
    {t : ℝ} (ht : t ^ 2 = (d : ℝ)) : t ∈ sqrtExtension M d := by
  have hd : 0 ≤ (d : ℝ) := ht ▸ sq_nonneg t
  have hs := Real.sq_sqrt hd
  have hm : Real.sqrt (d : ℝ) ∈ sqrtExtension M d :=
    IntermediateField.mem_adjoin_simple_self M _
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (ht.trans hs.symm) with h | h
  · exact h ▸ hm
  · rw [h]
    exact (sqrtExtension M d).neg_mem hm

/-- Base coordinates need no genuine adjunction; choosing d=0 makes the
simple extension the base field. -/
theorem in_quadratic_extension_of_coordinates (M : IntermediateField ℚ ℝ)
    {p : Point} (hp : HasCoordinates M p) : InQuadraticExtension M p := by
  obtain ⟨hf, hd⟩ := sqrt_extension_degree M 0 (by simp)
  refine ⟨0, by simp, hf, hd, ?_, ?_⟩
  · exact (sqrtExtension M 0).algebraMap_mem ⟨p.1, hp.1⟩
  · exact (sqrtExtension M 0).algebraMap_mem ⟨p.2, hp.2⟩

/-- Simultaneous linear and circle equations, without any division by an
individual line coefficient. Thus vertical lines are included. -/
theorem line_circle_coordinates_with_radicand (M : IntermediateField ℚ ℝ)
    (A B C cx cy r : M) (hAB : A ≠ 0 ∨ B ≠ 0) (p : Point)
    (hl : (A : ℝ) * p.1 + (B : ℝ) * p.2 + (C : ℝ) = 0)
    (hc : (p.1 - (cx : ℝ)) ^ 2 + (p.2 - (cy : ℝ)) ^ 2 = (r : ℝ)) :
    let d : M := (A ^ 2 + B ^ 2) * r - (A * cx + B * cy + C) ^ 2
    0 ≤ (d : ℝ) ∧ FiniteDimensional M (sqrtExtension M d) ∧
      Module.finrank M (sqrtExtension M d) ≤ 2 ∧
      p.1 ∈ sqrtExtension M d ∧ p.2 ∈ sqrtExtension M d := by
  let N : M := A ^ 2 + B ^ 2
  let L : M := A * cx + B * cy + C
  let d : M := N * r - L ^ 2
  let u : ℝ := (A : ℝ) * (p.2 - (cy : ℝ)) - (B : ℝ) * (p.1 - (cx : ℝ))
  have hN : (N : ℝ) ≠ 0 := by
    have hAB' : (A : ℝ) ≠ 0 ∨ (B : ℝ) ≠ 0 := by exact_mod_cast hAB
    dsimp [N]
    rcases hAB' with hA | hB
    · nlinarith [sq_pos_of_ne_zero hA, sq_nonneg (B : ℝ)]
    · nlinarith [sq_pos_of_ne_zero hB, sq_nonneg (A : ℝ)]
  have hl' : (A : ℝ) * (p.1 - (cx : ℝ)) +
      (B : ℝ) * (p.2 - (cy : ℝ)) = -(L : ℝ) := by
    dsimp [L]
    linear_combination hl
  have hu : u ^ 2 = (d : ℝ) := by
    calc
      u ^ 2 = ((A : ℝ) ^ 2 + (B : ℝ) ^ 2) *
          ((p.1 - (cx : ℝ)) ^ 2 + (p.2 - (cy : ℝ)) ^ 2) -
          ((A : ℝ) * (p.1 - (cx : ℝ)) + (B : ℝ) * (p.2 - (cy : ℝ))) ^ 2 := by
        dsimp [u]; ring
      _ = (d : ℝ) := by rw [hc, hl']; dsimp [d, N]; ring
  have hd : 0 ≤ (d : ℝ) := hu ▸ sq_nonneg u
  have hum := mem_sqrt_extension_of_sq M d hu
  let E := sqrtExtension M d
  have base (v : M) : (v : ℝ) ∈ E := E.algebraMap_mem v
  have hx : p.1 = (cx : ℝ) + (-(A : ℝ) * (L : ℝ) - (B : ℝ) * u) / (N : ℝ) := by
    rw [add_comm]
    apply sub_eq_iff_eq_add.mp
    apply (eq_div_iff hN).2
    dsimp [N, L, u]
    linear_combination (A : ℝ) * hl
  have hy : p.2 = (cy : ℝ) + (-(B : ℝ) * (L : ℝ) + (A : ℝ) * u) / (N : ℝ) := by
    rw [add_comm]
    apply sub_eq_iff_eq_add.mp
    apply (eq_div_iff hN).2
    dsimp [N, L, u]
    linear_combination (B : ℝ) * hl
  obtain ⟨hf, hdeg⟩ := sqrt_extension_degree M d hd
  refine ⟨hd, hf, hdeg, ?_, ?_⟩
  · rw [hx]
    exact E.add_mem (base cx) (E.div_mem
      (E.sub_mem (E.mul_mem (E.neg_mem (base A)) (base L)) (E.mul_mem (base B) hum)) (base N))
  · rw [hy]
    exact E.add_mem (base cy) (E.div_mem
      (E.add_mem (E.mul_mem (E.neg_mem (base B)) (base L)) (E.mul_mem (base A) hum)) (base N))

/-- Packaging the explicit common radicand as an extension witness. -/
theorem line_circle_coordinates (M : IntermediateField ℚ ℝ)
    (A B C cx cy r : M) (hAB : A ≠ 0 ∨ B ≠ 0) (p : Point)
    (hl : (A : ℝ) * p.1 + (B : ℝ) * p.2 + (C : ℝ) = 0)
    (hc : (p.1 - (cx : ℝ)) ^ 2 + (p.2 - (cy : ℝ)) ^ 2 = (r : ℝ)) :
    InQuadraticExtension M p :=
  ⟨_, line_circle_coordinates_with_radicand M A B C cx cy r hAB p hl hc⟩

theorem tangent_line_circle : TangentLineCircle := by
  intro M A B C cx cy r p hAB hl hc hd
  have h := line_circle_coordinates_with_radicand M A B C cx cy r hAB p hl hc
  dsimp only at h
  rw [hd, zero_radicand M] at h
  constructor
  · obtain ⟨x, hx⟩ := IntermediateField.mem_bot.mp h.2.2.2.1
    exact hx ▸ x.2
  · obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp h.2.2.2.2
    exact hy ▸ y.2

/-- Cramer's rule, with coefficients in the given subfield. -/
theorem two_linear_coordinates (M : IntermediateField ℚ ℝ)
    (A B C A' B' C' : M) (p : Point)
    (hD : A * B' - A' * B ≠ 0)
    (h1 : (A : ℝ) * p.1 + (B : ℝ) * p.2 + (C : ℝ) = 0)
    (h2 : (A' : ℝ) * p.1 + (B' : ℝ) * p.2 + (C' : ℝ) = 0) :
    HasCoordinates M p := by
  have hDr : (A : ℝ) * (B' : ℝ) - (A' : ℝ) * (B : ℝ) ≠ 0 := by
    exact_mod_cast hD
  have hx : p.1 = ((B : ℝ) * (C' : ℝ) - (B' : ℝ) * (C : ℝ)) /
      ((A : ℝ) * (B' : ℝ) - (A' : ℝ) * (B : ℝ)) := by
    apply (eq_div_iff hDr).2
    linear_combination (B' : ℝ) * h1 - (B : ℝ) * h2
  have hy : p.2 = ((C : ℝ) * (A' : ℝ) - (C' : ℝ) * (A : ℝ)) /
      ((A : ℝ) * (B' : ℝ) - (A' : ℝ) * (B : ℝ)) := by
    apply (eq_div_iff hDr).2
    linear_combination (A : ℝ) * h2 - (A' : ℝ) * h1
  constructor
  · rw [hx]
    exact M.div_mem (M.sub_mem (M.mul_mem B.2 C'.2) (M.mul_mem B'.2 C.2))
      (M.sub_mem (M.mul_mem A.2 B'.2) (M.mul_mem A'.2 B.2))
  · rw [hy]
    exact M.div_mem (M.sub_mem (M.mul_mem C.2 A'.2) (M.mul_mem C'.2 A.2))
      (M.sub_mem (M.mul_mem A.2 B'.2) (M.mul_mem A'.2 B.2))

/-- Parallel lines through a common point have the same locus. This also
covers the cases in which either line is vertical. -/
theorem linear_zero_of_parallel (A B C A' B' C' : ℝ) (p q : Point)
    (hAB : A ≠ 0 ∨ B ≠ 0) (hD : A * B' - A' * B = 0)
    (h1 : A * p.1 + B * p.2 + C = 0)
    (h2 : A' * p.1 + B' * p.2 + C' = 0)
    (hq : A * q.1 + B * q.2 + C = 0) :
    A' * q.1 + B' * q.2 + C' = 0 := by
  rcases hAB with hA | hB
  · apply (mul_eq_zero.mp (show A * (A' * q.1 + B' * q.2 + C') = 0 from ?_)).resolve_left hA
    linear_combination A' * hq + A * h2 - A' * h1 + (q.2 - p.2) * hD
  · apply (mul_eq_zero.mp (show B * (A' * q.1 + B' * q.2 + C') = 0 from ?_)).resolve_left hB
    linear_combination B' * hq + B * h2 - B' * h1 - (q.1 - p.1) * hD

/-- Distinct intersecting nondegenerate lines cannot have zero determinant. -/
theorem two_distinct_lines_coordinates (M : IntermediateField ℚ ℝ)
    (a b c d p : Point) (ha : HasCoordinates M a) (hb : HasCoordinates M b)
    (hc : HasCoordinates M c) (hd : HasCoordinates M d) (hab : a ≠ b) (hcd : c ≠ d)
    (hne : (Curve.line a b).locus ≠ (Curve.line c d).locus)
    (hp : p ∈ (Curve.line a b).locus) (hp' : p ∈ (Curve.line c d).locus) :
    HasCoordinates M p := by
  obtain ⟨A, B, C, hAB, hL⟩ := line_equation M a b ha hb hab
  obtain ⟨A', B', C', hAB', hL'⟩ := line_equation M c d hc hd hcd
  have h1 := (hL p).mp hp
  have h2 := (hL' p).mp hp'
  have hD : A * B' - A' * B ≠ 0 := by
    intro hz
    have hzr : (A : ℝ) * (B' : ℝ) - (A' : ℝ) * (B : ℝ) = 0 := by exact_mod_cast hz
    apply hne
    ext q
    rw [hL, hL']
    constructor
    · exact linear_zero_of_parallel _ _ _ _ _ _ p q (by exact_mod_cast hAB) hzr h1 h2
    · exact linear_zero_of_parallel _ _ _ _ _ _ p q (by exact_mod_cast hAB')
        (by nlinarith [hzr]) h2 h1
  exact two_linear_coordinates M A B C A' B' C' p hD h1 h2

theorem nonparallel_lines : NonparallelLines := by
  intro M a b c d p ha hb hc hd hdet hp hp'
  refine two_linear_coordinates M
    ⟨a.2 - b.2, M.sub_mem ha.2 hb.2⟩
    ⟨b.1 - a.1, M.sub_mem hb.1 ha.1⟩
    ⟨a.1 * b.2 - b.1 * a.2,
      M.sub_mem (M.mul_mem ha.1 hb.2) (M.mul_mem hb.1 ha.2)⟩
    ⟨c.2 - d.2, M.sub_mem hc.2 hd.2⟩
    ⟨d.1 - c.1, M.sub_mem hd.1 hc.1⟩
    ⟨c.1 * d.2 - d.1 * c.2,
      M.sub_mem (M.mul_mem hc.1 hd.2) (M.mul_mem hd.1 hc.2)⟩ p ?_ ?_ ?_
  · intro hz
    apply hdet
    have hzr := congrArg (fun z : M => (z : ℝ)) hz
    dsimp at hzr
    nlinarith [hzr]
  · change (b.1 - a.1) * (p.2 - a.2) = (b.2 - a.2) * (p.1 - a.1) at hp
    dsimp
    linear_combination hp
  · change (d.1 - c.1) * (p.2 - c.2) = (d.2 - c.2) * (p.1 - c.1) at hp'
    dsimp
    linear_combination hp'

/-- The geometric radius enters only through its squared value, which is in
M even if the radius itself is not. -/
theorem squared_distance_mem (M : IntermediateField ℚ ℝ) (a b : Point)
    (ha : HasCoordinates M a) (hb : HasCoordinates M b) : squaredDistance a b ∈ M :=
  M.add_mem (pow_mem (M.sub_mem ha.1 hb.1) 2) (pow_mem (M.sub_mem ha.2 hb.2) 2)

/-- Reduction of an actual allowed line and circle to the equation lemma. -/
theorem line_circle_intersection (M : IntermediateField ℚ ℝ)
    (a b c u v p : Point) (ha : HasCoordinates M a) (hb : HasCoordinates M b)
    (hc : HasCoordinates M c) (hu : HasCoordinates M u) (hv : HasCoordinates M v)
    (hab : a ≠ b) (hl : p ∈ (Curve.line a b).locus)
    (hcircle : p ∈ (Curve.circle c u v).locus) : InQuadraticExtension M p := by
  obtain ⟨A, B, C, hAB, heq⟩ := line_equation M a b ha hb hab
  exact line_circle_coordinates M A B C ⟨c.1, hc.1⟩ ⟨c.2, hc.2⟩
    ⟨squaredDistance u v, squared_distance_mem M u v hu hv⟩ hAB p ((heq p).mp hl) hcircle

/-- Subtracting circle equations produces a genuine line unless the centers
coincide. In that case an intersection forces the entire loci to coincide. -/
theorem circle_circle_intersection (M : IntermediateField ℚ ℝ)
    (c a b e u v p : Point) (hc : HasCoordinates M c)
    (ha : HasCoordinates M a) (hb : HasCoordinates M b)
    (he : HasCoordinates M e) (hu : HasCoordinates M u) (hv : HasCoordinates M v)
    (hne : (Curve.circle c a b).locus ≠ (Curve.circle e u v).locus)
    (h1 : p ∈ (Curve.circle c a b).locus)
    (h2 : p ∈ (Curve.circle e u v).locus) : InQuadraticExtension M p := by
  have hce : c ≠ e := by
    intro h
    subst e
    have hr : squaredDistance a b = squaredDistance u v := h1.symm.trans h2
    apply hne
    ext q
    change squaredDistance q c = squaredDistance a b ↔
      squaredDistance q c = squaredDistance u v
    rw [hr]
  let cx : M := ⟨c.1, hc.1⟩
  let cy : M := ⟨c.2, hc.2⟩
  let ex : M := ⟨e.1, he.1⟩
  let ey : M := ⟨e.2, he.2⟩
  let r : M := ⟨squaredDistance a b, squared_distance_mem M a b ha hb⟩
  let s : M := ⟨squaredDistance u v, squared_distance_mem M u v hu hv⟩
  let A : M := ex + ex - (cx + cx)
  let B : M := ey + ey - (cy + cy)
  let C : M := cx ^ 2 + cy ^ 2 - r - ex ^ 2 - ey ^ 2 + s
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_contra h
    push Not at h
    have hA := congrArg (fun z : M => (z : ℝ)) h.1
    have hB := congrArg (fun z : M => (z : ℝ)) h.2
    dsimp [A, B, cx, cy, ex, ey] at hA hB
    exact hce (Prod.ext (by linarith) (by linarith))
  apply line_circle_coordinates M A B C cx cy r hAB p ?_ h1
  change squaredDistance p c = squaredDistance a b at h1
  change squaredDistance p e = squaredDistance u v at h2
  dsimp [A, B, C, cx, cy, ex, ey, r, s, squaredDistance]
  dsimp [squaredDistance] at h1 h2
  linear_combination h1 - h2

/-- Both coordinates of every eligible selection belong to a single real
simple extension of the current coordinate field of degree at most two. -/
theorem intersection_coordinates : IntersectionCoordinates := by
  intro M S p hS hp
  obtain ⟨c, d, hc, hd, hne, _hfinite, hp, hp'⟩ := hp
  cases c with
  | line a b =>
    obtain ⟨ha, hb, hab⟩ := hc
    cases d with
    | line u v =>
      obtain ⟨hu, hv, huv⟩ := hd
      exact in_quadratic_extension_of_coordinates M
        (two_distinct_lines_coordinates M a b u v p (hS a ha) (hS b hb)
          (hS u hu) (hS v hv) hab huv hne hp hp')
    | circle e u v =>
      obtain ⟨he, hu, hv⟩ := hd
      exact line_circle_intersection M a b e u v p (hS a ha) (hS b hb)
        (hS e he) (hS u hu) (hS v hv) hab hp hp'
  | circle e a b =>
    obtain ⟨he, ha, hb⟩ := hc
    cases d with
    | line u v =>
      obtain ⟨hu, hv, huv⟩ := hd
      exact line_circle_intersection M u v e a b p (hS u hu) (hS v hv)
        (hS e he) (hS a ha) (hS b hb) huv hp' hp
    | circle f u v =>
      obtain ⟨hf, hu, hv⟩ := hd
      exact circle_circle_intersection M e a b f u v p (hS e he) (hS a ha) (hS b hb)
        (hS f hf) (hS u hu) (hS v hv) hne hp hp'

end D07.Ch15.QuadraticTowerIffIntersectionCoordinates
