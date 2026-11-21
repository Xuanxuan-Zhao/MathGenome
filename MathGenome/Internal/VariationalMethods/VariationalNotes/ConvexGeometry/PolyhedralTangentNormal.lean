import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolyhedralTangentNormal
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.PolarsBipolar
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.FiniteConesFarkas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

open Set Filter
open scoped Topology
noncomputable section
universe u v w
namespace VariationalNotes.ConvexGeometry

def contingentTangent {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (x : E) : Set E := Specs.contingentTangent C x

def polyhedralSet {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {I : Type v} {J : Type w} (a : I → E) (b : I → ℝ) (e : J → E) (d : J → ℝ) : Set E :=
  Specs.polyhedralSet a b e d

private def stepTime (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
private lemma stepTime_pos (k : ℕ) : 0 < stepTime k := by
  unfold stepTime
  positivity
private lemma stepTime_le_one (k : ℕ) : stepTime k ≤ 1 := by
  unfold stepTime
  rw [div_le_one (by positivity)]
  have := Nat.cast_nonneg (α := ℝ) k
  linarith
private lemma stepTime_tendsto : Tendsto stepTime atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- An eventually feasible ray supplies the positive-time contingent sequence. -/
private lemma mem_contingentTangent_of_ray {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {x v : E} (hx : x ∈ C)
    (h : ∀ᶠ k in atTop, x + stepTime k • v ∈ C) : v ∈ contingentTangent C x := by
  classical
  let z := fun k => if x + stepTime k • v ∈ C then x + stepTime k • v else x
  refine ⟨z, stepTime, ?_, stepTime_pos, stepTime_tendsto, ?_⟩
  · intro k
    dsimp [z]
    split <;> assumption
  · apply tendsto_const_nhds.congr'
    filter_upwards [h] with k hk
    simp [z, hk, smul_smul, (stepTime_pos k).ne']

lemma normal_nonpos_on_contingent {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {x v : E} {l : E →L[ℝ] ℝ}
    (hl : l ∈ normalCone C x) (hv : v ∈ contingentTangent C x) : l v ≤ 0 := by
  obtain ⟨z, t, hz, ht, _, hv⟩ := hv
  apply le_of_tendsto (l.continuous.tendsto v |>.comp hv)
  exact Eventually.of_forall fun k => by
    simpa using mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (ht k).le) (hl _ (hz k))

theorem convex_normal_tangent_polar : Specs.convex_normal_tangent_polar.{u} := by
  intro E _ _ C x hC hx
  ext l
  constructor
  · intro hl v hv
    exact normal_nonpos_on_contingent hl hv
  · intro hl y hy
    apply hl (y - x)
    apply mem_contingentTangent_of_ray hx
    exact Eventually.of_forall fun k =>
      hC.add_smul_mem hx (by simpa using hy) ⟨(stepTime_pos k).le, stepTime_le_one k⟩

theorem polyhedral_tangent : Specs.polyhedral_tangent.{u,v,w} := by
  intro E _ _ I J _ _ a b e d x hx
  ext v
  constructor
  · rintro ⟨z, t, hz, ht, _, hv⟩
    constructor
    · intro i hi
      apply le_of_tendsto ((continuous_const.inner continuous_id).tendsto v |>.comp hv)
      exact Eventually.of_forall fun k => by
        have h := (hz k).1 i
        change inner ℝ (a i) ((t k)⁻¹ • (z k - x)) ≤ 0
        rw [inner_smul_right, inner_sub_right]
        exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (ht k).le) (by linarith)
    · intro j
      have heq (k) : inner ℝ (e j) ((t k)⁻¹ • (z k - x)) = 0 := by
        simp only [inner_smul_right, inner_sub_right, (hz k).2 j, hx.2 j, sub_self, mul_zero]
      apply tendsto_nhds_unique ((continuous_const.inner continuous_id).tendsto v |>.comp hv)
      change Tendsto (fun k => inner ℝ (e j) ((t k)⁻¹ • (z k - x))) atTop (𝓝 0)
      simp_rw [heq]
      exact tendsto_const_nhds
  · intro hv
    apply mem_contingentTangent_of_ray hx
    have hlim : Tendsto (fun k => x + stepTime k • v) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add (stepTime_tendsto.smul (tendsto_const_nhds (x := v)))
    have hi : ∀ i, ∀ᶠ k in atTop, inner ℝ (a i) (x + stepTime k • v) ≤ b i := by
      intro i
      by_cases hia : inner ℝ (a i) x = b i
      · apply Eventually.of_forall
        intro k
        rw [inner_add_right, inner_smul_right, hia]
        exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (stepTime_pos k).le (hv.1 i hia))
      · have hlt : inner ℝ (a i) x < b i := lt_of_le_of_ne (hx.1 i) hia
        exact (((continuous_const.inner continuous_id).tendsto x).comp hlim).eventually
          (eventually_lt_nhds hlt) |>.mono fun _ hk => hk.le
    filter_upwards [eventually_all.mpr hi] with k hk
    refine ⟨hk, ?_⟩
    intro j
    simp only [inner_add_right, inner_smul_right, hv.2 j, mul_zero, add_zero, hx.2 j]

/-- The negative bipolar of finitely many generators is their conic hull.
Closedness, including an empty generating family, is supplied by the upstream theorem. -/
lemma mem_finite_conicHull_of_polar {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Type v} [Fintype K] (g : K → E) (z : E)
    (h : ∀ v : E, (∀ k, inner ℝ (g k) v ≤ 0) → inner ℝ z v ≤ 0) :
    z ∈ Specs.conicHull (range g) := by
  let C : ProperCone ℝ E :=
    ⟨PointedCone.hull ℝ (range g), finite_conicHull_isClosed g⟩
  by_contra hz
  obtain ⟨f, hf, hfz⟩ := C.hyperplane_separation_point hz
  let v := -(InnerProductSpace.toDual ℝ E).symm f
  have hv : ∀ k, inner ℝ (g k) v ≤ 0 := by
    intro k
    have hk := hf (g k) (PointedCone.subset_hull (mem_range_self k))
    change inner ℝ (g k) (-((InnerProductSpace.toDual ℝ E).symm f)) ≤ 0
    rw [inner_neg_right, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    linarith
  have hzv := h v hv
  have heq : inner ℝ z v = -f z := by
    change inner ℝ z (-((InnerProductSpace.toDual ℝ E).symm f)) = -f z
    rw [inner_neg_right, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  rw [heq] at hzv
  linarith

theorem polyhedral_normal : Specs.polyhedral_normal.{u,v,w} := by
  intro E _ _ _ I J _ _ a b e d x hx
  classical
  ext z
  constructor
  · intro hz
    let A := {i // inner ℝ (a i) x = b i}
    let g : A ⊕ (J ⊕ J) → E := Sum.elim (fun i => a i.val) (Sum.elim e (fun j => -e j))
    have hzg : z ∈ Specs.conicHull (range g) := by
      apply mem_finite_conicHull_of_polar
      intro v hv
      have hv' : v ∈ Specs.contingentTangent (Specs.polyhedralSet a b e d) x := by
        rw [polyhedral_tangent a b e d x hx]
        constructor
        · intro i hi
          exact hv (Sum.inl ⟨i, hi⟩)
        · intro j
          have hp := hv (Sum.inr (Sum.inl j))
          have hn := hv (Sum.inr (Sum.inr j))
          change inner ℝ (e j) v ≤ 0 at hp
          change inner ℝ (-e j) v ≤ 0 at hn
          rw [inner_neg_left] at hn
          linarith
      exact normal_nonpos_on_contingent hz hv'
    rw [finite_conicHull_eq g] at hzg
    obtain ⟨c, hc, hcz⟩ := hzg
    refine ⟨(fun i => c (Sum.inl i)),
      (fun j => c (Sum.inr (Sum.inl j)) - c (Sum.inr (Sum.inr j))),
      (fun i => hc (Sum.inl i)), ?_⟩
    rw [← hcz]
    simp only [Fintype.sum_sum_type, g, Sum.elim_inl, Sum.elim_inr, sub_smul,
      smul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    abel
  · rintro ⟨lam, nu, hlam, rfl⟩
    intro y hy
    change inner ℝ ((∑ i, lam i • a i.val) + ∑ j, nu j • e j) (y - x) ≤ 0
    rw [inner_add_left, sum_inner, sum_inner]
    have hi : (∑ i : {i // inner ℝ (a i) x = b i},
        inner ℝ (lam i • a i.val) (y - x)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      rw [real_inner_smul_left, inner_sub_right, i.property]
      exact mul_nonpos_of_nonneg_of_nonpos (hlam i) (sub_nonpos.mpr (hy.1 i.val))
    have hj : (∑ j, inner ℝ (nu j • e j) (y - x)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [real_inner_smul_left, inner_sub_right, hy.2 j, hx.2 j]
    linarith

lemma polyhedralSet_convex {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {I : Type v} {J : Type w} (a : I → E) (b : I → ℝ) (e : J → E) (d : J → ℝ) :
    Convex ℝ (polyhedralSet a b e d) := by
  intro y hy z hz s t hs ht hst
  constructor
  · intro i
    simp only [inner_add_right, inner_smul_right]
    calc
      s * inner ℝ (a i) y + t * inner ℝ (a i) z ≤ s * b i + t * b i :=
        add_le_add (mul_le_mul_of_nonneg_left (hy.1 i) hs)
          (mul_le_mul_of_nonneg_left (hz.1 i) ht)
      _ = b i := by rw [← add_mul, hst, one_mul]
  · intro j
    simp only [inner_add_right, inner_smul_right, hy.2 j, hz.2 j, ← add_mul, hst, one_mul]

theorem polyhedral_normal_polar : Specs.polyhedral_normal_polar.{u,v,w} := by
  intro E _ _ I J _ _ a b e d x hx
  exact convex_normal_tangent_polar _ _ (polyhedralSet_convex a b e d) hx

theorem polyhedral_dual_normal : Specs.polyhedral_dual_normal.{u,v,w} := by
  intro E _ _ _ I J _ _ a b e d x hx
  ext l
  constructor
  · intro hl
    let z := (InnerProductSpace.toDual ℝ E).symm l
    have hz : z ∈ (InnerProductSpace.toDual ℝ E) ⁻¹'
        Specs.normalCone (Specs.polyhedralSet a b e d) x := by
      simpa [z] using hl
    rw [polyhedral_normal a b e d x hx] at hz
    exact ⟨z, hz, (InnerProductSpace.toDual ℝ E).apply_symm_apply l⟩
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ (InnerProductSpace.toDual ℝ E) ⁻¹'
        Specs.normalCone (Specs.polyhedralSet a b e d) x := by
      rw [polyhedral_normal a b e d x hx]
      exact hz
    exact hz'

end VariationalNotes.ConvexGeometry
