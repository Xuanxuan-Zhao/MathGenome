import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.RefinedSlater
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.ConvexProgramModels
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.LocalValueSupport
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.PolyhedralSupport

noncomputable section
open Set Topology
open scoped BigOperators
universe u v w z
namespace VariationalNotes.Ch04
open ConvexAnalysis

section Algebra
variable {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J]

lemma commonDomain_convex (q : ConvexProgram X I A J) : Convex ℝ (commonDomain q) := by
  intro x hx y hy s t hs ht hst
  exact ⟨convex_effectiveDomain q.convex_f hx.1 hy.1 hs ht hst,
    fun i => convex_effectiveDomain (q.convex_g i) (hx.2 i) (hy.2 i) hs ht hst⟩

/-- Only the convex inequalities are perturbed; affine feasibility stays in P. -/
def slaterPerturbation (q : ConvexProgram X I A J) (z : X × (I → ℝ)) : WithTop ℝ := by
  classical
  exact if z.1 ∈ commonDomain q ∧ z.1 ∈ affinePolyhedron q ∧
    ∀ i, q.g i z.1 ≤ (z.2 i : WithTop ℝ) then q.f z.1 else ⊤

lemma slaterPerturbation_convex (q : ConvexProgram X I A J) :
    IsConvex (slaterPerturbation q) := by
  classical
  apply (convex_iff_twoPoint _).mpr
  intro x y r h hxr hyh s t hs ht hst
  have hx : x.1 ∈ commonDomain q ∧ x.1 ∈ affinePolyhedron q ∧
      ∀ i, q.g i x.1 ≤ (x.2 i : WithTop ℝ) := by
    by_contra hn
    simp [slaterPerturbation, hn] at hxr
  have hy : y.1 ∈ commonDomain q ∧ y.1 ∈ affinePolyhedron q ∧
      ∀ i, q.g i y.1 ≤ (y.2 i : WithTop ℝ) := by
    by_contra hn
    simp [slaterPerturbation, hn] at hyh
  have hdom := commonDomain_convex q hx.1 hy.1 hs ht hst
  have hP := affine_constraints_convex q.a q.b q.e q.d hx.2.1 hy.2.1 hs ht hst
  have hg : ∀ i, q.g i (s • x.1 + t • y.1) ≤
      (((s • x.2 + t • y.2) i : ℝ) : WithTop ℝ) := by
    intro i
    exact convex_upper_bound (q.convex_g i) (hx.2.2 i) (hy.2.2 i) hs ht hst
  have hfx : q.f x.1 = r := by simpa [slaterPerturbation, hx] using hxr
  have hfy : q.f y.1 = h := by simpa [slaterPerturbation, hy] using hyh
  change slaterPerturbation q (s • x.1 + t • y.1, s • x.2 + t • y.2) ≤ _
  rw [slaterPerturbation, if_pos ⟨hdom, hP, hg⟩]
  exact convex_upper_bound q.convex_f hfx.le hfy.le hs ht hst

lemma slaterPerturbation_zero (q : ConvexProgram X I A J) :
    marginal (slaterPerturbation q) 0 = convexProgramPrimalValue q := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro x
    have hx : x.val ∈ commonDomain q ∧ x.val ∈ affinePolyhedron q ∧
        ∀ i, q.g i x.val ≤ ((0 : I → ℝ) i : WithTop ℝ) := x.property
    have h := marginal_le_candidate (slaterPerturbation q) x.val 0
    rw [slaterPerturbation, if_pos hx] at h
    exact h
  · apply le_iInf
    intro x
    by_cases hx : x ∈ commonDomain q ∧ x ∈ affinePolyhedron q ∧ ∀ i, q.g i x ≤ 0
    · change (⨅ y : feasibleSet q, ConvexAnalysis.Specs.toEReal (q.f y)) ≤ _
      simp only [slaterPerturbation, Prod.fst, Prod.snd, Pi.zero_apply, WithTop.coe_zero, ite_eq_left hx]
      exact iInf_le (fun y : feasibleSet q => ConvexAnalysis.Specs.toEReal (q.f y)) ⟨x, hx⟩
    · simp only [slaterPerturbation, Prod.fst, Prod.snd, Pi.zero_apply, WithTop.coe_zero, ite_eq_right hx]
      exact le_top

/-- Enlarging the inequality right-hand sides can only lower the value. -/
lemma slaterPerturbation_antitone (q : ConvexProgram X I A J) :
    Antitone (marginal (slaterPerturbation q)) := by
  classical
  intro u v huv
  apply iInf_mono
  intro x
  by_cases hx : x ∈ commonDomain q ∧ x ∈ affinePolyhedron q ∧
      ∀ i, q.g i x ≤ (u i : WithTop ℝ)
  · have hv : x ∈ commonDomain q ∧ x ∈ affinePolyhedron q ∧
        ∀ i, q.g i x ≤ (v i : WithTop ℝ) :=
      ⟨hx.1, hx.2.1, fun i => (hx.2.2 i).trans (WithTop.coe_le_coe.mpr (huv i))⟩
    rw [slaterPerturbation, ite_eq_left hv, slaterPerturbation, ite_eq_left hx]
  · simp only [slaterPerturbation, ite_eq_right hx]
    exact le_top

/-- Strict feasibility supplies the convex-inequality multipliers. No
relative-interior assumption is needed in this first stage. -/
lemma exists_convex_inequality_multipliers (q : ConvexProgram X I A J) (p : ℝ)
    (hp : convexProgramPrimalValue q = (p : EReal)) (x₀ : X)
    (hxD : x₀ ∈ commonDomain q) (hxP : x₀ ∈ affinePolyhedron q)
    (hstrict : ∀ i, q.g i x₀ < 0) :
    ∃ lam : I → ℝ, (∀ i, 0 ≤ lam i) ∧
      ∀ x ∈ commonDomain q, x ∈ affinePolyhedron q →
        p ≤ (q.f x).untopD 0 + ∑ i, lam i * (q.g i x).untopD 0 := by
  classical
  let Φ := slaterPerturbation q
  obtain ⟨hfinite, hgfinite⟩ := commonDomain_finite q x₀ hxD
  have hzero : Φ (x₀, 0) = q.f x₀ := by
    have hcond : x₀ ∈ commonDomain q ∧ x₀ ∈ affinePolyhedron q ∧
        ∀ i, q.g i x₀ ≤ ((0 : I → ℝ) i : WithTop ℝ) :=
      ⟨hxD, hxP, fun i => (hstrict i).le⟩
    exact ite_eq_left hcond
  have hproper : Proper Φ := ⟨(x₀, 0), hzero ▸ hxD.1⟩
  let U : Set (I → ℝ) := {u | ∀ i, (q.g i x₀).untopD 0 < u i}
  have hopen : IsOpen U := by
    simpa only [U, setOf_forall] using
      (isOpen_iInter_of_finite (fun i : I =>
        isOpen_lt continuous_const (continuous_apply i)) :
        IsOpen (⋂ i, {u : I → ℝ | (q.g i x₀).untopD 0 < u i}))
  have hU : (0 : I → ℝ) ∈ U := by
    intro i
    have hi := hstrict i
    rw [hgfinite i] at hi
    exact WithTop.coe_lt_coe.mp hi
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hU)
  let M : ℝ := (q.f x₀).untopD 0
  have hM : ∀ u : I → ℝ, ‖u‖ < r → marginal Φ u ≤ (M : EReal) := by
    intro u hu
    have huU : u ∈ U := hball (by simpa using hu)
    have hcond : x₀ ∈ commonDomain q ∧ x₀ ∈ affinePolyhedron q ∧
        ∀ i, q.g i x₀ ≤ (u i : WithTop ℝ) := by
      refine ⟨hxD, hxP, fun i => ?_⟩
      rw [hgfinite i]
      exact WithTop.coe_le_coe.mpr (huU i).le
    have hh := marginal_le_candidate Φ x₀ u
    change marginal Φ u ≤ ConvexAnalysis.Specs.toEReal (slaterPerturbation q (x₀, u)) at hh
    rw [slaterPerturbation, ite_eq_left hcond, hfinite] at hh
    exact hh
  have h0 : marginal Φ 0 = (p : EReal) := (slaterPerturbation_zero q).trans hp
  obtain ⟨_, _, η, hη⟩ := local_value_support Φ hproper
    (slaterPerturbation_convex q) p r M h0 hr hM
  have hηneg (i : I) : η (Pi.single i 1) ≤ 0 := by
    have hpos : (0 : I → ℝ) ≤ Pi.single i 1 := by
      intro j
      simp only [Pi.zero_apply, Pi.single_apply]
      split_ifs <;> norm_num
    have hh := (hη (Pi.single i 1)).trans (slaterPerturbation_antitone q hpos)
    rw [h0] at hh
    have := EReal.coe_le_coe_iff.mp hh
    linarith
  have hrepr (u : I → ℝ) : η u = ∑ i, u i * η (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' u]
    simp only [map_sum, map_smul, smul_eq_mul]
  refine ⟨fun i => -η (Pi.single i 1), fun i => neg_nonneg.mpr (hηneg i), ?_⟩
  intro x hxD hxP
  obtain ⟨hf, hg⟩ := commonDomain_finite q x hxD
  let u : I → ℝ := fun i => (q.g i x).untopD 0
  have hcond : x ∈ commonDomain q ∧ x ∈ affinePolyhedron q ∧
      ∀ i, q.g i x ≤ (u i : WithTop ℝ) := ⟨hxD, hxP, fun i => (hg i).le⟩
  have hh := (hη u).trans (marginal_le_candidate Φ x u)
  change ((p + η u : ℝ) : EReal) ≤
    ConvexAnalysis.Specs.toEReal (slaterPerturbation q (x, u)) at hh
  rw [slaterPerturbation, ite_eq_left hcond, hf] at hh
  have hhreal := EReal.coe_le_coe_iff.mp hh
  rw [hrepr] at hhreal
  have hid : (∑ i, u i * η (Pi.single i 1)) =
      -(∑ i, -η (Pi.single i 1) * (q.g i x).untopD 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [u]
    ring
  rw [hid] at hhreal
  linarith

/-- Extend the partially penalized real objective by infinity outside D,
even when a multiplier is zero. -/
def penalizedObjective (q : ConvexProgram X I A J) (lam : I → ℝ) (x : X) : WithTop ℝ := by
  classical
  exact if x ∈ commonDomain q then
    (((q.f x).untopD 0 + ∑ i, lam i * (q.g i x).untopD 0 : ℝ) : WithTop ℝ) else ⊤

lemma penalizedObjective_domain (q : ConvexProgram X I A J) (lam : I → ℝ) :
    effectiveDomain (penalizedObjective q lam) = commonDomain q := by
  classical
  ext x
  change penalizedObjective q lam x < ⊤ ↔ x ∈ commonDomain q
  rw [penalizedObjective]
  split_ifs with hx
  · exact iff_of_true (WithTop.coe_lt_top _) hx
  · exact iff_of_false (lt_irrefl _) hx

lemma penalizedObjective_convex (q : ConvexProgram X I A J) (lam : I → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) : IsConvex (penalizedObjective q lam) := by
  classical
  have hf : ConvexOn ℝ (commonDomain q) (fun x => (q.f x).untopD 0) :=
    convexOn_untopD_comp q.convex_f (AffineMap.id ℝ X) (commonDomain_convex q)
      (fun x hx => hx.1)
  have hg (i : I) : ConvexOn ℝ (commonDomain q) (fun x => (q.g i x).untopD 0) :=
    convexOn_untopD_comp (q.convex_g i) (AffineMap.id ℝ X) (commonDomain_convex q)
      (fun x hx => hx.2 i)
  apply (convex_iff_twoPoint _).mpr
  intro x y r h hxr hyh s t hs ht hst
  have hx : x ∈ commonDomain q := by
    by_contra hn
    simp [penalizedObjective, hn] at hxr
  have hy : y ∈ commonDomain q := by
    by_contra hn
    simp [penalizedObjective, hn] at hyh
  have hz := commonDomain_convex q hx hy hs ht hst
  have hr : (q.f x).untopD 0 + ∑ i, lam i * (q.g i x).untopD 0 = r := by
    exact WithTop.coe_injective (by simpa [penalizedObjective, hx] using hxr)
  have hh : (q.f y).untopD 0 + ∑ i, lam i * (q.g i y).untopD 0 = h := by
    exact WithTop.coe_injective (by simpa [penalizedObjective, hy] using hyh)
  rw [penalizedObjective, ite_eq_left hz]
  apply WithTop.coe_le_coe.mpr
  have hff := hf.2 hx hy hs ht hst
  have hgg := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left ((hg i).2 hx hy hs ht hst) (hlam i))
  change (∑ i, lam i * (q.g i (s • x + t • y)).untopD 0) ≤
    ∑ i, lam i * (s * (q.g i x).untopD 0 + t * (q.g i y).untopD 0) at hgg
  have hsum : (∑ i, lam i * (s * (q.g i x).untopD 0 + t * (q.g i y).untopD 0)) =
      s * (∑ i, lam i * (q.g i x).untopD 0) +
      t * (∑ i, lam i * (q.g i y).untopD 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum] at hgg
  change (q.f (s • x + t • y)).untopD 0 ≤
    s * (q.f x).untopD 0 + t * (q.f y).untopD 0 at hff
  nlinarith

end Algebra

/-- Refined Slater dual attainment, including active affine inequalities,
empty index types, and a lower-dimensional common domain. -/
theorem refined_slater : Specs.refined_slater.{u,v,w,z} := by
  intro X _ _ _ _ _ _ _ I A J _ _ _ q p hp hwitness
  let : IsNormableSpace ℝ X := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup X := IsNormableSpace.toSeminormedAddCommGroup ℝ X
  let : NormedSpace ℝ X := IsNormableSpace.toNormedSpace ℝ X
  let : NormedAddCommGroup X := { MetricSpace.ofT0PseudoMetricSpace X with
    dist_eq := dist_eq_norm_neg_add }
  obtain ⟨x₀, hxri, hxP, hstrict⟩ := hwitness
  have hxD : x₀ ∈ commonDomain q := intrinsicInterior_subset hxri
  obtain ⟨lam, hlam, hbound⟩ :=
    exists_convex_inequality_multipliers q p hp x₀ hxD hxP hstrict
  let F := penalizedObjective q lam
  have hFdom : effectiveDomain F = commonDomain q := penalizedObjective_domain q lam
  have hFri : x₀ ∈ ConvexGeometry.relativeInterior (effectiveDomain F) := by
    rw [hFdom]
    exact hxri
  have hFval (x : X) (hx : x ∈ commonDomain q) :
      (F x).untopD 0 = (q.f x).untopD 0 + ∑ i, lam i * (q.g i x).untopD 0 := by
    change (penalizedObjective q lam x).untopD 0 = _
    rw [penalizedObjective, ite_eq_left hx, WithTop.untopD_coe]
  have hlower (x : X) (hx : (∀ i, q.a i x ≤ q.b i) ∧ (∀ j, q.e j x = q.d j))
      (r : ℝ) (hr : F x = (r : WithTop ℝ)) : p ≤ r := by
    have hxfin : x ∈ effectiveDomain F := by
      change F x < ⊤
      rw [hr]
      exact WithTop.coe_lt_top _
    rw [hFdom] at hxfin
    have hval := hFval x hxfin
    rw [hr, WithTop.untopD_coe] at hval
    rw [hval]
    exact hbound x hxfin hx
  obtain ⟨mu, nu, z₀, hmu, _, _, hfull⟩ :=
    affine_support_of_relativeInterior F (penalizedObjective_convex q lam hlam)
      q.a q.b q.e q.d x₀ hFri hxP p hlower
  let m : Multipliers I A J := ⟨lam, mu, nu⟩
  have hm : admissible m := ⟨hlam, hmu⟩
  have hdualLower : (p : EReal) ≤ dualFunction q m := by
    apply le_iInf
    intro x
    have hxd : x.val ∈ effectiveDomain F := by rw [hFdom]; exact x.property
    have hh := hfull x.val hxd
    rw [hFval x.val x.property] at hh
    exact EReal.coe_le_coe hh
  have heq : dualFunction q m = (p : EReal) :=
    le_antisymm ((weak_duality q m hm).trans_eq hp) hdualLower
  refine ⟨m, hm, heq, ?_⟩
  apply le_antisymm
  · exact (dualValue_le_primalValue q).trans_eq hp
  · rw [← heq]
    exact le_iSup (fun n : {n : Multipliers I A J // admissible n} => dualFunction q n.val) ⟨m, hm⟩

end VariationalNotes.Ch04
