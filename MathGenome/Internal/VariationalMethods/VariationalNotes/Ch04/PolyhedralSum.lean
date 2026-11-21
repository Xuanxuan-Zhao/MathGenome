import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.PolyhedralSum
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.PolyhedralSupport
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Subgradients
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeInteriorAffine

noncomputable section
open Set
open scoped Pointwise
universe u
namespace VariationalNotes.Ch04
open ConvexAnalysis ConvexGeometry

/-- At a finite minimum over a polyhedron, a normal absorbs the constraint.
The function need not be lower semicontinuous. -/
lemma polyhedral_support_at_minimum {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → WithTop ℝ) (hf : IsConvex f) (P : Set E) (hP : IsPolyhedron P)
    (hri : (relativeInterior (effectiveDomain f) ∩ P).Nonempty)
    (x : E) (hx : x ∈ P) (r : ℝ) (hr : f x = r)
    (hmin : ∀ z ∈ P, (r : WithTop ℝ) ≤ f z) :
    ∃ n : E →L[ℝ] ℝ, n ∈ normalCone P x ∧
      ∀ z ∈ effectiveDomain f, r ≤ (f z).untopD 0 + n (z - x) := by
  classical
  obtain ⟨s, hs⟩ := hP
  let a : s → E →ᵃ[ℝ] ℝ := fun i => i.val
  let b : s → ℝ := fun _ => 0
  let e : Fin 0 → E →ᵃ[ℝ] ℝ := fun i => Fin.elim0 i
  let d : Fin 0 → ℝ := fun i => Fin.elim0 i
  have hfeas (z : E) : z ∈ P ↔ (∀ i, a i z ≤ b i) ∧ (∀ j, e j z = d j) := by
    rw [hs]
    simp [a, b]
  obtain ⟨x₀, hx₀, hx₀P⟩ := hri
  obtain ⟨lam, nu, z₀, hlam, hz₀, hcomp, hbound⟩ :=
    affine_support_of_relativeInterior f hf a b e d x₀ hx₀ ((hfeas x₀).mp hx₀P) r
      (fun z hz t ht => WithTop.coe_le_coe.mp (ht ▸ hmin z ((hfeas z).mpr hz)))
  let n : E →L[ℝ] ℝ := (∑ i, lam i • (a i).linear).toContinuousLinearMap
  let R : E → ℝ := fun z => ∑ i, lam i * a i z
  have hR (z : E) : z ∈ P → R z ≤ 0 := by
    intro hz
    exact Finset.sum_nonpos fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (hlam i) (((hfeas z).mp hz).1 i)
  have hb (z : E) (hz : z ∈ effectiveDomain f) : r ≤ (f z).untopD 0 + R z := by
    simpa [b, e, d, R] using hbound z hz
  have hxdom : x ∈ effectiveDomain f := (mem_domain_iff f x).mpr ⟨r, hr⟩
  have hRx : R x = 0 := by
    have := hb x hxdom
    rw [hr, WithTop.untopD_coe] at this
    linarith [hR x hx]
  have hn (z : E) : n (z - x) = R z - R x := by
    simp only [n, LinearMap.coe_toContinuousLinearMap', LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, R, ← Finset.sum_sub_distrib, ← mul_sub]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun t => lam i * t) ((a i).linear_apply_vsub z x))
  refine ⟨n, ?_, ?_⟩
  · intro z hz
    rw [hn, hRx, sub_zero]
    exact hR z hz
  · intro z hz
    rw [hn, hRx, sub_zero]
    exact hb z hz

/-- Translating a finite height commutes with the extended-real order. -/
private lemma add_coe_le_coe_iff (v : WithTop ℝ) (a b : ℝ) :
    v + (a : WithTop ℝ) ≤ (b : WithTop ℝ) ↔ v ≤ ((b - a : ℝ) : WithTop ℝ) := by
  induction v using WithTop.recTopCoe with
  | top => simp
  | coe v => simp only [← WithTop.coe_add, WithTop.coe_le_coe]; constructor <;> intro h <;> linarith

lemma convex_linear_perturbation {E F : Type u} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : E → WithTop ℝ) (hf : IsConvex f)
    (A : F →ₗ[ℝ] E) (l : F →ₗ[ℝ] ℝ) :
    IsConvex (fun y => f (A y) + (l y : WithTop ℝ)) := by
  intro x hx y hy s t hs ht hst
  change f (A (s • x.1 + t • y.1)) + (l (s • x.1 + t • y.1) : WithTop ℝ) ≤
    ((s * x.2 + t * y.2 : ℝ) : WithTop ℝ)
  apply (add_coe_le_coe_iff _ _ _).mpr
  have hx' := (add_coe_le_coe_iff _ _ _).mp hx
  have hy' := (add_coe_le_coe_iff _ _ _).mp hy
  have hh := convex_upper_bound hf hx' hy' hs ht hst
  convert hh using 1 <;> simp only [map_add, map_smul, smul_eq_mul]
  congr 1
  ring

private lemma perturbed_domain {E F : Type u} (f : E → WithTop ℝ)
    (A : F → E) (l : F → ℝ) :
    effectiveDomain (fun y => f (A y) + (l y : WithTop ℝ)) = A ⁻¹' effectiveDomain f := by
  ext y
  change f (A y) + (l y : WithTop ℝ) < ⊤ ↔ f (A y) < ⊤
  induction f (A y) using WithTop.recTopCoe with
  | top => simp
  | coe r => simp [← WithTop.coe_add]

lemma subgradient_add {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (f g : E → WithTop ℝ) (x : E) :
    subdifferential f x + subdifferential g x ⊆ subdifferential (fun z => f z + g z) x := by
  rintro l ⟨a, ⟨r, hr, ha⟩, b, ⟨s, hs, hb⟩, rfl⟩
  refine ⟨r+s, by dsimp only; rw [hr, hs, WithTop.coe_add], ?_⟩
  intro z
  have h := add_le_add (ha z) (hb z)
  simpa only [← WithTop.coe_add, add_apply, add_add_add_comm] using h

lemma polyhedral_sum_normed {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f g : E → WithTop ℝ) (hf : IsConvex f) (_hg : IsConvex g)
    (hP : IsPolyhedron (epigraph g))
    (hri : (relativeInterior (effectiveDomain f) ∩ effectiveDomain g).Nonempty)
    (x : E) (hx : x ∈ effectiveDomain f ∩ effectiveDomain g) :
    subdifferential (fun z => f z + g z) x = subdifferential f x + subdifferential g x := by
  apply subset_antisymm _ (subgradient_add f g x)
  intro l hl
  obtain ⟨r, hr⟩ := (mem_domain_iff f x).mp hx.1
  obtain ⟨s, hs⟩ := (mem_domain_iff g x).mp hx.2
  have hsum : f x + g x = ((r+s : ℝ) : WithTop ℝ) := by rw [hr, hs, WithTop.coe_add]
  have hl' := (mem_subdifferential_iff (f := fun z => f z + g z) hsum l).mp hl
  let L : E × ℝ →ₗ[ℝ] ℝ := LinearMap.snd ℝ E ℝ - l.toLinearMap.comp (LinearMap.fst ℝ E ℝ)
  let F : E × ℝ → WithTop ℝ := fun y => f y.1 + (L y : WithTop ℝ)
  have hF : IsConvex F := convex_linear_perturbation f hf (LinearMap.fst ℝ E ℝ) L
  have hdom : effectiveDomain F = effectiveDomain f ×ˢ (univ : Set ℝ) := by
    rw [perturbed_domain]
    ext y
    simp only [mem_preimage, mem_prod, mem_univ, and_true]
  have hriF : (relativeInterior (effectiveDomain F) ∩ epigraph g).Nonempty := by
    obtain ⟨z, hz, hzg⟩ := hri
    obtain ⟨t, ht⟩ := (mem_domain_iff g z).mp hzg
    refine ⟨(z,t), ?_, ht.le⟩
    rw [hdom]
    change (z,t) ∈ intrinsicInterior ℝ (effectiveDomain f ×ˢ (univ : Set ℝ))
    rw [intrinsicInterior_prod_eq]
    exact ⟨hz, interior_subset_intrinsicInterior (by simp)⟩
  have hFx : F (x,s) = ((r - l x + s : ℝ) : WithTop ℝ) := by
    change f x + ((s - l x : ℝ) : WithTop ℝ) = ((r - l x + s : ℝ) : WithTop ℝ)
    rw [hr, ← WithTop.coe_add]
    congr 1
    ring
  have hmin : ∀ y ∈ epigraph g, ((r - l x + s : ℝ) : WithTop ℝ) ≤ F y := by
    rintro ⟨z,t⟩ hzt
    induction hfz : f z using WithTop.recTopCoe with
    | top => simp [F, hfz]
    | coe q =>
      obtain ⟨v, hv, hvt⟩ := WithTop.le_coe_iff.mp hzt
      have hh := hl' z
      rw [hfz, hv, ← WithTop.coe_add] at hh
      have hh' := WithTop.coe_le_coe.mp hh
      rw [map_sub] at hh'
      change ((r - l x + s : ℝ) : WithTop ℝ) ≤ f z + ((t - l z : ℝ) : WithTop ℝ)
      rw [hfz, ← WithTop.coe_add, WithTop.coe_le_coe]
      linarith
  obtain ⟨n, hnP, hn⟩ := polyhedral_support_at_minimum F hF (epigraph g) hP hriF
    (x,s) hs.le (r - l x + s) hFx hmin
  let a : E →L[ℝ] ℝ := n.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let beta : ℝ := n (0,1)
  have hn_eq (z : E) (t : ℝ) : n (z,t) = a z + t * beta := by
    have heq : (z,t) = (z,(0:ℝ)) + t • ((0:E),(1:ℝ)) := by simp
    rw [heq, map_add, map_smul]
    rfl
  have hbound (z : E) (hz : z ∈ effectiveDomain f) (t : ℝ) :
      r - l x + s ≤ (f z).untopD 0 + (t - l z) + a (z-x) + (t-s)*beta := by
    have hh := hn (z,t) (by rw [hdom]; exact ⟨hz, mem_univ _⟩)
    obtain ⟨q,hq⟩ := (mem_domain_iff f z).mp hz
    have hFt : F (z,t) = ((q + (t - l z) : ℝ) : WithTop ℝ) := by
      change f z + ((t - l z : ℝ) : WithTop ℝ) = _
      rw [hq, WithTop.coe_add]
    rw [hFt, WithTop.untopD_coe] at hh
    change r - l x + s ≤ q + (t - l z) + n (z-x,t-s) at hh
    rw [hn_eq] at hh
    simpa only [hq, WithTop.untopD_coe, add_assoc] using hh
  have hbeta : beta = -1 := by
    have hp := hbound x hx.1 (s+1)
    have hm := hbound x hx.1 (s-1)
    simp only [hr, WithTop.untopD_coe, sub_self, map_zero] at hp hm
    nlinarith
  have ha : a ∈ subdifferential g x := by
    apply (mem_subdifferential_iff hs a).mpr
    intro z
    induction hgz : g z using WithTop.recTopCoe with
    | top => exact le_top
    | coe t =>
      have hh := hnP (z,t) (show (z,t) ∈ epigraph g from hgz.le)
      change n (z-x,t-s) ≤ 0 at hh
      rw [hn_eq, hbeta] at hh
      apply WithTop.coe_le_coe.mpr
      linarith
  have hb : l-a ∈ subdifferential f x := by
    apply (mem_subdifferential_iff hr (l-a)).mpr
    intro z
    induction hfz : f z using WithTop.recTopCoe with
    | top => exact le_top
    | coe q =>
      have hz : z ∈ effectiveDomain f := (mem_domain_iff f z).mpr ⟨q,hfz⟩
      have hh := hbound z hz s
      rw [hfz, WithTop.untopD_coe, hbeta] at hh
      apply WithTop.coe_le_coe.mpr
      simp only [sub_apply, map_sub]
      rw [map_sub] at hh
      linarith
  exact ⟨l-a, hb, a, ha, sub_add_cancel l a⟩

/-- The sum rule in the original finite-dimensional vector topology. -/
theorem polyhedral_sum : Specs.polyhedral_sum.{u} := by
  intro E _ _ _ _ _ _ _ f g _hfproper hf _hgproper hg hP hri x hx
  let : IsNormableSpace ℝ E := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup E := IsNormableSpace.toSeminormedAddCommGroup ℝ E
  let : NormedSpace ℝ E := IsNormableSpace.toNormedSpace ℝ E
  let : NormedAddCommGroup E := { MetricSpace.ofT0PseudoMetricSpace E with
    dist_eq := dist_eq_norm_neg_add }
  exact polyhedral_sum_normed f g hf hg hP hri x hx

lemma indicator_epigraph {E : Type u} (C : Set E) :
    epigraph (ConvexAnalysis.indicator C) = C ×ˢ Ici (0 : ℝ) := by
  classical
  ext p
  by_cases hp : p.1 ∈ C
  · simp [epigraph, ConvexAnalysis.Specs.epigraph, ConvexAnalysis.indicator,
      ConvexAnalysis.Specs.indicator, hp, ← WithTop.coe_zero, WithTop.coe_le_coe]
  · simp [epigraph, ConvexAnalysis.Specs.epigraph, ConvexAnalysis.indicator,
      ConvexAnalysis.Specs.indicator, hp]

lemma convex_indicator {E : Type u} [AddCommGroup E] [Module ℝ E]
    (C : Set E) (hC : Convex ℝ C) : IsConvex (ConvexAnalysis.indicator C) := by
  change Convex ℝ (epigraph (ConvexAnalysis.indicator C))
  rw [indicator_epigraph]
  exact hC.prod (convex_Ici 0)

lemma indicator_domain {E : Type u} (C : Set E) : effectiveDomain (ConvexAnalysis.indicator C) = C := by
  classical
  ext x
  by_cases hx : x ∈ C <;>
    simp [effectiveDomain, ConvexAnalysis.Specs.effectiveDomain, ConvexAnalysis.indicator,
      ConvexAnalysis.Specs.indicator, hx]

lemma polyhedron_convex {E : Type u} [AddCommGroup E] [Module ℝ E]
    (P : Set E) (hP : IsPolyhedron P) : Convex ℝ P := by
  obtain ⟨s, rfl⟩ := hP
  intro x hx y hy a b ha hb hab q hq
  rw [Convex.combo_affine_apply hab]
  change a * q x + b * q y ≤ 0
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hx q hq))
    (mul_nonpos_of_nonneg_of_nonpos hb (hy q hq))

lemma polyhedron_indicator_epigraph {E : Type u} [AddCommGroup E] [Module ℝ E]
    (D : Set E) (hD : IsPolyhedron D) : IsPolyhedron (epigraph (ConvexAnalysis.indicator D)) := by
  classical
  let a : E × ℝ →ᵃ[ℝ] ℝ := -(AffineMap.snd : E × ℝ →ᵃ[ℝ] ℝ)
  have hhalf : IsPolyhedron {y : E × ℝ | 0 ≤ y.2} := by
    refine ⟨{a}, ?_⟩
    ext y
    simp [a]
  have h := polyhedron_inter
    (polyhedron_affine_preimage (AffineMap.fst : E × ℝ →ᵃ[ℝ] E) D hD) hhalf
  rw [indicator_epigraph]
  exact h

/-- Indicators specialize the one-polyhedral-summand rule to normals. -/
theorem polyhedral_normal_intersection : Specs.polyhedral_normal_intersection.{u} := by
  intro E _ _ _ _ _ _ _ C D hC hD hri x hx
  have hDC : Convex ℝ D := polyhedron_convex D hD
  have hsum : subdifferential (fun z => ConvexAnalysis.indicator C z + ConvexAnalysis.indicator D z) x =
      subdifferential (ConvexAnalysis.indicator C) x + subdifferential (ConvexAnalysis.indicator D) x := by
    apply polyhedral_sum (ConvexAnalysis.indicator C) (ConvexAnalysis.indicator D)
    · exact (indicator_values C).2.2.mpr ⟨x,hx.1⟩
    · exact convex_indicator C hC
    · exact (indicator_values D).2.2.mpr ⟨x,hx.2⟩
    · exact convex_indicator D hDC
    · exact polyhedron_indicator_epigraph D hD
    · change (relativeInterior (effectiveDomain (ConvexAnalysis.indicator C)) ∩
        effectiveDomain (ConvexAnalysis.indicator D)).Nonempty
      rw [indicator_domain, indicator_domain]
      exact hri
    · change x ∈ effectiveDomain (ConvexAnalysis.indicator C) ∩
        effectiveDomain (ConvexAnalysis.indicator D)
      rw [indicator_domain, indicator_domain]
      exact hx
  have hind : (fun z => ConvexAnalysis.indicator C z + ConvexAnalysis.indicator D z) = ConvexAnalysis.indicator (C ∩ D) := by
    classical
    funext z
    by_cases hc : z ∈ C <;> by_cases hd : z ∈ D <;>
      simp [ConvexAnalysis.indicator, ConvexAnalysis.Specs.indicator, hc, hd]
  rw [hind] at hsum
  change ConvexAnalysis.Specs.subdifferential (ConvexAnalysis.Specs.indicator (C ∩ D)) x =
    ConvexAnalysis.Specs.subdifferential (ConvexAnalysis.Specs.indicator C) x +
    ConvexAnalysis.Specs.subdifferential (ConvexAnalysis.Specs.indicator D) x at hsum
  rw [subdifferential_indicator (C ∩ D) ⟨x,hx⟩ (hC.inter hDC) x hx,
    subdifferential_indicator C ⟨x,hx.1⟩ hC x hx.1,
    subdifferential_indicator D ⟨x,hx.2⟩ hDC x hx.2] at hsum
  exact hsum

end VariationalNotes.Ch04
