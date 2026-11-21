import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.PolyhedralSupport
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.LocalLipschitz
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Separation
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.FiniteConesFarkas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Order.Monotone

noncomputable section
open Set Filter Topology
universe u v w
namespace VariationalNotes.Ch04
open ConvexAnalysis ConvexGeometry

/-- A finite family of affine inequalities and equalities defines a polyhedron. -/
lemma affine_constraints_polyhedron {E : Type u} [AddCommGroup E] [Module ℝ E]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (a : I → E →ᵃ[ℝ] ℝ) (b : I → ℝ)
    (e : J → E →ᵃ[ℝ] ℝ) (d : J → ℝ) :
    IsPolyhedron {x | (∀ i, a i x ≤ b i) ∧ (∀ j, e j x = d j)} := by
  classical
  let rows : I ⊕ (J ⊕ J) → E →ᵃ[ℝ] ℝ :=
    Sum.elim (fun i => a i - AffineMap.const ℝ E (b i))
      (Sum.elim (fun j => e j - AffineMap.const ℝ E (d j))
        (fun j => -e j + AffineMap.const ℝ E (d j)))
  refine ⟨Finset.univ.image rows, ?_⟩
  ext x
  change _ ↔ ∀ r ∈ Finset.univ.image rows, r x ≤ 0
  simp only [Finset.forall_mem_image, Finset.mem_univ, forall_const]
  simp only [Sum.forall, rows, Sum.elim_inl, Sum.elim_inr, AffineMap.coe_sub,
    AffineMap.coe_add, AffineMap.coe_neg, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
    AffineMap.const_apply, sub_nonpos]
  constructor
  · rintro ⟨hi, hj⟩
    exact ⟨hi, (fun j => (hj j).le), fun j => by linarith [hj j]⟩
  · rintro ⟨hi, hj, hk⟩
    exact ⟨hi, fun j => by linarith [hj j, hk j]⟩

/-- A bounded-above real affine image of a nonempty polyhedron attains its maximum. -/
lemma polyhedron_attains_maximum {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {P : Set E}
    (hP : IsPolyhedron P) (hne : P.Nonempty) (q : E →ᵃ[ℝ] ℝ)
    (hb : BddAbove (q '' P)) : ∃ z ∈ P, ∀ x ∈ P, q x ≤ q z := by
  have hclosed : IsClosed (q '' P) := polyhedron_affine_image_isClosed q P hP
  obtain ⟨z, hz, hqz⟩ := hclosed.csSup_mem (hne.image q) hb
  refine ⟨z, hz, fun x hx => ?_⟩
  rw [hqz]
  exact le_csSup hb (mem_image_of_mem q hx)

/-- Finite conic duality in the continuous dual, with no chosen inner product. -/
lemma dual_mem_finite_conicHull {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Type v} [Fintype K] (g : K → E →L[ℝ] ℝ) (q : E →L[ℝ] ℝ)
    (h : ∀ x : E, (∀ k, g k x ≤ 0) → q x ≤ 0) :
    q ∈ ConvexGeometry.Specs.conicHull (range g) := by
  let C : ProperCone ℝ (E →L[ℝ] ℝ) :=
    ⟨PointedCone.hull ℝ (range g), finite_conicHull_isClosed g⟩
  by_contra hq
  obtain ⟨l, hl, hlq⟩ := C.hyperplane_separation_point hq
  let phi : Module.Dual ℝ (Module.Dual ℝ E) :=
    l.toLinearMap.comp (LinearMap.toContinuousLinearMap :
      (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap
  let x : E := -(Module.evalEquiv ℝ E).symm phi
  have heval (r : E →L[ℝ] ℝ) : r x = -l r := by
    change r (-(Module.evalEquiv ℝ E).symm phi) = _
    rw [map_neg]
    congr 1
    exact Module.apply_evalEquiv_symm_apply ℝ E r.toLinearMap phi
  have hx : ∀ k, g k x ≤ 0 := by
    intro k
    rw [heval]
    exact neg_nonpos.mpr (hl _ (PointedCone.subset_hull (mem_range_self k)))
  have := h x hx
  rw [heval] at this
  linarith

/-- At a maximum over affine constraints the objective is a nonnegative
combination of active inequality rows and a free combination of equality rows.
The coefficients are extended by zero on inactive inequalities. -/
lemma affine_maximum_multipliers {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (a : I → E →ᵃ[ℝ] ℝ) (b : I → ℝ)
    (e : J → E →ᵃ[ℝ] ℝ) (d : J → ℝ) (q : E →ₗ[ℝ] ℝ) (z : E)
    (hz : (∀ i, a i z ≤ b i) ∧ (∀ j, e j z = d j))
    (hmax : ∀ x, ((∀ i, a i x ≤ b i) ∧ (∀ j, e j x = d j)) → q x ≤ q z) :
    ∃ (lam : I → ℝ) (nu : J → ℝ), (∀ i, 0 ≤ lam i) ∧
      (∀ i, lam i * (a i z - b i) = 0) ∧
      q = (∑ i, lam i • (a i).linear) + ∑ j, nu j • (e j).linear := by
  classical
  let A := {i // a i z = b i}
  let g : A ⊕ (J ⊕ J) → E →L[ℝ] ℝ :=
    Sum.elim (fun i => (a i.val).linear.toContinuousLinearMap)
      (Sum.elim (fun j => (e j).linear.toContinuousLinearMap)
        (fun j => -(e j).linear.toContinuousLinearMap))
  have hdir (v : E) (hv : ∀ k, g k v ≤ 0) : q v ≤ 0 := by
    have hi : ∀ i, a i z = b i → (a i).linear v ≤ 0 :=
      fun i hi => hv (Sum.inl ⟨i, hi⟩)
    have hj (j) : (e j).linear v = 0 := by
      have hp := hv (Sum.inr (Sum.inl j))
      have hn := hv (Sum.inr (Sum.inr j))
      change (e j).linear v ≤ 0 at hp
      change -(e j).linear v ≤ 0 at hn
      linarith
    have hsmall : ∀ i, ∀ᶠ t : ℝ in 𝓝 0,
        0 ≤ t → a i (t • v + z) ≤ b i := by
      intro i
      by_cases hia : a i z = b i
      · exact Filter.Eventually.of_forall fun t ht => by
          rw [show t • v + z = t • v +ᵥ z from rfl, (a i).map_vadd]
          simp only [map_smul, smul_eq_mul, vadd_eq_add]
          nlinarith [hi i hia]
      · have hc : ContinuousAt (fun t : ℝ => a i (t • v + z)) 0 :=
          (a i).continuous_of_finiteDimensional.continuousAt.comp
            ((continuous_id.smul continuous_const).add continuous_const).continuousAt
        have hlt : a i ((0 : ℝ) • v + z) < b i := by
          simpa using lt_of_le_of_ne (hz.1 i) hia
        filter_upwards [hc.eventually (gt_mem_nhds hlt)] with t ht
        exact fun _ => ht.le
    obtain ⟨t, ht, htmem⟩ := (eventually_all.mpr hsmall).exists_gt
    have hfeas : (∀ i, a i (t • v + z) ≤ b i) ∧
        (∀ j, e j (t • v + z) = d j) := by
      refine ⟨fun i => htmem i ht.le, fun j => ?_⟩
      rw [show t • v + z = t • v +ᵥ z from rfl, (e j).map_vadd]
      simp [hj j, hz.2 j]
    have h := hmax (t • v + z) hfeas
    simp only [map_add, map_smul, smul_eq_mul] at h
    exact nonpos_of_mul_nonpos_right (by linarith : t * q v ≤ 0) ht
  have hq : q.toContinuousLinearMap ∈ ConvexGeometry.Specs.conicHull (range g) :=
    dual_mem_finite_conicHull g q.toContinuousLinearMap hdir
  rw [finite_conicHull_eq g] at hq
  obtain ⟨c, hc, hsum⟩ := hq
  let lam : I → ℝ := fun i => if h : a i z = b i then c (Sum.inl ⟨i, h⟩) else 0
  let nu : J → ℝ := fun j => c (Sum.inr (Sum.inl j)) - c (Sum.inr (Sum.inr j))
  refine ⟨lam, nu, ?_, ?_, ?_⟩
  · intro i
    dsimp [lam]
    split
    · exact hc _
    · exact le_rfl
  · intro i
    dsimp [lam]
    split <;> simp_all
  · have hactive : (∑ i, lam i • (a i).linear) =
        ∑ i : A, c (Sum.inl i) • (a i.val).linear := by
      have hp (i : A) : lam i.val = c (Sum.inl i) := dite_eq_left i.property
      have hn (i : {i // ¬ a i z = b i}) : lam i.val = 0 := dite_eq_right i.property
      simpa only [hp, hn, zero_smul, Finset.sum_const_zero, add_zero] using
        (Fintype.sum_subtype_add_sum_subtype (fun i => a i z = b i)
          (fun i => lam i • (a i).linear)).symm
    rw [hactive]
    ext x
    have hx := congrArg (fun r : E →L[ℝ] ℝ => r x) hsum
    simp [Fintype.sum_sum_type, g, nu, sub_mul, smul_neg,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      sum_apply, LinearMap.sum_apply] at hx ⊢
    linarith

/-- Separation in a vector space whose domain has interior. Only a lower
bound over `P` is used; neither a minimizer nor closedness of `f` is needed. -/
lemma supporting_functional_on_domain {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → WithTop ℝ) (hf : IsConvex f) (P : Set E) (hP : Convex ℝ P)
    (x₀ : E) (hx₀ : x₀ ∈ interior (effectiveDomain f)) (hxP : x₀ ∈ P)
    (p : ℝ) (hp : ∀ x ∈ P, ∀ r : ℝ, f x = r → p ≤ r) :
    ∃ q : E →ₗ[ℝ] ℝ, ∀ x ∈ effectiveDomain f, ∀ z ∈ P,
      p + q z ≤ (f x).untopD 0 + q x := by
  let F : E → ℝ := fun x => (f x).untopD 0
  have hconv : ConvexOn ℝ (effectiveDomain f) F :=
    convexOn_untopD_comp hf (AffineMap.id ℝ E) (convex_effectiveDomain hf) (fun _ hx => hx)
  have hcont : ContinuousAt F x₀ :=
    hconv.continuousOn_interior.continuousAt (isOpen_interior.mem_nhds hx₀)
  let M : ℝ := F x₀ + 1
  have hbound : ∀ᶠ x in 𝓝 x₀, f x ≤ (M : WithTop ℝ) := by
    filter_upwards [hcont.eventually (gt_mem_nhds (show F x₀ < M by dsimp [M]; linarith)),
      isOpen_interior.mem_nhds hx₀] with x hx hxdom
    obtain ⟨r, hr⟩ := (mem_domain_iff f x).mp (interior_subset hxdom)
    have hfr : F x = r := by simp [F, hr]
    rw [hr, WithTop.coe_le_coe]
    exact (hfr ▸ hx).le
  let A : Set (E × ℝ) := epigraph f
  let B : Set (E × ℝ) := P ×ˢ Iio p
  have hA : Convex ℝ A := hf
  have hB : Convex ℝ B := hP.prod (convex_Iio p)
  have hint : (x₀, M + 1) ∈ interior A := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (prod_mem_nhds hbound (Ioi_mem_nhds (show M < M + 1 by linarith)))
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    change f x ≤ (t : WithTop ℝ)
    exact (show f x ≤ (M : WithTop ℝ) from hx).trans (WithTop.coe_le_coe.mpr ht.le)
  have hdis : Disjoint (interior A) B := by
    apply Set.disjoint_left.mpr
    rintro ⟨x, t⟩ hx ⟨hxP, htp⟩
    have hmem : (x, t) ∈ A := interior_subset hx
    obtain ⟨r, hr, hrt⟩ := WithTop.le_coe_iff.mp (show f x ≤ (t : WithTop ℝ) from hmem)
    have := hp x hxP r hr
    change t < p at htp
    linarith
  obtain ⟨g, c, hgA, hgB⟩ :=
    geometric_hahn_banach_open hA.interior isOpen_interior hB hdis
  have hgA' : ∀ z ∈ A, g z ≤ c := by
    intro z hz
    apply closure_minimal (fun y hy => (hgA y hy).le) (isClosed_Iic.preimage g.continuous)
    rw [hA.closure_interior_eq_closure_of_nonempty_interior ⟨_, hint⟩]
    exact subset_closure hz
  let l : E →L[ℝ] ℝ := g.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let beta : ℝ := g (0, 1)
  have g_eq (x : E) (t : ℝ) : g (x, t) = l x + t * beta := by
    have heq : (x, t) = (x, (0 : ℝ)) + t • ((0 : E), (1 : ℝ)) := by simp
    rw [heq, map_add, map_smul]
    rfl
  have hbeta : beta < 0 := by
    let s : ℝ := min p (M + 1) - 1
    have hs : s < p := by dsimp [s]; linarith [min_le_left p (M + 1)]
    have hst : s < M + 1 := by dsimp [s]; linarith [min_le_right p (M + 1)]
    have hu := hgA (x₀, M + 1) hint
    have hv := hgB (x₀, s) ⟨hxP, hs⟩
    rw [g_eq] at hu hv
    by_contra hn
    have hh := mul_le_mul_of_nonneg_right hst.le (le_of_not_gt hn)
    linarith
  have hgB' (z : E) (hz : z ∈ P) : c ≤ l z + p * beta := by
    apply ge_of_tendsto
      (((continuous_const.add (continuous_id.mul continuous_const)).continuousAt :
        ContinuousAt (fun s : ℝ => l z + s * beta) p).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio p)))
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa [g_eq] using hgB (z, s) ⟨hz, hs⟩
  let q : E →ₗ[ℝ] ℝ := beta⁻¹ • l.toLinearMap
  have hq (x : E) : q x = l x / beta := by
    simp only [q, LinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul, div_eq_mul_inv]
    ring
  refine ⟨q, ?_⟩
  intro x hx z hz
  obtain ⟨r, hr⟩ := (mem_domain_iff f x).mp hx
  have ha := hgA' (x, r) (by exact hr.le)
  have hb := hgB' z hz
  rw [g_eq] at ha
  have hd : p - r ≤ (l x - l z) / beta :=
    (le_div_iff_of_neg hbeta).mpr (by nlinarith)
  rw [sub_div, ← hq x, ← hq z] at hd
  simp only [hr, WithTop.untopD_coe]
  linarith

lemma affine_constraints_convex {E : Type u} [AddCommGroup E] [Module ℝ E]
    {I : Type v} {J : Type w} (a : I → E →ᵃ[ℝ] ℝ) (b : I → ℝ)
    (e : J → E →ᵃ[ℝ] ℝ) (d : J → ℝ) :
    Convex ℝ {x | (∀ i, a i x ≤ b i) ∧ (∀ j, e j x = d j)} := by
  intro x hx y hy s t hs ht hst
  constructor
  · intro i
    rw [Convex.combo_affine_apply hst]
    change s * a i x + t * a i y ≤ b i
    calc
      _ ≤ s * b i + t * b i := add_le_add
        (mul_le_mul_of_nonneg_left (hx.1 i) hs) (mul_le_mul_of_nonneg_left (hy.1 i) ht)
      _ = b i := by rw [← add_mul, hst, one_mul]
  · intro j
    rw [Convex.combo_affine_apply hst]
    change s * e j x + t * e j y = d j
    rw [hx.2 j, hy.2 j, ← add_mul, hst, one_mul]

/-- The supporting inequality with affine rows when the common point is
in the ambient interior of the effective domain. -/
lemma affine_support_of_interior {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (f : E → WithTop ℝ) (hf : IsConvex f)
    (a : I → E →ᵃ[ℝ] ℝ) (b : I → ℝ)
    (e : J → E →ᵃ[ℝ] ℝ) (d : J → ℝ) (x₀ : E)
    (hx₀ : x₀ ∈ interior (effectiveDomain f))
    (hxP : (∀ i, a i x₀ ≤ b i) ∧ (∀ j, e j x₀ = d j))
    (p : ℝ) (hp : ∀ x, ((∀ i, a i x ≤ b i) ∧ (∀ j, e j x = d j)) →
      ∀ r : ℝ, f x = r → p ≤ r) :
    ∃ (lam : I → ℝ) (nu : J → ℝ) (z : E), (∀ i, 0 ≤ lam i) ∧
      ((∀ i, a i z ≤ b i) ∧ (∀ j, e j z = d j)) ∧
      (∀ i, lam i * (a i z - b i) = 0) ∧
      (∀ x ∈ effectiveDomain f, p ≤ (f x).untopD 0 +
        (∑ i, lam i * (a i x - b i)) + ∑ j, nu j * (e j x - d j)) := by
  let P : Set E := {x | (∀ i, a i x ≤ b i) ∧ (∀ j, e j x = d j)}
  obtain ⟨q, hq⟩ := supporting_functional_on_domain f hf P
    (affine_constraints_convex a b e d) x₀ hx₀ hxP p hp
  have hb : BddAbove (q '' P) := by
    refine ⟨(f x₀).untopD 0 + q x₀ - p, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    linarith [hq x₀ (interior_subset hx₀) z hz]
  obtain ⟨z, hz, hzmax⟩ := polyhedron_attains_maximum
    (affine_constraints_polyhedron a b e d) ⟨x₀, hxP⟩ q.toAffineMap hb
  obtain ⟨lam, nu, hlam, hcomp, heq⟩ := affine_maximum_multipliers
    a b e d q z hz hzmax
  refine ⟨lam, nu, z, hlam, hz, hcomp, ?_⟩
  intro x hx
  have hid : q x - q z = (∑ i, lam i * (a i x - b i)) +
      ∑ j, nu j * (e j x - d j) := by
    rw [← map_sub, heq]
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [show (a i).linear (x - z) = a i x - a i z from (a i).linear_apply_vsub x z]
      nlinarith [hcomp i]
    · apply Finset.sum_congr rfl
      intro j _
      rw [show (e j).linear (x - z) = e j x - e j z from (e j).linear_apply_vsub x z, hz.2 j]
  have hh := hq x hx z hz
  linarith

/-- Work in the direction space of the affine hull, then keep the same
coefficients on the ambient affine rows. This includes a singleton hull. -/
lemma affine_support_of_relativeInterior {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (f : E → WithTop ℝ) (hf : IsConvex f)
    (a : I → E →ᵃ[ℝ] ℝ) (b : I → ℝ)
    (e : J → E →ᵃ[ℝ] ℝ) (d : J → ℝ) (x₀ : E)
    (hx₀ : x₀ ∈ relativeInterior (effectiveDomain f))
    (hxP : (∀ i, a i x₀ ≤ b i) ∧ (∀ j, e j x₀ = d j))
    (p : ℝ) (hp : ∀ x, ((∀ i, a i x ≤ b i) ∧ (∀ j, e j x = d j)) →
      ∀ r : ℝ, f x = r → p ≤ r) :
    ∃ (lam : I → ℝ) (nu : J → ℝ) (z : E), (∀ i, 0 ≤ lam i) ∧
      ((∀ i, a i z ≤ b i) ∧ (∀ j, e j z = d j)) ∧
      (∀ i, lam i * (a i z - b i) = 0) ∧
      (∀ x ∈ effectiveDomain f, p ≤ (f x).untopD 0 +
        (∑ i, lam i * (a i x - b i)) + ∑ j, nu j * (e j x - d j)) := by
  obtain ⟨xA, hxA, hxAval⟩ := mem_intrinsicInterior.mp hx₀
  let A := affineSpan ℝ (effectiveDomain f)
  let : Nonempty A := ⟨xA⟩
  let c : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ xA
  let chart : A.direction →ᵃ[ℝ] E := A.subtype.comp c.toAffineEquiv.toAffineMap
  let f' : A.direction → WithTop ℝ := fun y => f (chart y)
  let a' : I → A.direction →ᵃ[ℝ] ℝ := fun i => (a i).comp chart
  let e' : J → A.direction →ᵃ[ℝ] ℝ := fun j => (e j).comp chart
  let y₀ : A.direction := c.symm xA
  have chart_symm (x : A) : chart (c.symm x) = (x : E) := by
    simp only [chart, AffineMap.comp_apply, AffineEquiv.coe_toAffineMap,
      AffineIsometryEquiv.coe_toAffineEquiv, AffineIsometryEquiv.apply_symm_apply,
      AffineSubspace.subtype_apply]
  have hchart₀ : chart y₀ = x₀ := (chart_symm xA).trans hxAval
  have hf' : IsConvex f' := by
    intro y hy z hz s t hs ht hst
    change f (chart (s • y.1 + t • z.1)) ≤ ((s * y.2 + t * z.2 : ℝ) : WithTop ℝ)
    rw [Convex.combo_affine_apply hst]
    exact convex_upper_bound hf hy hz hs ht hst
  have hy₀ : y₀ ∈ interior (effectiveDomain f') := by
    let D : Set A := (Subtype.val : A → E) ⁻¹' effectiveDomain f
    have hpre : y₀ ∈ c.toHomeomorph ⁻¹' interior D := by
      change c (c.symm xA) ∈ interior D
      rw [c.apply_symm_apply]
      exact hxA
    rw [c.toHomeomorph.preimage_interior D] at hpre
    exact hpre
  have hyP : (∀ i, a' i y₀ ≤ b i) ∧ (∀ j, e' j y₀ = d j) := by
    simpa only [a', e', AffineMap.comp_apply, hchart₀] using hxP
  have hp' : ∀ y, ((∀ i, a' i y ≤ b i) ∧ (∀ j, e' j y = d j)) →
      ∀ r : ℝ, f' y = r → p ≤ r := by
    intro y hy r hr
    exact hp (chart y) hy r hr
  obtain ⟨lam, nu, z, hlam, hz, hcomp, hres⟩ :=
    affine_support_of_interior f' hf' a' b e' d y₀ hy₀ hyP p hp'
  refine ⟨lam, nu, chart z, hlam, hz, hcomp, ?_⟩
  intro x hx
  let x' : A := ⟨x, subset_affineSpan ℝ _ hx⟩
  have hchart : chart (c.symm x') = x := chart_symm x'
  have hx' : c.symm x' ∈ effectiveDomain f' := by
    change f (chart (c.symm x')) < ⊤
    rw [hchart]
    exact hx
  simpa only [f', a', e', AffineMap.comp_apply, hchart] using hres (c.symm x') hx'

/-- The manuscript's multiplier inequality, with the finite attained maximum
and its exact constraint-value formula. -/
theorem polyhedral_support : Specs.polyhedral_support.{u,v,w} := by
  intro E _ _ _ _ _ _ _ I J _ _ f a b e d _hproper hf
  -- Finite-dimensional Hausdorff vector topologies admit a compatible norm.
  let : IsNormableSpace ℝ E := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup E := IsNormableSpace.toSeminormedAddCommGroup ℝ E
  let : NormedSpace ℝ E := IsNormableSpace.toNormedSpace ℝ E
  let : NormedAddCommGroup E := { MetricSpace.ofT0PseudoMetricSpace E with
    dist_eq := dist_eq_norm_neg_add }
  dsimp only
  intro hri p hp
  let P : Set E := {x | (∀ i, a i x ≤ b i) ∧ (∀ j, e j x = d j)}
  obtain ⟨x₀, hx₀, hxP⟩ := hri
  have hbound (x : E) (hx : x ∈ P) (r : ℝ) (hr : f x = r) : p ≤ r := by
    have h := iInf_le (fun y : P => ConvexAnalysis.Specs.toEReal (f y.val)) ⟨x, hx⟩
    rw [hp, hr] at h
    exact EReal.coe_le_coe_iff.mp h
  obtain ⟨lam, nu, z, hlam, hz, hcomp, hres⟩ :=
    affine_support_of_relativeInterior f hf (fun i => (a i).toAffineMap) b
      (fun j => (e j).toAffineMap) d x₀ hx₀ hxP p hbound
  change (∀ i, a i z ≤ b i) ∧ (∀ j, e j z = d j) at hz
  change ∀ i, lam i * (a i z - b i) = 0 at hcomp
  change ∀ x ∈ effectiveDomain f, p ≤ (f x).untopD 0 +
    (∑ i, lam i * (a i x - b i)) + ∑ j, nu j * (e j x - d j) at hres
  let n : E →ₗ[ℝ] ℝ := (∑ i, lam i • a i) + ∑ j, nu j • e j
  let M : ℝ := (∑ i, lam i * b i) + ∑ j, nu j * d j
  have hn (x : E) : n x = (∑ i, lam i * a i x) + ∑ j, nu j * e j x := by
    simp [n, LinearMap.sum_apply]
  have hidentity (x : E) : (∑ i, lam i * (a i x - b i)) +
      (∑ j, nu j * (e j x - d j)) = n x - M := by
    simp only [hn, M, mul_sub, Finset.sum_sub_distrib]
    ring
  have hzM : n z = M := by
    have hi : (∑ i, lam i * (a i z - b i)) = 0 :=
      Finset.sum_eq_zero (fun i _ => hcomp i)
    have hj : (∑ j, nu j * (e j z - d j)) = 0 :=
      Finset.sum_eq_zero (fun j _ => by simp [hz.2 j])
    linarith [hidentity z]
  have hmax (x : E) (hx : x ∈ P) : n x ≤ M := by
    rw [hn]
    apply add_le_add
    · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx.1 i) (hlam i)
    · exact (Finset.sum_congr rfl (fun j _ => by rw [hx.2 j])).le
  have hb : BddAbove (n '' P) := by
    refine ⟨M, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hmax x hx
  have hsup : sSup (n '' P) = M := by
    apply le_antisymm
    · exact csSup_le ⟨n z, z, hz, rfl⟩ (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact hmax x hx)
    · rw [← hzM]
      exact le_csSup hb (mem_image_of_mem n hz)
  refine ⟨lam, nu, hlam, hres, ⟨z, hz, hzM, hmax⟩, hb, hsup, ?_⟩
  intro x hx
  have hr := hres x hx
  change p ≤ (f x).untopD 0 + n x - sSup (n '' P)
  rw [hsup]
  have hid := hidentity x
  linarith

end VariationalNotes.Ch04
