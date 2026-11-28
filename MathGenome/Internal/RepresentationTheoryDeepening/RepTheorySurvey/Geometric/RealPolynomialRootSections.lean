import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.RealPolynomialRootSections
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Order.Compact

namespace RepTheorySurvey.Geometric.RealPolynomialRootSections

open RealPolynomialRootSectionsSpecs (DerivativeFamilyType DerivativeProductType)

universe u v

open Set Filter Topology Polynomial
open scoped BigOperators ComplexConjugate

noncomputable abbrev derivativeFamily : DerivativeFamilyType.{u} :=
  RealPolynomialRootSectionsSpecs.derivativeFamily

noncomputable abbrev derivativeProduct : DerivativeProductType.{u} :=
  RealPolynomialRootSectionsSpecs.derivativeProduct

/-- A graph with compact range extends continuously when the fibres of its closure are
singletons. The closed projection also shows that every point of the closure of the original
domain has a nonempty fibre. -/
private theorem exists_continuousExtension_of_unique_graph_closure
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [CompactSpace B]
    (S : Set A) (f : S → B)
    (hunique : ∀ x y z,
      (x, y) ∈ closure (range fun s : S => (s.val, f s)) →
      (x, z) ∈ closure (range fun s : S => (s.val, f s)) → y = z) :
    ∃ F : closure S → B, Continuous F ∧
      (∀ x : closure S, (x.val, F x) ∈ closure (range fun s : S => (s.val, f s))) ∧
      ∀ x : S, F ⟨x.val, subset_closure x.property⟩ = f x := by
  let G : Set (A × B) := range fun s : S => (s.val, f s)
  have hg : Prod.fst '' G = S := by
    ext x
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact s.property
    · intro hx
      let s : S := ⟨x, hx⟩
      exact ⟨(x, f s), ⟨s, rfl⟩, rfl⟩
  have hc : Prod.fst '' closure G = closure S := by
    apply le_antisymm
    · simpa only [hg] using image_closure_subset_closure_image continuous_fst (s := G)
    · apply closure_minimal _ (isClosedMap_fst_of_compactSpace _ isClosed_closure)
      rw [← hg]
      exact image_mono subset_closure
  have hmaps : MapsTo Prod.fst (closure G) (closure S) := by
    rw [mapsTo_iff_image_subset, hc]
  let g := hmaps.restrict Prod.fst (closure G) (closure S)
  have hg_cont : Continuous g := continuous_fst.restrict hmaps
  have hg_closed : IsClosedMap g :=
    isClosedMap_fst_of_compactSpace.mapsToRestrict isClosed_closure hmaps
  have hg_bij : Function.Bijective g := by
    constructor
    · intro p q hpq
      have he : p.val.1 = q.val.1 := congrArg Subtype.val hpq
      apply Subtype.ext
      apply Prod.ext he
      exact hunique p.val.1 p.val.2 q.val.2 p.property (he ▸ q.property)
    · intro x
      obtain ⟨p, hp, he⟩ := (hc.symm.subset x.property : x.val ∈ Prod.fst '' closure G)
      exact ⟨⟨p, hp⟩, Subtype.ext he⟩
  let e := (Equiv.ofBijective g hg_bij).toHomeomorphOfContinuousClosed hg_cont hg_closed
  let F : closure S → B := fun x => (e.symm x).val.2
  have hproj (x : closure S) : (e.symm x).val.1 = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hmem (x : closure S) : (x.val, F x) ∈ closure G := by
    rw [← hproj x]
    exact (e.symm x).property
  refine ⟨F, continuous_snd.comp (continuous_subtype_val.comp e.symm.continuous), hmem, ?_⟩
  intro x
  exact hunique x.val _ _ (hmem ⟨x.val, subset_closure x.property⟩)
    (subset_closure (mem_range_self x))

/-- Joint continuity of evaluation for a family with bounded degree and continuous coefficients. -/
private theorem continuous_eval_family {A K : Type*} [TopologicalSpace A] [NormedField K]
    (p : A → K[X]) {N : ℕ} (hdegree : ∀ x, (p x).natDegree ≤ N)
    (hcoeff : ∀ k : ℕ, Continuous fun x => (p x).coeff k) :
    Continuous fun z : A × K => (p z.1).eval z.2 := by
  have heq (z : A × K) : (p z.1).eval z.2 =
      ∑ k ∈ Finset.range (N + 1), (p z.1).coeff k * z.2 ^ k :=
    eval_eq_sum_range' (Nat.lt_succ_of_le (hdegree z.1)) _
  simp_rw [heq]
  exact continuous_finsetSum _ fun k _ =>
    ((hcoeff k).comp continuous_fst).mul (continuous_snd.pow k)

private theorem continuous_eval_iterate_derivative_family {A : Type*} [TopologicalSpace A]
    (p : A → ℝ[X]) {N : ℕ} (hdegree : ∀ x, (p x).natDegree ≤ N)
    (hcoeff : ∀ k : ℕ, Continuous fun x => (p x).coeff k) (n : ℕ) :
    Continuous fun z : A × ℝ => (derivative^[n] (p z.1)).eval z.2 := by
  apply continuous_eval_family (fun x => derivative^[n] (p x)) (N := N)
  · intro x
    induction n with
    | zero => exact hdegree x
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (natDegree_derivative_le _).trans ((Nat.sub_le ..).trans ih)
  · intro k
    simp only [coeff_iterate_derivative, nsmul_eq_mul]
    exact (hcoeff _).const_mul _

private theorem eventually_exists_real_root_near_of_derivative_pos {A : Type*}
    [TopologicalSpace A] (p : A → ℝ[X]) (x₀ : A) (a : ℝ) (ha : (p x₀).IsRoot a)
    (hderiv : 0 < (p x₀).derivative.eval a)
    (hcont : ∀ t, ContinuousAt (fun x => (p x).eval t) x₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in nhds x₀, ∃ b ∈ Ioo (a - ε) (a + ε), (p x).IsRoot b := by
  let q := p x₀
  have hpos : IsOpen {s : ℝ | 0 < q.derivative.eval s} :=
    isOpen_lt continuous_const q.derivative.differentiable.continuous
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hpos.mem_nhds hderiv)
  rw [Real.ball_eq_Ioo] at hball
  let t := min (δ / 2) (ε / 2)
  have ht : 0 < t := lt_min (half_pos hδ) (half_pos hε)
  have htd : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hte : t < ε := (min_le_right _ _).trans_lt (half_lt_self hε)
  have hla : a - t < a := sub_lt_self _ ht
  have har : a < a + t := lt_add_of_pos_right _ ht
  have hcenter : a ∈ Ioo (a - δ) (a + δ) :=
    ⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩
  have hl : a - t ∈ Ioo (a - δ) (a + δ) :=
    ⟨sub_lt_sub_left htd a, hla.trans hcenter.2⟩
  have hr : a + t ∈ Ioo (a - δ) (a + δ) :=
    ⟨hcenter.1.trans har, add_lt_add_right htd a⟩
  have hmono := strictMonoOn_of_deriv_pos (convex_Ioo (a - δ) (a + δ))
    q.differentiable.continuous.continuousOn (fun s hs => by
      rw [q.deriv]
      exact hball (interior_subset hs))
  have hl₀ : (p x₀).eval (a - t) < 0 := (hmono hl hcenter hla).trans_eq (IsRoot.def.mp ha)
  have hr₀ : 0 < (p x₀).eval (a + t) := (IsRoot.def.mp ha).symm.trans_lt (hmono hcenter hr har)
  have hNl := (hcont (a - t)).eventually_lt continuousAt_const hl₀
  have hNr := continuousAt_const.eventually_lt (hcont (a + t)) hr₀
  filter_upwards [hNl, hNr] with x hxl hxr
  obtain ⟨b, hb, hb₀⟩ := intermediate_value_Icc (hla.trans har).le
    (p x).differentiable.continuous.continuousOn (show 0 ∈ Icc _ _ from ⟨hxl.le, hxr.le⟩)
  exact ⟨b, ⟨(sub_lt_sub_left hte a).trans_le hb.1, hb.2.trans_lt (add_lt_add_right hte a)⟩, hb₀⟩

/-- A simple real root persists in a small real interval as the polynomial varies. -/
private theorem eventually_exists_real_root_near_of_derivative_ne_zero {A : Type*}
    [TopologicalSpace A] (p : A → ℝ[X]) (x₀ : A) (a : ℝ) (ha : (p x₀).IsRoot a)
    (hderiv : (p x₀).derivative.eval a ≠ 0)
    (hcont : ∀ t, ContinuousAt (fun x => (p x).eval t) x₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in nhds x₀, ∃ b ∈ Ioo (a - ε) (a + ε), (p x).IsRoot b := by
  rcases lt_or_gt_of_ne hderiv with hn | hp
  · have he := eventually_exists_real_root_near_of_derivative_pos (fun x => -p x) x₀ a
      (by simpa only [IsRoot.def, eval_neg, neg_eq_zero] using ha)
      (by simpa only [derivative_neg, eval_neg, neg_pos] using hn)
      (fun t => by
        simp only [eval_neg]
        exact continuous_neg.continuousAt.comp (hcont t)) hε
    filter_upwards [he] with x hx
    simpa only [IsRoot.def, eval_neg, neg_eq_zero] using hx
  · exact eventually_exists_real_root_near_of_derivative_pos p x₀ a ha hp hcont hε

/-- The evaluation of a polynomial with continuously varying coefficients tends to zero at a
fixed root of the original polynomial. When the nearby monic polynomials split, their product
of linear factors forces at least one root to approach that fixed root. -/
private theorem eventually_exists_root_near {A K : Type*} [TopologicalSpace A] [NormedField K]
    (p : A → K[X]) (x₀ : A) (a : K) (ha : (p x₀).IsRoot a)
    (hcont : ContinuousAt (fun x => (p x).eval a) x₀) {d : ℕ}
    (hdegree : ∀ x, (p x).natDegree = d) (hmonic : ∀ x, (p x).Monic)
    (hsplit : ∀ x, (p x).Splits) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in nhds x₀, ∃ b, (p x).IsRoot b ∧ ‖a - b‖ < ε := by
  have hsmall : ∀ᶠ x in nhds x₀, ‖(p x).eval a‖ < ε ^ d :=
    hcont.norm.eventually_lt continuousAt_const (by simpa [IsRoot.def.mp ha] using pow_pos hε d)
  filter_upwards [hsmall] with x hx
  by_contra! hn
  have hprod := Multiset.prod_map_le_prod_map₀ (fun _ : K => ε) (fun b => ‖a - b‖)
    (fun _ _ => hε.le) (fun b hb => hn b ((mem_roots (hmonic x).ne_zero).mp hb))
  rw [Multiset.map_const', Multiset.prod_replicate, ← (hsplit x).natDegree_eq_card_roots,
    hdegree x] at hprod
  have heval : ‖(p x).eval a‖ = ((p x).roots.map fun b => ‖a - b‖).prod := by
    rw [(hsplit x).eval_eq_prod_roots_of_monic (hmonic x)]
    exact ((p x).roots.prod_hom' (NormedField.toMulRingNorm K) (fun b : K => a - b)).symm
  exact (not_lt_of_ge (heval ▸ hprod)) hx

private theorem eval_mem_uIcc_of_derivative_sign (p : ℝ[X]) {x y z : ℝ}
    (hz : z ∈ Icc x y) (h : (∀ t ∈ Icc x y, 0 ≤ p.derivative.eval t) ∨
      (∀ t ∈ Icc x y, p.derivative.eval t ≤ 0)) :
    p.eval z ∈ uIcc (p.eval x) (p.eval y) := by
  have hxy := hz.1.trans hz.2
  have hx : x ∈ Icc x y := left_mem_Icc.mpr hxy
  have hy : y ∈ Icc x y := right_mem_Icc.mpr hxy
  rcases h with h | h
  · have hm := monotoneOn_of_deriv_nonneg (convex_Icc x y)
      p.differentiable.continuous.continuousOn p.differentiable.differentiableOn
      (fun t ht => by rw [p.deriv]; exact h t (interior_subset ht))
    exact mem_uIcc_of_le (hm hx hz hz.1) (hm hz hy hz.2)
  · have hm := antitoneOn_of_deriv_nonpos (convex_Icc x y)
      p.differentiable.continuous.continuousOn p.differentiable.differentiableOn
      (fun t ht => by rw [p.deriv]; exact h t (interior_subset ht))
    exact mem_uIcc_of_ge (hm hz hy hz.2) (hm hx hz hz.1)

private theorem eval_mem_uIcc_of_iterate_derivatives (N : ℕ) (p : ℝ[X])
    (hN : derivative^[N] p = 0) {x y z : ℝ} (hz : z ∈ Icc x y)
    (h : ∀ n, let q := derivative^[n] p
      (0 ≤ q.eval x ∧ 0 ≤ q.eval y) ∨ (q.eval x ≤ 0 ∧ q.eval y ≤ 0)) :
    p.eval z ∈ uIcc (p.eval x) (p.eval y) := by
  induction N generalizing p z with
  | zero =>
    change p = 0 at hN
    simp [hN]
  | succ N ih =>
    have hd : ∀ t ∈ Icc x y, p.derivative.eval t ∈
        uIcc (p.derivative.eval x) (p.derivative.eval y) := by
      intro t ht
      exact ih p.derivative (by simpa only [Function.iterate_succ_apply] using hN) ht
        (fun n => by simpa only [Function.iterate_succ_apply] using h (n + 1))
    apply eval_mem_uIcc_of_derivative_sign p hz
    rcases h 1 with hpos | hneg
    · exact Or.inl fun t ht => le_trans (le_min hpos.1 hpos.2) (hd t ht).1
    · exact Or.inr fun t ht => le_trans (hd t ht).2 (max_le hneg.1 hneg.2)

/-- If the derivative signs at the two ends of an interval are weakly compatible,
the polynomial values throughout the interval lie between the endpoint values. -/
private theorem eval_mem_uIcc_of_compatible_derivatives (p : ℝ[X]) {x y z : ℝ} (hz : z ∈ Icc x y)
    (h : ∀ n, let q := derivative^[n] p
      (0 ≤ q.eval x ∧ 0 ≤ q.eval y) ∨ (q.eval x ≤ 0 ∧ q.eval y ≤ 0)) :
    p.eval z ∈ uIcc (p.eval x) (p.eval y) :=
  eval_mem_uIcc_of_iterate_derivatives (p.natDegree + 1) p
    (iterate_derivative_eq_zero (Nat.lt_succ_self _)) hz h

/-- Thom's root separation: for distinct real roots of a nonzero polynomial,
some derivative has strictly opposite signs at the two roots. -/
private theorem exists_derivative_opposite_sign_of_distinct_roots {p : ℝ[X]} (hp : p ≠ 0)
    {x y : ℝ} (hxy : x < y) (hx : p.IsRoot x) (hy : p.IsRoot y) :
    ∃ n, let q := derivative^[n] p
      (q.eval x < 0 ∧ 0 < q.eval y) ∨ (q.eval y < 0 ∧ 0 < q.eval x) := by
  by_contra hn
  have hc (n : ℕ) : let q := derivative^[n] p
      (0 ≤ q.eval x ∧ 0 ≤ q.eval y) ∨ (q.eval x ≤ 0 ∧ q.eval y ≤ 0) := by
    rcases le_or_gt 0 ((derivative^[n] p).eval x) with ha | ha
    · rcases le_or_gt 0 ((derivative^[n] p).eval y) with hb | hb
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr ⟨le_of_not_gt fun ha' => hn ⟨n, Or.inr ⟨hb, ha'⟩⟩, hb.le⟩
    · exact Or.inr ⟨ha.le, le_of_not_gt fun hb' => hn ⟨n, Or.inl ⟨ha, hb'⟩⟩⟩
  have hzero : Icc x y ⊆ {t | p.IsRoot t} := by
    intro t ht
    have hm := eval_mem_uIcc_of_compatible_derivatives p ht hc
    change p.eval x = 0 at hx
    change p.eval y = 0 at hy
    simpa [hx, hy, IsRoot] using hm
  exact (Icc_infinite hxy) ((finite_setOfPred_isRoot hp).subset hzero)

/-- Roots in a common bounded interval carrying a fixed derivative sign profile extend over
the closure of their parameter set as long as the limiting polynomials are nonzero. Weak
inequalities suffice, as they are preserved under taking the closure of the graph. -/
private theorem exists_continuousRootExtension {A : Type*} [TopologicalSpace A]
    (S : Set A) {a b : ℝ} (f : S → Icc a b) (p : A → ℝ[X])
    (hnonzero : ∀ x ∈ closure S, p x ≠ 0)
    (hcont : ∀ n : ℕ, Continuous fun z : A × ℝ => (derivative^[n] (p z.1)).eval z.2)
    (hroot : ∀ x : S, (p x.val).IsRoot (f x).val)
    (sign : ℕ → Bool)
    (hsign : ∀ (x : S) (n : ℕ), let q := (derivative^[n] (p x.val)).eval (f x).val
      if sign n then 0 ≤ q else q ≤ 0) :
    ∃ F : closure S → Icc a b, Continuous F ∧
      (∀ x : closure S, (p x.val).IsRoot (F x).val) ∧
      ∀ x : S, F ⟨x.val, subset_closure x.property⟩ = f x := by
  let G : Set (A × Icc a b) := range fun x : S => (x.val, f x)
  have hval (n : ℕ) : Continuous fun z : A × Icc a b =>
      (derivative^[n] (p z.1)).eval z.2.val :=
    (hcont n).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hg_root : closure G ⊆ {z | (p z.1).IsRoot z.2.val} := by
    apply closure_minimal
    · rintro _ ⟨x, rfl⟩
      exact hroot x
    · exact isClosed_eq (hval 0) continuous_const
  have hg_sign (n : ℕ) : closure G ⊆ {z | let q := (derivative^[n] (p z.1)).eval z.2.val
      if sign n then 0 ≤ q else q ≤ 0} := by
    apply closure_minimal
    · rintro _ ⟨x, rfl⟩
      exact hsign x n
    · cases hs : sign n with
      | false => simpa only [hs, Bool.false_eq_true, ↓reduceIte] using
          isClosed_le (hval n) continuous_const
      | true => simpa only [hs, ↓reduceIte] using isClosed_le continuous_const (hval n)
  have hg_base : closure G ⊆ Prod.fst ⁻¹' closure S := by
    refine closure_minimal ?_ (isClosed_closure.preimage continuous_fst)
    rintro _ ⟨x, rfl⟩
    exact subset_closure x.property
  have hfibre (x : A) (y z : Icc a b) (hy : (x, y) ∈ closure G) (hz : (x, z) ∈ closure G) :
      y = z := by
    suffices h : ∀ (u v : Icc a b), (x, u) ∈ closure G → (x, v) ∈ closure G →
        ¬u.val < v.val by
      exact Subtype.ext (le_antisymm (le_of_not_gt (h z y hz hy)) (le_of_not_gt (h y z hy hz)))
    intro u v hu hv huv
    obtain ⟨n, hn⟩ := exists_derivative_opposite_sign_of_distinct_roots
      (hnonzero x (hg_base hu)) huv (hg_root hu) (hg_root hv)
    have hsu := hg_sign n hu
    have hsv := hg_sign n hv
    dsimp only [mem_ofPred_eq] at hsu hsv hn
    cases hs : sign n <;> simp [hs] at hsu hsv
    · exact hn.elim (fun h => (not_lt_of_ge hsv) h.2) (fun h => (not_lt_of_ge hsu) h.2)
    · exact hn.elim (fun h => (not_lt_of_ge hsu) h.1) (fun h => (not_lt_of_ge hsv) h.1)
  obtain ⟨F, hF, hmem, hext⟩ := exists_continuousExtension_of_unique_graph_closure S f hfibre
  exact ⟨F, hF, fun x => hg_root (hmem x), hext⟩

private abbrev Vertical (σ : Type*) := Polynomial (MvPolynomial σ ℝ)

private noncomputable abbrev specialize {σ : Type*} (p : Vertical σ) (x : σ → ℝ) : Polynomial ℝ :=
  p.map (MvPolynomial.eval x)

private def HasConstantLeadingCoeff {σ : Type*} (p : Vertical σ) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ p.leadingCoeff = MvPolynomial.C c

private theorem HasConstantLeadingCoeff.ne_zero {σ : Type*} {p : Vertical σ}
    (h : HasConstantLeadingCoeff p) : p ≠ 0 := by
  obtain ⟨c, hc, hp⟩ := h
  intro hz
  apply hc
  have he : MvPolynomial.C c = (0 : MvPolynomial σ ℝ) := by simp [← hp, hz]
  simpa using congrArg (MvPolynomial.eval (fun _ : σ => 0)) he

private theorem HasConstantLeadingCoeff.iterate_derivative {σ : Type*} {p : Vertical σ}
    (hp : HasConstantLeadingCoeff p) (n : ℕ) (hn : derivative^[n] p ≠ 0) :
    HasConstantLeadingCoeff (derivative^[n] p) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hn ⊢
    have hdeg : (derivative^[n] p).natDegree ≠ 0 := derivative_ne_zero.mp hn
    obtain ⟨c, hc, he⟩ := ih fun hz => hn (by simp [hz])
    refine ⟨c * ((derivative^[n] p).natDegree : ℝ), mul_ne_zero hc (Nat.cast_ne_zero.mpr hdeg), ?_⟩
    rw [leadingCoeff_derivative, he, map_mul, map_natCast]

private theorem mem_derivativeFamily {σ : Type*} {P : Finset (Vertical σ)}
    {a b : ℝ} {q : Vertical σ} :
    q ∈ derivativeFamily P a b ↔
      q = X - Polynomial.C (MvPolynomial.C a) ∨
      q = X - Polynomial.C (MvPolynomial.C b) ∨
      (∃ p ∈ P, ∃ k ≤ p.natDegree, derivative^[k] p = q ∧ q ≠ 0) := by
  classical
  simp only [derivativeFamily, RealPolynomialRootSectionsSpecs.derivativeFamily, Finset.mem_insert,
    Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]
  grind

private theorem iterate_derivative_mem {σ : Type*} {P : Finset (Vertical σ)}
    {a b : ℝ} {p : Vertical σ} (hp : p ∈ P) (k : ℕ) (hk : derivative^[k] p ≠ 0) :
    derivative^[k] p ∈ derivativeFamily P a b :=
  mem_derivativeFamily.mpr <| Or.inr <| Or.inr
    ⟨p, hp, k, le_of_not_gt fun h => hk (iterate_derivative_eq_zero h), rfl, hk⟩

private theorem derivativeFamily_leadingCoeff {σ : Type*} {P : Finset (Vertical σ)}
    (hP : ∀ p ∈ P, HasConstantLeadingCoeff p) (a b : ℝ) :
    ∀ q ∈ derivativeFamily P a b, HasConstantLeadingCoeff q := by
  intro q hq
  rcases mem_derivativeFamily.mp hq with h | h | ⟨p, hp, n, _, rfl, hn⟩
  · exact ⟨1, one_ne_zero, by rw [h, leadingCoeff_X_sub_C, map_one]⟩
  · exact ⟨1, one_ne_zero, by rw [h, leadingCoeff_X_sub_C, map_one]⟩
  · exact (hP p hp).iterate_derivative n hn

/-- The derivative product has a nonzero real constant leading coefficient. -/
theorem derivativeProduct_leadingCoeff :
    RealPolynomialRootSectionsSpecs.DerivativeProductLeadingCoeff.{u} := by
  classical
  intro σ _ P a b _ hP
  have hprod (s : Finset (Vertical σ)) (hs : ∀ p ∈ s, HasConstantLeadingCoeff p) :
      HasConstantLeadingCoeff (s.prod id) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | @insert p s hp ih =>
      obtain ⟨c, hc, hcp⟩ := hs p (Finset.mem_insert_self p s)
      obtain ⟨d, hd, hds⟩ := ih fun q hq => hs q (Finset.mem_insert_of_mem hq)
      refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
      rw [Finset.prod_insert hp, leadingCoeff_mul, id_eq, hcp, hds, map_mul]
  exact hprod _ (derivativeFamily_leadingCoeff hP a b)

private theorem HasConstantLeadingCoeff.specialization_data {σ : Type*} {p : Vertical σ}
    (hp : HasConstantLeadingCoeff p) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ x, (specialize p x).leadingCoeff = c ∧
      (specialize p x).natDegree = p.natDegree := by
  obtain ⟨c, hc, hp⟩ := hp
  refine ⟨c, hc, fun x => ?_⟩
  have he : MvPolynomial.eval x p.leadingCoeff = c := by simp [hp]
  have hn : MvPolynomial.eval x p.leadingCoeff ≠ 0 := he ▸ hc
  exact ⟨(leadingCoeff_map_of_leadingCoeff_ne_zero _ hn).trans he,
    natDegree_map_of_leadingCoeff_ne_zero _ hn⟩

private theorem HasConstantLeadingCoeff.specialize_ne_zero {σ : Type*} {p : Vertical σ}
    (hp : HasConstantLeadingCoeff p) (x : σ → ℝ) : specialize p x ≠ 0 := by
  obtain ⟨c, hc, he⟩ := hp.specialization_data
  exact leadingCoeff_ne_zero.mp ((he x).1 ▸ hc)

private theorem continuous_specialized_eval {σ : Type*} (p : Vertical σ) (n : ℕ) :
    Continuous fun z : (σ → ℝ) × ℝ => (derivative^[n] (specialize p z.1)).eval z.2 := by
  apply continuous_eval_iterate_derivative_family _ (N := p.natDegree)
  · exact fun _ => natDegree_map_le
  · intro k
    simpa only [coeff_map] using (MvPolynomial.continuous_eval (p := p.coeff k))

private noncomputable abbrev complexSpecialize {σ : Type*} (p : Vertical σ) (x : σ → ℝ) :
    Polynomial ℂ := (specialize p x).map (algebraMap ℝ ℂ)

private abbrev complexRoots {σ : Type*} (p : Vertical σ) (x : σ → ℝ) :=
  (specialize p x).rootSet ℂ

private theorem mem_complexRoots {σ : Type*} {p : Vertical σ}
    (hp : HasConstantLeadingCoeff p) {x : σ → ℝ} {z : ℂ} :
    z ∈ complexRoots p x ↔ (complexSpecialize p x).IsRoot z := by
  rw [mem_rootSet_of_ne (hp.specialize_ne_zero x), IsRoot]
  change aeval z (specialize p x) = 0 ↔ ((specialize p x).map (algebraMap ℝ ℂ)).eval z = 0
  rw [eval_map_algebraMap]

private theorem ofReal_mem_complexRoots {σ : Type*} {p : Vertical σ}
    (hp : HasConstantLeadingCoeff p) {x : σ → ℝ} {t : ℝ} :
    (t : ℂ) ∈ complexRoots p x ↔ (specialize p x).IsRoot t := by
  rw [mem_complexRoots hp, IsRoot, IsRoot]
  change ((specialize p x).map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ t) = 0 ↔ _
  rw [eval_map_apply, map_eq_zero_iff _ (algebraMap ℝ ℂ).injective]

private theorem conj_mem_complexRoots {σ : Type*} {p : Vertical σ}
    (hp : HasConstantLeadingCoeff p) {x : σ → ℝ} {z : ℂ}
    (hz : z ∈ complexRoots p x) : conj z ∈ complexRoots p x := by
  rw [mem_rootSet_of_ne (hp.specialize_ne_zero x)] at hz ⊢
  rw [← Complex.conjAe_coe, aeval_algHom_apply, hz, map_zero]

private theorem continuous_complexSpecialized_eval {σ : Type*} (p : Vertical σ) :
    Continuous fun z : (σ → ℝ) × ℂ => (complexSpecialize p z.1).eval z.2 := by
  apply continuous_eval_family _ (N := p.natDegree)
  · exact fun _ => natDegree_map_le.trans natDegree_map_le
  · intro k
    simp only [coeff_map]
    exact Complex.continuous_ofReal.comp (MvPolynomial.continuous_eval (p := p.coeff k))

private theorem complexRoot_persistence {σ A : Type*} [TopologicalSpace A]
    {p : Vertical σ} (hp : HasConstantLeadingCoeff p) {f : A → σ → ℝ} (hf : Continuous f)
    (x : A) {z : ℂ} (hz : z ∈ complexRoots p (f x)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝 x, ∃ w ∈ complexRoots p (f y), dist w z < δ := by
  obtain ⟨c, hc, hdata⟩ := hp.specialization_data
  let q (y : A) := Polynomial.C ((algebraMap ℝ ℂ) c)⁻¹ * complexSpecialize p (f y)
  have hcc : (algebraMap ℝ ℂ) c ≠ 0 := (map_ne_zero_iff _ (algebraMap ℝ ℂ).injective).mpr hc
  have hroot (y : A) (w : ℂ) : (q y).IsRoot w ↔ w ∈ complexRoots p (f y) := by
    rw [mem_complexRoots hp, IsRoot, IsRoot]
    simp [q, hc]
  have hcont : Continuous (fun y => (q y).eval z) := by
    have he := (continuous_complexSpecialized_eval p).comp (hf.prodMk (continuous_const (y := z)))
    simpa only [q, eval_mul, eval_C, Function.comp_apply] using he.const_mul ((algebraMap ℝ ℂ) c)⁻¹
  have hdeg (y : A) : (q y).natDegree = p.natDegree := by
    dsimp only [q]
    have hn : (algebraMap ℝ ℂ) (specialize p (f y)).leadingCoeff ≠ 0 :=
      (hdata (f y)).1 ▸ hcc
    rw [natDegree_C_mul (inv_ne_zero hcc)]
    exact (natDegree_map_of_leadingCoeff_ne_zero _ hn).trans (hdata (f y)).2
  have hmonic (y : A) : (q y).Monic := by
    unfold Monic
    dsimp only [q]
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_map,
      (hdata (f y)).1]
    exact inv_mul_cancel₀ hcc
  filter_upwards [eventually_exists_root_near q x z ((hroot x z).mpr hz)
    hcont.continuousAt hdeg hmonic (fun _ => IsAlgClosed.splits _) hδ] with y hy
  obtain ⟨w, hw, hd⟩ := hy
  exact ⟨w, (hroot y w).mp hw, by simpa [dist_comm, dist_eq_norm] using hd⟩

private theorem exists_small_root_radius {s : Set ℂ} [Finite s] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      (∀ z w : s, z ≠ w → 2 * δ < dist (z : ℂ) w) ∧
      (∀ z : s, (z : ℂ).im ≠ 0 → δ < |(z : ℂ).im|) := by
  have hsep : ∀ᶠ δ : ℝ in 𝓝 0, ∀ z w : s, z ≠ w → 2 * δ < dist (z : ℂ) w := by
    refine eventually_all.mpr fun z => eventually_all.mpr fun w => ?_
    by_cases h : z = w
    · exact Eventually.of_forall fun _ hn => (hn h).elim
    have hp : 0 < dist (z : ℂ) w := dist_pos.mpr (fun he => h (Subtype.ext he))
    exact ((continuous_const.mul continuous_id).continuousAt.eventually_lt continuousAt_const
      (show (2 : ℝ) * 0 < dist (z : ℂ) w by simpa using hp)).mono (fun _ hd _ => hd)
  have him : ∀ᶠ δ : ℝ in 𝓝 0, ∀ z : s, (z : ℂ).im ≠ 0 → δ < |(z : ℂ).im| := by
    refine eventually_all.mpr fun z => ?_
    by_cases h : (z : ℂ).im = 0
    · exact Eventually.of_forall fun _ hn => (hn h).elim
    exact (eventually_lt_nhds (abs_pos.mpr h)).mono fun _ hd _ => hd
  have he := ((eventually_lt_nhds hε).and (hsep.and him)).filter_mono
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  obtain ⟨δ, hpos, hδ⟩ := (eventually_mem_nhdsWithin.and he).exists
  exact ⟨δ, hpos, hδ⟩

private theorem unique_near_matched_root {s t : Set ℂ} {δ : ℝ}
    (hsep : ∀ z w : s, z ≠ w → 2 * δ < dist (z : ℂ) w)
    (e : s ≃ t) (he : ∀ z : s, dist (e z : ℂ) z < δ)
    {z : s} {w : t} (hw : dist (w : ℂ) z < δ) : w = e z := by
  have h : e.symm w = z := by
    by_contra hn
    have hcontr := hsep (e.symm w) z hn
    have hh := he (e.symm w)
    rw [e.apply_symm_apply] at hh
    have htri := dist_triangle (e.symm w : ℂ) (w : ℂ) (z : ℂ)
    rw [dist_comm _ (w : ℂ)] at htri
    linarith
  exact (e.symm_apply_eq).mp h

/-- Root persistence gives an injection into the nearby roots, which the fixed count makes
bijective. -/
private theorem complexRoots_eventually_equiv {σ A : Type*} [TopologicalSpace A]
    {p : Vertical σ} (hp : HasConstantLeadingCoeff p) {f : A → σ → ℝ} (hf : Continuous f)
    (x : A) (hcount : ∀ y, (complexRoots p (f x)).ncard = (complexRoots p (f y)).ncard)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ z w : complexRoots p (f x), z ≠ w → 2 * δ < dist (z : ℂ) w) :
    ∀ᶠ y in 𝓝 x, ∃ e : complexRoots p (f x) ≃ complexRoots p (f y),
      ∀ z : complexRoots p (f x), dist (e z : ℂ) z < δ := by
  classical
  have hev : ∀ᶠ y in 𝓝 x, ∀ z : complexRoots p (f x),
      ∃ w : complexRoots p (f y), dist (w : ℂ) z < δ := by
    refine eventually_all.mpr fun z => ?_
    exact (complexRoot_persistence hp hf x z.property hδ).mono fun _ ⟨w, hw, hd⟩ => ⟨⟨w, hw⟩, hd⟩
  filter_upwards [hev] with y hy
  choose g hg using hy
  have hginj : Function.Injective g := by
    intro z w he
    by_contra hn
    have hz := hg z
    have hw := hg w
    rw [← he] at hw
    have htri := dist_triangle (z : ℂ) (g z : ℂ) (w : ℂ)
    rw [dist_comm (z : ℂ) (g z : ℂ)] at htri
    have hh := hsep z w hn
    linarith
  have hcards : Fintype.card (complexRoots p (f x)) = Fintype.card (complexRoots p (f y)) := by
    simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using hcount y
  exact ⟨Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hcards⟩), hg⟩

private theorem abs_re_sub_le_dist (z w : ℂ) : |z.re - w.re| ≤ dist z w := by
  simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (z - w)

private theorem abs_im_sub_le_dist (z w : ℂ) : |z.im - w.im| ≤ dist z w := by
  simpa only [Complex.sub_im, dist_eq_norm] using Complex.abs_im_le_norm (z - w)

private theorem ofReal_re_of_im_zero {z : ℂ} (hz : z.im = 0) : (z.re : ℂ) = z :=
  Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr hz)

private theorem matched_root_im_eq_zero_iff {σ : Type*}
    {p : Vertical σ} (hp : HasConstantLeadingCoeff p) {x y : σ → ℝ} {δ : ℝ}
    (e : complexRoots p x ≃ complexRoots p y)
    (he : ∀ z : complexRoots p x, dist (e z : ℂ) z < δ)
    (hsep : ∀ z w : complexRoots p x, z ≠ w → 2 * δ < dist (z : ℂ) w)
    (him : ∀ z : complexRoots p x, (z : ℂ).im ≠ 0 → δ < |(z : ℂ).im|)
    (z : complexRoots p x) : (e z : ℂ).im = 0 ↔ (z : ℂ).im = 0 := by
  constructor
  · intro hz
    by_contra hn
    have hd := (abs_im_sub_le_dist (e z : ℂ) z).trans_lt (he z)
    rw [hz, zero_sub, abs_neg] at hd
    exact (not_lt_of_ge (him z hn).le) hd
  · intro hz
    let w : complexRoots p y := ⟨conj (e z : ℂ), conj_mem_complexRoots hp (e z).property⟩
    have hw : dist (w : ℂ) z < δ := by
      change dist (conj (e z : ℂ)) (z : ℂ) < δ
      rw [Complex.dist_conj_comm, Complex.conj_eq_iff_im.mpr hz]
      exact he z
    exact Complex.conj_eq_iff_im.mp (congrArg Subtype.val (unique_near_matched_root hsep e he hw))

private noncomputable def boundedRoots {σ : Type*} (p : Vertical σ) (a b : ℝ) (x : σ → ℝ) :
    Finset ℝ := by
  classical
  exact (specialize p x).roots.toFinset.filter (· ∈ Icc a b)

private theorem mem_boundedRoots {σ : Type*} {p : Vertical σ}
    (hp : HasConstantLeadingCoeff p) {a b t : ℝ} {x : σ → ℝ} :
    t ∈ boundedRoots p a b x ↔ t ∈ Icc a b ∧ (specialize p x).IsRoot t := by
  classical
  simp [boundedRoots, mem_roots (hp.specialize_ne_zero x), and_comm]

/-- The complex matching restricts to an increasing bijection of real roots between the fixed
cutoffs. -/
private theorem boundedRoots_eventually_equiv {σ A : Type*} [TopologicalSpace A]
    {p : Vertical σ} (hp : HasConstantLeadingCoeff p) {f : A → σ → ℝ} (hf : Continuous f)
    {a b : ℝ} (ha : ∀ y, (specialize p (f y)).IsRoot a)
    (hb : ∀ y, (specialize p (f y)).IsRoot b)
    (x : A) (hcount : ∀ y, (complexRoots p (f x)).ncard = (complexRoots p (f y)).ncard)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∃ e : ↥(boundedRoots p a b (f x)) ≃o ↥(boundedRoots p a b (f y)),
      ∀ t : boundedRoots p a b (f x), dist (e t : ℝ) t < ε := by
  classical
  obtain ⟨δ, hδ, hδε, hsep, him⟩ := exists_small_root_radius (s := complexRoots p (f x)) hε
  filter_upwards [complexRoots_eventually_equiv hp hf x hcount hδ hsep] with y hy
  obtain ⟨e, he⟩ := hy
  let lift (z : A) (t : ℝ) (ht : (specialize p (f z)).IsRoot t) : complexRoots p (f z) :=
    ⟨(t : ℂ), (ofReal_mem_complexRoots hp).mpr ht⟩
  have hr (t : ℝ) (ht : (specialize p (f x)).IsRoot t) :
      (e (lift x t ht) : ℂ).im = 0 :=
    (matched_root_im_eq_zero_iff hp e he hsep him _).mpr (Complex.ofReal_im _)
  have hrroot (t : ℝ) (ht : (specialize p (f x)).IsRoot t) :
      (specialize p (f y)).IsRoot (e (lift x t ht) : ℂ).re := by
    apply (ofReal_mem_complexRoots hp).mp
    rw [ofReal_re_of_im_zero (hr t ht)]
    exact (e _).property
  have hfixed (t : ℝ) (htx : (specialize p (f x)).IsRoot t)
      (hty : (specialize p (f y)).IsRoot t) : e (lift x t htx) = lift y t hty := by
    symm
    exact unique_near_matched_root hsep e he (by simpa [lift] using hδ)
  have horder {t s : ℝ} (ht : (specialize p (f x)).IsRoot t)
      (hs : (specialize p (f x)).IsRoot s) (hts : t < s) :
      (e (lift x t ht) : ℂ).re < (e (lift x s hs) : ℂ).re := by
    have hn : lift x t ht ≠ lift x s hs := fun heq =>
      hts.ne (congrArg (fun z : complexRoots p (f x) => (z : ℂ).re) heq)
    have hd := hsep _ _ hn
    change 2 * δ < dist (t : ℂ) (s : ℂ) at hd
    rw [Complex.isometry_ofReal.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.mpr hts)] at hd
    have hd' (r : ℝ) (hs' : (specialize p (f x)).IsRoot r) :
        |(e (lift x r hs') : ℂ).re - r| < δ :=
      (abs_re_sub_le_dist (e (lift x r hs') : ℂ) (r : ℂ)).trans_lt (he _)
    linarith [(abs_lt.mp (hd' t ht)).2, (abs_lt.mp (hd' s hs)).1]
  have horder_iff {t s : ℝ} (ht : (specialize p (f x)).IsRoot t)
      (hs : (specialize p (f x)).IsRoot s) :
      (e (lift x t ht) : ℂ).re ≤ (e (lift x s hs) : ℂ).re ↔ t ≤ s := by
    constructor
    · exact fun hh => le_of_not_gt fun hst => (not_lt_of_ge hh) (horder hs ht hst)
    · intro hts
      rcases hts.lt_or_eq with hlt | rfl
      · exact (horder ht hs hlt).le
      · rfl
  have hIcc (t : ℝ) (ht : (specialize p (f x)).IsRoot t) :
      (e (lift x t ht) : ℂ).re ∈ Icc a b ↔ t ∈ Icc a b := by
    have hleft := horder_iff (ha x) ht
    have hright := horder_iff ht (hb x)
    rw [hfixed a (ha x) (ha y)] at hleft
    rw [hfixed b (hb x) (hb y)] at hright
    exact and_congr hleft hright
  let g (t : boundedRoots p a b (f x)) : boundedRoots p a b (f y) :=
    let ht := (mem_boundedRoots hp).mp t.property
    ⟨(e (lift x t ht.2) : ℂ).re, (mem_boundedRoots hp).mpr
      ⟨(hIcc t ht.2).mpr ht.1, hrroot t ht.2⟩⟩
  have hmono : StrictMono g := by
    intro t s hts
    exact horder ((mem_boundedRoots hp).mp t.property).2
      ((mem_boundedRoots hp).mp s.property).2 hts
  have hsurj : Function.Surjective g := by
    intro t
    obtain ⟨htI, ht⟩ := (mem_boundedRoots hp).mp t.property
    let z := e.symm (lift y t ht)
    have hz : e z = lift y t ht := e.apply_symm_apply _
    have hzreal : (z : ℂ).im = 0 :=
      (matched_root_im_eq_zero_iff hp e he hsep him z).mp (by rw [hz]; exact Complex.ofReal_im _)
    let r := (z : ℂ).re
    have hzval : (r : ℂ) = (z : ℂ) := ofReal_re_of_im_zero hzreal
    have hrx : (specialize p (f x)).IsRoot r := by
      apply (ofReal_mem_complexRoots hp).mp
      rw [hzval]
      exact z.property
    have hlift : lift x r hrx = z := Subtype.ext hzval
    have hry : (e (lift x r hrx) : ℂ).re = t := by
      rw [hlift, hz]
      exact Complex.ofReal_re _
    have hrI := (hIcc r hrx).mp (hry.symm ▸ htI)
    exact ⟨⟨r, (mem_boundedRoots hp).mpr ⟨hrI, hrx⟩⟩, Subtype.ext hry⟩
  let iso : ↥(boundedRoots p a b (f x)) ≃o ↥(boundedRoots p a b (f y)) :=
    { Equiv.ofBijective g ⟨hmono.injective, hsurj⟩ with
      map_rel_iff' := fun {t s} => hmono.le_iff_le }
  refine ⟨iso, fun t => ?_⟩
  have hd := (abs_re_sub_le_dist (e (lift x t ((mem_boundedRoots hp).mp t.property).2) : ℂ)
    (t : ℂ)).trans_lt (he _)
  rw [Real.dist_eq]
  change |(e (lift x t ((mem_boundedRoots hp).mp t.property).2) : ℂ).re - (t : ℝ)| < ε
  exact hd.trans hδε

private theorem boundedRoots_enumerate {σ A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    [Nonempty A] {p : Vertical σ} (hp : HasConstantLeadingCoeff p)
    {f : A → σ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, (specialize p (f y)).IsRoot a) (hb : ∀ y, (specialize p (f y)).IsRoot b)
    (hcount : ∀ x y, (complexRoots p (f x)).ncard = (complexRoots p (f y)).ncard) :
    ∃ (m : ℕ) (h : Fin (m + 2) → A → Icc a b),
      (∀ k, Continuous (h k)) ∧
      (∀ x, StrictMono fun k => h k x) ∧
      (∀ x, (h 0 x).val = a ∧ (h (Fin.last (m + 1)) x).val = b) ∧
      ∀ x (t : ℝ), (∃ k, (h k x).val = t) ↔ t ∈ boundedRoots p a b (f x) := by
  classical
  let S (x : A) := boundedRoots p a b (f x)
  have hl (x : A) : a ∈ S x := (mem_boundedRoots hp).mpr ⟨⟨le_rfl, hab.le⟩, ha x⟩
  have hu (x : A) : b ∈ S x := (mem_boundedRoots hp).mpr ⟨⟨hab.le, le_rfl⟩, hb x⟩
  have hloc : IsLocallyConstant fun x => (S x).card := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
    filter_upwards [boundedRoots_eventually_equiv hp hf ha hb x (hcount x)
      (zero_lt_one : (0 : ℝ) < 1)] with y hy
    obtain ⟨e, _⟩ := hy
    simpa only [Fintype.card_coe] using Fintype.card_congr e.toEquiv.symm
  let x₀ : A := Classical.choice ‹Nonempty A›
  have htwo : 2 ≤ (S x₀).card :=
    (show (S x₀).Nontrivial from ⟨a, hl x₀, b, hu x₀, hab.ne⟩).two_le_card
  let m := (S x₀).card - 2
  have hc (x : A) : (S x).card = m + 2 :=
    (hloc.apply_eq_of_preconnectedSpace x x₀).trans (Nat.sub_add_cancel htwo).symm
  let e (x : A) := (S x).orderEmbOfFin (hc x)
  let h (k : Fin (m + 2)) (x : A) : Icc a b :=
    ⟨e x k, ((mem_boundedRoots hp).mp (Finset.orderEmbOfFin_mem (S x) (hc x) k)).1⟩
  have hmono (x : A) : StrictMono fun k => h k x := (e x).strictMono
  have hrange (x : A) (t : ℝ) : (∃ k, (h k x).val = t) ↔ t ∈ S x := by
    change t ∈ range (e x) ↔ t ∈ S x
    rw [Finset.range_orderEmbOfFin]
    rfl
  refine ⟨m, h, ?_, hmono, ?_, hrange⟩
  · intro k
    refine Continuous.subtype_mk ?_ _
    apply continuous_iff_continuousAt.mpr
    intro x
    refine Metric.continuousAt_iff'.mpr fun ε hε => ?_
    filter_upwards [boundedRoots_eventually_equiv hp hf ha hb x (hcount x) hε] with y hy
    obtain ⟨g, hg⟩ := hy
    let j := (S x).orderIsoOfFin (hc x)
    have he : (fun i => (g (j i) : ℝ)) = e y :=
      Finset.orderEmbOfFin_unique (hc y) (fun i => (g (j i)).property)
        (fun _ _ hi => g.strictMono (j.strictMono hi))
    rw [← congrFun he k]
    exact hg (j k)
  · intro x
    obtain ⟨i, hi⟩ := (hrange x a).mpr (hl x)
    obtain ⟨j, hj⟩ := (hrange x b).mpr (hu x)
    have hl' : (h 0 x).val ≤ (h i x).val := (hmono x).monotone (Fin.zero_le i)
    have hu' : (h j x).val ≤ (h (Fin.last (m + 1)) x).val :=
      (hmono x).monotone (Fin.le_last j)
    exact ⟨le_antisymm (hl'.trans_eq hi) (h 0 x).property.1,
      le_antisymm (h _ x).property.2 (hj.symm.trans_le hu')⟩

private theorem product_isRoot_iff {σ : Type*} {P : Finset (Vertical σ)}
    {a b t : ℝ} {x : σ → ℝ} :
    (specialize (derivativeProduct P a b) x).IsRoot t ↔
      ∃ q ∈ derivativeFamily P a b, (specialize q x).IsRoot t := by
  classical
  change (Polynomial.map (MvPolynomial.eval x) ((derivativeFamily P a b).prod id)).IsRoot t ↔ _
  rw [Polynomial.map_prod, isRoot_prod]
  rfl

private theorem cutoff_isRoot {σ : Type*} (x : σ → ℝ) (t : ℝ) :
    (specialize (X - Polynomial.C (MvPolynomial.C t)) x).IsRoot t := by
  simp [IsRoot, specialize]

private theorem factor_root_eventually {σ A : Type*} [TopologicalSpace A]
    {F p : Vertical σ} (hF : HasConstantLeadingCoeff F) (hp : HasConstantLeadingCoeff p)
    {f : A → σ → ℝ} (hf : Continuous f)
    (hsub : ∀ y, complexRoots p (f y) ⊆ complexRoots F (f y))
    (hcount : ∀ x y, (complexRoots F (f x)).ncard = (complexRoots F (f y)).ncard)
    {r : A → ℝ} (hr : Continuous r)
    (hroot : ∀ y, (specialize F (f y)).IsRoot (r y))
    (x : A) (hx : (specialize p (f x)).IsRoot (r x)) :
    ∀ᶠ y in 𝓝 x, (specialize p (f y)).IsRoot (r y) := by
  obtain ⟨δ, hδ, _, hsep, _⟩ :=
    exists_small_root_radius (s := complexRoots F (f x)) (zero_lt_one : (0 : ℝ) < 1)
  let center : complexRoots F (f x) :=
    ⟨r x, (ofReal_mem_complexRoots hF).mpr (hroot x)⟩
  have hd : ∀ᶠ y in 𝓝 x, dist (↑(r y) : ℂ) (r x : ℂ) < δ :=
    Metric.continuousAt_iff'.mp (Complex.continuous_ofReal.comp hr).continuousAt _ hδ
  filter_upwards [complexRoots_eventually_equiv hF hf x (hcount x) hδ hsep,
    complexRoot_persistence hp hf x ((ofReal_mem_complexRoots hp).mpr hx) hδ, hd] with y hy hz hd
  obtain ⟨e, he⟩ := hy
  obtain ⟨w, hw, hdist⟩ := hz
  let r' : complexRoots F (f y) := ⟨r y, (ofReal_mem_complexRoots hF).mpr (hroot y)⟩
  let w' : complexRoots F (f y) := ⟨w, hsub y hw⟩
  have hr' : r' = e center := unique_near_matched_root hsep e he hd
  have hw' : w' = e center := unique_near_matched_root hsep e he hdist
  have heq : (r y : ℂ) = w := congrArg Subtype.val (hr'.trans hw'.symm)
  apply (ofReal_mem_complexRoots hp).mp
  rwa [heq]

private theorem complexRoots_subset_product {σ : Type*} {P : Finset (Vertical σ)}
    {a b : ℝ} {p : Vertical σ} (hp : p ∈ derivativeFamily P a b)
    (hp' : HasConstantLeadingCoeff p) (hF : HasConstantLeadingCoeff (derivativeProduct P a b))
    (x : σ → ℝ) : complexRoots p x ⊆ complexRoots (derivativeProduct P a b) x := by
  intro z hz
  have hr := (mem_complexRoots hp').mp hz
  apply (mem_complexRoots hF).mpr
  change (((derivativeFamily P a b).prod id).map (MvPolynomial.eval x) |>.map
    (algebraMap ℝ ℂ)).IsRoot z
  rw [Polynomial.map_prod, Polynomial.map_prod, isRoot_prod]
  exact ⟨p, hp, hr⟩

private def SameSign (r t : ℝ) : Prop :=
  (0 ≤ r ↔ 0 ≤ t) ∧ (r ≤ 0 ↔ t ≤ 0)

private theorem sameSign_of_locally_constant_zero {A : Type*} [TopologicalSpace A]
    [PreconnectedSpace A] {g : A → ℝ} (hg : Continuous g)
    (hzero : ∀ x, g x = 0 → ∀ᶠ y in 𝓝 x, g y = 0) (x y : A) :
    SameSign (g x) (g y) := by
  let sign (z : A) : Prop × Prop := (0 ≤ g z, g z ≤ 0)
  have hl : IsLocallyConstant sign := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    rcases lt_trichotomy (g z) 0 with hneg | hz | hpos
    · filter_upwards [hg.continuousAt.eventually_lt continuousAt_const hneg] with w hw
      exact Prod.ext (propext (iff_of_false (not_le_of_gt hw) (not_le_of_gt hneg)))
        (propext (iff_of_true hw.le hneg.le))
    · exact (hzero z hz).mono fun w hw => by simp only [sign, hz, hw]
    · filter_upwards [continuousAt_const.eventually_lt hg.continuousAt hpos] with w hw
      exact Prod.ext (propext (iff_of_true hw.le hpos.le))
        (propext (iff_of_false (not_le_of_gt hw) (not_le_of_gt hpos)))
  have heq := hl.apply_eq_of_preconnectedSpace x y
  exact ⟨Iff.of_eq (congrArg Prod.fst heq), Iff.of_eq (congrArg Prod.snd heq)⟩

private theorem factor_sameSign_on_section {σ A : Type*} [TopologicalSpace A]
    [PreconnectedSpace A] {F p : Vertical σ}
    (hF : HasConstantLeadingCoeff F) (hp : HasConstantLeadingCoeff p)
    {f : A → σ → ℝ} (hf : Continuous f)
    (hsub : ∀ y, complexRoots p (f y) ⊆ complexRoots F (f y))
    (hcount : ∀ x y, (complexRoots F (f x)).ncard = (complexRoots F (f y)).ncard)
    {r : A → ℝ} (hr : Continuous r)
    (hroot : ∀ y, (specialize F (f y)).IsRoot (r y)) (x y : A) :
    SameSign ((specialize p (f x)).eval (r x)) ((specialize p (f y)).eval (r y)) := by
  have hc : Continuous fun z => (specialize p (f z)).eval (r z) :=
    (continuous_specialized_eval p 0).comp (hf.prodMk hr)
  exact sameSign_of_locally_constant_zero hc
    (factor_root_eventually hF hp hf hsub hcount hr hroot) x y

private theorem iterate_cutoff_succ_eq {σ : Type*} (t : ℝ) (n : ℕ) :
    derivative^[n + 1] (X - Polynomial.C (MvPolynomial.C t) : Vertical σ) =
      derivative^[n] (1 : Vertical σ) := by rw [Function.iterate_succ_apply, derivative_X_sub_C]

private theorem iterate_derivative_of_family {σ : Type*} {P : Finset (Vertical σ)}
    {a b : ℝ} {q : Vertical σ} (hq : q ∈ derivativeFamily P a b) (n : ℕ) :
    derivative^[n] q ∈ derivativeFamily P a b ∨
      ∃ c : ℝ, derivative^[n] q = Polynomial.C (MvPolynomial.C c) := by
  have hcut (t : ℝ) (h : q = X - Polynomial.C (MvPolynomial.C t)) :
      derivative^[n] q ∈ derivativeFamily P a b ∨
        ∃ c : ℝ, derivative^[n] q = Polynomial.C (MvPolynomial.C c) := by
    cases n with
    | zero => exact Or.inl hq
    | succ n =>
      rw [h, iterate_cutoff_succ_eq]
      cases n with
      | zero => exact Or.inr ⟨1, by simp⟩
      | succ n => exact Or.inr ⟨0, by simp [iterate_derivative_one (Nat.succ_pos n)]⟩
  rcases mem_derivativeFamily.mp hq with h | h | ⟨p, hp, k, _, hk, _⟩
  · exact hcut a h
  · exact hcut b h
  · rw [← hk, ← Function.iterate_add_apply]
    by_cases hzero : derivative^[n + k] p = 0
    · exact Or.inr ⟨0, by simpa using hzero⟩
    · exact Or.inl (iterate_derivative_mem hp _ hzero)

private theorem extend_section {σ : Type*} {P : Finset (Vertical σ)} {a b : ℝ}
    {S : Set (σ → ℝ)} (x₀ : S)
    (hD : ∀ q ∈ derivativeFamily P a b, HasConstantLeadingCoeff q)
    {r : S → Icc a b}
    (hr : ∀ x, (specialize (derivativeProduct P a b) x.val).IsRoot (r x).val)
    (hsgn : ∀ q ∈ derivativeFamily P a b, ∀ x y : S,
      SameSign ((specialize q x.val).eval (r x).val) ((specialize q y.val).eval (r y).val)) :
    ∃ H : closure S → Icc a b, Continuous H ∧
      (∀ x : closure S, (specialize (derivativeProduct P a b) x.val).IsRoot (H x).val) ∧
      ∀ x : S, H (Set.inclusion subset_closure x) = r x := by
  classical
  obtain ⟨q, hq, hqr⟩ := product_isRoot_iff.mp (hr x₀)
  have hqr' (x : S) : (specialize q x.val).IsRoot (r x).val := by
    have hs := hsgn q hq x x₀
    have hz := IsRoot.def.mp hqr
    exact le_antisymm (hs.2.mpr hz.le) (hs.1.mpr hz.ge)
  let sign (n : ℕ) : Bool := decide (0 ≤ (derivative^[n] (specialize q x₀.val)).eval (r x₀).val)
  have hs (x : S) (n : ℕ) :
      SameSign ((derivative^[n] (specialize q x.val)).eval (r x).val)
        ((derivative^[n] (specialize q x₀.val)).eval (r x₀).val) := by
    change SameSign ((derivative^[n] (q.map (MvPolynomial.eval x.val))).eval (r x).val)
      ((derivative^[n] (q.map (MvPolynomial.eval x₀.val))).eval (r x₀).val)
    rw [iterate_derivative_map, iterate_derivative_map]
    rcases iterate_derivative_of_family hq n with hm | ⟨c, hc⟩
    · exact hsgn _ hm x x₀
    · simp [hc, SameSign]
  have hsign (x : S) (n : ℕ) :
      let v := (derivative^[n] (specialize q x.val)).eval (r x).val
      if sign n then 0 ≤ v else v ≤ 0 := by
    dsimp only [sign]
    split_ifs with hh
    · exact (hs x n).1.mpr (of_decide_eq_true hh)
    · exact (hs x n).2.mpr (le_of_not_ge fun h => hh (decide_eq_true h))
  obtain ⟨H, hH, hHroot, hHr⟩ := exists_continuousRootExtension S r (specialize q)
    (fun x _ => (hD q hq).specialize_ne_zero x) (continuous_specialized_eval q) hqr' sign hsign
  exact ⟨H, hH, fun x => product_isRoot_iff.mpr ⟨q, hq, hHroot x⟩, hHr⟩

private theorem exists_simple_derivative_root {p : Polynomial ℝ} (hp : p ≠ 0)
    {t : ℝ} (ht : p.IsRoot t) :
    ∃ n, (derivative^[n] p).IsRoot t ∧ (derivative (derivative^[n] p)).eval t ≠ 0 := by
  generalize hd : p.natDegree = d
  induction d using Nat.strong_induction_on generalizing p with
  | h d ih =>
    by_cases h : p.derivative.IsRoot t
    · have hdeg : p.natDegree ≠ 0 := by
        intro hz
        apply hp
        have he := eq_C_of_natDegree_eq_zero hz
        rw [he] at ht ⊢
        simp only [IsRoot, eval_C] at ht
        simp [ht]
      obtain ⟨n, hn, hsimple⟩ := ih _ (hd ▸ natDegree_derivative_lt hdeg)
        (derivative_ne_zero.mpr hdeg) h rfl
      exact ⟨n + 1, by simpa only [Function.iterate_succ_apply] using hn,
        by simpa only [Function.iterate_succ_apply] using hsimple⟩
    · exact ⟨0, ht, h⟩

private theorem product_root_has_simple_factor {σ : Type*} {P : Finset (Vertical σ)}
    {a b t : ℝ} {x : σ → ℝ}
    (hD : ∀ q ∈ derivativeFamily P a b, HasConstantLeadingCoeff q)
    (ht : (specialize (derivativeProduct P a b) x).IsRoot t) :
    ∃ q ∈ derivativeFamily P a b,
      (specialize q x).IsRoot t ∧ (specialize q x).derivative.eval t ≠ 0 := by
  obtain ⟨p, hp, hroot⟩ := product_isRoot_iff.mp ht
  obtain ⟨n, hn, hs⟩ := exists_simple_derivative_root ((hD p hp).specialize_ne_zero x) hroot
  rw [show derivative^[n] (specialize p x) = specialize (derivative^[n] p) x from
    iterate_derivative_map _ _ _] at hn hs
  rcases iterate_derivative_of_family hp n with hm | ⟨c, hc⟩
  · exact ⟨_, hm, hn, hs⟩
  · simp [hc] at hs

private theorem SameSign.trans {r s t : ℝ} (h : SameSign r s) (h' : SameSign s t) :
    SameSign r t :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

private theorem sameSign_on_band {σ A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {p : Vertical σ} {f : A → σ → ℝ} (hf : Continuous f)
    {l u : A → ℝ} (hl : Continuous l) (hu : Continuous u) (hlu : ∀ x, l x < u x)
    (hn : ∀ x t, t ∈ Ioo (l x) (u x) → (specialize p (f x)).eval t ≠ 0)
    (x y : A) {s t : ℝ} (hs : s ∈ Ioo (l x) (u x)) (ht : t ∈ Ioo (l y) (u y)) :
    SameSign ((specialize p (f x)).eval s) ((specialize p (f y)).eval t) := by
  let center (x : A) := (l x + u x) / 2
  have hc (x : A) : center x ∈ Ioo (l x) (u x) := by
    have h := hlu x
    exact ⟨by dsimp [center]; linarith, by dsimp [center]; linarith⟩
  have hg : Continuous fun x => (specialize p (f x)).eval (center x) :=
    (continuous_specialized_eval p 0).comp (hf.prodMk ((hl.add hu).div_const 2))
  have hcenter := sameSign_of_locally_constant_zero hg (fun x h => (hn x _ (hc x) h).elim) x y
  have hfiber (x : A) (v w : Ioo (l x) (u x)) :
      SameSign ((specialize p (f x)).eval v.val) ((specialize p (f x)).eval w.val) := by
    have : PreconnectedSpace (Ioo (l x) (u x)) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
    have hcont : Continuous fun z : Ioo (l x) (u x) => (specialize p (f x)).eval z.val :=
      (continuous_specialized_eval p 0).comp (continuous_const.prodMk continuous_subtype_val)
    exact sameSign_of_locally_constant_zero hcont
      (fun z hz => (hn x z.val z.property hz).elim) v w
  exact (hfiber x ⟨s, hs⟩ ⟨center x, hc x⟩).trans
    (hcenter.trans (hfiber y ⟨center y, hc y⟩ ⟨t, ht⟩))

private structure PieceSections {σ : Type*} (P : Finset (Vertical σ))
    (a b : ℝ) (S : Set (σ → ℝ)) where
  count : ℕ
  level : Fin (count + 2) → closure S → Icc a b
  continuous (k) : Continuous (level k)
  monotone (x : closure S) : Monotone fun k => level k x
  strict (x : S) : StrictMono fun k => level k (Set.inclusion subset_closure x)
  endpoints (x : closure S) : (level 0 x).val = a ∧ (level (Fin.last (count + 1)) x).val = b
  root (k) (x : closure S) : (specialize (derivativeProduct P a b) x.val).IsRoot (level k x).val
  enumerate (x : S) (t : ℝ) :
    (∃ k, (level k (Set.inclusion subset_closure x)).val = t) ↔
      t ∈ Icc a b ∧ (specialize (derivativeProduct P a b) x.val).IsRoot t
  graph_sign (p : Vertical σ) (hp : p ∈ P) (k) (x y : S) :
    SameSign ((specialize p x.val).eval (level k (Set.inclusion subset_closure x)).val)
      ((specialize p y.val).eval (level k (Set.inclusion subset_closure y)).val)
  band_sign (p : Vertical σ) (hp : p ∈ P) (k : Fin (count + 1)) (x y : S) (s t : ℝ)
    (hs : s ∈ Ioo (level k.castSucc (Set.inclusion subset_closure x)).val
      (level k.succ (Set.inclusion subset_closure x)).val)
    (ht : t ∈ Ioo (level k.castSucc (Set.inclusion subset_closure y)).val
      (level k.succ (Set.inclusion subset_closure y)).val) :
    SameSign ((specialize p x.val).eval s) ((specialize p y.val).eval t)

private theorem exists_pieceSections {σ : Type*} {P : Finset (Vertical σ)}
    {a b : ℝ} (hab : a < b) {S : Set (σ → ℝ)} (hS : S.Nonempty)
    (hconn : IsPreconnected S) (hP : ∀ p ∈ P, HasConstantLeadingCoeff p)
    (hF : HasConstantLeadingCoeff (derivativeProduct P a b))
    (hcount : ∀ x y : S, (complexRoots (derivativeProduct P a b) x.val).ncard =
      (complexRoots (derivativeProduct P a b) y.val).ncard) :
    Nonempty (PieceSections P a b S) := by
  classical
  have : Nonempty S := hS.to_subtype
  have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hconn
  let F := derivativeProduct P a b
  have hD := derivativeFamily_leadingCoeff hP a b
  have ha (x : S) : (specialize F x.val).IsRoot a :=
    product_isRoot_iff.mpr ⟨_, mem_derivativeFamily.mpr (Or.inl rfl), cutoff_isRoot x.val a⟩
  have hb (x : S) : (specialize F x.val).IsRoot b :=
    product_isRoot_iff.mpr ⟨_, mem_derivativeFamily.mpr (Or.inr (Or.inl rfl)), cutoff_isRoot x.val b⟩
  obtain ⟨m, h, hc, hs, hend, henum⟩ :=
    boundedRoots_enumerate hF continuous_subtype_val hab ha hb hcount
  have henum' (x : S) (t : ℝ) :
      (∃ k, (h k x).val = t) ↔ t ∈ Icc a b ∧ (specialize F x.val).IsRoot t :=
    (henum x t).trans (mem_boundedRoots hF)
  have hroot (k) (x : S) : (specialize F x.val).IsRoot (h k x).val :=
    ((henum' x _).mp ⟨k, rfl⟩).2
  have hsign (k) (p : Vertical σ) (hp : p ∈ derivativeFamily P a b) (x y : S) :
      SameSign ((specialize p x.val).eval (h k x).val) ((specialize p y.val).eval (h k y).val) :=
    factor_sameSign_on_section hF (hD p hp) continuous_subtype_val
      (fun z => complexRoots_subset_product hp (hD p hp) hF z.val) hcount
      (continuous_subtype_val.comp (hc k)) (hroot k) x y
  let x₀ : S := Classical.choice ‹Nonempty S›
  choose H hH hHroot hExt using fun k => extend_section x₀ hD (hroot k) (hsign k)
  have hdense : DenseRange (Set.inclusion (subset_closure : S ⊆ closure S)) :=
    (denseRange_inclusion_iff subset_closure).mpr Subset.rfl
  have hcont (k) : Continuous (fun x => (H k x).val) :=
    continuous_subtype_val.comp (hH k)
  have hmem (p : Vertical σ) (hp : p ∈ P) : p ∈ derivativeFamily P a b :=
    iterate_derivative_mem hp 0 (hP p hp).ne_zero
  refine ⟨⟨m, H, hH, ?_, ?_, ?_, hHroot, ?_, ?_, ?_⟩⟩
  · intro x k l hkl
    change (H k x).val ≤ (H l x).val
    refine hdense.induction_on x (isClosed_le (hcont k) (hcont l)) ?_
    intro y
    rw [hExt k y, hExt l y]
    exact (hs y).monotone hkl
  · intro x k l hkl
    change H k (Set.inclusion subset_closure x) < H l (Set.inclusion subset_closure x)
    rw [hExt k x, hExt l x]
    exact hs x hkl
  · intro x
    refine hdense.induction_on x
      ((isClosed_eq (hcont 0) continuous_const).inter
        (isClosed_eq (hcont (Fin.last (m + 1))) continuous_const)) ?_
    intro y
    rw [hExt 0 y, hExt (Fin.last (m + 1)) y]
    exact hend y
  · intro x t
    simpa only [hExt] using henum' x t
  · intro p hp k x y
    simpa only [hExt] using hsign k p (hmem p hp) x y
  · intro p hp k x y s t hxs hyt
    have hxs' : s ∈ Ioo (h k.castSucc x).val (h k.succ x).val := by
      simpa only [hExt] using hxs
    have hyt' : t ∈ Ioo (h k.castSucc y).val (h k.succ y).val := by
      simpa only [hExt] using hyt
    apply sameSign_on_band continuous_subtype_val
      (continuous_subtype_val.comp (hc k.castSucc)) (continuous_subtype_val.comp (hc k.succ))
      (fun z => hs z (Fin.castSucc_lt_succ (i := k))) _ x y hxs' hyt'
    intro z r hr hpr
    change (h k.castSucc z).val < r ∧ r < (h k.succ z).val at hr
    have hFr : (specialize F z.val).IsRoot r := product_isRoot_iff.mpr ⟨p, hmem p hp, hpr⟩
    have hrI : r ∈ Icc a b := ⟨(h k.castSucc z).property.1.trans hr.1.le,
      hr.2.le.trans (h k.succ z).property.2⟩
    obtain ⟨l, hel⟩ := (henum' z r).mpr ⟨hrI, hFr⟩
    rcases Fin.succ_le_or_le_castSucc l k with hl | hl
    · exact (not_lt_of_ge (show (h k.succ z).val ≤ (h l z).val from (hs z).monotone hl))
        (hel.trans_lt hr.2)
    · exact (not_lt_of_ge (show (h l z).val ≤ (h k.castSucc z).val from (hs z).monotone hl))
        (hr.1.trans_eq hel.symm)

/-- Each interior root on the boundary of a piece persists as a real root of a derivative
factor. The finitely many extended sections therefore still cover every bounded real root. -/
private theorem PieceSections.cover_closure {σ : Type*} {P : Finset (Vertical σ)}
    {a b : ℝ} {S : Set (σ → ℝ)} (R : PieceSections P a b S)
    (hD : ∀ q ∈ derivativeFamily P a b, HasConstantLeadingCoeff q)
    (x : closure S) {t : ℝ} (htI : t ∈ Icc a b)
    (ht : (specialize (derivativeProduct P a b) x.val).IsRoot t) :
    ∃ k, (R.level k x).val = t := by
  rcases eq_or_ne t a with rfl | hne_a
  · exact ⟨0, (R.endpoints x).1⟩
  rcases eq_or_ne t b with rfl | hne_b
  · exact ⟨Fin.last _, (R.endpoints x).2⟩
  have hta : a < t := lt_of_le_of_ne htI.1 hne_a.symm
  have htb : t < b := lt_of_le_of_ne htI.2 hne_b
  by_contra! havoid
  have hsep : ∀ᶠ δ : ℝ in 𝓝 0, ∀ k, δ < |(R.level k x).val - t| :=
    eventually_all.mpr fun k =>
      eventually_lt_nhds (abs_pos.mpr (sub_ne_zero.mpr (havoid k)))
  have hδ := ((eventually_lt_nhds (sub_pos.mpr hta)).and
    ((eventually_lt_nhds (sub_pos.mpr htb)).and hsep)).filter_mono
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  obtain ⟨δ, δpos, hδa, hδb, hδsep⟩ := (eventually_mem_nhdsWithin.and hδ).exists
  have hev : ∀ᶠ y : closure S in 𝓝 x, ∀ k, δ < |(R.level k y).val - t| := by
    refine eventually_all.mpr fun k => ?_
    have hcont : Continuous fun y => |(R.level k y).val - t| :=
      ((continuous_subtype_val.comp (R.continuous k)).sub continuous_const).abs
    exact continuousAt_const.eventually_lt hcont.continuousAt (hδsep k)
  obtain ⟨p, hp, hpIsRoot, hsimple⟩ := product_root_has_simple_factor hD ht
  have hcont (r : ℝ) : ContinuousAt (fun y : closure S => (specialize p y.val).eval r) x :=
    ((continuous_specialized_eval p 0).comp
      (continuous_subtype_val.prodMk continuous_const)).continuousAt
  have hsimple_near := eventually_exists_real_root_near_of_derivative_ne_zero
    (fun y : closure S => specialize p y.val) x t hpIsRoot hsimple hcont δpos
  have hdense : DenseRange (Set.inclusion (subset_closure : S ⊆ closure S)) :=
    (denseRange_inclusion_iff subset_closure).mpr Subset.rfl
  obtain ⟨y, ⟨z, rfl⟩, hy, r, htδ, hr⟩ :=
    ((mem_closure_iff_frequently.mp (hdense x)).and_eventually (hev.and hsimple_near)).exists
  have hrI : r ∈ Icc a b := ⟨by linarith [htδ.1], by linarith [htδ.2]⟩
  have hFr : (specialize (derivativeProduct P a b) z.val).IsRoot r :=
    product_isRoot_iff.mpr ⟨p, hp, hr⟩
  obtain ⟨k, hk⟩ := (R.enumerate z r).mpr ⟨hrI, hFr⟩
  have hdist := hy k
  rw [hk] at hdist
  exact (not_lt_of_ge hdist.le) (abs_lt.mpr ⟨by linarith [htδ.1], by linarith [htδ.2]⟩)

private theorem PieceSections.compatible {σ : Type*} {P : Finset (Vertical σ)}
    {a b : ℝ} {S T : Set (σ → ℝ)} (R : PieceSections P a b S)
    (R' : PieceSections P a b T) (hT : T.Nonempty) (hconn : IsPreconnected T)
    (hD : ∀ q ∈ derivativeFamily P a b, HasConstantLeadingCoeff q)
    (hTS : T ⊆ closure S) :
    ∃ q : Fin (R.count + 2) → Fin (R'.count + 2), Monotone q ∧ Function.Surjective q ∧
      ∀ k (x : closure T), R.level k (Set.inclusion (closure_minimal hTS isClosed_closure) x) =
        R'.level (q k) x := by
  classical
  have : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp hconn
  let up : closure T → closure S := Set.inclusion (closure_minimal hTS isClosed_closure)
  let incl : T → closure T := Set.inclusion subset_closure
  let upper (k : Fin (R.count + 2)) (x : T) := R.level k (up (incl x))
  let lower (j : Fin (R'.count + 2)) (x : T) := R'.level j (incl x)
  have hup : Continuous up := continuous_inclusion (closure_minimal hTS isClosed_closure)
  have hupper (k) : Continuous (upper k) :=
    (R.continuous k).comp (hup.comp (continuous_inclusion subset_closure))
  have hlower (j) : Continuous (lower j) := (R'.continuous j).comp (continuous_inclusion _)
  have hmatch (k) (x : T) : ∃ j, lower j x = upper k x := by
    obtain ⟨j, hj⟩ := (R'.enumerate x _).mpr ⟨(upper k x).property, R.root k (up (incl x))⟩
    exact ⟨j, Subtype.ext hj⟩
  choose kAt hkAt using hmatch
  have hloc (k) : IsLocallyConstant (kAt k) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    have hev : ∀ᶠ y in 𝓝 x, ∀ j, j ≠ kAt k x → lower j y ≠ upper k y := by
      refine eventually_all.mpr fun j => ?_
      by_cases hj : j = kAt k x
      · exact Eventually.of_forall fun _ hn => (hn hj).elim
      have hne : lower j x ≠ upper k x := by
        rw [← hkAt k x]
        exact (R'.strict x).injective.ne hj
      have hopen : IsOpen {y | lower j y ≠ upper k y} :=
        (isClosed_eq (hlower j) (hupper k)).isOpen_compl
      have he : ∀ᶠ y in 𝓝 x, lower j y ≠ upper k y := hopen.mem_nhds hne
      exact he.mono fun _ h _ => h
    filter_upwards [hev] with y hy
    by_contra hne
    exact hy (kAt k y) hne (hkAt k y)
  let x₀ : T := Classical.choice hT.to_subtype
  let q (k : Fin (R.count + 2)) := kAt k x₀
  have hq (k) (x : T) : lower (q k) x = upper k x := by
    rw [show q k = kAt k x from (hloc k).apply_eq_of_preconnectedSpace x₀ x]
    exact hkAt k x
  refine ⟨q, ?_, ?_, ?_⟩
  · intro k l hkl
    apply (R'.strict x₀).le_iff_le.mp
    change lower (q k) x₀ ≤ lower (q l) x₀
    rw [hq k, hq l]
    exact R.monotone (up (incl x₀)) hkl
  · intro j
    let t := lower j x₀
    obtain ⟨k, hk⟩ := R.cover_closure hD (up (incl x₀)) t.property
      (R'.root j (incl x₀))
    refine ⟨k, (R'.strict x₀).injective ?_⟩
    change lower (q k) x₀ = lower j x₀
    rw [hq k]
    exact Subtype.ext hk
  · intro k x
    have hdense : DenseRange incl := (denseRange_inclusion_iff subset_closure).mpr Subset.rfl
    have he := hdense.equalizer ((R.continuous k).comp hup)
      (R'.continuous (q k)) (funext fun y => (hq k y).symm)
    exact congrFun he x

/-- The bounded real roots of the derivative product give compatible continuous sections
on the closures of the pieces. -/
theorem realPolynomialRootSections :
    RealPolynomialRootSectionsSpecs.RealPolynomialRootSections.{u,v} := by
  classical
  intro σ _ α _ P a b C hab hP hC hconn F hcount
  have hF : HasConstantLeadingCoeff (derivativeProduct P a b) :=
    derivativeProduct_leadingCoeff σ P a b hab hP
  let R (i : α) : PieceSections P a b (C i) :=
    Classical.choice (exists_pieceSections hab (hC i) (hconn i) hP hF (hcount i))
  refine ⟨fun i => (R i).count, fun i => (R i).level, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => (R i).continuous
  · exact fun i => (R i).monotone
  · exact fun i => (R i).strict
  · exact fun i => (R i).endpoints
  · intro i x t
    exact ((R i).enumerate x t).trans <| and_congr_right fun _ => by
      rw [mem_rootSet_of_ne (hF.specialize_ne_zero x.val), IsRoot, coe_aeval_eq_eval]
  · rintro i k p hp _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact (R i).graph_sign p hp k x y
  · intro i k p hp z hz w hw
    obtain ⟨x, hx, hxl, hxu⟩ := hz
    obtain ⟨y, hy, hyl, hyu⟩ := hw
    change SameSign ((specialize p z.1).eval z.2) ((specialize p w.1).eval w.2)
    rw [← hx, ← hy]
    exact (R i).band_sign p hp k x y z.2 w.2 ⟨hxl, hxu⟩ ⟨hyl, hyu⟩
  · exact fun i j => (R i).compatible (R j) (hC j) (hconn j) (derivativeFamily_leadingCoeff hP a b)

end RepTheorySurvey.Geometric.RealPolynomialRootSections
