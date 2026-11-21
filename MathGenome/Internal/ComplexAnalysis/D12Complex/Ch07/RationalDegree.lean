import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.RationalDegree
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.RationalInfinity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.AlgebraicClosure
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open Polynomial Filter Set
open scoped Topology Classical
namespace D12Complex.RationalDegree
open RationalInfinity
open LocalQuotientsArithmetic hiding fill
open Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects (fill)
open private rational_meromorphic reciprocal_meromorphic infinity_expression
  from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.RationalInfinity

/-- The scalar expression of a sphere map in the appropriate source chart. -/
def sourceFunction (F : RiemannSphere → RiemannSphere) (p : RiemannSphere) : ℂ → ℂ :=
  if p = sphereInfty then scalarFinitePart (F ∘ infinityParametrization)
  else scalarFinitePart (F ∘ sphereFinite)

def sourceCenter (p : RiemannSphere) : ℂ :=
  if p = sphereInfty then 0 else finiteCoordinate p

/-- Zero order of F-c, or pole order of F when the target is infinity.
The positive part is zero away from the fiber. -/
def localMultiplicity (F : RiemannSphere → RiemannSphere)
    (c p : RiemannSphere) : ℕ :=
  if c = sphereInfty then
    (-(meromorphicOrderAt (sourceFunction F p) (sourceCenter p)).untopD 0).toNat
  else
    ((meromorphicOrderAt (fun z => sourceFunction F p z - finiteCoordinate c)
      (sourceCenter p)).untopD 0).toNat

/-- The usual algebraic nonconstancy condition for P/Q with Q nonzero. -/
def Nonconstant (P Q : Polynomial ℂ) : Prop := ∀ c : ℂ, P ≠ Polynomial.C c * Q


lemma polynomial_order (P : Polynomial ℂ) (hP : P ≠ 0) (a : ℂ) :
    meromorphicOrderAt (fun z => P.eval z) a = (P.rootMultiplicity a : WithTop ℤ) := by
  rw [(AnalyticOnNhd.eval_polynomial P a (mem_univ _)).meromorphicOrderAt_eq]
  have h := PolynomialMultiplicity.polynomial_order_eq_rootMultiplicity P hP a
  change analyticOrderAt (fun z => P.eval z) a = _ at h
  rw [h]
  rfl

lemma rational_order (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0) (a : ℂ) :
    meromorphicOrderAt (rational P Q) a =
      ((P.rootMultiplicity a : ℤ) - Q.rootMultiplicity a : WithTop ℤ) := by
  change meromorphicOrderAt ((fun z => P.eval z) / (fun z => Q.eval z)) a = _
  rw [meromorphicOrderAt_div
    (AnalyticOnNhd.eval_polynomial P a (mem_univ _)).meromorphicAt
    (AnalyticOnNhd.eval_polynomial Q a (mem_univ _)).meromorphicAt,
    polynomial_order P hP a, polynomial_order Q hQ a]
  rfl

lemma no_common_root (P Q : Polynomial ℂ) (h : IsRelPrime P Q) (a : ℂ) :
    P.eval a ≠ 0 ∨ Q.eval a ≠ 0 := by
  obtain ⟨u, v, huv⟩ := isRelPrime_iff_isCoprime.mp h
  by_contra! hh
  have he := congrArg (fun R : Polynomial ℂ => R.eval a) huv
  simp [hh.1, hh.2] at he

lemma source_germ_finite (P Q : Polynomial ℂ) (a : ℂ) :
    sourceFunction (extension P Q) (sphereFinite a) =ᶠ[𝓝[≠] a] rational P Q := by
  have he : sourceFunction (extension P Q) (sphereFinite a) =
      scalarFinitePart (fill (rational P Q)) := by
    simp only [sourceFunction, show sphereFinite a ≠ sphereInfty from OnePoint.coe_ne_infty a]
    rfl
  rw [he]
  exact finitePart_fill_germ (rational_meromorphic P Q a)

lemma source_germ_infty (P Q : Polynomial ℂ) :
    sourceFunction (extension P Q) sphereInfty =ᶠ[𝓝[≠] 0]
      reciprocalPullback (rational P Q) := by
  simp only [sourceFunction, infinity_expression]
  exact finitePart_fill_germ (reciprocal_meromorphic P Q)

lemma fill_zero_iff {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) :
    fill f a = sphereFinite 0 ↔ 0 < meromorphicOrderAt f a := by
  by_cases hn : meromorphicOrderAt f a < 0
  · simp [fill, hn, not_lt.mpr hn.le, sphereFinite, sphereInfty]
  · have hnonneg := le_of_not_gt hn
    rw [fill, ite_eq_right hn]
    have he : sphereFinite (toMeromorphicNFAt f a a) = sphereFinite 0 ↔
        toMeromorphicNFAt f a a = 0 := sphereFinite_injective.eq_iff
    rw [he, ← not_ne_iff, ← hf.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero]
    exact ⟨fun h => lt_of_le_of_ne hnonneg (Ne.symm h), fun h => h.ne'⟩

lemma fill_limit_iff {f : ℂ → ℂ} {a c : ℂ} (hf : MeromorphicAt f a) :
    fill f a = sphereFinite c ↔ Tendsto f (𝓝[≠] a) (𝓝 c) := by
  constructor
  · intro he
    have hn : 0 ≤ meromorphicOrderAt f a := by
      by_contra h
      have hn := lt_of_not_ge h
      simp [fill, hn, sphereFinite, sphereInfty] at he
    have hg := hf.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp hn
    have hv : toMeromorphicNFAt f a a = c := by
      apply sphereFinite_injective
      simpa [fill, not_lt.mpr hn] using he
    rw [← hv]
    exact hg.continuousAt.continuousWithinAt.tendsto.congr' hf.eq_nhdsNE_toMeromorphicNFAt.symm
  · intro ht
    have hn := (tendsto_nhds_iff_meromorphicOrderAt_nonneg hf).mp ⟨c, ht⟩
    have hg := hf.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp hn
    have hv := tendsto_nhds_unique
      (hg.continuousAt.continuousWithinAt.tendsto.congr' hf.eq_nhdsNE_toMeromorphicNFAt.symm) ht
    simp [fill, not_lt.mpr hn, hv]

lemma fill_sub_zero_iff {f : ℂ → ℂ} {a c : ℂ} (hf : MeromorphicAt f a) :
    0 < meromorphicOrderAt (fun z => f z - c) a ↔ fill f a = sphereFinite c := by
  have hsub : MeromorphicAt (fun z => f z - c) a := hf.sub analyticAt_const.meromorphicAt
  rw [← tendsto_zero_iff_meromorphicOrderAt_pos hsub, fill_limit_iff hf]
  constructor
  · intro h
    simpa using h.add_const c
  · intro h
    simpa using h.sub_const c

lemma polynomial_eventually_nonzero (Q : Polynomial ℂ) (hQ : Q ≠ 0) (a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, Q.eval z ≠ 0 :=
  LocalZeroFactorization.finiteOrder_isolated _ _ _
    (PolynomialMultiplicity.polynomial_hasFiniteOrder Q hQ a)

open private reverse_eval from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.RationalInfinity
lemma reciprocal_eventually_nonzero (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∀ᶠ w in 𝓝[≠] (0 : ℂ), Q.eval w⁻¹ ≠ 0 := by
  have h0 : Q.reverse.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQ
  have ht := (Q.reverse.continuousAt (a := (0 : ℂ))).eventually_ne h0
  filter_upwards [ht.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hw0
  rw [reverse_eval Q hw0]
  exact div_ne_zero hw (pow_ne_zero _ hw0)

lemma subtract_rational (P Q : Polynomial ℂ) (c z : ℂ) (hQ : Q.eval z ≠ 0) :
    rational P Q z - c = rational (P - C c * Q) Q z := by
  simp only [rational, eval_sub, eval_mul, eval_C]
  field_simp

lemma difference_germ_finite (P Q : Polynomial ℂ) (hQ : Q ≠ 0) (c a : ℂ) :
    (fun z => sourceFunction (extension P Q) (sphereFinite a) z - c)
      =ᶠ[𝓝[≠] a] rational (P - C c * Q) Q := by
  filter_upwards [source_germ_finite P Q a, polynomial_eventually_nonzero Q hQ a]
    with z hz hQz
  rw [hz, subtract_rational P Q c z hQz]

lemma difference_germ_infty (P Q : Polynomial ℂ) (hQ : Q ≠ 0) (c : ℂ) :
    (fun w => sourceFunction (extension P Q) sphereInfty w - c)
      =ᶠ[𝓝[≠] 0] reciprocalPullback (rational (P - C c * Q) Q) := by
  filter_upwards [source_germ_infty P Q, reciprocal_eventually_nonzero Q hQ]
    with w hw hQw
  rw [hw]
  exact subtract_rational P Q c w⁻¹ hQw

lemma root_difference_positive (P Q : Polynomial ℂ) (_hP : P ≠ 0)
    (_hQ : Q ≠ 0) (hrel : IsRelPrime P Q) (a : ℂ) :
    ((P.rootMultiplicity a : ℤ) - Q.rootMultiplicity a).toNat = P.rootMultiplicity a := by
  rcases no_common_root P Q hrel a with hp | hq
  · have hr : P.rootMultiplicity a = 0 := rootMultiplicity_eq_zero hp
    rw [hr]
    omega
  · have hr : Q.rootMultiplicity a = 0 := rootMultiplicity_eq_zero hq
    simp [hr]

lemma multiplicity_finite_target_finite (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hrel : IsRelPrime P Q) (c a : ℂ) (hN : P - C c * Q ≠ 0) :
    localMultiplicity (extension P Q) (sphereFinite c) (sphereFinite a) =
      (P - C c * Q).rootMultiplicity a := by
  have hr : IsRelPrime (P - C c * Q) Q :=
    IsRelPrime.sub_mul_right_left_iff.mpr hrel
  simp only [localMultiplicity, show sphereFinite c ≠ sphereInfty from OnePoint.coe_ne_infty c,
    ↓reduceIte, sourceCenter, show sphereFinite a ≠ sphereInfty from OnePoint.coe_ne_infty a,
    finiteCoordinate_sphereFinite]
  rw [meromorphicOrderAt_congr (difference_germ_finite P Q hQ c a),
    rational_order _ _ hN hQ]
  simpa only [← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_natCast, WithTop.untopD_coe] using root_difference_positive _ _ hN hQ hr a

lemma multiplicity_finite_target_infty (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hrel : IsRelPrime P Q) (c : ℂ) (hN : P - C c * Q ≠ 0) :
    localMultiplicity (extension P Q) (sphereFinite c) sphereInfty =
      Q.natDegree - (P - C c * Q).natDegree := by
  have hr : IsRelPrime (P - C c * Q) Q :=
    IsRelPrime.sub_mul_right_left_iff.mpr hrel
  simp only [localMultiplicity, show sphereFinite c ≠ sphereInfty from OnePoint.coe_ne_infty c,
    ↓reduceIte, sourceCenter, finiteCoordinate_sphereFinite]
  rw [meromorphicOrderAt_congr (difference_germ_infty P Q hQ c),
    order_at_infinity _ _ hN hQ hr]
  simp only [← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.untopD_coe]
  omega

lemma multiplicity_infty_target_finite (P Q : Polynomial ℂ) (hP : P ≠ 0)
    (hQ : Q ≠ 0) (hrel : IsRelPrime P Q) (a : ℂ) :
    localMultiplicity (extension P Q) sphereInfty (sphereFinite a) =
      Q.rootMultiplicity a := by
  simp only [localMultiplicity, ↓reduceIte, sourceCenter,
    show sphereFinite a ≠ sphereInfty from OnePoint.coe_ne_infty a]
  rw [finiteCoordinate_sphereFinite, meromorphicOrderAt_congr (source_germ_finite P Q a),
    rational_order P Q hP hQ a]
  simpa only [← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_natCast, WithTop.untopD_coe, neg_sub] using
    root_difference_positive Q P hQ hP hrel.symm a

lemma multiplicity_infty_target_infty (P Q : Polynomial ℂ) (hP : P ≠ 0)
    (hQ : Q ≠ 0) (hrel : IsRelPrime P Q) :
    localMultiplicity (extension P Q) sphereInfty sphereInfty =
      P.natDegree - Q.natDegree := by
  simp only [localMultiplicity, ↓reduceIte, sourceCenter]
  rw [meromorphicOrderAt_congr (source_germ_infty P Q),
    order_at_infinity P Q hP hQ hrel]
  simp only [← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.untopD_coe]
  omega

lemma source_meromorphic (P Q : Polynomial ℂ) (p : RiemannSphere) :
    MeromorphicAt (sourceFunction (extension P Q) p) (sourceCenter p) := by
  rcases sphere_eq_infty_or_finite p with rfl | ⟨a, rfl⟩
  · simp only [sourceCenter, ↓reduceIte]
    exact (reciprocal_meromorphic P Q).congr (source_germ_infty P Q).symm
  · simp only [sourceCenter, show sphereFinite a ≠ sphereInfty from OnePoint.coe_ne_infty a,
      ↓reduceIte, finiteCoordinate_sphereFinite]
    exact (rational_meromorphic P Q a).congr (source_germ_finite P Q a).symm

lemma source_fill (P Q : Polynomial ℂ) (p : RiemannSphere) :
    fill (sourceFunction (extension P Q) p) (sourceCenter p) = extension P Q p := by
  rcases sphere_eq_infty_or_finite p with rfl | ⟨a, rfl⟩
  · simp only [sourceCenter, ↓reduceIte]
    change fill _ (0 : ℂ) = fill (reciprocalPullback (rational P Q)) 0
    exact fill_congr _ _ _ (source_germ_infty P Q)
  · simp only [sourceCenter, show sphereFinite a ≠ sphereInfty from OnePoint.coe_ne_infty a,
      ↓reduceIte, finiteCoordinate_sphereFinite]
    exact fill_congr _ _ _ (source_germ_finite P Q a)

lemma numerator_nonzero (P Q : Polynomial ℂ) (hn : Nonconstant P Q) (c : ℂ) :
    P - C c * Q ≠ 0 := sub_ne_zero.mpr (hn c)

lemma nonconstant_numerator_ne_zero (P Q : Polynomial ℂ) (hn : Nonconstant P Q) :
    P ≠ 0 := by simpa using hn 0

lemma source_order_finite (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hrel : IsRelPrime P Q) (p : RiemannSphere) :
    meromorphicOrderAt (sourceFunction (extension P Q) p) (sourceCenter p) ≠ ⊤ := by
  rcases sphere_eq_infty_or_finite p with rfl | ⟨a, rfl⟩
  · simp only [sourceCenter, ↓reduceIte]
    rw [meromorphicOrderAt_congr (source_germ_infty P Q),
      order_at_infinity P Q hP hQ hrel]
    simp only [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact WithTop.coe_ne_top
  · simp only [sourceCenter, show sphereFinite a ≠ sphereInfty from OnePoint.coe_ne_infty a,
      ↓reduceIte, finiteCoordinate_sphereFinite]
    rw [meromorphicOrderAt_congr (source_germ_finite P Q a), rational_order P Q hP hQ a]
    change (((P.rootMultiplicity a : ℤ) - Q.rootMultiplicity a : ℤ) : WithTop ℤ) ≠ ⊤
    exact WithTop.coe_ne_top

lemma difference_order_finite (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hrel : IsRelPrime P Q) (hn : Nonconstant P Q) (c : ℂ) (p : RiemannSphere) :
    meromorphicOrderAt (fun z => sourceFunction (extension P Q) p z - c)
      (sourceCenter p) ≠ ⊤ := by
  have hN := numerator_nonzero P Q hn c
  have hr : IsRelPrime (P - C c * Q) Q := IsRelPrime.sub_mul_right_left_iff.mpr hrel
  rcases sphere_eq_infty_or_finite p with rfl | ⟨a, rfl⟩
  · simp only [sourceCenter, ↓reduceIte]
    rw [meromorphicOrderAt_congr (difference_germ_infty P Q hQ c),
      order_at_infinity _ _ hN hQ hr]
    simp only [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact WithTop.coe_ne_top
  · simp only [sourceCenter, show sphereFinite a ≠ sphereInfty from OnePoint.coe_ne_infty a,
      ↓reduceIte, finiteCoordinate_sphereFinite]
    rw [meromorphicOrderAt_congr (difference_germ_finite P Q hQ c a),
      rational_order _ _ hN hQ a]
    change (((((P - C c * Q).rootMultiplicity a : ℤ) - Q.rootMultiplicity a) : ℤ) : WithTop ℤ) ≠ ⊤
    exact WithTop.coe_ne_top

lemma multiplicity_pos_iff (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hrel : IsRelPrime P Q) (hn : Nonconstant P Q) (c p : RiemannSphere) :
    0 < localMultiplicity (extension P Q) c p ↔ extension P Q p = c := by
  have hf := source_meromorphic P Q p
  have hv := source_fill P Q p
  rcases sphere_eq_infty_or_finite c with rfl | ⟨b, rfl⟩
  · have hfin := source_order_finite P Q (nonconstant_numerator_ne_zero P Q hn) hQ hrel p
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
    rw [← hv, show fill (sourceFunction (extension P Q) p) (sourceCenter p) = sphereInfty ↔
      meromorphicOrderAt (sourceFunction (extension P Q) p) (sourceCenter p) < 0 from
      LocalQuotientsArithmetic.fill_eq_infty_iff _ _]
    simp only [localMultiplicity, ↓reduceIte, ← hk, WithTop.untopD_coe]
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_lt_coe]
    omega
  · have hfin := difference_order_finite P Q hQ hrel hn b p
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
    rw [← hv, ← fill_sub_zero_iff hf]
    simp only [localMultiplicity, show sphereFinite b ≠ sphereInfty from OnePoint.coe_ne_infty b,
      ↓reduceIte, finiteCoordinate_sphereFinite, ← hk, WithTop.untopD_coe]
    rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_lt_coe]
    omega

/-- The total degree is unchanged by subtracting a finite target. -/
lemma max_degree_sub (P Q : Polynomial ℂ) (c : ℂ) :
    max (P - C c * Q).natDegree Q.natDegree = max P.natDegree Q.natDegree := by
  have hmul : (C c * Q).natDegree ≤ Q.natDegree := by
    simpa using natDegree_mul_le (p := C c) (q := Q)
  have hle : (P - C c * Q).natDegree ≤ max P.natDegree Q.natDegree :=
    (natDegree_sub_le _ _).trans (max_le_max_left _ hmul)
  have hrev : P.natDegree ≤ max (P - C c * Q).natDegree Q.natDegree := by
    have he : P = (P - C c * Q) + C c * Q := by ring
    calc
      P.natDegree = ((P - C c * Q) + C c * Q).natDegree := congrArg natDegree he
      _ ≤ max (P - C c * Q).natDegree Q.natDegree :=
        (natDegree_add_le _ _).trans (max_le_max_left _ hmul)
  omega

/-- Finite polynomial roots plus the exact zero order in the reciprocal chart. -/
def rootMultiset (P Q : Polynomial ℂ) : Multiset RiemannSphere :=
  P.roots.map sphereFinite + Multiset.replicate (Q.natDegree - P.natDegree) sphereInfty

lemma rootMultiset_card (P Q : Polynomial ℂ) :
    (rootMultiset P Q).card = max P.natDegree Q.natDegree := by
  have hc := (AlgebraicClosure.polynomial_splits P).natDegree_eq_card_roots
  simp only [rootMultiset, Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
  omega

lemma rootMultiset_count_finite (P Q : Polynomial ℂ) (a : ℂ) :
    (rootMultiset P Q).count (sphereFinite a) = P.rootMultiplicity a := by
  simp only [rootMultiset, Multiset.count_add,
    Multiset.count_map_eq_count' sphereFinite P.roots sphereFinite_injective,
    Multiset.count_replicate, show sphereInfty ≠ sphereFinite a from
      (OnePoint.coe_ne_infty a).symm, ↓reduceIte, add_zero, count_roots]

lemma rootMultiset_count_infty (P Q : Polynomial ℂ) :
    (rootMultiset P Q).count sphereInfty = Q.natDegree - P.natDegree := by
  have hm : sphereInfty ∉ P.roots.map sphereFinite := by
    simp only [Multiset.mem_map, not_exists, not_and]
    intro a _
    exact OnePoint.coe_ne_infty a
  simp only [rootMultiset, Multiset.count_add, Multiset.count_eq_zero.mpr hm,
    Multiset.count_replicate_self, zero_add]

/-- Every sphere fiber, including infinity, with its actual local multiplicities. -/
theorem fiber_count : Specs.D12Complex.Ch07.RationalDegree.fiber_count_type := by
  intro P Q hQ hrel hn c
  have hP := nonconstant_numerator_ne_zero P Q hn
  rcases sphere_eq_infty_or_finite c with rfl | ⟨b, rfl⟩
  · have hc : ∀ p, (rootMultiset Q P).count p = localMultiplicity (extension P Q) sphereInfty p := by
      intro p
      rcases sphere_eq_infty_or_finite p with rfl | ⟨a, rfl⟩
      · rw [rootMultiset_count_infty, multiplicity_infty_target_infty P Q hP hQ hrel]
      · rw [rootMultiset_count_finite, multiplicity_infty_target_finite P Q hP hQ hrel]
    refine ⟨rootMultiset Q P, (rootMultiset_card Q P).trans (max_comm _ _), ?_, hc⟩
    intro p
    rw [← Multiset.count_pos, hc p, multiplicity_pos_iff P Q hQ hrel hn]
    rfl
  · have hN := numerator_nonzero P Q hn b
    have hc : ∀ p, (rootMultiset (P - C b * Q) Q).count p =
        localMultiplicity (extension P Q) (sphereFinite b) p := by
      intro p
      rcases sphere_eq_infty_or_finite p with rfl | ⟨a, rfl⟩
      · rw [rootMultiset_count_infty, multiplicity_finite_target_infty P Q hQ hrel b hN]
      · rw [rootMultiset_count_finite, multiplicity_finite_target_finite P Q hQ hrel b a hN]
    refine ⟨rootMultiset (P - C b * Q) Q,
      (rootMultiset_card _ _).trans (max_degree_sub P Q b), ?_, hc⟩
    intro p
    rw [← Multiset.count_pos, hc p, multiplicity_pos_iff P Q hQ hrel hn]
    rfl

theorem fibers_finite : Specs.D12Complex.Ch07.RationalDegree.fibers_finite_type := by
  intro P Q hQ hrel hn c
  obtain ⟨A, _, hmem, _⟩ := fiber_count P Q hQ hrel hn c
  have he : {p | Specs.D12Complex.Ch07.RationalInfinity.Objects.extension P Q p = c} = (↑A.toFinset : Set RiemannSphere) := by
    ext p
    simpa using (hmem p).symm
  rw [he]
  exact Finset.finite_toSet _

theorem zeros_poles_count : Specs.D12Complex.Ch07.RationalDegree.zeros_poles_count_type := by
  intro P Q hQ hrel hn
  exact ⟨fiber_count P Q hQ hrel hn (sphereFinite 0), fiber_count P Q hQ hrel hn sphereInfty⟩

lemma constant_extension (Q : Polynomial ℂ) (hQ : Q ≠ 0) (c : ℂ) :
    extension (C c * Q) Q = fun _ => sphereFinite c := by
  funext p
  rcases sphere_eq_infty_or_finite p with rfl | ⟨a, rfl⟩
  · change fill (reciprocalPullback (rational (C c * Q) Q)) 0 = _
    apply (fill_limit_iff (reciprocal_meromorphic (C c * Q) Q)).mpr
    apply tendsto_const_nhds.congr'
    filter_upwards [reciprocal_eventually_nonzero Q hQ] with w hw
    simp [reciprocalPullback, rational, hw]
  · change fill (rational (C c * Q) Q) a = _
    apply (fill_limit_iff (rational_meromorphic (C c * Q) Q a)).mpr
    apply tendsto_const_nhds.congr'
    filter_upwards [polynomial_eventually_nonzero Q hQ a] with z hz
    simp [rational, hz]

theorem nonconstant_iff : Specs.D12Complex.Ch07.RationalDegree.nonconstant_iff_type := by
  intro P Q hQ hrel
  constructor
  · intro hn ⟨c, hc⟩
    have hfin := fibers_finite P Q hQ hrel hn c
    have he : {p | Specs.D12Complex.Ch07.RationalInfinity.Objects.extension P Q p = c} = Set.univ := by
      simp only [hc, Set.ofPred_true]
    rw [he] at hfin
    exact Set.infinite_univ hfin
  · intro hn c he
    apply hn
    refine ⟨sphereFinite c, ?_⟩
    rw [he]
    exact constant_extension Q hQ c

theorem nonzero_constant : Specs.D12Complex.Ch07.RationalDegree.nonzero_constant_type := by
  intro c hc
  constructor
  · intro p
    exact ⟨fun h => hc (sphereFinite_injective h), OnePoint.coe_ne_infty c⟩
  · intro p
    change localMultiplicity (fun _ => sphereFinite c) (sphereFinite 0) p = 0 ∧
      localMultiplicity (fun _ => sphereFinite c) sphereInfty p = 0
    have he : sourceFunction (fun _ => sphereFinite c) p = fun _ => c := by
      funext z
      by_cases hp : p = sphereInfty <;>
        simp [sourceFunction, hp, scalarFinitePart, finiteCoordinate_sphereFinite]
    simp only [localMultiplicity, show sphereFinite 0 ≠ sphereInfty from OnePoint.coe_ne_infty 0,
      ↓reduceIte, he, finiteCoordinate_sphereFinite, sub_zero]
    simp [meromorphicOrderAt_const, hc]

theorem local_orders_finite : Specs.D12Complex.Ch07.RationalDegree.local_orders_finite_type := by
  intro P Q hQ hrel hn p
  exact ⟨source_order_finite P Q (nonconstant_numerator_ne_zero P Q hn) hQ hrel p,
    fun c => difference_order_finite P Q hQ hrel hn c p⟩

theorem fiber_total : Specs.D12Complex.Ch07.RationalDegree.fiber_total_type := by
  intro P Q hQ hrel hn c
  obtain ⟨A, hcard, hmem, hcount⟩ := fiber_count P Q hQ hrel hn c
  refine ⟨A.toFinset, fun p => ?_, ?_⟩
  · simpa using hmem p
  · simp_rw [← hcount]
    exact A.toFinset_sum_count_eq.trans hcard

end D12Complex.RationalDegree
