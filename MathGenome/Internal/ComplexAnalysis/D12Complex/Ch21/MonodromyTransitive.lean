import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.MonodromyTransitive
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.FractionFieldIrreducibility
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Order.Filter.Finite
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.AlgebraicCovering
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.SymmetricCoefficients
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.AlgebraicGrowth
import Mathlib.Algebra.Polynomial.OfFn
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.ContinuationUniqueOperations

/-! Monodromy transitivity from rational symmetric coefficients of path-component
root systems. All irreducibility hypotheses concern the original ℂ[z][w] polynomial. -/

noncomputable section
namespace D12Complex.MonodromyTransitive.FactorBridge
open Polynomial

abbrev coeffMap : Polynomial ℂ →+* RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ)

theorem monic_normalization_irreducible
    (P : Polynomial (Polynomial ℂ)) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree) :
    Irreducible (C (coeffMap P.leadingCoeff)⁻¹ * P.map coeffMap) := by
  have hQ : Irreducible (P.map coeffMap) :=
    (D12Complex.Ch21.FractionFieldIrreducibility.gauss_bridge
      P P.natDegree hP rfl hdeg).2.2.1
  have hlc : (P.map coeffMap).leadingCoeff = coeffMap P.leadingCoeff :=
    leadingCoeff_map_of_injective (IsFractionRing.injective _ _) P
  rw [mul_comm, ← hlc, irreducible_mul_leadingCoeff_inv]
  exact hQ

theorem monic_normalization_monic (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0) :
    Monic (C (coeffMap P.leadingCoeff)⁻¹ * P.map coeffMap) := by
  have hlc : (P.map coeffMap).leadingCoeff = coeffMap P.leadingCoeff :=
    leadingCoeff_map_of_injective (IsFractionRing.injective _ _) P
  rw [mul_comm, ← hlc]
  exact monic_mul_leadingCoeff_inv ((Polynomial.map_ne_zero_iff (IsFractionRing.injective _ _)).mpr hP)

theorem monic_normalization_natDegree (P : Polynomial (Polynomial ℂ)) :
    (C (coeffMap P.leadingCoeff)⁻¹ * P.map coeffMap).natDegree = P.natDegree := by
  have hlc : (P.map coeffMap).leadingCoeff = coeffMap P.leadingCoeff :=
    leadingCoeff_map_of_injective (IsFractionRing.injective _ _) P
  rw [mul_comm, ← hlc, natDegree_mul_leadingCoeff_self_inv]
  exact natDegree_map_eq_of_injective (IsFractionRing.injective _ _) P

theorem no_positive_degree_factorization
    (P : Polynomial (Polynomial ℂ)) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree)
    (A B : Polynomial (RatFunc ℂ)) (hA : 0 < A.natDegree)
    (hB : 0 < B.natDegree) :
    C (coeffMap P.leadingCoeff)⁻¹ * P.map coeffMap ≠ A * B := by
  intro h
  have hi := monic_normalization_irreducible P hP hdeg
  rcases hi.isUnit_or_isUnit h with hu | hu
  · have := natDegree_eq_zero_of_isUnit hu
    omega
  · have := natDegree_eq_zero_of_isUnit hu
    omega

open Filter

theorem ratFunc_eq_of_eventually_eval_eq (p q : RatFunc ℂ)
    (h : ∀ᶠ z in (cofinite : Filter ℂ),
      RatFunc.eval (RingHom.id ℂ) z p = RatFunc.eval (RingHom.id ℂ) z q) : p = q := by
  have he : ∀ᶠ z in (cofinite : Filter ℂ),
      (p.num * q.denom).eval z = (q.num * p.denom).eval z := by
    filter_upwards [h, eventually_eval_ne_zero_cofinite p.denom_ne_zero,
      eventually_eval_ne_zero_cofinite q.denom_ne_zero] with z hz hp hq
    simp only [RatFunc.eval, eval₂_id] at hz
    simpa only [eval_mul] using (div_eq_div_iff hp hq).mp hz
  have hc := Polynomial.eq_of_infinite_eval_eq (p.num * q.denom)
    (q.num * p.denom) (Filter.frequently_cofinite_iff_infinite.mp he.frequently)
  exact (RatFunc.num_mul_eq_mul_denom_iff q.denom_ne_zero).mp hc |>.trans q.num_div_denom

open scoped BigOperators

theorem ratFunc_eval_add_eventually (p q : RatFunc ℂ) :
    ∀ᶠ z in (cofinite : Filter ℂ),
      RatFunc.eval (RingHom.id ℂ) z (p + q) =
        RatFunc.eval (RingHom.id ℂ) z p + RatFunc.eval (RingHom.id ℂ) z q := by
  filter_upwards [eventually_eval_ne_zero_cofinite p.denom_ne_zero,
    eventually_eval_ne_zero_cofinite q.denom_ne_zero] with z hp hq
  exact RatFunc.eval_add (RingHom.id ℂ) z hp hq

theorem ratFunc_eval_mul_eventually (p q : RatFunc ℂ) :
    ∀ᶠ z in (cofinite : Filter ℂ),
      RatFunc.eval (RingHom.id ℂ) z (p * q) =
        RatFunc.eval (RingHom.id ℂ) z p * RatFunc.eval (RingHom.id ℂ) z q := by
  filter_upwards [eventually_eval_ne_zero_cofinite p.denom_ne_zero,
    eventually_eval_ne_zero_cofinite q.denom_ne_zero] with z hp hq
  exact RatFunc.eval_mul (RingHom.id ℂ) z hp hq

theorem ratFunc_eval_sum_eventually {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℂ) :
    ∀ᶠ z in (cofinite : Filter ℂ),
      RatFunc.eval (RingHom.id ℂ) z (∑ i ∈ s, f i) =
        ∑ i ∈ s, RatFunc.eval (RingHom.id ℂ) z (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    filter_upwards [ih, ratFunc_eval_add_eventually (f i) (∑ j ∈ s, f j)] with z hz ha
    simpa only [Finset.sum_insert hi] using ha.trans (congrArg (RatFunc.eval (RingHom.id ℂ) z (f i) + ·) hz)

def specialize (z : ℂ) (P : Polynomial (RatFunc ℂ)) : Polynomial ℂ :=
  ofFinsupp (AddMonoidAlgebra.ofCoeff
    (P.toFinsupp.coeff.mapRange (RatFunc.eval (RingHom.id ℂ) z)
      (RatFunc.eval_zero _ _)))

@[simp] theorem coeff_specialize (z : ℂ) (P : Polynomial (RatFunc ℂ)) (n : ℕ) :
    (specialize z P).coeff n = RatFunc.eval (RingHom.id ℂ) z (P.coeff n) := rfl

theorem ratFunc_eval_coeff_mul_eventually (P Q : Polynomial (RatFunc ℂ)) (n : ℕ) :
    ∀ᶠ z in (cofinite : Filter ℂ),
      RatFunc.eval (RingHom.id ℂ) z ((P * Q).coeff n) =
        (specialize z P * specialize z Q).coeff n := by
  have hm : ∀ᶠ z in (cofinite : Filter ℂ), ∀ i ∈ Finset.antidiagonal n,
      RatFunc.eval (RingHom.id ℂ) z (P.coeff i.1 * Q.coeff i.2) =
        RatFunc.eval (RingHom.id ℂ) z (P.coeff i.1) *
          RatFunc.eval (RingHom.id ℂ) z (Q.coeff i.2) :=
    (Finset.eventually_all _).mpr (fun i _ => ratFunc_eval_mul_eventually _ _)
  filter_upwards [ratFunc_eval_sum_eventually (Finset.antidiagonal n)
    (fun i => P.coeff i.1 * Q.coeff i.2), hm] with z hs hm
  simp only [coeff_mul, coeff_specialize]
  exact hs.trans (Finset.sum_congr rfl hm)

theorem ratFunc_polynomial_factorization_of_specializations
    (P A B : Polynomial (RatFunc ℂ))
    (h : ∀ᶠ z in (cofinite : Filter ℂ),
      specialize z P = specialize z A * specialize z B) : P = A * B := by
  ext n
  apply ratFunc_eq_of_eventually_eval_eq
  filter_upwards [h, ratFunc_eval_coeff_mul_eventually A B n] with z hz hm
  exact (congrArg (fun R : Polynomial ℂ => R.coeff n) hz).trans hm.symm

theorem ratFunc_eval_quotient_eventually (p q : Polynomial ℂ) (hq : q ≠ 0) :
    ∀ᶠ z in (cofinite : Filter ℂ),
      RatFunc.eval (RingHom.id ℂ) z (coeffMap p / coeffMap q) = p.eval z / q.eval z := by
  let r : RatFunc ℂ := coeffMap p / coeffMap q
  have hc : r.num * q = p * r.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hq).mpr rfl
  filter_upwards [eventually_eval_ne_zero_cofinite r.denom_ne_zero,
    eventually_eval_ne_zero_cofinite hq] with z hr hqz
  change r.num.eval z / r.denom.eval z = p.eval z / q.eval z
  apply (div_eq_div_iff hr hqz).mpr
  simpa only [eval_mul] using congrArg (fun t : Polynomial ℂ => t.eval z) hc

theorem natDegree_specialize_le (z : ℂ) (P : Polynomial (RatFunc ℂ)) :
    (specialize z P).natDegree ≤ P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp [coeff_eq_zero_of_natDegree_lt hn]

theorem specialize_mul_eventually (P Q : Polynomial (RatFunc ℂ)) :
    ∀ᶠ z in (cofinite : Filter ℂ),
      specialize z (P * Q) = specialize z P * specialize z Q := by
  let N := P.natDegree + Q.natDegree
  have he : ∀ᶠ z in (cofinite : Filter ℂ), ∀ n ∈ Finset.range (N + 1),
      RatFunc.eval (RingHom.id ℂ) z ((P * Q).coeff n) =
        (specialize z P * specialize z Q).coeff n :=
    (Finset.eventually_all _).mpr (fun n _ => ratFunc_eval_coeff_mul_eventually P Q n)
  filter_upwards [he] with z hz
  ext n
  by_cases hn : n < N + 1
  · exact hz n (Finset.mem_range.mpr hn)
  · have hn' : N < n := by omega
    have h1 : (specialize z (P * Q)).natDegree ≤ N :=
      (natDegree_specialize_le z (P * Q)).trans natDegree_mul_le
    have h2 : (specialize z P * specialize z Q).natDegree ≤ N :=
      natDegree_mul_le.trans
        (Nat.add_le_add (natDegree_specialize_le z P) (natDegree_specialize_le z Q))
    rw [coeff_eq_zero_of_natDegree_lt (h1.trans_lt hn'),
      coeff_eq_zero_of_natDegree_lt (h2.trans_lt hn')]

@[simp] theorem specialize_C (z : ℂ) (a : RatFunc ℂ) :
    specialize z (C a) = C (RatFunc.eval (RingHom.id ℂ) z a) := by
  ext n
  by_cases hn : n = 0 <;> simp [hn, coeff_C]

@[simp] theorem specialize_map (z : ℂ) (P : Polynomial (Polynomial ℂ)) :
    specialize z (P.map coeffMap) = P.map (Polynomial.evalRingHom z) := by
  ext n
  simp [coeffMap, RatFunc.eval_algebraMap]

theorem specialize_monic_normalization_eventually (P : Polynomial (Polynomial ℂ))
    (hP : P ≠ 0) :
    ∀ᶠ z in (cofinite : Filter ℂ),
      specialize z (C (coeffMap P.leadingCoeff)⁻¹ * P.map coeffMap) =
        C (P.leadingCoeff.eval z)⁻¹ * P.map (Polynomial.evalRingHom z) := by
  have hi : ∀ᶠ z in (cofinite : Filter ℂ),
      RatFunc.eval (RingHom.id ℂ) z (coeffMap P.leadingCoeff)⁻¹ =
        (P.leadingCoeff.eval z)⁻¹ := by
    simpa only [map_one, one_div, eval_one] using
      ratFunc_eval_quotient_eventually 1 P.leadingCoeff (leadingCoeff_ne_zero.mpr hP)
  filter_upwards [specialize_mul_eventually (C (coeffMap P.leadingCoeff)⁻¹)
    (P.map coeffMap), hi] with z hz hi
  simpa only [specialize_C, specialize_map, hi] using hz

end D12Complex.MonodromyTransitive.FactorBridge

noncomputable section
open Set Polynomial Filter
open scoped Topology Classical
namespace D12Complex.MonodromyTransitive
open AlgebraicCovering

/-- Membership of the path component, expressed without dependent root proofs. -/
def Reachable (P : Polynomial (Polynomial ℂ)) (x : Curve P) (z w : ℂ) : Prop :=
  ∃ y : Curve P, y.val = (z,w) ∧ Joined x y

def classValues (P : Polynomial (Polynomial ℂ)) (x : Curve P) (b : Bool) (z : ℂ) : Multiset ℂ :=
  (fiber P z).roots.filter (fun w => if b then Reachable P x z w else ¬ Reachable P x z w)

lemma reachable_iff {P : Polynomial (Polynomial ℂ)} (x y : Curve P) :
    Reachable P x y.val.1 y.val.2 ↔ Joined x y := by
  constructor
  · rintro ⟨y', hy', h⟩
    have : y' = y := Subtype.ext hy'
    exact this ▸ h
  · intro h
    exact ⟨y, rfl, h⟩

lemma branch_graph_joined {P : Polynomial (Polynomial ℂ)} {d : ℕ} {a : ℂ}
    (L : LocalBranches P d a) (i : Fin d) {z : ℂ}
    (hz : z ∈ Metric.ball a L.radius) :
    Joined (⟨(a, L.branch i a), L.base_subset (Metric.mem_ball_self L.radius_pos),
      (L.exhaustive a (Metric.mem_ball_self L.radius_pos) _).mpr ⟨i, rfl⟩⟩ : Curve P)
      ⟨(z, L.branch i z), L.base_subset hz, (L.exhaustive z hz _).mpr ⟨i,rfl⟩⟩ := by
  let g : Metric.ball a L.radius → Curve P := fun u =>
    ⟨(u.val, L.branch i u.val), L.base_subset u.property,
      (L.exhaustive u.val u.property _).mpr ⟨i,rfl⟩⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    have hf : ContinuousOn (L.branch i) (Metric.ball a L.radius) :=
      fun z hz => ((L.holomorphic i).2 z hz).continuousAt.continuousWithinAt
    exact continuous_subtype_val.prodMk hf.domRestrict
  have hj := (convex_ball a L.radius).isPathConnected
      ⟨a, Metric.mem_ball_self L.radius_pos⟩
  have : PathConnectedSpace (Metric.ball a L.radius) :=
    isPathConnected_iff_pathConnectedSpace.mp hj
  exact (PathConnectedSpace.joined
    (⟨a, Metric.mem_ball_self L.radius_pos⟩ : Metric.ball a L.radius) ⟨z,hz⟩).map hg

lemma reachable_branch_iff {P : Polynomial (Polynomial ℂ)} {d : ℕ} {a : ℂ}
    (L : LocalBranches P d a) (x : Curve P) (i : Fin d) {z : ℂ}
    (hz : z ∈ Metric.ball a L.radius) :
    Reachable P x z (L.branch i z) ↔ Reachable P x a (L.branch i a) := by
  have h := branch_graph_joined L i hz
  change Reachable P x
    (⟨(z, L.branch i z), L.base_subset hz,
      (L.exhaustive z hz _).mpr ⟨i,rfl⟩⟩ : Curve P).val.1
    (⟨(z, L.branch i z), L.base_subset hz,
      (L.exhaustive z hz _).mpr ⟨i,rfl⟩⟩ : Curve P).val.2 ↔ _
  rw [reachable_iff]
  change Joined x _ ↔ Reachable P x
    (⟨(a, L.branch i a), L.base_subset (Metric.mem_ball_self L.radius_pos),
      (L.exhaustive a (Metric.mem_ball_self L.radius_pos) _).mpr ⟨i,rfl⟩⟩ : Curve P).val.1
    (⟨(a, L.branch i a), L.base_subset (Metric.mem_ball_self L.radius_pos),
      (L.exhaustive a (Metric.mem_ball_self L.radius_pos) _).mpr ⟨i,rfl⟩⟩ : Curve P).val.2
  rw [reachable_iff]
  exact ⟨fun hz => hz.trans h.symm, fun ha => ha.trans h⟩

lemma roots_eq_local {P : Polynomial (Polynomial ℂ)} {d : ℕ} {a : ℂ}
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (L : LocalBranches P d a) {z : ℂ} (hz : z ∈ Metric.ball a L.radius) :
    (fiber P z).roots = Finset.univ.val.map (fun i => L.branch i z) := by
  classical
  obtain ⟨_,_,hf⟩ := Ch21.FiniteExceptionalSet.finite_exceptional_set P d hP hdeg hd
  obtain ⟨_,hnd,_,hmem,_⟩ := hf z (L.base_subset hz)
  apply (Multiset.Nodup.ext hnd (Finset.univ.nodup.map (L.injective z hz))).mpr
  intro w
  simpa only [Multiset.mem_toFinset, Multiset.mem_map, Finset.mem_val,
    Finset.mem_univ, true_and, eq_comm] using (hmem w).trans (L.exhaustive z hz w)

lemma classValues_eq_local {P : Polynomial (Polynomial ℂ)} {d : ℕ} {a : ℂ}
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (L : LocalBranches P d a) (x : Curve P) (b : Bool) {z : ℂ}
    (hz : z ∈ Metric.ball a L.radius) :
    classValues P x b z =
      ((Finset.univ.filter (fun i => if b then Reachable P x a (L.branch i a)
        else ¬ Reachable P x a (L.branch i a))).val.map
        (fun i => L.branch i z)) := by
  classical
  rw [classValues, roots_eq_local hP hdeg hd L hz, Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro i _
  cases b
  · simpa using (reachable_branch_iff L x i hz).not
  · simpa using (reachable_branch_iff L x i hz)

lemma classValues_card_local {P : Polynomial (Polynomial ℂ)} {d : ℕ} {a : ℂ}
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (L : LocalBranches P d a) (x : Curve P) (b : Bool) {z : ℂ}
    (hz : z ∈ Metric.ball a L.radius) :
    (classValues P x b z).card = (classValues P x b a).card := by
  rw [classValues_eq_local hP hdeg hd L x b hz,
    classValues_eq_local hP hdeg hd L x b (Metric.mem_ball_self L.radius_pos)]
  simp

lemma classValues_card_locallyConstant {P : Polynomial (Polynomial ℂ)} {d : ℕ}
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (x : Curve P) (b : Bool) :
    IsLocallyConstant (fun z : Base P => (classValues P x b z).card) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro a
  obtain ⟨L⟩ := local_branches P d hP hdeg hd a a.property
  refine ⟨baseU P (Metric.ball (a : ℂ) L.radius), baseU_open P Metric.isOpen_ball,
    Metric.mem_ball_self L.radius_pos, ?_⟩
  intro z hz
  exact classValues_card_local hP hdeg hd L x b hz

lemma classValues_card_eq {P : Polynomial (Polynomial ℂ)} {d : ℕ}
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (x : Curve P) (b : Bool) (z a : Base P) :
    (classValues P x b z).card = (classValues P x b a).card := by
  have hconn := (base_domain P d hP hdeg hd).2.2
  have : PreconnectedSpace (Base P) := isPreconnected_iff_preconnectedSpace.mp hconn
  exact (classValues_card_locallyConstant hP hdeg hd x b).apply_eq_of_preconnectedSpace z a

/-- A fixed subset of a local root enumeration can be indexed by Fin n. -/
lemma classValues_local_enumeration {P : Polynomial (Polynomial ℂ)} {d n : ℕ} {a : ℂ}
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (L : LocalBranches P d a) (x : Curve P) (b : Bool)
    (hn : (classValues P x b a).card = n) :
    ∃ f : Fin n → ℂ → ℂ, (∀ i, HolomorphicOn (Metric.ball a L.radius) (f i)) ∧
      ∀ z ∈ Metric.ball a L.radius,
        classValues P x b z = Finset.univ.val.map (fun i => f i z) := by
  classical
  let s : Finset (Fin d) := Finset.univ.filter (fun i =>
    if b then Reachable P x a (L.branch i a) else ¬ Reachable P x a (L.branch i a))
  have hs : s.card = n := by
    simpa only [classValues_eq_local hP hdeg hd L x b (Metric.mem_ball_self L.radius_pos),
      Multiset.card_map, Finset.card, s] using hn
  let e : s ≃ Fin n := s.equivFinOfCardEq hs
  refine ⟨fun i => L.branch (e.symm i).val, fun i => L.holomorphic _, ?_⟩
  intro z hz
  rw [classValues_eq_local hP hdeg hd L x b hz]
  change s.val.map (fun i => L.branch i z) = _
  apply (Multiset.Nodup.ext
    (s.nodup.map (L.injective z hz))
    (Finset.univ.nodup.map ((L.injective z hz).comp
      (Subtype.val_injective.comp e.symm.injective)))).mpr
  intro w
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, h⟩
    refine ⟨e ⟨i, hi⟩, ?_⟩
    simpa using h
  · rintro ⟨i, h⟩
    exact ⟨(e.symm i).val, (e.symm i).property, h⟩

def classSphereValues (P : Polynomial (Polynomial ℂ)) (x : Curve P) (b : Bool)
    (p : RiemannSphere) : Multiset ℂ := classValues P x b (finiteCoordinate p)

lemma classSphereValues_locallyEnumerated {P : Polynomial (Polynomial ℂ)} {d n : ℕ}
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (x : Curve P) (b : Bool) (a : ℂ) (ha : a ∈ baseSet P)
    (hn : (classValues P x b a).card = n) :
    SymmetricCoefficientData.LocallyEnumerated n (classSphereValues P x b) (sphereFinite a) := by
  obtain ⟨L⟩ := local_branches P d hP hdeg hd a ha
  obtain ⟨f, hf, he⟩ := classValues_local_enumeration hP hdeg hd L x b hn
  refine ⟨L.radius, L.radius_pos, fun i u => f i (a + u), ?_, ?_⟩
  · intro i
    refine ⟨Metric.isOpen_ball, fun u hu => ?_⟩
    have hau : a + u ∈ Metric.ball a L.radius := by
      simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hu
    exact ((hf i).2 (a+u) hau).comp u ((differentiableAt_const a).add differentiableAt_id)
  · intro u hu
    have hau : a + u ∈ Metric.ball a L.radius := by
      simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hu
    simpa only [SymmetricCoefficients.parameter_finite, classSphereValues,
      finiteCoordinate_sphereFinite] using he (a+u) hau

lemma exists_sphere_exceptional {P : Polynomial (Polynomial ℂ)} {d : ℕ}
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d) :
    ∃ E : Finset RiemannSphere, sphereInfty ∈ E ∧
      ∀ a : ℂ, sphereFinite a ∉ E ↔ a ∈ baseSet P := by
  classical
  obtain ⟨_, hfinite, _⟩ := Ch21.FiniteExceptionalSet.finite_exceptional_set P d hP hdeg hd
  change (exceptionalSet P).Finite at hfinite
  refine ⟨insert sphereInfty (hfinite.toFinset.image sphereFinite), by simp, ?_⟩
  intro a
  simp only [Finset.mem_insert, Finset.mem_image, Set.Finite.mem_toFinset,
    sphereFinite_injective.eq_iff, exists_eq_right, baseSet, Set.mem_compl_iff]
  simp [sphereFinite, sphereInfty]

lemma classSphereValues_analytic {P : Polynomial (Polynomial ℂ)} {d n : ℕ}
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (x : Curve P) (b : Bool) (a : Base P)
    (hn : (classValues P x b a).card = n) (hnpos : 0 < n)
    (E : Finset RiemannSphere) (hI : sphereInfty ∈ E)
    (hE : ∀ z : ℂ, sphereFinite z ∉ E ↔ z ∈ baseSet P) :
    SymmetricCoefficientData.AnalyticMultiset E n (classSphereValues P x b) := by
  refine ⟨hnpos, ?_⟩
  intro p hp
  rcases sphere_eq_infty_or_finite p with rfl | ⟨z, rfl⟩
  · exact (hp hI).elim
  · have hz := (hE z).mp hp
    have hnz : (classValues P x b z).card = n :=
      (classValues_card_eq hP hdeg hd x b ⟨z,hz⟩ a).trans hn
    refine ⟨?_, classSphereValues_locallyEnumerated hP hdeg hd x b z hz hnz⟩
    simpa only [classSphereValues, finiteCoordinate_sphereFinite] using hnz

lemma classValues_partition (P : Polynomial (Polynomial ℂ)) (x : Curve P) (z : ℂ) :
    classValues P x true z + classValues P x false z = (fiber P z).roots := by
  classical
  simp only [classValues, Bool.false_eq_true, reduceIte]
  exact Multiset.filter_add_not _ _

lemma classSphereValues_roots (P : Polynomial (Polynomial ℂ)) (x : Curve P) (b : Bool)
    (z : ℂ) (w : ℂ) (hw : w ∈ classSphereValues P x b (sphereFinite z)) :
    (fiber P z).eval w = 0 := by
  have hm : w ∈ (fiber P z).roots := by
    simpa only [classSphereValues, finiteCoordinate_sphereFinite, classValues] using
      (Multiset.mem_of_le (Multiset.filter_le _ _) hw)
  exact Polynomial.isRoot_of_mem_roots hm

end D12Complex.MonodromyTransitive

noncomputable section
open Set Filter Polynomial
open scoped Topology BigOperators
namespace D12Complex.MonodromyTransitive
open SymmetricCoefficientData

/-- One common finite-point power bound controls every root, without choosing labels. -/
theorem all_roots_finite_bound (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0) (c : ℂ) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ u in 𝓝[≠] (0 : ℂ),
      ∀ w : ℂ, (AlgebraicCovering.fiber P (c + u)).eval w = 0 →
        ‖w‖ ≤ C * (‖u‖ ^ N)⁻¹ := by
  obtain ⟨k, hk⟩ := AlgebraicGrowth.polynomial_eval_has_finite_order P.leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hP) c
  obtain ⟨C, hC, hb⟩ := AlgebraicGrowth.coefficient_ratios_of_finite_order P c k hk
  have hto : Tendsto (fun u : ℂ => c + u) (𝓝[≠] 0) (𝓝[≠] c) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun u : ℂ => c + u) 0 :=
        continuousAt_const.add continuousAt_id
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simpa using hu
  have hsmall : ∀ᶠ u : ℂ in 𝓝[≠] 0, ‖u‖ < 1 :=
    (continuous_norm.continuousAt.eventually_lt_const (by norm_num : ‖(0 : ℂ)‖ < 1)).filter_mono
      nhdsWithin_le_nhds
  refine ⟨k, C + 1, by positivity, ?_⟩
  filter_upwards [hto.eventually hb, hsmall, self_mem_nhdsWithin] with u hu hus hu0
  intro w hw
  have hrat : ∀ j < P.natDegree,
      ‖(P.coeff j).eval (c + u) / P.leadingCoeff.eval (c + u)‖ ≤ C * (‖u‖ ^ k)⁻¹ := by
    simpa only [add_sub_cancel_left, zpow_neg, zpow_natCast] using hu.2
  have hroot := AlgebraicGrowth.fiber_root_norm_le hu.1 hw (by positivity) hrat
  have hpos : 0 < ‖u‖ ^ k := pow_pos (norm_pos_iff.mpr hu0) _
  have hle : ‖u‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hus.le
  have hinv : 1 ≤ (‖u‖ ^ k)⁻¹ := (one_le_inv₀ hpos).mpr hle
  nlinarith

/-- A reciprocal common power bound also controls every root at infinity. -/
theorem all_roots_infinity_bound (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ u in 𝓝[≠] (0 : ℂ),
      ∀ w : ℂ, (AlgebraicCovering.fiber P u⁻¹).eval w = 0 →
        ‖w‖ ≤ C * (‖u‖ ^ N)⁻¹ := by
  obtain ⟨L, C, hC, hb⟩ := AlgebraicGrowth.coefficient_growth_at_infinity P hP
  have hto : Tendsto (fun u : ℂ => u⁻¹) (𝓝[≠] 0) (Bornology.cobounded ℂ) :=
    tendsto_inv₀_nhdsNE_zero
  have hlead : ∀ᶠ z in Bornology.cobounded ℂ, P.leadingCoeff.eval z ≠ 0 :=
    (Polynomial.eventually_eval_ne_zero_cofinite
      (Polynomial.leadingCoeff_ne_zero.mpr hP)).filter_mono (Bornology.le_cofinite ℂ)
  have hsmall : ∀ᶠ u : ℂ in 𝓝[≠] 0, ‖u‖ < 1 :=
    (continuous_norm.continuousAt.eventually_lt_const (by norm_num : ‖(0 : ℂ)‖ < 1)).filter_mono
      nhdsWithin_le_nhds
  refine ⟨L, C + 1, by positivity, ?_⟩
  filter_upwards [hto.eventually hb, hto.eventually hlead, hsmall,
    self_mem_nhdsWithin] with u hu hl hus hu0
  intro w hw
  have hrat : ∀ j < P.natDegree,
      ‖(P.coeff j).eval u⁻¹ / P.leadingCoeff.eval u⁻¹‖ ≤ C * (‖u‖ ^ L)⁻¹ := by
    simpa only [norm_div, norm_inv, inv_pow] using hu
  have hroot := AlgebraicGrowth.fiber_root_norm_le hl hw (by positivity) hrat
  have hpos : 0 < ‖u‖ ^ L := pow_pos (norm_pos_iff.mpr hu0) _
  have hle : ‖u‖ ^ L ≤ 1 := pow_le_one₀ (norm_nonneg _) hus.le
  have hinv : 1 ≤ (‖u‖ ^ L)⁻¹ := (one_le_inv₀ hpos).mpr hle
  nlinarith

/-- Direct root bounds imply a common power bound for each analytic root submultiset. -/
theorem root_multiset_chart_bound
    (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0)
    (E : Finset RiemannSphere) (B : RiemannSphere → Multiset ℂ)
    (hroot : ∀ a : ℂ, sphereFinite a ∉ E → ∀ w ∈ B (sphereFinite a),
      (AlgebraicCovering.fiber P a).eval w = 0) (p : RiemannSphere) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ u in 𝓝[≠] (0 : ℂ),
      ∀ w ∈ B (parameter p u), ‖w‖ ≤ C * (‖u‖ ^ N)⁻¹ := by
  rcases sphere_eq_infty_or_finite p with rfl | ⟨c, rfl⟩
  · obtain ⟨N, C, hC, hb⟩ := all_roots_infinity_bound P hP
    refine ⟨N, C, hC, ?_⟩
    filter_upwards [hb, SymmetricCoefficients.eventually_regular E sphereInfty,
      self_mem_nhdsWithin] with u hu hreg hu0
    intro w hw
    have hparam := infinityParametrization_ne_zero u hu0
    apply hu w
    apply hroot u⁻¹
    · simpa only [SymmetricCoefficients.parameter_infty, hparam] using hreg
    · simpa only [SymmetricCoefficients.parameter_infty, hparam] using hw
  · obtain ⟨N, C, hC, hb⟩ := all_roots_finite_bound P hP c
    refine ⟨N, C, hC, ?_⟩
    filter_upwards [hb, SymmetricCoefficients.eventually_regular E (sphereFinite c)] with u hu hreg
    intro w hw
    apply hu w
    apply hroot (c + u)
    · simpa only [SymmetricCoefficients.parameter_finite] using hreg
    · simpa only [SymmetricCoefficients.parameter_finite] using hw

/-- Every coefficient of an analytic multiset of polynomial roots is meromorphic
in every sphere chart. No local cyclic parameter certificate is assumed. -/
theorem root_multiset_coefficient_meromorphic
    (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0)
    (E : Finset RiemannSphere) (d : ℕ) (B : RiemannSphere → Multiset ℂ)
    (hB : AnalyticMultiset E d B)
    (hroot : ∀ a : ℂ, sphereFinite a ∉ E → ∀ w ∈ B (sphereFinite a),
      (AlgebraicCovering.fiber P a).eval w = 0)
    (k : ℕ) (p : RiemannSphere) :
    MeromorphicAt (fun u => coefficient B k (parameter p u)) 0 := by
  obtain ⟨N, C, hC, hb⟩ := root_multiset_chart_bound P hP E B hroot p
  have hi := SymmetricCoefficients.isolated_coefficient hB k p
  have ho : (fun u => coefficient B k (parameter p u)) =O[𝓝[≠] (0 : ℂ)]
      (fun u => ((u-0)^(N*k))⁻¹) := by
    apply Asymptotics.IsBigO.of_bound ((d.choose k : ℝ) * C^k)
    filter_upwards [hb, SymmetricCoefficients.eventually_regular E p] with u hu hreg
    have hbound := SymmetricCoefficients.norm_coefficient_le (hB.2 _ hreg).1
      (mul_nonneg hC.le (inv_nonneg.mpr (pow_nonneg (norm_nonneg u) N))) hu k
    simpa only [sub_zero, norm_inv, norm_pow, mul_pow, inv_pow, ← pow_mul, mul_assoc]
      using hbound
  exact ((SingularityGrowth.atMost_iff_order hi (N*k)).mp
    ((SingularityGrowth.bigO_iff _ _ hi (N*k)).mp ho)).1

/-- The coefficient functions of a polynomial-root submultiset have rational
representatives agreeing at every ordinary finite point. -/
theorem root_multiset_rational_values
    (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0)
    (E : Finset RiemannSphere) (d : ℕ) (B : RiemannSphere → Multiset ℂ)
    (hB : AnalyticMultiset E d B)
    (hroot : ∀ a : ℂ, sphereFinite a ∉ E → ∀ w ∈ B (sphereFinite a),
      (AlgebraicCovering.fiber P a).eval w = 0) (k : ℕ) :
    ∃ A Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ a : ℂ, sphereFinite a ∉ E →
      sphereFinite (coefficient B k (sphereFinite a)) =
        LocalQuotientsArithmetic.fill (fun z => A.eval z / Q.eval z) a := by
  let f : ℂ → ℂ := fun z => coefficient B k (sphereFinite z)
  have hf : MeromorphicOn f univ := by
    intro a _
    have hm := root_multiset_coefficient_meromorphic P hP E d B hB hroot k (sphereFinite a)
    have ht : MeromorphicAt (fun u : ℂ => f (u+a)) 0 := by
      simpa only [SymmetricCoefficients.parameter_finite, add_comm, f] using hm
    simpa only [zero_add] using meromorphicAt_fun_comp_add_const_iff_meromorphicAt.mp ht
  have hbad : Set.Finite {a | ¬ AnalyticAt ℂ f a} := by
    apply (E.finite_toSet.preimage sphereFinite_injective.injOn).subset
    intro a ha
    by_contra hn
    exact ha (SymmetricCoefficients.analytic_finite hB k hn)
  have hrec : (fun u => coefficient B k (parameter sphereInfty u)) =ᶠ[𝓝[≠] (0 : ℂ)]
      reciprocalPullback f := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [SymmetricCoefficients.parameter_infty, infinityParametrization_ne_zero _ hu,
      reciprocalPullback, f]
  have hI := (root_multiset_coefficient_meromorphic P hP E d B hB hroot k sphereInfty).congr hrec
  obtain ⟨A, Q, hQ, he, _⟩ := SymmetricCoefficients.rational_of_meromorphic f hf hbad hI
  refine ⟨A, Q, hQ, fun a ha => ?_⟩
  exact (LocalQuotientsArithmetic.fill_of_analyticAt
    (SymmetricCoefficients.analytic_finite hB k ha)).symm.trans (he a)


/-- The same rational representatives agree with raw coefficient values off
one finite set, which is suitable for rational-function identities. -/
theorem root_multiset_rational_eventually
    (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0)
    (E : Finset RiemannSphere) (d : ℕ) (B : RiemannSphere → Multiset ℂ)
    (hB : AnalyticMultiset E d B)
    (hroot : ∀ a : ℂ, sphereFinite a ∉ E → ∀ w ∈ B (sphereFinite a),
      (AlgebraicCovering.fiber P a).eval w = 0) (k : ℕ) :
    ∃ A Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ᶠ a in (cofinite : Filter ℂ),
      coefficient B k (sphereFinite a) = A.eval a / Q.eval a := by
  obtain ⟨A, Q, hQ, he⟩ := root_multiset_rational_values P hP E d B hB hroot k
  refine ⟨A, Q, hQ, ?_⟩
  have hreg : ∀ᶠ a in (cofinite : Filter ℂ), sphereFinite a ∉ E :=
    sphereFinite_injective.tendsto_cofinite.eventually E.eventually_cofinite_notMem
  filter_upwards [hreg, Polynomial.eventually_eval_ne_zero_cofinite hQ] with a ha hQa
  apply sphereFinite_injective
  rw [he a ha]
  exact LocalQuotientsArithmetic.fill_of_analyticAt
    (((AnalyticOnNhd.eval_polynomial A) a (mem_univ a)).div
      ((AnalyticOnNhd.eval_polynomial Q) a (mem_univ a)) hQa)


/-- Lift the monic product of an analytic root multiset to a polynomial over
ℂ(z); specialization agrees away from a finite set. -/
theorem root_multiset_rational_polynomial
    (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0)
    (E : Finset RiemannSphere) (n : ℕ) (B : RiemannSphere → Multiset ℂ)
    (hB : AnalyticMultiset E n B)
    (hroot : ∀ a : ℂ, sphereFinite a ∉ E → ∀ w ∈ B (sphereFinite a),
      (AlgebraicCovering.fiber P a).eval w = 0) :
    ∃ A : Polynomial (RatFunc ℂ), A.Monic ∧ A.natDegree = n ∧
      ∀ᶠ a in (cofinite : Filter ℂ), FactorBridge.specialize a A =
        ((B (sphereFinite a)).map fun v => Polynomial.X - Polynomial.C v).prod := by
  classical
  have hr (j : Fin (n + 1)) : ∃ r : RatFunc ℂ,
      ∀ᶠ a in (cofinite : Filter ℂ), RatFunc.eval (RingHom.id ℂ) a r =
        coefficient B (n - j) (sphereFinite a) := by
    obtain ⟨A, Q, hQ, he⟩ := root_multiset_rational_eventually P hP E n B hB hroot (n - j)
    refine ⟨FactorBridge.coeffMap A / FactorBridge.coeffMap Q, ?_⟩
    filter_upwards [FactorBridge.ratFunc_eval_quotient_eventually A Q hQ, he] with a ha he
    exact ha.trans he.symm
  choose f hf using hr
  let A : Polynomial (RatFunc ℂ) := Polynomial.ofFn (n + 1) f
  have hreg : ∀ᶠ a in (cofinite : Filter ℂ), sphereFinite a ∉ E :=
    sphereFinite_injective.tendsto_cofinite.eventually E.eventually_cofinite_notMem
  have hspec : ∀ᶠ a in (cofinite : Filter ℂ), FactorBridge.specialize a A =
      ((B (sphereFinite a)).map fun v => Polynomial.X - Polynomial.C v).prod := by
    filter_upwards [Filter.eventually_all.mpr hf, hreg] with a ha hareg
    have hcard := (hB.2 _ hareg).1
    ext j
    rw [FactorBridge.coeff_specialize]
    by_cases hj : j < n + 1
    · rw [show A.coeff j = f ⟨j, hj⟩ from Polynomial.ofFn_coeff_eq_val_of_lt f hj,
        ha ⟨j, hj⟩]
      rw [Multiset.prod_X_sub_C_coeff (B (sphereFinite a)) (by rw [hcard]; omega)]
      simp only [SymmetricCoefficientData.coefficient, hcard]
    · rw [show A.coeff j = 0 from Polynomial.ofFn_coeff_eq_zero_of_ge f (by omega),
        RatFunc.eval_zero]
      symm
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hcard]
      omega
  have hle : A.natDegree ≤ n := by
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) f)
  have hcoeff : A.coeff n = 1 := by
    apply FactorBridge.ratFunc_eq_of_eventually_eval_eq
    filter_upwards [hspec, hreg] with a ha hareg
    have hcard := (hB.2 _ hareg).1
    have hdegree := Polynomial.natDegree_multiset_prod_X_sub_C_eq_card (B (sphereFinite a))
    have hmonic := Polynomial.monic_multisetProd_X_sub_C (B (sphereFinite a))
    have he := congrArg (fun q : Polynomial ℂ => q.coeff n) ha
    rw [FactorBridge.coeff_specialize] at he
    rw [RatFunc.eval_one]
    apply he.trans
    rw [← hcard, ← hdegree]
    exact hmonic.coeff_natDegree
  refine ⟨A, Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hle hcoeff,
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeff]; exact one_ne_zero), hspec⟩


/-- Two analytic root multisets which partition the full fiber produce an
actual monic factorization over ℂ(z). -/
theorem analytic_root_partition_factorization
    (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0)
    (E : Finset RiemannSphere) (n m : ℕ)
    (B D : RiemannSphere → Multiset ℂ)
    (hB : AnalyticMultiset E n B) (hD : AnalyticMultiset E m D)
    (hrootB : ∀ a : ℂ, sphereFinite a ∉ E → ∀ w ∈ B (sphereFinite a),
      (AlgebraicCovering.fiber P a).eval w = 0)
    (hrootD : ∀ a : ℂ, sphereFinite a ∉ E → ∀ w ∈ D (sphereFinite a),
      (AlgebraicCovering.fiber P a).eval w = 0)
    (hpartition : ∀ᶠ a in (cofinite : Filter ℂ),
      B (sphereFinite a) + D (sphereFinite a) = (AlgebraicCovering.fiber P a).roots) :
    ∃ A F : Polynomial (RatFunc ℂ), A.Monic ∧ F.Monic ∧
      A.natDegree = n ∧ F.natDegree = m ∧
      Polynomial.C (FactorBridge.coeffMap P.leadingCoeff)⁻¹ *
        P.map FactorBridge.coeffMap = A * F := by
  obtain ⟨A, hAm, hAd, hAs⟩ := root_multiset_rational_polynomial P hP E n B hB hrootB
  obtain ⟨F, hFm, hFd, hFs⟩ := root_multiset_rational_polynomial P hP E m D hD hrootD
  refine ⟨A, F, hAm, hFm, hAd, hFd, ?_⟩
  apply FactorBridge.ratFunc_polynomial_factorization_of_specializations
  have hlead : ∀ᶠ a in (cofinite : Filter ℂ), P.leadingCoeff.eval a ≠ 0 :=
    Polynomial.eventually_eval_ne_zero_cofinite (Polynomial.leadingCoeff_ne_zero.mpr hP)
  filter_upwards [hAs, hFs, hpartition,
    FactorBridge.specialize_monic_normalization_eventually P hP, hlead] with a hA hF hp hn hl
  rw [hA, hF, ← Multiset.prod_add, ← Multiset.map_add, hp, hn]
  have hprod := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (p := AlgebraicCovering.fiber P a) IsAlgClosed.card_roots_eq_natDegree
  have hfl : (AlgebraicCovering.fiber P a).leadingCoeff = P.leadingCoeff.eval a :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hl
  rw [hfl] at hprod
  change Polynomial.C (P.leadingCoeff.eval a)⁻¹ * AlgebraicCovering.fiber P a = _
  calc
    _ = Polynomial.C (P.leadingCoeff.eval a)⁻¹ *
        (Polynomial.C (P.leadingCoeff.eval a) *
          ((AlgebraicCovering.fiber P a).roots.map fun v => Polynomial.X - Polynomial.C v).prod) :=
      congrArg (Polynomial.C (P.leadingCoeff.eval a)⁻¹ * ·) hprod.symm
    _ = _ := by
      rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hl, Polynomial.C_1, one_mul]

/-- Irreducibility excludes any partition into two nonempty analytic root
systems. Their growth and rational coefficients have been proved above. -/
theorem no_proper_analytic_root_partition
    (P : Polynomial (Polynomial ℂ)) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree)
    (E : Finset RiemannSphere) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (B D : RiemannSphere → Multiset ℂ)
    (hB : AnalyticMultiset E n B) (hD : AnalyticMultiset E m D)
    (hrootB : ∀ a : ℂ, sphereFinite a ∉ E → ∀ w ∈ B (sphereFinite a),
      (AlgebraicCovering.fiber P a).eval w = 0)
    (hrootD : ∀ a : ℂ, sphereFinite a ∉ E → ∀ w ∈ D (sphereFinite a),
      (AlgebraicCovering.fiber P a).eval w = 0)
    (hpartition : ∀ᶠ a in (cofinite : Filter ℂ),
      B (sphereFinite a) + D (sphereFinite a) = (AlgebraicCovering.fiber P a).roots) : False := by
  obtain ⟨A, F, _, _, hAd, hFd, hfactor⟩ := analytic_root_partition_factorization
    P hP.ne_zero E n m B D hB hD hrootB hrootD hpartition
  exact FactorBridge.no_positive_degree_factorization P hP hdeg A F
    (by rwa [hAd]) (by rwa [hFd]) hfactor

end D12Complex.MonodromyTransitive

noncomputable section
open Set Filter unitInterval
open scoped Topology
namespace D12Complex.AlgebraicCovering

theorem monodromy_transitive_of_curve_pathConnected
    (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hd : P.natDegree = d) (hpos : 0 < d)
    (hconn : PathConnectedSpace (Curve P)) (a : Base P)
    (M : Path a a → Equiv.Perm (RootGerm P (a : ℂ)))
    (hM : ∀ γ g, ∃ Φ : GermFamily (fun t => (γ t : ℂ)),
      IsContinuation (baseSet P) (fun t => (γ t : ℂ))
        ((congrArg Subtype.val γ.source).symm ▸ g.val) Φ ∧
      (∀ t, IsRootGerm P (γ t : ℂ) (Φ t)) ∧
      (congrArg Subtype.val γ.target ▸ Φ 1) = (M γ g).val) :
    ∀ g h, ∃ γ : Path a a, M γ g = h := by
  let : PathConnectedSpace (Curve P) := hconn
  intro g h
  let Γ : Path (rootGermToFiber a g).val (rootGermToFiber a h).val :=
    PathConnectedSpace.somePath _ _
  have hp : Continuous (projection P) := continuous_subtype_val.fst.subtype_mk _
  let γ : Path a a := Γ.map hp
  let g₀ : RootGerm P (γ 0 : ℂ) :=
    (congrArg Subtype.val γ.source).symm ▸ g
  have hγ : Continuous (fun t => (γ t : ℂ)) :=
    continuous_subtype_val.comp γ.continuous
  have hw : Continuous (fun t => (Γ t).val.2) :=
    continuous_snd.comp (continuous_subtype_val.comp Γ.continuous)
  have hzero (t : I) : (fiber P (γ t : ℂ)).eval (Γ t).val.2 = 0 :=
    (Γ t).property.2
  have hinit : (Γ 0).val.2 = g₀.val.value := by
    rw [Γ.source]
    simp only [g₀, rootGerm_value_cast]
    rfl
  obtain ⟨Φ, hΦ, hr, hvalue⟩ := continuation_of_root_selection
    (base_domain P d hP hd hpos) (local_branches P d hP hd hpos)
    (fun t => (γ t : ℂ)) (fun t => (Γ t).val.2)
    hγ hw (fun t => (γ t).property) hzero g₀ hinit
  have hΦ' : IsContinuation (baseSet P) (fun t => (γ t : ℂ))
      ((congrArg Subtype.val γ.source).symm ▸ g.val) Φ := by
    simpa only [g₀, rootGerm_cast_val] using hΦ
  obtain ⟨Ψ, hΨ, hΨroot, hΨend⟩ := hM γ g
  have heq : Φ 1 = Ψ 1 :=
    ContinuationOperations.continuation_unique (baseSet P)
      (fun t => (γ t : ℂ)) _ Φ Ψ hΦ' hΨ 1
  let g₁ : RootGerm P (a : ℂ) :=
    congrArg Subtype.val γ.target ▸ (⟨Φ 1, hr 1⟩ : RootGerm P (γ 1 : ℂ))
  let L := Classical.choice (local_branches P d hP hd hpos (a : ℂ) a.property)
  have hvalues : g₁.val.value = h.val.value := by
    rw [show g₁.val.value = (Φ 1).value from
      rootGerm_value_cast (congrArg Subtype.val γ.target)
        (⟨Φ 1, hr 1⟩ : RootGerm P (γ 1 : ℂ))]
    rw [hvalue 1, Γ.target]
    rfl
  have hfinal : g₁ = h := rootGerm_ext L g₁ h hvalues
  have hΦend : (congrArg Subtype.val γ.target ▸ Φ 1) = h.val :=
    (rootGerm_cast_val (congrArg Subtype.val γ.target)
      (⟨Φ 1, hr 1⟩ : RootGerm P (γ 1 : ℂ))).symm.trans
      (congrArg Subtype.val hfinal)
  refine ⟨γ, ?_⟩
  apply Subtype.ext
  calc
    (M γ g).val = (congrArg Subtype.val γ.target ▸ Ψ 1) := hΨend.symm
    _ = (congrArg Subtype.val γ.target ▸ Φ 1) := by rw [heq]
    _ = h.val := hΦend

end D12Complex.AlgebraicCovering

noncomputable section
open Set Polynomial Filter
open scoped Topology Classical
namespace D12Complex.MonodromyTransitive
open AlgebraicCovering

lemma mem_classValues_of_point {P : Polynomial (Polynomial ℂ)} {d : ℕ}
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (x y : Curve P) (b : Bool) (hy : if b then Joined x y else ¬ Joined x y) :
    y.val.2 ∈ classValues P x b y.val.1 := by
  obtain ⟨_, _, hf⟩ := Ch21.FiniteExceptionalSet.finite_exceptional_set P d hP hdeg hd
  obtain ⟨_, _, _, hmem, _⟩ := hf y.val.1 y.property.1
  have hr : y.val.2 ∈ (fiber P y.val.1).roots :=
    Multiset.mem_toFinset.mp ((hmem y.val.2).mpr y.property.2)
  apply Multiset.mem_filter.mpr
  refine ⟨hr, ?_⟩
  cases b <;> simpa only [Bool.false_eq_true, reduceIte, reachable_iff] using hy

/-- The original irreducible affine covering has just one path component.
A hypothetical second component supplies two analytic root multisets; their
rational symmetric coefficients factor the actual normalization of P. -/
theorem curve_pathConnected (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d) :
    PathConnectedSpace (Curve P) := by
  classical
  constructor
  · obtain ⟨a, ha⟩ := (base_domain P d hP hdeg hd).1
    obtain ⟨L⟩ := local_branches P d hP hdeg hd a ha
    have hac : a ∈ Metric.ball a L.radius := Metric.mem_ball_self L.radius_pos
    exact ⟨⟨(a, L.branch ⟨0, hd⟩ a), ha,
      (L.exhaustive a hac _).mpr ⟨⟨0,hd⟩,rfl⟩⟩⟩
  · intro x y
    by_contra hxy
    obtain ⟨E, hI, hE⟩ := exists_sphere_exceptional hP hdeg hd
    let n := (classValues P x true x.val.1).card
    let m := (classValues P x false y.val.1).card
    have hn : 0 < n := Multiset.card_pos_iff_exists_mem.mpr
      ⟨x.val.2, mem_classValues_of_point hP hdeg hd x x true (Joined.refl x)⟩
    have hm : 0 < m := Multiset.card_pos_iff_exists_mem.mpr
      ⟨y.val.2, mem_classValues_of_point hP hdeg hd x y false hxy⟩
    have hB := classSphereValues_analytic hP hdeg hd x true (projection P x) rfl hn E hI hE
    have hD := classSphereValues_analytic hP hdeg hd x false (projection P y) rfl hm E hI hE
    apply no_proper_analytic_root_partition P hP (by omega) E n m hn hm
      (classSphereValues P x true) (classSphereValues P x false) hB hD
      (fun z _ w hw => classSphereValues_roots P x true z w hw)
      (fun z _ w hw => classSphereValues_roots P x false z w hw)
    exact Filter.Eventually.of_forall (fun z => by
      simpa only [classSphereValues, finiteCoordinate_sphereFinite]
        using classValues_partition P x z)

/-- Connectedness and path connectedness of the literal curve in ℂ². -/
theorem connected : Specs.D12Complex.Ch21.MonodromyTransitive.connected_type := by
  intro P d hP hdeg hd
  have : PathConnectedSpace (Curve P) := curve_pathConnected P d hP hdeg hd
  exact ⟨inferInstance, inferInstance⟩

/-- Transitivity is independent of the chosen representative of the actual
monodromy action: its terminal continuation condition fixes it. -/
theorem every_monodromy_transitive :
    Specs.D12Complex.Ch21.MonodromyTransitive.every_monodromy_transitive_type := by
  intro P d hP hdeg hd a M hM
  exact AlgebraicCovering.monodromy_transitive_of_curve_pathConnected P d hP hdeg hd
    (curve_pathConnected P d hP hdeg hd) a M hM.2.2.2

/-- At every ordinary basepoint, the d roots carry the transitive action
with all the homotopy, reversal and concatenation laws. -/
theorem monodromy_transitive :
    Specs.D12Complex.Ch21.MonodromyTransitive.monodromy_transitive_type := by
  intro P d hP hdeg hd a
  obtain ⟨M, hh, hi, ht, he⟩ := AlgebraicCovering.monodromy P d hP hdeg hd a
  have hM : Specs.D12Complex.Ch21.MonodromyTransitive.IsRootMonodromy P a M :=
    ⟨hh, hi, ht, he⟩
  exact ⟨M, hM, every_monodromy_transitive P d hP hdeg hd a M hM⟩

end D12Complex.MonodromyTransitive
