import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalLatticeIntersection
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Ideal.GoingUp

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Polynomial RatFunc WithZero Pointwise
open Set Submodule WithZero
open scoped Topology

namespace LinearAlgebraicGroups.Arithmetic

section Coordinates

variable {A C D ι : Type*} [CommRing A] [Field C] [Field D]
  [Algebra A C] [Algebra A D] [Algebra C D] [IsScalarTower A C D]

private def coordinateLinearMap : (ι → C) →ₗ[A] (ι → D) where
  toFun := embedCoordinates (algebraMap C D)
  map_add' x y := by funext i; exact map_add _ _ _
  map_smul' a x := by
    funext i
    change algebraMap C D (a • x i) = a • algebraMap C D (x i)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]

end Coordinates

section Clearing

variable {A C V : Type*} [CommRing A] [IsDomain A] [Field C]
  [Algebra A C] [IsFractionRing A C]
  [AddCommGroup V] [Module A V] [Module C V] [IsScalarTower A C V]

private lemma clearSpan (L : Submodule A V) {ι : Type*} [Finite ι] (x : ι → V)
    (hx : ∀ i, x i ∈ span C (L : Set V)) :
    ∃ a : A, a ≠ 0 ∧ ∀ i, a • x i ∈ L := by
  classical
  let := Fintype.ofFinite ι
  have hreps (i : ι) : ∃ c : V →₀ C,
      ↑c.support ⊆ (L : Set V) ∧ (c.sum fun y r => r • y) = x i :=
    mem_span_set.mp (hx i)
  choose c hc heq using hreps
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors A) (fun j : Σ i, (c i).support => c j.1 j.2)
  refine ⟨a, nonZeroDivisors.ne_zero a.2, fun i => ?_⟩
  rw [← heq i, Finsupp.sum, Finset.smul_sum]
  apply L.sum_mem
  intro y hy
  obtain ⟨b, hb⟩ := ha ⟨i, ⟨y, hy⟩⟩
  change algebraMap A C b = (a : A) • c i y at hb
  rw [← smul_assoc, ← hb, algebraMap_smul]
  exact L.smul_mem b (hc i hy)

private lemma commensurable (L N : Submodule A V)
    (hL : L.FG) (hN : N.FG)
    (hLs : span C (L : Set V) = ⊤) (hNs : span C (N : Set V) = ⊤) :
    ∃ a : A, a ≠ 0 ∧ (∀ x ∈ L, a • x ∈ N) ∧ ∀ x ∈ N, a • x ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hL
  obtain ⟨t, ht⟩ := hN
  obtain ⟨a, ha, hab⟩ := clearSpan (C := C) N (fun j : s => (j : V))
    (fun j => by rw [hNs]; trivial)
  obtain ⟨b, hb, hba⟩ := clearSpan (C := C) L (fun j : t => (j : V))
    (fun j => by rw [hLs]; trivial)
  have h₁ : ∀ x ∈ L, a • x ∈ N := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hab ⟨y, hy⟩
    | zero => simp
    | add y z _ _ hy hz => simpa only [smul_add] using N.add_mem hy hz
    | smul r y _ hy => simpa only [smul_comm a r y] using N.smul_mem r hy
  have h₂ : ∀ x ∈ N, b • x ∈ L := by
    intro x hx
    rw [← ht] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hba ⟨y, hy⟩
    | zero => simp
    | add y z _ _ hy hz => simpa only [smul_add] using L.add_mem hy hz
    | smul r y _ hy => simpa only [smul_comm b r y] using L.smul_mem r hy
  refine ⟨a * b, mul_ne_zero ha hb, ?_, ?_⟩
  · intro x hx
    rw [mul_comm, mul_smul]
    exact N.smul_mem b (h₁ x hx)
  · intro x hx
    rw [mul_smul]
    exact L.smul_mem a (h₂ x hx)

end Clearing

section Approximation

variable {R K ι : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

private lemma mem_adic_nhds (v : HeightOneSpectrum R) {x : v.adicCompletion K}
    {U : Set (v.adicCompletion K)} (hU : U ∈ 𝓝 x) :
    ∃ γ : (ℤᵐ⁰)ˣ, ∀ y, Valued.v (y - x) < (γ : ℤᵐ⁰) → y ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
  let e := MonoidWithZeroHom.ValueGroup₀.embedding
    (f := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).toMonoidWithZeroHom)
  refine ⟨Units.map e.toMonoidHom γ, fun y hy => hγ ?_⟩
  exact (Valuation.restrict_lt_iff_lt_embedding _).mpr hy

private lemma approximateAdicInteger (v : HeightOneSpectrum R)
    (x : v.adicCompletionIntegers K) (γ : (ℤᵐ⁰)ˣ) :
    ∃ a : R, Valued.v (algebraMap R (v.adicCompletion K) a - x) < (γ : ℤᵐ⁰) := by
  let C := v.adicCompletion K
  let w : Valuation C ℤᵐ⁰ := Valued.v
  let δ : (ℤᵐ⁰)ˣ := min γ 1
  have hδ₁ : (δ : ℤᵐ⁰) ≤ 1 := by
    change (δ : ℤᵐ⁰) ≤ ((1 : (ℤᵐ⁰)ˣ) : ℤᵐ⁰)
    exact Units.val_le_val.mpr (min_le_right _ _)
  have hball : {z : C | w (z - x) < (δ : ℤᵐ⁰)} ∈ 𝓝 (x : C) := by
    rw [Valued.mem_nhds]
    obtain ⟨b, hb⟩ := v.valuedAdicCompletion_surjective (K := K) (δ : ℤᵐ⁰)
    let b' := w.restrict b
    have hb' : b' ≠ 0 := by
      rw [ne_eq, Valuation.restrict_eq_zero_iff, hb]
      exact Units.ne_zero _
    refine ⟨Units.mk0 b' hb', ?_⟩
    intro z hz
    change w.restrict (z - x) < b' at hz
    change w (z - x) < (δ : ℤᵐ⁰)
    rwa [Valuation.restrict_lt_iff, hb] at hz
  obtain ⟨y, hy⟩ := (v.denseRange_algebraMap (K := K)).mem_nhds hball
  change w (algebraMap K C y - x) < (δ : ℤᵐ⁰) at hy
  have hyInt : v.valuation K y ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation']
    change w (algebraMap K C y) ≤ 1
    rw [← sub_add_cancel (algebraMap K C y) (x : C)]
    exact (w.map_add _ _).trans (max_le (hy.le.trans hδ₁) x.property)
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hyInt γ
  have ha' : w (algebraMap R C a - algebraMap K C y) < (γ : ℤᵐ⁰) := by
    rw [IsScalarTower.algebraMap_apply R K C, ← map_sub]
    exact (valuedAdicCompletion_eq_valuation' (v := v) _).trans_lt ha
  refine ⟨a, ?_⟩
  change w (algebraMap R C a - x) < (γ : ℤᵐ⁰)
  rw [← sub_add_sub_cancel (algebraMap R C a) (algebraMap K C y) (x : C)]
  exact (w.map_add _ _).trans_lt (max_lt ha' (hy.trans_le (Units.val_le_val.mpr (min_le_left _ _))))

/-- Finite simultaneous approximation follows from reduction modulo powers of distinct primes. -/
private lemma denseFiniteIntegers (S : Finset (HeightOneSpectrum R)) :
    DenseRange (fun a : R => fun v : S => algebraMap R (v.1.adicCompletionIntegers K) a) := by
  classical
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨J, _, W, hW, hsub⟩ := hU
  have hlocal (v : S) : ∃ γ : (ℤᵐ⁰)ˣ, ∀ z : v.1.adicCompletionIntegers K,
      Valued.v ((z : v.1.adicCompletion K) - x v) < (γ : ℤᵐ⁰) → z ∈ W v := by
    have hv := hW v
    rw [nhds_subtype_eq_comap, Filter.mem_comap] at hv
    obtain ⟨Q, hQ, hQ'⟩ := hv
    obtain ⟨γ, hγ⟩ := mem_adic_nhds v.1 hQ
    exact ⟨γ, fun z hz => hQ' (hγ z hz)⟩
  choose γ hγ using hlocal
  choose a ha using fun v : S => approximateAdicInteger v.1 (x v) (γ v)
  have hex (v : S) : ∃ n : ℕ, exp (-(n : ℤ)) < (γ v : ℤᵐ⁰) := by
    obtain ⟨n, hn, _⟩ := exists_exp_neg_natCast_lt_and_lt (Units.ne_zero (γ v)) one_ne_zero
    exact ⟨n, hn⟩
  choose n hn using hex
  obtain ⟨b, hb⟩ := Ideal.exists_forall_sub_mem_ideal
    (I := fun v : S => v.1.asIdeal ^ n v)
    (fun v w h => v.1.isCoprime_pow_of_ne w.1 (Subtype.val_injective.ne h) _ _) a
  refine ⟨_, hsub ?_, ⟨b, rfl⟩⟩
  intro v _
  apply hγ
  change Valued.v (algebraMap R (v.1.adicCompletion K) b - x v) < (γ v : ℤᵐ⁰)
  rw [← sub_add_sub_cancel (algebraMap R (v.1.adicCompletion K) b)
    (algebraMap R (v.1.adicCompletion K) (a v)) (x v : v.1.adicCompletion K)]
  refine (Valued.v.map_add _ _).trans_lt (max_lt ?_ (ha v))
  rw [← map_sub, valuedAdicCompletion_eq_valuation, v.1.valuation_of_algebraMap]
  exact ((v.1.intValuation_le_pow_iff_mem _ _).2 (hb v)).trans_lt (hn v)

end Approximation

section IntegerBox

variable {A C ι : Type*} [CommRing A] [Field C] [Algebra A C]

private def integerBox : Submodule A (ι → C) :=
  LinearMap.range (LinearMap.pi fun i : ι =>
    (Algebra.linearMap A C).comp (LinearMap.proj i))

private lemma mem_integerBox {x : ι → C} :
    x ∈ integerBox (A := A) ↔ ∀ i, x i ∈ (algebraMap A C).range := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext hy⟩

private lemma integerBox_fg [Finite ι] : (integerBox (A := A) (C := C) (ι := ι)).FG := by
  rw [integerBox, LinearMap.range_eq_map]
  exact (show (⊤ : Submodule A (ι → A)).FG from Module.Finite.fg_top).map _

private lemma integerBox_span [Finite ι] :
    span C ((integerBox : Submodule A (ι → C)) : Set (ι → C)) = ⊤ := by
  classical
  rw [eq_top_iff, ← (Pi.basisFun C ι).span_eq]
  apply span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply subset_span
  apply mem_integerBox.mpr
  intro j
  by_cases h : j = i
  · subst j
    exact ⟨1, by simp [Pi.basisFun_apply]⟩
  · exact ⟨0, by simp [Pi.basisFun_apply, h]⟩

end IntegerBox

section AdicLattices

variable {R K ι : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

local notation "C[" v "]" => HeightOneSpectrum.adicCompletion K v
set_option quotPrecheck false in
local notation "O[" v "]" => ↥(HeightOneSpectrum.adicCompletionIntegers K v)
local notation "e[" v "]" => embedCoordinates (algebraMap K (C[v]))

private lemma embed_rsmul (v : HeightOneSpectrum R) (a : R) (x : ι → K) :
    e[v] (a • x) = a • e[v] x :=
  (coordinateLinearMap (A := R)).map_smul a x

private lemma completedLattice_span (v : HeightOneSpectrum R) (s : Set (ι → K)) :
    completedLattice v (span R s) = span O[v] (e[v] '' s) := by
  let f : (ι → K) →ₗ[R] (ι → C[v]) := coordinateLinearMap
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact subset_span ⟨x, hx, rfl⟩
    | zero =>
      rw [show e[v] (0 : ι → K) = 0 from f.map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [show e[v] (x + y) = e[v] x + e[v] y from
        f.map_add x y]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [embed_rsmul, ← algebraMap_smul O[v]]
      exact smul_mem _ _ hx
  · exact span_mono (image_mono subset_span)

private lemma completedLattice_isLattice (v : HeightOneSpectrum R) [Finite ι]
    (L : Submodule R (ι → K)) [Submodule.IsLattice K L] :
    Submodule.IsLattice (C[v]) (completedLattice v L) := by
  classical
  constructor
  · obtain ⟨s, hs⟩ := Submodule.IsLattice.fg (M := L)
    rw [← hs, completedLattice_span]
    exact fg_span (s.finite_toSet.image _)
  · change span (C[v]) ((span O[v] (e[v] '' (L : Set (ι → K)))) : Set (ι → C[v])) = ⊤
    rw [Submodule.span_span_of_tower O[v]]
    let f : (ι → K) →ₗ[K] (ι → C[v]) := coordinateLinearMap
    have hL := Submodule.IsLattice.span_eq_top (A := K) (M := L)
    have hmap : Submodule.map f ⊤ ≤
        (span (C[v]) (e[v] '' (L : Set (ι → K)))).restrictScalars K := by
      rw [← hL, Submodule.map_span]
      exact span_le_restrictScalars K (C[v]) _
    rw [eq_top_iff, ← (Pi.basisFun (C[v]) ι).span_eq]
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply hmap
    refine ⟨Pi.basisFun K ι i, trivial, ?_⟩
    funext j
    change algebraMap K (C[v]) (Pi.basisFun K ι i j) = Pi.basisFun (C[v]) ι i j
    by_cases h : j = i <;> simp [Pi.basisFun_apply, h]

private lemma open_adicBox (v : HeightOneSpectrum R) [Finite ι] :
    IsOpen ((integerBox : Submodule O[v] (ι → C[v])) : Set (ι → C[v])) := by
  have heq : ((integerBox : Submodule O[v] (ι → C[v])) : Set (ι → C[v])) =
      (Set.univ : Set ι).pi (fun _ => (v.adicCompletionIntegers K : Set (C[v]))) := by
    ext x
    rw [SetLike.mem_coe, mem_integerBox]
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_congr' fun i => ⟨fun ⟨a, ha⟩ => ha ▸ a.property, fun ha => ⟨⟨x i, ha⟩, rfl⟩⟩
  rw [heq]
  apply isOpen_set_pi Set.finite_univ
  intro i _
  exact Valued.isOpen_valuationSubring (C[v])

private lemma open_localLattice (v : HeightOneSpectrum R) [Finite ι]
    (P : Submodule O[v] (ι → C[v])) [Submodule.IsLattice (C[v]) P] :
    IsOpen (P : Set (ι → C[v])) := by
  let N : Submodule O[v] (ι → C[v]) := integerBox
  have hN : N.FG := integerBox_fg
  have hNs : span (C[v]) (N : Set (ι → C[v])) = ⊤ := integerBox_span
  have hP : P.FG := Submodule.IsLattice.fg
  have hPs : span (C[v]) (P : Set (ι → C[v])) = ⊤ := Submodule.IsLattice.span_eq_top
  obtain ⟨a, ha, h₁, _⟩ := commensurable (C := C[v]) N P hN hP hNs hPs
  let b : C[v] := a
  have hb : b ≠ 0 := fun h => ha (Subtype.ext h)
  apply P.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
  have ho : IsOpen {x : ι → C[v] | b⁻¹ • x ∈ integerBox (A := O[v])} :=
    (open_adicBox v).preimage (continuous_const_smul b⁻¹)
  apply Filter.mem_of_superset (ho.mem_nhds (by simp)) (fun x hx => ?_)
  have hh := h₁ (b⁻¹ • x) hx
  rw [← algebraMap_smul (C[v])] at hh
  change b • b⁻¹ • x ∈ P at hh
  rwa [smul_smul, mul_inv_cancel₀ hb, one_smul] at hh

/-- A finite generating set reduces simultaneous vector approximation to approximation of its
coefficients. -/
private lemma referenceApproximation (L : Submodule R (ι → K)) (hL : L.FG)
    (S : Finset (HeightOneSpectrum R)) (U : ∀ v : S, Set (ι → C[v.1]))
    (hU : ∀ v, IsOpen (U v)) (y : ∀ v : S, ι → C[v.1])
    (hy : ∀ v, y v ∈ completedLattice v.1 L) (hyU : ∀ v, y v ∈ U v) :
    ∃ x ∈ L, ∀ v : S, e[v.1] x ∈ U v := by
  classical
  obtain ⟨s, hs⟩ := hL
  have hrep (v : S) : ∃ c : ↥s → O[v.1], ∑ i, c i • e[v.1] (i : ι → K) = y v := by
    have hv := hy v
    rw [← hs, completedLattice_span] at hv
    exact (Submodule.mem_span_image_finset_iff_exists_fun O[v.1]).mp hv
  choose c hc using hrep
  let eval : (↥s → ∀ v : S, O[v.1]) → ((v : S) → ι → C[v.1]) :=
    fun z v => ∑ i, z i v • e[v.1] (i : ι → K)
  have heval : Continuous eval := by
    apply continuous_pi
    intro v
    apply continuous_pi
    intro j
    change Continuous fun z : ↥s → ∀ v : S, O[v.1] =>
      (∑ i, z i v • e[v.1] (i : ι → K)) j
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply continuous_finsetSum
    intro i _
    exact (continuous_subtype_val.comp ((continuous_apply v).comp (continuous_apply i))).mul
      continuous_const
  have ho : IsOpen ((Set.univ : Set S).pi U) := isOpen_set_pi Set.finite_univ (fun v _ => hU v)
  have hmem : eval (fun i v => c v i) ∈ (Set.univ : Set S).pi U :=
    fun v _ => by
      change (∑ i, c v i • e[v.1] (i : ι → K)) ∈ U v
      rw [hc v]
      exact hyU v
  obtain ⟨a, ha⟩ := (DenseRange.piMap (fun _ : ↥s => denseFiniteIntegers (K := K) S)).mem_nhds
    ((ho.preimage heval).mem_nhds hmem)
  refine ⟨∑ i : ↥s, a i • (i : ι → K), L.sum_mem (fun i _ => L.smul_mem _ ?_), ?_⟩
  · rw [← hs]
    exact subset_span i.property
  · intro v
    have hv := ha v (Set.mem_univ v)
    change (∑ i : ↥s, (algebraMap R O[v.1] (a i)) • e[v.1] (i : ι → K)) ∈ U v at hv
    simp_rw [algebraMap_smul (R := R) O[v.1]] at hv
    let f : (ι → K) →ₗ[R] (ι → C[v.1]) := coordinateLinearMap
    change f (∑ i : ↥s, a i • (i : ι → K)) ∈ _
    rw [map_sum]
    simp_rw [LinearMap.map_smul f]
    exact hv


omit [IsDedekindDomain R] in
private lemma fractionScalar_ne_zero {a : R} (ha : a ≠ 0) : algebraMap R K a ≠ 0 := by
  simpa only [map_zero] using (IsFractionRing.injective R K).ne ha

private lemma adicScalar_ne_zero (v : HeightOneSpectrum R) {a : R} (ha : a ≠ 0) :
    algebraMap R (C[v]) a ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply R K (C[v])]
  exact (map_ne_zero _).mpr (fractionScalar_ne_zero ha)

private lemma finite_nonunit_places (a : R) (ha : a ≠ 0) :
    {v : HeightOneSpectrum R | ¬ IsUnit (algebraMap R O[v] a)}.Finite := by
  apply (HeightOneSpectrum.Support.finite R ((algebraMap R K a)⁻¹)).subset
  intro v hv
  change 1 < v.valuation K ((algebraMap R K a)⁻¹)
  rw [map_inv₀, one_lt_inv₀ ((v.valuation K).pos_iff.mpr
    (fractionScalar_ne_zero ha))]
  apply lt_of_le_of_ne (v.valuation_le_one a)
  intro heq
  apply hv
  rw [adicCompletionIntegers.isUnit_iff_valued_eq_one]
  exact (valuedAdicCompletion_eq_valuation (v := v) a).trans heq

private lemma embed_mem_adicBox (v : HeightOneSpectrum R) {x : ι → K} :
    e[v] x ∈ integerBox (A := O[v]) ↔ ∀ i, v.valuation K (x i) ≤ 1 := by
  rw [mem_integerBox]
  refine forall_congr' fun i => ?_
  change (algebraMap K (C[v]) (x i)) ∈ (algebraMap O[v] (C[v])).range ↔ _
  rw [← valuedAdicCompletion_eq_valuation' (v := v)]
  constructor
  · rintro ⟨a, ha⟩
    change Valued.v (algebraMap K (C[v]) (x i)) ≤ 1
    rw [← ha]
    exact a.property
  · intro hx
    exact ⟨⟨_, hx⟩, rfl⟩

private lemma globalBox_of_local (x : ι → K)
    (hx : ∀ v : HeightOneSpectrum R, e[v] x ∈ integerBox (A := O[v])) :
    x ∈ integerBox (A := R) := by
  apply mem_integerBox.mpr
  intro i
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K (x i)
    (fun v => (embed_mem_adicBox v).mp (hx v) i)

private lemma map_inverse_smul (v : HeightOneSpectrum R) (a : R) (x : ι → K) :
    e[v] ((algebraMap R K a)⁻¹ • x) = (algebraMap R (C[v]) a)⁻¹ • e[v] x := by
  funext i
  change algebraMap K (C[v]) ((algebraMap R K a)⁻¹ * x i) =
    (algebraMap R (C[v]) a)⁻¹ * algebraMap K (C[v]) (x i)
  rw [map_mul, map_inv₀, IsScalarTower.algebraMap_apply R K (C[v])]

private lemma inverse_smul_of_local_unit (v : HeightOneSpectrum R) (a : R)
    (ha : IsUnit (algebraMap R O[v] a)) (P : Submodule O[v] (ι → C[v]))
    {x : ι → C[v]} (hx : x ∈ P) :
    (algebraMap R (C[v]) a)⁻¹ • x ∈ P := by
  obtain ⟨u, hu⟩ := ha
  have h := P.smul_mem (↑u⁻¹ : O[v]) hx
  change (algebraMap O[v] (C[v]) (↑u⁻¹ : O[v])) • x ∈ P at h
  let f : O[v] →* C[v] := (algebraMap O[v] (C[v])).toMonoidHom
  have hinv : algebraMap O[v] (C[v]) (↑u⁻¹ : O[v]) =
      (algebraMap R (C[v]) a)⁻¹ := by
    change f (↑u⁻¹ : O[v]) = _
    rw [← Units.coe_map_inv f u, Units.val_inv_eq_inv_val, Units.coe_map]
    change (algebraMap O[v] (C[v]) (↑u : O[v]))⁻¹ = _
    rw [hu, ← IsScalarTower.algebraMap_apply R O[v] (C[v])]
  rw [hinv] at h
  exact h

private lemma integral_rsmul (v : HeightOneSpectrum R) (P : Submodule O[v] (ι → C[v]))
    (a : R) {x : ι → C[v]} (hx : x ∈ P) : a • x ∈ P := by
  rw [← algebraMap_smul O[v]]
  exact P.smul_mem _ hx

private lemma completedLattice_scaled_le (v : HeightOneSpectrum R)
    {L : Submodule R (ι → K)} {P : Submodule O[v] (ι → C[v])} (a : R)
    (h : ∀ x ∈ L, a • e[v] x ∈ P) :
    ∀ y ∈ completedLattice v L, a • y ∈ P := by
  intro y hy
  change y ∈ span O[v] (e[v] '' (L : Set (ι → K))) at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simpa only [smul_add] using P.add_mem hx hy
  | smul b x _ hx => simpa only [smul_comm a b x] using P.smul_mem b hx

/-- The standard coordinate box detects global integrality. Approximation at the primes of a
denominator then detects membership in the original reference lattice. -/
private lemma reference_saturated [Finite ι] (L : Submodule R (ι → K))
    [Submodule.IsLattice K L] {x : ι → K}
    (hx : ∀ v : HeightOneSpectrum R, e[v] x ∈ completedLattice v L) :
    x ∈ L := by
  classical
  obtain ⟨a, ha, h₁, h₂⟩ := commensurable (C := K) L integerBox Submodule.IsLattice.fg
    integerBox_fg Submodule.IsLattice.span_eq_top integerBox_span
  have hc (v : HeightOneSpectrum R) :
      ∀ y ∈ completedLattice v L, a • y ∈ integerBox (A := O[v]) := by
    apply completedLattice_scaled_le
    intro z hz
    rw [← embed_rsmul]
    apply (embed_mem_adicBox v).mpr
    intro i
    obtain ⟨b, hb⟩ := mem_integerBox.mp (h₁ z hz) i
    rw [← hb]
    exact v.valuation_le_one b
  let S := (finite_nonunit_places (K := K) a ha).toFinset
  let U (v : S) : Set (ι → C[v.1]) :=
    {z | (algebraMap R (C[v.1]) a)⁻¹ • (e[v.1] x - z) ∈ integerBox (A := O[v.1])}
  have ho (v : S) : IsOpen (U v) := by
    apply (open_adicBox v.1).preimage
    exact (continuous_const_smul _).comp (continuous_const.sub continuous_id)
  obtain ⟨z, hz, hzU⟩ := referenceApproximation L Submodule.IsLattice.fg S U ho
    (fun v => e[v.1] x) (fun v => hx v.1) (fun v => by simp [U])
  have hzloc (v : HeightOneSpectrum R) : e[v] z ∈ completedLattice v L :=
    subset_span ⟨z, hz, rfl⟩
  let w := (algebraMap R K a)⁻¹ • (x - z)
  have hw : w ∈ integerBox (A := R) := by
    apply globalBox_of_local
    intro v
    rw [show e[v] w = (algebraMap R (C[v]) a)⁻¹ • (e[v] x - e[v] z) by
      rw [map_inverse_smul]
      congr 1
      exact (coordinateLinearMap (A := R) (D := C[v])).map_sub x z]
    by_cases hv : v ∈ S
    · exact hzU ⟨v, hv⟩
    · have hu : IsUnit (algebraMap R O[v] a) := by
        simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv
      have haC := adicScalar_ne_zero (K := K) v ha
      have hdiff := (integerBox (A := O[v]) (C := C[v]) (ι := ι)).sub_mem
        (hc v _ (hx v)) (hc v _ (hzloc v))
      rw [← smul_sub] at hdiff
      rw [← algebraMap_smul (C[v])] at hdiff
      have ht := inverse_smul_of_local_unit v a hu _ hdiff
      rw [smul_smul, inv_mul_cancel₀ haC, one_smul] at ht
      exact inverse_smul_of_local_unit v a hu _ ht
  have h := h₂ w hw
  rw [← algebraMap_smul K] at h
  change (algebraMap R K a) • (algebraMap R K a)⁻¹ • (x - z) ∈ L at h
  rw [smul_smul, mul_inv_cancel₀ (fractionScalar_ne_zero (K := K) ha), one_smul] at h
  simpa only [sub_add_cancel] using L.add_mem h hz

private lemma localDenominator [Finite ι] (v : HeightOneSpectrum R)
    (L P : Submodule O[v] (ι → C[v]))
    [Submodule.IsLattice (C[v]) L] [Submodule.IsLattice (C[v]) P] :
    ∃ a : R, a ≠ 0 ∧ (∀ y ∈ L, a • y ∈ P) ∧ ∀ y ∈ P, a • y ∈ L := by
  obtain ⟨c, hc, h₁, h₂⟩ := commensurable (C := C[v]) L P Submodule.IsLattice.fg
    Submodule.IsLattice.fg Submodule.IsLattice.span_eq_top Submodule.IsLattice.span_eq_top
  obtain ⟨a, ha, hca⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v
    ((c : C[v])⁻¹)
  let d : O[v] := ⟨_, hca⟩
  have hcd : d * c = algebraMap R O[v] a := by
    apply Subtype.ext
    change ((c : C[v])⁻¹ * algebraMap R (C[v]) a) * c = algebraMap R (C[v]) a
    have hc' : (c : C[v]) ≠ 0 := fun h => hc (Subtype.ext h)
    rw [mul_right_comm, inv_mul_cancel₀ hc', one_mul]
  refine ⟨a, nonZeroDivisors.ne_zero ha, ?_, ?_⟩
  · intro y hy
    rw [← algebraMap_smul O[v], ← hcd, mul_smul]
    exact P.smul_mem d (h₁ y hy)
  · intro y hy
    rw [← algebraMap_smul O[v], ← hcd, mul_smul]
    exact L.smul_mem d (h₂ y hy)

/-- A product clears denominators over the integer ring. Integrality over the base ring supplies
a nonzero base multiple of that product. -/
private lemma commonDenominator {B : Type*} [CommRing B] [Algebra B R]
    [FaithfulSMul B R] [Algebra.IsIntegral B R] [Finite ι]
    (L : Submodule R (ι → K)) [Submodule.IsLattice K L]
    (P : ∀ v : HeightOneSpectrum R, Submodule O[v] (ι → C[v]))
    [∀ v, Submodule.IsLattice (C[v]) (P v)]
    (hfin : {v | P v ≠ completedLattice v L}.Finite) :
    ∃ m : B, m ≠ 0 ∧ ∀ v : HeightOneSpectrum R,
      (∀ y ∈ completedLattice v L, algebraMap B R m • y ∈ P v) ∧
      (∀ y ∈ P v, algebraMap B R m • y ∈ completedLattice v L) := by
  classical
  have h (v : HeightOneSpectrum R) := by
    let := completedLattice_isLattice v L
    exact localDenominator v (completedLattice v L) (P v)
  choose a ha h₁ h₂ using h
  let b := ∏ v ∈ hfin.toFinset, a v
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => ha v)
  let : Nontrivial B := (algebraMap B R).domain_nontrivial
  obtain ⟨m, hm, hmn⟩ := (Submodule.ne_bot_iff (Ideal.under B (Ideal.span {b}))).mp
    (Ideal.under_ne_bot B (by simpa using hb))
  have hm' : b ∣ algebraMap B R m := Ideal.mem_span_singleton.mp hm
  refine ⟨m, hmn, fun v => ?_⟩
  by_cases hv : v ∈ hfin.toFinset
  · obtain ⟨c, hc⟩ := (Finset.dvd_prod_of_mem a hv).trans hm'
    rw [hc, mul_comm (a v) c]
    simp only [mul_smul]
    exact ⟨fun y hy => integral_rsmul v _ c (h₁ v y hy),
      fun y hy => integral_rsmul v _ c (h₂ v y hy)⟩
  · have he : P v = completedLattice v L := by simpa using hv
    rw [he]
    exact ⟨fun _ hy => integral_rsmul v _ _ hy, fun _ hy => integral_rsmul v _ _ hy⟩

/-- After scaling, approximate inside the reference lattice at the target prime and all primes
where either the denominator or the reference comparison imposes a condition. -/
private lemma closure_intersection [Finite ι]
    (L : Submodule R (ι → K)) (hL : L.FG)
    (P : ∀ v : HeightOneSpectrum R, Submodule O[v] (ι → C[v]))
    [∀ v, Submodule.IsLattice (C[v]) (P v)]
    (hfin : {v | P v ≠ completedLattice v L}.Finite)
    {a : R} (ha : a ≠ 0)
    (hscaled : ∀ v (y : ι → C[v]), y ∈ P v → a • y ∈ completedLattice v L)
    (v : HeightOneSpectrum R) :
    closure (e[v] '' ((rationalLatticeIntersection P : Submodule R (ι → K)) : Set (ι → K))) = (P v : Set (ι → C[v])) := by
  classical
  apply subset_antisymm
  · have hclosed : IsClosed (P v : Set (ι → C[v])) :=
      (P v).toAddSubgroup.isClosed_of_isOpen (open_localLattice v (P v))
    apply closure_minimal _ hclosed
    rintro _ ⟨x, hx, rfl⟩
    exact hx v
  · intro y hy
    rw [_root_.mem_closure_iff]
    intro U ho hyU
    let S := insert v (hfin.union (finite_nonunit_places (K := K) a ha)).toFinset
    let j : S := ⟨v, Finset.mem_insert_self _ _⟩
    let scaled (w : HeightOneSpectrum R) (z : ι → C[w]) :=
      (algebraMap R (C[w]) a)⁻¹ • z
    have hscaledContinuous (w : HeightOneSpectrum R) : Continuous (scaled w) :=
      continuous_const_smul _
    have hcancel (w : HeightOneSpectrum R) (z : ι → C[w]) : scaled w (a • z) = z := by
      rw [← algebraMap_smul (C[w]) a z]
      change (algebraMap R (C[w]) a)⁻¹ • (algebraMap R (C[w]) a) • z = z
      rw [smul_smul, inv_mul_cancel₀ (adicScalar_ne_zero w ha), one_smul]
    let V (w : S) : Set (ι → C[w.1]) :=
      scaled w.1 ⁻¹' (P w.1 : Set (ι → C[w.1])) ∩
        if h : w = j then h.symm ▸ (scaled v ⁻¹' U) else Set.univ
    have hV (w : S) : IsOpen (V w) := by
      apply ((open_localLattice w.1 (P w.1)).preimage (hscaledContinuous w.1)).inter
      split
      · next h => subst w; exact ho.preimage (hscaledContinuous v)
      · exact isOpen_univ
    let target (w : S) : ι → C[w.1] := if h : w = j then h.symm ▸ (a • y) else 0
    have htL (w : S) : target w ∈ completedLattice w.1 L := by
      by_cases h : w = j
      · subst w
        simpa [target] using hscaled v y hy
      · simp [target, h]
    have htV (w : S) : target w ∈ V w := by
      by_cases h : w = j
      · subst w
        simp [V, target, hcancel, hy, hyU, j]
      · simp [V, target, h, scaled]
    obtain ⟨z, hz, hzV⟩ := referenceApproximation L hL S V hV target htL htV
    let x := (algebraMap R K a)⁻¹ • z
    have hembed (w : HeightOneSpectrum R) : e[w] x = scaled w (e[w] z) :=
      map_inverse_smul w a z
    refine ⟨e[v] x, ?_, x, ?_, rfl⟩
    · rw [hembed]
      have h := (hzV j).2
      simpa [V, j] using h
    · intro w
      rw [hembed]
      by_cases hw : w ∈ S
      · exact (hzV ⟨w, hw⟩).1
      · have hh : P w = completedLattice w L ∧ IsUnit (algebraMap R O[w] a) := by
          have hw' : w ≠ v ∧ w ∉ (hfin.union (finite_nonunit_places (K := K) a ha)).toFinset := by
            simpa only [S, Finset.mem_insert, not_or] using hw
          simpa only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] using hw'.2
        rw [hh.1]
        exact inverse_smul_of_local_unit w a hh.2 _ (subset_span ⟨z, hz, rfl⟩)

/-- The local integer span of a full reference lattice is its topological completion. -/
theorem completedLattice_eq_closure : LocalLatticeIntersectionSpec.completedLatticeClosure := by
  intro R K ι _ _ _ _ _ _ L _ v
  let P (w : HeightOneSpectrum R) := completedLattice w L
  let : ∀ w, Submodule.IsLattice (w.adicCompletion K) (P w) :=
    fun w => completedLattice_isLattice w L
  have he : rationalLatticeIntersection P = L := by
    ext x
    exact ⟨fun hx => reference_saturated L hx, fun hx w => subset_span ⟨x, hx, rfl⟩⟩
  have hfin : {w | P w ≠ completedLattice w L}.Finite := by simp [P]
  have h := closure_intersection L Submodule.IsLattice.fg P hfin
    (a := 1) one_ne_zero (fun _ _ hy => by simpa only [one_smul] using hy) v
  rwa [he] at h

end AdicLattices

/-- A common base denominator and recovery of the prescribed lattices by completion. -/
theorem dedekindLatticeIntersection : LocalLatticeIntersectionSpec.dedekindIntersection := by
  intro B R K ι _ _ _ _ _ _ _ _ _ _ L _ P _ hfin
  classical
  obtain ⟨m, hm, hs⟩ := commonDenominator (B := B) L P hfin
  let a := algebraMap B R m
  have ha : a ≠ 0 := by
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective B R).ne hm
  let I := rationalLatticeIntersection P
  have hlow (x : ι → K) (hx : x ∈ L) : a • x ∈ I := by
    intro v
    rw [embed_rsmul]
    exact (hs v).1 _ (subset_span ⟨x, hx, rfl⟩)
  have hupp (x : ι → K) (hx : x ∈ I) : a • x ∈ L := by
    apply reference_saturated
    intro v
    rw [embed_rsmul]
    exact (hs v).2 _ (hx v)
  have haK : algebraMap R K a ≠ 0 := fractionScalar_ne_zero ha
  let u : Kˣ := Units.mk0 (algebraMap R K a) haK
  have hupp' : I ≤ u⁻¹ • L := by
    intro x hx
    rw [← show u⁻¹ • (a • x) = x by
      rw [← algebraMap_smul K a x]
      change (algebraMap R K a)⁻¹ • (algebraMap R K a) • x = x
      rw [smul_smul, inv_mul_cancel₀ haK, one_smul]]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (hupp x hx)
  have hL' : Submodule.IsLattice K (u⁻¹ • L) := inferInstance
  have hfg : I.FG := hL'.fg.of_le hupp'
  have hspan : span K (I : Set (ι → K)) = ⊤ := by
    have hle : L ≤ (span K (I : Set (ι → K))).restrictScalars R := by
      intro x hx
      have hmem := subset_span (R := K) (hlow x hx)
      change x ∈ span K (I : Set (ι → K))
      rw [← show (algebraMap R K a)⁻¹ • (a • x) = x by
        rw [← algebraMap_smul K a x]
        rw [smul_smul, inv_mul_cancel₀ haK, one_smul]]
      exact (span K (I : Set (ι → K))).smul_mem _ hmem
    rw [eq_top_iff, ← Submodule.IsLattice.span_eq_top (A := K) (M := L)]
    exact span_le.mpr hle
  let hI : Submodule.IsLattice K I := ⟨hfg, hspan⟩
  refine ⟨m, hm, hI, hlow, hupp, fun v => ⟨(hs v).1, (hs v).2, ?_, ?_⟩⟩
  · exact closure_intersection L Submodule.IsLattice.fg P hfin ha (fun w => (hs w).2) v
  · have hc := closure_intersection L Submodule.IsLattice.fg P hfin ha (fun w => (hs w).2) v
    let := completedLattice_isLattice v I
    apply le_antisymm
    · apply span_le.mpr
      rintro _ ⟨z, hz, rfl⟩
      exact hz v
    · intro y hy
      have hclosed : IsClosed (↑(completedLattice v I) : Set (ι → v.adicCompletion K)) :=
        (completedLattice v I).toAddSubgroup.isClosed_of_isOpen
          (open_localLattice v (completedLattice v I))
      rw [← SetLike.mem_coe, ← hc] at hy
      exact (closure_minimal (subset_span (R := ↥(v.adicCompletionIntegers K))) hclosed) hy

theorem numberLatticeIntersection : LocalLatticeIntersectionSpec.numberIntersection := by
  intro K ι _ _ _ L _ P _ h
  exact dedekindLatticeIntersection (B := ℤ) L P h

theorem functionLatticeIntersection : LocalLatticeIntersectionSpec.functionIntersection := by
  intro F K ι _ _ _ _ _ t L _ P _ h
  let : FaithfulSMul F[X] t.integerRing := (faithfulSMul_iff_algebraMap_injective _ _).2
    (fun _ _ hxy => (transcendental_iff_injective.mp t.transcendental) (congrArg Subtype.val hxy))
  let : Algebra.IsIntegral F[X] t.integerRing := by
    let := t.polynomialAlgebra
    exact inferInstanceAs (Algebra.IsIntegral F[X] (integralClosure F[X] K))
  exact dedekindLatticeIntersection (B := F[X]) L P h


theorem functionLatticeCompletionTransport :
    LocalLatticeIntersectionSpec.functionCompletionTransport := by
  intro F K ι _ _ _ t v
  let w := GlobalPlacesSpec.placeOfPrimeValue t v
  obtain ⟨e, he, hdiag, hint⟩ := t.placeOfPrime_completion_comparison v
  let h₀ : w.Completion ≃ₜ v.adicCompletion K :=
    e.toEquiv.toHomeomorphOfIsInducing he.isInducing
  let h : (ι → w.Completion) ≃ₜ (ι → v.adicCompletion K) :=
    Homeomorph.piCongrRight (fun _ => h₀)
  change ∃ h : (ι → w.Completion) ≃ₜ (ι → v.adicCompletion K),
      (∀ x : ι → K, h (embedCoordinates w.embedding x) =
        embedCoordinates (algebraMap K (v.adicCompletion K)) x) ∧
      (∀ (a : K) (x : ι → w.Completion),
        h (w.embedding a • x) = algebraMap K (v.adicCompletion K) a • h x) ∧
      ∀ S : Set (ι → w.Completion),
        h '' (Submodule.span w.integers S : Set (ι → w.Completion)) =
          (Submodule.span (v.adicCompletionIntegers K) (h '' S) : Set (ι → v.adicCompletion K))
  refine ⟨h, ?_, ?_, ?_⟩
  · intro x
    funext i
    exact hdiag (x i)
  · intro a x
    funext i
    change e (w.embedding a * x i) = algebraMap K (v.adicCompletion K) a * e (x i)
    exact (e.map_mul (w.embedding a) (x i)).trans
      (congrArg (fun z => z * e (x i)) (hdiag a))
  let f := (e.toRingHom.comp w.integers.subtype).codRestrict
    (v.adicCompletionIntegers K) (fun a => (hint (a : w.Completion)).2 a.property)
  have hsurj : Function.Surjective f := by
    intro b
    have hb : e.symm (b : v.adicCompletion K) ∈ w.integers :=
      (hint _).1 (by rw [e.apply_symm_apply]; exact b.property)
    refine ⟨⟨e.symm (b : v.adicCompletion K), hb⟩, Subtype.ext ?_⟩
    exact e.apply_symm_apply _
  let : RingHomSurjective f := ⟨hsurj⟩
  let g : (ι → w.Completion) →ₛₗ[f] (ι → v.adicCompletion K) :=
    { toFun := h
      map_add' := fun x y => funext fun i => e.map_add (x i) (y i)
      map_smul' := fun a x => funext fun i => e.map_mul (a : w.Completion) (x i) }
  intro S
  have hg := Submodule.map_span g S
  exact congrArg (fun Q : Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K) =>
    (Q : Set (ι → v.adicCompletion K))) hg

theorem functionLatticePlaceIndex : LocalLatticeIntersectionSpec.functionPlaceIndex := by
  intro F K _ _ _ _ t
  refine ⟨t.placeOfPrime_injective, t.range_placeOfPrime, ?_⟩
  change Set.range t.placeOfPrime = _
  rw [t.range_placeOfPrime]
  ext v
  change t.element ∈ v.1 ↔ ¬v.1.comap t.rationalMap.toRingHom = _
  exact not_not.symm.trans (not_congr (t.comap_eq_infty_iff v)).symm

end LinearAlgebraicGroups.Arithmetic
