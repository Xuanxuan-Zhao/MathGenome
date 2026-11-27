import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.SimpleDifferentialDomain
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.SimpleDifferenceComponents
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.SimpleOperatorComponents
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Pi

namespace GaloisFormalization.PV

universe u v

open scoped nonZeroDivisors

namespace Operator

variable {kind : OperatorKind} {R : Type u} {K : Type v} [CommRing R] [CommRing K]

private theorem apply_mul_of_isConstant {D : Operator kind R} {c : R}
    (hc : D.IsConstant c) (x : R) : D (x * c) = D x * c := by
  cases kind with
  | differential =>
    change D.toDerivation c = 0 at hc
    change D.toDerivation (x * c) = D.toDerivation x * c
    simp [D.toDerivation.leibniz, hc, smul_eq_mul, mul_comm]
  | difference =>
    change D.toRingEquiv c = c at hc
    change D.toRingEquiv (x * c) = D.toRingEquiv x * c
    rw [map_mul, hc]

private theorem symm_apply_of_isConstant {D : Operator .difference R} {c : R}
    (hc : D.IsConstant c) : D.toRingEquiv.symm c = c := by
  change D.toRingEquiv c = c at hc
  exact (D.toRingEquiv.symm_apply_eq).2 hc.symm

/-- Every nonzero constant has an inverse in the constant subring of a simple operator ring. -/
theorem isField_constantSubring_of_isSimple (D : Operator kind R) (hD : D.IsSimple) :
    IsField D.constantSubring := by
  let : Nontrivial R := hD.1
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro c hc₀
  have hc := (mem_constantSubring D (c : R)).mp c.property
  let I := _root_.Ideal.span ({(c : R)} : Set R)
  have hForward (x : R) (hx : x ∈ I) : D x ∈ I := by
    obtain ⟨a, rfl⟩ := _root_.Ideal.mem_span_singleton'.mp hx
    exact _root_.Ideal.mem_span_singleton'.mpr ⟨D a, (apply_mul_of_isConstant hc a).symm⟩
  have hI : D.IsStable (I : Set R) := by
    cases kind with
    | differential => exact fun {x} => hForward x
    | difference =>
      refine ⟨fun {x} => hForward x, ?_⟩
      intro x hx
      obtain ⟨a, rfl⟩ := _root_.Ideal.mem_span_singleton'.mp hx
      refine _root_.Ideal.mem_span_singleton'.mpr ⟨D.toRingEquiv.symm a, ?_⟩
      change D.toRingEquiv.symm a * (c : R) = D.toRingEquiv.symm (a * (c : R))
      rw [map_mul, symm_apply_of_isConstant hc]
  have hI₀ : I ≠ ⊥ := by
    intro hbot
    have hm : (c : R) ∈ I := _root_.Ideal.mem_span_singleton_self _
    rw [hbot, Submodule.mem_bot] at hm
    exact hc₀ (Subtype.ext hm)
  have htop := (hD.2 I hI).resolve_left hI₀
  obtain ⟨b, hb⟩ := _root_.Ideal.mem_span_singleton'.mp ((_root_.Ideal.eq_top_iff_one I).mp htop)
  have hb' : (c : R) * b = 1 := (mul_comm _ _).trans hb
  have hu : IsUnit (c : R) := ⟨⟨c, b, hb', hb⟩, rfl⟩
  have hmul : D b * (c : R) = D 1 := by rw [← apply_mul_of_isConstant hc, hb]
  have hbc : D.IsConstant b := by
    cases kind with
    | differential =>
      change D b = 0
      apply hu.mul_right_cancel
      rw [hmul, zero_mul]
      exact D.toDerivation.map_one_eq_zero
    | difference =>
      change D b = b
      apply hu.mul_right_cancel
      rw [hmul, hb]
      exact D.toRingEquiv.map_one
  exact ⟨⟨b, (mem_constantSubring D b).mpr hbc⟩, Subtype.ext hb'⟩

variable [Algebra R K] [IsFractionRing R K]

/-- Simplicity survives the passage to the total ring of fractions. -/
theorem isSimple_fractionRing (D : Operator kind R) (E : Operator kind K)
    (hD : D.IsSimple) (h : D.Commutes E (algebraMap R K)) : E.IsSimple := by
  let : Nontrivial R := hD.1
  refine ⟨IsFractionRing.nontrivial R K, fun J hJ => ?_⟩
  let I := J.comap (algebraMap R K)
  have hForward (x : R) (hx : x ∈ I) : D x ∈ I := by
    change algebraMap R K (D x) ∈ J
    rw [h x]
    exact hJ.apply_mem hx
  have hI : D.IsStable (I : Set R) := by
    cases kind with
    | differential => exact fun {x} => hForward x
    | difference =>
      refine ⟨fun {x} => hForward x, ?_⟩
      intro x hx
      change algebraMap R K (D.toRingEquiv.symm x) ∈ J
      rw [h.difference_symm x]
      exact hJ.symm_apply_mem hx
  have hmap : I.map (algebraMap R K) = J := IsLocalization.map_under R⁰ K J
  rcases hD.2 I hI with hbot | htop
  · left
    rw [← hmap, hbot, _root_.Ideal.map_bot]
  · right
    rw [← hmap, htop, _root_.Ideal.map_top]

private def denominatorIdeal (q : K) : _root_.Ideal R where
  carrier := {a | ∃ b, algebraMap R K a * q = algebraMap R K b}
  zero_mem' := ⟨0, by simp only [_root_.map_zero, zero_mul]⟩
  add_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    exact ⟨a' + b', by simp only [_root_.map_add, add_mul, ha, hb]⟩
  smul_mem' := by
    rintro a b ⟨b', hb⟩
    exact ⟨a * b', by rw [smul_eq_mul, map_mul, mul_assoc, hb, map_mul]⟩

/-- The inclusion into the total ring of fractions induces an isomorphism of constants. -/
theorem constants_fractionRing (D : Operator kind R) (E : Operator kind K)
    (hD : D.IsSimple) (h : D.Commutes E (algebraMap R K)) :
    Function.Bijective (RingHom.mapConstants (D := D) (E := E) ⟨algebraMap R K, h⟩) ∧
    IsField E.constantSubring := by
  let : Nontrivial R := hD.1
  refine ⟨⟨?_, ?_⟩, isField_constantSubring_of_isSimple E (isSimple_fractionRing D E hD h)⟩
  · intro a b hab
    exact Subtype.ext (IsFractionRing.injective R K (congrArg Subtype.val hab))
  · intro q
    have hq := (mem_constantSubring E (q : K)).mp q.property
    let I := denominatorIdeal (R := R) (q : K)
    have hForward (a : R) (ha : a ∈ I) : D a ∈ I := by
      obtain ⟨b, hb⟩ := ha
      refine ⟨D b, ?_⟩
      rw [h a, ← apply_mul_of_isConstant hq, hb, h b]
    have hI : D.IsStable (I : Set R) := by
      cases kind with
      | differential => exact fun {a} => hForward a
      | difference =>
        refine ⟨fun {a} => hForward a, ?_⟩
        intro a ha
        obtain ⟨b, hb⟩ := ha
        refine ⟨D.toRingEquiv.symm b, ?_⟩
        change algebraMap R K (D.toRingEquiv.symm a) * (q : K) =
          algebraMap R K (D.toRingEquiv.symm b)
        rw [h.difference_symm a, h.difference_symm b]
        calc
          _ = E.toRingEquiv.symm (algebraMap R K a * (q : K)) := by
            rw [map_mul, symm_apply_of_isConstant hq]
          _ = _ := congrArg E.toRingEquiv.symm hb
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (M := R⁰) (q : K)
    have hn : I ≠ ⊥ := by
      intro hbot
      have hm : (s : R) ∈ I := ⟨n, (mul_comm _ _).trans hs⟩
      rw [hbot, Submodule.mem_bot] at hm
      exact nonZeroDivisors.coe_ne_zero s hm
    obtain ⟨r, hr⟩ := (_root_.Ideal.eq_top_iff_one I).mp ((hD.2 I hI).resolve_left hn)
    have hr' : (q : K) = algebraMap R K r := by simpa only [map_one, one_mul] using hr
    have hrc : D.IsConstant r := by
      rw [hr'] at hq
      cases kind with
      | differential =>
        change D r = 0
        apply IsFractionRing.injective R K
        rw [h r, _root_.map_zero]
        exact hq
      | difference =>
        change D r = r
        apply IsFractionRing.injective R K
        rw [h r]
        exact hq
    exact ⟨⟨r, (mem_constantSubring D r).mpr hrc⟩, Subtype.ext hr'.symm⟩

/-- In the differential case, the total ring of fractions is a field. -/
theorem simpleDifferentialFractionField {R : Type u} {K : Type v}
    [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    (D : Operator .differential R) (hD : D.IsSimple) : IsDomain R ∧ IsField K := by
  have h := D.isDomain_of_isSimple hD
  exact ⟨h, IsFractionRing.isDomain_iff_isField.mp h⟩

end Operator

private theorem piIsFractionRing {ι : Type u} (A : ι → Type v)
    [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)] :
    IsFractionRing ((i : ι) → A i) ((i : ι) → FractionRing (A i)) := by
  classical
  have hM : ((i : ι) → A i)⁰ = Submonoid.pi Set.univ (fun i => (A i)⁰) := by
    ext a
    change a ∈ ((i : ι) → A i)⁰ ↔ ∀ i ∈ Set.univ, a i ∈ (A i)⁰
    constructor
    · intro ha i _
      apply mem_nonZeroDivisors_iff_ne_zero.mpr
      intro hi
      have hz : a * Pi.single i (1 : A i) = 0 := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [hi]
        · simp [Pi.single_eq_of_ne hj]
      have hs := mem_nonZeroDivisors_iff_left.mp ha _ hz
      simpa using congrFun hs i
    · intro ha
      apply mem_nonZeroDivisors_iff_left.mpr
      intro b hab
      funext i
      exact mem_nonZeroDivisors_iff_left.mp (ha i (Set.mem_univ i)) _ (congrFun hab i)
  change IsLocalization (((i : ι) → A i)⁰) ((i : ι) → FractionRing (A i))
  rw [hM]
  infer_instance

/-- The total fractions of a simple Noetherian difference ring form a product
of fraction fields, with the same transitive action on the factors. -/
theorem simpleDifferenceFractionComponents : Specs.simpleDifferenceFractionComponents.{u, v} := by
  intro R K _ _ _ _ _ σ τ hσ hστ
  change (Operator.difference σ).IsSimple at hσ
  obtain ⟨hfinite, hnonempty, hdomain, e, p, f, hp, ht, he, hf⟩ := simpleDifferenceComponents σ hσ
  let A (i : minimalPrimes R) := R ⧸ i.val
  let F (i : minimalPrimes R) := FractionRing (A i)
  let : ∀ i, IsDomain (A i) := hdomain
  let : IsFractionRing ((i : minimalPrimes R) → A i) ((i : minimalPrimes R) → F i) :=
    piIsFractionRing A
  let eK : K ≃+* ((i : minimalPrimes R) → F i) := Operator.fractionRingEquiv e
  have heK (x : R) (i : minimalPrimes R) :
      eK (algebraMap R K x) i = algebraMap (A i) (F i) (e x i) :=
    congrFun (Operator.fractionRingEquiv_algebraMap e x) i
  refine ⟨hfinite, hnonempty, hdomain,
    fun i => IsFractionRing.isDomain_iff_isField.mp (hdomain i),
    e, p, f, eK, hp, ht, he, hf, heK, ?_⟩
  intro q i
  let proj (j : minimalPrimes R) : K →+* F j := (Pi.evalRingHom F j).comp eK.toRingHom
  let g : F i ≃+* F (p i) := Operator.fractionRingEquiv (f i)
  have hcomp : (proj (p i)).comp τ.toRingHom = g.toRingHom.comp (proj i) := by
    apply IsLocalization.ringHom_ext R⁰
    apply RingHom.ext
    intro x
    change eK (τ (algebraMap R K x)) (p i) = g (eK (algebraMap R K x) i)
    have h : algebraMap R K (σ x) = τ (algebraMap R K x) := hστ x
    rw [← h, heK, heK]
    change algebraMap (A (p i)) (F (p i)) (e (σ x) (p i)) =
      Operator.fractionRingEquiv (K := F i) (L := F (p i)) (f i)
        (algebraMap (A i) (F i) (e x i))
    rw [Operator.fractionRingEquiv_algebraMap, hf]
  exact RingHom.congr_fun hcomp q

end GaloisFormalization.PV
