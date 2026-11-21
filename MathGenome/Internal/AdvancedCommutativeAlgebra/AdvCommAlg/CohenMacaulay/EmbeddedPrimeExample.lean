import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.EmbeddedPrimeExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.SerreDepthConditions
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

universe u
namespace AdvCommAlg.CohenMacaulay.EmbeddedPrimeExample
open Polynomial
variable (k : Type u) [Field k]

/-- The kernel description really is the coordinate origin `(x,y)`. -/
theorem ambientOrigin_eq_span : ambientOrigin k =
    Ideal.span {X, C (X : Polynomial k)} := by
  ext p
  have h := Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero
    (a := (0 : k)) (b := (0 : Polynomial k)) (P := p)
  simpa [ambientOrigin, RingHom.mem_ker, Ideal.span_pair_comm] using h.symm

/-- Factor out `x`, allowing cancellation in the ambient polynomial domain. -/
theorem relations_eq_product : relations k =
    Ideal.span {(X : Ambient k)} * ambientOrigin k := by
  rw [ambientOrigin_eq_span, Ideal.span_insert, Ideal.mul_sup,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_insert]
  simp [relations, pow_two]

theorem mul_X_mem_relations_iff (p : Ambient k) :
    p * X ∈ relations k ↔ p ∈ ambientOrigin k := by
  rw [relations_eq_product, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨q, hq, heq⟩
    have : q = p := mul_left_cancel₀ (Polynomial.X_ne_zero) (heq.trans (mul_comm p X))
    simpa [this] using hq
  · intro hp
    exact ⟨p, hp, mul_comm _ _⟩

/-- Multiplication by the nonzero coordinate class detects the maximal ideal. -/
theorem mul_xBar_eq_zero_iff (a : CoordinateRing k) :
    a * xBar k = 0 ↔ a ∈ origin k := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [xBar, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, mul_X_mem_relations_iff]
  exact (Ideal.mem_quotient_iff_mem (relations_le_ambientOrigin k)).symm

theorem xBar_ne_zero : xBar k ≠ 0 := by
  intro h
  have : (1 : CoordinateRing k) ∈ origin k :=
    (mul_xBar_eq_zero_iff k 1).mp (by simpa using h)
  exact (origin_isMaximal k).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

theorem x_ne_zero : x k ≠ 0 := by
  intro hx
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (origin k).primeCompl
    (LocalRing k) (xBar k)).mp hx
  exact s.property ((mul_xBar_eq_zero_iff k s).mp hs)

theorem x_sq : x k ^ 2 = 0 := by
  rw [x, ← map_pow, xBar, ← map_pow]
  have h : Ideal.Quotient.mk (relations k) (X ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  rw [h, map_zero]

theorem x_mul_y : x k * y k = 0 := by
  rw [x, y, ← map_mul, xBar, yBar, ← map_mul]
  have h : Ideal.Quotient.mk (relations k) (X * C (X : Polynomial k)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  rw [h, map_zero]

theorem origin_eq_span : origin k = Ideal.span {xBar k, yBar k} := by
  rw [origin, ambientOrigin_eq_span, Ideal.map_span]
  simp [Set.image_insert_eq, Set.image_singleton, xBar, yBar]

theorem maximalIdeal_eq_span : IsLocalRing.maximalIdeal (LocalRing k) =
    Ideal.span {x k, y k} := by
  calc
    _ = (origin k).map (algebraMap (CoordinateRing k) (LocalRing k)) :=
      (Localization.AtPrime.map_eq_maximalIdeal (I := origin k)).symm
    _ = (Ideal.span {xBar k, yBar k}).map
        (algebraMap (CoordinateRing k) (LocalRing k)) :=
      congrArg (Ideal.map (algebraMap (CoordinateRing k) (LocalRing k))) (origin_eq_span k)
    _ = _ := by simp [Ideal.map_span, x, y]

theorem annihilator_x : (⊥ : Submodule (LocalRing k) (LocalRing k)).colon {x k} =
    IsLocalRing.maximalIdeal (LocalRing k) := by
  apply le_antisymm
  · apply IsLocalRing.le_maximalIdeal
    intro h
    have h1 : (1 : LocalRing k) ∈
        (⊥ : Submodule (LocalRing k) (LocalRing k)).colon {x k} := by simp [h]
    exact x_ne_zero k (by simpa [Submodule.mem_colon_singleton] using h1)
  · rw [maximalIdeal_eq_span]
    apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ⟨rfl⟩
    · simpa [Submodule.mem_colon_singleton, smul_eq_mul, ← pow_two] using x_sq k
    · simpa [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using x_mul_y k

theorem maximalIdeal_associated : IsLocalRing.maximalIdeal (LocalRing k) ∈
    associatedPrimes (LocalRing k) (LocalRing k) := by
  apply isAssociatedPrime_iff.mpr
  exact ⟨inferInstance, x k, (annihilator_x k).symm⟩

theorem depth_eq_zero : AdvCommAlg.Depth.depth (LocalRing k) (LocalRing k) = 0 := by
  apply (AdvCommAlg.Depth.depth_zero_iff_socle_ne_bot (LocalRing k) (LocalRing k)).mpr
  intro hbot
  have hx : x k ∈ Submodule.torsionBySet (LocalRing k) (LocalRing k)
      (IsLocalRing.maximalIdeal (LocalRing k) : Set (LocalRing k)) := by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have ha : (a : LocalRing k) ∈
        (⊥ : Submodule (LocalRing k) (LocalRing k)).colon {x k} := by
      rw [annihilator_x]
      exact a.property
    simpa [Submodule.mem_colon_singleton] using ha
  exact x_ne_zero k (by simpa [hbot] using hx)

/-- The quotient map obtained by setting `x = 0` (and retaining `y`). -/
noncomputable def reduction : CoordinateRing k →+* Polynomial k :=
  Ideal.Quotient.lift (relations k) (evalRingHom 0) (by
    intro p hp
    have hle : relations k ≤ Ideal.span {(X : Ambient k)} := by
      rw [relations_eq_product]
      exact Ideal.mul_le_left
    have : p ∈ RingHom.ker (evalRingHom (0 : Polynomial k)) := by
      simpa [Polynomial.ker_evalRingHom] using hle hp
    exact this)

@[simp] theorem reduction_mk (p : Ambient k) :
    reduction k (Ideal.Quotient.mk (relations k) p) = p.eval 0 := rfl

theorem reduction_surjective : Function.Surjective (reduction k) := by
  intro p
  exact ⟨Ideal.Quotient.mk (relations k) (C p), by simp⟩

theorem ker_reduction : RingHom.ker (reduction k) = Ideal.span {xBar k} := by
  rw [reduction, Ideal.ker_quotient_lift]
  simp [Polynomial.ker_evalRingHom, Ideal.map_span, xBar]

instance span_xBar_isPrime : (Ideal.span {xBar k}).IsPrime := by
  rw [← ker_reduction]
  exact RingHom.ker_isPrime _

theorem span_xBar_le_origin : Ideal.span {xBar k} ≤ origin k := by
  rw [origin_eq_span]
  exact Ideal.span_mono (by simp)

theorem yBar_not_mem_span_xBar : yBar k ∉ Ideal.span {xBar k} := by
  rw [← ker_reduction, RingHom.mem_ker]
  simp [yBar]

/-- The coordinate `x` is nilpotent even before localization. -/
theorem xBar_sq : xBar k ^ 2 = 0 := by
  rw [xBar, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

/-- Every prime contains `x`, as required for the correspondence with `k[y]`. -/
theorem span_xBar_le_prime (p : PrimeSpectrum (CoordinateRing k)) :
    Ideal.span {xBar k} ≤ p.asIdeal := by
  apply Ideal.span_le.mpr
  rintro a ⟨rfl⟩
  exact p.isPrime.mem_of_pow_mem 2 (by rw [xBar_sq]; exact p.asIdeal.zero_mem)

/-- The nilpotent coordinate introduces no extra primes. -/
noncomputable def primeSpectrumPolynomial :
    PrimeSpectrum (CoordinateRing k) ≃o PrimeSpectrum (Polynomial k) :=
  let e := Ideal.primeSpectrumOrderIsoZeroLocusOfSurj (reduction k)
    (reduction_surjective k) (ker_reduction k)
  let g : PrimeSpectrum (CoordinateRing k) ≃o
      PrimeSpectrum.zeroLocus (Ideal.span {xBar k}) :=
    { toFun := fun p => ⟨p, (PrimeSpectrum.mem_zeroLocus p _).mpr (span_xBar_le_prime k p)⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  g.trans e.symm

theorem coordinateRing_dimension : ringKrullDim (CoordinateRing k) = 1 := by
  calc
    _ = ringKrullDim (Polynomial k) := Order.krullDim_eq_of_orderIso (primeSpectrumPolynomial k)
    _ = 1 := by simp

private lemma span_xBar_disjoint :
    Disjoint ((origin k).primeCompl : Set (CoordinateRing k))
      (Ideal.span {xBar k} : Set (CoordinateRing k)) := by
  apply Set.disjoint_left.mpr
  intro a ha hx
  exact ha (span_xBar_le_origin k hx)

theorem map_span_xBar :
    (Ideal.span {xBar k}).map (algebraMap (CoordinateRing k) (LocalRing k)) =
      Ideal.span {x k} := by simp [Ideal.map_span, x]

instance span_x_isPrime : (Ideal.span {x k}).IsPrime := by
  rw [← map_span_xBar]
  exact IsLocalization.isPrime_of_isPrime_disjoint (origin k).primeCompl (LocalRing k)
    _ (span_xBar_isPrime k) (span_xBar_disjoint k)

theorem comap_span_x :
    (Ideal.span {x k}).comap (algebraMap (CoordinateRing k) (LocalRing k)) =
      Ideal.span {xBar k} := by
  rw [← map_span_xBar]
  exact IsLocalization.under_map_of_isPrime_disjoint (origin k).primeCompl (LocalRing k)
    (span_xBar_isPrime k) (span_xBar_disjoint k)

theorem y_not_mem_span_x : y k ∉ Ideal.span {x k} := by
  intro h
  have hy : yBar k ∈
      (Ideal.span {x k}).comap (algebraMap (CoordinateRing k) (LocalRing k)) := h
  rw [comap_span_x] at hy
  exact yBar_not_mem_span_xBar k hy

theorem span_x_lt_maximalIdeal :
    Ideal.span {x k} < IsLocalRing.maximalIdeal (LocalRing k) := by
  apply lt_of_le_of_ne
  · rw [maximalIdeal_eq_span]
    exact Ideal.span_mono (by simp)
  · intro heq
    apply y_not_mem_span_x k
    rw [heq, maximalIdeal_eq_span]
    exact Ideal.subset_span (by simp)

theorem localRing_dimension : ringKrullDim (LocalRing k) = 1 := by
  apply le_antisymm
  · apply le_trans (b := ringKrullDim (CoordinateRing k))
    · let e := IsLocalization.AtPrime.primeSpectrumOrderIso (LocalRing k) (origin k)
      exact Order.krullDim_le_of_strictMono (fun p => (e p).val)
        (fun _ _ h => e.strictMono h)
    · exact le_of_eq (coordinateRing_dimension k)
  · apply Order.one_le_krullDim_iff.mpr
    exact ⟨⟨Ideal.span {x k}, span_x_isPrime k⟩,
      IsLocalRing.closedPoint (LocalRing k), span_x_lt_maximalIdeal k⟩

theorem span_x_le_prime (p : PrimeSpectrum (LocalRing k)) :
    Ideal.span {x k} ≤ p.asIdeal := by
  apply Ideal.span_le.mpr
  rintro a ⟨rfl⟩
  exact p.isPrime.mem_of_pow_mem 2 (by rw [x_sq]; exact p.asIdeal.zero_mem)

theorem minimalPrimes_eq_singleton :
    minimalPrimes (LocalRing k) = {Ideal.span {x k}} := by
  ext p
  constructor
  · intro hp
    apply Set.mem_singleton_iff.mpr
    have hle := span_x_le_prime k ⟨p, hp.isPrime⟩
    exact le_antisymm (hp.2 ⟨span_x_isPrime k, bot_le⟩ hle) hle
  · rintro ⟨rfl⟩
    exact ⟨⟨span_x_isPrime k, bot_le⟩,
      fun q hq _ => span_x_le_prime k ⟨q, hq.1⟩⟩

theorem not_serreCondition_one : ¬ RingSerreCondition (LocalRing k) 1 := by
  intro hs
  have h := (serreCondition_one_iff_associatedPrimes_eq_minimalPrimes
    (LocalRing k) (LocalRing k)).mp hs
  have hm := maximalIdeal_associated k
  have hz : Module.annihilator (LocalRing k) (LocalRing k) = ⊥ :=
    Module.annihilator_eq_bot.mpr inferInstance
  rw [h, hz] at hm
  change IsLocalRing.maximalIdeal (LocalRing k) ∈ minimalPrimes (LocalRing k) at hm
  rw [minimalPrimes_eq_singleton, Set.mem_singleton_iff] at hm
  exact (span_x_lt_maximalIdeal k).ne hm.symm

/-- All conclusions of the embedded-prime example, over every field. -/
theorem embeddedPrimeExample : Specs.embeddedPrimeExampleType.{u} := by
  intro k _
  exact ⟨inferInstance, inferInstance, localRing_dimension k, depth_eq_zero k,
    x_ne_zero k, annihilator_x k, minimalPrimes_eq_singleton k,
    maximalIdeal_associated k, span_x_lt_maximalIdeal k, not_serreCondition_one k⟩

end AdvCommAlg.CohenMacaulay.EmbeddedPrimeExample
