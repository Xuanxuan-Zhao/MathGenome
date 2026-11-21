import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.SerreDepthConditions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.SerreFlatTransfer
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! Flat transfer of the all-prime Serre condition (CM-11). -/
universe u
open scoped TensorProduct Pointwise
open TensorProduct
noncomputable section
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
namespace AdvCommAlg.CohenMacaulay
namespace SerreFlatTransfer

/-- The numerical Serre inequality for the maximal ideal of a local ring. -/
def LocalSerreBound (A : Type u) [CommRing A] [IsLocalRing A] (k : ℕ) : Prop :=
  min (k : WithBot ℕ∞) (ringKrullDim A) ≤
    (IsLocalRing.depth (ModuleCat.of A A) : WithBot ℕ∞)

/-- Changing rings by an isomorphism preserves local ring depth. -/
lemma ring_depth_eq_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) :
    IsLocalRing.depth (ModuleCat.of A A) = IsLocalRing.depth (ModuleCat.of B B) := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  have h : Function.Surjective (algebraMap A B) := e.surjective
  let f : A ≃ₗ[A] B :=
    { __ := e.toAddEquiv
      map_smul' := fun a b => e.map_mul a b }
  rw [← Depth.depth_eq_libraryDepth, ← Depth.depth_eq_libraryDepth]
  exact (FlatLocalDepth.depth_eq_of_linearEquiv f).trans
    (FlatLocalDepth.depth_of_surjective A B h B).symm

lemma localSerreBound_iff_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (k : ℕ) : LocalSerreBound A k ↔ LocalSerreBound B k := by
  unfold LocalSerreBound
  rw [e.ringKrullDim, ring_depth_eq_of_ringEquiv e]

/-- Localization of the regular module is the regular module of the local ring. -/
def localizedSelfEquiv (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    LocalizedModule.AtPrime p.asIdeal R ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal :=
  (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl R)
    (Algebra.linearMap R (Localization.AtPrime p.asIdeal))).extendScalarsOfIsLocalization
      p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)

/-- For rings, the canonical module Serre predicate is the usual local ring inequality. -/
lemma ringSerreCondition_iff (R : Type u) [CommRing R] [IsNoetherianRing R] (k : ℕ) :
    RingSerreCondition R k ↔
      ∀ p : PrimeSpectrum R, LocalSerreBound (Localization.AtPrime p.asIdeal) k := by
  change (∀ p : PrimeSpectrum R, p ∈ Module.support R R → _) ↔ _
  have hs : Module.support R R = Set.univ := by
    rw [Module.support_eq_zeroLocus, Module.annihilator_eq_bot.mpr inferInstance,
      PrimeSpectrum.zeroLocus_bot]
  simp only [hs, Set.mem_univ, forall_const]
  apply forall_congr'
  intro p
  rw [IsLocalRing.depth_eq_of_linearEquiv (localizedSelfEquiv R p),
    Module.supportDim_eq_of_equiv (localizedSelfEquiv R p),
    Module.supportDim_self_eq_ringKrullDim]
  rfl

/-- Ring isomorphisms transport the complete all-prime Serre condition. -/
lemma ringSerreCondition_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (e : A ≃+* B) (k : ℕ)
    (h : RingSerreCondition A k) : RingSerreCondition B k := by
  apply (ringSerreCondition_iff B k).mpr
  intro q
  let p := PrimeSpectrum.comap e.toRingHom q
  let e' : Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal :=
    Localization.localRingEquiv p.asIdeal q.asIdeal e rfl
  exact (localSerreBound_iff_of_ringEquiv e' k).mp
    ((ringSerreCondition_iff A k).mp h p)

lemma ringSerreCondition_iff_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (e : A ≃+* B) (k : ℕ) :
    RingSerreCondition A k ↔ RingSerreCondition B k :=
  ⟨ringSerreCondition_of_ringEquiv e k, ringSerreCondition_of_ringEquiv e.symm k⟩

/-- Serre's condition in a local ring implies its maximal-ideal inequality. -/
lemma localSerreBound_of_ringSerreCondition (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (k : ℕ) (h : RingSerreCondition A k) :
    LocalSerreBound A k := by
  let p := IsLocalRing.closedPoint A
  have hp := (ringSerreCondition_iff A k).mp h p
  let e : A ≃ₐ[A] Localization.AtPrime p.asIdeal :=
    IsLocalization.atUnits _ p.asIdeal.primeCompl (by
      intro a ha
      exact IsLocalRing.notMem_maximalIdeal.mp ha)
  exact (localSerreBound_iff_of_ringEquiv e.toRingEquiv k).mpr hp

/-- Localization preserves the all-prime Serre condition. -/
lemma ringSerreCondition_localization (R : Type u) [CommRing R] [IsNoetherianRing R]
    (k : ℕ) (h : RingSerreCondition R k) (p : PrimeSpectrum R) :
    RingSerreCondition (Localization.AtPrime p.asIdeal) k := by
  apply (ringSerreCondition_iff _ k).mpr
  intro q
  let e : Localization.AtPrime (q.asIdeal.comap (algebraMap R _)) ≃ₐ[R]
      Localization.AtPrime q.asIdeal :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization p.asIdeal.primeCompl q.asIdeal
  have hq : LocalSerreBound
      (Localization.AtPrime (q.asIdeal.comap (algebraMap R (Localization.AtPrime p.asIdeal)))) k :=
    (ringSerreCondition_iff R k).mp h
      (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q)
  exact (localSerreBound_iff_of_ringEquiv e.toRingEquiv k).mp hq

/-- Ring specialization of both flat local family formulas. -/
lemma flatLocal_ring_formulas (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B] :
    let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
    letI := Specs.closedFiberLocalRing A B
    ringKrullDim B = ringKrullDim A + ringKrullDim (B ⧸ J) ∧
    IsLocalRing.depth (ModuleCat.of B B) = IsLocalRing.depth (ModuleCat.of A A) +
      IsLocalRing.depth (ModuleCat.of (B ⧸ J) (B ⧸ J)) := by
  let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  letI := Specs.closedFiberLocalRing A B
  letI := RegularSequence.Specs.rightTensorModule (R := A) (S := B) A B
  letI := Specs.rightTensorFinite A B A B
  let F := B ⧸ (J • (⊤ : Submodule B B))
  letI : Module.Finite (B ⧸ J) F := Module.Finite.of_restrictScalars_finite B (B ⧸ J) F
  let e : (A ⊗[A] B) ≃ₗ[B] B :=
    RegularSequence.rightTensorComm (S := B) A B ≪≫ₗ AlgebraTensorModule.rid A B B
  have hdim := flatLocal_tensor_dimension A B A B
  have hdepth := flatLocal_tensor_depth A B A B
  change Module.supportDim B (A ⊗[A] B) = Module.supportDim A A +
    Module.supportDim (B ⧸ J) F at hdim
  change Depth.depth B (A ⊗[A] B) = Depth.depth A A + Depth.depth (B ⧸ J) F at hdepth
  rw [Module.supportDim_eq_of_equiv e,
    Module.supportDim_eq_of_equiv (quotientSelfEquiv B J),
    Module.supportDim_self_eq_ringKrullDim, Module.supportDim_self_eq_ringKrullDim,
    Module.supportDim_self_eq_ringKrullDim] at hdim
  rw [FlatLocalDepth.depth_eq_of_linearEquiv e,
    FlatLocalDepth.depth_eq_of_linearEquiv (quotientSelfEquiv B J),
    Depth.depth_eq_libraryDepth (ModuleCat.of B B),
    Depth.depth_eq_libraryDepth (ModuleCat.of A A),
    Depth.depth_eq_libraryDepth (ModuleCat.of (B ⧸ J) (B ⧸ J))] at hdepth
  exact ⟨hdim, hdepth⟩

/-- The elementary inequality used to add the two depth bounds. -/
lemma min_le_add_min (k : ℕ) {a b : WithBot ℕ∞} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min (k : WithBot ℕ∞) (a + b) ≤ min (k : WithBot ℕ∞) a + min (k : WithBot ℕ∞) b := by
  have hk : (0 : WithBot ℕ∞) ≤ k := by exact_mod_cast (Nat.zero_le k)
  by_cases hka : (k : WithBot ℕ∞) ≤ a
  · rw [min_eq_left hka]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (le_min hk hb))
  · by_cases hkb : (k : WithBot ℕ∞) ≤ b
    · rw [min_eq_left hkb]
      exact (min_le_left _ _).trans (le_add_of_nonneg_left (le_min hk ha))
    · rw [min_eq_right (le_of_not_ge hka), min_eq_right (le_of_not_ge hkb)]
      exact min_le_right _ _

/-- Local ascent is the sum of the base and closed-fiber inequalities. -/
lemma localSerreBound_flatLocal_ascent (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (k : ℕ) (hA : LocalSerreBound A k) :
    let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
    letI := Specs.closedFiberLocalRing A B
    LocalSerreBound (B ⧸ J) k → LocalSerreBound B k := by
  let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  letI := Specs.closedFiberLocalRing A B
  change LocalSerreBound (B ⧸ J) k → LocalSerreBound B k
  intro hF
  obtain ⟨hdim, hdepth⟩ := flatLocal_ring_formulas A B
  unfold LocalSerreBound at hA hF ⊢
  rw [hdim, hdepth]
  exact (min_le_add_min k ringKrullDim_nonneg_of_nontrivial
    ringKrullDim_nonneg_of_nontrivial).trans (by exact_mod_cast add_le_add hA hF)

/-- A zero-dimensional closed fiber makes the local Serre bound descend. -/
lemma localSerreBound_flatLocal_descent (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (k : ℕ) (hB : LocalSerreBound B k)
    (hF : ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) = 0) :
    LocalSerreBound A k := by
  let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  letI := Specs.closedFiberLocalRing A B
  obtain ⟨hdim, hdepth⟩ := flatLocal_ring_formulas A B
  have hz : IsLocalRing.depth (ModuleCat.of (B ⧸ J) (B ⧸ J)) = 0 := by
    have h := Depth.depth_le_supportDim (R := B ⧸ J) (B ⧸ J)
    rw [Depth.depth_eq_libraryDepth (ModuleCat.of (B ⧸ J) (B ⧸ J)),
      Module.supportDim_self_eq_ringKrullDim, hF] at h
    exact le_antisymm (WithBot.coe_le_coe.mp h) zero_le
  change IsLocalRing.depth (ModuleCat.of B B) =
    IsLocalRing.depth (ModuleCat.of A A) +
      IsLocalRing.depth (ModuleCat.of (B ⧸ J) (B ⧸ J)) at hdepth
  rw [hz, add_zero] at hdepth
  unfold LocalSerreBound at hB ⊢
  rw [hdim, hdepth] at hB
  simpa only [hF, add_zero] using hB

section LocalizedMaps
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)]

lemma localizedMap_isLocalHom :
    IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
  rw [Localization.AtPrime.algebraMap_eq p q]
  exact Localization.isLocalHom_localRingHom p q (algebraMap R S) Ideal.LiesOver.over

lemma localizedMap_flat [Module.Flat R S] :
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
  (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
    (Localization.AtPrime q)).mpr inferInstance

lemma localized_closedFiberIdeal :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) =
      p.map (algebraMap R (Localization.AtPrime q)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]
end LocalizedMaps

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The contraction of a prime in the fiber lies over the specified base prime. -/
lemma fiberPrime_liesOver (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (r : PrimeSpectrum (p.asIdeal.Fiber S)) :
    (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom r).asIdeal.LiesOver
      p.asIdeal := by
  change (r.asIdeal.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S)).LiesOver
    p.asIdeal
  exact Ideal.comap_liesOver r.asIdeal p.asIdeal
    (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S)

/-- The local closed fiber at a fiber prime is the localization of the global fiber. -/
def fiberLocalEquiv (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (r : PrimeSpectrum (p.asIdeal.Fiber S)) :
    let q := PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom r
    letI : q.asIdeal.LiesOver p.asIdeal := fiberPrime_liesOver R S p r
    letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
    Localization.AtPrime r.asIdeal ≃+*
      ((Localization.AtPrime q.asIdeal) ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map
          (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))) := by
  let q := PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom r
  letI : q.asIdeal.LiesOver p.asIdeal := fiberPrime_liesOver R S p r
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  have hJ := localized_closedFiberIdeal R S p.asIdeal q.asIdeal
  have hJ' : (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) =
      (p.asIdeal.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime q.asIdeal)) := by
    rw [hJ, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  exact (Ideal.Fiber.algEquivAux₂ (R := R) (S := S) p.asIdeal r.asIdeal).toRingEquiv.trans
    (Ideal.quotientEquivAlgOfEq R hJ'.symm).toRingEquiv

/-- Global Serre bounds on a fiber supply the needed local closed-fiber bound. -/
lemma localSerreBound_of_fiber (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] (p : PrimeSpectrum R)
    (r : PrimeSpectrum (p.asIdeal.Fiber S)) (k : ℕ)
    (hF : letI := Specs.fiberNoetherian R S p
      RingSerreCondition (p.asIdeal.Fiber S) k) :
    let q := PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom r
    letI : q.asIdeal.LiesOver p.asIdeal := fiberPrime_liesOver R S p r
    letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
    letI := localizedMap_isLocalHom R S p.asIdeal q.asIdeal
    letI := Specs.closedFiberLocalRing (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
    LocalSerreBound
      ((Localization.AtPrime q.asIdeal) ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map
          (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))) k := by
  letI := Specs.fiberNoetherian R S p
  let q := PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom r
  letI : q.asIdeal.LiesOver p.asIdeal := fiberPrime_liesOver R S p r
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI := localizedMap_isLocalHom R S p.asIdeal q.asIdeal
  letI := Specs.closedFiberLocalRing (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
  exact (localSerreBound_iff_of_ringEquiv (fiberLocalEquiv R S p r) k).mp
    ((ringSerreCondition_iff (p.asIdeal.Fiber S) k).mp hF r)

/-- Ascent at the point corresponding to a prime in a fiber. -/
lemma localSerreBound_at_fiberPrime (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (k : ℕ) (hR : RingSerreCondition R k) (p : PrimeSpectrum R)
    (hF : letI := Specs.fiberNoetherian R S p
      RingSerreCondition (p.asIdeal.Fiber S) k)
    (r : PrimeSpectrum (p.asIdeal.Fiber S)) :
    LocalSerreBound (Localization.AtPrime
      (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom r).asIdeal) k := by
  let q := PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom r
  letI : q.asIdeal.LiesOver p.asIdeal := fiberPrime_liesOver R S p r
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI := localizedMap_isLocalHom R S p.asIdeal q.asIdeal
  letI := localizedMap_flat R S p.asIdeal q.asIdeal
  exact localSerreBound_flatLocal_ascent (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime q.asIdeal) k ((ringSerreCondition_iff R k).mp hR p)
      (localSerreBound_of_fiber R S p r k hF)

/-- If base and every fiber satisfy `(S_k)`, the flat target satisfies `(S_k)`. -/
theorem _root_.AdvCommAlg.CohenMacaulay.ringSerreCondition_flat_ascent : Specs.ringSerreCondition_flat_ascentType.{u} := by
  intro R S _ _ _ _ _ _ k hR hF
  change RingSerreCondition S k
  apply (ringSerreCondition_iff S k).mpr
  intro q
  let p := PrimeSpectrum.comap (algebraMap R S) q
  let e := PrimeSpectrum.preimageEquivFiber R S p
  let r := e ⟨q, rfl⟩
  have hr : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom r = q :=
    congrArg Subtype.val (e.symm_apply_apply ⟨q, rfl⟩)
  letI := Specs.fiberNoetherian R S p
  letI := Specs.rightFiberNoetherian R S p
  have hF' : RingSerreCondition (p.asIdeal.Fiber S) k :=
    (ringSerreCondition_iff_of_ringEquiv
      (Algebra.TensorProduct.comm R p.asIdeal.ResidueField S).toRingEquiv k).mpr (hF p)
  have h := localSerreBound_at_fiberPrime R S k hR p hF' r
  change LocalSerreBound (Localization.AtPrime
    (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom r).asIdeal) k at h
  exact hr ▸ h

/-- Faithful flat descent uses a prime minimal in each fiber. -/
lemma ringSerreCondition_faithfullyFlat_descent (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.FaithfullyFlat R S]
    (k : ℕ) (hS : RingSerreCondition S k) : RingSerreCondition R k := by
  apply (ringSerreCondition_iff R k).mpr
  intro p
  letI := Specs.fiberNoetherian R S p
  obtain ⟨q₀, hq₀⟩ :=
    (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S)) p
  let r₀ := PrimeSpectrum.preimageEquivFiber R S p ⟨q₀, hq₀⟩
  obtain ⟨J, hJ, _⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (p.asIdeal.Fiber S)))
    (J := r₀.asIdeal) bot_le
  let r : PrimeSpectrum (p.asIdeal.Fiber S) := ⟨J, hJ.isPrime⟩
  letI : r.asIdeal.IsPrime := r.isPrime
  let q := PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom r
  letI : q.asIdeal.LiesOver p.asIdeal := fiberPrime_liesOver R S p r
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI := localizedMap_isLocalHom R S p.asIdeal q.asIdeal
  letI := localizedMap_flat R S p.asIdeal q.asIdeal
  letI := Specs.closedFiberLocalRing (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
  have hd : ringKrullDim (Localization.AtPrime r.asIdeal) = 0 := by
    letI : Ring.KrullDimLE 0 (Localization.AtPrime r.asIdeal) :=
      Ring.KrullDimLE.of_isLocalization J hJ (Localization.AtPrime r.asIdeal)
    exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  have hfiber : ringKrullDim
      ((Localization.AtPrime q.asIdeal) ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map
          (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))) = 0 :=
    (fiberLocalEquiv R S p r).ringKrullDim.symm.trans hd
  exact localSerreBound_flatLocal_descent (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime q.asIdeal) k ((ringSerreCondition_iff S k).mp hS q) hfiber

/-- Primewise flat descent requires no faithful flatness of the global map. -/
theorem _root_.AdvCommAlg.CohenMacaulay.ringSerreCondition_localization_descent :
    Specs.ringSerreCondition_localization_descentType.{u} := by
  intro R S _ _ _ _ _ _ k q hS
  let p := PrimeSpectrum.comap (algebraMap R S) q
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI := localizedMap_isLocalHom R S p.asIdeal q.asIdeal
  letI := localizedMap_flat R S p.asIdeal q.asIdeal
  letI := faithfullyFlat_of_flatLocal (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)
  exact ringSerreCondition_faithfullyFlat_descent (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime q.asIdeal) k hS

end SerreFlatTransfer
end AdvCommAlg.CohenMacaulay
