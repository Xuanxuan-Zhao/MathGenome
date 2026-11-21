import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.FiberProductRegularInCodimensionOne
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.Definitions
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Tactic.LinearCombination

noncomputable section
universe u v w
namespace AdvCommAlg.Normality.FiberProduct

/-- The two projection kernels of a pullback annihilate one another. -/
theorem pullback_kernels_mul {B : Type u} {C : Type v} {D : Type w}
    [CommRing B] [CommRing C] [CommRing D] (f : B →+* D) (g : C →+* D) :
    RingHom.ker (f.pullbackFst g) * RingHom.ker (f.pullbackSnd g) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Ideal.mul_le.mpr
  intro a ha b hb
  change a * b = 0
  apply Subtype.ext
  apply Prod.ext
  · change a.val.1 * b.val.1 = 0
    change a.val.1 = 0 at ha
    simp [ha]
  · change a.val.2 * b.val.2 = 0
    change b.val.2 = 0 at hb
    simp [hb]

/-- The kernel of the common residue map is the sum of the projection kernels. -/
theorem pullback_kernels_sup {B : Type u} {C : Type v} {D : Type w}
    [CommRing B] [CommRing C] [CommRing D] (f : B →+* D) (g : C →+* D) :
    RingHom.ker (f.pullbackFst g) ⊔ RingHom.ker (f.pullbackSnd g) =
      RingHom.ker (f.comp (f.pullbackFst g)) := by
  apply le_antisymm
  · apply sup_le
    · intro a ha
      change f a.val.1 = 0
      change a.val.1 = 0 at ha
      simp [ha]
    · intro a ha
      change f a.val.1 = 0
      change a.val.2 = 0 at ha
      have hab : f a.val.1 = g a.val.2 := a.property
      rw [hab, ha, map_zero]
  · intro a ha
    change f a.val.1 = 0 at ha
    have hb : g a.val.2 = 0 := a.property.symm.trans ha
    let b : f.pullback g := ⟨(0, a.val.2), by simpa using hb.symm⟩
    let c : f.pullback g := ⟨(a.val.1, 0), by simpa using ha⟩
    have hbc : a = b + c := by ext <;> simp [b, c]
    rw [hbc]
    exact Submodule.add_mem_sup (show b ∈ RingHom.ker (f.pullbackFst g) from rfl)
      (show c ∈ RingHom.ker (f.pullbackSnd g) from rfl)

/-- Both projections together are injective. -/
theorem pullback_kernels_inf {B : Type u} {C : Type v} {D : Type w}
    [CommRing B] [CommRing C] [CommRing D] (f : B →+* D) (g : C →+* D) :
    RingHom.ker (f.pullbackFst g) ⊓ RingHom.ker (f.pullbackSnd g) = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  change a = 0
  apply Subtype.ext
  exact Prod.ext ha.1 ha.2

/-- A pullback of two Noetherian rings along surjections is Noetherian.
For any ideal `J`, first generate its intersection with the first projection
kernel using the second projection, which is injective on that intersection.
Then generate `J` using its first projection and this intersection. -/
theorem pullback_isNoetherianRing {B : Type u} {C : Type v} {D : Type w}
    [CommRing B] [CommRing C] [CommRing D] [IsNoetherianRing B] [IsNoetherianRing C]
    (f : B →+* D) (g : C →+* D) (hf : Function.Surjective f)
    (hg : Function.Surjective g) : IsNoetherianRing (f.pullback g) := by
  apply (isNoetherianRing_iff_ideal_fg _).mpr
  intro J
  have hfst := RingHom.surjective_pullbackFst_of_surjective f g hg
  have hsnd := RingHom.surjective_pullbackSnd_of_surjective f g hf
  apply Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective
    ((J.map (f.pullbackFst g)).fg_of_isNoetherianRing) _ hfst
  apply Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective
    (((J ⊓ RingHom.ker (f.pullbackFst g)).map (f.pullbackSnd g)).fg_of_isNoetherianRing)
    _ hsnd
  simp only [inf_assoc, pullback_kernels_inf, inf_bot_eq]
  exact Submodule.fg_bot

/-- A surjection induces an isomorphism of local rings if an element outside
its contracted prime annihilates its kernel. -/
theorem localRingHom_bijective_of_annihilator
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap f)
    (ha : ∃ a : R, a ∉ p ∧ ∀ x ∈ RingHom.ker f, a * x = 0) :
    Function.Bijective (Localization.localRingHom p q f hpq) := by
  constructor
  · apply IsLocalization.injective_of_map_algebraMap_zero
      (M := p.primeCompl) (Localization.AtPrime p)
    intro x hx
    rw [Localization.localRingHom_to_map] at hx
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl
      (Localization.AtPrime q) (f x)).mp hx
    obtain ⟨s, hs⟩ := hf t.val
    have hsp : s ∉ p := by
      rw [hpq]
      change f s ∉ q
      rw [hs]
      exact t.property
    have hker : s * x ∈ RingHom.ker f := by
      change f (s * x) = 0
      simpa [map_mul, hs] using ht
    obtain ⟨a, hap, hak⟩ := ha
    apply (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) x).mpr
    exact ⟨⟨a * s, (inferInstance : p.IsPrime).mul_notMem hap hsp⟩,
      by simpa [mul_assoc] using hak (s * x) hker⟩
  · intro z
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl z
    obtain ⟨a, rfl⟩ := hf b
    obtain ⟨s, hs⟩ := hf t.val
    have hsp : s ∉ p := by
      rw [hpq]
      change f s ∉ q
      rw [hs]
      exact t.property
    refine ⟨IsLocalization.mk' (M := p.primeCompl) (Localization.AtPrime p) a ⟨s, hsp⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs

/-- The isomorphism also identifies the heights of the two primes. -/
theorem height_eq_of_localization_equiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (e : Localization.AtPrime p ≃+* Localization.AtPrime q) : q.height = p.height := by
  have h := ringKrullDim_eq_of_ringEquiv e
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p,
    IsLocalization.AtPrime.ringKrullDim_eq_height q] at h
  exact WithBot.coe_injective h.symm

/-- A prime chain contained in one component is bounded by that component's
Krull dimension. No finite-dimensionality assumption is needed. -/
theorem length_le_dimension_of_ker_le_head
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (c : LTSeries (PrimeSpectrum R)) (hk : RingHom.ker f ≤ c.head.asIdeal) :
    (c.length : WithBot ℕ∞) ≤ ringKrullDim S := by
  have hk' (i : Fin (c.length + 1)) : RingHom.ker f ≤ (c i).asIdeal :=
    hk.trans (c.head_le i)
  let d : LTSeries (PrimeSpectrum S) := LTSeries.mk c.length
    (fun i => ⟨(c i).asIdeal.map f, Ideal.map_isPrime_of_surjective hf (hk' i)⟩) (by
      intro i j hij
      have h := c.strictMono hij
      apply lt_of_le_of_ne (Ideal.map_mono h.le)
      intro heq
      have hcom (i : Fin (c.length + 1)) : ((c i).asIdeal.map f).comap f = (c i).asIdeal := by
        rw [Ideal.comap_map_of_surjective _ hf, ← RingHom.ker_eq_comap_bot,
          sup_eq_left.mpr (hk' i)]
      have hij' : (c i).asIdeal = (c j).asIdeal := by
        rw [← hcom i, ← hcom j, heq]
      exact h.ne (PrimeSpectrum.ext hij'))
  exact Order.LTSeries.length_le_krullDim d

/-- The spectrum of a pullback with surjective projections is the union of
its two components, so its dimension is their maximum. -/
theorem pullback_dimension {B : Type u} {C : Type v} {D : Type w}
    [CommRing B] [CommRing C] [CommRing D]
    (f : B →+* D) (g : C →+* D) (hf : Function.Surjective f)
    (hg : Function.Surjective g) :
    ringKrullDim (f.pullback g) = max (ringKrullDim B) (ringKrullDim C) := by
  have hfst := RingHom.surjective_pullbackFst_of_surjective f g hg
  have hsnd := RingHom.surjective_pullbackSnd_of_surjective f g hf
  apply le_antisymm
  · change (⨆ c : LTSeries (PrimeSpectrum (f.pullback g)),
      (c.length : WithBot ℕ∞)) ≤ _
    apply iSup_le
    intro c
    have hor : RingHom.ker (f.pullbackFst g) ≤ c.head.asIdeal ∨
        RingHom.ker (f.pullbackSnd g) ≤ c.head.asIdeal :=
      c.head.isPrime.mul_le.mp (by rw [pullback_kernels_mul]; exact bot_le)
    rcases hor with h | h
    · exact (length_le_dimension_of_ker_le_head _ hfst c h).trans (le_max_left _ _)
    · exact (length_le_dimension_of_ker_le_head _ hsnd c h).trans (le_max_right _ _)
  · exact max_le (ringKrullDim_le_of_surjective _ hfst) (ringKrullDim_le_of_surjective _ hsnd)

variable (k : Type u) [Field k]

theorem planeResidue_surjective : Function.Surjective (planeResidue k) := by
  intro a
  exact ⟨algebraMap (PolynomialRing k 2) (LocalPlane k) (MvPolynomial.C a), by
    simp [planeResidue]⟩

instance planeResidue_isLocalHom : IsLocalHom (planeResidue k) :=
  IsLocalHom.of_surjective _ (planeResidue_surjective k)

instance ring_isLocalRing : IsLocalRing (Ring k) :=
  RingHom.isLocalRing_pullback _ _

instance plane_isNoetherianRing : IsNoetherianRing (LocalPlane k) := inferInstance


instance ring_isNoetherianRing : IsNoetherianRing (Ring k) :=
  pullback_isNoetherianRing _ _ (planeResidue_surjective k) (planeResidue_surjective k)

instance plane_isRegularRing : IsRegularRing (LocalPlane k) := by
  apply isRegularRing_iff.mpr
  intro p hp
  let q := p.comap (algebraMap (PolynomialRing k 2) (LocalPlane k))
  let e := IsLocalization.algEquiv q.primeCompl
    (Localization.AtPrime p) (Localization.AtPrime q)
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm

/-- The local affine plane at its origin has dimension two. -/
theorem plane_dimension : ringKrullDim (LocalPlane k) = 2 := by
  let I : Ideal (PolynomialRing k 2) := Ideal.span {MvPolynomial.X (0 : Fin 2)}
  have hI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime (MvPolynomial.X_prime (i := 0))
  have h0I : (⊥ : Ideal (PolynomialRing k 2)) < I := by
    apply bot_lt_iff_ne_bot.mpr
    intro heq
    have h : MvPolynomial.X (0 : Fin 2) ∈ I := Ideal.subset_span (by simp)
    rw [heq] at h
    exact MvPolynomial.X_ne_zero _ h
  have hIo : I < origin k 2 := by
    apply lt_of_le_of_ne
    · apply Ideal.span_le.mpr
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      simp [origin]
    · intro heq
      have h : MvPolynomial.X (1 : Fin 2) ∈ origin k 2 := by simp [origin]
      rw [← heq, Ideal.mem_span_singleton] at h
      have h01 := MvPolynomial.X_dvd_X.mp h
      norm_num at h01
  have h1 : (1 : ℕ∞) ≤ I.height := by
    simpa using Ideal.height_add_one_le_of_lt_of_isPrime h0I
  have h2 : (2 : ℕ∞) ≤ (origin k 2).height := calc
    (2 : ℕ∞) = 1 + 1 := rfl
    _ ≤ I.height + 1 := add_le_add h1 le_rfl
    _ ≤ (origin k 2).height := Ideal.height_add_one_le_of_lt_of_isPrime hIo
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (origin k 2)]
  apply le_antisymm
  · have h := (origin k 2).height_le_ringKrullDim_of_isPrime
    simpa [PolynomialRing] using h
  · exact WithBot.coe_le_coe.mpr h2

theorem dimension : ringKrullDim (Ring k) = 2 := by
  rw [pullback_dimension _ _ (planeResidue_surjective k) (planeResidue_surjective k),
    max_self, plane_dimension]

theorem first_surjective : Function.Surjective (first k) :=
  RingHom.surjective_pullbackFst_of_surjective _ _ (planeResidue_surjective k)

theorem second_surjective : Function.Surjective (second k) :=
  RingHom.surjective_pullbackSnd_of_surjective _ _ (planeResidue_surjective k)

theorem kernels_mul : firstKernel k * secondKernel k = ⊥ :=
  pullback_kernels_mul _ _

theorem kernels_sup : firstKernel k ⊔ secondKernel k = IsLocalRing.maximalIdeal (Ring k) := by
  rw [pullback_kernels_sup]
  exact IsLocalRing.ker_eq_maximalIdeal _
    ((planeResidue_surjective k).comp (first_surjective k))

theorem nonmaximal_prime (p : Ideal (Ring k)) [p.IsPrime]
    (hp : p ≠ IsLocalRing.maximalIdeal (Ring k)) :
    (firstKernel k ≤ p ∧ ¬ secondKernel k ≤ p) ∨
    (secondKernel k ≤ p ∧ ¬ firstKernel k ≤ p) := by
  have hnot : ¬ (firstKernel k ≤ p ∧ secondKernel k ≤ p) := by
    intro ⟨h₁, h₂⟩
    have h := sup_le h₁ h₂
    rw [kernels_sup] at h
    exact hp ((IsLocalRing.le_maximalIdeal (show p ≠ ⊤ from (inferInstance : p.IsPrime).ne_top)).antisymm h)
  have hor : firstKernel k ≤ p ∨ secondKernel k ≤ p := by
    exact ((inferInstance : p.IsPrime).mul_le.mp (show firstKernel k * secondKernel k ≤ p by
      rw [kernels_mul]; exact bot_le))
  rcases hor with h | h
  · exact Or.inl ⟨h, fun h₂ => hnot ⟨h, h₂⟩⟩
  · exact Or.inr ⟨h, fun h₁ => hnot ⟨h₁, h⟩⟩

/-- The first branch away from the closed point. -/
theorem localization_first (p : Ideal (Ring k)) [p.IsPrime]
    (hp : ¬ secondKernel k ≤ p) :
    ∃ (q : Ideal (LocalPlane k)) (_ : q.IsPrime),
      q = p.map (first k) ∧ q.comap (first k) = p ∧
      Nonempty (Localization.AtPrime p ≃+* Localization.AtPrime q) ∧
      q.height = p.height := by
  have hfst : firstKernel k ≤ p :=
    ((inferInstance : p.IsPrime).mul_le.mp
      (show firstKernel k * secondKernel k ≤ p by rw [kernels_mul]; exact bot_le)).resolve_right hp
  let q := p.map (first k)
  have hq : q.IsPrime := Ideal.map_isPrime_of_surjective (first_surjective k) hfst
  have hqp : q.comap (first k) = p := by
    rw [Ideal.comap_map_of_surjective _ (first_surjective k)]
    exact sup_eq_left.mpr hfst
  have ha : ∃ a : Ring k, a ∉ p ∧ ∀ x ∈ firstKernel k, a * x = 0 := by
    obtain ⟨a, hak, hap⟩ := Set.not_subset.mp hp
    refine ⟨a, hap, fun x hx => ?_⟩
    have h := Ideal.mul_mem_mul hx hak
    rw [kernels_mul] at h
    simpa [mul_comm] using h
  let e := RingEquiv.ofBijective (Localization.localRingHom p q (first k) hqp.symm)
    (localRingHom_bijective_of_annihilator (first k) (first_surjective k) p q hqp.symm ha)
  exact ⟨q, hq, rfl, hqp, ⟨e⟩, height_eq_of_localization_equiv p q e⟩

/-- The second branch away from the closed point. -/
theorem localization_second (p : Ideal (Ring k)) [p.IsPrime]
    (hp : ¬ firstKernel k ≤ p) :
    ∃ (q : Ideal (LocalPlane k)) (_ : q.IsPrime),
      q = p.map (second k) ∧ q.comap (second k) = p ∧
      Nonempty (Localization.AtPrime p ≃+* Localization.AtPrime q) ∧
      q.height = p.height := by
  have hsnd : secondKernel k ≤ p :=
    ((inferInstance : p.IsPrime).mul_le.mp
      (show firstKernel k * secondKernel k ≤ p by rw [kernels_mul]; exact bot_le)).resolve_left hp
  let q := p.map (second k)
  have hq : q.IsPrime := Ideal.map_isPrime_of_surjective (second_surjective k) hsnd
  have hqp : q.comap (second k) = p := by
    rw [Ideal.comap_map_of_surjective _ (second_surjective k)]
    exact sup_eq_left.mpr hsnd
  have ha : ∃ a : Ring k, a ∉ p ∧ ∀ x ∈ secondKernel k, a * x = 0 := by
    obtain ⟨a, hak, hap⟩ := Set.not_subset.mp hp
    refine ⟨a, hap, fun x hx => ?_⟩
    have h := Ideal.mul_mem_mul hak hx
    rw [kernels_mul] at h
    exact h
  let e := RingEquiv.ofBijective (Localization.localRingHom p q (second k) hqp.symm)
    (localRingHom_bijective_of_annihilator (second k) (second_surjective k) p q hqp.symm ha)
  exact ⟨q, hq, rfl, hqp, ⟨e⟩, height_eq_of_localization_equiv p q e⟩

/-- Every point except the closed point is regular. -/
theorem regular_at_nonmaximal (p : Ideal (Ring k)) [p.IsPrime]
    (hp : p ≠ IsLocalRing.maximalIdeal (Ring k)) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  rcases nonmaximal_prime k p hp with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨q, hq, _, _, ⟨e⟩, _⟩ := localization_first k p h
    exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime q) e.symm
  · obtain ⟨q, hq, _, _, ⟨e⟩, _⟩ := localization_second k p h
    exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime q) e.symm

/-- SN-12: the fiber product satisfies Serre's `(R₁)`. -/
theorem regularInCodimensionOne : AdvCommAlg.Normality.RegularInCodimension (Ring k) 1 := by
  intro p hp
  apply regular_at_nonmaximal k p.asIdeal
  intro heq
  have h : (IsLocalRing.maximalIdeal (Ring k)).height ≤ (1 : ℕ∞) := by simpa [heq] using hp
  have hd := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := Ring k)
  rw [dimension] at hd
  have h2 : (IsLocalRing.maximalIdeal (Ring k)).height = (2 : ℕ∞) :=
    WithBot.coe_injective hd
  rw [h2] at h
  norm_num at h

namespace Presentation

abbrev evaluation : PolynomialRing k 2 →+* k := MvPolynomial.eval (fun _ => 0)
abbrev GlobalRing := (evaluation k).pullback (evaluation k)

def coefficient : k →+* GlobalRing k :=
  (MvPolynomial.C.prod MvPolynomial.C).codRestrict _ (by intro a; simp)

def globalVariable (i : Fin 4) : GlobalRing k :=
  if h : i.val < 2 then
    ⟨(MvPolynomial.X ⟨i.val, h⟩, 0), by simp⟩
  else
    ⟨(0, MvPolynomial.X ⟨i.val - 2, by omega⟩), by simp⟩

def polynomialToGlobal : PolynomialRing k 4 →+* GlobalRing k :=
  MvPolynomial.eval₂Hom (coefficient k) (globalVariable k)

@[simp] theorem globalVariable_left (i : Fin 2) :
    globalVariable k (Fin.castAdd 2 i) = ⟨(MvPolynomial.X i, 0), by simp⟩ := by
  simp [globalVariable, Fin.castAdd, i.isLt]

@[simp] theorem globalVariable_right (i : Fin 2) :
    globalVariable k (Fin.natAdd 2 i) = ⟨(0, MvPolynomial.X i), by simp⟩ := by
  simp [globalVariable, Fin.natAdd]
  split_ifs <;> first | omega | rfl

def quotientToGlobal : CoordinateRing k →+* GlobalRing k :=
  Ideal.Quotient.lift (crossIdeal k) (polynomialToGlobal k) (by
    change crossIdeal k ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    rintro p ⟨i, j, rfl⟩
    change polynomialToGlobal k (_ * _) = 0
    simp only [map_mul, polynomialToGlobal, MvPolynomial.eval₂Hom_X',
      globalVariable_left, globalVariable_right]
    apply Subtype.ext
    apply Prod.ext <;> simp)

def scalar : k →+* CoordinateRing k := (Ideal.Quotient.mk (crossIdeal k)).comp MvPolynomial.C

def leftEmbedding : PolynomialRing k 2 →+* CoordinateRing k :=
  (Ideal.Quotient.mk (crossIdeal k)).comp (MvPolynomial.rename (Fin.castAdd 2)).toRingHom

def rightEmbedding : PolynomialRing k 2 →+* CoordinateRing k :=
  (Ideal.Quotient.mk (crossIdeal k)).comp (MvPolynomial.rename (Fin.natAdd 2)).toRingHom

@[simp] theorem leftEmbedding_X (i : Fin 2) :
    leftEmbedding k (MvPolynomial.X i) = Ideal.Quotient.mk (crossIdeal k)
      (MvPolynomial.X (Fin.castAdd 2 i)) := by simp [leftEmbedding]

@[simp] theorem rightEmbedding_X (i : Fin 2) :
    rightEmbedding k (MvPolynomial.X i) = Ideal.Quotient.mk (crossIdeal k)
      (MvPolynomial.X (Fin.natAdd 2 i)) := by simp [rightEmbedding]

@[simp] theorem leftEmbedding_C (a : k) : leftEmbedding k (MvPolynomial.C a) = scalar k a := by
  simp [leftEmbedding, scalar]

@[simp] theorem rightEmbedding_C (a : k) : rightEmbedding k (MvPolynomial.C a) = scalar k a := by
  simp [rightEmbedding, scalar]

theorem cross_variable (i j : Fin 2) :
    leftEmbedding k (MvPolynomial.X i) * rightEmbedding k (MvPolynomial.X j) = 0 := by
  rw [leftEmbedding_X, rightEmbedding_X, ← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨i, j, rfl⟩

/-- The two augmentation ideals have zero product in the displayed quotient. -/
theorem cross_augmentation (p q : PolynomialRing k 2) :
    (leftEmbedding k p - scalar k (evaluation k p)) *
      (rightEmbedding k q - scalar k (evaluation k q)) = 0 := by
  have hx (i : Fin 2) (q : PolynomialRing k 2) :
      leftEmbedding k (MvPolynomial.X i) *
        (rightEmbedding k q - scalar k (evaluation k q)) = 0 := by
    induction q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add]; linear_combination hp + hq
    | mul_X q j _ =>
      simp only [map_mul, MvPolynomial.eval_X, mul_zero, map_zero, sub_zero]
      calc
        _ = rightEmbedding k q *
            (leftEmbedding k (MvPolynomial.X i) * rightEmbedding k (MvPolynomial.X j)) := by ring
        _ = 0 := by rw [cross_variable]; simp
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp only [map_add]; linear_combination hp + hr
  | mul_X p i _ =>
    simp only [map_mul, MvPolynomial.eval_X, mul_zero, map_zero, sub_zero]
    calc
      _ = leftEmbedding k p * (leftEmbedding k (MvPolynomial.X i) *
          (rightEmbedding k q - scalar k (evaluation k q))) := by ring
      _ = 0 := by rw [hx]; simp

/-- Gluing polynomials with the same constant term. -/
def globalToQuotient : GlobalRing k →+* CoordinateRing k where
  toFun a := leftEmbedding k a.val.1 + rightEmbedding k a.val.2 - scalar k (evaluation k a.val.1)
  map_zero' := by simp
  map_one' := by simp
  map_add' a b := by simp only [Subring.coe_add, Prod.fst_add, Prod.snd_add, map_add]; ring
  map_mul' a b := by
    have ha : evaluation k a.val.2 = evaluation k a.val.1 := a.property.symm
    have hb : evaluation k b.val.2 = evaluation k b.val.1 := b.property.symm
    have h1 := cross_augmentation k a.val.1 b.val.2
    have h2 := cross_augmentation k b.val.1 a.val.2
    rw [hb] at h1
    rw [ha] at h2
    simp only [Subring.coe_mul, Prod.fst_mul, Prod.snd_mul, map_mul]
    linear_combination -h1 - h2

@[simp] theorem quotientToGlobal_left (p : PolynomialRing k 2) :
    quotientToGlobal k (leftEmbedding k p) =
      ⟨(p, MvPolynomial.C (evaluation k p)), by simp⟩ := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [leftEmbedding, quotientToGlobal, polynomialToGlobal, coefficient]; rfl
  | add p q hp hq => simp only [map_add, hp, hq]; rfl
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, leftEmbedding_X]
    simp only [quotientToGlobal, Ideal.Quotient.lift_mk, polynomialToGlobal,
      MvPolynomial.eval₂Hom_X', globalVariable_left]
    apply Subtype.ext
    apply Prod.ext <;> simp

@[simp] theorem quotientToGlobal_right (p : PolynomialRing k 2) :
    quotientToGlobal k (rightEmbedding k p) =
      ⟨(MvPolynomial.C (evaluation k p), p), by simp⟩ := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [rightEmbedding, quotientToGlobal, polynomialToGlobal, coefficient]; rfl
  | add p q hp hq => simp only [map_add, hp, hq]; rfl
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, rightEmbedding_X]
    simp only [quotientToGlobal, Ideal.Quotient.lift_mk, polynomialToGlobal,
      MvPolynomial.eval₂Hom_X', globalVariable_right]
    apply Subtype.ext
    apply Prod.ext <;> simp

@[simp] theorem quotientToGlobal_scalar (a : k) :
    quotientToGlobal k (scalar k a) = coefficient k a := by
  simp [scalar, quotientToGlobal, polynomialToGlobal]

@[simp] theorem globalToQuotient_coefficient (a : k) :
    globalToQuotient k (coefficient k a) = scalar k a := by
  change leftEmbedding k (MvPolynomial.C a) + rightEmbedding k (MvPolynomial.C a) -
    scalar k (evaluation k (MvPolynomial.C a)) = _
  simp

@[simp] theorem globalToQuotient_variable (i : Fin 4) :
    globalToQuotient k (globalVariable k i) =
      Ideal.Quotient.mk (crossIdeal k) (MvPolynomial.X i) := by
  unfold globalVariable
  split_ifs with h
  · change leftEmbedding k (MvPolynomial.X ⟨i.val, h⟩) + rightEmbedding k 0 -
      scalar k (evaluation k (MvPolynomial.X ⟨i.val, h⟩)) = _
    simp only [map_zero, MvPolynomial.eval_X, sub_zero, add_zero, leftEmbedding_X]
    rfl
  · change leftEmbedding k 0 + rightEmbedding k (MvPolynomial.X ⟨i.val - 2, by omega⟩) -
      scalar k (evaluation k 0) = _
    simp only [map_zero, sub_zero, zero_add, rightEmbedding_X]
    congr 2
    apply Fin.ext
    simp
    omega

theorem quotientToGlobal_left_inverse :
    Function.LeftInverse (globalToQuotient k) (quotientToGlobal k) := by
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h : (globalToQuotient k).comp (polynomialToGlobal k) = Ideal.Quotient.mk (crossIdeal k) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [polynomialToGlobal, scalar]
    · intro i
      simp [polynomialToGlobal]
  exact congrArg (fun f : PolynomialRing k 4 →+* CoordinateRing k => f p) h

theorem quotientToGlobal_right_inverse :
    Function.RightInverse (globalToQuotient k) (quotientToGlobal k) := by
  intro a
  change quotientToGlobal k (leftEmbedding k a.val.1 + rightEmbedding k a.val.2 -
    scalar k (evaluation k a.val.1)) = a
  rw [map_sub, map_add, quotientToGlobal_left, quotientToGlobal_right, quotientToGlobal_scalar]
  apply Subtype.ext
  apply Prod.ext
  · change a.val.1 + MvPolynomial.C (evaluation k a.val.2) -
      MvPolynomial.C (evaluation k a.val.1) = _
    rw [show evaluation k a.val.2 = evaluation k a.val.1 from a.property.symm]
    exact add_sub_cancel_right _ _
  · change MvPolynomial.C (evaluation k a.val.1) + a.val.2 -
      MvPolynomial.C (evaluation k a.val.1) = _
    exact add_sub_cancel_left _ _

/-- The unlocalized coordinate ring is the polynomial fiber product. -/
def quotientEquivGlobal : CoordinateRing k ≃+* GlobalRing k :=
  { quotientToGlobal k with
    invFun := globalToQuotient k
    left_inv := quotientToGlobal_left_inverse k
    right_inv := quotientToGlobal_right_inverse k }

/-- The polynomial fiber product maps coordinatewise into the local one. -/
def globalToLocal : GlobalRing k →+* Ring k where
  toFun a := ⟨(algebraMap (PolynomialRing k 2) (LocalPlane k) a.val.1,
    algebraMap (PolynomialRing k 2) (LocalPlane k) a.val.2), by
      change planeResidue k (algebraMap (PolynomialRing k 2) (LocalPlane k) a.val.1) =
        planeResidue k (algebraMap (PolynomialRing k 2) (LocalPlane k) a.val.2)
      have ha : evaluation k a.val.1 = evaluation k a.val.2 := a.property
      simpa only [planeResidue, IsLocalization.lift_eq] using ha⟩
  map_zero' := by apply Subtype.ext; apply Prod.ext <;> exact map_zero _
  map_one' := by apply Subtype.ext; apply Prod.ext <;> exact map_one _
  map_add' a b := by apply Subtype.ext; apply Prod.ext <;> exact map_add _ _ _
  map_mul' a b := by apply Subtype.ext; apply Prod.ext <;> exact map_mul _ _ _

theorem globalToLocal_injective : Function.Injective (globalToLocal k) := by
  intro a b hab
  have hi : Function.Injective (algebraMap (PolynomialRing k 2) (LocalPlane k)) :=
    IsLocalization.injective (LocalPlane k) (origin k 2).primeCompl_le_nonZeroDivisors
  apply Subtype.ext
  apply Prod.ext
  · apply hi
    exact congrArg (fun c : Ring k => c.val.1) hab
  · apply hi
    exact congrArg (fun c : Ring k => c.val.2) hab

def quotientToLocal : CoordinateRing k →+* Ring k :=
  (globalToLocal k).comp (quotientToGlobal k)

instance quotientAlgebra : Algebra (CoordinateRing k) (Ring k) := (quotientToLocal k).toAlgebra

theorem quotient_residue (a : CoordinateRing k) :
    evaluation k (quotientToGlobal k a).val.1 = coordinateResidue k a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h : ((evaluation k).comp ((evaluation k).pullbackFst (evaluation k))).comp
      (polynomialToGlobal k) = MvPolynomial.eval (fun _ => (0 : k)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [polynomialToGlobal, coefficient]
      change MvPolynomial.constantCoeff (MvPolynomial.C a) = a
      simp
    · intro i
      simp [polynomialToGlobal, globalVariable]
      split_ifs <;> simp
  exact congrArg (fun f : PolynomialRing k 4 →+* k => f p) h

@[simp] theorem quotientToLocal_residue (a : CoordinateRing k) :
    planeResidue k (first k (quotientToLocal k a)) = coordinateResidue k a := by
  change planeResidue k (algebraMap (PolynomialRing k 2) (LocalPlane k)
    (quotientToGlobal k a).val.1) = _
  simp only [planeResidue, IsLocalization.lift_eq]
  exact quotient_residue k a

@[simp] theorem quotientToLocal_global (a : GlobalRing k) :
    quotientToLocal k (globalToQuotient k a) = globalToLocal k a := by
  change globalToLocal k (quotientToGlobal k (globalToQuotient k a)) = _
  rw [quotientToGlobal_right_inverse k a]

/-- Clearing the two denominators simultaneously: multiply their polynomial
coordinates by the other denominator's nonzero constant term. -/
instance ring_isLocalization : IsLocalization (coordinateOrigin k).primeCompl (Ring k) where
  map_units s := by
    apply isUnit_of_map_unit ((planeResidue k).comp (first k))
    change IsUnit (planeResidue k (first k (quotientToLocal k s.val)))
    rw [quotientToLocal_residue]
    exact isUnit_iff_ne_zero.mpr s.property
  surj z := by
    obtain ⟨⟨p, s⟩, hb⟩ := IsLocalization.surj (origin k 2).primeCompl z.val.1
    obtain ⟨⟨q, t⟩, hc⟩ := IsLocalization.surj (origin k 2).primeCompl z.val.2
    have hbr : planeResidue k z.val.1 * evaluation k s.val = evaluation k p := by
      simpa only [map_mul, planeResidue, IsLocalization.lift_eq] using congrArg (planeResidue k) hb
    have hcr : planeResidue k z.val.2 * evaluation k t.val = evaluation k q := by
      simpa only [map_mul, planeResidue, IsLocalization.lift_eq] using congrArg (planeResidue k) hc
    have hcompat : evaluation k p * evaluation k t.val = evaluation k q * evaluation k s.val := by
      rw [← hbr, ← hcr]
      have hz : planeResidue k z.val.1 = planeResidue k z.val.2 := z.property
      rw [hz]
      ring
    let d : GlobalRing k := ⟨(s.val * MvPolynomial.C (evaluation k t.val),
      t.val * MvPolynomial.C (evaluation k s.val)), by
      change evaluation k (_ * _) = evaluation k (_ * _)
      simp only [map_mul, MvPolynomial.eval_C]
      ring⟩
    let n : GlobalRing k := ⟨(p * MvPolynomial.C (evaluation k t.val),
      q * MvPolynomial.C (evaluation k s.val)), by
      change evaluation k (_ * _) = evaluation k (_ * _)
      simpa only [map_mul, MvPolynomial.eval_C] using hcompat⟩
    have hd : globalToQuotient k d ∈ (coordinateOrigin k).primeCompl := by
      change coordinateResidue k (globalToQuotient k d) ≠ 0
      rw [← quotient_residue, quotientToGlobal_right_inverse k d]
      change evaluation k (s.val * MvPolynomial.C (evaluation k t.val)) ≠ 0
      simp only [map_mul, MvPolynomial.eval_C]
      exact mul_ne_zero s.property t.property
    refine ⟨⟨globalToQuotient k n, globalToQuotient k d, hd⟩, ?_⟩
    change z * quotientToLocal k (globalToQuotient k d) = quotientToLocal k (globalToQuotient k n)
    rw [quotientToLocal_global, quotientToLocal_global]
    apply Subtype.ext
    apply Prod.ext
    · change z.val.1 * algebraMap (PolynomialRing k 2) (LocalPlane k)
        (s.val * MvPolynomial.C (evaluation k t.val)) =
        algebraMap (PolynomialRing k 2) (LocalPlane k) (p * MvPolynomial.C (evaluation k t.val))
      rw [map_mul, map_mul, ← mul_assoc, hb]
    · change z.val.2 * algebraMap (PolynomialRing k 2) (LocalPlane k)
        (t.val * MvPolynomial.C (evaluation k s.val)) =
        algebraMap (PolynomialRing k 2) (LocalPlane k) (q * MvPolynomial.C (evaluation k s.val))
      rw [map_mul, map_mul, ← mul_assoc, hc]
  exists_of_eq {a b} h := by
    have hi : Function.Injective (quotientToLocal k) :=
      (globalToLocal_injective k).comp (quotientEquivGlobal k).injective
    have hab : a = b := hi h
    exact ⟨1, by simp [hab]⟩

/-- The specified canonical localization isomorphism. -/
def presentationEquiv : PresentedRing k ≃+* Ring k :=
  (IsLocalization.algEquiv (coordinateOrigin k).primeCompl (PresentedRing k) (Ring k)).toRingEquiv

@[simp] theorem presentationEquiv_algebraMap (a : CoordinateRing k) :
    presentationEquiv k (algebraMap (CoordinateRing k) (PresentedRing k) a) = quotientToLocal k a :=
  (IsLocalization.algEquiv (coordinateOrigin k).primeCompl (PresentedRing k) (Ring k)).commutes a

@[simp] theorem presentationEquiv_variable (i : Fin 4) :
    presentationEquiv k (presentedVariable k i) = pairVariable k i := by
  rw [presentedVariable, presentationEquiv_algebraMap]
  change globalToLocal k (polynomialToGlobal k (MvPolynomial.X i)) = _
  rw [polynomialToGlobal, MvPolynomial.eval₂Hom_X']
  unfold globalVariable pairVariable
  split_ifs <;> apply Subtype.ext <;> apply Prod.ext <;> simp [globalToLocal, planeVariable]

@[simp] theorem presentationEquiv_coefficient (a : k) :
    presentationEquiv k (algebraMap (CoordinateRing k) (PresentedRing k)
      (Ideal.Quotient.mk (crossIdeal k) (MvPolynomial.C a))) =
      ⟨(algebraMap (PolynomialRing k 2) (LocalPlane k) (MvPolynomial.C a),
        algebraMap (PolynomialRing k 2) (LocalPlane k) (MvPolynomial.C a)), by
          simp [planeResidue]⟩ := by
  rw [presentationEquiv_algebraMap]
  change globalToLocal k (polynomialToGlobal k (MvPolynomial.C a)) = _
  rw [polynomialToGlobal, MvPolynomial.eval₂Hom_C]
  rfl

end Presentation

/-- The canonical presentation at the origin, with all four coordinates and
all coefficients identified. -/
theorem presentation : Specs.presentationType.{u} := by
  intro k _
  exact ⟨Presentation.presentationEquiv k, Presentation.presentationEquiv_variable k,
    Presentation.presentationEquiv_coefficient k⟩

end AdvCommAlg.Normality.FiberProduct
