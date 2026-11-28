import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.AdjointLocalNilpotence
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.TriangularRootSpaces
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Abel

/-! Local nilpotence of the untwisted affine simple generators. -/

noncomputable section

universe u v

namespace RepTheorySurvey.Affine

open LieAlgebrasAndRepresentations
open Specs.RepTheorySurvey.Affine.LoopAlgebra
open Specs.RepTheorySurvey.Affine.AdjointLocalNilpotence
open UniversalEnvelopingAlgebra (ι)
open private cartanMaximalToral from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.LoopAlgebra
open private affine_induction homogeneous_zero from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.TriangularRootSpaces

private theorem iterate_eq_zero_add {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (D : Module.End R V) {x y : V}
    (hx : ∃ k : ℕ, (D : V → V)^[k] x = 0) (hy : ∃ l : ℕ, (D : V → V)^[l] y = 0) :
    ∃ n : ℕ, (D : V → V)^[n] (x + y) = 0 := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := hy
  refine ⟨k + l, ?_⟩
  have hx' : (D : V → V)^[k + l] x = 0 := by
    rw [Nat.add_comm, Function.iterate_add_apply, hk]
    exact Function.iterate_fixed D.map_zero l
  have hy' : (D : V → V)^[k + l] y = 0 := by
    rw [Function.iterate_add_apply, hl]
    exact Function.iterate_fixed D.map_zero k
  rw [← Module.End.pow_apply, map_add, Module.End.pow_apply, Module.End.pow_apply,
    hx', hy', add_zero]

section Affine

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
variable [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]

/-- The adjoint iterates of a finite root vector shift the input weight by successive
multiples of that root. Only finitely many of the shifted weights can occur. -/
private theorem finiteRoot_ad_iterate_eq_zero {α : Module.Dual ℂ H} (hα : α ≠ 0)
    {x : G} (hx : x ∈ rootSpace H α) (y : G) :
    ∃ n : ℕ, (LieAlgebra.ad ℂ G x : G → G)^[n] y = 0 := by
  let D := LieAlgebra.ad ℂ G x
  let hT := (cartanMaximalToral H).1
  have hy : y ∈ ⨆ β, rootSpace H β := by
    rw [iSup_rootSpace_eq_top H hT]
    trivial
  refine Submodule.iSup_induction (rootSpace H)
    (motive := fun y => ∃ n : ℕ, (D : G → G)^[n] y = 0)
    hy (fun β z hz => ?_) ⟨0, rfl⟩ (fun _ _ => iterate_eq_zero_add D)
  have hshift (n : ℕ) : (D : G → G)^[n] z ∈ rootSpace H (n • α + β) := by
    induction n with
    | zero => simpa using hz
    | succ n ih =>
      rw [Function.iterate_succ_apply', succ_nsmul', add_assoc]
      exact rootSpace_bracket H _ _ _ _ hx ih
  have hinj : Function.Injective (fun n : ℕ => n • α + β) := by
    intro m n he
    have he' : (m : ℂ) • α = (n : ℂ) • α := by
      simpa only [Nat.cast_smul_eq_nsmul] using add_right_cancel he
    exact Nat.cast_injective (smul_left_injective ℂ hα he')
  by_contra! h
  have hfin := (rootSet_finite H hT).insert (0 : Module.Dual ℂ H)
  apply (Set.infinite_range_of_injective hinj) (hfin.subset ?_)
  rintro _ ⟨n, rfl⟩
  rw [Set.mem_insert_iff]
  by_cases hn : n • α + β = 0
  · exact Or.inl hn
  · right
    refine ⟨hn, ?_⟩
    intro hb
    change rootSpace H (n • α + β) = ⊥ at hb
    have hm := hshift n
    rw [hb, Submodule.mem_bot] at hm
    exact h n hm

private theorem homogeneous_ad_iterate_eq_zero (B : InvariantForm G) (p : ℤ)
    {α : Module.Dual ℂ H} (hα : α ≠ 0) {x : G} (hx : x ∈ rootSpace H α)
    (y : AffineAlgebra B) :
    ∃ n : ℕ, (LieAlgebra.ad ℂ (AffineAlgebra B) (homogeneous B p x) :
      AffineAlgebra B → AffineAlgebra B)^[n] y = 0 := by
  classical
  let a := homogeneous B p x
  let D := LieAlgebra.ad ℂ (AffineAlgebra B) a
  let E := LieAlgebra.ad ℂ G x
  have hK : ⁅a, K B⁆ = 0 := by rw [← lie_skew a, centralGenerator, neg_zero]
  change ∃ n : ℕ, (D : AffineAlgebra B → AffineAlgebra B)^[n] y = 0
  refine affine_induction B (p := fun z => ∃ n : ℕ,
    (D : AffineAlgebra B → AffineAlgebra B)^[n] z = 0) y
    ⟨0, rfl⟩ (fun _ _ => iterate_eq_zero_add D)
    (fun m z => ?_) (fun c => ?_) (fun c => ?_)
  · have hloop (n : ℕ) : ∃ c : ℂ,
        (D : AffineAlgebra B → AffineAlgebra B)^[n] (homogeneous B m z) =
          homogeneous B ((n : ℤ) * p + m) ((E : G → G)^[n] z) + c • K B := by
      induction n with
      | zero => exact ⟨0, by simp⟩
      | succ n ih =>
        obtain ⟨c, hc⟩ := ih
        let q : ℤ := (n : ℤ) * p + m
        let w : G := (E : G → G)^[n] z
        refine ⟨if p = -q then (p : ℂ) * B.form x w else 0, ?_⟩
        rw [Function.iterate_succ_apply', hc, Function.iterate_succ_apply']
        change ⁅a, homogeneous B q w + c • K B⁆ =
          homogeneous B ((n.succ : ℤ) * p + m) ⁅x, w⁆ + _ • K B
        rw [lie_add, lie_smul, hK, smul_zero, add_zero]
        change ⁅homogeneous B p x, homogeneous B q w⁆ = _
        rw [homogeneousBracket]
        have hq : p + q = (n.succ : ℤ) * p + m := by
          simp only [q, Nat.cast_succ, add_mul, one_mul]
          abel
        rw [hq]
    obtain ⟨n, hn⟩ := finiteRoot_ad_iterate_eq_zero H hα hx z
    obtain ⟨c, hc⟩ := hloop n
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply', hc, show (E : G → G)^[n] z = 0 from hn,
      homogeneous_zero, zero_add]
    change ⁅a, c • K B⁆ = 0
    rw [lie_smul, hK, smul_zero]
  · refine ⟨1, ?_⟩
    change ⁅a, c • K B⁆ = 0
    rw [lie_smul, hK, smul_zero]
  · have hd : ⁅a, d B⁆ = -(p : ℂ) • a := by
      rw [← lie_skew a, show ⁅d B, a⁆ = (p : ℂ) • a from degreeBracket B p x, neg_smul]
    refine ⟨2, ?_⟩
    have hD (w : AffineAlgebra B) : D w = ⁅a, w⁆ := rfl
    rw [show (2 : ℕ) = 1 + 1 by rfl, Function.iterate_add_apply,
      Function.iterate_one, hD, hD]
    simp only [lie_smul, hd, lie_self, smul_zero]

theorem affineSimpleAdjointLocallyNilpotent : affineSimpleAdjointLocallyNilpotent_type.{u} := by
  intro G _ _ _ _ B H _ φ _ _ θ hθ T S i a ha y
  have hθ' : θ ≠ 0 := hθ.1.1.1
  have aux (p : ℤ) {α : Module.Dual ℂ H} (hα : α ≠ 0) {x : G} (hx : x ∈ rootSpace H α) :
      ∃ n : ℕ, (affineBracket_value B (homogeneous B p x))^[n] y = 0 :=
    homogeneous_ad_iterate_eq_zero H B p hα hx y
  rcases ha with rfl | rfl
  · cases i with
    | none => exact aux 1 (neg_ne_zero.mpr hθ') T.f_mem
    | some i =>
      have hi : i.val ≠ 0 := i.property.1.1.1
      exact aux 0 hi (S i).e_mem
  · cases i with
    | none => exact aux (-1) hθ' T.e_mem
    | some i =>
      have hi : i.val ≠ 0 := i.property.1.1.1
      exact aux 0 (neg_ne_zero.mpr hi) (S i).f_mem

end Affine

/-- If an operator differentiates a two-variable map, the sum of two annihilating
exponents kills the image. This applies to multiplication and to the module action. -/
private theorem pow_apply₂_eq_zero {X Y Z : Type*}
    [AddMonoid X] [AddMonoid Y] [AddMonoid Z]
    (P : AddMonoid.End X) (Q : AddMonoid.End Y) (D : AddMonoid.End Z)
    (F : X → Y → Z) (hleft : ∀ y, F 0 y = 0) (hright : ∀ x, F x 0 = 0)
    (step : ∀ x y, D (F x y) = F (P x) y + F x (Q y)) :
    ∀ k l (x : X) (y : Y), (P ^ k) x = 0 → (Q ^ l) y = 0 → (D ^ (k + l)) (F x y) = 0 := by
  intro k
  induction k with
  | zero =>
    intro l x y hx _
    have hx' : x = 0 := hx
    rw [hx', hleft, map_zero]
  | succ k ihk =>
    intro l
    induction l with
    | zero =>
      intro x y _ hy
      have hy' : y = 0 := hy
      rw [hy', hright, map_zero]
    | succ l ihl =>
      intro x y hx hy
      have hx' : (P ^ k) (P x) = 0 := by
        simpa only [pow_succ, AddMonoid.End.coe_mul, Function.comp_apply] using hx
      have hy' : (Q ^ l) (Q y) = 0 := by
        simpa only [pow_succ, AddMonoid.End.coe_mul, Function.comp_apply] using hy
      rw [Nat.add_succ, pow_succ]
      change (D ^ (k.succ + l)) (D (F x y)) = 0
      rw [step, map_add]
      have h₁ : (D ^ (k.succ + l)) (F (P x) y) = 0 := by
        simpa only [Nat.succ_add, Nat.add_succ] using ihk l.succ (P x) y hx' hy
      rw [h₁, ihl x (Q y) hx hy', add_zero]

section Enveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

private theorem enveloping_ad_iterate_eq_zero (a : L)
    (ha : ∀ x : L, ∃ n : ℕ, (fun y : L => ⁅a, y⁆)^[n] x = 0) :
    let A := UniversalEnvelopingAlgebra ℂ L
    let z : A := ι ℂ a
    let D : A →ₗ[ℂ] A := LinearMap.mulLeft ℂ z - LinearMap.mulRight ℂ z
    (∀ p q : A, D (p * q) = D p * q + p * D q) ∧
      ∀ p : A, ∃ n : ℕ, (D : A → A)^[n] p = 0 := by
  let A := UniversalEnvelopingAlgebra ℂ L
  let z : A := ι ℂ a
  let D : Module.End ℂ A := LinearMap.mulLeft ℂ z - LinearMap.mulRight ℂ z
  have hmul (p q : A) : D (p * q) = D p * q + p * D q := by
    change z * (p * q) - (p * q) * z = (z * p - p * z) * q + p * (z * q - q * z)
    simp only [sub_mul, mul_sub, mul_assoc]
    abel
  change (∀ p q, D (p * q) = D p * q + p * D q) ∧
    ∀ p, ∃ n : ℕ, (D : A → A)^[n] p = 0
  refine ⟨hmul, fun p => ?_⟩
  have hι (x : L) : D (ι ℂ x) = ι ℂ ⁅a, x⁆ := ((ι ℂ).map_lie a x).symm
  have hiter (n : ℕ) (x : L) :
      (D : A → A)^[n] (ι ℂ x) = ι ℂ ((fun y : L => ⁅a, y⁆)^[n] x) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hι]
  let π := UniversalEnvelopingAlgebra.mkAlgHom ℂ L
  obtain ⟨t, rfl⟩ : ∃ t, π t = p :=
    RingCon.mkₐ_surjective (UniversalEnvelopingAlgebra.ringCon ℂ L) p
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
    refine ⟨1, ?_⟩
    rw [AlgHom.commutes, Function.iterate_one]
    change z * algebraMap ℂ A c - algebraMap ℂ A c * z = 0
    rw [← Algebra.commutes, sub_self]
  | ι x =>
    change ∃ n : ℕ, (D : A → A)^[n] (ι ℂ x) = 0
    obtain ⟨n, hn⟩ := ha x
    exact ⟨n, by rw [hiter, hn, map_zero]⟩
  | mul p q hp hq =>
    rw [map_mul]
    obtain ⟨k, hk⟩ := hp
    obtain ⟨l, hl⟩ := hq
    let E : AddMonoid.End A := D.toAddMonoidHom
    refine ⟨k + l, ?_⟩
    have hE : (E : A → A) = (D : A → A) := rfl
    have hm := pow_apply₂_eq_zero E E E (· * ·) zero_mul mul_zero hmul k l (π p) (π q)
    simpa only [AddMonoid.End.coe_pow, hE] using hm
      (by simpa only [AddMonoid.End.coe_pow, hE] using hk)
      (by simpa only [AddMonoid.End.coe_pow, hE] using hl)
  | add p q hp hq =>
    rw [map_add]
    exact iterate_eq_zero_add D hp hq

end Enveloping

theorem affineSimpleEnvelopingAdjointLocallyNilpotent :
    affineSimpleEnvelopingAdjointLocallyNilpotent_type.{u} := by
  intro G _ _ _ _ B H _ φ hB hφ θ hθ T S i a ha ring algebra hcompat
  apply enveloping_ad_iterate_eq_zero
  have hbracket : (fun y : AffineAlgebra B => ⁅a, y⁆) = affineBracket_value B a :=
    funext (hcompat.2.2 a)
  intro x
  rw [hbracket]
  obtain ⟨n, hn⟩ := affineSimpleAdjointLocallyNilpotent B H φ hB hφ θ hθ T S i a ha x
  have hzero := congrArg (fun g : AddCommGroup (AffineAlgebra B) => g.toZero.zero) hcompat.1
  exact ⟨n, hn.trans hzero.symm⟩

private theorem pow_smul_eq_zero {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]
    (z p : A) (m : M) (n k : ℕ) (hn : (fun q : A => z * q - q * z)^[n] p = 0)
    (hk : z ^ k • m = 0) : z ^ (n + k) • (p • m) = 0 := by
  let D : AddMonoid.End A :=
    (LinearMap.mulLeft ℤ z - LinearMap.mulRight ℤ z : A →ₗ[ℤ] A).toAddMonoidHom
  let Q : AddMonoid.End M := Module.toAddMonoidEnd A M z
  have hpow (l : ℕ) (w : M) : (Q ^ l) w = z ^ l • w := by
    change ((Module.toAddMonoidEnd A M z) ^ l) w = _
    rw [← map_pow]
    rfl
  have step (q : A) (w : M) : Q (q • w) = D q • w + q • Q w := by
    change z • (q • w) = (z * q - q * z) • w + q • (z • w)
    rw [sub_smul, mul_smul, mul_smul]
    abel
  rw [← hpow]
  have hD : (D : A → A) = (fun q : A => z * q - q * z) := rfl
  exact pow_apply₂_eq_zero D Q Q (· • ·) (zero_smul A) (fun q => smul_zero q)
    step n k p m (by simpa only [AddMonoid.End.coe_pow, hD] using hn) ((hpow k m).trans hk)

theorem affineSimpleLocallyNilpotentOnCyclic :
    affineSimpleLocallyNilpotentOnCyclic_type.{u,v} := by
  intro G _ _ _ _ B H _ φ hB hφ θ hθ T S i a ha ring algebra hcompat
  dsimp only
  intro M _ _ m hm w hw
  obtain ⟨p, rfl⟩ := Submodule.mem_span_singleton.mp hw
  obtain ⟨k, hk⟩ := hm
  obtain ⟨n, hn⟩ := (affineSimpleEnvelopingAdjointLocallyNilpotent
    B H φ hB hφ θ hθ T S i a ha hcompat).2 p
  exact ⟨n + k, pow_smul_eq_zero (ι ℂ a) p m n k hn hk⟩

end RepTheorySurvey.Affine
