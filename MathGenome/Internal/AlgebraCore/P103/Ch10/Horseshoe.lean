import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Horseshoe
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel

noncomputable section
namespace P103.Ch10.Horseshoe
open CategoryTheory
open P103.Specs.Ch10.Horseshoe
universe u v w

section LinearAlgebra
variable {R : Type u} [Ring R]
variable {U V W X : Type*} {E : Type v} [AddCommGroup U] [AddCommGroup V]
  [AddCommGroup W] [AddCommGroup X] [AddCommGroup E]
  [Module R U] [Module R V] [Module R W] [Module R X] [Module R E]

/-- Projectivity lifts a map into a kernel along any exact preceding map. -/
theorem lift_exact [Module.Projective R X] (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (h : Function.Exact f g) (r : X →ₗ[R] V) (hr : g.comp r = 0) :
    ∃ t : X →ₗ[R] U, f.comp t = r := by
  let q := f.codRestrict (LinearMap.ker g) (h.apply_apply_eq_zero)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := (h y.val).mp y.property
    exact ⟨x, Subtype.ext hx⟩
  let r' := r.codRestrict (LinearMap.ker g) (fun x => LinearMap.congr_fun hr x)
  obtain ⟨t, ht⟩ := Module.projective_lifting_property q r' hq
  exact ⟨t, LinearMap.ext fun x => congrArg Subtype.val (LinearMap.congr_fun ht x)⟩

/-- A linear map killing a kernel descends through a surjection. -/
theorem descend_surjective (p : V →ₗ[R] W) (hp : Function.Surjective p)
    (r : V →ₗ[R] E) (hr : LinearMap.ker p ≤ LinearMap.ker r) :
    ∃ t : W →ₗ[R] E, t.comp p = r := by
  let t := ((LinearMap.ker p).liftQ r hr).comp
    (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  refine ⟨t, ?_⟩
  ext x
  change (LinearMap.ker p).liftQ r hr
    ((p.quotKerEquivOfSurjective hp).symm (p x)) = r x
  rw [show (p.quotKerEquivOfSurjective hp).symm (p x) =
    (LinearMap.ker p).mkQ x from
      (p.quotKerEquivOfSurjective hp).symm_apply_eq.mpr
        (p.quotKerEquivOfSurjective_apply_mk hp x).symm]
  rfl

/-- Injectivity extends a map through an exact following map. -/
theorem extend_exact [Module.Injective R E] [Small.{v} R]
    (f : U →ₗ[R] V) (g : V →ₗ[R] W) (h : Function.Exact f g)
    (r : V →ₗ[R] E) (hr : r.comp f = 0) :
    ∃ t : W →ₗ[R] E, t.comp g = r := by
  have hk : LinearMap.ker g ≤ LinearMap.ker r := by
    intro y hy
    obtain ⟨x, rfl⟩ := (h y).mp hy
    exact LinearMap.congr_fun hr x
  obtain ⟨s, hs⟩ := descend_surjective g.rangeRestrict g.surjective_rangeRestrict r (by
    intro x hx
    exact hk (congrArg Subtype.val hx))
  obtain ⟨t, ht⟩ := Module.Injective.extension_property R E _ _
    (LinearMap.range g).subtype Subtype.val_injective s
  refine ⟨t, ?_⟩
  ext x
  exact (LinearMap.congr_fun ht (g.rangeRestrict x)).trans (LinearMap.congr_fun hs x)

end LinearAlgebra


section Blocks
variable {R : Type u} [Ring R]
variable {U₁ U₂ V₁ V₂ W₁ W₂ : Type*}
  [AddCommGroup U₁] [AddCommGroup U₂] [AddCommGroup V₁] [AddCommGroup V₂]
  [AddCommGroup W₁] [AddCommGroup W₂]
  [Module R U₁] [Module R U₂] [Module R V₁] [Module R V₂]
  [Module R W₁] [Module R W₂]

def upper (f : U₁ →ₗ[R] V₁) (g : U₂ →ₗ[R] V₂) (t : U₂ →ₗ[R] V₁) :
    U₁ × U₂ →ₗ[R] V₁ × V₂ :=
  ((f.comp (LinearMap.fst R U₁ U₂)) +
    t.comp (LinearMap.snd R U₁ U₂)).prod (g.comp (LinearMap.snd R U₁ U₂))

@[simp] theorem upper_apply (f : U₁ →ₗ[R] V₁) (g : U₂ →ₗ[R] V₂)
    (t : U₂ →ₗ[R] V₁) (x : U₁ × U₂) :
    upper f g t x = (f x.1 + t x.2, g x.2) := rfl

theorem exact_upper (f : U₁ →ₗ[R] V₁) (g : U₂ →ₗ[R] V₂)
    (t : U₂ →ₗ[R] V₁) (a : V₁ →ₗ[R] W₁) (b : V₂ →ₗ[R] W₂)
    (s : V₂ →ₗ[R] W₁) (hf : Function.Exact f a) (hg : Function.Exact g b)
    (ht : a.comp t + s.comp g = 0) :
    Function.Exact (upper f g t) (upper a b s) := by
  intro z
  constructor
  · intro hz
    have hz₁ : a z.1 + s z.2 = 0 := congrArg Prod.fst hz
    have hz₂ : b z.2 = 0 := congrArg Prod.snd hz
    obtain ⟨y, hy⟩ := (hg z.2).mp hz₂
    have hc : a (z.1 - t y) = 0 := by
      have ht' := LinearMap.congr_fun ht y
      change a (t y) + s (g y) = 0 at ht'
      rw [map_sub]
      rw [hy] at ht'
      exact sub_eq_zero.mpr (add_right_cancel (hz₁.trans ht'.symm))
    obtain ⟨x, hx⟩ := (hf _).mp hc
    refine ⟨(x, y), ?_⟩
    apply Prod.ext
    · change f x + t y = z.1
      rw [hx]
      abel
    · exact hy
  · rintro ⟨x, rfl⟩
    apply Prod.ext
    · change a (f x.1 + t x.2) + s (g x.2) = 0
      rw [map_add, hf.apply_apply_eq_zero, zero_add]
      exact LinearMap.congr_fun ht x.2
    · exact hg.apply_apply_eq_zero x.2

end Blocks

namespace Projective
open P103.Specs.Ch10.ProjectiveResolutions
variable {R : Type u} [Ring R]
variable {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]
variable (L : Resolution R A) (N : Resolution R C)

abbrev δ (Q : Resolution R A) (n : ℕ) := (Q.complex.d (n + 1) n).hom

/-- Cycles include the augmentation equation in degree zero. -/
def Cycle {X : Type*} [AddCommGroup X] [Module R X]
    (n : ℕ) (r : X →ₗ[R] L.complex.X n) : Prop :=
  match n with
  | 0 => L.ε.comp r = 0
  | n + 1 => (δ L n).comp r = 0

theorem δ_square (Q : Resolution R A) (n : ℕ) :
    (δ Q n).comp (δ Q (n + 1)) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (Q.complex.d_comp_d (n + 2) (n + 1) n)
  exact h

theorem δ_augmentation (Q : Resolution R A) : Q.ε.comp (δ Q 0) = 0 := by
  exact (LinearMap.exact_iff.mpr Q.exact_zero.symm).linearMap_comp_eq_zero

theorem lift_cycle {X : Type*} [AddCommGroup X] [Module R X]
    [Module.Projective R X] (n : ℕ) (r : X →ₗ[R] L.complex.X n)
    (hr : Cycle L n r) : ∃ t : X →ₗ[R] L.complex.X (n + 1), (δ L n).comp t = r := by
  cases n with
  | zero => exact lift_exact _ _ (LinearMap.exact_iff.mpr L.exact_zero.symm) r hr
  | succ n => exact lift_exact _ _ (LinearMap.exact_iff.mpr (L.exact_succ n).symm) r hr

/-- The invariant needed to continue choosing the upper-right blocks. -/
structure Correction (n : ℕ) where
  t : N.complex.X (n + 1) →ₗ[R] L.complex.X n
  cycle : Cycle L n (t.comp (δ N (n + 1)))

variable {L N}

def next (hN : N.IsProjective) (n : ℕ) (c : Correction L N n) :
    Correction L N (n + 1) := by
  letI := hN (n + 2)
  have h : Cycle L n (-(c.t.comp (δ N (n + 1)))) := by
    cases n <;> simpa [Cycle] using congrArg Neg.neg c.cycle
  let t := Classical.choose (lift_cycle L n (-(c.t.comp (δ N (n + 1)))) h)
  have ht : (δ L n).comp t = -(c.t.comp (δ N (n + 1))) :=
    Classical.choose_spec (lift_cycle L n (-(c.t.comp (δ N (n + 1)))) h)
  refine ⟨t, ?_⟩
  change (δ L n).comp (t.comp (δ N (n + 2))) = 0
  rw [← LinearMap.comp_assoc, ht]
  ext x
  change -(c.t ((δ N (n + 1)) ((δ N (n + 2)) x))) = 0
  have hs := LinearMap.congr_fun (δ_square N (n + 1)) x
  change (δ N (n + 1)) ((δ N (n + 2)) x) = 0 at hs
  rw [hs, map_zero, neg_zero]

theorem next_equation (hN : N.IsProjective) (n : ℕ) (c : Correction L N n) :
    (δ L n).comp (next hN n c).t + c.t.comp (δ N (n + 1)) = 0 := by
  letI := hN (n + 2)
  dsimp [next]
  apply add_eq_zero_iff_eq_neg.mpr
  exact Classical.choose_spec (lift_cycle L n (-(c.t.comp (δ N (n + 1))))
    (by cases n <;> simpa [Cycle] using congrArg Neg.neg c.cycle))



/-- The only initial choice lifts the right augmentation, without splitting
of the coefficient sequence. -/
theorem initial (i : A →ₗ[R] B) (p : B →ₗ[R] C) (hi : Function.Injective i)
    (he : Function.Exact i p) (hp : Function.Surjective p) (hN : N.IsProjective) :
    ∃ (s : N.complex.X 0 →ₗ[R] B) (c : Correction L N 0),
      p.comp s = N.ε ∧ (i.comp L.ε).comp c.t + s.comp (δ N 0) = 0 := by
  letI := hN 0
  letI := hN 1
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p N.ε hp
  have hz : p.comp (-(s.comp (δ N 0))) = 0 := by
    rw [LinearMap.comp_neg, ← LinearMap.comp_assoc, hs, δ_augmentation, neg_zero]
  obtain ⟨t, ht⟩ := lift_exact (i.comp L.ε) p
    (L.surjective.comp_exact_iff_exact.mpr he) (-(s.comp (δ N 0))) hz
  have hc : Cycle L 0 (t.comp (δ N 1)) := by
    ext x
    change L.ε (t ((δ N 1) x)) = 0
    apply hi
    have ht' := LinearMap.congr_fun ht ((δ N 1) x)
    change i (L.ε (t ((δ N 1) x))) = -s ((δ N 0) ((δ N 1) x)) at ht'
    have hh := LinearMap.congr_fun (δ_square N 0) x
    change (δ N 0) ((δ N 1) x) = 0 at hh
    simpa only [hh, map_zero, neg_zero] using ht'
  refine ⟨s, ⟨t, hc⟩, hs, ?_⟩
  rw [ht, neg_add_cancel]

def corrections (hN : N.IsProjective) (c : Correction L N 0) :
    ∀ n, Correction L N n
  | 0 => c
  | n + 1 => next hN n (corrections hN c n)

def differential (hN : N.IsProjective) (c : Correction L N 0) (n : ℕ) :=
  upper (δ L n) (δ N n) (corrections hN c n).t

theorem exact_differential (hN : N.IsProjective) (c : Correction L N 0) (n : ℕ) :
    Function.Exact (differential hN c (n + 1)) (differential hN c n) := by
  apply exact_upper _ _ _ _ _ _
    (LinearMap.exact_iff.mpr (L.exact_succ n).symm)
    (LinearMap.exact_iff.mpr (N.exact_succ n).symm)
  exact next_equation hN n (corrections hN c n)

/-- The same elementary chase establishes exactness at the augmentation. -/
theorem exact_augmentation (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i p)
    (s : N.complex.X 0 →ₗ[R] B) (hs : p.comp s = N.ε)
    (c : Correction L N 0)
    (hc : (i.comp L.ε).comp c.t + s.comp (δ N 0) = 0) :
    Function.Exact (upper (δ L 0) (δ N 0) c.t) ((i.comp L.ε).coprod s) := by
  intro z
  constructor
  · intro hz
    change i (L.ε z.1) + s z.2 = 0 at hz
    have hy : N.ε z.2 = 0 := by
      have h := congrArg p hz
      have hps : p (s z.2) = N.ε z.2 := LinearMap.congr_fun hs z.2
      simpa only [map_add, he.apply_apply_eq_zero, zero_add, map_zero, hps] using h
    obtain ⟨y, hy⟩ := (LinearMap.exact_iff.mpr N.exact_zero.symm _).mp hy
    have hx : L.ε (z.1 - c.t y) = 0 := by
      apply hi
      have hh := LinearMap.congr_fun hc y
      change i (L.ε (c.t y)) + s ((δ N 0) y) = 0 at hh
      rw [hy] at hh
      rw [map_zero, map_sub, map_sub]
      exact sub_eq_zero.mpr (add_right_cancel (hz.trans hh.symm))
    obtain ⟨x, hx⟩ := (LinearMap.exact_iff.mpr L.exact_zero.symm _).mp hx
    refine ⟨(x,y), Prod.ext ?_ hy⟩
    change (δ L 0) x + c.t y = z.1
    rw [hx]
    abel
  · rintro ⟨x, rfl⟩
    change i (L.ε ((δ L 0) x.1 + c.t x.2)) + s ((δ N 0) x.2) = 0
    rw [map_add, map_add]
    have hh := LinearMap.congr_fun (δ_augmentation L) x.1
    change L.ε ((δ L 0) x.1) = 0 at hh
    rw [hh, map_zero, zero_add]
    exact LinearMap.congr_fun hc x.2

theorem surjective_augmentation (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (he : Function.Exact i p) (s : N.complex.X 0 →ₗ[R] B)
    (hs : p.comp s = N.ε) : Function.Surjective ((i.comp L.ε).coprod s) := by
  intro z
  obtain ⟨y, hy⟩ := N.surjective (p z)
  have hz : p (z - s y) = 0 := by
    rw [map_sub, ← LinearMap.comp_apply, hs, hy, sub_self]
  obtain ⟨a, ha⟩ := (he _).mp hz
  obtain ⟨x, hx⟩ := L.surjective a
  refine ⟨(x,y), ?_⟩
  change i (L.ε x) + s y = z
  rw [hx, ha]
  abel



def complex (hN : N.IsProjective) (c : Correction L N 0) :
    ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (L.complex.X n × N.complex.X n))
    (fun n => ModuleCat.ofHom (differential hN c n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact (exact_differential hN c n).linearMap_comp_eq_zero)

@[simp] theorem complex_d (hN : N.IsProjective) (c : Correction L N 0) (n : ℕ) :
    ((complex hN c).d (n + 1) n).hom = differential hN c n := by
  simp only [complex, ChainComplex.of_d]
  rfl

def middle (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i p)
    (hN : N.IsProjective) (s : N.complex.X 0 →ₗ[R] B) (hs : p.comp s = N.ε)
    (c : Correction L N 0)
    (hc : (i.comp L.ε).comp c.t + s.comp (δ N 0) = 0) : Resolution R B where
  complex := complex hN c
  ε := (i.comp L.ε).coprod s
  surjective := surjective_augmentation i p he s hs
  exact_zero := by
    rw [complex_d]
    exact (LinearMap.exact_iff.mp (exact_augmentation i p hi he s hs c hc)).symm
  exact_succ n := by
    simp only [complex_d]
    change LinearMap.range (differential hN c (n + 1)) =
      LinearMap.ker (differential hN c n)
    exact (LinearMap.exact_iff.mp (exact_differential hN c n)).symm

def inclusion (hN : N.IsProjective) (c : Correction L N 0) :
    L.complex ⟶ complex hN c :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.inl R _ _)) (by
    intro n
    apply ModuleCat.hom_ext
    change ((complex hN c).d (n + 1) n).hom.comp (LinearMap.inl R _ _) =
      (LinearMap.inl R _ _).comp (δ L n)
    rw [complex_d]
    ext x
    change ((δ L n) x + (corrections hN c n).t 0, (δ N n) 0) =
      ((δ L n) x, 0)
    simp)

def projection (hN : N.IsProjective) (c : Correction L N 0) :
    complex hN c ⟶ N.complex :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.snd R _ _)) (by
    intro n
    apply ModuleCat.hom_ext
    change (δ N n).comp (LinearMap.snd R _ _) =
      (LinearMap.snd R _ _).comp ((complex hN c).d (n + 1) n).hom
    rw [complex_d]
    rfl)

end Projective

theorem projective_horseshoe : projectiveHorseshoeType.{u,v} := by
  intro R _ A B C _ _ _ _ _ _ i p hi he hp L N hL hN
  obtain ⟨s, c, hs, hc⟩ := Projective.initial (L := L) (N := N) i p hi he hp hN
  refine ⟨{
    middle := Projective.middle i p hi he hN s hs c hc
    projective := ?_
    term := fun n => LinearEquiv.refl R _
    inclusion := Projective.inclusion hN c
    projection := Projective.projection hN c
    inclusion_apply := fun _ _ => rfl
    projection_apply := fun _ _ => rfl
    augmentation_inclusion := ?_
    augmentation_projection := ?_ }⟩
  · intro n
    letI := hL n
    letI := hN n
    change Module.Projective R (L.complex.X n × N.complex.X n)
    infer_instance
  · ext x
    change i (L.ε x) + s 0 = i (L.ε x)
    rw [map_zero, add_zero]
  · ext x
    change N.ε x.2 = p (i (L.ε x.1) + s x.2)
    rw [map_add, he.apply_apply_eq_zero, zero_add]
    exact (LinearMap.congr_fun hs x.2).symm



namespace Injective
open P103.Specs.Ch10.InjectiveResolutions
variable {R : Type u} [Ring R]
variable {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]
variable (L : Resolution R A) (N : Resolution R C)

abbrev δ (Q : Resolution R A) (n : ℕ) := (Q.complex.d n (n + 1)).hom

def Cocycle {X : Type*} [AddCommGroup X] [Module R X]
    (n : ℕ) (r : N.complex.X n →ₗ[R] X) : Prop :=
  match n with
  | 0 => r.comp N.η = 0
  | n + 1 => r.comp (δ N n) = 0

theorem δ_square (Q : Resolution R A) (n : ℕ) :
    (δ Q (n + 1)).comp (δ Q n) = 0 :=
  congrArg ModuleCat.Hom.hom (Q.complex.d_comp_d n (n + 1) (n + 2))

theorem δ_augmentation (Q : Resolution R A) : (δ Q 0).comp Q.η = 0 :=
  Q.exact_zero.linearMap_comp_eq_zero

theorem extend_cocycle {X : Type (max u v)} [AddCommGroup X] [Module R X]
    [Module.Injective R X] (n : ℕ) (r : N.complex.X n →ₗ[R] X)
    (hr : Cocycle N n r) :
    ∃ t : N.complex.X (n + 1) →ₗ[R] X, t.comp (δ N n) = r := by
  cases n with
  | zero => exact extend_exact _ _ N.exact_zero r hr
  | succ n => exact extend_exact _ _ (N.exact_succ n) r hr

structure Correction (n : ℕ) where
  t : N.complex.X n →ₗ[R] L.complex.X (n + 1)
  cycle : Cocycle N n ((δ L (n + 1)).comp t)

variable {L N}

def next (n : ℕ) (c : Correction L N n) : Correction L N (n + 1) := by
  letI := L.injectiveTerm (n + 2)
  have h : Cocycle N n (-((δ L (n + 1)).comp c.t)) := by
    cases n <;> simpa [Cocycle] using congrArg Neg.neg c.cycle
  let t := Classical.choose (extend_cocycle N n (-((δ L (n + 1)).comp c.t)) h)
  have ht : t.comp (δ N n) = -((δ L (n + 1)).comp c.t) :=
    Classical.choose_spec (extend_cocycle N n (-((δ L (n + 1)).comp c.t)) h)
  refine ⟨t, ?_⟩
  change ((δ L (n + 2)).comp t).comp (δ N n) = 0
  rw [LinearMap.comp_assoc, ht]
  ext x
  change (δ L (n + 2)) (-((δ L (n + 1)) (c.t x))) = 0
  rw [map_neg]
  have hs := LinearMap.congr_fun (δ_square L (n + 1)) (c.t x)
  change (δ L (n + 2)) ((δ L (n + 1)) (c.t x)) = 0 at hs
  rw [hs, neg_zero]

theorem next_equation (n : ℕ) (c : Correction L N n) :
    (δ L (n + 1)).comp c.t + (next n c).t.comp (δ N n) = 0 := by
  letI := L.injectiveTerm (n + 2)
  dsimp [next]
  apply add_eq_zero_iff_eq_neg'.mpr
  exact Classical.choose_spec (extend_cocycle N n (-((δ L (n + 1)).comp c.t))
    (by cases n <;> simpa [Cocycle] using congrArg Neg.neg c.cycle))

theorem initial (i : A →ₗ[R] B) (p : B →ₗ[R] C) (hi : Function.Injective i)
    (he : Function.Exact i p) (hp : Function.Surjective p) :
    ∃ (s : B →ₗ[R] L.complex.X 0) (c : Correction L N 0),
      s.comp i = L.η ∧ (δ L 0).comp s + (c.t.comp N.η).comp p = 0 := by
  letI := L.injectiveTerm 0
  letI := L.injectiveTerm 1
  obtain ⟨s, hs⟩ := Module.Injective.extension_property R _ _ _ i hi L.η
  have hz : (-((δ L 0).comp s)).comp i = 0 := by
    rw [LinearMap.neg_comp, LinearMap.comp_assoc, hs, δ_augmentation, neg_zero]
  obtain ⟨r, hr⟩ := extend_exact i p he (-((δ L 0).comp s)) hz
  obtain ⟨t, ht⟩ := Module.Injective.extension_property R _ _ _ N.η N.injective_η r
  have hc : Cocycle N 0 ((δ L 1).comp t) := by
    ext a
    obtain ⟨b, rfl⟩ := hp a
    change (δ L 1) (t (N.η (p b))) = 0
    have htr : t (N.η (p b)) = -(δ L 0) (s b) :=
      (LinearMap.congr_fun ht (p b)).trans (LinearMap.congr_fun hr b)
    rw [htr, map_neg]
    have hh := LinearMap.congr_fun (δ_square L 0) (s b)
    change (δ L 1) ((δ L 0) (s b)) = 0 at hh
    rw [hh, neg_zero]
  refine ⟨s, ⟨t, hc⟩, hs, ?_⟩
  rw [ht, hr, add_neg_cancel]

def corrections (c : Correction L N 0) : ∀ n, Correction L N n
  | 0 => c
  | n + 1 => next n (corrections c n)

def differential (c : Correction L N 0) (n : ℕ) :=
  upper (δ L n) (δ N n) (corrections c n).t

theorem exact_differential (c : Correction L N 0) (n : ℕ) :
    Function.Exact (differential c n) (differential c (n + 1)) := by
  exact exact_upper _ _ _ _ _ _ (L.exact_succ n) (N.exact_succ n)
    (next_equation n (corrections c n))



theorem injective_prod (E F : Type w) [AddCommGroup E] [AddCommGroup F]
    [Module R E] [Module R F] (hE : Module.Injective R E) (hF : Module.Injective R F) :
    Module.Injective R (E × F) := by
  constructor
  intro X Y _ _ _ _ f hf g
  obtain ⟨s, hs⟩ := hE.out f hf ((LinearMap.fst R E F).comp g)
  obtain ⟨t, ht⟩ := hF.out f hf ((LinearMap.snd R E F).comp g)
  exact ⟨s.prod t, fun x => Prod.ext (hs x) (ht x)⟩

theorem augmentation_square (p : B →ₗ[R] C) (s : B →ₗ[R] L.complex.X 0)
    (c : Correction L N 0)
    (hc : (δ L 0).comp s + (c.t.comp N.η).comp p = 0) :
    (upper (δ L 0) (δ N 0) c.t).comp (s.prod (N.η.comp p)) = 0 := by
  apply LinearMap.ext
  intro b
  apply Prod.ext
  · exact LinearMap.congr_fun hc b
  · exact LinearMap.congr_fun (δ_augmentation N) (p b)

theorem injective_augmentation (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (he : Function.Exact i p) (s : B →ₗ[R] L.complex.X 0)
    (hs : s.comp i = L.η) : Function.Injective (s.prod (N.η.comp p)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro b hb
  have h₁ : s b = 0 := congrArg Prod.fst hb
  have h₂ : N.η (p b) = 0 := congrArg Prod.snd hb
  have hpb : p b = 0 := N.injective_η (h₂.trans (map_zero N.η).symm)
  obtain ⟨a, ha⟩ := (he b).mp hpb
  have hη : L.η a = 0 := by
    rw [← hs]
    change s (i a) = 0
    rw [ha, h₁]
  have ha0 : a = 0 := L.injective_η (hη.trans (map_zero L.η).symm)
  change b = 0
  simpa only [ha0, map_zero] using ha.symm

theorem exact_augmentation (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (he : Function.Exact i p) (hp : Function.Surjective p)
    (s : B →ₗ[R] L.complex.X 0) (hs : s.comp i = L.η)
    (c : Correction L N 0)
    (hc : (δ L 0).comp s + (c.t.comp N.η).comp p = 0) :
    Function.Exact (s.prod (N.η.comp p)) (upper (δ L 0) (δ N 0) c.t) := by
  intro z
  constructor
  · intro hz
    have hz₁ : (δ L 0) z.1 + c.t z.2 = 0 := congrArg Prod.fst hz
    have hz₂ : (δ N 0) z.2 = 0 := congrArg Prod.snd hz
    obtain ⟨a, ha⟩ := (N.exact_zero z.2).mp hz₂
    obtain ⟨b, hb⟩ := hp a
    have hy : N.η (p b) = z.2 := by rw [hb, ha]
    have hx : (δ L 0) (z.1 - s b) = 0 := by
      have hh := LinearMap.congr_fun hc b
      change (δ L 0) (s b) + c.t (N.η (p b)) = 0 at hh
      rw [hy] at hh
      rw [map_sub]
      exact sub_eq_zero.mpr (add_right_cancel (hz₁.trans hh.symm))
    obtain ⟨a', ha'⟩ := (L.exact_zero _).mp hx
    refine ⟨b + i a', ?_⟩
    apply Prod.ext
    · change s (b + i a') = z.1
      rw [map_add, ← LinearMap.comp_apply, hs, ha']
      abel
    · change N.η (p (b + i a')) = z.2
      rw [map_add, he.apply_apply_eq_zero, add_zero, hy]
  · rintro ⟨b, rfl⟩
    exact LinearMap.congr_fun (augmentation_square p s c hc) b

def complex (c : Correction L N 0) : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (L.complex.X n × N.complex.X n))
    (fun n => ModuleCat.ofHom (differential c n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact (exact_differential c n).linearMap_comp_eq_zero)

@[simp] theorem complex_d (c : Correction L N 0) (n : ℕ) :
    ((complex c).d n (n + 1)).hom = differential c n := by
  simp only [complex, CochainComplex.of_d]
  rfl

def middle (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (he : Function.Exact i p) (hp : Function.Surjective p)
    (s : B →ₗ[R] L.complex.X 0) (hs : s.comp i = L.η)
    (c : Correction L N 0)
    (hc : (δ L 0).comp s + (c.t.comp N.η).comp p = 0) : Resolution R B where
  complex := complex c
  injectiveTerm n := injective_prod _ _ (L.injectiveTerm n) (N.injectiveTerm n)
  η := s.prod (N.η.comp p)
  injective_η := injective_augmentation i p he s hs
  exact_zero := by
    rw [complex_d]
    exact exact_augmentation i p he hp s hs c hc
  exact_succ n := by
    simp only [complex_d]
    change Function.Exact (differential c n) (differential c (n + 1))
    exact exact_differential c n

def inclusion (c : Correction L N 0) : L.complex ⟶ complex c :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.inl R _ _)) (by
    intro n
    apply ModuleCat.hom_ext
    change ((complex c).d n (n + 1)).hom.comp (LinearMap.inl R _ _) =
      (LinearMap.inl R _ _).comp (δ L n)
    rw [complex_d]
    ext x
    change ((δ L n) x + (corrections c n).t 0, (δ N n) 0) = ((δ L n) x, 0)
    simp)

def projection (c : Correction L N 0) : complex c ⟶ N.complex :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.snd R _ _)) (by
    intro n
    apply ModuleCat.hom_ext
    change (δ N n).comp (LinearMap.snd R _ _) =
      (LinearMap.snd R _ _).comp ((complex c).d n (n + 1)).hom
    rw [complex_d]
    rfl)

end Injective

theorem injective_horseshoe : injectiveHorseshoeType.{u,v} := by
  intro R _ A B C _ _ _ _ _ _ i p hi he hp L N
  obtain ⟨s, c, hs, hc⟩ := Injective.initial (L := L) (N := N) i p hi he hp
  refine ⟨{
    middle := Injective.middle i p he hp s hs c hc
    term := fun n => LinearEquiv.refl R _
    inclusion := Injective.inclusion c
    projection := Injective.projection c
    inclusion_apply := fun _ _ => rfl
    projection_apply := fun _ _ => rfl
    augmentation_inclusion := ?_
    augmentation_projection := rfl }⟩
  ext a
  apply Prod.ext
  · exact (LinearMap.congr_fun hs a).symm
  · change 0 = N.η (p (i a))
    rw [he.apply_apply_eq_zero, map_zero]



/-- The specified product coordinates give an actual split short exact row. -/
theorem split_of_product {R : Type u} [Ring R] {U V W : Type*}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module R U] [Module R V] [Module R W]
    (e : V ≃ₗ[R] U × W) (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (hf : ∀ x, e (f x) = (x, 0)) (hg : ∀ z, g z = (e z).2) :
    DegreewiseSplit f g := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y h
    have h' := congrArg e h
    rw [hf, hf] at h'
    exact congrArg Prod.fst h'
  · intro z
    constructor
    · intro hz
      refine ⟨(e z).1, e.injective ?_⟩
      rw [hf]
      apply Prod.ext
      · rfl
      · exact (hg z).symm.trans hz |>.symm
    · rintro ⟨x, rfl⟩
      rw [hg, hf]
  · intro w
    refine ⟨e.symm (0, w), ?_⟩
    rw [hg, e.apply_symm_apply]
  · refine ⟨e.symm.toLinearMap.comp (LinearMap.inr R U W), ?_⟩
    ext w
    change g (e.symm (0, w)) = w
    rw [hg, e.apply_symm_apply]
  · refine ⟨(LinearMap.fst R U W).comp e.toLinearMap, ?_⟩
    ext x
    change (e (f x)).1 = x
    rw [hf]

theorem projective_degreewise_split : projectiveDegreewiseSplitType.{u,v} := by
  intro R _ A B C _ _ _ _ _ _ i p L N H n
  exact split_of_product (H.term n) _ _ (H.inclusion_apply n) (H.projection_apply n)

theorem injective_degreewise_split : injectiveDegreewiseSplitType.{u,v} := by
  intro R _ A B C _ _ _ _ _ _ i p L N H n
  exact split_of_product (H.term n) _ _ (H.inclusion_apply n) (H.projection_apply n)

end P103.Ch10.Horseshoe
