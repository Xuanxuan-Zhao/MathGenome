import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ArtinSurjectionsAndGluing
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LargestArtinLiftQuotient
import Batteries.Tactic.OpenPrivate

/-! The smallest quotient kernel on which an element of F(A) lifts. -/

universe u w

namespace CommutativeAlgebraNotes

open LargestArtinLiftQuotientSpec CategoryTheory

namespace LocalArtinAlgebra

variable {k : Type u} [Field k] {A B : LocalArtinAlgebra.{u,u} k}

/-- A vector subspace of a kernel killed by the maximal ideal is an ideal:
multiplication on the kernel is given by the residue scalar. -/
def idealOfSocleSubmodule (f : Hom B A)
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal B, ∀ b ∈ RingHom.ker f.val.toRingHom, a * b = 0)
    (J : Submodule k B) (hJ : J ≤ kernelSubspace f) : Ideal B where
  carrier := J
  zero_mem' := J.zero_mem
  add_mem' := J.add_mem
  smul_mem' a b hb := by
    have ha : a - algebraMap k B (B.residue a) ∈ IsLocalRing.maximalIdeal B := by
      rw [← ker_residue B, RingHom.mem_ker]
      simp
    have heq := hkill _ ha b (hJ hb)
    rw [sub_mul, sub_eq_zero, ← Algebra.smul_def] at heq
    change a * b ∈ J
    rw [heq]
    exact J.smul_mem _ hb

@[simp]
theorem restrictScalars_idealOfSocleSubmodule (f : Hom B A)
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal B, ∀ b ∈ RingHom.ker f.val.toRingHom, a * b = 0)
    (J : Submodule k B) (hJ : J ≤ kernelSubspace f) :
    (idealOfSocleSubmodule f hkill J hJ).restrictScalars k = J :=
  rfl

end LocalArtinAlgebra

namespace ArtinFunctor

open LocalArtinAlgebra
open private map_comp_apply ker_le_maximalIdeal from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ArtinSurjectionsAndGluing

variable {k : Type u} [Field k] {A B Q P : LocalArtinAlgebra.{u,u} k}

/-- The element x lifts over the quotient of B by J. -/
abbrev LiftsModulo (F : ArtinFunctor.{u,w} k) (f : Hom B A)
    (x : F.toFunctor.obj A) (J : Submodule k B) : Prop :=
  LiftsModuloModel F f x J

private theorem lift_of_presentation (F : ArtinFunctor.{u,w} k) {f : Hom B A}
    {x : F.toFunctor.obj A} {J : Submodule k B} (h : F.LiftsModulo f x J)
    (p : Hom B P) (r : Hom P A) (hker : J ≤ kernelSubspace p) (hp : r.comp p = f) :
    ∃ z : F.toFunctor.obj P, F.toFunctor.map r z = x := by
  obtain ⟨Q, q, g, hq, hqker, hcomp, y, hy⟩ := h
  have hle : RingHom.ker q.val.toRingHom ≤ RingHom.ker p.val.toRingHom := by
    change kernelSubspace q ≤ kernelSubspace p
    rwa [hqker]
  let d := q.val.liftOfSurjective hq p.val hle
  have hd (b : B) : d (q b) = p b := AlgHom.liftOfSurjective_apply q.val hq p.val hle b
  let e : Hom Q P := ⟨d, ⟨fun a ha => by
    obtain ⟨b, rfl⟩ := hq a
    exact (IsUnit.of_map p.val b (hd b ▸ ha)).map q.val⟩⟩
  have he : r.comp e = g := by
    apply Hom.ext
    intro a
    obtain ⟨b, rfl⟩ := hq a
    change r (d (q b)) = g (q b)
    rw [hd b]
    exact congrArg (fun m : Hom B A => m b) (hp.trans hcomp.symm)
  exact ⟨F.toFunctor.map e y, (map_comp_apply F e r y).symm.trans
    (he ▸ hy : F.toFunctor.map (r.comp e) y = x)⟩

/-- A lift expressed through a quotient presentation is equivalent to a lift over
the canonical Artin quotient with the map induced by f. -/
theorem liftsModulo_iff_quotientLift (F : ArtinFunctor.{u,w} k) (f : Hom B A)
    (x : F.toFunctor.obj A) (J : Ideal B) (hmax : J ≤ IsLocalRing.maximalIdeal B)
    (hJ : J ≤ RingHom.ker f.val.toRingHom) :
    F.LiftsModulo f x (J.restrictScalars k) ↔
      ∃ y : F.toFunctor.obj (B.quotient J hmax),
        F.toFunctor.map (quotientLift J hmax f hJ) y = x := by
  have hker : kernelSubspace (quotientMk J hmax) = J.restrictScalars k :=
    congrArg (fun I : Ideal B => I.restrictScalars k) (ker_quotientMk J hmax)
  have hcomp := quotientLift_comp_quotientMk J hmax f hJ
  exact ⟨fun h => lift_of_presentation F h _ _ hker.ge hcomp, fun h =>
    ⟨_, _, _, quotientMk_surjective J hmax, hker, hcomp, h⟩⟩

private theorem liftsModulo_mono (F : ArtinFunctor.{u,w} k) {f : Hom B A}
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal B, ∀ b ∈ RingHom.ker f.val.toRingHom, a * b = 0)
    {x : F.toFunctor.obj A} {J L : Submodule k B} (hJL : J ≤ L)
    (hL : L ≤ kernelSubspace f) (h : F.LiftsModulo f x J) : F.LiftsModulo f x L := by
  let I := idealOfSocleSubmodule f hkill L hL
  have hIf : I ≤ RingHom.ker f.val.toRingHom := hL
  have hmax := hIf.trans (ker_le_maximalIdeal f)
  apply (F.liftsModulo_iff_quotientLift f x I hmax hIf).mpr
  apply lift_of_presentation F h (quotientMk I hmax) (quotientLift I hmax f hIf)
  · change J ≤ (RingHom.ker (quotientMk I hmax).val.toRingHom).restrictScalars k
    rw [ker_quotientMk]
    exact hJL
  · exact quotientLift_comp_quotientMk I hmax f hIf

/-- When the two quotient kernels sum to ker f, their fibre product is a
quotient of B with kernel their intersection. -/
private theorem liftsModulo_inf_of_sup_eq (F : ArtinFunctor.{u,w} k) (hF : F.H1)
    {f : Hom B A} (hf : Function.Surjective f) {x : F.toFunctor.obj A}
    {J₁ J₂ : Submodule k B} (hsup : J₁ ⊔ J₂ = kernelSubspace f)
    (h₁ : F.LiftsModulo f x J₁) (h₂ : F.LiftsModulo f x J₂) :
    F.LiftsModulo f x (J₁ ⊓ J₂) := by
  obtain ⟨Q₁, q₁, g₁, hq₁, hk₁, hc₁, y₁, hy₁⟩ := h₁
  obtain ⟨Q₂, q₂, g₂, hq₂, hk₂, hc₂, y₂, hy₂⟩ := h₂
  let l := pullbackLift g₁ g₂ q₁ q₂ (hc₁.trans hc₂.symm)
  have hl : Function.Surjective l.val := by
    intro p
    obtain ⟨b, hb⟩ := hq₁ ((pullbackFst g₁ g₂).val p)
    obtain ⟨c, hc⟩ := hq₂ ((pullbackSnd g₁ g₂).val p)
    have hd : b - c ∈ kernelSubspace f := by
      change f.val (b - c) = 0
      rw [map_sub, sub_eq_zero, ← congrArg (fun m : Hom B A => m b) hc₁,
        ← congrArg (fun m : Hom B A => m c) hc₂]
      change g₁ (q₁ b) = g₂ (q₂ c)
      rw [hb, hc]
      exact p.property
    rw [← hsup] at hd
    obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ := Submodule.mem_sup.mp hd
    have hz₁ : q₁.val j₁ = 0 := show j₁ ∈ kernelSubspace q₁ by rwa [hk₁]
    have hz₂ : q₂.val j₂ = 0 := show j₂ ∈ kernelSubspace q₂ by rwa [hk₂]
    have hbc : b - j₁ = c + j₂ := by
      rw [sub_eq_iff_eq_add]
      calc
        b = (b - c) + c := (sub_add_cancel b c).symm
        _ = (c + j₂) + j₁ := by rw [← hj]; ac_rfl
    refine ⟨b - j₁, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change q₁.val (b - j₁) = _
      rw [map_sub, hz₁, sub_zero]
      exact hb
    · change q₂.val (b - j₁) = _
      rw [hbc, map_add, hz₂, add_zero]
      exact hc
  have hkl : kernelSubspace l = J₁ ⊓ J₂ := by
    ext b
    rw [Submodule.mem_inf, ← hk₁, ← hk₂]
    change l.val b = 0 ↔ q₁ b = 0 ∧ q₂ b = 0
    exact ⟨fun h => ⟨congrArg (fun p => (pullbackFst g₁ g₂).val p) h,
      congrArg (fun p => (pullbackSnd g₁ g₂).val p) h⟩,
      fun h => Subtype.ext (Prod.ext h.1 h.2)⟩
  have hg₂ : Function.Surjective g₂ := by
    intro a
    obtain ⟨b, rfl⟩ := hf a
    exact ⟨q₂ b, congrArg (fun m : Hom B A => m b) hc₂⟩
  obtain ⟨z, hz⟩ := F.comparison_surjective_of_surjective hF g₁ g₂ hg₂
    ⟨(y₁, y₂), hy₁.trans hy₂.symm⟩
  have hz₁ : F.toFunctor.map (pullbackFst g₁ g₂) z = y₁ :=
    congrArg (fun p => p.val.1) hz
  let r := g₁.comp (pullbackFst g₁ g₂)
  refine ⟨_, l, r, hl, hkl, hc₁, z, ?_⟩
  change F.toFunctor.map (g₁.comp (pullbackFst g₁ g₂)) z = x
  rw [map_comp_apply, hz₁, hy₁]

private theorem liftsModulo_inf (F : ArtinFunctor.{u,w} k) (hF : F.H1)
    {f : Hom B A} (hf : Function.Surjective f)
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal B, ∀ b ∈ RingHom.ker f.val.toRingHom, a * b = 0)
    {x : F.toFunctor.obj A} {J₁ J₂ : Submodule k B}
    (hJ₁ : J₁ ≤ kernelSubspace f) (hJ₂ : J₂ ≤ kernelSubspace f)
    (h₁ : F.LiftsModulo f x J₁) (h₂ : F.LiftsModulo f x J₂) :
    F.LiftsModulo f x (J₁ ⊓ J₂) := by
  obtain ⟨C, hC⟩ := (J₁ ⊔ J₂).exists_isCompl
  let D := C ⊓ kernelSubspace f
  have hsup : (J₁ ⊔ J₂) ⊔ D = kernelSubspace f := by
    change (J₁ ⊔ J₂) ⊔ (C ⊓ kernelSubspace f) = _
    rw [← sup_inf_assoc_of_le C (sup_le hJ₁ hJ₂), hC.sup_eq_top, top_inf_eq]
  have hdis : (J₁ ⊔ J₂) ⊓ D = ⊥ := by
    change (J₁ ⊔ J₂) ⊓ (C ⊓ kernelSubspace f) = _
    rw [← inf_assoc, hC.inf_eq_bot, bot_inf_eq]
  have hinf : (J₁ ⊔ D) ⊓ J₂ = J₁ ⊓ J₂ := by
    calc
      (J₁ ⊔ D) ⊓ J₂ = ((J₁ ⊔ D) ⊓ (J₁ ⊔ J₂)) ⊓ J₂ := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : J₂ ≤ J₁ ⊔ J₂)]
      _ = J₁ ⊓ J₂ := by
        rw [sup_inf_assoc_of_le D (le_sup_left : J₁ ≤ J₁ ⊔ J₂),
          inf_comm D (J₁ ⊔ J₂), hdis, sup_bot_eq]
  have hsup' : (J₁ ⊔ D) ⊔ J₂ = kernelSubspace f := (sup_right_comm J₁ D J₂).trans hsup
  have h₁' : F.LiftsModulo f x (J₁ ⊔ D) :=
    liftsModulo_mono F hkill le_sup_left (sup_le hJ₁ inf_le_right) h₁
  rw [← hinf]
  exact liftsModulo_inf_of_sup_eq F hF hf hsup' h₁' h₂

/-- Under H1 there is a least vector subspace J of the annihilated kernel
of B → A such that x lifts over B/J. -/
theorem exists_least_lift_subspace (F : ArtinFunctor.{u,w} k) (hF : F.H1)
    {A B : LocalArtinAlgebra.{u,u} k} (f : Hom B A) (hf : Function.Surjective f)
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal B, ∀ b ∈ RingHom.ker f.val.toRingHom, a * b = 0)
    (x : F.toFunctor.obj A) :
    ∃ J : Submodule k B,
      IsLeast {L | L ≤ kernelSubspace f ∧ F.LiftsModulo f x L} J := by
  classical
  let : Module.Finite k B := moduleFinite B
  let S : Set (Submodule k B) := {L | L ≤ kernelSubspace f ∧ F.LiftsModulo f x L}
  let P (n : ℕ) := ∃ J ∈ S, Module.finrank k J = n
  have hK : kernelSubspace f ∈ S := by
    refine ⟨le_rfl, ⟨A, f, Hom.id A, hf, rfl, rfl, x, ?_⟩⟩
    exact ConcreteCategory.congr_hom (F.toFunctor.map_id A) x
  have hP : ∃ n, P n := ⟨_, _, hK, rfl⟩
  obtain ⟨J, hJ, hd⟩ := Nat.find_spec hP
  refine ⟨J, hJ, ?_⟩
  intro L hL
  have hJL : J ⊓ L ∈ S :=
    ⟨inf_le_left.trans hJ.1, liftsModulo_inf F hF hf hkill hJ.1 hL.1 hJ.2 hL.2⟩
  have hdim : Module.finrank k J ≤ Module.finrank k ↥(J ⊓ L) :=
    hd.trans_le (Nat.find_min' hP ⟨_, hJL, rfl⟩)
  have heq := Submodule.eq_of_le_of_finrank_le (S₁ := J ⊓ L) inf_le_left hdim
  exact heq ▸ inf_le_right

end ArtinFunctor
end CommutativeAlgebraNotes
