import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerConditions
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ArtinSurjectionsAndGluing
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Factorisation of Artin surjections and gluing under H1. -/

universe u v w

namespace CommutativeAlgebraNotes

namespace LocalArtinAlgebra

open ArtinSurjectionsAndGluingSpec

variable {k : Type u} [Field k]
variable {A B C : LocalArtinAlgebra.{u,v} k}

/-- A finite composite of small extensions, with isomorphisms as length-zero composites. -/
abbrev SmallExtensionChain {A B : LocalArtinAlgebra.{u,v} k} (f : Hom A B) (n : ℕ) :=
  SmallExtensionChainModel f n

/-- The identity is the empty composite of small extensions. -/
theorem smallExtensionChain_id (A : LocalArtinAlgebra.{u,v} k) :
    SmallExtensionChain (Hom.id A) 0 :=
  .zero _ Function.bijective_id

/-- Quotient by an ideal contained in the maximal ideal, with its induced residue map. -/
def quotient (A : LocalArtinAlgebra.{u,v} k) (I : Ideal A)
    (hI : I ≤ IsLocalRing.maximalIdeal A) : LocalArtinAlgebra.{u,v} k := by
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top hI)
  letI : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI : Module.Finite k A := moduleFinite A
  letI : Module.Finite k (A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I).toLinearMap
      (Ideal.Quotient.mkₐ_surjective k I)
  letI : IsArtinianRing (A ⧸ I) := IsArtinianRing.of_finite k _
  have hker : I ≤ RingHom.ker A.residue := (ker_residue A).symm ▸ hI
  let ρ := Ideal.Quotient.liftₐ I A.residue hker
  refine { carrier := A ⧸ I, residue := ρ, localResidue := ⟨?_⟩ }
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) x
  exact (IsUnit.of_map A.residue a hx).map (Ideal.Quotient.mk I)

/-- The canonical map to the quotient by an ideal in the maximal ideal. -/
def quotientMk (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) :
    Hom A (A.quotient I hI) := by
  let q : A →ₐ[k] A.quotient I hI := Ideal.Quotient.mkₐ k I
  exact ⟨q, ⟨(IsLocalHom.of_surjective q.toRingHom (Ideal.Quotient.mkₐ_surjective k I)).map_nonunit⟩⟩

theorem quotientMk_surjective (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) :
    Function.Surjective (quotientMk I hI) :=
  Ideal.Quotient.mkₐ_surjective k I

@[simp]
theorem ker_quotientMk (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) :
    RingHom.ker (quotientMk I hI).val.toRingHom = I :=
  Ideal.Quotient.mkₐ_ker k I

/-- A local map that kills an ideal descends to the corresponding quotient. -/
def quotientLift (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (f : Hom A B)
    (hf : I ≤ RingHom.ker f.val.toRingHom) : Hom (A.quotient I hI) B := by
  refine ⟨Ideal.Quotient.liftₐ I f.val hf, ⟨?_⟩⟩
  intro x hx
  obtain ⟨a, rfl⟩ := quotientMk_surjective I hI x
  exact (IsUnit.of_map f.val a hx).map (quotientMk I hI).val

@[simp]
theorem quotientLift_comp_quotientMk (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A)
    (f : Hom A B) (hf : I ≤ RingHom.ker f.val.toRingHom) :
    (quotientLift I hI f hf).comp (quotientMk I hI) = f :=
  Hom.ext fun _ => rfl

private theorem ker_le_maximalIdeal (f : Hom A B) :
    RingHom.ker f.val.toRingHom ≤ IsLocalRing.maximalIdeal A := by
  intro a ha
  rw [← ker_residue A, RingHom.mem_ker, ← f.residue_apply a]
  change f a = 0 at ha
  rw [ha, map_zero]

private theorem exists_socle_line (K : Ideal A) (hK : K ≠ ⊥) :
    ∃ I : Ideal A, I ≤ K ∧ Module.finrank k I = 1 ∧
      ∀ a ∈ IsLocalRing.maximalIdeal A, ∀ b ∈ I, a * b = 0 := by
  classical
  let m := IsLocalRing.maximalIdeal A
  have hnil : ∃ n : ℕ, m ^ n * K = ⊥ := by
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
    exact ⟨n, by rw [show m ^ n = ⊥ from hn, Ideal.bot_mul]⟩
  have hmin := Nat.find_spec hnil
  cases hn : Nat.find hnil with
  | zero => exact (hK (by simpa [hn] using hmin)).elim
  | succ n =>
    have hprev : m ^ n * K ≠ ⊥ :=
      fun h => Nat.not_lt_of_ge (Nat.find_min' hnil h) (by omega)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hprev
    have hkill (a : A) (ha : a ∈ m) : a * x = 0 := by
      have hp : a * x ∈ m ^ (n + 1) * K := by
        rw [pow_succ', mul_assoc]
        exact Ideal.mul_mem_mul ha hx
      rw [show m ^ (n + 1) * K = ⊥ by simpa only [hn] using hmin] at hp
      simpa using hp
    have hscalar (a : A) : a * x = A.residue a • x := by
      have ha : a - algebraMap k A (A.residue a) ∈ m := by
        change _ ∈ IsLocalRing.maximalIdeal A
        rw [← ker_residue A, RingHom.mem_ker]
        simp
      have h := hkill _ ha
      rwa [sub_mul, sub_eq_zero, ← Algebra.smul_def] at h
    let I := Ideal.span ({x} : Set A)
    have hline : I.restrictScalars k = Submodule.span k ({x} : Set A) := by
      apply le_antisymm
      · intro y hy
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp
          (show y ∈ Ideal.span ({x} : Set A) from hy)
        exact Submodule.mem_span_singleton.mpr ⟨A.residue a, (hscalar a).symm⟩
      · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_span_singleton_self x))
    refine ⟨I, (Ideal.span_singleton_le_iff_mem K).mpr (Ideal.mul_le_right hx), ?_, ?_⟩
    · change Module.finrank k (I.restrictScalars k) = 1
      rw [hline]
      exact finrank_span_singleton hx0
    · intro a ha b hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      rw [mul_left_comm, hkill a ha, mul_zero]

private theorem smallExtension_comp_of_bijective (f : Hom A B) (g : Hom B C)
    (hf : SmallExtension f) (hg : Function.Bijective g) : SmallExtension (g.comp f) := by
  have heq : RingHom.ker (g.comp f).val.toRingHom = RingHom.ker f.val.toRingHom := by
    ext a
    simp only [RingHom.mem_ker]
    change g (f a) = 0 ↔ f a = 0
    rw [← map_zero g.val, hg.1.eq_iff]
  change Function.Surjective (g.comp f) ∧
    Module.finrank k (RingHom.ker (g.comp f).val.toRingHom) = 1 ∧
    ∀ a ∈ IsLocalRing.maximalIdeal A,
      ∀ b ∈ RingHom.ker (g.comp f).val.toRingHom, a * b = 0
  rw [heq]
  exact ⟨hg.2.comp hf.1, hf.2⟩

private theorem bijective_of_chain_length_zero {f : Hom A B} {n : ℕ}
    (hf : SmallExtensionChain f n) (hn : n = 0) : Function.Bijective f := by
  cases hf with
  | zero _ h => exact h
  | single => contradiction
  | cons => contradiction

/-- Every surjection of local Artin algebras is a finite composite of small extensions. -/
theorem surjection_factors_smallExtensions (f : Hom A B) (hf : Function.Surjective f) :
    ∃ n : ℕ, SmallExtensionChain f n := by
  classical
  generalize hd : Module.finrank k A = d
  induction d using Nat.strong_induction_on generalizing A with
  | h d ih =>
    by_cases hK : RingHom.ker f.val.toRingHom = ⊥
    · exact ⟨0, .zero f ⟨(RingHom.injective_iff_ker_eq_bot f.val.toRingHom).mpr hK, hf⟩⟩
    obtain ⟨I, hIf, hdim, hkill⟩ := exists_socle_line _ hK
    have hI := hIf.trans (ker_le_maximalIdeal f)
    let q := quotientMk I hI
    let g := quotientLift I hI f hIf
    have hcomp : g.comp q = f := quotientLift_comp_quotientMk I hI f hIf
    have hq : SmallExtension q := by
      change SmallExtensionModel q
      unfold SmallExtensionModel
      rw [show RingHom.ker q.val.toRingHom = I from ker_quotientMk I hI]
      exact ⟨quotientMk_surjective I hI, hdim, hkill⟩
    have hg : Function.Surjective g := by
      intro b
      obtain ⟨a, rfl⟩ := hf b
      exact ⟨q a, congrArg (fun e : Hom A B => e a) hcomp⟩
    let : Module.Finite k A := moduleFinite A
    have hd' : Module.finrank k (A.quotient I hI) + 1 = d := by
      change Module.finrank k (A ⧸ I) + 1 = d
      have h := (I.restrictScalars k).finrank_quotient_add_finrank
      change Module.finrank k (A ⧸ I) + Module.finrank k I = Module.finrank k A at h
      simpa only [hdim, hd] using h
    obtain ⟨n, hn⟩ := ih _ (by omega) g hg rfl
    rw [← hcomp]
    cases n with
    | zero =>
      exact ⟨1, .single _ (smallExtension_comp_of_bijective q g hq
        (bijective_of_chain_length_zero hn rfl))⟩
    | succ n => exact ⟨_, .cons q g hq hn⟩

end LocalArtinAlgebra

namespace ArtinFunctor

open LocalArtinAlgebra CategoryTheory

variable {k : Type u} [Field k]
variable {A₁ A B C : LocalArtinAlgebra.{u,u} k}

private theorem map_comp_apply (F : ArtinFunctor.{u,w} k)
    (f : Hom A B) (g : Hom B C) (x : F.toFunctor.obj A) :
    F.toFunctor.map (g.comp f) x = F.toFunctor.map g (F.toFunctor.map f x) :=
  ConcreteCategory.congr_hom (F.toFunctor.map_comp f g) x

private theorem comparison_surjective_of_bijective (F : ArtinFunctor.{u,w} k)
    (f : Hom A₁ A) (g : Hom B A) (hg : Function.Bijective g) :
    Function.Surjective (F.comparison f g) := by
  let e := AlgEquiv.ofBijective g.val hg
  let s : Hom A B :=
    ⟨e.symm.toAlgHom, ⟨(IsLocalHom.of_surjective e.symm.toRingHom e.symm.surjective).map_nonunit⟩⟩
  have hgs : ∀ a, g (s a) = a := e.apply_symm_apply
  have hsg : s.comp g = Hom.id B := Hom.ext e.symm_apply_apply
  let l := pullbackLift f g (Hom.id A₁) (s.comp f) (Hom.ext fun a => (hgs (f a)).symm)
  intro p
  have hp : F.toFunctor.map f p.val.1 = F.toFunctor.map g p.val.2 := p.property
  refine ⟨F.toFunctor.map l p.val.1, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change F.toFunctor.map (pullbackFst f g) (F.toFunctor.map l p.val.1) = p.val.1
    rw [← map_comp_apply, show (pullbackFst f g).comp l = Hom.id A₁ from Hom.ext fun _ => rfl]
    exact ConcreteCategory.congr_hom (F.toFunctor.map_id A₁) _
  · change F.toFunctor.map (pullbackSnd f g) (F.toFunctor.map l p.val.1) = p.val.2
    rw [← map_comp_apply, show (pullbackSnd f g).comp l = s.comp f from Hom.ext fun _ => rfl,
      map_comp_apply, hp, ← map_comp_apply, hsg]
    exact ConcreteCategory.congr_hom (F.toFunctor.map_id B) _

private theorem comparison_surjective_comp (F : ArtinFunctor.{u,w} k)
    (f : Hom A₁ A) (g : Hom B A) (q : Hom C B)
    (hg : Function.Surjective (F.comparison f g))
    (hq : Function.Surjective (F.comparison (pullbackSnd f g) q)) :
    Function.Surjective (F.comparison f (g.comp q)) := by
  let a := pullbackFst f g
  let b := pullbackSnd f g
  let c := pullbackFst b q
  let d := pullbackSnd b q
  have h : f.comp (a.comp c) = (g.comp q).comp d := by
    rw [show f.comp (a.comp c) = (f.comp a).comp c from rfl,
      show f.comp a = g.comp b from pullback_comm f g]
    change g.comp (b.comp c) = g.comp (q.comp d)
    rw [show b.comp c = q.comp d from pullback_comm b q]
  let l := pullbackLift f (g.comp q) (a.comp c) d h
  rintro ⟨⟨x, y⟩, hxy⟩
  have hxy' : F.toFunctor.map f x = F.toFunctor.map g (F.toFunctor.map q y) :=
    hxy.trans (map_comp_apply F q g y)
  obtain ⟨z, hz⟩ := hg ⟨(x, F.toFunctor.map q y), hxy'⟩
  have hza : F.toFunctor.map a z = x := congrArg (fun p => p.val.1) hz
  have hzb : F.toFunctor.map b z = F.toFunctor.map q y := congrArg (fun p => p.val.2) hz
  obtain ⟨t, ht⟩ := hq ⟨(z, y), hzb⟩
  have htc : F.toFunctor.map c t = z := congrArg (fun p => p.val.1) ht
  have htd : F.toFunctor.map d t = y := congrArg (fun p => p.val.2) ht
  refine ⟨F.toFunctor.map l t, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change F.toFunctor.map (pullbackFst f (g.comp q)) (F.toFunctor.map l t) = x
    rw [← map_comp_apply,
      show (pullbackFst f (g.comp q)).comp l = a.comp c from Hom.ext fun _ => rfl,
      map_comp_apply, htc, hza]
  · change F.toFunctor.map (pullbackSnd f (g.comp q)) (F.toFunctor.map l t) = y
    rw [← map_comp_apply,
      show (pullbackSnd f (g.comp q)).comp l = d from Hom.ext fun _ => rfl, htd]

private theorem comparison_surjective_of_chain (F : ArtinFunctor.{u,w} k) (hF : F.H1)
    {g : Hom B A} {n : ℕ} (hg : SmallExtensionChain g n) :
    ∀ {A₁ : LocalArtinAlgebra.{u,u} k} (f : Hom A₁ A),
      Function.Surjective (F.comparison f g) := by
  induction hg with
  | zero g h => exact fun f => comparison_surjective_of_bijective F f g h
  | single g h => exact fun f => hF f g h
  | cons q g hq _ ih =>
    intro A₁ f
    exact comparison_surjective_comp F f g q (ih f) (hF (pullbackSnd f g) q hq)

/-- H1 gives surjectivity of the fibre-product comparison along any surjective second leg. -/
theorem comparison_surjective_of_surjective (F : ArtinFunctor.{u,w} k) (hF : F.H1)
    {A₁ A A₂ : LocalArtinAlgebra.{u,u} k} (f : Hom A₁ A) (g : Hom A₂ A) (hg : Function.Surjective g) :
    Function.Surjective (F.comparison f g) := by
  obtain ⟨_, h⟩ := surjection_factors_smallExtensions g hg
  exact comparison_surjective_of_chain F hF h f

end ArtinFunctor
end CommutativeAlgebraNotes
