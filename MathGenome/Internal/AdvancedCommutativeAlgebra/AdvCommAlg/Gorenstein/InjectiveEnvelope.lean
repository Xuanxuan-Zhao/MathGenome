import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.InjectiveEnvelope
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Zorn

noncomputable section
namespace AdvCommAlg.Gorenstein
universe u
variable {R : Type u} [Ring R]
variable {M E F : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- Elementwise form of an essential extension inside a fixed ambient module. -/
def EssentialIn (A B : Submodule R E) : Prop :=
  A ≤ B ∧ ∀ x ∈ B, x ≠ 0 → ∃ r : R, r • x ∈ A ∧ r • x ≠ 0

lemma EssentialIn.refl (A : Submodule R E) : EssentialIn A A :=
  ⟨le_rfl, fun x hx hn => ⟨1, by simpa, by simpa⟩⟩

lemma EssentialIn.trans {A B C : Submodule R E}
    (h : EssentialIn A B) (h' : EssentialIn B C) : EssentialIn A C := by
  refine ⟨h.1.trans h'.1, fun x hx hn => ?_⟩
  obtain ⟨r, hr, hrn⟩ := h'.2 x hx hn
  obtain ⟨s, hs, hsn⟩ := h.2 (r • x) hr hrn
  exact ⟨s * r, by simpa [mul_smul] using hs, by simpa [mul_smul] using hsn⟩

lemma essential_iff_scalar (ι : M →ₗ[R] E) :
    IsEssential ι ↔ ∀ x : E, x ≠ 0 → ∃ r : R,
      r • x ∈ LinearMap.range ι ∧ r • x ≠ 0 := by
  constructor
  · intro h x hn
    have hs : Submodule.span R {x} ≠ ⊥ := by
      intro hs
      have := Submodule.mem_span_singleton_self (R := R) x
      rw [hs, Submodule.mem_bot] at this
      exact hn this
    have hi := h _ hs
    obtain ⟨y, hy, hyn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hi
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy.1
    exact ⟨r, hy.2, hyn⟩
  · intro h N hn heq
    obtain ⟨x, hx, hxn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
    obtain ⟨r, hr, hrn⟩ := h x hxn
    have hm : r • x ∈ N ⊓ LinearMap.range ι := ⟨N.smul_mem r hx, hr⟩
    rw [heq, Submodule.mem_bot] at hm
    exact hrn hm

lemma exists_maximal_essential (A : Submodule R E) :
    ∃ B : Submodule R E, Maximal (EssentialIn A) B := by
  apply zorn_le₀
  intro c hc hchain
  by_cases hn : c.Nonempty
  · refine ⟨sSup c, ⟨?_, ?_⟩, fun B hB => le_sSup hB⟩
    · obtain ⟨B, hB⟩ := hn
      exact (hc hB).1.trans (le_sSup hB)
    · intro x hx hxn
      obtain ⟨B, hB, hxB⟩ :=
        (Submodule.mem_sSup_of_directed hn hchain.directedOn).mp hx
      exact (hc hB).2 x hxB hxn
  · exact ⟨A, EssentialIn.refl A, fun B hB => (hn ⟨B, hB⟩).elim⟩

lemma exists_maximal_disjoint (B : Submodule R E) :
    ∃ N : Submodule R E, Maximal (fun N => Disjoint B N) N := by
  apply zorn_le₀
  intro c hc hchain
  by_cases hn : c.Nonempty
  · refine ⟨sSup c, Submodule.disjoint_def.mpr ?_, fun N hN => le_sSup hN⟩
    intro x hxB hxc
    obtain ⟨N, hN, hxN⟩ :=
      (Submodule.mem_sSup_of_directed hn hchain.directedOn).mp hxc
    exact Submodule.disjoint_def.mp (hc hN) x hxB hxN
  · exact ⟨⊥, disjoint_bot_right, fun N hN => (hn ⟨N, hN⟩).elim⟩

/-- A maximal essential extension inside an injective module is a retract. -/
lemma maximal_essential_retract [Module.Injective R E] (A B : Submodule R E)
    (hB : Maximal (EssentialIn A) B) :
    ∃ p : E →ₗ[R] B, ∀ x : B, p x = x := by
  obtain ⟨N, hN⟩ := exists_maximal_disjoint B
  let q : B →ₗ[R] E ⧸ N := N.mkQ.comp B.subtype
  have hq : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm _ bot_le
    change ∀ x, q x = 0 → x = 0
    intro x hx
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hN.prop x x.2
      ((Submodule.Quotient.mk_eq_zero N).mp hx)
  obtain ⟨g, hg⟩ := Module.Injective.out q hq B.subtype
  let f : E →ₗ[R] E := g.comp N.mkQ
  have hf (x : B) : f x = x := hg x
  have hNk : N ≤ LinearMap.ker f := by
    intro x hx
    change g (N.mkQ x) = 0
    rw [show N.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero N).mpr hx, map_zero]
  -- Maximal disjointness forces every nonzero cyclic submodule of the image
  -- to meet B. Maximal essentiality then forces the entire image into B.
  have hBrange : EssentialIn B (LinearMap.range f) := by
    refine ⟨fun x hx => ⟨x, hf ⟨x, hx⟩⟩, ?_⟩
    rintro z ⟨y, rfl⟩ hzn
    have hsup : ¬ Disjoint B (N ⊔ Submodule.span R {y}) := by
      intro hd
      have he : N ⊔ Submodule.span R {y} = N :=
        (hN.eq_of_le hd le_sup_left).symm
      have hy : y ∈ N := he ▸
        (show y ∈ N ⊔ Submodule.span R {y} from
          (show Submodule.span R {y} ≤ N ⊔ Submodule.span R {y} from le_sup_right)
            (Submodule.mem_span_singleton_self y))
      exact hzn (show f y = 0 from hNk hy)
    have hne : B ⊓ (N ⊔ Submodule.span R {y}) ≠ ⊥ :=
      fun he => hsup (disjoint_iff.mpr he)
    obtain ⟨b, hb, hbn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨n, hn, v, hv, hbv⟩ := Submodule.mem_sup.mp hb.2
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have he : r • f y = b := by
      calc
        r • f y = f (n + r • y) := by simp [show f n = 0 from hNk hn]
        _ = f b := congrArg f hbv
        _ = b := hf ⟨b, hb.1⟩
    exact ⟨r, he ▸ hb.1, he ▸ hbn⟩
  have hrange : LinearMap.range f ≤ B :=
    hB.2 (hB.prop.trans hBrange) hBrange.1
  refine ⟨f.codRestrict B (fun x => hrange ⟨x, rfl⟩), ?_⟩
  intro x
  apply Subtype.ext
  exact hf x

lemma injective_of_retract [Module.Injective R E] (B : Submodule R E)
    (p : E →ₗ[R] B) (hp : ∀ x : B, p x = x) : Module.Injective R B where
  out X Y _ _ _ _ i hi g := by
    obtain ⟨l, hl⟩ := Module.Injective.out i hi (B.subtype.comp g)
    refine ⟨p.comp l, fun x => ?_⟩
    change p (l (i x)) = g x
    rw [hl x]
    exact hp (g x)

/-- General module theorem, specialized below to the residue field. -/
theorem exists_injectiveEnvelope (R M : Type u) [Ring R] [AddCommGroup M] [Module R M] :
    Nonempty (InjectiveEnvelope R M) := by
  let P := Classical.choice (CategoryTheory.EnoughInjectives.presentation (ModuleCat.of R M))
  let I := P.J
  let ι : M →ₗ[R] I := P.f.hom
  have hι : Function.Injective ι := (ModuleCat.mono_iff_injective P.f).mp P.mono
  have : Module.Injective R I := Module.injective_module_of_injective_object R I (inj := P.injective)
  obtain ⟨B, hB⟩ := exists_maximal_essential (LinearMap.range ι)
  obtain ⟨p, hp⟩ := maximal_essential_retract _ _ hB
  let j : M →ₗ[R] B := ι.codRestrict B (fun x => hB.prop.1 ⟨x, rfl⟩)
  refine ⟨⟨B, j, ⟨?_, injective_of_retract B p hp, ?_⟩⟩⟩
  · intro x y h
    exact hι (congrArg Subtype.val h)
  · apply (essential_iff_scalar j).mpr
    intro x hxn
    obtain ⟨r, hr, hrn⟩ := hB.prop.2 x x.2 (fun he => hxn (Subtype.ext he))
    obtain ⟨m, hm⟩ := hr
    refine ⟨r, ⟨m, Subtype.ext hm⟩, ?_⟩
    exact fun he => hrn (congrArg Subtype.val he)

/-- Essentiality detects injectivity of a map on the whole envelope. -/
lemma injective_of_essential (ι : M →ₗ[R] E) (hι : IsEssential ι)
    (f : E →ₗ[R] F) (hf : Function.Injective (f.comp ι)) : Function.Injective f := by
  have hmeet : LinearMap.ker f ⊓ LinearMap.range ι = ⊥ := by
    apply le_antisymm _ bot_le
    rintro x ⟨hx, m, rfl⟩
    have hm : m = 0 := hf (by simpa using hx)
    simp [hm]
  apply LinearMap.ker_eq_bot.mp
  by_contra hn
  exact hι _ hn hmeet

/-- The extending isomorphism need not be unique. -/
theorem injectiveEnvelope_equiv (ι : M →ₗ[R] E) (κ : M →ₗ[R] F)
    (hι : IsInjectiveEnvelope ι) (hκ : IsInjectiveEnvelope κ) :
    ∃ e : E ≃ₗ[R] F, e.toLinearMap.comp ι = κ := by
  have := hι.injectiveModule
  have := hκ.injectiveModule
  obtain ⟨f, hf⟩ := Module.Injective.out ι hι.injective κ
  have hcomp : f.comp ι = κ := LinearMap.ext hf
  have hfi : Function.Injective f :=
    injective_of_essential ι hι.essential f (hcomp ▸ hκ.injective)
  obtain ⟨r, hr⟩ := Module.Injective.out f hfi (LinearMap.id : E →ₗ[R] E)
  have hrcomp : r.comp κ = ι := by
    ext m
    rw [LinearMap.comp_apply, ← hf m, hr]
    rfl
  have hri : Function.Injective r :=
    injective_of_essential κ hκ.essential r (hrcomp ▸ hι.injective)
  have hfs : Function.Surjective f := by
    intro y
    refine ⟨r y, hri ?_⟩
    exact hr (r y)
  exact ⟨LinearEquiv.ofBijective f ⟨hfi, hfs⟩, hcomp⟩

/-- Every nonzero commutative Artinian local ring has an injective envelope of its residue field. -/
theorem residueField_injectiveEnvelope_exists : InjectiveEnvelopeSpec.existence.{u} := by
  intro R _ _ _ _
  exact exists_injectiveEnvelope R (IsLocalRing.ResidueField R)

/-- Any two displayed envelopes of the residue field are compatibly isomorphic. -/
theorem residueField_injectiveEnvelope_unique : InjectiveEnvelopeSpec.uniqueness.{u} := by
  intro R _ _ _ _ E F _ _ _ _ ι κ hι hκ
  exact injectiveEnvelope_equiv ι κ hι hκ

end AdvCommAlg.Gorenstein
