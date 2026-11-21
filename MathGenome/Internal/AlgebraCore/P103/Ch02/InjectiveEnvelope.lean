import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.InjectiveEnvelope
import MathGenome.Internal.AlgebraCore.P103.Ch02.EnoughInjectives
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Zorn
import Mathlib.LinearAlgebra.Span.Basic

noncomputable section

namespace P103.Ch02.InjectiveEnvelope
open P103.Specs.Ch02.InjectiveEnvelope
universe u v w z

section EssentialLemmas
variable {R : Type u} [Ring R]
variable {M : Type v} {E : Type w} {F : Type z}
variable [AddCommGroup M] [AddCommGroup E] [AddCommGroup F]
variable [Module R M] [Module R E] [Module R F]

theorem essential_iff_disjoint (S : Submodule R E) :
    Essential S ↔ ∀ U : Submodule R E, Disjoint U S → U = ⊥ := by
  simp only [Essential, disjoint_iff]
  constructor
  · intro h U hU
    by_contra hn
    exact h U hn hU
  · intro h U hU hUS
    exact hU (h U hUS)

theorem essential_iff_smul (S : Submodule R E) :
    Essential S ↔ ∀ x : E, x ≠ 0 → ∃ r : R, r • x ≠ 0 ∧ r • x ∈ S := by
  constructor
  · intro h x hx
    have hspan : Submodule.span R {x} ≠ ⊥ := by
      intro heq
      have := Submodule.mem_span_singleton_self (R := R) x
      rw [heq] at this
      exact hx this
    have hne := h _ hspan
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy.1
    exact ⟨r, hy0, hy.2⟩
  · intro h U hU
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    obtain ⟨r, hr0, hr⟩ := h x hx0
    intro heq
    have hm : r • x ∈ U ⊓ S := ⟨U.smul_mem r hx, hr⟩
    rw [heq] at hm
    exact hr0 hm

theorem essential_mono {S T : Submodule R E} (h : Essential S) (hst : S ≤ T) :
    Essential T := by
  rw [essential_iff_smul] at h ⊢
  intro x hx
  obtain ⟨r, hr, hs⟩ := h x hx
  exact ⟨r, hr, hst hs⟩

theorem essential_comp {i : M →ₗ[R] E} {j : E →ₗ[R] F}
    (hi : EssentialExtension i) (hj : EssentialExtension j) :
    EssentialExtension (j.comp i) := by
  refine ⟨hj.1.comp hi.1, (essential_iff_smul _).mpr ?_⟩
  intro x hx
  obtain ⟨r, hr0, y, hy⟩ := (essential_iff_smul _).mp hj.2 x hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy; exact hr0 hy.symm
  obtain ⟨s, hs0, m, hm⟩ := (essential_iff_smul _).mp hi.2 y hy0
  refine ⟨s * r, ?_, m, ?_⟩
  · rw [mul_smul, ← hy, ← map_smul]
    exact fun h => hs0 (hj.1 (h.trans (map_zero j).symm))
  · change j (i m) = _
    rw [hm, map_smul, hy, mul_smul]

theorem injective_of_essential {i : M →ₗ[R] E} (hi : EssentialExtension i)
    (f : E →ₗ[R] F) (hf : Function.Injective (f.comp i)) : Function.Injective f := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro x hx
  by_contra hx0
  obtain ⟨r, hr0, m, hm⟩ := (essential_iff_smul _).mp hi.2 x hx0
  have hfm : (f.comp i) m = (f.comp i) 0 := by
    change f (i m) = _
    rw [hm, map_smul]
    simpa using congrArg (r • ·) hx
  have hm0 : m = 0 := hf hfm
  exact hr0 (by simpa [hm0] using hm.symm)

theorem surjective_of_essential_retraction {j : E →ₗ[R] F}
    (hj : EssentialExtension j) (r : F →ₗ[R] E)
    (hr : r.comp j = LinearMap.id) : Function.Surjective j := by
  have hrinj : Function.Injective r :=
    injective_of_essential hj r (by rw [hr]; exact Function.injective_id)
  intro x
  refine ⟨r x, hrinj ?_⟩
  exact LinearMap.congr_fun hr (r x)

end EssentialLemmas

section MaximalDisjoint
variable {R : Type u} [Ring R] {I : Type w} [AddCommGroup I] [Module R I]

/-- The union of a chain of submodules disjoint from `S` is still disjoint. -/
theorem exists_maximal_disjoint (S : Submodule R I) :
    ∃ K : Submodule R I, Maximal (fun K => Disjoint K S) K := by
  apply zorn_le₀ {K | Disjoint K S}
  intro c hc hchain
  by_cases hn : c.Nonempty
  · refine ⟨sSup c, ?_, fun K hK => le_sSup hK⟩
    apply Submodule.disjoint_def.mpr
    intro x hx hS
    obtain ⟨K, hK, hxK⟩ :=
      (Submodule.mem_sSup_of_directed hn hchain.directedOn).mp hx
    exact Submodule.disjoint_def.mp (hc hK) x hxK hS
  · refine ⟨⊥, disjoint_bot_left, ?_⟩
    intro K hK
    exact (hn ⟨K, hK⟩).elim

/-- Factoring out a maximal disjoint submodule makes the image essential. -/
theorem essential_quotient_of_maximal_disjoint (S K : Submodule R I)
    (hK : Maximal (fun K => Disjoint K S) K) :
    Essential (S.map K.mkQ) := by
  apply (essential_iff_disjoint _).mpr
  intro U hU
  let V : Submodule R I := U.comap K.mkQ
  have hVS : Disjoint V S := by
    apply Submodule.disjoint_def.mpr
    intro x hx hS
    have hqx : K.mkQ x = 0 := Submodule.disjoint_def.mp hU (K.mkQ x) hx
      ⟨x, hS, rfl⟩
    have hxK : x ∈ K := (Submodule.Quotient.mk_eq_zero K).mp hqx
    exact Submodule.disjoint_def.mp hK.1 x hxK hS
  have hKV : K ≤ V := by
    intro x hx
    change K.mkQ x ∈ U
    have hx0 : K.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hx
    rw [hx0]
    exact U.zero_mem
  have hVK : V ≤ K := hK.2 hVS hKV
  apply le_antisymm _ bot_le
  intro y hy
  obtain ⟨x, rfl⟩ := K.mkQ_surjective y
  exact (Submodule.Quotient.mk_eq_zero K).mpr (hVK hy)

end MaximalDisjoint

section Injectivity
variable {R : Type u} [Ring R]

/-- A retract of an injective module is injective, including the zero retract. -/
theorem injective_retract {E I : Type w} [AddCommGroup E] [AddCommGroup I]
    [Module R E] [Module R I] (hI : Module.Injective R I)
    (e : E →ₗ[R] I) (r : I →ₗ[R] E) (hr : r.comp e = LinearMap.id) :
    Module.Injective R E := by
  constructor
  intro X Y _ _ _ _ j hj f
  obtain ⟨g, hg⟩ := hI.out j hj (e.comp f)
  refine ⟨r.comp g, ?_⟩
  intro x
  change r (g (j x)) = f x
  rw [hg]
  exact LinearMap.congr_fun hr (f x)

/-- A module with no proper essential extension is injective. The quotient
by a maximal disjoint submodule supplies an essential extension in which the
original module must exhaust the quotient. -/
theorem injective_of_no_proper_essential
    {E : Type (max u w)} [AddCommGroup E] [Module R E]
    (h : ∀ (F : Type (max u w)) [AddCommGroup F] [Module R F]
      (j : E →ₗ[R] F), EssentialExtension j → Function.Surjective j) :
    Module.Injective R E := by
  obtain ⟨I, hIa, hIm, e, he, hI⟩ := P103.Ch02.EnoughInjectives.leftEmbedding R E
  let _ := hIa
  let _ := hIm
  obtain ⟨K, hK⟩ := exists_maximal_disjoint (LinearMap.range e)
  let j : E →ₗ[R] (I ⧸ K) := K.mkQ.comp e
  have hj : Function.Injective j := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro x hx
    have hxK : e x ∈ K := (Submodule.Quotient.mk_eq_zero K).mp hx
    have hex : e x = 0 := Submodule.disjoint_def.mp hK.1 (e x) hxK ⟨x, rfl⟩
    exact he (hex.trans (map_zero e).symm)
  have hess : EssentialExtension j := by
    refine ⟨hj, ?_⟩
    have hm := essential_quotient_of_maximal_disjoint (LinearMap.range e) K hK
    simpa only [j, LinearMap.range_comp] using hm
  let a : E ≃ₗ[R] (I ⧸ K) := LinearEquiv.ofBijective j ⟨hj, h _ j hess⟩
  let r : I →ₗ[R] E := a.symm.toLinearMap.comp K.mkQ
  apply injective_retract hI e r
  ext x
  exact a.symm_apply_apply x

end Injectivity

/-- Relative essentiality for two submodules of one fixed ambient module.
The scalar criterion keeps the Zorn argument entirely inside a set. -/
def RelativeEssential {R : Type u} [Ring R] {I : Type w}
    [AddCommGroup I] [Module R I] (S T : Submodule R I) : Prop :=
  S ≤ T ∧ ∀ x ∈ T, x ≠ 0 → ∃ r : R, r • x ≠ 0 ∧ r • x ∈ S

section MaximalEssentialSubmodule
variable {R : Type u} [Ring R] {I : Type w} [AddCommGroup I] [Module R I]

theorem relativeEssential_self (S : Submodule R I) : RelativeEssential S S := by
  refine ⟨le_rfl, ?_⟩
  intro x hx hx0
  exact ⟨1, by simpa, by simpa⟩

theorem exists_maximal_relativeEssential (S : Submodule R I) :
    ∃ T : Submodule R I, Maximal (RelativeEssential S) T := by
  apply zorn_le₀ {T | RelativeEssential S T}
  intro c hc hchain
  by_cases hn : c.Nonempty
  · refine ⟨sSup c, ⟨?_, ?_⟩, fun T hT => le_sSup hT⟩
    · obtain ⟨T, hT⟩ := hn
      exact (hc hT).1.trans (le_sSup hT)
    · intro x hx hx0
      obtain ⟨T, hT, hxT⟩ :=
        (Submodule.mem_sSup_of_directed hn hchain.directedOn).mp hx
      exact (hc hT).2 x hxT hx0
  · refine ⟨S, relativeEssential_self S, ?_⟩
    intro T hT
    exact (hn ⟨T, hT⟩).elim

/-- A maximal essential extension in an injective ambient module admits no
proper essential extension, even one outside that ambient module. -/
theorem maximal_relativeEssential_injective
    {I : Type (max u w)} [AddCommGroup I] [Module R I]
    (hI : Module.Injective R I) (S T : Submodule R I)
    (hT : Maximal (RelativeEssential S) T) : Module.Injective R T := by
  apply injective_of_no_proper_essential
  intro F _ _ j hj
  obtain ⟨f, hf⟩ := hI.out j hj.1 T.subtype
  have hfj : f.comp j = T.subtype := LinearMap.ext hf
  have hfinj : Function.Injective f := injective_of_essential hj f
    (by rw [hfj]; exact Subtype.val_injective)
  have hTrange : T ≤ LinearMap.range f := by
    intro x hx
    exact ⟨j ⟨x, hx⟩, hf ⟨x, hx⟩⟩
  have hrel : RelativeEssential S (LinearMap.range f) := by
    refine ⟨hT.1.1.trans hTrange, ?_⟩
    rintro x ⟨y, rfl⟩ hx0
    have hy0 : y ≠ 0 := by intro hy; simp [hy] at hx0
    obtain ⟨r, hr0, t, ht⟩ := (essential_iff_smul _).mp hj.2 y hy0
    have ht0 : (t : I) ≠ 0 := by
      intro h0
      have tz : t = 0 := Subtype.ext h0
      simp [tz] at ht
      exact hr0 ht.symm
    obtain ⟨s, hs0, hsS⟩ := hT.1.2 t t.property ht0
    have hft : f (j t) = (t : I) := hf t
    have hrt : r • f y = (t : I) := by
      rw [← map_smul, ← ht, hft]
    refine ⟨s * r, ?_, ?_⟩
    · simpa only [mul_smul, hrt] using hs0
    · simpa only [mul_smul, hrt] using hsS
  have hle : LinearMap.range f ≤ T := hT.2 hrel hTrange
  intro y
  let t : T := ⟨f y, hle ⟨y, rfl⟩⟩
  refine ⟨t, hfinj ?_⟩
  exact hf t

end MaximalEssentialSubmodule

/-- Every module, with no nonzero or commutativity hypothesis, has an envelope. -/
theorem existsEnvelope : existsEnvelopeType.{u, v} := by
  intro R M _ _ _
  obtain ⟨I, hIa, hIm, e, he, hI⟩ := P103.Ch02.EnoughInjectives.leftEmbedding R M
  let _ := hIa
  let _ := hIm
  obtain ⟨T, hT⟩ := exists_maximal_relativeEssential (LinearMap.range e)
  let i : M →ₗ[R] T := e.codRestrict T (fun m => hT.1.1 ⟨m, rfl⟩)
  refine ⟨T, inferInstance, inferInstance, i,
    maximal_relativeEssential_injective hI _ _ hT, ?_, ?_⟩
  · intro x y hxy
    exact he (congrArg Subtype.val hxy)
  · apply (essential_iff_smul _).mpr
    intro t ht
    have ht0 : (t : I) ≠ 0 := fun h => ht (Subtype.ext h)
    obtain ⟨r, hr0, m, hm⟩ := hT.1.2 t t.property ht0
    refine ⟨r, ?_, m, ?_⟩
    · intro h
      exact hr0 (congrArg Subtype.val h)
    · exact Subtype.ext hm

/-- There is no proper further essential extension, with no restriction on
its universe relative to the universe of the envelope. -/
theorem noProperExtension : noProperExtensionType.{u, v, w, z} := by
  intro R M E F _ _ _ _ _ _ _ i j hi hj hji
  have hjess : EssentialExtension j :=
    ⟨hj, essential_mono hji.2 (LinearMap.range_comp_le_range i j)⟩
  let : Module.Injective R E := hi.1
  obtain ⟨r, hr⟩ := Module.Injective.extension_property R E E F j hj LinearMap.id
  exact surjective_of_essential_retraction hjess r hr

/-- An injective essential extension is a maximal essential extension. -/
theorem envelope_iff_maximal : envelope_iff_maximalType.{u, v, w} := by
  intro R M E _ _ _ _ _ i
  constructor
  · intro hi
    refine ⟨hi.2, ?_⟩
    intro F _ _ j hj hji
    exact noProperExtension R M E F i j hi hj hji
  · intro hi
    refine ⟨?_, hi.1⟩
    apply injective_of_no_proper_essential
    intro F _ _ j hj
    exact hi.2 F j hj.1 (essential_comp hi.1 hj)

/-- The minimal injective extensions are exactly the injective essential ones. -/
theorem envelope_iff_minimal : envelope_iff_minimalType.{u, v, w} := by
  intro R M E _ _ _ _ _ i
  constructor
  · intro hi
    refine ⟨hi.2.1, hi.1, ?_⟩
    intro S hS hSinj
    have hsub : EssentialExtension S.subtype := by
      refine ⟨Subtype.val_injective, ?_⟩
      have hess : Essential S := essential_mono hi.2.2 hS
      simpa only [Submodule.range_subtype] using hess
    obtain ⟨r, hr⟩ := hSinj.out S.subtype Subtype.val_injective
      (LinearMap.id : S →ₗ[R] S)
    have hsurj := surjective_of_essential_retraction hsub r (LinearMap.ext hr)
    apply Submodule.eq_top_iff'.mpr
    intro x
    obtain ⟨s, hs⟩ := hsurj x
    exact hs ▸ s.property
  · intro hi
    refine ⟨hi.2.1, hi.1, ?_⟩
    obtain ⟨T, hT⟩ := exists_maximal_relativeEssential (LinearMap.range i)
    have hTinj := maximal_relativeEssential_injective hi.2.1 _ _ hT
    have htop : T = ⊤ := hi.2.2 T hT.1.1 hTinj
    apply (essential_iff_smul _).mpr
    intro x hx
    exact hT.1.2 x (htop.symm ▸ Submodule.mem_top) hx

/-- The isomorphism fixes the original module; no uniqueness of the
isomorphism itself is asserted. -/
theorem unique : uniqueType.{u, v, w, z} := by
  intro R M E F _ _ _ _ _ _ _ i j hi hj
  let : Module.Injective R F := hj.1
  obtain ⟨f, hf⟩ := Module.Injective.extension_property R F M E i hi.2.1 j
  have hfinj : Function.Injective f := injective_of_essential hi.2 f
    (by rw [hf]; exact hj.2.1)
  have hfess : EssentialExtension f :=
    ⟨hfinj, essential_mono hj.2.2 (by
      rw [← hf]
      exact LinearMap.range_comp_le_range i f)⟩
  let : Module.Injective R E := hi.1
  obtain ⟨r, hr⟩ := Module.Injective.extension_property R E E F f hfinj LinearMap.id
  have hfsurj := surjective_of_essential_retraction hfess r hr
  exact ⟨LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩, hf⟩

theorem rightExistsEnvelope : rightExistsEnvelopeType.{u, v} := by
  intro R M _ _ _
  exact existsEnvelope Rᵐᵒᵖ M

end P103.Ch02.InjectiveEnvelope
