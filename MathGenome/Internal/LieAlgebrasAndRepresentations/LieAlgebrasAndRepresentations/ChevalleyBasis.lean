import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ChevalleyBasis
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootStrings
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Lie.Basis.Base
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

noncomputable section

universe u

namespace LieAlgebrasAndRepresentations

open Specs.LieAlgebrasAndRepresentations.ChevalleyBasis
open LieModule
open scoped BigOperators

open private maximalToral_isCartan rootSpace_eq_generalized rootWeight rootWeight_toLinear
  rootWeight_nonzero coroot_rootWeight from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L}

private theorem coroot_ne_zero (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {α : Module.Dual ℂ H} (ha : α ∈ rootSet H) : (killingCoroot H α : L) ≠ 0 := by
  obtain ⟨e, _, _, _, he, _, _, h, _⟩ := exists_root_triple hss H hH α ha
  intro hc
  rw [hc, zero_lie, eq_comm, smul_eq_zero] at h
  exact h.elim (by norm_num) he

private theorem neg_mem_rootSet (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {α : Module.Dual ℂ H} (ha : α ∈ rootSet H) : -α ∈ rootSet H := by
  obtain ⟨_, f, _, hf, _, hf₀, _, _, _⟩ := exists_root_triple hss H hH α ha
  exact ⟨neg_ne_zero.mpr ha.1, fun h => hf₀ ((Submodule.mem_bot ℂ).mp (h ▸ hf))⟩

private theorem coroot_neg (α : Module.Dual ℂ H) :
    killingCoroot H (-α) = -killingCoroot H α := by
  simp [Specs.LieAlgebrasAndRepresentations.RootForm.tAlpha_value]

private theorem rootVector_spans (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {α : Module.Dual ℂ H} (ha : α ∈ rootSet H) {x y : L}
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H α) (hx₀ : x ≠ 0) :
    ∃ c : ℂ, c • x = y := by
  let x' : rootSpace H α := ⟨x, hx⟩
  have hx' : x' ≠ 0 := fun h => hx₀ (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' x' hx').mp
    (finrank_rootSpace_eq_one hss H hH α ha) ⟨y, hy⟩
  exact ⟨c, congrArg Subtype.val hc⟩

section Cartan

open LieAlgebra.IsKilling
open Set Submodule

variable [H.IsCartanSubalgebra] [LieAlgebra.IsKilling ℂ L]

private theorem rootSystem_mem_iff (hH : IsMaximalToral H) (α : Module.Dual ℂ H) :
    α ∈ range (rootSystem H).root ↔ α ∈ rootSet H := by
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨(rootSystem H).ne_zero i, ?_⟩
    change (weightSpace L (i.val : H → ℂ)).toSubmodule ≠ ⊥
    rw [← rootSpace_eq_generalized H hH]
    exact fun h => LieModule.Weight.genWeightSpace_ne_bot L i.val
      (LieSubmodule.toSubmodule_injective h)
  · intro ha
    exact ⟨⟨rootWeight H hH α ha, by
      simpa using rootWeight_nonzero H hH α ha⟩, rootWeight_toLinear H hH α ha⟩

private theorem rootSystem_coroot_eq (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (i : H.root) :
    (rootSystem H).coroot i = killingCoroot H ((rootSystem H).root i) := by
  have hi := (rootSystem_mem_iff hH _).mp (mem_range_self i)
  have he : rootWeight H hH ((rootSystem H).root i) hi = i.val := by
    ext h
    rfl
  rw [rootSystem_coroot_apply, ← he]
  exact coroot_rootWeight hss H hH _ hi

set_option maxHeartbeats 1000000 in
/-- The regular functional determines the same set of simple roots on the ordinary
root spaces and on Mathlib's root pairing. -/
private theorem exists_base_for_functional (hH : IsMaximalToral H)
    (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) (hφ : ∀ α ∈ rootSet H, φ α ≠ 0) :
    ∃ B : (rootSystem H).Base, ∀ i : H.root,
      i ∈ B.support ↔ (rootSystem H).root i ∈
        Specs.LieAlgebrasAndRepresentations.SerreRelations.simple H φ := by
  classical
  let P := rootSystem H
  let s := IsAddIndecomposable.baseOf P.root φ.toAddMonoidHom
  let _ : P.IsValuedIn ℝ := RootPairing.IsValuedIn.trans P ℝ ℤ
  let _ := P.indexNeg
  have hreg (i : H.root) : φ (P.root i) ≠ 0 :=
    hφ _ ((rootSystem_mem_iff hH _).mp (mem_range_self i))
  have hsp (i : H.root) : P.root i ∈ AddSubmonoid.closure (P.root '' s) ∨
      -P.root i ∈ AddSubmonoid.closure (P.root '' s) :=
    IsAddIndecomposable.mem_or_neg_mem_closure_baseOf P.root φ.toAddMonoidHom i (hreg i)
      (by simp)
  have hli : LinearIndepOn ℝ P.root s := P.linearIndepOn_root_baseOf' φ hreg
  let v (i : s) : P.rootSpan ℝ := ⟨P.root i, subset_span (mem_range_self _)⟩
  let _ : Fintype s := Fintype.ofFinite s
  have hspR : span ℝ (range (fun i : s => P.root i)) = P.rootSpan ℝ := by
    have hrange : range (fun i : s => P.root i) = P.root '' s := by ext a; simp
    rw [hrange]
    apply le_antisymm (span_mono (image_subset_range _ _))
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hc : AddSubmonoid.closure (P.root '' s) ≤ (span ℝ (P.root '' s)).toAddSubmonoid :=
      AddSubmonoid.closure_le.mpr subset_span
    rcases hsp i with h | h
    · exact hc h
    · exact neg_mem_iff.mp (hc h)
  have hv : span ℝ (range v) = ⊤ := by
    apply Submodule.map_injective_of_injective (P.rootSpan ℝ).injective_subtype
    rw [map_span, Submodule.map_top, range_subtype, ← range_comp]
    exact hspR
  have hv' : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp (P.rootSpan ℝ).subtype
    change LinearIndependent ℝ (fun i : s => P.root i)
    exact hli
  let b : Module.Basis s ℝ (P.rootSpan ℝ) := Module.Basis.mk hv' hv.ge
  have hc : Fintype.card s = Module.finrank ℂ (Module.Dual ℂ H) := by
    rw [← P.finrank_rootSpanIn ℝ, Module.finrank_eq_card_basis b]
  have ht : span ℂ (range (fun i : s => P.root i)) = ⊤ := by
    rw [← span_span_of_tower ℝ, hspR, RootPairing.rootSpan, span_span_of_tower,
      RootPairing.IsRootSystem.span_root_eq_top (P := P)]
  have hliC : LinearIndepOn ℂ P.root s := by
    change LinearIndependent ℂ (fun i : s => P.root i)
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ht, finrank_top]
    exact hc
  refine ⟨RootPairing.Base.mk' P s hliC hsp, fun i => ?_⟩
  have hmem (a : Module.Dual ℂ H) : a ∈ range P.root ↔
      a ∈ Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSet_value H :=
    rootSystem_mem_iff hH a
  change i ∈ (Set.toFinite s).toFinset ↔ P.root i ∈ _
  rw [Set.Finite.mem_toFinset]
  simp only [s, IsAddIndecomposable.baseOf, IsAddIndecomposable, Set.mem_ofPred_eq,
    Specs.LieAlgebrasAndRepresentations.SerreRelations.simple,
    Specs.LieAlgebrasAndRepresentations.SerreRelations.positive, LinearMap.toAddMonoidHom_coe]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨⟨(hmem _).mp (mem_range_self i), hi⟩, ?_⟩
    rintro α ⟨hα, hαp⟩ β ⟨hβ, hβp⟩ he
    obtain ⟨j, rfl⟩ := (hmem _).mpr hα
    obtain ⟨k, rfl⟩ := (hmem _).mpr hβ
    exact (h j hαp k hβp he).elim (P.ne_zero j) (P.ne_zero k)
  · rintro ⟨⟨_, hi⟩, h⟩
    exact ⟨hi, fun j hj k hk =>
      fun he => False.elim (h _ ⟨(hmem _).mp (mem_range_self j), hj⟩
        _ ⟨(hmem _).mp (mem_range_self k), hk⟩ he)⟩

omit [LieAlgebra.IsKilling ℂ L] in
/-- A nonzero ideal meets the Cartan. A nonzero vector in a nonzero weight
of the ideal brackets with an opposite-root vector to give a coroot. -/
private theorem ideal_eq_bot_of_disjoint_cartan
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) (I : LieIdeal ℂ L)
    (hI : ∀ x : H, (x : L) ∈ I → (x : L) = 0) : I = ⊥ := by
  let J : LieSubmodule ℂ H L := I.restr H
  have hj : J = ⊥ := by
    rw [LieModule.eq_iSup_inf_genWeightSpace ℂ H L J]
    apply iSup_eq_bot.mpr
    intro χ
    apply le_antisymm _ bot_le
    intro x hx
    have hxI : x ∈ I := hx.1
    have hxχ : x ∈ rootSpace H (χ : Module.Dual ℂ H) := by
      change x ∈ (weightSpace L (χ : H → ℂ)).toSubmodule
      rw [← rootSpace_eq_generalized H hH]
      exact hx.2
    rw [LieSubmodule.mem_bot]
    by_contra hx₀
    by_cases hχ : (χ : Module.Dual ℂ H) = 0
    · rw [hχ, rootSpace_zero hss H hH] at hxχ
      exact hx₀ (hI ⟨x, hxχ⟩ hxI)
    have hroot : (χ : Module.Dual ℂ H) ∈ rootSet H :=
      ⟨hχ, fun he => hx₀ ((Submodule.mem_bot ℂ).mp (he ▸ hxχ))⟩
    obtain ⟨e, f, he, _, _, _, hef, _, _⟩ := exists_root_triple hss H hH _ hroot
    obtain ⟨c, hc⟩ := rootVector_spans hss hH hroot hxχ he hx₀
    have heI : e ∈ I := hc ▸ I.smul_mem c hxI
    have hcorootI : (killingCoroot H (χ : Module.Dual ℂ H) : L) ∈ I :=
      hef ▸ (by rw [← lie_skew e f]; exact I.neg_mem (I.lie_mem heI))
    exact coroot_ne_zero hss hH hroot (hI _ hcorootI)
  apply le_antisymm _ bot_le
  intro x hx
  have : x ∈ J := hx
  simpa [hj] using this

omit [LieAlgebra.IsKilling ℂ L] in
set_option maxHeartbeats 1000000 in
/-- The paired generators with the same Cartan matrix form the graph of
the sign involution. The second projection of the first kernel is an ideal
whose intersection with the Cartan is zero. -/
private theorem exists_sign_involution (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {ι : Type u} [Fintype ι] (b : LieAlgebra.Basis ι H) :
    ∃ σ : L ≃ₗ⁅ℂ⁆ L, Function.Involutive σ ∧
      (∀ h : H, σ (h : L) = -(h : L)) := by
  classical
  let E : ι → L × L := fun i => (b.e i, -b.f i)
  let F : ι → L × L := fun i => (b.f i, -b.e i)
  let G := LieSubalgebra.lieSpan ℂ (L × L) (range E ∪ range F)
  let e (i : ι) : G := ⟨E i, LieSubalgebra.subset_lieSpan (Or.inl (mem_range_self i))⟩
  let f (i : ι) : G := ⟨F i, LieSubalgebra.subset_lieSpan (Or.inr (mem_range_self i))⟩
  let h (i : ι) : G := ⁅e i, f i⁆
  let K := LieSubalgebra.lieSpan ℂ G (range h)
  let p₁ : G →ₗ⁅ℂ⁆ L := (LieHom.fst ℂ L L).comp G.incl
  let p₂ : G →ₗ⁅ℂ⁆ L := (LieHom.snd ℂ L L).comp G.incl
  have he₁ (i : ι) : p₁ (e i) = b.e i := rfl
  have he₂ (i : ι) : p₂ (e i) = -b.f i := rfl
  have hf₁ (i : ι) : p₁ (f i) = b.f i := rfl
  have hf₂ (i : ι) : p₂ (f i) = -b.e i := rfl
  have hh₁ (i : ι) : p₁ (h i) = b.h i := (b.sl2 i).lie_e_f
  have hh₂ (i : ι) : p₂ (h i) = -b.h i := by
    change ⁅-b.f i, -b.e i⁆ = _
    rw [neg_lie, lie_neg, neg_neg, ← lie_skew (b.f i) (b.e i), (b.sl2 i).lie_e_f]
  have extG {x y : G} (h₁ : p₁ x = p₁ y) (h₂ : p₂ x = p₂ y) : x = y :=
    Subtype.ext (Prod.ext h₁ h₂)
  have hspan : LieSubalgebra.lieSpan ℂ G (range e ∪ range f) = ⊤ := by
    let S := LieSubalgebra.lieSpan ℂ G (range e ∪ range f)
    have hle : G ≤ S.map G.incl := by
      change LieSubalgebra.lieSpan ℂ (L × L) (range E ∪ range F) ≤ _
      rw [LieSubalgebra.lieSpan_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨e i, LieSubalgebra.subset_lieSpan (Or.inl (mem_range_self i)), rfl⟩
      · exact ⟨f i, LieSubalgebra.subset_lieSpan (Or.inr (mem_range_self i)), rfl⟩
    apply top_unique
    intro x _
    obtain ⟨y, hy, heq⟩ := hle x.property
    exact (Subtype.ext heq : y = x) ▸ hy
  let B : LieAlgebra.Basis ι K :=
    { A := b.A
      h := h
      e := e
      f := f
      cartan_eq_lieSpan := rfl
      span_ef := hspan
      linInd := LinearIndependent.of_comp p₁.toLinearMap (by simpa [Function.comp_def, hh₁]
        using b.linInd)
      nondegen := b.nondegen
      sl2 := fun i => {
        h_ne_zero := fun hz => (b.sl2 i).h_ne_zero <| by
          simpa [hh₁] using congrArg p₁ hz
        lie_e_f := rfl
        lie_h_e_nsmul := extG
          (by simpa [he₁, hh₁] using (b.sl2 i).lie_h_e_nsmul)
          (by simp [he₂, hh₂, (b.sl2 i).lie_h_f_nsmul])
        lie_h_f_nsmul := extG
          (by simpa [hf₁, hh₁] using (b.sl2 i).lie_h_f_nsmul)
          (by simp [hf₂, hh₂, (b.sl2 i).lie_h_e_nsmul]) }
      lie_h_h := fun i j => extG (by simp [hh₁, b.lie_h_h]) (by simp [hh₂, b.lie_h_h])
      lie_h_e := fun i j => extG
        (by simpa [he₁, hh₁] using b.lie_h_e i j)
        (by simp [he₂, hh₂, b.lie_h_f])
      lie_h_f := fun i j => extG
        (by simpa [hf₁, hh₁] using b.lie_h_f i j)
        (by simp [hf₂, hh₂, b.lie_h_e])
      lie_e_f_ne := fun i j hij => extG
        (by simp [he₁, hf₁, b.lie_e_f_ne i j hij])
        (by simp [he₂, hf₂, ← lie_skew (b.f i) (b.e j), b.lie_e_f_ne j i hij.symm]) }
  let : K.IsCartanSubalgebra := B.isCartanSubalgebra
  have hp₁ : Function.Surjective p₁ := by
    rw [← LieHom.range_eq_top]
    apply top_unique
    rw [← b.span_ef, LieSubalgebra.lieSpan_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨e i, he₁ i⟩
    · exact ⟨f i, hf₁ i⟩
  have hp₂ : Function.Surjective p₂ := by
    rw [← LieHom.range_eq_top]
    apply top_unique
    rw [← b.span_ef, LieSubalgebra.lieSpan_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨-f i, by simp [hf₂]⟩
    · exact ⟨-e i, by simp [he₂]⟩
  have hK (x : G) (hx : x ∈ K) : p₂ x = -p₁ x := by
    have hx' : x ∈ Submodule.span ℂ (Set.range B.h) := by
      rw [← B.coe_cartan_eq_span]
      exact hx
    refine Submodule.span_induction (p := fun y _ => p₂ y = -p₁ y) ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨i, rfl⟩
      change p₂ (h i) = -p₁ (h i)
      rw [hh₁, hh₂]
    · simp
    · intro x y _ _ hx hy
      simp only [map_add, hx, hy, neg_add_rev]; exact add_comm _ _
    · intro c x _ hx
      simp [hx]
  have hK₁ (x : G) (hx : x ∈ K) : p₁ x ∈ H := by
    rw [← LieSubalgebra.mem_toSubmodule, b.coe_cartan_eq_span]
    have hx' : x ∈ Submodule.span ℂ (Set.range B.h) := by
      rw [← B.coe_cartan_eq_span]
      exact hx
    refine Submodule.span_induction (p := fun y _ => p₁ y ∈ span ℂ (range b.h))
      ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨i, rfl⟩
      change p₁ (h i) ∈ _
      rw [hh₁]
      exact subset_span (mem_range_self i)
    · simp
    · intro _ _ _ _ hx hy
      simpa using add_mem hx hy
    · intro c _ _ hx
      simpa using Submodule.smul_mem _ c hx
  let I := p₁.ker.map p₂
  have hI : I = ⊥ := by
    apply ideal_eq_bot_of_disjoint_cartan hss hH
    intro x hx
    change (x : L) ∈ (I : Set L) at hx
    rw [show (I : Set L) = p₂ '' p₁.ker from congrArg SetLike.coe (p₁.ker.coe_map_of_surjective hp₂)] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hy₁ : p₁ y = 0 := hy
    have hyK : y ∈ K := by
      rw [← LieSubalgebra.mem_toLieSubmodule, ← LieAlgebra.rootSpace_zero_eq,
        LieModule.mem_genWeightSpace]
      intro z
      refine ⟨1, ?_⟩
      simp only [pow_one, LieModule.toEnd_apply_apply, Pi.zero_apply, zero_smul, sub_zero]
      apply Subtype.ext
      apply Prod.ext
      · change ⁅p₁ (z : G), p₁ y⁆ = 0
        simp [hy₁]
      · change ⁅p₂ (z : G), p₂ y⁆ = 0
        rw [hxy]
        rw [hK _ z.property, neg_lie]
        have : IsLieAbelian H := hH.1.1
        let z' : H := ⟨p₁ (z : G), hK₁ _ z.property⟩
        change -⁅(z' : L), (x : L)⁆ = 0
        rw [← LieSubalgebra.coe_bracket, trivial_lie_zero, Submodule.coe_zero, neg_zero]
    rw [← hxy, hK y hyK, hy₁, neg_zero]
  have hinj : Function.Injective p₁ := by
    rw [← p₁.ker_eq_bot, eq_bot_iff]
    intro y hy
    have hx : p₂ y ∈ I := LieIdeal.mem_map (f := p₂) hy
    rw [hI, LieSubmodule.mem_bot] at hx
    have hf : p₁ y = 0 := hy
    exact Subtype.ext (Prod.ext hf hx)
  let τ := p₂.comp (LieEquiv.ofBijective p₁ ⟨hinj, hp₁⟩).symm.toLieHom
  have hτ (x : G) : τ (p₁ x) = p₂ x := by
    change p₂ ((LieEquiv.ofBijective p₁ ⟨hinj, hp₁⟩).symm
      ((LieEquiv.ofBijective p₁ ⟨hinj, hp₁⟩) x)) = _
    rw [LieEquiv.symm_apply_apply]
  have he (i : ι) : τ (b.e i) = -b.f i :=
    by simpa [he₁, he₂] using hτ (e i)
  have hf (i : ι) : τ (b.f i) = -b.e i :=
    by simpa [hf₁, hf₂] using hτ (f i)
  have hh (i : ι) : τ (b.h i) = -b.h i :=
    by simpa [hh₁, hh₂] using hτ (h i)
  have hinv : Function.Involutive τ := by
    intro x
    have hx : x ∈ LieSubalgebra.lieSpan ℂ L (range b.e ∪ range b.f) := by
      simp [b.span_ef]
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem y hy =>
      rcases hy with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · simp [he, hf]
      · simp [he, hf]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
    | lie x y _ _ hx hy => simp [hx, hy]
  refine ⟨LieEquiv.ofBijective τ ⟨hinv.injective, hinv.surjective⟩, hinv, ?_⟩
  intro x
  change τ (x : L) = -(x : L)
  have hx : (x : L) ∈ span ℂ (range b.h) := by rw [← b.coe_cartan_eq_span]; exact x.property
  refine Submodule.span_induction (p := fun y _ => τ y = -y) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    exact hh i
  · simp
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy, neg_add_rev]; exact add_comm _ _
  · intro c x _ hx
    simp [hx]

end Cartan

omit [FiniteDimensional ℂ L] in
private theorem involution_mem_opposite (σ : L ≃ₗ⁅ℂ⁆ L)
    (hσ : ∀ h : H, σ (h : L) = -(h : L))
    {α : Module.Dual ℂ H} {x : L} (hx : x ∈ rootSpace H α) :
    σ x ∈ rootSpace H (-α) := by
  rw [mem_rootSpace] at hx ⊢
  intro h
  have he := congrArg σ (hx h)
  rw [LieEquiv.map_lie, hσ, neg_lie, map_smul] at he
  simpa only [LinearMap.neg_apply, neg_smul, neg_neg] using congrArg Neg.neg he

/-- Normalize each pair using a square root, and use the same involution for
the partners of all positive roots. -/
private theorem exists_normalized_root_vectors
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) (hφ : ∀ α ∈ rootSet H, φ α ≠ 0)
    (σ : L ≃ₗ⁅ℂ⁆ L) (hσ₂ : Function.Involutive σ)
    (hσ : ∀ h : H, σ (h : L) = -(h : L)) :
    let opp := fun α : Root H => (⟨-α.val, neg_mem_rootSet hss hH α.property⟩ : Root H)
    ∃ x : Root H → L,
      (∀ α, x α ∈ rootSpace H α.val ∧ x α ≠ 0) ∧
      (∀ α, ⁅x α, x (opp α)⁆ = (killingCoroot H α.val : L)) ∧
      ∀ α, σ (x α) = -x (opp α) := by
  classical
  intro opp
  have hopp : Function.Involutive opp := fun a => Subtype.ext (neg_neg a.val)
  have hn (a : Root H) : φ (opp a).val = -φ a.val := map_neg φ a.val
  have hex (a : Root H) : ∃ y : L, y ∈ rootSpace H a.val ∧ y ≠ 0 ∧
      ⁅y, -σ y⁆ = (killingCoroot H a.val : L) := by
    obtain ⟨e, f, he, hf, he₀, hf₀, hef, _, _⟩ :=
      exists_root_triple hss H hH a.val a.property
    have hσe : -σ e ∈ rootSpace H (-a.val) :=
      Submodule.neg_mem _ (involution_mem_opposite σ hσ he)
    obtain ⟨c, hc⟩ := rootVector_spans hss hH (opp a).property hf hσe hf₀
    have heσ₀ : -σ e ≠ 0 := neg_ne_zero.mpr <| by simpa using he₀
    have hc₀ : c ≠ 0 := fun h => heσ₀ (by simp [← hc, h])
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (n := 2) (by decide)
    have hd₀ : d ≠ 0 := by
      intro hz
      exact hc₀ (by simpa [hz, eq_comm] using hd)
    refine ⟨d • e, Submodule.smul_mem _ _ he, smul_ne_zero hd₀ he₀, ?_⟩
    rw [map_smul, ← smul_neg, smul_lie, lie_smul, ← hc, lie_smul, hef,
      smul_smul, smul_smul, ← pow_two, hd, inv_mul_cancel₀ hc₀, one_smul]
  choose y hy hy₀ hyσ using hex
  let x (a : Root H) : L := if 0 < φ a.val then y a else -σ (y (opp a))
  have xpos (a : Root H) (ha : 0 < φ a.val) :
      x a = y a ∧ x (opp a) = -σ (y a) := by
    have ha' : ¬0 < φ (opp a).val := by rw [hn]; linarith
    simp [x, ha, ha', hopp a]
  have xneg (a : Root H) (ha : ¬0 < φ a.val) :
      x a = -σ (y (opp a)) ∧ x (opp a) = y (opp a) := by
    have hneg : φ a.val < 0 := lt_of_le_of_ne (le_of_not_gt ha) (hφ _ a.property)
    have ha' : 0 < φ (opp a).val := by rw [hn]; linarith
    simp [x, ha, ha']
  refine ⟨x, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : 0 < φ a.val
    · rw [(xpos a ha).1]
      exact ⟨hy a, hy₀ a⟩
    · rw [(xneg a ha).1]
      have h := Submodule.neg_mem _ (involution_mem_opposite σ hσ (hy (opp a)))
      exact ⟨by simpa [opp] using h, by simpa using hy₀ (opp a)⟩
  · intro a
    by_cases ha : 0 < φ a.val
    · rw [(xpos a ha).1, (xpos a ha).2, hyσ]
    · rw [(xneg a ha).1, (xneg a ha).2, ← lie_skew (-σ (y (opp a))) (y (opp a)), hyσ]
      change -(killingCoroot H (-a.val) : L) = (killingCoroot H a.val : L)
      rw [coroot_neg, Submodule.coe_neg, neg_neg]
  · intro a
    by_cases ha : 0 < φ a.val
    · simp [(xpos a ha).1, (xpos a ha).2]
    · simp [(xneg a ha).1, (xneg a ha).2, hσ₂ _]

private theorem not_proportional_of_root_add (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {α β : Module.Dual ℂ H} (ha : α ∈ rootSet H) (hb : β ∈ rootSet H)
    (hab : α + β ∈ rootSet H) : ∀ c : ℂ, β ≠ c • α := by
  intro c h
  rcases proportional_root_eq hss H hH α β ha hb c h with h | h
  · rw [h] at hab
    have h₂ : α + α = (2 : ℂ) • α := (two_smul ℂ α).symm
    have hh := proportional_root_eq hss H hH α (α + α) ha hab 2 h₂
    rcases hh with h₁ | h₁
    · exact ha.1 (by simpa using add_left_cancel (h₁.trans (add_zero α).symm))
    · have hz : (3 : ℂ) • α = 0 := by
        calc
          (3 : ℂ) • α = (α + α) + α := by module
          _ = 0 := by simp [h₁]
      exact ha.1 ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  · exact hab.1 (by simp [h])

omit [FiniteDimensional ℂ L] in
private theorem shift_not_proportional {α β : Module.Dual ℂ H}
    (hn : ∀ c : ℂ, β ≠ c • α) (k : ℤ) (c : ℂ) :
    β + k • α ≠ c • α := by
  intro he
  apply hn (c - (k : ℂ))
  rw [sub_smul, Int.cast_smul_eq_zsmul]
  exact eq_sub_of_add_eq he

private theorem coroot_eval_self (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {α : Module.Dual ℂ H} (ha : α ∈ rootSet H) :
    α (killingCoroot H α) = 2 := by
  rw [killingCoroot_pairing hss H hH, mul_div_cancel_right₀ _ (rootForm_self_ne_zero hss H hH _ ha)]

omit [FiniteDimensional ℂ L] in
private theorem ad_pow_mem_rootSpace {α β : Module.Dual ℂ H} {e y : L}
    (he : e ∈ rootSpace H α) (hy : y ∈ rootSpace H β) (n : ℕ) :
    ((LieModule.toEnd ℂ L L e) ^ n) y ∈ rootSpace H (β + (n : ℤ) • α) := by
  induction n with
  | zero => simpa using hy
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply]
    convert rootSpace_bracket H α (β + (n : ℤ) • α) e _ he ih using 2
    rw [Nat.cast_succ, add_zsmul, one_zsmul]
    abel

/-- On the root line at position p above the bottom, the lowering operator
after the raising operator acts by q(p+1). -/
private theorem lowering_raising_rootVector (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {α β : Module.Dual ℂ H} (ha : α ∈ rootSet H) (hb : β ∈ rootSet H)
    (hn : ∀ c : ℂ, β ≠ c • α) {p q : ℕ}
    (hpq : β (killingCoroot H α) = (p : ℂ) - q) (hs : IsString H α β p q)
    {e f x : L} (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hef : ⁅e, f⁆ = (killingCoroot H α : L)) (hx : x ∈ rootSpace H β) :
    ⁅f, ⁅e, x⁆⁆ = ((q : ℂ) * (p + 1)) • x := by
  let h := killingCoroot H α
  have hh := coroot_eval_self hss hH ha
  have T : IsSl2Triple (h : L) e f :=
    { h_ne_zero := coroot_ne_zero hss hH ha
      lie_e_f := hef
      lie_h_e_nsmul := by
        rw [(mem_rootSpace H _ _).mp he h]
        change α (killingCoroot H α) • e = _
        rw [hh]
        norm_cast
      lie_h_f_nsmul := by
        rw [(mem_rootSpace H _ _).mp hf h]
        change -α (killingCoroot H α) • f = _
        rw [hh, neg_smul]
        norm_cast }
  let γ := β + (-(p : ℤ)) • α
  have hγ : γ ∈ rootSet H := (hs _).mpr ⟨le_rfl, by omega⟩
  obtain ⟨y, hy, _, _, hy₀, _⟩ : ∃ y : L, y ∈ rootSpace H γ ∧
      ∃ z : L, z ∈ rootSpace H (-γ) ∧ y ≠ 0 ∧ z ≠ 0 := by
    obtain ⟨y, z, hy, hz, hy₀, hz₀, _⟩ := exists_root_triple hss H hH γ hγ
    exact ⟨y, hy, z, hz, hy₀, hz₀⟩
  have hfy : ⁅f, y⁆ = 0 := by
    have hm := rootSpace_bracket H (-α) γ f y hf hy
    have heq : -α + γ = β + (-(p : ℤ) - 1) • α := by
      dsimp [γ]
      rw [sub_zsmul, one_zsmul]
      abel
    rw [heq] at hm
    have hz : β + (-(p : ℤ) - 1) • α ≠ 0 := by
      simpa using shift_not_proportional hn (-(p : ℤ) - 1) 0
    rw [rootSpace_eq_bot_of_not_mem H _ hz
      (fun hmem => by have := (hs _).mp hmem; omega)] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  have P : T.symm.HasPrimitiveVectorWith y ((p : ℂ) + q) := by
    refine ⟨hy₀, ?_, hfy⟩
    rw [neg_lie, (mem_rootSpace H _ _).mp hy h, ← neg_smul]
    congr 1
    change -((β + (-(p : ℤ)) • α) (killingCoroot H α)) = _
    rw [← Int.cast_smul_eq_zsmul ℂ]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Int.cast_neg, Int.cast_natCast,
      hpq, hh, smul_eq_mul]
    ring
  let E := LieModule.toEnd ℂ L L e
  have hv₀ : (E ^ p) y ≠ 0 :=
    P.pow_toEnd_f_ne_zero_of_eq_nat (n := p + q) (by norm_num) (by omega)
  have hv : (E ^ p) y ∈ rootSpace H β := by
    simpa [γ] using ad_pow_mem_rootSpace he hy p
  obtain ⟨c, hc⟩ := rootVector_spans hss hH hb hv hx hv₀
  have h := P.lie_e_pow_succ_toEnd_f p
  change ⁅f, (E ^ (p + 1)) y⁆ = _ at h
  have heq : ((p : ℂ) + 1) * ((p : ℂ) + q - p) = (q : ℂ) * (p + 1) := by ring
  rw [heq, pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply] at h
  rw [← hc, lie_smul, lie_smul, h, smul_comm c]

private theorem rootForm_symm (α β : Module.Dual ℂ H) :
    rootForm H α β = rootForm H β α := by
  rw [rootForm_apply H α β, rootForm_apply H β α]
  exact killingForm_symmetric ℂ L _ _

set_option maxHeartbeats 600000 in
/-- At the top of an independent string of length at least two, the reverse
Cartan integer is one. This determines the length ratio in (6.5). -/
private theorem string_length_ratio (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {α β : Module.Dual ℂ H} (ha : α ∈ rootSet H)
    (hn : ∀ c : ℂ, β ≠ c • α) {p q : ℕ} (hq : 0 < q)
    (hpq : β (killingCoroot H α) = (p : ℂ) - q) (hs : IsString H α β p q) :
    (q : ℂ) * rootForm H (α + β) (α + β) = (p + 1 : ℂ) * rootForm H β β := by
  let B := rootForm H
  have hcross : 2 * B β α = ((p : ℂ) - q) * B α α := by
    rw [killingCoroot_pairing hss H hH] at hpq
    exact (div_eq_iff (rootForm_self_ne_zero hss H hH _ ha)).mp hpq
  have hlen (k : ℂ) :
      B (β + k • α) (β + k • α) = B β β + k * (k + (p : ℂ) - q) * B α α := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [show B α β = B β α from rootForm_symm α β]
    linear_combination k * hcross
  have hplus : B (α + β) (α + β) = B β β + ((p : ℂ) - q + 1) * B α α := by
    have he := hlen 1
    rw [one_smul, add_comm β α, one_mul] at he
    convert he using 2
    ring
  by_cases heasy : p + 1 = q
  · have hcast : (q : ℂ) = (p : ℂ) + 1 := by exact_mod_cast heasy.symm
    rw [hplus, hcast]
    ring
  have hn₂ : 2 ≤ p + q := by omega
  let δ := β + (q : ℤ) • α
  have hd : δ ∈ rootSet H := (hs _).mpr ⟨by omega, le_rfl⟩
  have hdeval : δ (killingCoroot H α) = (p : ℂ) + q := by
    dsimp only [δ]
    rw [← Int.cast_smul_eq_zsmul ℂ]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Int.cast_natCast, hpq,
      smul_eq_mul, coroot_eval_self hss hH ha]
    ring
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  let wα : H.root := ⟨rootWeight H hH α ha, by simpa using rootWeight_nonzero H hH α ha⟩
  let wδ : H.root := ⟨rootWeight H hH δ hd, by simpa using rootWeight_nonzero H hH δ hd⟩
  let P := LieAlgebra.IsKilling.rootSystem H
  have hwα : P.root wα = α := rootWeight_toLinear H hH α ha
  have hwδ : P.root wδ = δ := rootWeight_toLinear H hH δ hd
  have hcart (i j : H.root) :
      (P.pairingIn ℤ i j : ℂ) = P.root i (killingCoroot H (P.root j)) := by
    change algebraMap ℤ ℂ (P.pairingIn ℤ i j) = _
    rw [P.algebraMap_pairingIn, LieAlgebra.IsKilling.rootSystem_pairing_apply,
      ← LieAlgebra.IsKilling.rootSystem_coroot_apply, rootSystem_coroot_eq hss hH]
    rfl
  have hc : P.pairingIn ℤ wδ wα = (p : ℤ) + q := by
    have hh := hcart wδ wα
    rw [hwδ, hwα, hdeval] at hh
    exact_mod_cast hh
  have hoptions := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' (i := wδ) (j := wα)
    (by rw [hwδ, hwα]; simpa [δ] using shift_not_proportional hn q 1)
    (by rw [hwδ, hwα]; simpa [δ] using shift_not_proportional hn q (-1))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, hc] at hoptions
  have hrev : P.pairingIn ℤ wα wδ = 1 := by omega
  have hbound : p + q ≤ 3 := by omega
  have hαδ : α (killingCoroot H δ) = 1 := by
    simpa [hwα, hwδ, hrev] using (hcart wα wδ).symm
  have hδlen : B δ δ = ((p : ℂ) + q) * B α α := by
    rw [killingCoroot_pairing hss H hH] at hdeval hαδ
    have hd₁ := (div_eq_iff (rootForm_self_ne_zero hss H hH _ ha)).mp hdeval
    have hd₂ := (div_eq_iff (rootForm_self_ne_zero hss H hH _ hd)).mp hαδ
    rw [rootForm_symm δ α] at hd₁
    simpa only [one_mul] using hd₂.symm.trans hd₁
  have hβlen : B β β = (q : ℂ) * B α α := by
    have hl := hlen (q : ℂ)
    have hδ : β + (q : ℂ) • α = δ := by
      dsimp [δ]
      rw [← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast]
    rw [hδ] at hl
    rw [hδlen] at hl
    have hh : p = 0 ∨ q = 1 := by omega
    rcases hh with h | h
    · simp [h] at hl
      exact hl.symm
    · rw [h] at hl ⊢
      push_cast at hl ⊢
      linear_combination -hl
  rw [hplus, hβlen]
  ring

private theorem square_constant_of_coroot_relation
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {α β : Module.Dual ℂ H} (hb : β ∈ rootSet H) (hab : α + β ∈ rootSet H)
    (hn : ∀ c : ℂ, β ≠ c • α) {r s t : ℂ}
    (h : r • (killingCoroot H (α + β) : L) =
      s • (killingCoroot H α : L) + t • (killingCoroot H β : L)) :
    r * rootForm H β β = t * rootForm H (α + β) (α + β) := by
  let d (γ : Module.Dual ℂ H) := 2 / rootForm H γ γ
  have h' : r • killingCoroot H (α + β) =
      s • killingCoroot H α + t • killingCoroot H β := Subtype.ext h
  have ht : (r * d (α + β)) • (α + β) = (s * d α) • α + (t * d β) • β := by
    ext z
    have hz := congrArg (fun v : H => killingForm ℂ L (v : L) (z : L)) h'
    change killingForm ℂ L (r • (killingCoroot H (α + β) : L)) (z : L) =
      killingForm ℂ L (s • (killingCoroot H α : L) + t • (killingCoroot H β : L)) (z : L) at hz
    have hcoe (a : Module.Dual ℂ H) : (killingCoroot H a : L) = d a • (tAlpha H a : L) := rfl
    simpa only [hcoe, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, mul_assoc, tAlpha_pairing hss H hH] using hz
  have hcoef : r * d (α + β) = t * d β := by
    let c := r * d (α + β)
    have hx : (c - t * d β) • β = (s * d α - c) • α := by
      rw [smul_add] at ht
      rw [sub_smul, sub_smul]
      exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa [c, add_comm, add_left_comm] using ht)
    by_contra hne
    have hc : c - t * d β ≠ 0 := sub_ne_zero.mpr hne
    apply hn ((c - t * d β)⁻¹ * (s * d α - c))
    rw [← smul_smul, ← hx, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hd : r / rootForm H (α + β) (α + β) = t / rootForm H β β := by
    apply mul_left_cancel₀ (two_ne_zero (α := ℂ))
    simp only [d, div_eq_mul_inv] at hcoef ⊢
    linear_combination hcoef
  exact (div_eq_div_iff (rootForm_self_ne_zero hss H hH _ hab)
    (rootForm_self_ne_zero hss H hH _ hb)).mp hd

set_option maxHeartbeats 900000 in
private theorem root_constant_magnitude
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (opp : Root H → Root H) (ho : ∀ α, (opp α).val = -α.val)
    (x : Root H → L) (hx : ∀ α, x α ∈ rootSpace H α.val ∧ x α ≠ 0)
    (hopp : ∀ α, ⁅x α, x (opp α)⁆ = (killingCoroot H α.val : L))
    (σ : L ≃ₗ⁅ℂ⁆ L) (hσ : ∀ α, σ (x α) = -x (opp α))
    (α β : Root H) (hab : α.val + β.val ∈ rootSet H) {n : ℂ}
    (hn : ⁅x α, x β⁆ = n • x ⟨_, hab⟩) :
    ∃ p q : ℕ, IsString H α.val β.val p q ∧
      (n = (p : ℂ) + 1 ∨ n = -((p : ℂ) + 1)) := by
  let γ : Root H := ⟨_, hab⟩
  have hab' : β.val + α.val ∈ rootSet H := by simpa [add_comm] using hab
  have hnp := not_proportional_of_root_add hss hH α.property β.property hab
  have hnp' := not_proportional_of_root_add hss hH β.property α.property hab'
  obtain ⟨p, q, he, hs⟩ := RootStrings.root_string hss H hH α.val β.val α.property β.property
    (by simpa using hnp 1) (by simpa using hnp (-1))
  obtain ⟨p', q', he', hs'⟩ := RootStrings.root_string hss H hH β.val α.val β.property α.property
    (by simpa using hnp' 1) (by simpa using hnp' (-1))
  have hq : 0 < q := by
    have h₁ : β.val + (1 : ℤ) • α.val ∈ rootSet H := by simpa using hab'
    have := (hs 1).mp h₁
    omega
  have hαβ : ⁅x (opp α), ⁅x α, x β⁆⁆ = ((q : ℂ) * (p + 1)) • x β :=
    lowering_raising_rootVector hss hH α.property β.property hnp he hs (hx α).1
      (ho α ▸ (hx (opp α)).1) (hopp α) (hx β).1
  have hβα : ⁅x (opp β), ⁅x β, x α⁆⁆ = ((q' : ℂ) * (p' + 1)) • x α :=
    lowering_raising_rootVector hss hH β.property α.property hnp' he' hs' (hx β).1
      (ho β ▸ (hx (opp β)).1) (hopp β) (hx α).1
  have hn' : ⁅x (opp α), x (opp β)⁆ = -n • x (opp γ) := by
    have hh := congrArg σ hn
    simpa only [LieEquiv.map_lie, map_smul, hσ, neg_lie, lie_neg, neg_neg, neg_smul, smul_neg, γ] using hh
  have hrel : n ^ 2 • (killingCoroot H (α.val + β.val) : L) =
      ((q' : ℂ) * (p' + 1)) • (killingCoroot H α.val : L) +
      ((q : ℂ) * (p + 1)) • (killingCoroot H β.val : L) := by
    have heq₁ : ⁅⁅x α, x β⁆, x (opp α)⁆ = -(((q : ℂ) * (p + 1)) • x β) := by
      rw [← lie_skew ⁅x α, x β⁆ (x (opp α)), hαβ]
    have heq₂ : ⁅⁅x α, x β⁆, x (opp β)⁆ = ((q' : ℂ) * (p' + 1)) • x α := by
      rw [← lie_skew ⁅x α, x β⁆ (x (opp β)), ← lie_skew (x α) (x β), lie_neg, neg_neg, hβα]
    have hh := leibniz_lie ⁅x α, x β⁆ (x (opp α)) (x (opp β))
    rw [heq₁, heq₂, hn', hn] at hh
    change ⁅n • x γ, -n • x (opp γ)⁆ = _ at hh
    rw [smul_lie, lie_smul, smul_smul, mul_neg, ← pow_two, neg_smul,
      hopp, neg_lie, smul_lie, hopp, lie_smul, ← lie_skew (x (opp α)) (x α),
      hopp, smul_neg, ← neg_add_rev] at hh
    exact neg_injective hh
  have hsq := square_constant_of_coroot_relation hss hH β.property hab hnp hrel
  have hratio := string_length_ratio hss hH α.property hnp hq he hs
  have hsq' : n ^ 2 = ((p : ℂ) + 1) ^ 2 := by
    apply mul_right_cancel₀ (rootForm_self_ne_zero hss H hH _ β.property)
    linear_combination hsq + ((p : ℂ) + 1) * hratio
  exact ⟨p, q, hs, sq_eq_sq_iff_eq_or_eq_neg.mp hsq'⟩

omit [FiniteDimensional ℂ L] in
private theorem mem_int_span_has_int_coordinates {ι : Type u} (b : Module.Basis ι ℂ L)
    {x : L} (hx : x ∈ Submodule.span ℤ (Set.range b)) (k : ι) :
    ∃ z : ℤ, b.repr x k = (z : ℂ) := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [b.repr_self_apply]
    split
    · exact ⟨1, by norm_num⟩
    · exact ⟨0, by norm_num⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b', hb⟩ := hy
    exact ⟨a + b', by simp [ha, hb]⟩
  | smul a x _ hx =>
    obtain ⟨z, hz⟩ := hx
    exact ⟨a * z, by rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, Finsupp.smul_apply, hz,
      smul_eq_mul, Int.cast_mul]⟩

section CartanBasis

open Specs.LieAlgebrasAndRepresentations.SerreRelations
open LieAlgebra.IsKilling
open Set Submodule

variable [H.IsCartanSubalgebra] [LieAlgebra.IsKilling ℂ L]

private theorem exists_cartan_basis_with_int_coroots
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ)
    (B : (rootSystem H).Base)
    (hB : ∀ i : H.root, i ∈ B.support ↔ (rootSystem H).root i ∈ simple H φ) :
    ∃ b : Module.Basis (simple H φ) ℂ H,
      (∀ i, b i = killingCoroot H i.val) ∧
      ∀ α : Root H, killingCoroot H α.val ∈ span ℤ (range b) := by
  classical
  let P := rootSystem H
  let f (i : B.support) : simple H φ := ⟨P.root i, (hB i).mp i.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact Subtype.ext (P.root.injective (congrArg Subtype.val hij))
    · intro i
      have hi : i.val ∈ rootSet H := i.property.1.1
      obtain ⟨j, hj⟩ := (rootSystem_mem_iff hH i.val).mpr hi
      have hjs : j ∈ B.support := (hB j).mpr (hj ▸ i.property)
      exact ⟨⟨j, hjs⟩, Subtype.ext hj⟩
  let E := Equiv.ofBijective f hf
  let b := B.toCoweightBasis.reindex E
  have hb (i : B.support) : b (E i) = P.coroot i := by
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
    exact B.toCoweightBasis_apply i
  refine ⟨b, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := E.surjective i
    rw [hb, rootSystem_coroot_eq hss hH]
    rfl
  · intro α
    obtain ⟨i, hi⟩ := (rootSystem_mem_iff hH α.val).mpr α.property
    rw [← hi, ← rootSystem_coroot_eq hss hH]
    apply (span_mono ?_ : span ℤ (P.coroot '' (B.support : Set H.root)) ≤ _)
      (B.coroot_mem_span_int i)
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨E ⟨j, hj⟩, hb ⟨j, hj⟩⟩

end CartanBasis

private theorem exists_root_cartan_basis
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {ι : Type u} (bH : Module.Basis ι ℂ H)
    (x : Root H → L) (hx : ∀ α, x α ∈ rootSpace H α.val ∧ x α ≠ 0) :
    ∃ b : Module.Basis (ι ⊕ Root H) ℂ L,
      (∀ i, b (.inl i) = (bH i : L)) ∧ ∀ α, b (.inr α) = x α := by
  classical
  let : DecidableEq (Option (Root H)) := Classical.decEq _
  let I : Option (Root H) → Type u
    | none => ι
    | some _ => PUnit
  let v (α : Root H) (_ : PUnit.{u+1}) : rootSpace H α.val := ⟨x α, (hx α).1⟩
  have hv (α : Root H) : LinearIndependent ℂ (v α) :=
    linearIndependent_unique_iff.mpr (fun h => (hx α).2 (congrArg Subtype.val h))
  let bα (α : Root H) : Module.Basis PUnit.{u+1} ℂ (rootSpace H α.val) :=
    basisOfLinearIndependentOfCardEqFinrank' (v α) (hv α)
      (by simp only [Fintype.card_punit, finrank_rootSpace_eq_one hss H hH α.val α.property])
  have hbα (α : Root H) : bα α PUnit.unit = v α PUnit.unit :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (v α) (hv α) _) PUnit.unit
  let bv : ∀ i, Module.Basis (I i) ℂ (rootSummand H i)
    | none => bH
    | some α => bα α
  let E : (Σ i, I i) ≃ (ι ⊕ Root H) :=
    { toFun := fun ⟨i, a⟩ => match i, a with
        | none, a => .inl a
        | some α, _ => .inr α
      invFun := fun
        | .inl i => ⟨none, i⟩
        | .inr α => ⟨some α, PUnit.unit⟩
      left_inv := by intro ⟨i, a⟩; cases i <;> rfl
      right_inv := by intro i; cases i <;> rfl }
  let bi := (root_decomposition hss H hH).collectedBasis bv
  let b := bi.reindex E
  refine ⟨b, fun i => ?_, fun α => ?_⟩
  · simp only [b, Module.Basis.reindex_apply, bi, DirectSum.IsInternal.collectedBasis_coe]
    rfl
  · simp only [b, Module.Basis.reindex_apply, bi, DirectSum.IsInternal.collectedBasis_coe]
    change ((bα α PUnit.unit : rootSpace H α.val) : L) = x α
    exact congrArg Subtype.val (hbα α)

set_option maxHeartbeats 1300000 in
/-- Chevalley bases for a maximal toral subalgebra and a regular positive system. -/
theorem chevalley_basis : chevalley_basis_type.{u} := by
  classical
  intro L _ _ _ hss H hH φ hφ
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  obtain ⟨B, hB⟩ := exists_base_for_functional hH φ hφ
  obtain ⟨bH, hbH, hbHℤ⟩ := exists_cartan_basis_with_int_coroots hss hH φ B hB
  obtain ⟨g, _, _⟩ := LieAlgebra.exists_basis_of_base B
  let : Fintype B.support := Fintype.ofFinite _
  obtain ⟨σ, hσ₂, hσ⟩ := exists_sign_involution hss hH g
  let negRoot (α : Root H) := neg_mem_rootSet hss hH α.property
  let opp (α : Root H) : Root H := ⟨-α.val, negRoot α⟩
  obtain ⟨x, hx, hOpp, hSign⟩ := exists_normalized_root_vectors hss hH φ hφ σ hσ₂ hσ
  change (∀ α, ⁅x α, x (opp α)⁆ = (killingCoroot H α.val : L)) at hOpp
  change (∀ α, σ (x α) = -x (opp α)) at hSign
  have hconstants (α β : Root H) (hab : α.val + β.val ∈ rootSet H) :
      ∃ n : ℤ, ⁅x α, x β⁆ = (n : ℂ) • x ⟨_, hab⟩ ∧
        ∃ p q : ℕ, IsString H α.val β.val p q ∧
          (n = (p : ℤ) + 1 ∨ n = -((p : ℤ) + 1)) := by
    let γ : Root H := ⟨_, hab⟩
    have hb := rootSpace_bracket H α.val β.val (x α) (x β) (hx α).1 (hx β).1
    obtain ⟨c, hc⟩ := rootVector_spans hss hH hab (hx γ).1 hb (hx γ).2
    obtain ⟨p, q, hpq, hc'⟩ :=
      root_constant_magnitude hss hH opp (fun _ => rfl) x hx hOpp σ hSign α β hab hc.symm
    rcases hc' with h | h
    · exact ⟨(p : ℤ) + 1, by simpa [h] using hc.symm, p, q, hpq, Or.inl rfl⟩
    · exact ⟨-((p : ℤ) + 1), by simpa [h] using hc.symm, p, q, hpq, Or.inr rfl⟩
  choose N hN hNm using hconstants
  obtain ⟨b, hbC, hbR⟩ := exists_root_cartan_basis hss hH bH x hx
  have hbH' (i) : b (.inl i) = (killingCoroot H i.val : L) := by rw [hbC, hbH]
  have hzero (α β : Root H) (hne : α.val + β.val ≠ 0) (hab : α.val + β.val ∉ rootSet H) :
      ⁅x α, x β⁆ = 0 := by
    have hb := rootSpace_bracket H α.val β.val (x α) (x β) (hx α).1 (hx β).1
    rw [rootSpace_eq_bot_of_not_mem H _ hne hab] at hb
    exact (Submodule.mem_bot ℂ).mp hb
  refine ⟨negRoot, x, N, σ, b, hx, hOpp, hσ₂, hσ, hSign, ?_, hzero, hbH', hbR, ?_, ?_, ?_⟩
  · intro α β hab
    let γ : Root H := ⟨_, hab⟩
    have hneg : (opp α).val + (opp β).val ∈ rootSet H := by
      change -α.val + -β.val ∈ rootSet H
      rw [← neg_add]
      exact negRoot γ
    have heq : (⟨(opp α).val + (opp β).val, hneg⟩ : Root H) = opp γ :=
      Subtype.ext (neg_add α.val β.val).symm
    have hs := congrArg σ (hN α β hab)
    have hs' : ⁅x (opp α), x (opp β)⁆ = -(N α β hab : ℂ) • x (opp γ) := by
      simpa only [LieEquiv.map_lie, map_smul, hSign, neg_lie, lie_neg, neg_neg, smul_neg, neg_smul, γ] using hs
    have he := hN (opp α) (opp β) hneg
    rw [heq, hs'] at he
    have hn := (smul_left_injective ℂ (hx (opp γ)).2) he
    refine ⟨hN α β hab, ?_, hNm α β hab⟩
    exact_mod_cast hn.symm
  · let S := Submodule.span ℤ (Set.range b)
    have hgen (i) : b i ∈ S := Submodule.subset_span (Set.mem_range_self i)
    have hC (a : Root H) : (killingCoroot H a.val : L) ∈ S := by
      let incl : H →ₗ[ℤ] L := H.toSubmodule.subtype.restrictScalars ℤ
      have he : incl (killingCoroot H a.val) ∈ Submodule.map incl (Submodule.span ℤ (Set.range bH)) :=
        Submodule.mem_map_of_mem (hbHℤ a)
      rw [Submodule.map_span] at he
      apply Submodule.span_mono ?_ he
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, hbC i⟩
    have hR (a : Root H) : x a ∈ S := hbR a ▸ hgen (.inr a)
    intro i j k
    apply mem_int_span_has_int_coordinates b _ k
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        rw [hbH', hbH']
        let : IsLieAbelian H := hH.1.1
        rw [← LieSubalgebra.coe_bracket, trivial_lie_zero]
        exact S.zero_mem
      | inr a =>
        rw [hbH', hbR, (mem_rootSpace H _ _).mp (hx a).1 (killingCoroot H i.val)]
        obtain ⟨n, hn, _⟩ := RootStrings.coroot_pairing_integral hss H hH
          i.val a.val i.property.1.1 a.property
        rw [hn, Int.cast_smul_eq_zsmul]
        exact S.smul_mem n (hR a)
    | inr a =>
      cases j with
      | inl j =>
        rw [hbR, hbH', ← lie_skew (x a) (killingCoroot H j.val : L),
          (mem_rootSpace H _ _).mp (hx a).1 (killingCoroot H j.val)]
        obtain ⟨n, hn, _⟩ := RootStrings.coroot_pairing_integral hss H hH
          j.val a.val j.property.1.1 a.property
        rw [hn, Int.cast_smul_eq_zsmul]
        exact S.neg_mem (S.smul_mem n (hR a))
      | inr d =>
        rw [hbR, hbR]
        by_cases ha : a.val + d.val = 0
        · have he : d = opp a := Subtype.ext (eq_neg_of_add_eq_zero_right ha)
          rw [he, hOpp]
          exact hC a
        · by_cases hh : a.val + d.val ∈ rootSet H
          · rw [hN a d hh, Int.cast_smul_eq_zsmul]
            exact S.smul_mem _ (hR ⟨_, hh⟩)
          · rw [hzero a d ha hh]
            exact S.zero_mem
  · intro c
    constructor
    · intro hc α
      have he := hc α
      change ⁅c α • x α, c (opp α) • x (opp α)⁆ = _ at he
      rw [smul_lie, lie_smul, hOpp, smul_smul] at he
      apply smul_left_injective ℂ (coroot_ne_zero hss hH α.property)
      simpa only [one_smul] using he
    · intro hc α
      change ⁅c α • x α, c (opp α) • x (opp α)⁆ = _
      rw [smul_lie, lie_smul, hOpp, smul_smul, hc, one_smul]
  · intro c hc α β hab
    let γ : Root H := ⟨_, hab⟩
    have hcγ : c γ ≠ 0 := by
      intro h
      have hh := hc γ
      change c γ * c (opp γ) = 1 at hh
      simp [h] at hh
    rw [smul_lie, lie_smul, hN α β hab, smul_smul, smul_smul, smul_smul]
    congr 1
    change c α * c β * (N α β hab : ℂ) =
      c α * c β / c γ * (N α β hab : ℂ) * c γ
    field_simp

end LieAlgebrasAndRepresentations
