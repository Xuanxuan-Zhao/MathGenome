import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.HomotopyAndContraction
import MathGenome.Internal.AlgebraCore.P103.Ch10.Complexes

namespace P103.Ch10.HomotopyAndContraction
open CategoryTheory CategoryTheory.Limits
open P103.Ch10.Complexes
open P103.Specs.Ch10.HomotopyAndContraction
noncomputable section
universe u v w

abbrev cycleDifferential := @P103.Specs.Ch10.HomotopyAndContraction.cycleDifferential.{u,v,w}
abbrev Contractible := @P103.Specs.Ch10.HomotopyAndContraction.Contractible.{u,v,w}
abbrev SplitExactCycles := @P103.Specs.Ch10.HomotopyAndContraction.SplitExactCycles.{u,v,w}
abbrev doubleModTwo := P103.Specs.Ch10.HomotopyAndContraction.doubleModTwo
abbrev reductionModTwo := P103.Specs.Ch10.HomotopyAndContraction.reductionModTwo

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
variable {C D : HomologicalComplex (ModuleCat.{v} R) c}

theorem homotopy_homologyMap {f g : C ⟶ D} (h : Homotopy f g) (n : ι) :
    homologyMap f n = homologyMap g n := by
  apply (cycleBoundaries C n).quot_hom_ext
  intro z
  apply (homologyClass_eq_iff D n _ _).mpr
  refine ⟨(h.hom n (c.prev n)).hom z.val, ?_⟩
  have he := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (h.comm n)) z.val
  change (f.f n).hom z.val =
    (h.hom (c.next n) n).hom ((C.d n (c.next n)).hom z.val) +
      (D.d (c.prev n) n).hom ((h.hom n (c.prev n)).hom z.val) + (g.f n).hom z.val at he
  have hz : (C.d n (c.next n)).hom z.val = 0 := z.property
  rw [hz, map_zero, zero_add] at he
  exact (eq_sub_iff_add_eq).mpr he.symm

theorem chain_homotopy_homologyMap : chain_homotopy_homologyMapType.{u,v} := by
  intro R _ C D f g s hs n
  apply (cycleBoundaries C n).quot_hom_ext
  intro z
  apply (homologyClass_eq_iff D n _ _).mpr
  rw [boundaries_chain]
  refine ⟨s n z.val, ?_⟩
  have he := LinearMap.congr_fun (hs n) z.val
  have hz : (C.d n (n - 1)).hom z.val = 0 := by
    have h : z.val ∈ cycles C n := z.property
    rw [cycles_chain] at h
    exact h
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero, add_zero] at he
  exact he.symm

theorem cochain_homotopy_homologyMap : cochain_homotopy_homologyMapType.{u,v} := by
  intro R _ C D f g s hs n
  apply (cycleBoundaries C n).quot_hom_ext
  intro z
  apply (homologyClass_eq_iff D n _ _).mpr
  rw [boundaries_cochain]
  refine ⟨s n z.val, ?_⟩
  have he := LinearMap.congr_fun (hs n) z.val
  have hz : (C.d n (n + 1)).hom z.val = 0 := by
    have h : z.val ∈ cycles C n := z.property
    rw [cycles_cochain] at h
    exact h
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero, add_zero] at he
  exact he.symm

theorem homotopyEquiv_homology :
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {C D : HomologicalComplex (ModuleCat.{v} R) c}
    (h : HomotopyEquiv C D) (n : ι),
    ∃ e : Homology C n ≃ₗ[R] Homology D n,
      e.toLinearMap = homologyMap h.hom n ∧ e.symm.toLinearMap = homologyMap h.inv n := by
  intro R _ ι c C D h n
  have hl : Function.LeftInverse (homologyMap h.inv n) (homologyMap h.hom n) := by
    intro x
    have he := homotopy_homologyMap h.homotopyHomInvId n
    rw [homologyMap_comp, homologyMap_id] at he
    exact LinearMap.congr_fun he x
  have hr : Function.RightInverse (homologyMap h.inv n) (homologyMap h.hom n) := by
    intro x
    have he := homotopy_homologyMap h.homotopyInvHomId n
    rw [homologyMap_comp, homologyMap_id] at he
    exact LinearMap.congr_fun he x
  let e := LinearEquiv.ofBijective (homologyMap h.hom n) ⟨hl.injective, hr.surjective⟩
  refine ⟨e, rfl, ?_⟩
  apply LinearMap.ext
  intro x
  apply e.injective
  exact (e.apply_symm_apply x).trans (hr x).symm

theorem homotopyEquiv_quasiIsomorphism :
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {C D : HomologicalComplex (ModuleCat.{v} R) c}
    (h : HomotopyEquiv C D), QuasiIsomorphism h.hom := by
  intro R _ ι c C D h n
  obtain ⟨e, he, _⟩ := homotopyEquiv_homology h n
  change Function.Bijective (homologyMap h.hom n)
  rw [← he]
  exact e.bijective

theorem contractible_acyclic :
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c), Contractible C → Acyclic C := by
  intro R _ ι c C ⟨h⟩ n
  have he := homotopy_homologyMap h n
  rw [homologyMap_id, homologyMap_zero] at he
  refine ⟨fun x y => ?_⟩
  have hx : x = 0 := LinearMap.congr_fun he x
  have hy : y = 0 := LinearMap.congr_fun he y
  exact hx.trans hy.symm

/-- A contraction restricts to a section on each cycle module. -/
theorem splitExactCycles_of_contractible (C : HomologicalComplex (ModuleCat.{v} R) c)
    (hp : ∀ n, c.Rel (c.prev n) n) (hC : Contractible C) : SplitExactCycles C := by
  obtain ⟨h⟩ := hC
  intro n
  let s : cycles C n →ₗ[R] C.X (c.prev n) :=
    (h.hom n (c.prev n)).hom.comp (cycles C n).subtype
  have hs : (cycleDifferential C n).comp s = LinearMap.id := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    have he := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (h.comm n)) z.val
    change z.val =
      (h.hom (c.next n) n).hom ((C.d n (c.next n)).hom z.val) +
        (C.d (c.prev n) n).hom ((h.hom n (c.prev n)).hom z.val) + 0 at he
    have hz : (C.d n (c.next n)).hom z.val = 0 := z.property
    rw [hz, map_zero, zero_add, add_zero] at he
    exact he.symm
  refine ⟨Subtype.val_injective, ?_, ?_, s, hs⟩
  · intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      change (C.d (c.prev n) (c.next (c.prev n))).hom x = 0
      rw [c.next_eq' (hp n)]
      exact congrArg Subtype.val hx
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      have hz : (C.d (c.prev n) (c.next (c.prev n))).hom z.val = 0 := z.property
      rw [c.next_eq' (hp n)] at hz
      exact hz
  · intro z
    exact ⟨s z, LinearMap.congr_fun hs z⟩

/-- Splittings give a cycle projection x ↦ x-s(dx), hence a contraction. -/
theorem contractible_of_splitExactCycles (C : HomologicalComplex (ModuleCat.{v} R) c)
    (hn : ∀ n, c.Rel n (c.next n)) (hp : ∀ n, c.Rel (c.prev n) n)
    (hC : SplitExactCycles C) : Contractible C := by
  have hex : ∀ i j, c.Rel i j → ∃ s : cycles C j →ₗ[R] C.X i,
      (C.d i j).hom.comp s = (cycles C j).subtype := by
    intro i j hij
    obtain rfl := c.prev_eq' hij
    obtain ⟨s, hs⟩ := (hC j).2.2.2
    refine ⟨s, ?_⟩
    apply LinearMap.ext
    intro z
    exact congrArg Subtype.val (LinearMap.congr_fun hs z)
  let s (i j : ι) (hij : c.Rel i j) : cycles C j →ₗ[R] C.X i :=
    Classical.choose (hex i j hij)
  have hs (i j : ι) (hij : c.Rel i j) :
      (C.d i j).hom.comp (s i j hij) = (cycles C j).subtype :=
    Classical.choose_spec (hex i j hij)
  let q (n : ι) : C.X n →ₗ[R] cycles C (c.next n) :=
    (C.d n (c.next n)).hom.codRestrict (cycles C (c.next n)) (by
      intro x
      exact LinearMap.congr_fun (differential_squared C n (c.next n) (c.next (c.next n))) x)
  let r (n : ι) : C.X n →ₗ[R] cycles C n :=
    (LinearMap.id - (s n (c.next n) (hn n)).comp (q n)).codRestrict (cycles C n) (by
      intro x
      change (C.d n (c.next n)).hom (x - s n (c.next n) (hn n) (q n x)) = 0
      rw [map_sub]
      have he := LinearMap.congr_fun (hs n (c.next n) (hn n)) (q n x)
      change (C.d n (c.next n)).hom (s n (c.next n) (hn n) (q n x)) =
        (C.d n (c.next n)).hom x at he
      rw [he, sub_self])
  have hr (n : ι) (z : cycles C n) : r n z.val = z := by
    apply Subtype.ext
    change z.val - s n (c.next n) (hn n) (q n z.val) = z.val
    have hz : q n z.val = 0 := Subtype.ext z.property
    rw [hz, map_zero, sub_zero]
  let hom (i j : ι) (hji : c.Rel j i) : C.X i ⟶ C.X j :=
    ModuleCat.ofHom ((s j i hji).comp (r i))
  have he : Homotopy.nullHomotopicMap' hom = 𝟙 C := by
    apply HomologicalComplex.Hom.ext
    funext n
    rw [Homotopy.nullHomotopicMap'_f (hp n) (hn n)]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change s n (c.next n) (hn n) (r (c.next n) ((C.d n (c.next n)).hom x)) +
      (C.d (c.prev n) n).hom (s (c.prev n) n (hp n) (r n x)) = x
    have he₁ : r (c.next n) ((C.d n (c.next n)).hom x) = q n x := hr (c.next n) (q n x)
    rw [he₁]
    have he₂ := LinearMap.congr_fun (hs (c.prev n) n (hp n)) (r n x)
    change (C.d (c.prev n) n).hom (s (c.prev n) n (hp n) (r n x)) = (r n x).val at he₂
    rw [he₂]
    change s n (c.next n) (hn n) (q n x) + (x - s n (c.next n) (hn n) (q n x)) = x
    rw [add_comm, sub_add_cancel]
  exact ⟨(Homotopy.ofEq he.symm).trans (Homotopy.nullHomotopy' hom)⟩

theorem chain_contractible_iff : chain_contractible_iffType.{u,v} := by
  intro R _ C
  have hn : ∀ n : ℤ, (ComplexShape.down ℤ).Rel n ((ComplexShape.down ℤ).next n) := by
    intro n
    rw [ChainComplex.next]
    change n - 1 + 1 = n
    exact sub_add_cancel n 1
  have hp : ∀ n : ℤ, (ComplexShape.down ℤ).Rel ((ComplexShape.down ℤ).prev n) n := by
    intro n
    rw [ChainComplex.prev]
    rfl
  exact ⟨fun h => ⟨contractible_acyclic C h, splitExactCycles_of_contractible C hp h⟩,
    fun h => contractible_of_splitExactCycles C hn hp h.2⟩

theorem cochain_contractible_iff : cochain_contractible_iffType.{u,v} := by
  intro R _ C
  have hn : ∀ n : ℤ, (ComplexShape.up ℤ).Rel n ((ComplexShape.up ℤ).next n) := by
    intro n
    rw [CochainComplex.next]
    rfl
  have hp : ∀ n : ℤ, (ComplexShape.up ℤ).Rel ((ComplexShape.up ℤ).prev n) n := by
    intro n
    rw [CochainComplex.prev]
    change n - 1 + 1 = n
    exact sub_add_cancel n 1
  exact ⟨fun h => ⟨contractible_acyclic C h, splitExactCycles_of_contractible C hp h⟩,
    fun h => contractible_of_splitExactCycles C hn hp h.2⟩

theorem modTwo_shortExact : modTwo_shortExactType := by
  constructor
  · decide
  constructor
  · unfold Function.Exact
    decide
  · decide

theorem modTwo_no_additive_section : modTwo_no_additive_sectionType := by
  rintro ⟨s, hs⟩
  have hred : reductionModTwo (s 1) = 1 := DFunLike.congr_fun hs 1
  have hadd : s 1 + s 1 = 0 := by
    rw [← map_add]
    exact s.map_zero
  have hfinite : ∀ x : ZMod 4, reductionModTwo x = 1 → x + x ≠ 0 := by decide
  exact hfinite (s 1) hred hadd

/-! The three-term integral counterexample. -/
private def exampleTerm (n : ℤ) : ModuleCat.{0} ℤ :=
  if n = 0 then ModuleCat.of ℤ (ZMod 2)
  else if n = 1 then ModuleCat.of ℤ (ZMod 4)
  else if n = 2 then ModuleCat.of ℤ (ZMod 2)
  else ModuleCat.of ℤ PUnit

private def exampleDelta (n : ℤ) : exampleTerm (n + 1) ⟶ exampleTerm n := by
  classical
  by_cases hn₀ : n = 0
  · subst n
    exact ModuleCat.ofHom reductionModTwo
  by_cases hn₁ : n = 1
  · subst n
    exact ModuleCat.ofHom doubleModTwo
  exact 0

private theorem exampleDelta_zero (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ 1) : exampleDelta n = 0 := by
  simp [exampleDelta, h₀, h₁]

private theorem exampleDelta_sq (n : ℤ) : exampleDelta (n + 1) ≫ exampleDelta n = 0 := by
  by_cases hn₀ : n = 0
  · subst n
    change ModuleCat.ofHom doubleModTwo ≫ ModuleCat.ofHom reductionModTwo = 0
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact modTwo_shortExact.2.1.apply_apply_eq_zero x
  by_cases hn₁ : n = 1
  · subst n
    change exampleDelta 2 ≫ exampleDelta 1 = 0
    rw [exampleDelta_zero 2 (by decide) (by decide), zero_comp]
  rw [exampleDelta_zero n hn₀ hn₁, comp_zero]

private def exampleComplex : Chain.{0,0} ℤ :=
  ChainComplex.of exampleTerm exampleDelta exampleDelta_sq

private theorem exampleComplex_supported :
    SupportedIn exampleComplex ({0, 1, 2} : Set ℤ) := by
  intro n hn
  have h₀ : n ≠ 0 := by intro h; exact hn (by simp [h])
  have h₁ : n ≠ 1 := by intro h; exact hn (by simp [h])
  have h₂ : n ≠ 2 := by intro h; exact hn (by simp [h])
  change Subsingleton (exampleTerm n)
  simp only [exampleTerm, ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂]
  infer_instance

private theorem exampleComplex_acyclic : Acyclic exampleComplex := by
  apply (acyclic_iff exampleComplex).mpr
  intro n
  rw [boundaries_chain, cycles_chain]
  by_cases h₀ : n = 0
  · subst n
    change LinearMap.range reductionModTwo = LinearMap.ker (0 : ZMod 2 →ₗ[ℤ] PUnit)
    rw [LinearMap.range_eq_top.mpr modTwo_shortExact.2.2, LinearMap.ker_zero]
  by_cases h₁ : n = 1
  · subst n
    change LinearMap.range doubleModTwo = LinearMap.ker reductionModTwo
    ext x
    exact (modTwo_shortExact.2.1 x).symm
  by_cases h₂ : n = 2
  · subst n
    change LinearMap.range (0 : PUnit →ₗ[ℤ] ZMod 2) = LinearMap.ker doubleModTwo
    rw [LinearMap.range_zero, LinearMap.ker_eq_bot.mpr modTwo_shortExact.1]
  have hsub : Subsingleton (exampleComplex.X n) := exampleComplex_supported n (by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using And.intro h₀ (And.intro h₁ h₂))
  let := hsub
  exact Subsingleton.elim _ _

private theorem exampleComplex_not_contractible : ¬ Contractible exampleComplex := by
  rintro ⟨h⟩
  apply modTwo_no_additive_section
  let s : ZMod 2 →+ ZMod 4 := (h.hom 0 1).hom.toAddMonoidHom
  refine ⟨s, ?_⟩
  apply AddMonoidHom.ext
  intro x
  have he := h.comm (0 : ℤ)
  rw [dNext_eq h.hom (show (ComplexShape.down ℤ).Rel 0 (-1) by decide),
    prevD_eq h.hom (show (ComplexShape.down ℤ).Rel 1 0 by decide)] at he
  have hd₀ : exampleComplex.d 0 (-1) = 0 := rfl
  rw [hd₀, zero_comp, zero_add, HomologicalComplex.zero_f_apply, add_zero] at he
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom he) x).symm

theorem acyclic_noncontractible_example : acyclic_noncontractible_exampleType := by
  refine ⟨exampleComplex, LinearEquiv.refl ℤ (ZMod 2), LinearEquiv.refl ℤ (ZMod 4),
    LinearEquiv.refl ℤ (ZMod 2), exampleComplex_supported, ?_, ?_,
    exampleComplex_acyclic, exampleComplex_not_contractible⟩
  · rfl
  · rfl

end
end P103.Ch10.HomotopyAndContraction
