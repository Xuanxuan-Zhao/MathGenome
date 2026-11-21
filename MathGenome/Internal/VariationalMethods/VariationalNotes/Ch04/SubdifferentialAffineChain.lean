import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.SubdifferentialAffineChain
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.SubdifferentialSum

noncomputable section
open Set Topology
universe u v
namespace VariationalNotes.Ch04
open VariationalNotes.ConvexAnalysis
open VariationalNotes.ConvexGeometry

section Algebra
variable {X : Type u} {Y : Type v}
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]

omit [TopologicalSpace Y] in
/-- Translating the argument preserves epigraph convexity. -/
lemma convex_argument_translate (g : Y → WithTop ℝ) (hg : IsConvex g) (b : Y) :
    IsConvex (fun z => g (z+b)) := by
  apply (convex_iff_twoPoint _).mpr
  intro z w r s hz hw a c ha hc hac
  have heq : a • z + c • w + b = a • (z+b) + c • (w+b) := by
    have hb : a • b + c • b = b := by rw [← add_smul, hac, one_smul]
    calc
      _ = a • z + c • w + (a • b + c • b) := by rw [hb]
      _ = _ := by module
  rw [heq]
  exact (convex_iff_twoPoint g).mp hg (z+b) (w+b) r s hz hw a c ha hc hac

omit [Module ℝ Y] [TopologicalSpace Y] in
lemma proper_argument_translate (g : Y → WithTop ℝ) (hg : Proper g) (b : Y) :
    Proper (fun z => g (z+b)) := by
  obtain ⟨z,hz⟩ := hg
  exact ⟨z-b, by simpa only [sub_add_cancel] using hz⟩

/-- Pulling back a support through the affine map gives its adjoint slope. -/
lemma subdifferential_affine_pullback (A : X →L[ℝ] Y) (b : Y)
    (g : Y → WithTop ℝ) (x : X) :
    (fun y : Y →L[ℝ] ℝ => y.comp A) '' subdifferential g (A x+b) ⊆
      subdifferential (fun z => g (A z+b)) x := by
  rintro _ ⟨y, ⟨r,hr,hy⟩, rfl⟩
  refine ⟨r,hr,fun z => ?_⟩
  convert hy (A z+b) using 1
  simp only [ContinuousLinearMap.comp_apply, map_sub, add_sub_add_right_eq_sub]

lemma subgradient_argument_translate (g : Y → WithTop ℝ) (b z : Y)
    (y : Y →L[ℝ] ℝ) :
    y ∈ subdifferential (fun w => g (w+b)) z ↔ y ∈ subdifferential g (z+b) := by
  constructor
  · rintro ⟨r,hr,hy⟩
    refine ⟨r,hr,fun w => ?_⟩
    convert hy (w-b) using 1 <;> congr 2 <;> abel
  · rintro ⟨r,hr,hy⟩
    refine ⟨r,hr,fun w => ?_⟩
    simpa only [add_sub_add_right_eq_sub] using hy (w+b)

/-- Finite dual equality implies equality in both Fenchel inequalities. -/
lemma subgradients_of_fenchel_dual_equality (A : X →L[ℝ] Y)
    (f : X → WithTop ℝ) (g : Y → WithTop ℝ) (x : X)
    (y : Y →L[ℝ] ℝ) {r s : ℝ} (hr : f x = (r : WithTop ℝ))
    (hs : g (A x) = (s : WithTop ℝ))
    (heq : -conjugate f (-(y.comp A)) - conjugate g y = ((r+s : ℝ) : EReal)) :
    -(y.comp A) ∈ subdifferential f x ∧ y ∈ subdifferential g (A x) := by
  have hflo := conjugate_finite_lower_bound f x r hr (-(y.comp A))
  have hglo := conjugate_finite_lower_bound g (A x) s hs y
  have hfbot : conjugate f (-(y.comp A)) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hflo
  have hgbot : conjugate g y ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hglo
  obtain ⟨a,ha⟩ : ∃ a : ℝ, conjugate f (-(y.comp A)) = (a : EReal) := by
    cases h : conjugate f (-(y.comp A)) using EReal.rec with
    | bot => exact (hfbot h).elim
    | coe a => exact ⟨a,rfl⟩
    | top =>
      have hh : (⊥ : EReal) = ((r+s : ℝ) : EReal) := by
        simpa only [h, sub_eq_add_neg, EReal.neg_top, EReal.bot_add] using heq
      exact (EReal.coe_ne_bot _ hh.symm).elim
  obtain ⟨c,hc⟩ : ∃ c : ℝ, conjugate g y = (c : EReal) := by
    cases h : conjugate g y using EReal.rec with
    | bot => exact (hgbot h).elim
    | coe c => exact ⟨c,rfl⟩
    | top =>
      have hh : (⊥ : EReal) = ((r+s : ℝ) : EReal) := by
        simpa only [h, sub_eq_add_neg, EReal.neg_top, EReal.add_bot] using heq
      exact (EReal.coe_ne_bot _ hh.symm).elim
  rw [ha,hc,← EReal.coe_neg,← EReal.coe_sub] at heq
  have he := EReal.coe_injective heq
  change ((-(y.comp A) x - r : ℝ) : EReal) ≤ conjugate f (-(y.comp A)) at hflo
  change ((y (A x) - s : ℝ) : EReal) ≤ conjugate g y at hglo
  rw [ha] at hflo
  rw [hc] at hglo
  have hfa := EReal.coe_le_coe_iff.mp hflo
  have hgc := EReal.coe_le_coe_iff.mp hglo
  simp only [ContinuousLinearMap.comp_apply] at hfa
  constructor
  · apply (subgradient_iff_conjugate_eq hr (-(y.comp A))).mpr
    rw [ha]
    congr 1
    change a = -y (A x) - r
    linarith
  · apply (subgradient_iff_conjugate_eq hs y).mpr
    rw [hc]
    congr 1
    linarith

/-- A real linear function has just its own slope as subgradient. -/
lemma subgradient_linear_unique (l k : X →L[ℝ] ℝ) (x : X)
    (hk : k ∈ subdifferential (fun z => ((l z : ℝ) : WithTop ℝ)) x) : k = l := by
  have h := (mem_subdifferential_iff (f := fun z => ((l z : ℝ) : WithTop ℝ)) (x := x) rfl k).mp hk
  ext w
  have hp := WithTop.coe_le_coe.mp (h (x+w))
  have hm := WithTop.coe_le_coe.mp (h (x-w))
  simp only [add_sub_cancel_left, sub_sub_cancel_left, map_neg, map_add, map_sub] at hp hm
  linarith

/-- A support for the composition is the finite attained primal value. -/
lemma affine_chain_primal_minimum (A : X →L[ℝ] Y) (b : Y)
    (g : Y → WithTop ℝ) (x : X) (l : X →L[ℝ] ℝ)
    {r : ℝ} (hr : g (A x+b) = (r : WithTop ℝ))
    (hl : l ∈ subdifferential (fun z => g (A z+b)) x) :
    (⨅ z, toEReal (((-l z : ℝ) : WithTop ℝ) + g (A z+b))) =
      ((-l x+r : ℝ) : EReal) := by
  have h := (mem_subdifferential_iff (f := fun z => g (A z+b)) (x := x) hr l).mp hl
  apply le_antisymm
  · apply iInf_le_of_le x
    rw [hr,← WithTop.coe_add]
    exact le_rfl
  · apply le_iInf
    intro z
    apply (toEReal_conventions.2.2.2.2 _ _).mpr
    have hz := add_le_add (le_refl ((-l z : ℝ) : WithTop ℝ)) (h z)
    rw [← WithTop.coe_add, map_sub] at hz
    convert hz using 1
    congr 1
    ring

lemma affine_chain_of_dual_equality (A : X →L[ℝ] Y) (b : Y)
    (g : Y → WithTop ℝ) (x : X) (l : X →L[ℝ] ℝ) (y : Y →L[ℝ] ℝ)
    {r : ℝ} (hr : g (A x+b) = (r : WithTop ℝ))
    (heq : -conjugate (fun z => ((-l z : ℝ) : WithTop ℝ)) (-(y.comp A)) -
      conjugate (fun z => g (z+b)) y = ((-l x+r : ℝ) : EReal)) :
    l ∈ (fun y : Y →L[ℝ] ℝ => y.comp A) '' subdifferential g (A x+b) := by
  obtain ⟨hf,hg⟩ := subgradients_of_fenchel_dual_equality A
    (fun z => ((-l z : ℝ) : WithTop ℝ)) (fun z => g (z+b)) x y rfl hr heq
  have he : -(y.comp A) = -l := subgradient_linear_unique (-l) _ x hf
  exact ⟨y,(subgradient_argument_translate g b (A x) y).mp hg,neg_injective he⟩

lemma convex_linear_function (l : X →L[ℝ] ℝ) :
    IsConvex (fun z => ((l z : ℝ) : WithTop ℝ)) := by
  apply (convex_iff_twoPoint _).mpr
  intro x z r s hx hz a b _ _ _
  have hr : l x = r := WithTop.coe_injective hx
  have hs : l z = s := WithTop.coe_injective hz
  simp only [map_add, map_smul, smul_eq_mul, hr, hs, le_refl]

end Algebra

/-- Ambient norm continuity is the qualification in Banach spaces. -/
theorem subdifferential_affine_chain_banach :
    Specs.subdifferential_affine_chain_banach.{u,v} := by
  intro X Y _ _ _ _ _ _ A b g hgp hgc hqual x hx
  change subdifferential (fun z => g (A z+b)) x =
    (fun y : Y →L[ℝ] ℝ => y.comp A) '' subdifferential g (A x+b)
  apply Set.Subset.antisymm ?_ (subdifferential_affine_pullback A b g x)
  intro l hl
  obtain ⟨r,hr⟩ := (mem_domain_iff g (A x+b)).mp hx
  have hfp : Proper (fun z => ((-l z : ℝ) : WithTop ℝ)) :=
    ⟨0,WithTop.coe_lt_top _⟩
  have hq : ∃ z : X, ((-l z : ℝ) : WithTop ℝ) < ⊤ ∧
      g (A z+b) < ⊤ ∧ ContinuousAt (fun w => g (w+b)) (A z) := by
    obtain ⟨z,hz,hcont⟩ := hqual
    have hc : ContinuousAt (fun w : Y => w+b) (A z) :=
      continuousAt_id.add continuousAt_const
    exact ⟨z,WithTop.coe_lt_top _,hz,hcont.comp (f := fun w : Y => w+b) hc⟩
  have hp := affine_chain_primal_minimum A b g x l hr hl
  obtain ⟨⟨y,hy,_⟩,_⟩ := banach_fenchel A
    (fun z => ((-l z : ℝ) : WithTop ℝ)) (fun z => g (z+b))
    hfp (convex_linear_function (-l)) (proper_argument_translate g hgp b)
    (convex_argument_translate g hgc b) hq (-l x+r) hp
  exact affine_chain_of_dual_equality A b g x l y hr hy

/-- Relative-interior qualification in the original finite-dimensional topologies. -/
theorem subdifferential_affine_chain_finite :
    Specs.subdifferential_affine_chain_finite.{u,v} := by
  intro X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ A b g hgp hgc hqual x hx
  let Ac := A.toContinuousLinearMap
  change subdifferential (fun z => g (Ac z+b)) x =
    (fun y : Y →L[ℝ] ℝ => y.comp Ac) '' subdifferential g (Ac x+b)
  apply Set.Subset.antisymm ?_ (subdifferential_affine_pullback Ac b g x)
  intro l hl
  obtain ⟨r,hr⟩ := (mem_domain_iff g (A x+b)).mp hx
  have hfp : Proper (fun z => ((-l z : ℝ) : WithTop ℝ)) :=
    ⟨0,WithTop.coe_lt_top _⟩
  have hfc := convex_linear_function (-l)
  have htc := convex_argument_translate g hgc b
  have hq : (A '' relativeInterior (effectiveDomain (fun z => ((-l z : ℝ) : WithTop ℝ))) ∩
      relativeInterior (effectiveDomain (fun z => g (z+b)))).Nonempty := by
    obtain ⟨_,⟨z,rfl⟩,hz⟩ := hqual
    have hzD : A z+b ∈ effectiveDomain g := intrinsicInterior_subset hz
    have hzt : A z ∈ relativeInterior (effectiveDomain (fun w => g (w+b))) := by
      apply (mem_relativeInterior_iff_extendible _ (convex_effectiveDomain htc) (A z) hzD).mpr
      intro w hw
      obtain ⟨s,hs,hmem⟩ :=
        (mem_relativeInterior_iff_extendible _ (convex_effectiveDomain hgc) (A z+b) hzD).mp
          hz (w+b) hw
      refine ⟨s,hs,?_⟩
      change g ((A z+s • (A z-w))+b) < ⊤
      change g ((A z+b)+s • ((A z+b)-(w+b))) < ⊤ at hmem
      have he : (A z+s • (A z-w))+b = (A z+b)+s • ((A z+b)-(w+b)) := by
        rw [add_sub_add_right_eq_sub]
        abel
      rwa [he]
    refine ⟨A z,⟨z,?_,rfl⟩,hzt⟩
    apply (mem_relativeInterior_iff_extendible _ (convex_effectiveDomain hfc) z
      (WithTop.coe_lt_top _)).mpr
    intro w _
    exact ⟨1,zero_lt_one,WithTop.coe_lt_top _⟩
  have hp := affine_chain_primal_minimum Ac b g x l hr hl
  obtain ⟨y,hy,_⟩ := finite_fenchel A
    (fun z => ((-l z : ℝ) : WithTop ℝ)) (fun z => g (z+b))
    hfp hfc (proper_argument_translate g hgp b) htc hq (-l x+r) hp
  exact affine_chain_of_dual_equality Ac b g x l y hr hy.symm

/-- Both clauses of the source theorem, with each of its two qualifications. -/
theorem exact_subdifferential_rules : Specs.exact_subdifferential_rules.{u,v} :=
  ⟨subdifferential_sum_banach,subdifferential_sum_finite,
    subdifferential_affine_chain_banach,subdifferential_affine_chain_finite⟩

end VariationalNotes.Ch04
