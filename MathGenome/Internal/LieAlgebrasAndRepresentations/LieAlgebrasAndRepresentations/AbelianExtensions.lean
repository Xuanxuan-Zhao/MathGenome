import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.AbelianExtensions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Lie.TransferInstance
import Mathlib.Tactic.FinCases
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergComplex

/-! Abelian extensions with a fixed action (LA-I01). The independent Specs
module supplies the definitions and full classification statements. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w z z'

namespace LieAlgebrasAndRepresentations.AbelianExtensions
open LieModule.Cohomology
variable {k : Type u} {g : Type v} {M : Type w}
  [Field k] [LieRing g] [LieAlgebra k g]
  [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]

theorem twisted_jacobi_iff (c : twoCochain k g M) :
    (∀ p q r : g × M,
      twistedBracket c p (twistedBracket c q r) +
      twistedBracket c q (twistedBracket c r p) +
      twistedBracket c r (twistedBracket c p q) = 0) ↔ d₂₃ k g M c = 0 := by
  constructor
  · intro h
    ext x y z
    have hh := congrArg Prod.snd (h (x, 0) (y, 0) (z, 0))
    simp only [twistedBracket, Prod.snd_add, Prod.snd_zero, lie_zero,
      sub_zero] at hh
    simp only [zero_add, ← twoCochain_skew c x z, lie_neg] at hh
    rw [← lie_skew z x, map_neg] at hh
    rw [← twoCochain_skew c ⁅y, z⁆ x, ← twoCochain_skew c ⁅x, z⁆ y,
      ← twoCochain_skew c ⁅x, y⁆ z] at hh
    simp only [neg_neg] at hh
    simp only [d₂₃_apply, LinearMap.zero_apply]
    convert hh using 1; abel
  · intro hc p q r
    let a : twoCocycle k g M := ⟨c, hc⟩
    have h := congrArg (fun t : LieAlgebra.ofTwoCocycle a => t.carrier)
      (lie_jacobi (LieAlgebra.ofProd a p) (LieAlgebra.ofProd a q) (LieAlgebra.ofProd a r))
    change
      (⁅p.1, ⁅q.1, r.1⁆⁆,
        c p.1 ⁅q.1, r.1⁆ + ⁅p.1, c q.1 r.1 + ⁅q.1, r.2⁆ - ⁅r.1, q.2⁆⁆ - ⁅⁅q.1, r.1⁆, p.2⁆) +
      (⁅q.1, ⁅r.1, p.1⁆⁆,
        c q.1 ⁅r.1, p.1⁆ + ⁅q.1, c r.1 p.1 + ⁅r.1, p.2⁆ - ⁅p.1, r.2⁆⁆ - ⁅⁅r.1, p.1⁆, q.2⁆) +
      (⁅r.1, ⁅p.1, q.1⁆⁆,
        c r.1 ⁅p.1, q.1⁆ + ⁅r.1, c p.1 q.1 + ⁅p.1, q.2⁆ - ⁅q.1, p.2⁆⁆ - ⁅⁅p.1, q.1⁆, r.2⁆) = 0 at h
    apply Prod.ext
    · exact lie_jacobi p.1 q.1 r.1
    · have hh := congrArg Prod.snd h
      simp only [Prod.snd_add, Prod.snd_zero] at hh
      simp only [twistedBracket, Prod.snd_add, Prod.snd_zero, lie_add, lie_sub] at hh ⊢
      convert hh using 1; abel


/-- Coordinate change by `+b` goes from the model for `c+db` to the model
for `c`. This is compatible with the section-change sign `s ↦ s+b`. -/
theorem shear (c : twoCochain k g M) (b : g →ₗ[k] M) (p q : g × M) :
    let T : g × M → g × M := fun p => (p.1, p.2 + b p.1)
    T (twistedBracket (c + d₁₂ k g M b) p q) = twistedBracket c (T p) (T q) := by
  apply Prod.ext
  · rfl
  · simp only [twistedBracket, add_apply_apply, d₁₂_apply_apply,
      lie_add]
    abel

theorem Extension.proj_incl (E : Extension.{u,v,w,z} k g M) (m : M) :
    E.proj (E.incl m) = 0 := by
  have h : E.incl m ∈ LinearMap.range E.incl := ⟨m, rfl⟩
  rw [E.exact] at h
  exact h

theorem central_iff (E : Extension.{u,v,w,z} k g M) :
    IsCentral E ↔ ∀ x : g, ∀ m : M, ⁅x, m⁆ = 0 := by
  constructor
  · intro h x m
    obtain ⟨e, rfl⟩ := E.surjective x
    apply E.injective
    rw [← E.action, h, map_zero]
  · intro h e m
    rw [E.action, h, map_zero]

theorem section_change (E : Extension.{u,v,w,z} k g M)
    (s : g →ₗ[k] E.carrier) (c : twoCocycle k g M)
    (h : IsSectionCocycle E s c) (b : g →ₗ[k] M) :
    IsSectionCocycle E (s + E.incl.comp b) (c + coboundaryToCocycles b) := by
  constructor
  · intro x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, E.proj_incl, add_zero]
    exact h.1 x
  · intro x y
    change E.incl (c.1 x y + (d₁₂ k g M b) x y) = _
    rw [map_add, h.2, d₁₂_apply_apply]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, add_lie, lie_add,
      E.abelian, add_zero, E.action, h.1, map_sub, ← lie_skew (E.incl (b x)) (s y),
      E.action, h.1, neg_lie, map_add, E.proj_incl]
    abel

/-- Exactness identifies the original coefficient space with the actual kernel. -/
def Extension.kernelEquiv (E : Extension.{u,v,w,z} k g M) :
    M ≃ₗ[k] LinearMap.ker E.proj.toLinearMap :=
  LinearEquiv.ofBijective
    (E.incl.codRestrict (LinearMap.ker E.proj.toLinearMap) E.proj_incl)
    ⟨fun _ _ h => E.injective (congrArg Subtype.val h), by
      intro y
      have hy : y.1 ∈ LinearMap.range E.incl := by
        rw [E.exact]
        exact y.2
      obtain ⟨m, hm⟩ := hy
      exact ⟨m, Subtype.ext hm⟩⟩

@[simp] theorem Extension.kernelEquiv_apply (E : Extension.{u,v,w,z} k g M) (m : M) :
    (E.kernelEquiv m).1 = E.incl m := rfl

@[simp] theorem Extension.incl_kernelEquiv_symm (E : Extension.{u,v,w,z} k g M)
    (y : LinearMap.ker E.proj.toLinearMap) :
    E.incl (E.kernelEquiv.symm y) = y.1 :=
  congrArg Subtype.val (E.kernelEquiv.apply_symm_apply y)

/-- Surjective linear maps split over every field, with unrestricted dimension. -/
theorem Extension.exists_linearSection (E : Extension.{u,v,w,z} k g M) :
    ∃ s : g →ₗ[k] E.carrier, ∀ x, E.proj (s x) = x := by
  obtain ⟨s, hs⟩ := E.proj.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr E.surjective)
  exact ⟨s, fun x => LinearMap.congr_fun hs x⟩

/-- The bilinear section defect takes values in the original kernel. -/
def sectionDefect (E : Extension.{u,v,w,z} k g M) (s : g →ₗ[k] E.carrier)
    (hs : ∀ x, E.proj (s x) = x) : twoCochain k g M :=
  ⟨({ toFun := fun x =>
        { toFun := fun y =>
            (⟨⁅s x, s y⁆ - s ⁅x, y⁆, by simp [hs]⟩ : LinearMap.ker E.proj.toLinearMap)
          map_add' := by intros; ext; simp; abel
          map_smul' := by intros; ext; simp [smul_sub] }
      map_add' := by intros; ext; simp; abel
      map_smul' := by intros; ext; simp [smul_sub] } :
      g →ₗ[k] g →ₗ[k] LinearMap.ker E.proj.toLinearMap).compr₂
        E.kernelEquiv.symm.toLinearMap,
    by intro x; simp⟩

@[simp] theorem sectionDefect_formula (E : Extension.{u,v,w,z} k g M)
    (s : g →ₗ[k] E.carrier) (hs : ∀ x, E.proj (s x) = x) (x y : g) :
    E.incl (sectionDefect E s hs x y) = ⁅s x, s y⁆ - s ⁅x, y⁆ := by
  exact E.incl_kernelEquiv_symm _

/-- Coordinates from a section preserve the full twisted bracket. -/
theorem section_coordinates_bracket (E : Extension.{u,v,w,z} k g M)
    (s : g →ₗ[k] E.carrier) (hs : ∀ x, E.proj (s x) = x) (p q : g × M) :
    let F : g × M → E.carrier := fun p => s p.1 + E.incl p.2
    F (twistedBracket (sectionDefect E s hs) p q) = ⁅F p, F q⁆ := by
  dsimp [twistedBracket]
  rw [map_add, map_sub, sectionDefect_formula]
  simp only [add_lie, lie_add, E.abelian, add_zero, E.action, hs,
    ← lie_skew (E.incl p.2) (s q.1), E.action, hs, map_add, E.proj_incl]
  abel

/-- The section error is an actual 2-cocycle, by transferring Jacobi along
its injective coordinate map. No cocycle certificate is assumed. -/
theorem sectionDefect_cocycle (E : Extension.{u,v,w,z} k g M)
    (s : g →ₗ[k] E.carrier) (hs : ∀ x, E.proj (s x) = x) :
    d₂₃ k g M (sectionDefect E s hs) = 0 := by
  apply (twisted_jacobi_iff _).mp
  let F : g × M →ₗ[k] E.carrier :=
    s.comp (LinearMap.fst k g M) + E.incl.comp (LinearMap.snd k g M)
  have hF : Function.Injective F := by
    intro p q hpq
    have hfirst : p.1 = q.1 := by
      have hh := congrArg E.proj hpq
      simpa only [F, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, map_add, hs, E.proj_incl, add_zero] using hh
    have hsecond : p.2 = q.2 := by
      apply E.injective
      change s p.1 + E.incl p.2 = s q.1 + E.incl q.2 at hpq
      rw [hfirst] at hpq
      exact add_left_cancel hpq
    exact Prod.ext hfirst hsecond
  have hb (p q : g × M) :
      F (twistedBracket (sectionDefect E s hs) p q) = ⁅F p, F q⁆ :=
    section_coordinates_bracket E s hs p q
  intro p q r
  apply hF
  rw [map_zero, map_add, map_add, hb, hb, hb, hb, hb, hb]
  exact lie_jacobi _ _ _

/-- The vector-space normal form from any chosen section and its cocycle. -/
theorem normal_form (E : Extension.{u,v,w,z} k g M) (s : g →ₗ[k] E.carrier)
    (c : twoCocycle k g M) (h : IsSectionCocycle E s c) :
    ∃ e : (g × M) ≃ₗ[k] E.carrier,
      (∀ p, e p = s p.1 + E.incl p.2) ∧
      (∀ p q, e (twistedBracket c.1 p q) = ⁅e p, e q⁆) := by
  let F : g × M →ₗ[k] E.carrier :=
    s.comp (LinearMap.fst k g M) + E.incl.comp (LinearMap.snd k g M)
  have hinj : Function.Injective F := by
    intro p q hpq
    have hfirst : p.1 = q.1 := by
      have hh := congrArg E.proj hpq
      simpa only [F, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, map_add, h.1, E.proj_incl, add_zero] using hh
    apply Prod.ext hfirst
    apply E.injective
    change s p.1 + E.incl p.2 = s q.1 + E.incl q.2 at hpq
    rw [hfirst] at hpq
    exact add_left_cancel hpq
  have hsurj : Function.Surjective F := by
    intro e
    have hker : e - s (E.proj e) ∈ LinearMap.ker E.proj.toLinearMap := by
      change E.proj (e - s (E.proj e)) = 0
      simp only [map_sub, h.1, sub_self]
    rw [← E.exact] at hker
    obtain ⟨m, hm⟩ := hker
    refine ⟨(E.proj e, m), ?_⟩
    change s (E.proj e) + E.incl m = e
    rw [hm]
    abel
  have hc : c.1 = sectionDefect E s h.1 := by
    apply Subtype.ext
    ext x y
    apply E.injective
    exact (h.2 x y).trans (sectionDefect_formula E s h.1 x y).symm
  refine ⟨LinearEquiv.ofBijective F ⟨hinj, hsurj⟩, fun _ => rfl, ?_⟩
  intro p q
  change F (twistedBracket c.1 p q) = ⁅F p, F q⁆
  rw [hc]
  exact section_coordinates_bracket E s h.1 p q

theorem normalForm_spec :
    Specs.LieAlgebrasAndRepresentations.AbelianExtensions.normalFormStatement.{u,v,w,z} k g M :=
  normal_form

theorem section_spec :
    Specs.LieAlgebrasAndRepresentations.AbelianExtensions.sectionStatement.{u,v,w,z} k g M := by
  intro E
  obtain ⟨s, hs⟩ := E.exists_linearSection
  exact ⟨s, ⟨sectionDefect E s hs, sectionDefect_cocycle E s hs⟩, hs,
    sectionDefect_formula E s hs⟩

theorem jacobi_spec :
    Specs.LieAlgebrasAndRepresentations.AbelianExtensions.jacobiStatement k g M :=
  twisted_jacobi_iff

theorem shear_spec :
    Specs.LieAlgebrasAndRepresentations.AbelianExtensions.shearStatement k g M :=
  shear

theorem central_spec :
    Specs.LieAlgebrasAndRepresentations.AbelianExtensions.centralStatement.{u,v,w,z} k g M :=
  central_iff

theorem sectionChange_spec :
    Specs.LieAlgebrasAndRepresentations.AbelianExtensions.sectionChangeStatement.{u,v,w,z} k g M :=
  section_change

private def productToCocycle (c : twoCocycle k g M) : (g × M) ≃ₗ[k] LieAlgebra.ofTwoCocycle c :=
  { LieAlgebra.ofProd c with
    map_add' := LieAlgebra.of_add c
    map_smul' := LieAlgebra.of_smul c }

private theorem productBracket (c : twoCocycle k g M) (p q : g × M) :
    letI := (productToCocycle c).toAddEquiv.lieRing
    twistedBracket c.1 p q = ⁅p, q⁆ := by
  change (⁅p.1, q.1⁆, ⁅p.1, q.2⁆ - ⁅q.1, p.2⁆ + c.1 p.1 q.1) =
    (⁅p.1, q.1⁆, c.1 p.1 q.1 + ⁅p.1, q.2⁆ - ⁅q.1, p.2⁆)
  congr 1
  abel

/-- The cocycle model on the product, with the transported Lie structure
kept local to this extension. -/
def modelExtension (c : twoCocycle k g M) : Extension.{u,v,w,max v w} k g M :=
  letI := (productToCocycle c).toAddEquiv.lieRing
  letI := (productToCocycle c).lieAlgebra
  { carrier := g × M
    instLieRing := inferInstance
    instLieAlgebra := inferInstance
    incl := LinearMap.inr k g M
    proj :=
      { toLinearMap := LinearMap.fst k g M
        map_lie' := by
          intro p q
          rw [← productBracket c]
          rfl }
    injective := by intro x y h; exact congrArg Prod.snd h
    surjective := fun x => ⟨(x, 0), rfl⟩
    exact := by
      ext p
      simp only [LinearMap.mem_range, LinearMap.inr_apply, LinearMap.mem_ker, LinearMap.fst_apply]
      constructor
      · rintro ⟨m, hm⟩
        exact (congrArg Prod.fst hm).symm
      · intro hp
        exact ⟨p.2, Prod.ext hp.symm rfl⟩
    abelian := by
      intro m n
      change ⁅(0, m), (0, n)⁆ = (0 : g × M)
      rw [← productBracket c]
      simp [twistedBracket]
    action := by
      intro p m
      change ⁅p, (0, m)⁆ = ((0, ⁅p.1, m⁆) : g × M)
      rw [← productBracket c]
      simp [twistedBracket] }

def modelCoordinates (c : twoCocycle k g M) : (g × M) ≃ₗ[k] (modelExtension c).carrier :=
  LinearEquiv.refl k (g × M)

theorem modelCoordinates_bracket (c : twoCocycle k g M) (p q : g × M) :
    modelCoordinates c (twistedBracket c.1 p q) =
      ⁅modelCoordinates c p, modelCoordinates c q⁆ :=
  productBracket c p q

theorem models_spec :
    Specs.LieAlgebrasAndRepresentations.AbelianExtensions.modelsStatement k g M := by
  intro c
  exact ⟨modelExtension c, modelCoordinates c, modelCoordinates_bracket c,
    fun _ => rfl, fun _ => rfl⟩

open AdvancedHomologicalAlgebra.CE in
/-- The enveloping action extending the specified action gives the canonical complex. -/
theorem canonicalCEExists_spec :
    Specs.LieAlgebrasAndRepresentations.AbelianExtensions.canonicalCEExistsStatement k g M := by
  let a := Shared.Lie.representationEquiv k g M (LieModule.toEnd k g M)
  letI := Shared.Lie.actionModule k g M a
  letI := Shared.Lie.action_tower k g M a
  refine ⟨coboundary k g M (boundary k g),
    coboundary_squared k g M _ (boundary_squared k g), ?_⟩
  intro n f x
  rw [coboundary_formula k g M _ (boundary_formula k g)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact Shared.Lie.lie_extension k g M _ _

/-- The quotient relation is exactly addition of a coboundary. -/
theorem lowClass_eq_iff (c d : twoCocycle k g M) :
    lowClass c = lowClass d ↔ ∃ b : g →ₗ[k] M, c = d + coboundaryToCocycles b := by
  change Submodule.Quotient.mk c = Submodule.Quotient.mk d ↔ _
  rw [Submodule.Quotient.eq]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by rw [hb]; abel⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, by abel⟩

theorem sectionCocycle_unique (E : Extension.{u,v,w,z} k g M)
    (s : g →ₗ[k] E.carrier) (c d : twoCocycle k g M)
    (hc : IsSectionCocycle E s c) (hd : IsSectionCocycle E s d) : c = d := by
  apply Subtype.ext
  apply Subtype.ext
  ext x y
  apply E.injective
  exact (hc.2 x y).trans (hd.2 x y).symm

/-- Two linear sections differ by a linear map to the specified kernel. -/
theorem section_difference (E : Extension.{u,v,w,z} k g M)
    (s t : g →ₗ[k] E.carrier) (hs : ∀ x, E.proj (s x) = x)
    (ht : ∀ x, E.proj (t x) = x) :
    ∃ b : g →ₗ[k] M, t = s + E.incl.comp b := by
  let D : g →ₗ[k] LinearMap.ker E.proj.toLinearMap :=
    (t - s).codRestrict _ (by intro x; change E.proj (t x - s x) = 0; simp [hs, ht])
  refine ⟨E.kernelEquiv.symm.toLinearMap.comp D, ?_⟩
  ext x
  change t x = s x + E.incl (E.kernelEquiv.symm (D x))
  rw [E.incl_kernelEquiv_symm]
  change t x = s x + (t x - s x)
  abel

theorem section_classes_equal (E : Extension.{u,v,w,z} k g M)
    (s t : g →ₗ[k] E.carrier) (c d : twoCocycle k g M)
    (hc : IsSectionCocycle E s c) (hd : IsSectionCocycle E t d) :
    lowClass c = lowClass d := by
  obtain ⟨b, rfl⟩ := section_difference E s t hc.1 hd.1
  have he := sectionCocycle_unique E _ d (c + coboundaryToCocycles b) hd
    (section_change E s c hc b)
  exact ((lowClass_eq_iff d c).mpr ⟨b, he⟩).symm

theorem ExtensionEquiv.sectionCocycle
    {E : Extension.{u,v,w,z} k g M} {F : Extension.{u,v,w,z'} k g M}
    (e : ExtensionEquiv E F) (s : g →ₗ[k] E.carrier) (c : twoCocycle k g M)
    (hc : IsSectionCocycle E s c) :
    IsSectionCocycle F (e.lieEquiv.toLinearMap.comp s) c := by
  constructor
  · intro x
    exact (e.proj_comm _).trans (hc.1 x)
  · intro x y
    change F.incl (c.1 x y) = ⁅e.lieEquiv (s x), e.lieEquiv (s y)⁆ - e.lieEquiv (s ⁅x,y⁆)
    rw [← e.incl_comm, hc.2, map_sub, LieEquiv.map_lie]

/-- Matching section cocycles give an isomorphism fixing both endpoints. -/
theorem equivalent_of_same_cocycle
    (E : Extension.{u,v,w,z} k g M) (F : Extension.{u,v,w,z'} k g M)
    (s : g →ₗ[k] E.carrier) (t : g →ₗ[k] F.carrier) (c : twoCocycle k g M)
    (hc : IsSectionCocycle E s c) (hd : IsSectionCocycle F t c) : Equivalent E F := by
  obtain ⟨a, ha, hba⟩ := normal_form E s c hc
  obtain ⟨b, hb, hbb⟩ := normal_form F t c hd
  let f : E.carrier ≃ₗ[k] F.carrier := a.symm.trans b
  have hf (p : g × M) : f (a p) = b p := by simp [f]
  refine ⟨{ lieEquiv := { f with map_lie' := ?_ }, incl_comm := ?_, proj_comm := ?_ }⟩
  · intro x y
    obtain ⟨p, rfl⟩ := a.surjective x
    obtain ⟨q, rfl⟩ := a.surjective y
    change f ⁅a p, a q⁆ = ⁅f (a p), f (a q)⁆
    rw [← hba, hf, hf, hf, hbb]
  · intro m
    change f (E.incl m) = F.incl m
    have h : a (0,m) = E.incl m := by rw [ha]; simp
    rw [← h, hf, hb]
    simp
  · intro x
    obtain ⟨p, rfl⟩ := a.surjective x
    change F.proj (f (a p)) = E.proj (a p)
    rw [hf, ha, hb, map_add, map_add, hc.1, hd.1, E.proj_incl, F.proj_incl]

/-- Equality of classes is sufficient for endpoint-preserving equivalence. -/
theorem equivalent_of_class_eq
    (E : Extension.{u,v,w,z} k g M) (F : Extension.{u,v,w,z'} k g M)
    (s : g →ₗ[k] E.carrier) (t : g →ₗ[k] F.carrier) (c d : twoCocycle k g M)
    (hc : IsSectionCocycle E s c) (hd : IsSectionCocycle F t d)
    (h : lowClass c = lowClass d) : Equivalent E F := by
  obtain ⟨b, hb⟩ := (lowClass_eq_iff c d).mp h
  have ht := section_change F t d hd b
  rw [← hb] at ht
  exact equivalent_of_same_cocycle E F s _ c hc ht

/-- Choose a section only to define the class; the following lemma removes that choice. -/
def extensionClass (E : Extension.{u,v,w,z} k g M) : LowH2 (k := k) (g := g) (M := M) :=
  lowClass (Classical.choose (Classical.choose_spec (section_spec E)))

theorem extensionClass_eq (E : Extension.{u,v,w,z} k g M)
    (s : g →ₗ[k] E.carrier) (c : twoCocycle k g M) (hc : IsSectionCocycle E s c) :
    extensionClass E = lowClass c :=
  section_classes_equal E _ s _ c
    (Classical.choose_spec (Classical.choose_spec (section_spec E))) hc

theorem extensionClass_eq_iff
    (E : Extension.{u,v,w,z} k g M) (F : Extension.{u,v,w,z'} k g M) :
    extensionClass E = extensionClass F ↔ Equivalent E F := by
  obtain ⟨s, c, hc⟩ := section_spec E
  obtain ⟨t, d, hd⟩ := section_spec F
  rw [extensionClass_eq E s c hc, extensionClass_eq F t d hd]
  constructor
  · exact equivalent_of_class_eq E F s t c d hc hd
  · rintro ⟨e⟩
    exact section_classes_equal F _ t c d (e.sectionCocycle s c hc) hd

/-- The cocycle model has the displayed cocycle for its tautological section. -/
theorem modelSectionCocycle (c : twoCocycle k g M) :
    IsSectionCocycle (modelExtension c)
      ((modelCoordinates c).toLinearMap.comp (LinearMap.inl k g M)) c := by
  constructor
  · intro x
    change ((modelCoordinates c).symm (modelCoordinates c (x,0))).1 = x
    simp
  · intro x y
    change modelCoordinates c (0, c.1 x y) =
      ⁅modelCoordinates c (x,0), modelCoordinates c (y,0)⁆ - modelCoordinates c (⁅x,y⁆,0)
    rw [← modelCoordinates_bracket, ← map_sub]
    congr 1
    simp [twistedBracket]

theorem extensionClass_surjective :
    Function.Surjective (extensionClass.{u,v,w,max v w} (k := k) (g := g) (M := M)) := by
  intro q
  obtain ⟨c, rfl⟩ := (lowBoundaries (k := k) (g := g) (M := M)).mkQ_surjective q
  exact ⟨modelExtension c, extensionClass_eq _ _ c (modelSectionCocycle c)⟩

theorem extensionClass_zero_iff (E : Extension.{u,v,w,z} k g M) :
    HasLieSection E ↔ extensionClass E = 0 := by
  constructor
  · rintro ⟨s, hs⟩
    have hc : IsSectionCocycle E s.toLinearMap 0 := by
      refine ⟨hs, ?_⟩
      intro x y
      change E.incl 0 = ⁅s x, s y⁆ - s ⁅x,y⁆
      rw [map_zero, LieHom.map_lie, sub_self]
    rw [extensionClass_eq E _ 0 hc]
    rfl
  · intro he
    obtain ⟨s, c, hc⟩ := section_spec E
    rw [extensionClass_eq E s c hc] at he
    have hz : lowClass c = lowClass (0 : twoCocycle k g M) := he
    obtain ⟨b, hb⟩ := (lowClass_eq_iff c 0).mp hz
    have ht := section_change E s c hc (-b)
    have hz' : c + coboundaryToCocycles (-b) = 0 := by rw [hb, map_neg]; abel
    rw [hz'] at ht
    refine ⟨{ toLinearMap := s + E.incl.comp (-b), map_lie' := ?_ }, ht.1⟩
    intro x y
    have hh := ht.2 x y
    change E.incl 0 = _ at hh
    rw [map_zero] at hh
    exact (sub_eq_zero.mp hh.symm).symm

theorem hasLowClass_iff_eq (E : Extension.{u,v,w,z} k g M)
    (a : LowH2 (k := k) (g := g) (M := M)) :
    HasLowClass E a ↔ extensionClass E = a := by
  constructor
  · rintro ⟨s, c, hc, rfl⟩
    exact extensionClass_eq E s c hc
  · intro ha
    obtain ⟨s, c, hc⟩ := section_spec E
    exact ⟨s, c, hc, (extensionClass_eq E s c hc).symm.trans ha⟩

theorem lowClassification_spec :
    Specs.LieAlgebrasAndRepresentations.AbelianExtensions.lowClassificationStatement.{u,v,w,z,z'}
      k g M := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E
    exact ⟨extensionClass E, (hasLowClass_iff_eq E _).mpr rfl,
      fun a ha => ((hasLowClass_iff_eq E a).mp ha).symm⟩
  · intro a
    obtain ⟨E, hE⟩ := extensionClass_surjective a
    exact ⟨E, (hasLowClass_iff_eq E a).mpr hE⟩
  · intro E F
    rw [← extensionClass_eq_iff]
    constructor
    · intro h
      exact ⟨extensionClass F, (hasLowClass_iff_eq E _).mpr h, (hasLowClass_iff_eq F _).mpr rfl⟩
    · rintro ⟨a, hE, hF⟩
      exact ((hasLowClass_iff_eq E a).mp hE).trans ((hasLowClass_iff_eq F a).mp hF).symm
  · intro E
    exact (extensionClass_zero_iff E).trans (hasLowClass_iff_eq E 0).symm

open AdvancedHomologicalAlgebra.CE

/-- Turn an alternating bilinear cochain into its exterior-power functional. -/
def cochainAlternating (c : twoCochain k g M) : g [⋀^Fin 2]→ₗ[k] M where
  toFun x := c (x 0) (x 1)
  map_update_add' := by
    intro _ x i a b
    fin_cases i <;> simp [Function.update, map_add, LinearMap.add_apply]
  map_update_smul' := by
    intro _ x i r a
    fin_cases i <;> simp [Function.update, map_smul]
  map_eq_zero_of_eq' := by
    intro x i j hij hne
    fin_cases i <;> fin_cases j <;> simp_all [twoCochain_alt]

def cochainExterior (c : twoCochain k g M) : W k g 2 →ₗ[k] M :=
  exteriorPower.alternatingMapLinearEquiv (cochainAlternating c)

@[simp] theorem cochainExterior_wedge (c : twoCochain k g M) (x : Fin 2 → g) :
    cochainExterior c (wedge k g 2 x) = c (x 0) (x 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

private theorem update_vec_two_zero (a b c : g) :
    Function.update ![a,b] (0 : Fin 2) c = ![c,b] := by
  ext i
  fin_cases i <;> simp

private theorem update_vec_two_one (a b c : g) :
    Function.update ![a,b] (1 : Fin 2) c = ![a,c] := by
  ext i
  fin_cases i <;> simp

/-- Read a degree-two exterior functional as an alternating bilinear map. -/
def exteriorCochain (f : W k g 2 →ₗ[k] M) : twoCochain k g M :=
  ⟨({ toFun := fun x =>
      { toFun := fun y => f (wedge k g 2 ![x,y])
        map_add' := by
          intro y z
          have hh := (wedge k g 2).map_update_add ![x,y] 1 y z
          simpa only [update_vec_two_zero, update_vec_two_one, map_add, map_smul, RingHom.id_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_mk] using congrArg f hh
        map_smul' := by
          intro r y
          have hh := (wedge k g 2).map_update_smul ![x,y] 1 r y
          simpa only [update_vec_two_zero, update_vec_two_one, map_add, map_smul, RingHom.id_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_mk] using congrArg f hh }
      map_add' := by
        intro x y
        ext z
        change f (wedge k g 2 ![x + y,z]) =
          f (wedge k g 2 ![x,z]) + f (wedge k g 2 ![y,z])
        have hh := (wedge k g 2).map_update_add ![x,z] 0 x y
        simpa only [update_vec_two_zero, update_vec_two_one, map_add, map_smul, RingHom.id_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_mk] using congrArg f hh
      map_smul' := by
        intro r x
        ext y
        change f (wedge k g 2 ![r • x,y]) = r • f (wedge k g 2 ![x,y])
        have hh := (wedge k g 2).map_update_smul ![x,y] 0 r x
        simpa only [update_vec_two_zero, update_vec_two_one, map_add, map_smul, RingHom.id_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_mk] using congrArg f hh } : g →ₗ[k] g →ₗ[k] M),
    by
      intro x
      change f (wedge k g 2 ![x,x]) = 0
      rw [(wedge k g 2).map_eq_zero_of_eq ![x,x] (i := 0) (j := 1) rfl (by decide), map_zero]⟩

theorem wedge_ext {n : ℕ} {f h : W k g n →ₗ[k] M}
    (hh : ∀ x, f (wedge k g n x) = h (wedge k g n x)) : f = h :=
  exteriorPower.linearMap_ext (AlternatingMap.ext hh)

def twoCochainExteriorEquiv : twoCochain k g M ≃ₗ[k] (W k g 2 →ₗ[k] M) where
  toFun := cochainExterior
  invFun := exteriorCochain
  left_inv c := by apply Subtype.ext; ext x y; simp [exteriorCochain]
  right_inv f := by
    apply wedge_ext
    intro x
    rw [cochainExterior_wedge]
    change f (wedge k g 2 ![x 0,x 1]) = f (wedge k g 2 x)
    congr 2
  map_add' c d := by apply wedge_ext; intro x; simp [add_apply_apply]
  map_smul' r c := by apply wedge_ext; intro x; simp [smul_apply_apply]

variable (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M))
  (hδ : HasLieCEFormula δ)

include hδ

/-- The degree-one canonical formula agrees with the source's `db`. -/
theorem ce_one_formula (f : W k g 1 →ₗ[k] M) (x y : g) :
    δ 1 f (wedge k g 2 ![x,y]) =
      ⁅x, f (wedge k g 1 ![y])⁆ - ⁅y, f (wedge k g 1 ![x])⁆ -
        f (wedge k g 1 ![⁅x,y⁆]) := by
  have hr : (1 : Fin 2).removeNth ![x,y] = ![x] := by
    ext i
    fin_cases i
    rfl
  rw [hδ]
  simp [cochainBracketSum, Fin.sum_univ_succ, hr]
  abel

/-- The degree-two canonical formula agrees with the source's cocycle equation. -/
theorem ce_two_formula (c : twoCochain k g M) (x y z : g) :
    δ 2 (cochainExterior c) (wedge k g 3 ![x,y,z]) = d₂₃ k g M c x y z := by
  rw [hδ]
  have hi : Finset.Ici (1 : Fin 2) = {1} := by decide
  simp [cochainBracketSum, Fin.sum_univ_succ, d₂₃_apply, hi, Fin.removeNth, Fin.succAbove]
  abel

/-- The degree-two exterior identification restricts to the actual cycle spaces. -/
theorem exterior_cycle_iff (c : twoCochain k g M) :
    δ 2 (cochainExterior c) = 0 ↔ d₂₃ k g M c = 0 := by
  constructor
  · intro hc
    ext x y z
    rw [← ce_two_formula δ hδ, hc]
    rfl
  · intro hc
    apply wedge_ext
    intro x
    have hx : x = ![x 0,x 1,x 2] := by ext i; fin_cases i <;> rfl
    rw [hx, ce_two_formula δ hδ, hc]
    rfl

def cocycleExteriorMap : twoCocycle k g M →ₗ[k] LinearMap.ker (δ 2) :=
  ((twoCochainExteriorEquiv (k := k) (g := g) (M := M)).toLinearMap.comp
    (twoCocycle k g M).subtype).codRestrict _
      (fun c => (exterior_cycle_iff δ hδ c.1).mpr c.2)

@[simp] theorem cocycleExteriorMap_val (c : twoCocycle k g M) :
    (cocycleExteriorMap δ hδ c).1 = cochainExterior c.1 := rfl

def cocycleExteriorEquiv : twoCocycle k g M ≃ₗ[k] LinearMap.ker (δ 2) :=
  LinearEquiv.ofBijective (cocycleExteriorMap δ hδ) ⟨by
    intro c d h
    apply Subtype.ext
    apply (twoCochainExteriorEquiv (k := k) (g := g) (M := M)).injective
    exact congrArg Subtype.val h, by
    intro f
    let c := (twoCochainExteriorEquiv (k := k) (g := g) (M := M)).symm f.1
    have hc : cochainExterior c = f.1 :=
      (twoCochainExteriorEquiv (k := k) (g := g) (M := M)).apply_symm_apply f.1
    refine ⟨⟨c, (exterior_cycle_iff δ hδ c).mp ?_⟩, ?_⟩
    · rw [hc]; exact f.2
    · apply Subtype.ext; exact hc⟩

/-- The degree-one formula carries every ordinary coboundary to a CE boundary. -/
theorem exterior_coboundary (b : g →ₗ[k] M) :
    cochainExterior (d₁₂ k g M b) = δ 1 (b.comp (exteriorPower.oneEquiv k g).toLinearMap) := by
  apply wedge_ext
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, cochainExterior_wedge, ce_one_formula δ hδ]
  simp [d₁₂_apply_apply, wedge]

/-- Conversely every canonical degree-one cochain is obtained from a linear map on g. -/
theorem exterior_coboundary_surj (f : W k g 1 →ₗ[k] M) :
    ∃ b : g →ₗ[k] M, cochainExterior (d₁₂ k g M b) = δ 1 f := by
  refine ⟨f.comp (exteriorPower.oneEquiv k g).symm.toLinearMap, ?_⟩
  rw [exterior_coboundary δ hδ]
  congr 1
  apply LinearMap.ext
  intro x
  simp

/-- The cycle equivalence identifies the two boundary submodules. -/
theorem cocycleExterior_boundaries :
    (lowBoundaries (k := k) (g := g) (M := M)).map
      (cocycleExteriorEquiv δ hδ).toLinearMap = ceBoundaries δ := by
  ext f
  constructor
  · rintro ⟨c, ⟨b, rfl⟩, rfl⟩
    change cochainExterior (d₁₂ k g M b) ∈ LinearMap.range (δ 1)
    exact ⟨b.comp (exteriorPower.oneEquiv k g).toLinearMap, (exterior_coboundary δ hδ b).symm⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := exterior_coboundary_surj δ hδ b
    refine ⟨coboundaryToCocycles a, ⟨a, rfl⟩, ?_⟩
    apply Subtype.ext
    exact ha.trans hb

omit hδ

/-- Identification with H² of the canonical exterior-power complex. -/
theorem ceComparison_spec :
    Specs.LieAlgebrasAndRepresentations.AbelianExtensions.ceComparisonStatement k g M := by
  intro δ hs hδ
  let j := cocycleExteriorEquiv δ hδ
  refine ⟨Submodule.Quotient.equiv _ _ j (cocycleExterior_boundaries δ hδ),
    j.toLinearMap, ?_, ?_⟩
  · intro c x y
    exact cochainExterior_wedge c.1 ![x,y]
  · intro c
    rfl

/-- A section represents the corresponding class under the comparison of
the two quotients. Its values on pure wedges determine its exterior cochain. -/
private theorem hasCEClass_iff
    (e : LowH2 (k := k) (g := g) (M := M) ≃ₗ[k] CEH2 δ)
    (j : twoCocycle k g M →ₗ[k] LinearMap.ker (δ 2))
    (hj : ∀ c x y, (j c).1 (wedge k g 2 ![x,y]) = c.1 x y)
    (he : ∀ c, e (lowClass c) = Submodule.Quotient.mk (j c))
    (E : Extension.{u,v,w,z} k g M) (a : CEH2 δ) :
    HasCEClass E δ a ↔ HasLowClass E (e.symm a) := by
  constructor
  · rintro ⟨s, c, h, hc, hh, ha⟩
    have h' : h = j c := by
      apply Subtype.ext
      apply wedge_ext
      intro x
      have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
      rw [hx, hh, hj]
    subst h
    refine ⟨s, c, hc, e.injective ?_⟩
    rw [e.apply_symm_apply, he]
    exact ha
  · rintro ⟨s, c, hc, ha⟩
    refine ⟨s, c, j c, hc, hj c, ?_⟩
    rw [← he, ha, e.apply_symm_apply]

theorem classification_of_comparisons
    (hclasses : Specs.LieAlgebrasAndRepresentations.AbelianExtensions.lowClassificationStatement.{u,v,w,z,z'} k g M)
    (hcomparison : Specs.LieAlgebrasAndRepresentations.AbelianExtensions.ceComparisonStatement k g M) :
    Specs.LieAlgebrasAndRepresentations.AbelianExtensions.classificationStatement.{u,v,w,z,z'} k g M := by
  intro δ hs hδ
  obtain ⟨hexists, hsurj, hequiv, hsplit⟩ := hclasses
  obtain ⟨e, j, hj, he⟩ := hcomparison δ hs hδ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro E
    obtain ⟨b, hb, huniq⟩ := hexists E
    refine ⟨e b, (hasCEClass_iff δ e j hj he E _).mpr (by simpa using hb), ?_⟩
    intro a ha
    apply e.symm.injective
    rw [e.symm_apply_apply]
    exact huniq _ ((hasCEClass_iff δ e j hj he E a).mp ha)
  · intro a
    obtain ⟨E, hE⟩ := hsurj (e.symm a)
    exact ⟨E, (hasCEClass_iff δ e j hj he E a).mpr hE⟩
  · intro E F
    rw [hequiv E F]
    constructor
    · rintro ⟨a, hE, hF⟩
      exact ⟨e a, (hasCEClass_iff δ e j hj he E _).mpr (by simpa using hE),
        (hasCEClass_iff δ e j hj he F _).mpr (by simpa using hF)⟩
    · rintro ⟨a, hE, hF⟩
      exact ⟨e.symm a, (hasCEClass_iff δ e j hj he E a).mp hE,
        (hasCEClass_iff δ e j hj he F a).mp hF⟩
  · intro E
    rw [hsplit E, hasCEClass_iff δ e j hj he, map_zero]
  · intro E s c hc
    exact ⟨j c, hj c, s, c, j c, hc, hj c, rfl⟩

theorem classification_spec :
    Specs.LieAlgebrasAndRepresentations.AbelianExtensions.classificationStatement.{u,v,w,z,z'} k g M :=
  classification_of_comparisons lowClassification_spec ceComparison_spec

end LieAlgebrasAndRepresentations.AbelianExtensions
