import MathGenome.Internal.LieTheoryDeepening.LieNotes.Virasoro.WittCohomology
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Virasoro.VirasoroStructure
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.UniversalCentralExtension
import Mathlib.Algebra.Module.Projective

/-! The Virasoro projection is initial among central extensions of the Witt algebra. -/

noncomputable section

open LieModule.Cohomology

namespace LieNotes.Virasoro.Vir

local notation "W" => Witt.W

variable {E : Type*} [LieRing E] [LieAlgebra ℂ E]

/-- The actual kernel, regarded as a trivial Witt module. -/
private abbrev Kernel (p : E →ₗ⁅ℂ⁆ W) :=
  TrivialLieModule ℂ W (LinearMap.ker p.toLinearMap)

private def kernelInclusion (p : E →ₗ⁅ℂ⁆ W) : Kernel p →ₗ[ℂ] E :=
  (LinearMap.ker p.toLinearMap).subtype ∘ₗ (TrivialLieModule.equiv ℂ W _).toLinearMap

private theorem kernelInclusion_injective (p : E →ₗ⁅ℂ⁆ W) :
    Function.Injective (kernelInclusion p) :=
  Subtype.val_injective

private theorem kernelInclusion_zero (p : E →ₗ⁅ℂ⁆ W) (k : Kernel p) :
    p (kernelInclusion p k) = 0 :=
  (TrivialLieModule.equiv ℂ W _ k).property

private theorem lie_add_kernel (p : E →ₗ⁅ℂ⁆ W)
    (hc : ∀ x y : E, p y = 0 → ⁅x, y⁆ = 0)
    (x y a b : E) (ha : p a = 0) (hb : p b = 0) :
    ⁅x + a, y + b⁆ = ⁅x, y⁆ := by
  rw [add_lie, lie_add, hc x b hb, add_zero, ← lie_skew a (y + b),
    hc (y + b) a ha, neg_zero, add_zero]

private def sectionDefect (p : E →ₗ⁅ℂ⁆ W) (s : W →ₗ[ℂ] E)
    (hs : ∀ x, p (s x) = x) : twoCochain ℂ W (Kernel p) := by
  letI : LieRing (Module.End ℂ E) := LieRing.ofAssociativeRing
  letI : LieRing (Module.End ℂ W) := LieRing.ofAssociativeRing
  let defect : W →ₗ[ℂ] W →ₗ[ℂ] E :=
    ((LieAlgebra.ad ℂ E).toLinearMap.compl₂ s).comp s -
      (LieAlgebra.ad ℂ W).toLinearMap.compr₂ s
  have hdefect (x y : W) : defect x y ∈ LinearMap.range (kernelInclusion p) := by
    have hk : p (defect x y) = 0 := by
      change p (⁅s x, s y⁆ - s ⁅x, y⁆) = 0
      rw [map_sub, p.map_lie, hs, hs, hs, sub_self]
    exact ⟨(TrivialLieModule.equiv ℂ W _).symm ⟨defect x y, hk⟩, by
      exact congrArg Subtype.val ((TrivialLieModule.equiv ℂ W _).apply_symm_apply _)⟩
  refine ⟨LinearMap.codRestrict₂ defect (kernelInclusion p)
    (kernelInclusion_injective p) hdefect, fun x => ?_⟩
  apply kernelInclusion_injective p
  rw [LinearMap.codRestrict₂_apply, map_zero]
  change ⁅s x, s x⁆ - s ⁅x, x⁆ = 0
  rw [lie_self, lie_self, map_zero, sub_self]

private theorem sectionDefect_apply (p : E →ₗ⁅ℂ⁆ W) (s : W →ₗ[ℂ] E)
    (hs : ∀ x, p (s x) = x) (x y : W) :
    kernelInclusion p (sectionDefect p s hs x y) = ⁅s x, s y⁆ - s ⁅x, y⁆ :=
  LinearMap.codRestrict₂_apply _ _ _ _ x y

private theorem sectionDefect_isCocycle (p : E →ₗ⁅ℂ⁆ W)
    (hc : ∀ x y : E, p y = 0 → ⁅x, y⁆ = 0)
    (s : W →ₗ[ℂ] E) (hs : ∀ x, p (s x) = x) :
    sectionDefect p s hs ∈ twoCocycle ℂ W (Kernel p) := by
  apply (mem_twoCocycle_iff_of_trivial ℂ W _ _).mpr
  have hsbr (x y : W) :
      ⁅s x, s y⁆ = s ⁅x, y⁆ + kernelInclusion p (sectionDefect p s hs x y) := by
    rw [sectionDefect_apply]
    abel
  have hr (e : E) (x y : W) : ⁅e, s ⁅x, y⁆⁆ = ⁅e, ⁅s x, s y⁆⁆ := by
    rw [hsbr, lie_add, hc _ _ (kernelInclusion_zero p _), add_zero]
  have hl (e : E) (x y : W) : ⁅s ⁅x, y⁆, e⁆ = ⁅⁅s x, s y⁆, e⁆ := by
    rw [← lie_skew (s ⁅x, y⁆) e, ← lie_skew ⁅s x, s y⁆ e, hr]
  intro x y z
  apply kernelInclusion_injective p
  rw [map_add, sectionDefect_apply, sectionDefect_apply, sectionDefect_apply,
    hr (s x) y z, hl (s z) x y, hr (s y) x z,
    LieRing.leibniz_lie (s x) (s y) (s z), LieRing.leibniz_lie x y z, map_add]
  abel

private theorem omegaForm_eq_smul {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (z : Z) (x y : W) : omegaForm z x y = omegaForm (1 : ℂ) x y • z := by
  have h : omegaForm z =
      (omegaForm (1 : ℂ)).compr₂ ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight z) := by
    apply LinearMap.ext_basis Witt.basis Witt.basis
    intro m n
    simp [Witt.basis_apply, omegaForm_modes]
  rw [h, LinearMap.compr₂_apply, LinearMap.smulRight_apply, LinearMap.id_apply]

private theorem exists_lift (p : E →ₗ⁅ℂ⁆ W) (hp : Function.Surjective p)
    (hc : ∀ x y : E, p y = 0 → ⁅x, y⁆ = 0) :
    ∃ f : Vir →ₗ⁅ℂ⁆ E, p.comp f = proj := by
  obtain ⟨s, hs⟩ := p.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hp)
  have hs_apply (x : W) : p (s x) = x :=
    DFunLike.congr_fun hs x
  let c : twoCocycle ℂ W (Kernel p) :=
    ⟨sectionDefect p s hs_apply, sectionDefect_isCocycle p hc s hs_apply⟩
  obtain ⟨z, ⟨φ, hφ⟩, _⟩ := witt_cocycle_classification c
  let t := s + (kernelInclusion p).comp φ
  have ht (x : W) : p (t x) = x := by
    change p (s x + kernelInclusion p (φ x)) = x
    rw [map_add, hs_apply, kernelInclusion_zero, add_zero]
  have ht_lie (x y : W) :
      ⁅t x, t y⁆ = t ⁅x, y⁆ + omegaForm (1 : ℂ) x y • kernelInclusion p z := by
    have h := hφ x y
    rw [d₁₂_apply_apply_ofTrivial] at h
    have hi := congrArg (kernelInclusion p) h
    change kernelInclusion p (sectionDefect p s hs_apply x y + -φ ⁅x, y⁆) =
      kernelInclusion p (omegaForm z x y) at hi
    rw [map_add, map_neg, sectionDefect_apply, omegaForm_eq_smul, map_smul] at hi
    change ⁅s x + kernelInclusion p (φ x), s y + kernelInclusion p (φ y)⁆ =
      (s ⁅x, y⁆ + kernelInclusion p (φ ⁅x, y⁆)) +
        omegaForm (1 : ℂ) x y • kernelInclusion p z
    rw [lie_add_kernel p hc _ _ _ _ (kernelInclusion_zero p _) (kernelInclusion_zero p _),
      ← hi]
    abel
  let centralMap : ℂ →ₗ[ℂ] E := (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (kernelInclusion p z)
  have hcentral (a : ℂ) : p (centralMap a) = 0 := by
    change p (a • kernelInclusion p z) = 0
    rw [map_smul, kernelInclusion_zero, smul_zero]
  let f : Vir →ₗ⁅ℂ⁆ E :=
    { toLinearMap := (t.coprod centralMap).comp coordinates.toLinearMap
      map_lie' := by
        intro x y
        change t (coordinates ⁅x, y⁆).1 + centralMap (coordinates ⁅x, y⁆).2 =
          ⁅t (coordinates x).1 + centralMap (coordinates x).2,
            t (coordinates y).1 + centralMap (coordinates y).2⁆
        rw [coordinates_lie, lie_add_kernel p hc _ _ _ _ (hcentral _) (hcentral _)]
        exact (ht_lie (coordinates x).1 (coordinates y).1).symm }
  refine ⟨f, LieHom.ext fun x => ?_⟩
  change p (t (coordinates x).1 + centralMap (coordinates x).2) = (coordinates x).1
  rw [map_add, ht, hcentral, add_zero]

private theorem lift_unique (p : E →ₗ⁅ℂ⁆ W)
    (hc : ∀ x y : E, p y = 0 → ⁅x, y⁆ = 0)
    (f g : Vir →ₗ⁅ℂ⁆ E) (hf : p.comp f = proj) (hg : p.comp g = proj) : f = g := by
  let d := f.toLinearMap - g.toLinearMap
  have hd (x : Vir) : p (d x) = 0 := by
    change p (f x - g x) = 0
    rw [map_sub, sub_eq_zero]
    exact (DFunLike.congr_fun hf x).trans (DFunLike.congr_fun hg x).symm
  have hg_add (x : Vir) : g x + d x = f x := by
    change g x + (f x - g x) = f x
    abel
  have hbr (x y : Vir) : d ⁅x, y⁆ = 0 := by
    change f ⁅x, y⁆ - g ⁅x, y⁆ = 0
    rw [f.map_lie, g.map_lie, sub_eq_zero, ← hg_add x, ← hg_add y]
    exact lie_add_kernel p hc _ _ _ _ (hd x) (hd y)
  have hker : (⊤ : Submodule ℂ Vir) ≤ LinearMap.ker d := by
    rw [← span_brackets_eq_top, Submodule.span_le]
    rintro _ ⟨x, y, rfl⟩
    exact hbr x y
  exact LieHom.ext fun x => sub_eq_zero.mp (hker (Submodule.mem_top (x := x)))

/-- Every complex central extension of Witt admits a unique Lie lift from Virasoro. -/
theorem existsUnique_lift (p : E →ₗ⁅ℂ⁆ W) (hp : Function.Surjective p)
    (hc : ∀ x y : E, p y = 0 → ⁅x, y⁆ = 0) :
    ∃! f : Vir →ₗ⁅ℂ⁆ E, p.comp f = proj :=
  let ⟨f, hf⟩ := exists_lift p hp hc
  ⟨f, hf, fun g hg => lift_unique p hc g f hg hf⟩

theorem universal_property : VirasoroSpec.UniversalProperty := by
  intro E _ _ p hp hc
  obtain ⟨f, hf, huniq⟩ := existsUnique_lift p hp hc
  refine ⟨f.toLinearMap, ⟨congrArg LieHom.toLinearMap hf, fun x y => f.map_lie x y⟩, ?_⟩
  rintro g ⟨hg, hbr⟩
  let g' : Vir →ₗ⁅ℂ⁆ E := { toLinearMap := g, map_lie' := hbr _ _ }
  have hg' : p.comp g' = proj :=
    LieHom.ext fun x => DFunLike.congr_fun hg x
  exact congrArg LieHom.toLinearMap (huniq g' hg')

/-- The canonical projection has central kernel. -/
theorem proj_central_kernel : VirasoroSpec.ProjectionCentralKernel := by
  intro x y hy
  obtain ⟨a, rfl⟩ := (proj_eq_zero_iff y).mp hy
  change ⁅x, a • C⁆ = 0
  rw [lie_smul, ← lie_skew x C, lie_C, neg_zero, smul_zero]

end LieNotes.Virasoro.Vir

namespace LieNotes.Virasoro

/-- The full Virasoro theorem, on the Laurent derivation model of Witt. -/
theorem virasoro_theorem : VirasoroSpec.TheoremKM11 :=
  ⟨omegaForm_modes, exists_omega, witt_cocycle_classification, witt_scalar_cohomology_dimension,
    Vir.lie_L, Vir.lie_C, Vir.mem_center_iff_mem_span, Vir.span_brackets_eq_top,
    Vir.canonicalLieProjection, Vir.proj_surjective, Vir.proj_central_kernel,
    Vir.universal_property⟩

end LieNotes.Virasoro
