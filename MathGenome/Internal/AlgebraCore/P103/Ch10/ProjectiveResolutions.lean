import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.ProjectiveResolutions
import MathGenome.Internal.AlgebraCore.P103.Ch10.Complexes
import MathGenome.Internal.AlgebraCore.P103.Ch01.FreeModules

noncomputable section
universe u v
namespace P103.Ch10.ProjectiveResolutions
open CategoryTheory
open P103.Specs.Ch10.ProjectiveResolutions
open P103.Specs.Ch10.Complexes

variable {R : Type u} [Ring R]

/-- The free cover sends the generator labelled by an element to that element. -/
def cover (M : ModuleCat.{v} R) : (M →₀ R) →ₗ[R] M :=
  Finsupp.linearCombination R id

theorem cover_surjective (M : ModuleCat.{v} R) : Function.Surjective (cover M) :=
  Finsupp.linearCombination_surjective R Function.surjective_id

/-- Successive kernels, starting from the given module (lifted only in universe). -/
def syzygy (A : Type v) [AddCommGroup A] [Module R A] : ℕ → ModuleCat.{max u v} R
  | 0 => ModuleCat.of R (ULift.{u} A)
  | n + 1 => ModuleCat.of R (LinearMap.ker (cover (syzygy A n)))

variable (A : Type v) [AddCommGroup A] [Module R A]

abbrev term (n : ℕ) := (syzygy (R := R) A n) →₀ R

def differential (n : ℕ) : term (R := R) A (n + 1) →ₗ[R] term (R := R) A n :=
  (LinearMap.ker (cover (syzygy A n))).subtype.comp (cover (syzygy A (n + 1)))

theorem differential_square (n : ℕ) :
    (differential (R := R) A n).comp (differential A (n + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  change (cover (syzygy A (n + 1)) (cover (syzygy A (n + 2)) x).val).val = 0
  exact congrArg Subtype.val (cover (syzygy A (n + 2)) x).property

def resolutionComplex : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (term (R := R) A n))
    (fun n => ModuleCat.ofHom (differential A n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact differential_square A n)

@[simp] theorem resolutionComplex_d (n : ℕ) :
    ((resolutionComplex (R := R) A).d (n + 1) n).hom = differential A n := by
  simp only [resolutionComplex, ChainComplex.of_d]
  rfl

/-- Each new image is exactly the kernel just covered. -/
theorem differential_range (n : ℕ) :
    LinearMap.range (differential (R := R) A n) =
      LinearMap.ker (cover (syzygy A n)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (cover (syzygy A (n + 1)) y).property
  · intro hx
    obtain ⟨y, hy⟩ := cover_surjective (syzygy (R := R) A (n + 1)) ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

def augmentation : term (R := R) A 0 →ₗ[R] A :=
  (ULift.moduleEquiv : ULift.{u} A ≃ₗ[R] A).toLinearMap.comp
    (cover (syzygy A 0))

theorem augmentation_surjective : Function.Surjective (augmentation (R := R) A) :=
  (ULift.moduleEquiv : ULift.{u} A ≃ₗ[R] A).surjective.comp
    (cover_surjective (syzygy A 0))

theorem augmentation_kernel : LinearMap.ker (augmentation (R := R) A) =
    LinearMap.ker (cover (syzygy A 0)) := by
  ext x
  change (cover (syzygy A 0) x).down = 0 ↔ cover (syzygy A 0) x = 0
  exact ⟨fun h => ULift.ext h, fun h => congrArg ULift.down h⟩

theorem differential_kernel (n : ℕ) : LinearMap.ker (differential (R := R) A n) =
    LinearMap.ker (cover (syzygy A (n + 1))) := by
  ext x
  change (cover (syzygy A (n + 1)) x).val = 0 ↔ cover (syzygy A (n + 1)) x = 0
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

def freeResolution : Resolution R A where
  complex := resolutionComplex A
  ε := augmentation A
  surjective := augmentation_surjective A
  exact_zero := by
    change LinearMap.range ((resolutionComplex A).d 1 0).hom = _
    simp only [resolutionComplex_d]
    change LinearMap.range (differential A 0) = LinearMap.ker (augmentation A)
    exact (differential_range A 0).trans (augmentation_kernel A).symm
  exact_succ n := by
    simp only [resolutionComplex_d]
    change LinearMap.range (differential A (n + 1)) = LinearMap.ker (differential A n)
    exact (differential_range A (n + 1)).trans (differential_kernel A n).symm

theorem exists_free_resolution : exists_free_resolutionType.{u,v} := by
  intro R _ A _ _
  refine ⟨freeResolution (R := R) A, ?_⟩
  intro n
  obtain ⟨b, _⟩ := P103.Ch01.FreeModules.standard_basis R (syzygy (R := R) A n)
  exact Module.Free.of_basis b

theorem free_is_projective : free_is_projectiveType.{u,v} := by
  intro R _ A _ _ Q hQ n
  let := hQ n
  exact Module.Projective.of_free

theorem exists_projective_resolution : exists_projective_resolutionType.{u,v} := by
  intro R _ A _ _
  obtain ⟨Q, hQ⟩ := exists_free_resolution R A
  exact ⟨Q, free_is_projective R A Q hQ⟩

/-- In the unaugmented nonnegative complex the outgoing map in degree zero
vanishes, so every element of the zeroth term is a cycle. -/
theorem mem_cycles_zero (Q : Resolution R A) (x : Q.complex.X 0) :
    x ∈ cycles Q.complex 0 := by
  change (Q.complex.d 0 ((ComplexShape.down ℕ).next 0)).hom x = 0
  rw [ChainComplex.next_nat_zero, Q.complex.shape 0 0 (by simp)]
  rfl

theorem homology_zero : homology_zeroType.{u,v} := by
  intro R _ A _ _ Q
  let g : cycles Q.complex 0 →ₗ[R] A := Q.ε.comp (cycles Q.complex 0).subtype
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨x, hx⟩ := Q.surjective a
    exact ⟨⟨x, mem_cycles_zero A Q x⟩, hx⟩
  have hk : cycleBoundaries Q.complex 0 = LinearMap.ker g := by
    ext z
    change z.val ∈ LinearMap.range (Q.complex.d ((ComplexShape.down ℕ).prev 0) 0).hom ↔
      Q.ε z.val = 0
    rw [ChainComplex.prev]
    change z.val ∈ LinearMap.range (Q.complex.d 1 0).hom ↔ Q.ε z.val = 0
    rw [Q.exact_zero]
    rfl
  refine ⟨(Submodule.quotEquivOfEq _ _ hk).trans (g.quotKerEquivOfSurjective hg), ?_⟩
  intro z
  exact LinearMap.quotKerEquivOfSurjective_apply_mk g hg z

theorem homology_succ : homology_succType.{u,v} := by
  intro R _ A _ _ Q n
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro z _
  change z.val ∈ LinearMap.range
    (Q.complex.d ((ComplexShape.down ℕ).prev (n + 1)) (n + 1)).hom
  rw [ChainComplex.prev]
  change z.val ∈ LinearMap.range (Q.complex.d (n + 2) (n + 1)).hom
  rw [Q.exact_succ]
  have hc : cycles Q.complex (n + 1) =
      LinearMap.ker (Q.complex.d (n + 1) n).hom := by
    unfold cycles
    rw [ChainComplex.next_nat_succ]
  exact hc ▸ z.property

theorem homology_zero_natural : homology_zero_naturalType.{u,v} := by
  intro R _ A B _ _ _ _ Q T f g h eQ eT hQ hT
  apply (cycleBoundaries Q.complex 0).quot_hom_ext
  intro z
  change eT (homologyMap g 0 (homologyClass Q.complex 0 z)) =
    f (eQ (homologyClass Q.complex 0 z))
  rw [P103.Ch10.Complexes.homologyMap_apply, hT, hQ]
  exact LinearMap.congr_fun h z.val

theorem right_resolution : right_resolutionType.{u,v} := by
  intro R _ A _ _
  obtain ⟨Q, hQ⟩ := exists_free_resolution Rᵐᵒᵖ A
  exact ⟨Q, hQ, free_is_projective Rᵐᵒᵖ A Q hQ,
    homology_zero Rᵐᵒᵖ A Q, homology_succ Rᵐᵒᵖ A Q⟩

end P103.Ch10.ProjectiveResolutions
