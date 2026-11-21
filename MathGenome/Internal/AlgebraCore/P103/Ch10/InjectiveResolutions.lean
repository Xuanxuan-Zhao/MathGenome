import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.InjectiveResolutions
import MathGenome.Internal.AlgebraCore.P103.Ch02.EnoughInjectives
import MathGenome.Internal.AlgebraCore.P103.Ch10.Complexes

namespace P103.Ch10.InjectiveResolutions

open CategoryTheory P103.Specs.Ch10.InjectiveResolutions
open P103.Specs.Ch10.Complexes
noncomputable section
universe u v w
variable {R : Type u} [Ring R]

/-- One embedding, retaining its source so that the next step can use its cokernel. -/
structure Stage (R : Type u) [Ring R] where
  K : ModuleCat.{max u v} R
  E : ModuleCat.{max u v} R
  i : K →ₗ[R] E
  injective_i : Function.Injective i
  injective_E : Module.Injective R E

/-- An injective ambient module for a fixed source. -/
structure IntoInjective (M : ModuleCat.{max u v} R) where
  E : ModuleCat.{max u v} R
  i : M →ₗ[R] E
  injective_i : Function.Injective i
  injective_E : Module.Injective R E

/-- The sole choice at each step is supplied by enough injectives. -/
def chooseEmbedding (M : ModuleCat.{max u v} R) : IntoInjective M := Classical.choice (by
  obtain ⟨E, hE, mE, i, hi, hI⟩ := P103.Ch02.EnoughInjectives.leftEmbedding R M
  exact ⟨IntoInjective.mk (ModuleCat.of R E) i hi hI⟩)

def embed (M : ModuleCat.{max u v} R) : Stage.{u,v} R where
  K := M
  E := (chooseEmbedding M).E
  i := (chooseEmbedding M).i
  injective_i := (chooseEmbedding M).injective_i
  injective_E := (chooseEmbedding M).injective_E

/-- Start at M and then repeatedly embed the preceding cokernel. -/
def tower (M : ModuleCat.{max u v} R) : ℕ → Stage.{u,v} R
  | 0 => embed M
  | n + 1 => embed (ModuleCat.of R
      ((tower M n).E ⧸ LinearMap.range (tower M n).i))

def differential (M : ModuleCat.{max u v} R) (n : ℕ) :
    (tower M n).E →ₗ[R] (tower M (n + 1)).E :=
  (tower M (n + 1)).i.comp (LinearMap.range (tower M n).i).mkQ

/-- The new embedding does not change the kernel of the cokernel projection. -/
theorem exact_embedding_differential (M : ModuleCat.{max u v} R) (n : ℕ) :
    Function.Exact (tower M n).i (differential M n) := by
  exact (tower M (n + 1)).injective_i.comp_exact_iff_exact.mpr
    (LinearMap.exact_map_mkQ_range (tower M n).i)

/-- Surjectivity onto the cokernel identifies the preceding image with the
image of its embedding. Thus each image is the next kernel. -/
theorem exact_differentials (M : ModuleCat.{max u v} R) (n : ℕ) :
    Function.Exact (differential M n) (differential M (n + 1)) := by
  exact (LinearMap.range (tower M n).i).mkQ_surjective.comp_exact_iff_exact.mpr
    (exact_embedding_differential M (n + 1))

def resolutionComplex (M : ModuleCat.{max u v} R) :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.of (fun n => (tower M n).E)
    (fun n => ModuleCat.ofHom (differential M n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact (exact_differentials M n).linearMap_comp_eq_zero)

@[simp] theorem resolutionComplex_d (M : ModuleCat.{max u v} R) (n : ℕ) :
    (resolutionComplex M).d n (n + 1) = ModuleCat.ofHom (differential M n) :=
  CochainComplex.of_d (fun k => (tower M k).E)
    (fun k => ModuleCat.ofHom (differential M k)) n

/-- Construction for any universe of modules: first lift A to the common
universe, then use successive cokernels. -/
def resolution (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A] :
    Resolution R A where
  complex := resolutionComplex (ModuleCat.of R (ULift.{u} A))
  injectiveTerm n := (tower (ModuleCat.of R (ULift.{u} A)) n).injective_E
  η := (tower (ModuleCat.of R (ULift.{u} A)) 0).i.comp
    (ULift.moduleEquiv.symm.toLinearMap : A →ₗ[R] ULift.{u} A)
  injective_η := (tower (ModuleCat.of R (ULift.{u} A)) 0).injective_i.comp
    ULift.moduleEquiv.symm.injective
  exact_zero := by
    rw [show 1 = 0 + 1 from rfl, resolutionComplex_d]
    exact ((ULift.moduleEquiv.symm : A ≃ₗ[R] ULift.{u} A).surjective.comp_exact_iff_exact
      (f := (tower (ModuleCat.of R (ULift.{u} A)) 0).i)
      (g := differential (ModuleCat.of R (ULift.{u} A)) 0)).mpr
      (exact_embedding_differential (ModuleCat.of R (ULift.{u} A)) 0)
  exact_succ n := by
    rw [resolutionComplex_d, show n + 2 = (n + 1) + 1 from rfl, resolutionComplex_d]
    exact exact_differentials (ModuleCat.of R (ULift.{u} A)) n

theorem existsResolution : existsResolutionType.{u,v} := by
  intro R _ A _ _
  exact ⟨resolution R A⟩

/-- With the augmentation deleted there is no incoming differential in
nonnegative degree zero. -/
theorem cycleBoundaries_zero (C : CochainComplex (ModuleCat.{w} R) ℕ) :
    cycleBoundaries C 0 = ⊥ := by
  ext z
  simp [cycleBoundaries, boundaries, CochainComplex.prev_nat_zero]

/-- Exactness at I⁰ identifies A with the cycles, and the boundary quotient
in degree zero is the quotient by zero. -/
theorem homologyZero : homologyZeroType.{u,v} := by
  intro R _ A _ _ I
  have hbij : Function.Bijective I.augmentationCycles := by
    constructor
    · intro a b h
      exact I.injective_η (congrArg Subtype.val h)
    · intro z
      have hz := z.property
      change (I.complex.d 0 ((ComplexShape.up ℕ).next 0)).hom z.val = 0 at hz
      rw [CochainComplex.next] at hz
      obtain ⟨a, ha⟩ := (I.exact_zero z.val).mp hz
      exact ⟨a, Subtype.ext ha⟩
  let e := LinearEquiv.ofBijective I.augmentationCycles hbij
  let q := (cycleBoundaries I.complex 0).quotEquivOfEqBot (cycleBoundaries_zero I.complex)
  exact ⟨e.trans q.symm, rfl⟩

/-- At every positive degree exactness says that every cycle is a boundary. -/
theorem positiveHomology : positiveHomologyType.{u,v} := by
  intro R _ A _ _ I n
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro z _
  change z.val ∈ LinearMap.range (I.complex.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)).hom
  rw [CochainComplex.prev_nat_succ]
  apply (I.exact_succ n z.val).mp
  have hz := z.property
  change (I.complex.d (n + 1) ((ComplexShape.up ℕ).next (n + 1))).hom z.val = 0 at hz
  rw [CochainComplex.next] at hz
  exact hz

/-- The degree-zero identification is natural for arbitrary commuting
augmentation squares, hence for every comparison map when one is chosen. -/
theorem homologyZeroNaturality : homologyZeroNaturalityType.{u,v} := by
  intro R _ A B _ _ _ _ I J u f h
  ext a
  change homologyClass J.complex 0 (cyclesMap f 0 (I.augmentationCycles a)) =
    homologyClass J.complex 0 (J.augmentationCycles (u a))
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun h a

theorem rightResolution : rightResolutionType.{u,v} := by
  intro R _ A _ _
  exact existsResolution Rᵐᵒᵖ A

end
end P103.Ch10.InjectiveResolutions
