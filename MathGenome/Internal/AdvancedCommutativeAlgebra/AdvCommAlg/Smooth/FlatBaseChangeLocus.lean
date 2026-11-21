import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.PointwiseCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.FlatBaseChangeLocus
import Mathlib.RingTheory.Extension.Cotangent.BaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization

/-! SM-13. Flat base change of the smooth locus. The proof uses vanishing of
H₁ and freeness of Ω at the local rings; faithful flatness is used only on the
local map at a given prime upstairs. See Stacks, tag 00TG. -/
namespace AdvCommAlg.Smooth

noncomputable section
open TensorProduct
universe u v w

section Modules
variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Localizing a scalar extension equals scalar extension of the localization. -/
def localizedTensorEquiv (p : PrimeSpectrum S) :
    let q := p.comap (algebraMap R S)
    letI := Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
    LocalizedModule p.asIdeal.primeCompl (S ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal ⊗[Localization.AtPrime
        (p.comap (algebraMap R S)).asIdeal]
        LocalizedModule (p.comap (algebraMap R S)).asIdeal.primeCompl M := by
  let q := p.comap (algebraMap R S)
  let := Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
  exact LocalizedModule.equivTensorProduct _ _ ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange R S _ _ M ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime q.asIdeal) _ _ M).symm ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl _ _)
      (LocalizedModule.equivTensorProduct _ M).symm

/-- Flat base change detects vanishing at corresponding primes, even for
modules which are not finitely generated. -/
lemma notMem_support_baseChange [Module.Flat R S] (p : PrimeSpectrum S) :
    p ∉ Module.support S (S ⊗[R] M) ↔
      p.comap (algebraMap R S) ∉ Module.support R M := by
  let q := p.comap (algebraMap R S)
  let := Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
  have : Module.FaithfullyFlat (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime p.asIdeal) := .of_flat_of_isLocalHom
  rw [Module.notMem_support_iff, Module.notMem_support_iff,
    (localizedTensorEquiv R S M p).subsingleton_congr]
  exact ⟨fun _ => Module.FaithfullyFlat.lTensor_reflects_triviality
    (Localization.AtPrime q.asIdeal) (Localization.AtPrime p.asIdeal) _, fun _ => inferInstance⟩

/-- Freeness at a prime descends along a flat extension for finite modules. -/
lemma mem_freeLocus_baseChange [Module.Flat R S] [Module.Finite R M]
    (p : PrimeSpectrum S) :
    p ∈ Module.freeLocus S (S ⊗[R] M) ↔
      p.comap (algebraMap R S) ∈ Module.freeLocus R M := by
  let q := p.comap (algebraMap R S)
  let := Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
  have : Module.FaithfullyFlat (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime p.asIdeal) := .of_flat_of_isLocalHom
  constructor
  · intro hp
    have : Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl (S ⊗[R] M)) := hp
    have : Module.Free (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[Localization.AtPrime q.asIdeal]
          LocalizedModule q.asIdeal.primeCompl M) :=
      .of_equiv (localizedTensorEquiv R S M p)
    have : Module.Flat (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) :=
      Module.Flat.of_flat_tensorProduct (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) (Localization.AtPrime p.asIdeal)
    exact Module.free_of_flat_of_isLocalRing
  · intro hp
    exact Module.comap_freeLocus_le (R := R) (M := M) (A := S) hp

end Modules

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Homology
variable (A B T : Type*) [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Module.Flat A T]

set_option backward.isDefEq.respectTransparency false in
/-- Flat base change for H₁, expressed linearly over the target algebra. -/
def h1BaseChangeEquiv :
    ((T ⊗[A] B) ⊗[B] Algebra.H1Cotangent A B) ≃ₗ[T ⊗[A] B]
      Algebra.H1Cotangent T (T ⊗[A] B) := by
  let e₁ : ((T ⊗[A] B) ⊗[B] Algebra.H1Cotangent A B) ≃ₗ[T]
      T ⊗[A] Algebra.H1Cotangent A B :=
    IsTensorProduct.assocOfMapSMul (TensorProduct.mk A T B) (isTensorProduct _ _ _)
      (TensorProduct.mk B B (Algebra.H1Cotangent A B)) (isTensorProduct _ _ _)
      (by intros; simp [Algebra.smul_def])
      (by intros; simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]) ≪≫ₗ
    ((TensorProduct.lid B (Algebra.H1Cotangent A B)).restrictScalars A).baseChange A T _ _
  let f := (Algebra.H1Cotangent.map A T B (T ⊗[A] B)).liftBaseChange (T ⊗[A] B)
  have he₁ (t : T) (b : B) (x : Algebra.H1Cotangent A B) :
      e₁ ((t ⊗ₜ[A] b) ⊗ₜ[B] x) = t ⊗ₜ[A] (b • x) := by
    dsimp only [e₁, LinearEquiv.trans_apply]
    erw [IsTensorProduct.assocOfMapSMul_tmul]
    rfl
  have hf : f.restrictScalars T =
      (e₁ ≪≫ₗ Algebra.tensorH1CotangentOfFlat A B T).toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul z x =>
      induction z with
      | add z z' hz hz' => simp only [add_tmul, map_add, hz, hz']
      | tmul t b =>
        change (t ⊗ₜ[A] b) • Algebra.H1Cotangent.map A T B (T ⊗[A] B) x =
          Algebra.tensorH1CotangentOfFlat A B T (e₁ ((t ⊗ₜ[A] b) ⊗ₜ[B] x))
        rw [he₁, Algebra.tensorH1CotangentOfFlat_tmul, map_smul]
        rw [← IsScalarTower.algebraMap_smul (T ⊗[A] B) t,
          ← IsScalarTower.algebraMap_smul (T ⊗[A] B) b, ← mul_smul]
        congr 1
        simp [Algebra.TensorProduct.right_algebraMap_apply]
  exact LinearEquiv.ofBijective f (by
    change Function.Bijective (f.restrictScalars T)
    rw [hf]
    exact (e₁ ≪≫ₗ Algebra.tensorH1CotangentOfFlat A B T).bijective)

end Homology

/-- The comparison of smoothness at each prime upstairs (SM-13). -/
theorem isSmoothAt_flat_base_change :
    Specs.AdvCommAlg.Smooth.FlatBaseChangeLocus.pointwise.{u,v,w} := by
  intro A B T _ _ _ _ _ _ _ p
  have : Module.Flat B (T ⊗[A] B) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight A B T).symm.toLinearEquiv
  have hcompare :
      p ∈ Algebra.smoothLocus T (T ⊗[A] B) ↔
        p.comap (algebraMap B (T ⊗[A] B)) ∈ Algebra.smoothLocus A B := by
    rw [Algebra.smoothLocus_eq_compl_support_inter,
      Algebra.smoothLocus_eq_compl_support_inter]
    simp only [Set.mem_inter_iff, Set.mem_compl_iff]
    rw [← (h1BaseChangeEquiv A B T).support_eq,
      ← Module.freeLocus_congr (KaehlerDifferential.tensorKaehlerEquiv A T B (T ⊗[A] B)),
      notMem_support_baseChange B (T ⊗[A] B) (Algebra.H1Cotangent A B) p,
      mem_freeLocus_baseChange B (T ⊗[A] B) (KaehlerDifferential A B) p]
  rw [neighborhood_iff_formal T (T ⊗[A] B) p,
    neighborhood_iff_formal A B (p.comap (algebraMap B (T ⊗[A] B))),
    FormalLifting.formallySmooth_iff, FormalLifting.formallySmooth_iff]
  exact hcompare

/-- The smooth locus is exactly the inverse image under the canonical map
of spectra, with no faithful flatness assumption on the global base change. -/
theorem smoothLocus_flat_base_change :
    Specs.AdvCommAlg.Smooth.FlatBaseChangeLocus.locus.{u,v,w} := by
  intro A B T _ _ _ _ _ _ _
  ext p
  exact isSmoothAt_flat_base_change A B T p

end
end AdvCommAlg.Smooth
