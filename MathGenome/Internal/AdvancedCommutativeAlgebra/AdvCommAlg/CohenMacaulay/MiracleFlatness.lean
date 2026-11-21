import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.MiracleFlatness
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.LocalFlatnessCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Resolution

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits
open RingTheory.Sequence
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.BalancedTensor
open scoped TensorProduct
universe u
namespace AdvCommAlg.CohenMacaulay

namespace MiracleFlatness

/-- A surjection of scalar rings preserves support dimension of a finite module. -/
lemma supportDim_of_surjective_algebraMap (S T : Type u) [CommRing S] [CommRing T]
    [Algebra S T] (M : Type u) [AddCommGroup M] [Module S M] [Module T M]
    [IsScalarTower S T M] [Module.Finite S M]
    (hf : Function.Surjective (algebraMap S T)) :
    Module.supportDim S M = Module.supportDim T M := by
  letI : Module.Finite T M := Module.Finite.of_restrictScalars_finite S T M
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  let f := Ideal.quotientMap (Module.annihilator T M) (algebraMap S T)
    (Module.comap_annihilator (R₀ := S)).symm.le
  exact RingEquiv.ringKrullDim (RingEquiv.ofBijective f
    ⟨Ideal.quotientMap_injective' (Module.comap_annihilator (R₀ := S)).le,
      Ideal.quotientMap_surjective hf⟩)

/-- Dimension equality makes the images of the base generators regular. -/
lemma regular_base_generators (R S : Type u) [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsNoetherianRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (N : Type u) [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.Finite S N] [Nontrivial N]
    (hCM : LocalCohenMacaulay S N)
    (h : dimension S N = ringKrullDim R +
      Module.supportDim (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
          (⊤ : Submodule S N))))
    (x : List R) (hgen : Ideal.ofList x = IsLocalRing.maximalIdeal R)
    (hd : ringKrullDim R = (x.length : WithBot ℕ∞)) :
    IsWeaklyRegular N x := by
  have hmem : ∀ a ∈ x.map (algebraMap R S), a ∈ IsLocalRing.maximalIdeal S := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact map_nonunit (algebraMap R S) b (hgen ▸ Ideal.subset_span hb)
  apply (isWeaklyRegular_map_algebraMap_iff S N x).mp
  apply IsRegular.toIsWeaklyRegular
  apply (regular_iff_dimension N hCM (x.map (algebraMap R S)) hmem).mpr
  rw [← Ideal.map_ofList, hgen, List.length_map]
  rw [h, hd, ← supportDim_of_surjective_algebraMap S
    (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) _
    Ideal.Quotient.mk_surjective]
  exact add_comm _ _

/-- The exterior resolution, augmented to the actual residue quotient. -/
def koszulResidueResolution (R : Type u) [CommRing R] [IsLocalRing R]
    (x : List R) (hx : RegularSequence.RingRegular x)
    (hgen : Ideal.ofList x = IsLocalRing.maximalIdeal R) :
    LeftResolution R (R ⧸ IsLocalRing.maximalIdeal R) where
  complex := Koszul.listComplex x
  ε := (Submodule.quotEquivOfEq _ _ hgen).toLinearMap.comp (Koszul.augmentationZero x).hom
  surjective := (Submodule.quotEquivOfEq _ _ hgen).surjective.comp
    (Koszul.augmentationZero_surjective x)
  exact_zero := by
    have h := (Koszul.augmentation_exact x).moduleCat_range_eq_ker
    rw [h]
    ext a
    exact ((Submodule.quotEquivOfEq _ _ hgen).map_eq_zero_iff).symm
  exact_succ n := by
    exact ((HomologicalComplex.exactAt_iff' _ _ _ _
      (by simp [ChainComplex.prev]) (by simp)).mp
        (Koszul.listComplex_exactAt x hx.toIsWeaklyRegular (n+1) (by omega))).moduleCat_range_eq_ker

lemma koszulResidueResolution_projective (R : Type u) [CommRing R] [IsLocalRing R]
    (x : List R) (hx : RegularSequence.RingRegular x)
    (hgen : Ideal.ofList x = IsLocalRing.maximalIdeal R) :
    (koszulResidueResolution R x hx hgen).IsProjective := by
  intro n
  change Module.Projective R ((Koszul.listComplex x).X n)
  letI : Module.Free R ((Koszul.listComplex x).X n) := (Koszul.listComplex_finiteFree x n).1
  exact Module.Projective.of_free

/-- Comparison of the balanced tensor with the commutative tensor. -/
def balancedTensorEquiv (R : Type u) [CommRing R]
    (A B : Type u) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] :
    letI := commRightModule R A
    Tensor R A B ≃+ A ⊗[R] B := by
  letI := commRightModule R A
  letI : IsCentralScalar R A := ⟨fun _ _ => rfl⟩
  exact commAddEquiv

lemma balancedTensorEquiv_natural {R : Type u} [CommRing R]
    {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (M : Type u) [AddCommGroup M] [Module R M] (f : A →ₗ[R] B) :
    letI := commRightModule R A
    letI := commRightModule R B
    ∀ z, balancedTensorEquiv R B M (tensorMap (commRightLinear f) LinearMap.id z) =
      f.rTensor M (balancedTensorEquiv R A M z) := by
  letI := commRightModule R A
  letI := commRightModule R B
  intro z
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht a m => rfl
  | ha z t hz ht => simp only [map_add, hz, ht]

/-- Weak coefficient regularity makes the residue Tor in degree one vanish. -/
lemma koszulResidue_torOne (R : Type u) [CommRing R] [IsLocalRing R]
    (N : Type u) [AddCommGroup N] [Module R N]
    (x : List R) (hx : RegularSequence.RingRegular x)
    (hgen : Ideal.ofList x = IsLocalRing.maximalIdeal R)
    (hN : IsWeaklyRegular N x) :
    letI := commRightModule R (R ⧸ IsLocalRing.maximalIdeal R)
    Subsingleton (TorWith (commRightResolution (koszulResidueResolution R x hx hgen)) N 1) := by
  letI := commRightModule R (R ⧸ IsLocalRing.maximalIdeal R)
  have hex : (Koszul.coefficientComplex N x).ExactAt 1 := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ModuleCat.isZero_iff_subsingleton.mpr (Koszul.weaklyRegular_acyclic N x hN 1 (by omega))
  have hex' := ((HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)).mp hex)
  have he : Function.Exact
      (((Koszul.listComplex x).d 2 1).hom.rTensor N)
      (((Koszul.listComplex x).d 1 0).hom.rTensor N) := by
    exact LinearMap.exact_iff.mpr hex'.moduleCat_range_eq_ker.symm
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro z _
  letI := commRightModule R ((Koszul.listComplex x).X 0)
  letI := commRightModule R ((Koszul.listComplex x).X 1)
  letI := commRightModule R ((Koszul.listComplex x).X 2)
  let e (n : ℕ) := balancedTensorEquiv R ((Koszul.listComplex x).X n) N
  have hz : (((Koszul.listComplex x).d 1 0).hom.rTensor N) (e 1 z.val) = 0 := by
    change (((Koszul.listComplex x).d 1 0).hom.rTensor N)
      (balancedTensorEquiv R _ N z.val) = 0
    rw [← balancedTensorEquiv_natural]
    apply (e 0).map_eq_zero_iff.mpr
    have hz' := z.property
    change ((tensorComplex (commRightResolution (koszulResidueResolution R x hx hgen)).complex N).d
      1 ((ComplexShape.down ℕ).next 1)).hom z.val = 0 at hz'
    rw [show (ComplexShape.down ℕ).next 1 = 0 from ChainComplex.next_nat_succ 0] at hz'
    exact hz'
  obtain ⟨a, ha⟩ := (he _).mp hz
  change z.val ∈ boundaries _ 1
  unfold boundaries
  rw [ChainComplex.prev]
  change ∃ b, tensorMap (commRightLinear ((Koszul.listComplex x).d 2 1).hom)
    LinearMap.id b = z.val
  refine ⟨(e 2).symm a, ?_⟩
  apply (e 1).injective
  rw [balancedTensorEquiv_natural]
  exact (congrArg (((Koszul.listComplex x).d 2 1).hom.rTensor N)
    ((e 2).apply_symm_apply a)).trans ha

end MiracleFlatness

open MiracleFlatness

/-- Miracle flatness for a finite Cohen–Macaulay module over the local target. -/
theorem miracleFlatness : Specs.miracleFlatnessType.{u} := by
  intro R S _ _ _ _ _ _ _ N _ _ _ _ _ _ hCM J hdim
  obtain ⟨x, hgen, hd, hx⟩ := exists_regular_generators R
  have hN := regular_base_generators R S N hCM hdim x hgen hd
  let P := koszulResidueResolution R x hx hgen
  letI := commRightModule R (R ⧸ IsLocalRing.maximalIdeal R)
  exact (localFlatnessCriterion R S N (commRightResolution P)
    (P103.Ch11.TorBalance.commRightResolution_projective P
      (koszulResidueResolution_projective R x hx hgen))).mp
    (koszulResidue_torOne R N x hx hgen hN)

/-- Ring form of miracle flatness. -/
theorem miracleFlatnessRing : Specs.miracleFlatnessRingType.{u} := by
  intro R S _ _ _ _ _ _ _ hCM hdim
  apply miracleFlatness R S S hCM
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  have he : (S ⧸ (J • (⊤ : Submodule S S))) ≃ₗ[S] (S ⧸ J) :=
    Submodule.quotEquivOfEq _ _ (by change J * ⊤ = J; exact Ideal.mul_top _)
  change dimension S S = ringKrullDim R + Module.supportDim (S ⧸ J) _
  rw [← supportDim_of_surjective_algebraMap S (S ⧸ J) _ Ideal.Quotient.mk_surjective,
    Module.supportDim_eq_of_equiv he, Module.supportDim_quotient_eq_ringKrullDim]
  exact (Module.supportDim_self_eq_ringKrullDim S).trans hdim

end AdvCommAlg.CohenMacaulay
