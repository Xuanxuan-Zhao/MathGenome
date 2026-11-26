import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
import MathGenome.Internal.AlgebraCore.P103.Ch06.FiniteColength
import MathGenome.Internal.AlgebraCore.P103.Ch11.TorBalance
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalDimension
import MathGenome.Internal.AlgebraCore.P103.Ch12.DerivedLocalization
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Resolution

noncomputable section

open CategoryTheory
open scoped TensorProduct
open P103.Specs.Ch10.Comparison (LeftResolution ProjectiveChoice)
open P103.Specs.Ch11.TorBalance (commRightFunctor commRightProjectiveChoice)
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch12.TorBaseChange (commutativeTor coefficientComplex)
open P103.Specs.Ch12.DerivedLocalization (localizationEquiv localizedResolution localizedTor)
open P103.Ch11.ExtTorDefinitions (resolutionFamily torMaps)
open P103.Ch11.TorBalance (torModule_smul_map torSymmetryLinearEquiv)
open P103.Ch12.TorBaseChange
open P103.Ch12.DerivedLocalization (localized_projective)

namespace CommutativeAlgebraNotes.Intersection.IsolatedTorSupport

universe u v w
variable {R : Type u} [CommRing R]

/-- The shared ordinary Tor module. -/
abbrev Tor (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (i : ℕ) : Type _ :=
  Specs.Tor M N i

theorem tensor_support (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] :
    Module.support R (M ⊗[R] N) = Module.support R M ∩ Module.support R N := by
  ext p
  let k := p.asIdeal.ResidueField
  let e := TensorProduct.AlgebraTensorModule.distribBaseChange R k M N
  change _ ↔ p ∈ Module.support R M ∧ p ∈ Module.support R N
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct p,
    e.nontrivial_congr,
    _root_.AdvCommAlg.CohenMacaulay.nontrivial_tensorProduct_iff_of_field,
    ← Module.mem_support_iff_nontrivial_residueField_tensorProduct p,
    ← Module.mem_support_iff_nontrivial_residueField_tensorProduct p]

theorem tensor_nontrivial [IsLocalRing R] (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N] :
    Nontrivial (M ⊗[R] N) := by
  apply (Module.nonempty_support_iff (R := R)).mp
  rw [tensor_support M N]
  exact ⟨IsLocalRing.closedPoint R, IsLocalRing.closedPoint_mem_support R M,
    IsLocalRing.closedPoint_mem_support R N⟩

theorem finite_length_iff_support [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] :
    IsFiniteLength R M ↔ Module.support R M ⊆ {IsLocalRing.closedPoint R} := by
  rcases subsingleton_or_nontrivial M with h | h
  · rw [Module.support_eq_empty]
    exact ⟨fun _ => Set.empty_subset _, fun _ => IsFiniteLength.of_subsingleton⟩
  · have hpt : {IsLocalRing.closedPoint R} ⊆ Module.support R M :=
      Set.singleton_subset_iff.mpr (IsLocalRing.closedPoint_mem_support R M)
    exact (P103.Ch06.FiniteColength.support_singleton_iff_finite_length R M).symm.trans
      ⟨fun he => he.le, fun hs => hs.antisymm hpt⟩

theorem isolated_tensor_iff [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] :
    IsFiniteLength R (M ⊗[R] N) ↔
      Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R} := by
  rw [← tensor_support M N]
  exact finite_length_iff_support (ModuleCat.of R (M ⊗[R] N))

private def resolutionEquiv (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{w} R)
    (P Q : ProjectiveChoice Rᵐᵒᵖ A) (i : ℕ) :
    letI := torModule (torMaps i) P B
    letI := torModule (torMaps i) Q B
    TorWith P.val B i ≃ₗ[R] TorWith Q.val B i := by
  let E : TorMaps.{u,v,w} R i := torMaps i
  letI := torModule E P B
  letI := torModule E Q B
  refine
    { toFun := E.map P Q (𝟙 A) (𝟙 B)
      invFun := E.map Q P (𝟙 A) (𝟙 B)
      left_inv := ?_
      right_inv := ?_
      map_add' := (E.map P Q (𝟙 A) (𝟙 B)).map_add
      map_smul' := P103.Ch11.ExtTorDefinitions.tor_linear R i E P Q (𝟙 A) (𝟙 B) }
  · intro x
    have h := E.comp P Q P (𝟙 A) (𝟙 A) (𝟙 B) (𝟙 B)
    rw [Category.id_comp, Category.id_comp, E.id] at h
    exact (LinearMap.congr_fun h x).symm
  · intro x
    have h := E.comp Q P Q (𝟙 A) (𝟙 A) (𝟙 B) (𝟙 B)
    rw [Category.id_comp, Category.id_comp, E.id] at h
    exact (LinearMap.congr_fun h x).symm

/-- Compute the canonical Tor from any projective resolution of the first module. -/
def torLeftEquiv (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (P : LeftResolution R M) (hP : P.IsProjective) (i : ℕ) :
    Tor M N i ≃ₗ[R] commutativeTor P N i := by
  let A := (commRightFunctor R).obj M
  let Q : ProjectiveChoice Rᵐᵒᵖ A := commRightProjectiveChoice (A := M) ⟨P, hP⟩
  letI := torModule (torMaps i) Q N
  refine (resolutionEquiv A N (resolutionFamily Rᵐᵒᵖ A) Q i).trans
    { torBridgeEquiv (S := R) P N i with map_smul' := ?_ }
  intro r z
  rw [torModule_smul_map (torMaps i) Q N]
  exact torBridgeEquiv_scalar (S := R) P N i r z

theorem tor_compute_left : Specs.torComputeLeft.{u,v,w} :=
  fun {_} _ M N P hP i => ⟨torLeftEquiv M N P hP i⟩

/-- Symmetry of canonical Tor, through the balanced tensor comparison. -/
def torSymmetryEquiv (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (i : ℕ) :
    Tor M N i ≃ₗ[R] Tor N M i := by
  let A := (commRightFunctor R).obj M
  let B := (commRightFunctor R).obj N
  let P := resolutionFamily R M
  let Q := resolutionFamily R N
  let E := torSymmetryLinearEquiv (P103.Ch11.TorBalance.tor_symmetry R).some
    i (torMaps i) (torMaps i) M N P Q
  exact (resolutionEquiv A N (resolutionFamily Rᵐᵒᵖ A) (commRightProjectiveChoice P) i).trans
    (E.trans (resolutionEquiv B M (commRightProjectiveChoice Q) (resolutionFamily Rᵐᵒᵖ B) i))

theorem tor_symmetry : Specs.torSymmetry.{u,v,w} :=
  fun {_} _ M N i => ⟨torSymmetryEquiv M N i⟩

/-- Compute the same Tor from a projective resolution of the second module. -/
def torRightEquiv (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (Q : LeftResolution R N) (hQ : Q.IsProjective) (i : ℕ) :
    Tor M N i ≃ₗ[R] commutativeTor Q M i :=
  (torSymmetryEquiv M N i).trans (torLeftEquiv N M Q hQ i)

theorem tor_compute_right : Specs.torComputeRight.{u,v,w} :=
  fun {_} _ M N Q hQ i => ⟨torRightEquiv M N Q hQ i⟩

/-- Degree zero is the original tensor product. -/
def torZeroEquiv (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) :
    Tor M N 0 ≃ₗ[R] M ⊗[R] N := by
  let A := (commRightFunctor R).obj M
  letI : Module Rᵐᵒᵖ M := P103.BalancedTensor.commRightModule R M
  letI : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  exact (P103.Ch11.ExtTorDefinitions.torZeroLinear R (torMaps 0)
    (resolutionFamily Rᵐᵒᵖ A) N).trans
      (P103.BalancedTensor.commLinearEquiv (K := R) (A := M) (B := N))

/-- Tor in degree zero is computed by the two coefficient modules. -/
theorem tor_zero : Specs.torZero.{u,v,w} :=
  fun {_} _ M N => ⟨torZeroEquiv M N⟩

/-- Flat scalar extension commutes with canonical Tor using the extension of
the chosen projective resolution. -/
def flatTorBaseChangeEquiv {S : Type u} [CommRing S] [Algebra R S] [Module.Flat R S]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (P : LeftResolution R M)
    (hP : P.IsProjective) (i : ℕ) :
    S ⊗[R] Tor M N i ≃ₗ[S] Tor (ModuleCat.of S (S ⊗[R] M)) (ModuleCat.of S (S ⊗[R] N)) i :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
    (torLeftEquiv M N P hP i)).trans
      (((flat_base_change.{u,v,w} R S).some.second P N i).trans
        (torLeftEquiv (ModuleCat.of S (S ⊗[R] M)) (ModuleCat.of S (S ⊗[R] N))
          (extendedResolution (S := S) P) (extendedResolution_projective P hP) i).symm)

theorem flat_tor_base_change : Specs.flatTorBaseChange.{u,v,w} :=
  fun {_ _} _ _ _ _ M N P hP i => ⟨flatTorBaseChangeEquiv M N P hP i⟩

private def localizedEquiv (T : Submonoid R)
    {U : Type*} {V : Type*} [AddCommGroup U] [AddCommGroup V] [Module R U] [Module R V]
    (e : U ≃ₗ[R] V) :
    LocalizedModule T U ≃ₗ[Localization T] LocalizedModule T V :=
  (localizationEquiv T U).symm.trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Localization T) (Localization T))
      e).trans (localizationEquiv T V))

/-- Localization identifies canonical Tor with the homology of the termwise
localized projective resolution with localized coefficients. -/
def torLocalizedHomologyEquiv (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (P : LeftResolution R M) (hP : P.IsProjective) (T : Submonoid R) (i : ℕ) :
    LocalizedModule T (Tor M N i) ≃ₗ[Localization T] localizedTor T P N i :=
  (localizedEquiv T (torLeftEquiv M N P hP i)).trans
    (P103.Ch12.DerivedLocalization.torComparison T
      (flat_base_change.{u,v,w} R (Localization T)).some P N i)

/-- Localization commutes with the canonical Tor. -/
def torLocalizationEquiv (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (T : Submonoid R) (i : ℕ) :
    LocalizedModule T (Tor M N i) ≃ₗ[Localization T]
      Tor (ModuleCat.of (Localization T) (LocalizedModule T M))
        (ModuleCat.of (Localization T) (LocalizedModule T N)) i := by
  let P := resolutionFamily R M
  exact (torLocalizedHomologyEquiv M N P.val P.property T i).trans
    (torLeftEquiv (ModuleCat.of _ (LocalizedModule T M))
      (ModuleCat.of _ (LocalizedModule T N)) (localizedResolution T P.val)
      (localized_projective T P.val P.property) i).symm

theorem tor_localization : Specs.torLocalization.{u,v,w} :=
  fun {_} _ M N T i => ⟨torLocalizationEquiv M N T i⟩

private theorem tor_support_right (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (i : ℕ) : Module.support R (Tor M N i) ⊆ Module.support R N := by
  intro p
  contrapose
  simp only [Module.notMem_support_iff]
  intro hN
  let T := p.asIdeal.primeCompl
  let P := resolutionFamily R M
  have : Subsingleton (LocalizedModule T N) := hN
  let C := coefficientComplex (S := Localization T) (localizedResolution T P.val).complex
    (LocalizedModule T N)
  have : Subsingleton (C.X i) := by
    change Subsingleton (LocalizedModule T N ⊗[Localization T] (localizedResolution T P.val).complex.X i)
    infer_instance
  have : Subsingleton (P103.Specs.Ch10.Complexes.cycles C i) :=
    Subtype.coe_injective.subsingleton
  have : Subsingleton (localizedTor T P.val N i) := by
    change Subsingleton (P103.Specs.Ch10.Complexes.Homology C i)
    infer_instance
  exact (torLocalizedHomologyEquiv M N P.val P.property T i).injective.subsingleton

theorem tor_support (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (i : ℕ) :
    Module.support R (Tor M N i) ⊆ Module.support R M ∩ Module.support R N := by
  refine Set.subset_inter ?_ (tor_support_right M N i)
  rw [(torSymmetryEquiv M N i).support_eq]
  exact tor_support_right N M i

theorem homology_finite [IsNoetherianRing R] (M : ModuleCat.{v} R)
    (N : ModuleCat.{w} R) [Module.Finite R N] (P : LeftResolution R M)
    (hP : ∀ j, Module.Finite R (P.complex.X j)) (i : ℕ) :
    Module.Finite R (commutativeTor P N i) := by
  let C := coefficientComplex (S := R) P.complex N
  let := hP i
  have : Module.Finite R (C.X i) :=
    inferInstanceAs (Module.Finite R (N ⊗[R] P.complex.X i))
  change Module.Finite R (P103.Specs.Ch10.Complexes.Homology C i)
  infer_instance

/-- Finiteness uses degreewise finite free resolutions over a Noetherian ring. -/
theorem tor_finite [IsNoetherianRing R] (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] (i : ℕ) : Module.Finite R (Tor M N i) := by
  obtain ⟨P, hfree, hfin⟩ := P103.Ch12.ExtBaseChange.exists_finite_free_resolution R M
  let := homology_finite M N P hfin i
  exact Module.Finite.equiv
    (torLeftEquiv M N P (P103.Ch10.ProjectiveResolutions.free_is_projective R M P hfree) i).symm

theorem tor_finite_length [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) [Module.Finite R M] [Module.Finite R N]
    (h : Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R})
    (i : ℕ) : IsFiniteLength R (Tor M N i) := by
  let := tor_finite M N i
  exact (finite_length_iff_support (ModuleCat.of R (Tor M N i))).mpr ((tor_support M N i).trans h)

theorem tor_finite_length_of_tensor [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) [Module.Finite R M] [Module.Finite R N]
    (h : IsFiniteLength R (M ⊗[R] N)) (i : ℕ) : IsFiniteLength R (Tor M N i) :=
  tor_finite_length M N ((isolated_tensor_iff M N).mp h) i

section Koszul

open _root_.AdvCommAlg.Koszul
open P103.Specs.Ch10.Complexes (Homology cycleBoundaries)

/-- The explicit quotient and the categorical homology use the same
differentials and the same submodule of boundaries inside the cycles. -/
private def categoricalHomologyEquiv (C : ChainComplex (ModuleCat.{v} R) ℕ) (i : ℕ) :
    C.homology i ≃ₗ[R] Homology C i := by
  let CS := C.sc i
  have h : LinearMap.range CS.moduleCatToCycles = cycleBoundaries C i := by
    exact LinearMap.range_codRestrict _ _ _
  exact CS.moduleCatHomologyIso.toLinearEquiv.trans
    (Submodule.quotEquivOfEq _ _ h)

private def ordinaryKoszulResolution (x : List R) (hx : RingTheory.Sequence.IsRegular R x) :
    LeftResolution R (R ⧸ listIdeal x) where
  complex := (koszulResolution x hx).complex
  ε := (augmentationZero x).hom
  surjective := augmentationZero_surjective x
  exact_zero := (augmentation_exact x).moduleCat_range_eq_ker
  exact_succ n := by
    have h := listComplex_exactAt x hx.toIsWeaklyRegular (n + 1) (Nat.succ_pos n)
    have he := (HomologicalComplex.exactAt_iff' (K := listComplex x)
      (i := n + 2) (j := n + 1) (k := n)
      (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n)).mp h
    exact he.moduleCat_range_eq_ker

private def koszulTensorOrderIso (N : ModuleCat.{w} R)
    (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    (tensorComplexFunctor.{u,w} C).obj N ≅
      P103.Specs.Ch12.TorBaseChange.coefficientComplex.{u,u,w} (S := R) C N :=
  HomologicalComplex.Hom.isoOfComponents (fun j => (TensorProduct.comm R (C.X j) N).toModuleIso)
    (by
      intro j k _
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a b
      rfl)

/-- Compare the Koszul library's derived Tor to our canonical Tor using
the very same Koszul projective resolution and a termwise tensor flip. -/
def koszulTorModelEquiv (N : ModuleCat.{w} R) (x : List R)
    (hx : RingTheory.Sequence.IsRegular R x) (i : ℕ) :
    ((quotientTorFunctor (listIdeal x) i).obj N) ≃ₗ[R]
      Tor (ModuleCat.of R (R ⧸ listIdeal x)) N i := by
  let P := ordinaryKoszulResolution x hx
  have hp : P.IsProjective := fun j => by
    let := (listComplex_finiteFree x j).1
    change Module.Projective R ((listComplex x).X j)
    infer_instance
  let C := P103.Specs.Ch12.TorBaseChange.coefficientComplex.{u,u,w} (S := R) P.complex N
  let e₁ : ((quotientTorFunctor (listIdeal x) i).obj N) ≃ₗ[R]
      ((tensorComplexFunctor P.complex).obj N).homology i :=
    ((resolutionTorIso (listIdeal x) (koszulResolution x hx) i).app N).symm.toLinearEquiv
  let e₂ : ((tensorComplexFunctor P.complex).obj N).homology i ≃ₗ[R] C.homology i :=
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (koszulTensorOrderIso N P.complex)).toLinearEquiv
  let e₃ : C.homology i ≃ₗ[R] commutativeTor P N i := categoricalHomologyEquiv C i
  exact e₁.trans (e₂.trans (e₃.trans
    (torLeftEquiv (ModuleCat.of R (R ⧸ listIdeal x)) N P hp i).symm))

theorem koszul_tor_model : Specs.koszulTorModel.{u,w} :=
  fun {_} _ N x hx i => ⟨koszulTorModelEquiv N x hx i⟩

/-- Koszul homology of a regular list with coefficients computes canonical Tor. -/
def koszulHomologyTorEquiv (N : ModuleCat.{w} R) (x : List R)
    (hx : RingTheory.Sequence.IsRegular R x) (i : ℕ) :
    homology N x i ≃ₗ[R] Tor (ModuleCat.of R (R ⧸ listIdeal x)) N i :=
  (homologyTorIsoAt N x hx i).toLinearEquiv.trans (koszulTorModelEquiv N x hx i)

theorem koszul_homology_tor : Specs.koszulHomologyTor.{u,w} :=
  fun {_} _ N x hx i => ⟨koszulHomologyTorEquiv N x hx i⟩

end Koszul

end CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
