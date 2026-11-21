import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Resolution
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.RegularAcyclicity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u v
namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]

/-- Removing the tensor factor R identifies K(x;R) with K(x). -/
def coefficientRingIso (x : List R) : coefficientComplex R x ≅ listComplex x :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (TensorProduct.rid R (⋀[R]^q (Fin x.length → R))).toModuleIso)
    (by
      intro i j hij
      subst i
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a r
      simp [coefficientComplex, listComplex, complex, coefficientDifferential,
        ChainComplex.of_d, map_smul])

/-- The non-augmented Koszul complex is exact in every positive degree. -/
theorem listComplex_exactAt (x : List R) (hx : RegularSequence.WeaklyRegular R x)
    (q : ℕ) (hq : 0 < q) : (listComplex x).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hz : IsZero ((coefficientComplex R x).homology q) :=
    ModuleCat.isZero_iff_subsingleton.mpr (weaklyRegular_acyclic R x hx q hq)
  exact hz.of_iso ((HomologicalComplex.homologyFunctor _ _ q).mapIso (coefficientRingIso x)).symm

/-- The augmentation kills the degree-one differential. -/
theorem differential_augmentationZero (x : List R) :
    (listComplex x).d 1 0 ≫ augmentationZero x = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (listIdeal x).mkQ (exteriorPower.zeroEquiv R _ (differential (listForm x) 0 a)) = 0
  rw [differential_one]
  exact (Submodule.Quotient.mk_eq_zero (listIdeal x)).mpr (listForm_mem x _)

/-- The canonical augmentation to R/(x), in the category of chain complexes. -/
def augmentation (x : List R) : listComplex x ⟶
    (ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R (R ⧸ listIdeal x)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨augmentationZero x, differential_augmentationZero x⟩

@[simp] theorem augmentation_f_zero (x : List R) :
    (augmentation x).f 0 = augmentationZero x := by simp [augmentation]

/-- Surjectivity at the augmentation, also when x is empty. -/
theorem augmentationZero_surjective (x : List R) :
    Function.Surjective (augmentationZero x).hom :=
  (Submodule.mkQ_surjective _).comp (exteriorPower.zeroEquiv R _).surjective

/-- In degree zero the tensor unit comparison is the standard scalar identification. -/
theorem coefficientRingIso_zero (x : List R)
    (a : (coefficientComplex R x).X 0) :
    exteriorPower.zeroEquiv R (Fin x.length → R) ((coefficientRingIso x).hom.f 0 a) =
      coefficientZeroEquiv R x a := by
  induction a using TensorProduct.inductionOn with
  | tmul a r =>
    change exteriorPower.zeroEquiv R _ (r • a) = _
    rw [map_smul, coefficientZeroEquiv_tmul]
    exact mul_comm _ _
  | add a b ha hb =>
    change exteriorPower.zeroEquiv R _ ((TensorProduct.rid R _) (a + b)) = _
    change exteriorPower.zeroEquiv R _ ((TensorProduct.rid R _) a) = _ at ha
    change exteriorPower.zeroEquiv R _ ((TensorProduct.rid R _) b) = _ at hb
    simp only [map_add, ha, hb]

/-- Exactness of the augmented complex at its degree-zero term. -/
theorem augmentation_exact (x : List R) :
    (ShortComplex.mk _ _ (differential_augmentationZero x)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  have hm : exteriorPower.zeroEquiv R (Fin x.length → R) a ∈ listIdeal x :=
    (Submodule.Quotient.mk_eq_zero (listIdeal x)).mp ha
  have hm' : exteriorPower.zeroEquiv R (Fin x.length → R) a ∈ listSubmodule R x := by
    simpa only [listSubmodule, Ideal.smul_eq_mul, Ideal.mul_top] using hm
  rw [← degreeZeroBoundary_range R x] at hm'
  obtain ⟨z, hz⟩ := hm'
  refine ⟨(coefficientRingIso x).hom.f 1 z, ?_⟩
  apply (exteriorPower.zeroEquiv R (Fin x.length → R)).injective
  have hc := congrArg (fun f => f.hom z) ((coefficientRingIso x).hom.comm 1 0)
  change ((listComplex x).d 1 0).hom (((coefficientRingIso x).hom.f 1).hom z) =
    ((coefficientRingIso x).hom.f 0).hom (coefficientDifferential R x 0 z) at hc
  change exteriorPower.zeroEquiv R _ (((listComplex x).d 1 0).hom
    (((coefficientRingIso x).hom.f 1).hom z)) = exteriorPower.zeroEquiv R _ a
  rw [hc, coefficientRingIso_zero]
  exact hz

/-- Regularity supplies precisely the positive-degree exactness needed here. -/
theorem augmentation_quasiIso (x : List R) (hx : RegularSequence.RingRegular x) :
    QuasiIso (augmentation x) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
        ⟨augmentation_exact x,
          (ModuleCat.epi_iff_surjective _).mpr (augmentationZero_surjective x)⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by rfl) (by simp [augmentation])
    · change (listComplex x).d 0 0 = 0
      simp
    · change ((ChainComplex.single₀ (ModuleCat R)).obj _).d 1 0 = 0
      simp
    · change ((ChainComplex.single₀ (ModuleCat R)).obj _).d 0 0 = 0
      simp
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ n)]
    exact listComplex_exactAt x hx.toIsWeaklyRegular (n+1) (Nat.zero_lt_succ n)

/-- K(x) itself, with its canonical augmentation, as a projective resolution. -/
def koszulResolution (x : List R) (hx : RegularSequence.RingRegular x) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ listIdeal x)) where
  complex := listComplex x
  projective q := ModuleCat.projective_of_free (listBasis x q)
  π := augmentation x
  quasiIso := augmentation_quasiIso x hx

/-- Each exterior term is finite free, with the increasing-wedge basis upstream. -/
theorem listComplex_finiteFree (x : List R) (q : ℕ) :
    Module.Free R ((listComplex x).X q) ∧ Module.Finite R ((listComplex x).X q) := by
  classical
  exact ⟨Module.Free.of_basis (listBasis x q), Module.Finite.of_basis (listBasis x q)⟩

/-- The finite free resolution assertion of RK-07. -/
theorem finite_free_resolution : Specs.AdvCommAlg.Koszul.finiteFreeResolution.{u} := by
  intro R _ x hx
  exact ⟨augmentation x, augmentation_f_zero x, augmentation_quasiIso x hx,
    listComplex_finiteFree x,
    fun q hq => ModuleCat.isZero_iff_subsingleton.mpr (listComplex_vanish x q hq)⟩

/-- Compute Tor from any chosen projective resolution, naturally in coefficients. -/
def resolutionTorIso (I : Ideal R)
    (P : ProjectiveResolution (ModuleCat.of R (R ⧸ I))) (q : ℕ) :
    tensorComplexFunctor.{u,v} P.complex ⋙ HomologicalComplex.homologyFunctor _ _ q ≅
      quotientTorFunctor I q :=
  NatIso.ofComponents (fun M => (P.isoLeftDerivedObj (tensorCoefficient M) q).symm)
    (by
      intro M N f
      change HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (tensorCoefficientMap f) _).app P.complex) q ≫
          (P.isoLeftDerivedObj (tensorCoefficient N) q).inv =
        (P.isoLeftDerivedObj (tensorCoefficient M) q).inv ≫
          (NatTrans.leftDerived (tensorCoefficientMap f) q).app _
      rw [P.leftDerived_app_eq (tensorCoefficientMap f) q]
      simp)

/-- The natural Koszul–Tor identification for a regular list. -/
def homologyTorIso (x : List R) (hx : RegularSequence.RingRegular x) (q : ℕ) :
    koszulHomologyFunctor.{u,v} x q ≅ quotientTorFunctor (listIdeal x) q :=
  resolutionTorIso (listIdeal x) (koszulResolution x hx) q

/-- Pointwise form, with exactly the canonical coefficient complex from RK-03. -/
def homologyTorIsoAt (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (hx : RegularSequence.RingRegular x) (q : ℕ) :
    homology M x q ≅ (quotientTorFunctor (listIdeal x) q).obj (ModuleCat.of R M) :=
  (eqToIso (congrArg (fun C => C.homology q)
    (tensorCoefficient_complex_eq (ModuleCat.of R M) x))).symm ≪≫
      (homologyTorIso x hx q).app (ModuleCat.of R M)

theorem homology_tor : Specs.AdvCommAlg.Koszul.homologyTor.{u,v} := by
  intro R _ x hx q
  exact ⟨homologyTorIso x hx q⟩

theorem homology_tor_pointwise : Specs.AdvCommAlg.Koszul.homologyTorPointwise.{u,v} := by
  intro R _ M _ _ x hx q
  exact ⟨homologyTorIsoAt M x hx q⟩

/-- Retain acyclicity without imposing regularity on the coefficient ring. -/
theorem coefficient_acyclicity : Specs.AdvCommAlg.Koszul.coefficientAcyclicity.{u,v} := by
  intro R _ M _ _ x hx q hq
  exact weaklyRegular_acyclic M x hx q hq

/-- Regular on R and weakly regular on M implies vanishing of higher Tor. -/
theorem regular_tor_vanish : Specs.AdvCommAlg.Koszul.regularTorVanish.{u,v} := by
  intro R _ M _ _ x hx hM q hq
  have hz : IsZero (homology M x q) :=
    ModuleCat.isZero_iff_subsingleton.mpr (weaklyRegular_acyclic M x hM q hq)
  exact hz.of_iso (homologyTorIsoAt M x hx q).symm

end AdvCommAlg.Koszul
