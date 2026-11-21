import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.TopHomologyAndRegularElement
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.SelfDuality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.NullHomotopy
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.CoefficientExactness
import Batteries.Tactic.OpenPrivate

open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v
namespace AdvCommAlg.Koszul.TopHomology
open CoefficientSequences
variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The multiplication-and-quotient sequence is short exact for an injective scalar. -/
theorem scalarCoefficientSequence_shortExact (y : R)
    (hy : Function.Injective (fun m : M => y • m)) :
    (scalarCoefficientSequence M y).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro m
    exact Submodule.Quotient.mk_eq_zero _
  · exact hy
  · exact Submodule.mkQ_surjective _

/-- Tensoring coefficients agrees with scalar multiplication on the complex. -/
theorem scalarChainMap (x : List R) (y : R) :
    (coefficientChainFunctor x).map (scalarCoefficientSequence M y).f =
      y • 𝟙 (coefficientComplex M x) := by
  ext n : 2
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro m
  change a ⊗ₜ[R] (y • (m : M)) = y • (a ⊗ₜ[R] (m : M))
  exact TensorProduct.tmul_smul _ _ _

/-- These are the zero maps adjacent to each connecting homomorphism. -/
theorem scalarHomologyMap_zero (x : List R) (y : R) (hy : y ∈ listIdeal x) (q : ℕ) :
    HomologicalComplex.homologyMap
      ((coefficientChainFunctor x).map (scalarCoefficientSequence M y).f) q = 0 := by
  have he := scalarChainMap M x y
  change HomologicalComplex.homologyMap (coefficientChainMap x
    (ModuleCat.ofHom (y • (LinearMap.id : M →ₗ[R] M)))) q = 0
  change coefficientChainMap x (ModuleCat.ofHom (y • (LinearMap.id : M →ₗ[R] M))) =
    y • 𝟙 (coefficientComplex M x) at he
  rw [he]
  rw [homologyMap_scalar]
  apply ModuleCat.hom_ext
  ext z
  exact annihilates_homology M x y hy q z

/-- The quotient and connecting maps give the short exact sequence in every positive degree. -/
theorem regularElement_shortExact :
    Specs.AdvCommAlg.Koszul.TopHomology.regularElementShortExact.{u,v} := by
  intro R _ M _ _ x y hy hinj
  let h := chainCoefficient_shortExact x (scalarCoefficientSequence M y)
    (scalarCoefficientSequence_shortExact M y hinj)
  refine ⟨h, ?_, ?_⟩
  · intro n
    refine { exact := h.homology_exact₃ (n+1) n rfl, mono_f := ?_, epi_g := ?_ }
    · exact ((ShortComplex.exact_iff_mono _
        (scalarHomologyMap_zero M x y hy (n+1))).mp (h.homology_exact₂ (n+1)))
    · exact ((ShortComplex.exact_iff_epi _
        (scalarHomologyMap_zero M x y hy n)).mp (h.homology_exact₁ (n+1) n rfl))
  · have : Epi ((coefficientChainFunctor x).map (scalarCoefficientSequence M y).g) := h.epi_g
    have : Epi (HomologicalComplex.homologyMap
        ((coefficientChainFunctor x).map (scalarCoefficientSequence M y).g) 0) := by
      apply HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
      intro j hj
      change j+1=0 at hj
      omega
    have : Mono (HomologicalComplex.homologyMap
        ((coefficientChainFunctor x).map (scalarCoefficientSequence M y).g) 0) :=
      (ShortComplex.exact_iff_mono _ (scalarHomologyMap_zero M x y hy 0)).mp
        (h.homology_exact₂ 0)
    exact isIso_of_mono_of_epi _

set_option backward.isDefEq.respectTransparency false in
/-- The quotient and connecting maps are natural in the coefficient module. -/
theorem reduction_naturality :
    Specs.AdvCommAlg.Koszul.TopHomology.reductionNaturality.{u,v} := by
  intro R _ M N x y f hM hN
  constructor
  · intro q
    have hfg : f ≫ (scalarCoefficientSequence N y).g =
        (scalarCoefficientSequence M y).g ≫ quotientScalarMap y f := by
      apply ModuleCat.hom_ext
      ext m
      rfl
    let F := coefficientChainFunctor x ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ) q
    change F.map f ≫ F.map (scalarCoefficientSequence N y).g =
      F.map (scalarCoefficientSequence M y).g ≫ F.map (quotientScalarMap y f)
    calc
      _ = F.map (f ≫ (scalarCoefficientSequence N y).g) := (F.map_comp _ _).symm
      _ = F.map ((scalarCoefficientSequence M y).g ≫ quotientScalarMap y f) :=
        congrArg F.map hfg
      _ = _ := F.map_comp _ _

  · intro n
    exact chainConnecting_natural x _ _ hM hN (scalarSequenceMap y f) n

/-- Homology is zero above the list length, for arbitrary coefficients. -/
theorem homology_bounded : Specs.AdvCommAlg.Koszul.TopHomology.homologyBounded.{u,v} := by
  intro R _ M _ _ x q hq
  apply ModuleCat.isZero_iff_subsingleton.mp
  exact HomologicalComplex.ExactAt.isZero_homology
    (HomologicalComplex.ExactAt.of_isZero
      (ModuleCat.isZero_iff_subsingleton.mpr (coefficientComplex_vanish M x q hq)))

/-- Evaluation of a degree-zero cochain, as a linear equivalence. -/
def zeroCochainValueEquiv (x : List R) :
    ((⋀[R]^0 (Fin x.length → R)) →ₗ[R] M) ≃ₗ[R] M :=
  ((exteriorPower.zeroEquiv R (Fin x.length → R)).congrLeft M R).trans
    (LinearMap.ringLmapEquivSelf R R M)

theorem zeroCochainValueEquiv_apply (x : List R) (f : ((⋀[R]^0 (Fin x.length → R)) →ₗ[R] M)) :
  zeroCochainValueEquiv M x f = zeroCochainValue M x f := rfl

theorem zeroCochain_reconstruct (x : List R) (f : ((⋀[R]^0 (Fin x.length → R)) →ₗ[R] M))
    (a : ⋀[R]^0 (Fin x.length → R)) :
    f a = exteriorPower.zeroEquiv R (Fin x.length → R) a • zeroCochainValue M x f := by
  let e := exteriorPower.zeroEquiv R (Fin x.length → R)
  obtain ⟨r, rfl⟩ := e.symm.surjective a
  change f (e.symm r) = e (e.symm r) • f (e.symm 1)
  rw [e.apply_symm_apply]
  calc
    f (e.symm r) = f (e.symm (r • (1 : R))) := by simp
    _ = r • f (e.symm 1) := by rw [map_smul, map_smul]

/-- With no incoming boundaries, homology is the concrete cycle kernel. -/
def homologyKernelEquiv (S : ShortComplex (ModuleCat.{v} R)) (hf : S.f = 0) :
    S.homology ≃ₗ[R] LinearMap.ker S.g.hom := by
  haveI := S.isIso_homologyπ hf
  exact (asIso S.homologyπ).toLinearEquiv.symm.trans S.moduleCatCyclesIso.toLinearEquiv

theorem homologyKernelEquiv_cycleClass {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (q : ι) (hf : (C.sc q).f = 0)
    (z : LinearMap.ker (C.sc q).g.hom) :
    homologyKernelEquiv (C.sc q) hf (cycleClass C q z) = z := by
  have := (C.sc q).isIso_homologyπ hf
  have hz : cycleClass C q z = (C.sc q).homologyπ ((C.sc q).moduleCatCyclesIso.inv z) :=
    ((C.sc q).moduleCatCyclesIso_inv_π_apply z).symm
  unfold homologyKernelEquiv
  change (C.sc q).moduleCatCyclesIso.hom
    (inv (C.sc q).homologyπ (cycleClass C q z)) = z
  rw [hz]
  have hz2 := congrArg (fun f : (C.sc q).cycles ⟶ (C.sc q).cycles => f ((C.sc q).moduleCatCyclesIso.inv z))
    (IsIso.hom_inv_id (C.sc q).homologyπ)
  change inv (C.sc q).homologyπ ((C.sc q).homologyπ _) = _ at hz2
  rw [hz2]
  exact (C.sc q).moduleCatCyclesIso.inv_hom_id_apply z

/-- It suffices to test annihilation on the displayed generators. -/
theorem mem_idealAnnihilator_iff (x : List R) (m : M) :
    m ∈ idealAnnihilator M (listIdeal x) ↔ ∀ i : Fin x.length, x.get i • m = 0 := by
  constructor
  · intro h i
    exact h _ (Ideal.subset_span (List.get_mem x i))
  · intro h a ha
    change a ∈ Submodule.span R {r | r ∈ x} at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
      exact h i
    | zero => exact zero_smul R m
    | add a b ha hb ha' hb' => rw [add_smul, ha', hb', add_zero]
    | smul r a ha ha' => rw [smul_eq_mul, mul_smul, ha', smul_zero]

/-- The degree-zero cochain cycles, evaluated at 1, are precisely 0 :_M (x). -/
theorem zeroCochain_cycles_iff (x : List R)
    (f : ((⋀[R]^0 (Fin x.length → R)) →ₗ[R] M)) :
    ((SelfDuality.cochainComplex M x).sc 0).g.hom f = 0 ↔
      zeroCochainValue M x f ∈ idealAnnihilator M (listIdeal x) := by
  have hn : (ComplexShape.up ℕ).next 0 = 1 := ComplexShape.next_eq' _ rfl
  change ((SelfDuality.cochainComplex M x).d 0 ((ComplexShape.up ℕ).next 0)).hom f = 0 ↔ _
  rw [hn, SelfDuality.cochain_differential]
  constructor
  · intro hf
    rw [mem_idealAnnihilator_iff]
    intro i
    have hi := LinearMap.congr_fun hf
      ((exteriorPower.oneEquiv R (Fin x.length → R)).symm (Pi.basisFun R _ i))
    change f (differential (listForm x) 0 _) = 0 at hi
    rwa [zeroCochain_reconstruct, differential_one, LinearEquiv.apply_symm_apply,
      listForm_basis] at hi
  · intro hf
    apply LinearMap.ext
    intro a
    change f (differential (listForm x) 0 a) = 0
    rw [zeroCochain_reconstruct, differential_one]
    exact hf _ (listForm_mem x _)

/-- Restrict evaluation at 1 to degree-zero cocycles. -/
def zeroCochainCyclesEquiv (x : List R) :
    LinearMap.ker ((SelfDuality.cochainComplex M x).sc 0).g.hom ≃ₗ[R]
      idealAnnihilator M (listIdeal x) :=
  (zeroCochainValueEquiv M x).ofSubmodules _ _ (by
    ext m
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (zeroCochain_cycles_iff M x f).mp hf
    · intro hm
      refine ⟨(zeroCochainValueEquiv M x).symm m, ?_, by simp⟩
      apply (zeroCochain_cycles_iff M x _).mpr
      change zeroCochainValueEquiv M x ((zeroCochainValueEquiv M x).symm m) ∈ _
      simpa using hm)

/-- There are no incoming degree-zero cochain boundaries. -/
theorem zeroCochain_incoming (x : List R) :
    ((SelfDuality.cochainComplex M x).sc 0).f = 0 := by
  have hp : (ComplexShape.up ℕ).prev 0 = 0 :=
    ComplexShape.prev_eq_self' _ _ (by intro i hi; change i+1=0 at hi; omega)
  change (SelfDuality.cochainComplex M x).d ((ComplexShape.up ℕ).prev 0) 0 = 0
  rw [hp]
  exact HomologicalComplex.shape _ _ _ (by intro h; change 0+1=0 at h; omega)

/-- H⁰ is canonically the ideal annihilator. -/
def zeroCohomologyAnnihilatorEquiv (x : List R) :
    SelfDuality.cohomology M x 0 ≃ₗ[R] idealAnnihilator M (listIdeal x) :=
  (homologyKernelEquiv _ (zeroCochain_incoming M x)).trans (zeroCochainCyclesEquiv M x)

@[simp] theorem zeroCohomologyAnnihilatorEquiv_cycleClass (x : List R)
    (z : LinearMap.ker ((SelfDuality.cochainComplex M x).sc 0).g.hom) :
    (zeroCohomologyAnnihilatorEquiv M x
      (cycleClass (SelfDuality.cochainComplex M x) 0 z) : M) = zeroCochainValue M x z.val := by
  change ((zeroCochainCyclesEquiv M x)
    (homologyKernelEquiv _ _ (cycleClass (SelfDuality.cochainComplex M x) 0 z)) : M) = _
  rw [homologyKernelEquiv_cycleClass]
  rfl

/-- Evaluation on the class of 1 identifies Hom(R/I,M) with 0 :_M I. -/
def quotientHomAnnihilatorEquiv (I : Ideal R) :
    ((R ⧸ I) →ₗ[R] M) ≃ₗ[R] idealAnnihilator M I where
  toFun f := ⟨f (Ideal.Quotient.mk I 1), by
    intro a ha
    rw [← map_smul]
    have he : a • (Ideal.Quotient.mk I 1) = Ideal.Quotient.mk I a := by
      simpa only [smul_eq_mul, mul_one, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk]
        using (I.mkQ.map_smul a (1 : R)).symm
    rw [he, (Ideal.Quotient.eq_zero_iff_mem).mpr ha, map_zero]⟩
  invFun m := I.liftQ (LinearMap.toSpanSingleton R M m.val) (by
    intro a ha
    exact m.property a ha)
  left_inv f := by
    apply LinearMap.ext
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    change a • f (Ideal.Quotient.mk I 1) = f (Ideal.Quotient.mk I a)
    rw [← map_smul]
    congr 1
    simpa only [smul_eq_mul, mul_one, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk]
        using (I.mkQ.map_smul a (1 : R)).symm
  right_inv m := by
    apply Subtype.ext
    change (1 : R) • m.val = m.val
    exact one_smul R m.val
  map_add' f g := rfl
  map_smul' r f := rfl

/-- H⁰(x;M) = Hom_R(R/(x),M), with the specified evaluation map. -/
def zeroCohomologyHomEquiv (x : List R) :
    SelfDuality.cohomology M x 0 ≃ₗ[R] ((R ⧸ listIdeal x) →ₗ[R] M) :=
  (zeroCohomologyAnnihilatorEquiv M x).trans (quotientHomAnnihilatorEquiv M (listIdeal x)).symm

theorem zero_cohomology : Specs.AdvCommAlg.Koszul.TopHomology.zeroCohomology.{u,v} := by
  intro R _ M _ _ x
  refine ⟨zeroCohomologyHomEquiv M x, ?_⟩
  intro z
  change ((quotientHomAnnihilatorEquiv M (listIdeal x)).symm
    (zeroCohomologyAnnihilatorEquiv M x (cycleClass (SelfDuality.cochainComplex M x) 0 z)))
      (Ideal.Quotient.mk _ 1) = _
  change (1 : R) • (zeroCohomologyAnnihilatorEquiv M x
    (cycleClass (SelfDuality.cochainComplex M x) 0 z) : M) = _
  rw [one_smul, zeroCohomologyAnnihilatorEquiv_cycleClass]

open private chainWindow cochainWindow oriented_cycles_iff down_next
  from MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.SelfDuality

/-- The degree-zero exterior pairing is exactly the ordered top coefficient. -/
theorem oriented_zero_value (x : List R)
    (a : (coefficientComplex M x).X x.length) :
    zeroCochainValue M x
      (SelfDuality.orientedDegreeEquiv M x 0 x.length (by simp) a) =
      topCoefficientEquiv M x a := by
  induction a using TensorProduct.inductionOn with
  | tmul a m =>
    change SelfDuality.orientedDegreeEquiv M x 0 x.length _ (a ⊗ₜ[R] m)
      ((exteriorPower.zeroEquiv R (Fin x.length → R)).symm 1) =
      SelfDuality.orientation x a • m
    rw [SelfDuality.orientedDegreeEquiv_tmul]
    simp only [SelfDuality.dualitySign, Nat.zero_mul, Nat.zero_div, pow_zero, one_smul]
    congr 1
    change SelfDuality.orientation x (SelfDuality.topWedge x 0 x.length _ _ a) =
      SelfDuality.orientation x a
    congr 1
    apply Subtype.ext
    rw [SelfDuality.topWedge_coe]
    have he : (((exteriorPower.zeroEquiv R (Fin x.length → R)).symm 1 :
        ⋀[R]^0 (Fin x.length → R)) : ExteriorAlgebra R (Fin x.length → R)) = 1 := by
      have hw := (exteriorPower.zeroEquiv R (Fin x.length → R)).symm_apply_apply
        (exteriorPower.ιMulti R 0 (fun i => Fin.elim0 i))
      rw [exteriorPower.zeroEquiv_ιMulti] at hw
      rw [hw]
      simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]
    rw [he, one_mul]
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]
    exact (map_add (topCoefficientEquiv M x) a b).symm

/-- The ordered top coefficient takes top cycles precisely to the ideal annihilator. -/
theorem top_cycles_iff (x : List R) (a : (coefficientComplex M x).X x.length) :
    ((coefficientComplex M x).sc x.length).g.hom a = 0 ↔
      topCoefficientEquiv M x a ∈ idealAnnihilator M (listIdeal x) := by
  have hc := oriented_cycles_iff M x 0 x.length (by simp) a
  have hn : (ComplexShape.down ℕ).next x.length = x.length-1 := down_next x.length
  have hnc : (ComplexShape.up ℕ).next 0 = 1 := ComplexShape.next_eq' _ rfl
  change ((coefficientComplex M x).d x.length ((ComplexShape.down ℕ).next x.length)).hom a = 0 ↔ _
  rw [hn]
  change ((chainWindow M x x.length).g.hom a = 0) ↔ _
  rw [hc]
  have hv := zeroCochain_cycles_iff M x
    (SelfDuality.orientedDegreeEquiv M x 0 x.length (by simp) a)
  rw [oriented_zero_value] at hv
  convert hv using 1
  change ((SelfDuality.cochainComplex M x).d 0 1).hom _ = 0 ↔
    ((SelfDuality.cochainComplex M x).d 0 ((ComplexShape.up ℕ).next 0)).hom _ = 0
  rw [hnc]

/-- Restriction of the ordered coefficient equivalence to top cycles. -/
def topCyclesEquiv (x : List R) :
    LinearMap.ker ((coefficientComplex M x).sc x.length).g.hom ≃ₗ[R]
      idealAnnihilator M (listIdeal x) :=
  (topCoefficientEquiv M x).ofSubmodules _ _ (by
    ext m
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (top_cycles_iff M x a).mp ha
    · intro hm
      refine ⟨(topCoefficientEquiv M x).symm m, ?_, by simp⟩
      apply (top_cycles_iff M x _).mpr
      simpa using hm)

/-- The incoming top differential is zero since its source has degree r+1. -/
theorem top_incoming (x : List R) : ((coefficientComplex M x).sc x.length).f = 0 := by
  have hp : (ComplexShape.down ℕ).prev x.length = x.length+1 := ComplexShape.prev_eq' _ rfl
  change (coefficientComplex M x).d ((ComplexShape.down ℕ).prev x.length) x.length = 0
  rw [hp]
  have hs := coefficientComplex_vanish M x (x.length+1) (by omega)
  apply ModuleCat.hom_ext
  exact Subsingleton.elim _ _

/-- Top homology, with its ordered basis identification. -/
def topHomologyAnnihilatorEquiv (x : List R) :
    homology M x x.length ≃ₗ[R] idealAnnihilator M (listIdeal x) :=
  (homologyKernelEquiv _ (top_incoming M x)).trans (topCyclesEquiv M x)

theorem top_homology : Specs.AdvCommAlg.Koszul.TopHomology.topHomology.{u,v} := by
  intro R _ M _ _ x
  refine ⟨topHomologyAnnihilatorEquiv M x, ?_⟩
  intro z
  change ((topCyclesEquiv M x)
    (homologyKernelEquiv _ _ (cycleClass (coefficientComplex M x) x.length z)) : M) = _
  rw [homologyKernelEquiv_cycleClass]
  rfl

end AdvCommAlg.Koszul.TopHomology
