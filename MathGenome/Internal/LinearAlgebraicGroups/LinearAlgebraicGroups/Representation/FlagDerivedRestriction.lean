import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagDerivedRestriction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.FlatPullback
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.PolynomialExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.NullHomotopy
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularFiniteProjectiveDimension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry
open scoped BigOperators TensorProduct

universe u v

namespace LinearAlgebraicGroups.Representation.FlagDerivedRestriction

open _root_.LinearAlgebraicGroups.Specs
open Specs.CharacterDescent (Character)
open Specs.EquivariantAffineModules
open Specs.FlagDerivedRestriction
open LinearAlgebraicGroups.Representation.EquivariantAffineModules
open AdvCommAlg.Koszul
open AdvCommAlg.Koszul.PolynomialExample

open private weightProject weightProject_of_mem weightProject_natural
  gradingDecomposition_apply_of_mem pullback_spec_isQuasicoherent
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules
open private finite_restrictScalars_of_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

noncomputable section

attribute [local instance] Classical.decEq

theorem koszulComputesTor : KoszulComputesTor.{u} := by
  intro k _ n M q
  let := evaluationAlgebra k n
  obtain ⟨π, _, hπ, _, _⟩ := resolves_coefficients k n
  let P : ProjectiveResolution (ModuleCat.of (PolynomialRing k n) k) :=
    { complex := listComplex (variableList k n)
      projective := fun i => ModuleCat.projective_of_free (listBasis (variableList k n) i)
      π := π
      quasiIso := hπ }
  refine ⟨?_⟩
  calc
    _ ≅ ((tensorComplexFunctor P.complex).obj M).homology q :=
      (eqToIso (congrArg (fun C => C.homology q)
        (tensorCoefficient_complex_eq M (variableList k n)))).symm
    _ ≅ _ := (P.isoLeftDerivedObj (tensorCoefficient M) q).symm

private theorem polynomial_sub_evaluation_mem {k : Type u} [Field k] {n : ℕ}
    (p : PolynomialRing k n) :
    p - MvPolynomial.C (MvPolynomial.eval (fun _ => (0 : k)) p) ∈
      listIdeal (variableList k n) := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (quotientCoefficientsEquiv (A := k) (r := n)).injective
  rw [map_zero, quotientCoefficientsEquiv_mk, map_sub, MvPolynomial.eval_C, sub_self]

private theorem finite_over_base_of_evaluation_action {k : Type u} [Field k] {n : ℕ}
    (Q : ModuleCat.{u} (PolynomialRing k n)) [Module.Finite (PolynomialRing k n) Q]
    (h : ∀ (p : PolynomialRing k n) (x : Q),
      p • x = (MvPolynomial.C (σ := Fin n) (MvPolynomial.eval (fun _ => (0 : k)) p)) • x) :
    Module.Finite k ((affineBaseRestriction k n).obj Q) := by
  let Q₀ := (affineBaseRestriction k n).obj Q
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := PolynomialRing k n) (M := Q))
  let s₀ : Finset Q₀ := s
  let P := Submodule.span k (s₀ : Set Q₀)
  have hP (x : Q) : (show Q₀ from x) ∈ P := by
    have hx : x ∈ Submodule.span (PolynomialRing k n) (s : Set Q) := by
      rw [hs]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (s := (s₀ : Set Q₀)) hy
    | zero => exact P.zero_mem
    | add y z _ _ hy hz => exact P.add_mem hy hz
    | smul p y _ hy =>
      show (show Q₀ from p • y) ∈ P
      rw [h p y]
      exact P.smul_mem (MvPolynomial.eval (fun _ => (0 : k)) p) hy
  exact ⟨⟨s₀, eq_top_iff.mpr (fun x _ => hP x)⟩⟩

private theorem koszulHomologyFiniteOverPolynomialRing {k : Type u} [Field k] {n : ℕ}
    (M : ModuleCat.{u} (polynomialAlgebra k n)) [Module.Finite (PolynomialRing k n) M] (q : ℕ) :
    Module.Finite (PolynomialRing k n) ((KoszulCoefficientComplex M).homology q) := by
  let C := KoszulCoefficientComplex M
  let S := C.sc q
  let R := PolynomialRing k n
  have : Module.Finite R S.X₂ :=
    Module.Finite.equiv (wedgeCoordinates M q).symm
  have : IsNoetherian R S.X₂ := inferInstance
  have : Module.Finite R S.cycles :=
    Module.Finite.of_injective S.iCycles.hom
      ((ModuleCat.mono_iff_injective S.iCycles).mp inferInstance)
  exact Module.Finite.of_surjective S.homologyπ.hom
    ((ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance)

theorem koszulFiniteness : KoszulFiniteness.{u} := by
  intro k _ n M q
  constructor
  · intro hM
    let := hM
    let := koszulHomologyFiniteOverPolynomialRing M q
    apply finite_over_base_of_evaluation_action
    intro p x
    apply sub_eq_zero.mp
    rw [← sub_smul]
    exact annihilates_homology M (variableList k n) _ (polynomial_sub_evaluation_mem p) q x
  · intro hq
    have hs := coefficientComplex_vanish M (variableList k n) q (by simpa using hq)
    exact ((KoszulCoefficientComplex M).sc q).isZero_homology_of_isZero_X₂
      (ModuleCat.isZero_iff_subsingleton.mpr hs)


section WedgeDifferential

open Set.powersetCard
open scoped ExteriorAlgebra

variable {k : Type u} [Field k] {n q : ℕ}

private def eraseWedge (s : WedgeIndex k n (q + 1)) (i : Fin (q + 1)) :
    WedgeIndex k n q :=
  ofFinEmbEquiv (i.succAboveOrderEmb.comp (ofFinEmbEquiv.symm s))

private theorem eraseWedge_val (s : WedgeIndex k n (q + 1)) (i : Fin (q + 1)) :
    (eraseWedge s i).val = s.val.erase (ofFinEmbEquiv.symm s i) := by
  ext j
  rw [Finset.mem_erase]
  change j ∈ eraseWedge s i ↔ _
  rw [eraseWedge, mem_ofFinEmbEquiv_iff_mem_range]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨fun h => Fin.succAbove_ne i l ((ofFinEmbEquiv.symm s).injective h),
      (mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨i.succAbove l, rfl⟩⟩
  · rintro ⟨hne, hj⟩
    obtain ⟨l, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s j).mpr hj
    obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq_iff.mpr (fun h => hne (congrArg _ h))
    exact ⟨m, rfl⟩

private theorem variable_mul_erased_weight {T : GroupScheme k} (ν : Fin n → Character T)
    (s : WedgeIndex k n (q + 1)) (i : Fin (q + 1)) :
    ν (variableIndex (ofFinEmbEquiv.symm s i)) * wedgeWeight ν (eraseWedge s i) =
      wedgeWeight ν s := by
  let j := ofFinEmbEquiv.symm s i
  have hj : j ∈ s.val := (mem_range_ofFinEmbEquiv_symm_iff_mem s j).mp ⟨i, rfl⟩
  unfold wedgeWeight
  rw [eraseWedge_val]
  exact Finset.mul_prod_erase s.val (fun t => ν (variableIndex t)) hj

private theorem variableList_get (i : Fin (variableList k n).length) :
    (variableList k n).get i = MvPolynomial.X (variableIndex i) := by
  exact List.get_ofFn (MvPolynomial.X (R := k)) i

private theorem exteriorDifferential_basis (s : WedgeIndex k n (q + 1)) :
    differential (listForm (variableList k n)) q (listBasis (variableList k n) (q + 1) s) =
      ∑ i : Fin (q + 1), (-1 : PolynomialRing k n)^i.val •
        ((MvPolynomial.X (variableIndex (ofFinEmbEquiv.symm s i)) : PolynomialRing k n) •
          listBasis (variableList k n) q (eraseWedge s i)) := by
  let R := PolynomialRing k n
  let b := Pi.basisFun R (Fin (variableList k n).length)
  let e : Fin (q + 1) → _ := b ∘ ofFinEmbEquiv.symm s
  have hb : listBasis (variableList k n) (q + 1) s = exteriorPower.ιMulti R (q + 1) e :=
    listBasis_apply _ _ _
  have hb' (i : Fin (q + 1)) :
      listBasis (variableList k n) q (eraseWedge s i) =
        exteriorPower.ιMulti R q (e ∘ i.succAbove) := by
    rw [listBasis_apply, exteriorPower.ιMulti_family, eraseWedge, Equiv.symm_apply_apply]
    rfl
  rw [hb]
  simp_rw [hb', ← variableList_get,
    ← listForm_basis (variableList k n) (ofFinEmbEquiv.symm s _)]
  apply Subtype.ext
  simp only [differential_coe, exteriorPower.ιMulti_apply_coe, Submodule.coe_sum, SetLike.val_smul]
  exact contraction_formula (listForm (variableList k n)) q e

private theorem wedgeCoordinates_basis_tmul (M : ModuleCat.{u} (polynomialAlgebra k n))
    (s : WedgeIndex k n q) (v : M) :
    wedgeCoordinates M q (listBasis (variableList k n) q s ⊗ₜ[PolynomialRing k n] v) =
      Finsupp.single s v := by
  classical
  let b := listBasis (variableList k n) q
  change TensorProduct.equivFinsuppOfBasisLeft (N := M) b (b s ⊗ₜ[PolynomialRing k n] v) = _
  ext t
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.repr_self]
  by_cases he : t = s <;> simp [he]

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateD_single (M : ModuleCat.{u} (polynomialAlgebra k n))
    (s : WedgeIndex k n (q + 1)) (v : M) :
    coordinateD M (q + 1) q (Finsupp.single s v) =
      ∑ i : Fin (q + 1), Finsupp.single (eraseWedge s i)
        (((-1 : PolynomialRing k n)^i.val) •
          ((MvPolynomial.X (variableIndex (ofFinEmbEquiv.symm s i)) : PolynomialRing k n) • v)) := by
  classical
  unfold coordinateD
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hs :
      (wedgeCoordinates M (q + 1)).symm (Finsupp.single s v) =
        listBasis (variableList k n) (q + 1) s ⊗ₜ[PolynomialRing k n] v := by
    apply (wedgeCoordinates M (q + 1)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (wedgeCoordinates_basis_tmul M s v).symm
  rw [hs]
  have hd : (KoszulCoefficientComplex M).d (q + 1) q =
      ModuleCat.ofHom (coefficientDifferential M (variableList k n) q) :=
    ChainComplex.of_d
      (fun i => ModuleCat.of (PolynomialRing k n)
        ((⋀[PolynomialRing k n]^i (Fin (variableList k n).length → PolynomialRing k n)) ⊗[PolynomialRing k n] M))
      (fun i => ModuleCat.ofHom (coefficientDifferential M (variableList k n) i)) q
  rw [hd]
  change wedgeCoordinates M q
    (differential (listForm (variableList k n)) q
      (listBasis (variableList k n) (q + 1) s) ⊗ₜ[PolynomialRing k n] v) = _
  rw [exteriorDifferential_basis, TensorProduct.sum_tmul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul]
  rw [wedgeCoordinates_basis_tmul, smul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem koszulWeightPreservation : KoszulWeightPreservation.{u} := by
  intro k _ T Y a n U G M
  dsimp only
  intro H χ i j v hv
  have : IsScalarTower k (PolynomialRing k n) M :=
    moduleOverBaseField_tower (polynomialAlgebra k n) M
  by_cases hij : i = j + 1
  · subst i
    classical
    have hsingle (s : WedgeIndex k n (j + 1)) (m : M)
        (hm : m ∈ H.piece ((wedgeWeight U.weight s)⁻¹ * χ)) :
        coordinateD M (j + 1) j (Finsupp.single s m) ∈
          weightTerm M U.weight H.toWeightGrading χ j := by
      rw [coordinateD_single]
      apply Submodule.sum_mem
      intro l _
      let j₀ := variableIndex (ofFinEmbEquiv.symm s l)
      have hx : (MvPolynomial.X j₀ : ↥(polynomialAlgebra k n)) ∈ G.val.piece (U.weight j₀) :=
        (G.property _ _).mpr (U.homogeneous j₀)
      have hm' := H.smul_mem (r := (MvPolynomial.X j₀ : ↥(polynomialAlgebra k n))) hx hm
      have hw : U.weight (variableIndex (ofFinEmbEquiv.symm s l)) *
          ((wedgeWeight U.weight s)⁻¹ * χ) =
          (wedgeWeight U.weight (eraseWedge s l))⁻¹ * χ := by
        let c := U.weight (variableIndex (ofFinEmbEquiv.symm s l))
        let d := wedgeWeight U.weight (eraseWedge s l)
        have hs : c * d = wedgeWeight U.weight s := variable_mul_erased_weight U.weight s l
        change c * ((wedgeWeight U.weight s)⁻¹ * χ) = d⁻¹ * χ
        rw [← hs, mul_inv_rev, mul_comm d⁻¹ c⁻¹, mul_assoc, mul_inv_cancel_left]
      rw [hw] at hm'
      have hsign : ((-1 : PolynomialRing k n)^l.val) =
          algebraMap k (polynomialAlgebra k n) ((-1 : k)^l.val) := by
        simp
      rw [hsign]
      intro t
      by_cases ht : eraseWedge s l = t
      · subst t
        rw [Finsupp.single_eq_same]
        exact (H.piece _).smul_mem ((-1 : k)^l.val) hm'
      · rw [Finsupp.single_eq_of_ne (Ne.symm ht)]
        exact (H.piece _).zero_mem
    have hv' : v = ∑ s ∈ v.support, Finsupp.single s (v s) := (Finsupp.sum_single v).symm
    nth_rw 1 [hv']
    rw [map_sum]
    exact Submodule.sum_mem _ (fun s _ => hsingle s (v s) (hv s))
  · have hd : (KoszulCoefficientComplex M).d i j = 0 :=
      HomologicalComplex.shape _ _ _ (fun h => hij h.symm)
    unfold coordinateD
    rw [hd]
    simp

end WedgeDifferential


private theorem shiftedCoordinates_internal {k Λ V : Type u} {I : Type v} [Field k]
    [CommGroup Λ] [AddCommGroup V] [Module k V]
    (G : WeightGrading k Λ V) (τ : I → Λ) (M : Module k (I →₀ V))
    (W : Λ → @Submodule k (I →₀ V) _ _ M)
    (hsmul : ∀ (c : k) (f : I →₀ V) (i : I), (@SMul.smul k _ M.toSMul c f) i = c • f i)
    (hW : ∀ χ v, v ∈ W χ ↔ ∀ i, v i ∈ G.piece ((τ i)⁻¹ * χ)) :
    DirectSum.IsInternal W := by
  let : Module k (I →₀ V) := M
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro χ
    rw [Submodule.disjoint_def]
    intro v hv hrest
    apply Finsupp.ext
    intro s
    let α := τ s
    let eval : (I →₀ V) →ₗ[k] V :=
      { toFun := fun f => f s
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => hsmul c f s }
    have heval (ψ : Λ) :
        (W ψ).map eval ≤ G.piece (α⁻¹ * ψ) := by
      rintro _ ⟨w, hw, rfl⟩
      exact (hW ψ _).mp hw s
    have hle : (⨆ ψ, ⨆ (_ : ψ ≠ χ), W ψ).map eval ≤
        ⨆ η, ⨆ (_ : η ≠ α⁻¹ * χ), G.piece η := by
      simp only [Submodule.map_iSup]
      refine iSup_le fun ψ => iSup_le fun hψ => (heval ψ).trans ?_
      exact le_iSup_of_le (α⁻¹ * ψ) (le_iSup_of_le
        (fun he => hψ (mul_left_cancel he)) le_rfl)
    have hv' : v s ∈ ⨆ η, ⨆ (_ : η ≠ α⁻¹ * χ), G.piece η :=
      hle ⟨v, hrest, rfl⟩
    have hdisj := (iSupIndep_def.mp G.internal.submodule_iSupIndep) (α⁻¹ * χ)
    exact Submodule.disjoint_def.mp hdisj (v s) ((hW χ _).mp hv s) hv'
  · apply eq_top_iff.mpr
    intro v h
    clear h
    induction v using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add v w hv hw => exact Submodule.add_mem _ hv hw
    | single s v =>
      let α := τ s
      let put : V →ₗ[k] (I →₀ V) :=
        { toFun := Finsupp.single s
          map_add' := Finsupp.single_add s
          map_smul' := by
            intro c v
            ext i
            change Finsupp.single s (c • v) i =
              (@SMul.smul k _ M.toSMul c (Finsupp.single s v)) i
            rw [hsmul]
            by_cases hi : i = s
            · subst i
              simp only [Finsupp.single_eq_same]
            · rw [Finsupp.single_eq_of_ne hi, Finsupp.single_eq_of_ne hi, smul_zero] }
      have hle : (⨆ η, G.piece η) ≤ (iSup W).comap put := by
        apply iSup_le
        intro η m hm
        change Finsupp.single s m ∈ iSup W
        refine (le_iSup W (α * η)) ?_
        apply (hW _ _).mpr
        intro t
        by_cases ht : t = s
        · subst t
          simpa [α] using hm
        · rw [Finsupp.single_eq_of_ne ht]
          exact Submodule.zero_mem _
      exact hle (by rw [G.internal.submodule_iSup_eq_top]; exact Submodule.mem_top)

theorem koszulWeightDecomposition : KoszulWeightDecomposition.{u} := by
  intro k _ T n M ν G q
  apply shiftedCoordinates_internal (I := WedgeIndex k n q)
    G (fun s => wedgeWeight ν s) inferInstance (fun χ => weightTerm M ν G χ q)
  · intro c v i
    rfl
  · intro χ v
    rfl


section KoszulHomologyWeights

variable {k : Type u} [Field k] {T : GroupScheme k} {n : ℕ}
variable (M : ModuleCat.{u} (polynomialAlgebra k n)) (ν : Fin n → Character T)
variable (G : WeightGrading k (Character T) M)
variable (h : ∀ χ, PreservesKoszulWeight M ν G χ)

private def coordinateGrading (q : ℕ) :
    WeightGrading k (Character T) ((coordinateComplex M).X q) :=
  ⟨fun χ => weightTerm M ν G χ q, koszulWeightDecomposition M ν G q⟩

private def weightIncl (χ : Character T) :
    weightComplex M ν G χ (h χ) ⟶ coordinateComplex M where
  f q := ModuleCat.ofHom (weightTerm M ν G χ q).subtype
  comm' _ _ _ := rfl

private def weightProj (χ : Character T) :
    coordinateComplex M ⟶ weightComplex M ν G χ (h χ) where
  f q := ModuleCat.ofHom (weightProject (coordinateGrading M ν G q) χ)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact weightProject_natural (coordinateGrading M ν G i) (coordinateGrading M ν G j)
      (coordinateDOverBase M i j) (fun ψ v hv => h ψ i j v hv) χ x

private theorem weightIncl_comp_proj (χ : Character T) :
    weightIncl M ν G h χ ≫ weightProj M ν G h χ = 𝟙 _ := by
  ext q : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact weightProject_of_mem (coordinateGrading M ν G q) χ x

private theorem weightIncl_comp_proj_ne {χ ψ : Character T} (hne : χ ≠ ψ) :
    weightIncl M ν G h χ ≫ weightProj M ν G h ψ = 0 := by
  ext q : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let A := coordinateGrading M ν G q
  let v : A.piece χ := x
  change weightProject A ψ (v : (coordinateComplex M).X q) = 0
  have he := congrArg (DirectSum.component k (Character T) (fun i => A.piece i) ψ)
    (gradingDecomposition_apply_of_mem A χ v)
  rw [DirectSum.component.of, dite_eq_right hne] at he
  exact he

private def wedgeCoordinatesOverBase (q : ℕ) :
    (affineBaseRestriction k n).obj ((KoszulCoefficientComplex M).X q) ≃ₗ[k]
      (coordinateComplex M).X q where
  __ := (wedgeCoordinates M q).toAddEquiv
  map_smul' a x := by
    let v : (KoszulCoefficientComplex M).X q := x
    change wedgeCoordinates M q ((algebraMap k (PolynomialRing k n) a) • v) =
      a • wedgeCoordinates M q v
    calc
      _ = (algebraMap k (PolynomialRing k n) a) • wedgeCoordinates M q v :=
        (wedgeCoordinates M q).map_smul _ _
      _ = _ := by ext s; rfl

private def coordinateComplexIso :
    ((affineBaseRestriction k n).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (KoszulCoefficientComplex M) ≅ coordinateComplex M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (wedgeCoordinatesOverBase M q).toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let v : (KoszulCoefficientComplex M).X i := x
      change coordinateD M i j (wedgeCoordinates M i v) =
        wedgeCoordinates M j (((KoszulCoefficientComplex M).d i j).hom v)
      simp only [coordinateD, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply])

private theorem coordinateHomologyFinite [Module.Finite (PolynomialRing k n) M] (q : ℕ) :
    Module.Finite k ((coordinateComplex M).homology q) := by
  let F := affineBaseRestriction k n
  let C := KoszulCoefficientComplex M
  let C₀ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C
  have : Module.Finite k (F.obj (C.homology q)) := (koszulFiniteness n M q).1 inferInstance
  let e : F.obj (C.homology q) ≅ C₀.homology q :=
    ((C.sc q).mapHomologyIso F).symm
  exact Module.Finite.equiv
    (e ≪≫ (HomologicalComplex.homologyFunctor _ _ q).mapIso (coordinateComplexIso M)).toLinearEquiv

private def homologyIncl (q : ℕ) (χ : Character T) :
    (weightComplex M ν G χ (h χ)).homology q ⟶ (coordinateComplex M).homology q :=
  HomologicalComplex.homologyMap (weightIncl M ν G h χ) q

private def homologyProj (q : ℕ) (χ : Character T) :
    (coordinateComplex M).homology q ⟶ (weightComplex M ν G χ (h χ)).homology q :=
  HomologicalComplex.homologyMap (weightProj M ν G h χ) q

private lemma homologyIncl_comp_homologyProj (q : ℕ) (χ : Character T) :
    homologyIncl M ν G h q χ ≫ homologyProj M ν G h q χ = 𝟙 _ := by
  rw [homologyIncl, homologyProj, ← HomologicalComplex.homologyMap_comp,
    weightIncl_comp_proj, HomologicalComplex.homologyMap_id]

private lemma homologyIncl_comp_homologyProj_ne (q : ℕ) {χ ψ : Character T} (hne : χ ≠ ψ) :
    homologyIncl M ν G h q χ ≫ homologyProj M ν G h q ψ = 0 := by
  rw [homologyIncl, homologyProj, ← HomologicalComplex.homologyMap_comp,
    weightIncl_comp_proj_ne M ν G h hne]
  exact Functor.map_zero (HomologicalComplex.homologyFunctor (ModuleCat.{u} k)
    (ComplexShape.down ℕ) q) _ _

private theorem homologyIncl_injective (q : ℕ) (χ : Character T) :
    Function.Injective (homologyIncl M ν G h q χ) := by
  have e := homologyIncl_comp_homologyProj M ν G h q χ
  intro v w hv
  have hh (x : (weightComplex M ν G χ (h χ)).homology q) :
      homologyProj M ν G h q χ (homologyIncl M ν G h q χ x) = x := by
    exact congrArg (fun f => f x) e
  rw [← hh v, ← hh w, hv]

private theorem homologyRanges_independent (q : ℕ) :
    iSupIndep (fun χ => LinearMap.range (homologyIncl M ν G h q χ).hom) := by
  rw [iSupIndep_def]
  intro χ
  let p := (homologyProj M ν G h q χ).hom
  have hker (ψ : Character T) (hne : ψ ≠ χ) :
      LinearMap.range (homologyIncl M ν G h q ψ).hom ≤ LinearMap.ker p := by
    rintro _ ⟨v, rfl⟩
    exact congrArg (fun f => f v) (homologyIncl_comp_homologyProj_ne M ν G h q hne)
  refine Disjoint.mono_right (iSup_le fun ψ => iSup_le (hker ψ)) ?_
  rw [Submodule.disjoint_def]
  rintro x ⟨v, rfl⟩ hv
  have hz := congrArg (fun f => f v) (homologyIncl_comp_homologyProj M ν G h q χ)
  have hzero : v = 0 := hz.symm.trans hv
  simp [hzero]

private theorem finiteHomologyWeightSupport [Module.Finite (PolynomialRing k n) M] (q : ℕ) :
    { χ | LinearMap.range (homologyIncl M ν G h q χ).hom ≠ ⊥ }.Finite := by
  have := coordinateHomologyFinite M q
  exact Submodule.finite_ne_bot_of_iSupIndep (homologyRanges_independent M ν G h q)

private def koszulHomologyCharacter [Module.Finite (PolynomialRing k n) M] (q : ℕ) :
    CharacterRing T :=
  MonoidAlgebra.ofCoeff <| Finsupp.onFinset (finiteHomologyWeightSupport M ν G h q).toFinset
    (fun χ => (Module.finrank k ((weightComplex M ν G χ (h χ)).homology q) : ℤ))
    (by
      intro χ hχ
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      intro hz
      apply hχ
      have : Subsingleton ((weightComplex M ν G χ (h χ)).homology q) := by
        apply subsingleton_of_forall_eq (0 : (weightComplex M ν G χ (h χ)).homology q)
        intro v
        apply homologyIncl_injective M ν G h q χ
        have hv : (homologyIncl M ν G h q χ).hom v ∈
            LinearMap.range (homologyIncl M ν G h q χ).hom := ⟨v, rfl⟩
        rw [hz, Submodule.mem_bot] at hv
        simpa using hv
      exact_mod_cast (Module.finrank_zero_of_subsingleton (R := k)
        (M := (weightComplex M ν G χ (h χ)).homology q)))

end KoszulHomologyWeights


section HomogeneousHomology

variable {k : Type u} [Field k] {T : GroupScheme k} {n : ℕ}
variable (M : ModuleCat.{u} (polynomialAlgebra k n)) (ν : Fin n → Character T)
variable (G : WeightGrading k (Character T) M)
variable (h : ∀ χ, PreservesKoszulWeight M ν G χ)

open private gradingDecomposition from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

private theorem sum_weightProjections {Λ V : Type u} [CommGroup Λ] [AddCommGroup V] [Module k V]
    (D : WeightGrading k Λ V) (v : V) :
    ∃ s : Finset Λ, ∑ i ∈ s, (weightProject D i v).val = v := by
  let d := gradingDecomposition D v
  refine ⟨d.support, ?_⟩
  have hs := congrArg (DirectSum.coeLinearMap D.piece) (DirectSum.sum_support_of d)
  rw [map_sum] at hs
  have hv : DirectSum.coeLinearMap D.piece d = v := (gradingDecomposition D).symm_apply_apply v
  rw [hv] at hs
  refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) hs
  exact (DirectSum.coeLinearMap_lof D.piece i (d i)).symm

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
private theorem homologyRanges_span (q : ℕ) :
    (⨆ χ, LinearMap.range (homologyIncl M ν G h q χ).hom) = ⊤ := by
  let C := coordinateComplex M
  let K := C.sc q
  let F := HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) q
  let A (χ : Character T) := F.map (weightIncl M ν G h χ)
  let B (χ : Character T) := F.map (weightProj M ν G h χ)
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨v, rfl⟩ := (ModuleCat.epi_iff_surjective K.homologyπ).mp inferInstance x
  let w : C.X q := K.iCycles v
  obtain ⟨s, hs⟩ := sum_weightProjections (coordinateGrading M ν G q) w
  let vχ (χ : Character T) := ShortComplex.cyclesMap (B χ) v
  have hsum : (∑ χ ∈ s, ShortComplex.cyclesMap (A χ) (vχ χ)) = v := by
    apply (ModuleCat.mono_iff_injective K.iCycles).mp inferInstance
    change K.iCycles.hom (∑ χ ∈ s, ShortComplex.cyclesMap (A χ) (vχ χ)) = _
    rw [map_sum]
    have hpart (χ : Character T) :
        K.iCycles.hom (ShortComplex.cyclesMap (A χ) (vχ χ)) =
          ((weightProject (coordinateGrading M ν G q) χ) w).val := by
      have hA := congrArg (fun m => m (vχ χ)) (ShortComplex.cyclesMap_i (A χ))
      have hB := congrArg (fun m => m v) (ShortComplex.cyclesMap_i (B χ))
      change K.iCycles.hom (ShortComplex.cyclesMap (A χ) (vχ χ)) =
        ((A χ).τ₂) ((F.obj (weightComplex M ν G χ (h χ))).iCycles (vχ χ)) at hA
      rw [hA]
      change ((F.obj (weightComplex M ν G χ (h χ))).iCycles (vχ χ)) =
        weightProject (coordinateGrading M ν G q) χ w at hB
      rw [hB]
      rfl
    exact (Finset.sum_congr rfl (fun χ _ => hpart χ)).trans hs
  rw [← hsum]
  change K.homologyπ.hom (∑ χ ∈ s, ShortComplex.cyclesMap (A χ) (vχ χ)) ∈ _
  rw [map_sum]
  apply Submodule.sum_mem
  intro χ _
  refine (le_iSup (fun ψ => LinearMap.range (homologyIncl M ν G h q ψ).hom) χ) ?_
  refine ⟨((F.obj (weightComplex M ν G χ (h χ))).homologyπ) (vχ χ), ?_⟩
  exact congrArg (fun m => m (vχ χ)) (ShortComplex.homologyπ_naturality (A χ))

theorem koszulHomologyDecomposition : KoszulHomologyDecomposition.{u} := by
  intro k _ T n M ν G h q
  refine ⟨fun χ => LinearMap.range (homologyIncl M ν G h q χ).hom, ?_, ?_⟩
  · exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (homologyRanges_independent M ν G h q) (homologyRanges_span M ν G h q)
  · intro χ
    exact ⟨LinearEquiv.ofInjective _ (homologyIncl_injective M ν G h q χ)⟩

end HomogeneousHomology

private theorem weightGrading_ext {k Λ V : Type u} [Field k] [CommGroup Λ]
    [AddCommGroup V] [Module k V] {G H : WeightGrading k Λ V}
    (h : G.piece = H.piece) : G = H := by
  rcases G with ⟨p, hp⟩
  rcases H with ⟨q, hq⟩
  change p = q at h
  subst q
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem torCharacters : TorCharacters.{u} := by
  intro k _ T hT Y a n U H
  let R := polynomialAlgebra k n
  let M := (affineSections R).obj H.sheaf
  let : H.sheaf.IsFinitePresentation := H.coherent
  let hq : H.sheaf.IsQuasicoherent := inferInstance
  have : Module.Finite (PolynomialRing k n) M :=
    finitePresentationSections (affineRing R) H.sheaf
  obtain ⟨GA, E, hE, _, _⟩ := equivariantAffineComparison hT R U.action
  have : IsScalarTower k (↥R) ((affineSections R).obj H.sheaf) :=
    moduleOverBaseField_tower R ((affineSections R).obj H.sheaf)
  let GM := E H.sheaf hq H.lin
  let G : WeightGrading k (Character T) M := GM.toWeightGrading
  have hg (χ : Character T) (s : M) : s ∈ G.piece χ ↔ HasSectionWeight H.lin s χ :=
    (hE H.sheaf hq).2 H.lin χ s
  have hw (χ : Character T) : PreservesKoszulWeight M U.weight G χ :=
    koszulWeightPreservation U GA M GM χ
  refine ⟨fun q => koszulHomologyCharacter M U.weight G hw q, ?_, ?_⟩
  · refine ⟨G, hw, hg, ?_, ?_⟩
    · intro q χ
      have := coordinateHomologyFinite M q
      exact Module.Finite.of_injective (homologyIncl M U.weight G hw q χ).hom
        (homologyIncl_injective M U.weight G hw q χ)
    · intro q χ
      rfl
  · intro ch' hch'
    obtain ⟨G', hw', hg', _, he⟩ := hch'
    have hG : G' = G := by
      have hpieces : G'.piece = G.piece := by
        funext χ
        exact Submodule.ext (fun s => (hg' χ s).trans (hg χ s).symm)
      exact weightGrading_ext hpieces
    subst G'
    funext q
    ext χ
    exact he q χ



section ResidueLine

variable {k : Type u} [Field k] {T : GroupScheme k} {n : ℕ}

private theorem residueVariable_smul (i : Fin n) (v : residueModule k n) :
    (MvPolynomial.X i : PolynomialRing k n) • v = 0 := by
  let z : k := v
  change MvPolynomial.eval (fun _ => (0 : k)) (MvPolynomial.X i) * z = 0
  simp

private theorem residueCoordinateD_zero (i j : ℕ) :
    coordinateD (residueModule k n) i j = 0 := by
  by_cases hij : i = j + 1
  · subst i
    apply Finsupp.lhom_ext
    intro s v
    rw [coordinateD_single]
    simp only [residueVariable_smul, smul_zero, Finsupp.single_zero, Finset.sum_const_zero,
      LinearMap.zero_apply]
  · exact coordinateD_zero_of_shape _ _ _ (fun h => hij h.symm)

private def residueLinearEquiv : residueModule k n ≃ₗ[k] k where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' a x := by
    let z : k := x
    change MvPolynomial.eval (fun _ : Fin n => (0 : k)) (MvPolynomial.C a) * z = a * z
    rw [MvPolynomial.eval_C]

private theorem residueWeightTerm_eq_supported (ν : Fin n → Character T)
    (G : WeightGrading k (Character T) (residueModule k n))
    (hG : ∀ χ, G.piece χ = if χ = 1 then ⊤ else ⊥) (q : ℕ) (χ : Character T) :
    weightTerm (residueModule k n) ν G χ q =
      Finsupp.supported (residueModule k n) k {s | wedgeWeight ν s = χ} := by
  ext v
  rw [Finsupp.mem_supported]
  constructor
  · intro hv s hs
    change wedgeWeight ν s = χ
    have hvs := hv s
    rw [hG] at hvs
    by_contra hne
    have hni : (wedgeWeight ν s)⁻¹ * χ ≠ 1 := fun he =>
      hne (inv_mul_eq_one.mp he)
    rw [ite_eq_right hni, Submodule.mem_bot] at hvs
    exact Finsupp.mem_support_iff.mp hs hvs
  · intro hv s
    rw [hG]
    by_cases he : (wedgeWeight ν s)⁻¹ * χ = 1
    · simp [he]
    · rw [ite_eq_right he, Submodule.mem_bot]
      by_contra hne
      have hs : s ∈ v.support := Finsupp.mem_support_iff.mpr hne
      exact he (by rw [show χ = wedgeWeight ν s from (hv hs).symm, inv_mul_cancel])

set_option backward.isDefEq.respectTransparency false in
theorem residueKoszulWeights : ResidueKoszulWeights.{u} := by
  intro k _ T n ν G hG
  let M := residueModule k n
  have hd (χ : Character T) : PreservesKoszulWeight M ν G χ := by
    intro i j v _
    rw [residueCoordinateD_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  refine ⟨hd, ?_⟩
  intro q χ
  let C := weightComplex M ν G χ (hd χ)
  have hz (i j : ℕ) : C.d i j = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change coordinateD M i j v.val = 0
    rw [residueCoordinateD_zero, LinearMap.zero_apply]
  let S := C.sc q
  let h₀ := (ShortComplex.LeftHomologyData.ofZeros S (hz _ _) (hz _ _)).homologyIso
  change Module.finrank k S.homology = _
  rw [h₀.toLinearEquiv.finrank_eq]
  change Module.finrank k (weightTerm M ν G χ q) = _
  rw [residueWeightTerm_eq_supported ν G hG]
  rw [(Finsupp.supportedEquivFinsupp (R := k) (M := M) {s | wedgeWeight ν s = χ}).finrank_eq]
  let e := Finsupp.mapRange.linearEquiv (α := {s : WedgeIndex k n q // wedgeWeight ν s = χ})
    (residueLinearEquiv (k := k) (n := n))
  exact Module.finrank_eq_card_basis (Finsupp.basisSingleOne.map e.symm)

end ResidueLine


set_option backward.isDefEq.respectTransparency false in
theorem exteriorCharacterProduct : ExteriorCharacterProduct.{u} := by
  classical
  intro k _ T n ν
  let I := Fin (variableList k n).length
  let u : Finset I := Finset.univ
  let e := MonoidAlgebra.of ℤ (Character T)
  let w (s : Finset I) : Character T := ∏ i ∈ s, ν (variableIndex i)
  let f (s : Finset I) : CharacterRing T := (-1 : ℤ)^s.card • e (w s)
  have hu : u.card = n := by simp [u, I]
  calc
    _ = ∑ q ∈ Finset.range (n + 1), ∑ s ∈ u.powersetCard q, f s := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_subtype (p := fun s => s ∈ Set.powersetCard I q) (u.powersetCard q)
        (by intro s; simp [u, Set.powersetCard.mem_iff]) f]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro s _
      change (-1 : ℤ)^q • e (w s.val) = (-1 : ℤ)^s.val.card • e (w s.val)
      rw [s.property]
    _ = ∑ s ∈ u.powerset, f s := by
      have hsum : ∑ s ∈ u.powerset, f s =
          ∑ q ∈ Finset.range (u.card + 1), ∑ s ∈ u.powersetCard q, f s := by
        rw [Finset.powerset_card_disjiUnion]
        exact Finset.sum_disjiUnion _ _ _
      rw [hu] at hsum
      exact hsum.symm
    _ = ∏ i ∈ u, (1 - e (ν (variableIndex i))) := by
      rw [Finset.prod_sub]
      apply Finset.sum_congr rfl
      intro s _
      simp only [f, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        Finset.prod_const_one, mul_one, w, map_prod]
    _ = cotangentProduct ν := by
      exact (finCongr (variableList_length k n)).prod_comp (fun i => 1 - e (ν i))


section Pullbacks

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
variable {a : ModObj T.X Y} {b : ModObj T.X X}

set_option backward.isDefEq.respectTransparency false in
private theorem coherentEquivariantPullback (f : X ⟶ Y) (hf : IsEquivariantMap a b f)
    (F : EquivariantCoherent a) (hF : (Pull f F.sheaf).IsFinitePresentation) :
    ∃ (H : EquivariantCoherent b) (e : Pull f F.sheaf ≅ H.sheaf), IsEquivariantPullback f F H e := by
  obtain ⟨K, hK⟩ := linearizationPullback f hf F.lin
  refine ⟨⟨Pull f F.sheaf, hF, K⟩, Iso.refl _, fun S t y => ?_⟩
  obtain ⟨h, hh⟩ := hK S t y
  refine ⟨h, ?_⟩
  have he := congrArg (fun z => z ≫ (pullComp F.sheaf (actOn b t y) f).inv) hh
  simp only [Iso.refl_inv, Iso.refl_hom]
  rw [(Scheme.Modules.pullback y.left).map_id,
    (Scheme.Modules.pullback (actOn b t y).left).map_id, Category.id_comp]
  simpa only [Category.comp_id, Category.assoc, Iso.hom_inv_id] using he.symm

set_option backward.isDefEq.respectTransparency false in
private theorem openAffinePullback_coherent {R : TestAlgebra k}
    [IsNoetherianRing R] (f : affineScheme R ⟶ Y) [IsOpenImmersion f.left]
    (F : Y.left.Modules) [F.IsFinitePresentation] : (Pull f F).IsFinitePresentation := by
  let : IsAffine (affineScheme R).left := inferInstanceAs (IsAffine (Spec (affineRing R)))
  let U := f.left ''ᵁ ⊤
  let H := F.restrict f.left
  have hU : IsAffineOpen U := by
    rw [show U = f.left.opensRange from f.left.image_top_eq_opensRange]
    exact isAffineOpen_opensRange f.left
  let A : CommRingCat.{u} := affineRing R
  let φ := ((f.left.appIso ⊤).inv).hom
  let ψ := (Scheme.ΓSpecIso A).inv.hom
  have : Module.Finite Γ(Y.left, U) (F.val.obj (op U)) :=
    LinearAlgebraicGroups.ProjectiveFiniteness.finite_sections_of_isAffineOpen F hU
  have : Module.Finite Γ((affineScheme R).left, ⊤) (H.val.obj (op ⊤)) :=
    finite_restrictScalars_of_surjective φ
      (ConcreteCategory.bijective_of_isIso (f.left.appIso ⊤).inv).2 (F.val.obj (op U))
  have hfin : Module.Finite A ((moduleSpecΓFunctor (R := A)).obj H) := by
    let : Module.Finite Γ(Spec A, ⊤) (H.val.obj (op ⊤)) := inferInstanceAs
      (Module.Finite Γ((affineScheme R).left, ⊤) (H.val.obj (op ⊤)))
    exact finite_restrictScalars_of_surjective ψ
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).2 (H.val.obj (op ⊤))
  have hH : H.IsFinitePresentation := (finitePresentation_iff_finite_sections A H).mpr hfin
  exact (SheafOfModules.isFinitePresentation (affineScheme R).left.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback f.left).app F) hH

set_option backward.isDefEq.respectTransparency false in
theorem chartPullback : ChartPullback.{u} := by
  intro k _ T Y a n U F
  let : IsOpenImmersion U.inclusion.left := U.openImmersion
  let : F.sheaf.IsFinitePresentation := F.coherent
  let : IsNoetherianRing (↥(polynomialAlgebra k n)) :=
    inferInstanceAs (IsNoetherianRing (PolynomialRing k n))
  exact coherentEquivariantPullback U.inclusion U.equivariant F
    (openAffinePullback_coherent U.inclusion F.sheaf)

set_option backward.isDefEq.respectTransparency false in
private theorem originPullback_coherent {n : ℕ}
    (F : (affineScheme (polynomialAlgebra k n)).left.Modules) [F.IsFinitePresentation] :
    (Pull (origin k n) F).IsFinitePresentation := by
  let R := affineRing (polynomialAlgebra k n)
  let S := affineRing (CommAlgCat.of k k)
  let φ : R ⟶ S := CommRingCat.ofHom (MvPolynomial.aeval (fun _ : Fin n => (0 : k))).toRingHom
  have hq : (Pull (origin k n) F).IsQuasicoherent := pullback_spec_isQuasicoherent φ F
  let M := (moduleSpecΓFunctor (R := R)).obj F
  have : Module.Finite R M := finitePresentationSections R F
  have : Module.Finite S ((ModuleCat.extendScalars.{u,u,u} φ.hom).obj M) := by
    let : Algebra R S := φ.hom.toAlgebra
    exact Module.Finite.base_change R S M
  obtain ⟨e, _⟩ := affineSectionBaseChange φ F
  have he : Module.Finite S ((moduleSpecΓFunctor (R := S)).obj (Pull (origin k n) F)) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  exact (finitePresentation_iff_finite_sections S (Pull (origin k n) F)).mpr he

set_option backward.isDefEq.respectTransparency false in
theorem chartFiberCharacter : ChartFiberCharacter.{u} := by
  intro k _ T hT Y a n U F
  let : F.sheaf.IsFinitePresentation := F.coherent
  obtain ⟨H, e, he⟩ := coherentEquivariantPullback (origin k n) U.fixed F
    (originPullback_coherent F.sheaf)
  obtain ⟨GA, E, C, hE, hC, _, _⟩ := pointCharacterComparison T hT
  let hq := H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let R := CommAlgCat.of k k
  have : IsScalarTower k (↥R) ((affineSections R).obj H.sheaf) :=
    moduleOverBaseField_tower R ((affineSections R).obj H.sheaf)
  refine ⟨C (classOf H), H, e, (E H.sheaf hq H.lin).toWeightGrading, he, ?_, ?_⟩
  · exact hE H
  · exact hC H

end Pullbacks


section HomologyEuler

variable {k : Type u} [Field k]

/-- Additivity of finite alternating homology dimensions in a short exact
sequence of complexes. The top incoming boundary has zero source. -/
private theorem alternatingHomologyRank_additive
    (S : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ)) (hS : S.ShortExact)
    [∀ q, Module.Finite k (S.X₁.homology q)]
    [∀ q, Module.Finite k (S.X₂.homology q)]
    [∀ q, Module.Finite k (S.X₃.homology q)]
    (d : ℕ) (htop : IsZero (S.X₃.homology (d + 1))) :
    (∑ q ∈ Finset.range (d + 1), (-1 : ℤ)^q * Module.finrank k (S.X₂.homology q)) =
      (∑ q ∈ Finset.range (d + 1), (-1 : ℤ)^q * Module.finrank k (S.X₁.homology q)) +
      (∑ q ∈ Finset.range (d + 1), (-1 : ℤ)^q * Module.finrank k (S.X₃.homology q)) := by
  let A (q : ℕ) : ℤ := Module.finrank k (S.X₁.homology q)
  let B (q : ℕ) : ℤ := Module.finrank k (S.X₂.homology q)
  let C (q : ℕ) : ℤ := Module.finrank k (S.X₃.homology q)
  let δ (q : ℕ) := hS.δ (q + 1) q rfl
  let p : ℕ → ℤ
    | 0 => 0
    | q + 1 => Module.finrank k (LinearMap.range (δ q).hom)
  have hp : p (d + 1) = 0 := by
    change (Module.finrank k (LinearMap.range (δ d).hom) : ℤ) = 0
    have hz : δ d = 0 := htop.eq_of_src _ _
    rw [hz]
    simp
  have hstep (q : ℕ) : A q + C q - B q = p q + p (q + 1) := by
    let f := HomologicalComplex.homologyMap S.f q
    let g := HomologicalComplex.homologyMap S.g q
    have h₁ := (hS.homology_exact₁ (q + 1) q rfl).moduleCat_range_eq_ker
    have h₂ := (hS.homology_exact₂ q).moduleCat_range_eq_ker
    have hf := f.hom.finrank_range_add_finrank_ker
    have hg := g.hom.finrank_range_add_finrank_ker
    change LinearMap.range (δ q).hom = LinearMap.ker f.hom at h₁
    change LinearMap.range f.hom = LinearMap.ker g.hom at h₂
    rw [← h₁] at hf
    rw [← h₂] at hg
    have hc : (Module.finrank k (LinearMap.range g.hom) : ℤ) + p q = C q := by
      cases q with
      | zero =>
        have := hS.epi_g
        have : Epi g := by
          have he : Epi (g ≫ S.X₃.homologyι 0) := by
            change Epi (HomologicalComplex.homologyMap S.g 0 ≫ S.X₃.homologyι 0)
            rw [HomologicalComplex.homologyι_naturality]
            infer_instance
          have hg' : g = (g ≫ S.X₃.homologyι 0) ≫ inv (S.X₃.homologyι 0) := by simp
          rw [hg']
          infer_instance
        have hs := (ModuleCat.epi_iff_surjective g).mp inferInstance
        change (Module.finrank k (LinearMap.range g.hom) : ℤ) + 0 = _
        rw [LinearMap.range_eq_top.mpr hs, finrank_top, add_zero]
      | succ q =>
        have h₃ := (hS.homology_exact₃ (q + 1) q rfl).moduleCat_range_eq_ker
        change LinearMap.range g.hom = LinearMap.ker (δ q).hom at h₃
        have hδ := (δ q).hom.finrank_range_add_finrank_ker
        rw [← h₃, add_comm] at hδ
        dsimp only [p, C]
        exact_mod_cast hδ
    have hfa : (Module.finrank k (LinearMap.range f.hom) : ℤ) + p (q + 1) = A q := by
      dsimp only [p, A]
      exact_mod_cast hf
    have hgb : (Module.finrank k (LinearMap.range g.hom) : ℤ) +
        (Module.finrank k (LinearMap.range f.hom) : ℤ) = B q := by
      dsimp only [B]
      exact_mod_cast hg
    linarith
  have hsum (n : ℕ) : (∑ q ∈ Finset.range n, (-1 : ℤ)^q * (A q + C q - B q)) =
      -((-1 : ℤ)^n) * p n := by
    induction n with
    | zero => simp [p]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hstep, pow_succ]
      ring
  have hh := hsum (d + 1)
  rw [hp, mul_zero] at hh
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hh
  exact (sub_eq_zero.mp hh).symm

end HomologyEuler


section CoefficientMaps

variable {k : Type u} [Field k] {T : GroupScheme k} {n : ℕ}
variable {M N P : ModuleCat.{u} (polynomialAlgebra k n)}

private def overBaseMap (f : M ⟶ N) : M →ₗ[k] N where
  toFun := f
  map_add' := f.hom.map_add
  map_smul' a x := f.hom.map_smul (algebraMap k (polynomialAlgebra k n) a) x

private def coefficientMap (f : M ⟶ N) (q : ℕ) :
    (WedgeIndex k n q →₀ M) →ₗ[k] (WedgeIndex k n q →₀ N) :=
  Finsupp.mapRange.linearMap (overBaseMap f)

private lemma coefficientMap_apply (f : M ⟶ N) (q : ℕ)
    (v : WedgeIndex k n q →₀ M) (s : WedgeIndex k n q) :
    coefficientMap f q v s = f (v s) := rfl

private lemma coefficientMap_single (f : M ⟶ N) (q : ℕ) (s : WedgeIndex k n q) (v : M) :
    coefficientMap f q (Finsupp.single s v) = Finsupp.single s (f v) :=
  Finsupp.mapRange_single (hf := (overBaseMap f).map_zero)

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateD_commutes (f : M ⟶ N) (i j : ℕ) :
    (coordinateDOverBase N i j).comp (coefficientMap f i) =
      (coefficientMap f j).comp (coordinateDOverBase M i j) := by
  apply Finsupp.lhom_ext
  intro s v
  change coordinateD N i j (coefficientMap f i (Finsupp.single s v)) =
    coefficientMap f j (coordinateD M i j (Finsupp.single s v))
  by_cases hij : i = j + 1
  · subst i
    rw [coefficientMap_single, coordinateD_single, coordinateD_single, map_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [coefficientMap_single]
    apply congrArg (Finsupp.single (eraseWedge s l))
    change _ = f.hom (_ • (_ • v))
    simp only [LinearMap.map_smul]
  · rw [coordinateD_zero_of_shape N i j (fun h => hij h.symm),
      coordinateD_zero_of_shape M i j (fun h => hij h.symm), LinearMap.zero_apply,
      LinearMap.zero_apply, map_zero]

variable {ν : Fin n → Character T}
variable {GM : WeightGrading k (Character T) M} {GN : WeightGrading k (Character T) N}
variable {GP : WeightGrading k (Character T) P}
variable {χ : Character T}
variable (hM : PreservesKoszulWeight M ν GM χ) (hN : PreservesKoszulWeight N ν GN χ)
variable (hP : PreservesKoszulWeight P ν GP χ)

private def weightMap (f : M ⟶ N)
    (hf : ∀ ψ x, x ∈ GM.piece ψ → f x ∈ GN.piece ψ) :
    weightComplex M ν GM χ hM ⟶ weightComplex N ν GN χ hN where
  f q := ModuleCat.ofHom ((coefficientMap f q).restrict fun _ hv s =>
    hf _ _ (hv s))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact DFunLike.congr_fun (coordinateD_commutes f i j) v.val

set_option backward.isDefEq.respectTransparency false in
private theorem weightMap_shortExact (f : M ⟶ N) (g : N ⟶ P)
    (hf : ∀ ψ x, x ∈ GM.piece ψ → f x ∈ GN.piece ψ)
    (hg : ∀ ψ x, x ∈ GN.piece ψ → g x ∈ GP.piece ψ)
    (hi : Function.Injective f) (he : Function.Exact f g) (hs : Function.Surjective g) :
    ∃ w, (ShortComplex.mk (weightMap hM hN f hf) (weightMap hN hP g hg) w).ShortExact := by
  let F := weightMap hM hN f hf
  let G := weightMap hN hP g hg
  have w : F ≫ G = 0 := by
    ext q : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Finsupp.ext
    intro s
    change g (f (v.val s)) = 0
    exact he.apply_apply_eq_zero (v.val s)
  refine ⟨w, HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun q => ?_)⟩
  let Sq := (ShortComplex.mk F G w).map (HomologicalComplex.eval _ _ q)
  let ff := Sq.f
  let gg := Sq.g
  have hpiece (ψ : Character T) :=
    exactOnWeights GM GN GP (overBaseMap f) (overBaseMap g)
      (fun i _ hx => hf i _ hx) (fun i _ hx => hg i _ hx) hi he hs ψ
  have hfe (x : Sq.X₁) (s : WedgeIndex k n q) : (ff x).val s = f (x.val s) := rfl
  have hge (y : Sq.X₂) (s : WedgeIndex k n q) : (gg y).val s = g (y.val s) := rfl
  apply ModuleCat.shortComplex_shortExact Sq
  · intro y
    constructor
    · intro hy
      have hpre (s : WedgeIndex k n q) : ∃ x ∈ GM.piece ((wedgeWeight ν s)⁻¹ * χ),
          f x = y.val s := by
        let y₀ : GN.piece ((wedgeWeight ν s)⁻¹ * χ) := ⟨y.val s, y.property s⟩
        have hy₀ : g (y₀ : N) = 0 := by
          rw [← hge y s, hy]
          rfl
        have hh := (hpiece ((wedgeWeight ν s)⁻¹ * χ)).2.1 y₀
        obtain ⟨x, hx⟩ := hh.mp (Subtype.ext hy₀)
        exact ⟨x, x.property, congrArg Subtype.val hx⟩
      choose x hx hx' using hpre
      let v : WedgeIndex k n q →₀ M := Finsupp.equivFunOnFinite.symm x
      have hv (s : WedgeIndex k n q) : v s = x s :=
        congrFun (Finsupp.equivFunOnFinite.apply_symm_apply x) s
      let v₀ : Sq.X₁ := ⟨v, fun s => by rw [hv]; exact hx s⟩
      refine ⟨v₀, Subtype.ext (Finsupp.ext fun s => ?_)⟩
      rw [hfe, show v₀.val s = x s from hv s, hx']
    · rintro ⟨v, rfl⟩
      exact congrArg (fun t => t v) Sq.zero
  · intro x y hxy
    apply Subtype.ext
    apply Finsupp.ext
    intro s
    exact hi (by rw [← hfe x s, ← hfe y s, hxy])
  · intro z
    have hpre (s : WedgeIndex k n q) : ∃ y ∈ GN.piece ((wedgeWeight ν s)⁻¹ * χ),
        g y = z.val s := by
      obtain ⟨y, hy⟩ := (hpiece ((wedgeWeight ν s)⁻¹ * χ)).2.2 ⟨z.val s, z.property s⟩
      exact ⟨y, y.property, congrArg Subtype.val hy⟩
    choose y hy hy' using hpre
    let v : WedgeIndex k n q →₀ N := Finsupp.equivFunOnFinite.symm y
    have hv (s : WedgeIndex k n q) : v s = y s :=
      congrFun (Finsupp.equivFunOnFinite.apply_symm_apply y) s
    let v₀ : Sq.X₂ := ⟨v, fun s => by rw [hv]; exact hy s⟩
    refine ⟨v₀, Subtype.ext (Finsupp.ext fun s => ?_)⟩
    rw [hge, show v₀.val s = y s from hv s, hy']


private theorem weightHomologyFinite (M : ModuleCat.{u} (polynomialAlgebra k n))
    [Module.Finite (PolynomialRing k n) M]
    (G : WeightGrading k (Character T) M) (h : ∀ χ, PreservesKoszulWeight M ν G χ)
    (q : ℕ) (χ : Character T) :
    Module.Finite k ((weightComplex M ν G χ (h χ)).homology q) := by
  have := coordinateHomologyFinite M q
  exact Module.Finite.of_injective (homologyIncl M ν G h q χ).hom
    (homologyIncl_injective M ν G h q χ)

private theorem weightHomology_isZero_of_lt (M : ModuleCat.{u} (polynomialAlgebra k n))
    (G : WeightGrading k (Character T) M) (χ : Character T)
    (h : PreservesKoszulWeight M ν G χ) (q : ℕ) (hq : n < q) :
    IsZero ((weightComplex M ν G χ h).homology q) := by
  let C := weightComplex M ν G χ h
  have : IsEmpty (WedgeIndex k n q) := by
    refine ⟨fun s => (Nat.not_le_of_lt hq) ?_⟩
    simpa [s.property] using Finset.card_le_univ s.val
  have : Subsingleton (WedgeIndex k n q →₀ M) := inferInstance
  have : Subsingleton (weightTerm M ν G χ q) := inferInstance
  exact (C.sc q).isZero_homology_of_isZero_X₂
    (ModuleCat.isZero_iff_subsingleton.mpr (inferInstanceAs (Subsingleton (weightTerm M ν G χ q))))

set_option backward.isDefEq.respectTransparency false in
private theorem koszulEuler_additive
    [Module.Finite (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) N]
    [Module.Finite (PolynomialRing k n) P]
    (hM : ∀ χ, PreservesKoszulWeight M ν GM χ)
    (hN : ∀ χ, PreservesKoszulWeight N ν GN χ)
    (hP : ∀ χ, PreservesKoszulWeight P ν GP χ)
    (f : M ⟶ N) (g : N ⟶ P)
    (hf : ∀ ψ x, x ∈ GM.piece ψ → f x ∈ GN.piece ψ)
    (hg : ∀ ψ x, x ∈ GN.piece ψ → g x ∈ GP.piece ψ)
    (hi : Function.Injective f) (he : Function.Exact f g) (hs : Function.Surjective g) :
    (∑ q ∈ Finset.range (n + 1), (-1 : ℤ)^q • koszulHomologyCharacter N ν GN hN q) =
      (∑ q ∈ Finset.range (n + 1), (-1 : ℤ)^q • koszulHomologyCharacter M ν GM hM q) +
      (∑ q ∈ Finset.range (n + 1), (-1 : ℤ)^q • koszulHomologyCharacter P ν GP hP q) := by
  ext χ
  obtain ⟨w, hex⟩ := weightMap_shortExact (hM χ) (hN χ) (hP χ) f g hf hg hi he hs
  let S := ShortComplex.mk (weightMap (hM χ) (hN χ) f hf) (weightMap (hN χ) (hP χ) g hg) w
  have hfinM : ∀ q, Module.Finite k (S.X₁.homology q) := fun q => weightHomologyFinite M GM hM q χ
  have hfinN : ∀ q, Module.Finite k (S.X₂.homology q) := fun q => weightHomologyFinite N GN hN q χ
  have hfinP : ∀ q, Module.Finite k (S.X₃.homology q) := fun q => weightHomologyFinite P GP hP q χ
  have hEq := @alternatingHomologyRank_additive k _ S hex hfinM hfinN hfinP n
    (weightHomology_isZero_of_lt P GP χ (hP χ) (n + 1) (Nat.lt_succ_self n))
  let coeff : CharacterRing T →+ ℤ :=
    (Finsupp.applyAddHom χ).comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom
  change coeff _ = coeff (_ + _)
  have hc (z : ℤ) (p : CharacterRing T) : coeff (z • p) = z * coeff p := by
    change coeff (z • p) = z • coeff p
    exact map_zsmul coeff z p
  simp only [map_add, map_sum]
  simp_rw [hc]
  exact hEq

private def shiftedWeightMap (δ : Character T) (f : M ⟶ N)
    (hf : ∀ ψ x, x ∈ GM.piece ψ → f x ∈ GN.piece (δ * ψ))
    (hN' : PreservesKoszulWeight N ν GN (δ * χ)) :
    weightComplex M ν GM χ hM ⟶ weightComplex N ν GN (δ * χ) hN' where
  f q := ModuleCat.ofHom ((coefficientMap f q).restrict fun _ hv s => by
    change f _ ∈ GN.piece _
    simpa only [mul_left_comm ((wedgeWeight ν s)⁻¹) δ χ] using
      hf _ _ (hv s))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact DFunLike.congr_fun (coordinateD_commutes f i j) v.val

set_option backward.isDefEq.respectTransparency false in
private theorem shiftedWeightMap_isIso (δ : Character T) (e : M ≅ N)
    (he : ∀ ψ x, e.hom x ∈ GN.piece (δ * ψ) ↔ x ∈ GM.piece ψ)
    (hN' : PreservesKoszulWeight N ν GN (δ * χ)) :
    IsIso (shiftedWeightMap hM δ e.hom (fun ψ x => (he ψ x).mpr) hN') := by
  let f := shiftedWeightMap hM δ e.hom (fun ψ x => (he ψ x).mpr) hN'
  suffices ∀ q, IsIso (f.f q) by
    let := this
    exact HomologicalComplex.Hom.isIso_of_components f
  intro q
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro v w h
    apply Subtype.ext
    apply Finsupp.ext
    intro s
    exact e.toLinearEquiv.injective (congrArg (fun z => z.val s) h)
  · intro w
    let v : WedgeIndex k n q →₀ M := coefficientMap e.inv q w.val
    have hv : v ∈ weightTerm M ν GM χ q := by
      intro s
      apply (he _ _).mp
      change e.hom (e.inv (w.val s)) ∈ GN.piece _
      rw [show e.hom (e.inv (w.val s)) = w.val s from
        e.toLinearEquiv.apply_symm_apply _]
      simpa only [mul_left_comm ((wedgeWeight ν s)⁻¹) δ χ] using w.property s
    refine ⟨⟨v, hv⟩, Subtype.ext (Finsupp.ext fun s => ?_)⟩
    change e.hom (e.inv (w.val s)) = w.val s
    exact e.toLinearEquiv.apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
private theorem koszulCharacter_shift
    [Module.Finite (PolynomialRing k n) M] [Module.Finite (PolynomialRing k n) N]
    (hM' : ∀ χ, PreservesKoszulWeight M ν GM χ)
    (hN' : ∀ χ, PreservesKoszulWeight N ν GN χ)
    (δ : Character T) (e : M ≅ N)
    (he : ∀ ψ x, e.hom x ∈ GN.piece (δ * ψ) ↔ x ∈ GM.piece ψ)
    (q : ℕ) :
    koszulHomologyCharacter N ν GN hN' q =
      eChar δ * koszulHomologyCharacter M ν GM hM' q := by
  ext ψ
  change (koszulHomologyCharacter N ν GN hN' q).coeff ψ =
      (MonoidAlgebra.single δ 1 * koszulHomologyCharacter M ν GM hM' q).coeff ψ
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul]
  let χ := δ⁻¹ * ψ
  have hχ : δ * χ = ψ := mul_inv_cancel_left δ ψ
  change (Module.finrank k ((weightComplex N ν GN ψ (hN' ψ)).homology q) : ℤ) =
    Module.finrank k ((weightComplex M ν GM χ (hM' χ)).homology q)
  rw [← show δ * χ = ψ from hχ]
  let f := shiftedWeightMap (hM' χ) δ e.hom (fun i x => (he i x).mpr) (hN' (δ * χ))
  have : IsIso f := shiftedWeightMap_isIso (hM' χ) δ e he (hN' (δ * χ))
  exact congrArg (fun t : ℕ => (t : ℤ))
    (((HomologicalComplex.homologyFunctor (ModuleCat.{u} k) _ q).mapIso
      (asIso f)).toLinearEquiv.finrank_eq.symm)

end CoefficientMaps

section EquivariantInverseImage

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y Z : SchemeOver k}

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open private comparePull evalPullIso transport_eq_evalPullIso equivariant_actOn
  pullCongr_naturality twistLinearizationIso_hom comp_appTop_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

@[reassoc]
private theorem pullComp_naturality {F H : Y.left.Modules}
    (f : Z ⟶ X) (g : X ⟶ Y) (m : F ⟶ H) :
    (Scheme.Modules.pullback f.left).map ((Scheme.Modules.pullback g.left).map m) ≫
        (pullComp H f g).hom =
      (pullComp F f g).hom ≫ (Scheme.Modules.pullback (f ≫ g).left).map m :=
  ((Scheme.Modules.pullbackComp f.left g.left).hom.naturality m)

@[reassoc]
private theorem comparePull_naturality {F H : Y.left.Modules}
    (f : Z ⟶ X) (g : X ⟶ Y) {x : Z ⟶ Y} (e : f ≫ g = x) (m : F ⟶ H) :
    (Scheme.Modules.pullback f.left).map ((Scheme.Modules.pullback g.left).map m) ≫
        (comparePull H f g e).hom =
      (comparePull F f g e).hom ≫ (Scheme.Modules.pullback x.left).map m := by
  simp only [comparePull, Iso.trans_hom, Category.assoc, pullComp_naturality_assoc,
    pullCongr_naturality]

set_option backward.isDefEq.respectTransparency false in
private theorem evalPullIso_square {V : SchemeOver k} {F H : Y.left.Modules}
    {p q : X ⟶ Y} (f : V ⟶ X) {x y : V ⟶ Y} (hp : f ≫ p = x) (hq : f ≫ q = y)
    (L : Pull p F ≅ Pull q F) (K : Pull p H ≅ Pull q H) (m : F ⟶ H)
    (h : L.hom ≫ (Scheme.Modules.pullback q.left).map m =
      (Scheme.Modules.pullback p.left).map m ≫ K.hom) :
    (evalPullIso L f hp hq).hom ≫ (Scheme.Modules.pullback y.left).map m =
      (Scheme.Modules.pullback x.left).map m ≫ (evalPullIso K f hp hq).hom := by
  let P := Scheme.Modules.pullback f.left
  let A := comparePull F f p hp
  let B := comparePull H f p hp
  let C := comparePull F f q hq
  let D := comparePull H f q hq
  apply (cancel_epi A.hom).mp
  change A.hom ≫ (A.inv ≫ P.map L.hom ≫ C.hom) ≫ _ =
    A.hom ≫ (Scheme.Modules.pullback x.left).map m ≫ B.inv ≫ P.map K.hom ≫ D.hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comparePull_naturality f q hq m, ← reassoc_of% (comparePull_naturality f p hp m)]
  change P.map L.hom ≫ P.map ((Scheme.Modules.pullback q.left).map m) ≫ D.hom =
    P.map ((Scheme.Modules.pullback p.left).map m) ≫ B.hom ≫ B.inv ≫ P.map K.hom ≫ D.hom
  simp only [Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, h]

set_option backward.isDefEq.respectTransparency false in
private theorem evalPullIso_square_reflect {V : SchemeOver k} {F H : Y.left.Modules}
    {p q : X ⟶ Y} (f : V ⟶ X) {x y : V ⟶ Y} (hp : f ≫ p = x) (hq : f ≫ q = y)
    (L : Pull p F ≅ Pull q F) (K : Pull p H ≅ Pull q H) (m : F ⟶ H)
    [(Scheme.Modules.pullback f.left).Faithful]
    (h : (evalPullIso L f hp hq).hom ≫ (Scheme.Modules.pullback y.left).map m =
      (Scheme.Modules.pullback x.left).map m ≫ (evalPullIso K f hp hq).hom) :
    L.hom ≫ (Scheme.Modules.pullback q.left).map m =
      (Scheme.Modules.pullback p.left).map m ≫ K.hom := by
  let P := Scheme.Modules.pullback f.left
  let A := comparePull F f p hp
  let B := comparePull H f p hp
  let C := comparePull F f q hq
  let D := comparePull H f q hq
  apply P.map_injective
  apply (cancel_mono D.hom).mp
  have h' := congrArg (fun v => A.hom ≫ v) h
  change A.hom ≫ (A.inv ≫ P.map L.hom ≫ C.hom) ≫ _ =
    A.hom ≫ (Scheme.Modules.pullback x.left).map m ≫ B.inv ≫ P.map K.hom ≫ D.hom at h'
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h'
  rw [← comparePull_naturality f q hq m, ← reassoc_of% (comparePull_naturality f p hp m)] at h'
  change P.map L.hom ≫ P.map ((Scheme.Modules.pullback q.left).map m) ≫ D.hom =
    P.map ((Scheme.Modules.pullback p.left).map m) ≫ B.hom ≫ B.inv ≫ P.map K.hom ≫ D.hom at h'
  simpa only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc] using h'

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem linearizedMap_of_transport {a : ModObj T.X X} {F H : X.left.Modules}
    (L : Linearization a F) (K : Linearization a H) (m : F ⟶ H)
    (h : ∀ (Z : SchemeOver k) (t : Z ⟶ T.X) (x : Z ⟶ X),
      (transport a L.iso t x).hom ≫ (Scheme.Modules.pullback (actOn a t x).left).map m =
        (Scheme.Modules.pullback x.left).map m ≫ (transport a K.iso t x).hom) :
    IsLinearizedMap L K m := by
  let t := fst T.X X
  let x := snd T.X X
  let j := lift t x
  have hj : j = 𝟙 _ := by simp [j, t, x]
  have hj' : j.left = 𝟙 _ := congrArg Over.Hom.left hj
  let I : (Scheme.Modules.pullback j.left).Faithful :=
    Functor.Faithful.of_iso
      (Scheme.Modules.pullbackId (T.X ⊗ X).left).symm
      |> fun (hI : (Scheme.Modules.pullback (𝟙 (T.X ⊗ X).left)).Faithful) =>
          have := hI
          Functor.Faithful.of_iso (Scheme.Modules.pullbackCongr hj'.symm)
  have H := h (T.X ⊗ X) t x
  rw [transport_eq_evalPullIso, transport_eq_evalPullIso] at H
  exact evalPullIso_square_reflect j (lift_snd t x) rfl L.iso K.iso m H

variable {a : ModObj T.X Y} {b : ModObj T.X X}

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_map_linearized {f : X ⟶ Y} (hf : IsEquivariantMap a b f)
    {F H : Y.left.Modules} {L : Linearization a F} {K : Linearization a H}
    {m : F ⟶ H} (hm : IsLinearizedMap L K m) :
    IsLinearizedMap (pullbackLinearization hf L) (pullbackLinearization hf K)
      ((Scheme.Modules.pullback f.left).map m) := by
  let p := snd T.X X
  let q := b.smul
  let l := 𝟙 T.X ⊗ₘ f
  have hp : l ≫ snd T.X Y = p ≫ f := by simp [l, p]
  have hq : l ≫ a.smul = q ≫ f := hf.symm
  let A := evalPullIso L.iso l hp hq
  let B := evalPullIso K.iso l hp hq
  change (pullComp F p f).hom ≫ (A.hom ≫ (pullComp F q f).inv) ≫
      (Scheme.Modules.pullback q.left).map ((Scheme.Modules.pullback f.left).map m) =
    (Scheme.Modules.pullback p.left).map ((Scheme.Modules.pullback f.left).map m) ≫
      (pullComp H p f).hom ≫ (B.hom ≫ (pullComp H q f).inv)
  apply (cancel_mono (pullComp H q f).hom).mp
  simp only [Category.assoc, pullComp_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [pullComp_naturality, Iso.inv_hom_id_assoc]
  exact congrArg ((pullComp F p f).hom ≫ ·) (evalPullIso_square l hp hq L.iso K.iso m hm)

private abbrev canonicalPullback (f : X ⟶ Y) (hf : IsEquivariantMap a b f)
    (F : EquivariantCoherent a) (hF : (Pull f F.sheaf).IsFinitePresentation) :
    EquivariantCoherent b :=
  ⟨Pull f F.sheaf, hF, pullbackLinearization hf F.lin⟩

set_option backward.isDefEq.respectTransparency false in
private theorem canonicalPullback_equivariant (f : X ⟶ Y) (hf : IsEquivariantMap a b f)
    (F : EquivariantCoherent a) (hF : (Pull f F.sheaf).IsFinitePresentation) :
    IsEquivariantPullback f F (canonicalPullback f hf F hF) (Iso.refl _) := by
  intro Z t y
  refine ⟨equivariant_actOn hf, ?_⟩
  have hh := pullbackLinearization_transport hf F.lin.iso t y
  have he := congrArg (fun z => z ≫ (pullComp F.sheaf (actOn b t y) f).inv) hh
  simp only [Iso.refl_inv, Iso.refl_hom]
  rw [(Scheme.Modules.pullback y.left).map_id,
    (Scheme.Modules.pullback (actOn b t y).left).map_id, Category.id_comp, Category.comp_id]
  change (_ = (transport b (pullbackLinearizationIso hf F.lin.iso) t y).hom)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    using he.symm

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackComparison_linearized {f : X ⟶ Y} (hf : IsEquivariantMap a b f)
    {F : EquivariantCoherent a} {H : EquivariantCoherent b}
    {e : Pull f F.sheaf ≅ H.sheaf} (he : IsEquivariantPullback f F H e) :
    IsLinearizedMap (pullbackLinearization hf F.lin) H.lin e.hom := by
  apply linearizedMap_of_transport
  intro Z t y
  obtain ⟨h, hh⟩ := he Z t y
  let P := Scheme.Modules.pullback y.left
  let Q := Scheme.Modules.pullback (actOn b t y).left
  let R := transport b (pullbackLinearization hf F.lin).iso t y
  let C := pullComp F.sheaf (actOn b t y) f
  change P.map e.inv ≫ _ ≫ _ ≫ _ ≫ C.inv ≫ Q.map e.hom = _ at hh
  rw [← pullbackLinearization_transport_assoc hf F.lin.iso t y] at hh
  change P.map e.inv ≫ R.hom ≫ C.hom ≫ C.inv ≫ Q.map e.hom = _ at hh
  rw [Iso.hom_inv_id_assoc] at hh
  change R.hom ≫ Q.map e.hom = _
  rw [← hh, ← P.map_comp_assoc, e.hom_inv_id, P.map_id, Category.id_comp]

private theorem linearizedIso_inv {a : ModObj T.X X} {F H : X.left.Modules}
    {L : Linearization a F} {K : Linearization a H} {e : F ≅ H}
    (he : IsLinearizedMap L K e.hom) : IsLinearizedMap K L e.inv := by
  let P := Scheme.Modules.pullback (snd T.X X).left
  let Q := Scheme.Modules.pullback a.smul.left
  change L.iso.hom ≫ Q.map e.hom = P.map e.hom ≫ K.iso.hom at he
  change K.iso.hom ≫ Q.map e.inv = P.map e.inv ≫ L.iso.hom
  apply (cancel_epi (P.map e.hom)).mp
  rw [← Category.assoc (P.map e.hom), ← he, Category.assoc, ← Q.map_comp, e.hom_inv_id,
    Q.map_id, Category.comp_id, ← P.map_comp_assoc, e.hom_inv_id, P.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_twist_iso {f : X ⟶ Y} (hf : IsEquivariantMap a b f)
    (F : Y.left.Modules) (L : Linearization a F) (δ : Character T) :
    (pullbackLinearization hf (twistLinearization L δ)).iso.hom =
      (pullbackLinearization hf L).iso.hom ≫
        multiply _ ((fst T.X X).left.appTop (characterFunction δ)) := by
  let p := snd T.X X
  let q := b.smul
  let l := 𝟙 T.X ⊗ₘ f
  let P := Scheme.Modules.pullback l.left
  have hp : l ≫ snd T.X Y = p ≫ f := by simp [l, p]
  have hq : l ≫ a.smul = q ≫ f := hf.symm
  let C := comparePull F l a.smul hq
  let B := pullComp F q f
  have hc : l.left.appTop ((fst T.X Y).left.appTop (characterFunction δ)) =
      (fst T.X X).left.appTop (characterFunction δ) := by
    rw [← comp_appTop_apply]
    congr 2
    simp [l]
  change (pullComp F p f).hom ≫ ((comparePull F l (snd T.X Y) hp).inv ≫
      P.map (twistLinearization L δ).iso.hom ≫ C.hom) ≫ B.inv =
    ((pullComp F p f).hom ≫ ((comparePull F l (snd T.X Y) hp).inv ≫
      P.map L.iso.hom ≫ C.hom) ≫ B.inv) ≫ _
  rw [show (twistLinearization L δ).iso.hom = _ from twistLinearizationIso_hom δ L.iso,
    P.map_comp, pullback_multiply, hc]
  simp only [Category.assoc]
  rw [multiply_natural_assoc, multiply_natural]

end EquivariantInverseImage

section ClassMap

variable {k : Type u} [Field k] {T : GroupScheme k} {Y : SchemeOver k}
  {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n) (hT : IsSplitTorus T)

private def torCharacter (H : EquivariantCoherent U.action) : ℕ → CharacterRing T :=
  (torCharacters hT U H).exists.choose

private theorem torCharacter_spec (H : EquivariantCoherent U.action) :
    IsTorCharacter U H (torCharacter U hT H) :=
  (torCharacters hT U H).exists.choose_spec

private def chartEuler (H : EquivariantCoherent U.action) : CharacterRing T :=
  ∑ q ∈ Finset.range (n + 1), (-1 : ℤ)^q • torCharacter U hT H q

private abbrev ChartModule (H : EquivariantCoherent U.action) :=
  (affineSections (polynomialAlgebra k n)).obj H.sheaf

private theorem chartModule_finite (H : EquivariantCoherent U.action) :
    Module.Finite (PolynomialRing k n) (ChartModule U H) := by
  exact @finitePresentationSections (affineRing (polynomialAlgebra k n)) H.sheaf H.coherent

set_option backward.isDefEq.respectTransparency false in
private theorem torCharacter_eq (H : EquivariantCoherent U.action)
    (G : WeightGrading k (Character T) (ChartModule U H))
    (h : ∀ χ, PreservesKoszulWeight (ChartModule U H) U.weight G χ)
    (hg : ∀ χ s, s ∈ G.piece χ ↔ HasSectionWeight H.lin s χ) :
    letI := chartModule_finite U H
    torCharacter U hT H = koszulHomologyCharacter (ChartModule U H) U.weight G h := by
  let : Module.Finite (PolynomialRing k n) (ChartModule U H) := chartModule_finite U H
  obtain ⟨ch, hc, hu⟩ := torCharacters hT U H
  refine (hu _ (torCharacter_spec U hT H)).trans (hu _ ?_).symm
  exact ⟨G, h, hg, weightHomologyFinite _ G h, fun _ _ => rfl⟩

private abbrev chartWeights (GA : AffineGrading (polynomialAlgebra k n) U.action)
    (E : AffineModuleComparison (polynomialAlgebra k n) U.action GA)
    (H : EquivariantCoherent U.action) : WeightGrading k (Character T) (ChartModule U H) :=
  let hQ : H.sheaf.IsQuasicoherent := H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  letI : IsScalarTower k (↥(polynomialAlgebra k n)) (ChartModule U H) :=
    moduleOverBaseField_tower (polynomialAlgebra k n) (ChartModule U H)
  (E H.sheaf hQ H.lin).toWeightGrading

private theorem chartWeights_compatible (GA : AffineGrading (polynomialAlgebra k n) U.action)
    (E : AffineModuleComparison (polynomialAlgebra k n) U.action GA)
    (H : EquivariantCoherent U.action) (χ : Character T) :
    PreservesKoszulWeight (ChartModule U H) U.weight (chartWeights U GA E H) χ := by
  let : H.sheaf.IsFinitePresentation := H.coherent
  let : IsScalarTower k (↥(polynomialAlgebra k n)) (ChartModule U H) :=
    moduleOverBaseField_tower (polynomialAlgebra k n) (ChartModule U H)
  let hQ : H.sheaf.IsQuasicoherent := H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  exact koszulWeightPreservation U GA (ChartModule U H) (E H.sheaf hQ H.lin) χ

set_option backward.isDefEq.respectTransparency false in
private theorem chartEuler_exact {F H K : EquivariantCoherent U.action}
    (f : F.sheaf ⟶ H.sheaf) (g : H.sheaf ⟶ K.sheaf) (w : f ≫ g = 0)
    (hf : EquivariantHom f) (hg : EquivariantHom g)
    (hex : (ShortComplex.mk f g w).ShortExact) :
    chartEuler U hT H = chartEuler U hT F + chartEuler U hT K := by
  let S := affineSections (polynomialAlgebra k n)
  let : F.sheaf.IsFinitePresentation := F.coherent
  let : H.sheaf.IsFinitePresentation := H.coherent
  let : K.sheaf.IsFinitePresentation := K.coherent
  let := chartModule_finite U F
  let := chartModule_finite U H
  let := chartModule_finite U K
  obtain ⟨GA, E, hE, hMap, _⟩ := equivariantAffineComparison hT _ U.action
  let G := chartWeights U GA E
  let h := chartWeights_compatible U GA E
  have hG (V : EquivariantCoherent U.action) (χ) (s : ChartModule U V) :
      s ∈ (G V).piece χ ↔ HasSectionWeight V.lin s χ :=
    letI : V.sheaf.IsFinitePresentation := V.coherent
    (hE V.sheaf inferInstance).2 V.lin χ s
  obtain ⟨hi, he, hs⟩ := affineSectionsExact (ShortComplex.mk f g w) hex
  unfold chartEuler
  rw [torCharacter_eq U hT H (G H) (h H) (hG H),
    torCharacter_eq U hT F (G F) (h F) (hG F),
    torCharacter_eq U hT K (G K) (h K) (hG K)]
  exact koszulEuler_additive (h F) (h H) (h K) (S.map f) (S.map g)
    ((hMap _ _ inferInstance inferInstance _ _ f).mp hf)
    ((hMap _ _ inferInstance inferInstance _ _ g).mp hg) hi he hs

set_option backward.isDefEq.respectTransparency false in
private theorem chartEuler_shift {F H : EquivariantCoherent U.action}
    (δ : Character T) (i : F.sheaf ≅ H.sheaf)
    (hi : ∀ χ s, HasSectionWeight H.lin (i.hom.app ⊤ s) (δ * χ) ↔ HasSectionWeight F.lin s χ) :
    chartEuler U hT H = eChar δ • chartEuler U hT F := by
  let S := affineSections (polynomialAlgebra k n)
  let := chartModule_finite U F
  let := chartModule_finite U H
  obtain ⟨GA, E, hE, _, _⟩ := equivariantAffineComparison hT _ U.action
  let G := chartWeights U GA E
  let h := chartWeights_compatible U GA E
  have hG (V : EquivariantCoherent U.action) (χ) (s : ChartModule U V) :
      s ∈ (G V).piece χ ↔ HasSectionWeight V.lin s χ :=
    letI : V.sheaf.IsFinitePresentation := V.coherent
    (hE V.sheaf inferInstance).2 V.lin χ s
  have he (χ) (s : ChartModule U F) :
      (S.mapIso i).hom s ∈ (G H).piece (δ * χ) ↔ s ∈ (G F).piece χ :=
    (hG H _ _).trans ((hi χ s).trans (hG F _ _).symm)
  unfold chartEuler
  rw [torCharacter_eq U hT H (G H) (h H) (hG H),
    torCharacter_eq U hT F (G F) (h F) (hG F)]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [koszulCharacter_shift (h F) (h H) δ (S.mapIso i) he q, smul_comm]
  rfl

private theorem chartEuler_linearizedIso {F H : EquivariantCoherent U.action}
    {i : F.sheaf ≅ H.sheaf} (hi : IsLinearizedMap F.lin H.lin i.hom) :
    chartEuler U hT H = chartEuler U hT F := by
  have hh (χ) (s : Γ(F.sheaf, ⊤)) :
      HasSectionWeight H.lin (i.hom.app ⊤ s) (1 * χ) ↔ HasSectionWeight F.lin s χ := by
    rw [one_mul]
    refine ⟨fun hs => ?_, linearizedMap_preserves_sectionWeight hi⟩
    have h := linearizedMap_preserves_sectionWeight (linearizedIso_inv hi) hs
    have he : i.inv.app ⊤ (i.hom.app ⊤ s) = s := by
      change (i.hom ≫ i.inv).app ⊤ s = s
      rw [i.hom_inv_id]
      rfl
    change HasSectionWeight F.lin (i.inv.app ⊤ (i.hom.app ⊤ s)) χ at h
    rwa [he] at h
  rw [chartEuler_shift U hT 1 i hh, show eChar (1 : Character T) = 1 from map_one _, one_smul]

private theorem openPullback_shortExact {X Z : Scheme.{u}} (f : X ⟶ Z) [IsOpenImmersion f]
    (S : ShortComplex Z.Modules) (hS : S.ShortExact) :
    (S.map (Scheme.Modules.pullback f)).ShortExact := by
  let : (Scheme.Modules.pullback f).PreservesHomology :=
    LinearAlgebraicGroups.FlatCohomology.flatPullbackExact f
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map _

private theorem chartRestriction_finitePresentation (F : EquivariantCoherent a) :
    (Pull U.inclusion F.sheaf).IsFinitePresentation := by
  let : IsOpenImmersion U.inclusion.left := U.openImmersion
  let : F.sheaf.IsFinitePresentation := F.coherent
  let : IsNoetherianRing (↥(polynomialAlgebra k n)) :=
    inferInstanceAs (IsNoetherianRing (PolynomialRing k n))
  exact openAffinePullback_coherent U.inclusion F.sheaf

private abbrev restrictToChart (F : EquivariantCoherent a) : EquivariantCoherent U.action :=
  canonicalPullback U.inclusion U.equivariant F (chartRestriction_finitePresentation U F)

open private twistLinearizationIso_hom from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

set_option backward.isDefEq.respectTransparency false in
private theorem canonicalPullback_twist {X : SchemeOver k} {b : ModObj T.X X}
    {f : X ⟶ Y} (hf : IsEquivariantMap a b f)
    {F H : EquivariantCoherent a} {δ : Character T}
    (hF : (Pull f F.sheaf).IsFinitePresentation)
    (hH : (Pull f H.sheaf).IsFinitePresentation)
    (ht : IsTwist δ F H) :
    IsTwist δ (canonicalPullback f hf F hF) (canonicalPullback f hf H hH) := by
  obtain ⟨i, hi⟩ := ht
  let P := Scheme.Modules.pullback (CategoryTheory.CartesianMonoidalCategory.snd T.X Y).left
  let Q := Scheme.Modules.pullback a.smul.left
  have hl : IsLinearizedMap (twistLinearization F.lin δ) H.lin i.hom := by
    change (twistLinearization F.lin δ).iso.hom ≫ Q.map i.hom = P.map i.hom ≫ H.lin.iso.hom
    rw [hi, ← P.map_comp_assoc, i.hom_inv_id, P.map_id, Category.id_comp]
    rw [show (twistLinearization F.lin δ).iso.hom = _ from
      twistLinearizationIso_hom δ F.lin.iso, Category.assoc]
  let e := (Scheme.Modules.pullback f.left).mapIso i
  refine ⟨e, ?_⟩
  have hh := pullback_map_linearized hf hl
  let P' := Scheme.Modules.pullback (CategoryTheory.CartesianMonoidalCategory.snd T.X X).left
  let Q' := Scheme.Modules.pullback b.smul.left
  change (pullbackLinearization hf (twistLinearization F.lin δ)).iso.hom ≫ Q'.map e.hom =
    P'.map e.hom ≫ (pullbackLinearization hf H.lin).iso.hom at hh
  rw [pullback_twist_iso hf F.sheaf F.lin δ] at hh
  apply (cancel_epi (P'.map e.hom)).mp
  change P'.map e.hom ≫ (pullbackLinearization hf H.lin).iso.hom =
    P'.map e.hom ≫ P'.map e.inv ≫ (pullbackLinearization hf F.lin).iso.hom ≫
      multiply _ _ ≫ Q'.map e.hom
  rw [← P'.map_comp_assoc, e.hom_inv_id, P'.map_id, Category.id_comp]
  exact hh.symm.trans (Category.assoc _ _ _)

private def classMap : GZero a →ₗ[CharacterRing T] CharacterRing T :=
  liftClassMap (fun F => chartEuler U hT (restrictToChart U F))
    (fun f g w hf hg h => by
      let : IsOpenImmersion U.inclusion.left := U.openImmersion
      let S := (ShortComplex.mk f g w).map (Scheme.Modules.pullback U.inclusion.left)
      exact chartEuler_exact U hT S.f S.g S.zero (pullback_map_linearized U.equivariant hf)
        (pullback_map_linearized U.equivariant hg) (openPullback_shortExact U.inclusion.left _ h))
    (fun {δ F H} ht => by
      have hh := canonicalPullback_twist U.equivariant
        (chartRestriction_finitePresentation U F) (chartRestriction_finitePresentation U H) ht
      obtain ⟨e, he⟩ := sectionWeight_isTwist hT hh
      exact chartEuler_shift U hT δ e he)

private theorem classMap_apply (F : EquivariantCoherent a)
    (H : EquivariantCoherent U.action) (h : RestrictsTo U F H) :
    classMap U hT (classOf F) = chartEuler U hT H := by
  obtain ⟨e, he⟩ := h
  unfold classMap
  rw [liftClassMap_classOf]
  exact (chartEuler_linearizedIso U hT (pullbackComparison_linearized U.equivariant he)).symm

theorem derivedClassMap : DerivedClassMap.{u} := by
  intro k _ T hT Y a n U
  exact ⟨classMap U hT, fun F =>
    ⟨chartPullback U F, fun H h =>
      ⟨torCharacter U hT H, torCharacter_spec U hT H, classMap_apply U hT F H h⟩⟩⟩

end ClassMap

section OrdinaryFiber

variable {k : Type u} [Field k] {T : GroupScheme k} {Y : SchemeOver k}
  {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n)

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open private sectionWeight_pullback_of_iso from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

private abbrev BaseModule (H : EquivariantCoherent (pointAction T)) :=
  (affineSections (CommAlgCat.of k k)).obj H.sheaf

private abbrev originFiber (H : EquivariantCoherent U.action) :
    EquivariantCoherent (pointAction T) :=
  canonicalPullback (origin k n) U.fixed H (by
    let : H.sheaf.IsFinitePresentation := H.coherent
    exact originPullback_coherent H.sheaf)

set_option backward.isDefEq.respectTransparency false in
private theorem originSectionQuotient (H : EquivariantCoherent U.action) :
    letI := moduleOverBaseField_tower (polynomialAlgebra k n) (ChartModule U H)
    ∃ e : (ChartModule U H ⧸ listSubmodule (ChartModule U H) (variableList k n))
        ≃ₗ[k] BaseModule (originFiber U H),
      ∀ s, e (Submodule.Quotient.mk s) = pullSection (origin k n).left H.sheaf s := by
  let A := PolynomialRing k n
  let M := ChartModule U H
  let I := listIdeal (variableList k n)
  let φ : affineRing (polynomialAlgebra k n) ⟶ affineRing (CommAlgCat.of k k) :=
    CommRingCat.ofHom (MvPolynomial.aeval (fun _ : Fin n => (0 : k))).toRingHom
  let : H.sheaf.IsFinitePresentation := H.coherent
  obtain ⟨b, hb⟩ := affineSectionBaseChange φ H.sheaf
  let : IsScalarTower k (↥(polynomialAlgebra k n)) M :=
    moduleOverBaseField_tower (polynomialAlgebra k n) M
  let := evaluationAlgebra k n
  let c : (k ⊗[A] M) ≃ₗ[A] M ⧸ listSubmodule M (variableList k n) :=
    (TensorProduct.congr (quotientCoefficientsLinearEquiv k n).symm (LinearEquiv.refl A M)).trans
      (TensorProduct.quotTensorEquivQuotSMul M I)
  have hc (s : M) : c ((1 : k) ⊗ₜ[A] s) = Submodule.Quotient.mk s := by
    have hh : (quotientCoefficientsLinearEquiv k n).symm (1 : k) = 1 :=
      (quotientCoefficientsLinearEquiv k n).injective
        ((quotientCoefficientsLinearEquiv k n).apply_symm_apply 1 |>.trans (map_one (quotientCoefficientsEquiv)).symm)
    change TensorProduct.quotTensorEquivQuotSMul M I
      (TensorProduct.congr (quotientCoefficientsLinearEquiv k n).symm (LinearEquiv.refl A M)
        ((1 : k) ⊗ₜ[A] s)) = _
    rw [TensorProduct.congr_tmul, hh, LinearEquiv.refl_apply,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  let d : BaseModule (originFiber U H) ≃ₗ[k] k ⊗[A] M := b.toLinearEquiv
  let c' : (k ⊗[A] M) ≃ₗ[k] M ⧸ listSubmodule M (variableList k n) :=
    { c.toAddEquiv with
      map_smul' r z := by
        have he (w : k ⊗[A] M) : r • w = (MvPolynomial.C r : A) • w := by
          induction w using TensorProduct.inductionOn with
          | tmul x y =>
            rw [TensorProduct.smul_tmul']
            change (r * x) ⊗ₜ[A] y =
              (MvPolynomial.eval (fun _ => (0 : k)) (MvPolynomial.C r) * x) ⊗ₜ[A] y
            rw [MvPolynomial.eval_C]
          | add x y hx hy => rw [smul_add, smul_add, hx, hy]
        change c (r • z) = r • c z
        rw [he, map_smul]
        rfl }
  refine ⟨c'.symm.trans d.symm, fun s => ?_⟩
  apply d.injective
  change d (d.symm (c'.symm (Submodule.Quotient.mk s))) = d (pullSection (origin k n).left H.sheaf s)
  rw [d.apply_symm_apply]
  have hd : d (pullSection (origin k n).left H.sheaf s) = (1 : k) ⊗ₜ[A] s := hb s
  rw [hd]
  exact c'.symm_apply_eq.mpr (hc s).symm

private def zeroDegreeCoordinates (M : ModuleCat.{u} (polynomialAlgebra k n)) :
    (WedgeIndex k n 0 →₀ M) ≃ₗ[PolynomialRing k n] M :=
  (wedgeCoordinates M 0).symm.trans (coefficientZeroEquiv M (variableList k n))

private lemma zeroWedge_unique (s t : WedgeIndex k n 0) : s = t :=
  Subtype.ext ((Finset.card_eq_zero.mp s.property).trans (Finset.card_eq_zero.mp t.property).symm)

set_option backward.isDefEq.respectTransparency false in
private lemma zeroDegreeCoordinates_eq (M : ModuleCat.{u} (polynomialAlgebra k n))
    (s : WedgeIndex k n 0) (v : WedgeIndex k n 0 →₀ M) :
    zeroDegreeCoordinates M v = v s := by
  have hv : v = Finsupp.single s (v s) := by ext t; rw [zeroWedge_unique t s, Finsupp.single_eq_same]
  conv_lhs => rw [hv]
  rw [zeroDegreeCoordinates, LinearEquiv.trans_apply,
    ← wedgeCoordinates_basis_tmul M s (v s), LinearEquiv.symm_apply_apply,
    coefficientZeroEquiv_tmul, listBasis_apply, exteriorPower.ιMulti_family,
    exteriorPower.zeroEquiv_ιMulti, one_smul]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem degreeZeroCoordinates_boundary (M : ModuleCat.{u} (polynomialAlgebra k n)) :
    LinearMap.range ((zeroDegreeCoordinates M).toLinearMap.comp (coordinateD M 1 0)) =
      listSubmodule M (variableList k n) := by
  let X := variableList k n
  let e := (wedgeCoordinates M 1).symm
  let f := (coefficientZeroEquiv M X).toLinearMap.comp (coefficientDifferential M X 0)
  have h : (zeroDegreeCoordinates M).toLinearMap.comp (coordinateD M 1 0) =
      f.comp e.toLinearMap := by
    apply LinearMap.ext
    intro v
    change (coefficientZeroEquiv M X) ((wedgeCoordinates M 0).symm
      (wedgeCoordinates M 0 (((KoszulCoefficientComplex M).d 1 0).hom (e v)))) =
        coefficientZeroEquiv M X (coefficientDifferential M X 0 (e v))
    let w : (KoszulCoefficientComplex M).X 0 :=
      ((KoszulCoefficientComplex M).d 1 0).hom (e v)
    change (coefficientZeroEquiv M X) ((wedgeCoordinates M 0).symm (wedgeCoordinates M 0 w)) = _
    calc
      _ = coefficientZeroEquiv M X w :=
        congrArg (coefficientZeroEquiv M X) ((wedgeCoordinates M 0).symm_apply_apply w)
      _ = _ := by
        change (coefficientZeroEquiv M X) (((KoszulCoefficientComplex M).d 1 0).hom (e v)) = _
        have hd : (KoszulCoefficientComplex M).d 1 0 =
            ModuleCat.ofHom (coefficientDifferential M X 0) := by
          exact ChainComplex.of_d
            (fun j => ModuleCat.of (PolynomialRing k n)
              ((⋀[PolynomialRing k n]^j (Fin X.length → PolynomialRing k n)) ⊗[PolynomialRing k n] M))
            (fun j => ModuleCat.ofHom (coefficientDifferential M X j)) 0
        exact congrArg (fun a => coefficientZeroEquiv M X (a.hom (e v))) hd
  rw [h, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  exact degreeZeroBoundary_range M X

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryFiberHomology (H : EquivariantCoherent U.action)
    (G : WeightGrading k (Character T) (ChartModule U H))
    (hG : ∀ χ s, s ∈ G.piece χ ↔ HasSectionWeight H.lin s χ)
    (h : ∀ χ, PreservesKoszulWeight (ChartModule U H) U.weight G χ)
    (A : WeightGrading k (Character T) (BaseModule (originFiber U H)))
    (hA : ∀ χ s, s ∈ A.piece χ ↔ HasSectionWeight (originFiber U H).lin s χ)
    (χ : Character T) :
    Nonempty ((weightComplex (ChartModule U H) U.weight G χ (h χ)).homology 0 ≅
      ModuleCat.of k (A.piece χ)) := by
  let M := ChartModule U H
  let V := BaseModule (originFiber U H)
  let C := coordinateComplex M
  let : IsScalarTower k (↥(polynomialAlgebra k n)) M :=
    moduleOverBaseField_tower (polynomialAlgebra k n) M
  let Cχ := weightComplex M U.weight G χ (h χ)
  let W := coordinateGrading M U.weight G 0
  obtain ⟨e, he⟩ := originSectionQuotient U H
  let c := zeroDegreeCoordinates M
  let p : (WedgeIndex k n 0 →₀ M) →ₗ[k] V :=
    e.toLinearMap.comp (((listSubmodule M (variableList k n)).mkQ.comp c.toLinearMap).restrictScalars k)
  have hps (v : WedgeIndex k n 0 →₀ M) (s : WedgeIndex k n 0) :
      p v = pullSection (origin k n).left H.sheaf (v s) := by
    change e (Submodule.Quotient.mk (c v)) = _
    rw [he, zeroDegreeCoordinates_eq M s]
  let s₀ : WedgeIndex k n 0 := ⟨∅, rfl⟩
  have hp (ψ : Character T) (v : WedgeIndex k n 0 →₀ M) (hv : v ∈ W.piece ψ) : p v ∈ A.piece ψ := by
    rw [hps v s₀, hA]
    apply sectionWeight_pullback_of_iso U.fixed H.lin (originFiber U H).lin rfl
    apply (hG ψ (v s₀)).mp
    have hv₀ := (show v ∈ weightTerm M U.weight G ψ 0 from hv) s₀
    simpa only [wedgeWeight, show s₀.val = ∅ from rfl, Finset.prod_empty, inv_one, one_mul] using hv₀
  have hs : Function.Surjective p :=
    e.surjective.comp ((Submodule.mkQ_surjective _).comp c.surjective)
  have he' : Function.Exact (coordinateDOverBase M 1 0) p := by
    intro v
    change e (Submodule.Quotient.mk (c v)) = 0 ↔ v ∈ LinearMap.range (coordinateD M 1 0)
    rw [← e.map_zero, e.injective.eq_iff, Submodule.Quotient.mk_eq_zero,
      ← degreeZeroCoordinates_boundary, LinearMap.range_comp]
    constructor
    · rintro ⟨w, hw, hwv⟩
      exact (c.injective hwv) ▸ hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  let f := Cχ.d 1 0
  let g : Cχ.X 0 ⟶ ModuleCat.of k (A.piece χ) := ModuleCat.ofHom (p.restrict (hp χ))
  have hw (v : Cχ.X 1) : g (f v) = 0 := by
    apply Subtype.ext
    exact he'.apply_apply_eq_zero v.val
  have hw' : f ≫ g = 0 := by
    apply ModuleCat.hom_ext
    ext v : 1
    exact hw v
  let S := ShortComplex.mk f g hw'
  have hse : S.Exact := by
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
    intro v
    constructor
    · intro hv
      obtain ⟨w, hw⟩ := (he' v.val).mp (congrArg Subtype.val hv)
      refine ⟨weightProject (coordinateGrading M U.weight G 1) χ w, Subtype.ext ?_⟩
      have hn := weightProject_natural (coordinateGrading M U.weight G 1) W
        (coordinateDOverBase M 1 0) (fun ψ _ hz => h ψ 1 0 _ hz) χ w
      change _ = weightProject W χ (coordinateDOverBase M 1 0 w) at hn
      rw [hw, weightProject_of_mem W χ v] at hn
      have hv' := congrArg Subtype.val hn
      exact hv'
    · rintro ⟨w, rfl⟩
      exact hw w
  have hsur : Function.Surjective g := by
    intro v
    obtain ⟨w, hw⟩ := hs v.val
    refine ⟨weightProject W χ w, ?_⟩
    have hn := weightProject_natural W A p (fun ψ _ hz => hp ψ _ hz) χ w
    change g (weightProject W χ w) = weightProject A χ (p w) at hn
    rw [hw, weightProject_of_mem A χ v] at hn
    exact hn
  have hEpi : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr hsur
  let D := Cχ.sc' 1 0 0
  have hz : D.g = 0 := Cχ.shape 0 0 (by simp [ComplexShape.down])
  let hcol : IsColimit (CokernelCofork.ofπ g hw') := hse.gIsCokernel
  have hprev : (ComplexShape.down ℕ).prev 0 = 1 := ComplexShape.prev_eq' _ rfl
  have hnext : (ComplexShape.down ℕ).next 0 = 0 := by
    simp [ComplexShape.next, ComplexShape.down]
  refine ⟨Cχ.homologyIsoSc' 1 0 0 hprev hnext ≪≫ ?_⟩
  exact (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork D hz _ hcol).homologyIso

end OrdinaryFiber

section KoszulPointModules

variable {k : Type u} [Field k] {T : GroupScheme k} {Y : SchemeOver k}
  {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n) (hT : IsSplitTorus T)

private theorem chartEuler_eq_zero_of_homology (H : EquivariantCoherent U.action)
    (hz : ∀ q, IsZero ((KoszulCoefficientComplex (ChartModule U H)).homology q)) :
    chartEuler U hT H = 0 := by
  obtain ⟨G, h, hG, hFin, hc⟩ := torCharacter_spec U hT H
  have hz' (q : ℕ) : IsZero ((coordinateComplex (ChartModule U H)).homology q) := by
    let M := ChartModule U H
    let F := affineBaseRestriction k n
    let C := KoszulCoefficientComplex M
    let C₀ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C
    let i : F.obj (C.homology q) ≅ C₀.homology q := ((C.sc q).mapHomologyIso F).symm
    let j := (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) _ q).mapIso (coordinateComplexIso M)
    exact (i ≪≫ j).isZero_iff.mp (F.map_isZero (hz q))
  have hc₀ (q : ℕ) : torCharacter U hT H q = 0 := by
    ext χ
    change (torCharacter U hT H q).coeff χ = 0
    rw [hc q χ]
    let : Subsingleton ((coordinateComplex (ChartModule U H)).homology q) :=
      ModuleCat.subsingleton_of_isZero (hz' q)
    let : Subsingleton ((weightComplex _ U.weight G χ (h χ)).homology q) :=
      (homologyIncl_injective _ U.weight G h q χ).subsingleton
    rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  simp only [chartEuler, hc₀, smul_zero, Finset.sum_const_zero]

private theorem koszulHomology_annihilated_by_coefficient
    (M : ModuleCat.{u} (polynomialAlgebra k n)) (r : PolynomialRing k n)
    (hr : ∀ x : M, r • x = 0) (q : ℕ) (x : (KoszulCoefficientComplex M).homology q) :
    r • x = 0 := by
  let C := KoszulCoefficientComplex M
  let K := C.sc q
  change r • (x : K.homology) = 0
  obtain ⟨v, rfl⟩ := (ModuleCat.epi_iff_surjective K.homologyπ).mp inferInstance x
  change r • K.homologyπ.hom v = 0
  rw [← map_smul]
  suffices r • v = 0 by rw [this, map_zero]
  apply (ModuleCat.mono_iff_injective K.iCycles).mp inferInstance
  change K.iCycles.hom (r • v) = K.iCycles.hom 0
  rw [map_smul, map_zero]
  let w : (KoszulCoefficientComplex M).X q := K.iCycles.hom v
  change r • w = 0
  apply (wedgeCoordinates M q).injective
  rw [(wedgeCoordinates M q).map_smul, (wedgeCoordinates M q).map_zero]
  ext s
  exact hr _

private theorem chartEuler_eq_zero_of_nonzero_coordinate
    (H : EquivariantCoherent U.action) (i : Fin n) (c : k) (hc : c ≠ 0)
    (hx : ∀ x : ChartModule U H,
      (MvPolynomial.X i : PolynomialRing k n) • x = (MvPolynomial.C c : PolynomialRing k n) • x) :
    chartEuler U hT H = 0 := by
  let M := ChartModule U H
  apply chartEuler_eq_zero_of_homology U hT H
  intro q
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq (0 : (KoszulCoefficientComplex M).homology q)
  intro x
  have h1 := koszulHomology_annihilated_by_coefficient M
    (MvPolynomial.X i - MvPolynomial.C c) (fun x => by rw [sub_smul, hx, sub_self]) q x
  have h2 := annihilates_homology M (variableList k n) (MvPolynomial.X i) (variable_mem_listIdeal i) q x
  let z : (KoszulCoefficientComplex M).homology q := x
  have h1' : (MvPolynomial.X i : PolynomialRing k n) • z -
      (MvPolynomial.C c : PolynomialRing k n) • z = 0 := by
    rw [← sub_smul]
    exact h1
  have h2' : (MvPolynomial.X i : PolynomialRing k n) • z = 0 := h2
  have hz : (MvPolynomial.C c : PolynomialRing k n) • z = 0 := by
    rwa [h2', zero_sub, neg_eq_zero] at h1'
  change z = 0
  calc
    z = (1 : PolynomialRing k n) • z := (one_smul _ _).symm
    _ = (MvPolynomial.C (c⁻¹ * c) : PolynomialRing k n) • z := by rw [inv_mul_cancel₀ hc, map_one]
    _ = 0 := by rw [map_mul, mul_smul, hz, smul_zero]

open private WeightGrading.mapLinearEquiv from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

private theorem wedgeCharacter_coeff (ν : Fin n → Character T) (q : ℕ) (χ : Character T) :
    (∑ s : WedgeIndex k n q, eChar (wedgeWeight ν s)).coeff χ =
      (Fintype.card {s : WedgeIndex k n q // wedgeWeight ν s = χ} : ℤ) := by
  classical
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, eChar,
    MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Fintype.card_subtype]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
private theorem chartEuler_eq_cotangent_of_residue
    (H : EquivariantCoherent U.action) (i : ChartModule U H ≅ residueModule k n)
    (htriv : ∀ s : ChartModule U H, HasSectionWeight H.lin s 1) :
    chartEuler U hT H = cotangentProduct U.weight := by
  let M := ChartModule U H
  let N := residueModule k n
  let := chartModule_finite U H
  let : Module.Finite (PolynomialRing k n) N := Module.Finite.equiv i.toLinearEquiv
  obtain ⟨G, hG, hs, _, _⟩ := torCharacter_spec U hT H
  have ht : G.piece 1 = ⊤ := eq_top_iff.mpr (fun s _ => (hs 1 s).mpr (htriv s))
  have hbot {χ : Character T} (hne : χ ≠ 1) : G.piece χ = ⊥ := by
    have hdis : Disjoint (G.piece χ) (G.piece 1) :=
      G.internal.submodule_iSupIndep.pairwiseDisjoint hne
    rwa [ht, disjoint_top] at hdis
  let e : M ≃ₗ[k] N := LinearEquiv.ofBijective (overBaseMap i.hom) i.toLinearEquiv.bijective
  let G' := WeightGrading.mapLinearEquiv G e
  have he (χ) (s : M) : i.hom s ∈ G'.piece χ ↔ s ∈ G.piece χ := by
    change e s ∈ (G.piece χ).map e.toLinearMap ↔ _
    rw [Submodule.mem_map]
    exact ⟨fun ⟨x, hx, he⟩ => e.injective he ▸ hx, fun hx => ⟨s, hx, rfl⟩⟩
  have hG' (χ) : G'.piece χ = if χ = 1 then ⊤ else ⊥ := by
    obtain rfl | hne := eq_or_ne χ 1
    · change (G.piece 1).map e.toLinearMap = _
      simp [ht, e.range]
    · change (G.piece χ).map e.toLinearMap = _
      simp [hbot hne, hne]
  obtain ⟨h', hdim⟩ := residueKoszulWeights U.weight G' hG'
  have hchar (q : ℕ) :
      torCharacter U hT H q = ∑ s : WedgeIndex k n q, eChar (wedgeWeight U.weight s) := by
    rw [torCharacter_eq U hT H G hG hs]
    have hc := koszulCharacter_shift hG h' 1 i (fun χ s => by rw [one_mul]; exact he χ s) q
    rw [show eChar (1 : Character T) = 1 from map_one _, one_mul] at hc
    rw [← hc]
    ext χ
    change (Module.finrank k ((weightComplex N U.weight G' χ (h' χ)).homology q) : ℤ) = _
    rw [hdim, wedgeCharacter_coeff]
  simp only [chartEuler, hchar]
  exact exteriorCharacterProduct U.weight

end KoszulPointModules

section PointGeometry

variable {k : Type u} [Field k] {T : GroupScheme k} {Y : SchemeOver k}
  {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n) (hT : IsSplitTorus T)

private theorem openPullback_pushforward_isZero {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : X ⟶ Y)
    [IsOpenImmersion j] (h : Disjoint (Set.range i) (Set.range j)) (M : Z.Modules) :
    IsZero ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pushforward i).obj M)) := by
  let N := (Scheme.Modules.pushforward i).obj M
  apply ((Scheme.Modules.restrictFunctorIsoPullback j).app N).isZero_iff.mp
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Scheme.Modules.hom_ext
  intro V
  have hV : i ⁻¹ᵁ (j ''ᵁ V) = ⊥ := by
    apply bot_unique
    intro z hz
    change i z ∈ j '' (V : Set X) at hz
    obtain ⟨x, _, hx⟩ := hz
    exact (Set.disjoint_left.mp h (Set.mem_range_self z) ⟨x, hx⟩).elim
  let S : TopCat.Sheaf Ab Z := ⟨M.presheaf, M.isSheaf⟩
  have hz : IsZero Γ(M, i ⁻¹ᵁ (j ''ᵁ V)) := (S.isTerminalOfEqEmpty hV).isZero
  have hh : IsZero Γ(N.restrict j, V) := (N.restrictAppIso j V).isZero_iff.mpr
    (by rw [Scheme.Modules.pushforward_obj_obj]; exact hz)
  exact hh.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private def sectionsOfAffinePushforward {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (L : (Spec S).Modules) :
    (moduleSpecΓFunctor (R := R)).obj ((Scheme.Modules.pushforward (Spec.map φ)).obj L) ≅
      (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := S)).obj L) := by
  let A := pushforwardCompModulesSpecToSheafIso φ
  let P := A.app L
  let D := (TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec R)) ⋙
    (CategoryTheory.evaluation (Spec R).Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)
  refine D.mapIso P ≪≫ eqToIso ?_
  change (ModuleCat.restrictScalars φ.hom).obj
    (((modulesSpecToSheaf (R := S)).obj L).presheaf.obj (op ((Spec.map φ) ⁻¹ᵁ ⊤))) = _
  rw [Scheme.Hom.preimage_top]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def restrictPushforwardIso (y : pointScheme k ⟶ Y)
    (z : pointScheme k ⟶ affineScheme (polynomialAlgebra k n)) (hz : z ≫ U.inclusion = y)
    {F : EquivariantCoherent a} {L : EquivariantCoherent (pointAction T)}
    (e : F.sheaf ≅ (Scheme.Modules.pushforward y.left).obj L.sheaf) :
    (restrictToChart U F).sheaf ≅ (Scheme.Modules.pushforward z.left).obj L.sheaf := by
  let : IsOpenImmersion U.inclusion.left := U.openImmersion
  let J := Scheme.Modules.pullback U.inclusion.left
  let R := Scheme.Modules.pushforward U.inclusion.left
  let p := Scheme.Modules.pushforward z.left
  let c := (Scheme.Modules.pushforwardComp z.left U.inclusion.left).app L.sheaf
  let h := congrArg Over.Hom.left hz
  let d := (Scheme.Modules.pushforwardCongr (show z.left ≫ U.inclusion.left = y.left from h)).app L.sheaf
  let adj := Scheme.Modules.pullbackPushforwardAdjunction U.inclusion.left
  have hC : IsIso (adj.counit.app (p.obj L.sheaf)) := by infer_instance
  exact J.mapIso (e ≪≫ d.symm ≪≫ c.symm) ≪≫ asIso (adj.counit.app (p.obj L.sheaf))

private theorem evalAlgHom_of_vars_vanish (φ : PolynomialRing k n →ₐ[k] k)
    (h : ∀ i : Fin n, φ (MvPolynomial.X i) = 0) :
    φ = MvPolynomial.aeval (fun _ : Fin n => (0 : k)) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [MvPolynomial.aeval_X, h]

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
private theorem chartEuler_disjoint (y : pointScheme k ⟶ Y) (F : EquivariantCoherent a)
    (hy : IsPointClass y F) (hd : IsEmpty (pullback U.point y).left) :
    classMap U hT (classOf F) = 0 := by
  classical
  obtain ⟨L, i, e, _, _⟩ := hy
  let H := restrictToChart U F
  let j := U.inclusion
  have hF : classMap U hT (classOf F) = chartEuler U hT H := by
    unfold classMap
    rw [liftClassMap_classOf]
  rw [hF]
  let : IsOpenImmersion j.left := U.openImmersion
  by_cases hchart : Set.range y.left ⊆ Set.range j.left
  · let z : pointScheme k ⟶ affineScheme (polynomialAlgebra k n) :=
      Over.homMk (IsOpenImmersion.lift j.left y.left hchart) (by
        rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w y])
    have hz : z ≫ j = y := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    let A := polynomialAlgebra k n
    let S := CommAlgCat.of k k
    let φ : A ⟶ S := (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of k)).preimage z |>.unop
    have hφ : (testSpec k).map φ.op = z :=
      (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage z
    have hne : z ≠ origin k n := by
      intro he
      have hxy : U.point = y := by rw [← hz, he]
      let f := pullback.lift (𝟙 (pointScheme k)) (𝟙 (pointScheme k)) (by simpa using hxy)
      let p : (pointScheme k).left := IsLocalRing.closedPoint k
      exact hd.false (f.left p)
    have hex : ∃ q : Fin n, φ (MvPolynomial.X q) ≠ 0 := by
      by_contra! hh
      have ha : φ.hom = MvPolynomial.aeval (fun _ : Fin n => (0 : k)) :=
        evalAlgHom_of_vars_vanish φ.hom hh
      have he : φ = CommAlgCat.ofHom (MvPolynomial.aeval (fun _ : Fin n => (0 : k))) :=
        CommAlgCat.hom_ext ha
      apply hne
      change z = (testSpec k).map (CommAlgCat.ofHom
        (MvPolynomial.aeval (fun _ : Fin n => (0 : k)))).op
      rw [← hφ, he]
    obtain ⟨q, hq⟩ := hex
    let e' := restrictPushforwardIso U y z hz e
    let ψ : affineRing A ⟶ affineRing S := CommRingCat.ofHom φ.hom.toRingHom
    let d := (Scheme.Modules.pushforwardCongr
      (show z.left = Spec.map ψ from (congrArg Over.Hom.left hφ).symm)).app L.sheaf
    let e'' := (affineSections A).mapIso (e' ≪≫ d) ≪≫ sectionsOfAffinePushforward ψ L.sheaf
    apply chartEuler_eq_zero_of_nonzero_coordinate U hT H q (φ (MvPolynomial.X q)) hq
    intro x
    apply e''.toLinearEquiv.injective
    rw [map_smul, map_smul]
    change φ (MvPolynomial.X q) • (e''.hom x : BaseModule L) =
      φ (MvPolynomial.C (φ (MvPolynomial.X q))) • (e''.hom x : BaseModule L)
    rw [show φ (MvPolynomial.C (φ (MvPolynomial.X q))) = φ (MvPolynomial.X q) from φ.hom.commutes _]
  · have hd' : Disjoint (Set.range y.left) (Set.range j.left) := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨p, rfl⟩ hp
      apply hchart
      rintro _ ⟨q, rfl⟩
      have hpq : (show PrimeSpectrum k from p) = q := Subsingleton.elim _ _
      simpa only [← hpq] using hp
    have hz : IsZero H.sheaf :=
      ((Scheme.Modules.pullback j.left).mapIso e).isZero_iff.mpr
        (openPullback_pushforward_isZero y.left j.left hd' L.sheaf)
    let : Subsingleton (ChartModule U H) := by
      let S := affineSections (polynomialAlgebra k n)
      let : S.IsRightAdjoint := (tilde.adjunction (R := affineRing (polynomialAlgebra k n))).isRightAdjoint
      apply ModuleCat.subsingleton_of_isZero
      exact (hz.isTerminal.isTerminalObj S H.sheaf).isZero
    apply chartEuler_eq_zero_of_homology U hT H
    intro q
    exact ((KoszulCoefficientComplex (ChartModule U H)).sc q).isZero_homology_of_isZero_X₂
      (ModuleCat.isZero_iff_subsingleton.mpr ((wedgeCoordinates (ChartModule U H) q).injective.subsingleton))

end PointGeometry

section ComposedFibers

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y V : SchemeOver k}
  {a : ModObj T.X Y} {b : ModObj T.X X} {d : ModObj T.X V}

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open private equivariant_actOn pullComp_assoc pullCongr_trans pullComp_congr_left
  transport_congr_point transport_eq_evalPullIso from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

private theorem equivariant_comp {f : X ⟶ Y} {g : V ⟶ X}
    (hf : IsEquivariantMap a b f) (hg : IsEquivariantMap b d g) :
    IsEquivariantMap a d (g ≫ f) := by
  unfold IsEquivariantMap at *
  rw [← Category.assoc d.smul, hg, Category.assoc, hf, ← Category.assoc, tensorHom_comp_tensorHom]
  simp

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pullComp_linearized {f : X ⟶ Y} {g : V ⟶ X}
    (hf : IsEquivariantMap a b f) (hg : IsEquivariantMap b d g) {F : Y.left.Modules}
    (L : Linearization a F) :
    IsLinearizedMap (pullbackLinearization hg (pullbackLinearization hf L))
      (pullbackLinearization (equivariant_comp hf hg) L) (pullComp F g f).hom := by
  apply linearizedMap_of_transport
  intro Z t x
  let x' := actOn d t x
  let y' := actOn b t (x ≫ g)
  let hx : y' = x' ≫ g := equivariant_actOn hg
  let ha (z : Z ⟶ V) := Category.assoc z g f
  let h₁ := equivariant_actOn hf (t := t) (y := x ≫ g)
  let h₂ := equivariant_actOn (equivariant_comp hf hg) (t := t) (y := x)
  let Q := pullComp F g f
  let θ₂ := pullbackLinearizationIso hg (pullbackLinearizationIso hf L.iso)
  let θ₁ := pullbackLinearizationIso (equivariant_comp hf hg) L.iso
  let A := Scheme.Modules.pullback x.left
  let B := Scheme.Modules.pullback x'.left
  change (transport d θ₂ t x).hom ≫ B.map Q.hom =
    A.map Q.hom ≫ (transport d θ₁ t x).hom
  apply (cancel_mono (pullComp F x' (g ≫ f)).hom).mp
  have hL : B.map Q.hom ≫ (pullComp F x' (g ≫ f)).hom =
      (pullComp (Pull f F) x' g).hom ≫ (pullComp F (x' ≫ g) f).hom ≫
        (pullCongr F (ha x')).hom := pullComp_assoc F x' g f
  have hR : A.map Q.hom ≫ (pullComp F x (g ≫ f)).hom =
      (pullComp (Pull f F) x g).hom ≫ (pullComp F (x ≫ g) f).hom ≫
        (pullCongr F (ha x)).hom := pullComp_assoc F x g f
  rw [Category.assoc (transport d θ₂ t x).hom, hL]
  have hh₁ := pullbackLinearization_transport_assoc hg (pullbackLinearizationIso hf L.iso) t x
    ((pullComp F (x' ≫ g) f).hom ≫ (pullCongr F (ha x')).hom)
  change _ = _ at hh₁
  rw [hh₁]
  rw [reassoc_of% (pullComp_congr_left F f hx),
    pullbackLinearization_transport_assoc hf L.iso t (x ≫ g)]
  rw [Category.assoc (A.map Q.hom), pullbackLinearization_transport (equivariant_comp hf hg) L.iso,
    reassoc_of% hR]
  simp only [reassoc_of% (transport_congr_point L.iso t (ha x)), pullCongr_trans]

set_option backward.isDefEq.respectTransparency false in
private theorem linearizedMap_comp {F H K : Y.left.Modules}
    {L : Linearization a F} {M : Linearization a H} {N : Linearization a K}
    {f : F ⟶ H} {g : H ⟶ K}
    (hf : IsLinearizedMap L M f) (hg : IsLinearizedMap M N g) :
    IsLinearizedMap L N (f ≫ g) := by
  unfold IsLinearizedMap at *
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, hf, Category.assoc, hg, Category.assoc]

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem fiberCharacter_unique {x : pointScheme k ⟶ Y}
    (hx : IsEquivariantMap a (pointAction T) x) {F : EquivariantCoherent a}
    {c d : CharacterRing T} (hc : IsFiberCharacter x F c) (hd : IsFiberCharacter x F d) :
    c = d := by
  obtain ⟨H, e, A, he, hA, hc⟩ := hc
  obtain ⟨J, f, B, hf, hB, hd⟩ := hd
  let i := e.symm ≪≫ f
  have hi : IsLinearizedMap H.lin J.lin i.hom :=
    linearizedMap_comp (linearizedIso_inv (pullbackComparison_linearized hx he))
      (pullbackComparison_linearized hx hf)
  let R := CommAlgCat.of k k
  let S := affineSections R
  let j := S.mapIso i
  let g : S.obj H.sheaf →ₗ[k] S.obj J.sheaf :=
    { toFun := j.hom
      map_add' := j.hom.hom.map_add
      map_smul' := fun c s => j.hom.hom.map_smul (algebraMap k R c) s }
  let E := LinearEquiv.ofBijective g j.toLinearEquiv.bijective
  have hw (χ : Character T) (s : S.obj H.sheaf) :
      E s ∈ B.piece χ ↔ s ∈ A.piece χ := by
    rw [hB, hA]
    change HasSectionWeight J.lin (i.hom.app ⊤ s) χ ↔ HasSectionWeight H.lin s χ
    refine ⟨fun hs => ?_, linearizedMap_preserves_sectionWeight hi⟩
    have hv := linearizedMap_preserves_sectionWeight (linearizedIso_inv hi) hs
    have hh : i.inv.app ⊤ (i.hom.app ⊤ s) = s := by
      change (i.hom ≫ i.inv).app ⊤ s = s
      rw [i.hom_inv_id]
      rfl
    change HasSectionWeight H.lin (i.inv.app ⊤ (i.hom.app ⊤ s)) χ at hv
    rwa [hh] at hv
  ext χ
  rw [hc, hd]
  have heq : (A.piece χ).map E.toLinearMap = B.piece χ := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (hw χ s).mpr hs
    · intro hy
      exact ⟨E.symm y, (hw χ _).mp (by simpa only [E.apply_symm_apply] using hy),
        E.apply_symm_apply y⟩
  exact congrArg (fun n : ℕ => (n : ℤ)) (E.ofSubmodules _ _ heq).finrank_eq

set_option backward.isDefEq.respectTransparency false in
private theorem equivariantPullback_of_linearized
    {f : X ⟶ Y} (hf : IsEquivariantMap a b f)
    {F : EquivariantCoherent a} {H : EquivariantCoherent b}
    {e : Pull f F.sheaf ≅ H.sheaf}
    (he : IsLinearizedMap (pullbackLinearization hf F.lin) H.lin e.hom) :
    IsEquivariantPullback f F H e := by
  intro Z t x
  let θ := pullbackLinearizationIso hf F.lin.iso
  have hh := evalPullIso_square (lift t x) (lift_snd t x) rfl θ H.lin.iso e.hom he
  rw [← transport_eq_evalPullIso, ← transport_eq_evalPullIso] at hh
  refine ⟨equivariant_actOn hf, ?_⟩
  rw [← pullbackLinearization_transport_assoc hf F.lin.iso t x, Iso.hom_inv_id_assoc]
  rw [hh, ← Functor.map_comp_assoc, e.inv_hom_id,
    (Scheme.Modules.pullback x.left).map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem equivariantPullback_comp_of_canonical
    {f : X ⟶ Y} {g : V ⟶ X} (hf : IsEquivariantMap a b f)
    (hg : IsEquivariantMap b d g)
    {F : EquivariantCoherent a} (hF : (Pull f F.sheaf).IsFinitePresentation)
    {L : EquivariantCoherent d} {i : Pull g (Pull f F.sheaf) ≅ L.sheaf}
    (hi : IsEquivariantPullback g (canonicalPullback f hf F hF) L i) :
    IsEquivariantPullback (g ≫ f) F L ((pullComp F.sheaf g f).symm ≪≫ i) := by
  apply equivariantPullback_of_linearized (equivariant_comp hf hg)
  have hlin : IsLinearizedMap
      (pullbackLinearization hg (pullbackLinearization hf F.lin)) L.lin i.hom :=
    pullbackComparison_linearized (f := g) hg
      (F := canonicalPullback f hf F hF) (H := L) (e := i) hi
  exact linearizedMap_comp (linearizedIso_inv (pullComp_linearized hf hg F.lin)) hlin

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
private theorem fiberCharacter_of_chart (U : PolynomialChart a n)
    (F : EquivariantCoherent a) (c : CharacterRing T)
    (hc : IsFiberCharacter (origin k n) (restrictToChart U F) c) :
    IsFiberCharacter U.point F c := by
  obtain ⟨L, i, A, hi, hA, hc⟩ := hc
  refine ⟨L, (pullComp F.sheaf (origin k n) U.inclusion).symm ≪≫ i, A, ?_, hA, hc⟩
  exact equivariantPullback_comp_of_canonical U.equivariant U.fixed
    (chartRestriction_finitePresentation U F) hi

end ComposedFibers

section DiagonalFiber

variable {k : Type u} [Field k] {T : GroupScheme k} {Y : SchemeOver k}
  {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n) (hT : IsSplitTorus T)

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open private equivariant_actOn sectionWeight_pullback_of_iso trivialWeight_one from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

set_option backward.isDefEq.respectTransparency false in
private theorem adjointOfEquivariantPushforward {X : SchemeOver k} {b : ModObj T.X X}
    {f : X ⟶ Y} (hf : IsEquivariantMap a b f)
    {L : EquivariantCoherent b} {F : EquivariantCoherent a}
    {i : F.sheaf ≅ (Scheme.Modules.pushforward f.left).obj L.sheaf}
    (hi : IsEquivariantPushforward f L F i) :
    IsLinearizedMap (pullbackLinearization hf F.lin) L.lin
      (((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm i.hom) := by
  apply linearizedMap_of_transport
  intro Z t z
  obtain ⟨h, hh⟩ := hi Z t z
  have he : h = equivariant_actOn hf := Subsingleton.elim _ _
  dsimp only at hh
  rw [he, ← pullbackLinearization_transport_assoc hf F.lin.iso t z, Iso.hom_inv_id_assoc] at hh
  exact hh

set_option maxHeartbeats 550000 in
set_option backward.isDefEq.respectTransparency false in
private theorem composedPushforwardAdjoint {X V : Scheme.{u}} (f : X ⟶ Y.left) (g : V ⟶ X)
    {F : Y.left.Modules} {L : V.Modules} (m : F ⟶ (Scheme.Modules.pushforward (g ≫ f)).obj L) :
    let adjF := Scheme.Modules.pullbackPushforwardAdjunction f
    let adjG := Scheme.Modules.pullbackPushforwardAdjunction g
    let adj := Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)
    (adjG.homEquiv _ _).symm
      ((adjF.homEquiv _ _).symm (m ≫ (Scheme.Modules.pushforwardComp g f).inv.app L)) =
      (Scheme.Modules.pullbackComp g f).hom.app F ≫ (adj.homEquiv _ _).symm m := by
  intro adjF adjG adj
  let P := Scheme.Modules.pullback (g ≫ f)
  let Q := Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g
  let e := Scheme.Modules.pullbackComp g f
  let E := Scheme.Modules.pushforwardComp g f
  let c := m ≫ E.inv.app L
  have hmate := conjugateEquiv_counit (adjF.comp adjG) adj e.inv L
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hmate
  change P.map (E.hom.app L) ≫ adj.counit.app L =
    e.inv.app _ ≫ (adjF.comp adjG).counit.app L at hmate
  have hcomp : (adjG.homEquiv _ _).symm ((adjF.homEquiv _ _).symm c) =
    Q.map c ≫ (adjF.comp adjG).counit.app L := by
    calc
      _ = ((adjF.comp adjG).homEquiv F L).symm c := by
        rw [Adjunction.comp_homEquiv]
        rfl
      _ = _ := (adjF.comp adjG).homEquiv_counit F L c
  change (adjG.homEquiv _ _).symm ((adjF.homEquiv _ _).symm c) =
    e.hom.app F ≫ (adj.homEquiv _ _).symm m
  rw [hcomp, adj.homEquiv_counit]
  calc
    _ = Q.map c ≫ e.hom.app _ ≫ e.inv.app _ ≫ (adjF.comp adjG).counit.app L := by
      rw [show e.hom.app _ ≫ e.inv.app _ ≫ _ = _ from (e.app _).hom_inv_id_assoc _]
    _ = e.hom.app F ≫ P.map c ≫ P.map (E.hom.app L) ≫ adj.counit.app L := by
      have hc := e.hom.naturality c
      change Q.map c ≫ e.hom.app _ = e.hom.app F ≫ P.map c at hc
      rw [← Category.assoc (Q.map c), ← hmate, hc, Category.assoc]
    _ = _ := by
      rw [← P.map_comp_assoc]
      have hc : c ≫ E.hom.app L = m := by
        change (m ≫ E.inv.app L) ≫ E.hom.app L = m
        exact (Category.assoc _ _ _).trans
          ((congrArg (m ≫ ·) (E.app L).inv_hom_id).trans (Category.comp_id _))
      rw [hc]

set_option maxHeartbeats 850000 in
set_option backward.isDefEq.respectTransparency false in
private theorem chartEuler_diagonal (F : EquivariantCoherent a) (hF : IsPointClass U.point F) :
    classMap U hT (classOf F) = cotangentProduct U.weight := by
  obtain ⟨L, i, e, hL, he⟩ := hF
  let H := restrictToChart U F
  let f := U.inclusion
  let g := origin k n
  let : IsOpenImmersion f.left := U.openImmersion
  let P := Scheme.Modules.pullbackPushforwardAdjunction f.left
  let Q := Scheme.Modules.pullbackPushforwardAdjunction g.left
  let E := Scheme.Modules.pushforwardComp g.left f.left
  let w := (P.homEquiv _ _).symm (e.hom ≫ E.inv.app L.sheaf)
  have hw : IsIso w := by
    dsimp only [w]
    rw [P.homEquiv_counit]
    infer_instance
  let c := (Q.homEquiv H.sheaf L.sheaf).symm w
  have hc : IsLinearizedMap (originFiber U H).lin L.lin c := by
    have h := composedPushforwardAdjoint f.left g.left e.hom
    change c = (pullComp F.sheaf g f).hom ≫
      (((Scheme.Modules.pullbackPushforwardAdjunction U.point.left).homEquiv _ _).symm e.hom) at h
    rw [h]
    exact linearizedMap_comp (pullComp_linearized U.equivariant U.fixed F.lin)
      (adjointOfEquivariantPushforward (equivariant_comp U.equivariant U.fixed) he)
  have hsec (s : ChartModule U H) :
      w.app ⊤ s = c.app ⊤ (pullSection g.left H.sheaf s) := by
    have hc' : (Q.homEquiv _ _) c = w := (Q.homEquiv _ _).apply_symm_apply w
    rw [Q.homEquiv_unit] at hc'
    exact (congrArg (fun m : H.sheaf ⟶ (Scheme.Modules.pushforward g.left).obj L.sheaf =>
      m.app ⊤ s) hc').symm
  have hpres (χ : Character T) (s : ChartModule U H) (hs : HasSectionWeight H.lin s χ) :
      HasSectionWeight L.lin (w.app ⊤ s) χ := by
    rw [hsec]
    exact linearizedMap_preserves_sectionWeight hc
      (sectionWeight_pullback_of_iso U.fixed H.lin (originFiber U H).lin rfl hs)
  have hall (s : BaseModule L) : HasSectionWeight L.lin s 1 := by
    have h := trivialWeight_one hT L.sheaf s
    unfold HasSectionWeight at *
    rw [hL]
    exact h
  obtain ⟨GA, E', _, hLweight, _, _, _⟩ := pointCharacterComparison T hT
  let A := (E' L.sheaf L.coherent.exists_quasicoherentData.choose.isQuasicoherent L.lin).toWeightGrading
  have ha : A.piece 1 = ⊤ := eq_top_iff.mpr (fun s _ => (hLweight L 1 s).mpr (hall s))
  obtain ⟨G, _, hG, _, _⟩ := torCharacter_spec U hT H
  have hb {χ : Character T} (hne : χ ≠ 1) : G.piece χ = ⊥ := by
    apply le_antisymm _ bot_le
    intro s hs
    have hmem : (w.app ⊤ s : BaseModule L) ∈ A.piece χ :=
      (hLweight L χ _).mpr (hpres χ s ((hG χ s).mp hs))
    have hdis : Disjoint (A.piece χ) (A.piece 1) :=
      A.internal.submodule_iSupIndep.pairwiseDisjoint hne
    rw [ha, disjoint_top] at hdis
    rw [hdis, Submodule.mem_bot] at hmem
    let m := (affineSections (polynomialAlgebra k n)).map w
    have hh : m s = 0 := hmem
    exact (ConcreteCategory.bijective_of_isIso m).1 (hh.trans m.hom.map_zero.symm)
  have ht : G.piece 1 = ⊤ := by
    rw [← G.internal.submodule_iSup_eq_top]
    apply le_antisymm (le_iSup G.piece 1)
    apply iSup_le
    intro χ
    obtain rfl | hne := eq_or_ne χ 1
    · rfl
    · rw [hb hne]
      exact bot_le
  have htriv (s : ChartModule U H) : HasSectionWeight H.lin s 1 :=
    (hG 1 s).mp (by rw [ht]; exact Submodule.mem_top)
  let φ : affineRing (polynomialAlgebra k n) ⟶ affineRing (CommAlgCat.of k k) :=
    CommRingCat.ofHom (MvPolynomial.aeval (fun _ : Fin n => (0 : k))).toRingHom
  let η := (tilde.toTildeΓNatIso (R := affineRing (CommAlgCat.of k k))).app (ModuleCat.of k k)
  let i' : ChartModule U H ≅ residueModule k n :=
    (affineSections (polynomialAlgebra k n)).mapIso (asIso w) ≪≫
      sectionsOfAffinePushforward φ L.sheaf ≪≫ (ModuleCat.restrictScalars φ.hom).mapIso
        (((affineSections (CommAlgCat.of k k)).mapIso i).symm ≪≫ η.symm)
  rw [classMap_apply U hT F H ⟨Iso.refl _, canonicalPullback_equivariant f U.equivariant F _⟩]
  exact chartEuler_eq_cotangent_of_residue U hT H i' htriv

end DiagonalFiber

section LocallyFreeFiber

open SheafOfModules
open TopologicalSpace
open RingTheory.Sequence

variable {k : Type u} [Field k] {T : GroupScheme k} {Y : SchemeOver k}
  {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n) (hT : IsSplitTorus T)

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackFree_over_local {R : CommRingCat.{u}} [IsLocalRing R]
    (f : Spec R ⟶ Y.left) (F : Y.left.Modules) (hF : F.IsLocallyFree) :
    ∃ (ι : Type u), Nonempty ((Scheme.Modules.pullback f).obj F ≅ free ι) := by
  obtain ⟨D, hD⟩ := hF.exists_isLocallyFreeData
  let p : Spec R := IsLocalRing.closedPoint R
  have hcov : (⨆ i, D.X i) = ⊤ := (Opens.coversTop_iff Y.left D.X).mp D.coversTop
  have hp : f p ∈ ⨆ i, D.X i := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hp
  let W : Y.left.Opens := D.X i
  let j := W.ι
  have htop : f ⁻¹ᵁ W = ⊤ := (IsLocalRing.closedPoint_mem_iff (f ⁻¹ᵁ W)).mp hi
  have hr : Set.range f ⊆ Set.range j := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change x ∈ f ⁻¹ᵁ W
    rw [htop]
    trivial
  let g := IsOpenImmersion.lift j f hr
  have hg : g ≫ j = f := IsOpenImmersion.lift_fac _ _ _
  let F₀ := (Scheme.Modules.overEquiv W).functor
  let I := (D.generators i).I
  let e : (Scheme.Modules.pullback j).obj F ≅ free I :=
    ((Scheme.Modules.restrictFunctorIsoPullback j).app F).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv W).app F).symm ≪≫
      F₀.mapIso (asIso (D.generators i).π).symm ≪≫
      (mapFreeIso F₀ I (W.sheafOfModulesEquivOverUnit Y.left.ringCatSheaf).symm).symm
  refine ⟨I, ⟨((Scheme.Modules.pullbackCongr hg).app F).symm ≪≫
    ((Scheme.Modules.pullbackComp g j).app F).symm ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫ pullbackObjFreeIso g.toRingCatSheafHom I⟩⟩

set_option maxHeartbeats 700000 in
set_option backward.isDefEq.respectTransparency false in
private theorem flat_sections_pullback_of_locallyFree {R : CommRingCat.{u}}
    (f : Spec R ⟶ Y.left) (F : Y.left.Modules) (hF : F.IsLocallyFree)
    (hq : ((Scheme.Modules.pullback f).obj F).IsQuasicoherent) :
    Module.Flat R ((moduleSpecΓFunctor (R := R)).obj ((Scheme.Modules.pullback f).obj F)) := by
  let H := (Scheme.Modules.pullback f).obj F
  let M := (moduleSpecΓFunctor (R := R)).obj H
  apply Module.flat_of_localized_maximal
  intro p hp
  let S := Localization.AtPrime p
  let S₀ := CommRingCat.of S
  let φ : R ⟶ S₀ := CommRingCat.ofHom (algebraMap R S)
  let i := Spec.map φ
  let : H.IsQuasicoherent := hq
  obtain ⟨J, ⟨j⟩⟩ := pullbackFree_over_local (i ≫ f) F hF
  let l := ((Scheme.Modules.pullbackComp i f).app F) ≪≫ j ≪≫ (tildeFinsupp J).symm
  let e := (moduleSpecΓFunctor (R := S₀)).mapIso l ≪≫
    ((tilde.toTildeΓNatIso (R := S₀)).app (ModuleCat.of S (J →₀ S))).symm
  obtain ⟨b, _⟩ := affineSectionBaseChange φ H
  let d := (b.symm ≪≫ e).toLinearEquiv
  let S' := (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)
  let : Module S S' := inferInstanceAs (Module S S)
  let : IsScalarTower R S S' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let e₀ : S ≃ₗ[S] S' := LinearEquiv.refl S S
  let e₁ : (S ⊗[R] M) ≃ₗ[S] ((ModuleCat.extendScalars φ.hom).obj M) :=
    TensorProduct.AlgebraTensorModule.congr e₀ (LinearEquiv.refl R M)
  let d' : (S ⊗[R] M) ≃ₗ[S] (J →₀ S) := e₁.trans d
  have hfree : Module.Free S (S ⊗[R] M) := Module.Free.of_equiv d'.symm
  let g := LocalizedModule.mkLinearMap p.primeCompl M
  let m := (IsLocalizedModule.isBaseChange p.primeCompl S g).equiv
  let : Module.Flat S (J →₀ S) := Module.Flat.finsupp J
  let : Module.Flat S (LocalizedModule p.primeCompl M) := Module.Flat.of_linearEquiv (m.symm.trans d')
  change Module.Flat R (LocalizedModule p.primeCompl M)
  exact Module.Flat.trans R S (LocalizedModule p.primeCompl M)

set_option backward.isDefEq.respectTransparency false in
private theorem higherTor_isZero_of_flat (M : ModuleCat.{u} (polynomialAlgebra k n))
    [Module.Flat (PolynomialRing k n) M] (q : ℕ) (hq : 0 < q) :
    IsZero ((KoszulCoefficientComplex M).homology q) := by
  let R := PolynomialRing k n
  let xs := variableList k n
  have hm : IsWeaklyRegular M xs :=
    (TensorProduct.lid R M).isWeaklyRegular_congr xs |>.mp
      (variableList_weaklyRegular k n).isWeaklyRegular_rTensor
  exact ModuleCat.isZero_iff_subsingleton.mpr (weaklyRegular_acyclic M xs hm q hq)

set_option backward.isDefEq.respectTransparency false in
private theorem chartEuler_isFiberCharacter_of_flat (H : EquivariantCoherent U.action)
    [Module.Flat (PolynomialRing k n) (ChartModule U H)] :
    IsFiberCharacter (origin k n) H (chartEuler U hT H) := by
  let V := originFiber U H
  let : IsScalarTower k (↥(CommAlgCat.of k k)) (BaseModule V) :=
    moduleOverBaseField_tower (CommAlgCat.of k k) (BaseModule V)
  obtain ⟨GA, E, e, hV, he, _, _⟩ := pointCharacterComparison T hT
  let hQ := V.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let A := (E V.sheaf hQ V.lin).toWeightGrading
  obtain ⟨G, h, hG, _, hc⟩ := torCharacter_spec U hT H
  refine ⟨V, Iso.refl _, A, canonicalPullback_equivariant (origin k n) U.fixed H V.coherent,
    hV V, ?_⟩
  intro χ
  have hz (q : ℕ) (hq : 0 < q) : (torCharacter U hT H q).coeff χ = 0 := by
    let M := ChartModule U H
    let C := KoszulCoefficientComplex M
    let F := affineBaseRestriction k n
    let C₀ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C
    let β : F.obj (C.homology q) ≅ C₀.homology q := ((C.sc q).mapHomologyIso F).symm
    let γ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) _ q).mapIso (coordinateComplexIso M)
    let : Subsingleton ((coordinateComplex M).homology q) :=
      ModuleCat.subsingleton_of_isZero ((β ≪≫ γ).isZero_iff.mp
        (F.map_isZero (higherTor_isZero_of_flat M q hq)))
    let : Subsingleton ((weightComplex M U.weight G χ (h χ)).homology q) :=
      (homologyIncl_injective M U.weight G h q χ).subsingleton
    rw [hc, Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  have hχ : (torCharacter U hT H 0).coeff χ = (Module.finrank k (A.piece χ) : ℤ) := by
    obtain ⟨i⟩ := ordinaryFiberHomology U H G hG h A (hV V) χ
    rw [hc, i.toLinearEquiv.finrank_eq]
  let coeff : CharacterRing T →+ ℤ :=
    (Finsupp.applyAddHom χ).comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom
  change coeff (∑ q ∈ Finset.range (n + 1), (-1 : ℤ)^q • torCharacter U hT H q) = _
  rw [map_sum, Finset.sum_eq_single 0]
  · change (-1 : ℤ)^0 • (torCharacter U hT H 0).coeff χ = _
    simpa only [pow_zero, one_zsmul] using hχ
  · intro q _ hq
    rw [map_zsmul]
    change _ • (torCharacter U hT H q).coeff χ = 0
    rw [hz q (Nat.pos_of_ne_zero hq), smul_zero]
  · simp

private theorem chartEuler_isFiberCharacter_of_locallyFree (H : EquivariantCoherent U.action)
    (hH : H.sheaf.IsLocallyFree) :
    IsFiberCharacter (origin k n) H (chartEuler U hT H) := by
  let R := affineRing (polynomialAlgebra k n)
  let i := Scheme.Modules.pullbackId (Spec R)
  let hq : H.sheaf.IsQuasicoherent := H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let hq' := (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso (i.app H.sheaf).symm hq
  let G := (Scheme.Modules.pullback (𝟙 (Spec R))).obj H.sheaf
  let hflat : Module.Flat (PolynomialRing k n) ((affineSections (polynomialAlgebra k n)).obj G) :=
    flat_sections_pullback_of_locallyFree (Y := affineScheme (polynomialAlgebra k n))
      (𝟙 (Spec R)) H.sheaf hH hq' 
  let : Module.Flat (PolynomialRing k n) (ChartModule U H) :=
    Module.Flat.of_linearEquiv ((affineSections (polynomialAlgebra k n)).mapIso (i.app H.sheaf)).toLinearEquiv.symm
  exact chartEuler_isFiberCharacter_of_flat U hT H

private theorem classMap_isFiberCharacter_of_locallyFree (F : EquivariantCoherent a)
    (hF : F.sheaf.IsLocallyFree) :
    IsFiberCharacter U.point F (classMap U hT (classOf F)) := by
  let H := restrictToChart U F
  let : Module.Flat (PolynomialRing k n) (ChartModule U H) :=
    flat_sections_pullback_of_locallyFree U.inclusion.left F.sheaf hF
      H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  rw [classMap_apply U hT F H ⟨Iso.refl _, canonicalPullback_equivariant U.inclusion U.equivariant F _⟩]
  exact fiberCharacter_of_chart U F _ (chartEuler_isFiberCharacter_of_flat U hT H)

end LocallyFreeFiber

section GradedKernels

open private WeightGrading.mapLinearEquiv from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

variable {k : Type u} [Field k] {T : GroupScheme k} {Y : SchemeOver k}
  {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n) (hT : IsSplitTorus T)

set_option backward.isDefEq.respectTransparency false in
private theorem tilde_preserves_monos (R : CommRingCat.{u}) :
    (tilde.functor R).PreservesMonomorphisms := by
  constructor
  intro M N f hf
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro V x y h
  apply Subtype.ext
  funext p
  let S := p.val.asIdeal.primeCompl
  have hinj := LocalizedModule.map_injective S f.hom
    ((ModuleCat.mono_iff_injective f).mp hf)
  apply hinj
  exact congrArg (fun w => w.val p) h

private theorem tilde_additive (R : CommRingCat.{u}) : (tilde.functor R).Additive :=
  ⟨fun {_ _} {f g} => tilde.map_add (f := f) (g := g)⟩

private theorem tilde_preserves_exactness (R : CommRingCat.{u}) :
    (tilde.functor R).PreservesHomology := by
  let D := tilde.functor R
  let : D.IsLeftAdjoint := (tilde.adjunction (R := R)).isLeftAdjoint
  let : D.Additive := tilde_additive R
  let : D.PreservesMonomorphisms := tilde_preserves_monos R
  exact D.preservesHomology_of_preservesMonos_and_cokernels

private def mapModuleGrading (A : RingGrading k (Character T) (polynomialAlgebra k n))
    {M N : ModuleCat.{u} (polynomialAlgebra k n)}
    [IsScalarTower k (↥(polynomialAlgebra k n)) M]
    [IsScalarTower k (↥(polynomialAlgebra k n)) N]
    (G : ModuleGrading A M) (b : M ≅ N) : ModuleGrading A N := by
  let e : M ≃ₗ[k] N := LinearEquiv.ofBijective (overBaseMap b.hom) b.toLinearEquiv.bijective
  refine ⟨WeightGrading.mapLinearEquiv G.toWeightGrading e, ?_⟩
  intro i j r v hr hv
  obtain ⟨w, hw, rfl⟩ := hv
  exact ⟨r • w, G.smul_mem hr hw, b.hom.hom.map_smul _ _⟩

set_option backward.isDefEq.respectTransparency false in
private def kernelWeightGrading
    {M N : ModuleCat.{u} (polynomialAlgebra k n)}
    (G : WeightGrading k (Character T) M) (A : WeightGrading k (Character T) N)
    (f : M ⟶ N) (hf : PreservesWeight G A (overBaseMap f)) :
    let K := ModuleCat.of (↥(polynomialAlgebra k n)) (LinearMap.ker f.hom)
    letI := moduleOverBaseField (polynomialAlgebra k n) K
    WeightGrading k (Character T) K := by
  let K := ModuleCat.of (↥(polynomialAlgebra k n)) (LinearMap.ker f.hom)
  letI : Module k K := moduleOverBaseField (polynomialAlgebra k n) K
  let i : K ⟶ M := ModuleCat.ofHom (LinearMap.ker f.hom).subtype
  let ι := overBaseMap i
  let W (χ : Character T) : Submodule k K := (G.piece χ).comap ι
  refine ⟨W, DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_⟩
  · rw [iSupIndep_def]
    intro χ
    rw [Submodule.disjoint_def]
    intro v hv hw
    apply Subtype.ext
    have hLe (ψ : Character T) : (W ψ).map ι ≤ G.piece ψ :=
      Submodule.map_comap_le ι (G.piece ψ)
    have hle : (⨆ ψ, ⨆ (_ : ψ ≠ χ), W ψ).map ι ≤ ⨆ ψ, ⨆ (_ : ψ ≠ χ), G.piece ψ := by
      simp only [Submodule.map_iSup]
      exact iSup_le fun ψ => iSup_le fun hn => (hLe ψ).trans (le_iSup_of_le ψ (le_iSup (fun _ : ψ ≠ χ => G.piece ψ) hn))
    exact Submodule.disjoint_def.mp (G.internal.submodule_iSupIndep χ) v.val hv
      (hle ⟨v, hw, rfl⟩)
  · apply eq_top_iff.mpr
    intro v _
    obtain ⟨s, hs⟩ := sum_weightProjections G (ι v)
    have hz (χ : Character T) : (weightProject G χ (ι v)).val ∈ LinearMap.ker f.hom := by
      have hn := weightProject_natural G A (overBaseMap f) hf χ (ι v)
      rw [show overBaseMap f (ι v) = 0 from v.property, map_zero] at hn
      exact congrArg Subtype.val hn
    let w (χ : Character T) : K := ⟨(weightProject G χ (ι v)).val, hz χ⟩
    have hm (χ : Character T) : w χ ∈ W χ := (weightProject G χ (ι v)).property
    have he : (∑ χ ∈ s, w χ) = v := by
      apply Subtype.ext
      exact (map_sum ι w s).trans hs
    rw [← he]
    exact Submodule.sum_mem _ (fun χ _ => le_iSup W χ (hm χ))

include hT in
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_equivariant_kernel {F H : EquivariantCoherent U.action}
    (f : F.sheaf ⟶ H.sheaf) (hf : IsLinearizedMap F.lin H.lin f) :
    ∃ (K : EquivariantCoherent U.action) (i : K.sheaf ⟶ F.sheaf)
      (w : i ≫ f = 0), IsLinearizedMap K.lin F.lin i ∧
        Nonempty (IsLimit (KernelFork.ofι i w)) := by
  let R := polynomialAlgebra k n
  let R₀ := affineRing R
  let S := affineSections R
  let D := tilde.functor R₀
  let adj := tilde.adjunction (R := R₀)
  let : D.IsLeftAdjoint := (tilde.adjunction (R := R₀)).isLeftAdjoint
  let : D.Additive := tilde_additive R₀
  let : D.PreservesHomology := tilde_preserves_exactness R₀
  let : PreservesFiniteLimits D := D.preservesFiniteLimits_of_preservesHomology
  let hF := F.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let hH := H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let : F.sheaf.IsQuasicoherent := hF
  let : H.sheaf.IsQuasicoherent := hH
  obtain ⟨GA, E, hE, hmap, _⟩ := equivariantAffineComparison hT R U.action
  let M : ModuleCat.{u} R := S.obj F.sheaf
  let N : ModuleCat.{u} R := S.obj H.sheaf
  let : IsScalarTower k (↥R) M := moduleOverBaseField_tower R M
  let : IsScalarTower k (↥R) N := moduleOverBaseField_tower R N
  let GF := E F.sheaf hF F.lin
  let GH := E H.sheaf hH H.lin
  let f₀ : M ⟶ N := S.map f
  let KK := ModuleCat.kernelCone f₀
  let K : ModuleCat.{u} R := KK.pt
  let : Module k K := moduleOverBaseField R K
  let : IsScalarTower k (↥R) K := moduleOverBaseField_tower R K
  let j : K ⟶ M := KK.ι
  let hfj := (hmap _ _ hF hH F.lin H.lin f).mp hf
  let B := kernelWeightGrading GF.toWeightGrading GH.toWeightGrading f₀ hfj
  let KG : ModuleGrading GA.val K :=
    ⟨B, fun hr hv => GF.smul_mem hr hv⟩
  let : Module.Finite (↥R) (S.obj F.sheaf) := chartModule_finite U F
  let : IsNoetherianRing (↥R) := inferInstanceAs (IsNoetherianRing (PolynomialRing k n))
  let : Module.Finite (↥R) K := inferInstanceAs (Module.Finite (↥R) (LinearMap.ker f₀.hom))
  let L := D.obj K
  let b : S.obj L ≅ K := (((tilde.toTildeΓNatIso (R := R₀)).app K)).symm
  let : Module k (S.obj L) := moduleOverBaseField R (S.obj L)
  let : IsScalarTower k (↥R) (S.obj L) := moduleOverBaseField_tower R (S.obj L)
  let JM := mapModuleGrading GA.val KG b.symm
  let hL : L.IsQuasicoherent := inferInstanceAs (tilde (R := R₀) K).IsQuasicoherent
  let ℓ := (E L hL).symm JM
  let C : EquivariantCoherent U.action :=
    ⟨L, finitePresentation_tilde (R := R₀) K, ℓ⟩
  let ι : C.sheaf ⟶ F.sheaf := D.map j ≫ F.sheaf.fromTildeΓ
  have hnat : F.sheaf.fromTildeΓ ≫ f = D.map f₀ ≫ H.sheaf.fromTildeΓ :=
    ((tilde.adjunction (R := R₀)).counit.naturality f).symm
  have hj : j ≫ f₀ = 0 := KK.condition
  have hn : ι ≫ f = 0 := by
    change (D.map j ≫ F.sheaf.fromTildeΓ) ≫ f = 0
    rw [Category.assoc, hnat, ← D.map_comp_assoc, hj, D.map_zero, zero_comp]
  refine ⟨C, ι, hn, ?_, ?_⟩
  · apply (hmap _ _ hL hF ℓ F.lin ι).mpr
    intro χ s hs
    have hs' : s ∈ JM.piece χ := by simpa only [Equiv.apply_symm_apply, ℓ] using hs
    obtain ⟨w, hw, rfl⟩ := hs'
    have he : S.map ι = b.hom ≫ j := by
      apply (cancel_epi b.inv).mp
      change adj.unit.app K ≫ S.map (D.map j ≫ F.sheaf.fromTildeΓ) = _
      have htri : adj.unit.app M ≫ S.map F.sheaf.fromTildeΓ = 𝟙 M :=
        adj.right_triangle_components F.sheaf
      rw [Functor.map_comp, ← reassoc_of% adj.unit.naturality j, htri, Category.comp_id]
      exact ((b.inv_hom_id_assoc j).symm)
    rw [he]
    change j (b.hom (b.inv w)) ∈ GF.piece χ
    rw [show b.hom (b.inv w) = w from b.toLinearEquiv.apply_symm_apply w]
    exact hw
  · let hK := KernelFork.mapIsLimit KK (ModuleCat.kernelIsLimit f₀) D
    let : IsIso F.sheaf.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ _).mp hF
    let : IsIso H.sheaf.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ _).mp hH
    let cF := asIso F.sheaf.fromTildeΓ
    let cH := asIso H.sheaf.fromTildeΓ
    exact ⟨IsKernel.ofIso (D.map f₀) (s := KK.map D) hK (KernelFork.ofι ι hn) cF cH (Iso.refl _)
      hnat (Category.id_comp _)⟩

end GradedKernels

section ResolutionEuler

variable {k : Type u} [Field k] {T : GroupScheme k} {Y : SchemeOver k}
  {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n) (hT : IsSplitTorus T)

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false in
private theorem linearized_of_comp_mono {X : SchemeOver k} {b : ModObj T.X X}
    {F G H : X.left.Modules} {lF : Linearization b F} {lG : Linearization b G}
    {lH : Linearization b H} {f : F ⟶ G} {i : G ⟶ H} [Mono i]
    (hi : IsLinearizedMap lG lH i) (h : IsLinearizedMap lF lH (f ≫ i)) :
    IsLinearizedMap lF lG f := by
  let P := Scheme.Modules.pullback (snd T.X X).left
  let Q := Scheme.Modules.pullback b.smul.left
  have hPB := Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (fst T.X X) (snd T.X X)) (tensorProductIsBinaryProduct T.X X)
  let : Flat (snd T.X X).left :=
    MorphismProperty.of_isPullback hPB (show Flat T.X.hom from inferInstance)
  let : P.PreservesHomology := LinearAlgebraicGroups.FlatCohomology.flatPullbackExact _
  let : Mono (P.map i) := inferInstance
  change lG.iso.hom ≫ Q.map i = P.map i ≫ lH.iso.hom at hi
  have hmono : Mono (Q.map i) := by
    have hh : Mono (lG.iso.hom ≫ Q.map i) := by rw [hi]; infer_instance
    exact (mono_comp_iff_of_isIso lG.iso.hom (Q.map i)).mp hh
  apply (cancel_mono (Q.map i)).mp
  change (lF.iso.hom ≫ Q.map f) ≫ Q.map i = (P.map f ≫ lG.iso.hom) ≫ Q.map i
  rw [Category.assoc, ← Q.map_comp, Category.assoc, hi, ← P.map_comp_assoc]
  exact h

private structure ResolutionQuotient {F : EquivariantCoherent U.action}
    (C : LocallyFreeResolution F) (q : ℕ) where
  target : EquivariantCoherent U.action
  proj : (C.term q).sheaf ⟶ target.sheaf
  linearized : IsLinearizedMap (C.term q).lin target.lin proj
  epi : Epi proj
  zero : C.complex.d (q + 1) q ≫ proj = 0
  exactness : (ShortComplex.mk (C.complex.d (q + 1) q) proj zero).Exact

include hT in
set_option backward.isDefEq.respectTransparency false in
private theorem ResolutionQuotient.step {F : EquivariantCoherent U.action}
    {C : LocallyFreeResolution F} {q : ℕ} (P : ResolutionQuotient U C q) :
    ∃ Q : ResolutionQuotient U C (q + 1),
      ∃ (i : Q.target.sheaf ⟶ (C.term q).sheaf)
        (w : i ≫ P.proj = 0), IsLinearizedMap Q.target.lin (C.term q).lin i ∧
        (ShortComplex.mk i P.proj w).ShortExact := by
  obtain ⟨K, i, w, hi, ⟨hk⟩⟩ := exists_equivariant_kernel U hT P.proj P.linearized
  let : Mono i := mono_of_isLimit_fork hk
  let : Epi P.proj := P.epi
  let D := C.complex
  let lift := KernelFork.IsLimit.lift' hk (D.d (q+1) q) P.zero
  let f : D.X (q + 1) ⟶ K.sheaf := lift.val
  have hf : f ≫ i = D.d (q+1) q := lift.property
  have hl : IsLinearizedMap (C.term (q + 1)).lin K.lin f := by
    apply linearized_of_comp_mono hi
    rw [hf]
    exact C.equivariantD _ _
  have hEpi : Epi f := by
    let e := hk.conePointUniqueUpToIso (kernelIsKernel P.proj)
    have he : e.hom ≫ kernel.ι P.proj = i :=
      IsLimit.conePointUniqueUpToIso_hom_comp hk (kernelIsKernel P.proj) WalkingParallelPair.zero
    have hf' : f ≫ e.hom = kernel.lift P.proj (D.d (q+1) q) P.zero := by
      apply (cancel_mono (kernel.ι P.proj)).mp
      rw [Category.assoc, he, hf, kernel.lift_ι]
    let : Epi (f ≫ e.hom) := hf'.symm ▸ P.exactness.epi_kernelLift
    exact (epi_comp_iff_of_isIso f e.hom).mp inferInstance
  have w' : D.d (q+2) (q+1) ≫ f = 0 := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hf, D.d_comp_d, zero_comp]
  let S₁ := ShortComplex.mk (D.d (q+2) (q+1)) f w'
  let S₂ := ShortComplex.mk (D.d (q+2) (q+1)) (D.d (q+1) q) (D.d_comp_d ..)
  have hS₂ : S₂.Exact := by
    have hz : D.ExactAt (q + 1) :=
      (D.exactAt_iff_isZero_homology (q + 1)).mpr (C.exact_pos q)
    exact (D.exactAt_iff' (q+2) (q+1) q
      (ComplexShape.prev_eq' (ComplexShape.down ℕ) rfl)
      (ComplexShape.next_eq' (ComplexShape.down ℕ) rfl)).mp hz
  let m : S₁ ⟶ S₂ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := i
      comm₁₂ := by simp [S₁, S₂]
      comm₂₃ := by simpa only [Category.id_comp] using hf.symm }
  have hS₁ : S₁.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono m).mpr hS₂
  exact ⟨⟨K, f, hl, hEpi, w', hS₁⟩, i, w, hi,
    ShortComplex.ShortExact.mk' ((ShortComplex.mk i P.proj w).exact_of_f_is_kernel hk)
      inferInstance (P.epi)⟩

private def resolutionQuotients {F : EquivariantCoherent U.action} (C : LocallyFreeResolution F) :
    ∀ q : ℕ, ResolutionQuotient U C q
  | 0 => ⟨F, C.augmentation, C.equivariantAugmentation, C.epi, C.zero, C.exact_zero⟩
  | q + 1 => ((resolutionQuotients C q).step U hT).choose

private theorem chartEuler_zero_of_isZero (H : EquivariantCoherent U.action)
    (hH : IsZero H.sheaf) : chartEuler U hT H = 0 := by
  let w := hH.eq_of_src (𝟙 H.sheaf ≫ 𝟙 H.sheaf) 0
  let A := ShortComplex.mk (𝟙 H.sheaf) (𝟙 H.sheaf) w
  have hA : A.ShortExact := ShortComplex.ShortExact.mk'
    (A.exact_of_isZero_X₂ hH) (inferInstanceAs (Mono (𝟙 H.sheaf)))
    (inferInstanceAs (Epi (𝟙 H.sheaf)))
  have hi : IsLinearizedMap H.lin H.lin (𝟙 H.sheaf) := by
    unfold IsLinearizedMap
    rw [(Scheme.Modules.pullback U.action.smul.left).map_id,
      (Scheme.Modules.pullback (snd T.X (affineScheme (polynomialAlgebra k n))).left).map_id,
      Category.id_comp, Category.comp_id]
  exact right_eq_add.mp (chartEuler_exact U hT (𝟙 H.sheaf) (𝟙 H.sheaf) w hi hi hA)

private theorem chartEuler_resolution {F : EquivariantCoherent U.action}
    (C : LocallyFreeResolution F) :
    ∃ ch : ℕ → CharacterRing T,
      (∀ q, IsFiberCharacter (origin k n) (C.term q) (ch q)) ∧
      chartEuler U hT F = ∑ q ∈ Finset.range C.length, (-1 : ℤ)^q • ch q := by
  let V := resolutionQuotients U hT C
  let E (q : ℕ) := chartEuler U hT (V q).target
  let ch (q : ℕ) := chartEuler U hT (C.term q)
  have hq (q : ℕ) : ch q = E (q + 1) + E q := by
    obtain ⟨i, w, hi, hex⟩ := ((V q).step U hT).choose_spec
    exact chartEuler_exact U hT i (V q).proj w hi (V q).linearized hex
  have hs (l : ℕ) : (∑ q ∈ Finset.range l, (-1 : ℤ)^q • ch q) = E 0 - (-1 : ℤ)^l • E l := by
    induction l with
    | zero => simp
    | succ l ih =>
      rw [Finset.sum_range_succ, ih, hq, smul_add, pow_succ, mul_neg, mul_one, neg_smul]
      abel
  let : Epi (V C.length).proj := (V C.length).epi
  have hZ : IsZero (V C.length).target.sheaf :=
    (C.bounded C.length le_rfl).of_epi (V C.length).proj
  have hz : E C.length = 0 := chartEuler_zero_of_isZero U hT _ hZ
  have hh := hs C.length
  rw [hz, smul_zero, sub_zero] at hh
  exact ⟨ch, fun q => chartEuler_isFiberCharacter_of_locallyFree U hT (C.term q) (C.locallyFree q),
    hh.symm⟩

end ResolutionEuler

section HomogeneousFreeCover

variable {k : Type u} [Field k] {T : GroupScheme k} {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
private theorem exists_homogeneous_free_surjection
    (A : RingGrading k (Character T) (polynomialAlgebra k n))
    (M : ModuleCat.{u} (polynomialAlgebra k n))
    [IsScalarTower k (↥(polynomialAlgebra k n)) M]
    (G : ModuleGrading A M) [Module.Finite (PolynomialRing k n) M] :
    ∃ (I : Type u) (_ : Finite I),
      let P := ModuleCat.of (↥(polynomialAlgebra k n)) (I →₀ PolynomialRing k n)
      letI := moduleOverBaseField (polynomialAlgebra k n) P
      letI := moduleOverBaseField_tower (polynomialAlgebra k n) P
      ∃ (F : ModuleGrading A P) (p : P ⟶ M),
        Function.Surjective p ∧ PreservesWeight F.toWeightGrading G.toWeightGrading (overBaseMap p) := by
  classical
  let R := polynomialAlgebra k n
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := PolynomialRing k n) (M := M)
  choose t ht using fun y : (s : Set M) => sum_weightProjections G.toWeightGrading y.val
  let I := Σ y : (s : Set M), (t y : Set (Character T))
  let w (i : I) := i.2.val
  let v (i : I) := (weightProject G.toWeightGrading (w i) i.1.val).val
  let P : ModuleCat.{u} R := ModuleCat.of (↥R) (I →₀ PolynomialRing k n)
  let μ := moduleOverBaseField R P
  have hsmul (c : k) (f : I →₀ ↥R) (i : I) : (@SMul.smul k _ μ.toSMul c f) i = c • f i := by
    change ((algebraMap k R c) • f) i = _
    rw [Finsupp.smul_apply, smul_eq_mul, Algebra.smul_def]
  let B (χ : Character T) : @Submodule k P _ _ μ :=
    { carrier := {f | ∀ i, f i ∈ A.piece ((w i)⁻¹ * χ)}
      zero_mem' := fun _ => Submodule.zero_mem _
      add_mem' := fun hf hg i => Submodule.add_mem _ (hf i) (hg i)
      smul_mem' := by
        intro c f hf i
        change (@SMul.smul k _ μ.toSMul c f) i ∈ A.piece ((w i)⁻¹ * χ)
        rw [hsmul]
        exact Submodule.smul_mem _ c (hf i) }
  let J : @WeightGrading k (Character T) P _ _ _ μ :=
    ⟨B, shiftedCoordinates_internal A.toWeightGrading w μ B hsmul (fun _ _ => Iff.rfl)⟩
  let F := @ModuleGrading.mk k (Character T) (↥R) _ _ _ _ A P _ _ μ
    (moduleOverBaseField_tower R P) J (by
    intro χ ψ r f hr hf i
    change r * f i ∈ A.piece ((w i)⁻¹ * (χ * ψ))
    have h := A.mul_mem hr (show f i ∈ A.piece ((w i)⁻¹ * ψ) from hf i)
    simpa only [mul_left_comm χ ((w i)⁻¹) ψ] using h)
  let p : P ⟶ M := ModuleCat.ofHom (Finsupp.linearCombination _ v)
  refine ⟨I, inferInstance, F, p, ?_, ?_⟩
  · apply LinearMap.range_eq_top.mp
    suffices Submodule.span (PolynomialRing k n) (s : Set M) ≤ LinearMap.range p.hom by
      rw [hs] at this
      exact le_antisymm le_top this
    apply Submodule.span_le.mpr
    intro y hy
    let y' : (s : Set M) := ⟨y, hy⟩
    change y'.val ∈ _
    rw [← ht y']
    apply Submodule.sum_mem
    intro χ hχ
    refine ⟨Finsupp.single (⟨y', ⟨χ, hχ⟩⟩ : I) 1, ?_⟩
    exact (Finsupp.linearCombination_single _ _ _).trans (one_smul _ _)
  · intro χ x hx
    have hx' : ∀ i, x i ∈ A.piece ((w i)⁻¹ * χ) := hx
    change (Finsupp.linearCombination (PolynomialRing k n) v) x ∈ G.piece χ
    rw [Finsupp.linearCombination_apply]
    apply Submodule.sum_mem
    intro i hi
    have h := G.smul_mem (hx' i)
      (weightProject G.toWeightGrading (w i) i.1.val).property
    simpa only [inv_mul_cancel_comm] using h

end HomogeneousFreeCover

section FiniteProjectiveSheaves

open SheafOfModules TopologicalSpace
open CategoryTheory.Abelian

set_option maxHeartbeats 700000 in
set_option backward.isDefEq.respectTransparency false in
private theorem isLocallyFree_of_iso {X : Scheme.{u}} {F H : X.Modules}
    (e : F ≅ H) (hF : F.IsLocallyFree) : H.IsLocallyFree := by
  obtain ⟨D, hD⟩ := hF.exists_isLocallyFreeData
  let W : LocalGeneratorsData.{u} H :=
    { I := D.I
      X := D.X
      coversTop := D.coversTop
      generators := fun i => (D.generators i).ofEpi
        (((SheafOfModules.overFunctor X.ringCatSheaf (D.X i)).mapIso e).hom) }
  have hW (i : W.I) : IsIso (W.generators i).π := by
    let p := ((SheafOfModules.overFunctor X.ringCatSheaf (D.X i)).mapIso e).hom
    have he : (W.generators i).π = (D.generators i).π ≫ p :=
      GeneratingSections.ofEpi_π (D.generators i) p
    let : IsIso (D.generators i).π := hD.isIso i
    exact he.symm ▸ (inferInstanceAs (IsIso ((D.generators i).π ≫ p)))
  exact SheafOfModules.IsLocallyFree.mk (M := H)
    ⟨W, LocalGeneratorsData.IsLocallyFreeData.mk (q := W) hW⟩

private def extendScalarsTensorIso {R : CommRingCat.{u}} (S : Type u) [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) :
    (S ⊗[R] M) ≃ₗ[S] ((ModuleCat.extendScalars (algebraMap R S)).obj M) := by
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let : Module S S' := inferInstanceAs (Module S S)
  let : IsScalarTower R S S' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let e₀ : S ≃ₗ[S] S' := LinearEquiv.refl S S
  exact TensorProduct.AlgebraTensorModule.congr e₀ (LinearEquiv.refl R M)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem tilde_locallyFree_of_projective {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Projective M] :
    (tilde M).IsLocallyFree := by
  let X := Spec R
  have hR : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  let : Module.Projective R M := ModuleCat.projective_of_module_projective M
  have hc (p : PrimeSpectrum R) : ∃ r : R, r ∉ p.asIdeal ∧
      Module.Free (Localization.Away r) (LocalizedModule.Away r M) := by
    let S := Localization.AtPrime p.asIdeal
    let g := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M
    let : Module.Projective S (LocalizedModule p.asIdeal.primeCompl M) :=
      Module.projective_of_isLocalizedModule p.asIdeal.primeCompl g
    let : Module.Finite S (LocalizedModule p.asIdeal.primeCompl M) :=
      Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl (Rₚ := S) g
    let : Module.Free S (LocalizedModule p.asIdeal.primeCompl M) :=
      Module.free_of_flat_of_isLocalRing
    obtain ⟨r, hr, hf, _⟩ :=
      Module.FinitePresentation.exists_free_localizedModule_powers p.asIdeal.primeCompl g S
    exact ⟨r, hr, hf⟩
  choose x hx hfree using hc
  let W (p : PrimeSpectrum R) : X.Opens := PrimeSpectrum.basicOpen (x p)
  have he (p : PrimeSpectrum R) :
      ∃ (J : Type u), Nonempty (free J ≅ (tilde M).over (W p)) := by
    let r := x p
    let S := Localization.Away r
    let S₀ := CommRingCat.of S
    let φ : R ⟶ S₀ := CommRingCat.ofHom (algebraMap R S)
    let V := W p
    let j := V.ι
    let i := (basicOpenIsoSpecAway r).hom
    have hi : i ≫ Spec.map φ = j := basicOpenIsoSpecAway_hom_SpecMap r
    let N := LocalizedModule.Away r M
    let : Module.Free S N := hfree p
    let J := Module.Free.ChooseBasisIndex S N
    let b := Module.Free.chooseBasis S N
    let g := LocalizedModule.mkLinearMap (Submonoid.powers r) M
    let e : ((ModuleCat.extendScalars φ.hom).obj M) ≃ₗ[S] (J →₀ S) :=
      (extendScalarsTensorIso S M).symm.trans
        (((IsLocalizedModule.isBaseChange (Submonoid.powers r) S g).equiv).trans b.repr)
    obtain ⟨E, _⟩ := LinearAlgebraicGroups.FlatCohomology.affinePullback φ
    let iso : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅ free J :=
      E.app M ≪≫ (tilde.functor S₀).mapIso e.toModuleIso ≪≫ tildeFinsupp J
    let eV : (Scheme.Modules.pullback j).obj (tilde M) ≅ free J :=
      ((Scheme.Modules.pullbackCongr hi).app (tilde M)).symm ≪≫
        ((Scheme.Modules.pullbackComp i (Spec.map φ)).app (tilde M)).symm ≪≫
        (Scheme.Modules.pullback i).mapIso iso ≪≫ pullbackObjFreeIso i.toRingCatSheafHom J
    let D := Scheme.Modules.overEquiv V
    let eq₁ : D.functor.obj ((tilde M).over V) ≅ free J :=
      (Scheme.Modules.overFunctorEquiv V).app (tilde M) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback j).app (tilde M) ≪≫ eV
    exact ⟨J, ⟨mapFreeIso D.inverse J (V.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm ≪≫
      D.inverse.mapIso eq₁.symm ≪≫ (D.unitIso.app _).symm⟩⟩
  choose J iso using he
  let D : LocalGeneratorsData.{u} (tilde M) :=
    { I := PrimeSpectrum R
      X := W
      coversTop := (Opens.coversTop_iff X W).mpr (by
        apply eq_top_iff.mpr
        intro p _
        exact Opens.mem_iSup.mpr ⟨p, hx p⟩)
      generators p := (free.generatingSections (J p)).ofEpi (iso p).some.hom }
  have hD (p : D.I) : IsIso (D.generators p).π := by
    change IsIso ((free.generatingSections (J p)).ofEpi (iso p).some.hom).π
    rw [GeneratingSections.ofEpi_π]
    infer_instance
  exact SheafOfModules.IsLocallyFree.mk (M := tilde M)
    ⟨D, LocalGeneratorsData.IsLocallyFreeData.mk (q := D) hD⟩

end FiniteProjectiveSheaves

section ExistenceOfResolutions

open scoped CategoryTheory.MonObj

open CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

variable {k : Type u} [Field k] {T : GroupScheme k} {Y : SchemeOver k}
  {a : ModObj T.X Y} {n : ℕ} (U : PolynomialChart a n) (hT : IsSplitTorus T)

private theorem polynomial_projectiveDimension (M : ModuleCat.{u} (PolynomialRing k n))
    [Module.Finite (PolynomialRing k n) M] : HasProjectiveDimensionLE M n := by
  let A := PolynomialRing k n
  apply (ModuleCat.hasProjectiveDimensionLE_iff_forall_maximalSpectrum n M).mpr
  intro p
  let R := Localization.AtPrime p.asIdeal
  let N : ModuleCat.{u} R := M.localizedModule p.asIdeal.primeCompl
  change HasProjectiveDimensionLE N n
  have hA : ringKrullDim A = n := by
    change ringKrullDim (MvPolynomial (Fin n) k) = _
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  have hR : ringKrullDim R ≤ n := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal R, ← hA]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  obtain ⟨d, hd, hdn⟩ : ∃ d : ℕ, ringKrullDim R = d ∧ d ≤ n := by
    obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp
      (ne_of_gt (show ⊥ < ringKrullDim R from Order.bot_lt_krullDim))
    rw [← he] at hR
    obtain ⟨d, rfl, hdn⟩ := ENat.le_natCast_iff.mp (WithBot.coe_le_coe.mp hR)
    exact ⟨d, he.symm, hdn⟩
  apply (projectiveDimension_le_iff N n).mp
  let : Module.Finite R N := Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
    (M.localizedModuleMkLinearMap p.asIdeal.primeCompl)
  exact (AdvCommAlg.CohenMacaulay.regularLocal_projectiveDimension_le R N d hd).trans
    (by exact_mod_cast hdn)

include hT in
set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_equivariant_free_cover (F : EquivariantCoherent U.action) :
    ∃ (P : EquivariantCoherent U.action) (p : P.sheaf ⟶ F.sheaf),
      P.sheaf.IsLocallyFree ∧ Projective (ChartModule U P) ∧
      Epi p ∧ IsLinearizedMap P.lin F.lin p := by
  let R := polynomialAlgebra k n
  let R₀ := affineRing R
  let S := affineSections R
  let D := tilde.functor R₀
  let adj := tilde.adjunction (R := R₀)
  let : D.IsLeftAdjoint := adj.isLeftAdjoint
  let hF := F.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let : F.sheaf.IsQuasicoherent := hF
  let : IsNoetherianRing (↥R) := inferInstanceAs (IsNoetherianRing (PolynomialRing k n))
  let M : ModuleCat.{u} R := ChartModule U F
  let : Module.Finite (PolynomialRing k n) M := chartModule_finite U F
  let : IsScalarTower k (↥R) M := moduleOverBaseField_tower R M
  obtain ⟨GA, E, hE, hmap, _⟩ := equivariantAffineComparison hT R U.action
  let GF := E F.sheaf hF F.lin
  obtain ⟨I, hI, G, p, hp, hpg⟩ := exists_homogeneous_free_surjection GA.val M GF
  let : Finite I := hI
  let N : ModuleCat.{u} R := ModuleCat.of (↥R) (I →₀ PolynomialRing k n)
  let : Epi p := (ModuleCat.epi_iff_surjective _).mpr hp
  let basis : Module.Basis I (PolynomialRing k n) (I →₀ PolynomialRing k n) :=
    Finsupp.basisSingleOne
  let : Module.Finite (↥R) N := Module.Finite.of_basis basis
  let : Projective N := ModuleCat.projective_of_free basis
  let L := D.obj N
  let b : N ≅ S.obj L := (tilde.toTildeΓNatIso (R := R₀)).app N
  let JM := @mapModuleGrading k _ T n GA.val N (S.obj L)
    (moduleOverBaseField_tower R N) (moduleOverBaseField_tower R (S.obj L)) G b
  let hL : L.IsQuasicoherent := inferInstanceAs (tilde (R := R₀) N).IsQuasicoherent
  let ell := (E L hL).symm JM
  let C : EquivariantCoherent U.action := ⟨L, finitePresentation_tilde (R := R₀) N, ell⟩
  let i : C.sheaf ⟶ F.sheaf := D.map p ≫ F.sheaf.fromTildeΓ
  have hfree : L.IsLocallyFree := tilde_locallyFree_of_projective (R := R₀) N
  let : IsIso F.sheaf.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ _).mp hF
  have hi : Epi i := inferInstanceAs (Epi (D.map p ≫ F.sheaf.fromTildeΓ))
  refine ⟨C, i, hfree, Projective.of_iso b inferInstance, hi, ?_⟩
  apply (hmap _ _ hL hF ell F.lin i).mpr
  intro χ s hs
  have hs' : s ∈ JM.piece χ := by simpa only [ell, Equiv.apply_symm_apply] using hs
  obtain ⟨v, hv, rfl⟩ := hs'
  have hc : b.hom ≫ S.map i = p := by
    change adj.unit.app N ≫ S.map (D.map p ≫ F.sheaf.fromTildeΓ) = p
    have ht : adj.unit.app M ≫ S.map F.sheaf.fromTildeΓ = 𝟙 M := adj.right_triangle_components F.sheaf
    rw [Functor.map_comp, ← reassoc_of% adj.unit.naturality p, ht, Category.comp_id]
  change (b.hom ≫ S.map i) v ∈ GF.piece χ
  rw [hc]
  exact hpg χ hv

private theorem linearized_id {F : EquivariantCoherent U.action} :
    IsLinearizedMap F.lin F.lin (𝟙 F.sheaf) := by
  unfold IsLinearizedMap
  rw [(Scheme.Modules.pullback U.action.smul.left).map_id,
    (Scheme.Modules.pullback (snd T.X (affineScheme (polynomialAlgebra k n))).left).map_id,
    Category.id_comp, Category.comp_id]

private theorem linearized_zero {F G : EquivariantCoherent U.action} :
    IsLinearizedMap F.lin G.lin (0 : F.sheaf ⟶ G.sheaf) := by
  unfold IsLinearizedMap
  rw [(Scheme.Modules.pullback U.action.smul.left).map_zero,
    (Scheme.Modules.pullback (snd T.X (affineScheme (polynomialAlgebra k n))).left).map_zero,
    zero_comp, comp_zero]

private def zeroLinearization {X : SchemeOver k} (b : ModObj T.X X)
    {F : X.left.Modules} (hF : IsZero F) : Linearization b F where
  iso := ((Scheme.Modules.pullback (snd T.X X).left).map_isZero hF).iso
    ((Scheme.Modules.pullback b.smul.left).map_isZero hF)
  unit Z x := ⟨by
    let : ModObj T.X X := b
    change (1 : Z ⟶ T.X) • x = x
    exact one_smul (Z ⟶ T.X) x, ((Scheme.Modules.pullback x.left).map_isZero hF).eq_of_src _ _⟩
  mul _ s t x := ⟨by
    let : ModObj T.X X := b
    change s • (t • x) = (s * t) • x
    exact (mul_smul s t x).symm, ((Scheme.Modules.pullback x.left).map_isZero hF).eq_of_src _ _⟩

set_option maxHeartbeats 750000 in
set_option backward.isDefEq.respectTransparency false in
private theorem oneTermResolution (F : EquivariantCoherent U.action) (hF : F.sheaf.IsLocallyFree) :
    Nonempty (LocallyFreeResolution F) := by
  let R := affineRing (polynomialAlgebra k n)
  let A := PolynomialRing k n
  let N : ModuleCat.{u} R := ModuleCat.of A (ULift.{u} Empty →₀ A)
  let Z := tilde (R := R) N
  let D := tilde.functor R
  let : IsNoetherianRing R := inferInstanceAs (IsNoetherianRing (PolynomialRing k n))
  let : D.Additive := tilde_additive R
  let b : Module.Basis (ULift.{u} Empty) A (ULift.{u} Empty →₀ A) := Finsupp.basisSingleOne
  let : Module.Finite R N := Module.Finite.of_basis b
  have hZ : IsZero Z := D.map_isZero (ModuleCat.isZero_iff_subsingleton.mpr
    (inferInstanceAs (Subsingleton (ULift.{u} Empty →₀ A))))
  let P : ℕ → EquivariantCoherent U.action
    | 0 => F
    | _ + 1 => ⟨Z, finitePresentation_tilde (R := R) N, zeroLinearization U.action hZ⟩
  let C : ChainComplex (affineScheme (polynomialAlgebra k n)).left.Modules ℕ :=
    ChainComplex.of (fun q => (P q).sheaf) (fun _ => 0) (fun _ => zero_comp)
  have hd (i j : ℕ) : C.d i j = 0 := by simp [C, ChainComplex.of.d]
  refine ⟨
    { complex := C
      length := 1
      coherent q := (P q).coherent
      linearization q := (P q).lin
      locallyFree := ?_
      equivariantD := ?_
      bounded := ?_
      augmentation := 𝟙 _
      equivariantAugmentation := linearized_id U
      epi := inferInstance
      zero := by rw [hd, zero_comp]
      exact_zero := ?_
      exact_pos := fun q => (C.sc (q + 1)).isZero_homology_of_isZero_X₂ hZ }⟩
  · rintro (_ | q)
    · exact hF
    · exact isLocallyFree_of_iso (tildeFinsupp (R := R) (ULift.{u} Empty)).symm inferInstance
  · intro i j
    rw [hd]
    exact linearized_zero U (F := P i) (G := P j)
  · intro q hq
    cases q with
    | zero => omega
    | succ q => exact hZ
  · apply (ShortComplex.exact_iff_mono _ _).mpr
    · infer_instance
    · exact hd 1 0

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
private theorem prependResolution {K P F : EquivariantCoherent U.action}
    (i : K.sheaf ⟶ P.sheaf) (p : P.sheaf ⟶ F.sheaf) (w : i ≫ p = 0)
    (hi : IsLinearizedMap K.lin P.lin i) (hp : IsLinearizedMap P.lin F.lin p)
    (he : (ShortComplex.mk i p w).ShortExact) (hP : P.sheaf.IsLocallyFree)
    (C : LocallyFreeResolution K) : Nonempty (LocallyFreeResolution F) := by
  let D : ℕ → EquivariantCoherent U.action
    | 0 => P
    | q + 1 => C.term q
  let X : ℕ → (affineScheme (polynomialAlgebra k n)).left.Modules := fun q => (D q).sheaf
  let d : ∀ q : ℕ, X (q + 1) ⟶ X q
    | 0 => C.augmentation ≫ i
    | q + 1 => C.complex.d (q + 1) q
  have hd (q : ℕ) : d (q + 1) ≫ d q = 0 := by
    cases q with
    | zero =>
      change C.complex.d 1 0 ≫ C.augmentation ≫ i = 0
      rw [← Category.assoc, C.zero, zero_comp]
    | succ q => exact C.complex.d_comp_d _ _ _
  let E : ChainComplex (affineScheme (polynomialAlgebra k n)).left.Modules ℕ :=
    ChainComplex.of X d hd
  have hd' (q : ℕ) : E.d (q + 1) q = d q := by
    apply ChainComplex.of_d
  have h0 : E.d 1 0 ≫ p = 0 := by rw [hd' 0]; exact (Category.assoc ..).trans (by rw [w, comp_zero])
  let : Epi p := he.epi_g
  let : Mono i := he.mono_f
  let : Epi C.augmentation := C.epi
  refine ⟨
    { complex := E
      length := C.length + 1
      coherent q := (D q).coherent
      linearization q := (D q).lin
      locallyFree := by rintro (_ | q); exacts [hP, C.locallyFree q]
      equivariantD := ?_
      bounded := ?_
      augmentation := p
      equivariantAugmentation := hp
      epi := inferInstance
      zero := h0
      exact_zero := ?_
      exact_pos := ?_ }⟩
  · intro r q
    by_cases hr : r = q + 1
    · subst r
      rw [hd']
      cases q with
      | zero => exact linearizedMap_comp C.equivariantAugmentation hi
      | succ q => exact C.equivariantD _ _
    · rw [E.shape _ _ (fun h => hr h.symm)]
      exact linearized_zero U (F := D r) (G := D q)
  · intro q hq
    cases q with
    | zero => omega
    | succ q => exact C.bounded q (by omega)
  · let A := ShortComplex.mk (E.d 1 0) p h0
    let B := ShortComplex.mk i p w
    let f : A ⟶ B :=
      { τ₁ := C.augmentation
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          change C.augmentation ≫ i = E.d 1 0 ≫ 𝟙 P.sheaf
          rw [hd' 0, Category.comp_id]
        comm₂₃ := by simp [A, B] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mpr he.exact
  · intro q
    apply (E.exactAt_iff_isZero_homology (q + 1)).mp
    apply (E.exactAt_iff' (q + 2) (q + 1) q
      (ComplexShape.prev_eq' (ComplexShape.down ℕ) rfl)
      (ComplexShape.next_eq' (ComplexShape.down ℕ) rfl)).mpr
    -- Compare the explicit adjacent differential pair after shifting the complex.
    cases q with
    | zero =>
      let A := ShortComplex.mk (C.complex.d 1 0) C.augmentation C.zero
      let B := E.sc' 2 1 0
      let f : A ⟶ B :=
        { τ₁ := 𝟙 _
          τ₂ := 𝟙 _
          τ₃ := i
          comm₁₂ := by simp [A, B, hd' 1, d]
          comm₂₃ := by simp [A, B, hd' 0, d] }
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mp C.exact_zero
    | succ q =>
      have h := (C.complex.exactAt_iff_isZero_homology (q + 1)).mpr (C.exact_pos q)
      have h' := (C.complex.exactAt_iff' (q + 2) (q + 1) q
        (ComplexShape.prev_eq' (ComplexShape.down ℕ) rfl)
        (ComplexShape.next_eq' (ComplexShape.down ℕ) rfl)).mp h
      let A := C.complex.sc' (q + 2) (q + 1) q
      let B := E.sc' (q + 3) (q + 2) (q + 1)
      let e : A ≅ B := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [A, B, hd' (q + 2), d]) (by simp [A, B, hd' (q + 1), d])
      exact (ShortComplex.exact_iff_of_iso e).mp h'

include hT in
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_locallyFreeResolution (F : EquivariantCoherent U.action) :
    Nonempty (LocallyFreeResolution F) := by
  let R := polynomialAlgebra k n
  let R₀ := affineRing R
  let S := affineSections R
  let : IsNoetherianRing R₀ := inferInstanceAs (IsNoetherianRing (PolynomialRing k n))
  let : S.IsRightAdjoint := (tilde.adjunction (R := R₀)).isRightAdjoint
  let : S.PreservesZeroMorphisms := inferInstance
  have go (d : ℕ) (F : EquivariantCoherent U.action)
      (h : HasProjectiveDimensionLE (ChartModule U F) d) :
      Nonempty (LocallyFreeResolution F) := by
    induction d generalizing F with
    | zero =>
      let : Projective (ChartModule U F) :=
        projective_iff_hasProjectiveDimensionLT_one.mpr h
      let : Module.Finite R₀ (ChartModule U F) := chartModule_finite U F
      have hq : F.sheaf.IsQuasicoherent := F.coherent.exists_quasicoherentData.choose.isQuasicoherent
      let : IsIso F.sheaf.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ _).mp hq
      exact oneTermResolution U F (isLocallyFree_of_iso (asIso F.sheaf.fromTildeΓ)
        (tilde_locallyFree_of_projective (R := R₀) (ChartModule U F)))
    | succ d ih =>
      obtain ⟨P, p, hP, hproj, he, hp⟩ := exists_equivariant_free_cover U hT F
      obtain ⟨K, i, w, hi, ⟨hk⟩⟩ := exists_equivariant_kernel U hT p hp
      let : Epi p := he
      let : Mono i := mono_of_isLimit_fork hk
      let C := ShortComplex.mk i p w
      have hC : C.ShortExact := ShortComplex.ShortExact.mk' (C.exact_of_f_is_kernel hk)
        inferInstance inferInstance
      let : K.sheaf.IsQuasicoherent := K.coherent.exists_quasicoherentData.choose.isQuasicoherent
      let : P.sheaf.IsQuasicoherent := P.coherent.exists_quasicoherentData.choose.isQuasicoherent
      let : F.sheaf.IsQuasicoherent := F.coherent.exists_quasicoherentData.choose.isQuasicoherent
      obtain ⟨h₁, h₂, h₃⟩ := affineSectionsExact C hC
      let C₀ := C.map S
      have ex : Function.Exact C₀.f C₀.g := h₂
      have hinj : Function.Injective C₀.f := h₁
      have hsurj : Function.Surjective C₀.g := h₃
      have hC₀ : C₀.ShortExact := ModuleCat.shortComplex_shortExact C₀ ex hinj hsurj
      have hp₀ : Projective C₀.X₂ := hproj
      have hf₀ : HasProjectiveDimensionLT C₀.X₃ (d + 2) := h
      have hK : HasProjectiveDimensionLE (ChartModule U K) d :=
        (hC₀.hasProjectiveDimensionLT_X₃_iff d hp₀).mp hf₀
      obtain ⟨D⟩ := ih K hK
      exact prependResolution U i p w hi hp hC hP D
  let : Module.Finite (PolynomialRing k n) (ChartModule U F) := chartModule_finite U F
  exact go n F (polynomial_projectiveDimension (ChartModule U F))

end ExistenceOfResolutions

set_option backward.isDefEq.respectTransparency false in
theorem derivedRestriction : DerivedRestriction.{u} := by
  intro k _ T hT Y a n U
  refine ⟨classMap U hT, ?_, classMap_isFiberCharacter_of_locallyFree U hT,
    chartEuler_diagonal U hT, chartEuler_disjoint U hT⟩
  intro F
  refine ⟨chartPullback U F, fun H h => ?_⟩
  rw [classMap_apply U hT F H h]
  refine ⟨⟨torCharacter U hT H, torCharacter_spec U hT H, rfl⟩,
    exists_locallyFreeResolution U hT H, fun C => ?_⟩
  obtain ⟨ch, hch, hsum⟩ := chartEuler_resolution U hT C
  refine ⟨ch, ⟨hch, hsum⟩, ?_⟩
  intro ch' hc'
  funext q
  exact fiberCharacter_unique U.fixed (hc'.1 q) (hch q)

end

end LinearAlgebraicGroups.Representation.FlagDerivedRestriction
