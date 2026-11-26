import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.StaggeredKoszulFiltration
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.NullHomotopy
import MathGenome.Internal.AlgebraCore.P103.Ch07.ArtinRees
import MathGenome.Internal.AlgebraCore.P103.Ch07.HilbertSamuelPolynomial
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.TensorProduct.Basis

open CategoryTheory CategoryTheory.Limits AdvCommAlg.Koszul
open scoped TensorProduct
open Specs.CommutativeAlgebraNotes.Intersection.StaggeredKoszul

namespace CommutativeAlgebraNotes.Intersection.StaggeredKoszul

noncomputable section

universe u v

variable {A : Type u} [CommRing A] (E : Type v) [AddCommGroup E] [Module A E]
  (z : List A)

private abbrev K := coefficientComplex E z

private theorem differential_apply (i : ℕ) (x : (K E z).X (i + 1)) :
    (K E z).d (i + 1) i x = coefficientDifferential E z i x := by
  simp only [K, coefficientComplex, ChainComplex.of_d]
  rfl

private theorem differential_range_le (i : ℕ) :
    LinearMap.range ((K E z).d (i + 1) i).hom ≤ listIdeal z • ⊤ := by
  rintro _ ⟨x, rfl⟩
  change (K E z).d (i + 1) i x ∈ _
  rw [differential_apply]
  change coefficientDifferential E z i x ∈
    listIdeal z • (⊤ : Submodule A ((⋀[A]^i (Fin z.length → A)) ⊗[A] E))
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact map_add (coefficientDifferential E z i) x y ▸ Submodule.add_mem _ hx hy
  | tmul a e =>
    rw [coefficientDifferential, TensorProduct.map_tmul, LinearMap.id_apply]
    let f := (TensorProduct.mk A (⋀[A]^i (Fin z.length → A)) E).flip e
    change f (differential (listForm z) i a) ∈ _
    have hspan :
        (⊤ : Submodule A (⋀[A]^(i + 1) (Fin z.length → A))) ≤
          (listIdeal z • ⊤ : Submodule A ((⋀[A]^i (Fin z.length → A)) ⊗[A] E)).comap
            (f.comp (differential (listForm z) i)) := by
      rw [← exteriorPower.ιMulti_span A (i + 1) (Fin z.length → A), Submodule.span_le]
      rintro _ ⟨w, rfl⟩
      change f (differential (listForm z) i (exteriorPower.ιMulti A (i + 1) w)) ∈
        listIdeal z • (⊤ : Submodule A ((⋀[A]^i (Fin z.length → A)) ⊗[A] E))
      have hd : differential (listForm z) i (exteriorPower.ιMulti A (i + 1) w) =
          ∑ j : Fin (i + 1), (-1 : A) ^ j.val •
            (listForm z (w j) • exteriorPower.ιMulti A i (w ∘ j.succAbove)) := by
        apply Subtype.ext
        simpa only [differential_coe, exteriorPower.ιMulti_apply_coe, Submodule.coe_sum,
          SetLike.val_smul] using contraction_formula (listForm z) i w
      rw [hd, map_sum]
      apply Submodule.sum_mem
      intro j _
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem_smul (listForm_mem z _) Submodule.mem_top)
    exact hspan Submodule.mem_top

theorem differential_stable : differentialStableType.{u,v} := by
  intro A _ E _ _ z n i
  unfold layer
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_top]
  refine (smul_mono_right _ (differential_range_le E z i)).trans ?_
  rw [← Submodule.mul_smul, ← pow_succ]
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))

private def termEquiv (i : ℕ) :
    (K E z).X i ≃ₗ[A] (Fin (z.length.choose i) → E) := by
  classical
  let e : Set.powersetCard (Fin z.length) i ≃ Fin (z.length.choose i) :=
    Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using listBasis_card z i)
  exact (TensorProduct.equivFinsuppOfBasisLeft (listBasis z i)).trans
    ((Finsupp.linearEquivFunOnFinite A E _).trans
      (LinearEquiv.piCongrLeft A (fun _ : Fin (z.length.choose i) => E) e))

private theorem ideal_smul_pi_top {ι : Type*} [Fintype ι] (J : Ideal A) :
    J • (⊤ : Submodule A (ι → E)) =
      Submodule.pi Set.univ (fun _ : ι => J • (⊤ : Submodule A E)) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_pi]
    intro i _
    exact (Submodule.smul_top_le_comap_smul_top J (LinearMap.proj i)) hx
  · intro x hx
    rw [Submodule.mem_pi] at hx
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro i _
    exact (Submodule.smul_top_le_comap_smul_top J
      (LinearMap.single A (fun _ : ι => E) i)) (hx i (Set.mem_univ i))

theorem quotient_term : quotientTermType.{u,v} := by
  intro A _ E _ _ z n h i
  classical
  let e := termEquiv E z i
  let J := listIdeal z ^ (n - i)
  change Nonempty (((K E z).X i ⧸ layer E z n i) ≃ₗ[A] (Fin (z.length.choose i) →
    E ⧸ (J • (⊤ : Submodule A E))))
  refine ⟨(Submodule.Quotient.equiv _ _ e ?_).trans
    (Submodule.quotientPi (fun _ : Fin (z.length.choose i) => J • (⊤ : Submodule A E)))⟩
  change (J • (⊤ : Submodule A ((K E z).X i))).map e.toLinearMap = _
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective,
    ideal_smul_pi_top]

theorem quotient_finite_length : quotientFiniteLengthType.{u,v} := by
  intro A _ _ _ E _ _ _ z hJ hE n _ h i
  obtain ⟨e⟩ := quotient_term E z n h i
  apply IsFiniteLength.of_injective (f := e.toLinearMap) ?_ e.injective
  have hpower : IsFiniteLength A (E ⧸ (listIdeal z ^ (n - i) • (⊤ : Submodule A E))) := by
    rcases le_or_gt n i with hi | hi
    · rw [Nat.sub_eq_zero_of_le hi, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact IsFiniteLength.of_subsingleton
    · rcases subsingleton_or_nontrivial E with hE₀ | hE₀
      · exact IsFiniteLength.of_subsingleton
      have hk : n - i = (n - i - 1) + 1 := by omega
      rw [hk]
      exact P103.HilbertSamuelPolynomial.quotient_finite_length (listIdeal z) hJ hE _
  obtain ⟨hnoeth, hartin⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hpower
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

private def cycles (i : ℕ) : Submodule A ((K E z).X i) :=
  LinearMap.ker ((K E z).d i (i - 1)).hom

private theorem wedge_boundary (i : ℕ) (e : Fin z.length → A)
    (w : (K E z).X i) (hw : w ∈ cycles E z i) :
    (K E z).d (i + 1) i (coefficientWedge E z e i w) = listForm z e • w := by
  refine (differential_apply E z i (coefficientWedge E z e i w)).trans ?_
  cases i with
  | zero =>
    exact DFunLike.congr_fun (coefficient_wedge_zero E z e) w
  | succ i =>
    have hw' : coefficientDifferential E z i w = 0 := by
      change (K E z).d (i + 1) i w = 0 at hw
      exact (differential_apply E z i w).symm.trans hw
    have he := DFunLike.congr_fun (coefficient_wedge_succ E z e i) w
    change coefficientDifferential E z (i + 1) (coefficientWedge E z e (i + 1) w) +
      coefficientWedge E z e i (coefficientDifferential E z i w) = listForm z e • w at he
    rw [hw', map_zero, add_zero] at he
    exact he

private theorem filtration_d_val {n : ℕ} (h : DifferentialStable E z n) (i j : ℕ)
    (w : (filtration h).X i) :
    ((filtration h).d i j w).val = (K E z).d i j w.val := by
  exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((inclusion h).comm i j)) w).symm

private theorem exactAt_of_cycle_intersection {n : ℕ} (h : DifferentialStable E z n) (i : ℕ)
    (heq : layer E z n i ⊓ cycles E z i =
      listIdeal z • ((listIdeal z ^ (n - (i + 1)) • ⊤) ⊓ cycles E z i)) :
    (filtration h).ExactAt i := by
  have hprev : (ComplexShape.down ℕ).prev i = i + 1 :=
    ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl)
  have hnext : (ComplexShape.down ℕ).next i = i - 1 := by
    cases i with
    | zero => exact ComplexShape.next_eq_self' _ _ (by simp [ComplexShape.down_Rel])
    | succ i => exact ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl)
  rw [HomologicalComplex.exactAt_iff' (filtration h) (i + 1) i (i - 1) hprev hnext, ShortComplex.moduleCat_exact_iff]
  intro w hw
  have hw' : w.val ∈ layer E z n i ⊓ cycles E z i := by
    refine ⟨w.property, ?_⟩
    change (K E z).d i (i - 1) w.val = 0
    rw [← filtration_d_val E z h]
    change (filtration h).d i (i - 1) w = 0 at hw
    rw [hw]
    rfl
  rw [heq] at hw'
  -- Wedge multiplication sends each scalar multiple of a cycle to a boundary.
  have hmap :
      listIdeal z • ((listIdeal z ^ (n - (i + 1)) • ⊤) ⊓ cycles E z i) ≤
        (layer E z n (i + 1)).map ((K E z).d (i + 1) i).hom := by
    apply Submodule.smul_le.mpr
    intro a ha w hw
    obtain ⟨e, rfl⟩ := ideal_preimage z a ha
    have hwedge : coefficientWedge E z e i w ∈ layer E z n (i + 1) := by
      exact (Submodule.smul_top_le_comap_smul_top _ (coefficientWedge E z e i)) hw.1
    exact ⟨_, hwedge, wedge_boundary E z i e w hw.2⟩
  obtain ⟨y, hy, hdy⟩ := hmap hw'
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  change ((filtration h).d (i + 1) i (⟨y, hy⟩ : layer E z n (i + 1))).val = w.val
  exact (filtration_d_val E z h (i + 1) i ⟨y, hy⟩).trans hdy

private theorem projection_quasiIso {n : ℕ} (h : DifferentialStable E z n)
    (hF : (filtration h).Acyclic) : QuasiIso (projection h) := by
  let S := ShortComplex.mk (inclusion h) (projection h) (by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero _).mpr x.property)
  have hS : S.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
      change LinearMap.range (layer E z n i).subtype = LinearMap.ker (layer E z n i).mkQ
      rw [Submodule.range_subtype, Submodule.ker_mkQ]
    · exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
    · exact (ModuleCat.epi_iff_surjective _).mpr (layer E z n i).mkQ_surjective
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (HomologicalComplex.homologyMap S.g i) :=
    (hS.homology_exact₂ i).mono_g ((hF i).isZero_homology.eq_of_src _ _)
  have hepi : Epi (HomologicalComplex.homologyMap S.g i) := by
    cases i with
    | zero =>
      have := hS.epi_g
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0
        (by simp [ComplexShape.down_Rel])
    | succ i =>
      exact (hS.homology_exact₃ (i + 1) i rfl).epi_f ((hF i).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi (HomologicalComplex.homologyMap S.g i)

theorem eventual_acyclic : eventualAcyclicType.{u,v} := by
  intro A _ _ E _ _ _ z
  classical
  have har (i : ℕ) := by
    letI : Module.Finite A ((K E z).X i) := Module.Finite.equiv (termEquiv E z i).symm
    exact P103.Ch07.ArtinRees.artin_rees A (listIdeal z) _ (cycles E z i)
  choose c hc using har
  -- The bound includes the top Koszul degree; terms in higher degrees vanish.
  let b := (Finset.range (z.length + 1)).sup c
  refine ⟨z.length + 1 + b, fun n hn => ⟨by omega, ?_⟩⟩
  intro h
  have hF : (filtration h).Acyclic := by
    intro i
    by_cases hi : z.length < i
    · let := coefficientComplex_vanish E z i hi
      exact HomologicalComplex.ExactAt.of_isZero (ModuleCat.isZero_iff_subsingleton.mpr
        (inferInstanceAs (Subsingleton (layer E z n i))))
    · have hci : c i ≤ b := Finset.le_sup (f := c) (Finset.mem_range.mpr (by omega))
      have h₁ : c i ≤ n - i := by omega
      have h₂ : c i ≤ n - (i + 1) := by omega
      apply exactAt_of_cycle_intersection E z h i
      unfold layer
      rw [hc i _ h₁, hc i _ h₂, ← Submodule.mul_smul, ← pow_succ']
      congr 2
      omega
  exact ⟨hF, projection_quasiIso E z h hF⟩

end
end CommutativeAlgebraNotes.Intersection.StaggeredKoszul
