import MathGenome.Internal.D07.Ch21.RegularDecompositionFiniteIrreducibleTypes
import MathGenome.Internal.D07.Ch21.MatrixOrthogonality
import MathGenome.Internal.Specs.D07.Ch21.RegularDecomposition
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace D07.Ch21.RegularDecomposition

universe u r v w
noncomputable section
open Specs.D07.Ch21.RegularDecomposition
open Specs.D07.Ch21.MatrixOrthogonality
open Specs.D07.Ch21.HomPairing

theorem irreducible_finite : IrreducibleFinite.{u,w} :=
  RegularDecompositionFiniteIrreducibleTypes.dimension_bound

theorem finite_types : FiniteTypes.{u,w} :=
  RegularDecompositionFiniteIrreducibleTypes.finite_complete_family

theorem completeness_universal : CompletenessUniversal.{u,r,v,w} := by
  intro G _ _ I V _ _ ρ hc W _ _ σ hσ
  obtain ⟨n, U, hU, _, hcomp⟩ :=
    RegularDecompositionFiniteIrreducibleTypes.regular_summands_complete.{u,w} G
  obtain ⟨j, ⟨e⟩⟩ := hcomp W σ hσ
  obtain ⟨i, ⟨f⟩⟩ := hc (U j).toSubmodule (U j).toRepresentation (hU j)
  exact ⟨i, ⟨f.trans e⟩⟩

section Family
variable {G : Type u} [Group G] [Fintype G] {I : Type r} [Fintype I]
  {V : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (ρ : ∀ i, Representation ℂ G (V i))
  (b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i))

/-- The group algebra action, recorded by the columns of each action matrix. -/
def fourierColumns : MonoidAlgebra ℂ G →ₗ[ℂ]
    (∀ p : Σ i, Fin (Module.finrank ℂ (V i)), V p.1) :=
  LinearMap.pi fun p => (LinearMap.applyₗ (R := ℂ) (M₂ := V p.1) (b p.1 p.2)).comp
    (ρ p.1).asAlgebraHom.toLinearMap

omit [Fintype G] [Fintype I] [∀ i, FiniteDimensional ℂ (V i)] in
@[simp] lemma fourierColumns_apply (a : MonoidAlgebra ℂ G)
    (p : Σ i, Fin (Module.finrank ℂ (V i))) :
    fourierColumns ρ b a p = (ρ p.1).asAlgebraHom a (b p.1 p.2) := rfl

omit [Fintype I] [∀ i, FiniteDimensional ℂ (V i)] in
lemma fourierColumns_injective (hc : IsComplete ρ) :
    Function.Injective (fourierColumns ρ b) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro a ha
  have hz : ∀ i, (ρ i).asAlgebraHom a = 0 := by
    intro i
    apply (b i).ext
    intro j
    exact congrFun ha ⟨i, j⟩
  have := (GroupAlgebra.dimension G).1
  have hm : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  obtain ⟨n, U, hU, hi⟩ := D07.Ch17.CompleteReducibility.internal_decomposition
    ℂ G (MonoidAlgebra ℂ G) hm (Representation.leftRegular ℂ G)
  let T := (Representation.leftRegular ℂ G).asAlgebraHom a
  have hk : (⨆ j, (U j).toSubmodule) ≤ LinearMap.ker T := by
    apply iSup_le
    intro j x hx
    obtain ⟨i, ⟨e⟩⟩ := hc (U j).toSubmodule (U j).toRepresentation (hU j)
    let f : V i →ₗ[ℂ] MonoidAlgebra ℂ G :=
      (U j).toSubmodule.subtype.comp e.toLinearMap
    have hf : (ρ i).IsIntertwiningMap (Representation.leftRegular ℂ G) f := by
      constructor
      intro g y
      exact congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining
        (ρ i) (U j).toRepresentation e.toIntertwiningMap g y)
    have h := (GroupAlgebra.equivariant_iff_algebra_linear G (V i)
      (MonoidAlgebra ℂ G) (ρ i) (Representation.leftRegular ℂ G) f).mp hf a
      (e.symm ⟨x, hx⟩)
    change T x = 0
    simpa [f, T, hz i] using h.symm
  rw [hi.submodule_iSup_eq_top] at hk
  have hzero : T (MonoidAlgebra.single 1 1) = 0 := hk (by trivial)
  have hmul := Representation.asAlgebraHom_ofMulAction_smul_eq_mul
    (k := ℂ) (G := G) a (MonoidAlgebra.single 1 1)
  change a = 0
  simpa only [← MonoidAlgebra.one_def, mul_one] using hmul.symm.trans hzero

/-- Orthogonality gives independence before any completeness assertion is used. -/
lemma coefficients_independent
    (hi : ∀ i, Representation.IsIrreducible (ρ i))
    (hne : ∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j)))
    (hu : ∀ i g, LinearMap.toMatrix (b i) (b i) (ρ i g) ∈
      Matrix.unitaryGroup (Fin (Module.finrank ℂ (V i))) ℂ) :
    LinearIndependent ℂ (fun p : Σ i, Fin (Module.finrank ℂ (V i)) ×
        Fin (Module.finrank ℂ (V i)) => coefficient (ρ p.1) (b p.1) p.2.1 p.2.2) := by
  classical
  let f : (Σ i, Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i))) → G → ℂ :=
    fun p => coefficient (ρ p.1) (b p.1) p.2.1 p.2.2
  have ho := (MatrixOrthogonality.family_orthogonality G I V
    (fun i => Module.finrank ℂ (V i)) ρ b hi hne hu).2
  apply Fintype.linearIndependent_iff.mpr
  intro c hc q
  let L : (G → ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun x => pairingValue G x (f q)
    map_add' := by intros; simp [pairingValue, add_mul, Finset.sum_add_distrib, mul_add]
    map_smul' := by intros; simp [pairingValue, mul_assoc, Finset.mul_sum, mul_left_comm]
  }
  have he := congrArg L hc
  have hd : (Module.finrank ℂ (V q.1) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (MatrixOrthogonality.average_self G (V q.1) (ρ q.1) (hi q.1)).1)
  have hL (p) : L (f p) = if p = q then (Module.finrank ℂ (V p.1) : ℂ)⁻¹ else 0 := ho p q
  simp only [map_sum, map_smul, map_zero] at he
  change ∑ p, c p • L (f p) = 0 at he
  simp only [hL, smul_eq_mul, mul_ite, mul_zero] at he
  have he' : c q * (Module.finrank ℂ (V q.1) : ℂ)⁻¹ = 0 := by simpa using he
  exact (mul_eq_zero.mp he').resolve_right (inv_ne_zero hd)

lemma columns_finrank :
    Module.finrank ℂ (∀ p : Σ i, Fin (Module.finrank ℂ (V i)), V p.1) =
      ∑ i, Module.finrank ℂ (V i) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ _ : Fin (Module.finrank ℂ (V i)), Module.finrank ℂ (V i)) = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two]
  rfl

omit [∀ i, FiniteDimensional ℂ (V i)] in
lemma coefficient_card :
    Fintype.card (Σ i, Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i))) =
      ∑ i, Module.finrank ℂ (V i) ^ 2 := by
  simp [Fintype.card_sigma, pow_two]

/-- The two dimension bounds use different inputs: faithfulness uses the
regular irreducible summands; the opposite bound uses Schur orthogonality. -/
lemma square_sum_of_unitary
    (hi : ∀ i, Representation.IsIrreducible (ρ i))
    (hne : ∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j)))
    (hc : IsComplete ρ)
    (hu : ∀ i g, LinearMap.toMatrix (b i) (b i) (ρ i g) ∈
      Matrix.unitaryGroup (Fin (Module.finrank ℂ (V i))) ℂ) :
    Fintype.card G = ∑ i, Module.finrank ℂ (V i) ^ 2 := by
  apply Nat.le_antisymm
  · have h := LinearMap.finrank_le_finrank_of_injective (fourierColumns_injective ρ b hc)
    simpa only [(GroupAlgebra.dimension G).2, columns_finrank] using h
  · have h := (coefficients_independent ρ b hi hne hu).fintype_card_le_finrank
    simpa only [coefficient_card, Module.finrank_pi] using h

omit [Fintype I] in
lemma unitary_bases :
    ∃ b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i),
      ∀ i g, LinearMap.toMatrix (b i) (b i) (ρ i g) ∈
        Matrix.unitaryGroup (Fin (Module.finrank ℂ (V i))) ℂ := by
  classical
  have hb (i : I) : ∃ b : Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i),
      ∀ g, LinearMap.toMatrix b b (ρ i g) ∈ Matrix.unitaryGroup _ ℂ := by
    obtain ⟨h₀, hh⟩ := UnitaryAveraging.positive_form_exists (V i)
    obtain ⟨b, _, hu, _⟩ := UnitaryAveraging.averaged_unitary_basis G (V i) (ρ i) h₀ hh
    exact ⟨b, hu⟩
  exact Classical.skolem.mp hb

end Family

theorem square_sum : SquareSum.{u,r,v} := by
  intro G _ _ I _ V _ _ ρ hi hne hc
  have : ∀ i, FiniteDimensional ℂ (V i) := fun i =>
    (irreducible_finite G (V i) (ρ i) (hi i)).1
  obtain ⟨b, hb⟩ := unitary_bases ρ
  exact square_sum_of_unitary ρ b hi hne hc hb

theorem decomposition : Decomposition.{u,r,v} := by
  intro G _ _ I _ V _ _ ρ hi hne hc
  have : ∀ i, FiniteDimensional ℂ (V i) := fun i =>
    (irreducible_finite G (V i) (ρ i) (hi i)).1
  classical
  let b (i : I) := Module.finBasis ℂ (V i)
  let C := Σ i, Fin (Module.finrank ℂ (V i))
  let E := fourierColumns ρ b
  have hinj : Function.Injective E := fourierColumns_injective ρ b hc
  have hdim : Module.finrank ℂ (MonoidAlgebra ℂ G) =
      Module.finrank ℂ (∀ p : C, V p.1) := by
    rw [(GroupAlgebra.dimension G).2, columns_finrank]
    exact square_sum G I V ρ hi hne hc
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let e := LinearEquiv.ofBijective E ⟨hinj, hsurj⟩
  let d : (DirectSum C (fun p => V p.1)) ≃ₗ[ℂ] (∀ p : C, V p.1) :=
    DFinsupp.linearEquivFunOnFintype
  refine ⟨Representation.Equiv.mk (e.trans d.symm) ?_⟩
  intro g
  apply LinearMap.ext
  intro a
  apply d.injective
  ext p
  change E ((Representation.leftRegular ℂ G g) a) p =
    ρ p.1 g ((d.symm (E a)) p)
  rw [DFinsupp.linearEquivFunOnFintype_symm_apply]
  have hreg : Representation.leftRegular ℂ G g a = MonoidAlgebra.single g 1 * a := by
    have h := Representation.asAlgebraHom_ofMulAction_smul_eq_mul
      (k := ℂ) (G := G) (MonoidAlgebra.single g 1) a
    simpa using h
  change (ρ p.1).asAlgebraHom ((Representation.leftRegular ℂ G g) a) (b p.1 p.2) =
    ρ p.1 g ((ρ p.1).asAlgebraHom a (b p.1 p.2))
  rw [hreg, map_mul, Representation.asAlgebraHom_single_one]
  rfl

theorem matrix_coefficient_basis : MatrixCoefficientBasis.{u,r,v} := by
  intro G _ _ I _ V _ _ ρ b hi hne hc hu
  have : ∀ i, FiniteDimensional ℂ (V i) := fun i =>
    (irreducible_finite G (V i) (ρ i) (hi i)).1
  classical
  let f : (Σ i, Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i))) → G → ℂ :=
    fun p => coefficient (ρ p.1) (b p.1) p.2.1 p.2.2
  have hli : LinearIndependent ℂ f := coefficients_independent ρ b hi hne hu
  have hcard : Fintype.card (Σ i, Fin (Module.finrank ℂ (V i)) ×
      Fin (Module.finrank ℂ (V i))) = Module.finrank ℂ (G → ℂ) := by
    rw [coefficient_card, Module.finrank_pi, square_sum G I V ρ hi hne hc]
  let B := basisOfLinearIndependentOfCardEqFinrank' f hli hcard
  have hB (p) : B p = f p := congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' f hli hcard) p
  refine ⟨B, hB, ?_⟩
  intro p q
  rw [hB p, hB q]
  exact (MatrixOrthogonality.family_orthogonality G I V
    (fun i => Module.finrank ℂ (V i)) ρ b hi hne hu).2 p q

theorem regular_theorem : RegularTheorem.{u,w} := by
  intro G _ _
  classical
  have := (GroupAlgebra.dimension G).1
  obtain ⟨s, hs, hi, hne, hc⟩ :=
    RegularDecompositionFiniteIrreducibleTypes.finite_complete_family.{u,u} G
  let ρ (i : s) := i.val.toRepresentation
  have hirr : ∀ i, Representation.IsIrreducible (ρ i) := fun i => hi i.val i.property
  have hneq : ∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j)) := by
    intro i j hij
    exact hne i.property j.property (fun h => hij (Subtype.ext h))
  have hcomplete : IsComplete ρ := by
    intro W _ _ σ hσ
    obtain ⟨U, hU, he⟩ := hc W σ hσ
    exact ⟨⟨U, hU⟩, he⟩
  refine ⟨s, hs, hi, hne, hcomplete, ?_, ?_, ?_⟩
  · intro W _ _ σ hσ
    exact ⟨(irreducible_finite G W σ hσ).1,
      completeness_universal G s (fun i : s => i.val.toSubmodule) ρ hcomplete W σ hσ⟩
  · exact square_sum G s (fun i : s => i.val.toSubmodule) ρ hirr hneq hcomplete
  · exact decomposition G s (fun i : s => i.val.toSubmodule) ρ hirr hneq hcomplete

end
end D07.Ch21.RegularDecomposition
