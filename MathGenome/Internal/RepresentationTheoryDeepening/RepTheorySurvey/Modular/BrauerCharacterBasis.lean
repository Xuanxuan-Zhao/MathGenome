import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.BrauerCharacterBasis
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.CharacterReduction
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.CompositionMultiplicities
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.OrdinaryCharacterBasis
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.RegularTraceIndependence
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-! The Brauer character basis and simple-module count of MR05. -/

noncomputable section

namespace RepTheorySurvey.Modular

open IsLocalRing (ResidueField)
open scoped BigOperators

universe uG uO uK uI uV uW uM uN

set_option backward.isDefEq.respectTransparency false

/-- A nonzero finite family of coefficients in a DVR's fraction field can be scaled
to integral coefficients with a unit among them. -/
private theorem normalizeCoefficients {O K ι : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite ι]
    {π : O} (hπ : Irreducible π) (a : ι → K) {i : ι} (hi : a i ≠ 0) :
    ∃ (t : K) (b : ι → O) (j : ι), IsUnit (b j) ∧
      ∀ l, algebraMap O K (b l) = t * a l := by
  classical
  let I := {j : ι // a j ≠ 0}
  let x := algebraMap O K π
  have hx : x ≠ 0 := fun h => hπ.ne_zero ((IsFractionRing.injective O K) (h.trans (map_zero _).symm))
  choose n u hu using fun j : I =>
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ j.property
  obtain ⟨j, -, hj⟩ := Set.exists_min_image (Set.univ : Set I) n Set.finite_univ
    ⟨⟨i, hi⟩, Set.mem_univ _⟩
  let b (l : ι) : O :=
    if h : a l ≠ 0 then (u ⟨l, h⟩ : O) * π ^ (n ⟨l, h⟩ - n j).toNat else 0
  refine ⟨x ^ (-n j), b, j.val, ?_, ?_⟩
  · simp [b, j.property]
  · intro l
    by_cases hl : a l = 0
    · simp [b, hl]
    · let s : I := ⟨l, hl⟩
      have hn : 0 ≤ n s - n j := sub_nonneg.mpr (hj s (Set.mem_univ _))
      change algebraMap O K (b l) = x ^ (-n j) * a s.val
      rw [hu s, Units.smul_def, Algebra.smul_def, mul_left_comm, ← zpow_add₀ hx]
      have he : -n j + n s = ((n s - n j).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg hn]
        omega
      rw [he, zpow_natCast]
      simp only [b, dite_eq_left hl, map_mul, map_pow]
      rfl

private theorem finiteRestrictedScalarsOfSimple
    {F G M : Type*} [Field F] [Group G] [Finite G]
    [AddCommGroup M] [Module (MonoidAlgebra F G) M] [IsSimpleModule (MonoidAlgebra F G) M] :
    Module.Finite F (RestrictScalars F (MonoidAlgebra F G) M) :=
  CompositionMultiplicity.groundFinite_of_simple (F := F) (G := G) (S := M)

section Characters

variable {G : Type uG} [Group G] [Finite G] {p : ℕ}
  {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type uK} [Field K] [Algebra O K] (system : SplittingSystem G p O K)

local notation "k" => ResidueField O
local notation "kG" => MonoidAlgebra k G
local notation "C" => PRegularConjClasses G p

private def fractionBrauerCharacter
    (M : Type uM) [AddCommGroup M] [Module kG M] [Module.Finite k (RestrictScalars k kG M)] :
    C → K :=
  fun c => algebraMap O K (brauerClassCharacter system M c)

variable {ι : Type uI} (S : ι → ModuleCat.{uV} (MonoidAlgebra (ResidueField O) G)) (hS : IsSimpleRepresentativeFamily S)

private def simpleBrauerCharacter (i : ι) : C → K :=
  letI := hS.simple i
  letI := finiteRestrictedScalarsOfSimple (F := k) (G := G) (M := S i)
  fractionBrauerCharacter system (S i)

private theorem simpleBrauerCharacter_linearIndependent :
    LinearIndependent K (simpleBrauerCharacter system S hS) := by
  classical
  let _ := system.fractionRing
  let t (i : ι) (g : PRegular G p) :=
    LinearMap.trace k _ (moduleRepresentation k G (S i) g.val)
  have ht : LinearIndependent k t := regularTrace_linearIndependent system S hS
  let _ : Finite ι := ht.finite
  let _ := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff] at ht ⊢
  intro a ha i
  by_contra hi
  have hπ : Irreducible system.uniformizer :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr system.maximalIdeal_eq_span
  obtain ⟨s, b, j, hj, hb⟩ := normalizeCoefficients hπ a hi
  let _ (l : ι) := hS.simple l
  let _ (l : ι) := finiteRestrictedScalarsOfSimple (F := k) (G := G) (M := S l)
  have hO (g : PRegular G p) : ∑ l, b l * brauerCharacter system (S l) g = 0 := by
    apply IsFractionRing.injective O K
    simp only [map_sum, map_mul, hb, map_zero, mul_assoc, ← Finset.mul_sum]
    have hg := congrFun ha (pRegularConjClass g)
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, simpleBrauerCharacter,
      fractionBrauerCharacter, brauerClassCharacter_apply, smul_eq_mul] at hg
    rw [hg, mul_zero]
  have hk : ∑ l, IsLocalRing.residue O (b l) • t l = 0 := by
    funext g
    simpa only [map_sum, map_mul, map_zero, residue_brauerCharacter, t,
      Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using
      congrArg (IsLocalRing.residue O) (hO g)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hj (ht _ hk j)

end Characters

/-- Realize the simple columns in a module universe large enough for both fields. -/
private def liftedColumnModule {F : Type uM} [Field F] {A : Type uN} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F)) (i : Fin r) :
    ModuleCat.{max uM uW} A :=
  ModuleCat.of A (ULift.{uW} (columnModule q i))

private theorem liftedColumnModule_family
    {F : Type uM} [Field F] {A : Type uN} [Ring A] [Algebra F A]
    {r : ℕ} {d : Fin r → ℕ}
    (q : A →ₐ[F] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) F))
    (hd : ∀ i, 0 < d i) (hq : Function.Surjective q)
    (hker : RingHom.ker q.toRingHom ≤ Ring.jacobson A) :
    IsSimpleRepresentativeFamily (liftedColumnModule.{uW, uM, uN} q) := by
  let e (i : Fin r) : liftedColumnModule.{uW, uM, uN} q i ≃ₗ[A] columnModule q i :=
    ULift.moduleEquiv
  have hcols := column_family q hd hq hker
  refine ⟨fun i => (e i).isSimpleModule_iff.mpr (hcols.simple i), ?_, ?_⟩
  · rintro i j ⟨f⟩
    exact hcols.eq_of_iso ⟨(e i).symm.trans (f.trans (e j))⟩
  · intro M hM
    obtain ⟨i, ⟨f⟩⟩ := column_exhaustive q hd hq hker M hM
    exact ⟨i, ⟨f.trans (e i).symm⟩⟩

section Spanning

variable {G : Type uG} [Group G] [Finite G] {p : ℕ}
  {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type uK} [Field K] [Algebra O K] (system : SplittingSystem G p O K)

local notation "k" => ResidueField O
local notation "kG" => MonoidAlgebra k G
local notation "KG" => MonoidAlgebra K G
local notation "C" => PRegularConjClasses G p
local notation "Res" => RestrictScalars k kG

private theorem fractionBrauerCharacter_congr
    {M : Type uM} [AddCommGroup M] [Module kG M] [Module.Finite k (Res M)]
    {N : Type uN} [AddCommGroup N] [Module kG N] [Module.Finite k (Res N)]
    (e : M ≃ₗ[kG] N) :
    fractionBrauerCharacter system M = fractionBrauerCharacter system N := by
  let eₖ : Res M ≃ₗ[k] Res N :=
    { toAddEquiv := (RestrictScalars.addEquiv k kG M).trans
        (e.toAddEquiv.trans (RestrictScalars.addEquiv k kG N).symm)
      map_smul' := fun a x => e.map_smul (algebraMap k kG a) x }
  funext c
  obtain ⟨g, rfl⟩ := pRegularConjClass_surjective c
  have hg : eₖ.conj (moduleRepresentation k G M g.val) =
      moduleRepresentation k G N g.val := by
    ext x
    change e (moduleRepresentation k G M g.val (e.symm x)) =
      moduleRepresentation k G N g.val x
    simp only [← Representation.asAlgebraHom_of, Representation.ofModule_asAlgebraHom_apply_apply]
    let y := RestrictScalars.addEquiv k kG N x
    change e (MonoidAlgebra.of k G g.val • e.symm y) = MonoidAlgebra.of k G g.val • y
    rw [e.map_smul, e.apply_symm_apply]
  have hpoly := (LinearEquiv.charpoly_conj eₖ (moduleRepresentation k G M g.val))
  rw [hg] at hpoly
  simp only [fractionBrauerCharacter, brauerClassCharacter_apply, brauerCharacter, hpoly]

private def fractionBrauerAdditiveCharacter :
    CompositionMultiplicity.AdditiveCharacter.{uW} k G (C → K) := by
  refine CompositionMultiplicity.AdditiveCharacter.ofExact (fun M _ _ h => ?_) ?_
  · let _ : Module.Finite k (Res M) := h
    exact fractionBrauerCharacter system M
  · intro U M N _ _ hU _ _ hM _ _ hN i q hi hq hex
    let _ : Module.Finite k (Res U) := hU
    let _ : Module.Finite k (Res M) := hM
    let _ : Module.Finite k (Res N) := hN
    have h := brauerClassCharacter_add_of_exact system U M N i q hi hq hex
    funext c
    simp only [fractionBrauerCharacter, Pi.add_apply]
    exact (congrArg (algebraMap O K) (congrFun h c)).trans (map_add _ _ _)

private theorem simpleBrauerCharacter_span {ι : Type uI}
    (S : ι → ModuleCat.{max uO uV} kG) (hS : IsSimpleRepresentativeFamily S) :
    Submodule.span K (Set.range (simpleBrauerCharacter system S hS)) = ⊤ := by
  classical
  obtain ⟨r, d, hd, e, -⟩ := ordinary_columns_exist system.ordinarySplit
  let V := liftedColumnModule.{max uO uV, uK, max uK uG} e.toAlgHom
  have he : RingHom.ker e.toAlgHom.toRingHom ≤ Ring.jacobson KG := by
    intro a ha
    have hz : e a = 0 := RingHom.mem_ker.mp ha
    rw [← map_zero e] at hz
    rw [e.injective hz]
    exact (Ring.jacobson KG).zero_mem
  have hV : IsSimpleRepresentativeFamily V := liftedColumnModule_family _ hd e.surjective he
  obtain ⟨b, hb⟩ :=
    ordinary_character_basis.{uK, uG, 0, max uO uV} V system.ordinarySplit hV
  obtain ⟨r', d', hd', e', hcols⟩ := modular_columns_exist system.modularSplit
  let q := modularColumnMap e'
  let T := liftedColumnModule.{max uK uV, uO, max uO uG} q
  have hT : IsSimpleRepresentativeFamily T :=
    liftedColumnModule_family q hd' (modularColumnMap_surjective e') (modularColumnMap_ker e').le
  let _ (j : Fin r') := hT.simple j
  let _ (j : Fin r') : CompositionMultiplicity.GroundFinite k G (T j) :=
    CompositionMultiplicity.groundFinite_of_simple (F := k) (G := G) (S := T j)
  have hT' : CompositionMultiplicity.SimpleRepresentatives (F := k) (G := G)
      (fun j => (T j : Type (max uK uO uV))) :=
    ⟨hT.simple, fun h => hT.eq_of_iso h, fun W _ _ hW => hT.exhaustive (ModuleCat.of kG W) hW⟩
  let χ : CompositionMultiplicity.AdditiveCharacter.{max uK uO uV} k G (C → K) :=
    fractionBrauerAdditiveCharacter system
  let B := Submodule.span K (Set.range (simpleBrauerCharacter system S hS))
  have hχ (j : Fin r') : χ.value (T j) ∈ B := by
    let W := liftedColumnModule.{uV, uO, max uO uG} q j
    let eW : W ≃ₗ[kG] columnModule q j := ULift.moduleEquiv
    let eT : T j ≃ₗ[kG] columnModule q j := ULift.moduleEquiv
    obtain ⟨i, ⟨f⟩⟩ := hS.exhaustive W (eW.isSimpleModule_iff.mpr (hcols.simple j))
    let _ := hS.simple i
    let _ := finiteRestrictedScalarsOfSimple (F := k) (G := G) (M := S i)
    let _ := finiteRestrictedScalarsOfSimple (F := k) (G := G) (M := T j)
    change fractionBrauerCharacter system (T j) ∈ B
    rw [fractionBrauerCharacter_congr system (eT.trans (eW.symm.trans f))]
    exact Submodule.subset_span (Set.mem_range_self i)
  let restriction := LinearMap.funLeft K K (Subtype.val : C → ConjClasses G)
  have hres : Function.Surjective restriction :=
    LinearMap.funLeft_surjective_of_injective K K _ Subtype.val_injective
  have hb_mem (j : Fin r) : restriction (b j) ∈ B := by
    let _ := hV.simple j
    let _ := finiteRestrictedScalarsOfSimple (F := K) (G := G) (M := V j)
    obtain ⟨L⟩ := exists_nativeStableLattice system (V j)
    let M := NativeStableLattice.reduction L
    let hM := NativeStableLattice.finite_reduction (V j) L
    let _ : Module.Finite k (Res M) := hM
    let _ : CompositionMultiplicity.GroundFinite k G M := hM
    have hred : restriction (b j) = χ.value M := by
      funext c
      obtain ⟨g, rfl⟩ := pRegularConjClass_surjective c
      change b j (ConjClasses.mk g.val) =
        algebraMap O K (brauerClassCharacter system M (pRegularConjClass g))
      rw [hb, brauerClassCharacter_apply]
      exact (brauerCharacter_reduction system (V j) L g).symm
    rw [hred, CompositionMultiplicity.character_eq_sum χ _ _ hT']
    exact Submodule.sum_mem B fun i _ => nsmul_mem (hχ i) _
  change B = ⊤
  apply top_unique
  rw [← LinearMap.range_eq_top.mpr hres, ← Submodule.map_top, ← b.span_eq, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact hb_mem j

end Spanning

/-- The irreducible Brauer characters form a basis of the regular class functions. -/
theorem brauer_character_basis : MR05Spec.brauerCharacterBasisType.{uG, uO, uK, uI, uV} := by
  intro G _ _ p O _ _ _ K _ _ system ι S hS
  let χ := simpleBrauerCharacter system S hS
  let b := Module.Basis.mk (simpleBrauerCharacter_linearIndependent system S hS)
    (simpleBrauerCharacter_span system S hS).ge
  refine ⟨b, fun i c => ?_⟩
  change b i c = χ i c
  rw [Module.Basis.mk_apply]

/-- There are as many simple modules as regular conjugacy classes. -/
theorem card_simple_representatives :
    MR05Spec.cardSimpleRepresentativesType.{uG, uO, uK, uI, uV} := by
  intro G _ _ p O _ _ _ K _ _ system ι S hS
  obtain ⟨b, -⟩ := brauer_character_basis system S hS
  change Module.Basis ι K (PRegularConjClasses G p → K) at b
  change Finite ι ∧ Nat.card ι = Nat.card (PRegularConjClasses G p)
  let _ : Finite ι := b.linearIndependent.finite
  let _ := Fintype.ofFinite ι
  let _ := Fintype.ofFinite (PRegularConjClasses G p)
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis b,
    Module.finrank_fintype_fun_eq_card]

end RepTheorySurvey.Modular
