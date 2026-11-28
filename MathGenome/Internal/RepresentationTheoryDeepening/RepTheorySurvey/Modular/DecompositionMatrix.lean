import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.DecompositionMatrix
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.BrauerCharacterBasis
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.CompositionMultiplicities
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SplitMatrixColumns
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Batteries.Tactic.OpenPrivate

/-! Decomposition coefficients and the reduction of module classes. -/

namespace RepTheorySurvey.Modular

universe uG uO uK uF uV uW uI uJ

abbrev RepresentationGrothendieckGroup : MR06Spec.grothendieckGroupType.{uG, uF, uV} :=
  fun F _ G _ =>
    FreeAbelianGroup (MR06Spec.ModuleIsoClass.{uG, uF, uV} F G) ⧸
      MR06Spec.exactRelations.{uG, uF, uV} F G

noncomputable abbrev representationClass : MR06Spec.moduleClassType.{uG, uF, uV} :=
  fun V _ _ hV =>
    QuotientAddGroup.mk' (MR06Spec.exactRelations _ _)
      (MR06Spec.freeModuleClass ⟨ModuleCat.of _ V, hV⟩)

noncomputable abbrev decompositionMultiplicity :
    MR06Spec.decompositionMultiplicityType.{uG, uO, uK, uV, uW} :=
  @MR06Spec.decompositionMultiplicityValue.{uG, uO, uK, uV, uW}

noncomputable abbrev decompositionMatrix :
    MR06Spec.decompositionMatrixType.{uG, uO, uK, uV, uW, uI, uJ} :=
  @fun _ _ _ _ _ _ _ _ _ _ _ system _ V _ S χ i =>
    MR06Spec.decompositionMultiplicityValue system (V χ) (S i)

noncomputable abbrev decompositionMap : MR06Spec.decompositionMapType.{uG, uO, uK, uV} :=
  @MR06Spec.decompositionMapValue.{uG, uO, uK, uV}

open IsLocalRing (ResidueField)
open scoped BigOperators
open CompositionMultiplicity (GroundFinite multiplicity)

open private fractionBrauerCharacter simpleBrauerCharacter fractionBrauerAdditiveCharacter
  fractionBrauerCharacter_congr liftedColumnModule liftedColumnModule_family
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.BrauerCharacterBasis

set_option backward.isDefEq.respectTransparency false

section Characters

variable {G : Type uG} [Group G] [Finite G] {p : ℕ}
  {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type uK} [Field K] [Algebra O K] (system : SplittingSystem G p O K)

local notation "k" => ResidueField O
local notation "KG" => MonoidAlgebra K G
local notation "kG" => MonoidAlgebra k G
local notation "C" => PRegularConjClasses G p

include system in
private theorem exists_modular_family :
    ∃ (n : ℕ) (S : Fin n → ModuleCat.{max uO uV} kG), IsSimpleRepresentativeFamily S := by
  obtain ⟨n, d, hd, e, -⟩ := modular_columns_exist system.modularSplit
  let q := modularColumnMap e
  exact ⟨n, liftedColumnModule.{uV, uO, max uO uG} q,
    liftedColumnModule_family q hd (modularColumnMap_surjective e) (modularColumnMap_ker e).le⟩

private theorem familyGroundFinite {ι : Type uI} (S : ι → ModuleCat.{uV} kG)
    (hS : IsSimpleRepresentativeFamily S) : ∀ i, GroundFinite k G (S i) := by
  intro i
  let _ := hS.simple i
  exact CompositionMultiplicity.groundFinite_of_simple

omit [Finite G] in
private theorem familyRepresentatives {ι : Type uI} (S : ι → ModuleCat.{uV} kG)
    (hS : IsSimpleRepresentativeFamily S) :
    CompositionMultiplicity.SimpleRepresentatives (F := k) (G := G)
      (fun i => (S i : Type uV)) :=
  ⟨hS.simple, fun h => hS.eq_of_iso h, fun M _ _ hM => hS.exhaustive (ModuleCat.of kG M) hM⟩

private noncomputable def ordinaryRestriction (V : Type uV) [AddCommGroup V] [Module KG V]
    [GroundFinite K G V] : C → K :=
  letI : Module.Finite K (RestrictScalars K KG V) := ‹GroundFinite K G V›
  fun c => ordinaryClassCharacter (K := K) V c.val

private theorem ordinaryRestriction_eq_reduction
    (V : Type uV) [AddCommGroup V] [Module KG V] [GroundFinite K G V]
    (L : NativeStableLattice O K G V) :
    letI : Module.Finite k (RestrictScalars k kG (NativeStableLattice.reduction L)) :=
      NativeStableLattice.finite_reduction V L
    ordinaryRestriction (p := p) V = fractionBrauerCharacter system (NativeStableLattice.reduction L) := by
  let _ : Module.Finite K (RestrictScalars K KG V) := ‹GroundFinite K G V›
  funext c
  exact (brauerClassCharacter_reduction system V L c).symm

private theorem exists_brauer_basis {ι : Type uI} (S : ι → ModuleCat.{max uO uV} kG)
    (hS : IsSimpleRepresentativeFamily S) :
    ∃ b : Module.Basis ι K (C → K), ∀ i, b i = simpleBrauerCharacter system S hS i := by
  obtain ⟨b, hb⟩ := brauer_character_basis.{uG, uO, uK, uI, uV} system S hS
  exact ⟨b, fun i => funext (hb i)⟩

private theorem brauerCoordinates {ι : Type uI} [Fintype ι] (S : ι → ModuleCat.{uV} kG)
    (hS : IsSimpleRepresentativeFamily S) (b : Module.Basis ι K (C → K))
    (hb : ∀ i, b i = simpleBrauerCharacter system S hS i)
    (M : Type uV) [AddCommGroup M] [Module kG M] [GroundFinite k G M] (i : ι) :
    letI : Module.Finite k (RestrictScalars k kG M) := ‹GroundFinite k G M›
    b.repr (fractionBrauerCharacter system M) i = (multiplicity k G M (S i) : K) := by
  let _ : Module.Finite k (RestrictScalars k kG M) := ‹GroundFinite k G M›
  let χ := fractionBrauerAdditiveCharacter.{uG, uO, uK, uV} system
  let _ (j : ι) : GroundFinite k G (S j) := familyGroundFinite S hS j
  have h := CompositionMultiplicity.character_eq_sum χ M
    (fun j => (S j : Type uV)) (familyRepresentatives S hS)
  have hsum : fractionBrauerCharacter system M =
      ∑ j, (multiplicity k G M (S j) : K) • b j := by
    change χ.value M = _
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb, Nat.cast_smul_eq_nsmul]
    rfl
  rw [hsum, b.repr_sum_self]

private theorem latticeCoordinates {ι : Type uI} [Fintype ι]
    (S : ι → ModuleCat.{max uV uW} kG) (hS : IsSimpleRepresentativeFamily S)
    (b : Module.Basis ι K (C → K)) (hb : ∀ i, b i = simpleBrauerCharacter system S hS i)
    (V : Type uV) [AddCommGroup V] [Module KG V] [GroundFinite K G V]
    (L : NativeStableLattice O K G V) (i : ι) :
    b.repr (ordinaryRestriction (p := p) V) i =
      (multiplicity k G (NativeStableLattice.reduction L) (S i) : K) := by
  let M := NativeStableLattice.reduction L
  let _ : GroundFinite k G M := NativeStableLattice.finite_reduction V L
  let e : M ≃ₗ[kG] ULift.{uW} M := ULift.moduleEquiv.symm
  let _ : GroundFinite k G (ULift.{uW} M) :=
    CompositionMultiplicity.groundFinite_of_surjective e.toLinearMap e.surjective
  let _ : Module.Finite k (RestrictScalars k kG M) := ‹GroundFinite k G M›
  let _ : Module.Finite k (RestrictScalars k kG (ULift.{uW} M)) :=
    ‹GroundFinite k G (ULift.{uW} M)›
  rw [ordinaryRestriction_eq_reduction system V L]
  change b.repr (fractionBrauerCharacter system M) i = _
  rw [fractionBrauerCharacter_congr system e,
    brauerCoordinates system S hS b hb (ULift.{uW} M) i]
  exact congrArg (fun n : ℕ => (n : K))
    (CompositionMultiplicity.multiplicity_congr e (LinearEquiv.refl kG (S i))).symm

end Characters

/-- The composition multiplicity of a modular simple is independent of the stable lattice. -/
theorem decompositionMultiplicity_eq_lattice :
    MR06Spec.decompositionMultiplicityEqLattice.{uG, uO, uK, uV, uW} := by
  intro G _ _ p O _ _ _ K _ _ system V _ _ _ S _ _ hS L
  let k := ResidueField O
  let kG := MonoidAlgebra k G
  let _ : CharZero K := system.charZero
  obtain ⟨n, T, hT⟩ := exists_modular_family.{uG, uO, uK, max uV uW} system
  obtain ⟨b, hb⟩ := exists_brauer_basis.{uG, uO, uK, max uV uW, 0} system T hT
  let U : ModuleCat.{max uO uV uW} kG := ModuleCat.of kG (ULift.{max uO uV} S)
  let e : U ≃ₗ[kG] S := ULift.moduleEquiv
  obtain ⟨i, ⟨f⟩⟩ := hT.exhaustive U (e.isSimpleModule_iff.mpr hS)
  let iso : S ≃ₗ[kG] T i := e.symm.trans f
  have h (L' : NativeStableLattice O K G V) :
      b.repr (ordinaryRestriction (p := p) V) i =
        (multiplicity k G (NativeStableLattice.reduction L') S : K) := by
    let _ : GroundFinite k G (NativeStableLattice.reduction L') := NativeStableLattice.finite_reduction V L'
    have hcoord :=
      latticeCoordinates.{uG, uO, uK, uV, max uO uW, 0} system T hT b hb V L' i
    have hmult := CompositionMultiplicity.multiplicity_congr
      (LinearEquiv.refl kG (NativeStableLattice.reduction L')) iso
    exact hcoord.trans (congrArg (fun n : ℕ => (n : K)) hmult).symm
  let counts : Set ℕ := {a | ∃ L' : NativeStableLattice O K G V,
    multiplicity k G (NativeStableLattice.reduction L') S = a}
  change sInf counts = multiplicity k G (NativeStableLattice.reduction L) S
  obtain ⟨L', hL'⟩ := Nat.sInf_mem (s := counts) ⟨_, L, rfl⟩
  exact hL'.symm.trans (Nat.cast_injective (R := K) ((h L').symm.trans (h L)))

section Characters

variable {G : Type uG} [Group G] [Finite G] {p : ℕ}
  {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type uK} [Field K] [Algebra O K] (system : SplittingSystem G p O K)

local notation "k" => ResidueField O
local notation "KG" => MonoidAlgebra K G
local notation "kG" => MonoidAlgebra k G
local notation "C" => PRegularConjClasses G p

private theorem decompositionCoordinates {ι : Type uI} [Fintype ι]
    (S : ι → ModuleCat.{max uV uW} kG) (hS : IsSimpleRepresentativeFamily S)
    (b : Module.Basis ι K (C → K)) (hb : ∀ i, b i = simpleBrauerCharacter system S hS i)
    (V : Type uV) [AddCommGroup V] [Module KG V] [GroundFinite K G V] (i : ι) :
    b.repr (ordinaryRestriction (p := p) V) i = (decompositionMultiplicity system V (S i) : K) := by
  let _ : Module.Finite K (RestrictScalars K KG V) := ‹GroundFinite K G V›
  let _ := hS.simple i
  obtain ⟨L⟩ := exists_nativeStableLattice system V
  exact (latticeCoordinates system S hS b hb V L i).trans
    (congrArg (fun n : ℕ => (n : K)) (decompositionMultiplicity_eq_lattice system V (S i) L)).symm

include system in
/-- Enlarging the universe of the representatives preserves exhaustiveness in the larger
module category, because every simple is isomorphic to a column of the same split algebra. -/
private theorem liftedModularFamily {ι : Type uI}
    (S : ι → ModuleCat.{max uO uW} kG) (hS : IsSimpleRepresentativeFamily S) :
    IsSimpleRepresentativeFamily (fun i => ModuleCat.of kG (ULift.{uV} (S i))) := by
  let e (i : ι) : ULift.{uV} (S i) ≃ₗ[kG] S i := ULift.moduleEquiv
  refine ⟨fun i => (e i).isSimpleModule_iff.mpr (hS.simple i), ?_, ?_⟩
  · rintro i j ⟨f⟩
    exact hS.eq_of_iso ⟨(e i).symm.trans (f.trans (e j))⟩
  · intro M hM
    obtain ⟨n, d, hd, E, hcolumns⟩ := modular_columns_exist system.modularSplit
    let q := modularColumnMap E
    obtain ⟨j, ⟨f⟩⟩ := column_exhaustive q hd
      (modularColumnMap_surjective E) (modularColumnMap_ker E).le M hM
    let W := liftedColumnModule.{uW, uO, max uO uG} q j
    let eW : W ≃ₗ[kG] columnModule q j := ULift.moduleEquiv
    obtain ⟨i, ⟨f'⟩⟩ := hS.exhaustive W (eW.isSimpleModule_iff.mpr (hcolumns.simple j))
    exact ⟨i, ⟨f.trans (eW.symm.trans (f'.trans (e i).symm))⟩⟩

private theorem characterFormula {ι : Type uI} [Fintype ι]
    (S : ι → ModuleCat.{max uO uW} kG) (hS : IsSimpleRepresentativeFamily S)
    (V : Type uV) [AddCommGroup V] [Module KG V] [GroundFinite K G V] :
    ordinaryRestriction (p := p) V =
      ∑ i, (decompositionMultiplicity system V (S i) : K) • simpleBrauerCharacter system S hS i := by
  let _ : Module.Finite K (RestrictScalars K KG V) := ‹GroundFinite K G V›
  let T (i : ι) := ModuleCat.of kG (ULift.{uV} (S i))
  let e (i : ι) : T i ≃ₗ[kG] S i := ULift.moduleEquiv
  have hT : IsSimpleRepresentativeFamily T :=
    liftedModularFamily.{uG, uO, uK, uV, uW, uI} system S hS
  obtain ⟨L⟩ := exists_nativeStableLattice system V
  let M := NativeStableLattice.reduction L
  let _ : GroundFinite k G M := NativeStableLattice.finite_reduction V L
  obtain ⟨b, hb⟩ := exists_brauer_basis.{uG, uO, uK, max uV uW, uI} system T hT
  calc
    ordinaryRestriction (p := p) V =
        ∑ i, b.repr (ordinaryRestriction (p := p) V) i • b i := (b.sum_repr _).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      let _ := hS.simple i
      let _ : Module.Finite k (RestrictScalars k kG (S i)) := familyGroundFinite S hS i
      let _ : Module.Finite k (RestrictScalars k kG (T i)) := familyGroundFinite T hT i
      have hcount := CompositionMultiplicity.multiplicity_congr (LinearEquiv.refl kG M) (e i)
      have hcoord := latticeCoordinates.{uG, uO, uK, uV, max uO uW, uI} system T hT b hb V L i
      have hm : decompositionMultiplicity system V (S i) = multiplicity k G M (S i) :=
        decompositionMultiplicity_eq_lattice system V (S i) L
      have hchar : simpleBrauerCharacter system T hT i = simpleBrauerCharacter system S hS i :=
        fractionBrauerCharacter_congr system (e i)
      rw [hcoord, hcount, ← hm, hb, hchar]

end Characters

/-- Restriction of any finite-dimensional ordinary character to the regular classes. -/
theorem decompositionCharacter_formula :
    MR06Spec.decompositionCharacterFormula.{uG, uO, uK, uV, uJ} := by
  intro G _ _ p O _ _ _ K _ _ system ι _ S hS V _ _ hV
  let _ : GroundFinite K G V := hV
  exact characterFormula.{uG, uO, uK, max uO uV, uV, uJ} system S hS V

section MatrixEntries

variable {G : Type uG} [Group G] [Finite G] {p : ℕ}
  {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type uK} [Field K] [Algebra O K] (system : SplittingSystem G p O K)

local notation "k" => ResidueField O
local notation "KG" => MonoidAlgebra K G
local notation "kG" => MonoidAlgebra k G

/-- Each entry is the composition multiplicity in the reduction of any stable lattice. -/
theorem decompositionMatrix_apply_eq_lattice {ι : Type uI} {κ : Type uJ}
    (V : ι → ModuleCat.{uV} KG) (hV : IsSimpleRepresentativeFamily V)
    (S : κ → ModuleCat.{uW} kG) (hS : IsSimpleRepresentativeFamily S)
    (χ : ι) (i : κ) (L : NativeStableLattice O K G (V χ)) :
    decompositionMatrix system V S χ i = multiplicity k G (NativeStableLattice.reduction L) (S i) := by
  let _ := hV.simple χ
  let _ := hS.simple i
  let _ : GroundFinite K G (V χ) := CompositionMultiplicity.groundFinite_of_simple
  exact decompositionMultiplicity_eq_lattice system (V χ) (S i) L

/-- The pointwise character identity for any finite-dimensional ordinary module.
The carrier universes of the ordinary module and the modular simples may differ. -/
theorem ordinaryCharacter_decomposition_sum {κ : Type uJ} [Fintype κ]
    (S : κ → ModuleCat.{max uO uW} kG) (hS : IsSimpleRepresentativeFamily S)
    (V : Type uV) [AddCommGroup V] [Module KG V] [Module.Finite K (RestrictScalars K KG V)]
    (g : PRegular G p) :
    ordinaryCharacter (K := K) V g.val =
      ∑ i, (decompositionMultiplicity system V (S i) : K) *
        (letI : Module.Finite k (RestrictScalars k kG (S i)) := familyGroundFinite S hS i
         algebraMap O K (brauerCharacter system (S i) g)) := by
  let _ : GroundFinite K G V := ‹Module.Finite K (RestrictScalars K KG V)›
  have h := characterFormula.{uG, uO, uK, uV, uW, uJ} system S hS V
  have hg := congrFun h (pRegularConjClass g)
  simp only [ordinaryRestriction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    simpleBrauerCharacter, fractionBrauerCharacter, brauerClassCharacter_apply] at hg
  change ordinaryClassCharacter (K := K) V (ConjClasses.mk g.val) = _ at hg
  rwa [ordinaryClassCharacter_apply] at hg

/-- The row of the decomposition matrix gives the character identity at each regular element. -/
theorem decompositionMatrix_row_formula {ι : Type uI} {κ : Type uJ} [Fintype κ]
    (V : ι → ModuleCat.{uV} KG) (hV : IsSimpleRepresentativeFamily V)
    (S : κ → ModuleCat.{max uO uW} kG) (hS : IsSimpleRepresentativeFamily S)
    (χ : ι) :
    letI : Module.Finite K (RestrictScalars K KG (V χ)) :=
      letI := hV.simple χ
      CompositionMultiplicity.groundFinite_of_simple (F := K) (G := G) (S := V χ)
    ∀ g : PRegular G p,
      ordinaryCharacter (K := K) (V χ) g.val =
        ∑ i, (decompositionMatrix system V S χ i : K) *
          (letI : Module.Finite k (RestrictScalars k kG (S i)) := familyGroundFinite S hS i
           algebraMap O K (brauerCharacter system (S i) g)) := by
  intro g
  let _ := hV.simple χ
  let _ : Module.Finite K (RestrictScalars K KG (V χ)) :=
    CompositionMultiplicity.groundFinite_of_simple (F := K) (G := G) (S := V χ)
  exact ordinaryCharacter_decomposition_sum system S hS (V χ) g

end MatrixEntries

section ExactSequences

open private charpoly_mul_of_exact intertwines_moduleRepresentation
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.BrauerCharacterLaws

private theorem trace_eq_neg_charpoly_nextCoeff {F M : Type*} [Field F]
    [AddCommGroup M] [Module F M] [Module.Finite F M] (T : Module.End F M) :
    LinearMap.trace F M T = -T.charpoly.nextCoeff := by
  classical
  let b := Module.finBasis F M
  rw [LinearMap.trace_eq_matrix_trace F b, ← LinearMap.charpoly_toMatrix T b,
    Matrix.trace_eq_neg_charpoly_nextCoeff]

attribute [local instance] RestrictScalars.moduleOrig in
private theorem ordinaryRestriction_add_of_exact {G : Type uG} [Group G] {p : ℕ}
    {F : Type uF} [Field F]
    {U V W : Type uV}
    [AddCommGroup U] [Module (MonoidAlgebra F G) U] [GroundFinite F G U]
    [AddCommGroup V] [Module (MonoidAlgebra F G) V] [GroundFinite F G V]
    [AddCommGroup W] [Module (MonoidAlgebra F G) W] [GroundFinite F G W]
    (i : U →ₗ[MonoidAlgebra F G] V) (q : V →ₗ[MonoidAlgebra F G] W)
    (hi : Function.Injective i) (hq : Function.Surjective q) (hex : Function.Exact i q) :
    ordinaryRestriction (G := G) (K := F) (p := p) V =
      ordinaryRestriction (G := G) (K := F) (p := p) U +
        ordinaryRestriction (G := G) (K := F) (p := p) W := by
  let R := MonoidAlgebra F G
  let Res := RestrictScalars F R
  let _ : Module.Finite F (Res U) := ‹GroundFinite F G U›
  let _ : Module.Finite F (Res V) := ‹GroundFinite F G V›
  let _ : Module.Finite F (Res W) := ‹GroundFinite F G W›
  let i' : Res U →ₗ[F] Res V := (show Res U →ₗ[R] Res V from i).restrictScalars F
  let q' : Res V →ₗ[F] Res W := (show Res V →ₗ[R] Res W from q).restrictScalars F
  funext c
  obtain ⟨g, rfl⟩ := pRegularConjClass_surjective c
  let A := moduleRepresentation F G U g.val
  let B := moduleRepresentation F G V g.val
  let D := moduleRepresentation F G W g.val
  have h := charpoly_mul_of_exact (i := i') (q := q') hi hq hex A B D
    (intertwines_moduleRepresentation i g.val) (intertwines_moduleRepresentation q g.val)
  change LinearMap.trace F (Res V) B =
    LinearMap.trace F (Res U) A + LinearMap.trace F (Res W) D
  simp only [trace_eq_neg_charpoly_nextCoeff]
  rw [h, A.charpoly_monic.nextCoeff_mul D.charpoly_monic, neg_add]

end ExactSequences

section GrothendieckGroup

variable {F : Type uF} [Field F] {G : Type uG} [Group G]

local notation "R" => MonoidAlgebra F G

/-- The relation in the representation Grothendieck group attached to a short exact sequence. -/
theorem representationClass_add_of_exact {U V W : Type uV}
    [AddCommGroup U] [Module R U] [GroundFinite F G U]
    [AddCommGroup V] [Module R V] [GroundFinite F G V]
    [AddCommGroup W] [Module R W] [GroundFinite F G W]
    (i : U →ₗ[R] V) (q : V →ₗ[R] W)
    (hi : Function.Injective i) (hq : Function.Surjective q) (hex : Function.Exact i q) :
    (representationClass V : RepresentationGrothendieckGroup.{uG, uF, uV} F G) = representationClass U + representationClass W := by
  let U' : MR06Spec.FiniteModule.{uG, uF, uV} F G := ⟨ModuleCat.of R U, ‹GroundFinite F G U›⟩
  let V' : MR06Spec.FiniteModule.{uG, uF, uV} F G := ⟨ModuleCat.of R V, ‹GroundFinite F G V›⟩
  let W' : MR06Spec.FiniteModule.{uG, uF, uV} F G := ⟨ModuleCat.of R W, ‹GroundFinite F G W›⟩
  let π := QuotientAddGroup.mk' (MR06Spec.exactRelations.{uG, uF, uV} F G)
  change π (MR06Spec.freeModuleClass V') =
    π (MR06Spec.freeModuleClass U') + π (MR06Spec.freeModuleClass W')
  rw [← map_add, ← sub_eq_zero, ← map_sub]
  exact (QuotientAddGroup.eq_zero_iff _).mpr
    (AddSubgroup.subset_closure ⟨U', V', W', i, q, hi, hq, hex, rfl⟩)

private noncomputable def representationClassCharacter :
    CompositionMultiplicity.AdditiveCharacter.{uV} F G
      (RepresentationGrothendieckGroup.{uG, uF, uV} F G) :=
  CompositionMultiplicity.AdditiveCharacter.ofExact
    (fun V _ _ _ => representationClass V)
    (fun i q hi hq hex => representationClass_add_of_exact i q hi hq hex)

variable {B : Type uW} [AddCommGroup B]
  (χ : CompositionMultiplicity.AdditiveCharacter.{uV} F G B)

private noncomputable def isoClassValue : MR06Spec.ModuleIsoClass.{uG, uF, uV} F G → B :=
  Quotient.lift (fun V => @χ.value V.val _ _ V.property) (by
    rintro V W ⟨e⟩
    let _ := V.property
    let _ := W.property
    exact χ.congr e)

private theorem liftIsoClassValue_apply (V : MR06Spec.FiniteModule.{uG, uF, uV} F G) :
    FreeAbelianGroup.lift (isoClassValue χ) (MR06Spec.freeModuleClass V) =
      @χ.value V.val _ _ V.property := by
  rw [MR06Spec.freeModuleClass, FreeAbelianGroup.lift_apply_of]
  rfl

/-- An exact-additive invariant descends to the group presented by the module classes. -/
private noncomputable def liftRepresentationClass : RepresentationGrothendieckGroup.{uG, uF, uV} F G →+ B := by
  let f := FreeAbelianGroup.lift (isoClassValue χ)
  refine QuotientAddGroup.lift (MR06Spec.exactRelations.{uG, uF, uV} F G) f ?_
  rw [MR06Spec.exactRelations, AddSubgroup.closure_le]
  rintro _ ⟨U, V, W, i, q, hi, hq, hex, rfl⟩
  change f _ = 0
  simp only [map_sub, map_add, f, liftIsoClassValue_apply, sub_eq_zero]
  let _ := U.property
  let _ := V.property
  let _ := W.property
  exact χ.exact i q hi hq hex

private theorem liftRepresentationClass_apply (V : Type uV) [AddCommGroup V] [Module R V]
    [hV : GroundFinite F G V] :
    liftRepresentationClass χ (representationClass V) = χ.value V := by
  change FreeAbelianGroup.lift (isoClassValue χ)
    (MR06Spec.freeModuleClass ⟨ModuleCat.of R V, hV⟩) = _
  rw [liftIsoClassValue_apply]

private theorem representationClass_hom_ext
    {d e : RepresentationGrothendieckGroup.{uG, uF, uV} F G →+ B}
    (h : ∀ (V : Type uV) [AddCommGroup V] [Module R V] [GroundFinite F G V],
      d (representationClass V) = e (representationClass V)) : d = e := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro c
  obtain ⟨V, rfl⟩ := Quotient.exists_rep c
  let _ := V.property
  exact h V.val

end GrothendieckGroup

/-- Reduction on the representation Grothendieck groups sends every ordinary module class
to the class of the reduction of any stable lattice, which determines it uniquely. -/
theorem decompositionMap_onClasses : MR06Spec.decompositionMapOnClasses.{uG, uO, uK, uV} := by
  intro G _ _ p O _ _ _ K _ _ system
  let k := ResidueField O
  let KG := MonoidAlgebra K G
  let Target := RepresentationGrothendieckGroup.{uG, uO, max uO uV} k G
  let _ : CharZero K := system.charZero
  obtain ⟨n, S, hS⟩ := exists_modular_family.{uG, uO, uK, uV} system
  obtain ⟨b, hb⟩ := exists_brauer_basis.{uG, uO, uK, uV, 0} system S hS
  let _ (i : Fin n) : GroundFinite k G (S i) := familyGroundFinite S hS i
  let classOf (V : Type (max uO uV)) [AddCommGroup V] [Module KG V] : Target :=
    ∑ i, decompositionMultiplicity system V (S i) • representationClass (S i)
  have hcoord (V : Type (max uO uV)) [AddCommGroup V] [Module KG V]
      [GroundFinite K G V] (i : Fin n) :
      b.repr (ordinaryRestriction (p := p) V) i = (decompositionMultiplicity system V (S i) : K) :=
    decompositionCoordinates.{uG, uO, uK, max uO uV, 0, 0} system S hS b hb V i
  let χ : CompositionMultiplicity.AdditiveCharacter.{max uO uV} K G Target :=
    CompositionMultiplicity.AdditiveCharacter.ofExact (fun V _ _ _ => classOf V) (by
      intro U V W _ _ _ _ _ _ _ _ _ f q hf hq hex
      have hadd (i : Fin n) :
          decompositionMultiplicity system V (S i) =
            decompositionMultiplicity system U (S i) + decompositionMultiplicity system W (S i) := by
        apply Nat.cast_injective (R := K)
        rw [Nat.cast_add, ← hcoord V i, ← hcoord U i, ← hcoord W i,
          ordinaryRestriction_add_of_exact (p := p) f q hf hq hex, map_add, Finsupp.add_apply]
      change classOf V = classOf U + classOf W
      simp only [classOf, hadd, add_nsmul, Finset.sum_add_distrib])
  let d := liftRepresentationClass χ
  have hd : MR06Spec.SendsLattices (O := O) d := by
    intro V _ _ _ L
    let M := NativeStableLattice.reduction L
    let _ : GroundFinite k G M := NativeStableLattice.finite_reduction V L
    change d (representationClass V) = representationClass M
    rw [liftRepresentationClass_apply]
    have h := CompositionMultiplicity.character_eq_sum
      (representationClassCharacter (F := k) (G := G)) M
      (fun i => (S i : Type (max uO uV))) (familyRepresentatives S hS)
    change (representationClass M : Target) =
      ∑ i, multiplicity k G M (S i) • representationClass (S i) at h
    change (∑ i, decompositionMultiplicity system V (S i) • representationClass (S i)) =
      (representationClass M : Target)
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    let _ := hS.simple i
    have hmult : decompositionMultiplicity system V (S i) = multiplicity k G M (S i) :=
      decompositionMultiplicity_eq_lattice system V (S i) L
    rw [hmult]
  have hd' : MR06Spec.SendsLattices (decompositionMap.{uG, uO, uK, uV} system) :=
    Classical.epsilon_spec ⟨d, hd⟩
  refine ⟨hd', fun d' hd'' => ?_⟩
  apply representationClass_hom_ext
  intro V _ _ hV
  let _ : Module.Finite K (RestrictScalars K KG V) := hV
  obtain ⟨L⟩ := exists_nativeStableLattice system V
  exact (hd'' V L).trans (hd' V L).symm

end RepTheorySurvey.Modular
