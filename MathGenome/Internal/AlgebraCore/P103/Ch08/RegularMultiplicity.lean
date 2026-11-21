import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RegularMultiplicity
import MathGenome.Internal.AlgebraCore.P103.Ch08.Schur
import MathGenome.Internal.AlgebraCore.P103.Ch08.Maschke
import MathGenome.Internal.AlgebraCore.P103.Ch08.UnitarityPairing
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section
universe u v w
namespace P103.Ch08.RegularMultiplicity
open scoped MonoidAlgebra
open RegularMultiplicitySpecs
open private libraryIrreducible from MathGenome.Internal.AlgebraCore.P103.Ch08.Schur

/-- The orbit of any nonzero vector spans an irreducible representation.
The group algebra is finite-dimensional, so its surjective orbit map proves
finite-dimensionality without assuming it for the representation. -/
theorem finite_dimensional : finiteDimensionalType.{u,v} := by
  intro G _ _ V _ _ ρ hρ
  have := libraryIrreducible ρ hρ
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.asModule)
  let f := LinearMap.toSpanSingleton ℂ[G] ρ.asModule v
  have hf : Function.Surjective f := IsSimpleModule.toSpanSingleton_surjective ℂ[G] hv
  have : FiniteDimensional ℂ ρ.asModule :=
    Module.Finite.of_surjective (f.restrictScalars ℂ) hf
  exact Module.Finite.equiv ρ.asModuleEquiv

/-- Each irreducible is isomorphic to a simple left ideal of the regular
module. This uses semisimplicity, not an assumed finite-dimensionality. -/
theorem exists_simple_ideal {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : Irreducible ℂ G V ρ) :
    ∃ S : Submodule ℂ[G] ℂ[G], IsSimpleModule ℂ[G] S ∧
      Nonempty (ρ.asModule ≃ₗ[ℂ[G]] S) := by
  have := libraryIrreducible ρ hρ
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨S, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule ℂ[G] ρ.asModule
  exact ⟨S, IsSimpleModule.congr e.symm, ⟨e⟩⟩

/-- Passing from the canonical ideal action back to a group-algebra module
recovers the original module, through the identity on its underlying vectors. -/
def idealModuleEquiv {G : Type u} [Group G]
    (S : Submodule ℂ[G] ℂ[G]) :
    (idealRepresentation S).asModule ≃ₗ[ℂ[G]] S where
  __ := (idealRepresentation S).asModuleEquiv.toAddEquiv
  map_smul' a x := by
    change ((idealRepresentation S).asAlgebraHom a)
      ((idealRepresentation S).asModuleEquiv x) = a • ((idealRepresentation S).asModuleEquiv x)
    change ((MonoidAlgebra.lift ℂ (Module.End ℂ S) G)
      ((MonoidAlgebra.lift ℂ (Module.End ℂ S) G).symm (Algebra.lsmul ℂ ℂ S))) a ((idealRepresentation S).asModuleEquiv x) = _
    rw [Equiv.apply_symm_apply]
    rfl

/-- Algebra-linear equivalences with an ideal give equivariant equivalences
with its canonical representation. -/
def idealRepresentationEquiv {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {S : Submodule ℂ[G] ℂ[G]}
    (e : S ≃ₗ[ℂ[G]] ρ.asModule) : (idealRepresentation S).Equiv ρ :=
  Representation.Equiv.mk ((e.restrictScalars ℂ).trans ρ.asModuleEquiv) (by
    intro g
    ext x
    change ρ.asModuleEquiv (e (idealRepresentation S g x)) = ρ g (ρ.asModuleEquiv (e x))
    calc
      _ = ρ.asModuleEquiv (e (MonoidAlgebra.single g (1 : ℂ) • x)) := rfl
      _ = ρ.asModuleEquiv (MonoidAlgebra.single g (1 : ℂ) • e x) := by rw [e.map_smul]
      _ = _ := by simp; rfl)

/-- An equivariant equivalence induces the same equivalence of algebra modules. -/
def moduleEquivOfEquiv {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[ℂ[G]] σ.asModule :=
  LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap)
    e.toLinearEquiv.bijective

/-- Simplicity of the inherited ideal module is exactly the source's nonzero
irreducibility convention on its associated representation. -/
theorem ideal_irreducible {G : Type u} [Group G]
    (S : Submodule ℂ[G] ℂ[G]) [IsSimpleModule ℂ[G] S] :
    Irreducible ℂ G S (idealRepresentation S) := by
  have : IsSimpleModule ℂ[G] (idealRepresentation S).asModule :=
    IsSimpleModule.congr (idealModuleEquiv S)
  have : Representation.IsIrreducible (idealRepresentation S) :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr inferInstance
  exact ⟨IsSimpleModule.nontrivial ℂ[G] S, fun U => eq_bot_or_eq_top U⟩

/-- Completeness for ideals in the regular module gives completeness in any
universe of representation spaces. -/
theorem exhaustive_from_regular {G : Type u} [Group G] [Finite G]
    (C : Family G) (hC : Exhaustive.{u,u} C) : Exhaustive.{u,v} C := by
  intro V _ _ ρ hρ
  obtain ⟨S, hS, ⟨e⟩⟩ := exists_simple_ideal ρ hρ
  have := hS
  obtain ⟨i, ⟨f⟩⟩ := hC (idealRepresentation S) (ideal_irreducible S)
  exact ⟨i, ⟨idealRepresentationEquiv ρ
    ((idealModuleEquiv (C.space i)).symm.trans
      ((moduleEquivOfEquiv f).trans ((idealModuleEquiv S).trans e.symm)))⟩⟩

/-- The finite isotypic components of the regular module give one simple
ideal for each isomorphism type, in any universe of representations. -/
theorem finite_family : finiteFamilyType.{u,v} := by
  intro G _ _
  classical
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  let A := ℂ[G]
  let I := isotypicComponents A A
  let : Fintype I := Fintype.ofFinite I
  let E := Fintype.equivFin I
  choose S hS hc using fun c : I => c.2
  let C : Family G := ⟨Fintype.card I, fun i => S (E.symm i)⟩
  have valid : Valid C := by
    refine ⟨fun i => hS _, ?_⟩
    intro i j he
    apply E.symm.injective
    apply Subtype.ext
    exact (hc _).trans (he.some.isotypicComponent_eq.trans (hc _).symm)
  refine ⟨C, valid, ?_⟩
  intro V _ _ ρ hρ
  obtain ⟨T, hT, ⟨e⟩⟩ := exists_simple_ideal ρ hρ
  have := hT
  let c : I := ⟨isotypicComponent A A T, T, hT, rfl⟩
  have := hS c
  have hle : T ≤ isotypicComponent A A (S c) := by
    rw [← hc c]
    exact T.le_isotypicComponent
  obtain ⟨f⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent A A (S c)) T hle
  refine ⟨E c, ?_⟩
  have hspace : C.space (E c) = S c := by simp [C]
  rw [hspace]
  exact ⟨idealRepresentationEquiv ρ (f.symm.trans e.symm)⟩

/-- Equivariantly isomorphic representations have equal ordinary characters. -/
theorem character_of_equiv {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) :
    CharacterSpecs.characterValue ρ = CharacterSpecs.characterValue σ := by
  exact Representation.char_iso e

/-- The pairing with an ideal representative is the indicated nonnegative
integer. The actual direct-sum counting assertion is specified separately. -/
theorem pairing_multiplicity {G : Type u} [Group G] [Fintype G]
    (C : Family G) {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (i : Fin C.n) :
    UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue ρ)
      (CharacterSpecs.characterValue (idealRepresentation (C.space i))) =
        (multiplicity C ρ i : ℂ) := by
  exact (character_pairing ρ (idealRepresentation (C.space i))).1

/-- Evaluation at the unit identifies maps out of the left regular module
with vectors in the target. -/
def regularHomEquiv {G : Type u} [Group G]
    (S : Submodule ℂ[G] ℂ[G]) : (ℂ[G] →ₗ[ℂ[G]] S) ≃ₗ[ℂ] S where
  toFun f := f 1
  invFun v := LinearMap.toSpanSingleton ℂ[G] S v
  left_inv f := by
    apply LinearMap.ext
    intro a
    change a • f 1 = f a
    rw [← f.map_smul]
    simp
  right_inv v := one_smul ℂ[G] v
  map_add' f h := rfl
  map_smul' c f := rfl

/-- Once the regular decomposition is established, its ordinary vector-space
dimension is exactly the required sum of squares. -/
theorem square_sum_of_regular_equiv {G : Type u} [Group G] [Fintype G]
    (C : Family G)
    (e : ℂ[G] ≃ₗ[ℂ[G]]
      Π₀ i : Fin C.n, (Fin (Module.finrank ℂ (C.space i)) → C.space i)) :
    Fintype.card G = ∑ i : Fin C.n, (Module.finrank ℂ (C.space i)) ^ 2 := by
  have h := ((e.restrictScalars ℂ).trans DFinsupp.linearEquivFunOnFintype).finrank_eq
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis G ℂ)] at h
  simpa [Module.finrank_pi_fintype, pow_two] using h

/-- Recover the original algebra action after conversion to a representation. -/
def ofModuleModuleEquiv {G : Type u} [Group G]
    (M : Type v) [AddCommGroup M] [Module ℂ M] [Module ℂ[G] M]
    [IsScalarTower ℂ ℂ[G] M] :
    (Representation.ofModule' (k := ℂ) (G := G) M).asModule ≃ₗ[ℂ[G]] M where
  __ := (Representation.ofModule' (k := ℂ) (G := G) M).asModuleEquiv.toAddEquiv
  map_smul' a x := by
    change ((Representation.ofModule' M).asAlgebraHom a)
      ((Representation.ofModule' M).asModuleEquiv x) =
        a • ((Representation.ofModule' M).asModuleEquiv x)
    change ((MonoidAlgebra.lift ℂ (Module.End ℂ M) G)
      ((MonoidAlgebra.lift ℂ (Module.End ℂ M) G).symm (Algebra.lsmul ℂ ℂ M))) a _ = _
    rw [Equiv.apply_symm_apply]
    rfl

/-- Simple algebra modules give nonzero irreducible representations. -/
theorem ofModule_irreducible {G : Type u} [Group G]
    (M : Type v) [AddCommGroup M] [Module ℂ M] [Module ℂ[G] M]
    [IsScalarTower ℂ ℂ[G] M] [IsSimpleModule ℂ[G] M] :
    Irreducible ℂ G M (Representation.ofModule' M) := by
  have : IsSimpleModule ℂ[G] (Representation.ofModule' (G := G) M).asModule :=
    IsSimpleModule.congr (ofModuleModuleEquiv M)
  have : Representation.IsIrreducible (Representation.ofModule' (G := G) M) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (Representation.ofModule' (k := ℂ) (G := G) M)).mpr inferInstance
  exact ⟨IsSimpleModule.nontrivial ℂ[G] M, fun U => eq_bot_or_eq_top U⟩

/-- Group a product by the fibers of a function on its index set. -/
def piFiberwise {R : Type*} [Semiring R] {J I : Type*} (t : J → I)
    {X : J → Type*} {Y : I → Type*}
    [∀ j, AddCommMonoid (X j)] [∀ j, Module R (X j)]
    [∀ i, AddCommMonoid (Y i)] [∀ i, Module R (Y i)]
    (e : ∀ i, (∀ j : {j // t j = i}, X j.1) ≃ₗ[R] Y i) :
    (∀ j, X j) ≃ₗ[R] ∀ i, Y i where
  __ := Equiv.piCongrFiberwise (f := t) (fun i => (e i).toEquiv)
  map_add' x y := by ext i; exact (e i).map_add _ _
  map_smul' a x := by ext i; exact (e i).map_smul a _

/-- A finite semisimple decomposition can be collected by any exhaustive list
of representatives. Empty fibers give zero multiplicities. -/
theorem exists_decomposition {G : Type u} [Group G] [Fintype G]
    (C : Family G) (hC : Exhaustive.{u,v} C)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) : ∃ m, Decomposition C ρ m := by
  classical
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  have : Module.Finite ℂ[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite ℂ ℂ[G] ρ.asModule
  obtain ⟨n, S, e, hs⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp ℂ[G] ρ.asModule
  have choice (j : Fin n) : ∃ i, Nonempty (S j ≃ₗ[ℂ[G]] C.space i) := by
    have := hs j
    obtain ⟨i, ⟨f⟩⟩ := hC (Representation.ofModule' (S j)) (ofModule_irreducible (S j))
    exact ⟨i, ⟨(ofModuleModuleEquiv (S j)).symm.trans
      ((moduleEquivOfEquiv f).symm.trans (idealModuleEquiv (C.space i)))⟩⟩
  choose t ht using choice
  let F (i : Fin C.n) := {j : Fin n // t j = i}
  let m (i : Fin C.n) := Fintype.card (F i)
  have fiber (i : Fin C.n) : (∀ j : F i, S j.1) ≃ₗ[ℂ[G]] (Fin (m i) → C.space i) :=
    (LinearEquiv.piCongrRight fun j : F i =>
      (ht j.1).some.trans (LinearEquiv.ofEq _ _ (congrArg C.space j.2))).trans
      (LinearEquiv.piCongrLeft ℂ[G] (fun _ => C.space i) (Fintype.equivFin (F i)))
  exact ⟨m, ⟨e.trans DFinsupp.linearEquivFunOnFintype |>.trans
    (piFiberwise t fiber) |>.trans DFinsupp.linearEquivFunOnFintype.symm⟩⟩

/-- Change both modules in an algebra Hom space, retaining complex linearity. -/
def homCongr {A : Type*} [Ring A] [Algebra ℂ A]
    {M M' N N' : Type*}
    [AddCommMonoid M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
    [AddCommMonoid M'] [Module ℂ M'] [Module A M'] [IsScalarTower ℂ A M']
    [AddCommMonoid N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
    [AddCommMonoid N'] [Module ℂ N'] [Module A N'] [IsScalarTower ℂ A N']
    (e : M ≃ₗ[A] M') (f : N ≃ₗ[A] N') :
    (M →ₗ[A] N) ≃ₗ[ℂ] (M' →ₗ[A] N') where
  __ := e.arrowCongrAddEquiv f
  map_smul' c g := by
    apply LinearMap.ext
    intro x
    exact (f.restrictScalars ℂ).map_smul c (g (e.symm x))

/-- Schur's lemma gives the Kronecker delta for the Hom dimensions. -/
theorem finrank_ideal_hom {G : Type u} [Group G] [Fintype G]
    (C : Family G) (hC : Valid C) (i j : Fin C.n) :
    Module.finrank ℂ (C.space i →ₗ[ℂ[G]] C.space j) = if i = j then 1 else 0 := by
  classical
  have := hC.1 i
  have := hC.1 j
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    let e : ℂ ≃ₗ[ℂ] Module.End ℂ[G] (C.space i) :=
      LinearEquiv.ofBijective (Algebra.linearMap ℂ (Module.End ℂ[G] (C.space i)))
        (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ)
    exact e.finrank_eq.symm.trans (Module.finrank_self ℂ)
  · have : Subsingleton (C.space i →ₗ[ℂ[G]] C.space j) := by
      apply subsingleton_of_forall_eq 0
      intro f
      rcases LinearMap.bijective_or_eq_zero f with hf | hf
      · exact (hij (hC.2 i j ⟨LinearEquiv.ofBijective f hf⟩)).elim
      · exact hf
    simp [hij, Module.finrank_eq_zero_of_subsingleton]

/-- Hom spaces between the finite-dimensional representatives are finite. -/
instance finite_ideal_hom {G : Type u} [Group G] [Fintype G]
    (S T : Submodule ℂ[G] ℂ[G]) : Module.Finite ℂ (S →ₗ[ℂ[G]] T) :=
  Module.Finite.of_injective (LinearMap.restrictScalarsₗ ℂ ℂ[G] S T ℂ)
    (LinearMap.restrictScalars_injective _)

/-- A complex module presented with only its additive monoid still has a basis. -/
private theorem free_complex_module (M : Type*) [AddCommMonoid M] [Module ℂ M] :
    Module.Free ℂ M := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup ℂ
  exact Module.Free.of_divisionRing ℂ M

local instance (M : Type*) [AddCommMonoid M] [Module ℂ M] : Module.Free ℂ M :=
  free_complex_module M

/-- Restricting algebra-linear maps embeds them in a finite-dimensional
complex Hom space, also for the monoid presentations of finite products. -/
local instance finite_complex_hom {A : Type*} [Semiring A] [Algebra ℂ A]
    (M N : Type*) [AddCommMonoid M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
    [AddCommMonoid N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
    [Module.Finite ℂ M] [Module.Finite ℂ N] : Module.Finite ℂ (M →ₗ[A] N) := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup ℂ
  exact Module.Finite.of_injective (LinearMap.restrictScalarsₗ ℂ A M N ℂ)
    (LinearMap.restrictScalars_injective _)

/-- Maps into a finite product count the copies of a given simple module. -/
theorem finrank_hom_decomposition {G : Type u} [Group G] [Fintype G]
    (C : Family G) (hC : Valid C) (m : Fin C.n → ℕ) (i : Fin C.n) :
    Module.finrank ℂ (C.space i →ₗ[ℂ[G]]
      (Π₀ j : Fin C.n, (Fin (m j) → C.space j))) = m i := by
  classical
  let e := homCongr (LinearEquiv.refl ℂ[G] (C.space i))
    (DFinsupp.linearEquivFunOnFintype (R := ℂ[G]) (M := fun j => Fin (m j) → C.space j))
  rw [e.finrank_eq, ← (LinearEquiv.linearMapPi (R := ℂ[G])
    (M₂ := C.space i) (φ := fun j => Fin (m j) → C.space j) ℂ).finrank_eq]
  have inner (j : Fin C.n) :
      Module.finrank ℂ (C.space i →ₗ[ℂ[G]] (Fin (m j) → C.space j)) =
        m j * (if i = j then 1 else 0) := by
    rw [← (LinearEquiv.linearMapPi (R := ℂ[G])
      (M₂ := C.space i) (φ := fun _ : Fin (m j) => C.space j) ℂ).finrank_eq]
    simp [Module.finrank_pi_fintype, finrank_ideal_hom C hC]
  rw [Module.finrank_pi_fintype]
  simp_rw [inner]
  simp

/-- Maps out of a finite product give the same multiplicity count. -/
theorem finrank_decomposition_hom {G : Type u} [Group G] [Fintype G]
    (C : Family G) (hC : Valid C) (m : Fin C.n → ℕ) (i : Fin C.n) :
    Module.finrank ℂ ((Π₀ j : Fin C.n, (Fin (m j) → C.space j))
      →ₗ[ℂ[G]] C.space i) = m i := by
  classical
  let e := homCongr
    (DFinsupp.linearEquivFunOnFintype (R := ℂ[G]) (M := fun j => Fin (m j) → C.space j))
    (LinearEquiv.refl ℂ[G] (C.space i))
  rw [e.finrank_eq, ← (LinearMap.lsum ℂ[G]
    (fun j : Fin C.n => Fin (m j) → C.space j) ℂ (M := C.space i)).finrank_eq]
  have inner (j : Fin C.n) :
      Module.finrank ℂ ((Fin (m j) → C.space j) →ₗ[ℂ[G]] C.space i) =
        m j * (if j = i then 1 else 0) := by
    rw [← (LinearMap.lsum ℂ[G] (fun _ : Fin (m j) => C.space j)
      ℂ (M := C.space i)).finrank_eq]
    simp [Module.finrank_pi_fintype, finrank_ideal_hom C hC]
  rw [Module.finrank_pi_fintype]
  simp_rw [inner]
  simp

/-- The number of copies in any actual decomposition is the defined Hom
multiplicity, independently of the chosen decomposition. -/
theorem multiplicity_eq_count {G : Type u} [Group G] [Fintype G]
    (C : Family G) (hC : Valid C)
    {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (m : Fin C.n → ℕ) (e : Decomposition C ρ m) : multiplicity C ρ = m := by
  funext i
  let f := (Representation.IntertwiningMap.equivLinearMapAsModule
    (idealRepresentation (C.space i)) ρ).trans
      (homCongr (idealModuleEquiv (C.space i)) e.some)
  exact f.finrank_eq.trans (finrank_hom_decomposition C hC m i)

/-- Recover an equivariant equivalence from an algebra-module equivalence. -/
def representationEquivOfModuleEquiv {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.asModule ≃ₗ[ℂ[G]] σ.asModule) : ρ.Equiv σ :=
  Representation.Equiv.mk
    (ρ.asModuleEquiv.symm.trans ((e.restrictScalars ℂ).trans σ.asModuleEquiv)) (by
      intro g
      apply LinearMap.ext
      intro v
      change σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v))) =
        σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v)))
      rw [ρ.asModuleEquiv_symm_map_rho, e.map_smul,
        σ.asModuleEquiv_map_smul, σ.asAlgebraHom_of])

/-- In the regular module, evaluation at one makes the multiplicity of a
simple representation equal to its dimension. -/
theorem regular_decomposition : regularDecompositionType.{u} := by
  intro G _ _ C hC hEx
  classical
  obtain ⟨m, ⟨e⟩⟩ := exists_decomposition C hEx
    (Representation.ofModule' (k := ℂ) (G := G) ℂ[G])
  let f := (ofModuleModuleEquiv (G := G) ℂ[G]).symm.trans e
  have hm : m = fun i => Module.finrank ℂ (C.space i) := by
    funext i
    have h := (homCongr f (LinearEquiv.refl ℂ[G] (C.space i))).finrank_eq
    rw [(regularHomEquiv (C.space i)).finrank_eq,
      finrank_decomposition_hom C hC m i] at h
    exact h.symm
  have hf : Nonempty (ℂ[G] ≃ₗ[ℂ[G]]
      Π₀ i : Fin C.n, (Fin (Module.finrank ℂ (C.space i)) → C.space i)) := by
    rw [hm] at f
    exact ⟨f⟩
  exact ⟨hf, square_sum_of_regular_equiv C hf.some⟩

/-- Semisimplicity supplies an actual decomposition, and Schur's lemma and
character pairing identify every possible list of multiplicities. -/
theorem multiplicity_decomposition : multiplicityType.{u,v} := by
  intro G _ _ C hC hEx V _ _ _ ρ
  obtain ⟨m, e⟩ := exists_decomposition C hEx ρ
  have hm := multiplicity_eq_count C hC ρ m e
  refine ⟨hm.symm ▸ e, ?_⟩
  intro m' e' i
  rw [← multiplicity_eq_count C hC ρ m' e']
  exact (pairing_multiplicity C ρ i).symm

/-- Equal ordinary characters give the same natural multiplicities and hence
an equivariant isomorphism; the converse is trace invariance. -/
theorem character_classification : characterClassificationType.{u,v,w} := by
  intro G _ _ V _ _ _ W _ _ _ ρ σ
  classical
  let : Fintype G := Fintype.ofFinite G
  refine ⟨fun ⟨e⟩ => character_of_equiv e, ?_⟩
  intro hchar
  obtain ⟨C, hC, hEx⟩ := finite_family.{u,u} (G := G)
  obtain ⟨eρ⟩ := (multiplicity_decomposition C hC (exhaustive_from_regular C hEx) ρ).1
  obtain ⟨eσ⟩ := (multiplicity_decomposition C hC (exhaustive_from_regular C hEx) σ).1
  have hm : multiplicity C ρ = multiplicity C σ := by
    funext i
    apply Nat.cast_injective (R := ℂ)
    rw [← pairing_multiplicity C ρ i, ← pairing_multiplicity C σ i, hchar]
  rw [hm] at eρ
  exact ⟨representationEquivOfModuleEquiv (eρ.trans eσ.symm)⟩

end P103.Ch08.RegularMultiplicity
