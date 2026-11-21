import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.SplitFourierTransform
import MathGenome.Internal.AlgebraCore.P103.Ch08.RepresentationModules
import MathGenome.Internal.AlgebraCore.P103.Ch08.Maschke
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.Finiteness.Basic

noncomputable section
open scoped MonoidAlgebra
namespace P103.Ch08.SplitFourierTransform

/-- The source's nonzero convention agrees with the simple-order interface. -/
theorem simple_asModule {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (h : Irreducible k G V ρ) : IsSimpleModule k[G] ρ.asModule := by
  haveI : Nontrivial V := h.1
  haveI : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, fun he =>
    bot_ne_top (congrArg Subrepresentation.toSubmodule he)⟩⟩
  haveI : IsSimpleOrder (Subrepresentation ρ) := ⟨h.2⟩
  exact (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance

theorem finite_dimensional : Specs.finiteDimensionalType := by
  intro k G _ _ _ V _ _ ρ h
  haveI := simple_asModule ρ h
  haveI := IsSimpleModule.nontrivial k[G] ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.asModule)
  have hs := IsSimpleModule.toSpanSingleton_surjective k[G] hv
  haveI : Module.Finite k ρ.asModule :=
    Module.Finite.of_surjective ((LinearMap.toSpanSingleton k[G] ρ.asModule v).restrictScalars k) hs
  exact Module.Finite.equiv ρ.asModuleEquiv

section Algebra
variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)]
  [∀ i, Module k (M i)] [∀ i, Module A (M i)] [∀ i, IsScalarTower k A (M i)]

/-- A nonrepeating family of simples over a semisimple ring is finite. -/
theorem finite_simple_family [IsSemisimpleRing A] [∀ i, IsSimpleModule A (M i)]
    (hne : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) : Finite ι := by
  classical
  choose S e using fun i => IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A (M i)
  let e' (i) := (e i).some
  letI : ∀ i, IsSimpleModule A (S i) := fun i => IsSimpleModule.congr (e' i).symm
  let f : ι → isotypicComponents A A := fun i =>
    ⟨isotypicComponent A A (S i), S i, inferInstance, rfl⟩
  apply Finite.of_injective f
  intro i j hij
  have hc : isotypicComponent A A (S i) = isotypicComponent A A (S j) := congrArg Subtype.val hij
  have hle : S i ≤ isotypicComponent A A (S j) := hc ▸ (S i).le_isotypicComponent
  obtain ⟨d⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent A A (S j)) (S i) hle
  exact hne i j ⟨(e' i).trans (d.trans (e' j).symm)⟩

/-- Schur endomorphisms are preserved by module equivalence. -/
theorem scalar_end_of_equiv {N : Type*} [AddCommGroup N] [Module k N]
    [Module A N] [IsScalarTower k A N] {P : Type*} [AddCommGroup P]
    [Module k P] [Module A P] [IsScalarTower k A P]
    (e : N ≃ₗ[A] P)
    (h : Function.Surjective (algebraMap k (Module.End A P))) :
    Function.Surjective (algebraMap k (Module.End A N)) := by
  intro f
  obtain ⟨c, hc⟩ := h (e.conjAlgEquiv k f)
  refine ⟨c, (e.conjAlgEquiv k).injective ?_⟩
  simpa only [AlgEquiv.commutes] using hc

/-- Endomorphisms of a finite sum of pairwise distinct split simples are
coordinatewise scalar. -/
theorem end_pi_scalar [Fintype ι] [∀ i, IsSimpleModule A (M i)]
    (hne : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hscalar : ∀ i, Function.Surjective (algebraMap k (Module.End A (M i))))
    (g : Module.End A (Π i, M i)) (i : ι) :
    ∃ c : k, ∀ x, (g x) i = c • x i := by
  classical
  let gij (j) : M j →ₗ[A] M i :=
    (LinearMap.proj i).comp (g.comp (LinearMap.single A M j))
  obtain ⟨c, hc⟩ := hscalar i (gij i)
  have hoff (j) (hji : j ≠ i) : gij j = 0 := by
    by_contra hz
    have e := LinearEquiv.ofBijective (gij j) (LinearMap.bijective_of_ne_zero hz)
    exact hji (hne j i ⟨e⟩)
  refine ⟨c, fun x => ?_⟩
  calc
    (g x) i = ∑ j, gij j (x j) := by
      conv_lhs => rw [← LinearMap.sum_single_apply M x]
      simp [gij, map_sum, Finset.sum_apply]
    _ = gij i (x i) := Finset.sum_eq_single i
      (fun j _ hji => by rw [hoff j hji]; rfl) (by simp)
    _ = c • x i := by rw [← hc]; rfl

/-- Density realizes all independently prescribed linear operators on the
pairwise distinct split simple constituents. -/
theorem action_surjective [Finite ι] [IsSemisimpleRing A]
    [∀ i, IsSimpleModule A (M i)] [∀ i, Module.Finite k (M i)]
    (hne : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (hscalar : ∀ i, Function.Surjective (algebraMap k (Module.End A (M i)))) :
    Function.Surjective (AlgHom.pi (fun i => Algebra.lsmul k k (M i) (A := A))) := by
  classical
  letI := Fintype.ofFinite ι
  intro t
  let f : Module.End (Module.End A (Π i, M i)) (Π i, M i) :=
    { toFun := fun x i => t i (x i)
      map_add' := by intros; ext; simp
      map_smul' := by
        intro g x
        ext i
        obtain ⟨c, hc⟩ := end_pi_scalar M hne hscalar g i
        change t i ((g x) i) = (g (fun j => t j (x j))) i
        rw [hc, hc, map_smul] }
  haveI : Module.Finite (Module.End A (Π i, M i)) (Π i, M i) :=
    Module.Finite.of_restrictScalars_finite k _ _
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective
    (R := A) (M := Π i, M i) f
  refine ⟨a, ?_⟩
  ext i x
  have hx := congrArg (fun q : Module.End (Module.End A (Π i, M i)) (Π i, M i) =>
    q (Pi.single i x) i) ha
  simpa [f] using hx

/-- All simple regular constituents together detect elements of a semisimple algebra. -/
theorem action_injective [IsSemisimpleRing A]
    (hcomplete : ∀ S : Ideal A, IsSimpleModule A S →
      ∃ i, Nonempty (S ≃ₗ[A] M i)) :
    Function.Injective (AlgHom.pi (fun i => Algebra.lsmul k k (M i) (A := A))) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hz (S : Ideal A) (hs : IsSimpleModule A S) (x : A) (hx : x ∈ S) :
      a * x = 0 := by
    obtain ⟨i, ⟨e⟩⟩ := hcomplete S hs
    have hi : Algebra.lsmul k k (M i) a = 0 := congrArg (fun t => t i) ha
    have hex : a • e ⟨x, hx⟩ = 0 :=
      LinearMap.congr_fun hi (e ⟨x, hx⟩)
    have hez : a • (⟨x, hx⟩ : S) = 0 :=
      e.injective (by rw [map_smul, map_zero]; exact hex)
    exact congrArg Subtype.val hez
  have htop : (1 : A) ∈ (⨆ S : {S : Ideal A // IsSimpleModule A S}, S.1 : Ideal A) := by
    have ht := IsSemisimpleModule.sSup_simples_eq_top A A
    rw [sSup_eq_iSup'] at ht
    have ht' : (⨆ S : {S : Ideal A // IsSimpleModule A S}, S.1 : Ideal A) = ⊤ := ht
    rw [ht']
    trivial
  have h1 : a * (1 : A) = 0 :=
    Submodule.iSup_induction _ (motive := fun x => a * x = 0) htop
      (fun S x hx => hz S S.2 x hx) (mul_zero a)
      (fun x y hx hy => by rw [mul_add, hx, hy, add_zero])
  simpa using h1

end Algebra

theorem finite_family : Specs.finiteFamilyType := by
  intro k G _ _ _ ι V _ _ ρ hn hρ hne
  haveI : NeZero (Nat.card G : k) := ⟨hn⟩
  letI : ∀ i, IsSimpleModule k[G] (ρ i).asModule := fun i => simple_asModule (ρ i) (hρ i)
  exact finite_simple_family (fun i => (ρ i).asModule) hne

/-- Splitting gives the full product of linear operators, through the actual actions. -/
theorem actionMap_surjective
    {k G : Type*} [Field k] [Group G] [Finite G]
    {ι : Type*} {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (ρ : ∀ i, Representation k G (V i))
    (hn : (Nat.card G : k) ≠ 0) (hsplit : Splits k G)
    (hρ : ∀ i, Irreducible k G (V i) (ρ i)) (hne : Nonrepeating ρ) :
    Function.Surjective (actionMap ρ) := by
  haveI : NeZero (Nat.card G : k) := ⟨hn⟩
  letI : ∀ i, IsSimpleModule k[G] (ρ i).asModule :=
    fun i => simple_asModule (ρ i) (hρ i)
  haveI : Finite ι := finite_family ρ hn hρ hne
  letI : ∀ i, Module.Finite k (V i) := fun i => finite_dimensional (ρ i) (hρ i)
  have hscalar (i : ι) : Function.Surjective
      (algebraMap k (Module.End k[G] (ρ i).asModule)) := by
    obtain ⟨S, ⟨e⟩⟩ :=
      IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule k[G] (ρ i).asModule
    haveI : IsSimpleModule k[G] S := IsSimpleModule.congr e.symm
    exact scalar_end_of_equiv e (hsplit S inferInstance).2
  exact action_surjective (fun i => (ρ i).asModule) hne hscalar

/-- The split-field Fourier isomorphism, with its prescribed representative formula. -/
theorem fourier : Specs.fourierType := by
  intro k G _ _ _ ι V _ _ ρ hn hsplit hρ hcomplete hne
  haveI : NeZero (Nat.card G : k) := ⟨hn⟩
  have hinj : Function.Injective (actionMap ρ) :=
    action_injective (fun i => (ρ i).asModule) hcomplete
  have hsurj := actionMap_surjective ρ hn hsplit hρ hne
  exact ⟨AlgEquiv.ofBijective (actionMap ρ) ⟨hinj, hsurj⟩, fun _ _ => rfl⟩

end P103.Ch08.SplitFourierTransform
