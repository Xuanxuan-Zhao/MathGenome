import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.CompositionMultiplicities
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.FiniteLength

namespace RepTheorySurvey.Modular.CompositionMultiplicity

open scoped BigOperators
open Submodule

variable {F G : Type*} [Field F] [Group G]
local notation "A" => GroupAlgebra F G

variable {M N L S T : Type*}
variable [AddCommGroup M] [Module (GroupAlgebra F G) M]
  [AddCommGroup N] [Module (GroupAlgebra F G) N]
  [AddCommGroup L] [Module (GroupAlgebra F G) L]
  [AddCommGroup S] [Module (GroupAlgebra F G) S]
  [AddCommGroup T] [Module (GroupAlgebra F G) T]

variable (F G) in
noncomputable def factorCount (s : CompositionSeries (Submodule A M)) (S : Type*)
    [AddCommGroup S] [Module A S] : ℕ :=
  Spec.factorCount F G s S

variable (F G) in
/-- The composition multiplicity `[M:S]` for modules over the actual group algebra. -/
noncomputable def multiplicity (M S : Type*) [AddCommGroup M] [Module A M]
    [AddCommGroup S] [Module A S] : ℕ :=
  Spec.multiplicity F G M S

/-- A compatible ground-field action gives the same finite-dimensionality condition
as restriction along the coefficient map. -/
theorem groundFinite_iff [ground : Module F M] [IsScalarTower F A M] :
    GroundFinite F G M ↔ Module.Finite F M := by
  have actions : Module.compHom M (algebraMap F A) = ground :=
    Module.ext (funext₂ fun r x => IsScalarTower.algebraMap_smul A r x)
  change @Module.Finite F M _ _ (Module.compHom M (algebraMap F A)) ↔ _
  rw [actions]

theorem groundFinite_of_injective [hN : GroundFinite F G N] (f : M →ₗ[A] N)
    (hf : Function.Injective f) : GroundFinite F G M := by
  let _ : Module F M := Module.compHom M (algebraMap F A)
  let _ : Module F N := Module.compHom N (algebraMap F A)
  let _ : IsScalarTower F A M := IsScalarTower.of_compHom F A M
  let _ : IsScalarTower F A N := IsScalarTower.of_compHom F A N
  let _ : Module.Finite F N := hN
  exact Module.Finite.of_injective (f.restrictScalars F) hf

theorem groundFinite_of_surjective [hM : GroundFinite F G M] (f : M →ₗ[A] N)
    (hf : Function.Surjective f) : GroundFinite F G N := by
  let _ : Module F M := Module.compHom M (algebraMap F A)
  let _ : Module F N := Module.compHom N (algebraMap F A)
  let _ : IsScalarTower F A M := IsScalarTower.of_compHom F A M
  let _ : IsScalarTower F A N := IsScalarTower.of_compHom F A N
  let _ : Module.Finite F M := hM
  exact Module.Finite.of_surjective (f.restrictScalars F) hf

theorem groundFinite_groupAlgebra [Finite G] : GroundFinite F G A :=
  groundFinite_iff.mpr (Module.Finite.of_basis (MonoidAlgebra.basis G F))

private theorem exists_surjective_regular_of_simple [IsSimpleModule A S] :
    ∃ f : A →ₗ[A] S, Function.Surjective f := by
  have hS := isSimpleModule_iff_toSpanSingleton_surjective.mp (inferInstance : IsSimpleModule A S)
  let _ : Nontrivial S := hS.1
  obtain ⟨x, hx⟩ := exists_ne (0 : S)
  exact ⟨LinearMap.toSpanSingleton A S x, hS.2 x hx⟩

theorem groundFinite_of_simple [Finite G] [IsSimpleModule A S] : GroundFinite F G S := by
  obtain ⟨f, hf⟩ := exists_surjective_regular_of_simple (F := F) (G := G) (S := S)
  let _ : GroundFinite F G A := groundFinite_groupAlgebra
  exact groundFinite_of_surjective f hf

/-- Dimension increases strictly along inclusions, and the remaining dimension decreases
strictly. Thus the submodule lattice admits a bottom-to-top series of covers. -/
theorem exists_completeSeries (M : Type*) [AddCommGroup M] [Module A M]
    [hM : GroundFinite F G M] : Nonempty (CompleteSeries (F := F) (G := G) M) := by
  let _ : Module F M := Module.compHom M (algebraMap F A)
  let _ : IsScalarTower F A M := IsScalarTower.of_compHom F A M
  let _ : Module.Finite F M := hM
  let restrict := Submodule.restrictScalarsEmbedding F A M
  have rankMono : StrictMono (fun p : Submodule A M => Module.finrank F (restrict p)) :=
    Submodule.finrank_strictMono.comp restrict.strictMono
  have remainingAnti :
      StrictAnti (fun p : Submodule A M => Module.finrank F M - Module.finrank F (restrict p)) :=
    fun p q hpq => Nat.sub_lt_sub_left ((rankMono hpq).trans_le (restrict q).finrank_le)
      (rankMono hpq)
  let _ : WellFoundedLT (Submodule A M) := rankMono.wellFoundedLT
  let _ : WellFoundedGT (Submodule A M) := remainingAnti.wellFoundedGT
  obtain ⟨chain, hfirst, n, hlast, hstep⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (Submodule A M)
  exact ⟨⟨⟨n, fun i => chain i, fun i => hstep i i.isLt⟩, hfirst.eq_bot, hlast.eq_top⟩⟩

theorem factor_simple (s : CompositionSeries (Submodule A M)) (i : Fin s.length) :
    IsSimpleModule A (Factor s i) :=
  (covBy_iff_quot_is_simple (s.lt_succ i).le).mp (s.step i)

private theorem isomorphic_iff_of_equiv (e : M ≃ₗ[A] N) (d : S ≃ₗ[A] T) :
    Isomorphic (F := F) (G := G) M S ↔ Isomorphic (F := F) (G := G) N T := by
  constructor
  · rintro ⟨f⟩
    exact ⟨(e.symm.trans f).trans d⟩
  · rintro ⟨f⟩
    exact ⟨(e.trans f).trans d.symm⟩

private theorem factorCount_congr
    {s : CompositionSeries (Submodule A M)} {t : CompositionSeries (Submodule A N)}
    (e : Fin s.length ≃ Fin t.length) (h : ∀ i, Factor s i ≃ₗ[A] Factor t (e i))
    (d : S ≃ₗ[A] T) : factorCount F G s S = factorCount F G t T := by
  classical
  unfold factorCount Spec.factorCount
  refine Finset.sum_equiv e (fun _ => by simp) fun i _ => ?_
  simp only [isomorphic_iff_of_equiv (h i) d]

theorem multiplicity_eq_count (s : CompleteSeries (F := F) (G := G) M) :
    multiplicity F G M S = factorCount F G s.1 S := by
  let counts : Set ℕ := {n | ∃ t : CompleteSeries (F := F) (G := G) M,
    Spec.factorCount F G t.1 S = n}
  change sInf counts = _
  have realized : sInf counts ∈ counts := Nat.sInf_mem ⟨_, s, rfl⟩
  obtain ⟨t, ht⟩ := realized
  have hj := CompositionSeries.jordan_holder t.1 s.1
    (t.2.1.trans s.2.1.symm) (t.2.2.trans s.2.2.symm)
  obtain ⟨e, he⟩ := hj
  exact ht.symm.trans (factorCount_congr e (fun i => (he i).linearEquiv) (LinearEquiv.refl A S))

private noncomputable def quotientComapEquiv (f : M →ₗ[A] N)
    (hf : Function.Surjective f) (p : Submodule A N) :
    (M ⧸ p.comap f) ≃ₗ[A] (N ⧸ p) :=
  (Submodule.quotEquivOfEq _ _ (show p.comap f = LinearMap.ker (p.mkQ.comp f) by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
    ((p.mkQ.comp f).quotKerEquivOfSurjective (p.mkQ_surjective.comp hf))

private noncomputable def subquotientMapEquiv (f : M →ₗ[A] N)
    (hf : Function.Injective f) (p q : Submodule A M) :
    Subquotient p q ≃ₗ[A] Subquotient (p.map f) (q.map f) := by
  let e := q.equivMapOfInjective f hf
  refine (Submodule.quotEquivOfEq _ _
    (show p.comap q.subtype = ((p.map f).comap (q.map f).subtype).comap e.toLinearMap from ?_)).trans
    (quotientComapEquiv e.toLinearMap e.surjective _)
  ext x
  change (x : M) ∈ p ↔ f (x : M) ∈ p.map f
  exact (show f (x : M) ∈ p.map f ↔ (x : M) ∈ p from
    SetLike.ext_iff.mp (Submodule.comap_map_eq_of_injective hf p) (x : M)).symm

private noncomputable def subquotientComapEquiv (f : M →ₗ[A] N)
    (hf : Function.Surjective f) (p q : Submodule A N) :
    Subquotient (p.comap f) (q.comap f) ≃ₗ[A] Subquotient p q := by
  let g : q.comap f →ₗ[A] q := f.restrict (fun _ hx => hx)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    have hxq : f x ∈ q := hx.symm ▸ y.property
    exact ⟨⟨x, hxq⟩, Subtype.ext hx⟩
  exact quotientComapEquiv g hg (p.comap q.subtype)

private noncomputable def mapSeries (f : M →ₗ[A] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule A M)) : CompositionSeries (Submodule A N) :=
  s.map ⟨Submodule.map f, Submodule.map_covBy_of_injective hf⟩

private noncomputable def comapSeries (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule A N)) : CompositionSeries (Submodule A M) :=
  s.map ⟨Submodule.comap f, Submodule.comap_covBy_of_surjective hf⟩

theorem multiplicity_congr [GroundFinite F G M] (e : M ≃ₗ[A] N) (d : S ≃ₗ[A] T) :
    multiplicity F G M S = multiplicity F G N T := by
  obtain ⟨s⟩ := exists_completeSeries (F := F) (G := G) M
  let t : CompleteSeries (F := F) (G := G) N :=
    ⟨mapSeries e.toLinearMap e.injective s.1,
      by simp [mapSeries, s.2.1],
      by simp [mapSeries, s.2.2, LinearMap.range_eq_top.mpr e.surjective]⟩
  rw [multiplicity_eq_count s, multiplicity_eq_count t]
  exact factorCount_congr (Equiv.refl _) (fun i => subquotientMapEquiv _ e.injective _ _) d

private theorem factorCount_smash {s t : CompositionSeries (Submodule A M)}
    (h : s.last = t.head) :
    factorCount F G (s.smash t h) S = factorCount F G s S + factorCount F G t S := by
  classical
  unfold factorCount Spec.factorCount
  let count (p q : Submodule A M) : ℕ :=
    if Isomorphic (F := F) (G := G) (Subquotient p q) S then 1 else 0
  let term (j : Fin (s.length + t.length)) : ℕ :=
    count (s.smash t h j.castSucc) (s.smash t h j.succ)
  change ∑ j, term j = _
  rw [Fin.sum_univ_add term]
  congr 1
  · exact Finset.sum_congr rfl fun j _ =>
      congrArg₂ count (RelSeries.smash_castAdd h j) (RelSeries.smash_succ_castAdd h j)
  · exact Finset.sum_congr rfl fun j _ =>
      congrArg₂ count (RelSeries.smash_natAdd h j) (RelSeries.smash_succ_natAdd h j)

/-- Push the series of the submodule forward and pull the series of the quotient back.
They meet at the common image and kernel and retain their successive quotients. -/
theorem multiplicity_exact [GroundFinite F G L] [GroundFinite F G N]
    (f : L →ₗ[A] M) (g : M →ₗ[A] N) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) :
    multiplicity F G M S = multiplicity F G L S + multiplicity F G N S := by
  obtain ⟨s⟩ := exists_completeSeries (F := F) (G := G) L
  obtain ⟨t⟩ := exists_completeSeries (F := F) (G := G) N
  let left := mapSeries f hf s.1
  let right := comapSeries g hg t.1
  have joinEnds : left.last = right.head := by
    change Submodule.map f s.1.last = Submodule.comap g t.1.head
    rw [s.2.2, t.2.1, Submodule.map_top, Submodule.comap_bot, LinearMap.exact_iff.mp hex]
  let r : CompleteSeries (F := F) (G := G) M :=
    ⟨left.smash right joinEnds,
      by simp [left, mapSeries, s.2.1],
      by simp [right, comapSeries, t.2.2]⟩
  rw [multiplicity_eq_count r, multiplicity_eq_count s, multiplicity_eq_count t]
  change factorCount F G (left.smash right joinEnds) S = _
  rw [factorCount_smash]
  congr 1
  · exact factorCount_congr (Equiv.refl _) (fun i => (subquotientMapEquiv f hf _ _).symm)
      (LinearEquiv.refl A S)
  · exact factorCount_congr (Equiv.refl _) (fun i => subquotientComapEquiv g hg _ _)
      (LinearEquiv.refl A S)

theorem multiplicity_zero [Subsingleton M] : multiplicity F G M S = 0 := by
  let series : CompositionSeries (Submodule A M) := RelSeries.singleton _ ⊥
  have htop : (⊥ : Submodule A M) = ⊤ := by
    ext x
    simp [Subsingleton.elim x 0]
  let s : CompleteSeries (F := F) (G := G) M := ⟨series, rfl, htop⟩
  rw [multiplicity_eq_count s]
  simp [factorCount, Spec.factorCount, s, series]

theorem multiplicity_pos_iff (s : CompleteSeries (F := F) (G := G) M) :
    0 < multiplicity F G M S ↔ ∃ j : Fin s.1.length, Isomorphic (F := F) (G := G) (Factor s.1 j) S := by
  classical
  rw [multiplicity_eq_count s, factorCount, Spec.factorCount, Nat.pos_iff_ne_zero]
  let term (j : Fin s.1.length) : ℕ :=
    if Isomorphic (F := F) (G := G) (Factor s.1 j) S then 1 else 0
  change ¬ ((∑ j, term j) = 0) ↔ _
  rw [Finset.sum_eq_zero_iff (f := term)]
  simp [term]

open scoped IsSimpleOrder in
theorem multiplicity_of_simple [IsSimpleModule A M] :
    (Isomorphic (F := F) (G := G) M S → multiplicity F G M S = 1) ∧
    (¬ Isomorphic (F := F) (G := G) M S → multiplicity F G M S = 0) := by
  classical
  let series : CompositionSeries (Submodule A M) :=
    ⟨1, Fin.cases ⊥ (fun _ => ⊤), fun i => by
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact bot_covBy_top⟩
  let s : CompleteSeries (F := F) (G := G) M := ⟨series, rfl, rfl⟩
  let e : Factor s.1 0 ≃ₗ[A] M :=
    (Submodule.quotEquivOfEqBot _ (by
      change Submodule.comap (⊤ : Submodule A M).subtype ⊥ = ⊥
      rw [Submodule.comap_bot, Submodule.ker_subtype])).trans Submodule.topEquiv
  have hiso := isomorphic_iff_of_equiv e (LinearEquiv.refl A S)
  rw [multiplicity_eq_count s]
  have hcount : factorCount F G s.1 S =
      if Isomorphic (F := F) (G := G) (Factor s.1 0) S then 1 else 0 := by
    unfold factorCount Spec.factorCount
    exact Fin.sum_univ_one _
  rw [hcount]
  exact ⟨fun h => ite_eq_left (hiso.mpr h), fun h => ite_eq_right (mt hiso.mp h)⟩

private theorem regular_has_simple_factor [Finite G] [IsSimpleModule A S]
    (s : CompleteSeries (F := F) (G := G) A) :
    ∃ j : Fin s.1.length, Isomorphic (F := F) (G := G) (Factor s.1 j) S := by
  obtain ⟨g, hg⟩ := exists_surjective_regular_of_simple (F := F) (G := G) (S := S)
  let _ : GroundFinite F G A := groundFinite_groupAlgebra
  let _ : GroundFinite F G S := groundFinite_of_simple
  let _ : GroundFinite F G g.ker := groundFinite_of_injective g.ker.subtype g.ker.subtype_injective
  have hadd := multiplicity_exact (S := S) g.ker.subtype g g.ker.subtype_injective
    hg (LinearMap.exact_subtype_ker_map g)
  rw [(multiplicity_of_simple (M := S) (S := S)).1 ⟨LinearEquiv.refl A S⟩] at hadd
  exact (multiplicity_pos_iff (S := S) s).mp (by omega)

private def factorSetoid (s : CompositionSeries (Submodule A M)) : Setoid (Fin s.length) where
  r i j := Isomorphic (F := F) (G := G) (Factor s i) (Factor s j)
  iseqv :=
    ⟨fun _ => ⟨LinearEquiv.refl A _⟩, fun ⟨e⟩ => ⟨e.symm⟩,
      fun ⟨e⟩ ⟨d⟩ => ⟨e.trans d⟩⟩

section Representatives

universe u v
variable {E : Type u} {H : Type v} [Field E] [Group H] [Finite H]

/-- A finite group algebra has finitely many simple isomorphism classes. Representatives
can be chosen among the factors of a composition series of its left regular module. -/
theorem exists_simpleRepresentatives :
    ∃ (ι : Type) (_ : Fintype ι) (S : ι → Type (max u v)) (add : ∀ i, AddCommGroup (S i)),
      let _ := add
      ∃ mod : ∀ i, Module (GroupAlgebra E H) (S i),
        @SimpleRepresentatives E H _ _ ι S add mod := by
  classical
  let R := GroupAlgebra E H
  let _ : GroundFinite E H R := groundFinite_groupAlgebra
  obtain ⟨s⟩ := exists_completeSeries (F := E) (G := H) R
  let rel := factorSetoid s.1
  let ι := Quotient rel
  let _ : Finite ι := Finite.of_surjective (Quotient.mk rel) Quotient.mk_surjective
  let S (i : ι) := Factor s.1 i.out
  refine ⟨ι, Fintype.ofFinite ι, S, inferInstance, inferInstance, ?_⟩
  refine ⟨fun i => factor_simple s.1 i.out, ?_, ?_⟩
  · intro i j hij
    have hout : Quotient.mk rel i.out = Quotient.mk rel j.out := Quotient.sound hij
    exact i.out_eq.symm.trans (hout.trans j.out_eq)
  · intro T _ _ hT
    let _ : IsSimpleModule R T := hT
    obtain ⟨j, ⟨e⟩⟩ := regular_has_simple_factor (S := T) s
    let i : ι := Quotient.mk rel j
    have heq : Quotient.mk rel j = Quotient.mk rel i.out := i.out_eq.symm
    obtain ⟨d⟩ : Isomorphic (F := E) (G := H) (Factor s.1 j) (S i) := Quotient.exact heq
    exact ⟨i, ⟨e.symm.trans d⟩⟩

end Representatives

section Character

universe w

/-- For cancellative values, additivity on short exact sequences already forces
the value of a zero module to be zero. -/
noncomputable def AdditiveCharacter.ofExact {C : Type*} [AddCancelCommMonoid C]
    (value : ∀ (V : Type w), [AddCommGroup V] → [Module A V] → [GroundFinite F G V] → C)
    (law : ∀ {U V W : Type w}
      [AddCommGroup U] [Module A U] [GroundFinite F G U]
      [AddCommGroup V] [Module A V] [GroundFinite F G V]
      [AddCommGroup W] [Module A W] [GroundFinite F G W]
      (f : U →ₗ[A] V) (g : V →ₗ[A] W),
      Function.Injective f → Function.Surjective g → Function.Exact f g →
      value V = value U + value W) : AdditiveCharacter.{w} F G C where
  value := value
  zero V := by
    intro _ _ _ _
    let f : V →ₗ[A] V := 0
    have hexact : Function.Exact f f := by
      rw [LinearMap.exact_iff]
      ext x
      simp [f, Subsingleton.elim x 0]
    have h := law f f (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ => ⟨0, Subsingleton.elim _ _⟩) hexact
    exact (add_left_cancel ((add_zero (value V)).trans h)).symm
  exact := law

variable {C : Type*} [AddCommMonoid C]
variable (χ : AdditiveCharacter.{w} F G C)

theorem AdditiveCharacter.congr {V W : Type w} [AddCommGroup V] [Module A V] [GroundFinite F G V]
    [AddCommGroup W] [Module A W] [GroundFinite F G W] (e : V ≃ₗ[A] W) :
    χ.value V = χ.value W := by
  let _ : GroundFinite F G PUnit.{w + 1} := by
    let _ : Module F PUnit.{w + 1} := Module.compHom _ (algebraMap F A)
    change Module.Finite F PUnit.{w + 1}
    infer_instance
  let g : W →ₗ[A] PUnit.{w + 1} := 0
  have hexact : Function.Exact e.toLinearMap g := by
    rw [LinearMap.exact_iff, LinearMap.range_eq_top.mpr e.surjective]
    simp [g]
  have h := χ.exact e.toLinearMap g e.injective (fun y => ⟨0, Subsingleton.elim _ _⟩) hexact
  simpa only [χ.zero PUnit.{w + 1}, add_zero] using h.symm

variable {V : Type w} [AddCommGroup V] [Module (GroupAlgebra F G) V] [GroundFinite F G V]

private theorem groundFinite_submodule (p : Submodule A V) : GroundFinite F G p :=
  groundFinite_of_injective p.subtype p.subtype_injective

private theorem groundFinite_quotient (p : Submodule A V) : GroundFinite F G (V ⧸ p) :=
  groundFinite_of_surjective p.mkQ p.mkQ_surjective

attribute [local instance] groundFinite_submodule groundFinite_quotient

private theorem value_submodule_step {p q : Submodule A V} (hpq : p ≤ q) :
    χ.value q = χ.value p + χ.value (Subquotient p q) := by
  let lower := p.comap q.subtype
  exact (χ.exact lower.subtype lower.mkQ lower.subtype_injective lower.mkQ_surjective
    (LinearMap.exact_subtype_mkQ lower)).trans
    (congrArg (· + χ.value (Subquotient p q)) (χ.congr (V := ↥lower) (W := ↥p) (comapSubtypeEquivOfLe hpq)))

private theorem sum_of_successive_values {n : ℕ}
    (values : Fin (n + 1) → C) (terms : Fin n → C)
    (step : ∀ i : Fin n, values i.succ = values i.castSucc + terms i) :
    values (Fin.last n) = values 0 + ∑ i, terms i := by
  induction n with
  | zero => simp
  | succ n ih =>
    change values (Fin.last n).succ = _
    rw [step (Fin.last n), Fin.sum_univ_castSucc, ← add_assoc]
    congr 1
    exact ih (fun i => values i.castSucc) (fun i => terms i.castSucc) (fun i => by
      have hs : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
      rw [hs]
      exact step i.castSucc)

private theorem value_eq_factor_sum (s : CompleteSeries (F := F) (G := G) V) :
    χ.value V = ∑ j : Fin s.1.length, χ.value (Factor s.1 j) := by
  let valueOf (p : Submodule A V) : C := χ.value p
  have hfirst : valueOf s.1.head = 0 :=
    (congrArg valueOf s.2.1).trans (χ.zero (⊥ : Submodule A V))
  have hlast : valueOf s.1.last = χ.value V :=
    (congrArg valueOf s.2.2).trans (χ.congr Submodule.topEquiv)
  have hsum := sum_of_successive_values (fun i => valueOf (s.1 i))
    (fun i => χ.value (Factor s.1 i)) (fun i => value_submodule_step χ (s.1.lt_succ i).le)
  change valueOf s.1.last = valueOf s.1.head + _ at hsum
  simpa only [hfirst, hlast, zero_add] using hsum

/-- The value of a short-exact-additive character is the sum of the values on the
simple representatives, weighted by their composition multiplicities. -/
theorem character_eq_sum {ι : Type*} [Fintype ι] (V : Type w) [AddCommGroup V] [Module A V]
    [GroundFinite F G V] (S : ι → Type w) [∀ i, AddCommGroup (S i)]
    [∀ i, Module A (S i)] [∀ i, GroundFinite F G (S i)]
    (hS : SimpleRepresentatives (F := F) (G := G) S) :
    χ.value V = ∑ i, multiplicity F G V (S i) • χ.value (S i) := by
  classical
  obtain ⟨s⟩ := exists_completeSeries (F := F) (G := G) V
  rw [value_eq_factor_sum χ s]
  simp_rw [multiplicity_eq_count s, factorCount, Spec.factorCount, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨i, ⟨e⟩⟩ := hS.complete (Factor s.1 j) (factor_simple s.1 j)
  rw [Finset.sum_eq_single i]
  · simpa [show Isomorphic (F := F) (G := G) (Factor s.1 j) (S i) from ⟨e⟩] using χ.congr e
  · intro k _ hki
    have hnot : ¬ Isomorphic (F := F) (G := G) (Factor s.1 j) (S k) := by
      rintro ⟨f⟩
      exact hki (hS.distinct ⟨f.symm.trans e⟩)
    simp [hnot]
  · simp

end Character

end RepTheorySurvey.Modular.CompositionMultiplicity
