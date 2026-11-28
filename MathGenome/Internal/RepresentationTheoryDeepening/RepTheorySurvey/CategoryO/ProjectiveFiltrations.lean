import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.ProjectiveFiltrations
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.TruncatedProjectives
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.ComponentProjectors
import Batteries.Tactic.OpenPrivate

noncomputable section

open Module UniversalEnvelopingAlgebra
open scoped Classical ModuleCat.Algebra

namespace RepTheorySurvey.CategoryO.ProjectiveFiltrations

open Specs.RepTheorySurvey.CategoryO
open BorelInduction (U inclusion induceTensor)
open TruncatedProjectives
open Specs.RepTheorySurvey.CategoryO.ComponentProjectors
open scoped TensorProduct

open private weightMap_surjective tensor_unit_weight mem_initialWeights from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.TruncatedProjectives

universe u

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
variable (D : Setup g) {X Y : ModuleCat.{u} (U g)}

private theorem maps_weight (f : X →ₗ[U g] Y) {ν : D.Weight} {x : X}
    (h : x ∈ weightSpace_value D.cartan X ν) :
    f x ∈ weightSpace_value D.cartan Y ν := by
  apply (mem_weightSpace D.cartan Y ν (f x)).2
  intro t
  rw [← f.map_smul, (mem_weightSpace D.cartan X ν x).1 h t, f.map_smul_of_tower]

theorem map_weightGenerated_le (f : X →ₗ[U g] Y) (s : Finset D.Weight) :
    (weightGenerated D X s).map f ≤ weightGenerated D Y s := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro x ⟨ν, hν, hx⟩
  exact Submodule.subset_span ⟨ν, hν, maps_weight D f hx⟩

/-- A split projection carries a weight-generated submodule onto the one with the same
displayed weights in its target. -/
theorem map_weightGenerated_eq (p : X →ₗ[U g] Y) (j : Y →ₗ[U g] X)
    (hpj : p.comp j = LinearMap.id) (s : Finset D.Weight) :
    (weightGenerated D X s).map p = weightGenerated D Y s := by
  apply le_antisymm (map_weightGenerated_le D p s)
  apply Submodule.span_le.mpr
  rintro y ⟨ν, hν, hy⟩
  refine Submodule.mem_map.mpr ⟨j y, Submodule.subset_span ⟨ν, hν, maps_weight D j hy⟩, ?_⟩
  exact DFunLike.congr_fun hpj y

private theorem early_weight_mem {μ Λ : D.Weight} (F : GroupedFiltration D μ Λ)
    (i : Fin (F.length + 1)) (a : Fin F.length) (ha : a.val < i.val)
    {x : P D μ Λ} (hx : x ∈ weightSpace_value D.cartan (P D μ Λ) (F.weight a)) :
    x ∈ F.term i := by
  revert ha
  induction i using Fin.reverseInduction with
  | last =>
    intro _
    rw [F.last]
    exact Submodule.mem_top
  | cast j ih =>
    intro haj
    have hy : x ∈ F.term j.succ := ih (Nat.lt_succ_of_lt haj)
    let y : F.term j.succ := ⟨x, hy⟩
    let Qj := ModuleCat.of (U g) (Layer (F.term j.castSucc) (F.term j.succ))
    let q : F.term j.succ →ₗ[U g] Qj := ((F.term j.castSucc).comap (F.term j.succ).subtype).mkQ
    have hwy : y ∈ weightSpace_value D.cartan (ModuleCat.of (U g) (F.term j.succ))
        (F.weight a) := by
      apply (mem_weightSpace D.cartan _ _ _).2
      intro t
      apply Subtype.ext
      exact (mem_weightSpace D.cartan _ _ _).1 hx t
    have hwq := maps_weight D q hwy
    obtain ⟨f⟩ := F.factors j
    have hz : q y = 0 := by
      apply f.injective
      rw [map_zero]
      funext b
      change (f (q y)) b = 0
      let fb : Qj →ₗ[U g] verma_value D (F.weight j) :=
        (LinearMap.proj b).comp f.toLinearMap
      have hw := maps_weight D fb hwq
      by_contra hn
      have hs : F.weight a ∈ Specs.RepTheorySurvey.CategoryO.WeightBounds.support D
          (verma_value D (F.weight j)) := by
        intro hbot
        rw [hbot, Submodule.mem_bot] at hw
        exact hn hw
      have hle := ((verma_mem_O D (F.weight j)).2.2.2.2.1 (F.weight a)).mp hs
      have hja := F.higher_first a j hle (fun h => (Nat.ne_of_lt haj) (congrArg Fin.val h))
      exact (Nat.not_lt_of_ge (Nat.le_of_lt haj)) hja
    exact (Submodule.Quotient.mk_eq_zero ((F.term j.castSucc).comap (F.term j.succ).subtype)).mp hz

private theorem initialInduced_le_generated (μ Λ : D.Weight) (s : Finset D.Weight) :
    initialInduced D μ Λ s ≤ weightGenerated D (P D μ Λ) s := by
  let j : E D μ Λ →ₗ[ℂ] P D μ Λ :=
    ((BorelInduction.balance (inclusion D.borel) (E D μ Λ)).mkQ.restrictScalars ℂ).comp
      (TensorProduct.mk ℂ (U g) (E D μ Λ) 1)
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  have hle : initialSpace D μ Λ s ≤
      ((weightGenerated D (P D μ Λ) s).restrictScalars ℂ).comap j := by
    apply iSup_le
    intro ν y hy
    exact Submodule.subset_span ⟨ν.val, ν.property, tensor_unit_weight D y ν.val hy⟩
  exact hle hx

theorem generated : Expected.GeneratedType.{u} := by
  intro g _ _ _ D μ Λ h F i
  have hearly {ν : D.Weight} (hν : ν ∈ initialWeights D F.weight i) {x : P D μ Λ}
      (hx : x ∈ weightSpace_value D.cartan (P D μ Λ) ν) : x ∈ F.term i := by
    obtain ⟨a, ha, rfl⟩ := (mem_initialWeights D F.weight i ν).mp hν
    exact early_weight_mem D F i a ha hx
  refine ⟨le_antisymm ?_ (Submodule.span_le.mpr (by
    rintro x ⟨ν, hν, hx⟩
    exact hearly hν hx)), ?_⟩
  · rw [F.induced_initial]
    exact initialInduced_le_generated D μ Λ _
  · intro ν hν
    apply eq_bot_iff.mpr
    intro y hy
    let A := F.term i
    let Y := ModuleCat.of (U g) (P D μ Λ ⧸ A)
    let q : P D μ Λ →ₗ[U g] Y := A.mkQ
    obtain ⟨x, hx⟩ := weightMap_surjective D (inCutoff D μ Λ h).1.1.2.1 q
      A.mkQ_surjective ν ⟨y, hy⟩
    exact (congrArg Subtype.val hx).symm.trans
      ((Submodule.Quotient.mk_eq_zero A).mpr (hearly hν x.property))

private theorem component_projection_section {μ Λ : D.Weight}
    (h : weightLE_value D μ Λ)
    (hP : DirectSum.IsInternal (component D (P D μ Λ))) (k : Index D) :
    (projection D hP k).comp (component D (P D μ Λ) k).subtype = LinearMap.id :=
  (ComponentProjectors.projection_on_summands D ⟨P D μ Λ, (inCutoff D μ Λ h).1.1⟩ hP k).1

theorem componentFlag : Expected.ComponentType.{u} := by
  intro g _ _ _ D μ Λ h F hP k i
  let C := ModuleCat.of (U g) (component D (P D μ Λ) k)
  have hi : componentTerm D F hP k i = weightGenerated D
      (ModuleCat.of (U g) (component D (P D μ Λ) k)) (initialWeights D F.weight i) := by
    unfold componentTerm
    rw [(generated D μ Λ h F i).1]
    exact map_weightGenerated_eq D (X := P D μ Λ) (Y := C) _ _
      (component_projection_section D h hP k) _
  refine ⟨hi, fun f => ?_⟩
  rw [hi]
  exact Submodule.map_le_iff_le_comap.mp (map_weightGenerated_le D (X := C) (Y := C) f _)

section SplitLayers

variable {V W : Type u} [AddCommGroup V] [Module (U g) V]
  [AddCommGroup W] [Module (U g) W]

omit [FiniteDimensional ℂ g] in
/-- An invariant pair of terms inherits the splitting on its quotient. -/
private theorem split_layer (p : V →ₗ[U g] W) (j : W →ₗ[U g] V)
    (hs : ∀ x, p (j x) = x) (A B : Submodule (U g) V)
    (hA : ∀ x ∈ A, j (p x) ∈ A) (hB : ∀ x ∈ B, j (p x) ∈ B) :
    ∃ (pQ : Layer A B →ₗ[U g] Layer (A.map p) (B.map p))
      (jQ : Layer (A.map p) (B.map p) →ₗ[U g] Layer A B),
      ∀ x, pQ (jQ x) = x := by
  have hp (S : Submodule (U g) V) (x : V) (hx : x ∈ S) : p x ∈ S.map p :=
    Submodule.mem_map_of_mem hx
  have hj (S : Submodule (U g) V) (hS : ∀ x ∈ S, j (p x) ∈ S)
      (x : W) (hx : x ∈ S.map p) : j x ∈ S := by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact hS y hy
  let pB : B →ₗ[U g] B.map p := p.restrict (hp B)
  let jB : B.map p →ₗ[U g] B := j.restrict (hj B hB)
  let A₁ := A.comap B.subtype
  let A₂ := (A.map p).comap (B.map p).subtype
  let pQ := A₁.mapQ A₂ pB (fun x hx => hp A (x : V) hx)
  let jQ := A₂.mapQ A₁ jB (fun x hx => hj A hA (x : W) hx)
  refine ⟨pQ, jQ, ?_⟩
  intro x
  obtain ⟨y, rfl⟩ := A₂.mkQ_surjective x
  change A₂.mkQ (pB (jB y)) = A₂.mkQ y
  exact congrArg A₂.mkQ (Subtype.ext (hs y))

end SplitLayers

section Matrix

variable (V : ModuleCat.{u} (U g))

/-- Extend a scalar matrix to copies of a single enveloping module. -/
private def extendMatrix {m n : ℕ} (f : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    (Fin m → V) →ₗ[U g] (Fin n → V) :=
  LinearMap.lsum (U g) (fun _ : Fin m => V) ℂ fun i =>
    LinearMap.pi fun j => (f (Pi.single i 1) j) • (LinearMap.id : V →ₗ[U g] V)

omit [FiniteDimensional ℂ g] in
private theorem extendMatrix_single {m n : ℕ}
    (f : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (i : Fin m) (v : V) :
    extendMatrix V f (Pi.single i v) = fun j => f (Pi.single i 1) j • v := by
  rw [extendMatrix, LinearMap.lsum_piSingle]
  rfl

omit [FiniteDimensional ℂ g] in
private theorem extendMatrix_smul {m n : ℕ}
    (f : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (c : Fin m → ℂ) (v : V) :
    extendMatrix V f (fun i => c i • v) = fun j => f c j • v := by
  let J (k : ℕ) : (Fin k → ℂ) →ₗ[ℂ] (Fin k → V) :=
    LinearMap.pi fun i => ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight v).comp (LinearMap.proj i)
  have he : ((extendMatrix V f).restrictScalars ℂ).comp (J m) = (J n).comp f := by
    apply LinearMap.pi_ext
    intro i z
    have hz (k : ℕ) (a : Fin k) :
        J k (Pi.single a z) = Pi.single a (z • v) := by
      funext b
      by_cases h : b = a
      · subst b
        simp [J]
      · simp [J, Pi.single_eq_of_ne h]
    change extendMatrix V f (J m (Pi.single i z)) = J n (f (Pi.single i z))
    rw [hz, extendMatrix_single]
    have hi : Pi.single i z = z • Pi.single i (1 : ℂ) := by
      funext j
      by_cases h : j = i
      · subst j
        simp
      · simp [Pi.single_eq_of_ne h]
    rw [hi, f.map_smul]
    funext j
    change f (Pi.single i 1) j • (z • v) = (z * f (Pi.single i 1) j) • v
    rw [smul_smul, mul_comm]
  exact DFunLike.congr_fun he c

omit [FiniteDimensional ℂ g] in
private theorem extendMatrix_comp {l m n : ℕ}
    (f : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (q : (Fin l → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    extendMatrix V (f.comp q) = (extendMatrix V f).comp (extendMatrix V q) := by
  apply LinearMap.pi_ext
  intro i v
  rw [LinearMap.comp_apply, extendMatrix_single, extendMatrix_single, extendMatrix_smul]
  rfl

omit [FiniteDimensional ℂ g] in
private theorem extendMatrix_id (n : ℕ) :
    extendMatrix V (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = LinearMap.id := by
  apply LinearMap.pi_ext
  intro i v
  rw [extendMatrix_single]
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne h]

end Matrix

private theorem verma_matrix (ν : D.Weight) {n : ℕ}
    (f : (Fin n → verma_value D ν) →ₗ[U g] (Fin n → verma_value D ν)) :
    ∃ A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ), extendMatrix (verma_value D ν) A = f := by
  let V := verma_value D ν
  let w : V := Specs.LieAlgebrasAndRepresentations.VermaModules.highestVector_value
    D.cartan D.direction (character_value D ν)
  have htop := (verma_mem_O D ν).2.2.2.2.2
  have hw : w ∈ weightSpace_value D.cartan V ν := by
    rw [htop]
    exact Submodule.mem_span_singleton_self w
  have hcoeff (i j : Fin n) : ∃ c : ℂ, c • w = f (Pi.single i w) j := by
    let fji : V →ₗ[U g] V :=
      (LinearMap.proj j).comp (f.comp (LinearMap.single (U g) (fun _ : Fin n => V) i))
    have hwt := maps_weight D (X := V) (Y := V) fji hw
    rw [htop] at hwt
    exact Submodule.mem_span_singleton.mp hwt
  choose c hc using hcoeff
  let A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    LinearMap.lsum ℂ (fun _ : Fin n => ℂ) ℂ fun i =>
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (c i)
  refine ⟨A, LinearMap.pi_ext ?_⟩
  intro i v
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff (U g) w).mp
    (verma_mem_O D ν).2.2.1 v
  have hs : Pi.single i (a • w : V) = a • (Pi.single i w : Fin n → V) :=
    (LinearMap.single (U g) (fun _ : Fin n => V) i).map_smul a w
  rw [hs, map_smul, map_smul, extendMatrix_single]
  congr 1
  funext j
  have hA : A (Pi.single i 1) = c i := by
    dsimp only [A]
    rw [LinearMap.lsum_piSingle]
    simp
  rw [hA]
  exact hc i j


section Range

variable {R : Type*} [Ring R] {V W T : Type*}
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] [AddCommGroup T] [Module R T]

private theorem range_section (e : V →ₗ[R] V) (he : e.comp e = e) :
    e.rangeRestrict.comp e.range.subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, hy⟩ := x.property
  apply Subtype.ext
  change e (x : V) = (x : V)
  rw [← hy]
  exact DFunLike.congr_fun he y

private def equivOfSplittings (p : V →ₗ[R] W) (j : W →ₗ[R] V)
    (q : V →ₗ[R] T) (k : T →ₗ[R] V)
    (hp : p.comp j = LinearMap.id) (hq : q.comp k = LinearMap.id)
    (he : j.comp p = k.comp q) : W ≃ₗ[R] T :=
  LinearEquiv.ofLinearMap (q.comp j) (p.comp k)
    (by
      apply LinearMap.ext
      intro x
      change q (j (p (k x))) = x
      rw [show j (p (k x)) = k (q (k x)) from DFunLike.congr_fun he (k x),
        show q (k x) = x from DFunLike.congr_fun hq x]
      exact DFunLike.congr_fun hq x)
    (by
      apply LinearMap.ext
      intro x
      change p (k (q (j x))) = x
      rw [show k (q (j x)) = j (p (j x)) from (DFunLike.congr_fun he (j x)).symm,
        show p (j x) = x from DFunLike.congr_fun hp x]
      exact DFunLike.congr_fun hp x)

end Range

private theorem verma_retract (ν : D.Weight) {n : ℕ} {W : Type u}
    [AddCommGroup W] [Module (U g) W]
    (p : (Fin n → verma_value D ν) →ₗ[U g] W)
    (j : W →ₗ[U g] (Fin n → verma_value D ν))
    (h : p.comp j = LinearMap.id) :
    ∃ r : ℕ, Nonempty (W ≃ₗ[U g] (Fin r → verma_value D ν)) := by
  let V := verma_value D ν
  let w : V := Specs.LieAlgebrasAndRepresentations.VermaModules.highestVector_value
    D.cartan D.direction (character_value D ν)
  obtain ⟨A, hA⟩ := verma_matrix D ν (j.comp p)
  have h₀ : (j.comp p).comp (j.comp p) = j.comp p := by
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc p j, h, LinearMap.id_comp]
  have hAA : A.comp A = A := by
    have he : extendMatrix V (A.comp A) = extendMatrix V A := by
      rw [extendMatrix_comp, hA, h₀]
    apply LinearMap.ext
    intro c
    funext i
    have hc := DFunLike.congr_fun he (fun i => c i • w)
    rw [extendMatrix_smul, extendMatrix_smul] at hc
    exact smul_left_injective ℂ (show w ≠ 0 from (verma_mem_O D ν).2.1)
      (congrFun hc i)
  let r := finrank ℂ A.range
  let b : A.range ≃ₗ[ℂ] (Fin r → ℂ) := (Module.finBasis ℂ A.range).equivFun
  let q := b.toLinearMap.comp A.rangeRestrict
  let k := A.range.subtype.comp b.symm.toLinearMap
  have hq : q.comp k = LinearMap.id := by
    apply LinearMap.ext
    intro c
    funext i
    change b (A.rangeRestrict (b.symm c : Fin n → ℂ)) i = c i
    rw [show A.rangeRestrict (b.symm c : Fin n → ℂ) = b.symm c from
      DFunLike.congr_fun (range_section A hAA) (b.symm c), b.apply_symm_apply]
  have hk : k.comp q = A := by
    apply LinearMap.ext
    intro c
    funext i
    change ((b.symm (b (A.rangeRestrict c))) : Fin n → ℂ) i = A c i
    rw [b.symm_apply_apply]
    rfl
  refine ⟨r, ⟨equivOfSplittings p j (extendMatrix V q) (extendMatrix V k) h ?_ ?_⟩⟩
  · rw [← extendMatrix_comp, hq, extendMatrix_id]
  · rw [← extendMatrix_comp, hk, hA]


section Refinement

variable {V : Type u} [AddCommGroup V] [Module (U g) V]

private theorem append_flag {l m : List D.Weight} {A B C : Submodule (U g) V}
    (h : VermaFlag D l A B) (h' : VermaFlag D m B C) :
    VermaFlag D (l ++ m) A C := by
  induction h with
  | nil => exact h'
  | cons hAB hQ _ ih => exact .cons hAB hQ (ih h')

private theorem assemble_flag {n : ℕ} (S : Fin (n + 1) → Submodule (U g) V)
    (l : Fin n → List D.Weight)
    (h : ∀ i, VermaFlag D (l i) (S i.castSucc) (S i.succ)) :
    VermaFlag D (List.ofFn l).flatten (S 0) (S (Fin.last n)) := by
  induction n with
  | zero =>
    simpa using VermaFlag.nil (D := D) (S 0)
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    exact append_flag D (h 0) (ih (fun i => S i.succ) (fun i => l i.succ) (fun i => h i.succ))

private theorem layer_refinement (ν : D.Weight) {A B : Submodule (U g) V} (hAB : A ≤ B)
    {r : ℕ} (f : Layer A B ≃ₗ[U g] (Fin r → verma_value D ν)) :
    (r = 0 ↔ A = B) ∧ VermaFlag D (List.replicate r ν) A B := by
  let q : B →ₗ[U g] (Fin r → verma_value D ν) := f.toLinearMap.comp (A.comap B.subtype).mkQ
  have hq : Function.Surjective q := f.surjective.comp (A.comap B.subtype).mkQ_surjective
  have hker (x : B) : q x = 0 ↔ x.val ∈ A := by
    change f ((A.comap B.subtype).mkQ x) = 0 ↔ _
    rw [← f.map_zero, f.injective.eq_iff]
    exact Submodule.Quotient.mk_eq_zero _
  have hzero : r = 0 ↔ A = B := by
    constructor
    · rintro rfl
      exact le_antisymm hAB (fun x hx => (hker ⟨x, hx⟩).mp (Subsingleton.elim _ _))
    · intro h
      by_contra hr
      let i : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
      let w : verma_value D ν := Specs.LieAlgebrasAndRepresentations.VermaModules.highestVector_value
        D.cartan D.direction (character_value D ν)
      obtain ⟨x, hx⟩ := hq (Pi.single i w)
      have hqx := (hker x).mpr (h ▸ x.property)
      rw [hx] at hqx
      exact (verma_mem_O D ν).2.1 (by simpa using congrFun hqx i)
  refine ⟨hzero, ?_⟩
  let T (i : Fin (r + 1)) : Submodule (U g) B :=
    ⨅ j : {j : Fin r // i.val ≤ j.val}, LinearMap.ker ((LinearMap.proj j.val).comp q)
  let C (i : Fin (r + 1)) : Submodule (U g) V := (T i).map B.subtype
  have hC (i : Fin (r + 1)) (x : B) :
      x.val ∈ C i ↔ ∀ j : Fin r, i.val ≤ j.val → q x j = 0 := by
    rw [show x.val ∈ C i ↔ x ∈ T i from B.injective_subtype.mem_set_image]
    simp only [T, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.proj_apply]
    exact ⟨fun h j hj => h ⟨j, hj⟩, fun h j => h j.val j.property⟩
  have hCB (i : Fin (r + 1)) : C i ≤ B := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hmono : Monotone C := by
    intro i j hij x hx
    exact (hC j ⟨x, hCB i hx⟩).mpr (fun k hk => (hC i ⟨x, hCB i hx⟩).mp hx k (Nat.le_trans hij hk))
  have hfirst : C 0 = A := by
    apply le_antisymm
    · intro x hx
      apply (hker ⟨x, hCB 0 hx⟩).mp
      funext j
      exact (hC 0 ⟨x, hCB 0 hx⟩).mp hx j (Nat.zero_le _)
    · intro x hx
      apply (hC 0 ⟨x, hAB hx⟩).mpr
      intro j _
      exact congrFun ((hker ⟨x, hAB hx⟩).mpr hx) j
  have hlast : C (Fin.last r) = B := by
    refine le_antisymm (hCB _) ?_
    intro x hx
    apply (hC _ ⟨x, hx⟩).mpr
    intro j hj
    exact (Nat.not_le_of_lt j.isLt hj).elim
  have hstep (i : Fin r) : Nonempty (Layer (C i.castSucc) (C i.succ) ≃ₗ[U g] verma_value D ν) := by
    let k : C i.succ →ₗ[U g] B := (C i.succ).subtype.codRestrict B (fun x => hCB _ x.property)
    let fᵢ : C i.succ →ₗ[U g] verma_value D ν := (LinearMap.proj i).comp (q.comp k)
    have hkeri : (C i.castSucc).comap (C i.succ).subtype = fᵢ.ker := by
      ext x
      change x.val ∈ C i.castSucc ↔ q (k x) i = 0
      rw [show x.val = (k x : V) from rfl, hC]
      constructor
      · exact fun h => h i (Nat.le_refl _)
      · intro h j hj
        by_cases he : j = i
        · simpa [he] using h
        · apply (hC i.succ (k x)).mp x.property
          have hne : i.val ≠ j.val := fun hn => he (Fin.ext hn.symm)
          exact Nat.lt_of_le_of_ne hj hne
    have hfi : Function.Surjective fᵢ := by
      intro y
      obtain ⟨b, hb⟩ := hq (Pi.single i y)
      have hmem : b.val ∈ C i.succ := by
        apply (hC i.succ b).mpr
        intro j hj
        have hne : j ≠ i := fun he => (Nat.not_succ_le_self i.val) (he ▸ hj)
        rw [hb, Pi.single_eq_of_ne hne]
      refine ⟨⟨b.val, hmem⟩, ?_⟩
      change q b i = y
      rw [hb, Pi.single_eq_same]
    exact ⟨(Submodule.quotEquivOfEq _ _ hkeri).trans (fᵢ.quotKerEquivOfSurjective hfi)⟩
  have hflag (i : Fin (r + 1)) :
      VermaFlag D (List.replicate (r - i.val) ν) (C i) (C (Fin.last r)) := by
    induction i using Fin.reverseInduction with
    | last => simpa using VermaFlag.nil (D := D) (C (Fin.last r))
    | cast i ih =>
      have hs : r - i.castSucc.val = (r - i.succ.val) + 1 := by
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega
      rw [hs, List.replicate_succ]
      exact .cons (hmono Fin.castSucc_lt_succ.le) (hstep i) ih
  simpa only [hfirst, hlast, Fin.val_zero, Nat.sub_zero] using hflag 0

end Refinement


theorem summandFlag : Expected.SummandType.{u} := by
  intro g _ _ _ D μ Λ h F hP k e he
  let C := component D (P D μ Λ) k
  let p : P D μ Λ →ₗ[U g] e.range := e.rangeRestrict.comp (projection D hP k)
  let j : e.range →ₗ[U g] P D μ Λ := C.subtype.comp e.range.subtype
  have hpj : p.comp j = LinearMap.id := by
    apply LinearMap.ext
    intro y
    change e.rangeRestrict (projection D hP k (C.subtype (e.range.subtype y))) = y
    rw [show projection D hP k (C.subtype (e.range.subtype y)) = e.range.subtype y from
      DFunLike.congr_fun (component_projection_section D h hP k) (e.range.subtype y)]
    exact DFunLike.congr_fun (range_section e he) y
  let S := summandTerm D F hP k e
  have hS (i : Fin (F.length + 1)) : S i = (F.term i).map p := by
    exact (Submodule.map_comp _ _ _).symm
  have hm : Monotone S := by
    intro i l hil
    rw [hS, hS]
    exact Submodule.map_mono (F.monotone hil)
  have hfirst : S 0 = ⊥ := by rw [hS, F.first, Submodule.map_bot]
  have hlast : S (Fin.last F.length) = ⊤ := by
    rw [hS, F.last, Submodule.map_top, LinearMap.range_eq_top]
    exact fun y => ⟨j y, DFunLike.congr_fun hpj y⟩
  have hpres (i : Fin (F.length + 1)) (x : P D μ Λ) (hx : x ∈ F.term i) :
      j (p x) ∈ F.term i := by
    have hle := Submodule.map_le_iff_le_comap.mp
      (map_weightGenerated_le D (X := P D μ Λ) (Y := P D μ Λ) (j.comp p)
        (initialWeights D F.weight i))
    rw [← (generated D μ Λ h F i).1] at hle
    exact hle hx
  have hfactor (i : Fin F.length) : ∃ r : ℕ,
      Nonempty (Layer (S i.castSucc) (S i.succ) ≃ₗ[U g] (Fin r → verma_value D (F.weight i))) := by
    rw [hS, hS]
    obtain ⟨a, b, hab⟩ := split_layer p j (DFunLike.congr_fun hpj) (F.term i.castSucc)
      (F.term i.succ) (hpres i.castSucc) (hpres i.succ)
    obtain ⟨f⟩ := F.factors i
    apply verma_retract D (F.weight i) (a.comp f.symm.toLinearMap) (f.toLinearMap.comp b)
    apply LinearMap.ext
    intro x
    change a (f.symm (f (b x))) = x
    rw [f.symm_apply_apply, hab]
  choose r hr using hfactor
  have href i := layer_refinement D (F.weight i) (hm Fin.castSucc_lt_succ.le) (hr i).some
  refine ⟨hm, hfirst, hlast, r, hr, fun i => (href i).1, fun i => (href i).2, ?_⟩
  rw [← hfirst, ← hlast]
  exact assemble_flag D S (fun i => List.replicate (r i) (F.weight i)) (fun i => (href i).2)

end RepTheorySurvey.CategoryO.ProjectiveFiltrations
