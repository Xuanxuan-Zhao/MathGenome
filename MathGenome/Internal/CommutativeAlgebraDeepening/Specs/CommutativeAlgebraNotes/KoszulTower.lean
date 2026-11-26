import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.AugmentedCechComplex
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DerivedCechComparison
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.BaseChange

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators TensorProduct
open MonoidalCategory

namespace Specs.CommutativeAlgebraNotes.KoszulTower

noncomputable section

universe u
variable {R : Type u} [CommRing R]

abbrev Coeff (R : Type u) [CommRing R] := ModuleCat.{u} R
abbrev Complex (R : Type u) [CommRing R] := CochainComplex (Coeff R) ℤ

/-- The selected positions of an ordered list in degree `q`. -/
abbrev Positions (r : ℕ) (q : ℤ) := {J : Finset (Fin r) // (J.card : ℤ) = q}

def insertPosition {r : ℕ} {q : ℤ} (J : Positions r q) (a : Fin r) (ha : a ∉ J.val) :
    Positions r (q + 1) :=
  ⟨insert a J.val, by rw [Finset.card_insert_of_notMem ha, Nat.cast_add, J.property]; rfl⟩

def countBefore {r : ℕ} (J : Finset (Fin r)) (a : Fin r) : ℤ :=
  (J.filter (· < a)).card

def positionProduct (rs : List R) {q : ℤ} (J : Positions rs.length q) : R :=
  ∏ j ∈ J.val, rs.get j

abbrev term (rs : List R) (M : Coeff R) (q : ℤ) : Coeff R :=
  ∐ (fun _ : Positions rs.length q => M)

/-- Multiplication by a scalar as an endomorphism of a coefficient module. -/
def scalar (M : Coeff R) (x : R) : M ⟶ M :=
  ModuleCat.ofHom (x • LinearMap.id)

private theorem scalar_comp {M : Coeff R} (x y : R) :
    scalar M x ≫ scalar M y = scalar M (x * y) := by
  ext m
  change y • (x • m) = (x * y) • m
  rw [smul_smul, mul_comm]

/-- Signed insertion into a single column of the differential. -/
def component (rs : List R) (M : Coeff R) (n : ℕ) {q : ℤ} (J : Positions rs.length q)
    (a : Fin rs.length) : M ⟶ term rs M (q + 1) :=
  if ha : a ∉ J.val then
    (countBefore J.val a).negOnePow •
      (scalar M (rs.get a ^ (n + 1)) ≫ Sigma.ι (fun _ : Positions rs.length (q + 1) => M) (insertPosition J a ha))
  else 0

def differential (rs : List R) (M : Coeff R) (n : ℕ) (q : ℤ) :
    term rs M q ⟶ term rs M (q + 1) :=
  Sigma.desc (fun J => ∑ a, component rs M n J a)

@[reassoc (attr := simp)]
theorem ι_differential (rs : List R) (M : Coeff R) (n : ℕ) (q : ℤ)
    (J : Positions rs.length q) :
    Sigma.ι (fun _ : Positions rs.length q => M) J ≫ differential rs M n q =
      ∑ a, component rs M n J a := Sigma.ι_comp_desc _ _

private theorem countBefore_insert {r : ℕ} (J : Finset (Fin r)) (a b : Fin r)
    (ha : a ∉ J) :
    countBefore (insert a J) b = countBefore J b + if a < b then 1 else 0 := by
  unfold countBefore
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1), Nat.cast_add]
    rfl
  · simp

private def doubleComponent (rs : List R) (M : Coeff R) (n : ℕ) {q : ℤ}
    (J : Positions rs.length q) (a b : Fin rs.length) : M ⟶ term rs M (q + 1 + 1) :=
  if ha : a ∉ J.val then
    (countBefore J.val a).negOnePow •
      (scalar M (rs.get a ^ (n + 1)) ≫ component rs M n (insertPosition J a ha) b)
  else 0

private theorem component_comp (rs : List R) (M : Coeff R) (n : ℕ) {q : ℤ}
    (J : Positions rs.length q) (a : Fin rs.length) :
    component rs M n J a ≫ differential rs M n (q + 1) =
      ∑ b, doubleComponent rs M n J a b := by
  by_cases ha : a ∉ J.val
  · rw [component, dite_eq_left ha]
    simp only [doubleComponent, dite_eq_left ha]
    rw [show ∀ (z : ℤˣ) (f : M ⟶ term rs M (q+1)) (g : term rs M (q+1) ⟶ term rs M (q+1+1)),
        (z • f) ≫ g = z • (f ≫ g) from fun z f g => Preadditive.zsmul_comp f g z,
      Category.assoc, ι_differential, Preadditive.comp_sum, Finset.smul_sum]
  · simp [component, doubleComponent, ha]

private theorem doubleComponent_self (rs : List R) (M : Coeff R) (n : ℕ) {q : ℤ}
    (J : Positions rs.length q) (a : Fin rs.length) :
    doubleComponent rs M n J a a = 0 := by
  by_cases ha : a ∉ J.val
  · have h : a ∈ (insertPosition J a ha).val := Finset.mem_insert_self _ _
    simp [doubleComponent, ha, component, h]
  · simp [doubleComponent, ha]

private theorem doubleComponent_swap (rs : List R) (M : Coeff R) (n : ℕ) {q : ℤ}
    (J : Positions rs.length q) (a b : Fin rs.length) :
    doubleComponent rs M n J a b + doubleComponent rs M n J b a = 0 := by
  by_cases hab : a = b
  · subst b
    simp [doubleComponent_self]
  by_cases ha : a ∈ J.val
  · by_cases hb : b ∈ J.val
    · simp [doubleComponent, ha, hb]
    · have h : a ∈ (insertPosition J b hb).val := Finset.mem_insert_of_mem ha
      simp [doubleComponent, ha, hb, component, h]
  by_cases hb : b ∈ J.val
  · have h : b ∈ (insertPosition J a ha).val := Finset.mem_insert_of_mem hb
    simp [doubleComponent, ha, hb, component, h]
  have hab' : b ∉ (insertPosition J a ha).val := by simp [insertPosition, Ne.symm hab, hb]
  have hba' : a ∉ (insertPosition J b hb).val := by simp [insertPosition, hab, ha]
  have hins : insertPosition (insertPosition J a ha) b hab' =
      insertPosition (insertPosition J b hb) a hba' :=
    Subtype.ext (Finset.insert_comm b a J.val)
  simp only [doubleComponent, dite_eq_left ha, dite_eq_left hb, component, dite_eq_left hab', dite_eq_left hba']
  have hcomp (f : M ⟶ M) (g : M ⟶ term rs M (q + 1 + 1)) (z : ℤˣ) :
      f ≫ (z • g) = z • (f ≫ g) := Preadditive.comp_zsmul f g z
  simp only [hcomp, ← Category.assoc, scalar_comp, smul_smul, ← Int.negOnePow_add, hins]
  rw [show (insertPosition J a ha).val = insert a J.val from rfl,
    show (insertPosition J b hb).val = insert b J.val from rfl,
    countBefore_insert _ _ _ ha, countBefore_insert _ _ _ hb]
  have hmul := mul_comm (rs.get a ^ (n+1)) (rs.get b ^ (n+1))
  rw [hmul]
  rcases lt_or_gt_of_ne hab with h | h
  · simp only [h, ite_true, not_lt_of_gt h, ite_false, add_zero]
    rw [← add_assoc, add_comm (countBefore J.val b) (countBefore J.val a),
      Int.negOnePow_succ, Units.neg_smul, neg_add_cancel]
  · simp only [h, ite_true, not_lt_of_gt h, ite_false, add_zero]
    rw [← add_assoc, add_comm (countBefore J.val b) (countBefore J.val a),
      Int.negOnePow_succ, Units.neg_smul, add_neg_cancel]

private theorem differential_square (rs : List R) (M : Coeff R) (n : ℕ) (q : ℤ) :
    differential rs M n q ≫ differential rs M n (q + 1) = 0 := by
  apply Sigma.hom_ext
  intro J
  rw [ι_differential_assoc, Limits.comp_zero, Preadditive.sum_comp]
  simp only [component_comp]
  rw [← Fintype.sum_prod_type' (doubleComponent rs M n J)]
  refine Finset.sum_ninvolution (fun ab => (ab.2, ab.1)) ?_ ?_ (fun _ => Finset.mem_univ _) ?_
  · rintro ⟨a,b⟩
    exact doubleComponent_swap rs M n J a b
  · rintro ⟨a,b⟩ h he
    have hab : a = b := congrArg Prod.fst he.symm
    subst b
    exact h (doubleComponent_self rs M n J a)
  · rintro ⟨a,b⟩
    rfl

/-- The cochain Koszul complex at positive exponent `n+1`. -/
def stage (rs : List R) (M : Coeff R) (n : ℕ) : Complex R :=
  CochainComplex.of (term rs M) (differential rs M n) (differential_square rs M n)

@[simp]
theorem stage_d (rs : List R) (M : Coeff R) (n : ℕ) (q : ℤ) :
    (stage rs M n).d q (q + 1) = differential rs M n q :=
  CochainComplex.of_d _ _ _


@[simp]
theorem positionProduct_insert (rs : List R) {q : ℤ} (J : Positions rs.length q)
    (a : Fin rs.length) (ha : a ∉ J.val) :
    positionProduct rs (insertPosition J a ha) = rs.get a * positionProduct rs J :=
  Finset.prod_insert ha

/-- The degree map of the tower from positive exponent `n+1` to `m+1`. -/
def transitionTerm (rs : List R) (M : Coeff R) (n m : ℕ) (q : ℤ) :
    term rs M q ⟶ term rs M q :=
  Sigma.desc (fun J : Positions rs.length q =>
    scalar M (positionProduct rs J ^ (m - n)) ≫ Sigma.ι (fun _ : Positions rs.length q => M) J)

@[reassoc (attr := simp)]
theorem ι_transitionTerm (rs : List R) (M : Coeff R) (n m : ℕ) (q : ℤ)
    (J : Positions rs.length q) :
    Sigma.ι (fun _ : Positions rs.length q => M) J ≫ transitionTerm rs M n m q =
      scalar M (positionProduct rs J ^ (m - n)) ≫ Sigma.ι (fun _ : Positions rs.length q => M) J :=
  Sigma.ι_comp_desc _ _

private theorem transition_comm (rs : List R) (M : Coeff R) {n m : ℕ} (h : n ≤ m) (q : ℤ) :
    transitionTerm rs M n m q ≫ differential rs M m q =
      differential rs M n q ≫ transitionTerm rs M n m (q + 1) := by
  apply Sigma.hom_ext
  intro J
  rw [ι_transitionTerm_assoc, ι_differential, ι_differential_assoc,
    Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∉ J.val
  · simp only [component, dite_eq_left ha]
    have hl (x : M ⟶ M) (g : M ⟶ term rs M (q+1)) (z : ℤˣ) :
        x ≫ (z • g) = z • (x ≫ g) := Preadditive.comp_zsmul x g z
    have hr (f : M ⟶ term rs M (q+1)) (g : term rs M (q+1) ⟶ term rs M (q+1)) (z : ℤˣ) :
        (z • f) ≫ g = z • (f ≫ g) := Preadditive.zsmul_comp f g z
    rw [hl, hr, Category.assoc, ι_transitionTerm, ← Category.assoc, ← Category.assoc,
      scalar_comp, scalar_comp, positionProduct_insert, mul_pow, ← mul_assoc, ← pow_add]
    rw [show n + 1 + (m - n) = m + 1 by omega, mul_comm]
  · simp [component, ha]

/-- The transition is multiplication by the selected product on adjacent stages. -/
def transition (rs : List R) (M : Coeff R) {n m : ℕ} (h : n ≤ m) :
    stage rs M n ⟶ stage rs M m where
  f := transitionTerm rs M n m
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    rw [stage_d, stage_d]
    exact transition_comm rs M h i

@[simp]
theorem scalar_one (M : Coeff R) : scalar M 1 = 𝟙 M := by
  apply ModuleCat.hom_ext
  simp [scalar]

/-- The positive-exponent Koszul tower, indexed by `n ↦ n+1`. -/
def tower (rs : List R) (M : Coeff R) : ℕ ⥤ Complex R where
  obj := stage rs M
  map f := transition rs M f.le
  map_id n := by
    apply HomologicalComplex.hom_ext
    intro q
    apply Sigma.hom_ext
    intro J
    change Sigma.ι (fun _ : Positions rs.length q => M) J ≫ transitionTerm rs M n n q = _
    change _ = Sigma.ι (fun _ : Positions rs.length q => M) J ≫ 𝟙 (term rs M q)
    simp
  map_comp {n m l} f g := by
    apply HomologicalComplex.hom_ext
    intro q
    apply Sigma.hom_ext
    intro J
    change Sigma.ι (fun _ : Positions rs.length q => M) J ≫ transitionTerm rs M n l q =
      Sigma.ι (fun _ : Positions rs.length q => M) J ≫
        transitionTerm rs M n m q ≫ transitionTerm rs M m l q
    rw [ι_transitionTerm, ι_transitionTerm_assoc, ι_transitionTerm, ← Category.assoc, scalar_comp, ← pow_add]
    have hf := f.le
    have hg := g.le
    rw [show m - n + (l - m) = l - n by omega]

/-- The submodule generated by all `fᵢ^(n+1) M`. -/
def powersSubmodule (rs : List R) (M : Coeff R) (n : ℕ) : Submodule R M :=
  Ideal.span (Set.range (fun a : Fin rs.length => rs.get a ^ (n + 1))) • ⊤

/-- The scalar in the top-degree transition. -/
def totalProduct (rs : List R) : R := ∏ a : Fin rs.length, rs.get a

abbrev QuotientTerm (rs : List R) (M : Coeff R) (n : ℕ) : Coeff R :=
  ModuleCat.of R (M ⧸ powersSubmodule rs M n)


/-- The power of the denominator used at a given stage. -/
def denominator (p : R) (n : ℕ) : Submonoid.powers p := ⟨p ^ n, ⟨n, rfl⟩⟩

/-- The stage map on a localization component, sending `x` to `x/p^(n+1)`. -/
def fraction (M : Coeff R) (p : R) (n : ℕ) :
    M ⟶ ModuleCat.of R (LocalizedModule.Away p M) :=
  ModuleCat.ofHom ((LocalizedModule.divBy (denominator p (n + 1))).comp
    (LocalizedModule.mkLinearMap (Submonoid.powers p) M))

@[simp]
theorem fraction_apply (M : Coeff R) (p : R) (n : ℕ) (x : M) :
    fraction M p n x = LocalizedModule.mk x (denominator p (n + 1)) := by
  change LocalizedModule.divBy _ (LocalizedModule.mk x 1) = _
  rw [LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]


open scoped Pointwise in
theorem powersSubmodule_eq_iSup (rs : List R) (M : Coeff R) (n : ℕ) :
    powersSubmodule rs M n = ⨆ a : Fin rs.length, (scalar M (rs.get a ^ (n+1))).hom.range := by
  rw [powersSubmodule, Ideal.span_range_eq_iSup, Submodule.iSup_smul]
  congr 1
  funext a
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  exact ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, trivial, hy⟩⟩

/-- The product is divisible by the generator at each position. -/
theorem generator_dvd_totalProduct (rs : List R) (a : Fin rs.length) :
    rs.get a ∣ totalProduct rs :=
  ⟨∏ j ∈ Finset.univ.erase a, rs.get j,
    (Finset.mul_prod_erase _ rs.get (Finset.mem_univ a)).symm⟩

private theorem transition_preserves (rs : List R) (M : Coeff R) {n m : ℕ} (h : n ≤ m) :
    powersSubmodule rs M n ≤ (powersSubmodule rs M m).comap
      (scalar M (totalProduct rs ^ (m-n))).hom := by
  rw [powersSubmodule_eq_iSup rs M n]
  apply iSup_le
  intro a x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨c, hc⟩ := generator_dvd_totalProduct rs a
  change totalProduct rs ^ (m-n) • (rs.get a ^ (n+1) • y) ∈ powersSubmodule rs M m
  rw [hc, mul_pow, mul_smul, smul_comm (c ^ (m-n)), smul_smul, ← pow_add,
    show m - n + (n + 1) = m + 1 by omega]
  rw [powersSubmodule_eq_iSup]
  exact Submodule.mem_iSup_of_mem a ⟨c ^ (m-n) • y, rfl⟩

/-- The quotient transition, induced by multiplication by the product to the gap power. -/
def quotientTransition (rs : List R) (M : Coeff R) {n m : ℕ} (h : n ≤ m) :
    QuotientTerm rs M n ⟶ QuotientTerm rs M m :=
  ModuleCat.ofHom ((powersSubmodule rs M n).mapQ (powersSubmodule rs M m)
    (scalar M (totalProduct rs ^ (m-n))).hom (transition_preserves rs M h))

def quotientProjection (rs : List R) (M : Coeff R) (n : ℕ) :
    M ⟶ QuotientTerm rs M n := ModuleCat.ofHom (powersSubmodule rs M n).mkQ

instance quotientProjection_epi (rs : List R) (M : Coeff R) (n : ℕ) :
    Epi (quotientProjection rs M n) :=
  (ModuleCat.epi_iff_range_eq_top _).mpr (Submodule.range_mkQ _)

@[reassoc (attr := simp)]
theorem quotientProjection_transition (rs : List R) (M : Coeff R) {n m : ℕ} (h : n ≤ m) :
    quotientProjection rs M n ≫ quotientTransition rs M h =
      scalar M (totalProduct rs ^ (m-n)) ≫ quotientProjection rs M m := rfl

/-- The actual diagram of successive quotients by the powers of the generators. -/
def quotientDiagram (rs : List R) (M : Coeff R) : ℕ ⥤ Coeff R where
  obj := QuotientTerm rs M
  map f := quotientTransition rs M f.le
  map_id n := by
    apply (cancel_epi (quotientProjection rs M n)).mp
    change quotientProjection rs M n ≫ quotientTransition rs M (le_refl n) =
      quotientProjection rs M n ≫ 𝟙 (QuotientTerm rs M n)
    simp
  map_comp {n m l} f g := by
    apply (cancel_epi (quotientProjection rs M n)).mp
    rw [quotientProjection_transition, quotientProjection_transition_assoc,
      quotientProjection_transition, ← Category.assoc, scalar_comp, ← pow_add]
    have hf := f.le
    have hg := g.le
    rw [show m-n + (l-m) = l-n by omega]

private theorem quotientMap_preserves (rs : List R) {M N : Coeff R} (f : M ⟶ N) (n : ℕ) :
    powersSubmodule rs M n ≤ (powersSubmodule rs N n).comap f.hom :=
  Submodule.smul_top_le_comap_smul_top _ _

def quotientMap (rs : List R) {M N : Coeff R} (f : M ⟶ N) (n : ℕ) :
    QuotientTerm rs M n ⟶ QuotientTerm rs N n :=
  ModuleCat.ofHom ((powersSubmodule rs M n).mapQ (powersSubmodule rs N n)
    f.hom (quotientMap_preserves rs f n))

@[reassoc (attr := simp)]
theorem quotientProjection_map (rs : List R) {M N : Coeff R} (f : M ⟶ N) (n : ℕ) :
    quotientProjection rs M n ≫ quotientMap rs f n = f ≫ quotientProjection rs N n := rfl

@[reassoc]
theorem scalar_naturality {M N : Coeff R} (f : M ⟶ N) (x : R) :
    scalar M x ≫ f = f ≫ scalar N x := by
  ext y
  exact f.hom.map_smul x y

def quotientDiagramMap (rs : List R) {M N : Coeff R} (f : M ⟶ N) :
    quotientDiagram rs M ⟶ quotientDiagram rs N where
  app := quotientMap rs f
  naturality {n m} g := by
    apply (cancel_epi (quotientProjection rs M n)).mp
    change quotientProjection rs M n ≫ quotientTransition rs M g.le ≫ quotientMap rs f m =
      quotientProjection rs M n ≫ quotientMap rs f n ≫ quotientTransition rs N g.le
    rw [quotientProjection_transition_assoc, quotientProjection_map, quotientProjection_map_assoc,
      quotientProjection_transition, scalar_naturality_assoc]

/-- The quotient colimit as a functor of the coefficients. -/
def quotientColimit (rs : List R) : Coeff R ⥤ Coeff R :=
  ({ obj := quotientDiagram rs
     map := quotientDiagramMap rs
     map_id M := by
       apply NatTrans.ext
       funext n
       apply (cancel_epi (quotientProjection rs M n)).mp
       change quotientProjection rs M n ≫ quotientMap rs (𝟙 M) n =
         quotientProjection rs M n ≫ 𝟙 (QuotientTerm rs M n)
       simp
     map_comp {M N P} f g := by
       apply NatTrans.ext
       funext n
       apply (cancel_epi (quotientProjection rs M n)).mp
       change quotientProjection rs M n ≫ quotientMap rs (f ≫ g) n =
         quotientProjection rs M n ≫ quotientMap rs f n ≫ quotientMap rs g n
       simp } : Coeff R ⥤ (ℕ ⥤ Coeff R)) ⋙ colim

/-- The local cohomology statement with its specified quotient diagram, natural in the module. -/
def TopComparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (rs : List R),
    Ideal.span {r | r ∈ rs} = I →
    Nonempty (Specs.CommutativeAlgebraNotes.IdealTorsion.localCohomology I (rs.length : ℤ) ≅
      quotientColimit rs)


abbrev ComplexType := ∀ {R : Type u} [CommRing R], List R → Coeff R → ℕ → Complex R
def complexValue : ComplexType.{u} := @stage

abbrev DiagramType := ∀ {R : Type u} [CommRing R], List R → Coeff R → (ℕ ⥤ Complex R)
def diagramValue : DiagramType.{u} := @tower

abbrev localizationTensorIso (M : Coeff R) (p : R) :
    ModuleCat.of R (LocalizedModule.Away p M) ≅ ModuleCat.of R (Localization.Away p) ⊗ M :=
  ((LocalizedModule.equivTensorProduct (Submonoid.powers p) M).restrictScalars R).toModuleIso

open AugmentedCechComplex (Selection selected product)

/-- The Čech colimit cocone has the specified fraction map on each ordered-subset summand. -/
def CechColimitComparison : Prop :=
  ∀ {R : Type u} [CommRing R] (rs : List R),
    ∃ (e : ∀ q, Selection rs.length q ≃ Positions rs.length q)
      (ι : ∀ q (s : Selection rs.length q), AugmentedCechComplex.term R rs s ⟶
        (AugmentedCechComplex.complex R rs).X q),
      (∀ q s, (e q s).val = Finset.univ.filter fun j => selected s j = true) ∧
      (∀ q s, product R rs s = positionProduct rs (e q s)) ∧
      (∀ q, Nonempty (IsColimit (Cofan.mk ((AugmentedCechComplex.complex R rs).X q) (ι q)))) ∧
      ∀ M : Coeff R,
        ∃ η : tower rs M ⟶ (Functor.const ℕ).obj (AugmentedCechComplex.coefficients R rs M),
          Nonempty (IsColimit (Cocone.mk (AugmentedCechComplex.coefficients R rs M) η)) ∧
          ∀ n q (s : Selection rs.length q),
            Sigma.ι (fun _ : Positions rs.length q => M) (e q s) ≫ (η.app n).f q =
              fraction M (product R rs s) n ≫
                (localizationTensorIso M (product R rs s)).hom ≫
                (ι q s ▷ M) ≫
                HomologicalComplex.ιTensorObj (AugmentedCechComplex.complex R rs)
                  ((HomologicalComplex.single (Coeff R) (.up ℤ) 0).obj M) q 0 q (add_zero q)

/-- The stage identifications respect the quotient transition maps. -/
def StageTopComparison : Prop :=
  ∀ {R : Type u} [CommRing R] (rs : List R) (M : Coeff R),
    Nonempty (tower rs M ⋙ HomologicalComplex.homologyFunctor (Coeff R) (.up ℤ) (rs.length : ℤ) ≅
      quotientDiagram rs M)

end
end Specs.CommutativeAlgebraNotes.KoszulTower
