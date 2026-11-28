import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.IndecomposableVectors
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.ReflectionEquivalence
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.RootVectorReduction
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Conj
import Batteries.Tactic.OpenPrivate

/-! Gabriel's dimension-vector bijection via reflection functors. -/

open CategoryTheory CategoryTheory.Limits
open scoped Matrix

namespace RepTheorySurvey.Quiver.IndecomposableVectors

noncomputable section

universe u v w d

open Forms SimpleReflections SinkCycle RootVectorReduction CoxeterDynamics
open ReflectionEquivalenceSpec (ArrowReversal IsSink IsSource Port SinkObjects SourceObjects)
open ReflectionEquivalence (sink_noSimpleSummand_iff source_noSimpleSummand_iff
  reflectSink_indecomposable_iff reflectSource_indecomposable_iff
  reflectSink_dimensionVector reflectSource_dimensionVector aggregateReflectionEquivalence
  sinkRestriction sourceRestriction)
open private coxeterPrefix_preservesTitsForm coxeter_pow_preservesTitsForm
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.CoxeterDynamics
open private titsForm_smul_vertexUnit from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.SimpleReflections
open private simpleCenter simpleOff_zero from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.ReflectionEquivalence

variable {Q : Type u}

/-- The prefix of the sink schedule, with arrows written in their original arrow universe.
As in `endpointsAt`, each edge is reversed just when one endpoint has been processed. -/
@[instance_reducible]
private def prefixQuiver [Fintype Q] (q : Quiver.{v} Q) (number : Q ≃ Fin (Fintype.card Q))
    (m : ℕ) : Quiver.{v} Q := by
  classical
  exact ⟨fun j l => if ((number j : ℕ) < m ↔ (number l : ℕ) < m)
    then q.Hom j l else q.Hom l j⟩

private theorem prefixQuiver_zero [Fintype Q] (q : Quiver.{v} Q)
    (number : Q ≃ Fin (Fintype.card Q)) : prefixQuiver q number 0 = q := by
  cases q
  rfl

private theorem prefixQuiver_card [Fintype Q] (q : Quiver.{v} Q)
    (number : Q ≃ Fin (Fintype.card Q)) : prefixQuiver q number (Fintype.card Q) = q := by
  cases q with
  | mk Hom =>
    apply congrArg (fun f : Q → Q → Type v => Quiver.mk f)
    funext j l
    change (if _ then _ else _) = Hom j l
    simp [(number j).isLt, (number l).isLt]

private theorem prefixQuiver_edgeMultiplicity [Fintype Q] (q : Quiver.{v} Q)
    (number : Q ≃ Fin (Fintype.card Q)) (m : ℕ) (j l : Q) :
    @edgeMultiplicity Q (prefixQuiver q number m) j l = @edgeMultiplicity Q q j l := by
  classical
  change Nat.card (if ((number j : ℕ) < m ↔ (number l : ℕ) < m)
      then q.Hom j l else q.Hom l j) +
    Nat.card (if ((number l : ℕ) < m ↔ (number j : ℕ) < m)
      then q.Hom l j else q.Hom j l) = Nat.card (q.Hom j l) + Nat.card (q.Hom l j)
  split_ifs <;> first | rfl | exact Nat.add_comm _ _ | omega

private theorem prefixQuiver_isSink [Fintype Q] {q : Quiver.{v} Q}
    {number : Q ≃ Fin (Fintype.card Q)} (h : @IsSinkNumbering Q q _ number)
    (i : Fin (Fintype.card Q)) : IsSink (prefixQuiver q number i.val) (number.symm i) := by
  classical
  intro j
  change IsEmpty (if ((number (number.symm i) : ℕ) < i.val ↔ (number j : ℕ) < i.val)
    then q.Hom (number.symm i) j else q.Hom j (number.symm i))
  simp only [Equiv.apply_symm_apply, lt_irrefl, false_iff]
  split
  · rename_i hj
    exact ⟨fun a => hj (by simpa using h ⟨number.symm i, j, a⟩)⟩
  · rename_i hj
    refine ⟨fun a => ?_⟩
    have hji : i < number j := by simpa using h ⟨j, number.symm i, a⟩
    exact hj (not_lt_of_ge (le_of_lt hji))

private theorem prefixQuiver_isSource [Fintype Q] {q : Quiver.{v} Q}
    {number : Q ≃ Fin (Fintype.card Q)} (h : @IsSinkNumbering Q q _ number)
    (i : Fin (Fintype.card Q)) :
    IsSource (prefixQuiver q number (i.val + 1)) (number.symm i) := by
  classical
  intro j
  change IsEmpty (if ((number j : ℕ) < i.val + 1 ↔
      (number (number.symm i) : ℕ) < i.val + 1)
    then q.Hom j (number.symm i) else q.Hom (number.symm i) j)
  simp only [Equiv.apply_symm_apply, Nat.lt_succ_self, iff_true]
  split
  · rename_i hj
    refine ⟨fun a => ?_⟩
    have hji : (i : ℕ) < (number j : ℕ) := by simpa using h ⟨j, number.symm i, a⟩
    omega
  · rename_i hj
    refine ⟨fun a => ?_⟩
    have hji : (number j : ℕ) < (i : ℕ) := by simpa using h ⟨number.symm i, j, a⟩
    omega

private def prefixQuiver_reversal [Fintype Q] {q : Quiver.{v} Q}
    {number : Q ≃ Fin (Fintype.card Q)} (h : @IsSinkNumbering Q q _ number)
    (i : Fin (Fintype.card Q)) :
    ArrowReversal (prefixQuiver q number i.val) (prefixQuiver q number (i.val + 1))
      (number.symm i) := by
  classical
  refine ⟨prefixQuiver_isSink h i, prefixQuiver_isSource h i, ?_, ?_⟩
  · intro j
    apply Equiv.cast
    have hj : (number (j : Q) : ℕ) ≠ (i : ℕ) := by
      intro he
      exact j.property (number.injective ((Fin.ext he).trans (number.apply_symm_apply i).symm))
    change (if ((number (j : Q) : ℕ) < i.val ↔
        (number (number.symm i) : ℕ) < i.val) then q.Hom j (number.symm i)
        else q.Hom (number.symm i) j) =
      (if ((number (number.symm i) : ℕ) < i.val + 1 ↔ (number (j : Q) : ℕ) < i.val + 1)
        then q.Hom (number.symm i) j else q.Hom j (number.symm i))
    simp only [Equiv.apply_symm_apply, lt_irrefl, iff_false, Nat.lt_succ_self, true_iff]
    split_ifs <;> first | rfl | omega
  · intro j l
    apply Equiv.cast
    have hj : (number (j : Q) : ℕ) ≠ i.val := fun he =>
      j.property (number.injective ((Fin.ext he).trans (number.apply_symm_apply i).symm))
    have hl : (number (l : Q) : ℕ) ≠ i.val := fun he =>
      l.property (number.injective ((Fin.ext he).trans (number.apply_symm_apply i).symm))
    change (if ((number (j : Q) : ℕ) < i.val ↔ (number (l : Q) : ℕ) < i.val)
        then q.Hom j l else q.Hom l j) =
      (if ((number (j : Q) : ℕ) < i.val + 1 ↔ (number (l : Q) : ℕ) < i.val + 1)
        then q.Hom j l else q.Hom l j)
    split_ifs <;> first | rfl | omega

private abbrev stageQuiver [Fintype Q] (q : Quiver.{v} Q)
    (number : Q ≃ Fin (Fintype.card Q)) (m : ℕ) : Quiver.{v} Q :=
  prefixQuiver q number (m % Fintype.card Q)

private theorem stageQuiver_zero [Fintype Q] (q : Quiver.{v} Q)
    (number : Q ≃ Fin (Fintype.card Q)) : stageQuiver q number 0 = q := by
  simp [stageQuiver, prefixQuiver_zero]

private def stageReversal [Fintype Q] {q : Quiver.{v} Q}
    {number : Q ≃ Fin (Fintype.card Q)} (h : @IsSinkNumbering Q q _ number)
    (m : ℕ) (i : Fin (Fintype.card Q)) (hi : i.val = m % Fintype.card Q) :
    ArrowReversal (stageQuiver q number m) (stageQuiver q number (m + 1)) (number.symm i) := by
  have hsucc : (m + 1) % Fintype.card Q = (i.val + 1) % Fintype.card Q := by
    rw [Nat.add_mod m 1 _, Nat.add_mod i.val 1 _, ← hi, Nat.mod_eq_of_lt i.isLt]
  have horient : stageQuiver q number (m + 1) = prefixQuiver q number (i.val + 1) := by
    unfold stageQuiver
    rw [hsucc]
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt i.isLt) with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt]
    · rw [show i.val + 1 = Fintype.card Q from heq, Nat.mod_self,
        prefixQuiver_zero, prefixQuiver_card]
  have horient' : stageQuiver q number m = prefixQuiver q number i.val := by
    unfold stageQuiver
    rw [hi]
  rw [horient', horient]
  exact prefixQuiver_reversal h i

private theorem prefixQuiver_finite [Fintype Q] (q : Quiver.{v} Q)
    [Finite (@RM03.Arrow Q q)] (number : Q ≃ Fin (Fintype.card Q)) (m : ℕ) :
    Finite (@RM03.Arrow Q (prefixQuiver q number m)) := by
  classical
  have fiberFinite (j l : Q) : Finite ((prefixQuiver q number m).Hom j l) := by
    have hf (a b : Q) : Finite (q.Hom a b) :=
      Finite.of_injective (fun e => (⟨a, b, e⟩ : @RM03.Arrow Q q)) (by
        intro e f h
        cases h
        rfl)
    change Finite (if _ then _ else _)
    split <;> apply hf
  change Finite (Σ j, Σ l, (prefixQuiver q number m).Hom j l)
  let (j l : Q) := fiberFinite j l
  infer_instance

private theorem stageReflection [Fintype Q] (q : Quiver.{v} Q)
    (number : Q ≃ Fin (Fintype.card Q)) (m : ℕ) (i : Q) (x : DimensionVector Q) :
    @simpleReflection Q (stageQuiver q number m) _ ℤ _ i x =
      @simpleReflection Q q _ ℤ _ i x := by
  have hB : @polarizationMatrix Q (stageQuiver q number m) ℤ _ =
      @polarizationMatrix Q q ℤ _ := by
    ext j l
    simp [polarizationMatrix, FormsSpec.polarizationMatrix, prefixQuiver_edgeMultiplicity]
  rw [@simpleReflection_apply Q (stageQuiver q number m), @simpleReflection_apply Q q, hB]

private theorem simpleReflection_unitVector [Fintype Q] (q : Quiver.{v} Q) (i : Q) :
    @simpleReflection Q q _ ℤ _ i (unitVector i) = -unitVector i := by
  classical
  change @simpleReflection Q q _ ℤ _ i (FormsSpec.unitVector i) = -FormsSpec.unitVector i
  rw [← vertexUnit_int i, @simpleReflection_apply Q q, @vertexUnit_squareLength Q q]
  funext j
  change vertexUnit ℤ i j - 2 * vertexUnit ℤ i j = -vertexUnit ℤ i j
  omega

private theorem unitVector_self (i : Q) : unitVector i i = 1 := by
  simp [unitVector, FormsSpec.unitVector]

private abbrev Indec (k : Type w) [Field k] (q : Quiver.{v} Q) :=
  @IndecomposableRepresentation.{u, v, w, max w d} k Q _ q

private abbrev dims {k : Type w} [Field k] {q : Quiver.{v} Q}
    (V : Indec.{u, v, w, d} k q) : DimensionVector Q :=
  @dimensionVector k Q _ q V.val

private theorem dims_nonneg {k : Type w} [Field k] {q : Quiver.{v} Q}
    (V : Indec.{u, v, w, d} k q) (j : Q) : 0 ≤ dims V j := Int.natCast_nonneg _

private theorem isZero_vertex_of_dim_zero {k : Type w} [Field k] {q : Quiver.{v} Q}
    (V : Indec.{u, v, w, d} k q) (j : Q) (hj : dims V j = 0) :
    IsZero (ReflectionEquivalenceSpec.vertex V.val.obj j) := by
  let : Module.Finite k (ReflectionEquivalenceSpec.vertex V.val.obj j) := V.val.property j
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact (Module.finrank_eq_zero_iff_of_free k _).mp (Int.ofNat_eq_zero.mp hj)

private theorem dims_ne_zero {k : Type w} [Field k] {q : Quiver.{v} Q}
    (V : Indec.{u, v, w, d} k q) : dims V ≠ 0 := by
  intro h
  apply V.property.1
  apply (Functor.isZero_iff _).mpr
  intro j
  exact isZero_vertex_of_dim_zero V j (congrFun h j)

private def simpleIndec (k : Type w) [Field k] (q : Quiver.{v} Q) (i : Q) :
    Indec.{u, v, w, d} k q := by
  letI := q
  let S := vertexSimple.{u, v, w, d} k i
  letI : Simple S := vertexSimple_isSimple k i
  exact ⟨⟨S, finite_vertexSimple k i⟩, indecomposable_of_simple S⟩

private theorem dims_simpleIndec (k : Type w) [Field k] (q : Quiver.{v} Q) (i : Q) :
    dims (simpleIndec.{u, v, w, d} k q i) = unitVector i := by
  let := q
  exact dimensionVector_vertexSimple k i _

private theorem noSimpleSummand_of_dim_ne {k : Type w} [Field k] {q : Quiver.{v} Q}
    (V : Indec.{u, v, w, d} k q) (i : Q) (h : dims V ≠ unitVector i) :
    ReflectionEquivalenceSpec.NoSimpleSummand.{u, v, w, d} i V.val.obj := by
  let := q
  rintro ⟨W, ⟨e⟩⟩
  let S := simpleIndec.{u, v, w, d} k q i
  have e' : V.val.obj ≅ S.val.obj ⊞ W := e
  have hz := (V.property.2 S.val.obj W e').resolve_left S.property.1
  have : IsIso (biprod.inl : S.val.obj ⟶ S.val.obj ⊞ W) :=
    (Biprod.isIso_inl_iff_isZero _ _).mpr hz
  apply h
  exact (dimensionVector_iso (V := V.val) (W := S.val)
    (e'.trans (asIso biprod.inl).symm)).trans (dims_simpleIndec k q i)

private theorem iso_simple_of_dims {k : Type w} [Field k] {q : Quiver.{v} Q}
    (V : Indec.{u, v, w, d} k q) (i : Q) (hli : IsEmpty (q.Hom i i))
    (h : dims V = unitVector i) : Nonempty (V.val.obj ≅ (simpleIndec k q i).val.obj) := by
  classical
  let := q
  let S := simpleIndec.{u, v, w, d} k q i
  have hdim : dims V = dims S := h.trans (dims_simpleIndec k q i).symm
  let e (j : Q) : RM03.QuiverRepresentation.vertex V.val.obj j ≃ₗ[k]
      RM03.QuiverRepresentation.vertex S.val.obj j := by
    letI := V.val.property j
    letI := S.val.property j
    exact LinearEquiv.ofFinrankEq _ _ (Int.ofNat_inj.mp (congrFun hdim j))
  let f : V.val.obj ⟶ S.val.obj := RM03.QuiverRepresentation.homMk
    (fun j => (e j).toLinearMap) (by
      intro j l a
      change (e l).toLinearMap.comp (RM03.QuiverRepresentation.arrow V.val.obj a) =
        (RM03.QuiverRepresentation.arrow S.val.obj a).comp (e j).toLinearMap
      rw [show RM03.QuiverRepresentation.arrow S.val.obj a = 0 from vertexSimple_arrow k i a,
        LinearMap.zero_comp]
      have hzero (j : Q) (hj : j ≠ i) :
          Subsingleton (RM03.QuiverRepresentation.vertex V.val.obj j) := by
        apply ModuleCat.isZero_iff_subsingleton.mp
        exact isZero_vertex_of_dim_zero V j (by simp [h, unitVector, FormsSpec.unitVector, hj])
      by_cases hj : j = i
      · subst j
        by_cases hl : l = i
        · subst l
          exact (hli.false a).elim
        · have := hzero l hl
          rw [show RM03.QuiverRepresentation.arrow V.val.obj a = 0 from Subsingleton.elim _ _,
            LinearMap.comp_zero]
      · have := hzero j hj
        ext x
        rw [Subsingleton.elim x 0]
        simp)
  have hf : IsIso f := by
    apply (NatTrans.isIso_iff_isIso_app f).mpr
    intro j
    change IsIso (ModuleCat.ofHom (e j).toLinearMap)
    exact (e j).toModuleIso.isIso_hom
  exact ⟨asIso f⟩

private def endAlgEquivOfIso {k : Type*} [Field k] {C : Type*} [Category* C]
    [Preadditive C] [Linear k C] {X Y : C} (e : X ≅ Y) : End X ≃ₐ[k] End Y where
  toMulEquiv := e.conj
  map_add' f g := by
    ext
    change e.inv ≫ (f.asHom + g.asHom) ≫ e.hom =
      (e.inv ≫ f.asHom ≫ e.hom) + (e.inv ≫ g.asHom ≫ e.hom)
    simp [Preadditive.add_comp, Preadditive.comp_add]
  commutes' c := by
    ext
    simp only [Algebra.algebraMap_eq_smul_one]
    change e.inv ≫ (c • 𝟙 X) ≫ e.hom = c • 𝟙 Y
    simp [Linear.smul_comp, Linear.comp_smul]

private def endAlgEquivOfFullyFaithful {k : Type*} [Field k]
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [Linear k C] [Linear k D] (F : C ⥤ D) [F.Additive] [F.Linear k]
    (hF : F.FullyFaithful) (X : C) : End X ≃ₐ[k] End (F.obj X) where
  toMulEquiv := hF.mulEquivEnd X
  map_add' f g := by
    ext
    exact F.map_add
  commutes' c := by
    ext
    simp only [Algebra.algebraMap_eq_smul_one]
    change F.map (c • 𝟙 X) = c • 𝟙 (F.obj X)
    rw [F.map_smul, F.map_id]

private def simpleEndAlgEquiv (k : Type w) [Field k] (q : Quiver.{v} Q) (i : Q) :
    End (simpleIndec.{u, v, w, d} k q i).val.obj ≃ₐ[k] k := by
  classical
  letI := q
  let S := (simpleIndec.{u, v, w, d} k q i).val.obj
  let e : S.obj (i : Paths Q) ≃ₗ[k] k := simpleCenter q i
  let one : S.obj (i : Paths Q) := e.symm 1
  have hmap (c : k) (x : S.obj (i : Paths Q)) :
      (algebraMap k (End S) c).asHom.app (i : Paths Q) x = c • x := by
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  have h_eval (c : k) : e ((algebraMap k (End S) c).asHom.app i one) = c := by
    calc
      _ = e (c • one) := congrArg e (hmap c one)
      _ = c := by simp [one, smul_eq_mul]
  refine (AlgEquiv.ofBijective (Algebra.ofId k (End S)) ⟨?_, ?_⟩).symm
  · intro a b hab
    exact (h_eval a).symm.trans
      ((congrArg (fun f : End S => e (f.asHom.app i one)) hab).trans (h_eval b))
  · intro f
    let c := e (f.asHom.app i one)
    refine ⟨c, ?_⟩
    apply End.ext
    apply NatTrans.ext
    funext j
    by_cases hj : j = (i : Paths Q)
    · subst j
      apply ModuleCat.hom_ext
      ext x
      change (algebraMap k (End S) c).asHom.app i x = f.asHom.app i x
      refine (hmap c x).trans ?_
      let f₀ := (f.asHom.app (i : Paths Q)).hom
      change c • x = f₀ x
      have hx : x = (e x) • one := by
        apply e.injective
        simp [one, smul_eq_mul]
      have hcenter : f₀ one = c • one := by
        apply e.injective
        change e (f₀ one) = e (c • one)
        simp [f₀, c, one, smul_eq_mul]
      calc
        c • x = c • (e x • one) := congrArg (c • ·) hx
        _ = e x • (c • one) := smul_comm c (e x) one
        _ = f₀ (e x • one) := by rw [map_smul, hcenter]
        _ = f₀ x := congrArg f₀ hx.symm
    · exact (simpleOff_zero.{u, v, w, d} (k := k) q hj).eq_of_src _ _

section ReflectionStep

variable {k : Type w} [Field k] {q r : Quiver.{v} Q} {i : Q}
variable [Finite (Port q i)] (A : ArrowReversal q r i)

private def sinkObject (V : Indec.{u, v, w, d} k q) (h : dims V ≠ unitVector i) :
    (SinkObjects.{u, v, w, max w d} k q i).FullSubcategory :=
  ⟨V.val.obj, V.val.property, (sink_noSimpleSummand_iff A.sink V.val.obj).mp
    (noSimpleSummand_of_dim_ne V i h)⟩

private def sourceObject (V : Indec.{u, v, w, d} k r) (h : dims V ≠ unitVector i) :
    (SourceObjects.{u, v, w, max w d} k A).FullSubcategory :=
  ⟨V.val.obj, V.val.property, (source_noSimpleSummand_iff A V.val.obj).mp
    (noSimpleSummand_of_dim_ne V i h)⟩

private def forward (V : Indec.{u, v, w, d} k q) (h : dims V ≠ unitVector i) :
    Indec.{u, v, w, d} k r :=
  let X := sinkObject A V h
  let Y := (sinkRestriction A).obj X
  ⟨⟨Y.obj, Y.property.1⟩, (reflectSink_indecomposable_iff A X).mpr V.property⟩

private def backward (V : Indec.{u, v, w, d} k r) (h : dims V ≠ unitVector i) :
    Indec.{u, v, w, d} k q :=
  let X := sourceObject A V h
  let Y := (sourceRestriction A).obj X
  ⟨⟨Y.obj, Y.property.1⟩, (reflectSource_indecomposable_iff A X).mpr V.property⟩

private theorem dims_forward [Fintype Q] (V : Indec.{u, v, w, d} k q)
    (h : dims V ≠ unitVector i) :
    dims (forward A V h) = @simpleReflection Q q _ ℤ _ i (dims V) := by
  obtain ⟨_, he⟩ := reflectSink_dimensionVector A (sinkObject A V h)
  exact he

private theorem dims_backward [Fintype Q] (V : Indec.{u, v, w, d} k r)
    (h : dims V ≠ unitVector i) :
    dims (backward A V h) = @simpleReflection Q r _ ℤ _ i (dims V) := by
  obtain ⟨_, he⟩ := reflectSource_dimensionVector A (sourceObject A V h)
  exact he

private def isoOfForwardIso (V W : Indec.{u, v, w, d} k q)
    (hV : dims V ≠ unitVector i) (hW : dims W ≠ unitVector i)
    (e : (forward A V hV).val.obj ≅ (forward A W hW).val.obj) : V.val.obj ≅ W.val.obj :=
  let E := aggregateReflectionEquivalence (k := k) A
  (SinkObjects k q i).ι.mapIso
    (E.fullyFaithfulFunctor.isoEquiv.symm ((SourceObjects k A).isoMk e))

private def endForwardEquiv (V : Indec.{u, v, w, d} k q) (h : dims V ≠ unitVector i) :
    End V.val.obj ≃ₐ[k] End (forward A V h).val.obj :=
  let X := sinkObject A V h
  let E := aggregateReflectionEquivalence (k := k) A
  let Y := E.functor.obj X
  letI : E.functor.Additive := ReflectionEquivalence.sinkRestriction_additive A
  letI : E.functor.Linear k := ReflectionEquivalence.sinkRestriction_linear A
  let P := SinkObjects.{u, v, w, max w d} k q i
  let P' := SourceObjects.{u, v, w, max w d} k A
  (endAlgEquivOfFullyFaithful P.ι P.fullyFaithfulι X).symm.trans
    ((endAlgEquivOfFullyFaithful E.functor E.fullyFaithfulFunctor X).trans
      (endAlgEquivOfFullyFaithful P'.ι P'.fullyFaithfulι Y))

end ReflectionStep

private theorem ne_unitVector_of_reflection_nonneg [Fintype Q] (q : Quiver.{v} Q)
    (i : Q) (x : DimensionVector Q)
    (h : ∀ l, 0 ≤ @simpleReflection Q q _ ℤ _ i x l) :
    x ≠ unitVector i := by
  rintro rfl
  specialize h i
  rw [simpleReflection_unitVector] at h
  change 0 ≤ -unitVector i i at h
  rw [unitVector_self] at h
  omega

private abbrev RepFiber (k : Type w) [Field k] (q : Quiver.{v} Q) (x : DimensionVector Q) :=
  {V : Indec.{u, v, w, d} k q // dims V = x}

/-- Existence, uniqueness up to isomorphism, and the endomorphism algebra in one
dimension-vector fiber. -/
private abbrev Classified (k : Type w) [Field k] (q : Quiver.{v} Q) (x : DimensionVector Q) :=
  Nonempty (RepFiber.{u, v, w, d} k q x) ∧
    (∀ V W : RepFiber.{u, v, w, d} k q x, Nonempty (V.val.val.obj ≅ W.val.val.obj)) ∧
    (∀ V : RepFiber.{u, v, w, d} k q x, Nonempty (End V.val.val.obj ≃ₐ[k] k))

private theorem classified_unitVector (k : Type w) [Field k] (q : Quiver.{v} Q) (i : Q)
    (h : IsEmpty (q.Hom i i)) : Classified.{u, v, w, d} k q (unitVector i) := by
  refine ⟨⟨⟨simpleIndec k q i, dims_simpleIndec k q i⟩⟩, ?_, ?_⟩
  · intro V W
    obtain ⟨e⟩ := iso_simple_of_dims V.val i h V.property
    obtain ⟨f⟩ := iso_simple_of_dims W.val i h W.property
    exact ⟨e.trans f.symm⟩
  · intro V
    obtain ⟨e⟩ := iso_simple_of_dims V.val i h V.property
    exact ⟨(endAlgEquivOfIso e).trans (simpleEndAlgEquiv k q i)⟩

private def forwardFiber {k : Type w} [Field k] [Fintype Q] {q r : Quiver.{v} Q} {i : Q}
    [Finite (Port q i)] (A : ArrowReversal q r i) {x y : DimensionVector Q}
    (hxy : @simpleReflection Q q _ ℤ _ i x = y) (hy : ∀ l, 0 ≤ y l)
    (V : RepFiber.{u, v, w, d} k q x) : RepFiber.{u, v, w, d} k r y := by
  have hV : dims V.val ≠ unitVector i := by
    rw [V.property]
    exact ne_unitVector_of_reflection_nonneg q i x (by simpa only [hxy] using hy)
  exact ⟨forward A V.val hV, (dims_forward A V.val hV).trans
    (by rw [V.property, hxy])⟩

private theorem classified_before_reflection {k : Type w} [Field k] [Fintype Q]
    {q r : Quiver.{v} Q} {i : Q} [Finite (Port q i)] (A : ArrowReversal q r i)
    {x y : DimensionVector Q}
    (hxy : @simpleReflection Q q _ ℤ _ i x = y)
    (hyx : @simpleReflection Q r _ ℤ _ i y = x)
    (hx : ∀ l, 0 ≤ x l) (hy : ∀ l, 0 ≤ y l)
    (h : Classified.{u, v, w, d} k r y) : Classified.{u, v, w, d} k q x := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨W⟩ := h.1
    have hW : dims W.val ≠ unitVector i := by
      rw [W.property]
      exact ne_unitVector_of_reflection_nonneg r i y (by simpa only [hyx] using hx)
    exact ⟨⟨backward A W.val hW, (dims_backward A W.val hW).trans
      (by rw [W.property, hyx])⟩⟩
  · intro V W
    obtain ⟨e⟩ := h.2.1 (forwardFiber A hxy hy V) (forwardFiber A hxy hy W)
    exact ⟨isoOfForwardIso A V.val W.val _ _ e⟩
  · intro V
    obtain ⟨e⟩ := h.2.2 (forwardFiber A hxy hy V)
    exact ⟨(endForwardEquiv A V.val _).trans e⟩

section CyclicSchedule

variable {k : Type w} [Field k] [q : Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)]
variable {number : Q ≃ Fin (Fintype.card Q)} (hn : IsSinkNumbering number)

omit [Fintype (RM03.Arrow Q)] in
private theorem step_formula (m : ℕ) (i : Fin (Fintype.card Q))
    (hi : i.val = m % Fintype.card Q) (x : DimensionVector Q) :
    @simpleReflection Q (stageQuiver q number m) _ ℤ _ (number.symm i)
      (vectorAtStep number m x) = vectorAtStep number (m + 1) x :=
  (stageReflection q number m _ _).trans (vectorAtStep_succ number m i hi x).symm

omit [Fintype (RM03.Arrow Q)] in
private theorem inverse_step_formula (m : ℕ) (i : Fin (Fintype.card Q))
    (hi : i.val = m % Fintype.card Q) (x : DimensionVector Q) :
    @simpleReflection Q (stageQuiver q number (m + 1)) _ ℤ _ (number.symm i)
      (vectorAtStep number (m + 1) x) = vectorAtStep number m x := by
  calc
    _ = simpleReflection ℤ (number.symm i) (vectorAtStep number (m + 1) x) :=
      stageReflection q number (m + 1) _ _
    _ = simpleReflection ℤ (number.symm i)
          (simpleReflection ℤ (number.symm i) (vectorAtStep number m x)) :=
      congrArg (simpleReflection ℤ (number.symm i)) (vectorAtStep_succ number m i hi x)
    _ = _ := simpleReflection_involutive ℤ (number.symm i) _

include hn

/-- Up to the last nonnegative vector, the sink reflections can be applied to
a representation with the starting dimension vector. -/
private theorem nonempty_fiber_at (hcard : 0 < Fintype.card Q) (x : DimensionVector Q)
    (hstart : Nonempty (RepFiber.{u, v, w, d} k (stageQuiver q number 0)
      (vectorAtStep number 0 x))) (m : ℕ)
    (hnn : ∀ j ≤ m, ∀ l, 0 ≤ vectorAtStep number j x l) :
    Nonempty (RepFiber.{u, v, w, d} k (stageQuiver q number m) (vectorAtStep number m x)) := by
  induction m with
  | zero => exact hstart
  | succ m ih =>
    obtain ⟨V⟩ := ih (fun j hj => hnn j (Nat.le_succ_of_le hj))
    let i : Fin (Fintype.card Q) := ⟨m % Fintype.card Q, Nat.mod_lt _ hcard⟩
    let A := stageReversal hn m i rfl
    let : Finite (@RM03.Arrow Q (stageQuiver q number m)) := prefixQuiver_finite q number _
    exact ⟨forwardFiber A (step_formula m i rfl x) (hnn (m + 1) le_rfl) V⟩

private theorem classified_at_zero (hcard : 0 < Fintype.card Q) (x : DimensionVector Q)
    (m : ℕ) (hnn : ∀ j ≤ m, ∀ l, 0 ≤ vectorAtStep number j x l)
    (hc : Classified.{u, v, w, d} k (stageQuiver q number m) (vectorAtStep number m x)) :
    Classified.{u, v, w, d} k (stageQuiver q number 0) (vectorAtStep number 0 x) := by
  induction m with
  | zero => exact hc
  | succ m ih =>
    apply ih (fun j hj => hnn j (Nat.le_succ_of_le hj))
    let i : Fin (Fintype.card Q) := ⟨m % Fintype.card Q, Nat.mod_lt _ hcard⟩
    let A := stageReversal hn m i rfl
    let : Finite (@RM03.Arrow Q (stageQuiver q number m)) := prefixQuiver_finite q number _
    exact classified_before_reflection A (step_formula m i rfl x)
      (inverse_step_formula m i rfl x) (hnn m (Nat.le_succ m)) (hnn (m + 1) le_rfl) hc

private theorem classified_of_titsForm_one
    (hacyc : ¬ RM03.HasOrientedCycle Q) (hpos : PositiveDefinite Q)
    (x : DimensionVector Q) (hx : ∀ l, 0 ≤ x l) (h1 : titsForm x = 1) :
    Classified.{u, v, w, d} k q x := by
  obtain ⟨m, i, hi, hnn, hunit, _⟩ := firstNegativeStep hacyc hpos number hn x hx h1
  let A := stageReversal hn m i hi
  have hu : vectorAtStep number m x = unitVector (number.symm i) := hunit
  have hc : Classified.{u, v, w, d} k (stageQuiver q number m) (vectorAtStep number m x) := by
    rw [hu]
    exact classified_unitVector k _ (number.symm i) (A.sink (number.symm i))
  have h0 := classified_at_zero hn (Nat.zero_lt_of_lt i.isLt) x m hnn hc
  simpa only [stageQuiver_zero, vectorAtStep_zero] using h0

private theorem titsForm_dims_eq_one
    (hacyc : ¬ RM03.HasOrientedCycle Q) (hpos : PositiveDefinite Q)
    (V : Indec.{u, v, w, d} k q) : titsForm (dims V) = 1 := by
  classical
  let x := dims V
  have hcard : 0 < Fintype.card Q := by
    apply Fintype.card_pos_iff.mpr
    by_contra h
    apply dims_ne_zero V
    funext j
    exact (h ⟨j⟩).elim
  have hneg : ∃ n, ∃ j, vectorAtStep number n x j < 0 := by
    obtain ⟨m, j, hj⟩ := coxeter_negativeCoordinateIntegral hacyc hpos number hn
      x (dims_ne_zero V) (dims_nonneg V)
    exact ⟨Fintype.card Q * m, j, by rwa [vectorAtStep_mul_card number hcard]⟩
  have hn0 : Nat.find hneg ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := Nat.find_spec hneg
    rw [h, vectorAtStep_zero] at hj
    exact (not_lt_of_ge (dims_nonneg V j)) hj
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hnn (j : ℕ) (hj : j ≤ m) (l : Q) : 0 ≤ vectorAtStep number j x l := by
    by_contra! h
    apply (Nat.find_min hneg (m := j) (by omega))
    exact ⟨l, h⟩
  have hstart : Nonempty (RepFiber.{u, v, w, d} k (stageQuiver q number 0)
      (vectorAtStep number 0 x)) := by
    simpa only [stageQuiver_zero, vectorAtStep_zero] using
      (show Nonempty (RepFiber.{u, v, w, d} k q x) from ⟨⟨V, rfl⟩⟩)
  obtain ⟨W⟩ := nonempty_fiber_at hn hcard x hstart m hnn
  let i : Fin (Fintype.card Q) := ⟨m % Fintype.card Q, Nat.mod_lt _ hcard⟩
  let A := stageReversal hn m i rfl
  let : Finite (@RM03.Arrow Q (stageQuiver q number m)) := prefixQuiver_finite q number _
  have hu : vectorAtStep number m x = unitVector (number.symm i) := by
    by_contra h
    obtain ⟨j, hj⟩ := Nat.find_spec hneg
    rw [hm] at hj
    let W' := forward A W.val (W.property.symm ▸ h)
    have he : dims W' = vectorAtStep number (m + 1) x :=
      (dims_forward A W.val _).trans (by rw [W.property, step_formula m i rfl x])
    exact (not_lt_of_ge (dims_nonneg W' j)) (by rwa [he])
  have hinv : titsForm (vectorAtStep number m x) = titsForm x :=
    (coxeterPrefix_preservesTitsForm hacyc number _
      _).trans (coxeter_pow_preservesTitsForm hacyc number _ x)
  calc
    titsForm x = titsForm (vectorAtStep number m x) := hinv.symm
    _ = titsForm (unitVector (number.symm i)) := congrArg titsForm hu
    _ = 1 := by
      simpa only [one_smul, vertexUnit_int, one_pow] using
        (titsForm_smul_vertexUnit hacyc (number.symm i) (1 : ℤ))

end CyclicSchedule

open IndecomposableVectorsSpec (PositiveTitsVector)

/-- The dimension-vector map is a bijection onto the nonnegative integral Tits roots. -/
theorem dimensionVector_bijection :
    IndecomposableVectorsSpec.DimensionVectorBijection.{u, v, w, d} := by
  intro k Q _ _ q _ _ hacyc hpos
  obtain ⟨number, hn⟩ := exists_sinkNumbering hacyc
  let f : IndecomposableClass.{u, v, w, max w d} k Q → PositiveTitsVector Q :=
    Quotient.lift
      (fun V : Indec.{u, v, w, d} k q =>
        ⟨dims V, dims_nonneg V, titsForm_dims_eq_one hn hacyc hpos V⟩)
      (by
        intro V W he
        obtain ⟨e⟩ := he
        exact Subtype.ext (dimensionVector_iso (V := V.val) (W := W.val) e))
  have hinj : Function.Injective f := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro V W hVW
    have hdim : dims V = dims W := congrArg Subtype.val hVW
    have hc := classified_of_titsForm_one.{u, v, w, d} (k := k) hn hacyc hpos
      (dims V) (dims_nonneg V) (titsForm_dims_eq_one hn hacyc hpos V)
    obtain ⟨e⟩ := hc.2.1 ⟨V, rfl⟩ ⟨W, hdim.symm⟩
    exact Quotient.sound ⟨e⟩
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨V⟩ := (classified_of_titsForm_one.{u, v, w, d} (k := k) hn hacyc hpos x.val
      x.property.1 x.property.2).1
    exact ⟨Quotient.mk _ V.val, Subtype.ext V.property⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩

/-- Reflection along the sink schedule identifies each endomorphism algebra with the
ground field. -/
theorem endomorphismAlgebra : IndecomposableVectorsSpec.EndomorphismAlgebra.{u, v, w, d} := by
  intro k Q _ _ q _ _ hacyc hpos V
  obtain ⟨number, hn⟩ := exists_sinkNumbering hacyc
  have hc := classified_of_titsForm_one.{u, v, w, d} (k := k) hn hacyc hpos
    (dims V) (dims_nonneg V) (titsForm_dims_eq_one hn hacyc hpos V)
  exact hc.2.2 ⟨V, rfl⟩

end

end RepTheorySurvey.Quiver.IndecomposableVectors
