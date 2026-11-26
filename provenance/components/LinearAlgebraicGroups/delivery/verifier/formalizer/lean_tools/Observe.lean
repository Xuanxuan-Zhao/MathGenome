import Lean
import Lean.Elab.Import

/- Trusted, standalone observer. It loads compiled declarations without loading
   candidate initializers and never elaborates an expected expression in a
   candidate's notation or instance context. -/
open Lean

structure Binding where
  actual_name : String
  expected_name : String
  expected_value_name : Option String := none
  deriving FromJson

structure CachedAxioms where
  name : String
  module : String
  axioms : Array String
  deriving FromJson

structure Request where
  mode : String := "observe"
  modules : Array String := #[]
  targets : Array String := #[]
  expected : Array Binding := #[]
  sources : Array String := #[]
  declarations : Option (Array String) := none
  raw : Option Bool := none
  kernel_evidence : Option Bool := none
  axiom_summaries : Option (Array CachedAxioms) := none
  deriving FromJson

def kind (c : ConstantInfo) : String :=
  match c with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def used (e : Expr) : Array Name :=
  e.foldConsts #[] fun n acc => acc.push n

/- Build dependencies from the actual imported types/values, never from candidate
   metadata. Propagate each reachable axiom backwards to its users. Shared proof
   terms are scanned once; cycles (including inductive declarations) terminate
   because each (declaration, axiom) pair is propagated only once. All state is
   local to this immutable imported environment. Exact owner-validated upstream
   closures can be leaves; new declarations still enter the same fixed point. -/
def axiomSets (env : Environment) (roots : List Name) (cached : NameMap NameSet) :
    NameMap NameSet × Nat × Nat := Id.run do
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut users : NameMap (Array Name) := {}
  let mut pending : List (Name × Name) := []
  let mut scanned := 0
  let mut reused := 0
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some axioms := cached.find? n then
      reused := reused + 1
      for axName in axioms.toList do pending := (n, axName) :: pending
      continue
    let some c := env.find? n | continue
    scanned := scanned + 1
    if kind c == "axiom" then pending := (n, n) :: pending
    let next := used c.type ++ (c.value? true |>.map used |>.getD #[])
    let mut unique : NameSet := {}
    for dep in next do
      if unique.contains dep then continue
      unique := unique.insert dep
      users := users.insert dep ((users.find? dep).getD #[] |>.push n)
      todo := dep :: todo
  let mut result : NameMap NameSet := {}
  while !pending.isEmpty do
    let (n, axName) := pending.head!
    pending := pending.tail!
    let found := (result.find? n).getD {}
    if found.contains axName then continue
    result := result.insert n (found.insert axName)
    for user in (users.find? n).getD #[] do
      pending := (user, axName) :: pending
  return (result, scanned, reused)

/- Inputs come only from owner-validated module reports. Check ownership again
   in the actual environment. Explicit empty closures are evidence; absence is a miss. -/
def validatedSeeds (env : Environment) (rows : Array CachedAxioms) : NameMap NameSet := Id.run do
  let mut result : NameMap NameSet := {}
  for row in rows do
    let name := row.name.toName
    let some idx := env.getModuleIdxFor? name | continue
    if env.header.moduleNames[idx.toNat]! != row.module.toName then continue
    if !(row.axioms.all fun ax => match env.find? ax.toName with
        | some (.axiomInfo _) => true
        | _ => false) then continue
    let axioms := row.axioms.foldl (fun (s : NameSet) ax => s.insert ax.toName) {}
    result := result.insert name axioms
  return result

def sortedNames (s : NameSet) : Array String :=
  (s.toList.map toString).toArray.qsort (· < ·)

def aligned (e : Expr) : Expr :=
  -- Irrelevant declared universe parameters are not a mathematical interface.
  -- Canonicalize only parameters actually occurring in the expression.
  let ps := (collectLevelParams {} e).params.toList
  let ls := ps.zipIdx |>.map fun (_, i) => Level.param (Name.num `_v8u i)
  e.instantiateLevelParams ps ls

def compareExpr (env : Environment) (ea eb : Expr) : Except String Bool := do
  if ea.hasMVar || eb.hasMVar || ea.hasFVar || eb.hasFVar then
    throw "open expression in trusted comparison"
  match Kernel.isDefEq env {} (aligned ea) (aligned eb) with
  | .ok result => return result
  | .error _ => throw "kernel could not compare closed expressions"

def checkBinding (env : Environment) (b : Binding) : Json := Id.run do
  let fail (message : String) := Json.mkObj [
    ("actual_name", toJson b.actual_name), ("expected_name", toJson b.expected_name),
    ("matched", toJson false), ("error", toJson message)]
  let some a := env.find? b.actual_name.toName | return fail "actual declaration missing"
  let some e := env.find? b.expected_name.toName | return fail "expected declaration missing"
  let some et := e.value? | return fail "expected type must be a definition with a value"
  -- A naked reference to the expected definition already specifies its universe
  -- substitution. Aligning its levels separately from the unfolded body may
  -- permute them. Keep the full generality check: every level must be a distinct
  -- parameter, so a specialization such as .{u,u} still takes the ordinary path.
  let typeComparison :=
    if a.type.isConstOf e.name then
      let levels := a.type.constLevels!
      if levels.length == e.levelParams.length && levels.all Level.isParam &&
          levels.eraseDups.length == levels.length then
        match Kernel.isDefEq env {} a.type (et.instantiateLevelParams e.levelParams levels) with
        | .ok equal => .ok equal
        | .error _ => .error "kernel could not compare closed expressions"
      else compareExpr env a.type et
    else compareExpr env a.type et
  let .ok typeMatch := typeComparison
    | return fail "expected type comparison failed"
  let mut valueMatch : Option Bool := none
  if let some valueName := b.expected_value_name then
    let some v := env.find? valueName.toName | return fail "expected value declaration missing"
    let some av := a.value? true | return fail "actual declaration has no value"
    let some ev := v.value? true | return fail "expected value declaration has no value"
    let .ok result := compareExpr env av ev | return fail "value comparison failed"
    valueMatch := some result
  return Json.mkObj [
    ("actual_name", toJson b.actual_name), ("expected_name", toJson b.expected_name),
    ("expected_value_name", toJson b.expected_value_name),
    ("type_matched", toJson typeMatch), ("value_matched", toJson valueMatch),
    ("matched", toJson (typeMatch && valueMatch.getD true))]

def pretty (env : Environment) (e : Expr) (all : Bool := false) : IO String := do
  let opts := ((({} : Options).setBool `pp.all all).setBool `pp.deepTerms true)
    |>.set `pp.maxSteps (1000000000 : Nat)
  let context : PPContext := { env := env, opts := opts }
  return (← context.runMetaM (Meta.ppExpr e)).pretty

/- One request has one environment/options context. Structural equality also
   preserves binder names and annotations, unlike Expr's default alpha equality. -/
def cachedPretty (env : Environment) (all : Bool)
    (cache : IO.Ref (ExprStructMap String)) (e : Expr) : IO String := do
  if let some text := (← cache.get).get? ⟨e⟩ then return text
  let text ← pretty env e all
  cache.modify (·.insert ⟨e⟩ text)
  return text

/- Imported module metadata lists all of its constants, including private
   declarations. Resolve names through the final environment rather than using
   an earlier ConstantInfo that may have been subsumed during import. The export
   loop still checks final module ownership. No proof or axiom data is omitted. -/
def moduleDeclarations (env : Environment) (owned : NameSet) : List (Name × ConstantInfo) := Id.run do
  if env.header.moduleData.size != env.header.moduleNames.size then
    return env.constants.toList
  let mut result := []
  let mut seen : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    unless owned.contains env.header.moduleNames[i]! do continue
    for n in env.header.moduleData[i]!.constNames do
      if seen.contains n then continue
      seen := seen.insert n
      let some c := env.find? n | continue
      result := (n, c) :: result
  return result

def observe (request : Request) : IO Json := do
  let selected := request.declarations.getD #[]
  let raw := request.raw.getD false
  let t0 ← IO.monoMsNow
  initSearchPath (← findSysroot)
  let imports := request.modules.map fun n => ({ module := n.toName, importAll := true } : Import)
  let env ← importModules imports {} (trustLevel := 0) (loadExts := false)
  let env := env.setExporting false
  let t1 ← IO.monoMsNow
  let rendered ← IO.mkRef ({} : ExprStructMap String)
  let owned := request.modules.foldl (fun (s : NameSet) n => s.insert n.toName) {}
  let mut declarations : Array Json := #[]
  let mut roots : List Name := []
  for (n, c) in moduleDeclarations env owned do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless owned.contains mod do continue
    roots := n :: roots
    if request.mode == "inspect" && !selected.contains n.toString then continue
    let value := c.value? true
    -- The kernel and axiom traversal still inspect the real proof term. It is
    -- redundant and often enormous in a human/model meaning-review report.
    let exportedValue := if kind c == "theorem" then none else value
    let mut fields := [
      ("name", toJson n.toString), ("module", toJson mod.toString),
      ("kind", toJson (kind c)), ("level_params", toJson (c.levelParams.map toString)),
      ("type", toJson (← cachedPretty env raw rendered c.type)),
      ("value", toJson (← exportedValue.mapM (cachedPretty env raw rendered))),
      ("value_omitted", toJson (if kind c == "theorem" then some "theorem_proof_term" else (none : Option String))),
      ("type_dependencies", toJson (used c.type |>.map toString)),
      ("value_dependencies", toJson (value.map used |>.getD #[] |>.map toString))]
    if raw then
      fields := fields ++ [("type_raw", toJson (reprStr c.type)),
        ("value_raw", toJson (exportedValue.map reprStr))]
    declarations := declarations.push <| Json.mkObj fields
  let t2 ← IO.monoMsNow
  if request.mode == "inspect" then
    return Json.mkObj [("declarations", toJson declarations),
      ("missing", toJson (selected.filter fun n => (env.find? n.toName).isNone))]
  let missing := request.targets.filter fun n => (env.find? n.toName).isNone
  -- Force pure work before its timestamp; the compiler may otherwise postpone
  -- it until JSON serialization, making the individual timings misleading.
  let axiomData ← IO.mkRef <| Id.run do
    let seeds := validatedSeeds env (request.axiom_summaries.getD #[])
    let (closures, scanned, reused) := axiomSets env
      (roots ++ request.targets.toList.map String.toName) seeds
    let axioms := sortedNames (roots.foldl (fun acc n =>
      ((closures.find? n).getD {}).toList.foldl (fun s a => s.insert a) acc) ({} : NameSet))
    let targetAxioms := request.targets.map fun n => Json.mkObj [
      ("name", toJson n), ("axioms", toJson (sortedNames ((closures.find? n.toName).getD {})))]
    let withAxioms := if request.kernel_evidence.getD false then
      declarations.map fun row =>
        let name := (row.getObjValAs? String "name").toOption.getD ""
        row.setObjVal! "transitive_axioms"
          (toJson (sortedNames ((closures.find? name.toName).getD {})))
      else declarations
    return (axioms, targetAxioms, withAxioms, scanned, reused)
  let (axioms, targetAxioms, observedDeclarations, scanned, reused) ← axiomData.get
  let t3 ← IO.monoMsNow
  let comparisonData ← IO.mkRef (request.expected.map (checkBinding env))
  let comparisons ← comparisonData.get
  let t4 ← IO.monoMsNow
  let result := Json.mkObj [
    ("axiom_traversal", Json.mkObj [("scanned_declarations", toJson scanned),
      ("reused_declarations", toJson reused)]),
    ("phase_ms", Json.mkObj [("imports", toJson (t1-t0)),
      ("declarations", toJson (t2-t1)), ("axioms", toJson (t3-t2)),
      ("comparisons", toJson (t4-t3))]),
    ("actual_declarations", Json.arr observedDeclarations),
    ("axioms", toJson axioms), ("target_axioms", Json.arr targetAxioms),
    ("missing_targets", toJson missing),
    ("comparisons", Json.arr comparisons)]
  if request.kernel_evidence.getD false then
    let graph := env.header.moduleNames.toList.zip env.header.moduleData.toList
      |>.map fun (name, data) => (name.toString, toJson (data.imports.map (·.module.toString)))
    return (result.setObjVal! "kernel_imports" (Json.mkObj graph)).setObjVal!
      "axiom_summary_format" (toJson "declaration-axioms-1")
  return result

def parseSources (request : Request) : IO Json := do
  let mut result := #[]
  for path in request.sources do
    let contents ← IO.FS.readFile path
    let (imports, _, messages) ← Lean.Elab.parseImports contents (some path)
    result := result.push <| Json.mkObj [
      ("path", toJson path), ("imports", toJson (imports.map (·.module.toString)))]
      |>.setObjVal! "error" (toJson (if messages.hasErrors then some "invalid import header" else (none : Option String)))
  return Json.arr result

def main (args : List String) : IO UInt32 := do
  try
    let [requestPath] := args | throw <| IO.userError "one request path is required"
    let raw ← IO.FS.readFile requestPath
    let .ok json := Json.parse raw | throw <| IO.userError "invalid request JSON"
    let request ← match fromJson? (α := Request) json with
      | .ok request => pure request
      | .error message => throw <| IO.userError ("invalid request shape: " ++ message)
    let result ← if request.mode == "imports" then parseSources request else observe request
    IO.println result.compress
    return 0
  catch e =>
    IO.eprintln s!"trusted-observer: {e}"
    return 1
