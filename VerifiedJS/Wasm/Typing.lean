/-
  VerifiedJS — Wasm Type Checking / Validation
  SPEC: WebAssembly 1.0 §3 (Validation)
  REF: WasmCert-Coq `theories/type_checker.v`

  Stack-based type checking: each instruction consumes and produces typed operands.
  We track an operand type stack plus an `unreachable` flag for polymorphic typing
  after `unreachable`/`br`/`return`.
-/

import VerifiedJS.Wasm.Syntax

namespace VerifiedJS.Wasm

/-- Validation context — tracks types available in scope.
    REF: WasmCert-Coq `t_context` in datatypes.v -/
structure ValCtx where
  types : Array FuncType
  funcs : Array FuncType         -- resolved function types (imports ++ module funcs)
  tables : Array TableType
  memories : Array MemType
  globals : Array GlobalType
  locals : Array ValType
  labels : List (List ValType)   -- label stack (innermost first)
  return_ : Option (List ValType)
  numDatas : Nat
  numElems : Nat
  deriving Repr

/-- Checker state: operand type stack + unreachable flag.
    REF: WasmCert-Coq `checker_type` in type_checker.v -/
structure CheckerType where
  stack : List ValType
  unreachable : Bool
  deriving Repr

private def emptyChecker : CheckerType := { stack := [], unreachable := false }

/-- Pop `n` types from the checker stack.  Under unreachable, missing slots are ok.
    REF: WasmCert-Coq `consume` -/
private def consume (ct : CheckerType) (expected : List ValType) : Except String CheckerType := do
  let rec go (stk : List ValType) (exp : List ValType) (unr : Bool) :
      Except String (List ValType) :=
    match exp with
    | [] => .ok stk
    | t :: ts =>
      match stk with
      | s :: ss =>
        if s == t then go ss ts unr
        else .error s!"type mismatch: expected {repr t}, got {repr s}"
      | [] =>
        if unr then go [] ts unr
        else .error s!"stack underflow: expected {repr t}"
  let stk' ← go ct.stack expected ct.unreachable
  .ok { ct with stack := stk' }

/-- Push types onto the checker stack.
    REF: WasmCert-Coq `produce` -/
private def produce (ct : CheckerType) (types : List ValType) : CheckerType :=
  { ct with stack := types.reverse ++ ct.stack }

/-- Consume then produce.
    REF: WasmCert-Coq `type_update` -/
private def typeUpdate (ct : CheckerType) (consumed produced : List ValType) :
    Except String CheckerType := do
  let ct' ← consume ct consumed
  .ok (produce ct' produced)

/-- Resolve a block type to input/output type lists. -/
private def resolveBlockType (ctx : ValCtx) (bt : BlockType) : Except String (List ValType × List ValType) :=
  match bt with
  | .none => .ok ([], [])
  | .valType t => .ok ([], [t])
  | .typeIdx idx =>
    match ctx.types[idx]? with
    | some ft => .ok (ft.params, ft.results)
    | none => .error s!"unknown type index {idx}"

mutual
/-- Type-check a single instruction. Returns updated checker state.
    REF: WasmCert-Coq `check_single` in type_checker.v -/
def checkInstr (ctx : ValCtx) (ct : CheckerType) (instr : Instr) :
    Except String CheckerType := do
  match instr with
  -- Control
  | .unreachable => .ok { stack := [], unreachable := true }
  | .nop => .ok ct
  | .block bt body =>
    let (inputs, outputs) ← resolveBlockType ctx bt
    let ct0 ← consume ct inputs
    let ctx' := { ctx with labels := outputs :: ctx.labels }
    let ct1 ← checkInstrs ctx' (produce emptyChecker inputs) body
    let ct1' ← consume ct1 outputs
    if ct1'.stack.isEmpty || ct1'.unreachable then
      .ok (produce ct0 outputs)
    else
      .error "block body leaves extra values on stack"
  | .loop bt body =>
    let (inputs, outputs) ← resolveBlockType ctx bt
    let ct0 ← consume ct inputs
    -- loop labels branch to the top, so label type = inputs
    let ctx' := { ctx with labels := inputs :: ctx.labels }
    let ct1 ← checkInstrs ctx' (produce emptyChecker inputs) body
    let ct1' ← consume ct1 outputs
    if ct1'.stack.isEmpty || ct1'.unreachable then
      .ok (produce ct0 outputs)
    else
      .error "loop body leaves extra values on stack"
  | .if_ bt then_ else_ =>
    let ct0 ← consume ct [.i32]
    let (inputs, outputs) ← resolveBlockType ctx bt
    let ct1 ← consume ct0 inputs
    let ctx' := { ctx with labels := outputs :: ctx.labels }
    let ctThen ← checkInstrs ctx' (produce emptyChecker inputs) then_
    let ctElse ← checkInstrs ctx' (produce emptyChecker inputs) else_
    let ctThen' ← consume ctThen outputs
    let ctElse' ← consume ctElse outputs
    if (ctThen'.stack.isEmpty || ctThen'.unreachable) &&
       (ctElse'.stack.isEmpty || ctElse'.unreachable) then
      .ok (produce ct1 outputs)
    else
      .error "if branches leave extra values on stack"
  | .br depth =>
    match ctx.labels[depth]? with
    | some labelTypes =>
      let _ ← consume ct labelTypes
      .ok { stack := [], unreachable := true }
    | none => .error s!"unknown label index {depth}"
  | .brIf depth =>
    match ctx.labels[depth]? with
    | some labelTypes =>
      let ct0 ← consume ct [.i32]
      let ct1 ← consume ct0 labelTypes
      .ok (produce ct1 labelTypes)
    | none => .error s!"unknown label index {depth}"
  | .brTable labels default_ =>
    let ct0 ← consume ct [.i32]
    match ctx.labels[default_]? with
    | some defaultTypes =>
      let _ ← consume ct0 defaultTypes
      for lbl in labels do
        match ctx.labels[lbl]? with
        | some lblTypes =>
          if lblTypes.length != defaultTypes.length then
            throw s!"br_table label arity mismatch"
          let _ ← consume ct0 lblTypes
        | none => throw s!"unknown label index {lbl}"
      .ok { stack := [], unreachable := true }
    | none => .error s!"unknown label index {default_}"
  | .return_ =>
    match ctx.return_ with
    | some retTypes =>
      let _ ← consume ct retTypes
      .ok { stack := [], unreachable := true }
    | none => .error "return outside of function"
  | .call idx =>
    match ctx.funcs[idx]? with
    | some ft => typeUpdate ct ft.params ft.results
    | none => .error s!"unknown function index {idx}"
  | .callIndirect typeIdx tableIdx =>
    if tableIdx >= ctx.tables.size then
      .error s!"unknown table index {tableIdx}"
    else
      match ctx.types[typeIdx]? with
      | some ft =>
        let ct0 ← consume ct [.i32]
        typeUpdate ct0 ft.params ft.results
      | none => .error s!"unknown type index {typeIdx}"

  -- Parametric
  | .drop =>
    if ct.stack.isEmpty then
      if ct.unreachable then .ok ct
      else .error "stack underflow in drop"
    else
      .ok { ct with stack := ct.stack.tail }
  | .select =>
    let ct0 ← consume ct [.i32]
    match ct0.stack with
    | t1 :: t2 :: rest =>
      if t1 == t2 then .ok { ct0 with stack := t1 :: rest }
      else .error s!"select type mismatch: {repr t1} vs {repr t2}"
    | _ =>
      if ct0.unreachable then .ok ct0
      else .error "stack underflow in select"

  -- Variables
  | .localGet idx =>
    match ctx.locals[idx]? with
    | some t => .ok (produce ct [t])
    | none => .error s!"unknown local index {idx}"
  | .localSet idx =>
    match ctx.locals[idx]? with
    | some t => consume ct [t]
    | none => .error s!"unknown local index {idx}"
  | .localTee idx =>
    match ctx.locals[idx]? with
    | some t =>
      let ct0 ← consume ct [t]
      .ok (produce ct0 [t])
    | none => .error s!"unknown local index {idx}"
  | .globalGet idx =>
    match ctx.globals[idx]? with
    | some gt => .ok (produce ct [gt.val])
    | none => .error s!"unknown global index {idx}"
  | .globalSet idx =>
    match ctx.globals[idx]? with
    | some gt =>
      if gt.mutability == .var then consume ct [gt.val]
      else .error s!"global {idx} is immutable"
    | none => .error s!"unknown global index {idx}"

  -- Memory loads
  | .i32Load _ | .i32Load8s _ | .i32Load8u _ | .i32Load16s _ | .i32Load16u _ =>
    typeUpdate ct [.i32] [.i32]
  | .i64Load _ | .i64Load8s _ | .i64Load8u _ | .i64Load16s _ | .i64Load16u _
  | .i64Load32s _ | .i64Load32u _ =>
    typeUpdate ct [.i32] [.i64]
  | .f32Load _ => typeUpdate ct [.i32] [.f32]
  | .f64Load _ => typeUpdate ct [.i32] [.f64]

  -- Memory stores
  | .i32Store _ | .i32Store8 _ | .i32Store16 _ =>
    consume ct [.i32, .i32]   -- addr, value (value on top)
  | .i64Store _ | .i64Store8 _ | .i64Store16 _ | .i64Store32 _ =>
    consume ct [.i64, .i32]
  | .f32Store _ => consume ct [.f32, .i32]
  | .f64Store _ => consume ct [.f64, .i32]

  | .memorySize _ => .ok (produce ct [.i32])
  | .memoryGrow _ => typeUpdate ct [.i32] [.i32]

  -- i32 constants and operations
  | .i32Const _ => .ok (produce ct [.i32])
  | .i32Eqz => typeUpdate ct [.i32] [.i32]
  | .i32Eq | .i32Ne
  | .i32Lts | .i32Ltu | .i32Gts | .i32Gtu
  | .i32Les | .i32Leu | .i32Ges | .i32Geu =>
    typeUpdate ct [.i32, .i32] [.i32]
  | .i32Clz | .i32Ctz | .i32Popcnt =>
    typeUpdate ct [.i32] [.i32]
  | .i32Add | .i32Sub | .i32Mul
  | .i32DivS | .i32DivU | .i32RemS | .i32RemU
  | .i32And | .i32Or | .i32Xor
  | .i32Shl | .i32ShrS | .i32ShrU | .i32Rotl | .i32Rotr =>
    typeUpdate ct [.i32, .i32] [.i32]

  -- i64 constants and operations
  | .i64Const _ => .ok (produce ct [.i64])
  | .i64Eqz => typeUpdate ct [.i64] [.i32]
  | .i64Eq | .i64Ne
  | .i64Lts | .i64Ltu | .i64Gts | .i64Gtu
  | .i64Les | .i64Leu | .i64Ges | .i64Geu =>
    typeUpdate ct [.i64, .i64] [.i32]
  | .i64Clz | .i64Ctz | .i64Popcnt =>
    typeUpdate ct [.i64] [.i64]
  | .i64Add | .i64Sub | .i64Mul
  | .i64DivS | .i64DivU | .i64RemS | .i64RemU
  | .i64And | .i64Or | .i64Xor
  | .i64Shl | .i64ShrS | .i64ShrU | .i64Rotl | .i64Rotr =>
    typeUpdate ct [.i64, .i64] [.i64]

  -- f32 constants and operations
  | .f32Const _ => .ok (produce ct [.f32])
  | .f32Eq | .f32Ne | .f32Lt | .f32Gt | .f32Le | .f32Ge =>
    typeUpdate ct [.f32, .f32] [.i32]
  | .f32Abs | .f32Neg | .f32Ceil | .f32Floor | .f32Trunc | .f32Nearest | .f32Sqrt =>
    typeUpdate ct [.f32] [.f32]
  | .f32Add | .f32Sub | .f32Mul | .f32Div | .f32Min | .f32Max | .f32Copysign =>
    typeUpdate ct [.f32, .f32] [.f32]

  -- f64 constants and operations
  | .f64Const _ => .ok (produce ct [.f64])
  | .f64Eq | .f64Ne | .f64Lt | .f64Gt | .f64Le | .f64Ge =>
    typeUpdate ct [.f64, .f64] [.i32]
  | .f64Abs | .f64Neg | .f64Ceil | .f64Floor | .f64Trunc | .f64Nearest | .f64Sqrt =>
    typeUpdate ct [.f64] [.f64]
  | .f64Add | .f64Sub | .f64Mul | .f64Div | .f64Min | .f64Max | .f64Copysign =>
    typeUpdate ct [.f64, .f64] [.f64]

  -- Conversions
  | .i32WrapI64 => typeUpdate ct [.i64] [.i32]
  | .i32TruncF32s | .i32TruncF32u => typeUpdate ct [.f32] [.i32]
  | .i32TruncF64s | .i32TruncF64u => typeUpdate ct [.f64] [.i32]
  | .i64ExtendI32s | .i64ExtendI32u => typeUpdate ct [.i32] [.i64]
  | .i64TruncF32s | .i64TruncF32u => typeUpdate ct [.f32] [.i64]
  | .i64TruncF64s | .i64TruncF64u => typeUpdate ct [.f64] [.i64]
  | .f32ConvertI32s | .f32ConvertI32u => typeUpdate ct [.i32] [.f32]
  | .f32ConvertI64s | .f32ConvertI64u => typeUpdate ct [.i64] [.f32]
  | .f32DemoteF64 => typeUpdate ct [.f64] [.f32]
  | .f64ConvertI32s | .f64ConvertI32u => typeUpdate ct [.i32] [.f64]
  | .f64ConvertI64s | .f64ConvertI64u => typeUpdate ct [.i64] [.f64]
  | .f64PromoteF32 => typeUpdate ct [.f32] [.f64]
  | .i32ReinterpretF32 => typeUpdate ct [.f32] [.i32]
  | .f32ReinterpretI32 => typeUpdate ct [.i32] [.f32]
  | .i64ReinterpretF64 => typeUpdate ct [.f64] [.i64]
  | .f64ReinterpretI64 => typeUpdate ct [.i64] [.f64]

  -- Bulk memory / table
  | .memoryInit dataIdx _ =>
    if dataIdx >= ctx.numDatas then .error s!"unknown data index {dataIdx}"
    else consume ct [.i32, .i32, .i32]
  | .dataDrop dataIdx =>
    if dataIdx >= ctx.numDatas then .error s!"unknown data index {dataIdx}"
    else .ok ct
  | .memoryCopy _ _ => consume ct [.i32, .i32, .i32]
  | .memoryFill _ => consume ct [.i32, .i32, .i32]
  | .tableInit elemIdx tableIdx =>
    if elemIdx >= ctx.numElems then .error s!"unknown elem index {elemIdx}"
    else if tableIdx >= ctx.tables.size then .error s!"unknown table index {tableIdx}"
    else consume ct [.i32, .i32, .i32]
  | .elemDrop elemIdx =>
    if elemIdx >= ctx.numElems then .error s!"unknown elem index {elemIdx}"
    else .ok ct
  | .tableCopy dst src =>
    if dst >= ctx.tables.size then .error s!"unknown table index {dst}"
    else if src >= ctx.tables.size then .error s!"unknown table index {src}"
    else consume ct [.i32, .i32, .i32]

/-- Type-check an instruction sequence (fold-left over instructions).
    REF: WasmCert-Coq `check` -/
def checkInstrs (ctx : ValCtx) (ct : CheckerType) (instrs : List Instr) :
    Except String CheckerType :=
  match instrs with
  | [] => .ok ct
  | i :: rest => do
    let ct' ← checkInstr ctx ct i
    checkInstrs ctx ct' rest
end

/-- Resolve the function types for imports. -/
private def importFuncTypes (m : Module) : Except String (Array FuncType) := do
  let mut result : Array FuncType := #[]
  for imp in m.imports do
    match imp.desc with
    | .func typeIdx =>
      match m.types[typeIdx]? with
      | some ft => result := result.push ft
      | none => throw s!"import references unknown type index {typeIdx}"
    | _ => pure ()
  .ok result

/-- Validate a function body against its type signature.
    REF: WasmCert-Coq `check_single` for block-like validation -/
private def validateFunc (ctx : ValCtx) (func : Func) : Except String Unit := do
  match ctx.types[func.typeIdx]? with
  | some ft =>
    let locals := ft.params ++ func.locals
    let ctx' := { ctx with
      locals := locals.toArray
      labels := [ft.results]
      return_ := some ft.results
    }
    let ct0 := produce emptyChecker ft.params
    let ctFinal ← checkInstrs ctx' ct0 func.body
    let ctEnd ← consume ctFinal ft.results
    if ctEnd.stack.isEmpty || ctEnd.unreachable then
      .ok ()
    else
      .error s!"function body leaves extra values on stack"
  | none => .error s!"function references unknown type index {func.typeIdx}"

/-- Validate a constant expression (used in globals, data/elem offsets). -/
private def validateConstExpr (ctx : ValCtx) (expr : Expr) (expected : ValType) :
    Except String Unit := do
  let ct ← checkInstrs ctx emptyChecker expr
  let _ ← consume ct [expected]
  .ok ()

/-- Validate a Wasm module.
    SPEC: WebAssembly 1.0 §3.10
    REF: WasmCert-Coq `type_checker.v` -/
def validate (m : Module) : Except String Unit := do
  -- Check memory count (MVP: at most 1)
  if m.memories.size > 1 then
    throw "multiple memories not supported in MVP"

  -- Resolve import function types
  let importFuncs ← importFuncTypes m

  -- Build full function type array: imports ++ module funcs
  let mut allFuncTypes : Array FuncType := importFuncs
  for func in m.funcs do
    match m.types[func.typeIdx]? with
    | some ft => allFuncTypes := allFuncTypes.push ft
    | none => throw s!"function references unknown type index {func.typeIdx}"

  -- Build validation context
  let ctx : ValCtx := {
    types := m.types
    funcs := allFuncTypes
    tables := m.tables
    memories := m.memories
    globals := m.globals.map (·.type)
    locals := #[]
    labels := []
    return_ := none
    numDatas := m.datas.size
    numElems := m.elems.size
  }

  -- Validate each function body
  for func in m.funcs do
    validateFunc ctx func

  -- Validate global initializers
  for g in m.globals do
    validateConstExpr ctx g.init g.type.val

  -- Validate start function index
  match m.start with
  | some idx =>
    if idx >= allFuncTypes.size then
      throw s!"start function index {idx} out of bounds"
  | none => pure ()

  -- Validate data segment offsets
  for ds in m.datas do
    if ds.memIdx >= m.memories.size then
      throw s!"data segment references unknown memory {ds.memIdx}"
    validateConstExpr ctx ds.offset .i32

  -- Validate element segment offsets
  for es in m.elems do
    if es.tableIdx >= m.tables.size then
      throw s!"element segment references unknown table {es.tableIdx}"
    validateConstExpr ctx es.offset .i32
    for funcIdx in es.funcIdxs do
      if funcIdx >= allFuncTypes.size then
        throw s!"element segment references unknown function {funcIdx}"

  .ok ()

end VerifiedJS.Wasm
