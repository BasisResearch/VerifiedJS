/-
  VerifiedJS — Lowering: JS.ANF → Wasm.IR
-/

import VerifiedJS.ANF.Syntax
import VerifiedJS.Runtime.Values
import VerifiedJS.Wasm.IR

namespace VerifiedJS.Wasm

open Std

abbrev RuntimeFuncIdx := Nat

-- Runtime helper dispatch table used by lowering.
-- These helpers model ECMA-262 runtime operations (e.g. property access and calls; §13, §7.3).
namespace RuntimeIdx

def hostFdWrite : RuntimeFuncIdx := 0
def base : RuntimeFuncIdx := 1
def call : RuntimeFuncIdx := base + 0
def construct : RuntimeFuncIdx := base + 1
def getProp : RuntimeFuncIdx := base + 2
def setProp : RuntimeFuncIdx := base + 3
def getIndex : RuntimeFuncIdx := base + 4
def setIndex : RuntimeFuncIdx := base + 5
def deleteProp : RuntimeFuncIdx := base + 6
def typeofOp : RuntimeFuncIdx := base + 7
def getEnv : RuntimeFuncIdx := base + 8
def makeEnv : RuntimeFuncIdx := base + 9
def makeClosure : RuntimeFuncIdx := base + 10
def objectLit : RuntimeFuncIdx := base + 11
def arrayLit : RuntimeFuncIdx := base + 12
def throwOp : RuntimeFuncIdx := base + 13
def yieldOp : RuntimeFuncIdx := base + 14
def awaitOp : RuntimeFuncIdx := base + 15
def toNumber : RuntimeFuncIdx := base + 16
def encodeNumber : RuntimeFuncIdx := base + 17
def truthy : RuntimeFuncIdx := base + 18
def encodeBool : RuntimeFuncIdx := base + 19
def unaryNeg : RuntimeFuncIdx := base + 20
def unaryPos : RuntimeFuncIdx := base + 21
def unaryLogNot : RuntimeFuncIdx := base + 22
def binaryAdd : RuntimeFuncIdx := base + 23
def binarySub : RuntimeFuncIdx := base + 24
def binaryMul : RuntimeFuncIdx := base + 25
def binaryDiv : RuntimeFuncIdx := base + 26
def binaryMod : RuntimeFuncIdx := base + 27
def binaryLt : RuntimeFuncIdx := base + 28
def binaryGt : RuntimeFuncIdx := base + 29
def binaryLe : RuntimeFuncIdx := base + 30
def binaryGe : RuntimeFuncIdx := base + 31
def binaryEq : RuntimeFuncIdx := base + 32
def binaryNeq : RuntimeFuncIdx := base + 33
def getGlobal : RuntimeFuncIdx := base + 34
def printValue : RuntimeFuncIdx := base + 35
def writeStrNl : RuntimeFuncIdx := base + 36
def logicalAnd : RuntimeFuncIdx := base + 37
def logicalOr : RuntimeFuncIdx := base + 38

end RuntimeIdx

private def hostImportCount : Nat := 1

/-! ## Runtime string table for typeof results and printValue.
    Stored in linear memory at offset 1024.
    String data (64 bytes), lookup table (56 bytes), extra strings. -/

private def runtimeStrBase : Nat := 1024
/-- Offset of "[object Object]" string in memory -/
private def runtimeStrObjObj : Nat := 1088
/-- Lookup table base: after string data (64) + "[object Object]" (15) + padding (1) = 80 -/
private def runtimeStrLookupBase : Nat := 1104  -- runtimeStrBase + 80

/-- Encode a Nat as a 4-byte little-endian ByteArray. -/
private def encodeLE32 (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (n % 256),
    UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat ((n / 65536) % 256),
    UInt8.ofNat ((n / 16777216) % 256)]

/-- Runtime string data segment: typeof strings, utility strings, and lookup table.
    Layout (offsets relative to runtimeStrBase = 1024):
    @0:  "true"(4) "false"(5) "null"(4) "undefined"(9) "number"(6)
         "boolean"(7) "string"(6) "object"(6) "function"(8) "symbol"(6) "NaN"(3)
    @64: "[object Object]" (15 bytes) + 1 byte padding
    @80: lookup table (7 entries × 8 bytes: offset_le32, length_le32)
    User string table entries are appended by buildStringDataSegment. -/
private def runtimeStringData : ByteArray :=
  -- String data (64 bytes total)
  "true".toUTF8 ++ "false".toUTF8 ++ "null".toUTF8 ++ "undefined".toUTF8 ++
  "number".toUTF8 ++ "boolean".toUTF8 ++ "string".toUTF8 ++ "object".toUTF8 ++
  "function".toUTF8 ++ "symbol".toUTF8 ++ "NaN".toUTF8 ++
  -- "[object Object]" at offset 64 from base (= 1088)
  "[object Object]".toUTF8 ++ ByteArray.mk #[0] ++  -- 15 bytes + 1 padding = 16
  -- Typeof lookup table at offset 80 from base (= 1104): ID → (memOffset, length)
  encodeLE32 1037 ++ encodeLE32 9 ++   -- ID 0 "undefined"
  encodeLE32 1052 ++ encodeLE32 7 ++   -- ID 1 "boolean"
  encodeLE32 1046 ++ encodeLE32 6 ++   -- ID 2 "number"
  encodeLE32 1059 ++ encodeLE32 6 ++   -- ID 3 "string"
  encodeLE32 1065 ++ encodeLE32 6 ++   -- ID 4 "object"
  encodeLE32 1071 ++ encodeLE32 8 ++   -- ID 5 "function"
  encodeLE32 1079 ++ encodeLE32 6      -- ID 6 "symbol"

/-- Number of pre-reserved typeof string IDs (0..6). User strings start at 7. -/
private def typeofStringCount : Nat := 7

structure LowerCtx where
  locals : List (ANF.VarName × Nat)
  consoleLogVars : List ANF.VarName := []
  /-- Variables bound to makeClosure(funcIdx, _), mapping name → Wasm function index. -/
  directCallVars : List (ANF.VarName × Nat) := []
  /-- Offset to add to ANF/Flat function indices to get Wasm function indices. -/
  funcOffset : Nat := 0
  deriving Inhabited

structure LowerState where
  nextLocal : Nat
  locals : Array IR.IRType
  nextStringId : Nat
  strings : List (String × Nat)
  nextLabelId : Nat
  deriving Inhabited

abbrev LowerM := StateT LowerState (Except String)

structure CtrlFrame where
  userLabel : Option String
  breakTarget : String
  continueTarget : Option String
  allowUnlabeledBreak : Bool
  allowUnlabeledContinue : Bool

private def lookupLocal (ctx : LowerCtx) (name : ANF.VarName) : Except String Nat :=
  match ctx.locals.find? (fun pair => pair.fst = name) with
  | some (_, idx) => .ok idx
  | none => .error s!"lower: unbound variable '{name}'"

private def allocLocal (name : ANF.VarName) (ctx : LowerCtx) : LowerM (Nat × LowerCtx) := do
  let st ← get
  let idx := st.nextLocal
  set { st with nextLocal := idx + 1, locals := st.locals.push .f64 }
  pure (idx, { ctx with locals := (name, idx) :: ctx.locals })

private def mkF64BitsConst (bits : UInt64) : IR.IRInstr :=
  IR.IRInstr.const_ .f64 s!"bits:{bits.toNat}"

private def mkBoxedConst (v : Runtime.NanBoxed) : IR.IRInstr :=
  mkF64BitsConst v.bits

private def encodeNatAsInt32 (n : Nat) : Runtime.NanBoxed :=
  Runtime.NanBoxed.encodeInt32 (Int32.ofInt (Int.ofNat n))

private def encodeBoolBox (b : Bool) : Runtime.NanBoxed :=
  Runtime.NanBoxed.encodeBool b

private def encodeUndefinedBox : Runtime.NanBoxed :=
  Runtime.NanBoxed.encodeUndefined

private def encodeNullBox : Runtime.NanBoxed :=
  Runtime.NanBoxed.encodeNull

private def internString (s : String) : LowerM Nat := do
  let st ← get
  match st.strings.find? (fun (name, _) => name = s) with
  | some (_, idx) => pure idx
  | none =>
      let idx := st.nextStringId
      set { st with nextStringId := idx + 1, strings := (s, idx) :: st.strings }
      pure idx

private def freshLabel (lblPrefix : String) : LowerM String := do
  let st ← get
  let n := st.nextLabelId
  set { st with nextLabelId := n + 1 }
  pure s!"{lblPrefix}_{n}"

private def mkStringRefConstM (s : String) : LowerM IR.IRInstr := do
  let sid ← internString s
  pure <| mkBoxedConst (Runtime.NanBoxed.encodeStringRef sid)

private def lowerUnaryOp : Core.UnaryOp → String
  | .neg => "neg"
  | .pos => "pos"
  | .bitNot => "bit_not"
  | .logNot => "log_not"
  | .void => "void"

private def lowerBinOp : Core.BinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .mod => "mod"
  | .exp => "exp"
  | .eq => "eq"
  | .neq => "neq"
  | .strictEq => "strict_eq"
  | .strictNeq => "strict_neq"
  | .lt => "lt"
  | .gt => "gt"
  | .le => "le"
  | .ge => "ge"
  | .bitAnd => "bit_and"
  | .bitOr => "bit_or"
  | .bitXor => "bit_xor"
  | .shl => "shl"
  | .shr => "shr"
  | .ushr => "ushr"
  | .logAnd => "log_and"
  | .logOr => "log_or"
  | .instanceof => "instanceof"
  | .in => "in"

private def lowerUnaryRuntime? : Core.UnaryOp → Option RuntimeFuncIdx
  | .neg => some RuntimeIdx.unaryNeg
  | .pos => some RuntimeIdx.unaryPos
  | .logNot => some RuntimeIdx.unaryLogNot
  | _ => none

private def lowerBinaryRuntime? : Core.BinOp → Option RuntimeFuncIdx
  | .add => some RuntimeIdx.binaryAdd
  | .sub => some RuntimeIdx.binarySub
  | .mul => some RuntimeIdx.binaryMul
  | .div => some RuntimeIdx.binaryDiv
  | .mod => some RuntimeIdx.binaryMod
  | .lt => some RuntimeIdx.binaryLt
  | .gt => some RuntimeIdx.binaryGt
  | .le => some RuntimeIdx.binaryLe
  | .ge => some RuntimeIdx.binaryGe
  | .eq | .strictEq => some RuntimeIdx.binaryEq
  | .neq | .strictNeq => some RuntimeIdx.binaryNeq
  | .logAnd => some RuntimeIdx.logicalAnd
  | .logOr => some RuntimeIdx.logicalOr
  | _ => none

private def drops (n : Nat) : List IR.IRInstr :=
  List.replicate n IR.IRInstr.drop

private def lowerTrivial (ctx : LowerCtx) : ANF.Trivial → LowerM (List IR.IRInstr)
  | .var name =>
      match lookupLocal ctx name with
      | .ok idx => pure [IR.IRInstr.localGet idx]
      | .error _ => do
          let globalName ← mkStringRefConstM name
          pure [globalName, IR.IRInstr.call RuntimeIdx.getGlobal]
  -- JS values are carried as NaN-boxed bit patterns reinterpreted as f64.
  | .litNull => pure [mkBoxedConst encodeNullBox]
  | .litUndefined => pure [mkBoxedConst encodeUndefinedBox]
  | .litBool b => pure [mkBoxedConst (encodeBoolBox b)]
  | .litNum n => pure [mkBoxedConst (Runtime.NanBoxed.encodeNumber n)]
  | .litStr s => do
      let sid ← internString s
      pure [mkBoxedConst (Runtime.NanBoxed.encodeStringRef sid)]
  | .litObject addr => pure [mkBoxedConst (Runtime.NanBoxed.encodeObjectRef addr)]
  | .litClosure funcIdx envPtr =>
      let wasmFuncIdx := funcIdx + ctx.funcOffset
      pure [mkBoxedConst (Runtime.NanBoxed.encodeObjectRef (wasmFuncIdx * 65536 + envPtr))]

private def lowerTrivialM (ctx : LowerCtx) (t : ANF.Trivial) : LowerM (List IR.IRInstr) :=
  lowerTrivial ctx t

private def lowerTrivialList (ctx : LowerCtx) (ts : List ANF.Trivial) : LowerM (List IR.IRInstr) := do
  let mut out := []
  for t in ts do
    out := out ++ (← lowerTrivialM ctx t)
  pure out

private partial def lowerComplex (ctx : LowerCtx) : ANF.ComplexExpr → LowerM (List IR.IRInstr)
  | .trivial t => lowerTrivialM ctx t
  | .assign name value => do
      let valueCode ← lowerTrivialM ctx value
      match lookupLocal ctx name with
      | .ok idx => pure (valueCode ++ [IR.IRInstr.localSet idx, IR.IRInstr.localGet idx])
      | .error _ =>
          -- Non-local assignment target (e.g. global): keep compilation total by preserving RHS value.
          pure valueCode
  | .call callee env args => do
      -- Detect console.log calls and emit printValue instead of generic call
      let isConsoleLog := match callee with
        | .var name => ctx.consoleLogVars.elem name
        | _ => false
      if isConsoleLog then do
        -- Print each argument, return undefined
        let mut code : List IR.IRInstr := []
        for arg in args do
          let argCode ← lowerTrivialM ctx arg
          code := code ++ argCode ++ [IR.IRInstr.call RuntimeIdx.printValue, IR.IRInstr.drop]
        pure (code ++ [mkBoxedConst encodeUndefinedBox])
      else do
        -- Check for direct function call (callee bound to makeClosure)
        let directFuncIdx := match callee with
          | .var name => ctx.directCallVars.find? (fun (n, _) => n == name) |>.map (·.2)
          | _ => none
        match directFuncIdx with
        | some funcIdx => do
            -- Direct call: push args + env param, call function directly
            let argsCode ← lowerTrivialList ctx args
            let envCode ← lowerTrivialM ctx env
            pure (argsCode ++ envCode ++ [IR.IRInstr.call funcIdx])
        | none => do
            let calleeCode ← lowerTrivialM ctx callee
            let envCode ← lowerTrivialM ctx env
            let firstArgCode ←
              match args with
              | a :: _ => lowerTrivialM ctx a
              | [] => pure [mkBoxedConst encodeUndefinedBox]
            let argsCode ← lowerTrivialList ctx args
            pure
              (calleeCode ++ envCode ++ firstArgCode ++ argsCode ++ drops args.length ++
                [IR.IRInstr.call RuntimeIdx.call])
  | .newObj callee env args => do
      let calleeCode ← lowerTrivialM ctx callee
      let envCode ← lowerTrivialM ctx env
      let argsCode ← lowerTrivialList ctx args
      pure
        (calleeCode ++ envCode ++ argsCode ++ drops args.length ++
          [IR.IRInstr.call RuntimeIdx.construct])
  | .getProp obj prop => do
      let objCode ← lowerTrivialM ctx obj
      let propCode ← mkStringRefConstM prop
      pure (objCode ++ [propCode, IR.IRInstr.call RuntimeIdx.getProp])
  | .setProp obj prop value => do
      let objCode ← lowerTrivialM ctx obj
      let valCode ← lowerTrivialM ctx value
      let propCode ← mkStringRefConstM prop
      pure
        (objCode ++ [propCode] ++ valCode ++
          [IR.IRInstr.call RuntimeIdx.setProp])
  | .getIndex obj idx => do
      let objCode ← lowerTrivialM ctx obj
      let idxCode ← lowerTrivialM ctx idx
      pure (objCode ++ idxCode ++ [IR.IRInstr.call RuntimeIdx.getIndex])
  | .setIndex obj idx value => do
      let objCode ← lowerTrivialM ctx obj
      let idxCode ← lowerTrivialM ctx idx
      let valCode ← lowerTrivialM ctx value
      pure (objCode ++ idxCode ++ valCode ++ [IR.IRInstr.call RuntimeIdx.setIndex])
  | .deleteProp obj prop => do
      let objCode ← lowerTrivialM ctx obj
      let propCode ← mkStringRefConstM prop
      pure (objCode ++ [propCode, IR.IRInstr.call RuntimeIdx.deleteProp])
  | .typeof arg => do
      let argCode ← lowerTrivialM ctx arg
      pure (argCode ++ [IR.IRInstr.call RuntimeIdx.typeofOp])
  | .getEnv env idx => do
      let envCode ← lowerTrivialM ctx env
      pure (envCode ++ [mkBoxedConst (encodeNatAsInt32 idx), IR.IRInstr.call RuntimeIdx.getEnv])
  | .makeEnv values => do
      let valuesCode ← lowerTrivialList ctx values
      pure (valuesCode ++ drops values.length ++ [IR.IRInstr.call RuntimeIdx.makeEnv])
  | .makeClosure funcIdx env => do
      let envCode ← lowerTrivialM ctx env
      let wasmFuncIdx := funcIdx + ctx.funcOffset
      pure
        ([mkBoxedConst (encodeNatAsInt32 wasmFuncIdx)] ++ envCode ++
          [IR.IRInstr.call RuntimeIdx.makeClosure])
  | .objectLit props => do
      let mut out := []
      for (prop, value) in props do
        let propCode ← mkStringRefConstM prop
        out := out ++ [propCode] ++ (← lowerTrivialM ctx value)
      pure (out ++ drops (2 * props.length) ++ [IR.IRInstr.call RuntimeIdx.objectLit])
  | .arrayLit elems => do
      let elemsCode ← lowerTrivialList ctx elems
      pure (elemsCode ++ drops elems.length ++ [IR.IRInstr.call RuntimeIdx.arrayLit])
  | .unary op arg => do
      let argCode ← lowerTrivialM ctx arg
      match lowerUnaryRuntime? op with
      | some fn => pure (argCode ++ [IR.IRInstr.call fn])
      | none => pure (argCode ++ [IR.IRInstr.unOp .f64 (lowerUnaryOp op)])
  | .binary op lhs rhs => do
      let lhsCode ← lowerTrivialM ctx lhs
      let rhsCode ← lowerTrivialM ctx rhs
      match lowerBinaryRuntime? op with
      | some fn => pure (lhsCode ++ rhsCode ++ [IR.IRInstr.call fn])
      | none => pure (lhsCode ++ rhsCode ++ [IR.IRInstr.binOp .f64 (lowerBinOp op)])

private def lookupBreakTarget (stack : List CtrlFrame) (label : Option String) : Option String :=
  match label with
  | some wanted =>
      (stack.find? (fun f => f.userLabel = some wanted)).map (·.breakTarget)
  | none =>
      (stack.find? (fun f => f.allowUnlabeledBreak)).map (·.breakTarget)

private def lookupContinueTarget (stack : List CtrlFrame) (label : Option String) : Option String :=
  match label with
  | some wanted =>
      match stack.find? (fun f => f.userLabel = some wanted) with
      | some f => f.continueTarget
      | none => none
  | none =>
      match stack.find? (fun f => f.allowUnlabeledContinue) with
      | some f => f.continueTarget
      | none => none

mutual

private partial def lowerExprWithExn (ctx : LowerCtx) (exnTarget : Option String)
    (ctrlStack : List CtrlFrame) :
    ANF.Expr → LowerM (List IR.IRInstr)
  | .trivial t => lowerTrivialM ctx t
  | .«let» name rhs body => do
      let rhsCode ← lowerComplex ctx rhs
      let (idx, ctx') ← allocLocal name ctx
      -- Detect special patterns for optimization
      let ctx' := match rhs with
        | .getProp (.var "console") "log" =>
            { ctx' with consoleLogVars := name :: ctx'.consoleLogVars }
        | .makeClosure funcIdx _ =>
            { ctx' with directCallVars := (name, funcIdx + ctx'.funcOffset) :: ctx'.directCallVars }
        | .trivial (.litClosure funcIdx _) =>
            { ctx' with directCallVars := (name, funcIdx + ctx'.funcOffset) :: ctx'.directCallVars }
        | _ => ctx'
      let bodyCode ← lowerExprWithExn ctx' exnTarget ctrlStack body
      pure (rhsCode ++ [IR.IRInstr.localSet idx] ++ bodyCode)
  | .seq a b => do
      let aCode ← lowerExprWithExn ctx exnTarget ctrlStack a
      let bCode ← lowerExprWithExn ctx exnTarget ctrlStack b
      pure (aCode ++ [IR.IRInstr.drop] ++ bCode)
  | .«if» cond then_ else_ => do
      let condCode ← lowerTrivialM ctx cond
      let thenCode ← lowerExprWithExn ctx exnTarget ctrlStack then_
      let elseCode ← lowerExprWithExn ctx exnTarget ctrlStack else_
      pure (condCode ++ [IR.IRInstr.call RuntimeIdx.truthy, IR.IRInstr.if_ (some .f64) thenCode elseCode])
  | .while_ cond body =>
      lowerWhile ctx exnTarget ctrlStack none cond body
  | .throw arg => do
      let argCode ← lowerTrivialM ctx arg
      let transfer :=
        match exnTarget with
        | some lbl => [IR.IRInstr.br lbl]
        | none => [IR.IRInstr.return_]
      pure (argCode ++ [IR.IRInstr.call RuntimeIdx.throwOp] ++ transfer)
  | .tryCatch body _ catchBody finally_ => do
      let catchLabel ← freshLabel "catch"
      let doneLabel ← freshLabel "try_done"
      let bodyCode ← lowerExprWithExn ctx (some catchLabel) ctrlStack body
      let catchCode ← lowerExprWithExn ctx exnTarget ctrlStack catchBody
      let finallyCode ←
        match finally_ with
        | some f => lowerExprWithExn ctx exnTarget ctrlStack f
        | none => pure []
      let tryCatchCode : List IR.IRInstr :=
        [IR.IRInstr.block doneLabel
          ([IR.IRInstr.block catchLabel (bodyCode ++ [IR.IRInstr.br doneLabel])] ++ catchCode)]
      pure (tryCatchCode ++ finallyCode)
  | .«return» arg =>
      match arg with
      | some v => do
          let code ← lowerTrivialM ctx v
          pure (code ++ [IR.IRInstr.return_])
      | none => pure [IR.IRInstr.return_]
  | .yield arg delegate => do
      let argCode ←
        match arg with
        | some v => lowerTrivialM ctx v
        | none => pure [mkBoxedConst encodeUndefinedBox]
      pure
        (argCode ++
          [mkBoxedConst (encodeBoolBox delegate), IR.IRInstr.call RuntimeIdx.yieldOp])
  | .await arg => do
      let argCode ← lowerTrivialM ctx arg
      pure (argCode ++ [IR.IRInstr.call RuntimeIdx.awaitOp])
  | .labeled label body => do
      match body with
      | .while_ cond loopBody =>
          lowerWhile ctx exnTarget ctrlStack (some label) cond loopBody
      | _ => do
          let exitLbl ← freshLabel s!"label_{label}"
          let frame : CtrlFrame :=
            { userLabel := some label
              breakTarget := exitLbl
              continueTarget := none
              allowUnlabeledBreak := false
              allowUnlabeledContinue := false }
          let bodyCode ← lowerExprWithExn ctx exnTarget (frame :: ctrlStack) body
          pure [IR.IRInstr.block exitLbl bodyCode]
  | .«break» label =>
      match lookupBreakTarget ctrlStack label with
      | some target => pure [IR.IRInstr.br target]
      | none => throw s!"lower: unresolved break target {label.getD "<unlabeled>"}"
  | .«continue» label =>
      match lookupContinueTarget ctrlStack label with
      | some target => pure [IR.IRInstr.br target]
      | none => throw s!"lower: unresolved continue target {label.getD "<unlabeled>"}"

private partial def lowerWhile (ctx : LowerCtx) (exnTarget : Option String) (ctrlStack : List CtrlFrame)
    (userLabel : Option String) (cond body : ANF.Expr) : LowerM (List IR.IRInstr) := do
  let exitLbl ← freshLabel "while_exit"
  let loopLbl ← freshLabel "while_loop"
  let frame : CtrlFrame :=
    { userLabel := userLabel
      breakTarget := exitLbl
      continueTarget := some loopLbl
      allowUnlabeledBreak := true
      allowUnlabeledContinue := true }
  let condCode ← lowerExprWithExn ctx exnTarget (frame :: ctrlStack) cond
  let bodyCode ← lowerExprWithExn ctx exnTarget (frame :: ctrlStack) body
  pure
    ([IR.IRInstr.block exitLbl
      [IR.IRInstr.loop loopLbl
        (condCode ++
          [IR.IRInstr.call RuntimeIdx.truthy, IR.IRInstr.unOp .i32 "eqz",
            IR.IRInstr.brIf exitLbl] ++
          bodyCode ++
          [IR.IRInstr.drop, IR.IRInstr.br loopLbl])]] ++
    [mkBoxedConst encodeUndefinedBox])

end

private partial def lowerExpr (ctx : LowerCtx) : ANF.Expr → LowerM (List IR.IRInstr) :=
  lowerExprWithExn ctx none []

private def mkInitialCtx (params : List ANF.VarName) (envParam : ANF.VarName)
    (funcOffset : Nat := 0) : LowerCtx :=
  let rec go (ps : List ANF.VarName) (idx : Nat) (acc : List (ANF.VarName × Nat)) :
      List (ANF.VarName × Nat) :=
    match ps with
    | [] => acc
    | p :: rest => go rest (idx + 1) ((p, idx) :: acc)
  let envIdx := params.length
  { locals := (envParam, envIdx) :: go params 0 [], funcOffset := funcOffset }

/-- String table state threaded across function lowerings. -/
structure StringTableState where
  nextStringId : Nat
  strings : List (String × Nat)

private def lowerFunctionWithStrings (f : ANF.FuncDef) (sts : StringTableState)
    (selfRef : Option (ANF.VarName × Nat) := none) (funcOffset : Nat := 0) :
    Except String (IR.IRFunc × StringTableState) := do
  let paramTypes := List.replicate (f.params.length + 1) IR.IRType.f64
  let initState : LowerState :=
    { nextLocal := paramTypes.length, locals := #[], nextStringId := sts.nextStringId,
      strings := sts.strings, nextLabelId := 0 }
  let ctx := mkInitialCtx f.params f.envParam funcOffset
  -- If a self-reference is provided, add it to directCallVars for recursive calls
  let ctx := match selfRef with
    | some (name, wasmIdx) => { ctx with directCallVars := (name, wasmIdx) :: ctx.directCallVars }
    | none => ctx
  let (body, st) ← (lowerExpr ctx f.body).run initState
  let func : IR.IRFunc :=
    { name := f.name
      params := paramTypes
      results := [IR.IRType.f64]
      locals := st.locals.toList
      body := body }
  pure (func, { nextStringId := st.nextStringId, strings := st.strings })

private def lowerFunction (f : ANF.FuncDef) : Except String IR.IRFunc := do
  let (func, _) ← lowerFunctionWithStrings f { nextStringId := typeofStringCount, strings := [] }
  pure func

/-- Build a preamble that binds each top-level function name to its closure value.
    funcIdx is the ANF/Flat function index (Wasm offset applied in lowerComplex). -/
private def buildFuncBindings (funcs : Array ANF.FuncDef) (mainBody : ANF.Expr) :
    ANF.Expr :=
  let rec go (i : Nat) (fns : List ANF.FuncDef) (body : ANF.Expr) : ANF.Expr :=
    match fns with
    | [] => body
    | f :: rest =>
      .«let» f.name (.makeClosure i (.litNull)) (go (i + 1) rest body)
  go 0 funcs.toList mainBody

private def runtimeHelpers : Array IR.IRFunc :=
  #[
    { name := "__rt_call", params := [.f64, .f64, .f64], results := [.f64], locals := [.i32]
      body :=
        [ -- local 0=callee, 1=env, 2=firstArg, 3=funcIdx(i32)
          -- Extract funcIdx from closure: payload / 65536
          IR.IRInstr.localGet 0
        , IR.IRInstr.unOp .i64 "reinterpret_f64"
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
        , IR.IRInstr.binOp .i64 "and"
        , IR.IRInstr.unOp .i32 "wrap_i64"
        , IR.IRInstr.const_ .i32 "65536"
        , IR.IRInstr.binOp .i32 "div_u"
        , IR.IRInstr.localSet 3
        -- Push params for called function: (firstArg, env), then table index
        , IR.IRInstr.localGet 2  -- firstArg (param 0 of callee)
        , IR.IRInstr.localGet 1  -- env (param 1 of callee)
        , IR.IRInstr.localGet 3  -- funcIdx as table index (i32)
        -- call_indirect with type (f64, f64) → f64 (type index 1 in typical emission)
        , IR.IRInstr.callIndirect 1
        , IR.IRInstr.return_ ] },
    { name := "__rt_construct", params := [.f64, .f64], results := [.f64], locals := [.i32]
      body :=
        [ -- Allocate empty object (same as objectLit for now)
          -- local 0=callee, local 1=env, local 2=heap_ptr
          IR.IRInstr.globalGet 0
        , IR.IRInstr.localSet 2
        -- Store count = 0
        , IR.IRInstr.localGet 2
        , IR.IRInstr.const_ .i32 "0"
        , IR.IRInstr.store .i32 0
        -- Bump heap pointer by 200 (4 + 16 slots × 12 bytes)
        , IR.IRInstr.localGet 2
        , IR.IRInstr.const_ .i32 "200"
        , IR.IRInstr.binOp .i32 "add"
        , IR.IRInstr.globalSet 0
        -- Return NaN-boxed object ref with heap address as payload
        , IR.IRInstr.localGet 2
        , IR.IRInstr.unOp .i64 "extend_i32_u"
        , IR.IRInstr.const_ .i64 s!"{(Runtime.NanBoxed.encodeObjectRef 0).bits.toNat}"
        , IR.IRInstr.binOp .i64 "or"
        , IR.IRInstr.unOp .f64 "reinterpret_i64"
        , IR.IRInstr.return_ ] },
    { name := "__rt_getProp", params := [.f64, .f64], results := [.f64]
      locals := [.i32, .i32, .i32, .i32, .i32]
      body :=
        [ -- local 0=obj, 1=propKeyRef, 2=obj_addr, 3=key_sid, 4=count, 5=i, 6=entry_addr
          -- Extract object address from NaN-boxed obj ref
          IR.IRInstr.localGet 0
        , IR.IRInstr.unOp .i64 "reinterpret_f64"
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
        , IR.IRInstr.binOp .i64 "and"
        , IR.IRInstr.unOp .i32 "wrap_i64"
        , IR.IRInstr.localSet 2
        -- Extract key string ID
        , IR.IRInstr.localGet 1
        , IR.IRInstr.unOp .i64 "reinterpret_f64"
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
        , IR.IRInstr.binOp .i64 "and"
        , IR.IRInstr.unOp .i32 "wrap_i64"
        , IR.IRInstr.localSet 3
        -- Read property count
        , IR.IRInstr.localGet 2
        , IR.IRInstr.load .i32 0
        , IR.IRInstr.localSet 4
        -- Search loop
        , IR.IRInstr.const_ .i32 "0"
        , IR.IRInstr.localSet 5
        , IR.IRInstr.block "prop_not_found"
            [ IR.IRInstr.loop "prop_search"
                [ -- if i >= count, break
                  IR.IRInstr.localGet 5
                , IR.IRInstr.localGet 4
                , IR.IRInstr.binOp .i32 "ge_u"
                , IR.IRInstr.brIf "prop_not_found"
                -- entry_addr = obj_addr + 4 + i * 12
                , IR.IRInstr.localGet 2
                , IR.IRInstr.const_ .i32 "4"
                , IR.IRInstr.binOp .i32 "add"
                , IR.IRInstr.localGet 5
                , IR.IRInstr.const_ .i32 "12"
                , IR.IRInstr.binOp .i32 "mul"
                , IR.IRInstr.binOp .i32 "add"
                , IR.IRInstr.localSet 6
                -- Compare key
                , IR.IRInstr.localGet 6
                , IR.IRInstr.load .i32 0
                , IR.IRInstr.localGet 3
                , IR.IRInstr.binOp .i32 "eq"
                , IR.IRInstr.if_ none
                    [ -- Found: return value at entry_addr + 4
                      IR.IRInstr.localGet 6
                    , IR.IRInstr.load .f64 4
                    , IR.IRInstr.return_ ] []
                -- i++
                , IR.IRInstr.localGet 5
                , IR.IRInstr.const_ .i32 "1"
                , IR.IRInstr.binOp .i32 "add"
                , IR.IRInstr.localSet 5
                , IR.IRInstr.br "prop_search"
                ]
            ]
        -- Not found: return undefined
        , mkBoxedConst encodeUndefinedBox
        , IR.IRInstr.return_ ] },
    { name := "__rt_setProp", params := [.f64, .f64, .f64], results := [.f64]
      locals := [.i32, .i32, .i32, .i32, .i32]
      body :=
        [ -- local 0=obj, 1=propKeyRef, 2=value, 3=obj_addr, 4=key_sid, 5=count, 6=i, 7=entry_addr
          -- Extract object address
          IR.IRInstr.localGet 0
        , IR.IRInstr.unOp .i64 "reinterpret_f64"
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
        , IR.IRInstr.binOp .i64 "and"
        , IR.IRInstr.unOp .i32 "wrap_i64"
        , IR.IRInstr.localSet 3
        -- Extract key string ID
        , IR.IRInstr.localGet 1
        , IR.IRInstr.unOp .i64 "reinterpret_f64"
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
        , IR.IRInstr.binOp .i64 "and"
        , IR.IRInstr.unOp .i32 "wrap_i64"
        , IR.IRInstr.localSet 4
        -- Read property count
        , IR.IRInstr.localGet 3
        , IR.IRInstr.load .i32 0
        , IR.IRInstr.localSet 5
        -- Search for existing property
        , IR.IRInstr.const_ .i32 "0"
        , IR.IRInstr.localSet 6
        , IR.IRInstr.block "set_append"
            [ IR.IRInstr.loop "set_search"
                [ IR.IRInstr.localGet 6
                , IR.IRInstr.localGet 5
                , IR.IRInstr.binOp .i32 "ge_u"
                , IR.IRInstr.brIf "set_append"
                -- entry_addr = obj_addr + 4 + i * 12
                , IR.IRInstr.localGet 3
                , IR.IRInstr.const_ .i32 "4"
                , IR.IRInstr.binOp .i32 "add"
                , IR.IRInstr.localGet 6
                , IR.IRInstr.const_ .i32 "12"
                , IR.IRInstr.binOp .i32 "mul"
                , IR.IRInstr.binOp .i32 "add"
                , IR.IRInstr.localSet 7
                -- Compare key
                , IR.IRInstr.localGet 7
                , IR.IRInstr.load .i32 0
                , IR.IRInstr.localGet 4
                , IR.IRInstr.binOp .i32 "eq"
                , IR.IRInstr.if_ none
                    [ -- Found: update value at entry_addr + 4
                      IR.IRInstr.localGet 7
                    , IR.IRInstr.localGet 2
                    , IR.IRInstr.store .f64 4
                    , IR.IRInstr.localGet 2
                    , IR.IRInstr.return_ ] []
                , IR.IRInstr.localGet 6
                , IR.IRInstr.const_ .i32 "1"
                , IR.IRInstr.binOp .i32 "add"
                , IR.IRInstr.localSet 6
                , IR.IRInstr.br "set_search"
                ]
            ]
        -- Append: new_entry_addr = obj_addr + 4 + count * 12
        , IR.IRInstr.localGet 3
        , IR.IRInstr.const_ .i32 "4"
        , IR.IRInstr.binOp .i32 "add"
        , IR.IRInstr.localGet 5
        , IR.IRInstr.const_ .i32 "12"
        , IR.IRInstr.binOp .i32 "mul"
        , IR.IRInstr.binOp .i32 "add"
        , IR.IRInstr.localSet 7
        -- Store key_sid
        , IR.IRInstr.localGet 7
        , IR.IRInstr.localGet 4
        , IR.IRInstr.store .i32 0
        -- Store value
        , IR.IRInstr.localGet 7
        , IR.IRInstr.localGet 2
        , IR.IRInstr.store .f64 4
        -- Increment count
        , IR.IRInstr.localGet 3
        , IR.IRInstr.localGet 5
        , IR.IRInstr.const_ .i32 "1"
        , IR.IRInstr.binOp .i32 "add"
        , IR.IRInstr.store .i32 0
        -- Return value
        , IR.IRInstr.localGet 2
        , IR.IRInstr.return_ ] },
    { name := "__rt_getIndex", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_setIndex", params := [.f64, .f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_deleteProp", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst (encodeBoolBox true), IR.IRInstr.return_] },
    { name := "__rt_typeof", params := [.f64], results := [.f64], locals := [.i64, .i64]
      body :=
        [ -- Reinterpret param as i64
          IR.IRInstr.localGet 0
        , IR.IRInstr.unOp .i64 "reinterpret_f64"
        , IR.IRInstr.localSet 1
        -- Check if NaN-boxed: (bits & nanMask) == nanMask
        , IR.IRInstr.localGet 1
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.nanMask.toNat}"
        , IR.IRInstr.binOp .i64 "and"
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.nanMask.toNat}"
        , IR.IRInstr.binOp .i64 "eq"
        , IR.IRInstr.if_ (some .f64)
            [ -- Tagged: extract tag
              IR.IRInstr.localGet 1
            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagMask.toNat}"
            , IR.IRInstr.binOp .i64 "and"
            , IR.IRInstr.localSet 2
            -- null → "object" (ECMA-262 §13.5.3: typeof null === "object")
            , IR.IRInstr.localGet 2
            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagNull.toNat}"
            , IR.IRInstr.binOp .i64 "eq"
            , IR.IRInstr.if_ (some .f64)
                [mkBoxedConst (Runtime.NanBoxed.encodeStringRef 4)]
                [ IR.IRInstr.localGet 2
                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagUndefined.toNat}"
                , IR.IRInstr.binOp .i64 "eq"
                , IR.IRInstr.if_ (some .f64)
                    [mkBoxedConst (Runtime.NanBoxed.encodeStringRef 0)] -- "undefined"
                    [ IR.IRInstr.localGet 2
                    , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagBool.toNat}"
                    , IR.IRInstr.binOp .i64 "eq"
                    , IR.IRInstr.if_ (some .f64)
                        [mkBoxedConst (Runtime.NanBoxed.encodeStringRef 1)] -- "boolean"
                        [ IR.IRInstr.localGet 2
                        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagInt32.toNat}"
                        , IR.IRInstr.binOp .i64 "eq"
                        , IR.IRInstr.if_ (some .f64)
                            [mkBoxedConst (Runtime.NanBoxed.encodeStringRef 2)] -- "number"
                            [ IR.IRInstr.localGet 2
                            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagString.toNat}"
                            , IR.IRInstr.binOp .i64 "eq"
                            , IR.IRInstr.if_ (some .f64)
                                [mkBoxedConst (Runtime.NanBoxed.encodeStringRef 3)] -- "string"
                                [ IR.IRInstr.localGet 2
                                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagObject.toNat}"
                                , IR.IRInstr.binOp .i64 "eq"
                                , IR.IRInstr.if_ (some .f64)
                                    [mkBoxedConst (Runtime.NanBoxed.encodeStringRef 4)] -- "object"
                                    [mkBoxedConst (Runtime.NanBoxed.encodeStringRef 6)] -- "symbol"
                                ]
                            ]
                        ]
                    ]
                ]
            ]
            -- Not tagged: number
            [mkBoxedConst (Runtime.NanBoxed.encodeStringRef 2)]
        , IR.IRInstr.return_ ] },
    { name := "__rt_getEnv", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_makeEnv", params := [], results := [.f64], locals := []
      body := [mkBoxedConst (Runtime.NanBoxed.encodeObjectRef 1), IR.IRInstr.return_] },
    { name := "__rt_makeClosure", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst (Runtime.NanBoxed.encodeObjectRef 2), IR.IRInstr.return_] },
    { name := "__rt_objectLit", params := [], results := [.f64], locals := [.i32]
      body :=
        [ -- Allocate empty object on heap
          IR.IRInstr.globalGet 0
        , IR.IRInstr.localSet 0
        -- Store count = 0
        , IR.IRInstr.localGet 0
        , IR.IRInstr.const_ .i32 "0"
        , IR.IRInstr.store .i32 0
        -- Bump heap pointer by 200
        , IR.IRInstr.localGet 0
        , IR.IRInstr.const_ .i32 "200"
        , IR.IRInstr.binOp .i32 "add"
        , IR.IRInstr.globalSet 0
        -- Return NaN-boxed object ref
        , IR.IRInstr.localGet 0
        , IR.IRInstr.unOp .i64 "extend_i32_u"
        , IR.IRInstr.const_ .i64 s!"{(Runtime.NanBoxed.encodeObjectRef 0).bits.toNat}"
        , IR.IRInstr.binOp .i64 "or"
        , IR.IRInstr.unOp .f64 "reinterpret_i64"
        , IR.IRInstr.return_ ] },
    { name := "__rt_arrayLit", params := [], results := [.f64], locals := []
      body := [mkBoxedConst (Runtime.NanBoxed.encodeObjectRef 4), IR.IRInstr.return_] },
    { name := "__rt_throw", params := [.f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_yield", params := [.f64, .f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] },
    { name := "__rt_await", params := [.f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] }
    ,
    { name := "__rt_toNumber", params := [.f64], results := [.f64], locals := [.i64, .i64]
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.unOp .i64 "reinterpret_f64"
        , IR.IRInstr.localSet 1
        , IR.IRInstr.localGet 1
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.nanMask.toNat}"
        , IR.IRInstr.binOp .i64 "and"
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.nanMask.toNat}"
        , IR.IRInstr.binOp .i64 "eq"
        , IR.IRInstr.if_ (some .f64)
            [ IR.IRInstr.localGet 1
            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagMask.toNat}"
            , IR.IRInstr.binOp .i64 "and"
            , IR.IRInstr.localSet 2
            , IR.IRInstr.localGet 2
            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagNull.toNat}"
            , IR.IRInstr.binOp .i64 "eq"
            , IR.IRInstr.if_ (some .f64)
                [IR.IRInstr.const_ .f64 "0.0"]
                [ IR.IRInstr.localGet 2
                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagUndefined.toNat}"
                , IR.IRInstr.binOp .i64 "eq"
                , IR.IRInstr.if_ (some .f64)
                    [mkBoxedConst (Runtime.NanBoxed.encodeNumber (0.0 / 0.0))]
                    [ IR.IRInstr.localGet 2
                    , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagBool.toNat}"
                    , IR.IRInstr.binOp .i64 "eq"
                    , IR.IRInstr.if_ (some .f64)
                        [ IR.IRInstr.localGet 1
                        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
                        , IR.IRInstr.binOp .i64 "and"
                        , IR.IRInstr.unOp .i64 "eqz"
                        , IR.IRInstr.unOp .i32 "eqz"
                        , IR.IRInstr.if_ (some .f64) [IR.IRInstr.const_ .f64 "1.0"] [IR.IRInstr.const_ .f64 "0.0"] ]
                        [ IR.IRInstr.localGet 2
                        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagInt32.toNat}"
                        , IR.IRInstr.binOp .i64 "eq"
                        , IR.IRInstr.if_ (some .f64)
                            [ IR.IRInstr.localGet 1
                            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
                            , IR.IRInstr.binOp .i64 "and"
                            , IR.IRInstr.unOp .i32 "wrap_i64"
                            , IR.IRInstr.unOp .f64 "convert_i32_s" ]
                            [mkBoxedConst (Runtime.NanBoxed.encodeNumber (0.0 / 0.0))] ] ] ] ]
            [IR.IRInstr.localGet 0]
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_encodeNumber", params := [.f64], results := [.f64], locals := []
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.localGet 0
        , IR.IRInstr.binOp .f64 "raw_eq"
        , IR.IRInstr.if_ (some .f64)
            [IR.IRInstr.localGet 0]
            [mkBoxedConst (Runtime.NanBoxed.encodeNumber (0.0 / 0.0))]
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_truthy", params := [.f64], results := [.i32], locals := [.i64, .i64]
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.unOp .i64 "reinterpret_f64"
        , IR.IRInstr.localSet 1
        , IR.IRInstr.localGet 1
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.nanMask.toNat}"
        , IR.IRInstr.binOp .i64 "and"
        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.nanMask.toNat}"
        , IR.IRInstr.binOp .i64 "eq"
        , IR.IRInstr.if_ (some .i32)
            [ IR.IRInstr.localGet 1
            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagMask.toNat}"
            , IR.IRInstr.binOp .i64 "and"
            , IR.IRInstr.localSet 2
            , IR.IRInstr.localGet 2
            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagNull.toNat}"
            , IR.IRInstr.binOp .i64 "eq"
            , IR.IRInstr.if_ (some .i32)
                [IR.IRInstr.const_ .i32 "0"]
                [ IR.IRInstr.localGet 2
                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagUndefined.toNat}"
                , IR.IRInstr.binOp .i64 "eq"
                , IR.IRInstr.if_ (some .i32)
                    [IR.IRInstr.const_ .i32 "0"]
                    [ IR.IRInstr.localGet 2
                    , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagBool.toNat}"
                    , IR.IRInstr.binOp .i64 "eq"
                    , IR.IRInstr.if_ (some .i32)
                        [ IR.IRInstr.localGet 1
                        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
                        , IR.IRInstr.binOp .i64 "and"
                        , IR.IRInstr.unOp .i64 "eqz"
                        , IR.IRInstr.unOp .i32 "eqz" ]
                        [ IR.IRInstr.localGet 2
                        , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagInt32.toNat}"
                        , IR.IRInstr.binOp .i64 "eq"
                        , IR.IRInstr.if_ (some .i32)
                            [ IR.IRInstr.localGet 1
                            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
                            , IR.IRInstr.binOp .i64 "and"
                            , IR.IRInstr.unOp .i64 "eqz"
                            , IR.IRInstr.unOp .i32 "eqz" ]
                            [IR.IRInstr.const_ .i32 "1"] ] ] ] ]
            [ IR.IRInstr.localGet 0
            , IR.IRInstr.localGet 0
            , IR.IRInstr.binOp .f64 "raw_eq"
            , IR.IRInstr.localGet 0
            , IR.IRInstr.const_ .f64 "0.0"
            , IR.IRInstr.binOp .f64 "raw_ne"
            , IR.IRInstr.binOp .i32 "and" ]
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_encodeBool", params := [.i32], results := [.f64], locals := []
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.if_ (some .f64)
            [mkBoxedConst (encodeBoolBox true)]
            [mkBoxedConst (encodeBoolBox false)]
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_unaryNeg", params := [.f64], results := [.f64], locals := []
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.call RuntimeIdx.toNumber
        , IR.IRInstr.unOp .f64 "neg_raw"
        , IR.IRInstr.call RuntimeIdx.encodeNumber
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_unaryPos", params := [.f64], results := [.f64], locals := []
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.call RuntimeIdx.toNumber
        , IR.IRInstr.call RuntimeIdx.encodeNumber
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_unaryLogNot", params := [.f64], results := [.f64], locals := []
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.call RuntimeIdx.truthy
        , IR.IRInstr.unOp .i32 "eqz"
        , IR.IRInstr.call RuntimeIdx.encodeBool
        , IR.IRInstr.return_ ] }
    ,
    { name := "__rt_binaryAdd", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "add_raw",
        IR.IRInstr.call RuntimeIdx.encodeNumber, IR.IRInstr.return_] }
    ,
    { name := "__rt_binarySub", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "sub_raw",
        IR.IRInstr.call RuntimeIdx.encodeNumber, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryMul", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "mul_raw",
        IR.IRInstr.call RuntimeIdx.encodeNumber, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryDiv", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "div_raw",
        IR.IRInstr.call RuntimeIdx.encodeNumber, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryMod", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "mod_raw",
        IR.IRInstr.call RuntimeIdx.encodeNumber, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryLt", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "raw_lt",
        IR.IRInstr.call RuntimeIdx.encodeBool, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryGt", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "raw_gt",
        IR.IRInstr.call RuntimeIdx.encodeBool, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryLe", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "raw_le",
        IR.IRInstr.call RuntimeIdx.encodeBool, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryGe", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "raw_ge",
        IR.IRInstr.call RuntimeIdx.encodeBool, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryEq", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "raw_eq",
        IR.IRInstr.call RuntimeIdx.encodeBool, IR.IRInstr.return_] }
    ,
    { name := "__rt_binaryNeq", params := [.f64, .f64], results := [.f64], locals := []
      body := [IR.IRInstr.localGet 0, IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.localGet 1,
        IR.IRInstr.call RuntimeIdx.toNumber, IR.IRInstr.binOp .f64 "raw_ne",
        IR.IRInstr.call RuntimeIdx.encodeBool, IR.IRInstr.return_] }
    ,
    { name := "__rt_getGlobal", params := [.f64], results := [.f64], locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_] }
    ,
    /- __rt_printValue: print NaN-boxed value to stdout with newline.
       Dispatches on NaN-boxing tag to handle all JS value types.
       param 0: f64 (NaN-boxed value)
       local 1: i64 (bits / integer value for digit loop)
       local 2: i64 (tag bits)
       local 3: i32 (buffer position for digit loop)
       local 4: i32 (isNegative flag / temp)
       Memory layout: iovec at 256, buffer at 268..300, newline at 300.
       String table at 1024 (runtimeStrBase). -/
    { name := "__rt_printValue", params := [.f64], results := [.f64]
      locals := [.i64, .i64, .i32, .i32]
      body :=
        [ -- Reinterpret param as i64
          IR.IRInstr.localGet 0
        , IR.IRInstr.unOp .i64 "reinterpret_f64"
        , IR.IRInstr.localSet 1
        -- Block wrapping type dispatch; br $to_int_print jumps to integer print path
        , IR.IRInstr.block "to_int_print"
            [ -- Check if NaN-boxed: (bits & nanMask) == nanMask
              IR.IRInstr.localGet 1
            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.nanMask.toNat}"
            , IR.IRInstr.binOp .i64 "and"
            , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.nanMask.toNat}"
            , IR.IRInstr.binOp .i64 "eq"
            , IR.IRInstr.if_ none
                [ -- TAGGED: extract tag
                  IR.IRInstr.localGet 1
                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagMask.toNat}"
                , IR.IRInstr.binOp .i64 "and"
                , IR.IRInstr.localSet 2
                -- Check null
                , IR.IRInstr.localGet 2
                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagNull.toNat}"
                , IR.IRInstr.binOp .i64 "eq"
                , IR.IRInstr.if_ none
                    [ IR.IRInstr.const_ .i32 "1033", IR.IRInstr.const_ .i32 "4"
                    , IR.IRInstr.call RuntimeIdx.writeStrNl
                    , IR.IRInstr.drop
                    , mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_ ] []
                -- Check undefined
                , IR.IRInstr.localGet 2
                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagUndefined.toNat}"
                , IR.IRInstr.binOp .i64 "eq"
                , IR.IRInstr.if_ none
                    [ IR.IRInstr.const_ .i32 "1037", IR.IRInstr.const_ .i32 "9"
                    , IR.IRInstr.call RuntimeIdx.writeStrNl
                    , IR.IRInstr.drop
                    , mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_ ] []
                -- Check bool
                , IR.IRInstr.localGet 2
                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagBool.toNat}"
                , IR.IRInstr.binOp .i64 "eq"
                , IR.IRInstr.if_ none
                    [ IR.IRInstr.localGet 1
                    , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
                    , IR.IRInstr.binOp .i64 "and"
                    , IR.IRInstr.unOp .i64 "eqz"
                    , IR.IRInstr.if_ none
                        [ IR.IRInstr.const_ .i32 "1028", IR.IRInstr.const_ .i32 "5"
                        , IR.IRInstr.call RuntimeIdx.writeStrNl, IR.IRInstr.drop ]
                        [ IR.IRInstr.const_ .i32 "1024", IR.IRInstr.const_ .i32 "4"
                        , IR.IRInstr.call RuntimeIdx.writeStrNl, IR.IRInstr.drop ]
                    , mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_ ] []
                -- Check int32: extract payload, sign-extend, jump to int print
                , IR.IRInstr.localGet 2
                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagInt32.toNat}"
                , IR.IRInstr.binOp .i64 "eq"
                , IR.IRInstr.if_ none
                    [ IR.IRInstr.localGet 1
                    , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
                    , IR.IRInstr.binOp .i64 "and"
                    , IR.IRInstr.unOp .i32 "wrap_i64"
                    , IR.IRInstr.unOp .i64 "extend_i32_s"
                    , IR.IRInstr.localSet 1
                    , IR.IRInstr.br "to_int_print" ] []
                -- Check string ref: lookup in typeof string table
                , IR.IRInstr.localGet 2
                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagString.toNat}"
                , IR.IRInstr.binOp .i64 "eq"
                , IR.IRInstr.if_ none
                    [ IR.IRInstr.localGet 1
                    , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.payloadMask.toNat}"
                    , IR.IRInstr.binOp .i64 "and"
                    , IR.IRInstr.unOp .i32 "wrap_i64"  -- string ID (i32)
                    , IR.IRInstr.const_ .i32 "8"
                    , IR.IRInstr.binOp .i32 "mul"
                    , IR.IRInstr.const_ .i32 s!"{runtimeStrLookupBase}"
                    , IR.IRInstr.binOp .i32 "add"
                    , IR.IRInstr.localSet 3  -- table entry address
                    , IR.IRInstr.localGet 3
                    , IR.IRInstr.load .i32 0   -- str_offset
                    , IR.IRInstr.localGet 3
                    , IR.IRInstr.load .i32 4   -- str_length
                    , IR.IRInstr.call RuntimeIdx.writeStrNl
                    , IR.IRInstr.drop
                    , mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_ ] []
                -- Check object ref
                , IR.IRInstr.localGet 2
                , IR.IRInstr.const_ .i64 s!"{Runtime.NanBoxed.tagObject.toNat}"
                , IR.IRInstr.binOp .i64 "eq"
                , IR.IRInstr.if_ none
                    [ IR.IRInstr.const_ .i32 s!"{runtimeStrObjObj}", IR.IRInstr.const_ .i32 "15"
                    , IR.IRInstr.call RuntimeIdx.writeStrNl
                    , IR.IRInstr.drop
                    , mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_ ] []
                -- Default (symbol etc.): print "undefined"
                , IR.IRInstr.const_ .i32 "1037", IR.IRInstr.const_ .i32 "9"
                , IR.IRInstr.call RuntimeIdx.writeStrNl
                , IR.IRInstr.drop
                , mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_
                ]
                [ -- NOT TAGGED: it's a number (f64)
                  -- Check for NaN: param != param
                  IR.IRInstr.localGet 0
                , IR.IRInstr.localGet 0
                , IR.IRInstr.binOp .f64 "raw_ne"
                , IR.IRInstr.if_ none
                    [ IR.IRInstr.const_ .i32 "1085", IR.IRInstr.const_ .i32 "3"
                    , IR.IRInstr.call RuntimeIdx.writeStrNl
                    , IR.IRInstr.drop
                    , mkBoxedConst encodeUndefinedBox, IR.IRInstr.return_ ] []
                -- Not NaN: truncate to i64 for integer printing
                , IR.IRInstr.localGet 0
                , IR.IRInstr.unOp .i64 "trunc_f64_s"
                , IR.IRInstr.localSet 1
                , IR.IRInstr.br "to_int_print"
                ]
            ]
        -- INTEGER PRINT PATH: local 1 has signed i64 value
        -- Check if negative
        , IR.IRInstr.localGet 1
        , IR.IRInstr.const_ .i64 "0"
        , IR.IRInstr.binOp .i64 "lt"
        , IR.IRInstr.localSet 4
        -- If negative, negate
        , IR.IRInstr.localGet 4
        , IR.IRInstr.if_ none
            [ IR.IRInstr.const_ .i64 "0"
            , IR.IRInstr.localGet 1
            , IR.IRInstr.binOp .i64 "sub"
            , IR.IRInstr.localSet 1
            ] []
        -- Init buffer position at 299
        , IR.IRInstr.const_ .i32 "299"
        , IR.IRInstr.localSet 3
        -- Digit loop
        , IR.IRInstr.loop "digit_loop"
            [ IR.IRInstr.localGet 3
            , IR.IRInstr.localGet 1
            , IR.IRInstr.const_ .i64 "10"
            , IR.IRInstr.binOp .i64 "rem_u"
            , IR.IRInstr.unOp .i32 "wrap_i64"
            , IR.IRInstr.const_ .i32 "48"
            , IR.IRInstr.binOp .i32 "add"
            , IR.IRInstr.store8 0
            , IR.IRInstr.localGet 3
            , IR.IRInstr.const_ .i32 "1"
            , IR.IRInstr.binOp .i32 "sub"
            , IR.IRInstr.localSet 3
            , IR.IRInstr.localGet 1
            , IR.IRInstr.const_ .i64 "10"
            , IR.IRInstr.binOp .i64 "div_u"
            , IR.IRInstr.localSet 1
            , IR.IRInstr.localGet 1
            , IR.IRInstr.const_ .i64 "0"
            , IR.IRInstr.binOp .i64 "neq"
            , IR.IRInstr.brIf "digit_loop"
            ]
        -- Negative sign
        , IR.IRInstr.localGet 4
        , IR.IRInstr.if_ none
            [ IR.IRInstr.localGet 3
            , IR.IRInstr.const_ .i32 "45"
            , IR.IRInstr.store8 0
            , IR.IRInstr.localGet 3
            , IR.IRInstr.const_ .i32 "1"
            , IR.IRInstr.binOp .i32 "sub"
            , IR.IRInstr.localSet 3
            ] []
        -- Write newline at 300
        , IR.IRInstr.const_ .i32 "300"
        , IR.IRInstr.const_ .i32 "10"
        , IR.IRInstr.store8 0
        -- Set up iovec
        , IR.IRInstr.const_ .i32 "256"
        , IR.IRInstr.localGet 3
        , IR.IRInstr.const_ .i32 "1"
        , IR.IRInstr.binOp .i32 "add"
        , IR.IRInstr.store .i32 0
        , IR.IRInstr.const_ .i32 "260"
        , IR.IRInstr.const_ .i32 "301"
        , IR.IRInstr.localGet 3
        , IR.IRInstr.const_ .i32 "1"
        , IR.IRInstr.binOp .i32 "add"
        , IR.IRInstr.binOp .i32 "sub"
        , IR.IRInstr.store .i32 0
        -- fd_write
        , IR.IRInstr.const_ .i32 "1"
        , IR.IRInstr.const_ .i32 "256"
        , IR.IRInstr.const_ .i32 "1"
        , IR.IRInstr.const_ .i32 "264"
        , IR.IRInstr.call RuntimeIdx.hostFdWrite
        , IR.IRInstr.drop
        , mkBoxedConst encodeUndefinedBox
        , IR.IRInstr.return_
        ] }
    ,
    /- __rt_writeStrNl: write string at mem[offset..offset+length] followed by newline to stdout.
       param 0: i32 (memory offset of string)
       param 1: i32 (length in bytes)
       Uses iovec area at 256, newline byte at 300. -/
    { name := "__rt_writeStrNl", params := [.i32, .i32], results := [.f64], locals := []
      body :=
        [ -- Set up iovec for string at 256
          IR.IRInstr.const_ .i32 "256"
        , IR.IRInstr.localGet 0
        , IR.IRInstr.store .i32 0
        , IR.IRInstr.const_ .i32 "260"
        , IR.IRInstr.localGet 1
        , IR.IRInstr.store .i32 0
        -- fd_write string
        , IR.IRInstr.const_ .i32 "1"
        , IR.IRInstr.const_ .i32 "256"
        , IR.IRInstr.const_ .i32 "1"
        , IR.IRInstr.const_ .i32 "264"
        , IR.IRInstr.call RuntimeIdx.hostFdWrite
        , IR.IRInstr.drop
        -- Write newline at 300
        , IR.IRInstr.const_ .i32 "300"
        , IR.IRInstr.const_ .i32 "10"
        , IR.IRInstr.store8 0
        -- Set up iovec for newline
        , IR.IRInstr.const_ .i32 "256"
        , IR.IRInstr.const_ .i32 "300"
        , IR.IRInstr.store .i32 0
        , IR.IRInstr.const_ .i32 "260"
        , IR.IRInstr.const_ .i32 "1"
        , IR.IRInstr.store .i32 0
        -- fd_write newline
        , IR.IRInstr.const_ .i32 "1"
        , IR.IRInstr.const_ .i32 "256"
        , IR.IRInstr.const_ .i32 "1"
        , IR.IRInstr.const_ .i32 "264"
        , IR.IRInstr.call RuntimeIdx.hostFdWrite
        , IR.IRInstr.drop
        , mkBoxedConst encodeUndefinedBox
        , IR.IRInstr.return_ ] }
    ,
    -- logicalAnd(a, b): if truthy(a) then b else a
    { name := "__rt_logicalAnd", params := [.f64, .f64], results := [.f64], locals := []
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.call RuntimeIdx.truthy
        , IR.IRInstr.if_ (some .f64)
            [IR.IRInstr.localGet 1]
            [IR.IRInstr.localGet 0]
        , IR.IRInstr.return_ ] }
    ,
    -- logicalOr(a, b): if truthy(a) then a else b
    { name := "__rt_logicalOr", params := [.f64, .f64], results := [.f64], locals := []
      body :=
        [ IR.IRInstr.localGet 0
        , IR.IRInstr.call RuntimeIdx.truthy
        , IR.IRInstr.if_ (some .f64)
            [IR.IRInstr.localGet 0]
            [IR.IRInstr.localGet 1]
        , IR.IRInstr.return_ ] }
  ]

/-- Build a complete string table data segment from typeof strings + user-interned strings. -/
private def buildStringDataSegment (userStrings : List (String × Nat)) : ByteArray :=
  -- First: typeof strings + lookup table + "[object Object]" (runtimeStringData = 135 bytes)
  -- Then: user string lookup table entries (for IDs >= typeofStringCount)
  -- Then: user string data
  let sortedUserStrings := userStrings.toArray.qsort (fun a b => a.2 < b.2)
  -- Compute user string data offset: after runtimeStringData + user lookup table
  let userTableBytes := sortedUserStrings.size * 8  -- each entry: (offset_le32, length_le32)
  let userDataStart := runtimeStrBase + runtimeStringData.size + userTableBytes
  -- Build user string data and lookup table
  let (userTable, userData, _) := sortedUserStrings.foldl (init := (ByteArray.empty, ByteArray.empty, userDataStart))
    fun (table, data, offset) (s, _) =>
      let sBytes := s.toUTF8
      let entry := encodeLE32 offset ++ encodeLE32 sBytes.size
      (table ++ entry, data ++ sBytes, offset + sBytes.size)
  runtimeStringData ++ userTable ++ userData

def lower (prog : ANF.Program) : Except String IR.IRModule := do
  let runtimeCount := runtimeHelpers.size
  -- Thread string table state through all function lowerings
  let initStrState : StringTableState := { nextStringId := typeofStringCount, strings := [] }
  let funcOffset := hostImportCount + runtimeCount
  let funcList := prog.functions.toList
  let (loweredFns, strState) ← funcList.zipIdx.foldlM
    (init := ([], initStrState))
    fun (fns, sts) (f, i) => do
      let wasmIdx := funcOffset + i
      let (fn, sts') ← lowerFunctionWithStrings f sts (some (f.name, wasmIdx)) funcOffset
      pure (fns ++ [fn], sts')
  -- Wrap main body with top-level function bindings (funcIdx offset applied in lowerComplex)
  let wrappedMain := buildFuncBindings prog.functions prog.main
  let mainFn : ANF.FuncDef :=
    { name := "__verifiedjs_main"
      params := []
      envParam := "__env"
      body := wrappedMain }
  let (loweredMain, finalStrState) ← lowerFunctionWithStrings mainFn strState (funcOffset := funcOffset)
  let mainIdx := hostImportCount + runtimeCount + loweredFns.length
  -- Create a _start wrapper with zero params/results (Wasm spec requires this for start func)
  let startWrapper : IR.IRFunc :=
    { name := "_start"
      params := []
      results := []
      locals := []
      body := [mkBoxedConst encodeUndefinedBox, IR.IRInstr.call mainIdx, IR.IRInstr.drop] }
  let startIdx := mainIdx + 1
  let functions := runtimeHelpers ++ loweredFns.toArray ++ #[loweredMain, startWrapper]
  -- Build complete string data segment including user strings
  let stringData := buildStringDataSegment finalStrState.strings
  -- Build function table for call_indirect: all functions in the module
  let totalFuncs := functions.size
  let tableEntries := Array.ofFn (n := totalFuncs) (fun i => i.val)
  pure
    { functions := functions
      memories := #[{ lim := { min := 1, max := none } }]
      globals := #[(.i32, true, s!"{runtimeStrBase + stringData.size}")]
      exports := #[("main", mainIdx), ("_start", startIdx)]
      dataSegments := #[(runtimeStrBase, stringData)]
      startFunc := none
      tableEntries := tableEntries }

/-- Successful lowering produces a module with no Wasm start section (WASI uses _start export). -/
theorem lower_startFunc_none (prog : ANF.Program) (t : IR.IRModule)
    (h : lower prog = .ok t) :
    t.startFunc = none := by
  simp only [lower, Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at h; rw [← h]

/-- Successful lowering always exports `main` and `_start` with computed indices. -/
theorem lower_exports_shape (prog : ANF.Program) (t : IR.IRModule)
    (h : lower prog = .ok t) :
    ∃ mainIdx startIdx, t.exports = #[("main", mainIdx), ("_start", startIdx)] := by
  simp only [lower, Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
      rw [← h]
      exact ⟨_, _, rfl⟩

/-- Successful lowering always produces the canonical single-memory declaration. -/
theorem lower_memory_shape (prog : ANF.Program) (t : IR.IRModule)
    (h : lower prog = .ok t) :
    t.memories = #[{ lim := { min := 1, max := none } }] := by
  simp only [lower, Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at h; rw [← h]

end VerifiedJS.Wasm
