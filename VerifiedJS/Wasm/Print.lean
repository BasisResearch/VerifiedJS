/-
  VerifiedJS — WAT (WebAssembly Text Format) Printer
-/

import VerifiedJS.Wasm.Syntax

namespace VerifiedJS.Wasm

private def printValType : ValType → String
  | .i32 => "i32"
  | .i64 => "i64"
  | .f32 => "f32"
  | .f64 => "f64"

private def printBlockType : BlockType → String
  | .none => ""
  | .valType t => " (result " ++ printValType t ++ ")"
  | .typeIdx idx => " (type " ++ toString idx ++ ")"

private def printMemArg (ma : MemArg) : String :=
  let o := if ma.offset == 0 then "" else " offset=" ++ toString ma.offset
  let a := if ma.align == 0 then "" else " align=" ++ toString ma.align
  o ++ a

private partial def printInstr (depth : Nat) : Instr → String
  | .unreachable => indent depth ++ "unreachable"
  | .nop => indent depth ++ "nop"
  | .block bt body =>
    indent depth ++ "(block" ++ printBlockType bt ++ "\n" ++
    printInstrs (depth + 1) body ++
    indent depth ++ ")"
  | .loop bt body =>
    indent depth ++ "(loop" ++ printBlockType bt ++ "\n" ++
    printInstrs (depth + 1) body ++
    indent depth ++ ")"
  | .if_ bt then_ else_ =>
    indent depth ++ "(if" ++ printBlockType bt ++ "\n" ++
    indent (depth + 1) ++ "(then\n" ++
    printInstrs (depth + 2) then_ ++
    indent (depth + 1) ++ ")\n" ++
    indent (depth + 1) ++ "(else\n" ++
    printInstrs (depth + 2) else_ ++
    indent (depth + 1) ++ ")\n" ++
    indent depth ++ ")"
  | .br idx => indent depth ++ "br " ++ toString idx
  | .brIf idx => indent depth ++ "br_if " ++ toString idx
  | .brTable labels default_ =>
    indent depth ++ "br_table " ++
    " ".intercalate (labels.map toString) ++ " " ++ toString default_
  | .return_ => indent depth ++ "return"
  | .call idx => indent depth ++ "call " ++ toString idx
  | .callIndirect tidx tabIdx =>
    indent depth ++ "call_indirect " ++ toString tabIdx ++ " (type " ++ toString tidx ++ ")"
  | .drop => indent depth ++ "drop"
  | .select => indent depth ++ "select"
  | .localGet idx => indent depth ++ "local.get " ++ toString idx
  | .localSet idx => indent depth ++ "local.set " ++ toString idx
  | .localTee idx => indent depth ++ "local.tee " ++ toString idx
  | .globalGet idx => indent depth ++ "global.get " ++ toString idx
  | .globalSet idx => indent depth ++ "global.set " ++ toString idx
  | .i32Load ma => indent depth ++ "i32.load" ++ printMemArg ma
  | .i64Load ma => indent depth ++ "i64.load" ++ printMemArg ma
  | .f32Load ma => indent depth ++ "f32.load" ++ printMemArg ma
  | .f64Load ma => indent depth ++ "f64.load" ++ printMemArg ma
  | .i32Load8s ma => indent depth ++ "i32.load8_s" ++ printMemArg ma
  | .i32Load8u ma => indent depth ++ "i32.load8_u" ++ printMemArg ma
  | .i32Load16s ma => indent depth ++ "i32.load16_s" ++ printMemArg ma
  | .i32Load16u ma => indent depth ++ "i32.load16_u" ++ printMemArg ma
  | .i64Load8s ma => indent depth ++ "i64.load8_s" ++ printMemArg ma
  | .i64Load8u ma => indent depth ++ "i64.load8_u" ++ printMemArg ma
  | .i64Load16s ma => indent depth ++ "i64.load16_s" ++ printMemArg ma
  | .i64Load16u ma => indent depth ++ "i64.load16_u" ++ printMemArg ma
  | .i64Load32s ma => indent depth ++ "i64.load32_s" ++ printMemArg ma
  | .i64Load32u ma => indent depth ++ "i64.load32_u" ++ printMemArg ma
  | .i32Store ma => indent depth ++ "i32.store" ++ printMemArg ma
  | .i64Store ma => indent depth ++ "i64.store" ++ printMemArg ma
  | .f32Store ma => indent depth ++ "f32.store" ++ printMemArg ma
  | .f64Store ma => indent depth ++ "f64.store" ++ printMemArg ma
  | .i32Store8 ma => indent depth ++ "i32.store8" ++ printMemArg ma
  | .i32Store16 ma => indent depth ++ "i32.store16" ++ printMemArg ma
  | .i64Store8 ma => indent depth ++ "i64.store8" ++ printMemArg ma
  | .i64Store16 ma => indent depth ++ "i64.store16" ++ printMemArg ma
  | .i64Store32 ma => indent depth ++ "i64.store32" ++ printMemArg ma
  | .memorySize _ => indent depth ++ "memory.size"
  | .memoryGrow _ => indent depth ++ "memory.grow"
  | .i32Const n => indent depth ++ "i32.const " ++ toString n.toNat
  | .i32Eqz => indent depth ++ "i32.eqz"
  | .i32Eq => indent depth ++ "i32.eq"
  | .i32Ne => indent depth ++ "i32.ne"
  | .i32Lts => indent depth ++ "i32.lt_s"
  | .i32Ltu => indent depth ++ "i32.lt_u"
  | .i32Gts => indent depth ++ "i32.gt_s"
  | .i32Gtu => indent depth ++ "i32.gt_u"
  | .i32Les => indent depth ++ "i32.le_s"
  | .i32Leu => indent depth ++ "i32.le_u"
  | .i32Ges => indent depth ++ "i32.ge_s"
  | .i32Geu => indent depth ++ "i32.ge_u"
  | .i32Clz => indent depth ++ "i32.clz"
  | .i32Ctz => indent depth ++ "i32.ctz"
  | .i32Popcnt => indent depth ++ "i32.popcnt"
  | .i32Add => indent depth ++ "i32.add"
  | .i32Sub => indent depth ++ "i32.sub"
  | .i32Mul => indent depth ++ "i32.mul"
  | .i32DivS => indent depth ++ "i32.div_s"
  | .i32DivU => indent depth ++ "i32.div_u"
  | .i32RemS => indent depth ++ "i32.rem_s"
  | .i32RemU => indent depth ++ "i32.rem_u"
  | .i32And => indent depth ++ "i32.and"
  | .i32Or => indent depth ++ "i32.or"
  | .i32Xor => indent depth ++ "i32.xor"
  | .i32Shl => indent depth ++ "i32.shl"
  | .i32ShrS => indent depth ++ "i32.shr_s"
  | .i32ShrU => indent depth ++ "i32.shr_u"
  | .i32Rotl => indent depth ++ "i32.rotl"
  | .i32Rotr => indent depth ++ "i32.rotr"
  | .i64Const n => indent depth ++ "i64.const " ++ toString n.toNat
  | .i64Eqz => indent depth ++ "i64.eqz"
  | .i64Eq => indent depth ++ "i64.eq"
  | .i64Ne => indent depth ++ "i64.ne"
  | .i64Lts => indent depth ++ "i64.lt_s"
  | .i64Ltu => indent depth ++ "i64.lt_u"
  | .i64Gts => indent depth ++ "i64.gt_s"
  | .i64Gtu => indent depth ++ "i64.gt_u"
  | .i64Les => indent depth ++ "i64.le_s"
  | .i64Leu => indent depth ++ "i64.le_u"
  | .i64Ges => indent depth ++ "i64.ge_s"
  | .i64Geu => indent depth ++ "i64.ge_u"
  | .i64Clz => indent depth ++ "i64.clz"
  | .i64Ctz => indent depth ++ "i64.ctz"
  | .i64Popcnt => indent depth ++ "i64.popcnt"
  | .i64Add => indent depth ++ "i64.add"
  | .i64Sub => indent depth ++ "i64.sub"
  | .i64Mul => indent depth ++ "i64.mul"
  | .i64DivS => indent depth ++ "i64.div_s"
  | .i64DivU => indent depth ++ "i64.div_u"
  | .i64RemS => indent depth ++ "i64.rem_s"
  | .i64RemU => indent depth ++ "i64.rem_u"
  | .i64And => indent depth ++ "i64.and"
  | .i64Or => indent depth ++ "i64.or"
  | .i64Xor => indent depth ++ "i64.xor"
  | .i64Shl => indent depth ++ "i64.shl"
  | .i64ShrS => indent depth ++ "i64.shr_s"
  | .i64ShrU => indent depth ++ "i64.shr_u"
  | .i64Rotl => indent depth ++ "i64.rotl"
  | .i64Rotr => indent depth ++ "i64.rotr"
  | .f32Const n => indent depth ++ "f32.const " ++ toString n
  | .f32Eq => indent depth ++ "f32.eq"
  | .f32Ne => indent depth ++ "f32.ne"
  | .f32Lt => indent depth ++ "f32.lt"
  | .f32Gt => indent depth ++ "f32.gt"
  | .f32Le => indent depth ++ "f32.le"
  | .f32Ge => indent depth ++ "f32.ge"
  | .f32Abs => indent depth ++ "f32.abs"
  | .f32Neg => indent depth ++ "f32.neg"
  | .f32Ceil => indent depth ++ "f32.ceil"
  | .f32Floor => indent depth ++ "f32.floor"
  | .f32Trunc => indent depth ++ "f32.trunc"
  | .f32Nearest => indent depth ++ "f32.nearest"
  | .f32Sqrt => indent depth ++ "f32.sqrt"
  | .f32Add => indent depth ++ "f32.add"
  | .f32Sub => indent depth ++ "f32.sub"
  | .f32Mul => indent depth ++ "f32.mul"
  | .f32Div => indent depth ++ "f32.div"
  | .f32Min => indent depth ++ "f32.min"
  | .f32Max => indent depth ++ "f32.max"
  | .f32Copysign => indent depth ++ "f32.copysign"
  | .f64Const n => indent depth ++ "f64.const " ++ toString n
  | .f64Eq => indent depth ++ "f64.eq"
  | .f64Ne => indent depth ++ "f64.ne"
  | .f64Lt => indent depth ++ "f64.lt"
  | .f64Gt => indent depth ++ "f64.gt"
  | .f64Le => indent depth ++ "f64.le"
  | .f64Ge => indent depth ++ "f64.ge"
  | .f64Abs => indent depth ++ "f64.abs"
  | .f64Neg => indent depth ++ "f64.neg"
  | .f64Ceil => indent depth ++ "f64.ceil"
  | .f64Floor => indent depth ++ "f64.floor"
  | .f64Trunc => indent depth ++ "f64.trunc"
  | .f64Nearest => indent depth ++ "f64.nearest"
  | .f64Sqrt => indent depth ++ "f64.sqrt"
  | .f64Add => indent depth ++ "f64.add"
  | .f64Sub => indent depth ++ "f64.sub"
  | .f64Mul => indent depth ++ "f64.mul"
  | .f64Div => indent depth ++ "f64.div"
  | .f64Min => indent depth ++ "f64.min"
  | .f64Max => indent depth ++ "f64.max"
  | .f64Copysign => indent depth ++ "f64.copysign"
  | .i32WrapI64 => indent depth ++ "i32.wrap_i64"
  | .i32TruncF32s => indent depth ++ "i32.trunc_f32_s"
  | .i32TruncF32u => indent depth ++ "i32.trunc_f32_u"
  | .i32TruncF64s => indent depth ++ "i32.trunc_f64_s"
  | .i32TruncF64u => indent depth ++ "i32.trunc_f64_u"
  | .i64ExtendI32s => indent depth ++ "i64.extend_i32_s"
  | .i64ExtendI32u => indent depth ++ "i64.extend_i32_u"
  | .i64TruncF32s => indent depth ++ "i64.trunc_f32_s"
  | .i64TruncF32u => indent depth ++ "i64.trunc_f32_u"
  | .i64TruncF64s => indent depth ++ "i64.trunc_f64_s"
  | .i64TruncF64u => indent depth ++ "i64.trunc_f64_u"
  | .f32ConvertI32s => indent depth ++ "f32.convert_i32_s"
  | .f32ConvertI32u => indent depth ++ "f32.convert_i32_u"
  | .f32ConvertI64s => indent depth ++ "f32.convert_i64_s"
  | .f32ConvertI64u => indent depth ++ "f32.convert_i64_u"
  | .f32DemoteF64 => indent depth ++ "f32.demote_f64"
  | .f64ConvertI32s => indent depth ++ "f64.convert_i32_s"
  | .f64ConvertI32u => indent depth ++ "f64.convert_i32_u"
  | .f64ConvertI64s => indent depth ++ "f64.convert_i64_s"
  | .f64ConvertI64u => indent depth ++ "f64.convert_i64_u"
  | .f64PromoteF32 => indent depth ++ "f64.promote_f32"
  | .i32ReinterpretF32 => indent depth ++ "i32.reinterpret_f32"
  | .f32ReinterpretI32 => indent depth ++ "f32.reinterpret_i32"
  | .i64ReinterpretF64 => indent depth ++ "i64.reinterpret_f64"
  | .f64ReinterpretI64 => indent depth ++ "f64.reinterpret_i64"
  | .memoryInit didx _ => indent depth ++ "memory.init " ++ toString didx
  | .dataDrop didx => indent depth ++ "data.drop " ++ toString didx
  | .memoryCopy _ _ => indent depth ++ "memory.copy"
  | .memoryFill _ => indent depth ++ "memory.fill"
  | .tableInit eidx _ => indent depth ++ "table.init " ++ toString eidx
  | .elemDrop eidx => indent depth ++ "elem.drop " ++ toString eidx
  | .tableCopy _ _ => indent depth ++ "table.copy"
where
  indent (n : Nat) : String := String.ofList (List.replicate (n * 2) ' ')
  printInstrs (d : Nat) (instrs : List Instr) : String :=
    String.join (instrs.map (fun i => printInstr d i ++ "\n"))

private def printFuncType (ft : FuncType) : String :=
  let ps := if ft.params.isEmpty then "" else " (param " ++ " ".intercalate (ft.params.map printValType) ++ ")"
  let rs := if ft.results.isEmpty then "" else " (result " ++ " ".intercalate (ft.results.map printValType) ++ ")"
  "(func" ++ ps ++ rs ++ ")"

private def printFunc (idx : Nat) (f : Func) (types : Array FuncType) : String :=
  let ft := if h : idx < types.size then types[idx] else { params := [], results := [] }
  let params := ft.params.map (fun t => "(param " ++ printValType t ++ ")")
  let results := ft.results.map (fun t => "(result " ++ printValType t ++ ")")
  let locals := f.locals.map (fun t => "(local " ++ printValType t ++ ")")
  let header := "  (func (;" ++ toString idx ++ ";) " ++
    " ".intercalate (params ++ results ++ locals)
  let body := String.join (f.body.map (fun i => printInstr 2 i ++ "\n"))
  header ++ "\n" ++ body ++ "  )"

private def printExport (e : Export) : String :=
  let desc := match e.desc with
    | .func idx => "(func " ++ toString idx ++ ")"
    | .table idx => "(table " ++ toString idx ++ ")"
    | .memory idx => "(memory " ++ toString idx ++ ")"
    | .global idx => "(global " ++ toString idx ++ ")"
  "  (export \"" ++ e.name ++ "\" " ++ desc ++ ")"

/-- Print a Wasm module in WAT format -/
def printWat (m : Module) : String :=
  let types := m.types.toList.zip (List.range m.types.size) |>.map (fun (ft, i) =>
    "  (type (;" ++ toString i ++ ";) " ++ printFuncType ft ++ ")")
  let funcs := m.funcs.toList.zip (List.range m.funcs.size) |>.map (fun (f, i) =>
    printFunc i f m.types)
  let mems := m.memories.toList.map (fun mem =>
    "  (memory " ++ toString mem.lim.min ++
    (match mem.lim.max with | some mx => " " ++ toString mx | none => "") ++ ")")
  let exports := m.exports.toList.map printExport
  let startS := match m.start with
    | some idx => ["  (start " ++ toString idx ++ ")"]
    | none => []
  "(module\n" ++
  String.join (types.map (· ++ "\n")) ++
  String.join (funcs.map (· ++ "\n")) ++
  String.join (mems.map (· ++ "\n")) ++
  String.join (exports.map (· ++ "\n")) ++
  String.join (startS.map (· ++ "\n")) ++
  ")"

end VerifiedJS.Wasm
