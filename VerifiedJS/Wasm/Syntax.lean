/- 
  VerifiedJS — Wasm AST
  Abstract syntax aligned with WasmCert-Coq `theories/datatypes.v`.
  Target: Wasm 1.0 MVP + bulk memory + mutable globals.
-/

namespace VerifiedJS.Wasm

instance : Repr ByteArray where
  reprPrec ba _ := s!"ByteArray.mk #[{", ".intercalate (ba.toList.map (fun b => toString b))}]"

abbrev TypeIdx := Nat
abbrev FuncIdx := Nat
abbrev TableIdx := Nat
abbrev MemIdx := Nat
abbrev GlobalIdx := Nat
abbrev LocalIdx := Nat
abbrev LabelIdx := Nat
abbrev DataIdx := Nat
abbrev ElemIdx := Nat

/-- Wasm value types (numeric subset used by MVP). -/
inductive ValType where
  | i32 | i64 | f32 | f64
  deriving Repr, BEq, Hashable

/-- Wasm function type. -/
structure FuncType where
  params : List ValType
  results : List ValType
  deriving Repr, BEq

/-- Wasm limits (`min` and optional `max`). -/
structure Limits where
  min : Nat
  max : Option Nat
  deriving Repr, BEq

/-- Table element type (MVP uses only `funcref`). -/
inductive ElemType where
  | funcref
  deriving Repr, BEq

/-- Wasm table type. -/
structure TableType where
  elem : ElemType
  lim : Limits
  deriving Repr, BEq

/-- Wasm memory type (sizes in 64KiB pages). -/
structure MemType where
  lim : Limits
  deriving Repr, BEq

/-- Wasm mutability qualifier. -/
inductive Mut where
  | const_
  | var
  deriving Repr, BEq

/-- Wasm global type. -/
structure GlobalType where
  val : ValType
  mutability : Mut
  deriving Repr, BEq

/-- Wasm block type. -/
inductive BlockType where
  | none
  | valType (t : ValType)
  | typeIdx (idx : TypeIdx)
  deriving Repr, BEq

/-- Memory argument for loads/stores. -/
structure MemArg where
  offset : Nat
  align : Nat
  deriving Repr, BEq

/-- Wasm instructions. -/
inductive Instr where
  -- Control
  | unreachable | nop
  | block (bt : BlockType) (body : List Instr)
  | loop (bt : BlockType) (body : List Instr)
  | if_ (bt : BlockType) (then_ : List Instr) (else_ : List Instr)
  | br (labelIdx : LabelIdx)
  | brIf (labelIdx : LabelIdx)
  | brTable (labels : List LabelIdx) (default_ : LabelIdx)
  | return_
  | call (funcIdx : FuncIdx)
  | callIndirect (typeIdx : TypeIdx) (tableIdx : TableIdx)
  -- Parametric
  | drop
  | select
  -- Variable
  | localGet (idx : LocalIdx)
  | localSet (idx : LocalIdx)
  | localTee (idx : LocalIdx)
  | globalGet (idx : GlobalIdx)
  | globalSet (idx : GlobalIdx)
  -- Memory
  | i32Load (ma : MemArg) | i64Load (ma : MemArg)
  | f32Load (ma : MemArg) | f64Load (ma : MemArg)
  | i32Load8s (ma : MemArg) | i32Load8u (ma : MemArg)
  | i32Load16s (ma : MemArg) | i32Load16u (ma : MemArg)
  | i64Load8s (ma : MemArg) | i64Load8u (ma : MemArg)
  | i64Load16s (ma : MemArg) | i64Load16u (ma : MemArg)
  | i64Load32s (ma : MemArg) | i64Load32u (ma : MemArg)
  | i32Store (ma : MemArg) | i64Store (ma : MemArg)
  | f32Store (ma : MemArg) | f64Store (ma : MemArg)
  | i32Store8 (ma : MemArg) | i32Store16 (ma : MemArg)
  | i64Store8 (ma : MemArg) | i64Store16 (ma : MemArg) | i64Store32 (ma : MemArg)
  | memorySize (mem : MemIdx)
  | memoryGrow (mem : MemIdx)
  -- Numeric i32
  | i32Const (n : UInt32)
  | i32Eqz | i32Eq | i32Ne
  | i32Lts | i32Ltu | i32Gts | i32Gtu | i32Les | i32Leu | i32Ges | i32Geu
  | i32Clz | i32Ctz | i32Popcnt
  | i32Add | i32Sub | i32Mul | i32DivS | i32DivU | i32RemS | i32RemU
  | i32And | i32Or | i32Xor | i32Shl | i32ShrS | i32ShrU | i32Rotl | i32Rotr
  -- Numeric i64
  | i64Const (n : UInt64)
  | i64Eqz | i64Eq | i64Ne
  | i64Lts | i64Ltu | i64Gts | i64Gtu | i64Les | i64Leu | i64Ges | i64Geu
  | i64Clz | i64Ctz | i64Popcnt
  | i64Add | i64Sub | i64Mul | i64DivS | i64DivU | i64RemS | i64RemU
  | i64And | i64Or | i64Xor | i64Shl | i64ShrS | i64ShrU | i64Rotl | i64Rotr
  -- Numeric f32
  | f32Const (n : Float)
  | f32Eq | f32Ne | f32Lt | f32Gt | f32Le | f32Ge
  | f32Abs | f32Neg | f32Ceil | f32Floor | f32Trunc | f32Nearest | f32Sqrt
  | f32Add | f32Sub | f32Mul | f32Div | f32Min | f32Max | f32Copysign
  -- Numeric f64
  | f64Const (n : Float)
  | f64Eq | f64Ne | f64Lt | f64Gt | f64Le | f64Ge
  | f64Abs | f64Neg | f64Ceil | f64Floor | f64Trunc | f64Nearest | f64Sqrt
  | f64Add | f64Sub | f64Mul | f64Div | f64Min | f64Max | f64Copysign
  -- Conversions / reinterpretations
  | i32WrapI64
  | i32TruncF32s | i32TruncF32u | i32TruncF64s | i32TruncF64u
  | i64ExtendI32s | i64ExtendI32u
  | i64TruncF32s | i64TruncF32u | i64TruncF64s | i64TruncF64u
  | f32ConvertI32s | f32ConvertI32u | f32ConvertI64s | f32ConvertI64u
  | f32DemoteF64
  | f64ConvertI32s | f64ConvertI32u | f64ConvertI64s | f64ConvertI64u
  | f64PromoteF32
  | i32ReinterpretF32 | f32ReinterpretI32
  | i64ReinterpretF64 | f64ReinterpretI64
  -- Bulk memory / table
  | memoryInit (data : DataIdx) (mem : MemIdx)
  | dataDrop (data : DataIdx)
  | memoryCopy (dst : MemIdx) (src : MemIdx)
  | memoryFill (mem : MemIdx)
  | tableInit (elem : ElemIdx) (table : TableIdx)
  | elemDrop (elem : ElemIdx)
  | tableCopy (dst : TableIdx) (src : TableIdx)
  deriving Repr

abbrev Expr := List Instr

/-- Global definition. -/
structure Global where
  type : GlobalType
  init : Expr
  deriving Repr

/-- Function body with type index and locals. -/
structure Func where
  typeIdx : TypeIdx
  locals : List ValType
  body : Expr
  deriving Repr

abbrev Table := TableType
abbrev Memory := MemType

/-- Wasm export descriptor. -/
inductive ExportDesc where
  | func (idx : FuncIdx)
  | table (idx : TableIdx)
  | memory (idx : MemIdx)
  | global (idx : GlobalIdx)
  deriving Repr

/-- Wasm export declaration. -/
structure Export where
  name : String
  desc : ExportDesc
  deriving Repr

/-- Wasm import descriptor. -/
inductive ImportDesc where
  | func (typeIdx : TypeIdx)
  | table (t : TableType)
  | memory (m : MemType)
  | global (gt : GlobalType)
  deriving Repr

/-- Wasm import declaration. -/
structure Import where
  module_ : String
  name : String
  desc : ImportDesc
  deriving Repr

/-- Active data segment (MVP + bulk memory). -/
structure DataSegment where
  memIdx : MemIdx
  offset : Expr
  init : ByteArray
  deriving Repr

/-- Active element segment (function indices). -/
structure ElemSegment where
  tableIdx : TableIdx
  offset : Expr
  funcIdxs : List FuncIdx
  deriving Repr

/-- Wasm module. -/
structure Module where
  types : Array FuncType
  imports : Array Import
  funcs : Array Func
  tables : Array TableType
  memories : Array MemType
  globals : Array Global
  exports : Array Export
  start : Option FuncIdx
  elems : Array ElemSegment
  datas : Array DataSegment
  deriving Repr

end VerifiedJS.Wasm
