/-
  VerifiedJS — Wasm AST
  Abstract Wasm module (mirrors WasmCert-Coq `theories/datatypes.v`).
  Target: Wasm 1.0 MVP + bulk memory + mutable globals.
-/

instance : Repr ByteArray where
  reprPrec ba _ := s!"ByteArray.mk #[{", ".intercalate (ba.toList.map (fun b => toString b))}]"

namespace VerifiedJS.Wasm

/-- Wasm value types -/
inductive ValType where
  | i32 | i64 | f32 | f64
  deriving Repr, BEq, Hashable

/-- Wasm function types -/
structure FuncType where
  params : List ValType
  results : List ValType
  deriving Repr, BEq

/-- Wasm block type -/
inductive BlockType where
  | none
  | valType (t : ValType)
  | typeIdx (idx : Nat)
  deriving Repr, BEq

/-- Memory argument for load/store instructions -/
structure MemArg where
  offset : Nat
  align : Nat
  deriving Repr, BEq

/-- Wasm instructions -/
inductive Instr where
  -- Control
  | unreachable | nop
  | block (bt : BlockType) (body : List Instr)
  | loop (bt : BlockType) (body : List Instr)
  | if_ (bt : BlockType) (then_ : List Instr) (else_ : List Instr)
  | br (labelIdx : Nat)
  | brIf (labelIdx : Nat)
  | brTable (labels : List Nat) (default_ : Nat)
  | return_
  | call (funcIdx : Nat)
  | callIndirect (typeIdx : Nat) (tableIdx : Nat)
  -- Parametric
  | drop | select
  -- Variable
  | localGet (idx : Nat)
  | localSet (idx : Nat)
  | localTee (idx : Nat)
  | globalGet (idx : Nat)
  | globalSet (idx : Nat)
  -- Memory
  | i32Load (ma : MemArg) | i64Load (ma : MemArg)
  | f32Load (ma : MemArg) | f64Load (ma : MemArg)
  | i32Store (ma : MemArg) | i64Store (ma : MemArg)
  | f32Store (ma : MemArg) | f64Store (ma : MemArg)
  | i32Load8s (ma : MemArg) | i32Load8u (ma : MemArg)
  | i32Load16s (ma : MemArg) | i32Load16u (ma : MemArg)
  | i64Load8s (ma : MemArg) | i64Load8u (ma : MemArg)
  | i64Load16s (ma : MemArg) | i64Load16u (ma : MemArg)
  | i64Load32s (ma : MemArg) | i64Load32u (ma : MemArg)
  | i32Store8 (ma : MemArg) | i32Store16 (ma : MemArg)
  | i64Store8 (ma : MemArg) | i64Store16 (ma : MemArg) | i64Store32 (ma : MemArg)
  | memorySize | memoryGrow
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
  -- Numeric f64
  | f64Const (n : Float)
  | f64Eq | f64Ne | f64Lt | f64Gt | f64Le | f64Ge
  | f64Abs | f64Neg | f64Ceil | f64Floor | f64Trunc | f64Nearest | f64Sqrt
  | f64Add | f64Sub | f64Mul | f64Div | f64Min | f64Max | f64Copysign
  -- Conversions
  | i32WrapI64 | i64ExtendI32s | i64ExtendI32u
  | i32TruncF64s | i32TruncF64u | i64TruncF64s | i64TruncF64u
  | f64ConvertI32s | f64ConvertI32u | f64ConvertI64s | f64ConvertI64u
  | i32ReinterpretF32 | f32ReinterpretI32
  | i64ReinterpretF64 | f64ReinterpretI64
  -- Bulk memory
  | memoryCopy | memoryFill
  deriving Repr

/-- Wasm global definition -/
structure Global where
  type : ValType
  mutable_ : Bool
  init : List Instr
  deriving Repr

/-- Wasm function body -/
structure Func where
  type : FuncType
  locals : List ValType
  body : List Instr
  deriving Repr

/-- Wasm table -/
structure Table where
  min : Nat
  max : Option Nat
  deriving Repr

/-- Wasm memory -/
structure Memory where
  min : Nat  -- in pages (64KiB each)
  max : Option Nat
  deriving Repr

/-- Wasm export description -/
inductive ExportDesc where
  | func (idx : Nat)
  | table (idx : Nat)
  | memory (idx : Nat)
  | global (idx : Nat)
  deriving Repr

/-- Wasm export -/
structure Export where
  name : String
  desc : ExportDesc
  deriving Repr

/-- Wasm import description -/
inductive ImportDesc where
  | func (typeIdx : Nat)
  | table (t : Table)
  | memory (m : Memory)
  | global (type : ValType) (mutable_ : Bool)
  deriving Repr

/-- Wasm import -/
structure Import where
  module_ : String
  name : String
  desc : ImportDesc
  deriving Repr

/-- Wasm data segment -/
structure DataSegment where
  memIdx : Nat
  offset : List Instr
  init : ByteArray
  deriving Repr

/-- Wasm element segment -/
structure ElemSegment where
  tableIdx : Nat
  offset : List Instr
  funcIdxs : List Nat
  deriving Repr

/-- Wasm module -/
structure Module where
  types : Array FuncType
  funcs : Array Func
  tables : Array Table
  memories : Array Memory
  globals : Array Global
  exports : Array Export
  imports : Array Import
  start : Option Nat
  elems : Array ElemSegment
  datas : Array DataSegment
  deriving Repr

end VerifiedJS.Wasm
