/-
  VerifiedJS — Wasm Binary Encoding
  Outside the verified TCB — validated by wasm-tools + Valex-style checker.
-/

import VerifiedJS.Wasm.Syntax

namespace VerifiedJS.Wasm

-- ============================================================
-- LEB128 encoding
-- ============================================================

/-- Encode a natural number as unsigned LEB128. -/
partial def encodeLEB128U (n : Nat) : ByteArray :=
  if n < 128 then
    ByteArray.mk #[n.toUInt8]
  else
    let byte := (n % 128 + 128).toUInt8  -- low 7 bits with high bit set
    (ByteArray.mk #[byte]).append (encodeLEB128U (n / 128))

/-- Encode an integer as signed LEB128. -/
partial def encodeLEB128S (n : Int) : ByteArray :=
  let byte := (n % 128).toNat.toUInt8
  let n' := n / 128  -- arithmetic shift right by 7
  -- Check if we're done: remaining value is 0 with sign bit clear,
  -- or -1 with sign bit set
  if (n' == 0 && byte.toNat &&& 0x40 == 0) ||
     (n' == -1 && byte.toNat &&& 0x40 != 0) then
    ByteArray.mk #[byte]
  else
    let byte' := (byte.toNat ||| 0x80).toUInt8
    (ByteArray.mk #[byte']).append (encodeLEB128S n')

-- ============================================================
-- Value type encoding
-- ============================================================

def encodeValType (t : ValType) : UInt8 :=
  match t with
  | .i32 => (0x7F : UInt8)
  | .i64 => (0x7E : UInt8)
  | .f32 => (0x7D : UInt8)
  | .f64 => (0x7C : UInt8)

-- ============================================================
-- Helpers
-- ============================================================

/-- Encode a vector: length (LEB128) followed by elements. -/
def encodeVec (items : List ByteArray) : ByteArray :=
  let count := encodeLEB128U items.length
  items.foldl (fun acc b => acc.append b) count

/-- Encode a byte vector (raw bytes with length prefix). -/
def encodeByteVec (bs : ByteArray) : ByteArray :=
  (encodeLEB128U bs.size).append bs

/-- Encode a string as UTF-8 name (length-prefixed). -/
def encodeName (s : String) : ByteArray :=
  let utf8 := s.toUTF8
  (encodeLEB128U utf8.size).append utf8

/-- Wrap content bytes in a section header: id byte, size, content. -/
def encodeSection (id : UInt8) (content : ByteArray) : ByteArray :=
  if content.size == 0 then
    ByteArray.mk #[]
  else
    (ByteArray.mk #[id]).append ((encodeLEB128U content.size).append content)

-- ============================================================
-- Block type encoding
-- ============================================================

def encodeBlockType (bt : BlockType) : ByteArray :=
  match bt with
  | .none => ByteArray.mk #[(0x40 : UInt8)]
  | .valType t => ByteArray.mk #[encodeValType t]
  | .typeIdx idx => encodeLEB128S (Int.ofNat idx)

-- ============================================================
-- Memory argument encoding
-- ============================================================

def encodeMemArg (ma : MemArg) : ByteArray :=
  (encodeLEB128U ma.align).append (encodeLEB128U ma.offset)

-- ============================================================
-- Instruction encoding
-- ============================================================

/-- Encode a single Wasm instruction to binary. -/
partial def encodeInstr (instr : Instr) : ByteArray :=
  match instr with
  -- Control
  | .unreachable => ByteArray.mk #[(0x00 : UInt8)]
  | .nop => ByteArray.mk #[(0x01 : UInt8)]
  | .block bt body =>
    let header := (ByteArray.mk #[(0x02 : UInt8)]).append (encodeBlockType bt)
    let bodyBytes := body.foldl (fun acc i => acc.append (encodeInstr i)) (ByteArray.mk #[])
    header.append (bodyBytes.append (ByteArray.mk #[(0x0B : UInt8)]))
  | .loop bt body =>
    let header := (ByteArray.mk #[(0x03 : UInt8)]).append (encodeBlockType bt)
    let bodyBytes := body.foldl (fun acc i => acc.append (encodeInstr i)) (ByteArray.mk #[])
    header.append (bodyBytes.append (ByteArray.mk #[(0x0B : UInt8)]))
  | .if_ bt then_ else_ =>
    let header := (ByteArray.mk #[(0x04 : UInt8)]).append (encodeBlockType bt)
    let thenBytes := then_.foldl (fun acc i => acc.append (encodeInstr i)) (ByteArray.mk #[])
    if else_.isEmpty then
      header.append (thenBytes.append (ByteArray.mk #[(0x0B : UInt8)]))
    else
      let elseBytes := else_.foldl (fun acc i => acc.append (encodeInstr i)) (ByteArray.mk #[])
      header.append (thenBytes.append ((ByteArray.mk #[(0x05 : UInt8)]).append (elseBytes.append (ByteArray.mk #[(0x0B : UInt8)]))))
  | .br idx => (ByteArray.mk #[(0x0C : UInt8)]).append (encodeLEB128U idx)
  | .brIf idx => (ByteArray.mk #[(0x0D : UInt8)]).append (encodeLEB128U idx)
  | .brTable labels default_ =>
    let header := ByteArray.mk #[(0x0E : UInt8)]
    let vec := encodeVec (labels.map encodeLEB128U)
    header.append (vec.append (encodeLEB128U default_))
  | .return_ => ByteArray.mk #[(0x0F : UInt8)]
  | .call idx => (ByteArray.mk #[(0x10 : UInt8)]).append (encodeLEB128U idx)
  | .callIndirect typeIdx tableIdx =>
    (ByteArray.mk #[(0x11 : UInt8)]).append ((encodeLEB128U typeIdx).append (encodeLEB128U tableIdx))
  -- Parametric
  | .drop => ByteArray.mk #[(0x1A : UInt8)]
  | .select => ByteArray.mk #[(0x1B : UInt8)]
  -- Variable
  | .localGet idx => (ByteArray.mk #[(0x20 : UInt8)]).append (encodeLEB128U idx)
  | .localSet idx => (ByteArray.mk #[(0x21 : UInt8)]).append (encodeLEB128U idx)
  | .localTee idx => (ByteArray.mk #[(0x22 : UInt8)]).append (encodeLEB128U idx)
  | .globalGet idx => (ByteArray.mk #[(0x23 : UInt8)]).append (encodeLEB128U idx)
  | .globalSet idx => (ByteArray.mk #[(0x24 : UInt8)]).append (encodeLEB128U idx)
  -- Memory loads
  | .i32Load ma => (ByteArray.mk #[(0x28 : UInt8)]).append (encodeMemArg ma)
  | .i64Load ma => (ByteArray.mk #[(0x29 : UInt8)]).append (encodeMemArg ma)
  | .f32Load ma => (ByteArray.mk #[(0x2A : UInt8)]).append (encodeMemArg ma)
  | .f64Load ma => (ByteArray.mk #[(0x2B : UInt8)]).append (encodeMemArg ma)
  | .i32Load8s ma => (ByteArray.mk #[(0x2C : UInt8)]).append (encodeMemArg ma)
  | .i32Load8u ma => (ByteArray.mk #[(0x2D : UInt8)]).append (encodeMemArg ma)
  | .i32Load16s ma => (ByteArray.mk #[(0x2E : UInt8)]).append (encodeMemArg ma)
  | .i32Load16u ma => (ByteArray.mk #[(0x2F : UInt8)]).append (encodeMemArg ma)
  | .i64Load8s ma => (ByteArray.mk #[(0x30 : UInt8)]).append (encodeMemArg ma)
  | .i64Load8u ma => (ByteArray.mk #[(0x31 : UInt8)]).append (encodeMemArg ma)
  | .i64Load16s ma => (ByteArray.mk #[(0x32 : UInt8)]).append (encodeMemArg ma)
  | .i64Load16u ma => (ByteArray.mk #[(0x33 : UInt8)]).append (encodeMemArg ma)
  | .i64Load32s ma => (ByteArray.mk #[(0x34 : UInt8)]).append (encodeMemArg ma)
  | .i64Load32u ma => (ByteArray.mk #[(0x35 : UInt8)]).append (encodeMemArg ma)
  -- Memory stores
  | .i32Store ma => (ByteArray.mk #[(0x36 : UInt8)]).append (encodeMemArg ma)
  | .i64Store ma => (ByteArray.mk #[(0x37 : UInt8)]).append (encodeMemArg ma)
  | .f32Store ma => (ByteArray.mk #[(0x38 : UInt8)]).append (encodeMemArg ma)
  | .f64Store ma => (ByteArray.mk #[(0x39 : UInt8)]).append (encodeMemArg ma)
  | .i32Store8 ma => (ByteArray.mk #[(0x3A : UInt8)]).append (encodeMemArg ma)
  | .i32Store16 ma => (ByteArray.mk #[(0x3B : UInt8)]).append (encodeMemArg ma)
  | .i64Store8 ma => (ByteArray.mk #[(0x3C : UInt8)]).append (encodeMemArg ma)
  | .i64Store16 ma => (ByteArray.mk #[(0x3D : UInt8)]).append (encodeMemArg ma)
  | .i64Store32 ma => (ByteArray.mk #[(0x3E : UInt8)]).append (encodeMemArg ma)
  -- Memory size/grow
  | .memorySize _mem => ByteArray.mk #[(0x3F : UInt8), (0x00 : UInt8)]
  | .memoryGrow _mem => ByteArray.mk #[(0x40 : UInt8), (0x00 : UInt8)]
  -- Numeric constants
  | .i32Const n => (ByteArray.mk #[(0x41 : UInt8)]).append (encodeLEB128S (Int.ofNat n.toNat))
  | .i64Const n => (ByteArray.mk #[(0x42 : UInt8)]).append (encodeLEB128S (Int.ofNat n.toNat))
  | .f32Const _n =>
    -- Placeholder: 4 zero bytes for f32
    ByteArray.mk #[(0x43 : UInt8), (0x00 : UInt8), (0x00 : UInt8), (0x00 : UInt8), (0x00 : UInt8)]
  | .f64Const _n =>
    -- Placeholder: 8 zero bytes for f64
    ByteArray.mk #[(0x44 : UInt8), (0x00 : UInt8), (0x00 : UInt8), (0x00 : UInt8), (0x00 : UInt8),
                    (0x00 : UInt8), (0x00 : UInt8), (0x00 : UInt8), (0x00 : UInt8)]
  -- i32 comparison
  | .i32Eqz => ByteArray.mk #[(0x45 : UInt8)]
  | .i32Eq => ByteArray.mk #[(0x46 : UInt8)]
  | .i32Ne => ByteArray.mk #[(0x47 : UInt8)]
  | .i32Lts => ByteArray.mk #[(0x48 : UInt8)]
  | .i32Ltu => ByteArray.mk #[(0x49 : UInt8)]
  | .i32Gts => ByteArray.mk #[(0x4A : UInt8)]
  | .i32Gtu => ByteArray.mk #[(0x4B : UInt8)]
  | .i32Les => ByteArray.mk #[(0x4C : UInt8)]
  | .i32Leu => ByteArray.mk #[(0x4D : UInt8)]
  | .i32Ges => ByteArray.mk #[(0x4E : UInt8)]
  | .i32Geu => ByteArray.mk #[(0x4F : UInt8)]
  -- i64 comparison
  | .i64Eqz => ByteArray.mk #[(0x50 : UInt8)]
  | .i64Eq => ByteArray.mk #[(0x51 : UInt8)]
  | .i64Ne => ByteArray.mk #[(0x52 : UInt8)]
  | .i64Lts => ByteArray.mk #[(0x53 : UInt8)]
  | .i64Ltu => ByteArray.mk #[(0x54 : UInt8)]
  | .i64Gts => ByteArray.mk #[(0x55 : UInt8)]
  | .i64Gtu => ByteArray.mk #[(0x56 : UInt8)]
  | .i64Les => ByteArray.mk #[(0x57 : UInt8)]
  | .i64Leu => ByteArray.mk #[(0x58 : UInt8)]
  | .i64Ges => ByteArray.mk #[(0x59 : UInt8)]
  | .i64Geu => ByteArray.mk #[(0x5A : UInt8)]
  -- f32 comparison
  | .f32Eq => ByteArray.mk #[(0x5B : UInt8)]
  | .f32Ne => ByteArray.mk #[(0x5C : UInt8)]
  | .f32Lt => ByteArray.mk #[(0x5D : UInt8)]
  | .f32Gt => ByteArray.mk #[(0x5E : UInt8)]
  | .f32Le => ByteArray.mk #[(0x5F : UInt8)]
  | .f32Ge => ByteArray.mk #[(0x60 : UInt8)]
  -- f64 comparison
  | .f64Eq => ByteArray.mk #[(0x61 : UInt8)]
  | .f64Ne => ByteArray.mk #[(0x62 : UInt8)]
  | .f64Lt => ByteArray.mk #[(0x63 : UInt8)]
  | .f64Gt => ByteArray.mk #[(0x64 : UInt8)]
  | .f64Le => ByteArray.mk #[(0x65 : UInt8)]
  | .f64Ge => ByteArray.mk #[(0x66 : UInt8)]
  -- i32 unary
  | .i32Clz => ByteArray.mk #[(0x67 : UInt8)]
  | .i32Ctz => ByteArray.mk #[(0x68 : UInt8)]
  | .i32Popcnt => ByteArray.mk #[(0x69 : UInt8)]
  -- i32 binary
  | .i32Add => ByteArray.mk #[(0x6A : UInt8)]
  | .i32Sub => ByteArray.mk #[(0x6B : UInt8)]
  | .i32Mul => ByteArray.mk #[(0x6C : UInt8)]
  | .i32DivS => ByteArray.mk #[(0x6D : UInt8)]
  | .i32DivU => ByteArray.mk #[(0x6E : UInt8)]
  | .i32RemS => ByteArray.mk #[(0x6F : UInt8)]
  | .i32RemU => ByteArray.mk #[(0x70 : UInt8)]
  | .i32And => ByteArray.mk #[(0x71 : UInt8)]
  | .i32Or => ByteArray.mk #[(0x72 : UInt8)]
  | .i32Xor => ByteArray.mk #[(0x73 : UInt8)]
  | .i32Shl => ByteArray.mk #[(0x74 : UInt8)]
  | .i32ShrS => ByteArray.mk #[(0x75 : UInt8)]
  | .i32ShrU => ByteArray.mk #[(0x76 : UInt8)]
  | .i32Rotl => ByteArray.mk #[(0x77 : UInt8)]
  | .i32Rotr => ByteArray.mk #[(0x78 : UInt8)]
  -- i64 unary
  | .i64Clz => ByteArray.mk #[(0x79 : UInt8)]
  | .i64Ctz => ByteArray.mk #[(0x7A : UInt8)]
  | .i64Popcnt => ByteArray.mk #[(0x7B : UInt8)]
  -- i64 binary
  | .i64Add => ByteArray.mk #[(0x7C : UInt8)]
  | .i64Sub => ByteArray.mk #[(0x7D : UInt8)]
  | .i64Mul => ByteArray.mk #[(0x7E : UInt8)]
  | .i64DivS => ByteArray.mk #[(0x7F : UInt8)]
  | .i64DivU => ByteArray.mk #[(0x80 : UInt8)]
  | .i64RemS => ByteArray.mk #[(0x81 : UInt8)]
  | .i64RemU => ByteArray.mk #[(0x82 : UInt8)]
  | .i64And => ByteArray.mk #[(0x83 : UInt8)]
  | .i64Or => ByteArray.mk #[(0x84 : UInt8)]
  | .i64Xor => ByteArray.mk #[(0x85 : UInt8)]
  | .i64Shl => ByteArray.mk #[(0x86 : UInt8)]
  | .i64ShrS => ByteArray.mk #[(0x87 : UInt8)]
  | .i64ShrU => ByteArray.mk #[(0x88 : UInt8)]
  | .i64Rotl => ByteArray.mk #[(0x89 : UInt8)]
  | .i64Rotr => ByteArray.mk #[(0x8A : UInt8)]
  -- f32 unary
  | .f32Abs => ByteArray.mk #[(0x8B : UInt8)]
  | .f32Neg => ByteArray.mk #[(0x8C : UInt8)]
  | .f32Ceil => ByteArray.mk #[(0x8D : UInt8)]
  | .f32Floor => ByteArray.mk #[(0x8E : UInt8)]
  | .f32Trunc => ByteArray.mk #[(0x8F : UInt8)]
  | .f32Nearest => ByteArray.mk #[(0x90 : UInt8)]
  | .f32Sqrt => ByteArray.mk #[(0x91 : UInt8)]
  -- f32 binary
  | .f32Add => ByteArray.mk #[(0x92 : UInt8)]
  | .f32Sub => ByteArray.mk #[(0x93 : UInt8)]
  | .f32Mul => ByteArray.mk #[(0x94 : UInt8)]
  | .f32Div => ByteArray.mk #[(0x95 : UInt8)]
  | .f32Min => ByteArray.mk #[(0x96 : UInt8)]
  | .f32Max => ByteArray.mk #[(0x97 : UInt8)]
  | .f32Copysign => ByteArray.mk #[(0x98 : UInt8)]
  -- f64 unary
  | .f64Abs => ByteArray.mk #[(0x99 : UInt8)]
  | .f64Neg => ByteArray.mk #[(0x9A : UInt8)]
  | .f64Ceil => ByteArray.mk #[(0x9B : UInt8)]
  | .f64Floor => ByteArray.mk #[(0x9C : UInt8)]
  | .f64Trunc => ByteArray.mk #[(0x9D : UInt8)]
  | .f64Nearest => ByteArray.mk #[(0x9E : UInt8)]
  | .f64Sqrt => ByteArray.mk #[(0x9F : UInt8)]
  -- f64 binary
  | .f64Add => ByteArray.mk #[(0xA0 : UInt8)]
  | .f64Sub => ByteArray.mk #[(0xA1 : UInt8)]
  | .f64Mul => ByteArray.mk #[(0xA2 : UInt8)]
  | .f64Div => ByteArray.mk #[(0xA3 : UInt8)]
  | .f64Min => ByteArray.mk #[(0xA4 : UInt8)]
  | .f64Max => ByteArray.mk #[(0xA5 : UInt8)]
  | .f64Copysign => ByteArray.mk #[(0xA6 : UInt8)]
  -- Conversions
  | .i32WrapI64 => ByteArray.mk #[(0xA7 : UInt8)]
  | .i32TruncF32s => ByteArray.mk #[(0xA8 : UInt8)]
  | .i32TruncF32u => ByteArray.mk #[(0xA9 : UInt8)]
  | .i32TruncF64s => ByteArray.mk #[(0xAA : UInt8)]
  | .i32TruncF64u => ByteArray.mk #[(0xAB : UInt8)]
  | .i64ExtendI32s => ByteArray.mk #[(0xAC : UInt8)]
  | .i64ExtendI32u => ByteArray.mk #[(0xAD : UInt8)]
  | .i64TruncF32s => ByteArray.mk #[(0xAE : UInt8)]
  | .i64TruncF32u => ByteArray.mk #[(0xAF : UInt8)]
  | .i64TruncF64s => ByteArray.mk #[(0xB0 : UInt8)]
  | .i64TruncF64u => ByteArray.mk #[(0xB1 : UInt8)]
  | .f32ConvertI32s => ByteArray.mk #[(0xB2 : UInt8)]
  | .f32ConvertI32u => ByteArray.mk #[(0xB3 : UInt8)]
  | .f32ConvertI64s => ByteArray.mk #[(0xB4 : UInt8)]
  | .f32ConvertI64u => ByteArray.mk #[(0xB5 : UInt8)]
  | .f32DemoteF64 => ByteArray.mk #[(0xB6 : UInt8)]
  | .f64ConvertI32s => ByteArray.mk #[(0xB7 : UInt8)]
  | .f64ConvertI32u => ByteArray.mk #[(0xB8 : UInt8)]
  | .f64ConvertI64s => ByteArray.mk #[(0xB9 : UInt8)]
  | .f64ConvertI64u => ByteArray.mk #[(0xBA : UInt8)]
  | .f64PromoteF32 => ByteArray.mk #[(0xBB : UInt8)]
  | .i32ReinterpretF32 => ByteArray.mk #[(0xBC : UInt8)]
  | .i64ReinterpretF64 => ByteArray.mk #[(0xBD : UInt8)]
  | .f32ReinterpretI32 => ByteArray.mk #[(0xBE : UInt8)]
  | .f64ReinterpretI64 => ByteArray.mk #[(0xBF : UInt8)]
  -- Bulk memory (0xFC prefix)
  | .memoryInit dataIdx memIdx =>
    (ByteArray.mk #[(0xFC : UInt8)]).append
      ((encodeLEB128U 8).append ((encodeLEB128U dataIdx).append (encodeLEB128U memIdx)))
  | .dataDrop dataIdx =>
    (ByteArray.mk #[(0xFC : UInt8)]).append ((encodeLEB128U 9).append (encodeLEB128U dataIdx))
  | .memoryCopy dst src =>
    (ByteArray.mk #[(0xFC : UInt8)]).append
      ((encodeLEB128U 10).append ((encodeLEB128U dst).append (encodeLEB128U src)))
  | .memoryFill mem =>
    (ByteArray.mk #[(0xFC : UInt8)]).append ((encodeLEB128U 11).append (encodeLEB128U mem))
  | .tableInit elemIdx tableIdx =>
    (ByteArray.mk #[(0xFC : UInt8)]).append
      ((encodeLEB128U 12).append ((encodeLEB128U elemIdx).append (encodeLEB128U tableIdx)))
  | .elemDrop elemIdx =>
    (ByteArray.mk #[(0xFC : UInt8)]).append ((encodeLEB128U 13).append (encodeLEB128U elemIdx))
  | .tableCopy dst src =>
    (ByteArray.mk #[(0xFC : UInt8)]).append
      ((encodeLEB128U 14).append ((encodeLEB128U dst).append (encodeLEB128U src)))

/-- Encode a list of instructions (expression) followed by end marker. -/
def encodeExpr (instrs : List Instr) : ByteArray :=
  let body := instrs.foldl (fun acc i => acc.append (encodeInstr i)) (ByteArray.mk #[])
  body.append (ByteArray.mk #[(0x0B : UInt8)])

-- ============================================================
-- Section encoders
-- ============================================================

/-- Section 1: Type section — function types. -/
def encodeTypeSection (types : Array FuncType) : ByteArray :=
  if types.isEmpty then ByteArray.mk #[]
  else
    let entries := types.toList.map fun ft =>
      let tag := ByteArray.mk #[(0x60 : UInt8)]
      let params := encodeVec (ft.params.map fun t => ByteArray.mk #[encodeValType t])
      let results := encodeVec (ft.results.map fun t => ByteArray.mk #[encodeValType t])
      tag.append (params.append results)
    encodeSection (0x01 : UInt8) (encodeVec entries)

/-- Section 2: Import section. -/
def encodeImportSection (imports : Array Import) : ByteArray :=
  if imports.isEmpty then ByteArray.mk #[]
  else
    let entries := imports.toList.map fun imp =>
      let modName := encodeName imp.module_
      let name := encodeName imp.name
      let desc := match imp.desc with
        | .func typeIdx => (ByteArray.mk #[(0x00 : UInt8)]).append (encodeLEB128U typeIdx)
        | .table t =>
          let elemByte := match t.elem with | .funcref => (0x70 : UInt8)
          let lim := match t.lim.max with
            | Option.none => (ByteArray.mk #[(0x00 : UInt8)]).append (encodeLEB128U t.lim.min)
            | Option.some mx => (ByteArray.mk #[(0x01 : UInt8)]).append ((encodeLEB128U t.lim.min).append (encodeLEB128U mx))
          (ByteArray.mk #[(0x01 : UInt8), elemByte]).append lim
        | .memory m =>
          let lim := match m.lim.max with
            | Option.none => (ByteArray.mk #[(0x00 : UInt8)]).append (encodeLEB128U m.lim.min)
            | Option.some mx => (ByteArray.mk #[(0x01 : UInt8)]).append ((encodeLEB128U m.lim.min).append (encodeLEB128U mx))
          (ByteArray.mk #[(0x02 : UInt8)]).append lim
        | .global gt =>
          let mutByte := match gt.mutability with | .const_ => (0x00 : UInt8) | .var => (0x01 : UInt8)
          (ByteArray.mk #[(0x03 : UInt8), encodeValType gt.val, mutByte])
      modName.append (name.append desc)
    encodeSection (0x02 : UInt8) (encodeVec entries)

/-- Section 3: Function section — type indices for each function. -/
def encodeFunctionSection (funcs : Array Func) : ByteArray :=
  if funcs.isEmpty then ByteArray.mk #[]
  else
    let entries := funcs.toList.map fun f => encodeLEB128U f.typeIdx
    encodeSection (0x03 : UInt8) (encodeVec entries)

/-- Section 4: Table section. -/
def encodeTableSection (tables : Array TableType) : ByteArray :=
  if tables.isEmpty then ByteArray.mk #[]
  else
    let entries := tables.toList.map fun t =>
      let elemByte := match t.elem with | .funcref => (0x70 : UInt8)
      match t.lim.max with
      | Option.none => ByteArray.mk #[elemByte, (0x00 : UInt8)] |>.append (encodeLEB128U t.lim.min)
      | Option.some mx => (ByteArray.mk #[elemByte, (0x01 : UInt8)]).append ((encodeLEB128U t.lim.min).append (encodeLEB128U mx))
    encodeSection (0x04 : UInt8) (encodeVec entries)

/-- Encode limits. -/
def encodeLimits (lim : Limits) : ByteArray :=
  match lim.max with
  | Option.none => (ByteArray.mk #[(0x00 : UInt8)]).append (encodeLEB128U lim.min)
  | Option.some mx => (ByteArray.mk #[(0x01 : UInt8)]).append ((encodeLEB128U lim.min).append (encodeLEB128U mx))

/-- Section 5: Memory section. -/
def encodeMemorySection (memories : Array MemType) : ByteArray :=
  if memories.isEmpty then ByteArray.mk #[]
  else
    let entries := memories.toList.map fun m => encodeLimits m.lim
    encodeSection (0x05 : UInt8) (encodeVec entries)

/-- Section 6: Global section. -/
def encodeGlobalSection (globals : Array Global) : ByteArray :=
  if globals.isEmpty then ByteArray.mk #[]
  else
    let entries := globals.toList.map fun g =>
      let vtByte := encodeValType g.type.val
      let mutByte := match g.type.mutability with | .const_ => (0x00 : UInt8) | .var => (0x01 : UInt8)
      (ByteArray.mk #[vtByte, mutByte]).append (encodeExpr g.init)
    encodeSection (0x06 : UInt8) (encodeVec entries)

/-- Section 7: Export section. -/
def encodeExportSection (exports : Array Export) : ByteArray :=
  if exports.isEmpty then ByteArray.mk #[]
  else
    let entries := exports.toList.map fun e =>
      let name := encodeName e.name
      let desc := match e.desc with
        | .func idx => (ByteArray.mk #[(0x00 : UInt8)]).append (encodeLEB128U idx)
        | .table idx => (ByteArray.mk #[(0x01 : UInt8)]).append (encodeLEB128U idx)
        | .memory idx => (ByteArray.mk #[(0x02 : UInt8)]).append (encodeLEB128U idx)
        | .global idx => (ByteArray.mk #[(0x03 : UInt8)]).append (encodeLEB128U idx)
      name.append desc
    encodeSection (0x07 : UInt8) (encodeVec entries)

/-- Section 8: Start section. -/
def encodeStartSection (start : Option FuncIdx) : ByteArray :=
  match start with
  | Option.none => ByteArray.mk #[]
  | Option.some idx => encodeSection (0x08 : UInt8) (encodeLEB128U idx)

/-- Section 9: Element section. -/
def encodeElementSection (elems : Array ElemSegment) : ByteArray :=
  if elems.isEmpty then ByteArray.mk #[]
  else
    let entries := elems.toList.map fun seg =>
      let tableIdx := encodeLEB128U seg.tableIdx
      let offset := encodeExpr seg.offset
      let funcIdxs := encodeVec (seg.funcIdxs.map encodeLEB128U)
      tableIdx.append (offset.append funcIdxs)
    encodeSection (0x09 : UInt8) (encodeVec entries)

/-- Encode a function body for the code section. -/
def encodeFuncBody (f : Func) : ByteArray :=
  -- Compress locals: group consecutive same-type locals
  let localGroups := f.locals.foldl (fun acc t =>
    match acc with
    | [] => [(1, t)]
    | (n, t') :: rest => if t == t' then (n + 1, t') :: rest else (1, t) :: (n, t') :: rest
    ) ([] : List (Nat × ValType))
  let localGroups := localGroups.reverse
  let localsEncoded := encodeVec (localGroups.map fun (n, t) =>
    (encodeLEB128U n).append (ByteArray.mk #[encodeValType t]))
  let bodyBytes := encodeExpr f.body
  let funcBytes := localsEncoded.append bodyBytes
  -- Prefix with size
  (encodeLEB128U funcBytes.size).append funcBytes

/-- Section 10: Code section. -/
def encodeCodeSection (funcs : Array Func) : ByteArray :=
  if funcs.isEmpty then ByteArray.mk #[]
  else
    let entries := funcs.toList.map encodeFuncBody
    encodeSection (0x0A : UInt8) (encodeVec entries)

/-- Section 11: Data section. -/
def encodeDataSection (datas : Array DataSegment) : ByteArray :=
  if datas.isEmpty then ByteArray.mk #[]
  else
    let entries := datas.toList.map fun seg =>
      let memIdx := encodeLEB128U seg.memIdx
      let offset := encodeExpr seg.offset
      let initData := encodeByteVec seg.init
      memIdx.append (offset.append initData)
    encodeSection (0x0B : UInt8) (encodeVec entries)

-- ============================================================
-- Main encoder
-- ============================================================

/-- Encode a Wasm module to binary format. -/
def encodeBinary (m : Module) : ByteArray :=
  let magic := ByteArray.mk #[(0x00 : UInt8), (0x61 : UInt8), (0x73 : UInt8), (0x6D : UInt8)]
  let version := ByteArray.mk #[(0x01 : UInt8), (0x00 : UInt8), (0x00 : UInt8), (0x00 : UInt8)]
  let header := magic.append version
  let s1 := encodeTypeSection m.types
  let s2 := encodeImportSection m.imports
  let s3 := encodeFunctionSection m.funcs
  let s4 := encodeTableSection m.tables
  let s5 := encodeMemorySection m.memories
  let s6 := encodeGlobalSection m.globals
  let s7 := encodeExportSection m.exports
  let s8 := encodeStartSection m.start
  let s9 := encodeElementSection m.elems
  let s10 := encodeCodeSection m.funcs
  let s11 := encodeDataSection m.datas
  header
    |>.append s1 |>.append s2 |>.append s3 |>.append s4
    |>.append s5 |>.append s6 |>.append s7 |>.append s8
    |>.append s9 |>.append s10 |>.append s11

/-- Write a Wasm module to a .wasm file. -/
def writeWasm (m : Module) (path : String) : IO Unit := do
  let bytes := encodeBinary m
  IO.FS.writeBinFile ⟨path⟩ bytes

end VerifiedJS.Wasm
