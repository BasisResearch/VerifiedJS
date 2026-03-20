/-
  VerifiedJS — Root module
  A formally verified JavaScript-to-WebAssembly compiler in Lean 4.
-/

-- Source (outside TCB)
import VerifiedJS.Source.AST
import VerifiedJS.Source.Lexer
import VerifiedJS.Source.Parser
import VerifiedJS.Source.Print

-- Core IL
import VerifiedJS.Core.Syntax
import VerifiedJS.Core.Semantics
import VerifiedJS.Core.Interp
import VerifiedJS.Core.Print
import VerifiedJS.Core.Elaborate

-- Flat IL
import VerifiedJS.Flat.Syntax
import VerifiedJS.Flat.Semantics
import VerifiedJS.Flat.Interp
import VerifiedJS.Flat.Print
import VerifiedJS.Flat.ClosureConvert

-- ANF IL
import VerifiedJS.ANF.Syntax
import VerifiedJS.ANF.Semantics
import VerifiedJS.ANF.Interp
import VerifiedJS.ANF.Print
import VerifiedJS.ANF.Convert
import VerifiedJS.ANF.Optimize

-- Wasm
import VerifiedJS.Wasm.Syntax
import VerifiedJS.Wasm.Typing
import VerifiedJS.Wasm.Semantics
import VerifiedJS.Wasm.Numerics
import VerifiedJS.Wasm.Interp
import VerifiedJS.Wasm.Print
import VerifiedJS.Wasm.IR
import VerifiedJS.Wasm.IRInterp
import VerifiedJS.Wasm.IRPrint
import VerifiedJS.Wasm.Lower
import VerifiedJS.Wasm.Emit
import VerifiedJS.Wasm.Binary

-- Runtime
import VerifiedJS.Runtime.Values
import VerifiedJS.Runtime.GC
import VerifiedJS.Runtime.Objects
import VerifiedJS.Runtime.Strings
import VerifiedJS.Runtime.Regex
import VerifiedJS.Runtime.Generators

-- Proofs
import VerifiedJS.Proofs.ElaborateCorrect
import VerifiedJS.Proofs.ClosureConvertCorrect
import VerifiedJS.Proofs.ANFConvertCorrect
import VerifiedJS.Proofs.OptimizeCorrect
import VerifiedJS.Proofs.LowerCorrect
import VerifiedJS.Proofs.EmitCorrect
import VerifiedJS.Proofs.EndToEnd

-- Utilities
import VerifiedJS.Util
