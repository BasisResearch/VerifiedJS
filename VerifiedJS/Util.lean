/-
  VerifiedJS — Shared Utility Functions
  Dedup target: all shared helpers should be coalesced here.
-/

namespace VerifiedJS.Util

/-- Read a file's contents -/
def readFile (path : String) : IO String := do
  IO.FS.readFile ⟨path⟩

/-- Write a string to a file -/
def writeFile (path : String) (content : String) : IO Unit := do
  IO.FS.writeFile ⟨path⟩ content

/-- Write bytes to a file -/
def writeBytes (path : String) (content : ByteArray) : IO Unit := do
  IO.FS.writeBinFile ⟨path⟩ content

end VerifiedJS.Util
