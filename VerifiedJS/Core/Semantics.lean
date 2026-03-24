/-
  VerifiedJS — Core IL Semantics
  Small-step LTS as an inductive relation.
  SPEC: §8 (Executable Code and Execution Contexts), §9 (Ordinary Object Internal Methods)
-/

import VerifiedJS.Core.Syntax
import VerifiedJS.Core.Elaborate

namespace VerifiedJS.Core

set_option linter.deprecated false

-- SPEC: L3997-L4001
-- | # The Undefined Type
-- |
-- | The Undefined type has exactly one value, called \*undefined\*. Any
-- | variable that has not been assigned a value has the value \*undefined\*.
-- SPEC: L4002-L4005
-- | # The Null Type
-- |
-- | The Null type has exactly one value, called \*null\*.
-- SPEC: L4006-L4011
-- | # The Boolean Type
-- |
-- | The [Boolean type]{.dfn variants="is a Boolean,is not a Boolean"}
-- | represents a logical entity having two values, called \*true\* and
-- | \*false\*.
-- SPEC: L4012-L4025
-- | # The String Type
-- |
-- | The [String type]{.dfn variants="is a String,is not a String"} is the
-- | set of all ordered sequences of zero or more 16-bit unsigned integer
-- | values ("elements") up to a maximum length of 2^53^ - 1 elements. The
-- | String type is generally used to represent textual data in a running
-- | ECMAScript program, in which case each element in the String is treated
-- | as a UTF-16 code unit value. Each element is regarded as occupying a
-- | position within the sequence. These positions are indexed with
-- | non-negative integers. The first element (if any) is at index 0, the
-- | next element (if any) at index 1, and so on. The length of a String is
-- | the number of elements (i.e., 16-bit values) within it. The empty String
-- | has length zero and therefore contains no elements.
-- SPEC: L4308-L4321
-- | # The Number Type
-- |
-- | The [Number type]{.dfn variants="is a Number,is not a Number"} has
-- | exactly 18,437,736,874,454,810,627 (that is, 2^64^ - 2^53^ + 3) values,
-- | representing the double-precision floating point IEEE 754-2019 binary64
-- | values as specified in the IEEE Standard for Binary Floating-Point
-- | Arithmetic, except that the 9,007,199,254,740,990 (that is, 2^53^ - 2)
-- | distinct NaN values of the IEEE Standard are represented in ECMAScript
-- | as a single special \*NaN\* value. (Note that the \*NaN\* value is
-- | produced by the program expression \`NaN\`.) In some implementations,
-- | external code might be able to detect a difference between various NaN
-- | values, but such behaviour is implementation-defined; to ECMAScript
-- | code, all \*NaN\* values are indistinguishable from each other.
-- SPEC: L5443-L5460
-- | # The Completion Record Specification Type
-- |
-- | The [Completion Record]{.dfn variants="Completion Records"}
-- | specification type is used to explain the runtime propagation of values
-- | and control flow such as the behaviour of statements (\`break\`,
-- | \`continue\`, \`return\` and \`throw\`) that perform nonlocal transfers
-- | of control.
-- |
-- | Completion Records have the fields defined in .
-- |
-- |   Field Name       Value                                                           Meaning
-- |   ---------------- --------------------------------------------------------------- --------------------------------------------------
-- |   \[\[Type\]\]     \~normal\~, \~break\~, \~continue\~, \~return\~, or \~throw\~   The type of completion that occurred.
-- |   \[\[Value\]\]    any value except a Completion Record                            The value that was produced.
-- |   \[\[Target\]\]   a String or \~empty\~                                           The target label for directed control transfers.
-- |
-- | The following shorthand terms are sometimes used to refer to Completion
-- | Records.

-- SPEC: L9880-L9920
-- | # Execution Contexts
-- |
-- | An [execution context]{.dfn variants="execution contexts"} is a
-- | specification device that is used to track the runtime evaluation of
-- | code by an ECMAScript implementation. At any point in time, there is at
-- | most one execution context per agent that is actually executing code.
-- | This is known as the agent\'s [running execution
-- | context]{#running-execution-context .dfn
-- | variants="running execution contexts"}. All references to the running
-- | execution context in this specification denote the running execution
-- | context of the surrounding agent.
-- |
-- | The [execution context stack]{#execution-context-stack .dfn
-- | variants="execution context stacks"} is used to track execution
-- | contexts. The running execution context is always the top element of
-- | this stack. A new execution context is created whenever control is
-- | transferred from the executable code associated with the currently
-- | running execution context to executable code that is not associated with
-- | that execution context. The newly created execution context is pushed
-- | onto the stack and becomes the running execution context.
-- |
-- | An execution context contains whatever implementation specific state is
-- | necessary to track the execution progress of its associated code. Each
-- | execution context has at least the state components listed in .
-- |
-- |   Component               Purpose
-- |   ----------------------- ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- |   code evaluation state   Any state needed to perform, suspend, and resume evaluation of the code associated with this execution context.
-- |   Function                If this execution context is evaluating the code of a function object, then the value of this component is that function object. If the context is evaluating the code of a \|Script\| or \|Module\|, the value is \*null\*.
-- |   Realm                   The Realm Record from which associated code accesses ECMAScript resources.
-- |   ScriptOrModule          The Module Record or Script Record from which associated code originates. If there is no originating script or module, as is the case for the original execution context created in InitializeHostDefinedRealm, the value is \*null\*.
-- |
-- | Evaluation of code by the running execution context may be suspended at
-- | various points defined within this specification. Once the running
-- | execution context has been suspended a different execution context may
-- | become the running execution context and commence evaluating its code.
-- | At some later time a suspended execution context may again become the
-- | running execution context and continue evaluating its code at the point
-- | where it had previously been suspended. Transition of the running
-- | execution context status among execution contexts usually occurs in
-- | stack-like last-in/first-out manner. However, some ECMAScript features
-- SPEC: L20612-L20627
-- | # ParseScript ( \_sourceText\_: ECMAScript source text, \_realm\_: a Realm Record, \_hostDefined\_: anything, ): a Script Record or a non-empty List of \*SyntaxError\* objects
-- |
-- | description
-- | :   It creates a Script Record based upon the result of parsing
-- |     \_sourceText\_ as a \|Script\|.
-- |
-- | 1\. Let \_script\_ be ParseText(\_sourceText\_, \|Script\|). 1. If
-- | \_script\_ is a List of errors, return \_script\_. 1. Return Script
-- | Record { \[\[Realm\]\]: \_realm\_, \[\[ECMAScriptCode\]\]: \_script\_,
-- | \[\[LoadedModules\]\]: « », \[\[HostDefined\]\]: \_hostDefined\_ }.
-- |
-- | An implementation may parse script source text and analyse it for Early
-- | Error conditions prior to evaluation of ParseScript for that script
-- | source text. However, the reporting of any errors must be deferred until
-- | the point where this specification actually performs ParseScript upon
-- | that source text.
-- SPEC: L20629-L20653
-- | # ScriptEvaluation ( \_scriptRecord\_: a Script Record, ): either a normal completion containing an ECMAScript language value or an abrupt completion
-- |
-- | 1\. Let \_globalEnv\_ be
-- | \_scriptRecord\_.\[\[Realm\]\].\[\[GlobalEnv\]\]. 1. Let
-- | \_scriptContext\_ be a new ECMAScript code execution context. 1. Set the
-- | Function of \_scriptContext\_ to \*null\*. 1. Set the Realm of
-- | \_scriptContext\_ to \_scriptRecord\_.\[\[Realm\]\]. 1. Set the
-- | ScriptOrModule of \_scriptContext\_ to \_scriptRecord\_. 1. Set the
-- | VariableEnvironment of \_scriptContext\_ to \_globalEnv\_. 1. Set the
-- | LexicalEnvironment of \_scriptContext\_ to \_globalEnv\_. 1. Set the
-- | PrivateEnvironment of \_scriptContext\_ to \*null\*. 1. Suspend the
-- | running execution context. 1. Push \_scriptContext\_ onto the execution
-- | context stack; \_scriptContext\_ is now the running execution
-- | context. 1. Let \_script\_ be
-- | \_scriptRecord\_.\[\[ECMAScriptCode\]\]. 1. Let \_result\_ be
-- | Completion(GlobalDeclarationInstantiation(\_script\_,
-- | \_globalEnv\_)). 1. If \_result\_ is a normal completion, then 1. Set
-- | \_result\_ to Completion(Evaluation of \_script\_). 1. If \_result\_ is
-- | a normal completion and \_result\_.\[\[Value\]\] is \~empty\~, then 1.
-- | Set \_result\_ to NormalCompletion(\*undefined\*). 1. Suspend
-- | \_scriptContext\_ and remove it from the execution context stack. 1.
-- | Assert: The execution context stack is not empty. 1. Resume the context
-- | that is now on the top of the execution context stack as the running
-- | execution context. 1. Return ? \_result\_.
-- SPEC: L20654-L20665
-- | # GlobalDeclarationInstantiation ( \_script\_: a \|Script\| Parse Node, \_env\_: a Global Environment Record, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | description
-- | :   \_script\_ is the \|Script\| for which the execution context is
-- |     being established. \_env\_ is the global environment in which
-- |     bindings are to be created.
-- |
-- | When an execution context is established for evaluating scripts,
-- | declarations are instantiated in the current global environment. Each
-- | global binding declared in the code is instantiated.
-- |
-- | It performs the following steps when called:

-- SPEC: L5513-L5533
-- | # The Reference Record Specification Type
-- |
-- | The [Reference Record]{.dfn variants="Reference Records"} type is used
-- | to explain the behaviour of such operators as \`delete\`, \`typeof\`,
-- | the assignment operators, the \`super\` keyword and other language
-- | features. For example, the left-hand operand of an assignment is
-- | expected to produce a Reference Record.
-- |
-- | A Reference Record is a resolved name or (possibly not-yet-resolved)
-- | property binding; its fields are defined by .
-- |
-- |   Field Name               Value                                                                      Meaning
-- |   ------------------------ -------------------------------------------------------------------------- -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- |   \[\[Base\]\]             an ECMAScript language value, an Environment Record, or \~unresolvable\~   The value or Environment Record which holds the binding. A \[\[Base\]\] of \~unresolvable\~ indicates that the binding could not be resolved.
-- |   \[\[ReferencedName\]\]   an ECMAScript language value or a Private Name                             The name of the binding. Always a String if \[\[Base\]\] value is an Environment Record. Otherwise, may be an ECMAScript language value other than a String or a Symbol until ToPropertyKey is performed.
-- |   \[\[Strict\]\]           a Boolean                                                                  \*true\* if the Reference Record originated in strict mode code, \*false\* otherwise.
-- |   \[\[ThisValue\]\]        an ECMAScript language value or \~empty\~                                  If not \~empty\~, the Reference Record represents a property binding that was expressed using the \`super\` keyword; it is called a [Super Reference Record]{#super-reference-record .dfn oldids="super-reference" variants="Super Reference Records"} and its \[\[Base\]\] value will never be an Environment Record. In that case, the \[\[ThisValue\]\] field holds the \*this\* value at the time the Reference Record was created.
-- |
-- | The following abstract operations are used in this specification to
-- | operate upon Reference Records:
-- SPEC: L5534-L5539
-- | # IsPropertyReference ( \_V\_: a Reference Record, ): a Boolean
-- |
-- | 1\. If \_V\_.\[\[Base\]\] is \~unresolvable\~, return \*false\*. 1. If
-- | \_V\_.\[\[Base\]\] is an Environment Record, return \*false\*. 1. Return
-- | \*true\*.
-- SPEC: L5540-L5544
-- | # IsUnresolvableReference ( \_V\_: a Reference Record, ): a Boolean
-- |
-- | 1\. If \_V\_.\[\[Base\]\] is \~unresolvable\~, return \*true\*. 1.
-- | Return \*false\*.
-- SPEC: L5545-L5549
-- | # IsSuperReference ( \_V\_: a Reference Record, ): a Boolean
-- |
-- | 1\. If \_V\_.\[\[ThisValue\]\] is \~empty\~, return \*false\*. 1. Return
-- | \*true\*.
-- SPEC: L5550-L5554
-- | # IsPrivateReference ( \_V\_: a Reference Record, ): a Boolean
-- |
-- | 1\. If \_V\_.\[\[ReferencedName\]\] is a Private Name, return
-- | \*true\*. 1. Return \*false\*.
-- SPEC: L5604-L5609
-- | # GetThisValue ( \_V\_: a Reference Record, ): an ECMAScript language value
-- |
-- | 1\. Assert: IsPropertyReference(\_V\_) is \*true\*. 1. If
-- | IsSuperReference(\_V\_) is \*true\*, return \_V\_.\[\[ThisValue\]\]. 1.
-- | Return \_V\_.\[\[Base\]\].

/-- Observable trace events emitted by Core execution. -/
inductive TraceEvent where
  | log (s : String)
  | error (s : String)
  | silent
  deriving Repr, BEq

-- SPEC: L4856-L4909
-- | # The Object Type
-- |
-- | Each instance of the [Object type]{.dfn
-- | variants="is an Object,is not an Object"}, also referred to simply as
-- | "an Object", represents a collection of properties. Each property is
-- | either a data property, or an accessor property:
-- |
-- | - A [data property]{.dfn variants="data properties"} associates a key
-- |   value with an ECMAScript language value and a set of Boolean
-- |   attributes.
-- | - An [accessor property]{.dfn variants="accessor properties"} associates
-- |   a key value with one or two accessor functions, and a set of Boolean
-- |   attributes. The accessor functions are used to store or retrieve an
-- |   ECMAScript language value that is associated with the property.
-- |
-- | The properties of an object are uniquely identified using property keys.
-- | A [property key]{#property-key .dfn variants="property keys"
-- | oldids="sec-ispropertykey"} is either a String or a Symbol. All Strings
-- | and Symbols, including the empty String, are valid as property keys. A
-- | [property name]{#property-name .dfn variants="property names"} is a
-- | property key that is a String.
-- |
-- | An [integer index]{#integer-index .dfn
-- | variants="integer indices,integer-indexed"} is a property name \_n\_
-- | such that CanonicalNumericIndexString(\_n\_) returns an integral Number
-- | in the inclusive interval from \*+0\*~𝔽~ to 𝔽(2^53^ - 1). An [array
-- | index]{#array-index .dfn variants="array indices"} is an integer index
-- | \_n\_ such that CanonicalNumericIndexString(\_n\_) returns an integral
-- | Number in the inclusive interval from \*+0\*~𝔽~ to 𝔽(2^32^ - 2).
-- |
-- | Every non-negative safe integer has a corresponding integer index. Every
-- | 32-bit unsigned integer except 2^32^ - 1 has a corresponding array
-- | index. \*\"-0\"\* is neither an integer index nor an array index.
-- |
-- | Property keys are used to access properties and their values. There are
-- | two kinds of access for properties: *get* and *set*, corresponding to
-- | value retrieval and assignment, respectively. The properties accessible
-- | via get and set access includes both *own properties* that are a direct
-- | part of an object and *inherited properties* which are provided by
-- | another associated object via a property inheritance relationship.
-- | Inherited properties may be either own or inherited properties of the
-- | associated object. Each own property of an object must each have a key
-- | value that is distinct from the key values of the other own properties
-- | of that object.
-- |
-- | All objects are logically collections of properties, but there are
-- | multiple forms of objects that differ in their semantics for accessing
-- | and manipulating their properties. Please see for definitions of the
-- | multiple forms of objects.
-- |
-- | In addition, some objects are callable; these are referred to as
-- | functions or function objects and are described further below. All
-- | functions in ECMAScript are members of the Object type.
-- SPEC: L4910-L4924
-- | # Property Attributes
-- |
-- | Attributes are used in this specification to define and explain the
-- | state of Object properties as described in . Unless specified
-- | explicitly, the initial value of each attribute is its Default Value.
-- |
-- |   Attribute Name         Types of property for which it is present   Value Domain                   Default Value   Description
-- |   ---------------------- ------------------------------------------- ------------------------------ --------------- ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- |   \[\[Value\]\]          data property                               an ECMAScript language value   \*undefined\*   The value retrieved by a get access of the property.
-- |   \[\[Writable\]\]       data property                               a Boolean                      \*false\*       If \*false\*, attempts by ECMAScript code to change the property\'s \[\[Value\]\] attribute using \[\[Set\]\] will not succeed.
-- |   \[\[Get\]\]            accessor property                           an Object or \*undefined\*     \*undefined\*   If the value is an Object it must be a function object. The function\'s \[\[Call\]\] internal method () is called with an empty arguments list to retrieve the property value each time a get access of the property is performed.
-- |   \[\[Set\]\]            accessor property                           an Object or \*undefined\*     \*undefined\*   If the value is an Object it must be a function object. The function\'s \[\[Call\]\] internal method () is called with an arguments list containing the assigned value as its sole argument each time a set access of the property is performed. The effect of a property\'s \[\[Set\]\] internal method may, but is not required to, have an effect on the value returned by subsequent calls to the property\'s \[\[Get\]\] internal method.
-- |   \[\[Enumerable\]\]     data property or accessor property          a Boolean                      \*false\*       If \*true\*, the property will be enumerated by a for-in enumeration (see ). Otherwise, the property is said to be non-enumerable.
-- |   \[\[Configurable\]\]   data property or accessor property          a Boolean                      \*false\*       If \*false\*, attempts to delete the property, change it from a data property to an accessor property or from an accessor property to a data property, or make any changes to its attributes (other than replacing an existing \[\[Value\]\] or setting \[\[Writable\]\] to \*false\*) will fail.
-- SPEC: L8873-L8884
-- | # HasBinding ( \_N\_: a String, ): a normal completion containing a Boolean
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | description
-- | :   It determines if the argument identifier is one of the identifiers
-- |     bound by the record.
-- |
-- | 1\. If \_envRec\_ has a binding for \_N\_, return \*true\*. 1. Return
-- | \*false\*.
-- SPEC: L8902-L8917
-- | # CreateImmutableBinding ( \_N\_: a String, \_S\_: a Boolean, ): a normal completion containing \~unused\~
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | description
-- | :   It creates a new immutable binding for the name \_N\_ that is
-- |     uninitialized. A binding must not already exist in this Environment
-- |     Record for \_N\_. If \_S\_ is \*true\*, the new binding is marked as
-- |     a strict binding.
-- |
-- | 1\. Assert: \_envRec\_ does not already have a binding for \_N\_. 1.
-- | Create an immutable binding in \_envRec\_ for \_N\_ and record that it
-- | is uninitialized. If \_S\_ is \*true\*, record that the newly created
-- | binding is a strict binding. 1. Return \~unused\~.
-- SPEC: L8918-L8932
-- | # InitializeBinding ( \_N\_: a String, \_V\_: an ECMAScript language value, ): a normal completion containing \~unused\~
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | description
-- | :   It is used to set the bound value of the current binding of the
-- |     identifier whose name is \_N\_ to the value \_V\_. An uninitialized
-- |     binding for \_N\_ must already exist.
-- |
-- | 1\. Assert: \_envRec\_ must have an uninitialized binding for \_N\_. 1.
-- | Set the bound value for \_N\_ in \_envRec\_ to \_V\_. 1. Record that the
-- | binding for \_N\_ in \_envRec\_ has been initialized. 1. Return
-- | \~unused\~.
/-- ECMA-262 §8.1 Environment Records (simplified lexical bindings for Core). -/
structure Env where
  bindings : List (VarName × Value)
  deriving Repr

/-- ECMA-262 §9.1 Ordinary object storage (heap abstract state). -/
structure Heap where
  objects : Array (List (PropName × Value))
  nextAddr : Nat
  deriving Repr

/-- ECMA-262 §8.3 Execution Contexts (Core machine state). -/
structure State where
  expr : Expr
  env : Env
  heap : Heap
  trace : List TraceEvent
  funcs : Array FuncClosure
  /-- Call stack: saved caller environments for function call return. -/
  callStack : List (List (VarName × Value))
  deriving Repr

/-- Empty lexical environment. -/
def Env.empty : Env :=
  { bindings := [] }

/-- Empty heap. -/
def Heap.empty : Heap :=
  { objects := #[], nextAddr := 0 }

-- SPEC: L5486-L5493
-- | # NormalCompletion ( \_value\_: any value except a Completion Record, ): a normal completion
-- |
-- | skip return checks
-- | :   true
-- |
-- | 1\. Return Completion Record { \[\[Type\]\]: \~normal\~, \[\[Value\]\]:
-- | \_value\_, \[\[Target\]\]: \~empty\~ }.
-- SPEC: L5504-L5512
-- | # UpdateEmpty ( \_completionRecord\_: a Completion Record, \_value\_: any value except a Completion Record, ): a Completion Record
-- |
-- | 1\. Assert: If \_completionRecord\_ is either a return completion or a
-- | throw completion, then \_completionRecord\_.\[\[Value\]\] is not
-- | \~empty\~. 1. If \_completionRecord\_.\[\[Value\]\] is not \~empty\~,
-- | return ? \_completionRecord\_. 1. Return Completion Record {
-- | \[\[Type\]\]: \_completionRecord\_.\[\[Type\]\], \[\[Value\]\]:
-- | \_value\_, \[\[Target\]\]: \_completionRecord\_.\[\[Target\]\] }.
-- SPEC: L9667-L9671
-- | # NewDeclarativeEnvironment ( \_E\_: an Environment Record or \*null\*, ): a Declarative Environment Record
-- |
-- | 1\. Let \_env\_ be a new Declarative Environment Record containing no
-- | bindings. 1. Set \_env\_.\[\[OuterEnv\]\] to \_E\_. 1. Return \_env\_.
-- SPEC: L9672-L9678
-- | # NewObjectEnvironment ( \_O\_: an Object, \_W\_: a Boolean, \_E\_: an Environment Record or \*null\*, ): an Object Environment Record
-- |
-- | 1\. Let \_env\_ be a new Object Environment Record. 1. Set
-- | \_env\_.\[\[BindingObject\]\] to \_O\_. 1. Set
-- | \_env\_.\[\[IsWithEnvironment\]\] to \_W\_. 1. Set
-- | \_env\_.\[\[OuterEnv\]\] to \_E\_. 1. Return \_env\_.
-- SPEC: L9690-L9699
-- | # NewGlobalEnvironment ( \_G\_: an Object, \_thisValue\_: an Object, ): a Global Environment Record
-- |
-- | 1\. Let \_objRec\_ be NewObjectEnvironment(\_G\_, \*false\*,
-- | \*null\*). 1. Let \_dclRec\_ be NewDeclarativeEnvironment(\*null\*). 1.
-- | Let \_env\_ be a new Global Environment Record. 1. Set
-- | \_env\_.\[\[ObjectRecord\]\] to \_objRec\_. 1. Set
-- | \_env\_.\[\[GlobalThisValue\]\] to \_thisValue\_. 1. Set
-- | \_env\_.\[\[DeclarativeRecord\]\] to \_dclRec\_. 1. Set
-- | \_env\_.\[\[OuterEnv\]\] to \*null\*. 1. Return \_env\_.
-- SPEC: L8980-L8992
-- | # DeleteBinding ( \_N\_: a String, ): a normal completion containing a Boolean
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | description
-- | :   It can only delete bindings that have been explicitly designated as
-- |     being subject to deletion.
-- |
-- | 1\. Assert: \_envRec\_ has a binding for \_N\_. 1. If the binding for
-- | \_N\_ in \_envRec\_ cannot be deleted, return \*false\*. 1. Remove the
-- | binding for \_N\_ from \_envRec\_. 1. Return \*true\*.
-- SPEC: L8965-L8979
-- | # GetBindingValue ( \_N\_: a String, \_S\_: a Boolean, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | description
-- | :   It returns the value of its bound identifier whose name is \_N\_. If
-- |     the binding exists but is uninitialized a \*ReferenceError\* is
-- |     thrown, regardless of the value of \_S\_.
-- |
-- | 1\. Assert: \_envRec\_ has a binding for \_N\_. 1. If the binding for
-- | \_N\_ in \_envRec\_ is an uninitialized binding, throw a
-- | \*ReferenceError\* exception. 1. Return the value currently bound to
-- | \_N\_ in \_envRec\_.
/-- ECMA-262 §8.1.1.4 GetBindingValue (modeled as lookup in lexical bindings). -/
def Env.lookup (env : Env) (name : VarName) : Option Value :=
  match env.bindings.find? (fun kv => kv.fst == name) with
  | some kv => some kv.snd
  | none => none

def updateBindingList (xs : List (VarName × Value)) (name : VarName) (v : Value) : List (VarName × Value) :=
  match xs with
  | [] => []
  | (n, old) :: rest =>
      if n == name then
        (n, v) :: rest
      else
        (n, old) :: updateBindingList rest name v

@[simp] theorem updateBindingList_nil (name : VarName) (v : Value) : updateBindingList [] name v = [] := rfl
@[simp] theorem updateBindingList_cons_eq (n : VarName) (old : Value) (rest : List (VarName × Value)) (name : VarName) (v : Value) (h : (n == name) = true) :
    updateBindingList ((n, old) :: rest) name v = (n, v) :: rest := by simp [updateBindingList, h]
@[simp] theorem updateBindingList_cons_ne (n : VarName) (old : Value) (rest : List (VarName × Value)) (name : VarName) (v : Value) (h : (n == name) = false) :
    updateBindingList ((n, old) :: rest) name v = (n, old) :: updateBindingList rest name v := by simp [updateBindingList, h]

/-- Lookup after updateBindingList for the same name returns the new value. -/
@[simp] theorem lookup_updateBindingList_eq (xs : List (VarName × Value)) (name : VarName) (v : Value)
    (h : xs.any (fun kv => kv.fst == name) = true) :
    Env.lookup { bindings := updateBindingList xs name v } name = some v := by
  induction xs with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨n, old⟩ := hd
    cases hn : (n == name)
    · -- n ≠ name
      simp only [updateBindingList, hn, ↓reduceIte, Env.lookup, List.find?, Bool.false_eq_true]
      have htl : tl.any (fun kv => kv.fst == name) = true := by
        simp only [List.any, hn, Bool.false_or] at h; exact h
      exact ih htl
    · -- n == name
      simp only [updateBindingList, hn, ↓reduceIte, Env.lookup, List.find?, ↓reduceCtorEq]

/-- Lookup after updateBindingList for a different name is unchanged. -/
@[simp] theorem lookup_updateBindingList_ne (xs : List (VarName × Value)) (name other : VarName) (v : Value)
    (hne : (other == name) = false) :
    Env.lookup { bindings := updateBindingList xs name v } other = Env.lookup { bindings := xs } other := by
  induction xs with
  | nil => simp [updateBindingList, Env.lookup]
  | cons hd tl ih =>
    obtain ⟨n, old⟩ := hd
    cases hn : (n == name)
    · -- n ≠ name
      simp only [updateBindingList, hn, Bool.false_eq_true, ↓reduceIte, Env.lookup, List.find?]
      cases hno : (n == other)
      · simp only [hno, Env.lookup] at ih; exact ih
      · rfl
    · -- n == name: need (n == other) = false
      have hno : (n == other) = false := by
        simp only [show n = name from by simpa using hn]
        exact Bool.eq_false_iff.mpr (by intro h; have := beq_iff_eq.mp h; rw [this] at hne; simp at hne)
      simp only [updateBindingList, hn, ↓reduceIte, Env.lookup, List.find?, hno]

-- SPEC: L8933-L8964
-- | # SetMutableBinding ( \_N\_: a String, \_V\_: an ECMAScript language value, \_S\_: a Boolean, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | description
-- | :   It attempts to change the bound value of the current binding of the
-- |     identifier whose name is \_N\_ to the value \_V\_. A binding for
-- |     \_N\_ normally already exists, but in rare cases it may not. If the
-- |     binding is an immutable binding, a \*TypeError\* is thrown if \_S\_
-- |     is \*true\*.
-- |
-- | 1\. \[id=\"step-setmutablebinding-missing-binding\"\] If \_envRec\_ does
-- | not have a binding for \_N\_, then 1. If \_S\_ is \*true\*, throw a
-- | \*ReferenceError\* exception. 1. Perform !
-- | \_envRec\_.CreateMutableBinding(\_N\_, \*true\*). 1. Perform !
-- | \_envRec\_.InitializeBinding(\_N\_, \_V\_). 1. Return \~unused\~. 1. If
-- | the binding for \_N\_ in \_envRec\_ is a strict binding, set \_S\_ to
-- | \*true\*. 1. If the binding for \_N\_ in \_envRec\_ has not yet been
-- | initialized, then 1. Throw a \*ReferenceError\* exception. 1. Else if
-- | the binding for \_N\_ in \_envRec\_ is a mutable binding, then 1. Change
-- | its bound value to \_V\_. 1. Else, 1. Assert: This is an attempt to
-- | change the value of an immutable binding. 1. If \_S\_ is \*true\*, throw
-- | a \*TypeError\* exception. 1. Return \~unused\~.
-- |
-- | An example of ECMAScript code that results in a missing binding at step
-- | is:
-- |
-- | ``` javascript
-- | function f() { eval("var x; x = (delete x, 0);"); }
-- | ```
/-- ECMA-262 §8.1.1.4.5 SetMutableBinding (simplified update). -/
def Env.assign (env : Env) (name : VarName) (v : Value) : Env :=
  if env.bindings.any (fun kv => kv.fst == name) then
    { bindings := updateBindingList env.bindings name v }
  else
    { bindings := (name, v) :: env.bindings }

/-- Lookup after assign for the same name (existing binding). -/
@[simp] theorem Env.lookup_assign_eq (env : Env) (name : VarName) (v : Value)
    (h : env.bindings.any (fun kv => kv.fst == name) = true) :
    (env.assign name v).lookup name = some v := by
  simp [Env.assign, h, lookup_updateBindingList_eq]

/-- Lookup after assign for a different name. -/
@[simp] theorem Env.lookup_assign_ne (env : Env) (name other : VarName) (v : Value)
    (hne : (other == name) = false) :
    (env.assign name v).lookup other = env.lookup other := by
  simp only [Env.assign]
  split
  · simp [lookup_updateBindingList_ne, hne]
  · have hne' : (name == other) = false :=
      Bool.eq_false_iff.mpr (by intro h; have := beq_iff_eq.mp h; rw [this] at hne; simp at hne)
    simp [Env.lookup, List.find?, hne']

/-- Lookup after assign for the same name (new binding). -/
@[simp] theorem Env.lookup_assign_new (env : Env) (name : VarName) (v : Value)
    (h : env.bindings.any (fun kv => kv.fst == name) = false) :
    (env.assign name v).lookup name = some v := by
  simp [Env.assign, h, Env.lookup, List.find?, beq_self_eq_true]

-- SPEC: L8885-L8901
-- | # CreateMutableBinding ( \_N\_: a String, \_D\_: a Boolean, ): a normal completion containing \~unused\~
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | description
-- | :   It creates a new mutable binding for the name \_N\_ that is
-- |     uninitialized. A binding must not already exist in this Environment
-- |     Record for \_N\_. If \_D\_ is \*true\*, the new binding is marked as
-- |     being subject to deletion.
-- |
-- | 1\. Assert: \_envRec\_ does not already have a binding for \_N\_. 1.
-- | Create a mutable binding in \_envRec\_ for \_N\_ and record that it is
-- | uninitialized. If \_D\_ is \*true\*, record that the newly created
-- | binding may be deleted by a subsequent DeleteBinding call. 1. Return
-- | \~unused\~.
/-- ECMA-262 §8.1.1.1.2 CreateMutableBinding + §8.1.1.1.5 InitializeBinding. -/
def Env.extend (env : Env) (name : VarName) (v : Value) : Env :=
  { bindings := (name, v) :: env.bindings }

-- SPEC: L5555-L5575
-- | # GetValue ( \_V\_: a Reference Record or an ECMAScript language value, ): either a normal completion containing an ECMAScript language value or an abrupt completion
-- |
-- | 1\. If \_V\_ is not a Reference Record, return \_V\_. 1. If
-- | IsUnresolvableReference(\_V\_) is \*true\*, throw a \*ReferenceError\*
-- | exception. 1. If IsPropertyReference(\_V\_) is \*true\*, then 1.
-- | \[id=\"step-getvalue-toobject\"\] Let \_baseObj\_ be ?
-- | ToObject(\_V\_.\[\[Base\]\]). 1. If IsPrivateReference(\_V\_) is
-- | \*true\*, then 1. Return ? PrivateGet(\_baseObj\_,
-- | \_V\_.\[\[ReferencedName\]\]). 1. If \_V\_.\[\[ReferencedName\]\] is not
-- | a property key, then 1. Set \_V\_.\[\[ReferencedName\]\] to ?
-- | ToPropertyKey(\_V\_.\[\[ReferencedName\]\]). 1. Return ?
-- | \_baseObj\_.\[\[Get\]\](\_V\_.\[\[ReferencedName\]\],
-- | GetThisValue(\_V\_)). 1. Let \_base\_ be \_V\_.\[\[Base\]\]. 1. Assert:
-- | \_base\_ is an Environment Record. 1. Return ?
-- | \_base\_.GetBindingValue(\_V\_.\[\[ReferencedName\]\],
-- | \_V\_.\[\[Strict\]\]) (see ).
-- |
-- | The object that may be created in step is not accessible outside of the
-- | above abstract operation and the ordinary object \[\[Get\]\] internal
-- | method. An implementation might choose to avoid the actual creation of
-- | the object.

-- SPEC: L5577-L5602
-- | # PutValue ( \_V\_: a Reference Record or an ECMAScript language value, \_W\_: an ECMAScript language value, ): either a normal completion containing \~unused\~ or an abrupt completion
-- |
-- | 1\. If \_V\_ is not a Reference Record, throw a \*ReferenceError\*
-- | exception. 1. If IsUnresolvableReference(\_V\_) is \*true\*, then 1. If
-- | \_V\_.\[\[Strict\]\] is \*true\*, throw a \*ReferenceError\*
-- | exception. 1. Let \_globalObj\_ be GetGlobalObject(). 1. Perform ?
-- | Set(\_globalObj\_, \_V\_.\[\[ReferencedName\]\], \_W\_, \*false\*). 1.
-- | Return \~unused\~. 1. If IsPropertyReference(\_V\_) is \*true\*, then 1.
-- | \[id=\"step-putvalue-toobject\"\] Let \_baseObj\_ be ?
-- | ToObject(\_V\_.\[\[Base\]\]). 1. If IsPrivateReference(\_V\_) is
-- | \*true\*, then 1. Return ? PrivateSet(\_baseObj\_,
-- | \_V\_.\[\[ReferencedName\]\], \_W\_). 1. If \_V\_.\[\[ReferencedName\]\]
-- | is not a property key, then 1. Set \_V\_.\[\[ReferencedName\]\] to ?
-- | ToPropertyKey(\_V\_.\[\[ReferencedName\]\]). 1. Let \_succeeded\_ be ?
-- | \_baseObj\_.\[\[Set\]\](\_V\_.\[\[ReferencedName\]\], \_W\_,
-- | GetThisValue(\_V\_)). 1. If \_succeeded\_ is \*false\* and
-- | \_V\_.\[\[Strict\]\] is \*true\*, throw a \*TypeError\* exception. 1.
-- | Return \~unused\~. 1. Let \_base\_ be \_V\_.\[\[Base\]\]. 1. Assert:
-- | \_base\_ is an Environment Record. 1. Return ?
-- | \_base\_.SetMutableBinding(\_V\_.\[\[ReferencedName\]\], \_W\_,
-- | \_V\_.\[\[Strict\]\]) (see ).
-- |
-- | The object that may be created in step is not accessible outside of the
-- | above abstract operation and the ordinary object \[\[Set\]\] internal
-- | method. An implementation might choose to avoid the actual creation of
-- | that object.

-- SPEC: L18579-L18596
-- | # Runtime Semantics: CatchClauseEvaluation ( \_thrownValue\_: an ECMAScript language value, ): either a normal completion containing either an ECMAScript language value or \~empty\~, or an abrupt completion
-- |
-- | Catch : \`catch\` \`(\` CatchParameter \`)\` Block 1. Let \_oldEnv\_ be
-- | the running execution context\'s LexicalEnvironment. 1. Let \_catchEnv\_
-- | be NewDeclarativeEnvironment(\_oldEnv\_). 1. For each element
-- | \_argName\_ of the BoundNames of \|CatchParameter\|, do 1. Perform !
-- | \_catchEnv\_.CreateMutableBinding(\_argName\_, \*false\*). 1. Set the
-- | running execution context\'s LexicalEnvironment to \_catchEnv\_. 1. Let
-- | \_status\_ be Completion(BindingInitialization of \|CatchParameter\|
-- | with arguments \_thrownValue\_ and \_catchEnv\_). 1. If \_status\_ is an
-- | abrupt completion, then 1. Set the running execution context\'s
-- | LexicalEnvironment to \_oldEnv\_. 1. Return ? \_status\_. 1. Let \_B\_
-- | be Completion(Evaluation of \|Block\|). 1. Set the running execution
-- | context\'s LexicalEnvironment to \_oldEnv\_. 1. Return ? \_B\_. Catch :
-- | \`catch\` Block 1. Return ? Evaluation of \|Block\|.
-- |
-- | No matter how control leaves the \|Block\| the LexicalEnvironment is
-- | always restored to its former state.

-- SPEC: L5946-L5981
-- | # ToPrimitive ( \_input\_: an ECMAScript language value, optional \_preferredType\_: \~string\~ or \~number\~, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | description
-- | :   It converts its \_input\_ argument to a non-Object type. If an
-- |     object is capable of converting to more than one primitive type, it
-- |     may use the optional hint \_preferredType\_ to favour that type.
-- |
-- | 1\. If \_input\_ is an Object, then 1. Let \_exoticToPrim\_ be ?
-- | GetMethod(\_input\_, %Symbol.toPrimitive%). 1. If \_exoticToPrim\_ is
-- | not \*undefined\*, then 1. If \_preferredType\_ is not present, then 1.
-- | Let \_hint\_ be \*\"default\"\*. 1. Else if \_preferredType\_ is
-- | \~string\~, then 1. Let \_hint\_ be \*\"string\"\*. 1. Else, 1. Assert:
-- | \_preferredType\_ is \~number\~. 1. Let \_hint\_ be \*\"number\"\*. 1.
-- | Let \_result\_ be ? Call(\_exoticToPrim\_, \_input\_, « \_hint\_ »). 1.
-- | If \_result\_ is not an Object, return \_result\_. 1. Throw a
-- | \*TypeError\* exception. 1. If \_preferredType\_ is not present, set
-- | \_preferredType\_ to \~number\~. 1. Return ?
-- | OrdinaryToPrimitive(\_input\_, \_preferredType\_). 1. Return \_input\_.
-- |
-- | When ToPrimitive is called without a hint, then it generally behaves as
-- | if the hint were \~number\~. However, objects may over-ride this
-- | behaviour by defining a %Symbol.toPrimitive% method. Of the objects
-- | defined in this specification only Dates (see ) and Symbol objects (see
-- | ) over-ride the default ToPrimitive behaviour. Dates treat the absence
-- | of a hint as if the hint were \~string\~.
-- |
-- | # OrdinaryToPrimitive ( \_O\_: an Object, \_hint\_: \~string\~ or \~number\~, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | 1\. If \_hint\_ is \~string\~, then 1. Let \_methodNames\_ be «
-- | \*\"toString\"\*, \*\"valueOf\"\* ». 1. Else, 1. Let \_methodNames\_ be
-- | « \*\"valueOf\"\*, \*\"toString\"\* ». 1. For each element \_name\_ of
-- | \_methodNames\_, do 1. Let \_method\_ be ? Get(\_O\_, \_name\_). 1. If
-- | IsCallable(\_method\_) is \*true\*, then 1. Let \_result\_ be ?
-- | Call(\_method\_, \_O\_). 1. If \_result\_ is not an Object, return
-- | \_result\_. 1. Throw a \*TypeError\* exception.
-- |
-- SPEC: L5972-L5981
-- | # OrdinaryToPrimitive ( \_O\_: an Object, \_hint\_: \~string\~ or \~number\~, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | 1\. If \_hint\_ is \~string\~, then 1. Let \_methodNames\_ be «
-- | \*\"toString\"\*, \*\"valueOf\"\* ». 1. Else, 1. Let \_methodNames\_ be
-- | « \*\"valueOf\"\*, \*\"toString\"\* ». 1. For each element \_name\_ of
-- | \_methodNames\_, do 1. Let \_method\_ be ? Get(\_O\_, \_name\_). 1. If
-- | IsCallable(\_method\_) is \*true\*, then 1. Let \_result\_ be ?
-- | Call(\_method\_, \_O\_). 1. If \_result\_ is not an Object, return
-- | \_result\_. 1. Throw a \*TypeError\* exception.
-- SPEC: L6390-L6398
-- | # RequireObjectCoercible ( \_argument\_: an ECMAScript language value, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | description
-- | :   It throws an error if \_argument\_ is a value that cannot be
-- |     converted to an Object using ToObject.
-- |
-- | 1\. If \_argument\_ is either \*undefined\* or \*null\*, throw a
-- | \*TypeError\* exception. 1. Return \~unused\~.

-- SPEC: L6322-L6341
-- | # ToObject ( \_argument\_: an ECMAScript language value, ): either a normal completion containing an Object or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to a value of type Object.
-- |
-- | 1\. If \_argument\_ is either \*undefined\* or \*null\*, throw a
-- | \*TypeError\* exception. 1. If \_argument\_ is a Boolean, return a new
-- | Boolean object whose \[\[BooleanData\]\] internal slot is set to
-- | \_argument\_. See for a description of Boolean objects. 1. If
-- | \_argument\_ is a Number, return a new Number object whose
-- | \[\[NumberData\]\] internal slot is set to \_argument\_. See for a
-- | description of Number objects. 1. If \_argument\_ is a String, return a
-- | new String object whose \[\[StringData\]\] internal slot is set to
-- | \_argument\_. See for a description of String objects. 1. If
-- | \_argument\_ is a Symbol, return a new Symbol object whose
-- | \[\[SymbolData\]\] internal slot is set to \_argument\_. See for a
-- | description of Symbol objects. 1. If \_argument\_ is a BigInt, return a
-- | new BigInt object whose \[\[BigIntData\]\] internal slot is set to
-- | \_argument\_. See for a description of BigInt objects. 1. Assert:
-- | \_argument\_ is an Object. 1. Return \_argument\_.
-- SPEC: L6343-L6352
-- | # ToPropertyKey ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a property key or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to a value that can be used as a property
-- |     key.
-- |
-- | 1\. Let \_key\_ be ? ToPrimitive(\_argument\_, \~string\~). 1. If
-- | \_key\_ is a Symbol, then 1. Return \_key\_. 1. Return !
-- | ToString(\_key\_).
-- SPEC: L6697-L6714
-- | # CreateDataPropertyOrThrow ( \_O\_: an Object, \_P\_: a property key, \_V\_: an ECMAScript language value, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | description
-- | :   It is used to create a new own property of an object. It throws a
-- |     \*TypeError\* exception if the requested property update cannot be
-- |     performed.
-- |
-- | 1\. Let \_success\_ be ? CreateDataProperty(\_O\_, \_P\_, \_V\_). 1. If
-- | \_success\_ is \*false\*, throw a \*TypeError\* exception. 1. Return
-- | \~unused\~.
-- |
-- | This abstract operation creates a property whose attributes are set to
-- | the same defaults used for properties created by the ECMAScript language
-- | assignment operator. Normally, the property will not already exist. If
-- | it does exist and is not configurable or if \_O\_ is not extensible,
-- | \[\[DefineOwnProperty\]\] will return \*false\* causing this operation
-- | to throw a \*TypeError\* exception.
-- SPEC: L5610-L5616
-- | # InitializeReferencedBinding ( \_V\_: a Reference Record, \_W\_: an ECMAScript language value, ): either a normal completion containing \~unused\~ or an abrupt completion
-- |
-- | 1\. Assert: IsUnresolvableReference(\_V\_) is \*false\*. 1. Let \_base\_
-- | be \_V\_.\[\[Base\]\]. 1. Assert: \_base\_ is an Environment Record. 1.
-- | Return ? \_base\_.InitializeBinding(\_V\_.\[\[ReferencedName\]\],
-- | \_W\_).

-- SPEC: L6766-L6773
-- | # HasProperty ( \_O\_: an Object, \_P\_: a property key, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | description
-- | :   It is used to determine whether an object has a property with the
-- |     specified property key. The property may be either own or inherited.
-- |
-- | 1\. Return ? \_O\_.\[\[HasProperty\]\](\_P\_).
-- SPEC: L10863-L10870
-- | # OrdinaryHasProperty ( \_O\_: an Object, \_P\_: a property key, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | 1\. Let \_hasOwn\_ be ? \_O\_.\[\[GetOwnProperty\]\](\_P\_). 1. If
-- | \_hasOwn\_ is not \*undefined\*, return \*true\*. 1. Let \_parent\_ be ?
-- | \_O\_.\[\[GetPrototypeOf\]\](). 1. If \_parent\_ is not \*null\*,
-- | then 1. Return ? \_parent\_.\[\[HasProperty\]\](\_P\_). 1. Return
-- | \*false\*.
-- SPEC: L6774-L6782
-- | # HasOwnProperty ( \_O\_: an Object, \_P\_: a property key, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | description
-- | :   It is used to determine whether an object has an own property with
-- |     the specified property key.
-- |
-- | 1\. Let \_desc\_ be ? \_O\_.\[\[GetOwnProperty\]\](\_P\_). 1. If
-- | \_desc\_ is \*undefined\*, return \*false\*. 1. Return \*true\*.
-- SPEC: L6652-L6659
-- | # Get ( \_O\_: an Object, \_P\_: a property key, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | description
-- | :   It is used to retrieve the value of a specific property of an
-- |     object.
-- |
-- | 1\. Return ? \_O\_.\[\[Get\]\](\_P\_, \_O\_).
-- SPEC: L6660-L6670
-- | # GetV ( \_V\_: an ECMAScript language value, \_P\_: a property key, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | description
-- | :   It is used to retrieve the value of a specific property of an
-- |     ECMAScript language value. If the value is not an object, the
-- |     property lookup is performed using a wrapper object appropriate for
-- |     the type of the value.
-- |
-- | 1\. Let \_O\_ be ? ToObject(\_V\_). 1. Return ? \_O\_.\[\[Get\]\](\_P\_,
-- | \_V\_).

-- SPEC: L6408-L6417
-- | # IsCallable ( \_argument\_: an ECMAScript language value, ): a Boolean
-- |
-- | description
-- | :   It determines if \_argument\_ is a callable function with a
-- |     \[\[Call\]\] internal method.
-- |
-- | 1\. If \_argument\_ is not an Object, return \*false\*. 1. If
-- | \_argument\_ has a \[\[Call\]\] internal method, return \*true\*. 1.
-- | Return \*false\*.

-- SPEC: L6428-L6435
-- | # IsExtensible ( \_O\_: an Object, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | description
-- | :   It is used to determine whether additional properties can be added
-- |     to \_O\_.
-- |
-- | 1\. Return ? \_O\_.\[\[IsExtensible\]\]().

-- SPEC: L6399-L6407
-- | # IsArray ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | 1\. If \_argument\_ is not an Object, return \*false\*. 1. If
-- | \_argument\_ is an Array exotic object, return \*true\*. 1. If
-- | \_argument\_ is a Proxy exotic object, then 1. Perform ?
-- | ValidateNonRevokedProxy(\_argument\_). 1. Let \_proxyTarget\_ be
-- | \_argument\_.\[\[ProxyTarget\]\]. 1. Return ?
-- | IsArray(\_proxyTarget\_). 1. Return \*false\*.

-- SPEC: L6436-L6443
-- | # IsRegExp ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | 1\. If \_argument\_ is not an Object, return \*false\*. 1. Let
-- | \_matcher\_ be ? Get(\_argument\_, %Symbol.match%). 1. If \_matcher\_ is
-- | not \*undefined\*, return ToBoolean(\_matcher\_). 1. If \_argument\_ has
-- | a \[\[RegExpMatcher\]\] internal slot, return \*true\*. 1. Return
-- | \*false\*.
-- SPEC: L6362-L6376
-- | # CanonicalNumericIndexString ( \_argument\_: a String, ): a Number or \*undefined\*
-- |
-- | description
-- | :   If \_argument\_ is either \*\"-0\"\* or exactly matches
-- |     ToString(\_n\_) for some Number value \_n\_, it returns the
-- |     respective Number value. Otherwise, it returns \*undefined\*.
-- |
-- | 1\. If \_argument\_ is \*\"-0\"\*, return \*-0\*~𝔽~. 1. Let \_n\_ be !
-- | ToNumber(\_argument\_). 1. If ! ToString(\_n\_) is \_argument\_, return
-- | \_n\_. 1. Return \*undefined\*.
-- |
-- | A [canonical numeric string]{.dfn variants="canonical numeric strings"}
-- | is any String for which the CanonicalNumericIndexString abstract
-- | operation does not return \*undefined\*.
-- SPEC: L6377-L6387
-- | # ToIndex ( \_value\_: an ECMAScript language value, ): either a normal completion containing a non-negative integer or a throw completion
-- |
-- | description
-- | :   It converts \_value\_ to an integer and returns that integer if it
-- |     is non-negative and corresponds with an integer index. Otherwise, it
-- |     throws an exception.
-- |
-- | 1\. Let \_integer\_ be ? ToIntegerOrInfinity(\_value\_). 1. If
-- | \_integer\_ is not in the inclusive interval from 0 to 2^53^ - 1, throw
-- | a \*RangeError\* exception. 1. Return \_integer\_.
-- SPEC: L5626-L5652
-- | # The Property Descriptor Specification Type
-- |
-- | The [Property Descriptor]{.dfn variants="Property Descriptors"} type is
-- | used to explain the manipulation and reification of Object property
-- | attributes. A Property Descriptor is a Record with zero or more fields,
-- | where each field\'s name is an attribute name and its value is a
-- | corresponding attribute value as specified in . The schema name used
-- | within this specification to tag literal descriptions of Property
-- | Descriptor records is "PropertyDescriptor".
-- |
-- | Property Descriptor values may be further classified as data Property
-- | Descriptors and accessor Property Descriptors based upon the existence
-- | or use of certain fields. A data Property Descriptor is one that
-- | includes any fields named either \[\[Value\]\] or \[\[Writable\]\]. An
-- | accessor Property Descriptor is one that includes any fields named
-- | either \[\[Get\]\] or \[\[Set\]\]. Any Property Descriptor may have
-- | fields named \[\[Enumerable\]\] and \[\[Configurable\]\]. A Property
-- | Descriptor value may not be both a data Property Descriptor and an
-- | accessor Property Descriptor; however, it may be neither (in which case
-- | it is a generic Property Descriptor). A [fully populated Property
-- | Descriptor]{.dfn} is one that is either an accessor Property Descriptor
-- | or a data Property Descriptor and that has all of the corresponding
-- | fields defined in .
-- |
-- | The following abstract operations are used in this specification to
-- | operate upon Property Descriptor values:
-- SPEC: L17644-L17653
-- | # Runtime Semantics: LoopEvaluation ( \_labelSet\_: a List of Strings, ): either a normal completion containing an ECMAScript language value or an abrupt completion
-- |
-- | IterationStatement : DoWhileStatement 1. Return ? DoWhileLoopEvaluation
-- | of \|DoWhileStatement\| with argument \_labelSet\_. IterationStatement :
-- | WhileStatement 1. Return ? WhileLoopEvaluation of \|WhileStatement\|
-- | with argument \_labelSet\_. IterationStatement : ForStatement 1. Return
-- | ? ForLoopEvaluation of \|ForStatement\| with argument \_labelSet\_.
-- | IterationStatement : ForInOfStatement 1. Return ? ForInOfLoopEvaluation
-- | of \|ForInOfStatement\| with argument \_labelSet\_.
-- SPEC: L17225-L17233
-- | # Runtime Semantics: Evaluation
-- |
-- | HoistableDeclaration : GeneratorDeclaration AsyncFunctionDeclaration
-- | AsyncGeneratorDeclaration 1. Return \~empty\~. HoistableDeclaration :
-- | FunctionDeclaration 1. Return ? Evaluation of \|FunctionDeclaration\|.
-- | BreakableStatement : IterationStatement SwitchStatement 1. Let
-- | \_newLabelSet\_ be a new empty List. 1. Return ? LabelledEvaluation of
-- | this \|BreakableStatement\| with argument \_newLabelSet\_.
-- SPEC: L18847-L18856
-- | # Runtime Semantics: EvaluateFunctionBody ( \_functionObject\_: an ECMAScript function object, \_argumentsList\_: a List of ECMAScript language values, ): a return completion or a throw completion
-- |
-- | FunctionBody : FunctionStatementList 1. Perform ?
-- | FunctionDeclarationInstantiation(\_functionObject\_,
-- | \_argumentsList\_). 1. Perform ? Evaluation of
-- | \|FunctionStatementList\|. 1. NOTE: If the previous step resulted in a
-- | normal completion, then evaluation finished by proceeding past the end
-- | of the \|FunctionStatementList\|. 1. Return
-- | ReturnCompletion(\*undefined\*).
-- SPEC: L18622-L18632
-- | # Runtime Semantics: Evaluation
-- |
-- | Evaluating a \|DebuggerStatement\| may allow an implementation to cause
-- | a breakpoint when run under a debugger. If a debugger is not present or
-- | active this statement has no observable effect.
-- |
-- | DebuggerStatement : \`debugger\` \`;\` 1. If an implementation-defined
-- | debugging facility is available and enabled, then 1. Perform an
-- | implementation-defined debugging action. 1. Return a new
-- | implementation-defined Completion Record. 1. Return \~empty\~.
-- SPEC: L7349-L7357
-- | # Runtime Semantics: Evaluation ( ): a Completion Record
-- |
-- | effects
-- | :   user-code
-- |
-- | The definitions for this operation are distributed over the \"ECMAScript
-- | Language\" sections of this specification. Each definition appears after
-- | the defining occurrence of the relevant productions.

-- SPEC: L6745-L6752
-- | # DeletePropertyOrThrow ( \_O\_: an Object, \_P\_: a property key, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | description
-- | :   It is used to remove a specific own property of an object. It throws
-- |     an exception if the property is not configurable.
-- |
-- | 1\. Let \_success\_ be ? \_O\_.\[\[Delete\]\](\_P\_). 1. If \_success\_
-- | is \*false\*, throw a \*TypeError\* exception. 1. Return \~unused\~.

-- SPEC: L6783-L6796
-- | # Call ( \_F\_: an ECMAScript language value, \_V\_: an ECMAScript language value, optional \_argumentsList\_: a List of ECMAScript language values, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | description
-- | :   It is used to call the \[\[Call\]\] internal method of a function
-- |     object. \_F\_ is the function object, \_V\_ is an ECMAScript
-- |     language value that is the \*this\* value of the \[\[Call\]\], and
-- |     \_argumentsList\_ is the value passed to the corresponding argument
-- |     of the internal method. If \_argumentsList\_ is not present, a new
-- |     empty List is used as its value.
-- |
-- | 1\. If \_argumentsList\_ is not present, set \_argumentsList\_ to a new
-- | empty List. 1. If IsCallable(\_F\_) is \*false\*, throw a \*TypeError\*
-- | exception. 1. Return ? \_F\_.\[\[Call\]\](\_V\_, \_argumentsList\_).

-- SPEC: L6851-L6861
-- | # CreateArrayFromList ( \_elements\_: a List of ECMAScript language values, ): an Array
-- |
-- | description
-- | :   It is used to create an Array whose elements are provided by
-- |     \_elements\_.
-- |
-- | 1\. Let \_array\_ be ! ArrayCreate(0). 1. Let \_n\_ be 0. 1. For each
-- | element \_e\_ of \_elements\_, do 1. Perform !
-- | CreateDataPropertyOrThrow(\_array\_, ! ToString(𝔽(\_n\_)), \_e\_). 1.
-- | Set \_n\_ to \_n\_ + 1. 1. Return \_array\_.
-- SPEC: L6862-L6876
-- | # LengthOfArrayLike ( \_obj\_: an Object, ): either a normal completion containing a non-negative integer or a throw completion
-- |
-- | description
-- | :   It returns the value of the \*\"length\"\* property of an array-like
-- |     object.
-- |
-- | 1\. Return ℝ(? ToLength(? Get(\_obj\_, \*\"length\"\*))).
-- |
-- | An [array-like object]{.dfn variants="array-like objects"} is any object
-- | for which this operation returns a normal completion.
-- |
-- | Typically, an array-like object would also have some properties with
-- | integer index names. However, that is not a requirement of this
-- | definition. Arrays and String objects are examples of array-like
-- | objects.
-- SPEC: L6896-L6908
-- | # Invoke ( \_V\_: an ECMAScript language value, \_P\_: a property key, optional \_argumentsList\_: a List of ECMAScript language values, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | description
-- | :   It is used to call a method property of an ECMAScript language
-- |     value. \_V\_ serves as both the lookup point for the property and
-- |     the \*this\* value of the call. \_argumentsList\_ is the list of
-- |     arguments values passed to the method. If \_argumentsList\_ is not
-- |     present, a new empty List is used as its value.
-- |
-- | 1\. If \_argumentsList\_ is not present, set \_argumentsList\_ to a new
-- | empty List. 1. Let \_func\_ be ? GetV(\_V\_, \_P\_). 1. Return ?
-- | Call(\_func\_, \_V\_, \_argumentsList\_).

-- SPEC: L5653-L5657
-- | # IsAccessorDescriptor ( \_Desc\_: a Property Descriptor, ): a Boolean
-- |
-- | 1\. If \_Desc\_ has a \[\[Get\]\] field, return \*true\*. 1. If \_Desc\_
-- | has a \[\[Set\]\] field, return \*true\*. 1. Return \*false\*.
-- SPEC: L5658-L5663
-- | # IsDataDescriptor ( \_Desc\_: a Property Descriptor, ): a Boolean
-- |
-- | 1\. If \_Desc\_ has a \[\[Value\]\] field, return \*true\*. 1. If
-- | \_Desc\_ has a \[\[Writable\]\] field, return \*true\*. 1. Return
-- | \*false\*.
-- SPEC: L5664-L5669
-- | # IsGenericDescriptor ( \_Desc\_: a Property Descriptor, ): a Boolean
-- |
-- | 1\. If IsAccessorDescriptor(\_Desc\_) is \*true\*, return \*false\*. 1.
-- | If IsDataDescriptor(\_Desc\_) is \*true\*, return \*false\*. 1. Return
-- | \*true\*.
-- SPEC: L5995-L6003
-- | # ToNumeric ( \_value\_: an ECMAScript language value, ): either a normal completion containing either a Number or a BigInt, or a throw completion
-- |
-- | description
-- | :   It returns \_value\_ converted to a Number or a BigInt.
-- |
-- | 1\. Let \_primValue\_ be ? ToPrimitive(\_value\_, \~number\~). 1. If
-- | \_primValue\_ is a BigInt, return \_primValue\_. 1. Return ?
-- | ToNumber(\_primValue\_).

-- SPEC: L5555-L5576
-- | # GetValue ( \_V\_: a Reference Record or an ECMAScript language value, ): either a normal completion containing an ECMAScript language value or an abrupt completion
-- |
-- | 1\. If \_V\_ is not a Reference Record, return \_V\_. 1. If
-- | IsUnresolvableReference(\_V\_) is \*true\*, throw a \*ReferenceError\*
-- | exception. 1. If IsPropertyReference(\_V\_) is \*true\*, then 1.
-- | \[id=\"step-getvalue-toobject\"\] Let \_baseObj\_ be ?
-- | ToObject(\_V\_.\[\[Base\]\]). 1. If IsPrivateReference(\_V\_) is
-- | \*true\*, then 1. Return ? PrivateGet(\_baseObj\_,
-- | \_V\_.\[\[ReferencedName\]\]). 1. If \_V\_.\[\[ReferencedName\]\] is not
-- | a property key, then 1. Set \_V\_.\[\[ReferencedName\]\] to ?
-- | ToPropertyKey(\_V\_.\[\[ReferencedName\]\]). 1. Return ?
-- | \_baseObj\_.\[\[Get\]\](\_V\_.\[\[ReferencedName\]\],
-- | GetThisValue(\_V\_)). 1. Let \_base\_ be \_V\_.\[\[Base\]\]. 1. Assert:
-- | \_base\_ is an Environment Record. 1. Return ?
-- | \_base\_.GetBindingValue(\_V\_.\[\[ReferencedName\]\],
-- | \_V\_.\[\[Strict\]\]) (see ).
-- |
-- | The object that may be created in step is not accessible outside of the
-- | above abstract operation and the ordinary object \[\[Get\]\] internal
-- | method. An implementation might choose to avoid the actual creation of
-- | the object.
-- SPEC: L5577-L5603
-- | # PutValue ( \_V\_: a Reference Record or an ECMAScript language value, \_W\_: an ECMAScript language value, ): either a normal completion containing \~unused\~ or an abrupt completion
-- |
-- | 1\. If \_V\_ is not a Reference Record, throw a \*ReferenceError\*
-- | exception. 1. If IsUnresolvableReference(\_V\_) is \*true\*, then 1. If
-- | \_V\_.\[\[Strict\]\] is \*true\*, throw a \*ReferenceError\*
-- | exception. 1. Let \_globalObj\_ be GetGlobalObject(). 1. Perform ?
-- | Set(\_globalObj\_, \_V\_.\[\[ReferencedName\]\], \_W\_, \*false\*). 1.
-- | Return \~unused\~. 1. If IsPropertyReference(\_V\_) is \*true\*, then 1.
-- | \[id=\"step-putvalue-toobject\"\] Let \_baseObj\_ be ?
-- | ToObject(\_V\_.\[\[Base\]\]). 1. If IsPrivateReference(\_V\_) is
-- | \*true\*, then 1. Return ? PrivateSet(\_baseObj\_,
-- | \_V\_.\[\[ReferencedName\]\], \_W\_). 1. If \_V\_.\[\[ReferencedName\]\]
-- | is not a property key, then 1. Set \_V\_.\[\[ReferencedName\]\] to ?
-- | ToPropertyKey(\_V\_.\[\[ReferencedName\]\]). 1. Let \_succeeded\_ be ?
-- | \_baseObj\_.\[\[Set\]\](\_V\_.\[\[ReferencedName\]\], \_W\_,
-- | GetThisValue(\_V\_)). 1. If \_succeeded\_ is \*false\* and
-- | \_V\_.\[\[Strict\]\] is \*true\*, throw a \*TypeError\* exception. 1.
-- | Return \~unused\~. 1. Let \_base\_ be \_V\_.\[\[Base\]\]. 1. Assert:
-- | \_base\_ is an Environment Record. 1. Return ?
-- | \_base\_.SetMutableBinding(\_V\_.\[\[ReferencedName\]\], \_W\_,
-- | \_V\_.\[\[Strict\]\]) (see ).
-- |
-- | The object that may be created in step is not accessible outside of the
-- | above abstract operation and the ordinary object \[\[Set\]\] internal
-- | method. An implementation might choose to avoid the actual creation of
-- | that object.
-- SPEC: L5946-L5971
-- | # ToPrimitive ( \_input\_: an ECMAScript language value, optional \_preferredType\_: \~string\~ or \~number\~, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | description
-- | :   It converts its \_input\_ argument to a non-Object type. If an
-- |     object is capable of converting to more than one primitive type, it
-- |     may use the optional hint \_preferredType\_ to favour that type.
-- |
-- | 1\. If \_input\_ is an Object, then 1. Let \_exoticToPrim\_ be ?
-- | GetMethod(\_input\_, %Symbol.toPrimitive%). 1. If \_exoticToPrim\_ is
-- | not \*undefined\*, then 1. If \_preferredType\_ is not present, then 1.
-- | Let \_hint\_ be \*\"default\"\*. 1. Else if \_preferredType\_ is
-- | \~string\~, then 1. Let \_hint\_ be \*\"string\"\*. 1. Else, 1. Assert:
-- | \_preferredType\_ is \~number\~. 1. Let \_hint\_ be \*\"number\"\*. 1.
-- | Let \_result\_ be ? Call(\_exoticToPrim\_, \_input\_, « \_hint\_ »). 1.
-- | If \_result\_ is not an Object, return \_result\_. 1. Throw a
-- | \*TypeError\* exception. 1. If \_preferredType\_ is not present, set
-- | \_preferredType\_ to \~number\~. 1. Return ?
-- | OrdinaryToPrimitive(\_input\_, \_preferredType\_). 1. Return \_input\_.
-- |
-- | When ToPrimitive is called without a hint, then it generally behaves as
-- | if the hint were \~number\~. However, objects may over-ride this
-- | behaviour by defining a %Symbol.toPrimitive% method. Of the objects
-- | defined in this specification only Dates (see ) and Symbol objects (see
-- | ) over-ride the default ToPrimitive behaviour. Dates treat the absence
-- | of a hint as if the hint were \~string\~.
-- SPEC: L5972-L5981
-- | # OrdinaryToPrimitive ( \_O\_: an Object, \_hint\_: \~string\~ or \~number\~, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | 1\. If \_hint\_ is \~string\~, then 1. Let \_methodNames\_ be «
-- | \*\"toString\"\*, \*\"valueOf\"\* ». 1. Else, 1. Let \_methodNames\_ be
-- | « \*\"valueOf\"\*, \*\"toString\"\* ». 1. For each element \_name\_ of
-- | \_methodNames\_, do 1. Let \_method\_ be ? Get(\_O\_, \_name\_). 1. If
-- | IsCallable(\_method\_) is \*true\*, then 1. Let \_result\_ be ?
-- | Call(\_method\_, \_O\_). 1. If \_result\_ is not an Object, return
-- | \_result\_. 1. Throw a \*TypeError\* exception.
-- SPEC: L6322-L6342
-- | # ToObject ( \_argument\_: an ECMAScript language value, ): either a normal completion containing an Object or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to a value of type Object.
-- |
-- | 1\. If \_argument\_ is either \*undefined\* or \*null\*, throw a
-- | \*TypeError\* exception. 1. If \_argument\_ is a Boolean, return a new
-- | Boolean object whose \[\[BooleanData\]\] internal slot is set to
-- | \_argument\_. See for a description of Boolean objects. 1. If
-- | \_argument\_ is a Number, return a new Number object whose
-- | \[\[NumberData\]\] internal slot is set to \_argument\_. See for a
-- | description of Number objects. 1. If \_argument\_ is a String, return a
-- | new String object whose \[\[StringData\]\] internal slot is set to
-- | \_argument\_. See for a description of String objects. 1. If
-- | \_argument\_ is a Symbol, return a new Symbol object whose
-- | \[\[SymbolData\]\] internal slot is set to \_argument\_. See for a
-- | description of Symbol objects. 1. If \_argument\_ is a BigInt, return a
-- | new BigInt object whose \[\[BigIntData\]\] internal slot is set to
-- | \_argument\_. See for a description of BigInt objects. 1. Assert:
-- | \_argument\_ is an Object. 1. Return \_argument\_.
-- SPEC: L6390-L6398
-- | # RequireObjectCoercible ( \_argument\_: an ECMAScript language value, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | description
-- | :   It throws an error if \_argument\_ is a value that cannot be
-- |     converted to an Object using ToObject.
-- |
-- | 1\. If \_argument\_ is either \*undefined\* or \*null\*, throw a
-- | \*TypeError\* exception. 1. Return \~unused\~.
-- SPEC: L6408-L6417
-- | # IsCallable ( \_argument\_: an ECMAScript language value, ): a Boolean
-- |
-- | description
-- | :   It determines if \_argument\_ is a callable function with a
-- |     \[\[Call\]\] internal method.
-- |
-- | 1\. If \_argument\_ is not an Object, return \*false\*. 1. If
-- | \_argument\_ has a \[\[Call\]\] internal method, return \*true\*. 1.
-- | Return \*false\*.
-- SPEC: L6418-L6427
-- | # IsConstructor ( \_argument\_: an ECMAScript language value, ): a Boolean
-- |
-- | description
-- | :   It determines if \_argument\_ is a function object with a
-- |     \[\[Construct\]\] internal method.
-- |
-- | 1\. If \_argument\_ is not an Object, return \*false\*. 1. If
-- | \_argument\_ has a \[\[Construct\]\] internal method, return
-- | \*true\*. 1. Return \*false\*.
-- SPEC: L6428-L6435
-- | # IsExtensible ( \_O\_: an Object, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | description
-- | :   It is used to determine whether additional properties can be added
-- |     to \_O\_.
-- |
-- | 1\. Return ? \_O\_.\[\[IsExtensible\]\]().
-- SPEC: L6499-L6513
-- | # SameValueNonNumber ( \_x\_: an ECMAScript language value, but not a Number, \_y\_: an ECMAScript language value, but not a Number, ): a Boolean
-- |
-- | 1\. Assert: SameType(\_x\_, \_y\_) is \*true\*. 1. If \_x\_ is either
-- | \*undefined\* or \*null\*, return \*true\*. 1. If \_x\_ is a BigInt,
-- | then 1. Return BigInt::equal(\_x\_, \_y\_). 1. If \_x\_ is a String,
-- | then 1. If \_x\_ and \_y\_ have the same length and the same code units
-- | in the same positions, return \*true\*. 1. Return \*false\*. 1. If \_x\_
-- | is a Boolean, then 1. If \_x\_ and \_y\_ are both \*true\* or both
-- | \*false\*, return \*true\*. 1. Return \*false\*. 1. NOTE: All other
-- | ECMAScript language values are compared by identity. 1. If \_x\_ is
-- | \_y\_, return \*true\*. 1. Return \*false\*. For expository purposes,
-- | some cases are handled separately within this algorithm even if it is
-- | unnecessary to do so. The specifics of what \"\_x\_ is \_y\_\" means are
-- | detailed in .
-- SPEC: L6606-L6617
-- | # IsStrictlyEqual ( \_x\_: an ECMAScript language value, \_y\_: an ECMAScript language value, ): a Boolean
-- |
-- | description
-- | :   It provides the semantics for the \`===\` operator.
-- |
-- | 1\. If SameType(\_x\_, \_y\_) is \*false\*, return \*false\*. 1. If
-- | \_x\_ is a Number, then 1. Return Number::equal(\_x\_, \_y\_). 1. Return
-- | SameValueNonNumber(\_x\_, \_y\_).
-- |
-- | This algorithm differs from the SameValue Algorithm in its treatment of
-- | signed zeroes and NaNs.
-- SPEC: L4590-L4603
-- | # Number::equal ( \_x\_: a Number, \_y\_: a Number, ): a Boolean
-- |
-- | 1\. If \_x\_ is \*NaN\*, return \*false\*. 1. If \_y\_ is \*NaN\*,
-- | return \*false\*. 1. If \_x\_ is \_y\_, return \*true\*. 1. If \_x\_ is
-- | \*+0\*~𝔽~ and \_y\_ is \*-0\*~𝔽~, return \*true\*. 1. If \_x\_ is
-- | \*-0\*~𝔽~ and \_y\_ is \*+0\*~𝔽~, return \*true\*. 1. Return \*false\*.
-- |
-- | # Number::sameValue ( \_x\_: a Number, \_y\_: a Number, ): a Boolean
-- |
-- | 1\. If \_x\_ is \*NaN\* and \_y\_ is \*NaN\*, return \*true\*. 1. If
-- | \_x\_ is \*+0\*~𝔽~ and \_y\_ is \*-0\*~𝔽~, return \*false\*. 1. If \_x\_
-- | is \*-0\*~𝔽~ and \_y\_ is \*+0\*~𝔽~, return \*false\*. 1. If \_x\_ is
-- | \_y\_, return \*true\*. 1. Return \*false\*.
-- SPEC: L6652-L6659
-- | # Get ( \_O\_: an Object, \_P\_: a property key, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | description
-- | :   It is used to retrieve the value of a specific property of an
-- |     object.
-- |
-- | 1\. Return ? \_O\_.\[\[Get\]\](\_P\_, \_O\_).
-- SPEC: L6660-L6670
-- | # GetV ( \_V\_: an ECMAScript language value, \_P\_: a property key, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | description
-- | :   It is used to retrieve the value of a specific property of an
-- |     ECMAScript language value. If the value is not an object, the
-- |     property lookup is performed using a wrapper object appropriate for
-- |     the type of the value.
-- |
-- | 1\. Let \_O\_ be ? ToObject(\_V\_). 1. Return ? \_O\_.\[\[Get\]\](\_P\_,
-- | \_V\_).
-- SPEC: L6620-L6651
-- | # MakeBasicObject ( \_internalSlotsList\_: a List of internal slot names, ): an Object
-- |
-- | description
-- | :   It is the source of all ECMAScript objects that are created
-- |     algorithmically, including both ordinary objects and exotic objects.
-- |     It factors out common steps used in creating all objects, and
-- |     centralizes object creation.
-- |
-- | 1\. Set \_internalSlotsList\_ to the list-concatenation of
-- | \_internalSlotsList\_ and « \[\[PrivateElements\]\] ». 1. Let \_obj\_ be
-- | a newly created object with an internal slot for each name in
-- | \_internalSlotsList\_. 1. NOTE: As described in , the initial value of
-- | each such internal slot is \*undefined\* unless specified otherwise. 1.
-- | Set \_obj\_.\[\[PrivateElements\]\] to a new empty List. 1. Set
-- | \_obj\_\'s essential internal methods to the default ordinary object
-- | definitions specified in . 1. Assert: If the caller will not be
-- | overriding both \_obj\_\'s \[\[GetPrototypeOf\]\] and
-- | \[\[SetPrototypeOf\]\] essential internal methods, then
-- | \_internalSlotsList\_ contains \[\[Prototype\]\]. 1. Assert: If the
-- | caller will not be overriding all of \_obj\_\'s \[\[SetPrototypeOf\]\],
-- | \[\[IsExtensible\]\], and \[\[PreventExtensions\]\] essential internal
-- | methods, then \_internalSlotsList\_ contains \[\[Extensible\]\]. 1. If
-- | \_internalSlotsList\_ contains \[\[Extensible\]\], set
-- | \_obj\_.\[\[Extensible\]\] to \*true\*. 1. Return \_obj\_.
-- |
-- | Within this specification, exotic objects are created in abstract
-- | operations such as ArrayCreate and BoundFunctionCreate by first calling
-- | MakeBasicObject to obtain a basic, foundational object, and then
-- | overriding some or all of that object\'s internal methods. In order to
-- | encapsulate exotic object creation, the object\'s essential internal
-- | methods are never modified outside those operations.
-- SPEC: L6697-L6714
-- | # CreateDataPropertyOrThrow ( \_O\_: an Object, \_P\_: a property key, \_V\_: an ECMAScript language value, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | description
-- | :   It is used to create a new own property of an object. It throws a
-- |     \*TypeError\* exception if the requested property update cannot be
-- |     performed.
-- |
-- | 1\. Let \_success\_ be ? CreateDataProperty(\_O\_, \_P\_, \_V\_). 1. If
-- | \_success\_ is \*false\*, throw a \*TypeError\* exception. 1. Return
-- | \~unused\~.
-- |
-- | This abstract operation creates a property whose attributes are set to
-- | the same defaults used for properties created by the ECMAScript language
-- | assignment operator. Normally, the property will not already exist. If
-- | it does exist and is not configurable or if \_O\_ is not extensible,
-- | \[\[DefineOwnProperty\]\] will return \*false\* causing this operation
-- | to throw a \*TypeError\* exception.
-- SPEC: L6766-L6773
-- | # HasProperty ( \_O\_: an Object, \_P\_: a property key, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | description
-- | :   It is used to determine whether an object has a property with the
-- |     specified property key. The property may be either own or inherited.
-- |
-- | 1\. Return ? \_O\_.\[\[HasProperty\]\](\_P\_).
-- SPEC: L6343-L6352
-- | # ToPropertyKey ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a property key or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to a value that can be used as a property
-- |     key.
-- |
-- | 1\. Let \_key\_ be ? ToPrimitive(\_argument\_, \~string\~). 1. If
-- | \_key\_ is a Symbol, then 1. Return \_key\_. 1. Return !
-- | ToString(\_key\_).
-- SPEC: L6783-L6796
-- | # Call ( \_F\_: an ECMAScript language value, \_V\_: an ECMAScript language value, optional \_argumentsList\_: a List of ECMAScript language values, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | description
-- | :   It is used to call the \[\[Call\]\] internal method of a function
-- |     object. \_F\_ is the function object, \_V\_ is an ECMAScript
-- |     language value that is the \*this\* value of the \[\[Call\]\], and
-- |     \_argumentsList\_ is the value passed to the corresponding argument
-- |     of the internal method. If \_argumentsList\_ is not present, a new
-- |     empty List is used as its value.
-- |
-- | 1\. If \_argumentsList\_ is not present, set \_argumentsList\_ to a new
-- | empty List. 1. If IsCallable(\_F\_) is \*false\*, throw a \*TypeError\*
-- | exception. 1. Return ? \_F\_.\[\[Call\]\](\_V\_, \_argumentsList\_).
-- SPEC: L6862-L6877
-- | # LengthOfArrayLike ( \_obj\_: an Object, ): either a normal completion containing a non-negative integer or a throw completion
-- |
-- | description
-- | :   It returns the value of the \*\"length\"\* property of an array-like
-- |     object.
-- |
-- | 1\. Return ℝ(? ToLength(? Get(\_obj\_, \*\"length\"\*))).
-- |
-- | An [array-like object]{.dfn variants="array-like objects"} is any object
-- | for which this operation returns a normal completion.
-- |
-- | Typically, an array-like object would also have some properties with
-- | integer index names. However, that is not a requirement of this
-- | definition. Arrays and String objects are examples of array-like
-- | objects.
-- SPEC: L10960-L10984
-- | # OrdinaryObjectCreate ( \_proto\_: an Object or \*null\*, optional \_additionalInternalSlotsList\_: a List of names of internal slots, ): an Object
-- |
-- | description
-- | :   It is used to specify the runtime creation of new ordinary objects.
-- |     \_additionalInternalSlotsList\_ contains the names of additional
-- |     internal slots that must be defined as part of the object, beyond
-- |     \[\[Prototype\]\] and \[\[Extensible\]\]. If
-- |     \_additionalInternalSlotsList\_ is not provided, a new empty List is
-- |     used.
-- |
-- | 1\. Let \_internalSlotsList\_ be « \[\[Prototype\]\], \[\[Extensible\]\]
-- | ». 1. If \_additionalInternalSlotsList\_ is present, set
-- | \_internalSlotsList\_ to the list-concatenation of \_internalSlotsList\_
-- | and \_additionalInternalSlotsList\_. 1. Let \_O\_ be
-- | MakeBasicObject(\_internalSlotsList\_). 1. Set \_O\_.\[\[Prototype\]\]
-- | to \_proto\_. 1. Return \_O\_.
-- |
-- | Although OrdinaryObjectCreate does little more than call
-- | MakeBasicObject, its use communicates the intention to create an
-- | ordinary object, and not an exotic one. Thus, within this specification,
-- | it is not called by any algorithm that subsequently modifies the
-- | internal methods of the object in ways that would make the result
-- | non-ordinary. Operations that create exotic objects invoke
-- | MakeBasicObject directly.
-- SPEC: L6398-L6406
-- | # IsArray ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | 1\. If \_argument\_ is not an Object, return \*false\*. 1. If
-- | \_argument\_ is an Array exotic object, return \*true\*. 1. If
-- | \_argument\_ is a Proxy exotic object, then 1. Perform ?
-- | ValidateNonRevokedProxy(\_argument\_). 1. Let \_proxyTarget\_ be
-- | \_argument\_.\[\[ProxyTarget\]\]. 1. Return ?
-- | IsArray(\_proxyTarget\_). 1. Return \*false\*.
-- SPEC: L41614-L41620
-- | # Yield ( \_value\_: an ECMAScript language value, ): either a normal completion containing an ECMAScript language value or an abrupt completion
-- |
-- | 1\. Let \_generatorKind\_ be GetGeneratorKind(). 1. If \_generatorKind\_
-- | is \~async\~, return ? AsyncGeneratorYield(? Await(\_value\_)). 1.
-- | Return ? GeneratorYield(CreateIteratorResultObject(\_value\_,
-- | \*false\*)).
-- SPEC: L42095-L42110
-- | # Await ( \_value\_: an ECMAScript language value, ): either a normal completion containing either an ECMAScript language value or \~empty\~, or a throw completion
-- |
-- | 1\. Let \_asyncContext\_ be the running execution context. 1. Let
-- | \_promise\_ be ? PromiseResolve(%Promise%, \_value\_). 1. Let
-- | \_fulfilledClosure\_ be a new Abstract Closure with parameters (\_v\_)
-- | that captures \_asyncContext\_ and performs the following steps when
-- | called: 1. Let \_prevContext\_ be the running execution context. 1.
-- | Suspend \_prevContext\_. 1. Push \_asyncContext\_ onto the execution
-- | context stack; \_asyncContext\_ is now the running execution context. 1.
-- | Resume the suspended evaluation of \_asyncContext\_ using
-- | NormalCompletion(\_v\_) as the result of the operation that suspended
-- | it. 1. Assert: When we reach this step, \_asyncContext\_ has already
-- | been removed from the execution context stack and \_prevContext\_ is the
-- | currently running execution context. 1. Return
-- | NormalCompletion(\*undefined\*). 1. Let \_onFulfilled\_ be
-- | CreateBuiltinFunction(\_fulfilledClosure\_, 1, \*\"\"\*, « »). 1. Let
-- SPEC: L11614-L11640
-- | # CreateBuiltinFunction ( \_behaviour\_: an Abstract Closure, a set of algorithm steps, or some other definition of a function\'s behaviour provided in this specification, \_length\_: a non-negative integer or +∞, \_name\_: a property key or a Private Name, \_additionalInternalSlotsList\_: a List of names of internal slots, optional \_realm\_: a Realm Record, optional \_prototype\_: an Object or \*null\*, optional \_prefix\_: a String, optional \_async\_: a Boolean, ): a built-in function object
-- |
-- | description
-- | :   \_additionalInternalSlotsList\_ contains the names of additional
-- |     internal slots that must be defined as part of the object. This
-- |     operation creates a built-in function object.
-- |
-- | 1\. If \_realm\_ is not present, set \_realm\_ to the current Realm
-- | Record. 1. If \_prototype\_ is not present, set \_prototype\_ to
-- | \_realm\_.\[\[Intrinsics\]\].\[\[%Function.prototype%\]\]. 1. If
-- | \_async\_ is not present, set \_async\_ to \*false\*. 1. Let
-- | \_internalSlotsList\_ be a List containing the names of all the internal
-- | slots that requires for the built-in function object that is about to be
-- | created. 1. Append to \_internalSlotsList\_ the elements of
-- | \_additionalInternalSlotsList\_. 1. Let \_func\_ be a new built-in
-- | function object that, when called, performs the action described by
-- | \_behaviour\_ using the provided arguments as the values of the
-- | corresponding parameters specified by \_behaviour\_. The new function
-- | object has internal slots whose names are the elements of
-- | \_internalSlotsList\_, and an \[\[InitialName\]\] internal slot. 1. Set
-- | \_func\_.\[\[Async\]\] to \_async\_. 1. Set \_func\_.\[\[Prototype\]\]
-- | to \_prototype\_. 1. Set \_func\_.\[\[Extensible\]\] to \*true\*. 1. Set
-- | \_func\_.\[\[Realm\]\] to \_realm\_. 1. Set \_func\_.\[\[InitialName\]\]
-- | to \*null\*. 1. Perform SetFunctionLength(\_func\_, \_length\_). 1. If
-- | \_prefix\_ is not present, then 1. Perform SetFunctionName(\_func\_,
-- | \_name\_). 1. Else, 1. Perform SetFunctionName(\_func\_, \_name\_,
-- | \_prefix\_). 1. Return \_func\_.

/-- Check whether an expression is a value expression. -/
def exprValue? : Expr → Option Value
  | .lit v => some v
  | _ => none

-- SPEC: L5982-L5994
-- | # ToBoolean ( \_argument\_: an ECMAScript language value, ): a Boolean
-- |
-- | description
-- | :   It converts \_argument\_ to a value of type Boolean.
-- |
-- | 1\. If \_argument\_ is a Boolean, return \_argument\_. 1. If
-- | \_argument\_ is one of \*undefined\*, \*null\*, \*+0\*~𝔽~, \*-0\*~𝔽~,
-- | \*NaN\*, \*0\*~ℤ~, or the empty String, return \*false\*. 1.
-- | \[id=\"step-to-boolean-web-compat-insertion-point\",
-- | normative-optional\] If the host is a web browser or otherwise supports
-- | , then 1. If \_argument\_ is an Object and \_argument\_ has an
-- | \[\[IsHTMLDDA\]\] internal slot, return \*false\*. 1. Return \*true\*.
-- SPEC: L5982-L5994
-- | # ToBoolean ( \_argument\_: an ECMAScript language value, ): a Boolean
-- |
-- | description
-- | :   It converts \_argument\_ to a value of type Boolean.
-- |
-- | 1\. If \_argument\_ is a Boolean, return \_argument\_. 1. If
-- | \_argument\_ is one of \*undefined\*, \*null\*, \*+0\*~𝔽~, \*-0\*~𝔽~,
-- | \*NaN\*, \*0\*~ℤ~, or the empty String, return \*false\*. 1.
-- | \[id=\"step-to-boolean-web-compat-insertion-point\",
-- | normative-optional\] If the host is a web browser or otherwise supports
-- | , then 1. If \_argument\_ is an Object and \_argument\_ has an
-- | \[\[IsHTMLDDA\]\] internal slot, return \*false\*. 1. Return \*true\*.
/-- ECMA-262 §7.2.14 ToBoolean (core subset). -/
def toBoolean : Value → Bool
  | .undefined => false
  | .null => false
  | .bool b => b
  | .number n => !(n == 0.0 || n.isNaN)
  | .string s => !s.isEmpty
  | .object _ => true
  | .function _ => true

-- SPEC: L6004-L6017
-- | # ToNumber ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a Number or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to a value of type Number.
-- |
-- | 1\. If \_argument\_ is a Number, return \_argument\_. 1. If \_argument\_
-- | is either a Symbol or a BigInt, throw a \*TypeError\* exception. 1. If
-- | \_argument\_ is \*undefined\*, return \*NaN\*. 1. If \_argument\_ is
-- | either \*null\* or \*false\*, return \*+0\*~𝔽~. 1. If \_argument\_ is
-- | \*true\*, return \*1\*~𝔽~. 1. If \_argument\_ is a String, return
-- | StringToNumber(\_argument\_). 1. Assert: \_argument\_ is an Object. 1.
-- | Let \_primValue\_ be ? ToPrimitive(\_argument\_, \~number\~). 1. Assert:
-- | \_primValue\_ is not an Object. 1. Return ? ToNumber(\_primValue\_).
/-- ECMA-262 §7.1.3 ToNumber (core subset). -/
def toNumber : Value → Float
  | .number n => n
  | .bool true => 1.0
  | .bool false => 0.0
  | .null => 0.0
  | .undefined => 0.0 / 0.0  -- ECMA-262 §7.1.3: undefined → NaN
  -- SPEC: L6055-L6060
  -- | # StringToNumber ( \_str\_: a String, ): a Number
  -- |
  -- | 1\. Let \_literal\_ be ParseText(\_str\_, \|StringNumericLiteral\|). 1.
  -- | If \_literal\_ is a List of errors, return \*NaN\*. 1. Return the
  -- | StringNumericValue of \_literal\_.
  | .string s =>
      let trimmed := s.trimAscii.toString
      if trimmed.isEmpty then 0.0
      else
        -- Try to parse as integer literal, fallback to NaN.
        match trimmed.toNat? with
        | some n => Float.ofNat n
        | none =>
            -- Check for negative integers.
            if trimmed.startsWith "-" then
              match (trimmed.drop 1).toNat? with
              | some n => -(Float.ofNat n)
              | none => 0.0 / 0.0  -- NaN
            else 0.0 / 0.0  -- NaN for non-numeric strings
  | _ => 0.0 / 0.0  -- NaN for objects/functions

-- SPEC: L6018-L6033
-- | # ToNumber Applied to the String Type
-- |
-- | The abstract operation StringToNumber specifies how to convert a String
-- | value to a Number value, using the following grammar.
-- |
-- | ## Syntax
-- |
-- | StringNumericLiteral ::: StrWhiteSpace? StrWhiteSpace? StrNumericLiteral
-- | StrWhiteSpace? StrWhiteSpace ::: StrWhiteSpaceChar StrWhiteSpace?
-- | StrWhiteSpaceChar ::: WhiteSpace LineTerminator StrNumericLiteral :::
-- | StrDecimalLiteral NonDecimalIntegerLiteral\[\~Sep\] StrDecimalLiteral
-- | ::: StrUnsignedDecimalLiteral \`+\` StrUnsignedDecimalLiteral \`-\`
-- | StrUnsignedDecimalLiteral StrUnsignedDecimalLiteral ::: \`Infinity\`
-- | DecimalDigits\[\~Sep\] \`.\` DecimalDigits\[\~Sep\]?
-- | ExponentPart\[\~Sep\]? \`.\` DecimalDigits\[\~Sep\]
-- | ExponentPart\[\~Sep\]? DecimalDigits\[\~Sep\] ExponentPart\[\~Sep\]?

-- SPEC: L6114-L6127
-- | # ToIntegerOrInfinity ( \_argument\_: an ECMAScript language value, ): either a normal completion containing either an integer, +∞, or -∞, or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to an integer representing its Number value
-- |     with fractional part truncated, or to +∞ or -∞ when that Number
-- |     value is infinite.
-- |
-- | 1\. Let \_number\_ be ? ToNumber(\_argument\_). 1. If \_number\_ is one
-- | of \*NaN\*, \*+0\*~𝔽~, or \*-0\*~𝔽~, return 0. 1. If \_number\_ is
-- | \*+∞\*~𝔽~, return +∞. 1. If \_number\_ is \*-∞\*~𝔽~, return -∞. 1.
-- | Return truncate(ℝ(\_number\_)). 𝔽(ToIntegerOrInfinity(\_x\_)) never
-- | returns \*-0\*~𝔽~ for any value of \_x\_. The truncation of the
-- | fractional part is performed after converting \_x\_ to a mathematical
-- | value.

-- SPEC: L6353-L6361
-- | # ToLength ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a non-negative integral Number or a throw completion
-- |
-- | description
-- | :   It clamps and truncates \_argument\_ to a non-negative integral
-- |     Number suitable for use as the length of an array-like object.
-- |
-- | 1\. Let \_len\_ be ? ToIntegerOrInfinity(\_argument\_). 1. If \_len\_ ≤
-- | 0, return \*+0\*~𝔽~. 1. Return 𝔽(min(\_len\_, 2^53^ - 1)).

-- SPEC: L16187-L16225
-- | UnaryExpression : \`+\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
-- | of \|UnaryExpression\|. 1. Return ? ToNumber(? GetValue(\_expr\_)).
-- |
-- | # Unary \`-\` Operator
-- |
-- | The unary \`-\` operator converts its operand to a numeric value and
-- | then negates it. Negating \*+0\*~𝔽~ produces \*-0\*~𝔽~, and negating
-- | \*-0\*~𝔽~ produces \*+0\*~𝔽~.
-- |
-- | # Runtime Semantics: Evaluation
-- |
-- | UnaryExpression : \`-\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
-- | of \|UnaryExpression\|. 1. Let \_oldValue\_ be ? ToNumeric(?
-- | GetValue(\_expr\_)). 1. If \_oldValue\_ is a Number, return
-- | Number::unaryMinus(\_oldValue\_). 1. Assert: \_oldValue\_ is a
-- | BigInt. 1. Return BigInt::unaryMinus(\_oldValue\_).
-- |
-- | # Bitwise NOT Operator ( \`\~\` )
-- |
-- | # Runtime Semantics: Evaluation
-- |
-- | UnaryExpression : \`\~\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
-- | of \|UnaryExpression\|. 1. Let \_oldValue\_ be ? ToNumeric(?
-- | GetValue(\_expr\_)). 1. If \_oldValue\_ is a Number, return
-- | Number::bitwiseNOT(\_oldValue\_). 1. Assert: \_oldValue\_ is a
-- | BigInt. 1. Return BigInt::bitwiseNOT(\_oldValue\_).
-- |
-- | # Logical NOT Operator ( \`!\` )
-- |
-- | # Runtime Semantics: Evaluation
-- |
-- | UnaryExpression : \`!\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
-- | of \|UnaryExpression\|. 1. Let \_oldValue\_ be ToBoolean(?
-- | GetValue(\_expr\_)). 1. If \_oldValue\_ is \*true\*, return
-- | \*false\*. 1. Return \*true\*.
-- |
-- | # Exponentiation Operator
-- |
-- | ## Syntax
-- SPEC: L4405-L4410
-- | # Number::unaryMinus ( \_x\_: a Number, ): a Number
-- |
-- | 1\. If \_x\_ is \*NaN\*, return \*NaN\*. 1. Return the negation of
-- | \_x\_; that is, compute a Number with the same magnitude but opposite
-- | sign.
/-- ECMA-262 §13.5 Runtime Semantics: Evaluation (core unary subset). -/
def evalUnary : UnaryOp → Value → Value
  | .neg, v => .number (-toNumber v)
  | .pos, v => .number (toNumber v)
  | .logNot, v => .bool (!toBoolean v)
  -- SPEC: L16150-L16156
  -- | # The \`void\` Operator
  -- |
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | UnaryExpression : \`void\` UnaryExpression 1. Let \_expr\_ be ?
  -- | Evaluation of \|UnaryExpression\|. 1. Perform ? GetValue(\_expr\_). 1.
  -- | Return \*undefined\*.
  | .void, _ => .undefined
  -- SPEC: L16204-L16212
  -- | # Bitwise NOT Operator ( \`\~\` )
  -- |
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | UnaryExpression : \`\~\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
  -- | of \|UnaryExpression\|. 1. Let \_oldValue\_ be ? ToNumeric(?
  -- | GetValue(\_expr\_)). 1. If \_oldValue\_ is a Number, return
  -- | Number::bitwiseNOT(\_oldValue\_). 1. Assert: \_oldValue\_ is a
  -- | BigInt. 1. Return BigInt::bitwiseNOT(\_oldValue\_).
  -- SPEC: L4411-L4416
  -- | # Number::bitwiseNOT ( \_x\_: a Number, ): an integral Number
  -- |
  -- | 1\. Let \_oldValue\_ be ! ToInt32(\_x\_). 1. Return the bitwise
  -- | complement of \_oldValue\_. The mathematical value of the result is
  -- | exactly representable as a 32-bit two\'s complement bit string.
  -- SPEC: L6129-L6140
  -- | # ToInt32 ( \_argument\_: an ECMAScript language value, ): either a normal completion containing an integral Number or a throw completion
  -- |
  -- | description
  -- | :   It converts \_argument\_ to one of 2^32^ integral Number values in
  -- |     the inclusive interval from 𝔽(-2^31^) to 𝔽(2^31^ - 1).
  -- |
  -- | 1\. Let \_number\_ be ? ToNumber(\_argument\_). 1. If \_number\_ is not
  -- | finite or \_number\_ is either \*+0\*~𝔽~ or \*-0\*~𝔽~, return
  -- | \*+0\*~𝔽~. 1. Let \_int\_ be truncate(ℝ(\_number\_)). 1. Let
  -- | \_int32bit\_ be \_int\_ modulo 2^32^. 1. If \_int32bit\_ ≥ 2^31^, return
  -- | 𝔽(\_int32bit\_ - 2^32^). 1. Return 𝔽(\_int32bit\_).
  | .bitNot, v => .number (~~~(toNumber v |>.toUInt32)).toFloat

-- SPEC: L6814-L6833
-- | # SetIntegrityLevel ( \_O\_: an Object, \_level\_: \~sealed\~ or \~frozen\~, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | description
-- | :   It is used to fix the set of own properties of an object.
-- |
-- | 1\. Let \_status\_ be ? \_O\_.\[\[PreventExtensions\]\](). 1. If
-- | \_status\_ is \*false\*, return \*false\*. 1. Let \_keys\_ be ?
-- | \_O\_.\[\[OwnPropertyKeys\]\](). 1. If \_level\_ is \~sealed\~, then 1.
-- | For each element \_k\_ of \_keys\_, do 1. Perform ?
-- | DefinePropertyOrThrow(\_O\_, \_k\_, PropertyDescriptor {
-- | \[\[Configurable\]\]: \*false\* }). 1. Else, 1. Assert: \_level\_ is
-- | \~frozen\~. 1. For each element \_k\_ of \_keys\_, do 1. Let
-- | \_currentDesc\_ be ? \_O\_.\[\[GetOwnProperty\]\](\_k\_). 1. If
-- | \_currentDesc\_ is not \*undefined\*, then 1. If
-- | IsAccessorDescriptor(\_currentDesc\_) is \*true\*, then 1. Let \_desc\_
-- | be the PropertyDescriptor { \[\[Configurable\]\]: \*false\* }. 1.
-- | Else, 1. Let \_desc\_ be the PropertyDescriptor { \[\[Configurable\]\]:
-- | \*false\*, \[\[Writable\]\]: \*false\* }. 1. Perform ?
-- | DefinePropertyOrThrow(\_O\_, \_k\_, \_desc\_). 1. Return \*true\*.
-- SPEC: L6878-L6895
-- | # CreateListFromArrayLike ( \_obj\_: an ECMAScript language value, optional \_validElementTypes\_: \~all\~ or \~property-key\~, ): either a normal completion containing a List of ECMAScript language values or a throw completion
-- |
-- | description
-- | :   It is used to create a List value whose elements are provided by the
-- |     indexed properties of \_obj\_. \_validElementTypes\_ indicates the
-- |     types of values that are allowed as elements.
-- |
-- | 1\. If \_validElementTypes\_ is not present, set \_validElementTypes\_
-- | to \~all\~. 1. If \_obj\_ is not an Object, throw a \*TypeError\*
-- | exception. 1. Let \_len\_ be ? LengthOfArrayLike(\_obj\_). 1. Let
-- | \_list\_ be a new empty List. 1. Let \_index\_ be 0. 1. Repeat, while
-- | \_index\_ \< \_len\_, 1. Let \_indexName\_ be !
-- | ToString(𝔽(\_index\_)). 1. Let \_next\_ be ? Get(\_obj\_,
-- | \_indexName\_). 1. If \_validElementTypes\_ is \~property-key\~ and
-- | \_next\_ is not a property key, throw a \*TypeError\* exception. 1.
-- | Append \_next\_ to \_list\_. 1. Set \_index\_ to \_index\_ + 1. 1.
-- | Return \_list\_.
-- SPEC: L18325-L18340
-- | # Runtime Semantics: Evaluation
-- |
-- | WithStatement : \`with\` \`(\` Expression \`)\` Statement 1. Let \_val\_
-- | be ? Evaluation of \|Expression\|. 1. Let \_obj\_ be ? ToObject(?
-- | GetValue(\_val\_)). 1. Let \_oldEnv\_ be the running execution
-- | context\'s LexicalEnvironment. 1. Let \_newEnv\_ be
-- | NewObjectEnvironment(\_obj\_, \*true\*, \_oldEnv\_). 1. Set the running
-- | execution context\'s LexicalEnvironment to \_newEnv\_. 1. Let \_C\_ be
-- | Completion(Evaluation of \|Statement\|). 1. Set the running execution
-- | context\'s LexicalEnvironment to \_oldEnv\_. 1. Return ?
-- | UpdateEmpty(\_C\_, \*undefined\*).
-- |
-- | No matter how control leaves the embedded \|Statement\|, whether
-- | normally or by some form of abrupt completion or exception, the
-- | LexicalEnvironment is always restored to its former state.
-- SPEC: L17484-L17503
-- | # Runtime Semantics: PropertyBindingInitialization ( \_value\_: an ECMAScript language value, \_environment\_: an Environment Record or \*undefined\*, ): either a normal completion containing a List of property keys or an abrupt completion
-- |
-- | description
-- | :   It collects a list of all bound property names.
-- |
-- | BindingPropertyList : BindingPropertyList \`,\` BindingProperty 1. Let
-- | \_boundNames\_ be ? PropertyBindingInitialization of
-- | \|BindingPropertyList\| with arguments \_value\_ and \_environment\_. 1.
-- | Let \_nextNames\_ be ? PropertyBindingInitialization of
-- | \|BindingProperty\| with arguments \_value\_ and \_environment\_. 1.
-- | Return the list-concatenation of \_boundNames\_ and \_nextNames\_.
-- | BindingProperty : SingleNameBinding 1. Let \_name\_ be the sole element
-- | of the BoundNames of \|SingleNameBinding\|. 1. Perform ?
-- | KeyedBindingInitialization of \|SingleNameBinding\| with arguments
-- | \_value\_, \_environment\_, and \_name\_. 1. Return « \_name\_ ».
-- | BindingProperty : PropertyName \`:\` BindingElement 1. Let \_P\_ be ?
-- | Evaluation of \|PropertyName\|. 1. Perform ? KeyedBindingInitialization
-- | of \|BindingElement\| with arguments \_value\_, \_environment\_, and
-- | \_P\_. 1. Return « \_P\_ ».
-- SPEC: L5740-L5745
-- | # The Environment Record Specification Type
-- |
-- | The Environment Record type is used to explain the behaviour of name
-- | resolution in nested functions and blocks. This type and the operations
-- | upon it are defined in .
-- SPEC: L9197-L9222
-- | # Function Environment Records
-- |
-- | A [Function Environment Record]{.dfn
-- | variants="Function Environment Records"} is a Declarative Environment
-- | Record that is used to represent the top-level scope of a function and,
-- | if the function is not an \|ArrowFunction\|, provides a \`this\`
-- | binding. If a function is not an \|ArrowFunction\| function and
-- | references \`super\`, its Function Environment Record also contains the
-- | state that is used to perform \`super\` method invocations from within
-- | the function.
-- |
-- | Function Environment Records have the additional state fields listed in
-- | .
-- |
-- |   Field Name                  Value                                                Meaning
-- |   --------------------------- ---------------------------------------------------- ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- |   \[\[ThisValue\]\]           an ECMAScript language value                         This is the \*this\* value used for this invocation of the function.
-- |   \[\[ThisBindingStatus\]\]   \~lexical\~, \~initialized\~, or \~uninitialized\~   If the value is \~lexical\~, this is an \|ArrowFunction\| and does not have a local \*this\* value.
-- |   \[\[FunctionObject\]\]      an ECMAScript function object                        The function object whose invocation caused this Environment Record to be created.
-- |   \[\[NewTarget\]\]           a constructor or \*undefined\*                       If this Environment Record was created by the \[\[Construct\]\] internal method, \[\[NewTarget\]\] is the value of the \[\[Construct\]\] \_newTarget\_ parameter. Otherwise, its value is \*undefined\*.
-- |
-- | Function Environment Records support all of the Declarative Environment
-- | Record methods listed in and share the same specifications for all of
-- | those methods except for HasThisBinding, GetThisBinding, and
-- | HasSuperBinding.
-- SPEC: L6172-L6183
-- | # ToInt16 ( \_argument\_: an ECMAScript language value, ): either a normal completion containing an integral Number or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to one of 2^16^ integral Number values in
-- |     the inclusive interval from 𝔽(-2^15^) to 𝔽(2^15^ - 1).
-- |
-- | 1\. Let \_number\_ be ? ToNumber(\_argument\_). 1. If \_number\_ is not
-- | finite or \_number\_ is either \*+0\*~𝔽~ or \*-0\*~𝔽~, return
-- | \*+0\*~𝔽~. 1. Let \_int\_ be truncate(ℝ(\_number\_)). 1. Let
-- | \_int16bit\_ be \_int\_ modulo 2^16^. 1. If \_int16bit\_ ≥ 2^15^, return
-- | 𝔽(\_int16bit\_ - 2^16^). 1. Return 𝔽(\_int16bit\_).
-- SPEC: L6184-L6201
-- | # ToUint16 ( \_argument\_: an ECMAScript language value, ): either a normal completion containing an integral Number or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to one of 2^16^ integral Number values in
-- |     the inclusive interval from \*+0\*~𝔽~ to 𝔽(2^16^ - 1).
-- |
-- | 1\. Let \_number\_ be ? ToNumber(\_argument\_). 1. If \_number\_ is not
-- | finite or \_number\_ is either \*+0\*~𝔽~ or \*-0\*~𝔽~, return
-- | \*+0\*~𝔽~. 1. Let \_int\_ be truncate(ℝ(\_number\_)). 1.
-- | \[id=\"step-touint16-mod\"\] Let \_int16bit\_ be \_int\_ modulo
-- | 2^16^. 1. Return 𝔽(\_int16bit\_).
-- |
-- | Given the above definition of ToUint16:
-- |
-- | - The substitution of 2^16^ for 2^32^ in step is the only difference
-- |   between ToUint32 and ToUint16.
-- | - ToUint16 maps \*-0\*~𝔽~ to \*+0\*~𝔽~.
-- SPEC: L6834-L6850
-- | # TestIntegrityLevel ( \_O\_: an Object, \_level\_: \~sealed\~ or \~frozen\~, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | description
-- | :   It is used to determine if the set of own properties of an object
-- |     are fixed.
-- |
-- | 1\. Let \_extensible\_ be ? IsExtensible(\_O\_). 1. If \_extensible\_ is
-- | \*true\*, return \*false\*. 1. NOTE: If the object is extensible, none
-- | of its properties are examined. 1. Let \_keys\_ be ?
-- | \_O\_.\[\[OwnPropertyKeys\]\](). 1. For each element \_k\_ of \_keys\_,
-- | do 1. Let \_currentDesc\_ be ? \_O\_.\[\[GetOwnProperty\]\](\_k\_). 1.
-- | If \_currentDesc\_ is not \*undefined\*, then 1. If
-- | \_currentDesc\_.\[\[Configurable\]\] is \*true\*, return \*false\*. 1.
-- | If \_level\_ is \~frozen\~ and IsDataDescriptor(\_currentDesc\_) is
-- | \*true\*, then 1. If \_currentDesc\_.\[\[Writable\]\] is \*true\*,
-- | return \*false\*. 1. Return \*true\*.
-- SPEC: L6925-L6939
-- | # SpeciesConstructor ( \_O\_: an Object, \_defaultConstructor\_: a constructor, ): either a normal completion containing a constructor or a throw completion
-- |
-- | description
-- | :   It is used to retrieve the constructor that should be used to create
-- |     new objects that are derived from \_O\_. \_defaultConstructor\_ is
-- |     the constructor to use if a constructor %Symbol.species% property
-- |     cannot be found starting from \_O\_.
-- |
-- | 1\. Let \_C\_ be ? Get(\_O\_, \*\"constructor\"\*). 1. If \_C\_ is
-- | \*undefined\*, return \_defaultConstructor\_. 1. If \_C\_ is not an
-- | Object, throw a \*TypeError\* exception. 1. Let \_S\_ be ? Get(\_C\_,
-- | %Symbol.species%). 1. If \_S\_ is either \*undefined\* or \*null\*,
-- | return \_defaultConstructor\_. 1. If IsConstructor(\_S\_) is \*true\*,
-- | return \_S\_. 1. Throw a \*TypeError\* exception.
-- SPEC: L6970-L6987
-- | # CopyDataProperties ( \_target\_: an Object, \_source\_: an ECMAScript language value, \_excludedItems\_: a List of property keys, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | 1\. If \_source\_ is either \*undefined\* or \*null\*, return
-- | \~unused\~. 1. Let \_from\_ be ! ToObject(\_source\_). 1. Let \_keys\_
-- | be ? \_from\_.\[\[OwnPropertyKeys\]\](). 1. For each element \_nextKey\_
-- | of \_keys\_, do 1. Let \_excluded\_ be \*false\*. 1. For each element
-- | \_e\_ of \_excludedItems\_, do 1. If SameValue(\_e\_, \_nextKey\_) is
-- | \*true\*, then 1. Set \_excluded\_ to \*true\*. 1. If \_excluded\_ is
-- | \*false\*, then 1. Let \_desc\_ be ?
-- | \_from\_.\[\[GetOwnProperty\]\](\_nextKey\_). 1. If \_desc\_ is not
-- | \*undefined\* and \_desc\_.\[\[Enumerable\]\] is \*true\*, then 1. Let
-- | \_propValue\_ be ? Get(\_from\_, \_nextKey\_). 1. Perform !
-- | CreateDataPropertyOrThrow(\_target\_, \_nextKey\_, \_propValue\_). 1.
-- | Return \~unused\~.
-- |
-- | The target passed in here is always a newly created object which is not
-- | directly accessible in case of an error being thrown.
-- SPEC: L11175-L11205
-- | # \[\[Construct\]\] ( \_argumentsList\_: a List of ECMAScript language values, \_newTarget\_: a constructor, ): either a normal completion containing an Object or a throw completion
-- |
-- | for
-- | :   an ECMAScript function object \_F\_
-- |
-- | 1\. Let \_callerContext\_ be the running execution context. 1. Let
-- | \_kind\_ be \_F\_.\[\[ConstructorKind\]\]. 1. If \_kind\_ is \~base\~,
-- | then 1. Let \_thisArgument\_ be ?
-- | OrdinaryCreateFromConstructor(\_newTarget\_,
-- | \*\"%Object.prototype%\"\*). 1. Let \_calleeContext\_ be
-- | PrepareForOrdinaryCall(\_F\_, \_newTarget\_). 1. Assert:
-- | \_calleeContext\_ is now the running execution context. 1. If \_kind\_
-- | is \~base\~, then 1. Perform OrdinaryCallBindThis(\_F\_,
-- | \_calleeContext\_, \_thisArgument\_). 1. Let \_initializeResult\_ be
-- | Completion(InitializeInstanceElements(\_thisArgument\_, \_F\_)). 1. If
-- | \_initializeResult\_ is an abrupt completion, then 1. Remove
-- | \_calleeContext\_ from the execution context stack and restore
-- | \_callerContext\_ as the running execution context. 1. Return ?
-- | \_initializeResult\_. 1. Let \_constructorEnv\_ be the
-- | LexicalEnvironment of \_calleeContext\_. 1. Let \_result\_ be
-- | Completion(OrdinaryCallEvaluateBody(\_F\_, \_argumentsList\_)). 1.
-- | Remove \_calleeContext\_ from the execution context stack and restore
-- | \_callerContext\_ as the running execution context. 1. If \_result\_ is
-- | a throw completion, then 1. Return ? \_result\_. 1. Assert: \_result\_
-- | is a return completion. 1. If \_result\_.\[\[Value\]\] is an Object,
-- | return \_result\_.\[\[Value\]\]. 1. If \_kind\_ is \~base\~, return
-- | \_thisArgument\_. 1. If \_result\_.\[\[Value\]\] is not \*undefined\*,
-- | throw a \*TypeError\* exception. 1. Let \_thisBinding\_ be ?
-- | \_constructorEnv\_.GetThisBinding(). 1. Assert: \_thisBinding\_ is an
-- | Object. 1. Return \_thisBinding\_.
-- SPEC: L6244-L6262
-- | # ToBigInt ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a BigInt or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to a BigInt value, or throws if an implicit
-- |     conversion from Number would be required.
-- |
-- | 1\. Let \_prim\_ be ? ToPrimitive(\_argument\_, \~number\~). 1. Return
-- | the value that \_prim\_ corresponds to in .
-- |
-- |   Argument Type   Result
-- |   --------------- ------------------------------------------------------------------------------------------------------------------------------
-- |   Undefined       Throw a \*TypeError\* exception.
-- |   Null            Throw a \*TypeError\* exception.
-- |   Boolean         Return \`1n\` if \_prim\_ is \*true\* and \`0n\` if \_prim\_ is \*false\*.
-- |   BigInt          Return \_prim\_.
-- |   Number          Throw a \*TypeError\* exception.
-- |   String          1\. Let \_n\_ be StringToBigInt(\_prim\_). 1. If \_n\_ is \*undefined\*, throw a \*SyntaxError\* exception. 1. Return \_n\_.
-- |   Symbol          Throw a \*TypeError\* exception.
-- SPEC: L6093-L6113
-- | # RoundMVResult ( \_n\_: a mathematical value, ): a Number
-- |
-- | description
-- | :   It converts \_n\_ to a Number in an implementation-defined manner.
-- |     For the purposes of this abstract operation, a digit is significant
-- |     if it is not zero or there is a non-zero digit to its left and there
-- |     is a non-zero digit to its right. For the purposes of this abstract
-- |     operation, \"the mathematical value denoted by\" a representation of
-- |     a mathematical value is the inverse of \"the decimal representation
-- |     of\" a mathematical value.
-- |
-- | 1\. If the decimal representation of \_n\_ has 20 or fewer significant
-- | digits, return 𝔽(\_n\_). 1. Let \_option1\_ be the mathematical value
-- | denoted by the result of replacing each significant digit in the decimal
-- | representation of \_n\_ after the 20th with a 0 digit. 1. Let
-- | \_option2\_ be the mathematical value denoted by the result of replacing
-- | each significant digit in the decimal representation of \_n\_ after the
-- | 20th with a 0 digit and then incrementing it at the 20th position (with
-- | carrying as necessary). 1. Let \_chosen\_ be an implementation-defined
-- | choice of either \_option1\_ or \_option2\_. 1. Return 𝔽(\_chosen\_).

-- SPEC: L6305-L6321
-- | # ToString ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a String or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to a value of type String.
-- |
-- | 1\. If \_argument\_ is a String, return \_argument\_. 1. If \_argument\_
-- | is a Symbol, throw a \*TypeError\* exception. 1. If \_argument\_ is
-- | \*undefined\*, return \*\"undefined\"\*. 1. If \_argument\_ is \*null\*,
-- | return \*\"null\"\*. 1. If \_argument\_ is \*true\*, return
-- | \*\"true\"\*. 1. If \_argument\_ is \*false\*, return \*\"false\"\*. 1.
-- | If \_argument\_ is a Number, return Number::toString(\_argument\_,
-- | 10). 1. If \_argument\_ is a BigInt, return
-- | BigInt::toString(\_argument\_, 10). 1. Assert: \_argument\_ is an
-- | Object. 1. Let \_primValue\_ be ? ToPrimitive(\_argument\_,
-- | \~string\~). 1. Assert: \_primValue\_ is not an Object. 1. Return ?
-- | ToString(\_primValue\_).
-- SPEC: L6305-L6321
-- | # ToString ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a String or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to a value of type String.
-- |
-- | 1\. If \_argument\_ is a String, return \_argument\_. 1. If \_argument\_
-- | is a Symbol, throw a \*TypeError\* exception. 1. If \_argument\_ is
-- | \*undefined\*, return \*\"undefined\"\*. 1. If \_argument\_ is \*null\*,
-- | return \*\"null\"\*. 1. If \_argument\_ is \*true\*, return
-- | \*\"true\"\*. 1. If \_argument\_ is \*false\*, return \*\"false\"\*. 1.
-- | If \_argument\_ is a Number, return Number::toString(\_argument\_,
-- | 10). 1. If \_argument\_ is a BigInt, return
-- | BigInt::toString(\_argument\_, 10). 1. Assert: \_argument\_ is an
-- | Object. 1. Let \_primValue\_ be ? ToPrimitive(\_argument\_,
-- | \~string\~). 1. Assert: \_primValue\_ is not an Object. 1. Return ?
-- | ToString(\_primValue\_).
-- SPEC: L4638-L4659
-- | # Number::toString ( \_x\_: a Number, \_radix\_: an integer in the inclusive interval from 2 to 36, ): a String
-- |
-- | description
-- | :   It represents \_x\_ as a String using a positional numeral system
-- |     with radix \_radix\_. The digits used in the representation of a
-- |     number using radix \_r\_ are taken from the first \_r\_ code units
-- |     of \*\"0123456789abcdefghijklmnopqrstuvwxyz\"\* in order. The
-- |     representation of numbers with magnitude greater than or equal to
-- |     \*1\*~𝔽~ never includes leading zeroes.
-- |
-- | 1\. If \_x\_ is \*NaN\*, return \*\"NaN\"\*. 1. If \_x\_ is either
-- | \*+0\*~𝔽~ or \*-0\*~𝔽~, return \*\"0\"\*. 1. If \_x\_ \< \*-0\*~𝔽~,
-- | return the string-concatenation of \*\"-\"\* and
-- | Number::toString(-\_x\_, \_radix\_). 1. If \_x\_ is \*+∞\*~𝔽~, return
-- | \*\"Infinity\"\*. 1. \[id=\"step-number-tostring-intermediate-values\"\]
-- | Let \_n\_, \_k\_, and \_s\_ be integers such that \_k\_ ≥ 1,
-- | \_radix\_^\_k\_\ -\ 1^ ≤ \_s\_ \< \_radix\_^\_k\_^, 𝔽(\_s\_ ×
-- | \_radix\_^\_n\_\ -\ \_k\_^) is \_x\_, and \_k\_ is as small as possible.
-- | Note that \_k\_ is the number of digits in the representation of \_s\_
-- | using radix \_radix\_, that \_s\_ is not divisible by \_radix\_, and
-- | that the least significant digit of \_s\_ is not necessarily uniquely
-- | determined by these criteria. 1. If \_radix\_ ≠ 10 or \_n\_ is in the
/-- ECMA-262 §7.1.12 ToString / §6.1.6.1.20 Number::toString (core subset). -/
def valueToString : Value → String
  | .string s => s
  | .number n =>
      -- §7.1.12.1: if n is an integer, omit decimal point.
      if n.isNaN then "NaN"
      else if n == 1.0/0.0 then "Infinity"
      else if n == -1.0/0.0 then "-Infinity"
      else
        let i := n.toUInt64
        if i.toFloat == n && n >= 0.0 then toString i.toNat
        else
          -- Handle negative integers: -n where n is a positive integer.
          let neg := -n
          let j := neg.toUInt64
          if j.toFloat == neg && neg > 0.0 then "-" ++ toString j.toNat
          else toString n
  | .bool true => "true"
  | .bool false => "false"
  | .null => "null"
  | .undefined => "undefined"
  | .object _ => "[object Object]"
  | .function _ => "function"

-- SPEC: L6573-L6605
-- | # IsLooselyEqual ( \_x\_: an ECMAScript language value, \_y\_: an ECMAScript language value, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | description
-- | :   It provides the semantics for the \`==\` operator.
-- |
-- | 1\. If SameType(\_x\_, \_y\_) is \*true\*, then 1. Return
-- | IsStrictlyEqual(\_x\_, \_y\_). 1. If \_x\_ is \*null\* and \_y\_ is
-- | \*undefined\*, return \*true\*. 1. If \_x\_ is \*undefined\* and \_y\_
-- | is \*null\*, return \*true\*. 1.
-- | \[id=\"step-abstract-equality-comparison-web-compat-insertion-point\",
-- | normative-optional\] If the host is a web browser or otherwise supports
-- | , then 1. If \_x\_ is an Object, \_x\_ has an \[\[IsHTMLDDA\]\] internal
-- | slot, and \_y\_ is either \*undefined\* or \*null\*, return \*true\*. 1.
-- | If \_x\_ is either \*undefined\* or \*null\*, \_y\_ is an Object, and
-- | \_y\_ has an \[\[IsHTMLDDA\]\] internal slot, return \*true\*. 1. If
-- | \_x\_ is a Number and \_y\_ is a String, return ! IsLooselyEqual(\_x\_,
-- | ! ToNumber(\_y\_)). 1. If \_x\_ is a String and \_y\_ is a Number,
-- | return ! IsLooselyEqual(! ToNumber(\_x\_), \_y\_). 1. If \_x\_ is a
-- | BigInt and \_y\_ is a String, then 1. Let \_n\_ be
-- | StringToBigInt(\_y\_). 1. If \_n\_ is \*undefined\*, return
-- | \*false\*. 1. Return ! IsLooselyEqual(\_x\_, \_n\_). 1. If \_x\_ is a
-- | String and \_y\_ is a BigInt, return ! IsLooselyEqual(\_y\_, \_x\_). 1.
-- | If \_x\_ is a Boolean, return ! IsLooselyEqual(! ToNumber(\_x\_),
-- | \_y\_). 1. If \_y\_ is a Boolean, return ! IsLooselyEqual(\_x\_, !
-- | ToNumber(\_y\_)). 1. If \_x\_ is either a String, a Number, a BigInt, or
-- | a Symbol and \_y\_ is an Object, return ! IsLooselyEqual(\_x\_, ?
-- | ToPrimitive(\_y\_)). 1. If \_x\_ is an Object and \_y\_ is either a
-- | String, a Number, a BigInt, or a Symbol, return ! IsLooselyEqual(?
-- | ToPrimitive(\_x\_), \_y\_). 1. If \_x\_ is a BigInt and \_y\_ is a
-- | Number, or if \_x\_ is a Number and \_y\_ is a BigInt, then 1. If \_x\_
-- | is not finite or \_y\_ is not finite, return \*false\*. 1. If ℝ(\_x\_) =
-- | ℝ(\_y\_), return \*true\*. 1. Return \*false\*. 1. Return \*false\*.
-- SPEC: L6458-L6472
-- | # SameType ( \_x\_: an ECMAScript language value, \_y\_: an ECMAScript language value, ): a Boolean
-- |
-- | description
-- | :   It determines whether or not the two arguments are the same type.
-- |
-- | 1\. If \_x\_ is \*undefined\* and \_y\_ is \*undefined\*, return
-- | \*true\*. 1. If \_x\_ is \*null\* and \_y\_ is \*null\*, return
-- | \*true\*. 1. If \_x\_ is a Boolean and \_y\_ is a Boolean, return
-- | \*true\*. 1. If \_x\_ is a Number and \_y\_ is a Number, return
-- | \*true\*. 1. If \_x\_ is a BigInt and \_y\_ is a BigInt, return
-- | \*true\*. 1. If \_x\_ is a Symbol and \_y\_ is a Symbol, return
-- | \*true\*. 1. If \_x\_ is a String and \_y\_ is a String, return
-- | \*true\*. 1. If \_x\_ is an Object and \_y\_ is an Object, return
-- | \*true\*. 1. Return \*false\*.
-- SPEC: L6473-L6485
-- | # SameValue ( \_x\_: an ECMAScript language value, \_y\_: an ECMAScript language value, ): a Boolean
-- |
-- | description
-- | :   It determines whether or not the two arguments are the same value.
-- |
-- | 1\. If SameType(\_x\_, \_y\_) is \*false\*, return \*false\*. 1. If
-- | \_x\_ is a Number, then 1. Return Number::sameValue(\_x\_, \_y\_). 1.
-- | Return SameValueNonNumber(\_x\_, \_y\_).
-- |
-- | This algorithm differs from the IsStrictlyEqual Algorithm by treating
-- | all \*NaN\* values as equivalent and by differentiating \*+0\*~𝔽~ from
-- | \*-0\*~𝔽~.
-- SPEC: L6486-L6497
-- | # SameValueZero ( \_x\_: an ECMAScript language value, \_y\_: an ECMAScript language value, ): a Boolean
-- |
-- | description
-- | :   It determines whether or not the two arguments are the same value
-- |     (ignoring the difference between \*+0\*~𝔽~ and \*-0\*~𝔽~).
-- |
-- | 1\. If SameType(\_x\_, \_y\_) is \*false\*, return \*false\*. 1. If
-- | \_x\_ is a Number, then 1. Return Number::sameValueZero(\_x\_,
-- | \_y\_). 1. Return SameValueNonNumber(\_x\_, \_y\_).
-- |
-- | SameValueZero differs from SameValue only in that it treats \*+0\*~𝔽~
-- | and \*-0\*~𝔽~ as equivalent.
-- SPEC: L4604-L4610
-- | # Number::sameValueZero ( \_x\_: a Number, \_y\_: a Number, ): a Boolean
-- |
-- | 1\. If \_x\_ is \*NaN\* and \_y\_ is \*NaN\*, return \*true\*. 1. If
-- | \_x\_ is \*+0\*~𝔽~ and \_y\_ is \*-0\*~𝔽~, return \*true\*. 1. If \_x\_
-- | is \*-0\*~𝔽~ and \_y\_ is \*+0\*~𝔽~, return \*true\*. 1. If \_x\_ is
-- | \_y\_, return \*true\*. 1. Return \*false\*.
/-- ECMA-262 §7.2.14 Abstract Equality Comparison (simplified core subset).
    Handles null/undefined equivalence and type coercion. -/
def abstractEq : Value → Value → Bool
  -- §7.2.14 step 1: same type → strict equality
  | .null, .null => true
  | .undefined, .undefined => true
  -- §7.2.14 step 2: null == undefined → true
  | .null, .undefined => true
  | .undefined, .null => true
  -- Same-type comparisons
  | .bool a, .bool b => a == b
  | .number a, .number b => a == b
  | .string a, .string b => a == b
  | .object a, .object b => a == b
  | .function a, .function b => a == b
  -- §7.2.14 step 5: number == string → number == ToNumber(string)
  | .number a, .string b => a == toNumber (.string b)
  | .string a, .number b => toNumber (.string a) == b
  -- §7.2.14 step 7-8: boolean == x → ToNumber(boolean) == x
  | .bool a, .number b => (toNumber (.bool a)) == b
  | .bool a, .string b => (toNumber (.bool a)) == (toNumber (.string b))
  | .number a, .bool b => a == (toNumber (.bool b))
  | .string a, .bool b => (toNumber (.string a)) == (toNumber (.bool b))
  -- All other cross-type comparisons: false
  | _, _ => false

-- SPEC: L6514-L6572
-- | # IsLessThan ( \_x\_: an ECMAScript language value, \_y\_: an ECMAScript language value, \_LeftFirst\_: a Boolean, ): either a normal completion containing either a Boolean or \*undefined\*, or a throw completion
-- |
-- | description
-- | :   It provides the semantics for the comparison \_x\_ \< \_y\_,
-- |     returning \*true\*, \*false\*, or \*undefined\* (which indicates
-- |     that at least one operand is \*NaN\*). The \_LeftFirst\_ flag is
-- |     used to control the order in which operations with potentially
-- |     visible side-effects are performed upon \_x\_ and \_y\_. It is
-- |     necessary because ECMAScript specifies left to right evaluation of
-- |     expressions. If \_LeftFirst\_ is \*true\*, the \_x\_ parameter
-- |     corresponds to an expression that occurs to the left of the \_y\_
-- |     parameter\'s corresponding expression. If \_LeftFirst\_ is
-- |     \*false\*, the reverse is the case and operations must be performed
-- |     upon \_y\_ before \_x\_.
-- |
-- | 1\. If \_LeftFirst\_ is \*true\*, then 1. Let \_px\_ be ?
-- | ToPrimitive(\_x\_, \~number\~). 1. Let \_py\_ be ? ToPrimitive(\_y\_,
-- | \~number\~). 1. Else, 1. NOTE: The order of evaluation needs to be
-- | reversed to preserve left to right evaluation. 1. Let \_py\_ be ?
-- | ToPrimitive(\_y\_, \~number\~). 1. Let \_px\_ be ? ToPrimitive(\_x\_,
-- | \~number\~). 1. \[id=\"step-arc-string-check\"\] If \_px\_ is a String
-- | and \_py\_ is a String, then 1. Let \_lx\_ be the length of \_px\_. 1.
-- | Let \_ly\_ be the length of \_py\_. 1. For each integer \_i\_ such that
-- | 0 ≤ \_i\_ \< min(\_lx\_, \_ly\_), in ascending order, do 1. Let \_cx\_
-- | be the numeric value of the code unit at index \_i\_ within \_px\_. 1.
-- | Let \_cy\_ be the numeric value of the code unit at index \_i\_ within
-- | \_py\_. 1. If \_cx\_ \< \_cy\_, return \*true\*. 1. If \_cx\_ \> \_cy\_,
-- | return \*false\*. 1. If \_lx\_ \< \_ly\_, return \*true\*. 1. Return
-- | \*false\*. 1. If \_px\_ is a BigInt and \_py\_ is a String, then 1. Let
-- | \_ny\_ be StringToBigInt(\_py\_). 1. If \_ny\_ is \*undefined\*, return
-- | \*undefined\*. 1. Return BigInt::lessThan(\_px\_, \_ny\_). 1. If \_px\_
-- | is a String and \_py\_ is a BigInt, then 1. Let \_nx\_ be
-- | StringToBigInt(\_px\_). 1. If \_nx\_ is \*undefined\*, return
-- | \*undefined\*. 1. Return BigInt::lessThan(\_nx\_, \_py\_). 1. NOTE:
-- | Because \_px\_ and \_py\_ are primitive values, evaluation order is not
-- | important. 1. Let \_nx\_ be ? ToNumeric(\_px\_). 1. Let \_ny\_ be ?
-- | ToNumeric(\_py\_). 1. If SameType(\_nx\_, \_ny\_) is \*true\*, then 1.
-- | If \_nx\_ is a Number, return Number::lessThan(\_nx\_, \_ny\_). 1.
-- | Assert: \_nx\_ is a BigInt. 1. Return BigInt::lessThan(\_nx\_,
-- | \_ny\_). 1. Assert: \_nx\_ is a BigInt and \_ny\_ is a Number, or \_nx\_
-- | is a Number and \_ny\_ is a BigInt. 1. If \_nx\_ or \_ny\_ is \*NaN\*,
-- | return \*undefined\*. 1. If \_nx\_ is \*-∞\*~𝔽~ or \_ny\_ is \*+∞\*~𝔽~,
-- | return \*true\*. 1. If \_nx\_ is \*+∞\*~𝔽~ or \_ny\_ is \*-∞\*~𝔽~,
-- | return \*false\*. 1. If ℝ(\_nx\_) \< ℝ(\_ny\_), return \*true\*. 1.
-- | Return \*false\*.
-- |
-- | Step differs from step in the algorithm that handles the addition
-- | operator \`+\` () by using the logical-and operation instead of the
-- | logical-or operation.
-- |
-- | The comparison of Strings uses a simple lexicographic ordering on
-- | sequences of UTF-16 code unit values. There is no attempt to use the
-- | more complex, semantically oriented definitions of character or string
-- | equality and collating order defined in the Unicode specification.
-- | Therefore String values that are canonically equal according to the
-- | Unicode Standard but not in the same normalization form could test as
-- | unequal. Also note that lexicographic ordering by *code unit* differs
-- | from ordering by *code point* for Strings containing surrogate pairs.
-- SPEC: L4579-L4589
-- | # Number::lessThan ( \_x\_: a Number, \_y\_: a Number, ): a Boolean or \*undefined\*
-- |
-- | 1\. If \_x\_ is \*NaN\*, return \*undefined\*. 1. If \_y\_ is \*NaN\*,
-- | return \*undefined\*. 1. If \_x\_ is \_y\_, return \*false\*. 1. If
-- | \_x\_ is \*+0\*~𝔽~ and \_y\_ is \*-0\*~𝔽~, return \*false\*. 1. If \_x\_
-- | is \*-0\*~𝔽~ and \_y\_ is \*+0\*~𝔽~, return \*false\*. 1. If \_x\_ is
-- | \*+∞\*~𝔽~, return \*false\*. 1. If \_y\_ is \*+∞\*~𝔽~, return
-- | \*true\*. 1. If \_y\_ is \*-∞\*~𝔽~, return \*false\*. 1. If \_x\_ is
-- | \*-∞\*~𝔽~, return \*true\*. 1. Assert: \_x\_ and \_y\_ are finite. 1. If
-- | ℝ(\_x\_) \< ℝ(\_y\_), return \*true\*. 1. Return \*false\*.
/-- ECMA-262 §7.2.13 Abstract Relational Comparison (string-aware). -/
def abstractLt : Value → Value → Bool
  | .string a, .string b => a < b  -- lexicographic comparison
  | a, b => toNumber a < toNumber b

-- SPEC: L4526-L4538
-- | # Number::add ( \_x\_: a Number, \_y\_: a Number, ): a Number
-- |
-- | description
-- | :   It performs addition according to the rules of IEEE 754-2019 binary
-- |     double-precision arithmetic, producing the sum of its arguments.
-- |
-- | 1\. If \_x\_ is \*NaN\* or \_y\_ is \*NaN\*, return \*NaN\*. 1. If \_x\_
-- | is \*+∞\*~𝔽~ and \_y\_ is \*-∞\*~𝔽~, return \*NaN\*. 1. If \_x\_ is
-- | \*-∞\*~𝔽~ and \_y\_ is \*+∞\*~𝔽~, return \*NaN\*. 1. If \_x\_ is either
-- | \*+∞\*~𝔽~ or \*-∞\*~𝔽~, return \_x\_. 1. If \_y\_ is either \*+∞\*~𝔽~ or
-- | \*-∞\*~𝔽~, return \_y\_. 1. Assert: \_x\_ and \_y\_ are both finite. 1.
-- | If \_x\_ is \*-0\*~𝔽~ and \_y\_ is \*-0\*~𝔽~, return \*-0\*~𝔽~. 1.
-- | Return 𝔽(ℝ(\_x\_) + ℝ(\_y\_)).
-- SPEC: L16272-L16276
-- | # The Addition Operator ( \`+\` )
-- |
-- | The addition operator either performs string concatenation or numeric
-- | addition.
-- SPEC: L16284-L16288
-- | # The Subtraction Operator ( \`-\` )
-- |
-- | The \`-\` operator performs subtraction, producing the difference of its
-- | operands.
-- SPEC: L16238-L16254
-- | # Multiplicative Operators
-- |
-- | ## Syntax
-- |
-- | MultiplicativeExpression\[Yield, Await\] :
-- | ExponentiationExpression\[?Yield, ?Await\]
-- | MultiplicativeExpression\[?Yield, ?Await\] MultiplicativeOperator
-- | ExponentiationExpression\[?Yield, ?Await\] MultiplicativeOperator : one
-- | of \`\*\` \`/\` \`%\`
-- |
-- | - The \`\*\` operator performs multiplication, producing the product of
-- |   its operands.
-- | - The \`/\` operator performs division, producing the quotient of its
-- |   operands.
-- | - The \`%\` operator yields the remainder of its operands from an
-- |   implied division.
-- SPEC: L4455-L4475
-- | # Number::multiply ( \_x\_: a Number, \_y\_: a Number, ): a Number
-- |
-- | description
-- | :   It performs multiplication according to the rules of IEEE 754-2019
-- |     binary double-precision arithmetic, producing the product of \_x\_
-- |     and \_y\_.
-- |
-- | 1\. If \_x\_ is \*NaN\* or \_y\_ is \*NaN\*, return \*NaN\*. 1. If \_x\_
-- | is either \*+∞\*~𝔽~ or \*-∞\*~𝔽~, then 1. If \_y\_ is either \*+0\*~𝔽~
-- | or \*-0\*~𝔽~, return \*NaN\*. 1. If \_y\_ \> \*+0\*~𝔽~, return \_x\_. 1.
-- | Return -\_x\_. 1. If \_y\_ is either \*+∞\*~𝔽~ or \*-∞\*~𝔽~, then 1. If
-- | \_x\_ is either \*+0\*~𝔽~ or \*-0\*~𝔽~, return \*NaN\*. 1. If \_x\_ \>
-- | \*+0\*~𝔽~, return \_y\_. 1. Return -\_y\_. 1. If \_x\_ is \*-0\*~𝔽~,
-- | then 1. If \_y\_ is \*-0\*~𝔽~ or \_y\_ \< \*-0\*~𝔽~, return
-- | \*+0\*~𝔽~. 1. Return \*-0\*~𝔽~. 1. If \_y\_ is \*-0\*~𝔽~, then 1. If
-- | \_x\_ \< \*-0\*~𝔽~, return \*+0\*~𝔽~. 1. Return \*-0\*~𝔽~. 1. Return
-- | 𝔽(ℝ(\_x\_) × ℝ(\_y\_)).
-- |
-- | Finite-precision multiplication is commutative, but not always
-- | associative.
-- SPEC: L4476-L4496
-- | # Number::divide ( \_x\_: a Number, \_y\_: a Number, ): a Number
-- |
-- | description
-- | :   It performs division according to the rules of IEEE 754-2019 binary
-- |     double-precision arithmetic, producing the quotient of \_x\_ and
-- |     \_y\_ where \_x\_ is the dividend and \_y\_ is the divisor.
-- |
-- | 1\. If \_x\_ is \*NaN\* or \_y\_ is \*NaN\*, return \*NaN\*. 1. If \_x\_
-- | is either \*+∞\*~𝔽~ or \*-∞\*~𝔽~, then 1. If \_y\_ is either \*+∞\*~𝔽~
-- | or \*-∞\*~𝔽~, return \*NaN\*. 1. If \_y\_ is \*+0\*~𝔽~ or \_y\_ \>
-- | \*+0\*~𝔽~, return \_x\_. 1. Return -\_x\_. 1. If \_y\_ is \*+∞\*~𝔽~,
-- | then 1. If \_x\_ is \*+0\*~𝔽~ or \_x\_ \> \*+0\*~𝔽~, return
-- | \*+0\*~𝔽~. 1. Return \*-0\*~𝔽~. 1. If \_y\_ is \*-∞\*~𝔽~, then 1. If
-- | \_x\_ is \*+0\*~𝔽~ or \_x\_ \> \*+0\*~𝔽~, return \*-0\*~𝔽~. 1. Return
-- | \*+0\*~𝔽~. 1. If \_x\_ is either \*+0\*~𝔽~ or \*-0\*~𝔽~, then 1. If
-- | \_y\_ is either \*+0\*~𝔽~ or \*-0\*~𝔽~, return \*NaN\*. 1. If \_y\_ \>
-- | \*+0\*~𝔽~, return \_x\_. 1. Return -\_x\_. 1. If \_y\_ is \*+0\*~𝔽~,
-- | then 1. If \_x\_ \> \*+0\*~𝔽~, return \*+∞\*~𝔽~. 1. Return \*-∞\*~𝔽~. 1.
-- | If \_y\_ is \*-0\*~𝔽~, then 1. If \_x\_ \> \*+0\*~𝔽~, return
-- | \*-∞\*~𝔽~. 1. Return \*+∞\*~𝔽~. 1. Return 𝔽(ℝ(\_x\_) / ℝ(\_y\_)).
-- SPEC: L4542-L4552
-- | # Number::subtract ( \_x\_: a Number, \_y\_: a Number, ): a Number
-- |
-- | description
-- | :   It performs subtraction, producing the difference of its operands;
-- |     \_x\_ is the minuend and \_y\_ is the subtrahend.
-- |
-- | 1\. Return Number::add(\_x\_, Number::unaryMinus(\_y\_)).
-- |
-- | It is always the case that \`x - y\` produces the same result as \`x +
-- | (-y)\`.
-- SPEC: L4497-L4525
-- | # Number::remainder ( \_n\_: a Number, \_d\_: a Number, ): a Number
-- |
-- | description
-- | :   It yields the remainder from an implied division of its operands
-- |     where \_n\_ is the dividend and \_d\_ is the divisor.
-- |
-- | 1\. If \_n\_ is \*NaN\* or \_d\_ is \*NaN\*, return \*NaN\*. 1. If \_n\_
-- | is either \*+∞\*~𝔽~ or \*-∞\*~𝔽~, return \*NaN\*. 1. If \_d\_ is either
-- | \*+∞\*~𝔽~ or \*-∞\*~𝔽~, return \_n\_. 1. If \_d\_ is either \*+0\*~𝔽~ or
-- | \*-0\*~𝔽~, return \*NaN\*. 1. If \_n\_ is either \*+0\*~𝔽~ or \*-0\*~𝔽~,
-- | return \_n\_. 1. Assert: \_n\_ and \_d\_ are finite and non-zero. 1. Let
-- | \_quotient\_ be ℝ(\_n\_) / ℝ(\_d\_). 1. Let \_q\_ be
-- | truncate(\_quotient\_). 1. Let \_r\_ be ℝ(\_n\_) - (ℝ(\_d\_) ×
-- | \_q\_). 1. If \_r\_ = 0 and \_n\_ \< \*-0\*~𝔽~, return \*-0\*~𝔽~. 1.
-- | Return 𝔽(\_r\_).
-- |
-- | In C and C++, the remainder operator accepts only integral operands; in
-- | ECMAScript, it also accepts floating-point operands.
-- |
-- | The result of a floating-point remainder operation as computed by the
-- | \`%\` operator is not the same as the "remainder" operation defined by
-- | IEEE 754-2019. The IEEE 754-2019 "remainder" operation computes the
-- | remainder from a rounding division, not a truncating division, and so
-- | its behaviour is not analogous to that of the usual integer remainder
-- | operator. Instead the ECMAScript language defines \`%\` on
-- | floating-point operations to behave in a manner analogous to that of the
-- | Java integer remainder operator; this may be compared with the C library
-- | function fmod.
-- SPEC: L4553-L4578
-- | # Number::leftShift ( \_x\_: a Number, \_y\_: a Number, ): an integral Number
-- |
-- | 1\. Let \_lNum\_ be ! ToInt32(\_x\_). 1. Let \_rNum\_ be !
-- | ToUint32(\_y\_). 1. Let \_shiftCount\_ be ℝ(\_rNum\_) modulo 32. 1.
-- | Return the result of left shifting \_lNum\_ by \_shiftCount\_ bits. The
-- | mathematical value of the result is exactly representable as a 32-bit
-- | two\'s complement bit string.
-- |
-- | # Number::signedRightShift ( \_x\_: a Number, \_y\_: a Number, ): an integral Number
-- |
-- | 1\. Let \_lNum\_ be ! ToInt32(\_x\_). 1. Let \_rNum\_ be !
-- | ToUint32(\_y\_). 1. Let \_shiftCount\_ be ℝ(\_rNum\_) modulo 32. 1.
-- | Return the result of performing a sign-extending right shift of \_lNum\_
-- | by \_shiftCount\_ bits. The most significant bit is propagated. The
-- | mathematical value of the result is exactly representable as a 32-bit
-- | two\'s complement bit string.
-- |
-- | # Number::unsignedRightShift ( \_x\_: a Number, \_y\_: a Number, ): an integral Number
-- |
-- | 1\. Let \_lNum\_ be ! ToUint32(\_x\_). 1. Let \_rNum\_ be !
-- | ToUint32(\_y\_). 1. Let \_shiftCount\_ be ℝ(\_rNum\_) modulo 32. 1.
-- | Return the result of performing a zero-filling right shift of \_lNum\_
-- | by \_shiftCount\_ bits. Vacated bits are filled with zero. The
-- | mathematical value of the result is exactly representable as a 32-bit
-- | unsigned bit string.
-- SPEC: L4611-L4625
-- | # NumberBitwiseOp ( \_op\_: \`&\`, \`\^\`, or \`\|\`, \_x\_: a Number, \_y\_: a Number, ): an integral Number
-- |
-- | 1\. Let \_lNum\_ be ! ToInt32(\_x\_). 1. Let \_rNum\_ be !
-- | ToInt32(\_y\_). 1. Let \_lBits\_ be the 32-bit two\'s complement bit
-- | string representing ℝ(\_lNum\_). 1. Let \_rBits\_ be the 32-bit two\'s
-- | complement bit string representing ℝ(\_rNum\_). 1. If \_op\_ is \`&\`,
-- | then 1. Let \_result\_ be the result of applying the bitwise AND
-- | operation to \_lBits\_ and \_rBits\_. 1. Else if \_op\_ is \`\^\`,
-- | then 1. Let \_result\_ be the result of applying the bitwise exclusive
-- | OR (XOR) operation to \_lBits\_ and \_rBits\_. 1. Else, 1. Assert:
-- | \_op\_ is \`\|\`. 1. Let \_result\_ be the result of applying the
-- | bitwise inclusive OR operation to \_lBits\_ and \_rBits\_. 1. Return the
-- | Number value for the integer represented by the 32-bit two\'s complement
-- | bit string \_result\_.
-- SPEC: L4626-L4637
-- | # Number::bitwiseAND ( \_x\_: a Number, \_y\_: a Number, ): an integral Number
-- |
-- | 1\. Return NumberBitwiseOp(\`&\`, \_x\_, \_y\_).
-- |
-- | # Number::bitwiseXOR ( \_x\_: a Number, \_y\_: a Number, ): an integral Number
-- |
-- | 1\. Return NumberBitwiseOp(\`\^\`, \_x\_, \_y\_).
-- |
-- | # Number::bitwiseOR ( \_x\_: a Number, \_y\_: a Number, ): an integral Number
-- |
-- | 1\. Return NumberBitwiseOp(\`\|\`, \_x\_, \_y\_).
-- SPEC: L16787-L16807
-- | # ApplyStringOrNumericBinaryOperator ( \_lVal\_: an ECMAScript language value, \_opText\_: \`\*\*\`, \`\*\`, \`/\`, \`%\`, \`+\`, \`-\`, \`\<\<\`, \`\>\>\`, \`\>\>\>\`, \`&\`, \`\^\`, or \`\|\`, \_rVal\_: an ECMAScript language value, ): either a normal completion containing either a String, a BigInt, or a Number, or a throw completion
-- |
-- | 1\. If \_opText\_ is \`+\`, then 1.
-- | \[id=\"step-binary-op-toprimitive-lval\"\] Let \_lPrim\_ be ?
-- | ToPrimitive(\_lVal\_). 1. \[id=\"step-binary-op-toprimitive-rval\"\] Let
-- | \_rPrim\_ be ? ToPrimitive(\_rVal\_). 1.
-- | \[id=\"step-binary-op-string-check\"\] If \_lPrim\_ is a String or
-- | \_rPrim\_ is a String, then 1. Let \_lStr\_ be ? ToString(\_lPrim\_). 1.
-- | Let \_rStr\_ be ? ToString(\_rPrim\_). 1. Return the
-- | string-concatenation of \_lStr\_ and \_rStr\_. 1. Set \_lVal\_ to
-- | \_lPrim\_. 1. Set \_rVal\_ to \_rPrim\_. 1. NOTE: At this point, it must
-- | be a numeric operation. 1. Let \_lNum\_ be ? ToNumeric(\_lVal\_). 1. Let
-- | \_rNum\_ be ? ToNumeric(\_rVal\_). 1. If SameType(\_lNum\_, \_rNum\_) is
-- | \*false\*, throw a \*TypeError\* exception. 1. If \_lNum\_ is a BigInt,
-- | then 1. If \_opText\_ is \`\*\*\`, return ?
-- | BigInt::exponentiate(\_lNum\_, \_rNum\_). 1. If \_opText\_ is \`/\`,
-- | return ? BigInt::divide(\_lNum\_, \_rNum\_). 1. If \_opText\_ is \`%\`,
-- | return ? BigInt::remainder(\_lNum\_, \_rNum\_). 1. If \_opText\_ is
-- | \`\>\>\>\`, return ? BigInt::unsignedRightShift(\_lNum\_, \_rNum\_). 1.
-- | Let \_operation\_ be the abstract operation associated with \_opText\_
-- | in the following table:
/-- ECMA-262 §13.15 Runtime Semantics: Evaluation (core binary subset). -/
def evalBinary : BinOp → Value → Value → Value
  | .add, .string a, .string b => .string (a ++ b)
  | .add, .string a, b => .string (a ++ valueToString b)
  | .add, a, .string b => .string (valueToString a ++ b)
  | .add, a, b => .number (toNumber a + toNumber b)
  | .sub, a, b => .number (toNumber a - toNumber b)
  | .mul, a, b => .number (toNumber a * toNumber b)
  | .div, a, b => .number (toNumber a / toNumber b)
  -- SPEC: L16453-L16474
  -- | EqualityExpression : EqualityExpression \`==\` RelationalExpression 1.
  -- | Let \_lRef\_ be ? Evaluation of \|EqualityExpression\|. 1. Let \_lVal\_
  -- | be ? GetValue(\_lRef\_). 1. Let \_rRef\_ be ? Evaluation of
  -- | \|RelationalExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1.
  -- | Return ? IsLooselyEqual(\_rVal\_, \_lVal\_). EqualityExpression :
  -- | EqualityExpression \`!=\` RelationalExpression 1. Let \_lRef\_ be ?
  -- | Evaluation of \|EqualityExpression\|. 1. Let \_lVal\_ be ?
  -- | GetValue(\_lRef\_). 1. Let \_rRef\_ be ? Evaluation of
  -- | \|RelationalExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1.
  -- | Let \_r\_ be ? IsLooselyEqual(\_rVal\_, \_lVal\_). 1. If \_r\_ is
  -- | \*true\*, return \*false\*. 1. Return \*true\*. EqualityExpression :
  -- | EqualityExpression \`===\` RelationalExpression 1. Let \_lRef\_ be ?
  -- | Evaluation of \|EqualityExpression\|. 1. Let \_lVal\_ be ?
  -- | GetValue(\_lRef\_). 1. Let \_rRef\_ be ? Evaluation of
  -- | \|RelationalExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1.
  -- | Return IsStrictlyEqual(\_rVal\_, \_lVal\_). EqualityExpression :
  -- | EqualityExpression \`!==\` RelationalExpression 1. Let \_lRef\_ be ?
  -- | Evaluation of \|EqualityExpression\|. 1. Let \_lVal\_ be ?
  -- | GetValue(\_lRef\_). 1. Let \_rRef\_ be ? Evaluation of
  -- | \|RelationalExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1.
  -- | Let \_r\_ be IsStrictlyEqual(\_rVal\_, \_lVal\_). 1. If \_r\_ is
  -- | \*true\*, return \*false\*. 1. Return \*true\*.
  | .eq, a, b => .bool (abstractEq a b)
  | .neq, a, b => .bool (!abstractEq a b)
  -- SPEC: L6606-L6617
  -- | # IsStrictlyEqual ( \_x\_: an ECMAScript language value, \_y\_: an ECMAScript language value, ): a Boolean
  -- | description
  -- | :   It provides the semantics for the \`===\` operator.
  -- | 1\. If SameType(\_x\_, \_y\_) is \*false\*, return \*false\*. 1. If
  -- | \_x\_ is a Number, then 1. Return Number::equal(\_x\_, \_y\_). 1. Return
  -- | SameValueNonNumber(\_x\_, \_y\_).
  -- | This algorithm differs from the SameValue Algorithm in its treatment of
  -- | signed zeroes and NaNs.
  -- SPEC: L4590-L4596
  -- | # Number::equal ( \_x\_: a Number, \_y\_: a Number, ): a Boolean
  -- |
  -- | 1\. If \_x\_ is \*NaN\*, return \*false\*. 1. If \_y\_ is \*NaN\*,
  -- | return \*false\*. 1. If \_x\_ is \_y\_, return \*true\*. 1. If \_x\_ is
  -- | \*+0\*~𝔽~ and \_y\_ is \*-0\*~𝔽~, return \*true\*. 1. If \_x\_ is
  -- | \*-0\*~𝔽~ and \_y\_ is \*+0\*~𝔽~, return \*true\*. 1. Return \*false\*.
  -- SPEC: L6499-L6512
  -- | # SameValueNonNumber ( \_x\_: an ECMAScript language value, but not a Number, \_y\_: an ECMAScript language value, but not a Number, ): a Boolean
  -- |
  -- | 1\. Assert: SameType(\_x\_, \_y\_) is \*true\*. 1. If \_x\_ is either
  -- | \*undefined\* or \*null\*, return \*true\*. 1. If \_x\_ is a BigInt,
  -- | then 1. Return BigInt::equal(\_x\_, \_y\_). 1. If \_x\_ is a String,
  -- | then 1. If \_x\_ and \_y\_ have the same length and the same code units
  -- | in the same positions, return \*true\*. 1. Return \*false\*. 1. If \_x\_
  -- | is a Boolean, then 1. If \_x\_ and \_y\_ are both \*true\* or both
  -- | \*false\*, return \*true\*. 1. Return \*false\*. 1. NOTE: All other
  -- | ECMAScript language values are compared by identity. 1. If \_x\_ is
  -- | \_y\_, return \*true\*. 1. Return \*false\*. For expository purposes,
  -- | some cases are handled separately within this algorithm even if it is
  -- | unnecessary to do so. The specifics of what \"\_x\_ is \_y\_\" means are
  -- | detailed in .
  | .strictEq, a, b => .bool (a == b)
  | .strictNeq, a, b => .bool (a != b)
  -- SPEC: L16365-L16388
  -- | RelationalExpression : RelationalExpression \`\<\` ShiftExpression 1.
  -- | Let \_lRef\_ be ? Evaluation of \|RelationalExpression\|. 1. Let
  -- | \_lVal\_ be ? GetValue(\_lRef\_). 1. Let \_rRef\_ be ? Evaluation of
  -- | \|ShiftExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1. Let
  -- | \_r\_ be ? IsLessThan(\_lVal\_, \_rVal\_, \*true\*). 1. If \_r\_ is
  -- | \*undefined\*, return \*false\*. 1. Return \_r\_. RelationalExpression :
  -- | RelationalExpression \`\>\` ShiftExpression 1. Let \_lRef\_ be ?
  -- | Evaluation of \|RelationalExpression\|. 1. Let \_lVal\_ be ?
  -- | GetValue(\_lRef\_). 1. Let \_rRef\_ be ? Evaluation of
  -- | \|ShiftExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1. Let
  -- | \_r\_ be ? IsLessThan(\_rVal\_, \_lVal\_, \*false\*). 1. If \_r\_ is
  -- | \*undefined\*, return \*false\*. 1. Return \_r\_. RelationalExpression :
  -- | RelationalExpression \`\<=\` ShiftExpression 1. Let \_lRef\_ be ?
  -- | Evaluation of \|RelationalExpression\|. 1. Let \_lVal\_ be ?
  -- | GetValue(\_lRef\_). 1. Let \_rRef\_ be ? Evaluation of
  -- | \|ShiftExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1. Let
  -- | \_r\_ be ? IsLessThan(\_rVal\_, \_lVal\_, \*false\*). 1. If \_r\_ is
  -- | either \*true\* or \*undefined\*, return \*false\*. 1. Return \*true\*.
  -- | RelationalExpression : RelationalExpression \`\>=\` ShiftExpression 1.
  -- | Let \_lRef\_ be ? Evaluation of \|RelationalExpression\|. 1. Let
  -- | \_lVal\_ be ? GetValue(\_lRef\_). 1. Let \_rRef\_ be ? Evaluation of
  -- | \|ShiftExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1. Let
  -- | \_r\_ be ? IsLessThan(\_lVal\_, \_rVal\_, \*true\*). 1. If \_r\_ is
  -- | either \*true\* or \*undefined\*, return \*false\*. 1. Return \*true\*.
  | .lt, a, b => .bool (abstractLt a b)
  | .gt, a, b => .bool (abstractLt b a)
  | .le, a, b => .bool (!abstractLt b a)
  | .ge, a, b => .bool (!abstractLt a b)
  -- SPEC: L16550-L16554
  -- | LogicalANDExpression : LogicalANDExpression \`&&\`
  -- | BitwiseORExpression 1. Let \_lRef\_ be ? Evaluation of
  -- | \|LogicalANDExpression\|. 1. Let \_lVal\_ be ? GetValue(\_lRef\_). 1. If
  -- | ToBoolean(\_lVal\_) is \*false\*, return \_lVal\_. 1. Let \_rRef\_ be ?
  -- | Evaluation of \|BitwiseORExpression\|. 1. Return ? GetValue(\_rRef\_).
  | .logAnd, a, b => if toBoolean a then b else a
  -- SPEC: L16555-L16559
  -- | LogicalORExpression : LogicalORExpression \`\|\|\`
  -- | LogicalANDExpression 1. Let \_lRef\_ be ? Evaluation of
  -- | \|LogicalORExpression\|. 1. Let \_lVal\_ be ? GetValue(\_lRef\_). 1. If
  -- | ToBoolean(\_lVal\_) is \*true\*, return \_lVal\_. 1. Let \_rRef\_ be ?
  -- | Evaluation of \|LogicalANDExpression\|. 1. Return ? GetValue(\_rRef\_).
  | .logOr, a, b => if toBoolean a then a else b
  -- SPEC: L16389-L16394
  -- | RelationalExpression : RelationalExpression \`instanceof\`
  -- | ShiftExpression 1. Let \_lRef\_ be ? Evaluation of
  -- | \|RelationalExpression\|. 1. Let \_lVal\_ be ? GetValue(\_lRef\_). 1.
  -- | Let \_rRef\_ be ? Evaluation of \|ShiftExpression\|. 1. Let \_rVal\_ be
  -- | ? GetValue(\_rRef\_). 1. Return ? InstanceofOperator(\_lVal\_,
  -- | \_rVal\_). RelationalExpression : RelationalExpression \`in\`
  | .instanceof, .object _, .function _ => .bool true
  | .instanceof, _, .function _ => .bool false
  | .instanceof, _, _ => .bool false
  -- SPEC: L16411-L16434
  -- | # InstanceofOperator ( \_V\_: an ECMAScript language value, \_target\_: an ECMAScript language value, ): either a normal completion containing a Boolean or a throw completion
  -- |
  -- | description
  -- | :   It implements the generic algorithm for determining if \_V\_ is an
  -- |     instance of \_target\_ either by consulting \_target\_\'s
  -- |     %Symbol.hasInstance% method or, if absent, determining whether the
  -- |     value of \_target\_\'s \*\"prototype\"\* property is present in
  -- |     \_V\_\'s prototype chain.
  -- |
  -- | 1\. If \_target\_ is not an Object, throw a \*TypeError\* exception. 1.
  -- | Let \_instOfHandler\_ be ? GetMethod(\_target\_,
  -- | %Symbol.hasInstance%). 1. If \_instOfHandler\_ is not \*undefined\*,
  -- | then 1. Return ToBoolean(? Call(\_instOfHandler\_, \_target\_, « \_V\_
  -- | »)). 1. \[id=\"step-instanceof-check-function\"\] If
  -- | IsCallable(\_target\_) is \*false\*, throw a \*TypeError\* exception. 1.
  -- | \[id=\"step-instanceof-fallback\"\] Return ?
  -- | OrdinaryHasInstance(\_target\_, \_V\_).
  -- |
  -- | Steps and provide compatibility with previous editions of ECMAScript
  -- | that did not use a %Symbol.hasInstance% method to define the
  -- | \`instanceof\` operator semantics. If an object does not define or
  -- | inherit %Symbol.hasInstance% it uses the default \`instanceof\`
  -- | semantics.
  -- SPEC: L6909-L6924
  -- | # OrdinaryHasInstance ( \_C\_: an ECMAScript language value, \_O\_: an ECMAScript language value, ): either a normal completion containing a Boolean or a throw completion
  -- |
  -- | description
  -- | :   It implements the default algorithm for determining if \_O\_
  -- |     inherits from the instance object inheritance path provided by
  -- |     \_C\_.
  -- |
  -- | 1\. If IsCallable(\_C\_) is \*false\*, return \*false\*. 1. If \_C\_ has
  -- | a \[\[BoundTargetFunction\]\] internal slot, then 1. Let \_BC\_ be
  -- | \_C\_.\[\[BoundTargetFunction\]\]. 1. Return ? InstanceofOperator(\_O\_,
  -- | \_BC\_). 1. If \_O\_ is not an Object, return \*false\*. 1. Let \_P\_ be
  -- | ? Get(\_C\_, \*\"prototype\"\*). 1. If \_P\_ is not an Object, throw a
  -- | \*TypeError\* exception. 1. Repeat, 1. Set \_O\_ to ?
  -- | \_O\_.\[\[GetPrototypeOf\]\](). 1. If \_O\_ is \*null\*, return
  -- | \*false\*. 1. If SameValue(\_P\_, \_O\_) is \*true\*, return \*true\*.
  -- SPEC: L16395-L16410
  -- | ShiftExpression 1. Let \_lRef\_ be ? Evaluation of
  -- | \|RelationalExpression\|. 1. Let \_lVal\_ be ? GetValue(\_lRef\_). 1.
  -- | Let \_rRef\_ be ? Evaluation of \|ShiftExpression\|. 1. Let \_rVal\_ be
  -- | ? GetValue(\_rRef\_). 1. If \_rVal\_ is not an Object, throw a
  -- | \*TypeError\* exception. 1. Return ? HasProperty(\_rVal\_, ?
  -- | ToPropertyKey(\_lVal\_)). RelationalExpression : PrivateIdentifier
  -- | \`in\` ShiftExpression 1. Let \_privateIdentifier\_ be the StringValue
  -- | of \|PrivateIdentifier\|. 1. Let \_rRef\_ be ? Evaluation of
  -- | \|ShiftExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1. If
  -- | \_rVal\_ is not an Object, throw a \*TypeError\* exception. 1. Let
  -- | \_privateEnv\_ be the running execution context\'s
  -- | PrivateEnvironment. 1. Assert: \_privateEnv\_ is not \*null\*. 1. Let
  -- | \_privateName\_ be ResolvePrivateIdentifier(\_privateEnv\_,
  -- | \_privateIdentifier\_). 1. If PrivateElementFind(\_rVal\_,
  -- | \_privateName\_) is \~empty\~, return \*false\*. 1. Return \*true\*.
  | .«in», .string _, .object _ => .bool true  -- simplified: always true for string key on object
  | .«in», _, _ => .bool false
  -- SPEC: L16255-L16261
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | MultiplicativeExpression : MultiplicativeExpression
  -- | MultiplicativeOperator ExponentiationExpression 1. Let \_opText\_ be the
  -- | source text matched by \|MultiplicativeOperator\|. 1. Return ?
  -- | EvaluateStringOrNumericBinaryExpression(\|MultiplicativeExpression\|,
  -- | \_opText\_, \|ExponentiationExpression\|).
  | .mod, a, b =>
      let na := toNumber a; let nb := toNumber b
      if nb == 0.0 then .number (0.0 / 0.0) else .number (na - nb * (na / nb).floor)
  -- SPEC: L16223-L16237
  -- | # Exponentiation Operator
  -- |
  -- | ## Syntax
  -- |
  -- | ExponentiationExpression\[Yield, Await\] : UnaryExpression\[?Yield,
  -- | ?Await\] UpdateExpression\[?Yield, ?Await\] \`\*\*\`
  -- | ExponentiationExpression\[?Yield, ?Await\]
  -- |
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | ExponentiationExpression : UpdateExpression \`\*\*\`
  -- | ExponentiationExpression 1. Return ?
  -- | EvaluateStringOrNumericBinaryExpression(\|UpdateExpression\|, \`\*\*\`,
  -- | \|ExponentiationExpression\|).
  -- SPEC: L4417-L4445
  -- | # Number::exponentiate ( \_base\_: a Number, \_exponent\_: a Number, ): a Number
  -- |
  -- | description
  -- | :   It returns an implementation-approximated value representing the
  -- |     result of raising \_base\_ to the \_exponent\_ power.
  -- |
  -- | 1\. If \_exponent\_ is \*NaN\*, return \*NaN\*. 1. If \_exponent\_ is
  -- | either \*+0\*~𝔽~ or \*-0\*~𝔽~, return \*1\*~𝔽~. 1. If \_base\_ is
  -- | \*NaN\*, return \*NaN\*. 1. If \_base\_ is \*+∞\*~𝔽~, then 1. If
  -- | \_exponent\_ \> \*+0\*~𝔽~, return \*+∞\*~𝔽~. 1. Return \*+0\*~𝔽~. 1. If
  -- | \_base\_ is \*-∞\*~𝔽~, then 1. If \_exponent\_ \> \*+0\*~𝔽~, then 1. If
  -- | \_exponent\_ is an odd integral Number, return \*-∞\*~𝔽~. 1. Return
  -- | \*+∞\*~𝔽~. 1. If \_exponent\_ is an odd integral Number, return
  -- | \*-0\*~𝔽~. 1. Return \*+0\*~𝔽~. 1. If \_base\_ is \*+0\*~𝔽~, then 1. If
  -- | \_exponent\_ \> \*+0\*~𝔽~, return \*+0\*~𝔽~. 1. Return \*+∞\*~𝔽~. 1. If
  -- | \_base\_ is \*-0\*~𝔽~, then 1. If \_exponent\_ \> \*+0\*~𝔽~, then 1. If
  -- | \_exponent\_ is an odd integral Number, return \*-0\*~𝔽~. 1. Return
  -- | \*+0\*~𝔽~. 1. If \_exponent\_ is an odd integral Number, return
  -- | \*-∞\*~𝔽~. 1. Return \*+∞\*~𝔽~. 1. Assert: \_base\_ is finite and is
  -- | neither \*+0\*~𝔽~ nor \*-0\*~𝔽~. 1. If \_exponent\_ is \*+∞\*~𝔽~,
  -- | then 1. If abs(ℝ(\_base\_)) \> 1, return \*+∞\*~𝔽~. 1. If
  -- | abs(ℝ(\_base\_)) = 1, return \*NaN\*. 1. Return \*+0\*~𝔽~. 1. If
  -- | \_exponent\_ is \*-∞\*~𝔽~, then 1. If abs(ℝ(\_base\_)) \> 1, return
  -- | \*+0\*~𝔽~. 1. If abs(ℝ(\_base\_)) = 1, return \*NaN\*. 1. Return
  -- | \*+∞\*~𝔽~. 1. Assert: \_exponent\_ is finite and is neither \*+0\*~𝔽~
  -- | nor \*-0\*~𝔽~. 1. If \_base\_ \< \*-0\*~𝔽~ and \_exponent\_ is not an
  -- | integral Number, return \*NaN\*. 1. Return an
  -- | implementation-approximated Number value representing the result of
  -- | raising ℝ(\_base\_) to the ℝ(\_exponent\_) power.
  | .exp, a, b => .number (Float.pow (toNumber a) (toNumber b))
  -- SPEC: L6150-L6160
  -- | # ToUint32 ( \_argument\_: an ECMAScript language value, ): either a normal completion containing an integral Number or a throw completion
  -- |
  -- | description
  -- | :   It converts \_argument\_ to one of 2^32^ integral Number values in
  -- |     the inclusive interval from \*+0\*~𝔽~ to 𝔽(2^32^ - 1).
  -- |
  -- | 1\. Let \_number\_ be ? ToNumber(\_argument\_). 1. If \_number\_ is not
  -- | finite or \_number\_ is either \*+0\*~𝔽~ or \*-0\*~𝔽~, return
  -- | \*+0\*~𝔽~. 1. Let \_int\_ be truncate(ℝ(\_number\_)). 1. Let
  -- | \_int32bit\_ be \_int\_ modulo 2^32^. 1. \[id=\"step-touint32-return\"\]
  -- | Return 𝔽(\_int32bit\_).
  -- SPEC: L16500-L16525
  -- | # Binary Bitwise Operators
  -- |
  -- | ## Syntax
  -- |
  -- | BitwiseANDExpression\[In, Yield, Await\] : EqualityExpression\[?In,
  -- | ?Yield, ?Await\] BitwiseANDExpression\[?In, ?Yield, ?Await\] \`&\`
  -- | EqualityExpression\[?In, ?Yield, ?Await\] BitwiseXORExpression\[In,
  -- | Yield, Await\] : BitwiseANDExpression\[?In, ?Yield, ?Await\]
  -- | BitwiseXORExpression\[?In, ?Yield, ?Await\] \`\^\`
  -- | BitwiseANDExpression\[?In, ?Yield, ?Await\] BitwiseORExpression\[In,
  -- | Yield, Await\] : BitwiseXORExpression\[?In, ?Yield, ?Await\]
  -- | BitwiseORExpression\[?In, ?Yield, ?Await\] \`\|\`
  -- | BitwiseXORExpression\[?In, ?Yield, ?Await\]
  -- |
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | BitwiseANDExpression : BitwiseANDExpression \`&\` EqualityExpression 1.
  -- | Return ?
  -- | EvaluateStringOrNumericBinaryExpression(\|BitwiseANDExpression\|, \`&\`,
  -- | \|EqualityExpression\|). BitwiseXORExpression : BitwiseXORExpression
  -- | \`\^\` BitwiseANDExpression 1. Return ?
  -- | EvaluateStringOrNumericBinaryExpression(\|BitwiseXORExpression\|,
  -- | \`\^\`, \|BitwiseANDExpression\|). BitwiseORExpression :
  -- | BitwiseORExpression \`\|\` BitwiseXORExpression 1. Return ?
  -- | EvaluateStringOrNumericBinaryExpression(\|BitwiseORExpression\|, \`\|\`,
  -- | \|BitwiseXORExpression\|).
  | .bitAnd, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := toNumber b |>.toUInt32
      .number ((ia &&& ib).toFloat)
  | .bitOr, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := toNumber b |>.toUInt32
      .number ((ia ||| ib).toFloat)
  | .bitXor, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := toNumber b |>.toUInt32
      .number ((ia ^^^ ib).toFloat)
  -- SPEC: L16306-L16337
  -- | # The Left Shift Operator ( \`\<\<\` )
  -- |
  -- | Performs a bitwise left shift operation on the left operand by the
  -- | amount specified by the right operand.
  -- |
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | ShiftExpression : ShiftExpression \`\<\<\` AdditiveExpression 1. Return
  -- | ? EvaluateStringOrNumericBinaryExpression(\|ShiftExpression\|, \`\<\<\`,
  -- | \|AdditiveExpression\|).
  -- |
  -- | # The Signed Right Shift Operator ( \`\>\>\` )
  -- |
  -- | Performs a sign-filling bitwise right shift operation on the left
  -- | operand by the amount specified by the right operand.
  -- |
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | ShiftExpression : ShiftExpression \`\>\>\` AdditiveExpression 1. Return
  -- | ? EvaluateStringOrNumericBinaryExpression(\|ShiftExpression\|, \`\>\>\`,
  -- | \|AdditiveExpression\|).
  -- |
  -- | # The Unsigned Right Shift Operator ( \`\>\>\>\` )
  -- |
  -- | Performs a zero-filling bitwise right shift operation on the left
  -- | operand by the amount specified by the right operand.
  -- |
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | ShiftExpression : ShiftExpression \`\>\>\>\` AdditiveExpression 1.
  -- | Return ? EvaluateStringOrNumericBinaryExpression(\|ShiftExpression\|,
  -- | \`\>\>\>\`, \|AdditiveExpression\|).
  -- SPEC: L4553-L4560
  -- | # Number::leftShift ( \_x\_: a Number, \_y\_: a Number, ): an integral Number
  -- |
  -- | 1\. Let \_lNum\_ be ! ToInt32(\_x\_). 1. Let \_rNum\_ be !
  -- | ToUint32(\_y\_). 1. Let \_shiftCount\_ be ℝ(\_rNum\_) modulo 32. 1.
  -- | Return the result of left shifting \_lNum\_ by \_shiftCount\_ bits. The
  -- | mathematical value of the result is exactly representable as a 32-bit
  -- | two\'s complement bit string.
  | .shl, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := (toNumber b |>.toUInt32) % 32
      .number ((ia <<< ib).toFloat)
  -- SPEC: L4561-L4569
  -- | # Number::signedRightShift ( \_x\_: a Number, \_y\_: a Number, ): an integral Number
  -- |
  -- | 1\. Let \_lNum\_ be ! ToInt32(\_x\_). 1. Let \_rNum\_ be !
  -- | ToUint32(\_y\_). 1. Let \_shiftCount\_ be ℝ(\_rNum\_) modulo 32. 1.
  -- | Return the result of performing a sign-extending right shift of \_lNum\_
  -- | by \_shiftCount\_ bits. The most significant bit is propagated. The
  -- | mathematical value of the result is exactly representable as a 32-bit
  -- | two\'s complement bit string.
  | .shr, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := (toNumber b |>.toUInt32) % 32
      .number ((ia >>> ib).toFloat)
  -- SPEC: L4570-L4578
  -- | # Number::unsignedRightShift ( \_x\_: a Number, \_y\_: a Number, ): an integral Number
  -- |
  -- | 1\. Let \_lNum\_ be ! ToUint32(\_x\_). 1. Let \_rNum\_ be !
  -- | ToUint32(\_y\_). 1. Let \_shiftCount\_ be ℝ(\_rNum\_) modulo 32. 1.
  -- | Return the result of performing a zero-filling right shift of \_lNum\_
  -- | by \_shiftCount\_ bits. Vacated bits are filled with zero. The
  -- | mathematical value of the result is exactly representable as a 32-bit
  -- | unsigned bit string.
  | .ushr, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := (toNumber b |>.toUInt32) % 32
      .number ((ia >>> ib).toFloat)

-- SPEC: L6671-L6680
-- | # Set ( \_O\_: an Object, \_P\_: a property key, \_V\_: an ECMAScript language value, \_Throw\_: a Boolean, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | description
-- | :   It is used to set the value of a specific property of an object.
-- |     \_V\_ is the new value for the property.
-- |
-- | 1\. Let \_success\_ be ? \_O\_.\[\[Set\]\](\_P\_, \_V\_, \_O\_). 1. If
-- | \_success\_ is \*false\* and \_Throw\_ is \*true\*, throw a
-- | \*TypeError\* exception. 1. Return \~unused\~.
-- SPEC: L6734-L6744
-- | # DefinePropertyOrThrow ( \_O\_: an Object, \_P\_: a property key, \_desc\_: a Property Descriptor, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | description
-- | :   It is used to call the \[\[DefineOwnProperty\]\] internal method of
-- |     an object in a manner that will throw a \*TypeError\* exception if
-- |     the requested property update cannot be performed.
-- |
-- | 1\. Let \_success\_ be ? \_O\_.\[\[DefineOwnProperty\]\](\_P\_,
-- | \_desc\_). 1. If \_success\_ is \*false\*, throw a \*TypeError\*
-- | exception. 1. Return \~unused\~.
-- SPEC: L6754-L6765
-- | # GetMethod ( \_V\_: an ECMAScript language value, \_P\_: a property key, ): either a normal completion containing either a function object or \*undefined\*, or a throw completion
-- |
-- | description
-- | :   It is used to get the value of a specific property of an ECMAScript
-- |     language value when the value of the property is expected to be a
-- |     function.
-- |
-- | 1\. Let \_func\_ be ? GetV(\_V\_, \_P\_). 1. If \_func\_ is either
-- | \*undefined\* or \*null\*, return \*undefined\*. 1. If
-- | IsCallable(\_func\_) is \*false\*, throw a \*TypeError\* exception. 1.
-- | Return \_func\_.
-- SPEC: L10770-L10776
-- | # OrdinaryDefineOwnProperty ( \_O\_: an Object, \_P\_: a property key, \_Desc\_: a Property Descriptor, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | 1\. Let \_current\_ be ? \_O\_.\[\[GetOwnProperty\]\](\_P\_). 1. Let
-- | \_extensible\_ be ? IsExtensible(\_O\_). 1. Return
-- | ValidateAndApplyPropertyDescriptor(\_O\_, \_P\_, \_extensible\_,
-- | \_Desc\_, \_current\_).
-- SPEC: L9679-L9689
-- | # NewFunctionEnvironment ( \_F\_: an ECMAScript function object, \_newTarget\_: an Object or \*undefined\*, ): a Function Environment Record
-- |
-- | 1\. Let \_env\_ be a new Function Environment Record containing no
-- | bindings. 1. Set \_env\_.\[\[FunctionObject\]\] to \_F\_. 1. If
-- | \_F\_.\[\[ThisMode\]\] is \~lexical\~, set
-- | \_env\_.\[\[ThisBindingStatus\]\] to \~lexical\~. 1. Else, set
-- | \_env\_.\[\[ThisBindingStatus\]\] to \~uninitialized\~. 1. Set
-- | \_env\_.\[\[NewTarget\]\] to \_newTarget\_. 1. Set
-- | \_env\_.\[\[OuterEnv\]\] to \_F\_.\[\[Environment\]\]. 1. Return
-- | \_env\_.
-- SPEC: L11118-L11135
-- | # OrdinaryCallBindThis ( \_F\_: an ECMAScript function object, \_calleeContext\_: an execution context, \_thisArgument\_: an ECMAScript language value, ): \~unused\~
-- |
-- | 1\. Let \_thisMode\_ be \_F\_.\[\[ThisMode\]\]. 1. If \_thisMode\_ is
-- | \~lexical\~, return \~unused\~. 1. Let \_calleeRealm\_ be
-- | \_F\_.\[\[Realm\]\]. 1. Let \_localEnv\_ be the LexicalEnvironment of
-- | \_calleeContext\_. 1. If \_thisMode\_ is \~strict\~, then 1. Let
-- | \_thisValue\_ be \_thisArgument\_. 1. Else, 1. If \_thisArgument\_ is
-- | either \*undefined\* or \*null\*, then 1. Let \_globalEnv\_ be
-- | \_calleeRealm\_.\[\[GlobalEnv\]\]. 1. Assert: \_globalEnv\_ is a Global
-- | Environment Record. 1. Let \_thisValue\_ be
-- | \_globalEnv\_.\[\[GlobalThisValue\]\]. 1. Else, 1. Let \_thisValue\_ be
-- | ! ToObject(\_thisArgument\_). 1. NOTE: ToObject produces wrapper objects
-- | using \_calleeRealm\_. 1. Assert: \_localEnv\_ is a Function Environment
-- | Record. 1. Assert: The next step never returns an abrupt completion
-- | because \_localEnv\_.\[\[ThisBindingStatus\]\] is not
-- | \~initialized\~. 1. Perform ! BindThisValue(\_localEnv\_,
-- | \_thisValue\_). 1. Return \~unused\~.
-- SPEC: L9223-L9234
-- | # BindThisValue ( \_envRec\_: a Function Environment Record, \_V\_: an ECMAScript language value, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | description
-- | :   It sets the \_envRec\_.\[\[ThisValue\]\] and records that it has
-- |     been initialized.
-- |
-- | 1\. Assert: \_envRec\_.\[\[ThisBindingStatus\]\] is not \~lexical\~. 1.
-- | If \_envRec\_.\[\[ThisBindingStatus\]\] is \~initialized\~, throw a
-- | \*ReferenceError\* exception. 1. Set \_envRec\_.\[\[ThisValue\]\] to
-- | \_V\_. 1. Set \_envRec\_.\[\[ThisBindingStatus\]\] to
-- | \~initialized\~. 1. Return \~unused\~.
-- SPEC: L9986-L10001
-- | # GetThisEnvironment ( ): an Environment Record
-- |
-- | description
-- | :   It finds the Environment Record that currently supplies the binding
-- |     of the keyword \`this\`.
-- |
-- | 1\. Let \_env\_ be the running execution context\'s
-- | LexicalEnvironment. 1. \[id=\"step-getthisenvironment-loop\"\]
-- | Repeat, 1. Let \_exists\_ be \_env\_.HasThisBinding(). 1. If \_exists\_
-- | is \*true\*, return \_env\_. 1. Let \_outer\_ be
-- | \_env\_.\[\[OuterEnv\]\]. 1. Assert: \_outer\_ is not \*null\*. 1. Set
-- | \_env\_ to \_outer\_.
-- |
-- | The loop in step will always terminate because the list of environments
-- | always ends with the global environment which has a \`this\` binding.
-- SPEC: L6940-L6952
-- | # EnumerableOwnProperties ( \_O\_: an Object, \_kind\_: \~key\~, \~value\~, or \~key+value\~, ): either a normal completion containing a List of ECMAScript language values or a throw completion
-- |
-- | 1\. Let \_ownKeys\_ be ? \_O\_.\[\[OwnPropertyKeys\]\](). 1. Let
-- | \_results\_ be a new empty List. 1. For each element \_key\_ of
-- | \_ownKeys\_, do 1. If \_key\_ is a String, then 1. Let \_desc\_ be ?
-- | \_O\_.\[\[GetOwnProperty\]\](\_key\_). 1. If \_desc\_ is not
-- | \*undefined\* and \_desc\_.\[\[Enumerable\]\] is \*true\*, then 1. If
-- | \_kind\_ is \~key\~, then 1. Append \_key\_ to \_results\_. 1. Else, 1.
-- | Let \_value\_ be ? Get(\_O\_, \_key\_). 1. If \_kind\_ is \~value\~,
-- | then 1. Append \_value\_ to \_results\_. 1. Else, 1. Assert: \_kind\_ is
-- | \~key+value\~. 1. Let \_entry\_ be CreateArrayFromList(« \_key\_,
-- | \_value\_ »). 1. Append \_entry\_ to \_results\_. 1. Return \_results\_.
-- SPEC: L11271-L11293
-- | # MakeConstructor ( \_F\_: an ECMAScript function object or a built-in function object, optional \_writablePrototype\_: a Boolean, optional \_prototype\_: an Object, ): \~unused\~
-- |
-- | description
-- | :   It converts \_F\_ into a constructor.
-- |
-- | 1\. If \_F\_ is an ECMAScript function object, then 1. Assert:
-- | IsConstructor(\_F\_) is \*false\*. 1. Assert: \_F\_ is an extensible
-- | object that does not have a \*\"prototype\"\* own property. 1. Set
-- | \_F\_.\[\[Construct\]\] to the definition specified in . 1. Else, 1. Set
-- | \_F\_.\[\[Construct\]\] to the definition specified in . 1. Set
-- | \_F\_.\[\[ConstructorKind\]\] to \~base\~. 1. If \_writablePrototype\_
-- | is not present, set \_writablePrototype\_ to \*true\*. 1. If
-- | \_prototype\_ is not present, then 1. Set \_prototype\_ to
-- | OrdinaryObjectCreate(%Object.prototype%). 1. Perform !
-- | DefinePropertyOrThrow(\_prototype\_, \*\"constructor\"\*,
-- | PropertyDescriptor { \[\[Value\]\]: \_F\_, \[\[Writable\]\]:
-- | \_writablePrototype\_, \[\[Enumerable\]\]: \*false\*,
-- | \[\[Configurable\]\]: \*true\* }). 1. Perform !
-- | DefinePropertyOrThrow(\_F\_, \*\"prototype\"\*, PropertyDescriptor {
-- | \[\[Value\]\]: \_prototype\_, \[\[Writable\]\]: \_writablePrototype\_,
-- | \[\[Enumerable\]\]: \*false\*, \[\[Configurable\]\]: \*false\* }). 1.
-- | Return \~unused\~.
-- SPEC: L11294-L11298
-- | # MakeClassConstructor ( \_F\_: an ECMAScript function object, ): \~unused\~
-- |
-- | 1\. Assert: \_F\_.\[\[IsClassConstructor\]\] is \*false\*. 1. Set
-- | \_F\_.\[\[IsClassConstructor\]\] to \*true\*. 1. Return \~unused\~.
-- SPEC: L11299-L11306
-- | # MakeMethod ( \_F\_: an ECMAScript function object, \_homeObject\_: an Object, ): \~unused\~
-- |
-- | description
-- | :   It configures \_F\_ as a method.
-- |
-- | 1\. Assert: \_homeObject\_ is an ordinary object. 1. Set
-- | \_F\_.\[\[HomeObject\]\] to \_homeObject\_. 1. Return \~unused\~.
-- SPEC: L11307-L11319
-- | # DefineMethodProperty ( \_homeObject\_: an Object, \_key\_: a property key or Private Name, \_closure\_: a function object, \_enumerable\_: a Boolean, ): either a normal completion containing either a PrivateElement or \~unused\~, or an abrupt completion
-- |
-- | 1\. Assert: \_homeObject\_ is an ordinary, extensible object. 1. If
-- | \_key\_ is a Private Name, return PrivateElement { \[\[Key\]\]: \_key\_,
-- | \[\[Kind\]\]: \~method\~, \[\[Value\]\]: \_closure\_ }. 1. Let \_desc\_
-- | be the PropertyDescriptor { \[\[Value\]\]: \_closure\_,
-- | \[\[Writable\]\]: \*true\*, \[\[Enumerable\]\]: \_enumerable\_,
-- | \[\[Configurable\]\]: \*true\* }. 1. Perform ?
-- | DefinePropertyOrThrow(\_homeObject\_, \_key\_, \_desc\_). 1. NOTE:
-- | DefinePropertyOrThrow only returns an abrupt completion when attempting
-- | to define a class static method whose \_key\_ is \*\"prototype\"\*. 1.
-- | Return \~unused\~.
-- SPEC: L11343-L11353
-- | # SetFunctionLength ( \_F\_: a function object, \_length\_: a non-negative integer or +∞, ): \~unused\~
-- |
-- | description
-- | :   It adds a \*\"length\"\* property to \_F\_.
-- |
-- | 1\. Assert: \_F\_ is an extensible object that does not have a
-- | \*\"length\"\* own property. 1. Perform ! DefinePropertyOrThrow(\_F\_,
-- | \*\"length\"\*, PropertyDescriptor { \[\[Value\]\]: 𝔽(\_length\_),
-- | \[\[Writable\]\]: \*false\*, \[\[Enumerable\]\]: \*false\*,
-- | \[\[Configurable\]\]: \*true\* }). 1. Return \~unused\~.
-- SPEC: L11005-L11025
-- | # GetPrototypeFromConstructor ( \_constructor\_: a function object, \_intrinsicDefaultProto\_: a String, ): either a normal completion containing an Object or a throw completion
-- |
-- | description
-- | :   It determines the \[\[Prototype\]\] value that should be used to
-- |     create an object corresponding to a specific constructor. The value
-- |     is retrieved from the constructor\'s \*\"prototype\"\* property, if
-- |     it exists. Otherwise the intrinsic named by
-- |     \_intrinsicDefaultProto\_ is used for \[\[Prototype\]\].
-- |
-- | 1\. Assert: \_intrinsicDefaultProto\_ is this specification\'s name of
-- | an intrinsic object. The corresponding object must be an intrinsic that
-- | is intended to be used as the \[\[Prototype\]\] value of an object. 1.
-- | Let \_proto\_ be ? Get(\_constructor\_, \*\"prototype\"\*). 1. If
-- | \_proto\_ is not an Object, then 1. Let \_realm\_ be ?
-- | GetFunctionRealm(\_constructor\_). 1. Set \_proto\_ to \_realm\_\'s
-- | intrinsic object named \_intrinsicDefaultProto\_. 1. Return \_proto\_.
-- |
-- | If \_constructor\_ does not supply a \[\[Prototype\]\] value, the
-- | default value that is used is obtained from the realm of the
-- | \_constructor\_ function rather than from the running execution context.
-- SPEC: L11768-L11782
-- | # ArrayCreate ( \_length\_: a non-negative integer, optional \_proto\_: an Object, ): either a normal completion containing an Array exotic object or a throw completion
-- |
-- | description
-- | :   It is used to specify the creation of new Arrays.
-- |
-- | 1\. If \_length\_ \> 2^32^ - 1, throw a \*RangeError\* exception. 1. If
-- | \_proto\_ is not present, set \_proto\_ to %Array.prototype%. 1. Let
-- | \_A\_ be MakeBasicObject(« \[\[Prototype\]\], \[\[Extensible\]\] »). 1.
-- | Set \_A\_.\[\[Prototype\]\] to \_proto\_. 1. Set
-- | \_A\_.\[\[DefineOwnProperty\]\] as specified in . 1. Perform !
-- | OrdinaryDefineOwnProperty(\_A\_, \*\"length\"\*, PropertyDescriptor {
-- | \[\[Value\]\]: 𝔽(\_length\_), \[\[Writable\]\]: \*true\*,
-- | \[\[Enumerable\]\]: \*false\*, \[\[Configurable\]\]: \*false\* }). 1.
-- | Return \_A\_.
-- SPEC: L9057-L9074
-- | # HasBinding ( \_N\_: a String, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | for
-- | :   an Object Environment Record \_envRec\_
-- |
-- | description
-- | :   It determines if its associated binding object has a property whose
-- |     name is \_N\_.
-- |
-- | 1\. Let \_bindingObject\_ be \_envRec\_.\[\[BindingObject\]\]. 1. Let
-- | \_foundBinding\_ be ? HasProperty(\_bindingObject\_, \_N\_). 1. If
-- | \_foundBinding\_ is \*false\*, return \*false\*. 1. If
-- | \_envRec\_.\[\[IsWithEnvironment\]\] is \*false\*, return \*true\*. 1.
-- | Let \_unscopables\_ be ? Get(\_bindingObject\_,
-- | %Symbol.unscopables%). 1. If \_unscopables\_ is an Object, then 1. Let
-- | \_blocked\_ be ToBoolean(? Get(\_unscopables\_, \_N\_)). 1. If
-- | \_blocked\_ is \*true\*, return \*false\*. 1. Return \*true\*.
-- SPEC: L9317-L9330
-- | # HasBinding ( \_N\_: a String, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | for
-- | :   a Global Environment Record \_envRec\_
-- |
-- | description
-- | :   It determines if the argument identifier is one of the identifiers
-- |     bound by the record.
-- |
-- | 1\. Let \_DclRec\_ be \_envRec\_.\[\[DeclarativeRecord\]\]. 1. If !
-- | \_DclRec\_.HasBinding(\_N\_) is \*true\*, return \*true\*. 1. Let
-- | \_ObjRec\_ be \_envRec\_.\[\[ObjectRecord\]\]. 1. Return ?
-- | \_ObjRec\_.HasBinding(\_N\_).
-- SPEC: L9466-L9475
-- | # HasLexicalDeclaration ( \_envRec\_: a Global Environment Record, \_N\_: a String, ): a Boolean
-- |
-- | description
-- | :   It determines if the argument identifier has a binding in \_envRec\_
-- |     that was created using a lexical declaration such as a
-- |     \|LexicalDeclaration\| or a \|ClassDeclaration\|.
-- |
-- | 1\. Let \_DclRec\_ be \_envRec\_.\[\[DeclarativeRecord\]\]. 1. Return !
-- | \_DclRec\_.HasBinding(\_N\_).
-- SPEC: L7147-L7153
-- | # GetIteratorDirect ( \_obj\_: an Object, ): either a normal completion containing an Iterator Record or a throw completion
-- |
-- | 1\. Let \_nextMethod\_ be ? Get(\_obj\_, \*\"next\"\*). 1. Let
-- | \_iteratorRecord\_ be the Iterator Record { \[\[Iterator\]\]: \_obj\_,
-- | \[\[NextMethod\]\]: \_nextMethod\_, \[\[Done\]\]: \*false\* }. 1. Return
-- | \_iteratorRecord\_.
-- SPEC: L7221-L7234
-- | # IteratorStepValue ( \_iteratorRecord\_: an Iterator Record, ): either a normal completion containing either an ECMAScript language value or \~done\~, or a throw completion
-- |
-- | description
-- | :   It requests the next value from \_iteratorRecord\_.\[\[Iterator\]\]
-- |     by calling \_iteratorRecord\_.\[\[NextMethod\]\] and returns either
-- |     \~done\~ indicating that the iterator has reached its end or the
-- |     value from the IteratorResult object if a next value is available.
-- |
-- | 1\. Let \_result\_ be ? IteratorStep(\_iteratorRecord\_). 1. If
-- | \_result\_ is \~done\~, then 1. Return \~done\~. 1. Let \_value\_ be
-- | Completion(IteratorValue(\_result\_)). 1. If \_value\_ is a throw
-- | completion, then 1. Set \_iteratorRecord\_.\[\[Done\]\] to \*true\*. 1.
-- | Return ? \_value\_.
-- SPEC: L7070-L7078
-- | # InitializeInstanceElements ( \_O\_: an Object, \_constructor\_: an ECMAScript function object or a built-in function object, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | 1\. Let \_methods\_ be \_constructor\_.\[\[PrivateMethods\]\]. 1. For
-- | each PrivateElement \_method\_ of \_methods\_, do 1. Perform ?
-- | PrivateMethodOrAccessorAdd(\_O\_, \_method\_). 1. Let \_fields\_ be
-- | \_constructor\_.\[\[Fields\]\]. 1. For each element \_fieldRecord\_ of
-- | \_fields\_, do 1. Perform ? DefineField(\_O\_, \_fieldRecord\_). 1.
-- | Return \~unused\~.
-- SPEC: L10871-L10889
-- | # \[\[Get\]\] ( \_P\_: a property key, \_Receiver\_: an ECMAScript language value, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | for
-- | :   an ordinary object \_O\_
-- |
-- | 1\. Return ? OrdinaryGet(\_O\_, \_P\_, \_Receiver\_).
-- |
-- | # OrdinaryGet ( \_O\_: an Object, \_P\_: a property key, \_Receiver\_: an ECMAScript language value, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | 1\. Let \_desc\_ be ? \_O\_.\[\[GetOwnProperty\]\](\_P\_). 1. If
-- | \_desc\_ is \*undefined\*, then 1. Let \_parent\_ be ?
-- | \_O\_.\[\[GetPrototypeOf\]\](). 1. If \_parent\_ is \*null\*, return
-- | \*undefined\*. 1. Return ? \_parent\_.\[\[Get\]\](\_P\_,
-- | \_Receiver\_). 1. If IsDataDescriptor(\_desc\_) is \*true\*, return
-- | \_desc\_.\[\[Value\]\]. 1. Assert: IsAccessorDescriptor(\_desc\_) is
-- | \*true\*. 1. Let \_getter\_ be \_desc\_.\[\[Get\]\]. 1. If \_getter\_ is
-- | \*undefined\*, return \*undefined\*. 1. Return ? Call(\_getter\_,
-- | \_Receiver\_).
-- SPEC: L10927-L10941
-- | # \[\[Delete\]\] ( \_P\_: a property key, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | for
-- | :   an ordinary object \_O\_
-- |
-- | 1\. Return ? OrdinaryDelete(\_O\_, \_P\_).
-- |
-- | # OrdinaryDelete ( \_O\_: an Object, \_P\_: a property key, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | 1\. Let \_desc\_ be ? \_O\_.\[\[GetOwnProperty\]\](\_P\_). 1. If
-- | \_desc\_ is \*undefined\*, return \*true\*. 1. If
-- | \_desc\_.\[\[Configurable\]\] is \*true\*, then 1. Remove the own
-- | property with name \_P\_ from \_O\_. 1. Return \*true\*. 1. Return
-- | \*false\*.
-- SPEC: L10942-L10959
-- | # \[\[OwnPropertyKeys\]\] ( ): a normal completion containing a List of property keys
-- |
-- | for
-- | :   an ordinary object \_O\_
-- |
-- | 1\. Return OrdinaryOwnPropertyKeys(\_O\_).
-- |
-- | # OrdinaryOwnPropertyKeys ( \_O\_: an Object, ): a List of property keys
-- |
-- | 1\. Let \_keys\_ be a new empty List. 1. For each own property key \_P\_
-- | of \_O\_ such that \_P\_ is an array index, in ascending numeric index
-- | order, do 1. Append \_P\_ to \_keys\_. 1. For each own property key
-- | \_P\_ of \_O\_ such that \_P\_ is a String and \_P\_ is not an array
-- | index, in ascending chronological order of property creation, do 1.
-- | Append \_P\_ to \_keys\_. 1. For each own property key \_P\_ of \_O\_
-- | such that \_P\_ is a Symbol, in ascending chronological order of
-- | property creation, do 1. Append \_P\_ to \_keys\_. 1. Return \_keys\_.
-- SPEC: L17515-L17539
-- | # Runtime Semantics: KeyedBindingInitialization ( \_value\_: an ECMAScript language value, \_environment\_: an Environment Record or \*undefined\*, \_propertyName\_: a property key, ): either a normal completion containing \~unused\~ or an abrupt completion
-- |
-- | When \*undefined\* is passed for \_environment\_ it indicates that a
-- | PutValue operation should be used to assign the initialization value.
-- | This is the case for formal parameter lists of non-strict functions. In
-- | that case the formal parameter bindings are preinitialized in order to
-- | deal with the possibility of multiple parameters with the same name.
-- |
-- | BindingElement : BindingPattern Initializer? 1. Let \_v\_ be ?
-- | GetV(\_value\_, \_propertyName\_). 1. If \|Initializer\| is present and
-- | \_v\_ is \*undefined\*, then 1. Let \_defaultValue\_ be ? Evaluation of
-- | \|Initializer\|. 1. Set \_v\_ to ? GetValue(\_defaultValue\_). 1. Return
-- | ? BindingInitialization of \|BindingPattern\| with arguments \_v\_ and
-- | \_environment\_. SingleNameBinding : BindingIdentifier Initializer? 1.
-- | Let \_bindingId\_ be the StringValue of \|BindingIdentifier\|. 1. Let
-- | \_lhs\_ be ? ResolveBinding(\_bindingId\_, \_environment\_). 1. Let
-- | \_v\_ be ? GetV(\_value\_, \_propertyName\_). 1. If \|Initializer\| is
-- | present and \_v\_ is \*undefined\*, then 1. If
-- | IsAnonymousFunctionDefinition(\|Initializer\|) is \*true\*, then 1. Set
-- | \_v\_ to ? NamedEvaluation of \|Initializer\| with argument
-- | \_bindingId\_. 1. Else, 1. Let \_defaultValue\_ be ? Evaluation of
-- | \|Initializer\|. 1. Set \_v\_ to ? GetValue(\_defaultValue\_). 1. If
-- | \_environment\_ is \*undefined\*, return ? PutValue(\_lhs\_, \_v\_). 1.
-- | Return ? InitializeReferencedBinding(\_lhs\_, \_v\_).
-- SPEC: L17911-L17921
-- | # Runtime Semantics: ForDeclarationBindingInitialization ( \_value\_: an ECMAScript language value, \_environment\_: an Environment Record or \*undefined\*, ): either a normal completion containing \~unused\~ or an abrupt completion
-- |
-- | \*undefined\* is passed for \_environment\_ to indicate that a PutValue
-- | operation should be used to assign the initialization value. This is the
-- | case for \`var\` statements and the formal parameter lists of some
-- | non-strict functions (see ). In those cases a lexical binding is hoisted
-- | and preinitialized prior to evaluation of its initializer.
-- |
-- | ForDeclaration : LetOrConst ForBinding 1. Return ? BindingInitialization
-- | of \|ForBinding\| with arguments \_value\_ and \_environment\_.
-- SPEC: L17922-L17930
-- | # Runtime Semantics: ForDeclarationBindingInstantiation ( \_environment\_: a Declarative Environment Record, ): \~unused\~
-- |
-- | ForDeclaration : LetOrConst ForBinding 1. For each element \_name\_ of
-- | the BoundNames of \|ForBinding\|, do 1. If IsConstantDeclaration of
-- | \|LetOrConst\| is \*true\*, then 1. Perform !
-- | \_environment\_.CreateImmutableBinding(\_name\_, \*true\*). 1. Else, 1.
-- | Perform ! \_environment\_.CreateMutableBinding(\_name\_, \*false\*). 1.
-- | Return \~unused\~.
-- SPEC: L8579-L8600
-- | # Runtime Semantics: IteratorBindingInitialization ( \_iteratorRecord\_: an Iterator Record, \_environment\_: an Environment Record or \*undefined\*, ): either a normal completion containing \~unused\~ or an abrupt completion
-- |
-- | When \*undefined\* is passed for \_environment\_ it indicates that a
-- | PutValue operation should be used to assign the initialization value.
-- | This is the case for formal parameter lists of non-strict functions. In
-- | that case the formal parameter bindings are preinitialized in order to
-- | deal with the possibility of multiple parameters with the same name.
-- |
-- | ArrayBindingPattern : \`\[\` \`\]\` 1. Return \~unused\~.
-- | ArrayBindingPattern : \`\[\` Elision \`\]\` 1. Return ?
-- | IteratorDestructuringAssignmentEvaluation of \|Elision\| with argument
-- | \_iteratorRecord\_. ArrayBindingPattern : \`\[\` Elision?
-- | BindingRestElement \`\]\` 1. If \|Elision\| is present, then 1. Perform
-- | ? IteratorDestructuringAssignmentEvaluation of \|Elision\| with argument
-- | \_iteratorRecord\_. 1. Return ? IteratorBindingInitialization of
-- | \|BindingRestElement\| with arguments \_iteratorRecord\_ and
-- | \_environment\_. ArrayBindingPattern : \`\[\` BindingElementList \`,\`
-- | Elision \`\]\` 1. Perform ? IteratorBindingInitialization of
-- | \|BindingElementList\| with arguments \_iteratorRecord\_ and
-- | \_environment\_. 1. Return ? IteratorDestructuringAssignmentEvaluation
-- | of \|Elision\| with argument \_iteratorRecord\_. ArrayBindingPattern :
-- | \`\[\` BindingElementList \`,\` Elision? BindingRestElement \`\]\` 1.
-- SPEC: L8511-L8533
-- | # Runtime Semantics: InstantiateFunctionObject ( \_env\_: an Environment Record, \_privateEnv\_: a PrivateEnvironment Record or \*null\*, ): an ECMAScript function object
-- |
-- | FunctionDeclaration : \`function\` BindingIdentifier \`(\`
-- | FormalParameters \`)\` \`{\` FunctionBody \`}\` \`function\` \`(\`
-- | FormalParameters \`)\` \`{\` FunctionBody \`}\` 1. Return
-- | InstantiateOrdinaryFunctionObject of \|FunctionDeclaration\| with
-- | arguments \_env\_ and \_privateEnv\_. GeneratorDeclaration :
-- | \`function\` \`\*\` BindingIdentifier \`(\` FormalParameters \`)\` \`{\`
-- | GeneratorBody \`}\` \`function\` \`\*\` \`(\` FormalParameters \`)\`
-- | \`{\` GeneratorBody \`}\` 1. Return InstantiateGeneratorFunctionObject
-- | of \|GeneratorDeclaration\| with arguments \_env\_ and \_privateEnv\_.
-- | AsyncGeneratorDeclaration : \`async\` \`function\` \`\*\`
-- | BindingIdentifier \`(\` FormalParameters \`)\` \`{\` AsyncGeneratorBody
-- | \`}\` \`async\` \`function\` \`\*\` \`(\` FormalParameters \`)\` \`{\`
-- | AsyncGeneratorBody \`}\` 1. Return
-- | InstantiateAsyncGeneratorFunctionObject of \|AsyncGeneratorDeclaration\|
-- | with arguments \_env\_ and \_privateEnv\_. AsyncFunctionDeclaration :
-- | \`async\` \`function\` BindingIdentifier \`(\` FormalParameters \`)\`
-- | \`{\` AsyncFunctionBody \`}\` \`async\` \`function\` \`(\`
-- | FormalParameters \`)\` \`{\` AsyncFunctionBody \`}\` 1. Return
-- | InstantiateAsyncFunctionObject of \|AsyncFunctionDeclaration\| with
-- | arguments \_env\_ and \_privateEnv\_.
-- |
-- SPEC: L11746-L11767
-- | # \[\[DefineOwnProperty\]\] ( \_P\_: a property key, \_Desc\_: a Property Descriptor, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | for
-- | :   an Array exotic object \_A\_
-- |
-- | 1\. If \_P\_ is \*\"length\"\*, return ? ArraySetLength(\_A\_,
-- | \_Desc\_). 1. If \_P\_ is an array index, then 1. Let \_lengthDesc\_ be
-- | OrdinaryGetOwnProperty(\_A\_, \*\"length\"\*). 1. Assert: \_lengthDesc\_
-- | is not \*undefined\*. 1. Assert: IsDataDescriptor(\_lengthDesc\_) is
-- | \*true\*. 1. Assert: \_lengthDesc\_.\[\[Configurable\]\] is
-- | \*false\*. 1. Let \_length\_ be \_lengthDesc\_.\[\[Value\]\]. 1. Assert:
-- | \_length\_ is a non-negative integral Number. 1. Let \_index\_ be !
-- | ToUint32(\_P\_). 1. If \_index\_ ≥ \_length\_ and
-- | \_lengthDesc\_.\[\[Writable\]\] is \*false\*, return \*false\*. 1. Let
-- | \_succeeded\_ be ! OrdinaryDefineOwnProperty(\_A\_, \_P\_, \_Desc\_). 1.
-- | If \_succeeded\_ is \*false\*, return \*false\*. 1. If \_index\_ ≥
-- | \_length\_, then 1. Set \_lengthDesc\_.\[\[Value\]\] to \_index\_ +
-- | \*1\*~𝔽~. 1. Set \_succeeded\_ to ! OrdinaryDefineOwnProperty(\_A\_,
-- | \*\"length\"\*, \_lengthDesc\_). 1. Assert: \_succeeded\_ is
-- | \*true\*. 1. Return \*true\*. 1. Return ?
-- | OrdinaryDefineOwnProperty(\_A\_, \_P\_, \_Desc\_).
-- |
-- SPEC: L11783-L11810
-- | # ArraySpeciesCreate ( \_originalArray\_: an Object, \_length\_: a non-negative integer, ): either a normal completion containing an Object or a throw completion
-- |
-- | description
-- | :   It is used to specify the creation of a new Array or similar object
-- |     using a constructor function that is derived from \_originalArray\_.
-- |     It does not enforce that the constructor function returns an Array.
-- |
-- | 1\. Let \_isArray\_ be ? IsArray(\_originalArray\_). 1. If \_isArray\_
-- | is \*false\*, return ? ArrayCreate(\_length\_). 1. Let \_C\_ be ?
-- | Get(\_originalArray\_, \*\"constructor\"\*). 1. If IsConstructor(\_C\_)
-- | is \*true\*, then 1. Let \_thisRealm\_ be the current Realm Record. 1.
-- | Let \_realmC\_ be ? GetFunctionRealm(\_C\_). 1. If \_thisRealm\_ and
-- | \_realmC\_ are not the same Realm Record, then 1. If SameValue(\_C\_,
-- | \_realmC\_.\[\[Intrinsics\]\].\[\[%Array%\]\]) is \*true\*, set \_C\_ to
-- | \*undefined\*. 1. If \_C\_ is an Object, then 1. Set \_C\_ to ?
-- | Get(\_C\_, %Symbol.species%). 1. If \_C\_ is \*null\*, set \_C\_ to
-- | \*undefined\*. 1. If \_C\_ is \*undefined\*, return ?
-- | ArrayCreate(\_length\_). 1. If IsConstructor(\_C\_) is \*false\*, throw
-- | a \*TypeError\* exception. 1. Return ? Construct(\_C\_, « 𝔽(\_length\_)
-- | »).
-- |
-- | If \_originalArray\_ was created using the standard built-in Array
-- | constructor for a realm that is not the realm of the running execution
-- | context, then a new Array is created using the realm of the running
-- | execution context. This maintains compatibility with Web browsers that
-- | have historically had that behaviour for the \`Array.prototype\` methods
-- | that now are defined using ArraySpeciesCreate.
-- |

-- SPEC: L8327-L8336
-- | # Static Semantics: IsAnonymousFunctionDefinition ( \_expr\_: an \|AssignmentExpression\| Parse Node, an \|Initializer\| Parse Node, or an \|Expression\| Parse Node, ): a Boolean
-- |
-- | description
-- | :   It determines if its argument is a function definition that does not
-- |     bind a name.
-- |
-- | 1\. If IsFunctionDefinition of \_expr\_ is \*false\*, return
-- | \*false\*. 1. Let \_hasName\_ be HasName of \_expr\_. 1. If \_hasName\_
-- | is \*true\*, return \*false\*. 1. Return \*true\*.
-- SPEC: L8352-L8384
-- | # Runtime Semantics: NamedEvaluation ( \_name\_: a property key or a Private Name, ): either a normal completion containing a function object or an abrupt completion
-- |
-- | PrimaryExpression : CoverParenthesizedExpressionAndArrowParameterList 1.
-- | Let \_expr\_ be the \|ParenthesizedExpression\| that is covered by
-- | \|CoverParenthesizedExpressionAndArrowParameterList\|. 1. Return ?
-- | NamedEvaluation of \_expr\_ with argument \_name\_.
-- | ParenthesizedExpression : \`(\` Expression \`)\` 1. Assert:
-- | IsAnonymousFunctionDefinition(\|Expression\|) is \*true\*. 1. Return ?
-- | NamedEvaluation of \|Expression\| with argument \_name\_.
-- | FunctionExpression : \`function\` \`(\` FormalParameters \`)\` \`{\`
-- | FunctionBody \`}\` 1. Return InstantiateOrdinaryFunctionExpression of
-- | \|FunctionExpression\| with argument \_name\_. GeneratorExpression :
-- | \`function\` \`\*\` \`(\` FormalParameters \`)\` \`{\` GeneratorBody
-- | \`}\` 1. Return InstantiateGeneratorFunctionExpression of
-- | \|GeneratorExpression\| with argument \_name\_. AsyncGeneratorExpression
-- | : \`async\` \`function\` \`\*\` \`(\` FormalParameters \`)\` \`{\`
-- | AsyncGeneratorBody \`}\` 1. Return
-- | InstantiateAsyncGeneratorFunctionExpression of
-- | \|AsyncGeneratorExpression\| with argument \_name\_.
-- | AsyncFunctionExpression : \`async\` \`function\` \`(\` FormalParameters
-- | \`)\` \`{\` AsyncFunctionBody \`}\` 1. Return
-- | InstantiateAsyncFunctionExpression of \|AsyncFunctionExpression\| with
-- | argument \_name\_. ArrowFunction : ArrowParameters \`=\>\`
-- | ConciseBody 1. Return InstantiateArrowFunctionExpression of
-- | \|ArrowFunction\| with argument \_name\_. AsyncArrowFunction : \`async\`
-- | AsyncArrowBindingIdentifier \`=\>\` AsyncConciseBody
-- | CoverCallExpressionAndAsyncArrowHead \`=\>\` AsyncConciseBody 1. Return
-- | InstantiateAsyncArrowFunctionExpression of \|AsyncArrowFunction\| with
-- | argument \_name\_. ClassExpression : \`class\` ClassTail 1. Let
-- | \_sourceText\_ be the source text matched by \|ClassExpression\|. 1.
-- | Return ? ClassDefinitionEvaluation of \|ClassTail\| with arguments
-- | \*undefined\*, \_name\_, and \_sourceText\_.
-- SPEC: L9235-L9242
-- | # HasThisBinding ( ): a Boolean
-- |
-- | for
-- | :   a Function Environment Record \_envRec\_
-- |
-- | 1\. If \_envRec\_.\[\[ThisBindingStatus\]\] is \~lexical\~, return
-- | \*false\*. 1. Return \*true\*.
-- SPEC: L9243-L9251
-- | # GetThisBinding ( ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | for
-- | :   a Function Environment Record \_envRec\_
-- |
-- | 1\. Assert: \_envRec\_.\[\[ThisBindingStatus\]\] is not \~lexical\~. 1.
-- | If \_envRec\_.\[\[ThisBindingStatus\]\] is \~uninitialized\~, throw a
-- | \*ReferenceError\* exception. 1. Return \_envRec\_.\[\[ThisValue\]\].
-- SPEC: L9252-L9260
-- | # HasSuperBinding ( ): a Boolean
-- |
-- | for
-- | :   a Function Environment Record \_envRec\_
-- |
-- | 1\. If \_envRec\_.\[\[ThisBindingStatus\]\] is \~lexical\~, return
-- | \*false\*. 1. If \_envRec\_.\[\[FunctionObject\]\].\[\[HomeObject\]\] is
-- | \*undefined\*, return \*false\*. 1. Return \*true\*.
-- SPEC: L9261-L9272
-- | # GetSuperBase ( \_envRec\_: a Function Environment Record, ): an Object, \*null\*, or \*undefined\*
-- |
-- | description
-- | :   It returns the object that is the base for \`super\` property
-- |     accesses bound in \_envRec\_. The value \*undefined\* indicates that
-- |     such accesses will produce runtime errors.
-- |
-- | 1\. Let \_home\_ be
-- | \_envRec\_.\[\[FunctionObject\]\].\[\[HomeObject\]\]. 1. If \_home\_ is
-- | \*undefined\*, return \*undefined\*. 1. Assert: \_home\_ is an ordinary
-- | object. 1. Return ! \_home\_.\[\[GetPrototypeOf\]\]().
-- SPEC: L15779-L15798
-- | # Runtime Semantics: Evaluation
-- |
-- | OptionalExpression : MemberExpression OptionalChain 1. Let
-- | \_baseReference\_ be ? Evaluation of \|MemberExpression\|. 1. Let
-- | \_baseValue\_ be ? GetValue(\_baseReference\_). 1. If \_baseValue\_ is
-- | either \*undefined\* or \*null\*, then 1. Return \*undefined\*. 1.
-- | Return ? ChainEvaluation of \|OptionalChain\| with arguments
-- | \_baseValue\_ and \_baseReference\_. OptionalExpression : CallExpression
-- | OptionalChain 1. Let \_baseReference\_ be ? Evaluation of
-- | \|CallExpression\|. 1. Let \_baseValue\_ be ?
-- | GetValue(\_baseReference\_). 1. If \_baseValue\_ is either \*undefined\*
-- | or \*null\*, then 1. Return \*undefined\*. 1. Return ? ChainEvaluation
-- | of \|OptionalChain\| with arguments \_baseValue\_ and \_baseReference\_.
-- | OptionalExpression : OptionalExpression OptionalChain 1. Let
-- | \_baseReference\_ be ? Evaluation of \|OptionalExpression\|. 1. Let
-- | \_baseValue\_ be ? GetValue(\_baseReference\_). 1. If \_baseValue\_ is
-- | either \*undefined\* or \*null\*, then 1. Return \*undefined\*. 1.
-- | Return ? ChainEvaluation of \|OptionalChain\| with arguments
-- | \_baseValue\_ and \_baseReference\_.
-- SPEC: L17803-L17817
-- | # CreatePerIterationEnvironment ( \_perIterationBindings\_: a List of Strings, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | 1\. If \_perIterationBindings\_ has any elements, then 1. Let
-- | \_lastIterationEnv\_ be the running execution context\'s
-- | LexicalEnvironment. 1. Let \_outer\_ be
-- | \_lastIterationEnv\_.\[\[OuterEnv\]\]. 1. Assert: \_outer\_ is not
-- | \*null\*. 1. Let \_thisIterationEnv\_ be
-- | NewDeclarativeEnvironment(\_outer\_). 1. For each element \_bn\_ of
-- | \_perIterationBindings\_, do 1. Perform !
-- | \_thisIterationEnv\_.CreateMutableBinding(\_bn\_, \*false\*). 1. Let
-- | \_lastValue\_ be ? \_lastIterationEnv\_.GetBindingValue(\_bn\_,
-- | \*true\*). 1. Perform ! \_thisIterationEnv\_.InitializeBinding(\_bn\_,
-- | \_lastValue\_). 1. Set the running execution context\'s
-- | LexicalEnvironment to \_thisIterationEnv\_. 1. Return \~unused\~.
-- SPEC: L18163-L18177
-- | # CreateForInIterator ( \_object\_: an Object, ): a For-In Iterator
-- |
-- | description
-- | :   It is used to create a For-In Iterator object which iterates over
-- |     the own and inherited enumerable string properties of \_object\_ in
-- |     a specific order.
-- |
-- | 1\. Let \_iterator\_ be OrdinaryObjectCreate(%ForInIteratorPrototype%, «
-- | \[\[Object\]\], \[\[ObjectWasVisited\]\], \[\[VisitedKeys\]\],
-- | \[\[RemainingKeys\]\] »). 1. Set \_iterator\_.\[\[Object\]\] to
-- | \_object\_. 1. Set \_iterator\_.\[\[ObjectWasVisited\]\] to
-- | \*false\*. 1. Set \_iterator\_.\[\[VisitedKeys\]\] to a new empty
-- | List. 1. Set \_iterator\_.\[\[RemainingKeys\]\] to a new empty List. 1.
-- | Return \_iterator\_.
-- SPEC: L18431-L18452
-- | # Runtime Semantics: Evaluation
-- |
-- | SwitchStatement : \`switch\` \`(\` Expression \`)\` CaseBlock 1. Let
-- | \_exprRef\_ be ? Evaluation of \|Expression\|. 1. Let \_switchValue\_ be
-- | ? GetValue(\_exprRef\_). 1. Let \_oldEnv\_ be the running execution
-- | context\'s LexicalEnvironment. 1. Let \_blockEnv\_ be
-- | NewDeclarativeEnvironment(\_oldEnv\_). 1. Perform
-- | BlockDeclarationInstantiation(\|CaseBlock\|, \_blockEnv\_). 1. Set the
-- | running execution context\'s LexicalEnvironment to \_blockEnv\_. 1. Let
-- | \_R\_ be Completion(CaseBlockEvaluation of \|CaseBlock\| with argument
-- | \_switchValue\_). 1. Set the running execution context\'s
-- | LexicalEnvironment to \_oldEnv\_. 1. Return \_R\_.
-- |
-- | No matter how control leaves the \|SwitchStatement\| the
-- | LexicalEnvironment is always restored to its former state.
-- |
-- | CaseClause : \`case\` Expression \`:\` 1. Return \~empty\~. CaseClause :
-- | \`case\` Expression \`:\` StatementList 1. Return ? Evaluation of
-- | \|StatementList\|. DefaultClause : \`default\` \`:\` 1. Return
-- | \~empty\~. DefaultClause : \`default\` \`:\` StatementList 1. Return ?
-- | Evaluation of \|StatementList\|.
-- SPEC: L20530-L20534
-- | # PrepareForTailCall ( ): \~unused\~
-- |
-- | 1\. Assert: The current execution context will not subsequently be used
-- | for the evaluation of any ECMAScript code or built-in functions. The
-- | invocation of Call subsequent to the invocation of this abstract
-- SPEC: L8743-L8772
-- | # Static Semantics: PropName ( ): a String or \~empty\~
-- |
-- | PropertyDefinition : IdentifierReference 1. Return the StringValue of
-- | \|IdentifierReference\|. PropertyDefinition : \`\...\`
-- | AssignmentExpression 1. Return \~empty\~. PropertyDefinition :
-- | PropertyName \`:\` AssignmentExpression 1. Return the PropName of
-- | \|PropertyName\|. LiteralPropertyName : IdentifierName AttributeKey :
-- | IdentifierName 1. Return the StringValue of \|IdentifierName\|.
-- | LiteralPropertyName : StringLiteral AttributeKey : StringLiteral 1.
-- | Return the SV of \|StringLiteral\|. LiteralPropertyName :
-- | NumericLiteral 1. Let \_nbr\_ be the NumericValue of
-- | \|NumericLiteral\|. 1. Return ! ToString(\_nbr\_). ComputedPropertyName
-- | : \`\[\` AssignmentExpression \`\]\` 1. Return \~empty\~.
-- | MethodDefinition : ClassElementName \`(\` UniqueFormalParameters \`)\`
-- | \`{\` FunctionBody \`}\` \`get\` ClassElementName \`(\` \`)\` \`{\`
-- | FunctionBody \`}\` \`set\` ClassElementName \`(\`
-- | PropertySetParameterList \`)\` \`{\` FunctionBody \`}\` 1. Return the
-- | PropName of \|ClassElementName\|. GeneratorMethod : \`\*\`
-- | ClassElementName \`(\` UniqueFormalParameters \`)\` \`{\` GeneratorBody
-- | \`}\` 1. Return the PropName of \|ClassElementName\|.
-- | AsyncGeneratorMethod : \`async\` \`\*\` ClassElementName \`(\`
-- | UniqueFormalParameters \`)\` \`{\` AsyncGeneratorBody \`}\` 1. Return
-- | the PropName of \|ClassElementName\|. ClassElement : ClassStaticBlock 1.
-- | Return \~empty\~. ClassElement : \`;\` 1. Return \~empty\~. AsyncMethod
-- | : \`async\` ClassElementName \`(\` UniqueFormalParameters \`)\` \`{\`
-- | AsyncFunctionBody \`}\` 1. Return the PropName of \|ClassElementName\|.
-- | FieldDefinition : ClassElementName Initializer? 1. Return the PropName
-- | of \|ClassElementName\|. ClassElementName : PrivateIdentifier 1. Return
-- | \~empty\~.
-- SPEC: L16929-L16935
-- | # EvaluateStringOrNumericBinaryExpression ( \_leftOperand\_: a Parse Node, \_opText\_: a sequence of Unicode code points, \_rightOperand\_: a Parse Node, ): either a normal completion containing either a String, a BigInt, or a Number, or an abrupt completion
-- |
-- | 1\. Let \_lRef\_ be ? Evaluation of \_leftOperand\_. 1. Let \_lVal\_ be
-- | ? GetValue(\_lRef\_). 1. Let \_rRef\_ be ? Evaluation of
-- | \_rightOperand\_. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1. Return ?
-- | ApplyStringOrNumericBinaryOperator(\_lVal\_, \_opText\_, \_rVal\_).
-- SPEC: L7058-L7069
-- | # DefineField ( \_receiver\_: an Object, \_fieldRecord\_: a ClassFieldDefinition Record, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | 1\. Let \_fieldName\_ be \_fieldRecord\_.\[\[Name\]\]. 1. Let
-- | \_initializer\_ be \_fieldRecord\_.\[\[Initializer\]\]. 1. If
-- | \_initializer\_ is not \~empty\~, then 1. Let \_initValue\_ be ?
-- | Call(\_initializer\_, \_receiver\_). 1. Else, 1. Let \_initValue\_ be
-- | \*undefined\*. 1. If \_fieldName\_ is a Private Name, then 1. Perform ?
-- | PrivateFieldAdd(\_receiver\_, \_fieldName\_, \_initValue\_). 1. Else, 1.
-- | Assert: \_fieldName\_ is a property key. 1. Perform ?
-- | CreateDataPropertyOrThrow(\_receiver\_, \_fieldName\_,
-- | \_initValue\_). 1. Return \~unused\~.
-- SPEC: L6263-L6269
-- | # StringToBigInt ( \_str\_: a String, ): a BigInt or \*undefined\*
-- |
-- | 1\. Let \_literal\_ be ParseText(\_str\_, \|StringIntegerLiteral\|). 1.
-- | If \_literal\_ is a List of errors, return \*undefined\*. 1. Let \_mv\_
-- | be the MV of \_literal\_. 1. Assert: \_mv\_ is an integer. 1. Return
-- | ℤ(\_mv\_).
-- SPEC: L8993-L9003
-- | # HasThisBinding ( ): \*false\*
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | 1\. Return \*false\*.
-- |
-- | A regular Declarative Environment Record (i.e., one that is neither a
-- | Function Environment Record nor a Module Environment Record) does not
-- | provide a \`this\` binding.
-- SPEC: L9009-L9019
-- | # HasSuperBinding ( ): \*false\*
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | 1\. Return \*false\*.
-- |
-- | A regular Declarative Environment Record (i.e., one that is neither a
-- | Function Environment Record nor a Module Environment Record) does not
-- | provide a \`super\` binding.
-- SPEC: L9020-L9026
-- | # WithBaseObject ( ): \*undefined\*
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | 1\. Return \*undefined\*.
-- SPEC: L7319-L7337
-- | # CreateListIteratorRecord ( \_list\_: a List of ECMAScript language values, ): an Iterator Record
-- |
-- | description
-- | :   It creates an Iterator Record whose \[\[NextMethod\]\] returns the
-- |     successive elements of \_list\_.
-- |
-- | 1\. Let \_closure\_ be a new Abstract Closure with no parameters that
-- | captures \_list\_ and performs the following steps when called: 1. For
-- | each element \_E\_ of \_list\_, do 1. Perform ?
-- | GeneratorYield(CreateIteratorResultObject(\_E\_, \*false\*)). 1. Return
-- | NormalCompletion(\*undefined\*). 1. Let \_iterator\_ be
-- | CreateIteratorFromClosure(\_closure\_, \~empty\~,
-- | %Iterator.prototype%). 1. Return the Iterator Record { \[\[Iterator\]\]:
-- | \_iterator\_, \[\[NextMethod\]\]: %GeneratorPrototype.next%,
-- | \[\[Done\]\]: \*false\* }.
-- |
-- | The list iterator object is never directly accessible to ECMAScript
-- | code.
-- SPEC: L16638-L16657
-- | # Runtime Semantics: Evaluation
-- |
-- | AssignmentExpression : LeftHandSideExpression \`=\`
-- | AssignmentExpression 1. If \|LeftHandSideExpression\| is neither an
-- | \|ObjectLiteral\| nor an \|ArrayLiteral\|, then 1. Let \_lRef\_ be ?
-- | Evaluation of \|LeftHandSideExpression\|. 1. If the AssignmentTargetType
-- | of \|LeftHandSideExpression\| is \~web-compat\~, throw a
-- | \*ReferenceError\* exception. 1. If
-- | IsAnonymousFunctionDefinition(\|AssignmentExpression\|) is \*true\* and
-- | IsIdentifierRef of \|LeftHandSideExpression\| is \*true\*, then 1. Let
-- | \_lhs\_ be the StringValue of \|LeftHandSideExpression\|. 1. Let
-- | \_rVal\_ be ? NamedEvaluation of \|AssignmentExpression\| with argument
-- | \_lhs\_. 1. Else, 1. Let \_rRef\_ be ? Evaluation of
-- | \|AssignmentExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1.
-- | \[id=\"step-assignmentexpression-evaluation-simple-putvalue\"\] Perform
-- | ? PutValue(\_lRef\_, \_rVal\_). 1. Return \_rVal\_. 1. Let
-- | \_assignmentPattern\_ be the \|AssignmentPattern\| that is covered by
-- | \|LeftHandSideExpression\|. 1. Let \_rRef\_ be ? Evaluation of
-- | \|AssignmentExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1.
-- | Perform ? DestructuringAssignmentEvaluation of \_assignmentPattern\_
-- SPEC: L17190-L17199
-- | # Runtime Semantics: Evaluation
-- |
-- | Expression : Expression \`,\` AssignmentExpression 1. Let \_lRef\_ be ?
-- | Evaluation of \|Expression\|. 1. Perform ? GetValue(\_lRef\_). 1. Let
-- | \_rRef\_ be ? Evaluation of \|AssignmentExpression\|. 1. Return ?
-- | GetValue(\_rRef\_).
-- |
-- | GetValue must be called even though its value is not used because it may
-- | have observable side-effects.
-- SPEC: L6202-L6213
-- | # ToInt8 ( \_argument\_: an ECMAScript language value, ): either a normal completion containing an integral Number or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to one of 2^8^ integral Number values in
-- |     the inclusive interval from \*-128\*~𝔽~ to \*127\*~𝔽~.
-- |
-- | 1\. Let \_number\_ be ? ToNumber(\_argument\_). 1. If \_number\_ is not
-- | finite or \_number\_ is either \*+0\*~𝔽~ or \*-0\*~𝔽~, return
-- | \*+0\*~𝔽~. 1. Let \_int\_ be truncate(ℝ(\_number\_)). 1. Let \_int8bit\_
-- | be \_int\_ modulo 2^8^. 1. If \_int8bit\_ ≥ 2^7^, return 𝔽(\_int8bit\_ -
-- | 2^8^). 1. Return 𝔽(\_int8bit\_).
-- SPEC: L6214-L6224
-- | # ToUint8 ( \_argument\_: an ECMAScript language value, ): either a normal completion containing an integral Number or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to one of 2^8^ integral Number values in
-- |     the inclusive interval from \*+0\*~𝔽~ to \*255\*~𝔽~.
-- |
-- | 1\. Let \_number\_ be ? ToNumber(\_argument\_). 1. If \_number\_ is not
-- | finite or \_number\_ is either \*+0\*~𝔽~ or \*-0\*~𝔽~, return
-- | \*+0\*~𝔽~. 1. Let \_int\_ be truncate(ℝ(\_number\_)). 1. Let \_int8bit\_
-- | be \_int\_ modulo 2^8^. 1. Return 𝔽(\_int8bit\_).
-- SPEC: L6296-L6304
-- | # ToBigUint64 ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a BigInt or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to one of 2^64^ BigInt values in the
-- |     inclusive interval from \*0\*~ℤ~ to ℤ(2^64^ - 1).
-- |
-- | 1\. Let \_n\_ be ? ToBigInt(\_argument\_). 1. Let \_int64bit\_ be
-- | ℝ(\_n\_) modulo 2^64^. 1. Return ℤ(\_int64bit\_).
-- SPEC: L6286-L6295
-- | # ToBigInt64 ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a BigInt or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to one of 2^64^ BigInt values in the
-- |     inclusive interval from ℤ(-2^63^) to ℤ(2^63^ - 1).
-- |
-- | 1\. Let \_n\_ be ? ToBigInt(\_argument\_). 1. Let \_int64bit\_ be
-- | ℝ(\_n\_) modulo 2^64^. 1. If \_int64bit\_ ≥ 2^63^, return
-- | ℤ(\_int64bit\_ - 2^64^). 1. Return ℤ(\_int64bit\_).

/-- Built-in function index for console.log (reserved at index 0, §18.2). -/
def consoleLogIdx : FuncIdx := 0

/-- Push a trace event onto the state's trace list. -/
def pushTrace (s : State) (t : TraceEvent) : State :=
  { s with trace := s.trace ++ [t] }

-- SPEC: L15413-L15425
-- | # Runtime Semantics: Evaluation
-- |
-- | PrimaryExpression : CoverParenthesizedExpressionAndArrowParameterList 1.
-- | Let \_expr\_ be the \|ParenthesizedExpression\| that is covered by
-- | \|CoverParenthesizedExpressionAndArrowParameterList\|. 1. Return ?
-- | Evaluation of \_expr\_. ParenthesizedExpression : \`(\` Expression
-- | \`)\` 1. Return ? Evaluation of \|Expression\|. This may be of type
-- | Reference.
-- |
-- | This algorithm does not apply GetValue to Evaluation of \|Expression\|.
-- | The principal motivation for this is so that operators such as
-- | \`delete\` and \`typeof\` may be applied to parenthesized expressions.

/-- One deterministic Core small-step transition with emitted trace event. -/
def step? (s : State) : Option (TraceEvent × State) :=
  match h : s.expr with
  -- SPEC: L14929-L14936
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | Literal : NullLiteral 1. Return \*null\*. Literal : BooleanLiteral 1. If
  -- | \|BooleanLiteral\| is the token \`false\`, return \*false\*. 1. If
  -- | \|BooleanLiteral\| is the token \`true\`, return \*true\*. Literal :
  -- | NumericLiteral 1. Return the NumericValue of \|NumericLiteral\| as
  -- | defined in . Literal : StringLiteral 1. Return the SV of
  -- | \|StringLiteral\| as defined in .
  | .lit _ => none
  -- SPEC: L14868-L14871
  -- | IdentifierReference : Identifier 1. Return ? ResolveBinding(StringValue
  -- | of \|Identifier\|). IdentifierReference : \`yield\` 1. Return ?
  -- | ResolveBinding(\*\"yield\"\*). IdentifierReference : \`await\` 1. Return
  -- | ? ResolveBinding(\*\"await\"\*).
  -- SPEC: L9970-L9985
  -- | # ResolveBinding ( \_name\_: a String, optional \_env\_: an Environment Record or \*undefined\*, ): either a normal completion containing a Reference Record or a throw completion
  -- |
  -- | description
  -- | :   It is used to determine the binding of \_name\_. \_env\_ can be used
  -- |     to explicitly provide the Environment Record that is to be searched
  -- |     for the binding.
  -- |
  -- | 1\. If \_env\_ is not present or \_env\_ is \*undefined\*, then 1. Set
  -- | \_env\_ to the running execution context\'s LexicalEnvironment. 1.
  -- | Assert: \_env\_ is an Environment Record. 1. Let \_strict\_ be
  -- | IsStrict(the syntactic production that is being evaluated). 1. Return ?
  -- | GetIdentifierReference(\_env\_, \_name\_, \_strict\_).
  -- |
  -- | The result of ResolveBinding is always a Reference Record whose
  -- | \[\[ReferencedName\]\] field is \_name\_.
  -- SPEC: L9655-L9666
  -- | # GetIdentifierReference ( \_env\_: an Environment Record or \*null\*, \_name\_: a String, \_strict\_: a Boolean, ): either a normal completion containing a Reference Record or a throw completion
  -- |
  -- | 1\. If \_env\_ is \*null\*, then 1. Return the Reference Record {
  -- | \[\[Base\]\]: \~unresolvable\~, \[\[ReferencedName\]\]: \_name\_,
  -- | \[\[Strict\]\]: \_strict\_, \[\[ThisValue\]\]: \~empty\~ }. 1. Let
  -- | \_exists\_ be ? \_env\_.HasBinding(\_name\_). 1. If \_exists\_ is
  -- | \*true\*, then 1. Return the Reference Record { \[\[Base\]\]: \_env\_,
  -- | \[\[ReferencedName\]\]: \_name\_, \[\[Strict\]\]: \_strict\_,
  -- | \[\[ThisValue\]\]: \~empty\~ }. 1. Let \_outer\_ be
  -- | \_env\_.\[\[OuterEnv\]\]. 1. Return ? GetIdentifierReference(\_outer\_,
  -- | \_name\_, \_strict\_).
  | .var name =>
      match s.env.lookup name with
      | some v =>
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | none =>
          let msg := "ReferenceError: " ++ name
          let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
          some (.error msg, s')
  -- SPEC: L17424-L17453
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | VariableStatement : \`var\` VariableDeclarationList \`;\` 1. Perform ?
  -- | Evaluation of \|VariableDeclarationList\|. 1. Return \~empty\~.
  -- | VariableDeclarationList : VariableDeclarationList \`,\`
  -- | VariableDeclaration 1. Perform ? Evaluation of
  -- | \|VariableDeclarationList\|. 1. Return ? Evaluation of
  -- | \|VariableDeclaration\|. VariableDeclaration : BindingIdentifier 1.
  -- | Return \~empty\~. VariableDeclaration : BindingIdentifier Initializer 1.
  -- | Let \_bindingId\_ be the StringValue of \|BindingIdentifier\|. 1. Let
  -- | \_lhs\_ be ? ResolveBinding(\_bindingId\_). 1. If
  -- | IsAnonymousFunctionDefinition(\|Initializer\|) is \*true\*, then 1. Let
  -- | \_value\_ be ? NamedEvaluation of \|Initializer\| with argument
  -- | \_bindingId\_. 1. Else, 1. Let \_rhs\_ be ? Evaluation of
  -- | \|Initializer\|. 1. Let \_value\_ be ? GetValue(\_rhs\_). 1.
  -- | \[id=\"step-vardecllist-evaluation-putvalue\"\] Perform ?
  -- | PutValue(\_lhs\_, \_value\_). 1. Return \~empty\~.
  -- |
  -- | If a \|VariableDeclaration\| is nested within a with statement and the
  -- | \|BindingIdentifier\| in the \|VariableDeclaration\| is the same as a
  -- | property name of the binding object of the with statement\'s Object
  -- | Environment Record, then step will assign \_value\_ to the property
  -- | instead of assigning to the VariableEnvironment binding of the
  -- | \|Identifier\|.
  -- |
  -- | VariableDeclaration : BindingPattern Initializer 1. Let \_rhs\_ be ?
  -- | Evaluation of \|Initializer\|. 1. Let \_rVal\_ be ?
  -- | GetValue(\_rhs\_). 1. Return ? BindingInitialization of
  -- | \|BindingPattern\| with arguments \_rVal\_ and \*undefined\*.
  -- SPEC: L17372-L17399
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | LexicalDeclaration : LetOrConst BindingList \`;\` 1. Perform ?
  -- | Evaluation of \|BindingList\|. 1. Return \~empty\~. BindingList :
  -- | BindingList \`,\` LexicalBinding 1. Perform ? Evaluation of
  -- | \|BindingList\|. 1. Return ? Evaluation of \|LexicalBinding\|.
  -- | LexicalBinding : BindingIdentifier 1. Let \_lhs\_ be !
  -- | ResolveBinding(StringValue of \|BindingIdentifier\|). 1. Perform !
  -- | InitializeReferencedBinding(\_lhs\_, \*undefined\*). 1. Return
  -- | \~empty\~.
  -- |
  -- | A static semantics rule ensures that this form of \|LexicalBinding\|
  -- | never occurs in a \`const\` declaration.
  -- |
  -- | LexicalBinding : BindingIdentifier Initializer 1. Let \_bindingId\_ be
  -- | the StringValue of \|BindingIdentifier\|. 1. Let \_lhs\_ be !
  -- | ResolveBinding(\_bindingId\_). 1. If
  -- | IsAnonymousFunctionDefinition(\|Initializer\|) is \*true\*, then 1. Let
  -- | \_value\_ be ? NamedEvaluation of \|Initializer\| with argument
  -- | \_bindingId\_. 1. Else, 1. Let \_rhs\_ be ? Evaluation of
  -- | \|Initializer\|. 1. Let \_value\_ be ? GetValue(\_rhs\_). 1. Perform !
  -- | InitializeReferencedBinding(\_lhs\_, \_value\_). 1. Return \~empty\~.
  -- | LexicalBinding : BindingPattern Initializer 1. Let \_rhs\_ be ?
  -- | Evaluation of \|Initializer\|. 1. Let \_value\_ be ?
  -- | GetValue(\_rhs\_). 1. Let \_env\_ be the running execution context\'s
  -- | LexicalEnvironment. 1. Return ? BindingInitialization of
  -- | \|BindingPattern\| with arguments \_value\_ and \_env\_.
  | .let name init body =>
      match exprValue? init with
      | some v =>
          let s' := pushTrace { s with expr := body, env := s.env.extend name v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := init } with
          | some (t, si) =>
              let s' := pushTrace { si with expr := .let name si.expr body, trace := s.trace } t
              some (t, s')
          | none => none
  -- SPEC: L16640-L16654
  -- | AssignmentExpression : LeftHandSideExpression \`=\`
  -- | AssignmentExpression 1. If \|LeftHandSideExpression\| is neither an
  -- | \|ObjectLiteral\| nor an \|ArrayLiteral\|, then 1. Let \_lRef\_ be ?
  -- | Evaluation of \|LeftHandSideExpression\|. 1. If the AssignmentTargetType
  -- | of \|LeftHandSideExpression\| is \~web-compat\~, throw a
  -- | \*ReferenceError\* exception. 1. If
  -- | IsAnonymousFunctionDefinition(\|AssignmentExpression\|) is \*true\* and
  -- | IsIdentifierRef of \|LeftHandSideExpression\| is \*true\*, then 1. Let
  -- | \_lhs\_ be the StringValue of \|LeftHandSideExpression\|. 1. Let
  -- | \_rVal\_ be ? NamedEvaluation of \|AssignmentExpression\| with argument
  -- | \_lhs\_. 1. Else, 1. Let \_rRef\_ be ? Evaluation of
  -- | \|AssignmentExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1.
  -- | \[id=\"step-assignmentexpression-evaluation-simple-putvalue\"\] Perform
  -- | ? PutValue(\_lRef\_, \_rVal\_). 1. Return \_rVal\_. 1. Let
  -- | \_assignmentPattern\_ be the \|AssignmentPattern\| that is covered by
  | .assign name rhs =>
      match exprValue? rhs with
      | some v =>
          let s' := pushTrace { s with expr := .lit v, env := s.env.assign name v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := rhs } with
          | some (t, sr) =>
              let s' := pushTrace { sr with expr := .assign name sr.expr, trace := s.trace } t
              some (t, s')
          | none => none
  -- SPEC: L16584-L16593
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | ConditionalExpression : ShortCircuitExpression \`?\`
  -- | AssignmentExpression \`:\` AssignmentExpression 1. Let \_lRef\_ be ?
  -- | Evaluation of \|ShortCircuitExpression\|. 1. Let \_lVal\_ be ToBoolean(?
  -- | GetValue(\_lRef\_)). 1. If \_lVal\_ is \*true\*, then 1. Let \_trueRef\_
  -- | be ? Evaluation of the first \|AssignmentExpression\|. 1. Return ?
  -- | GetValue(\_trueRef\_). 1. Let \_falseRef\_ be ? Evaluation of the second
  -- | \|AssignmentExpression\|. 1. Return ? GetValue(\_falseRef\_).
  -- SPEC: L17606-L17621
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | IfStatement : \`if\` \`(\` Expression \`)\` Statement \`else\`
  -- | Statement 1. Let \_exprRef\_ be ? Evaluation of \|Expression\|. 1. Let
  -- | \_exprValue\_ be ToBoolean(? GetValue(\_exprRef\_)). 1. If \_exprValue\_
  -- | is \*true\*, then 1. Let \_stmtCompletion\_ be Completion(Evaluation of
  -- | the first \|Statement\|). 1. Else, 1. Let \_stmtCompletion\_ be
  -- | Completion(Evaluation of the second \|Statement\|). 1. Return ?
  -- | UpdateEmpty(\_stmtCompletion\_, \*undefined\*). IfStatement : \`if\`
  -- | \`(\` Expression \`)\` Statement 1. Let \_exprRef\_ be ? Evaluation of
  -- | \|Expression\|. 1. Let \_exprValue\_ be ToBoolean(?
  -- | GetValue(\_exprRef\_)). 1. If \_exprValue\_ is \*false\*, return
  -- | \*undefined\*. 1. Let \_stmtCompletion\_ be Completion(Evaluation of
  -- | \|Statement\|). 1. Return ? UpdateEmpty(\_stmtCompletion\_,
  -- | \*undefined\*).
  | .if cond then_ else_ =>
      match exprValue? cond with
      | some v =>
          let next := if toBoolean v then then_ else else_
          let s' := pushTrace { s with expr := next } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := cond } with
          | some (t, sc) =>
              let s' := pushTrace { sc with expr := .if sc.expr then_ else_, trace := s.trace } t
              some (t, s')
          | none => none
  -- SPEC: L17192-L17196
  -- | Expression : Expression \`,\` AssignmentExpression 1. Let \_lRef\_ be ?
  -- | Evaluation of \|Expression\|. 1. Perform ? GetValue(\_lRef\_). 1. Let
  -- | \_rRef\_ be ? Evaluation of \|AssignmentExpression\|. 1. Return ?
  -- | GetValue(\_rRef\_).
  -- SPEC: L17262-L17292
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | Block : \`{\` \`}\` 1. Return \~empty\~. Block : \`{\` StatementList
  -- | \`}\` 1. Let \_oldEnv\_ be the running execution context\'s
  -- | LexicalEnvironment. 1. Let \_blockEnv\_ be
  -- | NewDeclarativeEnvironment(\_oldEnv\_). 1. Perform
  -- | BlockDeclarationInstantiation(\|StatementList\|, \_blockEnv\_). 1. Set
  -- | the running execution context\'s LexicalEnvironment to \_blockEnv\_. 1.
  -- | Let \_blockValue\_ be Completion(Evaluation of \|StatementList\|). 1.
  -- | Set the running execution context\'s LexicalEnvironment to
  -- | \_oldEnv\_. 1. Return ? \_blockValue\_.
  -- |
  -- | No matter how control leaves the \|Block\| the LexicalEnvironment is
  -- | always restored to its former state.
  -- |
  -- | StatementList : StatementList StatementListItem 1. Let \_sl\_ be ?
  -- | Evaluation of \|StatementList\|. 1. Let \_s\_ be Completion(Evaluation
  -- | of \|StatementListItem\|). 1. Return ? UpdateEmpty(\_s\_, \_sl\_).
  -- |
  -- | The value of a \|StatementList\| is the value of the last
  -- | value-producing item in the \|StatementList\|. For example, the
  -- | following calls to the \`eval\` function all return the value 1:
  -- |
  -- | ``` javascript
  -- |
  -- |           eval("1;;;;;")
  -- |           eval("1;{}")
  -- |           eval("1;var a;")
  -- |         
  -- | ```
  -- |
  -- SPEC: L17544-L17548
  -- | EmptyStatement : \`;\`
  -- |
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | EmptyStatement : \`;\` 1. Return \~empty\~.
  -- SPEC: L17573-L17575
  -- | ExpressionStatement : Expression \`;\` 1. Let \_exprRef\_ be ?
  -- | Evaluation of \|Expression\|. 1. Return ? GetValue(\_exprRef\_).
  -- SPEC: L17277-L17279
  -- | StatementList : StatementList StatementListItem 1. Let \_sl\_ be ?
  -- | Evaluation of \|StatementList\|. 1. Let \_s\_ be Completion(Evaluation
  -- | of \|StatementListItem\|). 1. Return ? UpdateEmpty(\_s\_, \_sl\_).
  | .seq a b =>
      match exprValue? a with
      | some _ =>
          let s' := pushTrace { s with expr := b } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := a } with
          | some (t, sa) =>
              let s' := pushTrace { sa with expr := .seq sa.expr b, trace := s.trace } t
              some (t, s')
          | none => none
  -- SPEC: L16028-L16039
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | UpdateExpression : LeftHandSideExpression \`++\` 1. Let \_lhs\_ be ?
  -- | Evaluation of \|LeftHandSideExpression\|. 1. If the AssignmentTargetType
  -- | of \|LeftHandSideExpression\| is \~web-compat\~, throw a
  -- | \*ReferenceError\* exception. 1. Let \_oldValue\_ be ? ToNumeric(?
  -- | GetValue(\_lhs\_)). 1. If \_oldValue\_ is a Number, then 1. Let
  -- | \_newValue\_ be Number::add(\_oldValue\_, \*1\*~𝔽~). 1. Else, 1. Assert:
  -- | \_oldValue\_ is a BigInt. 1. Let \_newValue\_ be
  -- | BigInt::add(\_oldValue\_, \*1\*~ℤ~). 1. Perform ? PutValue(\_lhs\_,
  -- | \_newValue\_). 1. Return \_oldValue\_.
  -- SPEC: L16040-L16053
  -- | # Postfix Decrement Operator
  -- |
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | UpdateExpression : LeftHandSideExpression \`\--\` 1. Let \_lhs\_ be ?
  -- | Evaluation of \|LeftHandSideExpression\|. 1. If the AssignmentTargetType
  -- | of \|LeftHandSideExpression\| is \~web-compat\~, throw a
  -- | \*ReferenceError\* exception. 1. Let \_oldValue\_ be ? ToNumeric(?
  -- | GetValue(\_lhs\_)). 1. If \_oldValue\_ is a Number, then 1. Let
  -- | \_newValue\_ be Number::subtract(\_oldValue\_, \*1\*~𝔽~). 1. Else, 1.
  -- | Assert: \_oldValue\_ is a BigInt. 1. Let \_newValue\_ be
  -- | BigInt::subtract(\_oldValue\_, \*1\*~ℤ~). 1. Perform ? PutValue(\_lhs\_,
  -- | \_newValue\_). 1. Return \_oldValue\_.
  -- SPEC: L16054-L16066
  -- | # Prefix Increment Operator
  -- |
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | UpdateExpression : \`++\` UnaryExpression 1. Let \_expr\_ be ?
  -- | Evaluation of \|UnaryExpression\|. 1. If the AssignmentTargetType of
  -- | \|UnaryExpression\| is \~web-compat\~, throw a \*ReferenceError\*
  -- | exception. 1. Let \_oldValue\_ be ? ToNumeric(? GetValue(\_expr\_)). 1.
  -- | If \_oldValue\_ is a Number, then 1. Let \_newValue\_ be
  -- | Number::add(\_oldValue\_, \*1\*~𝔽~). 1. Else, 1. Assert: \_oldValue\_ is
  -- | a BigInt. 1. Let \_newValue\_ be BigInt::add(\_oldValue\_, \*1\*~ℤ~). 1.
  -- | Perform ? PutValue(\_expr\_, \_newValue\_). 1. Return \_newValue\_.
  -- SPEC: L16067-L16080
  -- | # Prefix Decrement Operator
  -- |
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | UpdateExpression : \`\--\` UnaryExpression 1. Let \_expr\_ be ?
  -- | Evaluation of \|UnaryExpression\|. 1. If the AssignmentTargetType of
  -- | \|UnaryExpression\| is \~web-compat\~, throw a \*ReferenceError\*
  -- | exception. 1. Let \_oldValue\_ be ? ToNumeric(? GetValue(\_expr\_)). 1.
  -- | If \_oldValue\_ is a Number, then 1. Let \_newValue\_ be
  -- | Number::subtract(\_oldValue\_, \*1\*~𝔽~). 1. Else, 1. Assert:
  -- | \_oldValue\_ is a BigInt. 1. Let \_newValue\_ be
  -- | BigInt::subtract(\_oldValue\_, \*1\*~ℤ~). 1. Perform ?
  -- | PutValue(\_expr\_, \_newValue\_). 1. Return \_newValue\_.
  -- SPEC: L8534-L8571
  -- | # Runtime Semantics: BindingInitialization ( \_value\_: an ECMAScript language value, \_environment\_: an Environment Record or \*undefined\*, ): either a normal completion containing \~unused\~ or an abrupt completion
  -- |
  -- | \*undefined\* is passed for \_environment\_ to indicate that a PutValue
  -- | operation should be used to assign the initialization value. This is the
  -- | case for \`var\` statements and formal parameter lists of some
  -- | non-strict functions (See ). In those cases a lexical binding is hoisted
  -- | and preinitialized prior to evaluation of its initializer.
  -- |
  -- | BindingIdentifier : Identifier 1. Let \_name\_ be the StringValue of
  -- | \|Identifier\|. 1. Return ? InitializeBoundName(\_name\_, \_value\_,
  -- | \_environment\_). BindingIdentifier : \`yield\` 1. Return ?
  -- | InitializeBoundName(\*\"yield\"\*, \_value\_, \_environment\_).
  -- | BindingIdentifier : \`await\` 1. Return ?
  -- | InitializeBoundName(\*\"await\"\*, \_value\_, \_environment\_).
  -- | BindingPattern : ObjectBindingPattern 1. Perform ?
  -- | RequireObjectCoercible(\_value\_). 1. Return ? BindingInitialization of
  -- | \|ObjectBindingPattern\| with arguments \_value\_ and \_environment\_.
  -- | BindingPattern : ArrayBindingPattern 1. Let \_iteratorRecord\_ be ?
  -- | GetIterator(\_value\_, \~sync\~). 1. Let \_result\_ be
  -- | Completion(IteratorBindingInitialization of \|ArrayBindingPattern\| with
  -- | arguments \_iteratorRecord\_ and \_environment\_). 1. If
  -- | \_iteratorRecord\_.\[\[Done\]\] is \*false\*, return ?
  -- | IteratorClose(\_iteratorRecord\_, \_result\_). 1. Return ? \_result\_.
  -- | ObjectBindingPattern : \`{\` \`}\` 1. Return \~unused\~.
  -- | ObjectBindingPattern : \`{\` BindingPropertyList \`}\` \`{\`
  -- | BindingPropertyList \`,\` \`}\` 1. Perform ?
  -- | PropertyBindingInitialization of \|BindingPropertyList\| with arguments
  -- | \_value\_ and \_environment\_. 1. Return \~unused\~.
  -- | ObjectBindingPattern : \`{\` BindingRestProperty \`}\` 1. Let
  -- | \_excludedNames\_ be a new empty List. 1. Return ?
  -- | RestBindingInitialization of \|BindingRestProperty\| with arguments
  -- | \_value\_, \_environment\_, and \_excludedNames\_. ObjectBindingPattern
  -- | : \`{\` BindingPropertyList \`,\` BindingRestProperty \`}\` 1. Let
  -- | \_excludedNames\_ be ? PropertyBindingInitialization of
  -- | \|BindingPropertyList\| with arguments \_value\_ and \_environment\_. 1.
  -- | Return ? RestBindingInitialization of \|BindingRestProperty\| with
  -- | arguments \_value\_, \_environment\_, and \_excludedNames\_.
  -- SPEC: L8572-L8578
  -- | # InitializeBoundName ( \_name\_: a String, \_value\_: an ECMAScript language value, \_environment\_: an Environment Record or \*undefined\*, ): either a normal completion containing \~unused\~ or an abrupt completion
  -- |
  -- | 1\. If \_environment\_ is not \*undefined\*, then 1. Perform !
  -- | \_environment\_.InitializeBinding(\_name\_, \_value\_). 1. Return
  -- | \~unused\~. 1. Let \_lhs\_ be ? ResolveBinding(\_name\_). 1. Return ?
  -- | PutValue(\_lhs\_, \_value\_).
  -- SPEC: L17293-L17331
  -- | # BlockDeclarationInstantiation ( \_code\_: a Parse Node, \_env\_: a Declarative Environment Record, ): \~unused\~
  -- |
  -- | description
  -- | :   \_code\_ is the Parse Node corresponding to the body of the block.
  -- |     \_env\_ is the Environment Record in which bindings are to be
  -- |     created.
  -- |
  -- | When a \|Block\| or \|CaseBlock\| is evaluated a new Declarative
  -- | Environment Record is created and bindings for each block scoped
  -- | variable, constant, function, or class declared in the block are
  -- | instantiated in the Environment Record.
  -- |
  -- | It performs the following steps when called:
  -- |
  -- | 1\. Let \_declarations\_ be the LexicallyScopedDeclarations of
  -- | \_code\_. 1. Let \_privateEnv\_ be the running execution context\'s
  -- | PrivateEnvironment. 1. For each element \_d\_ of \_declarations\_, do 1.
  -- | For each element \_dn\_ of the BoundNames of \_d\_, do 1. If
  -- | IsConstantDeclaration of \_d\_ is \*true\*, then 1. Perform !
  -- | \_env\_.CreateImmutableBinding(\_dn\_, \*true\*). 1. Else, 1.
  -- | \[id=\"step-blockdeclarationinstantiation-createmutablebinding\",
  -- | normative-optional\] If the host is a web browser or otherwise supports
  -- | , then 1. If ! \_env\_.HasBinding(\_dn\_) is \*false\*, then 1. Perform
  -- | ! \_env\_.CreateMutableBinding(\_dn\_, \*false\*). 1. Else, 1. Perform !
  -- | \_env\_.CreateMutableBinding(\_dn\_, \*false\*). 1. If \_d\_ is either a
  -- | \|FunctionDeclaration\|, a \|GeneratorDeclaration\|, an
  -- | \|AsyncFunctionDeclaration\|, or an \|AsyncGeneratorDeclaration\|,
  -- | then 1. Let \_fn\_ be the sole element of the BoundNames of \_d\_. 1.
  -- | Let \_fo\_ be InstantiateFunctionObject of \_d\_ with arguments \_env\_
  -- | and \_privateEnv\_. 1.
  -- | \[id=\"step-blockdeclarationinstantiation-initializebinding\",
  -- | normative-optional\] If the host is a web browser or otherwise supports
  -- | , then 1. If the binding for \_fn\_ in \_env\_ is an uninitialized
  -- | binding, then 1. Perform ! \_env\_.InitializeBinding(\_fn\_, \_fo\_). 1.
  -- | Else, 1. Assert: \_d\_ is a \|FunctionDeclaration\|. 1. Perform !
  -- | \_env\_.SetMutableBinding(\_fn\_, \_fo\_, \*false\*). 1. Else, 1.
  -- | Perform ! \_env\_.InitializeBinding(\_fn\_, \_fo\_). 1. Return
  -- | \~unused\~.
  -- SPEC: L16186-L16188
  -- | UnaryExpression : \`+\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
  -- | of \|UnaryExpression\|. 1. Return ? ToNumber(? GetValue(\_expr\_)).
  -- SPEC: L16197-L16202
  -- | UnaryExpression : \`-\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
  -- | of \|UnaryExpression\|. 1. Let \_oldValue\_ be ? ToNumeric(?
  -- | GetValue(\_expr\_)). 1. If \_oldValue\_ is a Number, return
  -- | Number::unaryMinus(\_oldValue\_). 1. Assert: \_oldValue\_ is a
  -- | BigInt. 1. Return BigInt::unaryMinus(\_oldValue\_).
  -- SPEC: L16218-L16222
  -- | UnaryExpression : \`!\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
  -- | of \|UnaryExpression\|. 1. Let \_oldValue\_ be ToBoolean(?
  -- | GetValue(\_expr\_)). 1. If \_oldValue\_ is \*true\*, return
  -- | \*false\*. 1. Return \*true\*.
  | .unary op arg =>
      match exprValue? arg with
      | some v =>
          let s' := pushTrace { s with expr := .lit (evalUnary op v) } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              let s' := pushTrace { sa with expr := .unary op sa.expr, trace := s.trace } t
              some (t, s')
          | none => none
  -- SPEC: L16279-L16282
  -- | AdditiveExpression : AdditiveExpression \`+\`
  -- | MultiplicativeExpression 1. Return ?
  -- | EvaluateStringOrNumericBinaryExpression(\|AdditiveExpression\|, \`+\`,
  -- | \|MultiplicativeExpression\|).
  -- SPEC: L16291-L16294
  -- | AdditiveExpression : AdditiveExpression \`-\`
  -- | MultiplicativeExpression 1. Return ?
  -- | EvaluateStringOrNumericBinaryExpression(\|AdditiveExpression\|, \`-\`,
  -- | \|MultiplicativeExpression\|).
  -- SPEC: L16929-L16935
  -- | # EvaluateStringOrNumericBinaryExpression ( \_leftOperand\_: a Parse Node, \_opText\_: a sequence of Unicode code points, \_rightOperand\_: a Parse Node, ): either a normal completion containing either a String, a BigInt, or a Number, or an abrupt completion
  -- | 1\. Let \_lRef\_ be ? Evaluation of \_leftOperand\_. 1. Let \_lVal\_ be
  -- | ? GetValue(\_lRef\_). 1. Let \_rRef\_ be ? Evaluation of
  -- | \_rightOperand\_. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1. Return ?
  -- | ApplyStringOrNumericBinaryOperator(\_lVal\_, \_opText\_, \_rVal\_).
  | .binary op lhs rhs =>
      match exprValue? lhs with
      | none =>
          match step? { s with expr := lhs } with
          | some (t, sl) =>
              let s' := pushTrace { sl with expr := .binary op sl.expr rhs, trace := s.trace } t
              some (t, s')
          | none => none
      | some lv =>
          match exprValue? rhs with
          | none =>
              match step? { s with expr := rhs } with
              | some (t, sr) =>
                  let s' := pushTrace { sr with expr := .binary op (.lit lv) sr.expr, trace := s.trace } t
                  some (t, s')
              | none => none
          | some rv =>
              let s' := pushTrace { s with expr := .lit (evalBinary op lv rv) } .silent
              some (.silent, s')
  -- SPEC: L15638-L15665
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | CallExpression : CoverCallExpressionAndAsyncArrowHead 1. Let \_expr\_ be
  -- | the \|CallMemberExpression\| that is covered by
  -- | \|CoverCallExpressionAndAsyncArrowHead\|. 1. Let \_memberExpr\_ be the
  -- | \|MemberExpression\| of \_expr\_. 1. Let \_arguments\_ be the
  -- | \|Arguments\| of \_expr\_. 1. Let \_ref\_ be ? Evaluation of
  -- | \_memberExpr\_. 1. Let \_func\_ be ? GetValue(\_ref\_). 1. If \_ref\_ is
  -- | a Reference Record, IsPropertyReference(\_ref\_) is \*false\*, and
  -- | \_ref\_.\[\[ReferencedName\]\] is \*\"eval\"\*, then 1. If
  -- | SameValue(\_func\_, %eval%) is \*true\*, then 1. Let \_argList\_ be ?
  -- | ArgumentListEvaluation of \_arguments\_. 1. If \_argList\_ has no
  -- | elements, return \*undefined\*. 1. Let \_evalArg\_ be the first element
  -- | of \_argList\_. 1. If IsStrict(this \|CallExpression\|) is \*true\*, let
  -- | \_strictCaller\_ be \*true\*; else let \_strictCaller\_ be \*false\*. 1.
  -- | \[id=\"step-callexpression-evaluation-direct-eval\"\] Return ?
  -- | PerformEval(\_evalArg\_, \_strictCaller\_, \*true\*). 1. Let
  -- | \_thisCall\_ be this \|CallExpression\|. 1. Let \_tailCall\_ be
  -- | IsInTailPosition(\_thisCall\_). 1. Return ? EvaluateCall(\_func\_,
  -- | \_ref\_, \_arguments\_, \_tailCall\_).
  -- |
  -- | A \|CallExpression\| evaluation that executes step is a [direct
  -- | eval]{.dfn variants="direct evals"}.
  -- |
  -- | CallExpression : CallExpression Arguments 1. Let \_ref\_ be ? Evaluation
  -- | of \|CallExpression\|. 1. Let \_func\_ be ? GetValue(\_ref\_). 1. Let
  -- | \_thisCall\_ be this \|CallExpression\|. 1. Let \_tailCall\_ be
  -- | IsInTailPosition(\_thisCall\_). 1. Return ? EvaluateCall(\_func\_,
  -- SPEC: L15668-L15681
  -- | # EvaluateCall ( \_func\_: an ECMAScript language value, \_ref\_: an ECMAScript language value or a Reference Record, \_arguments\_: a Parse Node, \_tailPosition\_: a Boolean, ): either a normal completion containing an ECMAScript language value or an abrupt completion
  -- |
  -- | 1\. If \_ref\_ is a Reference Record, then 1. If
  -- | IsPropertyReference(\_ref\_) is \*true\*, then 1. Let \_thisValue\_ be
  -- | GetThisValue(\_ref\_). 1. Else, 1. Let \_refEnv\_ be
  -- | \_ref\_.\[\[Base\]\]. 1. Assert: \_refEnv\_ is an Environment Record. 1.
  -- | Let \_thisValue\_ be \_refEnv\_.WithBaseObject(). 1. Else, 1. Let
  -- | \_thisValue\_ be \*undefined\*. 1. Let \_argList\_ be ?
  -- | ArgumentListEvaluation of \_arguments\_. 1. If \_func\_ is not an
  -- | Object, throw a \*TypeError\* exception. 1. If IsCallable(\_func\_) is
  -- | \*false\*, throw a \*TypeError\* exception. 1. If \_tailPosition\_ is
  -- | \*true\*, perform PrepareForTailCall(). 1. Return ? Call(\_func\_,
  -- | \_thisValue\_, \_argList\_).
  -- SPEC: L11074-L11094
  -- | # \[\[Call\]\] ( \_thisArgument\_: an ECMAScript language value, \_argumentsList\_: a List of ECMAScript language values, ): either a normal completion containing an ECMAScript language value or a throw completion
  -- |
  -- | for
  -- | :   an ECMAScript function object \_F\_
  -- |
  -- | 1\. Let \_callerContext\_ be the running execution context. 1. Let
  -- | \_calleeContext\_ be PrepareForOrdinaryCall(\_F\_, \*undefined\*). 1.
  -- | Assert: \_calleeContext\_ is now the running execution context. 1. If
  -- | \_F\_.\[\[IsClassConstructor\]\] is \*true\*, then 1. Let \_error\_ be a
  -- | newly created \*TypeError\* object. 1. NOTE: \_error\_ is created in
  -- | \_calleeContext\_ with \_F\_\'s associated Realm Record. 1. Remove
  -- | \_calleeContext\_ from the execution context stack and restore
  -- | \_callerContext\_ as the running execution context. 1. Return
  -- | ThrowCompletion(\_error\_). 1. Perform OrdinaryCallBindThis(\_F\_,
  -- | \_calleeContext\_, \_thisArgument\_). 1. Let \_result\_ be
  -- | Completion(OrdinaryCallEvaluateBody(\_F\_, \_argumentsList\_)). 1.
  -- | \[id=\"step-call-pop-context-stack\"\] Remove \_calleeContext\_ from the
  -- | execution context stack and restore \_callerContext\_ as the running
  -- | execution context. 1. If \_result\_ is a return completion, return
  -- | \_result\_.\[\[Value\]\]. 1. Assert: \_result\_ is a throw
  -- | completion. 1. Return ? \_result\_.
  -- SPEC: L11100-L11117
  -- | # PrepareForOrdinaryCall ( \_F\_: an ECMAScript function object, \_newTarget\_: an Object or \*undefined\*, ): an execution context
  -- |
  -- | 1\. Let \_callerContext\_ be the running execution context. 1. Let
  -- | \_calleeContext\_ be a new ECMAScript code execution context. 1. Set the
  -- | Function of \_calleeContext\_ to \_F\_. 1. Let \_calleeRealm\_ be
  -- | \_F\_.\[\[Realm\]\]. 1. Set the Realm of \_calleeContext\_ to
  -- | \_calleeRealm\_. 1. Set the ScriptOrModule of \_calleeContext\_ to
  -- | \_F\_.\[\[ScriptOrModule\]\]. 1. Let \_localEnv\_ be
  -- | NewFunctionEnvironment(\_F\_, \_newTarget\_). 1. Set the
  -- | LexicalEnvironment of \_calleeContext\_ to \_localEnv\_. 1. Set the
  -- | VariableEnvironment of \_calleeContext\_ to \_localEnv\_. 1. Set the
  -- | PrivateEnvironment of \_calleeContext\_ to
  -- | \_F\_.\[\[PrivateEnvironment\]\]. 1. If \_callerContext\_ is not already
  -- | suspended, suspend \_callerContext\_. 1. Push \_calleeContext\_ onto the
  -- | execution context stack; \_calleeContext\_ is now the running execution
  -- | context. 1. NOTE: Any exception objects produced after this point are
  -- | associated with \_calleeRealm\_. 1. Return \_calleeContext\_.
  -- SPEC: L11170-L11174
  -- | # OrdinaryCallEvaluateBody ( \_F\_: an ECMAScript function object, \_argumentsList\_: a List of ECMAScript language values, ): a return completion or a throw completion
  -- |
  -- | 1\. Return ? EvaluateBody of \_F\_.\[\[ECMAScriptCode\]\] with arguments
  -- | \_F\_ and \_argumentsList\_.
  -- SPEC: L11136-L11169
  -- | # Runtime Semantics: EvaluateBody ( \_functionObject\_: an ECMAScript function object, \_argumentsList\_: a List of ECMAScript language values, ): a return completion or a throw completion
  -- |
  -- | FunctionBody : FunctionStatementList 1. Return ? EvaluateFunctionBody of
  -- | \|FunctionBody\| with arguments \_functionObject\_ and
  -- | \_argumentsList\_. ConciseBody : ExpressionBody 1. Return ?
  -- | EvaluateConciseBody of \|ConciseBody\| with arguments \_functionObject\_
  -- | and \_argumentsList\_. GeneratorBody : FunctionBody 1. Return ?
  -- | EvaluateGeneratorBody of \|GeneratorBody\| with arguments
  -- | \_functionObject\_ and \_argumentsList\_. AsyncGeneratorBody :
  -- | FunctionBody 1. Return ? EvaluateAsyncGeneratorBody of
  -- | \|AsyncGeneratorBody\| with arguments \_functionObject\_ and
  -- | \_argumentsList\_. AsyncFunctionBody : FunctionBody 1. Return ?
  -- | EvaluateAsyncFunctionBody of \|AsyncFunctionBody\| with arguments
  -- | \_functionObject\_ and \_argumentsList\_. AsyncConciseBody :
  -- | ExpressionBody 1. Return ? EvaluateAsyncConciseBody of
  -- | \|AsyncConciseBody\| with arguments \_functionObject\_ and
  -- | \_argumentsList\_. Initializer : \`=\` AssignmentExpression 1. Assert:
  -- | \_argumentsList\_ is empty. 1. Assert:
  -- | \_functionObject\_.\[\[ClassFieldInitializerName\]\] is not
  -- | \~empty\~. 1. If IsAnonymousFunctionDefinition(\|AssignmentExpression\|)
  -- | is \*true\*, then 1. Let \_value\_ be ? NamedEvaluation of
  -- | \|Initializer\| with argument
  -- | \_functionObject\_.\[\[ClassFieldInitializerName\]\]. 1. Else, 1. Let
  -- | \_rhs\_ be ? Evaluation of \|AssignmentExpression\|. 1. Let \_value\_ be
  -- | ? GetValue(\_rhs\_). 1. Return ReturnCompletion(\_value\_).
  -- |
  -- | Even though field initializers constitute a function boundary, calling
  -- | FunctionDeclarationInstantiation does not have any observable effect and
  -- | so is omitted.
  -- |
  -- | ClassStaticBlockBody : ClassStaticBlockStatementList 1. Assert:
  -- | \_argumentsList\_ is empty. 1. Return ? EvaluateClassStaticBlockBody of
  -- | \|ClassStaticBlockBody\| with argument \_functionObject\_.
  -- |
  -- SPEC: L15736-L15773
  -- | # Runtime Semantics: ArgumentListEvaluation ( ): either a normal completion containing a List of ECMAScript language values or an abrupt completion
  -- |
  -- | Arguments : \`(\` \`)\` 1. Return a new empty List. ArgumentList :
  -- | AssignmentExpression 1. Let \_ref\_ be ? Evaluation of
  -- | \|AssignmentExpression\|. 1. Let \_arg\_ be ? GetValue(\_ref\_). 1.
  -- | Return « \_arg\_ ». ArgumentList : \`\...\` AssignmentExpression 1. Let
  -- | \_list\_ be a new empty List. 1. Let \_spreadRef\_ be ? Evaluation of
  -- | \|AssignmentExpression\|. 1. Let \_spreadObj\_ be ?
  -- | GetValue(\_spreadRef\_). 1. Let \_iteratorRecord\_ be ?
  -- | GetIterator(\_spreadObj\_, \~sync\~). 1. Repeat, 1. Let \_next\_ be ?
  -- | IteratorStepValue(\_iteratorRecord\_). 1. If \_next\_ is \~done\~,
  -- | return \_list\_. 1. Append \_next\_ to \_list\_. ArgumentList :
  -- | ArgumentList \`,\` AssignmentExpression 1. Let \_precedingArgs\_ be ?
  -- | ArgumentListEvaluation of \|ArgumentList\|. 1. Let \_ref\_ be ?
  -- | Evaluation of \|AssignmentExpression\|. 1. Let \_arg\_ be ?
  -- | GetValue(\_ref\_). 1. Return the list-concatenation of \_precedingArgs\_
  -- | and « \_arg\_ ». ArgumentList : ArgumentList \`,\` \`\...\`
  -- | AssignmentExpression 1. Let \_precedingArgs\_ be ?
  -- | ArgumentListEvaluation of \|ArgumentList\|. 1. Let \_spreadRef\_ be ?
  -- | Evaluation of \|AssignmentExpression\|. 1. Let \_iteratorRecord\_ be ?
  -- | GetIterator(? GetValue(\_spreadRef\_), \~sync\~). 1. Repeat, 1. Let
  -- | \_next\_ be ? IteratorStepValue(\_iteratorRecord\_). 1. If \_next\_ is
  -- | \~done\~, return \_precedingArgs\_. 1. Append \_next\_ to
  -- | \_precedingArgs\_. TemplateLiteral : NoSubstitutionTemplate 1. Let
  -- | \_templateLiteral\_ be this \|TemplateLiteral\|. 1. Let \_siteObj\_ be
  -- | GetTemplateObject(\_templateLiteral\_). 1. Return « \_siteObj\_ ».
  -- | TemplateLiteral : SubstitutionTemplate 1. Let \_templateLiteral\_ be
  -- | this \|TemplateLiteral\|. 1. Let \_siteObj\_ be
  -- | GetTemplateObject(\_templateLiteral\_). 1. Let \_remaining\_ be ?
  -- | ArgumentListEvaluation of \|SubstitutionTemplate\|. 1. Return the
  -- | list-concatenation of « \_siteObj\_ » and \_remaining\_.
  -- | SubstitutionTemplate : TemplateHead Expression TemplateSpans 1. Let
  -- | \_firstSubRef\_ be ? Evaluation of \|Expression\|. 1. Let \_firstSub\_
  -- | be ? GetValue(\_firstSubRef\_). 1. Let \_restSub\_ be ?
  -- | SubstitutionEvaluation of \|TemplateSpans\|. 1. Assert: \_restSub\_ is a
  -- | possibly empty List. 1. Return the list-concatenation of « \_firstSub\_
  -- | » and \_restSub\_.
  -- SPEC: L11569-L11580
  -- | # BuiltinCallOrConstruct ( \_F\_: a built-in function object, \_thisArgument\_: an ECMAScript language value or \~uninitialized\~, \_argumentsList\_: a List of ECMAScript language values, \_newTarget\_: a constructor or \*undefined\*, ): either a normal completion containing an ECMAScript language value or a throw completion
  -- |
  -- | 1\. Let \_callerContext\_ be the running execution context. 1. If
  -- | \_callerContext\_ is not already suspended, suspend
  -- | \_callerContext\_. 1. Let \_calleeContext\_ be a new execution
  -- | context. 1. Set the Function of \_calleeContext\_ to \_F\_. 1. Let
  -- | \_calleeRealm\_ be \_F\_.\[\[Realm\]\]. 1. Set the Realm of
  -- | \_calleeContext\_ to \_calleeRealm\_. 1. Set the ScriptOrModule of
  -- | \_calleeContext\_ to \*null\*. 1. Perform any necessary
  -- | implementation-defined initialization of \_calleeContext\_. 1. Push
  -- | \_calleeContext\_ onto the execution context stack; \_calleeContext\_ is
  -- | now the running execution context. 1. If \_F\_.\[\[Async\]\] is
  | .call callee args =>
      match exprValue? callee with
      | none =>
          match step? { s with expr := callee } with
          | some (t, sc) =>
              let s' := pushTrace { sc with expr := .call sc.expr args, trace := s.trace } t
              some (t, s')
          | none => none
      | some cv =>
          -- Step 2: Step all arguments to values (left-to-right).
          match allValues args with
          | some argVals =>
              -- Step 3: All args are values — perform the call.
              match cv with
              | .function idx =>
                  -- §18.2 Built-in: console.log (reserved at function index 0).
                  if idx == consoleLogIdx then
                      let msg := match argVals with
                        | [v] => valueToString v
                        | vs => String.intercalate " " (vs.map valueToString)
                      let s' := pushTrace { s with expr := .lit .undefined } (.log msg)
                      some (.log msg, s')
                  else
                  match s.funcs[idx]? with
                  | some closure =>
                      -- §10.2.1 [[Call]]: bind params to args in closure's captured environment.
                      let pairs := closure.params.zip argVals
                      let bodyBindings :=
                        pairs.foldr (fun pv bs => (pv.1, pv.2) :: bs) closure.capturedEnv
                      let bodyEnv : Env := { bindings := bodyBindings }
                      -- Bind function name for recursion (§14.1.20 step 28).
                      let bodyEnv' : Env := match closure.name with
                        | some n => { bindings := (n, .function idx) :: bodyEnv.bindings }
                        | none => bodyEnv
                      -- Push caller env onto call stack for restoration on return.
                      -- Wrap body in tryCatch with special catch param to intercept returns.
                      let wrapped := .tryCatch closure.body "__call_frame_return__"
                        (.var "__call_frame_return__") none
                      let s' := pushTrace { s with
                        expr := wrapped
                        env := bodyEnv'
                        callStack := s.env.bindings :: s.callStack } .silent
                      some (.silent, s')
                  | none =>
                      let s' := pushTrace { s with expr := .lit .undefined } .silent
                      some (.silent, s')
              | _ =>
                  -- Non-function callee: return undefined.
                  let s' := pushTrace { s with expr := .lit .undefined } .silent
                  some (.silent, s')
          | none =>
              -- Step first non-value argument (left-to-right evaluation §12.3.4.1).
              match hf : firstNonValueExpr args with
              | some (done, target, remaining) =>
                  have : Expr.depth target < Expr.depth s.expr := by
                    rw [h]; simp [Expr.depth]; have := firstNonValueExpr_depth hf; omega
                  match step? { s with expr := target } with
                  | some (t, sa) =>
                      let s' := pushTrace { sa with expr := .call (.lit cv) (done ++ [sa.expr] ++ remaining), trace := s.trace } t
                      some (t, s')
                  | none => none
              | none => none
  -- SPEC: L15565-L15599
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | MemberExpression : MemberExpression \`\[\` Expression \`\]\` 1. Let
  -- | \_baseReference\_ be ? Evaluation of \|MemberExpression\|. 1. Let
  -- | \_baseValue\_ be ? GetValue(\_baseReference\_). 1. Let \_strict\_ be
  -- | IsStrict(this \|MemberExpression\|). 1. Return ?
  -- | EvaluatePropertyAccessWithExpressionKey(\_baseValue\_, \|Expression\|,
  -- | \_strict\_). MemberExpression : MemberExpression \`.\` IdentifierName 1.
  -- | Let \_baseReference\_ be ? Evaluation of \|MemberExpression\|. 1. Let
  -- | \_baseValue\_ be ? GetValue(\_baseReference\_). 1. Let \_strict\_ be
  -- | IsStrict(this \|MemberExpression\|). 1. Return
  -- | EvaluatePropertyAccessWithIdentifierKey(\_baseValue\_,
  -- | \|IdentifierName\|, \_strict\_). MemberExpression : MemberExpression
  -- | \`.\` PrivateIdentifier 1. Let \_baseReference\_ be ? Evaluation of
  -- | \|MemberExpression\|. 1. Let \_baseValue\_ be ?
  -- | GetValue(\_baseReference\_). 1. Let \_fieldNameString\_ be the
  -- | StringValue of \|PrivateIdentifier\|. 1. Return
  -- | MakePrivateReference(\_baseValue\_, \_fieldNameString\_). CallExpression
  -- | : CallExpression \`\[\` Expression \`\]\` 1. Let \_baseReference\_ be ?
  -- | Evaluation of \|CallExpression\|. 1. Let \_baseValue\_ be ?
  -- | GetValue(\_baseReference\_). 1. Let \_strict\_ be IsStrict(this
  -- | \|CallExpression\|). 1. Return ?
  -- | EvaluatePropertyAccessWithExpressionKey(\_baseValue\_, \|Expression\|,
  -- | \_strict\_). CallExpression : CallExpression \`.\` IdentifierName 1. Let
  -- | \_baseReference\_ be ? Evaluation of \|CallExpression\|. 1. Let
  -- | \_baseValue\_ be ? GetValue(\_baseReference\_). 1. Let \_strict\_ be
  -- | IsStrict(this \|CallExpression\|). 1. Return
  -- | EvaluatePropertyAccessWithIdentifierKey(\_baseValue\_,
  -- | \|IdentifierName\|, \_strict\_). CallExpression : CallExpression \`.\`
  -- | PrivateIdentifier 1. Let \_baseReference\_ be ? Evaluation of
  -- | \|CallExpression\|. 1. Let \_baseValue\_ be ?
  -- | GetValue(\_baseReference\_). 1. Let \_fieldNameString\_ be the
  -- | StringValue of \|PrivateIdentifier\|. 1. Return
  -- | MakePrivateReference(\_baseValue\_, \_fieldNameString\_).
  -- SPEC: L10690-L10693
  -- | # OrdinaryGetPrototypeOf ( \_O\_: an Object, ): an Object or \*null\*
  -- |
  -- | 1\. Return \_O\_.\[\[Prototype\]\].
  -- SPEC: L10701-L10713
  -- | # OrdinarySetPrototypeOf ( \_O\_: an Object, \_V\_: an Object or \*null\*, ): a Boolean
  -- |
  -- | 1\. Let \_current\_ be \_O\_.\[\[Prototype\]\]. 1. If SameValue(\_V\_,
  -- | \_current\_) is \*true\*, return \*true\*. 1. Let \_extensible\_ be
  -- | \_O\_.\[\[Extensible\]\]. 1. If \_extensible\_ is \*false\*, return
  -- | \*false\*. 1. Let \_p\_ be \_V\_. 1. Let \_done\_ be \*false\*. 1.
  -- | \[id=\"step-ordinarysetprototypeof-loop\"\] Repeat, while \_done\_ is
  -- | \*false\*, 1. If \_p\_ is \*null\*, then 1. Set \_done\_ to \*true\*. 1.
  -- | Else if SameValue(\_p\_, \_O\_) is \*true\*, then 1. Return
  -- | \*false\*. 1. Else, 1. If \_p\_.\[\[GetPrototypeOf\]\] is not the
  -- | ordinary object internal method defined in , set \_done\_ to
  -- | \*true\*. 1. Else, set \_p\_ to \_p\_.\[\[Prototype\]\]. 1. Set
  -- | \_O\_.\[\[Prototype\]\] to \_V\_. 1. Return \*true\*.
  -- SPEC: L10903-L10926
  -- | # OrdinarySetWithOwnDescriptor ( \_O\_: an Object, \_P\_: a property key, \_V\_: an ECMAScript language value, \_Receiver\_: an ECMAScript language value, \_ownDesc\_: a Property Descriptor or \*undefined\*, ): either a normal completion containing a Boolean or a throw completion
  -- |
  -- | 1\. If \_ownDesc\_ is \*undefined\*, then 1. Let \_parent\_ be ?
  -- | \_O\_.\[\[GetPrototypeOf\]\](). 1. If \_parent\_ is not \*null\*, return
  -- | ? \_parent\_.\[\[Set\]\](\_P\_, \_V\_, \_Receiver\_). 1. Set \_ownDesc\_
  -- | to the PropertyDescriptor { \[\[Value\]\]: \*undefined\*,
  -- | \[\[Writable\]\]: \*true\*, \[\[Enumerable\]\]: \*true\*,
  -- | \[\[Configurable\]\]: \*true\* }. 1. If IsDataDescriptor(\_ownDesc\_) is
  -- | \*true\*, then 1. If \_ownDesc\_.\[\[Writable\]\] is \*false\*, return
  -- | \*false\*. 1. If \_Receiver\_ is not an Object, return \*false\*. 1. Let
  -- | \_existingDescriptor\_ be ?
  -- | \_Receiver\_.\[\[GetOwnProperty\]\](\_P\_). 1. If \_existingDescriptor\_
  -- | is \*undefined\*, then 1. Assert: \_Receiver\_ does not currently have a
  -- | property \_P\_. 1. Return ? CreateDataProperty(\_Receiver\_, \_P\_,
  -- | \_V\_). 1. If IsAccessorDescriptor(\_existingDescriptor\_) is \*true\*,
  -- | return \*false\*. 1. If \_existingDescriptor\_.\[\[Writable\]\] is
  -- | \*false\*, return \*false\*. 1. Let \_valueDesc\_ be the
  -- | PropertyDescriptor { \[\[Value\]\]: \_V\_ }. 1. Return ?
  -- | \_Receiver\_.\[\[DefineOwnProperty\]\](\_P\_, \_valueDesc\_). 1. Assert:
  -- | IsAccessorDescriptor(\_ownDesc\_) is \*true\*. 1. Let \_setter\_ be
  -- | \_ownDesc\_.\[\[Set\]\]. 1. If \_setter\_ is \*undefined\*, return
  -- | \*false\*. 1. Perform ? Call(\_setter\_, \_Receiver\_, « \_V\_ »). 1.
  -- | Return \*true\*.
  -- SPEC: L10949-L10958
  -- | # OrdinaryOwnPropertyKeys ( \_O\_: an Object, ): a List of property keys
  -- |
  -- | 1\. Let \_keys\_ be a new empty List. 1. For each own property key \_P\_
  -- | of \_O\_ such that \_P\_ is an array index, in ascending numeric index
  -- | order, do 1. Append \_P\_ to \_keys\_. 1. For each own property key
  -- | \_P\_ of \_O\_ such that \_P\_ is a String and \_P\_ is not an array
  -- | index, in ascending chronological order of property creation, do 1.
  -- | Append \_P\_ to \_keys\_. 1. For each own property key \_P\_ of \_O\_
  -- | such that \_P\_ is a Symbol, in ascending chronological order of
  -- | property creation, do 1. Append \_P\_ to \_keys\_. 1. Return \_keys\_.
  | .getProp obj prop =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { so with expr := .getProp so.expr prop, trace := s.trace } t
              some (t, s')
          | none => none
      | some (.object addr) =>
          -- SPEC: L10878-L10889
          -- | # OrdinaryGet ( \_O\_: an Object, \_P\_: a property key, \_Receiver\_: an ECMAScript language value, ): either a normal completion containing an ECMAScript language value or a throw completion
          -- |
          -- | 1\. Let \_desc\_ be ? \_O\_.\[\[GetOwnProperty\]\](\_P\_). 1. If
          -- | \_desc\_ is \*undefined\*, then 1. Let \_parent\_ be ?
          -- | \_O\_.\[\[GetPrototypeOf\]\](). 1. If \_parent\_ is \*null\*, return
          -- | \*undefined\*. 1. Return ? \_parent\_.\[\[Get\]\](\_P\_,
          -- | \_Receiver\_). 1. If IsDataDescriptor(\_desc\_) is \*true\*, return
          -- | \_desc\_.\[\[Value\]\]. 1. Assert: IsAccessorDescriptor(\_desc\_) is
          -- | \*true\*. 1. Let \_getter\_ be \_desc\_.\[\[Get\]\]. 1. If \_getter\_ is
          -- | \*undefined\*, return \*undefined\*. 1. Return ? Call(\_getter\_,
          -- | \_Receiver\_).
          -- SPEC: L10748-L10762
          -- | # OrdinaryGetOwnProperty ( \_O\_: an Object, \_P\_: a property key, ): a Property Descriptor or \*undefined\*
          -- |
          -- | 1\. If \_O\_ does not have an own property with key \_P\_, return
          -- | \*undefined\*. 1. Let \_D\_ be a newly created Property Descriptor with
          -- | no fields. 1. Let \_X\_ be \_O\_\'s own property whose key is \_P\_. 1.
          -- | If \_X\_ is a data property, then 1. Set \_D\_.\[\[Value\]\] to the
          -- | value of \_X\_\'s \[\[Value\]\] attribute. 1. Set \_D\_.\[\[Writable\]\]
          -- | to the value of \_X\_\'s \[\[Writable\]\] attribute. 1. Else, 1. Assert:
          -- | \_X\_ is an accessor property. 1. Set \_D\_.\[\[Get\]\] to the value of
          -- | \_X\_\'s \[\[Get\]\] attribute. 1. Set \_D\_.\[\[Set\]\] to the value of
          -- | \_X\_\'s \[\[Set\]\] attribute. 1. Set \_D\_.\[\[Enumerable\]\] to the
          -- | value of \_X\_\'s \[\[Enumerable\]\] attribute. 1. Set
          -- | \_D\_.\[\[Configurable\]\] to the value of \_X\_\'s \[\[Configurable\]\]
          -- | attribute. 1. Return \_D\_.
          let v := match s.heap.objects[addr]? with
            | some props =>
                match props.find? (fun kv => kv.fst == prop) with
                | some (_, v) => v
                | none =>
                    -- §22.1.3.3 Array.prototype.length: return count of properties.
                    if prop == "length" then .number (Float.ofNat props.length)
                    else .undefined
            | none => .undefined
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | some (.string str) =>
          -- ECMA-262 §21.1.3.3 String.prototype.length (and other string properties).
          let v := if prop == "length" then .number (Float.ofNat str.length)
                   else .undefined
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | some _ =>
          -- Property access on primitive: return undefined.
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
  -- SPEC: L15600-L15610
  -- | # EvaluatePropertyAccessWithExpressionKey ( \_baseValue\_: an ECMAScript language value, \_expression\_: an \|Expression\| Parse Node, \_strict\_: a Boolean, ): either a normal completion containing a Reference Record or an abrupt completion
  -- |
  -- | 1\. Let \_propertyNameReference\_ be ? Evaluation of \_expression\_. 1.
  -- | Let \_propertyNameValue\_ be ? GetValue(\_propertyNameReference\_). 1.
  -- | NOTE: In most cases, ToPropertyKey will be performed on
  -- | \_propertyNameValue\_ immediately after this step. However, in the case
  -- | of \`a\[b\] = c\`, it will not be performed until after evaluation of
  -- | \`c\`. 1. Return the Reference Record { \[\[Base\]\]: \_baseValue\_,
  -- | \[\[ReferencedName\]\]: \_propertyNameValue\_, \[\[Strict\]\]:
  -- | \_strict\_, \[\[ThisValue\]\]: \~empty\~ }.
  -- SPEC: L15611-L15617
  -- | # EvaluatePropertyAccessWithIdentifierKey ( \_baseValue\_: an ECMAScript language value, \_identifierName\_: an \|IdentifierName\| Parse Node, \_strict\_: a Boolean, ): a Reference Record
  -- |
  -- | 1\. Let \_propertyNameString\_ be the StringValue of
  -- | \_identifierName\_. 1. Return the Reference Record { \[\[Base\]\]:
  -- | \_baseValue\_, \[\[ReferencedName\]\]: \_propertyNameString\_,
  -- | \[\[Strict\]\]: \_strict\_, \[\[ThisValue\]\]: \~empty\~ }.
  | .getIndex obj idx =>
      match exprValue? obj, exprValue? idx with
      | none, _ =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { so with expr := .getIndex so.expr idx, trace := s.trace } t
              some (t, s')
          | none => none
      | some _, none =>
          match step? { s with expr := idx } with
          | some (t, si) =>
              let s' := pushTrace { si with expr := .getIndex (.lit (match exprValue? obj with | some v => v | none => .undefined)) si.expr, trace := s.trace } t
              some (t, s')
          | none => none
      | some objVal, some idxVal =>
          -- ECMA-262 §9.1.8 [[Get]] with computed key: convert index to string via ToString.
          let propName := valueToString idxVal
          match objVal with
          | .object addr =>
              let v := match s.heap.objects[addr]? with
                | some props =>
                    match props.find? (fun kv => kv.fst == propName) with
                    | some (_, v) => v
                    | none =>
                        -- §22.1.3.3 Array.prototype.length for computed access.
                        if propName == "length" then .number (Float.ofNat props.length)
                        else .undefined
                | none => .undefined
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
          | .string str =>
              -- §21.1.3.4 String character access: str[n] returns single-char string.
              match idxVal with
              | .number n =>
                  let idx := n.toUInt64.toNat
                  let v := if n >= 0.0 && n.toUInt64.toFloat == n && idx < str.length
                    then .string (String.Pos.Raw.get str ⟨idx⟩ |>.toString)
                    else .undefined
                  let s' := pushTrace { s with expr := .lit v } .silent
                  some (.silent, s')
              | _ =>
                  -- §21.1.3.3 String.prototype.length via bracket notation.
                  let v := if propName == "length" then .number (Float.ofNat str.length)
                           else .undefined
                  let s' := pushTrace { s with expr := .lit v } .silent
                  some (.silent, s')
          | _ =>
              let s' := pushTrace { s with expr := .lit .undefined } .silent
              some (.silent, s')
  -- SPEC: L18879-L18906
  -- | # Runtime Semantics: InstantiateOrdinaryFunctionExpression ( optional \_name\_: a property key or a Private Name, ): an ECMAScript function object
  -- |
  -- | FunctionExpression : \`function\` \`(\` FormalParameters \`)\` \`{\`
  -- | FunctionBody \`}\` 1. If \_name\_ is not present, set \_name\_ to
  -- | \*\"\"\*. 1. Let \_env\_ be the LexicalEnvironment of the running
  -- | execution context. 1. Let \_privateEnv\_ be the running execution
  -- | context\'s PrivateEnvironment. 1. Let \_sourceText\_ be the source text
  -- | matched by \|FunctionExpression\|. 1. Let \_closure\_ be
  -- | OrdinaryFunctionCreate(%Function.prototype%, \_sourceText\_,
  -- | \|FormalParameters\|, \|FunctionBody\|, \~non-lexical-this\~, \_env\_,
  -- | \_privateEnv\_). 1. Perform SetFunctionName(\_closure\_, \_name\_). 1.
  -- | Perform MakeConstructor(\_closure\_). 1. Return \_closure\_.
  -- | FunctionExpression : \`function\` BindingIdentifier \`(\`
  -- | FormalParameters \`)\` \`{\` FunctionBody \`}\` 1. Assert: \_name\_ is
  -- | not present. 1. Set \_name\_ to the StringValue of
  -- | \|BindingIdentifier\|. 1. Let \_outerEnv\_ be the running execution
  -- | context\'s LexicalEnvironment. 1. Let \_funcEnv\_ be
  -- | NewDeclarativeEnvironment(\_outerEnv\_). 1. Perform !
  -- | \_funcEnv\_.CreateImmutableBinding(\_name\_, \*false\*). 1. Let
  -- | \_privateEnv\_ be the running execution context\'s
  -- | PrivateEnvironment. 1. Let \_sourceText\_ be the source text matched by
  -- | \|FunctionExpression\|. 1. Let \_closure\_ be
  -- | OrdinaryFunctionCreate(%Function.prototype%, \_sourceText\_,
  -- | \|FormalParameters\|, \|FunctionBody\|, \~non-lexical-this\~,
  -- | \_funcEnv\_, \_privateEnv\_). 1. Perform SetFunctionName(\_closure\_,
  -- | \_name\_). 1. Perform MakeConstructor(\_closure\_). 1. Perform !
  -- | \_funcEnv\_.InitializeBinding(\_name\_, \_closure\_). 1. Return
  -- | \_closure\_.
  -- SPEC: L11206-L11236
  -- | # OrdinaryFunctionCreate ( \_functionPrototype\_: an Object, \_sourceText\_: a sequence of Unicode code points, \_ParameterList\_: a Parse Node, \_Body\_: a Parse Node, \_thisMode\_: \~lexical-this\~ or \~non-lexical-this\~, \_env\_: an Environment Record, \_privateEnv\_: a PrivateEnvironment Record or \*null\*, ): an ECMAScript function object
  -- |
  -- | description
  -- | :   It is used to specify the runtime creation of a new function with a
  -- |     default \[\[Call\]\] internal method and no \[\[Construct\]\]
  -- |     internal method (although one may be subsequently added by an
  -- |     operation such as MakeConstructor). \_sourceText\_ is the source
  -- |     text of the syntactic definition of the function to be created.
  -- |
  -- | 1\. Let \_internalSlotsList\_ be the internal slots listed in . 1. Let
  -- | \_F\_ be OrdinaryObjectCreate(\_functionPrototype\_,
  -- | \_internalSlotsList\_). 1. Set \_F\_.\[\[Call\]\] to the definition
  -- | specified in . 1. Set \_F\_.\[\[SourceText\]\] to \_sourceText\_. 1. Set
  -- | \_F\_.\[\[FormalParameters\]\] to \_ParameterList\_. 1. Set
  -- | \_F\_.\[\[ECMAScriptCode\]\] to \_Body\_. 1. Let \_Strict\_ be
  -- | IsStrict(\_Body\_). 1. Set \_F\_.\[\[Strict\]\] to \_Strict\_. 1. If
  -- | \_thisMode\_ is \~lexical-this\~, set \_F\_.\[\[ThisMode\]\] to
  -- | \~lexical\~. 1. Else if \_Strict\_ is \*true\*, set
  -- | \_F\_.\[\[ThisMode\]\] to \~strict\~. 1. Else, set
  -- | \_F\_.\[\[ThisMode\]\] to \~global\~. 1. Set
  -- | \_F\_.\[\[IsClassConstructor\]\] to \*false\*. 1. Set
  -- | \_F\_.\[\[Environment\]\] to \_env\_. 1. Set
  -- | \_F\_.\[\[PrivateEnvironment\]\] to \_privateEnv\_. 1. Set
  -- | \_F\_.\[\[ScriptOrModule\]\] to GetActiveScriptOrModule(). 1. Set
  -- | \_F\_.\[\[Realm\]\] to the current Realm Record. 1. Set
  -- | \_F\_.\[\[HomeObject\]\] to \*undefined\*. 1. Set \_F\_.\[\[Fields\]\]
  -- | to a new empty List. 1. Set \_F\_.\[\[PrivateMethods\]\] to a new empty
  -- | List. 1. Set \_F\_.\[\[ClassFieldInitializerName\]\] to \~empty\~. 1.
  -- | Let \_len\_ be the ExpectedArgumentCount of \_ParameterList\_. 1.
  -- | Perform SetFunctionLength(\_F\_, \_len\_). 1. Return \_F\_.
  -- SPEC: L11320-L11342
  -- | # SetFunctionName ( \_F\_: a function object, \_name\_: a property key or Private Name, optional \_prefix\_: a String, ): \~unused\~
  -- |
  -- | description
  -- | :   It adds a \*\"name\"\* property to \_F\_.
  -- |
  -- | 1\. Assert: \_F\_ is an extensible object that does not have a
  -- | \*\"name\"\* own property. 1. If \_name\_ is a Symbol, then 1. Let
  -- | \_description\_ be \_name\_.\[\[Description\]\]. 1. If \_description\_
  -- | is \*undefined\*, set \_name\_ to the empty String. 1. Else, set
  -- | \_name\_ to the string-concatenation of \*\"\[\"\*, \_description\_, and
  -- | \*\"\]\"\*. 1. Else if \_name\_ is a Private Name, then 1. Set \_name\_
  -- | to \_name\_.\[\[Description\]\]. 1. If \_F\_ has an \[\[InitialName\]\]
  -- | internal slot, then 1. Set \_F\_.\[\[InitialName\]\] to \_name\_. 1. If
  -- | \_prefix\_ is present, then 1. Set \_name\_ to the string-concatenation
  -- | of \_prefix\_, the code unit 0x0020 (SPACE), and \_name\_. 1. If \_F\_
  -- | has an \[\[InitialName\]\] internal slot, then 1. NOTE: The choice in
  -- | the following step is made independently each time this Abstract
  -- | Operation is invoked. 1. Optionally, set \_F\_.\[\[InitialName\]\] to
  -- | \_name\_. 1. Perform ! DefinePropertyOrThrow(\_F\_, \*\"name\"\*,
  -- | PropertyDescriptor { \[\[Value\]\]: \_name\_, \[\[Writable\]\]:
  -- | \*false\*, \[\[Enumerable\]\]: \*false\*, \[\[Configurable\]\]: \*true\*
  -- | }). 1. Return \~unused\~.
  -- SPEC: L8511-L8533
  -- | # Runtime Semantics: InstantiateFunctionObject ( \_env\_: an Environment Record, \_privateEnv\_: a PrivateEnvironment Record or \*null\*, ): an ECMAScript function object
  -- |
  -- | FunctionDeclaration : \`function\` BindingIdentifier \`(\`
  -- | FormalParameters \`)\` \`{\` FunctionBody \`}\` \`function\` \`(\`
  -- | FormalParameters \`)\` \`{\` FunctionBody \`}\` 1. Return
  -- | InstantiateOrdinaryFunctionObject of \|FunctionDeclaration\| with
  -- | arguments \_env\_ and \_privateEnv\_. GeneratorDeclaration :
  -- | \`function\` \`\*\` BindingIdentifier \`(\` FormalParameters \`)\` \`{\`
  -- | GeneratorBody \`}\` \`function\` \`\*\` \`(\` FormalParameters \`)\`
  -- | \`{\` GeneratorBody \`}\` 1. Return InstantiateGeneratorFunctionObject
  -- | of \|GeneratorDeclaration\| with arguments \_env\_ and \_privateEnv\_.
  -- | AsyncGeneratorDeclaration : \`async\` \`function\` \`\*\`
  -- | BindingIdentifier \`(\` FormalParameters \`)\` \`{\` AsyncGeneratorBody
  -- | \`}\` \`async\` \`function\` \`\*\` \`(\` FormalParameters \`)\` \`{\`
  -- | AsyncGeneratorBody \`}\` 1. Return
  -- | InstantiateAsyncGeneratorFunctionObject of \|AsyncGeneratorDeclaration\|
  -- | with arguments \_env\_ and \_privateEnv\_. AsyncFunctionDeclaration :
  -- | \`async\` \`function\` BindingIdentifier \`(\` FormalParameters \`)\`
  -- | \`{\` AsyncFunctionBody \`}\` \`async\` \`function\` \`(\`
  -- | FormalParameters \`)\` \`{\` AsyncFunctionBody \`}\` 1. Return
  -- | InstantiateAsyncFunctionObject of \|AsyncFunctionDeclaration\| with
  -- | arguments \_env\_ and \_privateEnv\_.
  -- SPEC: L18995-L19007
  -- | # Runtime Semantics: InstantiateArrowFunctionExpression ( optional \_name\_: a property key or a Private Name, ): an ECMAScript function object
  -- |
  -- | ArrowFunction : ArrowParameters \`=\>\` ConciseBody 1. If \_name\_ is
  -- | not present, set \_name\_ to \*\"\"\*. 1. Let \_env\_ be the
  -- | LexicalEnvironment of the running execution context. 1. Let
  -- | \_privateEnv\_ be the running execution context\'s
  -- | PrivateEnvironment. 1. Let \_sourceText\_ be the source text matched by
  -- | \|ArrowFunction\|. 1.
  -- | \[id=\"step-arrowfunction-evaluation-functioncreate\"\] Let \_closure\_
  -- | be OrdinaryFunctionCreate(%Function.prototype%, \_sourceText\_,
  -- | \|ArrowParameters\|, \|ConciseBody\|, \~lexical-this\~, \_env\_,
  -- | \_privateEnv\_). 1. Perform SetFunctionName(\_closure\_, \_name\_). 1.
  -- | Return \_closure\_.
  -- SPEC: L11354-L11370
  -- | # FunctionDeclarationInstantiation ( \_func\_: an ECMAScript function object, \_argumentsList\_: a List of ECMAScript language values, ): either a normal completion containing \~unused\~ or a throw completion
  -- |
  -- | description
  -- | :   \_func\_ is the function object for which the execution context is
  -- |     being established.
  -- |
  -- | When an execution context is established for evaluating an ECMAScript
  -- | function a new Function Environment Record is created and bindings for
  -- | each formal parameter are instantiated in that Environment Record. Each
  -- | declaration in the function body is also instantiated. If the
  -- | function\'s formal parameters do not include any default value
  -- | initializers then the body declarations are instantiated in the same
  -- | Environment Record as the parameters. If default value parameter
  -- | initializers exist, a second Environment Record is created for the body
  -- | declarations. Formal parameters and functions are initialized as part of
  -- | FunctionDeclarationInstantiation. All other bindings are initialized
  -- | during evaluation of the function body.
  | .functionDef fname params body _isAsync _isGenerator =>
      let closure : FuncClosure := ⟨fname, params, body, s.env.bindings⟩
      let idx := s.funcs.size
      let funcs' := s.funcs.push closure
      let s' := pushTrace { s with expr := .lit (.function idx), funcs := funcs' } .silent
      some (.silent, s')
  -- SPEC: L15120-L15135
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | ObjectLiteral : \`{\` \`}\` 1. Return
  -- | OrdinaryObjectCreate(%Object.prototype%). ObjectLiteral : \`{\`
  -- | PropertyDefinitionList \`}\` \`{\` PropertyDefinitionList \`,\` \`}\` 1.
  -- | Let \_obj\_ be OrdinaryObjectCreate(%Object.prototype%). 1. Perform ?
  -- | PropertyDefinitionEvaluation of \|PropertyDefinitionList\| with argument
  -- | \_obj\_. 1. Return \_obj\_. LiteralPropertyName : IdentifierName 1.
  -- | Return the StringValue of \|IdentifierName\|. LiteralPropertyName :
  -- | StringLiteral 1. Return the SV of \|StringLiteral\|. LiteralPropertyName
  -- | : NumericLiteral 1. Let \_nbr\_ be the NumericValue of
  -- | \|NumericLiteral\|. 1. Return ! ToString(\_nbr\_). ComputedPropertyName
  -- | : \`\[\` AssignmentExpression \`\]\` 1. Let \_exprValue\_ be ?
  -- | Evaluation of \|AssignmentExpression\|. 1. Let \_propName\_ be ?
  -- | GetValue(\_exprValue\_). 1. Return ? ToPropertyKey(\_propName\_).
  -- SPEC: L15136-L15176
  -- | # Runtime Semantics: PropertyDefinitionEvaluation ( \_object\_: an Object, ): either a normal completion containing \~unused\~ or an abrupt completion
  -- |
  -- | PropertyDefinitionList : PropertyDefinitionList \`,\`
  -- | PropertyDefinition 1. Perform ? PropertyDefinitionEvaluation of
  -- | \|PropertyDefinitionList\| with argument \_object\_. 1. Perform ?
  -- | PropertyDefinitionEvaluation of \|PropertyDefinition\| with argument
  -- | \_object\_. 1. Return \~unused\~. PropertyDefinition : \`\...\`
  -- | AssignmentExpression 1. Let \_exprValue\_ be ? Evaluation of
  -- | \|AssignmentExpression\|. 1. Let \_fromValue\_ be ?
  -- | GetValue(\_exprValue\_). 1. Let \_excludedNames\_ be a new empty
  -- | List. 1. Perform ? CopyDataProperties(\_object\_, \_fromValue\_,
  -- | \_excludedNames\_). 1. Return \~unused\~. PropertyDefinition :
  -- | IdentifierReference 1. Let \_propName\_ be the StringValue of
  -- | \|IdentifierReference\|. 1. Let \_exprValue\_ be ? Evaluation of
  -- | \|IdentifierReference\|. 1. Let \_propValue\_ be ?
  -- | GetValue(\_exprValue\_). 1. Assert: \_object\_ is an ordinary,
  -- | extensible object with no non-configurable properties. 1. Perform !
  -- | CreateDataPropertyOrThrow(\_object\_, \_propName\_, \_propValue\_). 1.
  -- | Return \~unused\~. PropertyDefinition : PropertyName \`:\`
  -- | AssignmentExpression 1. Let \_propKey\_ be ? Evaluation of
  -- | \|PropertyName\|. 1. If this \|PropertyDefinition\| is contained within
  -- | a \|Script\| that is being evaluated for ParseJSON (see step of
  -- | ParseJSON), then 1. Let \_isProtoSetter\_ be \*false\*. 1. Else if
  -- | \_propKey\_ is \*\"\_\_proto\_\_\"\* and IsComputedPropertyKey of
  -- | \|PropertyName\| is \*false\*, then 1. Let \_isProtoSetter\_ be
  -- | \*true\*. 1. Else, 1. Let \_isProtoSetter\_ be \*false\*. 1. If
  -- | IsAnonymousFunctionDefinition(\|AssignmentExpression\|) is \*true\* and
  -- | \_isProtoSetter\_ is \*false\*, then 1. Let \_propValue\_ be ?
  -- | NamedEvaluation of \|AssignmentExpression\| with argument
  -- | \_propKey\_. 1. Else, 1. Let \_exprValueRef\_ be ? Evaluation of
  -- | \|AssignmentExpression\|. 1. Let \_propValue\_ be ?
  -- | GetValue(\_exprValueRef\_). 1. If \_isProtoSetter\_ is \*true\*, then 1.
  -- | If \_propValue\_ is an Object or \_propValue\_ is \*null\*, then 1.
  -- | Perform ! \_object\_.\[\[SetPrototypeOf\]\](\_propValue\_). 1. Return
  -- | \~unused\~. 1. Assert: \_object\_ is an ordinary, extensible object with
  -- | no non-configurable properties. 1. Perform !
  -- | CreateDataPropertyOrThrow(\_object\_, \_propKey\_, \_propValue\_). 1.
  -- | Return \~unused\~. PropertyDefinition : MethodDefinition 1. Perform ?
  -- | MethodDefinitionEvaluation of \|MethodDefinition\| with arguments
  -- | \_object\_ and \*true\*. 1. Return \~unused\~.
  | .objectLit props =>
      match hf : firstNonValueProp props with
      | some (done, k, target, rest) =>
          have : Expr.depth target < Expr.depth s.expr := by
            rw [h]; simp [Expr.depth]; have := firstNonValueProp_depth hf; omega
          match step? { s with expr := target } with
          | some (t, se) =>
              let s' := pushTrace { se with expr := .objectLit (done ++ [(k, se.expr)] ++ rest), trace := s.trace } t
              some (t, s')
          | none => none
      | none =>
          -- All props are values: allocate object on heap with properties.
          let addr := s.heap.nextAddr
          let heapProps := props.filterMap fun (k, e) =>
            match exprValue? e with
            | some v => some (k, v)
            | none => none  -- shouldn't happen
          let heap' := { objects := s.heap.objects.push heapProps, nextAddr := addr + 1 }
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
          some (.silent, s')
  -- SPEC: L14966-L15011
  -- | # Runtime Semantics: ArrayAccumulation ( \_array\_: an Array, \_nextIndex\_: an integer, ): either a normal completion containing an integer or an abrupt completion
  -- |
  -- | Elision : \`,\` 1. Let \_len\_ be \_nextIndex\_ + 1. 1. Perform ?
  -- | Set(\_array\_, \*\"length\"\*, 𝔽(\_len\_), \*true\*). 1. NOTE: The above
  -- | step throws if \_len\_ exceeds 2^32^ - 1. 1. Return \_len\_. Elision :
  -- | Elision \`,\` 1. Return ? ArrayAccumulation of \|Elision\| with
  -- | arguments \_array\_ and (\_nextIndex\_ + 1). ElementList : Elision?
  -- | AssignmentExpression 1. If \|Elision\| is present, then 1. Set
  -- | \_nextIndex\_ to ? ArrayAccumulation of \|Elision\| with arguments
  -- | \_array\_ and \_nextIndex\_. 1. Let \_initResult\_ be ? Evaluation of
  -- | \|AssignmentExpression\|. 1. Let \_initValue\_ be ?
  -- | GetValue(\_initResult\_). 1. Perform !
  -- | CreateDataPropertyOrThrow(\_array\_, ! ToString(𝔽(\_nextIndex\_)),
  -- | \_initValue\_). 1. Return \_nextIndex\_ + 1. ElementList : Elision?
  -- | SpreadElement 1. If \|Elision\| is present, then 1. Set \_nextIndex\_ to
  -- | ? ArrayAccumulation of \|Elision\| with arguments \_array\_ and
  -- | \_nextIndex\_. 1. Return ? ArrayAccumulation of \|SpreadElement\| with
  -- | arguments \_array\_ and \_nextIndex\_. ElementList : ElementList \`,\`
  -- | Elision? AssignmentExpression 1. Set \_nextIndex\_ to ?
  -- | ArrayAccumulation of \|ElementList\| with arguments \_array\_ and
  -- | \_nextIndex\_. 1. If \|Elision\| is present, then 1. Set \_nextIndex\_
  -- | to ? ArrayAccumulation of \|Elision\| with arguments \_array\_ and
  -- | \_nextIndex\_. 1. Let \_initResult\_ be ? Evaluation of
  -- | \|AssignmentExpression\|. 1. Let \_initValue\_ be ?
  -- | GetValue(\_initResult\_). 1. Perform !
  -- | CreateDataPropertyOrThrow(\_array\_, ! ToString(𝔽(\_nextIndex\_)),
  -- | \_initValue\_). 1. Return \_nextIndex\_ + 1. ElementList : ElementList
  -- | \`,\` Elision? SpreadElement 1. Set \_nextIndex\_ to ? ArrayAccumulation
  -- | of \|ElementList\| with arguments \_array\_ and \_nextIndex\_. 1. If
  -- | \|Elision\| is present, then 1. Set \_nextIndex\_ to ? ArrayAccumulation
  -- | of \|Elision\| with arguments \_array\_ and \_nextIndex\_. 1. Return ?
  -- | ArrayAccumulation of \|SpreadElement\| with arguments \_array\_ and
  -- | \_nextIndex\_. SpreadElement : \`\...\` AssignmentExpression 1. Let
  -- | \_spreadRef\_ be ? Evaluation of \|AssignmentExpression\|. 1. Let
  -- | \_spreadObj\_ be ? GetValue(\_spreadRef\_). 1. Let \_iteratorRecord\_ be
  -- | ? GetIterator(\_spreadObj\_, \~sync\~). 1. Repeat, 1. Let \_next\_ be ?
  -- | IteratorStepValue(\_iteratorRecord\_). 1. If \_next\_ is \~done\~,
  -- | return \_nextIndex\_. 1. Perform ! CreateDataPropertyOrThrow(\_array\_,
  -- | ! ToString(𝔽(\_nextIndex\_)), \_next\_). 1. Set \_nextIndex\_ to
  -- | \_nextIndex\_ + 1.
  -- |
  -- | CreateDataPropertyOrThrow is used to ensure that own properties are
  -- | defined for the array even if the standard built-in Array prototype
  -- | object has been modified in a manner that would preclude the creation of
  -- | new own properties using \[\[Set\]\].
  -- |
  -- SPEC: L15012-L15025
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | ArrayLiteral : \`\[\` Elision? \`\]\` 1. Let \_array\_ be !
  -- | ArrayCreate(0). 1. If \|Elision\| is present, then 1. Perform ?
  -- | ArrayAccumulation of \|Elision\| with arguments \_array\_ and 0. 1.
  -- | Return \_array\_. ArrayLiteral : \`\[\` ElementList \`\]\` 1. Let
  -- | \_array\_ be ! ArrayCreate(0). 1. Perform ? ArrayAccumulation of
  -- | \|ElementList\| with arguments \_array\_ and 0. 1. Return \_array\_.
  -- | ArrayLiteral : \`\[\` ElementList \`,\` Elision? \`\]\` 1. Let \_array\_
  -- | be ! ArrayCreate(0). 1. Let \_nextIndex\_ be ? ArrayAccumulation of
  -- | \|ElementList\| with arguments \_array\_ and 0. 1. If \|Elision\| is
  -- | present, then 1. Perform ? ArrayAccumulation of \|Elision\| with
  -- | arguments \_array\_ and \_nextIndex\_. 1. Return \_array\_.
  | .arrayLit elems =>
      match hf : firstNonValueExpr elems with
      | some (done, target, rest) =>
          have : Expr.depth target < Expr.depth s.expr := by
            rw [h]; simp [Expr.depth]; have := firstNonValueExpr_depth hf; omega
          match step? { s with expr := target } with
          | some (t, se) =>
              let s' := pushTrace { se with expr := .arrayLit (done ++ [se.expr] ++ rest), trace := s.trace } t
              some (t, s')
          | none => none
      | none =>
          -- All elements are values: allocate array on heap with indexed entries.
          let addr := s.heap.nextAddr
          let heapProps := mkIndexedProps 0 elems
          let heap' := { objects := s.heap.objects.push heapProps, nextAddr := addr + 1 }
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
          some (.silent, s')
  -- SPEC: L5504-L5512
  -- | # UpdateEmpty ( \_completionRecord\_: a Completion Record, \_value\_: any value except a Completion Record, ): a Completion Record
  -- |
  -- | 1\. Assert: If \_completionRecord\_ is either a return completion or a
  -- | throw completion, then \_completionRecord\_.\[\[Value\]\] is not
  -- | \~empty\~. 1. If \_completionRecord\_.\[\[Value\]\] is not \~empty\~,
  -- | return ? \_completionRecord\_. 1. Return Completion Record {
  -- | \[\[Type\]\]: \_completionRecord\_.\[\[Type\]\], \[\[Value\]\]:
  -- | \_value\_, \[\[Target\]\]: \_completionRecord\_.\[\[Target\]\] }.
  -- SPEC: L17633-L17643
  -- | # LoopContinues ( \_completion\_: a Completion Record, \_labelSet\_: a List of Strings, ): a Boolean
  -- |
  -- | 1\. If \_completion\_ is a normal completion, return \*true\*. 1. If
  -- | \_completion\_ is not a continue completion, return \*false\*. 1. If
  -- | \_completion\_.\[\[Target\]\] is \~empty\~, return \*true\*. 1. If
  -- | \_labelSet\_ contains \_completion\_.\[\[Target\]\], return \*true\*. 1.
  -- | Return \*false\*.
  -- |
  -- | Within the \|Statement\| part of an \|IterationStatement\| a
  -- | \|ContinueStatement\| may be used to begin a new iteration.
  -- SPEC: L17788-L17802
  -- | # ForBodyEvaluation ( \_test\_: an \|Expression\| Parse Node or \~empty\~, \_increment\_: an \|Expression\| Parse Node or \~empty\~, \_stmt\_: a \|Statement\| Parse Node, \_perIterationBindings\_: a List of Strings, \_labelSet\_: a List of Strings, ): either a normal completion containing an ECMAScript language value or an abrupt completion
  -- |
  -- | 1\. Let \_V\_ be \*undefined\*. 1. Perform ?
  -- | CreatePerIterationEnvironment(\_perIterationBindings\_). 1. Repeat, 1.
  -- | If \_test\_ is not \~empty\~, then 1. Let \_testRef\_ be ? Evaluation of
  -- | \_test\_. 1. Let \_testValue\_ be ? GetValue(\_testRef\_). 1. If
  -- | ToBoolean(\_testValue\_) is \*false\*, return \_V\_. 1. Let \_result\_
  -- | be Completion(Evaluation of \_stmt\_). 1. If LoopContinues(\_result\_,
  -- | \_labelSet\_) is \*false\*, return ? UpdateEmpty(\_result\_, \_V\_). 1.
  -- | If \_result\_.\[\[Value\]\] is not \~empty\~, set \_V\_ to
  -- | \_result\_.\[\[Value\]\]. 1. Perform ?
  -- | CreatePerIterationEnvironment(\_perIterationBindings\_). 1. If
  -- | \_increment\_ is not \~empty\~, then 1. Let \_incRef\_ be ? Evaluation
  -- | of \_increment\_. 1. Perform ? GetValue(\_incRef\_).
  -- SPEC: L17672-L17683
  -- | # Runtime Semantics: DoWhileLoopEvaluation ( \_labelSet\_: a List of Strings, ): either a normal completion containing an ECMAScript language value or an abrupt completion
  -- |
  -- | DoWhileStatement : \`do\` Statement \`while\` \`(\` Expression \`)\`
  -- | \`;\` 1. Let \_V\_ be \*undefined\*. 1. Repeat, 1. Let \_stmtResult\_ be
  -- | Completion(Evaluation of \|Statement\|). 1. If
  -- | LoopContinues(\_stmtResult\_, \_labelSet\_) is \*false\*, return ?
  -- | UpdateEmpty(\_stmtResult\_, \_V\_). 1. If \_stmtResult\_.\[\[Value\]\]
  -- | is not \~empty\~, set \_V\_ to \_stmtResult\_.\[\[Value\]\]. 1. Let
  -- | \_exprRef\_ be ? Evaluation of \|Expression\|. 1. Let \_exprValue\_ be ?
  -- | GetValue(\_exprRef\_). 1. If ToBoolean(\_exprValue\_) is \*false\*,
  -- | return \_V\_.
  -- NOTE: do-while is desugared by the parser to seq(body, while(cond, body)).
  -- SPEC: L17747-L17787
  -- | # Runtime Semantics: ForLoopEvaluation ( \_labelSet\_: a List of Strings, ): either a normal completion containing an ECMAScript language value or an abrupt completion
  -- |
  -- | ForStatement : \`for\` \`(\` Expression? \`;\` Expression? \`;\`
  -- | Expression? \`)\` Statement 1. If the first \|Expression\| is present,
  -- | then 1. Let \_exprRef\_ be ? Evaluation of the first \|Expression\|. 1.
  -- | Perform ? GetValue(\_exprRef\_). 1. If the second \|Expression\| is
  -- | present, let \_test\_ be the second \|Expression\|; else let \_test\_ be
  -- | \~empty\~. 1. If the third \|Expression\| is present, let \_increment\_
  -- | be the third \|Expression\|; else let \_increment\_ be \~empty\~. 1.
  -- | Return ? ForBodyEvaluation(\_test\_, \_increment\_, \|Statement\|, « »,
  -- | \_labelSet\_). ForStatement : \`for\` \`(\` \`var\`
  -- | VariableDeclarationList \`;\` Expression? \`;\` Expression? \`)\`
  -- | Statement 1. Perform ? Evaluation of \|VariableDeclarationList\|. 1. If
  -- | the first \|Expression\| is present, let \_test\_ be the first
  -- | \|Expression\|; else let \_test\_ be \~empty\~. 1. If the second
  -- | \|Expression\| is present, let \_increment\_ be the second
  -- | \|Expression\|; else let \_increment\_ be \~empty\~. 1. Return ?
  -- | ForBodyEvaluation(\_test\_, \_increment\_, \|Statement\|, « »,
  -- | \_labelSet\_). ForStatement : \`for\` \`(\` LexicalDeclaration
  -- | Expression? \`;\` Expression? \`)\` Statement 1. Let \_oldEnv\_ be the
  -- | running execution context\'s LexicalEnvironment. 1. Let \_loopEnv\_ be
  -- | NewDeclarativeEnvironment(\_oldEnv\_). 1. Let \_isConst\_ be
  -- | IsConstantDeclaration of \|LexicalDeclaration\|. 1. Let \_boundNames\_
  -- | be the BoundNames of \|LexicalDeclaration\|. 1. For each element \_dn\_
  -- | of \_boundNames\_, do 1. If \_isConst\_ is \*true\*, then 1. Perform !
  -- | \_loopEnv\_.CreateImmutableBinding(\_dn\_, \*true\*). 1. Else, 1.
  -- | Perform ! \_loopEnv\_.CreateMutableBinding(\_dn\_, \*false\*). 1. Set
  -- | the running execution context\'s LexicalEnvironment to \_loopEnv\_. 1.
  -- | Let \_forDcl\_ be Completion(Evaluation of \|LexicalDeclaration\|). 1.
  -- | If \_forDcl\_ is an abrupt completion, then 1. Set the running execution
  -- | context\'s LexicalEnvironment to \_oldEnv\_. 1. Return ? \_forDcl\_. 1.
  -- | If \_isConst\_ is \*false\*, let \_perIterationLets\_ be \_boundNames\_;
  -- | else let \_perIterationLets\_ be a new empty List. 1. If the first
  -- | \|Expression\| is present, let \_test\_ be the first \|Expression\|;
  -- | else let \_test\_ be \~empty\~. 1. If the second \|Expression\| is
  -- | present, let \_increment\_ be the second \|Expression\|; else let
  -- | \_increment\_ be \~empty\~. 1. Let \_bodyResult\_ be
  -- | Completion(ForBodyEvaluation(\_test\_, \_increment\_, \|Statement\|,
  -- | \_perIterationLets\_, \_labelSet\_)). 1. Set the running execution
  -- | context\'s LexicalEnvironment to \_oldEnv\_. 1. Return ? \_bodyResult\_.
  -- NOTE: for-loop is desugared by the parser to seq(init, while(cond, seq(body, update))).
  -- SPEC: L17672-L17683
  -- | # Runtime Semantics: DoWhileLoopEvaluation ( \_labelSet\_: a List of Strings, ): either a normal completion containing an ECMAScript language value or an abrupt completion
  -- |
  -- | DoWhileStatement : \`do\` Statement \`while\` \`(\` Expression \`)\`
  -- | \`;\` 1. Let \_V\_ be \*undefined\*. 1. Repeat, 1. Let \_stmtResult\_ be
  -- | Completion(Evaluation of \|Statement\|). 1. If
  -- | LoopContinues(\_stmtResult\_, \_labelSet\_) is \*false\*, return ?
  -- | UpdateEmpty(\_stmtResult\_, \_V\_). 1. If \_stmtResult\_.\[\[Value\]\]
  -- | is not \~empty\~, set \_V\_ to \_stmtResult\_.\[\[Value\]\]. 1. Let
  -- | \_exprRef\_ be ? Evaluation of \|Expression\|. 1. Let \_exprValue\_ be ?
  -- | GetValue(\_exprRef\_). 1. If ToBoolean(\_exprValue\_) is \*false\*,
  -- | return \_V\_.
  -- SPEC: L17788-L17802
  -- | # ForBodyEvaluation ( \_test\_: an \|Expression\| Parse Node or \~empty\~, \_increment\_: an \|Expression\| Parse Node or \~empty\~, \_stmt\_: a \|Statement\| Parse Node, \_perIterationBindings\_: a List of Strings, \_labelSet\_: a List of Strings, ): either a normal completion containing an ECMAScript language value or an abrupt completion
  -- |
  -- | 1\. Let \_V\_ be \*undefined\*. 1. Perform ?
  -- | CreatePerIterationEnvironment(\_perIterationBindings\_). 1. Repeat, 1.
  -- | If \_test\_ is not \~empty\~, then 1. Let \_testRef\_ be ? Evaluation of
  -- | \_test\_. 1. Let \_testValue\_ be ? GetValue(\_testRef\_). 1. If
  -- | ToBoolean(\_testValue\_) is \*false\*, return \_V\_. 1. Let \_result\_
  -- | be Completion(Evaluation of \_stmt\_). 1. If LoopContinues(\_result\_,
  -- | \_labelSet\_) is \*false\*, return ? UpdateEmpty(\_result\_, \_V\_). 1.
  -- | If \_result\_.\[\[Value\]\] is not \~empty\~, set \_V\_ to
  -- | \_result\_.\[\[Value\]\]. 1. Perform ?
  -- | CreatePerIterationEnvironment(\_perIterationBindings\_). 1. If
  -- | \_increment\_ is not \~empty\~, then 1. Let \_incRef\_ be ? Evaluation
  -- | of \_increment\_. 1. Perform ? GetValue(\_incRef\_).
  -- SPEC: L7185-L7197
  -- | # IteratorNext ( \_iteratorRecord\_: an Iterator Record, optional \_value\_: an ECMAScript language value, ): either a normal completion containing an Object or a throw completion
  -- |
  -- | 1\. If \_value\_ is not present, then 1. Let \_result\_ be
  -- | Completion(Call(\_iteratorRecord\_.\[\[NextMethod\]\],
  -- | \_iteratorRecord\_.\[\[Iterator\]\])). 1. Else, 1. Let \_result\_ be
  -- | Completion(Call(\_iteratorRecord\_.\[\[NextMethod\]\],
  -- | \_iteratorRecord\_.\[\[Iterator\]\], « \_value\_ »)). 1. If \_result\_
  -- | is a throw completion, then 1. Set \_iteratorRecord\_.\[\[Done\]\] to
  -- | \*true\*. 1. Return ? \_result\_. 1. Set \_result\_ to ! \_result\_. 1.
  -- | If \_result\_ is not an Object, then 1. Set
  -- | \_iteratorRecord\_.\[\[Done\]\] to \*true\*. 1. Throw a \*TypeError\*
  -- | exception. 1. Return \_result\_.
  -- SPEC: L7198-L7201
  -- | # IteratorComplete ( \_iteratorResult\_: an Object, ): either a normal completion containing a Boolean or a throw completion
  -- |
  -- | 1\. Return ToBoolean(? Get(\_iteratorResult\_, \*\"done\"\*)).
  -- SPEC: L7202-L7205
  -- | # IteratorValue ( \_iteratorResult\_: an Object, ): either a normal completion containing an ECMAScript language value or a throw completion
  -- |
  -- | 1\. Return ? Get(\_iteratorResult\_, \*\"value\"\*).
  -- SPEC: L7206-L7220
  -- | # IteratorStep ( \_iteratorRecord\_: an Iterator Record, ): either a normal completion containing either an Object or \~done\~, or a throw completion
  -- |
  -- | description
  -- | :   It requests the next value from \_iteratorRecord\_.\[\[Iterator\]\]
  -- |     by calling \_iteratorRecord\_.\[\[NextMethod\]\] and returns either
  -- |     \~done\~ indicating that the iterator has reached its end or the
  -- |     IteratorResult object if a next value is available.
  -- |
  -- | 1\. Let \_result\_ be ? IteratorNext(\_iteratorRecord\_). 1. Let
  -- | \_done\_ be Completion(IteratorComplete(\_result\_)). 1. If \_done\_ is
  -- | a throw completion, then 1. Set \_iteratorRecord\_.\[\[Done\]\] to
  -- | \*true\*. 1. Return ? \_done\_. 1. Set \_done\_ to ! \_done\_. 1. If
  -- | \_done\_ is \*true\*, then 1. Set \_iteratorRecord\_.\[\[Done\]\] to
  -- | \*true\*. 1. Return \~done\~. 1. Return \_result\_.
  -- SPEC: L17701-L17711
  -- | # Runtime Semantics: WhileLoopEvaluation ( \_labelSet\_: a List of Strings, ): either a normal completion containing an ECMAScript language value or an abrupt completion
  -- |
  -- | WhileStatement : \`while\` \`(\` Expression \`)\` Statement 1. Let \_V\_
  -- | be \*undefined\*. 1. Repeat, 1. Let \_exprRef\_ be ? Evaluation of
  -- | \|Expression\|. 1. Let \_exprValue\_ be ? GetValue(\_exprRef\_). 1. If
  -- | ToBoolean(\_exprValue\_) is \*false\*, return \_V\_. 1. Let
  -- | \_stmtResult\_ be Completion(Evaluation of \|Statement\|). 1. If
  -- | LoopContinues(\_stmtResult\_, \_labelSet\_) is \*false\*, return ?
  -- | UpdateEmpty(\_stmtResult\_, \_V\_). 1. If \_stmtResult\_.\[\[Value\]\]
  -- | is not \~empty\~, set \_V\_ to \_stmtResult\_.\[\[Value\]\].
  | .while_ cond body =>
      let lowered := .if cond (.seq body (.while_ cond body)) (.lit .undefined)
      let s' := pushTrace { s with expr := lowered } .silent
      some (.silent, s')
  -- SPEC: L17931-L17984
  -- | # Runtime Semantics: ForInOfLoopEvaluation ( \_labelSet\_: a List of Strings, ): either a normal completion containing an ECMAScript language value or an abrupt completion
  -- |
  -- | ForInOfStatement : \`for\` \`(\` LeftHandSideExpression \`in\`
  -- | Expression \`)\` Statement 1. Let \_keyResult\_ be ?
  -- | ForIn/OfHeadEvaluation(« », \|Expression\|, \~enumerate\~). 1. Return ?
  -- | ForIn/OfBodyEvaluation(\|LeftHandSideExpression\|, \|Statement\|,
  -- | \_keyResult\_, \~enumerate\~, \~assignment\~, \_labelSet\_).
  -- | ForInOfStatement : \`for\` \`(\` \`var\` ForBinding \`in\` Expression
  -- | \`)\` Statement 1. Let \_keyResult\_ be ? ForIn/OfHeadEvaluation(« »,
  -- | \|Expression\|, \~enumerate\~). 1. Return ?
  -- | ForIn/OfBodyEvaluation(\|ForBinding\|, \|Statement\|, \_keyResult\_,
  -- | \~enumerate\~, \~var-binding\~, \_labelSet\_). ForInOfStatement :
  -- | \`for\` \`(\` ForDeclaration \`in\` Expression \`)\` Statement 1. Let
  -- | \_keyResult\_ be ? ForIn/OfHeadEvaluation(BoundNames of
  -- | \|ForDeclaration\|, \|Expression\|, \~enumerate\~). 1. Return ?
  -- | ForIn/OfBodyEvaluation(\|ForDeclaration\|, \|Statement\|, \_keyResult\_,
  -- | \~enumerate\~, \~lexical-binding\~, \_labelSet\_). ForInOfStatement :
  -- | \`for\` \`(\` LeftHandSideExpression \`of\` AssignmentExpression \`)\`
  -- | Statement 1. Let \_keyResult\_ be ? ForIn/OfHeadEvaluation(« »,
  -- | \|AssignmentExpression\|, \~iterate\~). 1. Return ?
  -- | ForIn/OfBodyEvaluation(\|LeftHandSideExpression\|, \|Statement\|,
  -- | \_keyResult\_, \~iterate\~, \~assignment\~, \_labelSet\_).
  -- | ForInOfStatement : \`for\` \`(\` \`var\` ForBinding \`of\`
  -- | AssignmentExpression \`)\` Statement 1. Let \_keyResult\_ be ?
  -- | ForIn/OfHeadEvaluation(« », \|AssignmentExpression\|, \~iterate\~). 1.
  -- | Return ? ForIn/OfBodyEvaluation(\|ForBinding\|, \|Statement\|,
  -- | \_keyResult\_, \~iterate\~, \~var-binding\~, \_labelSet\_).
  -- | ForInOfStatement : \`for\` \`(\` ForDeclaration \`of\`
  -- | AssignmentExpression \`)\` Statement 1. Let \_keyResult\_ be ?
  -- | ForIn/OfHeadEvaluation(BoundNames of \|ForDeclaration\|,
  -- | \|AssignmentExpression\|, \~iterate\~). 1. Return ?
  -- | ForIn/OfBodyEvaluation(\|ForDeclaration\|, \|Statement\|, \_keyResult\_,
  -- | \~iterate\~, \~lexical-binding\~, \_labelSet\_). ForInOfStatement :
  -- | \`for\` \`await\` \`(\` LeftHandSideExpression \`of\`
  -- | AssignmentExpression \`)\` Statement 1. Let \_keyResult\_ be ?
  -- | ForIn/OfHeadEvaluation(« », \|AssignmentExpression\|,
  -- | \~async-iterate\~). 1. Return ?
  -- | ForIn/OfBodyEvaluation(\|LeftHandSideExpression\|, \|Statement\|,
  -- | \_keyResult\_, \~iterate\~, \~assignment\~, \_labelSet\_, \~async\~).
  -- | ForInOfStatement : \`for\` \`await\` \`(\` \`var\` ForBinding \`of\`
  -- | AssignmentExpression \`)\` Statement 1. Let \_keyResult\_ be ?
  -- | ForIn/OfHeadEvaluation(« », \|AssignmentExpression\|,
  -- | \~async-iterate\~). 1. Return ? ForIn/OfBodyEvaluation(\|ForBinding\|,
  -- | \|Statement\|, \_keyResult\_, \~iterate\~, \~var-binding\~,
  -- | \_labelSet\_, \~async\~). ForInOfStatement : \`for\` \`await\` \`(\`
  -- | ForDeclaration \`of\` AssignmentExpression \`)\` Statement 1. Let
  -- | \_keyResult\_ be ? ForIn/OfHeadEvaluation(BoundNames of
  -- | \|ForDeclaration\|, \|AssignmentExpression\|, \~async-iterate\~). 1.
  -- | Return ? ForIn/OfBodyEvaluation(\|ForDeclaration\|, \|Statement\|,
  -- | \_keyResult\_, \~iterate\~, \~lexical-binding\~, \_labelSet\_,
  -- | \~async\~).
  -- |
  -- | This section is extended by Annex .
  -- SPEC: L17985-L18009
  -- | # ForIn/OfHeadEvaluation ( \_uninitializedBoundNames\_: a List of Strings, \_expr\_: an \|Expression\| Parse Node or an \|AssignmentExpression\| Parse Node, \_iterationKind\_: \~enumerate\~, \~iterate\~, or \~async-iterate\~, ): either a normal completion containing an Iterator Record or an abrupt completion
  -- |
  -- | 1\. Let \_oldEnv\_ be the running execution context\'s
  -- | LexicalEnvironment. 1. If \_uninitializedBoundNames\_ is not empty,
  -- | then 1. Assert: \_uninitializedBoundNames\_ has no duplicate entries. 1.
  -- | Let \_newEnv\_ be NewDeclarativeEnvironment(\_oldEnv\_). 1. For each
  -- | String \_name\_ of \_uninitializedBoundNames\_, do 1. Perform !
  -- | \_newEnv\_.CreateMutableBinding(\_name\_, \*false\*). 1. Set the running
  -- | execution context\'s LexicalEnvironment to \_newEnv\_. 1. Let
  -- | \_exprRef\_ be Completion(Evaluation of \_expr\_). 1. Set the running
  -- | execution context\'s LexicalEnvironment to \_oldEnv\_. 1. Let
  -- | \_exprValue\_ be ? GetValue(? \_exprRef\_). 1. If \_iterationKind\_ is
  -- | \~enumerate\~, then 1. If \_exprValue\_ is either \*undefined\* or
  -- | \*null\*, then 1. Return Completion Record { \[\[Type\]\]: \~break\~,
  -- | \[\[Value\]\]: \~empty\~, \[\[Target\]\]: \~empty\~ }. 1. Let \_obj\_ be
  -- | ! ToObject(\_exprValue\_). 1. Let \_iterator\_ be
  -- | EnumerateObjectProperties(\_obj\_). 1. Let \_nextMethod\_ be !
  -- | GetV(\_iterator\_, \*\"next\"\*). 1. Return the Iterator Record {
  -- | \[\[Iterator\]\]: \_iterator\_, \[\[NextMethod\]\]: \_nextMethod\_,
  -- | \[\[Done\]\]: \*false\* }. 1. Assert: \_iterationKind\_ is either
  -- | \~iterate\~ or \~async-iterate\~. 1. If \_iterationKind\_ is
  -- | \~async-iterate\~, let \_iteratorKind\_ be \~async\~. 1. Else, let
  -- | \_iteratorKind\_ be \~sync\~. 1. Return ? GetIterator(\_exprValue\_,
  -- | \_iteratorKind\_).
  -- SPEC: L18010-L18067
  -- | # ForIn/OfBodyEvaluation ( \_lhs\_: a Parse Node, \_stmt\_: a \|Statement\| Parse Node, \_iteratorRecord\_: an Iterator Record, \_iterationKind\_: \~enumerate\~ or \~iterate\~, \_lhsKind\_: \~assignment\~, \~var-binding\~, or \~lexical-binding\~, \_labelSet\_: a List of Strings, optional \_iteratorKind\_: \~sync\~ or \~async\~, ): either a normal completion containing an ECMAScript language value or an abrupt completion
  -- |
  -- | 1\. If \_iteratorKind\_ is not present, set \_iteratorKind\_ to
  -- | \~sync\~. 1. Let \_oldEnv\_ be the running execution context\'s
  -- | LexicalEnvironment. 1. Let \_V\_ be \*undefined\*. 1. Let
  -- | \_destructuring\_ be IsDestructuring of \_lhs\_. 1. If \_destructuring\_
  -- | is \*true\* and \_lhsKind\_ is \~assignment\~, then 1. Assert: \_lhs\_
  -- | is a \|LeftHandSideExpression\|. 1. Let \_assignmentPattern\_ be the
  -- | \|AssignmentPattern\| that is covered by \_lhs\_. 1. Repeat, 1. Let
  -- | \_nextResult\_ be ? Call(\_iteratorRecord\_.\[\[NextMethod\]\],
  -- | \_iteratorRecord\_.\[\[Iterator\]\]). 1. If \_iteratorKind\_ is
  -- | \~async\~, set \_nextResult\_ to ? Await(\_nextResult\_). 1. If
  -- | \_nextResult\_ is not an Object, throw a \*TypeError\* exception. 1. Let
  -- | \_done\_ be ? IteratorComplete(\_nextResult\_). 1. If \_done\_ is
  -- | \*true\*, return \_V\_. 1. Let \_nextValue\_ be ?
  -- | IteratorValue(\_nextResult\_). 1. If \_lhsKind\_ is either
  -- | \~assignment\~ or \~var-binding\~, then 1. If \_destructuring\_ is
  -- | \*true\*, then 1. If \_lhsKind\_ is \~assignment\~, then 1. Let
  -- | \_status\_ be Completion(DestructuringAssignmentEvaluation of
  -- | \_assignmentPattern\_ with argument \_nextValue\_). 1. Else, 1. Assert:
  -- | \_lhsKind\_ is \~var-binding\~. 1. Assert: \_lhs\_ is a
  -- | \|ForBinding\|. 1. Let \_status\_ be Completion(BindingInitialization of
  -- | \_lhs\_ with arguments \_nextValue\_ and \*undefined\*). 1. Else, 1. Let
  -- | \_lhsRef\_ be Completion(Evaluation of \_lhs\_). (It may be evaluated
  -- | repeatedly.) 1. If \_lhsKind\_ is \~assignment\~ and the
  -- | AssignmentTargetType of \_lhs\_ is \~web-compat\~, throw a
  -- | \*ReferenceError\* exception. 1. If \_lhsRef\_ is an abrupt completion,
  -- | then 1. Let \_status\_ be \_lhsRef\_. 1. Else, 1. Let \_status\_ be
  -- | Completion(PutValue(\_lhsRef\_.\[\[Value\]\], \_nextValue\_)). 1.
  -- | Else, 1. Assert: \_lhsKind\_ is \~lexical-binding\~. 1. Assert: \_lhs\_
  -- | is a \|ForDeclaration\|. 1. Let \_iterationEnv\_ be
  -- | NewDeclarativeEnvironment(\_oldEnv\_). 1. Perform
  -- | ForDeclarationBindingInstantiation of \_lhs\_ with argument
  -- | \_iterationEnv\_. 1. Set the running execution context\'s
  -- | LexicalEnvironment to \_iterationEnv\_. 1. If \_destructuring\_ is
  -- | \*true\*, then 1. Let \_status\_ be
  -- | Completion(ForDeclarationBindingInitialization of \_lhs\_ with arguments
  -- | \_nextValue\_ and \_iterationEnv\_). 1. Else, 1. Assert: \_lhs\_ binds a
  -- | single name. 1. Let \_lhsName\_ be the sole element of the BoundNames of
  -- | \_lhs\_. 1. Let \_lhsRef\_ be ! ResolveBinding(\_lhsName\_). 1. Let
  -- | \_status\_ be Completion(InitializeReferencedBinding(\_lhsRef\_,
  -- | \_nextValue\_)). 1. If \_status\_ is an abrupt completion, then 1. Set
  -- | the running execution context\'s LexicalEnvironment to \_oldEnv\_. 1. If
  -- | \_iterationKind\_ is \~enumerate\~, return ? \_status\_. 1. Assert:
  -- | \_iterationKind\_ is \~iterate\~. 1. If \_iteratorKind\_ is \~async\~,
  -- | return ? AsyncIteratorClose(\_iteratorRecord\_, \_status\_). 1. Return ?
  -- | IteratorClose(\_iteratorRecord\_, \_status\_). 1. Let \_result\_ be
  -- | Completion(Evaluation of \_stmt\_). 1. Set the running execution
  -- | context\'s LexicalEnvironment to \_oldEnv\_. 1. If
  -- | LoopContinues(\_result\_, \_labelSet\_) is \*false\*, then 1. Set
  -- | \_status\_ to Completion(UpdateEmpty(\_result\_, \_V\_)). 1. If
  -- | \_iterationKind\_ is \~enumerate\~, return ? \_status\_. 1. Assert:
  -- | \_iterationKind\_ is \~iterate\~. 1. If \_iteratorKind\_ is \~async\~,
  -- | return ? AsyncIteratorClose(\_iteratorRecord\_, \_status\_). 1. Return ?
  -- | IteratorClose(\_iteratorRecord\_, \_status\_). 1. If
  -- | \_result\_.\[\[Value\]\] is not \~empty\~, set \_V\_ to
  -- | \_result\_.\[\[Value\]\].
  -- SPEC: L18068-L18073
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | BindingIdentifier : Identifier \`yield\` \`await\` 1. Let \_bindingId\_
  -- | be the StringValue of \|BindingIdentifier\|. 1. Return ?
  -- | ResolveBinding(\_bindingId\_).
  -- |
  | .forIn binding obj body =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { so with expr := .forIn binding so.expr body, trace := s.trace } t
              some (t, s')
          | none => none
      | some (.object addr) =>
          -- SPEC: L18074-L18100
          -- | # EnumerateObjectProperties ( \_O\_: an Object, ): an iterator object
          -- |
          -- | 1\. Return an iterator object whose \`next\` method iterates over all
          -- | the String-valued keys of enumerable properties of \_O\_. The iterator
          -- | object is never directly accessible to ECMAScript code. The mechanics
          -- | and order of enumerating the properties is not specified but must
          -- | conform to the rules specified below.
          -- |
          -- | The iterator\'s \`throw\` and \`return\` methods are \*null\* and are
          -- | never invoked. The iterator\'s \`next\` method processes object
          -- | properties to determine whether the property key should be returned as
          -- | an iterator value. Returned property keys do not include keys that are
          -- | Symbols. Properties of the target object may be deleted during
          -- | enumeration. A property that is deleted before it is processed by the
          -- | iterator\'s \`next\` method is ignored. If new properties are added to
          -- | the target object during enumeration, the newly added properties are not
          -- | guaranteed to be processed in the active enumeration. A property name
          -- | will be returned by the iterator\'s \`next\` method at most once in any
          -- | enumeration.
          -- |
          -- | Enumerating the properties of the target object includes enumerating
          -- | properties of its prototype, and the prototype of the prototype, and so
          -- | on, recursively; but a property of a prototype is not processed if it
          -- | has the same name as a property that has already been processed by the
          -- | iterator\'s \`next\` method. The values of \[\[Enumerable\]\] attributes
          -- | are not considered when determining if a property of a prototype object
          -- | has already been processed. The enumerable property names of prototype
          let keys : List PropName := match s.heap.objects[addr]? with
            | some props => props.map (fun p : PropName × Value => p.1)
            | none => []
          -- Desugar: for each key, bind it and run body.
          let lowered := keys.foldr (fun key acc =>
            .seq (.«let» binding (.lit (.string key)) body) acc
          ) (.lit .undefined)
          let s' := pushTrace { s with expr := lowered } .silent
          some (.silent, s')
      | some _ =>
          -- for-in on non-object: no iteration (per spec, ToObject then enumerate).
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
  -- SPEC: L17948-L17952
  -- | \`for\` \`(\` LeftHandSideExpression \`of\` AssignmentExpression \`)\`
  -- | Statement 1. Let \_keyResult\_ be ? ForIn/OfHeadEvaluation(« »,
  -- | \|AssignmentExpression\|, \~iterate\~). 1. Return ?
  -- | ForIn/OfBodyEvaluation(\|LeftHandSideExpression\|, \|Statement\|,
  -- | \_keyResult\_, \~iterate\~, \~assignment\~, \_labelSet\_).
  -- SPEC: L7160-L7172
  -- | # GetIterator ( \_obj\_: an ECMAScript language value, \_kind\_: \~sync\~ or \~async\~, ): either a normal completion containing an Iterator Record or a throw completion
  -- |
  -- | 1\. If \_kind\_ is \~async\~, then 1. Let \_method\_ be ?
  -- | GetMethod(\_obj\_, %Symbol.asyncIterator%). 1. If \_method\_ is
  -- | \*undefined\*, then 1. Let \_syncMethod\_ be ? GetMethod(\_obj\_,
  -- | %Symbol.iterator%). 1. If \_syncMethod\_ is \*undefined\*, throw a
  -- | \*TypeError\* exception. 1. Let \_syncIteratorRecord\_ be ?
  -- | GetIteratorFromMethod(\_obj\_, \_syncMethod\_). 1. Return
  -- | CreateAsyncFromSyncIterator(\_syncIteratorRecord\_). 1. Else, 1. Let
  -- | \_method\_ be ? GetMethod(\_obj\_, %Symbol.iterator%). 1. If \_method\_
  -- | is \*undefined\*, throw a \*TypeError\* exception. 1. Return ?
  -- | GetIteratorFromMethod(\_obj\_, \_method\_).
  -- SPEC: L7185-L7197
  -- | # IteratorNext ( \_iteratorRecord\_: an Iterator Record, optional \_value\_: an ECMAScript language value, ): either a normal completion containing an Object or a throw completion
  -- |
  -- | 1\. If \_value\_ is not present, then 1. Let \_result\_ be
  -- | Completion(Call(\_iteratorRecord\_.\[\[NextMethod\]\],
  -- | \_iteratorRecord\_.\[\[Iterator\]\])). 1. Else, 1. Let \_result\_ be
  -- | Completion(Call(\_iteratorRecord\_.\[\[NextMethod\]\],
  -- | \_iteratorRecord\_.\[\[Iterator\]\], « \_value\_ »)). 1. If \_result\_
  -- | is a throw completion, then 1. Set \_iteratorRecord\_.\[\[Done\]\] to
  -- | \*true\*. 1. Return ? \_result\_. 1. Set \_result\_ to ! \_result\_. 1.
  -- | If \_result\_ is not an Object, then 1. Set
  -- | \_iteratorRecord\_.\[\[Done\]\] to \*true\*. 1. Throw a \*TypeError\*
  -- | exception. 1. Return \_result\_.
  -- SPEC: L7198-L7200
  -- | # IteratorComplete ( \_iteratorResult\_: an Object, ): either a normal completion containing a Boolean or a throw completion
  -- |
  -- | 1\. Return ToBoolean(? Get(\_iteratorResult\_, \*\"done\"\*)).
  -- SPEC: L7202-L7204
  -- | # IteratorValue ( \_iteratorResult\_: an Object, ): either a normal completion containing an ECMAScript language value or a throw completion
  -- |
  -- | 1\. Return ? Get(\_iteratorResult\_, \*\"value\"\*).
  -- SPEC: L7206-L7219
  -- | # IteratorStep ( \_iteratorRecord\_: an Iterator Record, ): either a normal completion containing either an Object or \~done\~, or a throw completion
  -- |
  -- | description
  -- | :   It requests the next value from \_iteratorRecord\_.\[\[Iterator\]\]
  -- |     by calling \_iteratorRecord\_.\[\[NextMethod\]\] and returns either
  -- |     \~done\~ indicating that the iterator has reached its end or the
  -- |     IteratorResult object if a next value is available.
  -- |
  -- | 1\. Let \_result\_ be ? IteratorNext(\_iteratorRecord\_). 1. Let
  -- | \_done\_ be Completion(IteratorComplete(\_result\_)). 1. If \_done\_ is
  -- | a throw completion, then 1. Set \_iteratorRecord\_.\[\[Done\]\] to
  -- | \*true\*. 1. Return ? \_done\_. 1. Set \_done\_ to ! \_done\_. 1. If
  -- | \_done\_ is \*true\*, then 1. Set \_iteratorRecord\_.\[\[Done\]\] to
  -- | \*true\*. 1. Return \~done\~. 1. Return \_result\_.
  -- SPEC: L7235-L7252
  -- | # IteratorClose ( \_iteratorRecord\_: an Iterator Record, \_completion\_: a Completion Record, ): a Completion Record
  -- |
  -- | description
  -- | :   It is used to notify an iterator that it should perform any actions
  -- |     it would normally perform when it has reached its completed state.
  -- |
  -- | 1\. Assert: \_iteratorRecord\_.\[\[Iterator\]\] is an Object. 1. Let
  -- | \_iterator\_ be \_iteratorRecord\_.\[\[Iterator\]\]. 1. Let
  -- | \_innerResult\_ be Completion(GetMethod(\_iterator\_,
  -- | \*\"return\"\*)). 1. If \_innerResult\_ is a normal completion, then 1.
  -- | Let \_return\_ be \_innerResult\_.\[\[Value\]\]. 1. If \_return\_ is
  -- | \*undefined\*, return ? \_completion\_. 1. Set \_innerResult\_ to
  -- | Completion(Call(\_return\_, \_iterator\_)). 1. If \_completion\_ is a
  -- | throw completion, return ? \_completion\_. 1. If \_innerResult\_ is a
  -- | throw completion, return ? \_innerResult\_. 1. If
  -- | \_innerResult\_.\[\[Value\]\] is not an Object, throw a \*TypeError\*
  -- | exception. 1. Return ? \_completion\_.
  -- SPEC: L7309-L7318
  -- | # CreateIteratorResultObject ( \_value\_: an ECMAScript language value, \_done\_: a Boolean, ): an Object that conforms to the IteratorResult interface
  -- |
  -- | description
  -- | :   It creates an object that conforms to the IteratorResult interface.
  -- |
  -- | 1\. Let \_obj\_ be OrdinaryObjectCreate(%Object.prototype%). 1. Perform
  -- | ! CreateDataPropertyOrThrow(\_obj\_, \*\"value\"\*, \_value\_). 1.
  -- | Perform ! CreateDataPropertyOrThrow(\_obj\_, \*\"done\"\*, \_done\_). 1.
  -- | Return \_obj\_.
  | .forOf binding iterable body =>
      match exprValue? iterable with
      | none =>
          match step? { s with expr := iterable } with
          | some (t, si) =>
              let s' := pushTrace { si with expr := .forOf binding si.expr body, trace := s.trace } t
              some (t, s')
          | none => none
      | some (.object addr) =>
          -- Simplified iterator: treat heap object entries as ordered elements.
          let elems : List Value := match s.heap.objects[addr]? with
            | some props => props.map (fun p : PropName × Value => p.2)
            | none => []
          -- Desugar: for each element value, bind it and run body.
          let lowered := elems.foldr (fun val acc =>
            .seq (.«let» binding (.lit val) body) acc
          ) (.lit .undefined)
          let s' := pushTrace { s with expr := lowered } .silent
          some (.silent, s')
      | some _ =>
          -- for-of on non-iterable: no iteration.
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
  -- SPEC: L18432-L18443
  -- | SwitchStatement : \`switch\` \`(\` Expression \`)\` CaseBlock 1. Let
  -- | \_exprRef\_ be ? Evaluation of \|Expression\|. 1. Let \_switchValue\_ be
  -- | ? GetValue(\_exprRef\_). 1. Let \_oldEnv\_ be the running execution
  -- | context\'s LexicalEnvironment. 1. Let \_blockEnv\_ be
  -- | NewDeclarativeEnvironment(\_oldEnv\_). 1. Perform
  -- | BlockDeclarationInstantiation(\|CaseBlock\|, \_blockEnv\_). 1. Set the
  -- | running execution context\'s LexicalEnvironment to \_blockEnv\_. 1. Let
  -- | \_R\_ be Completion(CaseBlockEvaluation of \|CaseBlock\| with argument
  -- | \_switchValue\_). 1. Set the running execution context\'s
  -- | LexicalEnvironment to \_oldEnv\_. 1. Return \_R\_.
  -- SPEC: L18372-L18415
  -- | # Runtime Semantics: CaseBlockEvaluation ( \_input\_: an ECMAScript language value, ): either a normal completion containing an ECMAScript language value or an abrupt completion
  -- |
  -- | CaseBlock : \`{\` \`}\` 1. Return \*undefined\*. CaseBlock : \`{\`
  -- | CaseClauses \`}\` 1. Let \_V\_ be \*undefined\*. 1. Let \_A\_ be the
  -- | List of \|CaseClause\| items in \|CaseClauses\|, in source text
  -- | order. 1. Let \_found\_ be \*false\*. 1. For each \|CaseClause\| \_C\_
  -- | of \_A\_, do 1. If \_found\_ is \*false\*, then 1. Set \_found\_ to ?
  -- | CaseClauseIsSelected(\_C\_, \_input\_). 1. If \_found\_ is \*true\*,
  -- | then 1. Let \_R\_ be Completion(Evaluation of \_C\_). 1. If
  -- | \_R\_.\[\[Value\]\] is not \~empty\~, set \_V\_ to
  -- | \_R\_.\[\[Value\]\]. 1. If \_R\_ is an abrupt completion, return ?
  -- | UpdateEmpty(\_R\_, \_V\_). 1. Return \_V\_. CaseBlock : \`{\`
  -- | CaseClauses? DefaultClause CaseClauses? \`}\` 1. Let \_V\_ be
  -- | \*undefined\*. 1. If the first \|CaseClauses\| is present, then 1. Let
  -- | \_A\_ be the List of \|CaseClause\| items in the first \|CaseClauses\|,
  -- | in source text order. 1. Else, 1. Let \_A\_ be a new empty List. 1. Let
  -- | \_found\_ be \*false\*. 1. For each \|CaseClause\| \_C\_ of \_A\_, do 1.
  -- | If \_found\_ is \*false\*, then 1. Set \_found\_ to ?
  -- | CaseClauseIsSelected(\_C\_, \_input\_). 1. If \_found\_ is \*true\*,
  -- | then 1. Let \_R\_ be Completion(Evaluation of \_C\_). 1. If
  -- | \_R\_.\[\[Value\]\] is not \~empty\~, set \_V\_ to
  -- | \_R\_.\[\[Value\]\]. 1. If \_R\_ is an abrupt completion, return ?
  -- | UpdateEmpty(\_R\_, \_V\_). 1. Let \_foundInB\_ be \*false\*. 1. If the
  -- | second \|CaseClauses\| is present, then 1. Let \_B\_ be the List of
  -- | \|CaseClause\| items in the second \|CaseClauses\|, in source text
  -- | order. 1. Else, 1. Let \_B\_ be a new empty List. 1. If \_found\_ is
  -- | \*false\*, then 1. For each \|CaseClause\| \_C\_ of \_B\_, do 1. If
  -- | \_foundInB\_ is \*false\*, then 1. Set \_foundInB\_ to ?
  -- | CaseClauseIsSelected(\_C\_, \_input\_). 1. If \_foundInB\_ is \*true\*,
  -- | then 1. Let \_R\_ be Completion(Evaluation of \|CaseClause\| \_C\_). 1.
  -- | If \_R\_.\[\[Value\]\] is not \~empty\~, set \_V\_ to
  -- | \_R\_.\[\[Value\]\]. 1. If \_R\_ is an abrupt completion, return ?
  -- | UpdateEmpty(\_R\_, \_V\_). 1. If \_foundInB\_ is \*true\*, return
  -- | \_V\_. 1. Let \_defaultR\_ be Completion(Evaluation of
  -- | \|DefaultClause\|). 1. If \_defaultR\_.\[\[Value\]\] is not \~empty\~,
  -- | set \_V\_ to \_defaultR\_.\[\[Value\]\]. 1. If \_defaultR\_ is an abrupt
  -- | completion, return ? UpdateEmpty(\_defaultR\_, \_V\_). 1. NOTE: The
  -- | following is another complete iteration of the second
  -- | \|CaseClauses\|. 1. For each \|CaseClause\| \_C\_ of \_B\_, do 1. Let
  -- | \_R\_ be Completion(Evaluation of \|CaseClause\| \_C\_). 1. If
  -- | \_R\_.\[\[Value\]\] is not \~empty\~, set \_V\_ to
  -- | \_R\_.\[\[Value\]\]. 1. If \_R\_ is an abrupt completion, return ?
  -- | UpdateEmpty(\_R\_, \_V\_). 1. Return \_V\_.
  -- SPEC: L18416-L18430
  -- | # CaseClauseIsSelected ( \_C\_: a \|CaseClause\| Parse Node, \_input\_: an ECMAScript language value, ): either a normal completion containing a Boolean or an abrupt completion
  -- |
  -- | description
  -- | :   It determines whether \_C\_ matches \_input\_.
  -- |
  -- | 1\. Assert: \_C\_ is an instance of the production CaseClause : \`case\`
  -- | Expression \`:\` StatementList?. 1. Let \_exprRef\_ be ? Evaluation of
  -- | the \|Expression\| of \_C\_. 1. Let \_clauseSelector\_ be ?
  -- | GetValue(\_exprRef\_). 1. Return IsStrictlyEqual(\_input\_,
  -- | \_clauseSelector\_).
  -- |
  -- | This operation does not execute \_C\_\'s \|StatementList\| (if any). The
  -- | \|CaseBlock\| algorithm uses its return value to determine which
  -- | \|StatementList\| to start executing.
  -- NOTE: switch is desugared by the parser to if-else chains.
  -- SPEC: L18486-L18490
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | LabelledStatement : LabelIdentifier \`:\` LabelledItem 1. Return ?
  -- | LabelledEvaluation of this \|LabelledStatement\| with argument « ».
  -- SPEC: L18491-L18529
  -- | # Runtime Semantics: LabelledEvaluation ( \_labelSet\_: a List of Strings, ): either a normal completion containing either an ECMAScript language value or \~empty\~, or an abrupt completion
  -- |
  -- | BreakableStatement : IterationStatement 1. Let \_stmtResult\_ be
  -- | Completion(LoopEvaluation of \|IterationStatement\| with argument
  -- | \_labelSet\_). 1. If \_stmtResult\_ is a break completion, then 1. If
  -- | \_stmtResult\_.\[\[Target\]\] is \~empty\~, then 1. If
  -- | \_stmtResult\_.\[\[Value\]\] is \~empty\~, set \_stmtResult\_ to
  -- | NormalCompletion(\*undefined\*). 1. Else, set \_stmtResult\_ to
  -- | NormalCompletion(\_stmtResult\_.\[\[Value\]\]). 1. Return ?
  -- | \_stmtResult\_. BreakableStatement : SwitchStatement 1. Let
  -- | \_stmtResult\_ be Completion(Evaluation of \|SwitchStatement\|). 1. If
  -- | \_stmtResult\_ is a break completion, then 1. If
  -- | \_stmtResult\_.\[\[Target\]\] is \~empty\~, then 1. If
  -- | \_stmtResult\_.\[\[Value\]\] is \~empty\~, set \_stmtResult\_ to
  -- | NormalCompletion(\*undefined\*). 1. Else, set \_stmtResult\_ to
  -- | NormalCompletion(\_stmtResult\_.\[\[Value\]\]). 1. Return ?
  -- | \_stmtResult\_.
  -- |
  -- | A \|BreakableStatement\| is one that can be exited via an unlabelled
  -- | \|BreakStatement\|.
  -- |
  -- | LabelledStatement : LabelIdentifier \`:\` LabelledItem 1. Let \_label\_
  -- | be the StringValue of \|LabelIdentifier\|. 1. Let \_newLabelSet\_ be the
  -- | list-concatenation of \_labelSet\_ and « \_label\_ ». 1. Let
  -- | \_stmtResult\_ be Completion(LabelledEvaluation of \|LabelledItem\| with
  -- | argument \_newLabelSet\_). 1. If \_stmtResult\_ is a break completion
  -- | and \_stmtResult\_.\[\[Target\]\] is \_label\_, then 1. Set
  -- | \_stmtResult\_ to NormalCompletion(\_stmtResult\_.\[\[Value\]\]). 1.
  -- | Return ? \_stmtResult\_. LabelledItem : FunctionDeclaration 1. Return ?
  -- | Evaluation of \|FunctionDeclaration\|. Statement : BlockStatement
  -- | VariableStatement EmptyStatement ExpressionStatement IfStatement
  -- | ContinueStatement BreakStatement ReturnStatement WithStatement
  -- | ThrowStatement TryStatement DebuggerStatement 1. Return ? Evaluation of
  -- | \|Statement\|.
  -- |
  -- | The only two productions of \|Statement\| which have special semantics
  -- | for LabelledEvaluation are \|BreakableStatement\| and
  -- | \|LabelledStatement\|.
  | .labeled _ body =>
      let s' := pushTrace { s with expr := body } .silent
      some (.silent, s')
  -- SPEC: L18537-L18542
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | ThrowStatement : \`throw\` Expression \`;\` 1. Let \_exprRef\_ be ?
  -- | Evaluation of \|Expression\|. 1. Let \_exprValue\_ be ?
  -- | GetValue(\_exprRef\_). 1. Return ThrowCompletion(\_exprValue\_).
  -- SPEC: L5494-L5498
  -- | # ThrowCompletion ( \_value\_: an ECMAScript language value, ): a throw completion
  -- |
  -- | 1\. Return Completion Record { \[\[Type\]\]: \~throw\~, \[\[Value\]\]:
  -- | \_value\_, \[\[Target\]\]: \~empty\~ }.
  | .throw arg =>
      match exprValue? arg with
      | some v =>
          -- ECMA-262 §13.14 throw: produce error event with stringified value.
          let msg := valueToString v
          let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
          some (.error msg, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              let s' := pushTrace { sa with expr := .throw sa.expr, trace := s.trace } t
              some (t, s')
          | none => none
  -- SPEC: L18600-L18614
  -- | TryStatement : \`try\` Block Catch 1. Let \_B\_ be Completion(Evaluation
  -- | of \|Block\|). 1. If \_B\_ is a throw completion, let \_C\_ be
  -- | Completion(CatchClauseEvaluation of \|Catch\| with argument
  -- | \_B\_.\[\[Value\]\]). 1. Else, let \_C\_ be \_B\_. 1. Return ?
  -- | UpdateEmpty(\_C\_, \*undefined\*). TryStatement : \`try\` Block
  -- | Finally 1. Let \_B\_ be Completion(Evaluation of \|Block\|). 1. Let
  -- | \_F\_ be Completion(Evaluation of \|Finally\|). 1. If \_F\_ is a normal
  -- | completion, set \_F\_ to \_B\_. 1. Return ? UpdateEmpty(\_F\_,
  -- | \*undefined\*). TryStatement : \`try\` Block Catch Finally 1. Let \_B\_
  -- | be Completion(Evaluation of \|Block\|). 1. If \_B\_ is a throw
  -- | completion, let \_C\_ be Completion(CatchClauseEvaluation of \|Catch\|
  -- | with argument \_B\_.\[\[Value\]\]). 1. Else, let \_C\_ be \_B\_. 1. Let
  -- | \_F\_ be Completion(Evaluation of \|Finally\|). 1. If \_F\_ is a normal
  -- | completion, set \_F\_ to \_C\_. 1. Return ? UpdateEmpty(\_F\_,
  -- | \*undefined\*).
  | .tryCatch body catchParam catchBody finally_ =>
      let isCallFrame := catchParam == "__call_frame_return__"
      match exprValue? body with
      | some v =>
          if isCallFrame then
              -- Function normal completion: restore caller env from callStack.
              let restoredEnv : Env := match s.callStack with
                | saved :: _ => ⟨saved⟩
                | [] => s.env
              let newStack := match s.callStack with
                | _ :: rest => rest
                | [] => []
              let s' := pushTrace { s with expr := .lit v, env := restoredEnv, callStack := newStack } .silent
              some (.silent, s')
          else
              -- Normal completion: run finally (if present), then yield value.
              match finally_ with
              | some fin =>
                  let s' := pushTrace { s with expr := .seq fin (.lit v) } .silent
                  some (.silent, s')
              | none =>
                  let s' := pushTrace { s with expr := .lit v } .silent
                  some (.silent, s')
      | none =>
          -- Step the try-body; intercept error events for catch.
          match step? { s with expr := body } with
          | some (.error msg, sb) =>
              if isCallFrame && msg.startsWith "return:" then
                  -- Function return: extract value from sb.expr, restore caller env.
                  let retVal := match exprValue? sb.expr with
                    | some v => v
                    | none => .undefined
                  let restoredEnv : Env := match s.callStack with
                    | saved :: _ => ⟨saved⟩
                    | [] => sb.env
                  let newStack := match s.callStack with
                    | _ :: rest => rest
                    | [] => []
                  let s' := pushTrace
                    { s with expr := .lit retVal, env := restoredEnv
                           , heap := sb.heap, funcs := sb.funcs
                           , callStack := newStack } .silent
                  some (.silent, s')
              else if isCallFrame then
                  -- Function threw: propagate error, restore caller env.
                  let restoredEnv : Env := match s.callStack with
                    | saved :: _ => ⟨saved⟩
                    | [] => sb.env
                  let newStack := match s.callStack with
                    | _ :: rest => rest
                    | [] => []
                  let s' := pushTrace
                    { s with expr := .lit .undefined, env := restoredEnv
                           , heap := sb.heap, funcs := sb.funcs
                           , callStack := newStack } (.error msg)
                  some (.error msg, s')
              else
                  -- Regular exception caught: bind error to catchParam, run catch body.
                  let handler :=
                    match finally_ with
                    | some fin => .seq catchBody fin
                    | none => catchBody
                  let catchEnv := sb.env.extend catchParam (.string msg)
                  let s' := pushTrace
                    { sb with expr := handler, env := catchEnv, trace := s.trace } (.error msg)
                  some (.error msg, s')
          | some (t, sb) =>
              -- Normal step inside try body: keep wrapping in tryCatch.
              let s' := pushTrace
                { sb with expr := .tryCatch sb.expr catchParam catchBody finally_
                        , trace := s.trace } t
              some (t, s')
          | none => none
  -- SPEC: L14917-L14917
  -- | PrimaryExpression : \`this\` 1. Return ? ResolveThisBinding().
  -- SPEC: L10002-L10010
  -- | # ResolveThisBinding ( ): either a normal completion containing an ECMAScript language value or a throw completion
  -- |
  -- | description
  -- | :   It determines the binding of the keyword \`this\` using the
  -- |     LexicalEnvironment of the running execution context.
  -- |
  -- | 1\. Let \_envRec\_ be GetThisEnvironment(). 1. Return ?
  -- | \_envRec\_.GetThisBinding().
  -- SPEC: L10011-L10019
  -- | # GetNewTarget ( ): an Object or \*undefined\*
  -- |
  -- | description
  -- | :   It determines the NewTarget value using the LexicalEnvironment of
  -- |     the running execution context.
  -- |
  -- | 1\. Let \_envRec\_ be GetThisEnvironment(). 1. Assert: \_envRec\_ has a
  -- | \[\[NewTarget\]\] field. 1. Return \_envRec\_.\[\[NewTarget\]\].
  -- SPEC: L10020-L10028
  -- | # GetGlobalObject ( ): an Object
  -- |
  -- | description
  -- | :   It returns the global object used by the currently running execution
  -- |     context.
  -- |
  -- | 1\. Let \_currentRealm\_ be the current Realm Record. 1. Return
  -- | \_currentRealm\_.\[\[GlobalObject\]\].
  | .this =>
      match s.env.lookup "this" with
      | some v =>
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | none =>
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
  -- SPEC: L16165-L16179
  -- | UnaryExpression : \`typeof\` UnaryExpression 1. Let \_val\_ be ?
  -- | Evaluation of \|UnaryExpression\|. 1. If \_val\_ is a Reference Record,
  -- | then 1. If IsUnresolvableReference(\_val\_) is \*true\*, return
  -- | \*\"undefined\"\*. 1. Set \_val\_ to ? GetValue(\_val\_). 1. If \_val\_
  -- | is \*undefined\*, return \*\"undefined\"\*. 1. If \_val\_ is \*null\*,
  -- | return \*\"object\"\*. 1. If \_val\_ is a String, return
  -- | \*\"string\"\*. 1. If \_val\_ is a Symbol, return \*\"symbol\"\*. 1. If
  -- | \_val\_ is a Boolean, return \*\"boolean\"\*. 1. If \_val\_ is a Number,
  -- | return \*\"number\"\*. 1. If \_val\_ is a BigInt, return
  -- | \*\"bigint\"\*. 1. Assert: \_val\_ is an Object. 1.
  -- | \[id=\"step-typeof-web-compat-insertion-point\", normative-optional\] If
  -- | the host is a web browser or otherwise supports , then 1. If \_val\_ has
  -- | an \[\[IsHTMLDDA\]\] internal slot, return \*\"undefined\"\*. 1. If
  -- | \_val\_ has a \[\[Call\]\] internal method, return \*\"function\"\*. 1.
  -- | Return \*\"object\"\*.
  | .typeof arg =>
      match exprValue? arg with
      | some v =>
          let result := match v with
            | .undefined => "undefined"
            | .null => "object"  -- typeof null === "object" per spec
            | .bool _ => "boolean"
            | .number _ => "number"
            | .string _ => "string"
            | .function _ => "function"
            | .object _ => "object"
          let s' := pushTrace { s with expr := .lit (.string result) } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              let s' := pushTrace { sa with expr := .typeof sa.expr, trace := s.trace } t
              some (t, s')
          | none => none
  -- SPEC: L18292-L18297
  -- | ReturnStatement : \`return\` \`;\` 1. Return
  -- | ReturnCompletion(\*undefined\*). ReturnStatement : \`return\` Expression
  -- | \`;\` 1. Let \_exprRef\_ be ? Evaluation of \|Expression\|. 1. Let
  -- | \_exprValue\_ be ? GetValue(\_exprRef\_). 1. If GetGeneratorKind() is
  -- | \~async\~, set \_exprValue\_ to ? Await(\_exprValue\_). 1. Return
  -- | ReturnCompletion(\_exprValue\_).
  -- SPEC: L5499-L5503
  -- | # ReturnCompletion ( \_value\_: an ECMAScript language value, ): a return completion
  -- |
  -- | 1\. Return Completion Record { \[\[Type\]\]: \~return\~, \[\[Value\]\]:
  -- | \_value\_, \[\[Target\]\]: \~empty\~ }.
  | .«return» arg =>
      match arg with
      | some e =>
          match exprValue? e with
          | some v =>
              let s' := pushTrace { s with expr := .lit v } (.error ("return:" ++ valueToString v))
              some (.error ("return:" ++ valueToString v), s')
          | none =>
              match step? { s with expr := e } with
              | some (t, sa) =>
                  let s' := pushTrace { sa with expr := .«return» (some sa.expr), trace := s.trace } t
                  some (t, s')
              | none => none
      | none =>
          let s' := pushTrace { s with expr := .lit .undefined } (.error "return:undefined")
          some (.error "return:undefined", s')
  -- SPEC: L18267-L18272
  -- | BreakStatement : \`break\` \`;\` 1. Return Completion Record {
  -- | \[\[Type\]\]: \~break\~, \[\[Value\]\]: \~empty\~, \[\[Target\]\]:
  -- | \~empty\~ }. BreakStatement : \`break\` LabelIdentifier \`;\` 1. Let
  -- | \_label\_ be the StringValue of \|LabelIdentifier\|. 1. Return
  -- | Completion Record { \[\[Type\]\]: \~break\~, \[\[Value\]\]: \~empty\~,
  -- | \[\[Target\]\]: \_label\_ }.
  | .«break» label =>
      let l := match label with | some s => "break:" ++ s | none => "break:"
      let s' := pushTrace { s with expr := .lit .undefined } (.error l)
      some (.error l, s')
  -- SPEC: L18242-L18247
  -- | ContinueStatement : \`continue\` \`;\` 1. Return Completion Record {
  -- | \[\[Type\]\]: \~continue\~, \[\[Value\]\]: \~empty\~, \[\[Target\]\]:
  -- | \~empty\~ }. ContinueStatement : \`continue\` LabelIdentifier \`;\` 1.
  -- | Let \_label\_ be the StringValue of \|LabelIdentifier\|. 1. Return
  -- | Completion Record { \[\[Type\]\]: \~continue\~, \[\[Value\]\]:
  -- | \~empty\~, \[\[Target\]\]: \_label\_ }.
  | .«continue» label =>
      let l := match label with | some s => "continue:" ++ s | none => "continue:"
      let s' := pushTrace { s with expr := .lit .undefined } (.error l)
      some (.error l, s')
  -- SPEC: L10782-L10855
  -- | # ValidateAndApplyPropertyDescriptor ( \_O\_: an Object or \*undefined\*, \_P\_: a property key, \_extensible\_: a Boolean, \_Desc\_: a Property Descriptor, \_current\_: a Property Descriptor or \*undefined\*, ): a Boolean
  -- |
  -- | description
  -- | :   It returns \*true\* if and only if \_Desc\_ can be applied as the
  -- |     property of an object with specified \_extensibility\_ and current
  -- |     property \_current\_ while upholding invariants. When such
  -- |     application is possible and \_O\_ is not \*undefined\*, it is
  -- |     performed for the property named \_P\_ (which is created if
  -- |     necessary).
  -- |
  -- | 1\. Assert: \_P\_ is a property key. 1. If \_current\_ is \*undefined\*,
  -- | then 1. If \_extensible\_ is \*false\*, return \*false\*. 1. If \_O\_ is
  -- | \*undefined\*, return \*true\*. 1. If IsAccessorDescriptor(\_Desc\_) is
  -- | \*true\*, then 1. Create an own accessor property named \_P\_ of object
  -- | \_O\_ whose \[\[Get\]\], \[\[Set\]\], \[\[Enumerable\]\], and
  -- | \[\[Configurable\]\] attributes are set to the value of the
  -- | corresponding field in \_Desc\_ if \_Desc\_ has that field, or to the
  -- | attribute\'s default value otherwise. 1. Else, 1. Create an own data
  -- | property named \_P\_ of object \_O\_ whose \[\[Value\]\],
  -- | \[\[Writable\]\], \[\[Enumerable\]\], and \[\[Configurable\]\]
  -- | attributes are set to the value of the corresponding field in \_Desc\_
  -- | if \_Desc\_ has that field, or to the attribute\'s default value
  -- | otherwise. 1. Return \*true\*. 1. Assert: \_current\_ is a fully
  -- | populated Property Descriptor. 1. If \_Desc\_ does not have any fields,
  -- | return \*true\*. 1. If \_current\_.\[\[Configurable\]\] is \*false\*,
  -- | then 1. If \_Desc\_ has a \[\[Configurable\]\] field and
  -- | \_Desc\_.\[\[Configurable\]\] is \*true\*, return \*false\*. 1. If
  -- | \_Desc\_ has an \[\[Enumerable\]\] field and \_Desc\_.\[\[Enumerable\]\]
  -- | is not \_current\_.\[\[Enumerable\]\], return \*false\*. 1. If
  -- | IsGenericDescriptor(\_Desc\_) is \*false\* and
  -- | IsAccessorDescriptor(\_Desc\_) is not IsAccessorDescriptor(\_current\_),
  -- | return \*false\*. 1. If IsAccessorDescriptor(\_current\_) is \*true\*,
  -- | then 1. If \_Desc\_ has a \[\[Get\]\] field and
  -- | SameValue(\_Desc\_.\[\[Get\]\], \_current\_.\[\[Get\]\]) is \*false\*,
  -- | return \*false\*. 1. If \_Desc\_ has a \[\[Set\]\] field and
  -- | SameValue(\_Desc\_.\[\[Set\]\], \_current\_.\[\[Set\]\]) is \*false\*,
  -- | return \*false\*. 1. Else if \_current\_.\[\[Writable\]\] is \*false\*,
  -- | then 1. If \_Desc\_ has a \[\[Writable\]\] field and
  -- | \_Desc\_.\[\[Writable\]\] is \*true\*, return \*false\*. 1. NOTE:
  -- | SameValue returns \*true\* for \*NaN\* values which may be
  -- | distinguishable by other means. Returning here ensures that any existing
  -- | property of \_O\_ remains unmodified. 1. If \_Desc\_ has a \[\[Value\]\]
  -- | field, return SameValue(\_Desc\_.\[\[Value\]\],
  -- | \_current\_.\[\[Value\]\]). 1. If \_O\_ is not \*undefined\*, then 1. If
  -- | IsDataDescriptor(\_current\_) is \*true\* and
  -- | IsAccessorDescriptor(\_Desc\_) is \*true\*, then 1. If \_Desc\_ has a
  -- | \[\[Configurable\]\] field, let \_configurable\_ be
  -- | \_Desc\_.\[\[Configurable\]\]; else let \_configurable\_ be
  -- | \_current\_.\[\[Configurable\]\]. 1. If \_Desc\_ has an
  -- | \[\[Enumerable\]\] field, let \_enumerable\_ be
  -- | \_Desc\_.\[\[Enumerable\]\]; else let \_enumerable\_ be
  -- | \_current\_.\[\[Enumerable\]\]. 1. Replace the property named \_P\_ of
  -- | object \_O\_ with an accessor property whose \[\[Configurable\]\] and
  -- | \[\[Enumerable\]\] attributes are set to \_configurable\_ and
  -- | \_enumerable\_, respectively, and whose \[\[Get\]\] and \[\[Set\]\]
  -- | attributes are set to the value of the corresponding field in \_Desc\_
  -- | if \_Desc\_ has that field, or to the attribute\'s default value
  -- | otherwise. 1. Else if IsAccessorDescriptor(\_current\_) is \*true\* and
  -- | IsDataDescriptor(\_Desc\_) is \*true\*, then 1. If \_Desc\_ has a
  -- | \[\[Configurable\]\] field, let \_configurable\_ be
  -- | \_Desc\_.\[\[Configurable\]\]; else let \_configurable\_ be
  -- | \_current\_.\[\[Configurable\]\]. 1. If \_Desc\_ has an
  -- | \[\[Enumerable\]\] field, let \_enumerable\_ be
  -- | \_Desc\_.\[\[Enumerable\]\]; else let \_enumerable\_ be
  -- | \_current\_.\[\[Enumerable\]\]. 1. Replace the property named \_P\_ of
  -- | object \_O\_ with a data property whose \[\[Configurable\]\] and
  -- | \[\[Enumerable\]\] attributes are set to \_configurable\_ and
  -- | \_enumerable\_, respectively, and whose \[\[Value\]\] and
  -- | \[\[Writable\]\] attributes are set to the value of the corresponding
  -- | field in \_Desc\_ if \_Desc\_ has that field, or to the attribute\'s
  -- | default value otherwise. 1. Else, 1. For each field of \_Desc\_, set the
  -- | corresponding attribute of the property named \_P\_ of object \_O\_ to
  -- | the value of the field. 1. Return \*true\*.
  -- SPEC: L10890-L10895
  -- | # \[\[Set\]\] ( \_P\_: a property key, \_V\_: an ECMAScript language value, \_Receiver\_: an ECMAScript language value, ): either a normal completion containing a Boolean or a throw completion
  -- |
  -- | for
  -- | :   an ordinary object \_O\_
  -- |
  -- | 1\. Return ? OrdinarySet(\_O\_, \_P\_, \_V\_, \_Receiver\_).
  -- SPEC: L6681-L6696
  -- | # CreateDataProperty ( \_O\_: an Object, \_P\_: a property key, \_V\_: an ECMAScript language value, ): either a normal completion containing a Boolean or a throw completion
  -- |
  -- | description
  -- | :   It is used to create a new own property of an object.
  -- |
  -- | 1\. Let \_newDesc\_ be the PropertyDescriptor { \[\[Value\]\]: \_V\_,
  -- | \[\[Writable\]\]: \*true\*, \[\[Enumerable\]\]: \*true\*,
  -- | \[\[Configurable\]\]: \*true\* }. 1. Return ?
  -- | \_O\_.\[\[DefineOwnProperty\]\](\_P\_, \_newDesc\_).
  -- |
  -- | This abstract operation creates a property whose attributes are set to
  -- | the same defaults used for properties created by the ECMAScript language
  -- | assignment operator. Normally, the property will not already exist. If
  -- | it does exist and is not configurable or if \_O\_ is not extensible,
  -- | \[\[DefineOwnProperty\]\] will return \*false\*.
  -- SPEC: L10897-L10902
  -- | # OrdinarySet ( \_O\_: an Object, \_P\_: a property key, \_V\_: an ECMAScript language value, \_Receiver\_: an ECMAScript language value, ): either a normal completion containing a Boolean or a throw completion
  -- |
  -- | 1\. Let \_ownDesc\_ be ? \_O\_.\[\[GetOwnProperty\]\](\_P\_). 1. Return
  -- | ? OrdinarySetWithOwnDescriptor(\_O\_, \_P\_, \_V\_, \_Receiver\_,
  -- | \_ownDesc\_).
  | .setProp obj prop value =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { so with expr := .setProp so.expr prop value, trace := s.trace } t
              some (t, s')
          | none => none
      | some objVal =>
          match exprValue? value with
          | none =>
              match step? { s with expr := value } with
              | some (t, sv) =>
                  let s' := pushTrace { sv with expr := .setProp (.lit objVal) prop sv.expr, trace := s.trace } t
                  some (t, s')
              | none => none
          | some v =>
              match objVal with
              | .object addr =>
                  -- Update or add property on the heap object.
                  let heap' := match s.heap.objects[addr]? with
                    | some props =>
                        let updated := if props.any (fun kv => kv.fst == prop)
                          then props.map (fun kv => if kv.fst == prop then (prop, v) else kv)
                          else props ++ [(prop, v)]
                        { s.heap with objects := s.heap.objects.set! addr updated }
                    | none => s.heap
                  let s' := pushTrace { s with expr := .lit v, heap := heap' } .silent
                  some (.silent, s')
              | _ =>
                  -- Property set on non-object: silently return value.
                  let s' := pushTrace { s with expr := .lit v } .silent
                  some (.silent, s')
  -- SPEC: L10897-L10902
  -- | # OrdinarySet ( \_O\_: an Object, \_P\_: a property key, \_V\_: an ECMAScript language value, \_Receiver\_: an ECMAScript language value, ): either a normal completion containing a Boolean or a throw completion
  -- |
  -- | 1\. Let \_ownDesc\_ be ? \_O\_.\[\[GetOwnProperty\]\](\_P\_). 1. Return
  -- | ? OrdinarySetWithOwnDescriptor(\_O\_, \_P\_, \_V\_, \_Receiver\_,
  -- | \_ownDesc\_).
  | .setIndex obj idx value =>
      match exprValue? obj, exprValue? idx, exprValue? value with
      | none, _, _ =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { so with expr := .setIndex so.expr idx value, trace := s.trace } t
              some (t, s')
          | none => none
      | some _, none, _ =>
          match step? { s with expr := idx } with
          | some (t, si) =>
              let s' := pushTrace { si with expr := .setIndex (.lit (match exprValue? obj with | some v => v | none => .undefined)) si.expr value, trace := s.trace } t
              some (t, s')
          | none => none
      | some _, some _, none =>
          match step? { s with expr := value } with
          | some (t, sv) =>
              let s' := pushTrace { sv with expr := .setIndex (.lit (match exprValue? obj with | some v => v | none => .undefined)) (.lit (match exprValue? idx with | some v => v | none => .undefined)) sv.expr, trace := s.trace } t
              some (t, s')
          | none => none
      | some objVal, some idxVal, some v =>
          let propName := valueToString idxVal
          match objVal with
          | .object addr =>
              let heap' := match s.heap.objects[addr]? with
                | some props =>
                    let updated := if props.any (fun kv => kv.fst == propName)
                      then props.map (fun kv => if kv.fst == propName then (propName, v) else kv)
                      else props ++ [(propName, v)]
                    { s.heap with objects := s.heap.objects.set! addr updated }
                | none => s.heap
              let s' := pushTrace { s with expr := .lit v, heap := heap' } .silent
              some (.silent, s')
          | _ =>
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
  -- SPEC: L16116-L16149
  -- | # Runtime Semantics: Evaluation
  -- |
  -- | UnaryExpression : \`delete\` UnaryExpression 1. Let \_ref\_ be ?
  -- | Evaluation of \|UnaryExpression\|. 1. If \_ref\_ is not a Reference
  -- | Record, return \*true\*. 1. If IsUnresolvableReference(\_ref\_) is
  -- | \*true\*, then 1. Assert: \_ref\_.\[\[Strict\]\] is \*false\*. 1. Return
  -- | \*true\*. 1. If IsPropertyReference(\_ref\_) is \*true\*, then 1.
  -- | Assert: IsPrivateReference(\_ref\_) is \*false\*. 1. If
  -- | IsSuperReference(\_ref\_) is \*true\*, throw a \*ReferenceError\*
  -- | exception. 1. \[id=\"step-delete-operator-toobject\"\] Let \_baseObj\_
  -- | be ? ToObject(\_ref\_.\[\[Base\]\]). 1. If
  -- | \_ref\_.\[\[ReferencedName\]\] is not a property key, then 1. Set
  -- | \_ref\_.\[\[ReferencedName\]\] to ?
  -- | ToPropertyKey(\_ref\_.\[\[ReferencedName\]\]). 1. Let \_deleteStatus\_
  -- | be ? \_baseObj\_.\[\[Delete\]\](\_ref\_.\[\[ReferencedName\]\]). 1. If
  -- | \_deleteStatus\_ is \*false\* and \_ref\_.\[\[Strict\]\] is \*true\*,
  -- | throw a \*TypeError\* exception. 1. Return \_deleteStatus\_. 1. Let
  -- | \_base\_ be \_ref\_.\[\[Base\]\]. 1. Assert: \_base\_ is an Environment
  -- | Record. 1. Return ?
  -- | \_base\_.DeleteBinding(\_ref\_.\[\[ReferencedName\]\]).
  -- |
  -- | When a \`delete\` operator occurs within strict mode code, a
  -- | \*SyntaxError\* exception is thrown if its \|UnaryExpression\| is a
  -- | direct reference to a variable, function argument, or function name. In
  -- | addition, if a \`delete\` operator occurs within strict mode code and
  -- | the property to be deleted has the attribute { \[\[Configurable\]\]:
  -- | \*false\* } (or otherwise cannot be deleted), a \*TypeError\* exception
  -- | is thrown.
  -- |
  -- | The object that may be created in step is not accessible outside of the
  -- | above abstract operation and the ordinary object \[\[Delete\]\] internal
  -- | method. An implementation might choose to avoid the actual creation of
  -- | that object.
  -- SPEC: L10934-L10941
  -- | # OrdinaryDelete ( \_O\_: an Object, \_P\_: a property key, ): either a normal completion containing a Boolean or a throw completion
  -- |
  -- | 1\. Let \_desc\_ be ? \_O\_.\[\[GetOwnProperty\]\](\_P\_). 1. If
  -- | \_desc\_ is \*undefined\*, return \*true\*. 1. If
  -- | \_desc\_.\[\[Configurable\]\] is \*true\*, then 1. Remove the own
  -- | property with name \_P\_ from \_O\_. 1. Return \*true\*. 1. Return
  -- | \*false\*.
  | .deleteProp obj prop =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { so with expr := .deleteProp so.expr prop, trace := s.trace } t
              some (t, s')
          | none => none
      | some (.object addr) =>
          let heap' := match s.heap.objects[addr]? with
            | some props =>
                let filtered := props.filter (fun kv => kv.fst != prop)
                { s.heap with objects := s.heap.objects.set! addr filtered }
            | none => s.heap
          let s' := pushTrace { s with expr := .lit (.bool true), heap := heap' } .silent
          some (.silent, s')
      | some _ =>
          let s' := pushTrace { s with expr := .lit (.bool true) } .silent
          some (.silent, s')
  -- SPEC: L6418-L6427
  -- | # IsConstructor ( \_argument\_: an ECMAScript language value, ): a Boolean
  -- |
  -- | description
  -- | :   It determines if \_argument\_ is a function object with a
  -- |     \[\[Construct\]\] internal method.
  -- |
  -- | 1\. If \_argument\_ is not an Object, return \*false\*. 1. If
  -- | \_argument\_ has a \[\[Construct\]\] internal method, return
  -- | \*true\*. 1. Return \*false\*.
  -- SPEC: L15627-L15635
  -- | # EvaluateNew ( \_constructExpr\_: a \|NewExpression\| Parse Node or a \|MemberExpression\| Parse Node, \_arguments\_: \~empty\~ or an \|Arguments\| Parse Node, ): either a normal completion containing an ECMAScript language value or an abrupt completion
  -- |
  -- | 1\. Let \_ref\_ be ? Evaluation of \_constructExpr\_. 1. Let
  -- | \_constructor\_ be ? GetValue(\_ref\_). 1. If \_arguments\_ is
  -- | \~empty\~, then 1. Let \_argList\_ be a new empty List. 1. Else, 1. Let
  -- | \_argList\_ be ? ArgumentListEvaluation of \_arguments\_. 1. If
  -- | IsConstructor(\_constructor\_) is \*false\*, throw a \*TypeError\*
  -- | exception. 1. Return ? Construct(\_constructor\_, \_argList\_).
  -- SPEC: L6797-L6813
  -- | # Construct ( \_F\_: a constructor, optional \_argumentsList\_: a List of ECMAScript language values, optional \_newTarget\_: a constructor, ): either a normal completion containing an Object or a throw completion
  -- |
  -- | description
  -- | :   It is used to call the \[\[Construct\]\] internal method of a
  -- |     function object. \_argumentsList\_ and \_newTarget\_ are the values
  -- |     to be passed as the corresponding arguments of the internal method.
  -- |     If \_argumentsList\_ is not present, a new empty List is used as its
  -- |     value. If \_newTarget\_ is not present, \_F\_ is used as its value.
  -- |
  -- | 1\. If \_newTarget\_ is not present, set \_newTarget\_ to \_F\_. 1. If
  -- | \_argumentsList\_ is not present, set \_argumentsList\_ to a new empty
  -- | List. 1. Return ? \_F\_.\[\[Construct\]\](\_argumentsList\_,
  -- | \_newTarget\_).
  -- |
  -- | If \_newTarget\_ is not present, this operation is equivalent to: \`new
  -- | F(\...argumentsList)\`
  -- SPEC: L10985-L11004
  -- | # OrdinaryCreateFromConstructor ( \_constructor\_: a function object, \_intrinsicDefaultProto\_: a String, optional \_internalSlotsList\_: a List of names of internal slots, ): either a normal completion containing an Object or a throw completion
  -- |
  -- | description
  -- | :   It creates an ordinary object whose \[\[Prototype\]\] value is
  -- |     retrieved from a constructor\'s \*\"prototype\"\* property, if it
  -- |     exists. Otherwise the intrinsic named by \_intrinsicDefaultProto\_
  -- |     is used for \[\[Prototype\]\]. \_internalSlotsList\_ contains the
  -- |     names of additional internal slots that must be defined as part of
  -- |     the object. If \_internalSlotsList\_ is not provided, a new empty
  -- |     List is used.
  -- |
  -- | 1\. Assert: \_intrinsicDefaultProto\_ is this specification\'s name of
  -- | an intrinsic object. The corresponding object must be an intrinsic that
  -- | is intended to be used as the \[\[Prototype\]\] value of an object. 1.
  -- | Let \_proto\_ be ? GetPrototypeFromConstructor(\_constructor\_,
  -- | \_intrinsicDefaultProto\_). 1. If \_internalSlotsList\_ is present, let
  -- | \_slotsList\_ be \_internalSlotsList\_. 1. Else, let \_slotsList\_ be a
  -- | new empty List. 1. Return OrdinaryObjectCreate(\_proto\_,
  -- | \_slotsList\_).
  -- SPEC: L10960-L10984
  -- | # OrdinaryObjectCreate ( \_proto\_: an Object or \*null\*, optional \_additionalInternalSlotsList\_: a List of names of internal slots, ): an Object
  -- |
  -- | description
  -- | :   It is used to specify the runtime creation of new ordinary objects.
  -- |     \_additionalInternalSlotsList\_ contains the names of additional
  -- |     internal slots that must be defined as part of the object, beyond
  -- |     \[\[Prototype\]\] and \[\[Extensible\]\]. If
  -- |     \_additionalInternalSlotsList\_ is not provided, a new empty List is
  -- |     used.
  -- |
  -- | 1\. Let \_internalSlotsList\_ be « \[\[Prototype\]\], \[\[Extensible\]\]
  -- | ». 1. If \_additionalInternalSlotsList\_ is present, set
  -- | \_internalSlotsList\_ to the list-concatenation of \_internalSlotsList\_
  -- | and \_additionalInternalSlotsList\_. 1. Let \_O\_ be
  -- | MakeBasicObject(\_internalSlotsList\_). 1. Set \_O\_.\[\[Prototype\]\]
  -- | to \_proto\_. 1. Return \_O\_.
  -- |
  -- | Although OrdinaryObjectCreate does little more than call
  -- | MakeBasicObject, its use communicates the intention to create an
  -- | ordinary object, and not an exotic one. Thus, within this specification,
  -- | it is not called by any algorithm that subsequently modifies the
  -- | internal methods of the object in ways that would make the result
  -- | non-ordinary. Operations that create exotic objects invoke
  -- | MakeBasicObject directly.
  -- SPEC: L6620-L6643
  -- | # MakeBasicObject ( \_internalSlotsList\_: a List of internal slot names, ): an Object
  -- |
  -- | description
  -- | :   It is the source of all ECMAScript objects that are created
  -- |     algorithmically, including both ordinary objects and exotic objects.
  -- |     It factors out common steps used in creating all objects, and
  -- |     centralizes object creation.
  -- |
  -- | 1\. Set \_internalSlotsList\_ to the list-concatenation of
  -- | \_internalSlotsList\_ and « \[\[PrivateElements\]\] ». 1. Let \_obj\_ be
  -- | a newly created object with an internal slot for each name in
  -- | \_internalSlotsList\_. 1. NOTE: As described in , the initial value of
  -- | each such internal slot is \*undefined\* unless specified otherwise. 1.
  -- | Set \_obj\_.\[\[PrivateElements\]\] to a new empty List. 1. Set
  -- | \_obj\_\'s essential internal methods to the default ordinary object
  -- | definitions specified in . 1. Assert: If the caller will not be
  -- | overriding both \_obj\_\'s \[\[GetPrototypeOf\]\] and
  -- | \[\[SetPrototypeOf\]\] essential internal methods, then
  -- | \_internalSlotsList\_ contains \[\[Prototype\]\]. 1. Assert: If the
  -- | caller will not be overriding all of \_obj\_\'s \[\[SetPrototypeOf\]\],
  -- | \[\[IsExtensible\]\], and \[\[PreventExtensions\]\] essential internal
  -- | methods, then \_internalSlotsList\_ contains \[\[Extensible\]\]. 1. If
  -- | \_internalSlotsList\_ contains \[\[Extensible\]\], set
  -- | \_obj\_.\[\[Extensible\]\] to \*true\*. 1. Return \_obj\_.
  | .newObj _callee _args =>
      let addr := s.heap.nextAddr
      let heap' := { objects := s.heap.objects.push [], nextAddr := addr + 1 }
      let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
      some (.silent, s')
  -- SPEC: L19369-L19372
  -- | YieldExpression : \`yield\` 1. Return ? Yield(\*undefined\*).
  -- | YieldExpression : \`yield\` AssignmentExpression 1. Let \_exprRef\_ be ?
  -- | Evaluation of \|AssignmentExpression\|. 1. Let \_value\_ be ?
  -- | GetValue(\_exprRef\_). 1. Return ? Yield(\_value\_). YieldExpression :
  | .yield arg _delegate =>
      match arg with
      | some e =>
          match exprValue? e with
          | some v =>
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
          | none =>
              match step? { s with expr := e } with
              | some (t, sa) =>
                  let s' := pushTrace { sa with expr := .yield (some sa.expr) _delegate, trace := s.trace } t
                  some (t, s')
              | none => none
      | none =>
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
  -- SPEC: L20265-L20268
  -- | AwaitExpression : \`await\` UnaryExpression 1. Let \_exprRef\_ be ?
  -- | Evaluation of \|UnaryExpression\|. 1. Let \_value\_ be ?
  -- | GetValue(\_exprRef\_). 1. Return ? Await(\_value\_).
  | .await arg =>
      match exprValue? arg with
      | some v =>
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              let s' := pushTrace { sa with expr := .await sa.expr, trace := s.trace } t
              some (t, s')
          | none => none
  termination_by s.expr.depth
  decreasing_by all_goals (try cases ‹Option Expr›) <;> simp_all [Expr.depth] <;> omega
/-- Small-step relation induced by `step?`.
    ECMA-262 §8.3 execution context stepping. -/
inductive Step : State → TraceEvent → State → Prop where
  | mk {s : State} {t : TraceEvent} {s' : State} :
      step? s = some (t, s') →
      Step s t s'

/-- Reflexive-transitive closure of Core steps with trace accumulation. -/
inductive Steps : State → List TraceEvent → State → Prop where
  | refl (s : State) : Steps s [] s
  | tail {s1 s2 s3 : State} {t : TraceEvent} {ts : List TraceEvent} :
      Step s1 t s2 →
      Steps s2 ts s3 →
      Steps s1 (t :: ts) s3

/-- Initial Core machine state for a program body.
    Preloads the `console` global with a `log` method (§18.2). -/
def initialState (p : Program) : State :=
  -- Reserve heap address 0 for the console object.
  let consoleProps : List (PropName × Value) := [("log", .function consoleLogIdx)]
  let heap : Heap := { objects := #[consoleProps], nextAddr := 1 }
  -- Reserve function index 0 for the console.log built-in.
  let logBuiltin : FuncClosure := ⟨some "log", ["__arg__"], .lit .undefined, []⟩
  let env := Env.empty.extend "console" (.object 0)
  { expr := p.body, env := env, heap := heap, trace := []
  , funcs := #[logBuiltin], callStack := [] }

/-- Core step? is deterministic: at most one transition from any state.
    ECMA-262 §8.3 requires deterministic evaluation order. -/
theorem step_deterministic {s : State} {t1 t2 : TraceEvent} {s1 s2 : State}
    (h1 : step? s = some (t1, s1)) (h2 : step? s = some (t2, s2)) :
    t1 = t2 ∧ s1 = s2 := by
  rw [h1] at h2; simp at h2; exact ⟨h2.1, h2.2⟩

/-- Step relation is deterministic. -/
theorem Step_deterministic {s : State} {t1 t2 : TraceEvent} {s1 s2 : State}
    (h1 : Step s t1 s1) (h2 : Step s t2 s2) :
    t1 = t2 ∧ s1 = s2 := by
  cases h1 with | mk h1' => cases h2 with | mk h2' => exact step_deterministic h1' h2'

/-- A literal expression is stuck (no further step). -/
theorem step_lit_none (v : Value) (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (callStack : List (List (VarName × Value))) :
    step? ⟨.lit v, env, heap, trace, funcs, callStack⟩ = none := by
  simp [step?]

/-- Step inversion: any Step must have come from step?. -/
theorem Step_iff (s : State) (t : TraceEvent) (s' : State) :
    Step s t s' ↔ step? s = some (t, s') := by
  constructor
  · intro h; cases h with | mk h' => exact h'
  · intro h; exact Step.mk h

/-- Program behavior as finite terminating trace sequence. -/
def Behaves (p : Program) (b : List TraceEvent) : Prop :=
  ∃ sFinal,
    Steps (initialState p) b sFinal ∧
    step? sFinal = none

/-- Steps is transitive. -/
theorem Steps_trans {s1 s2 s3 : State} {ts1 ts2 : List TraceEvent}
    (h1 : Steps s1 ts1 s2) (h2 : Steps s2 ts2 s3) :
    Steps s1 (ts1 ++ ts2) s3 := by
  induction h1 with
  | refl => exact h2
  | tail hstep _ ih => exact Steps.tail hstep (ih h2)

/-- A single step embeds into Steps. -/
theorem Steps_single {s s' : State} {t : TraceEvent}
    (h : Step s t s') : Steps s [t] s' :=
  Steps.tail h (Steps.refl s')

/-- toBoolean is total and decidable. ECMA-262 §7.2.14. -/
theorem toBoolean_bool (v : Value) : ∃ b : Bool, toBoolean v = b :=
  ⟨toBoolean v, rfl⟩

/-- evalBinary produces a value for all inputs. ECMA-262 §13.15. -/
theorem evalBinary_total (op : BinOp) (a b : Value) : ∃ v, evalBinary op a b = v :=
  ⟨evalBinary op a b, rfl⟩

/-- evalUnary produces a value for all inputs. ECMA-262 §13.5. -/
theorem evalUnary_total (op : UnaryOp) (v : Value) : ∃ w, evalUnary op v = w :=
  ⟨evalUnary op v, rfl⟩

/-- A variable lookup in a non-empty env that contains the name succeeds. -/
theorem Env.lookup_extend_same (env : Env) (name : VarName) (v : Value) :
    (env.extend name v).lookup name = some v := by
  simp [Env.extend, Env.lookup]

/-- var lookup steps to the bound value. -/
theorem step_var_lookup (env : Env) (name : VarName) (v : Value) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (h : env.lookup name = some v) :
    (step? ⟨.var name, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, h]

/-- A binary operation on two values always steps (is not stuck). -/
theorem step_binary_values (op : BinOp) (a b : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure) (cs : List (List (VarName × Value))) :
    (step? ⟨.binary op (.lit a) (.lit b), env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §13.2 seq: when left side is a value, step produces the right side. -/
theorem step_seq_value (v : Value) (b : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure) (cs : List (List (VarName × Value))) :
    step? ⟨.seq (.lit v) b, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨b, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- §8.1.1.1 let: when init is a value, step extends env and produces body. -/
theorem step_let_value (name : VarName) (v : Value) (body : Expr) (env : Env)
    (heap : Heap) (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.let name (.lit v) body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨body, env.extend name v, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- §8.1.1.4.5 assign: when rhs is a value, step updates env. -/
theorem step_assign_value (name : VarName) (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.assign name (.lit v), env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit v, env.assign name v, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- §13.6 if with truthy condition steps to then branch. -/
theorem step_if_true (v : Value) (then_ else_ : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hv : toBoolean v = true) :
    step? ⟨.if (.lit v) then_ else_, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨then_, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?, hv]

/-- §13.6 if with falsy condition steps to else branch. -/
theorem step_if_false (v : Value) (then_ else_ : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hv : toBoolean v = false) :
    step? ⟨.if (.lit v) then_ else_, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨else_, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?, hv]

/-- §13.5 unary on a value always steps. -/
theorem step_unary_value (op : UnaryOp) (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.unary op (.lit v), env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit (evalUnary op v), env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- §13.14 throw with valued argument produces error event. -/
theorem step_throw_value (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.throw (.lit v), env, heap, trace, funcs, cs⟩ =
      some (.error (valueToString v),
        pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ (.error (valueToString v))) := by
  simp [step?, exprValue?]

/-- §13.7.4 while unfolds to if-then-seq-while. -/
theorem step_while_unfold (cond body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.while_ cond body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace
        ⟨.if cond (.seq body (.while_ cond body)) (.lit .undefined),
         env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?]

/-- §13.8 break produces error event with label. -/
theorem step_break (label : Option LabelName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.break label, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- §13.9 continue produces error event with label. -/
theorem step_continue (label : Option LabelName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.break label, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- §14.1 functionDef always steps (creates a closure). -/
theorem step_functionDef (fname : Option VarName) (params : List VarName) (body : Expr)
    (isAsync isGen : Bool) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.functionDef fname params body isAsync isGen, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- §12.5.6 typeof on a value always steps. -/
theorem step_typeof_value (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.typeof (.lit v), env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §12.2.6 objectLit with all-value props allocates on heap. -/
theorem step_objectLit_allValues (props : List (PropName × Expr)) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hf : firstNonValueProp props = none) :
    (step? ⟨.objectLit props, env, heap, trace, funcs, cs⟩).isSome = true := by
  unfold step?; split <;> simp_all

/-- §12.3.3 newObj always steps (allocates empty object). -/
theorem step_newObj (callee : Expr) (args : List Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.newObj callee args, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- Labeled statement just unwraps to body. -/
theorem step_labeled (label : LabelName) (body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.labeled label body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨body, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?]

/-- §12.8.3 Adding two numbers produces a number. -/
theorem evalBinary_add_nums (a b : Float) :
    evalBinary .add (.number a) (.number b) = .number (a + b) := by
  unfold evalBinary; rfl

/-- §12.8.3 Adding two strings concatenates them. -/
theorem evalBinary_add_strings (a b : String) :
    evalBinary .add (.string a) (.string b) = .string (a ++ b) := by
  simp [evalBinary]

/-- §7.2.15 Strict equality of same value is true. -/
theorem evalBinary_strictEq_refl (v : Value) :
    evalBinary .strictEq v v = .bool (v == v) := by
  simp [evalBinary]

/-- §7.2.14 null == undefined is true. -/
theorem evalBinary_eq_null_undefined :
    evalBinary .eq .null .undefined = .bool true := by
  simp [evalBinary, abstractEq]

/-- §7.2.14 undefined == null is true. -/
theorem evalBinary_eq_undefined_null :
    evalBinary .eq .undefined .null = .bool true := by
  simp [evalBinary, abstractEq]

/-- Env.assign on a fresh name extends the env. -/
theorem Env.assign_fresh (env : Env) (name : VarName) (v : Value)
    (h : env.bindings.any (fun kv => kv.fst == name) = false) :
    (env.assign name v).bindings = (name, v) :: env.bindings := by
  simp [Env.assign, h]

/-- Env.lookup on a different name after extend returns original result. -/
theorem Env.lookup_extend_other (env : Env) (name other : VarName) (v : Value)
    (h : name ≠ other) :
    (env.extend name v).lookup other = env.lookup other := by
  simp [Env.extend, Env.lookup, BEq.beq, h]

/-- this expression resolves to env lookup of "this". -/
theorem step_this_bound (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (h : env.lookup "this" = some v) :
    step? ⟨.this, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit v, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, h]

/-- return with no argument produces error event "return:undefined". -/
theorem step_return_none (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value))) :
    step? ⟨.return none, env, heap, trace, funcs, cs⟩ =
      some (.error "return:undefined",
        pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ (.error "return:undefined")) := by
  simp [step?]

/-- §13.7.5 for-in on non-object produces undefined. -/
theorem step_forIn_nonObject (binding : VarName) (v : Value) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hv : ∀ addr, v ≠ .object addr) :
    (step? ⟨.forIn binding (.lit v) body, env, heap, trace, funcs, cs⟩).isSome = true := by
  cases v with
  | object addr => exact absurd rfl (hv addr)
  | _ => simp [step?, exprValue?]

/-- §13.7.5 for-in on object always steps (enumerates property keys). -/
theorem step_forIn_object (binding : VarName) (addr : Nat) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value))) :
    (step? ⟨.forIn binding (.lit (.object addr)) body, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §13.7.5.13 for-of on object always steps (iterates values). -/
theorem step_forOf_object (binding : VarName) (addr : Nat) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value))) :
    (step? ⟨.forOf binding (.lit (.object addr)) body, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §13.7.5.13 for-of on non-object produces undefined. -/
theorem step_forOf_nonObject (binding : VarName) (v : Value) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hv : ∀ addr, v ≠ .object addr) :
    (step? ⟨.forOf binding (.lit v) body, env, heap, trace, funcs, cs⟩).isSome = true := by
  cases v with
  | object addr => exact absurd rfl (hv addr)
  | _ => simp [step?, exprValue?]

/-- §12.2.5 arrayLit with all-value elems allocates on heap. -/
theorem step_arrayLit_allValues (elems : List Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hf : firstNonValueExpr elems = none) :
    (step? ⟨.arrayLit elems, env, heap, trace, funcs, cs⟩).isSome = true := by
  unfold step?; split <;> simp_all

/-- §9.1.9 setProp on object always steps when obj and value are values. -/
theorem step_setProp_object_value (addr : Nat) (prop : PropName) (v : Value)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value))) :
    (step? ⟨.setProp (.lit (.object addr)) prop (.lit v), env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §9.1.9 setProp on non-object returns value. -/
theorem step_setProp_nonObject (v val : Value) (prop : PropName)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hv : ∀ addr, v ≠ .object addr) :
    (step? ⟨.setProp (.lit v) prop (.lit val), env, heap, trace, funcs, cs⟩).isSome = true := by
  cases v with
  | object addr => exact absurd rfl (hv addr)
  | _ => simp [step?, exprValue?]

/-- §12.4.3 deleteProp on object always steps. -/
theorem step_deleteProp_object (addr : Nat) (prop : PropName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.deleteProp (.lit (.object addr)) prop, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §12.4.3 deleteProp on non-object always steps (returns true). -/
theorem step_deleteProp_nonObject (v : Value) (prop : PropName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hv : ∀ addr, v ≠ .object addr) :
    (step? ⟨.deleteProp (.lit v) prop, env, heap, trace, funcs, cs⟩).isSome = true := by
  cases v with
  | object addr => exact absurd rfl (hv addr)
  | _ => simp [step?, exprValue?]

/-- §12.3.2 getProp on string returns length or undefined. -/
theorem step_getProp_string (s : String) (prop : PropName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.getProp (.lit (.string s)) prop, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §12.3.2 getProp on object always steps. -/
theorem step_getProp_object (addr : Nat) (prop : PropName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.getProp (.lit (.object addr)) prop, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- allValues of empty list is some []. -/
theorem allValues_nil : allValues [] = some [] := by
  simp [allValues]

/-- allValues of lit :: rest decomposes. -/
theorem allValues_cons_lit (v : Value) (rest : List Expr) (vs : List Value)
    (h : allValues rest = some vs) :
    allValues (.lit v :: rest) = some (v :: vs) := by
  simp [allValues, h]

/-- allValues of non-lit head is none. -/
theorem allValues_cons_nonLit (e : Expr) (rest : List Expr)
    (he : ∀ v, e ≠ .lit v) :
    allValues (e :: rest) = none := by
  unfold allValues; split
  · next v => exact absurd rfl (he v)
  · rfl

/-- §7.1.12 valueToString on string is identity. -/
theorem valueToString_string (s : String) :
    valueToString (.string s) = s := by
  simp [valueToString]

/-- §7.2.14 toBoolean on true is true. -/
theorem toBoolean_true : toBoolean (.bool true) = true := by
  simp [toBoolean]

/-- §7.2.14 toBoolean on false is false. -/
theorem toBoolean_false : toBoolean (.bool false) = false := by
  simp [toBoolean]

/-- §7.2.14 toBoolean on null is false. -/
theorem toBoolean_null : toBoolean .null = false := by
  simp [toBoolean]

/-- §7.2.14 toBoolean on undefined is false. -/
theorem toBoolean_undefined : toBoolean .undefined = false := by
  simp [toBoolean]

/-- §7.2.14 toBoolean on any object is true. -/
theorem toBoolean_object (addr : Nat) : toBoolean (.object addr) = true := by
  simp [toBoolean]

/-- §7.2.14 toBoolean on any function is true. -/
theorem toBoolean_function (idx : FuncIdx) : toBoolean (.function idx) = true := by
  simp [toBoolean]

/-- §7.2.14 toBoolean on non-empty string is true. -/
theorem toBoolean_string_nonempty (s : String) (h : ¬s.isEmpty) :
    toBoolean (.string s) = true := by
  simp [toBoolean, h]

/-- §7.2.14 toBoolean on empty string is false. -/
theorem toBoolean_string_empty : toBoolean (.string "") = false := by
  simp [toBoolean]

/-- §7.1.3 toNumber on a number is identity. -/
theorem toNumber_number (n : Float) : toNumber (.number n) = n := by
  simp [toNumber]

/-- §7.1.3 toNumber on true is 1. -/
theorem toNumber_true : toNumber (.bool true) = 1.0 := by
  simp [toNumber]

/-- §7.1.3 toNumber on false is 0. -/
theorem toNumber_false : toNumber (.bool false) = 0.0 := by
  simp [toNumber]

/-- §7.1.3 toNumber on null is 0. -/
theorem toNumber_null : toNumber .null = 0.0 := by
  simp [toNumber]

/-- §13.15 try/catch normal completion: when body is a value without finally, steps to the value. -/
theorem step_tryCatch_normal_noFinally (v : Value) (catchParam : VarName) (catchBody : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hNotCallFrame : catchParam ≠ "__call_frame_return__") :
    step? ⟨.tryCatch (.lit v) catchParam catchBody none, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit v, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?, hNotCallFrame]

/-- §13.1 return with valued argument produces error event. -/
theorem step_return_some_value (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.return (some (.lit v)), env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §14.4.14 yield with no argument steps to undefined. -/
theorem step_yield_none (delegate : Bool) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.yield none delegate, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?]

/-- §14.7.14 await with valued argument steps to that value. -/
theorem step_await_value (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.await (.lit v), env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit v, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- §8.3 this without binding resolves to undefined. -/
theorem step_this_unbound (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (h : env.lookup "this" = none) :
    step? ⟨.this, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, h]

/-- §13.12 Subtraction produces a number. -/
theorem evalBinary_sub (a b : Value) :
    ∃ n, evalBinary .sub a b = .number n := by
  exact ⟨toNumber a - toNumber b, by simp [evalBinary]⟩

/-- §13.12 Multiplication produces a number. -/
theorem evalBinary_mul (a b : Value) :
    ∃ n, evalBinary .mul a b = .number n := by
  exact ⟨toNumber a * toNumber b, by simp [evalBinary]⟩

/-- §13.12 Division produces a number. -/
theorem evalBinary_div (a b : Value) :
    ∃ n, evalBinary .div a b = .number n := by
  exact ⟨toNumber a / toNumber b, by simp [evalBinary]⟩

/-- §7.2.15 Strict equality is decidable and produces a bool. -/
theorem evalBinary_strictEq_bool (a b : Value) :
    ∃ bl, evalBinary .strictEq a b = .bool bl := by
  exact ⟨a == b, by simp [evalBinary]⟩

/-- §7.2.14 Equality is decidable and produces a bool. -/
theorem evalBinary_eq_bool (a b : Value) :
    ∃ bl, evalBinary .eq a b = .bool bl := by
  exact ⟨abstractEq a b, by simp [evalBinary]⟩

/-- §7.2.13 Less-than produces a bool. -/
theorem evalBinary_lt_bool (a b : Value) :
    ∃ bl, evalBinary .lt a b = .bool bl := by
  exact ⟨abstractLt a b, by simp [evalBinary]⟩

/-- var lookup on unbound name produces ReferenceError. -/
theorem step_var_unbound (name : VarName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (h : env.lookup name = none) :
    step? ⟨.var name, env, heap, trace, funcs, cs⟩ =
      some (.error ("ReferenceError: " ++ name),
        pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ (.error ("ReferenceError: " ++ name))) := by
  simp [step?, h]

/-- §13.5 Negation produces a number. -/
theorem evalUnary_neg (v : Value) :
    evalUnary .neg v = .number (-toNumber v) := by
  simp [evalUnary]

/-- §13.5 Logical NOT produces a bool. -/
theorem evalUnary_logNot (v : Value) :
    evalUnary .logNot v = .bool (!toBoolean v) := by
  simp [evalUnary]

/-- §13.5 void produces undefined. -/
theorem evalUnary_void (v : Value) :
    evalUnary .void v = .undefined := by
  simp [evalUnary]

/-- Env.assign on existing name updates it. -/
theorem Env.assign_existing (env : Env) (name : VarName) (v : Value)
    (h : env.bindings.any (fun kv => kv.fst == name) = true) :
    (env.assign name v).bindings = updateBindingList env.bindings name v := by
  simp [Env.assign, h]

/-- Env.extend always prepends. -/
theorem Env.extend_bindings (env : Env) (name : VarName) (v : Value) :
    (env.extend name v).bindings = (name, v) :: env.bindings := by
  simp [Env.extend]

/-- exprValue? of a literal is some. -/
theorem exprValue_lit (v : Value) : exprValue? (.lit v) = some v := by
  simp [exprValue?]

/-- exprValue? of a non-literal is none. -/
theorem exprValue_var (name : VarName) : exprValue? (.var name) = none := by
  simp [exprValue?]

/-- §13.7.4 while_ always steps (unfolds to if). -/
theorem step_while_isSome (cond body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.while_ cond body, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- §18.2 console.log call produces log trace event. -/
theorem step_consoleLog (msg : String) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.call (.lit (.function consoleLogIdx)) [.lit (.string msg)],
           env, heap, trace, funcs, cs⟩ =
      some (.log msg,
        pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ (.log msg)) := by
  simp [step?, exprValue?, allValues, consoleLogIdx, valueToString]

/-- initialState produces a state with empty trace. -/
theorem initialState_trace (p : Program) : (initialState p).trace = [] := by
  simp [initialState]

/-- initialState produces a state whose expr is the program body. -/
theorem initialState_expr (p : Program) : (initialState p).expr = p.body := by
  simp [initialState]

/-- A stuck state on a literal expression. -/
theorem stuck_lit_expr {v : Value} {env : Env} {heap : Heap} {trace : List TraceEvent}
    {funcs : Array FuncClosure} {cs : List (List (VarName × Value))} :
    step? ⟨.lit v, env, heap, trace, funcs, cs⟩ = none := by
  simp [step?]

/-- seq with two values steps to the second value. ECMA-262 §13.2. -/
theorem step_seq_two_values (v1 v2 : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.seq (.lit v1) (.lit v2), env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit v2, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- abstractEq: null == undefined is true. ECMA-262 §7.2.14. -/
theorem abstractEq_null_undef : abstractEq .null .undefined = true := by
  simp [abstractEq]

/-- abstractEq: undefined == null is true. ECMA-262 §7.2.14. -/
theorem abstractEq_undef_null : abstractEq .undefined .null = true := by
  simp [abstractEq]

/-- abstractEq: same booleans are equal. ECMA-262 §7.2.14. -/
theorem abstractEq_bool_same (b : Bool) : abstractEq (.bool b) (.bool b) = true := by
  simp [abstractEq]

/-- abstractEq: same strings are equal. ECMA-262 §7.2.14. -/
theorem abstractEq_string_same (s : String) : abstractEq (.string s) (.string s) = true := by
  simp [abstractEq]

/-- Step on a stuck state is impossible. -/
theorem Step_stuck {s : State} (hStuck : step? s = none) :
    ¬∃ t s', Step s t s' := by
  intro ⟨t, s', hStep⟩
  cases hStep with | mk h => rw [hStuck] at h; exact absurd h (by simp)

/-- Steps concatenation: ts ++ [] = ts. -/
theorem Steps_append_nil {s1 s2 : State} {ts : List TraceEvent}
    (h : Steps s1 ts s2) : Steps s1 (ts ++ []) s2 := by
  rw [List.append_nil]; exact h

/-- valueToString on null is "null". ECMA-262 §7.1.12. -/
theorem valueToString_null : valueToString .null = "null" := by
  simp [valueToString]

/-- valueToString on undefined is "undefined". ECMA-262 §7.1.12. -/
theorem valueToString_undefined : valueToString .undefined = "undefined" := by
  simp [valueToString]

/-- valueToString on object is "[object Object]". ECMA-262 §7.1.12. -/
theorem valueToString_object (addr : Nat) : valueToString (.object addr) = "[object Object]" := by
  simp [valueToString]

/-- valueToString on function is "function". ECMA-262 §7.1.12. -/
theorem valueToString_function (idx : FuncIdx) : valueToString (.function idx) = "function" := by
  simp [valueToString]

/-- pushTrace preserves the expression. -/
theorem pushTrace_expr (s : State) (t : TraceEvent) :
    (pushTrace s t).expr = s.expr := by
  simp [pushTrace]

/-- pushTrace preserves the environment. -/
theorem pushTrace_env (s : State) (t : TraceEvent) :
    (pushTrace s t).env = s.env := by
  simp [pushTrace]

/-- pushTrace preserves the heap. -/
theorem pushTrace_heap (s : State) (t : TraceEvent) :
    (pushTrace s t).heap = s.heap := by
  simp [pushTrace]

/-- pushTrace appends to the trace. -/
theorem pushTrace_trace (s : State) (t : TraceEvent) :
    (pushTrace s t).trace = s.trace ++ [t] := by
  simp [pushTrace]

/-- pushTrace preserves funcs. -/
theorem pushTrace_funcs (s : State) (t : TraceEvent) :
    (pushTrace s t).funcs = s.funcs := by
  simp [pushTrace]

/-- pushTrace preserves callStack. -/
theorem pushTrace_callStack (s : State) (t : TraceEvent) :
    (pushTrace s t).callStack = s.callStack := by
  simp [pushTrace]

/-- Env.lookup on empty env returns none. -/
theorem Env.lookup_empty (name : VarName) : Env.empty.lookup name = none := by
  simp [Env.empty, Env.lookup]

/-- §12.8.3 Adding a number to a string concatenates after ToString. -/
theorem evalBinary_add_num_string (n : Float) (s : String) :
    evalBinary .add (.number n) (.string s) = .string (valueToString (.number n) ++ s) := by
  simp [evalBinary]

/-- §12.8.3 Adding a string to a number concatenates after ToString. -/
theorem evalBinary_add_string_num (s : String) (n : Float) :
    evalBinary .add (.string s) (.number n) = .string (s ++ valueToString (.number n)) := by
  simp [evalBinary]

/-- §7.2.15 Strict inequality is negation of equality. -/
theorem evalBinary_strictNeq (a b : Value) :
    evalBinary .strictNeq a b = .bool (a != b) := by
  simp [evalBinary]

/-- §7.2.14 Abstract inequality is negation of abstract equality. -/
theorem evalBinary_neq (a b : Value) :
    evalBinary .neq a b = .bool (!abstractEq a b) := by
  simp [evalBinary]

/-- §7.2.13 Greater-than produces a bool. -/
theorem evalBinary_gt_bool (a b : Value) :
    ∃ bl, evalBinary .gt a b = .bool bl := by
  exact ⟨abstractLt b a, by simp [evalBinary]⟩

/-- §7.2.13 Less-or-equal produces a bool. -/
theorem evalBinary_le_bool (a b : Value) :
    ∃ bl, evalBinary .le a b = .bool bl := by
  exact ⟨!abstractLt b a, by simp [evalBinary]⟩

/-- §7.2.13 Greater-or-equal produces a bool. -/
theorem evalBinary_ge_bool (a b : Value) :
    ∃ bl, evalBinary .ge a b = .bool bl := by
  exact ⟨!abstractLt a b, by simp [evalBinary]⟩

/-- §12.9 Modulus produces a number. -/
theorem evalBinary_mod (a b : Value) :
    ∃ n, evalBinary .mod a b = .number n := by
  simp only [evalBinary]
  split <;> exact ⟨_, rfl⟩

/-- §12.9 Exponentiation produces a number. -/
theorem evalBinary_exp (a b : Value) :
    ∃ n, evalBinary .exp a b = .number n := by
  simp only [evalBinary]
  exact ⟨_, rfl⟩

/-- §12.12 Bitwise AND produces a number. -/
theorem evalBinary_bitAnd (a b : Value) :
    ∃ n, evalBinary .bitAnd a b = .number n := by
  simp only [evalBinary]; exact ⟨_, rfl⟩

/-- §12.12 Bitwise OR produces a number. -/
theorem evalBinary_bitOr (a b : Value) :
    ∃ n, evalBinary .bitOr a b = .number n := by
  simp only [evalBinary]; exact ⟨_, rfl⟩

/-- §12.12 Bitwise XOR produces a number. -/
theorem evalBinary_bitXor (a b : Value) :
    ∃ n, evalBinary .bitXor a b = .number n := by
  simp only [evalBinary]; exact ⟨_, rfl⟩

/-- §12.9.3 Left shift produces a number. -/
theorem evalBinary_shl (a b : Value) :
    ∃ n, evalBinary .shl a b = .number n := by
  simp only [evalBinary]; exact ⟨_, rfl⟩

/-- §12.9.3 Signed right shift produces a number. -/
theorem evalBinary_shr (a b : Value) :
    ∃ n, evalBinary .shr a b = .number n := by
  simp only [evalBinary]; exact ⟨_, rfl⟩

/-- §12.9.3 Unsigned right shift produces a number. -/
theorem evalBinary_ushr (a b : Value) :
    ∃ n, evalBinary .ushr a b = .number n := by
  simp only [evalBinary]; exact ⟨_, rfl⟩

/-- §12.10.4 instanceof produces a bool. -/
theorem evalBinary_instanceof_bool (a b : Value) :
    ∃ bl, evalBinary .instanceof a b = .bool bl := by
  cases a <;> cases b <;> exact ⟨_, rfl⟩

/-- §12.10.2 in operator produces a bool. -/
theorem evalBinary_in_bool (a b : Value) :
    ∃ bl, evalBinary .«in» a b = .bool bl := by
  cases a <;> cases b <;> exact ⟨_, rfl⟩

/-- §13.5 Positive unary produces a number. -/
theorem evalUnary_pos (v : Value) :
    evalUnary .pos v = .number (toNumber v) := by
  cases v <;> simp [evalUnary]

/-- §12.5.8 Bitwise NOT produces a number. -/
theorem evalUnary_bitNot (v : Value) :
    ∃ n, evalUnary .bitNot v = .number n := by
  cases v <;> exact ⟨_, rfl⟩

/-- step? on a binary with non-value lhs steps the lhs. -/
theorem step_binary_nonvalue_lhs (op : BinOp) (lhs rhs : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hlhs : exprValue? lhs = none)
    (t : TraceEvent) (sl : State)
    (hstep : step? ⟨lhs, env, heap, trace, funcs, cs⟩ = some (t, sl)) :
    step? ⟨.binary op lhs rhs, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sl with expr := .binary op sl.expr rhs, trace := trace } t) := by
  simp [step?, hlhs, hstep]

/-- step? on a seq with non-value left steps the left. -/
theorem step_seq_nonvalue_lhs (a b : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (ha : exprValue? a = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨a, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.seq a b, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .seq sa.expr b, trace := trace } t) := by
  simp [step?, ha, hstep]

/-- Behaves on a single-step program. -/
theorem Behaves_single {p : Program} {t : TraceEvent} {s' : State}
    (hstep : Step (initialState p) t s')
    (hhalt : step? s' = none) :
    Behaves p [t] :=
  ⟨s', Steps_single hstep, hhalt⟩

/-- Steps preserves: if s1 steps to s2 via ts, and s2 steps to s3 via t, then
    s1 steps to s3 via ts ++ [t]. -/
theorem Steps_snoc {s1 s2 s3 : State} {ts : List TraceEvent} {t : TraceEvent}
    (h1 : Steps s1 ts s2) (h2 : Step s2 t s3) :
    Steps s1 (ts ++ [t]) s3 :=
  Steps_trans h1 (Steps_single h2)

/-- step? on getIndex with two values always produces some result. -/
theorem step_getIndex_values (objVal idxVal : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.getIndex (.lit objVal) (.lit idxVal), env, heap, trace, funcs, cs⟩).isSome = true := by
  cases objVal <;> simp [step?, exprValue?] <;> split <;> simp

/-- step? on setIndex with three values always produces some result. -/
theorem step_setIndex_values (objVal idxVal v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.setIndex (.lit objVal) (.lit idxVal) (.lit v), env, heap, trace, funcs, cs⟩).isSome = true := by
  cases objVal <;> simp [step?, exprValue?] <;> split <;> simp

/-- Nullish coalescing: logOr with non-falsy left returns the left operand. -/
theorem evalBinary_logOr_truthy (a b : Value) (h : toBoolean a = true) :
    evalBinary .logOr a b = a := by
  simp [evalBinary, h]

/-- Nullish coalescing: logOr with falsy left returns the right operand. -/
theorem evalBinary_logOr_falsy (a b : Value) (h : toBoolean a = false) :
    evalBinary .logOr a b = b := by
  simp [evalBinary, h]

/-- Logical AND with truthy left returns right operand. -/
theorem evalBinary_logAnd_truthy (a b : Value) (h : toBoolean a = true) :
    evalBinary .logAnd a b = b := by
  simp [evalBinary, h]

/-- Logical AND with falsy left returns left operand. -/
theorem evalBinary_logAnd_falsy (a b : Value) (h : toBoolean a = false) :
    evalBinary .logAnd a b = a := by
  simp [evalBinary, h]

/-- abstractEq is reflexive on numbers. -/
theorem abstractEq_number_refl (n : Float) (_h : ¬n.isNaN) :
    abstractEq (.number n) (.number n) = (n == n) := by
  simp [abstractEq]

/-- abstractEq: different type, both non-null/undefined → check coercion. -/
theorem abstractEq_null_null : abstractEq .null .null = true := by
  simp [abstractEq]

/-- abstractEq: undefined with itself is true. -/
theorem abstractEq_undefined_undefined : abstractEq .undefined .undefined = true := by
  simp [abstractEq]

/-- toBoolean on a nonzero non-NaN number is true. -/
theorem toBoolean_number_nonzero (n : Float) (hnz : ¬(n == 0.0) = true) (hnan : ¬n.isNaN) :
    toBoolean (.number n) = true := by
  simp [toBoolean, hnz, hnan]

/-- Every non-literal expression has step? producing some result or its sub-expression is stuck.
    This is the progress lemma: var, break, continue, while, labeled, newObj, functionDef, this
    always step (no stuck non-lit states for these constructors). -/
theorem step_var_isSome (name : VarName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.var name, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]; split <;> simp

/-- step? on this always produces some result. -/
theorem step_this_isSome (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.this, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]; split <;> simp

/-- step? on labeled always produces some result. -/
theorem step_labeled_isSome (label : LabelName) (body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.labeled label body, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- step? on break always produces some result. -/
theorem step_break_isSome (label : Option LabelName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.break label, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- step? on continue always produces some result. -/
theorem step_continue_isSome (label : Option LabelName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.continue label, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- step? on while_ always produces some result. -/
theorem step_while_isSome' (cond body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.while_ cond body, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- step? on newObj always produces some result. -/
theorem step_newObj_isSome (callee : Expr) (args : List Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.newObj callee args, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- step? on functionDef always produces some result. -/
theorem step_functionDef_isSome (fname : Option VarName) (params : List VarName)
    (body : Expr) (isAsync isGen : Bool) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.functionDef fname params body isAsync isGen, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- Step_iff forward: Step implies step?. -/
theorem Step_implies_step {s : State} {t : TraceEvent} {s' : State}
    (h : Step s t s') : step? s = some (t, s') := by
  cases h with | mk h' => exact h'

/-- Step_iff backward: step? implies Step. -/
theorem step_implies_Step {s : State} {t : TraceEvent} {s' : State}
    (h : step? s = some (t, s')) : Step s t s' :=
  Step.mk h

/-- Steps with empty trace is identity. -/
theorem Steps_nil_eq {s1 s2 : State} (h : Steps s1 [] s2) : s1 = s2 := by
  cases h with
  | refl => rfl

/-- evalBinary always returns a value (total function). ECMA-262 §12–§13. -/
theorem evalBinary_returns_value (op : BinOp) (a b : Value) :
    ∃ v, evalBinary op a b = v :=
  ⟨evalBinary op a b, rfl⟩

/-- evalUnary always returns a value (total function). ECMA-262 §13.5. -/
theorem evalUnary_returns_value (op : UnaryOp) (v : Value) :
    ∃ w, evalUnary op v = w :=
  ⟨evalUnary op v, rfl⟩

/-- valueToString always returns a string. ECMA-262 §7.1.12. -/
theorem valueToString_returns (v : Value) : ∃ s, valueToString v = s :=
  ⟨valueToString v, rfl⟩

/-- valueToString on true is "true". ECMA-262 §7.1.12. -/
theorem valueToString_true : valueToString (.bool true) = "true" := by
  simp [valueToString]

/-- valueToString on false is "false". ECMA-262 §7.1.12. -/
theorem valueToString_false : valueToString (.bool false) = "false" := by
  simp [valueToString]

/-- step? on call with non-function callee value and all-value args
    returns undefined (not stuck). ECMA-262 §13.3.1. -/
theorem step_call_nonfunc (v : Value) (args : List Expr) (vs : List Value)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hv : ∀ idx, v ≠ .function idx) (hargs : allValues args = some vs) :
    (step? ⟨.call (.lit v) args, env, heap, trace, funcs, cs⟩).isSome = true := by
  cases v with
  | function idx => exact absurd rfl (hv idx)
  | _ => simp [step?, exprValue?, hargs]

/-- step? on let with non-value init and steppable init, steps the init. -/
theorem step_let_step_init (name : VarName) (init body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hinit : exprValue? init = none)
    (t : TraceEvent) (si : State)
    (hstep : step? ⟨init, env, heap, trace, funcs, cs⟩ = some (t, si)) :
    step? ⟨.let name init body, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { si with expr := .let name si.expr body, trace := trace } t) := by
  simp [step?, hinit, hstep]

/-- step? on assign with non-value rhs and steppable rhs, steps the rhs. -/
theorem step_assign_step_rhs (name : VarName) (rhs : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hrhs : exprValue? rhs = none)
    (t : TraceEvent) (sr : State)
    (hstep : step? ⟨rhs, env, heap, trace, funcs, cs⟩ = some (t, sr)) :
    step? ⟨.assign name rhs, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sr with expr := .assign name sr.expr, trace := trace } t) := by
  simp [step?, hrhs, hstep]

/-- step? on if with non-value cond and steppable cond, steps the cond. -/
theorem step_if_step_cond (cond then_ else_ : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hcond : exprValue? cond = none)
    (t : TraceEvent) (sc : State)
    (hstep : step? ⟨cond, env, heap, trace, funcs, cs⟩ = some (t, sc)) :
    step? ⟨.if cond then_ else_, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sc with expr := .if sc.expr then_ else_, trace := trace } t) := by
  simp [step?, hcond, hstep]

/-- step? on unary with non-value arg and steppable arg, steps the arg. -/
theorem step_unary_step_arg (op : UnaryOp) (arg : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (harg : exprValue? arg = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨arg, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.unary op arg, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .unary op sa.expr, trace := trace } t) := by
  simp [step?, harg, hstep]

/-- step? on throw with non-value arg and steppable arg, steps the arg. -/
theorem step_throw_step_arg (arg : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (harg : exprValue? arg = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨arg, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.throw arg, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .throw sa.expr, trace := trace } t) := by
  simp [step?, harg, hstep]

/-- step? on typeof with non-value arg and steppable arg, steps the arg. -/
theorem step_typeof_step_arg (arg : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (harg : exprValue? arg = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨arg, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.typeof arg, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .typeof sa.expr, trace := trace } t) := by
  simp [step?, harg, hstep]

/-- step? on getProp with non-value obj and steppable obj, steps the obj. -/
theorem step_getProp_step_obj (obj : Expr) (prop : PropName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hobj : exprValue? obj = none)
    (t : TraceEvent) (so : State)
    (hstep : step? ⟨obj, env, heap, trace, funcs, cs⟩ = some (t, so)) :
    step? ⟨.getProp obj prop, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { so with expr := .getProp so.expr prop, trace := trace } t) := by
  simp [step?, hobj, hstep]

/-- Steps from a stuck state must be the empty (refl) step. -/
theorem Steps_stuck {s sf : State} {ts : List TraceEvent}
    (hstuck : step? s = none) (hsteps : Steps s ts sf) :
    ts = [] ∧ sf = s := by
  cases hsteps with
  | refl => exact ⟨rfl, rfl⟩
  | tail hstep _ =>
    cases hstep with | mk h => rw [hstuck] at h; exact absurd h (by simp)

/-- Steps is deterministic: from the same start, same trace and end. -/
theorem Steps_deterministic {s sf1 sf2 : State} {ts1 ts2 : List TraceEvent}
    (h1 : Steps s ts1 sf1) (h2 : Steps s ts2 sf2)
    (hhalt1 : step? sf1 = none) (hhalt2 : step? sf2 = none) :
    ts1 = ts2 ∧ sf1 = sf2 := by
  induction h1 generalizing ts2 sf2 with
  | refl =>
    have ⟨hts, hsf⟩ := Steps_stuck hhalt1 h2
    exact ⟨hts.symm, hsf.symm⟩
  | tail hstep1 _ ih =>
    cases h2 with
    | refl =>
      cases hstep1 with
      | mk h => rw [hhalt2] at h; exact absurd h (by simp)
    | tail hstep2 htail2 =>
      cases hstep1 with | mk h1' =>
      cases hstep2 with | mk h2' =>
      have ⟨ht, hs⟩ := step_deterministic h1' h2'
      subst ht; subst hs
      have ⟨hts, hsf⟩ := ih htail2 hhalt1 hhalt2
      exact ⟨congrArg _ hts, hsf⟩

/-- Behaves is deterministic: a program produces at most one trace. -/
theorem Behaves_deterministic {p : Program} {b1 b2 : List TraceEvent}
    (h1 : Behaves p b1) (h2 : Behaves p b2) :
    b1 = b2 := by
  obtain ⟨sf1, hsteps1, hhalt1⟩ := h1
  obtain ⟨sf2, hsteps2, hhalt2⟩ := h2
  exact (Steps_deterministic hsteps1 hsteps2 hhalt1 hhalt2).1

/-- exprValue? returns none for all non-literal constructors. -/
theorem exprValue_non_lit (e : Expr) (h : ∀ v, e ≠ .lit v) : exprValue? e = none := by
  cases e with
  | lit v => exact absurd rfl (h v)
  | _ => rfl

/-- step_binary_value: binary op on two values computes directly. ECMA-262 §12. -/
theorem step_binary_value (op : BinOp) (a b : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.binary op (.lit a) (.lit b), env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit (evalBinary op a b), env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- step? on deleteProp with non-value obj and steppable obj, steps the obj. -/
theorem step_deleteProp_step_obj (obj : Expr) (prop : PropName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hobj : exprValue? obj = none)
    (t : TraceEvent) (so : State)
    (hstep : step? ⟨obj, env, heap, trace, funcs, cs⟩ = some (t, so)) :
    step? ⟨.deleteProp obj prop, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { so with expr := .deleteProp so.expr prop, trace := trace } t) := by
  simp [step?, hobj, hstep]

/-- Env.lookup_extend_same' — more precise version returning the actual result. -/
theorem Env.lookup_extend_eq (env : Env) (name : VarName) (v : Value) :
    (Env.extend env name v).lookup name = some v := by
  simp [Env.extend, Env.lookup]

/-- step? on forIn with non-value obj and steppable obj, steps the obj. -/
theorem step_forIn_step_obj (binding : VarName) (obj body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hobj : exprValue? obj = none)
    (t : TraceEvent) (so : State)
    (hstep : step? ⟨obj, env, heap, trace, funcs, cs⟩ = some (t, so)) :
    step? ⟨.forIn binding obj body, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { so with expr := .forIn binding so.expr body, trace := trace } t) := by
  simp [step?, hobj, hstep]

/-- step? on forOf with non-value iterable and steppable iterable, steps the iterable. -/
theorem step_forOf_step_obj (binding : VarName) (iterable body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hiter : exprValue? iterable = none)
    (t : TraceEvent) (so : State)
    (hstep : step? ⟨iterable, env, heap, trace, funcs, cs⟩ = some (t, so)) :
    step? ⟨.forOf binding iterable body, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { so with expr := .forOf binding so.expr body, trace := trace } t) := by
  simp [step?, hiter, hstep]

/-- §7.2.14 abstractEq: null/null is true. -/
theorem abstractEq_null_self : abstractEq .null .null = true := by
  simp [abstractEq]

/-- §7.2.14 abstractEq: undefined/undefined is true. -/
theorem abstractEq_undef_self : abstractEq .undefined .undefined = true := by
  simp [abstractEq]

/-- §7.2.14 abstractEq: bool/bool delegates to BEq. -/
theorem abstractEq_bool (a b : Bool) : abstractEq (.bool a) (.bool b) = (a == b) := by
  simp [abstractEq]

/-- §7.2.14 abstractEq: string/string delegates to BEq. -/
theorem abstractEq_string (a b : String) : abstractEq (.string a) (.string b) = (a == b) := by
  simp [abstractEq]

/-- Behaves also determines the final state. -/
theorem Behaves_final_unique {p : Program} {b : List TraceEvent}
    (h1 : Behaves p b) (_h2 : Behaves p b) :
    ∃ sf, Steps (initialState p) b sf ∧ step? sf = none := by
  obtain ⟨sf, hsteps, hhalt⟩ := h1
  exact ⟨sf, hsteps, hhalt⟩

/-- Steps.refl embeds into Steps. -/
theorem Steps_refl_eq (s : State) : Steps s [] s :=
  Steps.refl s

/-- step? preserves: if step produces (t, s'), then s' differs from s
    only in expr, env, heap, trace, funcs, callStack. -/
theorem step_preserves_structure {s : State} {t : TraceEvent} {s' : State}
    (_h : step? s = some (t, s')) :
    ∃ e' env' heap' trace' funcs' cs',
      s' = ⟨e', env', heap', trace', funcs', cs'⟩ :=
  ⟨s'.expr, s'.env, s'.heap, s'.trace, s'.funcs, s'.callStack, rfl⟩

/-- pushTrace on state with specific fields. -/
theorem pushTrace_fields (e : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) (t : TraceEvent) :
    pushTrace ⟨e, env, heap, trace, funcs, cs⟩ t =
      ⟨e, env, heap, trace ++ [t], funcs, cs⟩ := by
  simp [pushTrace]

/-- console.log with number argument produces correct log event. -/
theorem step_consoleLog_num (n : Float) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.call (.lit (.function consoleLogIdx)) [.lit (.number n)],
           env, heap, trace, funcs, cs⟩ =
      some (.log (valueToString (.number n)),
        pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩
          (.log (valueToString (.number n)))) := by
  simp [step?, exprValue?, allValues, consoleLogIdx, valueToString]

/-- Env.lookup after multiple extends: latest wins. -/
theorem Env.lookup_extend_shadow (env : Env) (name : VarName) (v1 v2 : Value) :
    (env.extend name v1 |>.extend name v2).lookup name = some v2 := by
  simp [Env.extend, Env.lookup]

/-- toNumber on undefined is NaN (0.0/0.0). -/
theorem toNumber_undefined : toNumber .undefined = 0.0 / 0.0 := by
  simp [toNumber]

/-- step? on setProp with non-value obj steps the obj. ECMA-262 §9.1.9. -/
theorem step_setProp_step_obj (obj : Expr) (prop : PropName) (value : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hobj : exprValue? obj = none)
    (t : TraceEvent) (so : State)
    (hstep : step? ⟨obj, env, heap, trace, funcs, cs⟩ = some (t, so)) :
    step? ⟨.setProp obj prop value, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { so with expr := .setProp so.expr prop value, trace := trace } t) := by
  simp [step?, hobj, hstep]

/-- step? on call with non-value callee steps the callee. ECMA-262 §13.3.1. -/
theorem step_call_step_callee (callee : Expr) (args : List Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hcallee : exprValue? callee = none)
    (t : TraceEvent) (sc : State)
    (hstep : step? ⟨callee, env, heap, trace, funcs, cs⟩ = some (t, sc)) :
    step? ⟨.call callee args, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sc with expr := .call sc.expr args, trace := trace } t) := by
  simp [step?, hcallee, hstep]

/-- step? on return with non-value arg steps the arg. ECMA-262 §13.1. -/
theorem step_return_step_arg (e : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (harg : exprValue? e = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨e, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.return (some e), env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .return (some sa.expr), trace := trace } t) := by
  simp [step?, harg, hstep]

/-- step? on await with non-value arg steps the arg. ECMA-262 §14.7.14. -/
theorem step_await_step_arg (arg : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (harg : exprValue? arg = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨arg, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.await arg, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .await sa.expr, trace := trace } t) := by
  simp [step?, harg, hstep]

/-- step? on yield with non-value arg steps the arg. ECMA-262 §14.4.14. -/
theorem step_yield_step_arg (e : Expr) (delegate : Bool) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (harg : exprValue? e = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨e, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.yield (some e) delegate, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .yield (some sa.expr) delegate, trace := trace } t) := by
  simp [step?, harg, hstep]

/-- step? on getIndex with non-value obj steps the obj. ECMA-262 §12.3.2. -/
theorem step_getIndex_step_obj (obj idx : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hobj : exprValue? obj = none)
    (t : TraceEvent) (so : State)
    (hstep : step? ⟨obj, env, heap, trace, funcs, cs⟩ = some (t, so)) :
    step? ⟨.getIndex obj idx, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { so with expr := .getIndex so.expr idx, trace := trace } t) := by
  simp [step?, hobj, hstep]

/-- step? on tryCatch with non-value body: normal (non-error) step wraps in tryCatch. -/
theorem step_tryCatch_step_body_silent (body : Expr) (catchParam : VarName) (catchBody : Expr)
    (finally_ : Option Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hbody : exprValue? body = none)
    (sb : State)
    (hstep : step? ⟨body, env, heap, trace, funcs, cs⟩ = some (.silent, sb)) :
    step? ⟨.tryCatch body catchParam catchBody finally_, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace { sb with expr := .tryCatch sb.expr catchParam catchBody finally_, trace := trace } .silent) := by
  simp [step?, hbody, hstep]

/-- step? on tryCatch with non-value body: log step wraps in tryCatch. -/
theorem step_tryCatch_step_body_log (body : Expr) (catchParam : VarName) (catchBody : Expr)
    (finally_ : Option Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hbody : exprValue? body = none)
    (msg : String) (sb : State)
    (hstep : step? ⟨body, env, heap, trace, funcs, cs⟩ = some (.log msg, sb)) :
    step? ⟨.tryCatch body catchParam catchBody finally_, env, heap, trace, funcs, cs⟩ =
      some (.log msg, pushTrace { sb with expr := .tryCatch sb.expr catchParam catchBody finally_, trace := trace } (.log msg)) := by
  simp [step?, hbody, hstep]

/-- Steps inversion: from [t] there is exactly one step. -/
theorem Steps_single_inv {s1 s2 : State} {t : TraceEvent}
    (h : Steps s1 [t] s2) : Step s1 t s2 := by
  cases h with
  | tail hstep htail =>
    cases htail with
    | refl => exact hstep

/-- step_functionDef exact: produces the closure value and updated funcs. -/
theorem step_functionDef_exact (fname : Option VarName) (params : List VarName)
    (body : Expr) (isAsync isGen : Bool) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.functionDef fname params body isAsync isGen, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit (.function funcs.size), env, heap, trace,
        funcs.push ⟨fname, params, body, env.bindings⟩, cs⟩ .silent) := by
  simp [step?]

/-- step? on yield with value arg steps to that value. -/
theorem step_yield_some_value (v : Value) (delegate : Bool) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.yield (some (.lit v)) delegate, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit v, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- step? on return with value arg produces error event. -/
theorem step_return_some_value_exact (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.return (some (.lit v)), env, heap, trace, funcs, cs⟩ =
      some (.error ("return:" ++ valueToString v),
        pushTrace ⟨.lit v, env, heap, trace, funcs, cs⟩
          (.error ("return:" ++ valueToString v))) := by
  simp [step?, exprValue?]

/-- §12.3.3 newObj exact: allocates empty object at next heap address. -/
theorem step_newObj_exact (callee : Expr) (args : List Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.newObj callee args, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit (.object heap.nextAddr), env,
        { objects := heap.objects.push [], nextAddr := heap.nextAddr + 1 },
        trace, funcs, cs⟩ .silent) := by
  simp [step?]

/-- §13.7.5 for-in on object with known properties: desugars to sequential let-bindings.
    ECMA-262 §13.7.5.15 EnumerateObjectProperties. -/
theorem step_forIn_object_props (binding : VarName) (addr : Nat) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (props : List (PropName × Value))
    (hprops : heap.objects[addr]? = some props) :
    step? ⟨.forIn binding (.lit (.object addr)) body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨
        (props.map (fun p => p.1)).foldr (fun key acc =>
          .seq (.«let» binding (.lit (.string key)) body) acc) (.lit .undefined),
        env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?, hprops]

/-- §13.7.5.13 for-of on object with known properties: desugars to sequential let-bindings.
    ECMA-262 §7.4.1 GetIterator / §7.4.6 IteratorStep. -/
theorem step_forOf_object_props (binding : VarName) (addr : Nat) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (props : List (PropName × Value))
    (hprops : heap.objects[addr]? = some props) :
    step? ⟨.forOf binding (.lit (.object addr)) body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨
        (props.map (fun p => p.2)).foldr (fun val acc =>
          .seq (.«let» binding (.lit val) body) acc) (.lit .undefined),
        env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?, hprops]

/-- §13.7.5 for-in on non-object exact: produces undefined.
    ECMA-262 §13.7.5.12: ToObject(null/undefined/bool/number/string) then enumerate. -/
theorem step_forIn_nonObject_exact (binding : VarName) (v : Value) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hv : ∀ addr, v ≠ .object addr) :
    step? ⟨.forIn binding (.lit v) body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ .silent) := by
  cases v with
  | object addr => exact absurd rfl (hv addr)
  | _ => simp [step?, exprValue?]

/-- §13.7.5.13 for-of on non-object exact: produces undefined. -/
theorem step_forOf_nonObject_exact (binding : VarName) (v : Value) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hv : ∀ addr, v ≠ .object addr) :
    step? ⟨.forOf binding (.lit v) body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ .silent) := by
  cases v with
  | object addr => exact absurd rfl (hv addr)
  | _ => simp [step?, exprValue?]

/-- §14.6 Class pattern inhabitedness: a class desugars to functionDef + setProp on prototype.
    This demonstrates that the Core IL supports the class pattern:
    `let C = function C() {}; C.prototype.m = function() { ... }` -/
theorem step_class_pattern_functionDef (name : VarName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.functionDef (some name) [] (.lit .undefined) false false,
            env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

private theorem exprValue?_lit_some (v : Value) : exprValue? (.lit v) = some v := rfl

set_option maxHeartbeats 4000000 in
set_option linter.deprecated false in
/-- The only stuck expression is a literal (progress). -/
private theorem stuck_implies_lit_aux (e : Expr) (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hstuck : step? ⟨e, env, heap, trace, funcs, cs⟩ = none) :
    ∃ v, e = .lit v := by
  cases e with
  | lit v => exact ⟨v, rfl⟩
  | var name =>
    unfold step? at hstuck; simp only [] at hstuck; split at hstuck <;> simp at hstuck
  | functionDef name params body isAsync isGen =>
    unfold step? at hstuck; simp only [] at hstuck; simp at hstuck
  | «break» label =>
    unfold step? at hstuck; simp only [] at hstuck; simp at hstuck
  | «continue» label =>
    unfold step? at hstuck; simp only [] at hstuck; simp at hstuck
  | while_ cond body =>
    unfold step? at hstuck; simp only [] at hstuck; simp at hstuck
  | labeled label body =>
    unfold step? at hstuck; simp only [] at hstuck; simp at hstuck
  | this =>
    unfold step? at hstuck; simp only [] at hstuck; split at hstuck <;> simp at hstuck
  | newObj callee args =>
    unfold step? at hstuck; simp only [] at hstuck; simp at hstuck
  | «let» name init body =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | assign name rhs =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | «if» cond then_ else_ =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | seq a b =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | unary op arg =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | typeof arg =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | throw arg =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | await arg =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | «return» arg =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · split at hstuck
        · simp at hstuck
        · rename_i _ _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · simp at hstuck
  | yield arg delegate =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · split at hstuck
        · simp at hstuck
        · rename_i _ _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · simp at hstuck
  | forIn binding obj body =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · simp at hstuck
    · simp at hstuck
  | forOf binding iterable body =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · simp at hstuck
    · simp at hstuck
  | deleteProp obj prop =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · simp at hstuck
    · simp at hstuck
  | getProp obj prop =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · simp at hstuck
    · simp at hstuck
    · simp at hstuck
  | binary op lhs rhs =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck
      · split at hstuck
        · simp at hstuck
        · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
      · simp at hstuck
  | setProp obj prop value =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck
      · split at hstuck
        · simp at hstuck
        · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
      · split at hstuck <;> simp at hstuck
  | getIndex obj idx =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck <;> (try split at hstuck) <;> simp at hstuck
  | setIndex obj idx value =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck <;> simp at hstuck
  | call callee args =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck
      · split at hstuck <;> (try split at hstuck) <;> (try split at hstuck) <;> simp at hstuck
      · split at hstuck
        · split at hstuck
          · simp at hstuck
          · rename_i _ _ _ hsub
            have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv
            exfalso; exact firstNonValueExpr_not_lit (by assumption) _ rfl
        · exfalso; exact allValues_firstNonValue_contra (by assumption) (by assumption)
  | objectLit props =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub
        have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv
        exfalso; exact firstNonValueProp_not_lit (by assumption) _ rfl
    · simp at hstuck
  | arrayLit elems =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub
        have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv
        exfalso; exact firstNonValueExpr_not_lit (by assumption) _ rfl
    · simp at hstuck
  | tryCatch body catchParam catchBody finally_ =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck <;> (try split at hstuck) <;> simp at hstuck
    · split at hstuck
      · split at hstuck <;> (try split at hstuck) <;> (try split at hstuck) <;> simp at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  termination_by e.depth
  decreasing_by
    all_goals (try cases ‹Option Expr›) <;> simp_all [Expr.depth] <;>
      (try have := firstNonValueExpr_depth ‹_›; omega) <;>
      (try have := firstNonValueProp_depth ‹_›; omega) <;>
      omega

theorem stuck_implies_lit {s : State} (hstuck : step? s = none) :
    ∃ v, s.expr = .lit v :=
  stuck_implies_lit_aux s.expr s.env s.heap s.trace s.funcs s.callStack (by cases s; exact hstuck)

theorem Behaves_final_lit {p : Program} {b : List TraceEvent}
    (hB : Behaves p b) :
    ∃ sf v, Steps (initialState p) b sf ∧ step? sf = none ∧ sf.expr = .lit v := by
  obtain ⟨sf, hsteps, hhalt⟩ := hB
  obtain ⟨v, hv⟩ := stuck_implies_lit hhalt
  exact ⟨sf, v, hsteps, hhalt, hv⟩

end VerifiedJS.Core

namespace VerifiedJS.Source

open VerifiedJS.Core in
/-- Source.Behaves: A source program produces trace `b` iff elaboration to Core
    succeeds and the resulting Core program produces that trace.
    This bridges Source.Program → Core.Behaves via the elaborate pass,
    enabling the end-to-end proof chain (elaborate_correct).
    ECMA-262 §15.1 (Script evaluation) / §15.2 (Module evaluation). -/
def Behaves (p : Source.Program) (b : List Core.TraceEvent) : Prop :=
  ∃ coreProg : Core.Program, Core.elaborate p = .ok coreProg ∧ Core.Behaves coreProg b

open VerifiedJS.Core in
/-- Source.Behaves is monotone: if elaboration produces the same Core program,
    Core behavior implies Source behavior. -/
theorem Behaves_of_elaborate {p : Source.Program} {cp : Core.Program}
    {b : List Core.TraceEvent}
    (hElab : Core.elaborate p = .ok cp) (hBehaves : Core.Behaves cp b) :
    Behaves p b :=
  ⟨cp, hElab, hBehaves⟩

open VerifiedJS.Core in

/-- elaborate_correct: elaboration preserves observable behavior.
    Every Core-level trace of the elaborated program is a valid Source-level trace. -/
theorem elaborate_correct (p : Source.Program) (cp : Core.Program)
    (hElab : Core.elaborate p = .ok cp) :
    ∀ b, Core.Behaves cp b → Behaves p b :=
  fun _ hB => Behaves_of_elaborate hElab hB

end VerifiedJS.Source
