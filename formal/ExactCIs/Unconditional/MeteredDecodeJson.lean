/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredDecodeCore

/-! # Metered ASCII JSON parsing

Bounded lexical scans reserve their full possible traversal before inspecting
bytes. This is deliberately conservative (a short scan may spend less work than
reserved). Numeric-token recognition separately charges each list traversal,
digit arithmetic, integer conversion and comparison; it never expands a power
of ten. Recursive syntax construction charges AST/string/container slots before
allocation, and shape limits retain exactly the frozen refusal ordering.
-/
namespace ExactCIs.Unconditional.MeteredDecode

open BoundedJson MeteredProgram

def checkedPrimitive {α : Type} (event : ResourceModel.Event) (amount bits : Nat)
    (body : Unit → Except BoundedJson.Refusal α) : Parser α :=
  ExceptT.mk (primitive event amount bits body)

@[simp] theorem eraseP_checkedPrimitive {α : Type} (e : ResourceModel.Event)
    (n b : Nat) (body : Unit → Except BoundedJson.Refusal α) :
    eraseP (checkedPrimitive e n b body) = body () := rfl

def skip (s : BoundedJson.State) : Program BoundedJson.State :=
  primitive .structural (s.bytes.size - s.offset + 1) 0 (fun _ => BoundedJson.skip s)

@[simp] theorem erase_skip (s : BoundedJson.State) :
    (skip s).erase = BoundedJson.skip s := rfl

def expect (s : BoundedJson.State) (c : Nat) : Parser BoundedJson.State :=
  checkedPrimitive .structural 1 0 (fun _ => BoundedJson.expect s c)

@[simp] theorem erase_expect (s : BoundedJson.State) (c : Nat) :
    eraseP (expect s c) = BoundedJson.expect s c := rfl

def escaped (s : BoundedJson.State) : Parser (Char × BoundedJson.State) := do
  let _ ← liftP (reserve .structural 64)
  -- Reserve every hexadecimal classification comparison/subtraction, byte
  -- conversion, accumulator operation, range test and character conversion.
  -- Four hexadecimal digits have fewer than 64 such operations; every
  -- numeric intermediate fits sixteen bits. Routing is reserved separately.
  checkedPrimitive .integer 64 16 (fun _ => BoundedJson.escaped s)

@[simp] theorem erase_escaped (s : BoundedJson.State) :
    eraseP (escaped s) = BoundedJson.escaped s := by simp [escaped]

def stringLoop (caps : Caps) : Nat → BoundedJson.State → String → Nat →
    Parser (String × BoundedJson.State)
  | 0, _, _, _ => throw (.resource .parserFuel)
  | fuel + 1, s, out, count => do
      let _ ← liftP (reserve .structural)
      if s.offset ≥ s.bytes.size then throw .syntax
      let c := BoundedJson.peek s
      if c = 34 then return (out, BoundedJson.advance s)
      if count ≥ caps.string then throw (.resource .string)
      if c = 92 then
        let (ch, next) ← escaped (BoundedJson.advance s)
        let text ← liftP (push out ch)
        stringLoop caps fuel next text (count + 1)
      else
        if c < 32 || c > 127 then throw .syntax
        let ch ← liftP (primitive .integer 1 7 (fun _ => Char.ofNat c))
        let text ← liftP (push out ch)
        stringLoop caps fuel (BoundedJson.advance s) text (count + 1)

@[simp] theorem erase_stringLoop (caps : Caps) (fuel : Nat) (s : BoundedJson.State)
    (out : String) (count : Nat) :
    eraseP (stringLoop caps fuel s out count) =
      BoundedJson.stringLoop caps fuel s out count := by
  induction fuel generalizing s out count with
  | zero => rfl
  | succ fuel ih => simp [stringLoop, BoundedJson.stringLoop, ih]

def readString (caps : Caps) (s : BoundedJson.State) : Parser (String × BoundedJson.State) := do
  let next ← expect s 34
  stringLoop caps (s.bytes.size + 1) next "" 0

@[simp] theorem erase_readString (caps : Caps) (s : BoundedJson.State) :
    eraseP (readString caps s) = BoundedJson.readString caps s := by
  simp [readString, BoundedJson.readString]

def literal (s : BoundedJson.State) (text : String) (v : Value) :
    Parser (Value × BoundedJson.State) := do
  let _ ← liftP (reserve .decodeItem text.utf8ByteSize)
  let _ ← liftP (primitive .integer text.utf8ByteSize 7 (fun _ => ()))
  checkedPrimitive .structural (text.utf8ByteSize + 1) 0
    (fun _ => BoundedJson.literal s text v)

@[simp] theorem erase_literal (s : BoundedJson.State) (text : String) (v : Value) :
    eraseP (literal s text v) = BoundedJson.literal s text v := by simp [literal]

def spanChars (pred : Char → Bool) (cs : List Char) : Program (List Char × List Char) := do
  let n ← length cs
  let _ ← reserve .decodeItem n
  primitive .structural (2 * n) 0 (fun _ => cs.span pred)

@[simp] theorem erase_spanChars (p : Char → Bool) (cs : List Char) :
    (spanChars p cs).erase = cs.span p := by simp [spanChars]

def allChars (pred : Char → Bool) (cs : List Char) : Program Bool := do
  let n ← length cs
  primitive .structural n 0 (fun _ => cs.all pred)

@[simp] theorem erase_allChars (p : Char → Bool) (cs : List Char) :
    (allChars p cs).erase = cs.all p := by simp [allChars]

def appendChars (left right : List Char) : Program (List Char) := do
  let n ← length left
  let _ ← reserve .structural n
  primitive .decodeItem n 0 (fun _ => left ++ right)

@[simp] theorem erase_appendChars (l r : List Char) :
    (appendChars l r).erase = l ++ r := by simp [appendChars]

def dropZeros (cs : List Char) : Program (List Char) := do
  let n ← length cs
  primitive .structural n 0 (fun _ => cs.dropWhile (· == '0'))

@[simp] theorem erase_dropZeros (cs : List Char) :
    (dropZeros cs).erase = cs.dropWhile (· == '0') := by simp [dropZeros]

def numberText (caps : Caps) (text : String) : Parser Value := do
  let raw ← liftP (chars text)
  let negative := raw.head? == some '-'
  let raw := if negative then raw.tail else raw
  let (whole, rest) ← liftP (spanChars BoundedJson.digit raw)
  let wholeLength ← liftP (length whole)
  if whole.isEmpty || (wholeLength > 1 && whole.head! = '0') then throw .syntax
  let (fraction, rest) ← if rest.head? == some '.' then do
      let (ds, rest) ← liftP (spanChars BoundedJson.digit rest.tail)
      if ds.isEmpty then throw .syntax
      pure (ds, rest)
    else pure ([], rest)
  let exp : Int ← if rest.isEmpty then pure 0 else do
    if rest.head? != some 'e' && rest.head? != some 'E' then throw .syntax
    let rest := rest.tail
    let minus := rest.head? == some '-'
    let ds := if minus || rest.head? == some '+' then rest.tail else rest
    let digits ← liftP (allChars BoundedJson.digit ds)
    if ds.isEmpty || !digits then throw .syntax
    let nDigits ← liftP (length ds)
    if nDigits > caps.digits then throw (.resource .digits)
    let n ← liftP (digitFold ds 0)
    let z ← liftP (ofNat n)
    let neg ← liftP (negate z)
    pure (if minus then neg else z)
  let together ← liftP (appendChars whole fraction)
  let significant ← liftP (dropZeros together)
  if significant.isEmpty then
    if negative then throw .noncanonical else return .number 0
  let allZeros ← liftP (allChars (· == '0') significant.tail)
  if significant.head! != '1' || !allZeros then throw .shape
  let fractionLength ← liftP (length fraction)
  let tailLength ← liftP (length significant.tail)
  let a ← liftP (ofNat fractionLength)
  let b ← liftP (ofNat tailLength)
  let exponent ← liftP (intSub a b)
  let same ← liftP (primitive .integer 1
    (max (MeteredRationalReplay.intBits exp) (MeteredRationalReplay.intBits exponent))
    (fun _ => exp == exponent))
  if !same then throw .shape
  return .number (if negative then -1 else 1)

set_option maxRecDepth 8192 in
@[simp] theorem erase_numberText (caps : Caps) (text : String) :
    eraseP (numberText caps text) = BoundedJson.numberText caps text := by
  simp only [numberText, BoundedJson.numberText, eraseP_bind, eraseP_pure,
    eraseP_throw, eraseP_liftP, eraseP_ite, erase_chars, erase_spanChars,
    erase_length, erase_allChars, erase_digitFold, erase_ofNat, erase_negate,
    erase_appendChars, erase_dropZeros, erase_intSub, erase_primitive,
    except_ok_bind, except_throw_bind, except_throw_map,
    pure_bind, bind_pure_comp, Bool.beq_eq_decide_eq, bne]

/-- The bounded lexical scan has no numeric conversion. Character slots and
    scan steps are reserved before entering this loop. -/
def scanNumber (caps : Caps) (s : BoundedJson.State) :
    Except BoundedJson.Refusal (String × BoundedJson.State) := do
  let mut next := s
  let mut text := ""
  for _ in [:s.bytes.size - s.offset] do
    let c := BoundedJson.peek next
    if BoundedJson.whitespace c || c = 44 || c = 93 || c = 125 then break
    if text.utf8ByteSize ≥ caps.string then throw (.resource .string)
    if c > 127 then throw .syntax
    text := text.push (Char.ofNat c)
    next := BoundedJson.advance next
  return (text, next)

def number (caps : Caps) (s : BoundedJson.State) : Parser (Value × BoundedJson.State) := do
  let _ ← liftP (reserve .decodeItem (min (s.bytes.size - s.offset) caps.string))
  let _ ← liftP (primitive .integer (min (s.bytes.size - s.offset) caps.string) 7 (fun _ => ()))
  let (text, next) ← checkedPrimitive .structural (s.bytes.size - s.offset + 1) 0
    (fun _ => scanNumber caps s)
  return (← numberText caps text, next)

@[simp] theorem erase_number (caps : Caps) (s : BoundedJson.State) :
    eraseP (number caps s) = BoundedJson.number caps s := by
  simp [number, scanNumber, BoundedJson.number]

def hasKeyJson (key : String) : List (String × Value) → Program Bool
  | [] => pure false
  | (name, _) :: rest => do
      let _ ← reserve .structural
      let same ← MeteredDecodeInput.stringEQ name key
      if same then pure true else hasKeyJson key rest


mutual
  def value (caps : Caps) : Nat → Nat → BoundedJson.State → Parser (Value × BoundedJson.State)
    | 0, _, _ => throw (.resource .parserFuel)
    | fuel + 1, depth, state => do
        let _ ← liftP (reserve .structural)
        let s ← liftP (skip state)
        if depth > caps.depth then throw (.resource .depth)
        if s.nodes ≥ caps.nodes then throw (.resource .nodes)
        if s.offset ≥ s.bytes.size then throw .syntax
        let _ ← liftP (reserve .decodeItem)
        let s := { s with nodes := s.nodes + 1 }
        match BoundedJson.peek s with
        | 34 => let (text, next) ← readString caps s; return (.string text, next)
        | 91 => arrayJson caps fuel depth (← liftP (skip (BoundedJson.advance s))) [] 0
        | 123 => objectJson caps fuel depth (← liftP (skip (BoundedJson.advance s))) [] 0
        | 110 => literal s "null" .null
        | 45 | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57 => number caps s
        | _ => throw .syntax

  def arrayJson (caps : Caps) : Nat → Nat → BoundedJson.State → List Value → Nat →
      Parser (Value × BoundedJson.State)
    | 0, _, _, _, _ => throw (.resource .parserFuel)
    | fuel + 1, depth, s, rev, count => do
        let _ ← liftP (reserve .structural)
        if BoundedJson.peek s = 93 then
          return (.array (← liftP (reverse rev)), BoundedJson.advance s)
        if count ≥ caps.array then throw (.resource .array)
        let (item, next) ← value caps fuel (depth + 1) s
        let _ ← liftP (reserve .decodeItem)
        let next ← liftP (skip next)
        if BoundedJson.peek next = 93 then
          return (.array (← liftP (reverse (item :: rev))), BoundedJson.advance next)
        let next ← expect next 44
        let next ← liftP (skip next)
        if BoundedJson.peek next = 93 then throw .syntax
        arrayJson caps fuel depth next (item :: rev) (count + 1)

  def objectJson (caps : Caps) : Nat → Nat → BoundedJson.State → List (String × Value) → Nat →
      Parser (Value × BoundedJson.State)
    | 0, _, _, _, _ => throw (.resource .parserFuel)
    | fuel + 1, depth, s, rev, count => do
        let _ ← liftP (reserve .structural)
        if BoundedJson.peek s = 125 then
          return (.object (← liftP (reverse rev)), BoundedJson.advance s)
        if count ≥ caps.object then throw (.resource .object)
        let (key, next) ← readString caps s
        if ← liftP (hasKeyJson key rev) then throw .duplicateKey
        let next ← expect (← liftP (skip next)) 58
        let (item, next) ← value caps fuel (depth + 1) next
        let _ ← liftP (reserve .decodeItem)
        let next ← liftP (skip next)
        if BoundedJson.peek next = 125 then
          return (.object (← liftP (reverse ((key, item) :: rev))), BoundedJson.advance next)
        let next ← expect next 44
        let next ← liftP (skip next)
        if BoundedJson.peek next = 125 then throw .syntax
        objectJson caps fuel depth next ((key, item) :: rev) (count + 1)


end

@[simp] theorem erase_hasKeyJson (key : String) (fs : List (String × Value)) :
    (hasKeyJson key fs).erase = fs.any (fun p => p.1 == key) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
      rcases p with ⟨name, value⟩
      simp [hasKeyJson, List.any_cons, ih, Bool.beq_eq_decide_eq]

theorem erase_json (caps : Caps) (fuel : Nat) :
    (∀ depth s, eraseP (value caps fuel depth s) = BoundedJson.value caps fuel depth s) ∧
    (∀ depth s rev count, eraseP (arrayJson caps fuel depth s rev count) =
      BoundedJson.array caps fuel depth s rev count) ∧
    (∀ depth s rev count, eraseP (objectJson caps fuel depth s rev count) =
      BoundedJson.object caps fuel depth s rev count) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro depth s; simp [value, BoundedJson.value]; rfl
      · intro depth s rev count; simp [arrayJson, BoundedJson.array]; rfl
      · intro depth s rev count; simp [objectJson, BoundedJson.object]; rfl
  | succ fuel ih =>
      rcases ih with ⟨hv, ha, ho⟩
      refine ⟨?_, ?_, ?_⟩
      · intro depth s
        simp [value, BoundedJson.value]
        repeat' split
        all_goals simp_all
      · intro depth s rev count
        simp [arrayJson, BoundedJson.array, hv, ha]; rfl
      · intro depth s rev count
        simp [objectJson, BoundedJson.object, hv, ho]; rfl

@[simp] theorem erase_value (caps : Caps) (fuel depth : Nat) (s : BoundedJson.State) :
    eraseP (value caps fuel depth s) = BoundedJson.value caps fuel depth s :=
  (erase_json caps fuel).1 depth s

@[simp] theorem erase_arrayJson (caps : Caps) (fuel depth : Nat) (s : BoundedJson.State)
    (rev : List Value) (count : Nat) :
    eraseP (arrayJson caps fuel depth s rev count) = BoundedJson.array caps fuel depth s rev count :=
  (erase_json caps fuel).2.1 depth s rev count

@[simp] theorem erase_objectJson (caps : Caps) (fuel depth : Nat) (s : BoundedJson.State)
    (rev : List (String × Value)) (count : Nat) :
    eraseP (objectJson caps fuel depth s rev count) = BoundedJson.object caps fuel depth s rev count :=
  (erase_json caps fuel).2.2 depth s rev count

def parse (caps : Caps) (bytes : ByteArray) : Parser Value := do
  if bytes.size > caps.bytes then throw (.resource .bytes)
  let _ ← liftP (reserve .admitBytes bytes.size)
  let (out, state) ← value caps (2 * bytes.size + 2) 0 ⟨bytes, 0, 0⟩
  let final ← liftP (skip state)
  if final.offset ≠ bytes.size then throw .syntax
  pure out

@[simp] theorem erase_parse (caps : Caps) (bytes : ByteArray) :
    eraseP (parse caps bytes) = BoundedJson.parse caps bytes := by
  simp [parse, BoundedJson.parse]

end ExactCIs.Unconditional.MeteredDecode
