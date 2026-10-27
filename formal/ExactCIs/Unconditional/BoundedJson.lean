/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import Lean

/-! # Bounded JSON syntax for the ASCII-only frozen certificate vocabulary

The parser retains object pairs and rejects duplicate *decoded* keys. It builds
no unbounded JSON number: the only numeric values in this vocabulary are -1, 0,
and 1. Equivalent decimal/exponent spellings are recognized exactly, without
constructing powers of ten. Integers used for arithmetic are strings. Every
container slot, node and decoded string character is checked before insertion.
ASCII Unicode escapes and escaped slashes are accepted, so escaped duplicate
keys cannot bypass the duplicate check. No successful schema value needs a
non-ASCII character. This is a development decoder, not work-metered replay.
-/
namespace ExactCIs.Unconditional.BoundedJson

inductive Limit where
  | bytes | depth | nodes | array | object | string | digits | degree
  | coefficients | exponent | groupTotal | leaves | parserFuel
  deriving DecidableEq, Repr

inductive Refusal where
  | syntax | duplicateKey | fields | shape | noncanonical | invalidInput
  | resource (limit : Limit)
  deriving DecidableEq, Repr

/-- Trusted outer caps. Input/payload bytes are never allowed to raise them. -/
structure Caps where
  bytes : Nat := 2000000
  depth : Nat := 64
  nodes : Nat := 200000
  array : Nat := 20000
  object : Nat := 32
  string : Nat := 2048
  digits : Nat := 1024
  degree : Nat := 128
  coefficients : Nat := 20000
  exponent : Nat := 128
  groupTotal : Nat := 128
  deriving Repr

inductive Value where
  | null
  | number (value : Int)
  | string (value : String)
  | array (values : List Value)
  | object (fields : List (String × Value))
  deriving Repr, BEq

structure State where
  bytes : ByteArray
  offset : Nat := 0
  nodes : Nat := 0

abbrev Parser (α : Type) := Except Refusal α

def peek (s : State) : Nat := (s.bytes[s.offset]?).getD 0 |>.toNat
def advance (s : State) (n : Nat := 1) : State := { s with offset := s.offset + n }
def whitespace (c : Nat) : Bool := c = 32 || c = 9 || c = 10 || c = 13

def skip (s : State) : State := Id.run do
  let mut out := s
  for _ in [:s.bytes.size - s.offset] do
    if whitespace (peek out) then out := advance out else break
  return out

def expect (s : State) (c : Nat) : Parser State :=
  if s.offset < s.bytes.size && peek s = c then .ok (advance s) else .error .syntax

def hex (c : Nat) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c - 48)
  else if 65 ≤ c && c ≤ 70 then some (c - 55)
  else if 97 ≤ c && c ≤ 102 then some (c - 87) else none

def escaped (s : State) : Parser (Char × State) := do
  let c := peek s
  if c = 117 then
    let mut out := advance s
    let mut n := 0
    for _ in [:4] do
      let some h := hex (peek out) | throw .syntax
      if out.offset ≥ out.bytes.size then throw .syntax
      n := 16 * n + h
      out := advance out
    if n > 127 then throw .shape
    return (Char.ofNat n, out)
  else
    let decoded ← match c with
      | 34 => pure '"' | 92 => pure '\\' | 47 => pure '/'
      | 98 => pure '\x08' | 102 => pure '\x0c' | 110 => pure '\n'
      | 114 => pure '\r' | 116 => pure '\t'
      | _ => throw .syntax
    return (decoded, advance s)

def stringLoop (caps : Caps) : Nat → State → String → Nat → Parser (String × State)
  | 0, _, _, _ => .error (.resource .parserFuel)
  | fuel + 1, s, out, count => do
    if s.offset ≥ s.bytes.size then throw .syntax
    let c := peek s
    if c = 34 then return (out, advance s)
    if count ≥ caps.string then throw (.resource .string)
    if c = 92 then
      let (ch, next) ← escaped (advance s)
      stringLoop caps fuel next (out.push ch) (count + 1)
    else
      if c < 32 || c > 127 then throw .syntax
      stringLoop caps fuel (advance s) (out.push (Char.ofNat c)) (count + 1)

def readString (caps : Caps) (s : State) : Parser (String × State) := do
  let next ← expect s 34
  stringLoop caps (s.bytes.size + 1) next "" 0

def literal (s : State) (text : String) (value : Value) : Parser (Value × State) := do
  let mut out := s
  for c in text.toList do out ← expect out c.toNat
  return (value, out)

def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- Exact sign-token recognition. Exponent text is bounded before conversion;
no mantissa bignum or exponential expansion is performed. -/
def numberText (caps : Caps) (text : String) : Parser Value := do
  let raw := text.toList
  let negative := raw.head? == some '-'
  let raw := if negative then raw.tail else raw
  let (whole, rest) := raw.span digit
  if whole.isEmpty || (whole.length > 1 && whole.head! = '0') then throw .syntax
  let (fraction, rest) ← if rest.head? == some '.' then do
      let (ds, rest) := rest.tail.span digit
      if ds.isEmpty then throw .syntax
      pure (ds, rest)
    else pure ([], rest)
  let exp : Int ← if rest.isEmpty then pure 0 else do
    if rest.head? != some 'e' && rest.head? != some 'E' then throw .syntax
    let rest := rest.tail
    let minus := rest.head? == some '-'
    let ds := if minus || rest.head? == some '+' then rest.tail else rest
    if ds.isEmpty || !ds.all digit then throw .syntax
    if ds.length > caps.digits then throw (.resource .digits)
    let n := ds.foldl (fun n c => 10 * n + (c.toNat - 48)) 0
    pure (if minus then -Int.ofNat n else Int.ofNat n)
  let significant := (whole ++ fraction).dropWhile (· == '0')
  if significant.isEmpty then
    if negative then throw .noncanonical else return .number 0
  if significant.head! != '1' || !significant.tail.all (· == '0') then throw .shape
  if exp != (Int.ofNat fraction.length - Int.ofNat significant.tail.length) then throw .shape
  return .number (if negative then -1 else 1)

def number (caps : Caps) (s : State) : Parser (Value × State) := do
  let mut next := s
  let mut text := ""
  for _ in [:s.bytes.size - s.offset] do
    let c := peek next
    if whitespace c || c = 44 || c = 93 || c = 125 then break
    if text.utf8ByteSize ≥ caps.string then throw (.resource .string)
    if c > 127 then throw .syntax
    text := text.push (Char.ofNat c)
    next := advance next
  return (← numberText caps text, next)

mutual
  def value (caps : Caps) : Nat → Nat → State → Parser (Value × State)
    | 0, _, _ => .error (.resource .parserFuel)
    | fuel + 1, depth, state => do
      let s := skip state
      if depth > caps.depth then throw (.resource .depth)
      if s.nodes ≥ caps.nodes then throw (.resource .nodes)
      if s.offset ≥ s.bytes.size then throw .syntax
      let s := { s with nodes := s.nodes + 1 }
      match peek s with
      | 34 => let (text, next) ← readString caps s; return (.string text, next)
      | 91 => array caps fuel depth (skip (advance s)) [] 0
      | 123 => object caps fuel depth (skip (advance s)) [] 0
      | 110 => literal s "null" .null
      | 45 | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57 => number caps s
      | _ => throw .syntax

  def array (caps : Caps) : Nat → Nat → State → List Value → Nat → Parser (Value × State)
    | 0, _, _, _, _ => .error (.resource .parserFuel)
    | fuel + 1, depth, s, rev, count => do
      if peek s = 93 then return (.array rev.reverse, advance s)
      if count ≥ caps.array then throw (.resource .array)
      let (item, next) ← value caps fuel (depth + 1) s
      let next := skip next
      if peek next = 93 then return (.array (item :: rev).reverse, advance next)
      let next ← expect next 44
      let next := skip next
      if peek next = 93 then throw .syntax
      array caps fuel depth next (item :: rev) (count + 1)

  def object (caps : Caps) : Nat → Nat → State → List (String × Value) → Nat →
      Parser (Value × State)
    | 0, _, _, _, _ => .error (.resource .parserFuel)
    | fuel + 1, depth, s, rev, count => do
      if peek s = 125 then return (.object rev.reverse, advance s)
      if count ≥ caps.object then throw (.resource .object)
      let (key, next) ← readString caps s
      if rev.any (fun entry => entry.1 == key) then throw .duplicateKey
      let next ← expect (skip next) 58
      let (item, next) ← value caps fuel (depth + 1) next
      let next := skip next
      if peek next = 125 then return (.object ((key, item) :: rev).reverse, advance next)
      let next ← expect next 44
      let next := skip next
      if peek next = 125 then throw .syntax
      object caps fuel depth next ((key, item) :: rev) (count + 1)
end

def parse (caps : Caps) (bytes : ByteArray) : Parser Value := do
  if bytes.size > caps.bytes then throw (.resource .bytes)
  let (out, state) ← value caps (2 * bytes.size + 2) 0 ⟨bytes, 0, 0⟩
  if (skip state).offset ≠ bytes.size then throw .syntax
  return out

theorem parse_over_limit (caps : Caps) (bytes : ByteArray) (large : bytes.size > caps.bytes) :
    parse caps bytes = .error (.resource .bytes) := by
  unfold parse
  simp only [large, ite_true]
  rfl

end ExactCIs.Unconditional.BoundedJson
