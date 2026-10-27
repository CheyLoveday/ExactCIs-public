/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredDecodeCore

/-! # Metered frozen-record decoding

Object lookup visits every inspected pair and charges decoded-key equality.
Decimal conversion charges each digit multiplication and addition. Rational
canonicality charges gcd, casts, comparisons and division separately. Typed
container slots are reserved before construction, in addition to the JSON AST
slots. Limits precede expansion. Successful erasure is exactly the frozen
decoder, including its coefficient-state transitions and refusal order.
-/
namespace ExactCIs.Unconditional.MeteredDecode

open BoundedJson MeteredProgram

def require (condition : Bool) (reason : BoundedJson.Refusal := .shape) : Decode Unit :=
  if condition then pure () else throw reason

@[simp] theorem erase_require (c : Bool) (e : BoundedJson.Refusal) :
    eraseD (require c e) = GlobalCheckerDecode.require c e := by
  cases c <;> rfl

def hasKey (key : String) : List (String × Value) → Program Bool
  | [] => pure false
  | (name, _) :: rest => do
      let _ ← reserve .structural
      let same ← MeteredDecodeInput.stringEQ name key
      if same then pure true else hasKey key rest

@[simp] theorem erase_hasKey (key : String) (fs : List (String × Value)) :
    (hasKey key fs).erase = fs.any (fun p => p.1 == key) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
      rcases p with ⟨name, value⟩
      simp [hasKey, List.any_cons, ih, Bool.beq_eq_decide_eq]

def allKeys (fs : List (String × Value)) : List String → Program Bool
  | [] => pure true
  | key :: rest => do
      let _ ← reserve .structural
      let found ← hasKey key fs
      if found then allKeys fs rest else pure false

@[simp] theorem erase_allKeys (fs : List (String × Value)) (keys : List String) :
    (allKeys fs keys).erase = keys.all (fun k => fs.any (fun p => p.1 == k)) := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simp [allKeys, List.all_cons, ih, Bool.beq_eq_decide_eq]

def record (keys : List String) : Value → Decode (List (String × Value))
  | .object fs => do
      let n ← liftD (length fs)
      let k ← liftD (length keys)
      let valid ← liftD (allKeys fs keys)
      require (n == k && valid) .fields
      pure fs
  | _ => throw .shape

@[simp] theorem erase_record (keys : List String) (v : Value) :
    eraseD (record keys v) = GlobalCheckerDecode.record keys v := by
  cases v <;> simp [record, GlobalCheckerDecode.record]

def lookup (fs : List (String × Value)) (key : String) : Program Value :=
  match fs with
  | [] => pure .null
  | (name, value) :: rest => do
      let _ ← reserve .structural
      let same ← MeteredDecodeInput.stringEQ name key
      if same then pure value else lookup rest key

@[simp] theorem erase_lookup (fs : List (String × Value)) (key : String) :
    (lookup fs key).erase = GlobalCheckerDecode.field fs key := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
      rcases p with ⟨name, value⟩
      simp [lookup, GlobalCheckerDecode.field, List.find?_cons, ih, Bool.beq_eq_decide_eq]
      split <;> simp_all [GlobalCheckerDecode.field, Bool.beq_eq_decide_eq]

def field (fs : List (String × Value)) (key : String) : Decode Value :=
  liftD (lookup fs key)

@[simp] theorem erase_field (fs : List (String × Value)) (key : String) :
    eraseD (field fs key) = pure (GlobalCheckerDecode.field fs key) := by simp [field]

def text : Value → Decode String
  | .string s => pure s
  | _ => throw .shape

@[simp] theorem erase_text (v : Value) :
    eraseD (text v) = GlobalCheckerDecode.text v := by cases v <;> rfl

def tag (v : Value) : Decode String := do
  match v with
  | .object fs =>
      let s ← text (← field fs "kind")
      -- Every frozen sum has at most sixteen alternatives. This reserves all
      -- literal-string comparisons before the subsequent fixed tag dispatch.
      let _ ← liftD (reserve .structural (16 * (s.utf8ByteSize + 1)))
      pure s
  | _ => throw .shape

@[simp] theorem erase_tag (v : Value) :
    eraseD (tag v) = GlobalCheckerDecode.tag v := by
  cases v <;> simp [tag, GlobalCheckerDecode.tag]

def literalText (expected : String) (v : Value) : Decode String := do
  let s ← text v
  require (← liftD (MeteredDecodeInput.stringEQ s expected))
  pure s

@[simp] theorem erase_literalText (expected : String) (v : Value) :
    eraseD (literalText expected v) = GlobalCheckerDecode.literalText expected v := by
  simp [literalText, GlobalCheckerDecode.literalText, Bool.beq_eq_decide_eq]

def mapD {α : Type} (decode : Value → Decode α) : List Value → Decode (List α)
  | [] => pure []
  | v :: vs => do
      let _ ← liftD (reserve .structural)
      let _ ← liftD (reserve .decodeItem)
      let a ← decode v
      let rest ← mapD decode vs
      pure (a :: rest)

@[simp] theorem erase_mapD {α : Type} (decode : Value → Decode α) (vs : List Value) :
    eraseD (mapD decode vs) = vs.mapM (fun v => eraseD (decode v)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [mapD, List.mapM_cons, ih]

def array {α : Type} (decode : Value → Decode α) : Value → Decode (List α)
  | .array vs => mapD decode vs
  | _ => throw .shape

@[simp] theorem erase_array {α : Type} (decode : Value → Decode α) (v : Value) :
    eraseD (array decode v) = GlobalCheckerDecode.array (fun v => eraseD (decode v)) v := by
  cases v <;> simp [array, GlobalCheckerDecode.array]

def optional {α : Type} (decode : Value → Decode α) : Value → Decode (Option α)
  | .null => pure none
  | v => return some (← decode v)

@[simp] theorem erase_optional {α : Type} (decode : Value → Decode α) (v : Value) :
    eraseD (optional decode v) = GlobalCheckerDecode.optional (fun v => eraseD (decode v)) v := by
  cases v <;> simp [optional, GlobalCheckerDecode.optional]

def decimal (caps : Caps) (s : String) : Decode Nat := do
  require (s.utf8ByteSize ≤ caps.digits) (.resource .digits)
  let cs ← liftD (chars s)
  let n ← liftD (length cs)
  let allDigits ← liftD (primitive .structural n 0
    (fun _ => cs.all (fun c => '0' ≤ c && c ≤ '9')))
  require (!cs.isEmpty && allDigits && (n == 1 || cs.head! != '0')) .noncanonical
  liftD (digitFold cs 0)

@[simp] theorem erase_decimal (caps : Caps) (s : String) :
    eraseD (decimal caps s) = GlobalCheckerDecode.decimal caps s := by
  simp [decimal, GlobalCheckerDecode.decimal]

def natural (caps : Caps) (v : Value) : Decode Nat := do decimal caps (← text v)

@[simp] theorem erase_natural (caps : Caps) (v : Value) :
    eraseD (natural caps v) = GlobalCheckerDecode.natural caps v := by
  simp [natural, GlobalCheckerDecode.natural]

def integerText (caps : Caps) (s : String) : Decode Int := do
  require (s.utf8ByteSize ≤ caps.digits + 1) (.resource .digits)
  match ← liftD (chars s) with
  | '-' :: cs =>
      let tail ← liftD (fromChars cs)
      let n ← decimal caps tail
      require (!(← liftD (primitive .integer 1 (MeteredRationalReplay.natBits n)
        (fun _ => n == 0)))) .noncanonical
      let z ← liftD (ofNat n)
      liftD (negate z)
  | _ => liftD (ofNat (← decimal caps s))

@[simp] theorem erase_integerText (caps : Caps) (s : String) :
    eraseD (integerText caps s) = (do
      GlobalCheckerDecode.require (s.utf8ByteSize ≤ caps.digits + 1) (.resource .digits)
      match s.toList with
      | '-' :: cs =>
          let n ← GlobalCheckerDecode.decimal caps (String.ofList cs)
          GlobalCheckerDecode.require (n != 0) .noncanonical
          pure (-Int.ofNat n)
      | _ => return Int.ofNat (← GlobalCheckerDecode.decimal caps s)) := by
  cases h : s.toList with
  | nil => simp [integerText, h]
  | cons c cs =>
      by_cases hc : c = '-'
      · subst c; simp [integerText, h, bne]
      · simp [integerText, h, hc]

def integer (caps : Caps) (v : Value) : Decode Int := do integerText caps (← text v)

@[simp] theorem erase_integer (caps : Caps) (v : Value) :
    eraseD (integer caps v) = GlobalCheckerDecode.integer caps v := by
  simp [integer, GlobalCheckerDecode.integer]; rfl

def gcd (n : Int) (d : Nat) : Program Nat :=
  primitive .integer 1 (max (MeteredRationalReplay.intBits n) (MeteredRationalReplay.natBits d))
    (fun _ => n.natAbs.gcd d)

@[simp] theorem erase_gcd (n : Int) (d : Nat) : (gcd n d).erase = n.natAbs.gcd d := rfl

def ratOfInt (n : Int) : Program Rat :=
  primitive .integer 1 (max 1 (MeteredRationalReplay.intBits n)) (fun _ => (n : Rat))

@[simp] theorem erase_ratOfInt (n : Int) : (ratOfInt n).erase = (n : Rat) := rfl

def ratOfNat (n : Nat) : Program Rat :=
  primitive .integer 1 (max 1 (MeteredRationalReplay.natBits n)) (fun _ => (n : Rat))

@[simp] theorem erase_ratOfNat (n : Nat) : (ratOfNat n).erase = (n : Rat) := rfl

def rational (caps : Caps) (v : Value) : Decode Rat := do
  let fs ← record ["numerator", "denominator"] v
  let n ← integer caps (← field fs "numerator")
  let d ← natural caps (← field fs "denominator")
  let positive ← liftD (MeteredDecodeInput.positiveNat d)
  let g ← liftD (gcd n d)
  let canonical ← liftD (primitive .integer 1 (MeteredRationalReplay.natBits g) (fun _ => g == 1))
  require (positive && canonical) .noncanonical
  let a ← liftD (ratOfInt n)
  let b ← liftD (ratOfNat d)
  liftD (MeteredDecodeInput.divide a b)

@[simp] theorem erase_rational (caps : Caps) (v : Value) :
    eraseD (rational caps v) = GlobalCheckerDecode.rational caps v := by
  simp [rational, GlobalCheckerDecode.rational]

def last {α : Type} [Inhabited α] (xs : List α) : Program α := do
  let n ← length xs
  primitive .structural n 0 (fun _ => xs.getLast?.getD default)

@[simp] theorem erase_last {α : Type} [Inhabited α] (xs : List α) :
    (last xs).erase = xs.getLast! := by simp [last]

def observeDegree (n : Nat) : Program Unit :=
  compose (ResourceModel.tick .degree 0 0 n) (fun _ => ())
    (ResourceModel.tick_safe _ _ _ _) (ResourceModel.tick_refines _ _ _ _)

@[simp] theorem erase_observeDegree (n : Nat) : (observeDegree n).erase = () := rfl

def polynomial (caps : Caps) : Value → Decode RootCertificate.Coefficients
  | .array vs => do
      let n ← liftD (length vs)
      require (n ≤ caps.degree + 1) (.resource .degree)
      let supplied ← get
      let next ← liftD (MeteredDecodeInput.natAdd supplied n)
      require (next ≤ caps.coefficients) (.resource .coefficients)
      set next
      let _ ← liftD (observeDegree (n - 1))
      let _ ← liftD (reserve .coefficients n)
      let cs ← mapD (rational caps) vs
      let c ← liftD (last cs)
      let zero ← liftD (MeteredIntervalReplay.eq c 0)
      require (cs.isEmpty || !zero) .noncanonical
      pure cs
  | _ => throw .shape

@[simp] theorem erase_polynomial (caps : Caps) (v : Value) :
    eraseD (polynomial caps v) = GlobalCheckerDecode.polynomial caps v := by
  cases v <;> simp [polynomial, GlobalCheckerDecode.polynomial, Bool.beq_eq_decide_eq, bne]

def bivariate (caps : Caps) : Value → Decode AlgebraicSpecialization.Bivariate
  | .array vs => do
      let n ← liftD (length vs)
      require (n ≤ caps.degree + 1) (.resource .degree)
      let _ ← liftD (observeDegree (n - 1))
      let cs ← mapD (polynomial caps) vs
      let c ← liftD (last cs)
      require (cs.isEmpty || !c.isEmpty) .noncanonical
      pure cs
  | _ => throw .shape

@[simp] theorem erase_bivariate (caps : Caps) (v : Value) :
    eraseD (bivariate caps v) = GlobalCheckerDecode.bivariate caps v := by
  cases v <;> simp [bivariate, GlobalCheckerDecode.bivariate]

def exponent (caps : Caps) (v : Value) : Decode Nat := do
  let n ← natural caps v
  require (← liftD (MeteredDecodeInput.natLE n caps.exponent)) (.resource .exponent)
  pure n

@[simp] theorem erase_exponent (caps : Caps) (v : Value) :
    eraseD (exponent caps v) = GlobalCheckerDecode.exponent caps v := by
  simp [exponent, GlobalCheckerDecode.exponent]

def sign (v : Value) : Decode SignType := fun supplied =>
  ExceptT.mk (primitive .integer 3
    (match v with | .number n => MeteredRationalReplay.intBits n | _ => 0)
    (fun _ => GlobalCheckerDecode.sign v supplied))

@[simp] theorem erase_sign (v : Value) : eraseD (sign v) = GlobalCheckerDecode.sign v := by
  funext supplied
  rfl

end ExactCIs.Unconditional.MeteredDecode
