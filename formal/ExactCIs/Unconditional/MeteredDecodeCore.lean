/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerDecode
import ExactCIs.Unconditional.MeteredDecodeInput

/-! # Decoding effects and their exact erasure

The exception effect distinguishes frozen grammar refusals from the outer
resource refusal. The coefficient counter is local state; the resource vector
is the single outer `ResourceModel.M` state and is never reset by these effects.
Every primitive below is a named traversal, allocation, or integer operation.
`eraseP` and `eraseD` occur in specifications and proofs only.
-/
namespace ExactCIs.Unconditional.MeteredDecode

open BoundedJson MeteredProgram

abbrev Parser (α : Type) := ExceptT BoundedJson.Refusal Program α
abbrev Decode (α : Type) := StateT Nat Parser α

def eraseP {α : Type} (p : Parser α) : Except BoundedJson.Refusal α := p.run.erase
def eraseD {α : Type} (p : Decode α) : GlobalCheckerDecode.Decode α :=
  fun s => eraseP (p.run s)

@[simp] theorem eraseP_pure {α : Type} (a : α) :
    eraseP (pure a : Parser α) = pure a := rfl

@[simp] theorem eraseP_throw {α : Type} (e : BoundedJson.Refusal) :
    eraseP (throw e : Parser α) = throw e := rfl

@[simp] theorem eraseP_bind {α β : Type} (p : Parser α) (f : α → Parser β) :
    eraseP (p >>= f) = eraseP p >>= fun a => eraseP (f a) := by
  change (p.run >>= ExceptT.bindCont f).erase = _
  rw [erase_monadic_bind]
  cases h : p.run.erase <;> simp [eraseP, h, ExceptT.bindCont] <;> rfl

@[simp] theorem eraseP_map {α β : Type} (f : α → β) (p : Parser α) :
    eraseP (f <$> p) = f <$> eraseP p := by
  change (p.run >>= _).erase = _
  rw [erase_monadic_bind]
  cases h : p.run.erase <;> simp [eraseP, h]

def liftP {α : Type} (p : Program α) : Parser α :=
  ExceptT.mk (p >>= fun a => pure (.ok a))

@[simp] theorem eraseP_liftP {α : Type} (p : Program α) :
    eraseP (liftP p) = .ok p.erase := by
  simp [eraseP, liftP]

def liftD {α : Type} (p : Program α) : Decode α := fun s => do
  let a ← liftP p
  pure (a, s)

@[simp] theorem eraseD_pure {α : Type} (a : α) :
    eraseD (pure a : Decode α) = pure a := rfl

@[simp] theorem eraseD_throw {α : Type} (e : BoundedJson.Refusal) :
    eraseD (throw e : Decode α) = throw e := rfl

@[simp] theorem eraseD_bind {α β : Type} (p : Decode α) (f : α → Decode β) :
    eraseD (p >>= f) = eraseD p >>= fun a => eraseD (f a) := by
  funext s
  change eraseP ((p s) >>= fun (a, t) => f a t) = _
  rw [eraseP_bind]
  rfl

@[simp] theorem eraseD_map {α β : Type} (f : α → β) (p : Decode α) :
    eraseD (f <$> p) = f <$> eraseD p := by
  funext s
  change eraseP ((fun (a, t) => (f a, t)) <$> p s) = _
  rw [eraseP_map]
  rfl

@[simp] theorem eraseD_liftD {α : Type} (p : Program α) :
    eraseD (liftD p) = pure p.erase := by
  funext s
  change eraseP (liftP p >>= fun a => pure (a, s)) = _
  simp
  rfl

@[simp] theorem eraseD_get : eraseD (get : Decode Nat) = get := rfl
@[simp] theorem eraseD_set (n : Nat) : eraseD (set n : Decode Unit) = set n := rfl

@[simp] theorem eraseP_ite {α : Type} (c : Prop) [Decidable c] (p q : Parser α) :
    eraseP (if c then p else q) = if c then eraseP p else eraseP q := by split <;> rfl

@[simp] theorem eraseD_ite {α : Type} (c : Prop) [Decidable c] (p q : Decode α) :
    eraseD (if c then p else q) = if c then eraseD p else eraseD q := by split <;> rfl

@[simp] theorem erase_program_ite {α : Type} (c : Prop) [Decidable c] (p q : Program α) :
    (if c then p else q).erase = if c then p.erase else q.erase := by split <;> rfl

@[simp] theorem except_ok_bind {α β : Type} (a : α)
    (f : α → Except BoundedJson.Refusal β) : (Except.ok a >>= f) = f a := rfl

@[simp] theorem except_error_bind {α β : Type} (e : BoundedJson.Refusal)
    (f : α → Except BoundedJson.Refusal β) :
    (Except.error e >>= f) = Except.error e := rfl

@[simp] theorem except_throw_bind {α β : Type} (e : BoundedJson.Refusal)
    (f : α → Except BoundedJson.Refusal β) :
    ((throw e : Except BoundedJson.Refusal α) >>= f) = throw e := rfl

@[simp] theorem except_throw_map {α β : Type} (e : BoundedJson.Refusal) (f : α → β) :
    f <$> (throw e : Except BoundedJson.Refusal α) = throw e := rfl

@[simp] theorem if_false_and (c : Prop) [Decidable c] (b : Bool) :
    (if c then b else false) = (decide c && b) := by split <;> simp_all

@[simp] theorem if_true_or (c : Prop) [Decidable c] (b : Bool) :
    (if c then true else b) = (decide c || b) := by split <;> simp_all

/-- The concrete bodies at call sites are individually audited primitives. -/
def primitive {α : Type} (event : ResourceModel.Event) (amount bits : Nat)
    (body : Unit → α) : Program α :=
  compose (ResourceModel.perform event (ResourceModel.cost event amount bits) body)
    body (ResourceModel.perform_safe _ _ _) (ResourceModel.perform_refines _ _ _)

@[simp] theorem erase_primitive {α : Type} (e : ResourceModel.Event)
    (n b : Nat) (body : Unit → α) : (primitive e n b body).erase = body () := rfl

def reserve (event : ResourceModel.Event) (amount : Nat := 1) : Program Unit :=
  primitive event amount 0 (fun _ => ())

@[simp] theorem erase_reserve (e : ResourceModel.Event) (n : Nat) :
    (reserve e n).erase = () := rfl

def length {α : Type} (xs : List α) : Program Nat :=
  compose (MeteredRationalReplay.lengthM xs) (fun _ => xs.length)
    (MeteredRationalReplay.lengthM_safe _) (MeteredRationalReplay.lengthM_refines _)

@[simp] theorem erase_length {α : Type} (xs : List α) :
    (length xs).erase = xs.length := rfl

def chars (s : String) : Program (List Char) := do
  let _ ← reserve .structural s.utf8ByteSize
  primitive .decodeItem s.utf8ByteSize 0 (fun _ => s.toList)

@[simp] theorem erase_chars (s : String) : (chars s).erase = s.toList := by simp [chars]

def push (s : String) (c : Char) : Program String :=
  primitive .decodeItem 1 0 (fun _ => s.push c)

@[simp] theorem erase_push (s : String) (c : Char) : (push s c).erase = s.push c := rfl

def fromChars (cs : List Char) : Program String := do
  let n ← length cs
  let _ ← reserve .structural n
  primitive .decodeItem n 0 (fun _ => String.ofList cs)

@[simp] theorem erase_fromChars (cs : List Char) :
    (fromChars cs).erase = String.ofList cs := by simp [fromChars]

def reverse {α : Type} (xs : List α) : Program (List α) := do
  let n ← length xs
  let _ ← reserve .structural n
  primitive .decodeItem n 0 (fun _ => xs.reverse)

@[simp] theorem erase_reverse {α : Type} (xs : List α) :
    (reverse xs).erase = xs.reverse := by simp [reverse]

def natMul (a b : Nat) : Program Nat :=
  primitive .integer 1
    (MeteredRationalReplay.natBits a + MeteredRationalReplay.natBits b)
    (fun _ => a * b)

@[simp] theorem erase_natMul (a b : Nat) : (natMul a b).erase = a * b := rfl

def ofNat (n : Nat) : Program Int :=
  primitive .integer 1 (MeteredRationalReplay.natBits n) (fun _ => Int.ofNat n)

@[simp] theorem erase_ofNat (n : Nat) : (ofNat n).erase = Int.ofNat n := rfl

def negate (n : Int) : Program Int :=
  primitive .integer 1 (MeteredRationalReplay.intBits n) (fun _ => -n)

@[simp] theorem erase_negate (n : Int) : (negate n).erase = -n := rfl

def intSub (a b : Int) : Program Int :=
  primitive .integer 1
    (max (MeteredRationalReplay.intBits a) (MeteredRationalReplay.intBits b) + 1)
    (fun _ => a - b)

@[simp] theorem erase_intSub (a b : Int) : (intSub a b).erase = a - b := rfl

def digitFold : List Char → Nat → Program Nat
  | [], n => pure n
  | c :: cs, n => do
      let _ ← reserve .structural
      let m ← natMul 10 n
      let k ← primitive .integer 1 7 (fun _ => c.toNat - 48)
      let next ← MeteredDecodeInput.natAdd m k
      digitFold cs next

@[simp] theorem erase_digitFold (cs : List Char) (n : Nat) :
    (digitFold cs n).erase = cs.foldl (fun n c => 10 * n + (c.toNat - 48)) n := by
  induction cs generalizing n with
  | nil => rfl
  | cons c cs ih => simp [digitFold, List.foldl_cons, ih]

/-- Native work counters must fit the frozen signed-63-bit envelope. This guard
    has no erased semantic effect; refusal retains the already spent vector. -/
def admitWord (n : Nat) : Program Unit := do
  let admitted ← MeteredDecodeInput.natLE n ResourceModel.maxCounter
  if admitted then pure () else
    compose (fun _ used => .error (.context "wire_limits"
      (.resource ⟨.integer, used, ResourceModel.cost .integer (ResourceModel.maxCounter + 1)⟩)))
      (fun _ => ())
      (by intro _ _ _ _ _ h; contradiction)
      (by intro _ _ _ _ h; contradiction)

@[simp] theorem erase_admitWord (n : Nat) : (admitWord n).erase = () := by
  simp [admitWord]

end ExactCIs.Unconditional.MeteredDecode
