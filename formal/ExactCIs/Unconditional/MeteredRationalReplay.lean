/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredRationalKernel
import ExactCIs.Unconditional.RootSignCertificate

/-! # Vector-metered rational identity, PRS and root replay

The executable definitions below call concrete metered primitives. The pure
checker occurs in refinement statements/proofs, never as a successful runtime
fallback. A single vector is threaded through every nested replay operation.
-/
namespace ExactCIs.Unconditional.MeteredRationalReplay

open ResourceModel RootCertificate

theorem plain_add_eq (as bs : P) : Plain.add as bs = RootCertificate.add as bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => cases bs <;> simp [Plain.add, RootCertificate.add, ih]

theorem plain_scale_eq (a : Rat) (bs : P) : Plain.scale a bs = RootCertificate.scale a bs := by
  induction bs <;> simp_all [Plain.scale, RootCertificate.scale]

theorem plain_mul_eq (as bs : P) : Plain.mul as bs = RootCertificate.mul as bs := by
  induction as <;> simp_all [Plain.mul, RootCertificate.mul, plain_add_eq, plain_scale_eq]

theorem plain_value_eq (cs : P) (x : Rat) : Plain.value cs x = RootCertificate.value cs x := by
  induction cs <;> simp_all [Plain.value, RootCertificate.value]

theorem plain_power_eq (cs : P) (n : Nat) : Plain.power cs n = RootCertificate.power cs n := by
  induction n <;> simp_all [Plain.power, RootCertificate.power, plain_mul_eq]

theorem plain_derivative_eq (cs : P) : Plain.derivative cs = RootCertificate.derivative cs := by
  induction cs <;> simp_all [Plain.derivative, RootCertificate.derivative, plain_add_eq]

theorem plain_bounds_eq (cs : P) (l u : Rat) : Plain.bounds cs l u = RootCertificate.bounds cs l u := by
  induction cs <;> simp_all [Plain.bounds, RootCertificate.bounds, Plain.chooseMin,
    Plain.chooseMax, min_def, max_def]

theorem plain_identity_eq (as bs : P) : Plain.identity as bs = RootCertificate.identityCheck as bs := by
  simp only [Plain.identity, plain_add_eq, plain_scale_eq, RootCertificate.identityCheck]
  have same (x : Rat) : decide (x = 0) = (x == 0) := by
    by_cases h : x = 0 <;> simp [h]
  simp only [same]

theorem polyAdd_correct (as bs : P) : Refines (polyAdd as bs) (RootCertificate.add as bs) := by
  simpa only [plain_add_eq] using polyAdd_refines as bs
theorem polyScale_correct (a : Rat) (bs : P) : Refines (polyScale a bs) (RootCertificate.scale a bs) := by
  simpa only [plain_scale_eq] using polyScale_refines a bs
theorem polyMul_correct (as bs : P) : Refines (polyMul as bs) (RootCertificate.mul as bs) := by
  simpa only [plain_mul_eq] using polyMul_refines as bs
theorem polyValue_correct (cs : P) (x : Rat) : Refines (polyValue cs x) (RootCertificate.value cs x) := by
  simpa only [plain_value_eq] using polyValue_refines cs x
theorem polyPower_correct (cs : P) (n : Nat) : Refines (polyPower cs n) (RootCertificate.power cs n) := by
  simpa only [plain_power_eq] using polyPower_refines cs n
theorem polyDerivative_correct (cs : P) : Refines (polyDerivative cs) (RootCertificate.derivative cs) := by
  simpa only [plain_derivative_eq] using polyDerivative_refines cs
theorem polyBounds_correct (cs : P) (l u : Rat) : Refines (polyBounds cs l u) (RootCertificate.bounds cs l u) := by
  simpa only [plain_bounds_eq] using polyBounds_refines cs l u
theorem polyIdentity_correct (as bs : P) : Refines (polyIdentity as bs) (RootCertificate.identityCheck as bs) := by
  simpa only [plain_identity_eq] using polyIdentity_refines as bs

/-- Fixed-size dispatch and already-admitted index/counter metadata only.
Rational, polynomial and unbounded numeral computations use their named primitives. -/
def metadata {α : Type} (body : Unit → α) : M α := perform .structural (cost .structural 1) body
theorem metadata_safe {α : Type} (body : Unit → α) : Safe (metadata body) := perform_safe _ _ _
theorem metadata_refines {α : Type} (body : Unit → α) : Refines (metadata body) (body ()) := perform_refines _ _ _

def rootSetCheck (h s quotient powerQuotient : P) (exponent : Nat) : M Bool :=
  andThen (metadata fun _ => decide (0 < exponent)) fun _ =>
    andThen (do let product ← polyMul s quotient; polyIdentity h product) fun _ => do
      let power ← polyPower s exponent
      let product ← polyMul h powerQuotient
      polyIdentity power product

theorem rootSetCheck_safe (h s q t : P) (n : Nat) : Safe (rootSetCheck h s q t n) := by
  apply andThen_safe (metadata_safe _)
  apply andThen_safe
  · apply bind_safe (polyMul_safe _ _); intro product; exact polyIdentity_safe _ _
  · apply bind_safe (polyPower_safe _ _); intro power
    apply bind_safe (polyMul_safe _ _); intro product; exact polyIdentity_safe _ _

theorem rootSetCheck_refines (h s q t : P) (n : Nat) :
    Refines (rootSetCheck h s q t n) (AlgebraicCertificate.rootSetCheck h s q t n) := by
  unfold AlgebraicCertificate.rootSetCheck
  rw [Bool.and_assoc]
  exact andThen_refines (metadata_refines (fun _ => decide (0 < n)))
    (andThen_refines
      (bind_refines (polyMul_correct s q) (polyIdentity_correct h _))
      (bind_refines (polyPower_correct s n)
        (bind_refines (polyMul_correct h t) (polyIdentity_correct _ _))))

def bezoutCheck (s a b : P) : M Bool := do
  let derivative ← polyDerivative s
  let left ← polyMul a s
  let right ← polyMul b derivative
  let sum ← polyAdd left right
  polyIdentity sum [1]

theorem bezoutCheck_safe (s a b : P) : Safe (bezoutCheck s a b) := by
  apply bind_safe (polyDerivative_safe _); intro derivative
  apply bind_safe (polyMul_safe _ _); intro left
  apply bind_safe (polyMul_safe _ _); intro right
  apply bind_safe (polyAdd_safe _ _); intro sum
  exact polyIdentity_safe _ _

theorem bezoutCheck_refines (s a b : P) :
    Refines (bezoutCheck s a b) (RootCountCertificate.bezoutCheck s a b) :=
  bind_refines (polyDerivative_correct _) (bind_refines (polyMul_correct _ _)
    (bind_refines (polyMul_correct _ _) (bind_refines (polyAdd_correct _ _)
      (polyIdentity_correct _ _))))

def terminalChain (p : P) (qs : List P) (last : Rat) : M Bool :=
  match qs with
  | [] => andThen (polyIdentity p [last]) fun _ => do
      let zero ← ratEQ last 0
      ret (!zero)
  | _ :: _ => ret false

def chainTail (previous : P) (tail : List P) (qs : List P) (last : Rat) : M Bool :=
  scan fun _ => do
    tick .rootStep
    match tail with
    | [] => terminalChain previous qs last
    | q :: rest =>
      match rest with
      | [] => terminalChain q qs last
      | r :: _ =>
        match qs with
        | [] => ret false
        | quotient :: quotients =>
          andThen (do
            let product ← polyMul q quotient
            let negative ← polyScale (-1) r
            let sum ← polyAdd product negative
            polyIdentity previous sum) fun _ => chainTail q rest quotients last

def chainCheck (ps qs : List P) (last : Rat) : M Bool := scan fun _ =>
  match ps with
  | [] => ret false
  | p :: tail => chainTail p tail qs last

theorem terminalChain_safe (p : P) (qs : List P) (last : Rat) :
    Safe (terminalChain p qs last) := by
  cases qs with
  | nil =>
    unfold terminalChain
    apply andThen_safe (polyIdentity_safe _ _)
    exact bind_safe (ratEQ_safe _ _) (fun _ => ret_safe _)
  | cons _ _ => exact ret_safe _

theorem terminalChain_refines (p : P) (qs : List P) (last : Rat) :
    Refines (terminalChain p qs last)
      (match qs with | [] => RootCertificate.identityCheck p [last] && decide (last ≠ 0)
                     | _ :: _ => false) := by
  cases qs with
  | nil =>
    unfold terminalChain
    simp only [decide_not]
    apply andThen_refines (polyIdentity_correct p [last])
    exact bind_refines (ratEQ_refines last 0) (ret_refines _)
  | cons _ _ => exact ret_refines _

theorem chainTail_safe (previous : P) (tail qs : List P) (last : Rat) :
    Safe (chainTail previous tail qs last) := by
  induction tail generalizing previous qs with
  | nil =>
    exact scan_safe (bind_safe (tick_safe _ _ _ _) (fun _ => terminalChain_safe _ _ _))
  | cons q rest ih =>
    apply scan_safe
    apply bind_safe (tick_safe _ _ _ _)
    intro _
    cases rest with
    | nil => exact terminalChain_safe _ _ _
    | cons r rs =>
      cases qs with
      | nil => exact ret_safe _
      | cons quotient quotients =>
        apply andThen_safe
        · apply bind_safe (polyMul_safe _ _); intro product
          apply bind_safe (polyScale_safe _ _); intro negative
          apply bind_safe (polyAdd_safe _ _); intro sum
          exact polyIdentity_safe _ _
        · exact ih q quotients

theorem chainTail_refines (previous : P) (tail qs : List P) (last : Rat) :
    Refines (chainTail previous tail qs last)
      (SturmChainCertificate.chainCheck (previous :: tail) qs last) := by
  induction tail generalizing previous qs with
  | nil =>
    apply scan_refines
    apply bind_refines (tick_refines _ _ _ _)
    cases qs <;> exact terminalChain_refines _ _ _
  | cons q rest ih =>
    apply scan_refines
    apply bind_refines (tick_refines _ _ _ _)
    cases rest with
    | nil => cases qs <;> exact terminalChain_refines _ _ _
    | cons r rs =>
      cases qs with
      | nil => exact ret_refines _
      | cons quotient quotients =>
        exact andThen_refines
          (bind_refines (polyMul_correct q quotient)
            (bind_refines (polyScale_correct (-1) r)
              (bind_refines (polyAdd_correct _ _) (polyIdentity_correct previous _))))
          (ih q quotients)

theorem chainCheck_safe (ps qs : List P) (last : Rat) : Safe (chainCheck ps qs last) := by
  cases ps with
  | nil => exact scan_safe (ret_safe _)
  | cons p tail => exact scan_safe (chainTail_safe _ _ _ _)

theorem chainCheck_refines (ps qs : List P) (last : Rat) :
    Refines (chainCheck ps qs last) (SturmChainCertificate.chainCheck ps qs last) := by
  cases ps with
  | nil => exact scan_refines (ret_refines _)
  | cons p tail => exact scan_refines (chainTail_refines _ _ _ _)

def firstCheck (s : P) (tail : List P) : M Bool := scan fun _ =>
  match tail with
  | [] => ret true
  | d :: _ => do
    let derivative ← polyDerivative s
    polyIdentity d derivative

theorem firstCheck_safe (s : P) (tail : List P) : Safe (firstCheck s tail) := by
  cases tail with
  | nil => exact scan_safe (ret_safe _)
  | cons d ds => exact scan_safe (bind_safe (polyDerivative_safe _) (fun _ => polyIdentity_safe _ _))

theorem firstCheck_refines (s : P) (tail : List P) :
    Refines (firstCheck s tail) (RootCountCertificate.firstCheck s tail) := by
  cases tail with
  | nil => exact scan_refines (ret_refines _)
  | cons d ds =>
    exact scan_refines
      (bind_refines (polyDerivative_correct _) (polyIdentity_correct _ _))

def rootCheck (h : P) (c : RootCountCertificate.Certificate) : M Bool := do
  tick .rootStep
  andThen (rootSetCheck h c.representative c.quotient c.powerQuotient c.exponent) fun _ =>
    andThen (bezoutCheck c.representative c.bezoutLeft c.bezoutRight) fun _ =>
      andThen (chainCheck (c.representative :: c.tail) c.quotients c.last) fun _ =>
        firstCheck c.representative c.tail

theorem rootCheck_safe (h : P) (c : RootCountCertificate.Certificate) : Safe (rootCheck h c) :=
  bind_safe (tick_safe _ _ _ _) (fun _ => andThen_safe (rootSetCheck_safe _ _ _ _ _)
    (andThen_safe (bezoutCheck_safe _ _ _) (andThen_safe (chainCheck_safe _ _ _)
      (firstCheck_safe _ _))))

theorem rootCheck_refines (h : P) (c : RootCountCertificate.Certificate) :
    Refines (rootCheck h c) (RootCountCertificate.check h c) := by
  unfold RootCountCertificate.check
  simp only [Bool.and_assoc]
  exact bind_refines (tick_refines _ _ _ _)
    (andThen_refines (rootSetCheck_refines _ _ _ _ _)
      (andThen_refines (bezoutCheck_refines _ _ _) (andThen_refines
        (chainCheck_refines _ _ _) (firstCheck_refines _ _))))

def ratSign (a : Rat) : M SignType := do
  let positive ← ratLT 0 a
  if positive then ret 1 else do
    let negative ← ratLT a 0
    ret (if negative then -1 else 0)

theorem ratSign_safe (a : Rat) : Safe (ratSign a) := by
  unfold ratSign
  apply bind_safe (m := ratLT 0 a) (ratLT_safe 0 a)
  intro positive
  cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact bind_safe (m := ratLT a 0)
      (k := fun negative => ret (if negative then (-1 : SignType) else 0))
      (ratLT_safe a 0) (fun _ => ret_safe _)
  · exact ret_safe _

theorem ratSign_refines (a : Rat) : Refines (ratSign a) (SignType.sign a) := by
  rw [sign_apply]
  unfold ratSign
  apply bind_refines (m := ratLT 0 a) (ratLT_refines 0 a)
  by_cases positive : 0 < a
  · simp only [positive, decide_true, ↓reduceIte]; exact ret_refines _
  · simp only [positive, decide_false, ↓reduceIte]
    apply bind_refines (m := ratLT a 0)
      (k := fun negative => ret (if negative then (-1 : SignType) else 0))
      (ratLT_refines a 0)
    by_cases negative : a < 0 <;> simp only [negative, decide_true, decide_false, ↓reduceIte]
    · exact ret_refines _
    · exact ret_refines _

def changes (previous : SignType) (ss : List SignType) : M Nat := scan fun _ =>
  match ss with
  | [] => ret 0
  | s :: ss =>
    if s = 0 then changes previous ss else do
      let tail ← changes s ss
      ret ((if previous = 0 ∨ previous = s then 0 else 1) + tail)

theorem changes_safe (previous : SignType) (ss : List SignType) : Safe (changes previous ss) := by
  induction ss generalizing previous with
  | nil => exact scan_safe (ret_safe _)
  | cons s ss ih =>
    apply scan_safe
    by_cases h : s = 0
    · simpa only [h, ↓reduceIte] using ih previous
    · simp only [h, ↓reduceIte]
      exact bind_safe (ih s) (fun _ => ret_safe _)

theorem changes_refines (previous : SignType) (ss : List SignType) :
    Refines (changes previous ss) (SturmVariation.changesFrom previous ss) := by
  induction ss generalizing previous with
  | nil => exact scan_refines (ret_refines _)
  | cons s ss ih =>
    apply scan_refines
    by_cases h : s = 0
    · simpa only [h, ↓reduceIte, SturmVariation.changesFrom] using ih previous
    · simp only [h, ↓reduceIte, SturmVariation.changesFrom]
      exact bind_refines (ih s) (ret_refines _)

def rationalVariation (ps : List P) (x : Rat) : M Nat := do
  tick .rootStep
  let signs ← mapM .structural (fun p => do let y ← polyValue p x; ratSign y) ps
  changes 0 signs

theorem rationalVariation_safe (ps : List P) (x : Rat) : Safe (rationalVariation ps x) := by
  unfold rationalVariation
  apply bind_safe (m := tick .rootStep) (tick_safe .rootStep 1 0 0); intro _
  apply bind_safe
    (m := mapM .structural (fun p => do let y ← polyValue p x; ratSign y) ps)
    (mapM_safe .structural _ ps (fun p => bind_safe (polyValue_safe p x) ratSign_safe))
  intro signs; exact changes_safe 0 signs

theorem rationalVariation_refines (ps : List P) (x : Rat) :
    Refines (rationalVariation ps x) (RootCountCertificate.rationalVariation ps x) :=
  bind_refines (tick_refines _ _ _ _)
    (bind_refines (mapM_refines _ _ _ _ (fun p =>
      bind_refines (polyValue_correct p x) (ratSign_refines _))) (changes_refines _ _))

def rootCount (c : RootCountCertificate.Certificate) (a b : Rat) : M Nat := do
  let left ← rationalVariation (c.representative :: c.tail) a
  let right ← rationalVariation (c.representative :: c.tail) b
  metadata fun _ => left - right

theorem rootCount_safe (c : RootCountCertificate.Certificate) (a b : Rat) :
    Safe (rootCount c a b) :=
  bind_safe (rationalVariation_safe _ _) (fun _ => bind_safe (rationalVariation_safe _ _)
    (fun _ => metadata_safe _))

theorem rootCount_refines (c : RootCountCertificate.Certificate) (a b : Rat) :
    Refines (rootCount c a b) (RootCountCertificate.count c a b) :=
  bind_refines (rationalVariation_refines _ _) (bind_refines (rationalVariation_refines _ _)
    (metadata_refines _))

def signCheck (h : P) (a b : Rat) (c : RootCountCertificate.Certificate) : M (Option Bool) := do
  let order ← ratLE a b
  if !order then ret none else do
    let left ← polyValue h a
    let nonnegative ← ratLE 0 left
    if nonnegative then ret (some true) else do
      let valid ← rootCheck h c
      if !valid then ret none else do
        let count ← rootCount c a b
        metadata fun _ => some (decide (0 < count))

theorem signCheck_safe (h : P) (a b : Rat) (c : RootCountCertificate.Certificate) :
    Safe (signCheck h a b c) := by
  unfold signCheck
  apply bind_safe (m := ratLE a b) (ratLE_safe a b); intro order
  cases order
  · exact ret_safe _
  · apply bind_safe (m := polyValue h a) (polyValue_safe h a); intro left
    apply bind_safe (m := ratLE 0 left) (ratLE_safe 0 left); intro nonnegative
    cases nonnegative
    · apply bind_safe (m := rootCheck h c) (rootCheck_safe h c); intro valid
      cases valid
      · exact ret_safe _
      · exact bind_safe (m := rootCount c a b) (rootCount_safe c a b) (fun _ => metadata_safe _)
    · exact ret_safe _

theorem signCheck_refines (h : P) (a b : Rat) (c : RootCountCertificate.Certificate) :
    Refines (signCheck h a b c) (RootSignCertificate.check h a b c) := by
  unfold signCheck
  apply bind_refines (m := ratLE a b) (ratLE_refines a b)
  by_cases order : a ≤ b
  · simp only [order, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      RootSignCertificate.check]
    apply bind_refines (m := polyValue h a) (polyValue_correct h a)
    apply bind_refines (m := ratLE 0 (RootCertificate.value h a))
      (ratLE_refines 0 (RootCertificate.value h a))
    by_cases nonnegative : 0 ≤ RootCertificate.value h a
    · simp only [nonnegative, decide_true, ↓reduceIte]; exact ret_refines _
    · simp only [nonnegative, decide_false, ↓reduceIte]
      apply bind_refines (m := rootCheck h c) (rootCheck_refines h c)
      cases valid : RootCountCertificate.check h c
      · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]; exact ret_refines _
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact bind_refines (m := rootCount c a b) (rootCount_refines c a b) (metadata_refines _)
  · simp only [order, decide_false, Bool.not_false, ↓reduceIte, RootSignCertificate.check]
    exact ret_refines _

/-- Native replay success has the existing inclusive, closed-interval semantics. -/
theorem signCheck_sound {h : P} {a b : Rat} {c : RootCountCertificate.Certificate}
    {p : Profile} {used next : Vector} {answer : Bool}
    (checked : signCheck h a b c p used = .ok (some answer, next)) :
    a ≤ b ∧ (answer = true ↔ RootSignCertificate.Accepted h a b) := by
  have same := signCheck_refines h a b c p used (some answer) next checked
  exact RootSignCertificate.checkerSound same.symm

/-- Numeric and structural caps hold for every successful rational sign replay. -/
theorem signCheck_bounded {h : P} {a b : Rat} {c : RootCountCertificate.Certificate}
    {p : Profile} {used next : Vector} {answer : Option Bool}
    (fits : Fits p used) (checked : signCheck h a b c p used = .ok (answer, next)) :
    Fits p next := signCheck_safe h a b c p used fits answer next checked


end ExactCIs.Unconditional.MeteredRationalReplay
