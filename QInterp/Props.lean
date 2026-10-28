/-
Generators and properties. A property returns `none` when it holds and `some err` with the
measured error when it fails, so the sweep can record by how much.
-/
import Plausible
import QInterp.Model

namespace QInterp
open Plausible

/-- `old`: before godot PR 124915. `patch`: the PR as written. `fixed`: the PR with both fixes. -/
inductive Impl | old | patch | fixed
  deriving Repr, BEq, Inhabited

def Impl.name : Impl → String | .old => "old" | .patch => "patch" | .fixed => "fixed"
def Impl.all : List Impl := [.old, .patch, .fixed]

/-- One generated input: six keys, a weight, key times, a left factor, and the family that made it. -/
structure Case where
  family : String
  prePre : Q
  pre : Q
  a : Q
  b : Q
  post : Q
  postPost : Q
  w : Float
  tm : Times
  g : Q
  deriving Repr, Inhabited

instance : Shrinkable Case := ⟨fun _ => []⟩

def unif : Gen Float := do
  let n ← Gen.choose Nat 0 1000000000 (by omega)
  pure (n.val.toFloat / 1000000000.0)

def unifIn (lo hi : Float) : Gen Float := do pure (lo + (hi - lo) * (← unif))

def gauss : Gen Float := do
  let u1 ← unif
  let u2 ← unif
  let u1 := if u1 < 1e-12 then 1e-12 else u1
  pure ((-2 * Float.log u1).sqrt * Float.cos (TAU * u2))

def unitV3 : Gen V3 := do
  let v : V3 := ⟨← gauss, ← gauss, ← gauss⟩
  let v := if v.len < 1e-9 then ⟨0, 1, 0⟩ else v
  pure v.normalized

def unitQ : Gen Q := do
  let q : Q := ⟨← gauss, ← gauss, ← gauss, ← gauss⟩
  let q := if q.len < 1e-9 then Q.ident else q
  pure q.normalized

def expV (v : V3) : Q := Q.ofAxisAngle v.normalized v.len |>.normalized

/-- A key track k(i) = exp(i * omega + i^2 * alpha) * base, i = -2 .. 3 (from = 0, to = 1). -/
def track (base : Q) (omega alpha : V3) (i : Float) : Q :=
  let v := (omega.smul i).add (alpha.smul (i * i))
  (if v.len == 0 then Q.ident else expV v) * base

def randSign (q : Q) : Gen Q := do
  pure (if (← unif) < 0.5 then q.neg else q)

def genWeight : Gen Float := do
  let r ← unif
  if r < 0.1 then pure 0
  else if r < 0.2 then pure 1
  else if r < 0.25 then pure (← unifIn 0 1e-6)
  else if r < 0.3 then pure (1 - (← unifIn 0 1e-6))
  else unif

def genTimes : Gen Times := do
  let r ← unif
  if r < 0.5 then pure ⟨1, -1, 2, -2, 3⟩
  else
    let toT ← unifIn 0.05 2
    let preT := -(← unifIn 0.05 2)
    let postT := toT + (← unifIn 0.05 2)
    let prePreT := preT - (← unifIn 0.05 2)
    let postPostT := postT + (← unifIn 0.05 2)
    -- Coincident keys (zero gaps) are allowed by the makima code; sample them too.
    let c ← unif
    if c < 0.1 then pure ⟨toT, 0, postT, prePreT, postPostT⟩
    else if c < 0.2 then pure ⟨toT, preT, toT, prePreT, postPostT⟩
    else pure ⟨toT, preT, postT, prePreT, postPostT⟩

/-- Families, typical first: smooth tracks are what animations hold. -/
def genKeys : Gen (String × Array Q) := do
  let r ← unif
  if r < 0.40 then
    -- typical animation: per-key step up to ~70 degrees, mild acceleration
    let base ← unitQ
    let om := (← unitV3).smul (← unifIn 0 1.2)
    let al := (← unitV3).smul (← unifIn 0 0.2)
    pure ("track", #[-2, -1, 0, 1, 2, 3].map (track base om al))
  else if r < 0.50 then
    -- same track with random quaternion signs (q and -q are the same rotation)
    let base ← unitQ
    let om := (← unitV3).smul (← unifIn 0 1.2)
    let al := (← unitV3).smul (← unifIn 0 0.2)
    let ks ← (#[-2, -1, 0, 1, 2, 3].map (track base om al)).mapM randSign
    pure ("track-signs", ks)
  else if r < 0.60 then
    -- fast spin: steps from 90 to 200 degrees per key
    let base ← unitQ
    let om := (← unitV3).smul (← unifIn 1.6 3.5)
    let al := (← unitV3).smul (← unifIn 0 0.3)
    pure ("spin", #[-2, -1, 0, 1, 2, 3].map (track base om al))
  else if r < 0.70 then
    -- nearly equal keys: slerp's lerp branch and log's small-angle branch
    let base ← unitQ
    let om := (← unitV3).smul (← unifIn 0 0.01)
    let al := (← unitV3).smul (← unifIn 0 0.001)
    pure ("near", #[-2, -1, 0, 1, 2, 3].map (track base om al))
  else if r < 0.80 then
    -- 180-degree flips between keys
    let base ← unitQ
    let ax ← unitV3
    let eps ← unifIn 0 1e-3
    let om := ax.smul (PI - eps)
    pure ("half-turn", #[-2, -1, 0, 1, 2, 3].map (track base om ⟨0, 0, 0⟩))
  else
    let ks ← (List.range 6).toArray.mapM (fun _ => unitQ)
    pure ("random", ks)

instance : Arbitrary Case where
  arbitrary := do
    let (fam, ks) ← genKeys
    pure { family := fam, prePre := ks[0]!, pre := ks[1]!, a := ks[2]!, b := ks[3]!,
           post := ks[4]!, postPost := ks[5]!, w := ← genWeight, tm := ← genTimes, g := ← unitQ }

/-- Chordal distance between rotations: min(|a - b|, |a + b|) after normalizing. -/
def chord (a b : Q) : Float :=
  let a := a.normalized
  let b := b.normalized
  let d1 := (⟨a.x - b.x, a.y - b.y, a.z - b.z, a.w - b.w⟩ : Q).len
  let d2 := (⟨a.x + b.x, a.y + b.y, a.z + b.z, a.w + b.w⟩ : Q).len
  if d1 < d2 then d1 else d2

def TOL : Float := 1e-6

def check (err : Float) (tol : Float := TOL) : Option Float :=
  if err.isNaN || err > tol then some err else none

/-- The three interpolators, uniformly typed. -/
inductive Fn | sci | sciInTime | makima
  deriving Repr, BEq, Inhabited

def Fn.name : Fn → String
  | .sci => "spherical_cubic_interpolate"
  | .sciInTime => "spherical_cubic_interpolate_in_time"
  | .makima => "spherical_makima_interpolate_in_time"

def Fn.all : List Fn := [.sci, .sciInTime, .makima]

def run (i : Impl) (f : Fn) (prePre pre a b post postPost : Q) (w : Float) (tm : Times) : Q :=
  match i, f with
  | .old, .sci => Old.sci a b pre post w
  | .patch, .sci => New.sci a b pre post w
  | .fixed, .sci => New.sci a b pre post w
  | .old, .sciInTime => Old.sciInTime a b pre post w tm.toT tm.preT tm.postT
  | .patch, .sciInTime => New.sciInTime false a b pre post w tm.toT tm.preT tm.postT
  | .fixed, .sciInTime => New.sciInTime true a b pre post w tm.toT tm.preT tm.postT
  | .old, .makima => Old.makima a b pre post prePre postPost w tm
  | .patch, .makima => New.makima a b pre post prePre postPost w tm
  | .fixed, .makima => New.makima a b pre post prePre postPost w tm

def runC (i : Impl) (f : Fn) (c : Case) (w : Float := c.w) (tm : Times := c.tm) : Q :=
  run i f c.prePre c.pre c.a c.b c.post c.postPost w tm

def uniformTimes : Times := ⟨1, -1, 2, -2, 3⟩

/-- Mirror the key times about the segment for the reversal property. -/
def Times.mirror (t : Times) : Times :=
  ⟨t.toT, -(t.postT - t.toT), t.toT - t.preT, -(t.postPostT - t.toT), t.toT - t.prePreT⟩

/-- The properties. Each one is a statement that should hold for every input. -/
inductive Prop_
  | finite      -- output has no NaN or infinity
  | unit        -- output is a unit quaternion
  | endpoint0   -- weight 0 gives from
  | endpoint1   -- weight 1 gives to
  | constant    -- all keys equal gives that key
  | reversal    -- swapping the ends and mirroring the weight gives the same rotation
  | leftInv     -- interp(g * keys) = g * interp(keys)
  | geodesic    -- keys evenly spaced on one great circle give slerp(from, to, w)
  | continuity  -- a 1e-4 step in weight moves the output less than 1e-2 (no jumps)
  | timeUniform -- the in-time version with times 1, -1, 2 equals the plain one
  deriving Repr, BEq, Inhabited

def Prop_.name : Prop_ → String
  | .finite => "finite" | .unit => "unit" | .endpoint0 => "endpoint0" | .endpoint1 => "endpoint1"
  | .constant => "constant" | .reversal => "reversal" | .leftInv => "left_invariance"
  | .geodesic => "geodesic" | .continuity => "continuity" | .timeUniform => "time_uniform"

def Prop_.all : List Prop_ :=
  [.finite, .unit, .endpoint0, .endpoint1, .constant, .reversal, .leftInv, .geodesic, .continuity, .timeUniform]

def Prop_.appliesTo : Prop_ → Fn → Bool
  | .timeUniform, f => f == .sciInTime
  | _, _ => true

/-- Evaluate one property; `none` = holds, `some e` = fails with measured error `e`. -/
def eval (p : Prop_) (i : Impl) (f : Fn) (c : Case) : Option Float :=
  match p with
  | .finite => if (runC i f c).isFiniteQ then none else some (0.0/0.0)
  | .unit => check (Float.abs ((runC i f c).len - 1))
  | .endpoint0 => check (chord (runC i f c (w := 0)) c.a)
  | .endpoint1 => check (chord (runC i f c (w := 1)) c.b)
  | .constant => check (chord (run i f c.a c.a c.a c.a c.a c.a c.w c.tm) c.a)
  | .reversal =>
      let r1 := runC i f c
      let r2 := run i f c.postPost c.post c.b c.a c.pre c.prePre (1 - c.w) c.tm.mirror
      check (chord r1 r2)
  | .leftInv =>
      let g := c.g
      let r1 := run i f (g * c.prePre) (g * c.pre) (g * c.a) (g * c.b) (g * c.post) (g * c.postPost) c.w c.tm
      check (chord r1 (g * runC i f c))
  | .geodesic =>
      -- an even great circle through from and to: from * exp(k * v), v the step from -> to
      let v := (c.a.inverse * c.b).log.v
      if v.len > PI * 0.9 then none else
      let k (s : Float) := c.a * expV (v.smul s)
      let r := run i f (k (-2)) (k (-1)) c.a (k 1) (k 2) (k 3) c.w uniformTimes
      check (chord r (c.a.slerp (k 1) c.w))
  | .continuity =>
      let h := 1e-4
      let w := if c.w > 1 - h then 1 - h else c.w
      check (chord (runC i f c (w := w)) (runC i f c (w := w + h))) 1e-2
  | .timeUniform =>
      check (chord (run i .sciInTime c.prePre c.pre c.a c.b c.post c.postPost c.w uniformTimes)
                   (run i .sci c.prePre c.pre c.a c.b c.post c.postPost c.w uniformTimes))

def holds (p : Prop_) (i : Impl) (f : Fn) (c : Case) : Bool := (eval p i f c).isNone

/-! Quaternion::get_nearest_log has its own input: a quaternion and a log-space neighbor. -/

structure NLCase where
  q : Q
  neighbor : V3
  deriving Repr, Inhabited

instance : Shrinkable NLCase := ⟨fun _ => []⟩
instance : Arbitrary NLCase where
  arbitrary := do
    let r ← unif
    let q ← if r < 0.1 then pure (Q.neg Q.ident) else if r < 0.2 then pure Q.ident else unitQ
    let n := (← unitV3).smul (← unifIn 0 40)
    pure ⟨q, n⟩

/-- exp(get_nearest_log(q, n)) must be q itself (same sign, since the shift is 720 degrees). -/
def nlExpIsQ (c : NLCase) : Option Float :=
  let l := c.q.getNearestLog ⟨c.neighbor.x, c.neighbor.y, c.neighbor.z, 0⟩
  let e := Q.exp l
  check ((⟨e.x - c.q.x, e.y - c.q.y, e.z - c.q.z, e.w - c.q.w⟩ : Q).len) 1e-6

/-- No other 720-degree shift along the axis is closer to the neighbor. -/
def nlNearest (c : NLCase) : Option Float :=
  let l := (c.q.getNearestLog ⟨c.neighbor.x, c.neighbor.y, c.neighbor.z, 0⟩).v
  let ax := if l.len == 0 then V3.mk 0 0 0 else l.normalized
  let d0 := (l.sub c.neighbor).len
  let dp := ((l.add (ax.smul (2 * TAU))).sub c.neighbor).len
  let dm := ((l.sub (ax.smul (2 * TAU))).sub c.neighbor).len
  let best := if dp < dm then dp else dm
  if d0 <= best + 1e-9 then none else some (d0 - best)

end QInterp
