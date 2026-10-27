/-
A Float port of the Godot code under test. Each definition names the C++ function it follows.
`Old` is the tree before "Make Quaternion cubic/makima interpolation more stable" (godot PR 124915).
`New` is the tree after it. `New` with `fix := true` also normalizes the pre-blend quaternion and
uses `cubicInTimeFixed`, the two changes the properties in QInterp/Props.lean require.
-/
namespace QInterp

def CMP_EPSILON : Float := 0.00001
def UNIT_EPSILON : Float := 0.001
def PI : Float := 3.14159265358979323846
def TAU : Float := 6.28318530717958647692

def signbit (x : Float) : Bool := (x.toBits >>> 63) == 1
def isFinite (x : Float) : Bool := !(x.isNaN || x.isInf)

-- Math::is_equal_approx(a, b, tol)
def eqTol (a b tol : Float) : Bool := a == b || Float.abs (a - b) < tol
-- Math::is_equal_approx(a, b)
def eqApprox (a b : Float) : Bool :=
  if a == b then true else
  let t := CMP_EPSILON * Float.abs a
  let t := if t < CMP_EPSILON then CMP_EPSILON else t
  Float.abs (a - b) < t
def isZeroApprox (a : Float) : Bool := Float.abs a < CMP_EPSILON

def lerp (a b w : Float) : Float := a + (b - a) * w

structure V3 where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

namespace V3
def add (a b : V3) : V3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def sub (a b : V3) : V3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
def smul (a : V3) (s : Float) : V3 := ⟨a.x * s, a.y * s, a.z * s⟩
def dot (a b : V3) : Float := a.x * b.x + a.y * b.y + a.z * b.z
def cross (a b : V3) : V3 := ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩
def lenSq (a : V3) : Float := a.dot a
def len (a : V3) : Float := a.lenSq.sqrt
-- Vector3::normalized
def normalized (a : V3) : V3 :=
  if !(isFinite a.x && isFinite a.y && isFinite a.z) then ⟨0, 0, 0⟩ else
  let l := a.lenSq
  if l == 0 then ⟨0, 0, 0⟩ else let l := l.sqrt; ⟨a.x / l, a.y / l, a.z / l⟩
def isNormalized (a : V3) : Bool := eqTol a.lenSq 1 UNIT_EPSILON
def isZeroApprox (a : V3) : Bool := QInterp.isZeroApprox a.x && QInterp.isZeroApprox a.y && QInterp.isZeroApprox a.z
def lerp (a b : V3) (w : Float) : V3 := ⟨QInterp.lerp a.x b.x w, QInterp.lerp a.y b.y w, QInterp.lerp a.z b.z w⟩
end V3

structure Q where
  x : Float
  y : Float
  z : Float
  w : Float
  deriving Repr, Inhabited

namespace Q
def ident : Q := ⟨0, 0, 0, 1⟩
def zero : Q := ⟨0, 0, 0, 0⟩
def v (q : Q) : V3 := ⟨q.x, q.y, q.z⟩
def neg (q : Q) : Q := ⟨-q.x, -q.y, -q.z, -q.w⟩
def dot (a b : Q) : Float := a.x * b.x + a.y * b.y + a.z * b.z + a.w * b.w
def lenSq (q : Q) : Float := q.dot q
def len (q : Q) : Float := q.lenSq.sqrt
def smul (q : Q) (s : Float) : Q := ⟨q.x * s, q.y * s, q.z * s, q.w * s⟩
def normalized (q : Q) : Q := q.smul (1 / q.len)
def isFiniteQ (q : Q) : Bool := isFinite q.x && isFinite q.y && isFinite q.z && isFinite q.w
-- Quaternion::operator*=
def mul (a p : Q) : Q :=
  ⟨a.w * p.x + a.x * p.w + a.y * p.z - a.z * p.y,
   a.w * p.y + a.y * p.w + a.z * p.x - a.x * p.z,
   a.w * p.z + a.z * p.w + a.x * p.y - a.y * p.x,
   a.w * p.w - a.x * p.x - a.y * p.y - a.z * p.z⟩
instance : Mul Q := ⟨mul⟩
instance : Neg Q := ⟨neg⟩
-- Quaternion::inverse (the conjugate; MATH_CHECKS demands a unit input)
def inverse (q : Q) : Q := ⟨-q.x, -q.y, -q.z, q.w⟩
-- Quaternion(const Vector3 &axis, real_t angle)
def ofAxisAngle (axis : V3) (angle : Float) : Q :=
  let d := axis.len
  if d == 0 then zero else
  let s := Float.sin (angle * 0.5) / d
  ⟨axis.x * s, axis.y * s, axis.z * s, Float.cos (angle * 0.5)⟩
-- Quaternion::log (get_axis * get_angle)
def log (q : Q) : Q :=
  if Float.abs q.w > 1 - CMP_EPSILON then ⟨q.x * 2, q.y * 2, q.z * 2, 0⟩ else
  let r := 1 / (1 - q.w * q.w).sqrt
  let a := 2 * Float.acos q.w
  ⟨q.x * r * a, q.y * r * a, q.z * r * a, 0⟩
-- Quaternion::exp
def exp (q : Q) : Q :=
  let v := q.v
  let theta := v.len
  let n := v.normalized
  if theta < CMP_EPSILON || !n.isNormalized then ident else ofAxisAngle n theta
-- Quaternion::slerp
def slerp (a b : Q) (wt : Float) : Q :=
  let cosom := a.dot b
  let (cosom, to1) := if cosom < 0 then (-cosom, b.neg) else (cosom, b)
  let (s0, s1) :=
    if (1 - cosom) > CMP_EPSILON then
      let omega := Float.acos cosom
      let sinom := Float.sin omega
      (Float.sin ((1 - wt) * omega) / sinom, Float.sin (wt * omega) / sinom)
    else (1 - wt, wt)
  ⟨s0 * a.x + s1 * to1.x, s0 * a.y + s1 * to1.y, s0 * a.z + s1 * to1.z, s0 * a.w + s1 * to1.w⟩
-- New in the patch: Quaternion::get_nearest_log
def getNearestLog (q lnNeighbor : Q) : Q :=
  let PHASE := 2 * TAU
  let INV_PHASE := 1 / PHASE
  let neighbor := lnNeighbor.v
  let axis := q.v
  let angle := 2 * Float.atan2 axis.len q.w
  let axis := if axis.isZeroApprox then neighbor.normalized else axis.normalized
  let phases := Float.round ((neighbor.dot axis - angle) * INV_PHASE)
  let nearest := axis.smul (angle + phases * PHASE)
  ⟨nearest.x, nearest.y, nearest.z, 0⟩
end Q

/-- Basis(q).get_rotation_quaternion(): set_quaternion, orthonormalized, det sign, get_quaternion. -/
def rotationQuaternion (q : Q) : Q := Id.run do
  let d := q.lenSq
  let s := 2 / d
  let xs := q.x * s; let ys := q.y * s; let zs := q.z * s
  let wx := q.w * xs; let wy := q.w * ys; let wz := q.w * zs
  let xx := q.x * xs; let xy := q.x * ys; let xz := q.x * zs
  let yy := q.y * ys; let yz := q.y * zs; let zz := q.z * zs
  -- rows
  let r : Array Float := #[1 - (yy + zz), xy - wz, xz + wy,
                           xy + wz, 1 - (xx + zz), yz - wx,
                           xz - wy, yz + wx, 1 - (xx + yy)]
  let col (m : Array Float) (j : Nat) : V3 := ⟨m[j]!, m[3 + j]!, m[6 + j]!⟩
  -- Basis::orthonormalize (Gram-Schmidt on columns)
  let cx := (col r 0).normalized
  let cy := ((col r 1).sub (cx.smul (cx.dot (col r 1)))).normalized
  let cz := (((col r 2).sub (cx.smul (cx.dot (col r 2)))).sub (cy.smul (cy.dot (col r 2)))).normalized
  let mut m : Array Float := #[cx.x, cy.x, cz.x, cx.y, cy.y, cz.y, cx.z, cy.z, cz.z]
  let det := m[0]! * (m[4]! * m[8]! - m[5]! * m[7]!) - m[1]! * (m[3]! * m[8]! - m[5]! * m[6]!) + m[2]! * (m[3]! * m[7]! - m[4]! * m[6]!)
  if det < 0 then m := m.map (· * -1)
  let at_ (i j : Nat) : Float := m[3 * i + j]!
  let trace := at_ 0 0 + at_ 1 1 + at_ 2 2
  if trace > 0 then
    let s := (trace + 1).sqrt
    let w := s * 0.5
    let s := 0.5 / s
    return ⟨(at_ 2 1 - at_ 1 2) * s, (at_ 0 2 - at_ 2 0) * s, (at_ 1 0 - at_ 0 1) * s, w⟩
  else
    let i := if at_ 0 0 < at_ 1 1 then (if at_ 1 1 < at_ 2 2 then 2 else 1) else (if at_ 0 0 < at_ 2 2 then 2 else 0)
    let j := (i + 1) % 3
    let k := (i + 2) % 3
    let s := (at_ i i - at_ j j - at_ k k + 1).sqrt
    let mut t : Array Float := #[0, 0, 0, 0]
    t := t.set! i (s * 0.5)
    let s := 0.5 / s
    t := t.set! 3 ((at_ k j - at_ j k) * s)
    t := t.set! j ((at_ j i + at_ i j) * s)
    t := t.set! k ((at_ k i + at_ i k) * s)
    return ⟨t[0]!, t[1]!, t[2]!, t[3]!⟩

-- Math::cubic_interpolate
def cubic (f t p q w : Float) : Float :=
  0.5 * ((f * 2) + (-p + t) * w + (2 * p - 5 * f + 4 * t - q) * (w * w) + (-p + 3 * f - 3 * t + q) * (w * w * w))

-- Math::cubic_interpolate_in_time (Barry-Goldman)
def cubicInTime (f to pre post w toT preT postT : Float) : Float :=
  let t := lerp 0 toT w
  let a1 := lerp pre f (if preT == 0 then 0 else (t - preT) / -preT)
  let a2 := lerp f to (if toT == 0 then 0.5 else t / toT)
  let a3 := lerp to post (if postT - toT == 0 then 1 else (t - toT) / (postT - toT))
  let b1 := lerp a1 a2 (if toT - preT == 0 then 0 else (t - preT) / (toT - preT))
  let b2 := lerp a2 a3 (if postT == 0 then 1 else t / postT)
  lerp b1 b2 (if toT == 0 then 0.5 else t / toT)

/-- Fix: a coincident pre key (pre_t == 0) must leave `from` at t = 0, and a coincident post key
(post_t == to_t) must leave `to` at t = to_t. Upstream uses 0 and 1 there, which return pre and post. -/
def cubicInTimeFixed (f to pre post w toT preT postT : Float) : Float :=
  let t := lerp 0 toT w
  let a1 := lerp pre f (if preT == 0 then 1 else (t - preT) / -preT)
  let a2 := lerp f to (if toT == 0 then 0.5 else t / toT)
  let a3 := lerp to post (if postT - toT == 0 then 0 else (t - toT) / (postT - toT))
  let b1 := lerp a1 a2 (if toT - preT == 0 then 0 else (t - preT) / (toT - preT))
  let b2 := lerp a2 a3 (if postT == 0 then 1 else t / postT)
  lerp b1 b2 (if toT == 0 then 0.5 else t / toT)

def akimaExtrapolate (e en : Float) : Float := 2 * e - en
def makimaTangent (p0 p1 p2 p3 : Float) : Float :=
  let w1 := Float.abs (p3 - p2) + Float.abs (p3 + p2) * 0.5
  let w2 := Float.abs (p1 - p0) + Float.abs (p1 + p0) * 0.5
  if w1 + w2 == 0 then (p1 + p2) * 0.5 else (w1 * p1 + w2 * p2) / (w1 + w2)

-- Animation::makima_interpolate_in_time (double)
def makimaInTime (f to pre post prePre postPost w toT preT postT prePreT postPostT : Float) : Float :=
  let toC := toT == 0
  let preC := preT == 0
  let postC := postT - toT == 0
  let prePreC := preT - prePreT == 0
  let postPostC := postPostT - postT == 0
  let mFrom := if toC then 0 else (to - f) / toT
  let mPre := if preC then 0 else (f - pre) / -preT
  let mPost := if postC then 0 else (post - to) / (postT - toT)
  let mPre := if preC then (if postC then mFrom else akimaExtrapolate mFrom mPost) else mPre
  let mPost := if postC then (if preC then mFrom else akimaExtrapolate mFrom mPre) else mPost
  let mPrePre := if prePreC then akimaExtrapolate mPre mFrom else (pre - prePre) / (preT - prePreT)
  let mPostPost := if postPostC then akimaExtrapolate mPost mFrom else (postPost - post) / (postPostT - postT)
  let tFrom := makimaTangent mPrePre mPre mFrom mPost
  let tTo := makimaTangent mPre mFrom mPost mPostPost
  let s2 := w * w
  let s3 := s2 * w
  (2 * s3 - 3 * s2 + 1) * f + (s3 - 2 * s2 + w) * toT * tFrom + (-2 * s3 + 3 * s2) * to + (s3 - s2) * toT * tTo

/-- The shared prelude: Basis round trip, then the shortest-path flips. -/
def align4 (a b pre post : Q) : Q × Q × Q × Q :=
  let fromQ := rotationQuaternion a
  let preQ := rotationQuaternion pre
  let toQ := rotationQuaternion b
  let postQ := rotationQuaternion post
  let flip1 := signbit (fromQ.dot preQ)
  let preQ := if flip1 then preQ.neg else preQ
  let flip2 := signbit (fromQ.dot toQ)
  let toQ := if flip2 then toQ.neg else toQ
  let flip3 := if flip2 then toQ.dot postQ <= 0 else signbit (toQ.dot postQ)
  let postQ := if flip3 then postQ.neg else postQ
  (fromQ, toQ, preQ, postQ)

def lift3 (f : Float → Float → Float → Float → Float) (a b c d : Q) : Q :=
  ⟨f a.x b.x c.x d.x, f a.y b.y c.y d.y, f a.z b.z c.z d.z, 0⟩

namespace Old
-- Quaternion::blend_log (removed by the patch)
def blendLog (fromQ fromLn toLn toInFromLn : Q) (w : Float) : Q :=
  let fromLn := fromLn.v
  let toLn := toLn.v
  let tif := toInFromLn.v
  let theta := tif.len
  let cross := tif.cross toLn
  let toLn := toLn.add (tif.add (cross.smul 0.5))
  let toLn :=
    if theta >= CMP_EPSILON then
      let c := 1 / (theta * theta)
      let c := if !eqApprox theta PI then c - (1 + Float.cos theta) / (2 * theta * Float.sin theta) else c
      toLn.add ((tif.cross cross).smul c)
    else toLn
  let b := fromLn.lerp toLn w
  fromQ * (Q.exp ⟨b.x, b.y, b.z, 0⟩)

def twoSided (interp : Q → Q → Q → Q → Q) (fromQ toQ preQ postQ : Q) (w : Float) : Q :=
  let lnTo := (fromQ.inverse * toQ).log
  let fromLn := interp Q.zero lnTo (fromQ.inverse * preQ).log (fromQ.inverse * postQ).log
  let toLn := interp (toQ.inverse * fromQ).log Q.zero (toQ.inverse * preQ).log (toQ.inverse * postQ).log
  blendLog fromQ fromLn toLn lnTo w

def sci (a b pre post : Q) (w : Float) : Q :=
  let (f, t, p, q) := align4 a b pre post
  twoSided (lift3 (fun x y z u => cubic x y z u w)) f t p q w

def sciInTime (a b pre post : Q) (w bT preT postT : Float) : Q :=
  let (f, t, p, q) := align4 a b pre post
  twoSided (lift3 (fun x y z u => cubicInTime x y z u w bT preT postT)) f t p q w
end Old

namespace New
def oneSided (fix : Bool) (interp : Q → Q → Q → Q → Q) (fromQ toQ preQ postQ : Q) (w : Float) : Q :=
  let blendQ := fromQ.slerp toQ w
  let blendQ := if fix then blendQ.normalized else blendQ
  let bi := blendQ.inverse
  let ln := interp (bi * fromQ).log (bi * toQ).log (bi * preQ).log (bi * postQ).log
  blendQ * ln.exp

def sci (fix : Bool) (a b pre post : Q) (w : Float) : Q :=
  let (f, t, p, q) := align4 a b pre post
  oneSided fix (lift3 (fun x y z u => cubic x y z u w)) f t p q w

def sciInTime (fix : Bool) (a b pre post : Q) (w bT preT postT : Float) : Q :=
  let (f, t, p, q) := align4 a b pre post
  let cit := if fix then cubicInTimeFixed else cubicInTime
  oneSided fix (lift3 (fun x y z u => cit x y z u w bT preT postT)) f t p q w
end New

/-- The six-key prelude of Animation::spherical_makima_interpolate_in_time. -/
def align6 (a b pre post prePre postPost : Q) : Q × Q × Q × Q × Q × Q :=
  let fromQ := rotationQuaternion a
  let preQ := rotationQuaternion pre
  let toQ := rotationQuaternion b
  let postQ := rotationQuaternion post
  let prePreQ := rotationQuaternion prePre
  let postPostQ := rotationQuaternion postPost
  let flip1 := signbit (fromQ.dot preQ)
  let preQ := if flip1 then preQ.neg else preQ
  let flip0 := if flip1 then preQ.dot prePreQ <= 0 else signbit (preQ.dot prePreQ)
  let prePreQ := if flip0 then prePreQ.neg else prePreQ
  let flip2 := signbit (fromQ.dot toQ)
  let toQ := if flip2 then toQ.neg else toQ
  let flip3 := if flip2 then toQ.dot postQ <= 0 else signbit (toQ.dot postQ)
  let postQ := if flip3 then postQ.neg else postQ
  let flip4 := if flip3 then postQ.dot postPostQ <= 0 else signbit (postQ.dot postPostQ)
  let postPostQ := if flip4 then postPostQ.neg else postPostQ
  (fromQ, toQ, preQ, postQ, prePreQ, postPostQ)

def lift6 (f : Float → Float → Float → Float → Float → Float → Float) (a b c d e g : Q) : Q :=
  ⟨f a.x b.x c.x d.x e.x g.x, f a.y b.y c.y d.y e.y g.y, f a.z b.z c.z d.z e.z g.z, 0⟩

structure Times where
  toT : Float
  preT : Float
  postT : Float
  prePreT : Float
  postPostT : Float
  deriving Repr, Inhabited

-- Old Animation::get_nearest_log was the same body as Quaternion::get_nearest_log.
def Old.makima (a b pre post prePre postPost : Q) (w : Float) (tm : Times) : Q :=
  let (f, t, p, q, pp, qq) := align6 a b pre post prePre postPost
  let m := lift6 (fun x0 x1 x2 x3 x4 x5 => makimaInTime x0 x1 x2 x3 x4 x5 w tm.toT tm.preT tm.postT tm.prePreT tm.postPostT)
  let lnTo := (f.inverse * t).log
  let lnPre := (f.inverse * p).log
  let lnPost := (f.inverse * q).log
  let fromLn := m Q.zero lnTo lnPre lnPost ((f.inverse * pp).getNearestLog lnPre) ((f.inverse * qq).getNearestLog lnPost)
  let lnFrom2 := (t.inverse * f).log
  let lnPre2 := (t.inverse * p).log
  let lnPost2 := (t.inverse * q).log
  let toLn := m lnFrom2 Q.zero lnPre2 lnPost2 ((t.inverse * pp).getNearestLog lnPre2) ((t.inverse * qq).getNearestLog lnPost2)
  Old.blendLog f fromLn toLn lnTo w

def New.makima (fix : Bool) (a b pre post prePre postPost : Q) (w : Float) (tm : Times) : Q :=
  let (f, t, p, q, pp, qq) := align6 a b pre post prePre postPost
  let m := lift6 (fun x0 x1 x2 x3 x4 x5 => makimaInTime x0 x1 x2 x3 x4 x5 w tm.toT tm.preT tm.postT tm.prePreT tm.postPostT)
  let blendQ := f.slerp t w
  let blendQ := if fix then blendQ.normalized else blendQ
  let bi := blendQ.inverse
  let lnPre := (bi * p).log
  let lnPost := (bi * q).log
  let ln := m (bi * f).log (bi * t).log lnPre lnPost ((bi * pp).getNearestLog lnPre) ((bi * qq).getNearestLog lnPost)
  blendQ * ln.exp

/-- Angle between the rotations two quaternions stand for (sign ignored). -/
def rotDist (a b : Q) : Float :=
  let d := Float.abs ((a.normalized).dot (b.normalized))
  2 * Float.acos (if d > 1 then 1 else d)

end QInterp
