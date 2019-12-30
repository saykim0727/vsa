(*
  B2R2 - the Next-Generation Reversing Platform

  Author: Dongkwan Kim <dkay@kaist.ac.kr>
          Hyunki Kim <saykim0727@kaist.ac.kr>

  Copyright (c) SoftSec Lab. @ KAIST, since 2016

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
*)

namespace B2R2.VSA

open B2R2

open System

[<AutoOpen>]
module internal StridedIntervalHelper =
  exception StridedIntervalTypeException
  exception StridedIntervalNotImplemented
  exception StridedIntervalBoundException

  let nSizeErr t =
    failwithf "Invalid Bits value : %s" (t.ToString ())

  let boundErr a b c d =
    failwithf "Invalid Bound: [%s, %s] [%s, %s]" (a.ToString ())
                                                 (b.ToString ())
                                                 (c.ToString ())
                                                 (d.ToString ())

  // This only gets positive numbers as the inputs are strides. Therefore, we do
  // not need to consider the signedness.
  let rec gcd a b =
    if BitVector.isTrue <| BitVector.slt a b then gcd b a
    elif BitVector.isZero b then BitVector.abs a
    else gcd b (a % b)

  let lcm a b =
    if BitVector.isZero a then a
    elif BitVector.isZero b then b
    else a * b / (gcd a b)

  let pow a b =
    let bits = BitVector.getType a
    let one = BitVector.one bits
    if BitVector.isZero b then one
    else BitVector.shl a (b - one)

  let isDivisible a b =
    if BitVector.isZero a then true
    elif BitVector.isZero b then false
    elif BitVector.isZero <| (a % b) then true
    else false

  let minBV = Seq.reduce BitVector.smin

  let maxBV = Seq.reduce BitVector.smax

  let getSignedMin bits =
    match bits with
    | 1<rt> -> BitVector.zero bits
    | _ -> BitVector.signedMin bits

  let getSignedMax bits =
    match bits with
    | 1<rt> -> BitVector.one bits
    | _ -> BitVector.signedMax bits

// Warren's algorithm. This only handles unsigned integers.
[<AutoOpen>]
module Warren =
  let minOR a b c d bits =
    let one = BitVector.one bits
    let m = getSignedMin bits
    let rec loop a c m =
      if BitVector.isZero m then
        a ||| c
      else
        let newA = (a ||| m) &&& -m
        let newC = (c ||| m) &&& -m
        if not (BitVector.isZero ((~~~a) &&& c &&& m)) &&
           (BitVector.isTrue <| BitVector.lt newA b) then
          newA ||| c
        elif not (BitVector.isZero (a &&& (~~~c) &&& m)) &&
             (BitVector.isTrue <| BitVector.lt newC d) then
          a ||| newC
        else
          loop a c (BitVector.shr m one)
    loop a c m

  let maxOR a b c d bits =
    let one = BitVector.one bits
    let m = getSignedMin bits
    let rec loop b d m =
      if BitVector.isZero m then
        b ||| d
      else
        if not (BitVector.isZero (b &&& d &&& m)) then
          let newB = (b - m) ||| (m - one)
          let newD = (d - m) ||| (m - one)
          if BitVector.isTrue <| BitVector.ge newB a then
            newB ||| d
          elif BitVector.isTrue <| BitVector.ge newD c then
            b ||| newD
          else
            loop b d (BitVector.shr m one)
        else
          loop b d (BitVector.shr m one)
    loop b d m

type StridedIntervalValue = {
    Stride : BitVector
    Lower : BitVector
    Upper : BitVector
  }

type StridedIntervalType =
  | Value of StridedIntervalValue
  | All   // This represents Top (1[min,max])
  | None  // This represents Bottom (empty)

type StridedInterval = {
    Bits : RegType
    SI : StridedIntervalType
  }
with
  override __.ToString () =
    let str =
      match __.SI with
      | Value sival ->
        let st = sival.Stride.ToString ()
        let lb = sival.Lower.ToString ()
        let ub = sival.Upper.ToString ()
        sprintf "%s[%s, %s]" st lb ub
      | All -> "All"
      | None -> "None"
    sprintf "SI:I%s (%s)" (__.Bits.ToString ()) str

  /// This returns the effective (real) upper bound. This is because the
  /// upperbound may not be included in a given strided interval.
  /// ex) 4[0,15] -> 4[0,12]
  [<CompiledName("getRealUpperBound")>]
  static member getRealUpperBound st lb ub =
    if BitVector.isZero st then lb
    else lb + st * ((ub - lb) |/| st)

  static member getUpper si =
    match si.SI with
    | Value sival -> sival.Upper
    | _ -> raise StridedIntervalTypeException

  member __.MinValue = getSignedMin __.Bits

  member __.MaxValue =
    match __.SI with
    | Value sival ->
      let ub = getSignedMax __.Bits
      StridedInterval.getRealUpperBound sival.Stride sival.Lower ub
    | _ -> raise StridedIntervalTypeException

  // For widening bits
  [<CompiledName("SetType")>]
  static member setType si bits =
    match si.SI with
    | None
    | All -> { si with Bits = bits }
    | Value sival ->
      let ub = BitVector.extract sival.Upper bits 0
      let lb = BitVector.extract sival.Lower bits 0
      let st = BitVector.extract sival.Stride bits 0
      { Bits = bits; SI = StridedInterval.initSI st lb ub bits }

  // For casting operation
  [<CompiledName("SetSI")>]
  static member setSi si =
    match si.SI with
    | Value sival ->
      let bits = BitVector.ofInt64 (si.Bits |> int64) si.Bits
      let one = BitVector.one si.Bits
      let two = one + one
      let len = pow two bits - one
      let ub, lb, st = sival.Upper, sival.Lower, sival.Stride
      if (st = one) && (ub - lb = len) then { si with SI = All }
      else si
    | _ as e -> { si with SI = e }

  /// This is a wrapper for explicit StridedIntervalValue.
  [<CompiledName("initSI")>]
  static member initSI st lb ub bits =
    let zero = BitVector.zero bits
    let one = BitVector.one bits
    let two = one + one
    match bits with
    // This represents StridedInterval for Bool3.
    | 1<rt> -> Value ({ Stride = st; Lower = lb; Upper = ub })
    | _ ->
      let signedMin = getSignedMin bits
      let signedMax = getSignedMax bits
      // we do not need to check None here because we handle None directly.
      let newUb = StridedInterval.getRealUpperBound st lb ub
      let newSt =
        if lb = newUb then zero
        else st
      if lb = signedMin && newUb = signedMax && newSt = one then All
      elif BitVector.isTrue <| BitVector.sgt lb newUb then All
      else Value ({ Stride = newSt; Lower = lb; Upper = newUb })

  [<CompiledName("init")>]
  static member init st lb ub bits =
    let sival = StridedInterval.initSI st lb ub bits
    { Bits = bits; SI = sival }

  [<CompiledName("IsAll")>]
  static member isAll si =
    // Because we explicitly set All, we do not need to check other boundaries
    // here.
    match si.SI with
    | All -> true
    | _ -> false

  [<CompiledName("IsNone")>]
  static member isNone si =
    match si.SI with
    | None -> true
    | _ -> false

  [<CompiledName("IsConst")>]
  // As we make stride zero for all StridedInterval whose lowerbound and
  // upperbound are the same, we only need to check the stride.
  static member isConst si = BitVector.isZero si.Stride

  static member isConstSi si =
    match si.SI with
    | Value sival -> StridedInterval.isConst sival
    | _ -> false

  [<CompiledName("GetType")>]
  static member getType (si: StridedInterval) = si.Bits

  [<CompiledName("Concrete")>]
  static member concrete (si: StridedInterval) =
    let rec loop accList st lb ub =
      if lb = ub then
        lb :: accList |> List.rev
      elif BitVector.isTrue <| BitVector.sgt lb ub then
        accList |> List.rev
      else
        loop (lb :: accList) st (lb + st) ub
    match si.SI with
    | Value sival -> loop [] sival.Stride sival.Lower sival.Upper
    | None -> []
    | All -> raise StridedIntervalTypeException

  static member getConst si =
    match si.SI with
    | Value sival -> sival.Lower
    | (_ as e) -> failwithf "StridedInterval getConst not implemented %A" e

  /// https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf
  /// 3.1. Wrapped Intervals, Formally
  [<CompiledName("Cardinality")>]
  static member cardinality (si: StridedInterval) =
    let bits = si.Bits
    let zero = BitVector.zero bits
    let one = BitVector.one bits
    let two = one + one
    let typeBv = BitVector.ofInt32 (RegType.toByteWidth bits) bits
    match si.SI with
    | None -> zero
    | All -> pow two typeBv
    | Value sival -> ((sival.Upper - sival.Lower) |/| sival.Stride) + one

  [<CompiledName("OfBV")>]
  static member ofBV (bv: BitVector) =
    let bits = BitVector.getType bv
    let zero = BitVector.zero bits
    { Bits = bits; SI = StridedInterval.initSI zero bv bv bits }

  [<CompiledName("OfUInt64")>]
  static member ofUInt64 (stride: uint64) (lower: uint64) (upper: uint64) bits =
    let st = BitVector.ofUInt64 stride bits
    let lb = BitVector.ofUInt64 lower bits
    let ub = BitVector.ofUInt64 upper bits
    { Bits = bits; SI = StridedInterval.initSI st lb ub bits }

  [<CompiledName("OfInt64")>]
  static member ofInt64 (stride: int64) (lower: int64) (upper: int64) bits =
    StridedInterval.ofUInt64 (uint64 stride) (uint64 lower) (uint64 upper) bits

  [<CompiledName("OfUInt32")>]
  static member ofUInt32 (stride: uint32) (lower: uint32) (upper: uint32) bits =
    StridedInterval.ofUInt64 (uint64 stride) (uint64 lower) (uint64 upper) bits

  [<CompiledName("OfUInt32")>]
  static member ofInt32 (stride: int32) (lower: int32) (upper: int32) bits =
    StridedInterval.ofUInt64 (uint64 stride) (uint64 lower) (uint64 upper) bits

  [<CompiledName("All")>]
  static member all bits =
    { Bits = bits; SI = StridedIntervalType.All }

  [<CompiledName("None")>]
  static member none bits =
    { Bits = bits; SI = StridedIntervalType.None }

  static member zero bits =
    let zero = BitVector.zero bits
    let sival = { Stride = zero; Lower = zero; Upper = zero }
    { Bits = bits; SI = Value (sival) }

  static member one bits =
    let zero = BitVector.zero bits
    let one = BitVector.one bits
    let sival = { Stride = zero; Lower = one; Upper = one }
    { Bits = bits; SI = Value (sival) }

  static member True = StridedInterval.one 1<rt>

  static member False = StridedInterval.zero 1<rt>

  static member Maybe = StridedInterval.all 1<rt>

  /// Below represents abstract interpretation for the infix operators.
  static member (+) ((si1: StridedInterval), (si2: StridedInterval)) =
    StridedInterval.add si1 si2

  static member (*) ((si1: StridedInterval), (si2: StridedInterval)) =
    StridedInterval.mul si1 si2

  static member (/) ((si1: StridedInterval), (si2: StridedInterval)) =
    StridedInterval.sdiv si1 si2

  static member (|/|) ((si1: StridedInterval), (si2: StridedInterval)) =
    StridedInterval.div si1 si2

  static member (%) ((si1: StridedInterval), (si2: StridedInterval)) =
    StridedInterval.smodulo si1 si2

  static member (|%|) ((si1: StridedInterval), (si2: StridedInterval)) =
    StridedInterval.modulo si1 si2

  static member (~-) (si1: StridedInterval) =
    StridedInterval.neg si1

  static member (-) ((si1: StridedInterval), (si2: StridedInterval)) =
    StridedInterval.sub si1 si2

  static member (|||) ((si1: StridedInterval),(si2: StridedInterval)) =
    StridedInterval.bor si1 si2

  static member (~~~) (si1: StridedInterval) =
    StridedInterval.bnot si1

  static member (&&&) ((si1: StridedInterval), (si2: StridedInterval)) =
    StridedInterval.band si1 si2

  static member (^^^) ((si1: StridedInterval), (si2: StridedInterval)) =
    StridedInterval.bxor si1 si2

  /// Below represents actual implementation based on :
  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 4.2.1 Addition
  [<CompiledName("Add")>]
  static member add si1 si2 =
    match si1.SI, si2.SI with
    | None, _
    | All, _ -> si1
    | _, None
    | _, All -> si2
    | Value sival1, Value sival2 ->
      /// si1: s1[a, b], si2: s2[c, d]
      let bits = si1.Bits
      let one = BitVector.one bits
      let signedMin = getSignedMin bits
      let signedMax = getSignedMax bits
      let a, b = sival1.Lower, sival1.Upper
      let c, d = sival2.Lower, sival2.Upper
      let lb = a + c
      let ub = b + d
      let u = a &&& c &&& ~~~lb &&& ~~~(b &&& d &&& ~~~ub)
      let v = ((a ^^^ c) ||| ~~~(a ^^^ lb)) &&& (~~~b &&& ~~~d &&& ub)
      let newSt, newLb, newUb =
        // Check overflow happens
        if BitVector.isNegative (u ||| v) then
          // if overflow or underflow happens, set minimum and maximum bound.
          one, signedMin, signedMax
        else
          // if no overflow, gcd of two strides will be the new stride.
          gcd sival1.Stride sival2.Stride, lb, ub
      { si1 with SI = StridedInterval.initSI newSt newLb newUb bits }

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 4.2.2 Unary minus
  [<CompiledName("Neg")>]
  static member neg si =
    match si.SI with
    | None
    | All -> si
    | Value sival ->
      let bits = si.Bits
      let zero = BitVector.zero bits
      let one = BitVector.one bits
      let signedMin = getSignedMin bits
      let signedMax = getSignedMax bits
      let st, lb, ub = sival.Stride, sival.Lower, sival.Upper
      let newSt, newLb, newUb =
        if lb = ub && lb = si.MinValue then
          zero, signedMin, signedMin
        elif lb <> si.MinValue then
          st, -ub, -lb
        else
          one, signedMin, signedMax
      { si with SI = StridedInterval.initSI newSt newLb newUb bits }

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 4.2.3 Subtraction Increment and Decrement
  /// F# do not support increment and decrement as they only works for the
  /// mutable.
  [<CompiledName("Sub")>]
  static member sub si1 si2 =
    StridedInterval.add si1 (StridedInterval.neg si2)

  [<CompiledName("Inc")>]
  static member inc si1 =
    StridedInterval.add si1 (StridedInterval.one si1.Bits)

  [<CompiledName("Dec")>]
  static member dec si1 =
    StridedInterval.sub si1 (StridedInterval.one si1.Bits)

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  static member signedMinOR a b c d bits =
    let one = BitVector.one bits
    let isNeg x = BitVector.isNegative x
    match (isNeg a), (isNeg b), (isNeg c), (isNeg d) with
    | true, true, true, true -> Warren.minOR a b c d bits
    | true, true, true, false -> a
    | true, true, false, false -> Warren.minOR a b c d bits
    | true, false, true, true -> c
    | true, false, true, false -> BitVector.smin a c
    | true, false, false, false -> Warren.minOR a -one c d bits
    | false, false, true, true -> Warren.minOR a b c d bits
    | false, false, true, false -> Warren.minOR a b c -one bits
    | false, false, false, false -> Warren.minOR a b c d bits
    | _ -> boundErr a b c d // This will never reach as a <= b and c <= d

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  static member signedMaxOR a b c d bits =
    let zero = BitVector.zero bits
    let one = BitVector.one bits
    let isNeg x = BitVector.isNegative x
    match (isNeg a), (isNeg b), (isNeg c), (isNeg d) with
    | true, true, true, true -> Warren.maxOR a b c d bits
    | true, true, true, false -> -one
    | true, true, false, false -> Warren.maxOR a b c d bits
    | true, false, true, true -> -one
    | true, false, true, false -> Warren.maxOR zero b zero d bits
    | true, false, false, false -> Warren.maxOR zero b c d bits
    | false, false, true, true -> Warren.maxOR a b c d bits
    | false, false, true, false -> Warren.maxOR a b zero d bits
    | false, false, false, false -> Warren.maxOR a b c d bits
    | _ -> boundErr a b c d // This will never reach as a <= b and c <= d

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 4.2.4. Bitwise Or
  /// This counts the Number of Trailing Zeros (NTZ)
  static member ntz x =
    let bits = BitVector.getType x
    let zero = BitVector.zero bits
    let one = BitVector.one bits
    let rec loop n y =
      if BitVector.isZero y then n
      else loop (n + one) (BitVector.shr y one)
    loop zero (-x &&& (x - one))

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 4.2.4 Bitwise Or
  [<CompiledName("BitwiseOr")>]
  static member bor si1 si2 =
    match si1.SI, si2.SI with
    | None, _
    | All, _ -> si1
    | _, None
    | _, All -> si2
    | Value sival1, Value sival2 ->
      /// si1: s1[a, b], si2: s2[c, d]
      let bits = si1.Bits
      let one = BitVector.one bits
      let zero = BitVector.zero bits
      let a, b = sival1.Lower, sival1.Upper
      let c, d = sival2.Lower, sival2.Upper
      // ntz(x) >= 0
      let t = BitVector.smin <| (StridedInterval.ntz sival1.Stride)
                             <| (StridedInterval.ntz sival2.Stride)
      let mask = (BitVector.shl one t) - one
      let r = (a &&& mask) ||| (c &&& mask)
      let lb = StridedInterval.signedMinOR (a &&& ~~~mask)
                                           (b &&& ~~~mask)
                                           (c &&& ~~~mask)
                                           (d &&& ~~~mask)
                                           bits

      let ub = StridedInterval.signedMaxOR (a &&& ~~~mask)
                                           (b &&& ~~~mask)
                                           (c &&& ~~~mask)
                                           (d &&& ~~~mask)
                                           bits
      let newSt =
        if lb = ub then zero
        else pow (one + one) t
      let newLb = (lb &&& ~~~mask) ||| r
      let newUb = (ub &&& ~~~mask) ||| r
      { si1 with SI = StridedInterval.initSI newSt newLb newUb bits }

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 4.2.5 Bitwise Not, And, Xor
  [<CompiledName("BitwiseNot")>]
  static member bnot si =
    match si.SI with
    | None
    | All -> si
    | Value sival ->
      let lb, ub = ~~~sival.Upper, ~~~sival.Lower
      { si with SI = StridedInterval.initSI sival.Stride lb ub si.Bits }

  [<CompiledName("BitwiseAnd")>]
  static member band si1 si2 =
    // We may implement this with minAnd and maxAnd similar to BitwiseOr.
    StridedInterval.bor (StridedInterval.bnot si1) (StridedInterval.bnot si2)
    |> StridedInterval.bnot

  [<CompiledName("BitwiseXor")>]
  static member bxor si1 si2 =
    // We may implement this with minXor and maxXor similar to BitwiseOr.
    let t1 = StridedInterval.bor (StridedInterval.bnot si1) si2
    let t2 = StridedInterval.bor si1 (StridedInterval.bnot si2)
    StridedInterval.bor (StridedInterval.bnot t1) (StridedInterval.bnot t2)

  /// https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf
  /// 3.1. Wrapped Intervals, Formally
  /// We use two's complement.
  [<CompiledName("Complment")>]
  static member complement (si: StridedInterval) =
    match si.SI with
    | None -> { si with SI = All }
    | All -> { si with SI = None }
    | Value sival ->
      let one = BitVector.one si.Bits
      let lb = sival.Upper + one
      let ub = sival.Lower - one
      let st = BitVector.one si.Bits
      if BitVector.isTrue <| BitVector.sgt lb ub then
        { si with SI = StridedInterval.initSI st ub lb si.Bits }
      else { si with SI = StridedInterval.initSI st lb ub si.Bits }

  /// https://people.eng.unimelb.edu.au/pstuckey/papers/toplas15.pdf
  /// 3.2. Ordering wrapped intervals
  /// In addition, we need to check stride using gcd as strided interval can
  /// have different integers. (e.g., 2[2, 6] is not in 2[1, 7])
  /// Here, we also check casting si2 to si1
  [<CompiledName("Contains")>]
  static member contains (si1: StridedInterval) (si2: StridedInterval) =
    if si1 = si2 then true
    else
      match si1.SI, si2.SI with
      | All, _ -> true
      | None, _ -> false
      | Value _, None -> true
      | Value _, All -> false
      | Value sival1, Value sival2 ->
        let st1, st2 = sival1.Stride, sival2.Stride
        let lb2, ub2 = sival2.Lower, sival2.Upper
        if StridedInterval.containsBV sival1 lb2 &&
           StridedInterval.containsBV sival1 ub2 &&
           isDivisible st2 st1 then true
        else false

  [<CompiledName("ContainsBV")>]
  static member containsBV sival (bv: BitVector) =
    // if constant
    if StridedInterval.isConst sival then
      if sival.Lower = bv then true
      else false
    elif BitVector.isTrue <| BitVector.sle sival.Lower bv &&
         BitVector.isTrue <| BitVector.sge sival.Upper bv &&
         isDivisible (bv - sival.Lower) sival.Stride then true
    else false

  // https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf
  // 3.3. Biased Over- and Under-Approximation of Bounds
  // We use over-approximation here. We need to re-consider w-interval.
  // https://drona.csa.iisc.ac.in/~srikant/papers-theses/memocode-2007.pdf
  // 4.1 Set Operations
  [<CompiledName("Union")>]
  static member union si1 si2 =
    match si1.SI, si2.SI with
    | None, _ -> si2
    | _, None -> si1
    | All, _ -> si1
    | _, All -> si2
    | Value sival1, Value sival2 ->
      if StridedInterval.contains si1 si2 then si1
      elif StridedInterval.contains si2 si1 then si2
      else
        // Since we do not consider w-interval, we only need to check
        // upperbound.
        let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
        let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
        let one = BitVector.one si1.Bits
        let minLb =
          if BitVector.isTrue <| BitVector.sle lb1 lb2 then lb1
          else lb2
        let maxUb =
          if BitVector.isTrue <| BitVector.sge ub1 ub2 then ub1
          else ub2
        // Consider const value
        if StridedInterval.isConst sival1 && StridedInterval.isConst sival2 then
          let st = maxUb - minLb
          { si1 with SI = StridedInterval.initSI st minLb maxUb si1.Bits }
        elif StridedInterval.isConst sival1 ||
           StridedInterval.isConst sival2 then
          { si1 with SI = StridedInterval.initSI one minLb maxUb si1.Bits }
        else
          let gcdSt = gcd st1 st2
          { si1 with SI = StridedInterval.initSI gcdSt minLb maxUb si1.Bits }

  // https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf
  // 3.3. Biased Over- and Under-Approximation of Bounds
  // We use over-approximation here. We need to re-consider w-interval.
  // https://drona.csa.iisc.ac.in/~srikant/papers-theses/memocode-2007.pdf
  // 4.1 Set Operations
  [<CompiledName("Intersection")>]
  static member intersection si1 si2 =
    match si1.SI, si2.SI with
    | None, _ -> si1
    | _, None -> si2
    | All, _ -> si2
    | _, All -> si1
    | Value sival1, Value sival2 ->
      // First check if one is a subset of the other.
      if StridedInterval.contains si1 si2 then si2
      elif StridedInterval.contains si2 si1 then si1
      // Since we do not consider w-interval, we only need to check the
      // upperbounds.
      elif BitVector.isTrue <| BitVector.slt sival1.Upper sival2.Lower ||
           BitVector.isTrue <| BitVector.slt sival2.Upper sival1.Lower then
        { si1 with SI = None }
      // From above condition checks, there is no constant intervals left.
      else
        let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
        let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
        let gcdSt = gcd st1 st2
        let minUb =
          if BitVector.isTrue <| BitVector.sle ub1 ub2 then ub1
          else ub2
        let maxLb, maxLbSt, minLb, minLbSt  =
          if BitVector.isTrue <| BitVector.sge lb1 lb2 then lb1, st1, lb2, st2
          else lb2, st2, lb1, st1
        // First check if there exists common values to early reject.
        if not (BitVector.isOne <| gcdSt) &&
           not (isDivisible (lb1 - lb2) gcdSt) then
          { si1 with SI = None }
        else
          // This loop finds new lowerbound.
          let rec loop curLb =
            if isDivisible (curLb - minLb) minLbSt then
              let lcmSt = lcm st1 st2
              let newSi = StridedInterval.initSI lcmSt curLb minUb si1.Bits
              { si1 with SI = newSi }
            elif BitVector.isTrue <| BitVector.sgt curLb minUb then
              { si1 with SI = None }
            else
              loop (curLb + maxLbSt)
          loop maxLb

  static member limitedWiden ub lb cond op =
    match cond.SI with
    | Value sival ->
      let newUb =
        if Inc = op &&
           BitVector.isTrue <| BitVector.sge ub sival.Upper then sival.Upper
        else ub
      let newLb =
        if Dec = op &&
           BitVector.isTrue <| BitVector.sle lb sival.Lower then sival.Lower
        else lb
      newUb, newLb
    | _ -> ub, lb

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 7.1. Widening
  /// TODO : Consider constraint such as Figure 7.1 of
  [<CompiledName("Widen")>]
  static member widen si1 si2 =
    match si1.SI, si2.SI with
    | All, _ -> si1
    | _, All -> si2
    | None, _ -> si2
    | _, None -> si1
    | Value sival1, Value sival2 ->
      let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
      let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
      if si1 = si2 then si1
      else
        let newLb =
          if BitVector.isTrue <| BitVector.sle lb1 lb2 then lb1
          else getSignedMin si1.Bits
        let newUb =
          if BitVector.isTrue <| BitVector.sge ub1 ub2 then ub1
          else getSignedMax si1.Bits
        let newSt =
          if newLb = newUb then BitVector.zero si1.Bits
          elif st1 = st2 && newLb = lb1 && newUb = ub1 then st1
          else BitVector.one si1.Bits
          //let ub, lb = StridedInterval.limitedWiden newUb newLb cond op
        { si1 with SI = StridedInterval.initSI newSt newLb newUb si1.Bits }

  [<CompiledName("Narrow")>]
  static member narrow si1 si2 =
    match si1.SI, si2.SI with
    | All, _ -> si2
    | _, All -> si1
    | None, _ -> si2
    | _, None -> si1
    | Value sival1, Value sival2 ->
      let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
      let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
      let one = StridedInterval.one si1.Bits
      let ub = StridedInterval.getUpper (StridedInterval.removeUpperBounds one)
      if si1 = si2 then si1
      else
        let lb = if lb1 = getSignedMin si1.Bits then lb2 else lb1
        let ub = if ub1 = ub then ub2 else ub1
        let st = if lb = lb1 && ub = ub1 then st1 else BitVector.one si1.Bits
        { si1 with SI = StridedInterval.initSI st lb ub si1.Bits }


  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 3.1. Value-Set
  [<CompiledName("RemoveUpperBounds")>]
  static member removeUpperBounds si =
    match si.SI with
    | None
    | All -> si
    | Value sival ->
      let lb, ub = sival.Lower, getSignedMax si.Bits
      let st =
        if BitVector.isZero sival.Stride then BitVector.one si.Bits
        else sival.Stride
      { si with SI = StridedInterval.initSI st lb ub si.Bits }

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 3.1. Value-Set
  [<CompiledName("RemoveLowerBounds")>]
  static member removeLowerBounds si =
    match si.SI with
    | None
    | All -> si
    | Value sival ->
      let lb, ub = getSignedMin si.Bits, sival.Upper
      let st =
        if BitVector.isZero sival.Stride then BitVector.one si.Bits
        else sival.Stride
      { si with SI = StridedInterval.initSI st lb ub si.Bits }

  static member castHelper si bv bits pos =
    let si1 = BitVector.extract bv bits pos |> StridedInterval.ofBV
    StridedInterval.union si si1

  [<CompiledName("Cast")>]
  static member cast (si: StridedInterval) bits =
    match si.SI with
    | None
    | All -> { si with Bits = bits }
    | Value sival ->
      let ub = BitVector.cast sival.Upper bits
      let lb = BitVector.cast sival.Lower bits
      let st = BitVector.cast sival.Stride bits
      { Bits = bits; SI = StridedInterval.initSI st lb ub bits }

  [<CompiledName("Sext")>]
  static member sext (si: StridedInterval) bits =
    match si.SI with
    | None
    | All -> { si with Bits = bits }
    | Value sival ->
      let ub = BitVector.sext sival.Upper bits
      let lb = BitVector.sext sival.Lower bits
      let st = BitVector.sext sival.Stride bits
      { Bits = bits; SI = StridedInterval.initSI st lb ub bits }

  [<CompiledName("Zext")>]
  static member zext (si: StridedInterval) bits =
    match si.SI with
    | None
    | All -> { si with Bits = bits }
    | Value sival ->
      let ub = BitVector.zext sival.Upper bits
      let lb = BitVector.zext sival.Lower bits
      let st = BitVector.zext sival.Stride bits
      { Bits = bits; SI = StridedInterval.initSI st lb ub bits }

  static member getSignedBit si =
    let one = StridedInterval.one 1<rt>
    let zero = StridedInterval.zero 1<rt>
    match si.SI with
    | Value sival ->
      let isNegLower = BitVector.isNegative sival.Lower
      let isNegUpper = BitVector.isNegative sival.Upper
      match isNegLower, isNegUpper with
      | true, true -> one
      | true, false -> { Bits = 1<rt>; SI = All }
      | false, false -> zero
      | _ -> raise StridedIntervalTypeException
    | All -> { Bits = 1<rt>; SI = All }
    | _ -> raise StridedIntervalTypeException

  // 1st and 2nd will never be executed in normar case
  static member shrHelper l1 u1 l2 u2 =
    match BitVector.isPositive l1, BitVector.isPositive u1 with
    | false, false -> BitVector.shr l1 l2, BitVector.shr u1 u2
    | false, true  -> BitVector.shr l1 l2, BitVector.shr u1 l2
    | true , true  -> BitVector.shr l1 u2, BitVector.shr u1 l2
    | _ -> raise StridedIntervalTypeException

  // https://drona.csa.iisc.ac.in/~srikant/papers-theses/memocode-2007.pdf
  // 4.3 Shift Operations
  [<CompiledName("Shr")>]
  static member shr (si1: StridedInterval) (si2: StridedInterval) =
    match si1.SI, si2.SI with
    | None, _
    | All, _ -> si1
    | _, None
    | _, All -> si2
    | Value sival1, Value sival2 ->
      if BitVector.isNegative sival2.Lower then si1
        // raise StridedIntervalTypeException
      else
        let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
        let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
        let newSt, newLb, newUb =
          if StridedInterval.isConst sival2 then
            let st = BitVector.shr st1 lb2
            let lb, ub = BitVector.shr lb1 lb2, BitVector.shr ub1 lb2
            st, lb, ub
          else
            let st = BitVector.one si1.Bits
            let lb, ub = StridedInterval.shrHelper lb1 ub1 lb2 ub2
            // TODO: this is for test. will be removed later.
            if BitVector.isTrue <| BitVector.sgt lb ub then
              raise StridedIntervalNotImplemented
            st, lb, ub
        { si1 with SI = StridedInterval.initSI newSt newLb newUb si1.Bits }

  // https://drona.csa.iisc.ac.in/~srikant/papers-theses/memocode-2007.pdf
  // 4.3 Shift Operations
  [<CompiledName("Shl")>]
  static member shl (si1: StridedInterval) (si2: StridedInterval) =
    match si1.SI, si2.SI with
    | None, _
    | All, _ -> si1
    | _, None
    | _, All -> si2
    | Value sival1, Value sival2 ->
      if BitVector.isNegative sival2.Lower then si1
        //raise StridedIntervalTypeException
      else
        let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
        let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
        // constant and interval can be handled equally for lb and ub.
        let newLb, newUb = BitVector.shl lb1 lb2, BitVector.shl ub1 ub2
        let newSt =
          if StridedInterval.isConst sival2 then BitVector.shl st1 lb2
          else BitVector.shl (gcd (BitVector.abs lb1) st1) lb2
        { si1 with SI = StridedInterval.initSI newSt newLb newUb si1.Bits }

  [<CompiledName("Sar")>]
  static member sar (si1: StridedInterval) (si2: StridedInterval) =
    match si1.SI, si2.SI with
    | None, _
    | All, _ -> si1
    | _, None
    | _, All -> si2
    | Value sival1, Value sival2 ->
      if BitVector.isNegative sival2.Lower then
        raise StridedIntervalTypeException
      else
        let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
        let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
        let newLb, newUb = BitVector.sar lb1 lb2, BitVector.sar ub1 ub2
        let newSt =
          if StridedInterval.isConst sival2 then BitVector.sar st1 lb2
          else BitVector.one si1.Bits
        { si1 with SI = StridedInterval.initSI newSt newLb newUb si1.Bits }

  [<CompiledName("Extract")>]
  static member extract (si: StridedInterval) bits pos =
    let pos  = pos |> int64
    let shiftSI = StridedInterval.ofInt64 0L pos pos si.Bits
    let andSI =
      let maxBV = BitVector.zero bits - BitVector.one bits
      let max = StridedInterval.ofBV maxBV
      StridedInterval.zext max si.Bits
    let si = StridedInterval.shr si shiftSI
    let si = StridedInterval.band si andSI
    StridedInterval.cast si bits


  /// https://drona.csa.iisc.ac.in/~srikant/papers-theses/memocode-2007.pdf
  /// 4.2 Arithmetic Operations
  [<CompiledName("Mul")>]
  static member mul (si1: StridedInterval) (si2: StridedInterval) =
    match si1.SI, si2.SI with
    | None, _
    | All, _ -> si1
    | _, None
    | _, All -> si2
    | Value sival1, Value sival2 ->
      let bits = si1.Bits
      let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
      let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
      let newSt, newLb, newUb =
        if StridedInterval.isConst sival2 then
          let k = lb2
          let st = BitVector.abs (st1 * k)
          let lb = BitVector.smin (lb1 * k) (ub1 * k)
          let ub = BitVector.smax (lb1 * k) (ub1 * k)
          st, lb, ub
        else
          let candList = [ lb1 * lb2; ub1 * ub2; lb1 * ub2; ub1 * lb2 ]
          let lb, ub = minBV candList, maxBV candList
          let st =
            gcd (BitVector.abs (lb1 * st2)) (BitVector.abs (lb2 * st1))
            |> gcd (st1 * st2)
          st, lb, ub
      { si1 with SI = StridedInterval.initSI newSt newLb newUb bits }

  // TODO : implement StridedInterval.smodulo (WIP)
  [<CompiledName("Smodulo")>]
  static member smodulo (si1: StridedInterval) (si2: StridedInterval) =
    { si1 with SI = All }
//    // TODO : 2[4,8] % 2[-4,2] = ?
//    match si1.SI, si2.SI with
//    | Value sival1, Value sival2 ->
//      let bits = si1.Bits
//      let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
//      let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
//      // TODO : exception handling
//      if (BitVector.isZero lb2) || (BitVector.isZero ub2) then
//        { si1 with Bits = si1.Bits }
//      else // TODO : Normal case
//        let newSt = gcd sival1.Stride sival2.Stride
//        let op x y = BitVector.sdiv x y
//        let newLb, newUb = StridedInterval.getNewBound lb1 lb2 ub1 ub2 bits op
//        { si1 with SI = StridedInterval.initSI newSt newLb newUb bits }
//    | _ -> { si1 with Bits = si1.Bits }

  // TODO : implement StridedInterval.modulo
  [<CompiledName("Modulo")>]
  static member modulo (si1: StridedInterval) (si2: StridedInterval) =
    { si1 with SI = All }

  static member sdivHelper sival1 sival2 =
    // sival2 is not const because we already handled constant before calling
    // this function.
    let getPosMinNegMax st lb ub =
      let candPosMin, candNegMax = lb % st, ub % st
      let posMin =
        if not (BitVector.isPositive candPosMin) then candPosMin + st
        else candPosMin
      let negMax =
        if not (BitVector.isNegative candNegMax) then candNegMax - st
        else candNegMax
      posMin, negMax
    let l1, u1 = sival1.Lower, sival1.Upper
    let l2, u2 = sival2.Lower, sival2.Upper
    let isPos x = BitVector.isPositive x
    let l2Flag, u2Flag = isPos l2, isPos u2
    let l1Flag =
      if BitVector.isZero l1 then l2Flag
      else isPos l1
    let u1Flag =
      if BitVector.isZero u1 then u2Flag
      else isPos u1
    let a, b =
      // This value will not be used
      if not (BitVector.isNegative l2 && BitVector.isPositive u2) then l2, u2
      // Only below will be used
      else getPosMinNegMax sival2.Stride l2 u2
    match l1Flag, u1Flag, l2Flag, u2Flag with
    | false, false, false, false -> u1 / l2, l1 / u2
    | false, false, false, true  -> l1 / a , l1 / b
    | false, false, true , true  -> l1 / l2, u1 / u2
    | false, true , false, false -> u1 / u2, l1 / u2
    | false, true , false, true  -> BitVector.smin (u1 / b) (l1 / a),
                                    BitVector.smax (l1 / b) (u1 / a)
    | true , true , false, false -> u1 / u2, l1 / l2
    | true , true , false, true  -> u1 / b , u1 / a
    | false, true , true , true  -> l1 / l2, u1 / l2
    | true , true , true , true  -> l1 / u2, u1 / l2
    | _ -> raise StridedIntervalTypeException

  // https://drona.csa.iisc.ac.in/~srikant/papers-theses/memocode-2007.pdf
  // 4.2 Arithmetic Operations
  [<CompiledName("Sdiv")>]
  static member sdiv (si1: StridedInterval) (si2: StridedInterval) =
    match si1.SI, si2.SI with
    | None, _
    | All, _ -> si1
    | _, None
    | _, All -> si2
    | Value sival1, Value sival2 ->
      let zero = BitVector.zero si2.Bits
      if StridedInterval.containsBV sival2 zero then
        raise StridedIntervalTypeException
      else
        let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
        let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
        let newSt, newLb, newUb =
          if StridedInterval.isConst sival2 then
            let k = lb2
            let st = BitVector.abs (st1 / k)
            let lb = BitVector.smin (lb1 / k) (ub1 / k)
            let ub = BitVector.smax (lb1 / k) (ub1 / k)
            st, lb, ub
          else
            let st = BitVector.one si1.Bits
            let lb, ub = StridedInterval.sdivHelper sival1 sival2
            st, lb, ub
        { si1 with SI = StridedInterval.initSI newSt newLb newUb si1.Bits }

  [<CompiledName("Div")>]
  static member div (si1: StridedInterval) (si2: StridedInterval) =
    match si1.SI, si2.SI with
    | None, _
    | All, _ -> si1
    | _, None
    | _, All -> si2
    | Value sival1, Value sival2 ->
      let zero = BitVector.zero si2.Bits
      if StridedInterval.containsBV sival2 zero then
        raise StridedIntervalTypeException
      else
        let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
        let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
        let newSt, newLb, newUb =
          if StridedInterval.isConst sival2 then
            let k = lb2
            let st = st1 |/| k
            let lb = lb1 |/| k
            let ub = ub1 |/| k
            st, lb, ub
          else
            let st = BitVector.one si1.Bits
            let lb, ub = lb1 |/| ub2, ub1 |/| lb2
            st, lb, ub
        { si1 with SI = StridedInterval.initSI newSt newLb newUb si1.Bits }

  static member comp op si1 si2 =
    match si1.SI, si2.SI with
    | None, _
    | _, None -> raise StridedIntervalTypeException
    | All, _ -> StridedInterval.Maybe
    | _, All -> StridedInterval.Maybe
    | Value sival1, Value sival2 ->
      let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
      let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
      // s1[a, b], s2[c, d]
      if BitVector.isTrue <| op ub1 lb2 then StridedInterval.True
      elif BitVector.isFalse <| op lb1 ub2 then StridedInterval.False
      else StridedInterval.Maybe

  [<CompiledName("EQ")>]
  static member eq si1 si2 =
    if si1 = si2 then StridedInterval.True
    else StridedInterval.False

  [<CompiledName("NEQ")>]
  static member neq si1 si2 =
    if si1 <> si2 then StridedInterval.True
    else StridedInterval.False

  // TODO: this is for testing signedness. only used for lt, le.
  static member checkSigned si1 si2 =
    match si1.SI, si2.SI with
    | Value sival1, Value sival2 ->
      let st1, lb1, ub1 = sival1.Stride, sival1.Lower, sival1.Upper
      let st2, lb2, ub2 = sival2.Stride, sival2.Lower, sival2.Upper
      if (BitVector.isNegative lb1 && BitVector.isPositive ub1) ||
         (BitVector.isNegative lb2 && BitVector.isPositive ub2) then
           raise StridedIntervalBoundException
      else ()
    | _ -> ()

  [<CompiledName("LT")>]
  static member lt si1 si2 =
    // TODO: this is for test. need to check if there exists real case
    //StridedInterval.checkSigned si1 si2
    StridedInterval.comp BitVector.lt si1 si2

  [<CompiledName("LE")>]
  static member le si1 si2 =
    // TODO: this is for test. need to check if there exists real case
    //StridedInterval.checkSigned si1 si2
    StridedInterval.comp BitVector.le si1 si2

  [<CompiledName("GT")>]
  static member gt si1 si2 = StridedInterval.lt si2 si1

  [<CompiledName("GE")>]
  static member ge si1 si2 = StridedInterval.le si2 si1

  [<CompiledName("SLT")>]
  static member slt si1 si2 = StridedInterval.comp BitVector.slt si1 si2

  [<CompiledName("SLE")>]
  static member sle si1 si2 = StridedInterval.comp BitVector.sle si1 si2

  [<CompiledName("SGT")>]
  static member sgt si1 si2 = StridedInterval.slt si2 si1

  [<CompiledName("SGE")>]
  static member sge si1 si2 = StridedInterval.sle si2 si1

  [<CompiledName("Concat")>]
  static member concat si1 si2 =
    let bit = si1.Bits + si2.Bits
    match si1.SI, si2.SI with
    | Value sival1, Value sival2 ->
      let len1, len2 = si1.Bits, si2.Bits
      let st = BitVector.one bit
      let lb = BitVector.concat sival1.Lower sival2.Lower
      let ub = BitVector.concat sival1.Upper sival2.Upper
      { si1 with SI = StridedInterval.initSI st lb ub bit }
    | (All as e), _
    | _, (All as e) -> { Bits = bit; SI = All }
    | None, _
    | _, None -> failwithf "%A %A" si1 si2
