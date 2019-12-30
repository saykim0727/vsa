(*
  B2R2 - the Next-Generation Reversing Platform

  Author: Sang Kil Cha <sangkilc@kaist.ac.kr>

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

namespace B2R2

/// Raised when two address ranges overlap in an ARMap, which does not allow
/// overlapping intervals.
exception RangeOverlapException

/// Raised when creating/handling AddrRange that has wrong interval, i.e., Min
/// value is larger than Max value.
exception InvalidAddrRangeException

/// Address type in B2R2 is 64-bit unsigned integer.
type Addr = uint64

module Addr =
  let toString wordSize (addr: Addr) =
    if wordSize = WordSize.Bit32 then addr.ToString ("X8")
    else addr.ToString ("X16")

type AddrRange =
  val Min: Addr
  val Max: Addr

  new (min, max) =
    if min >= max then raise InvalidAddrRangeException else ()
    { Min = min; Max = max }

  override __.ToString () =
    __.Min.ToString ("X") + " -- " + __.Max.ToString ("X")

  override __.Equals (rhs: obj) =
    match rhs with
    | :? AddrRange as r -> __.Min = r.Min && __.Max = r.Max
    | _ -> raise InvalidAddrRangeException

  override __.GetHashCode () =
    hash ( __.Min, __.Max )

  member __.ToTuple () =
    __.Min, __.Max

  static member inline GetMin (range: AddrRange) = range.Min

  static member inline GetMax (range: AddrRange) = range.Max

// vim: set tw=80 sts=2 sw=2: