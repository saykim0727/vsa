(*
  B2R2 - the Next-Generation Reversing Platform

  Author: Dongkwan Kim <dkay@kaist.ac.kr>

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

[<AutoOpen>]
module internal Bool3Helper =
  exception ArithTypeMismatchException

  let noSuchOpErr b1 b2 =
    failwithf "No such operation for (%s * %s)" (b1.ToString ())
                                                (b2.ToString ())

/// 4.2.6 Boolean of flag setup and bit arithmetics
/// This may be used for comparison.
type Bool3 =
  | True
  | False
  | Maybe

  // We cannot override bool operation
  // So we will use Bool3.operation
(*  static member (&&&) (b1: Bool3, b2: Bool3) =
    Bool3.b3and b1 b2

  static member (|||) (b1: Bool3, b2: Bool3) =
    Bool3.b3or b1 b2

  static member (~~) (b1: Bool3) =
    Bool3.b3not b1

  static member (^^^) (b1: Bool3, b2: Bool3) =
    Bool3.b3xor b1 b2
*)

  static member b3and b1 b2 =
    match b1, b2 with
    | Bool3.False , _           -> Bool3.False
    | _           , Bool3.False -> Bool3.False
    | Bool3.Maybe , _           -> Bool3.Maybe
    | _           , Bool3.Maybe -> Bool3.Maybe
    | Bool3.True  , Bool3.True  -> Bool3.True

  static member b3or b1 b2 =
    match b1, b2 with
    | Bool3.True  , _           -> Bool3.True
    | _           , Bool3.True  -> Bool3.True
    | Bool3.Maybe , _           -> Bool3.Maybe
    | _           , Bool3.Maybe -> Bool3.Maybe
    | Bool3.False , Bool3.False -> Bool3.False

  static member b3not b1 =
    match b1 with
    | Bool3.False -> Bool3.True
    | Bool3.Maybe -> Bool3.Maybe
    | Bool3.True  -> Bool3.False

  static member b3xor b1 b2 =
    match b1, b2 with
    | Bool3.Maybe , _           -> Bool3.Maybe
    | _           , Bool3.Maybe -> Bool3.Maybe
    | (b1, b2) when b1 = b2     -> Bool3.False
    | (b1, b2) when b1 <> b2    -> Bool3.True
    // In fact, below will be never reached ...
    | _           , _           -> noSuchOpErr b1 b2

  static member b3join b1 b2 =
    if b1 = b2 then b1
    else Bool3.Maybe

