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

open B2R2 // For Addr

type Name = string

// TODO : infer accurate postfixOp
type PostfixOp =
  | Inc
  | Dec
  | Unknown

/// 2.1 Memory Region
/// This is also used in ValueSet when fetching StridedIntervals.
[<StructuralEquality; StructuralComparison>]
type MemRgn =
  // Global represents all memory (exists only one)
  | Global
  // Local represents function stack frame: (name) * (start address)
  // TODO: we can change Name * Addr to Function
  | Local of Name * Addr
  (* Heap represents function heap frame: (name) * (start address) Here, the
   * name may also represent n-th callsite. *)
  // TODO: need to consider representation of Heap
  | Heap of Name * Addr

  override __.ToString () =
    match __ with
    | Global -> "Global"
    | Local (name, addr)
    | Heap (name, addr) -> sprintf "AR_%s(0x%x)" name addr
