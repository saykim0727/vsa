(*
  B2R2 - the Next-Generation Reversing Platform

  Author: Sang Kil Cha <sangkilc@kaist.ac.kr>
          Soomin Kim <soomink@kaist.ac.kr>

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

namespace B2R2.BinGraph

/// We distinguish edges of a CFG by classifying them into several kinds.
type CFGEdgeKind =
  /// An edge of a direct jump, e.g., JMP +0x42.
  | InterJmpEdge
  /// An edge of a conditional jump that is exercised when the condition is
  /// true.
  | InterCJmpTrueEdge
  /// An edge of a conditional jump that is exercised when the condition is
  /// false.
  | InterCJmpFalseEdge
  /// A direct jump edge only visible from an IR-level CFG, because there is a
  /// control-flow inside a machine instruction.
  | IntraJmpEdge
  /// A true conditional edge only visible from an IR-level CFG, because there
  /// is a control-flow inside a machine instruction.
  | IntraCJmpTrueEdge
  /// A false conditional edge only visible from an IR-level CFG, because there
  /// is a control-flow inside a machine instruction.
  | IntraCJmpFalseEdge
  /// An edge of a regular call instruction.
  | CallEdge
  /// An edge from an indirect call/jmp instruction.
  | IndirectEdge
  /// An edge of a call/jmp instruction to an external function or PLT.
  | ExternalEdge
  /// An edge of a function return.
  | RetEdge
  /// A simple fall-through case. This type is created when an edge cuts in two
  /// consecutive instructions, or after a call instruction.
  | FallThroughEdge
  /// An implicit edge that is not explicitly visible from the current CALL
  /// instruction, but visible within the function. If there is a path in the
  /// callee that calls a function, then we create an implicit edge from a
  /// caller to any of the callees.
  | ImplicitCallEdge
  /// Unknown edge type. This should be an error case.
  | UnknownEdge
