(*
  B2R2 - the Next-Generation Reversing Platform

  Author: Soomin Kim <soomink@kaist.ac.kr>

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

[<RequireQualifiedAccess>]
module B2R2.BinIR.SSA.AST

open B2R2
open B2R2.BinIR

exception InvalidExprException

let rec translateDest = function
  | LowUIR.Var (ty, r, n, _) -> { Kind = RegVar (ty, r, n); Identifier = -1 }
  | LowUIR.PCVar (ty, _) -> { Kind = PCVar (ty); Identifier = -1 }
  | LowUIR.TempVar (ty, n) -> { Kind = TempVar (ty, n); Identifier = -1 }
  | _ -> raise InvalidExprException

let private translateLabel addr = function
  | LowUIR.Name symb -> addr, symb
  | LowUIR.Undefined (_, s) -> addr, (s, -1)
  | _ -> raise InvalidExprException

let rec translateExpr = function
  | LowUIR.Num bv -> Num bv
  | (LowUIR.Var _ as e)
  | (LowUIR.PCVar _ as e)
  | (LowUIR.TempVar _ as e) -> Var <| translateDest e
  | LowUIR.UnOp (op, e, _, _) -> UnOp (op, translateExpr e)
  | LowUIR.FuncName s -> FuncName s
  | LowUIR.BinOp (op, ty, e1, e2, _, _) ->
    BinOp (op, ty, translateExpr e1, translateExpr e2)
  | LowUIR.RelOp (op, e1, e2, _, _) ->
    RelOp (op, translateExpr e1, translateExpr e2)
  | LowUIR.Load (_, ty, e, _, _) ->
    Load ({ Kind = MemVar; Identifier = -1 }, ty, translateExpr e)
  | LowUIR.Ite (e1, e2, e3, _, _) ->
    Ite (translateExpr e1, translateExpr e2, translateExpr e3)
  | LowUIR.Cast (op, ty, e, _, _) -> Cast (op, ty, translateExpr e)
  | LowUIR.Extract (e, ty, pos, _, _) -> Extract (translateExpr e, ty, pos)
  | LowUIR.Undefined (ty, s) -> Undefined (ty, s)
  | _ -> raise InvalidExprException /// Name

let rec internal translateStmtAux defaultRegType addr = function
  | LowUIR.ISMark _ -> None
  | LowUIR.IEMark addr ->
    let pc = { Kind = PCVar (defaultRegType); Identifier = -1 }
    let num = Num <| BitVector.ofUInt64 addr defaultRegType
    Def (pc, num) |> Some
  | LowUIR.LMark symb ->
    LMark (addr, symb) |> Some
  | LowUIR.Put (var, expr) ->
    let dest = translateDest var
    let expr = translateExpr expr
    Def (dest, expr) |> Some
  | LowUIR.Store (_, addr, expr) ->
    let addr = translateExpr addr
    let expr = translateExpr expr
    let mem = { Kind = MemVar; Identifier = -1 }
    let store = Store (mem, addr, expr)
    Def (mem, store) |> Some
  | LowUIR.Jmp (expr) ->
    let label = translateLabel addr expr
    let jmp = IntraJmp label
    Jmp jmp |> Some
  | LowUIR.CJmp (expr, label1, label2) ->
    let expr = translateExpr expr
    let label1 = translateLabel addr label1
    let label2 = translateLabel addr label2
    let jmp = IntraCJmp (expr, label1, label2)
    Jmp jmp |> Some
  | LowUIR.InterJmp (pc, expr, _) ->
    let pc = translateDest pc
    let expr = translateExpr expr
    let jmp = InterJmp (pc, expr)
    Jmp jmp |> Some
  | LowUIR.InterCJmp (expr1, pc, expr2, expr3) ->
    let pc = translateDest pc
    let expr1 = translateExpr expr1
    let expr2 = translateExpr expr2
    let expr3 = translateExpr expr3
    let jmp = InterCJmp (expr1, pc, expr2, expr3)
    Jmp jmp |> Some
  | LowUIR.SideEffect s ->
    SideEffect s |> Some

let translateStmts defaultRegType addr stmts =
  stmts |> Array.choose (translateStmtAux defaultRegType addr)
