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

module B2R2.BinGraph.JumpTable

open B2R2
open B2R2.BinIR
open B2R2.BinIR.SSA
open B2R2.FrontEnd
open B2R2.BinFile
open System.Collections.Generic

type Range = {
  Type : RegType
  Left : BitVector
  Right : BitVector
}

type Interval =
  | Top of RegType
  | Empty of RegType
  | Interval of Range

module Interval =
  let t =
    { Type = 1<rt>; Left = BitVector.T; Right = BitVector.T } |> Interval
  let f =
    { Type = 1<rt>; Left = BitVector.F; Right = BitVector.F } |> Interval
  let maybe = Top 1<rt>

  let top ty = Top ty

  let empty ty = Empty ty

  let cons ty left right =
    let isTop =
      BitVector.eq left (right + BitVector.one ty) |> BitVector.isTrue
    if isTop then top ty
    else Interval { Type = ty; Left = left; Right = right }

  let getType = function
    | Top ty -> ty
    | Empty ty -> ty
    | Interval { Type = ty } -> ty

  let getLeft = function
    | Interval { Left = left } -> left
    | Top ty -> BitVector.signedMin ty
    | _ -> failwith "No"

  let getRight = function
    | Interval { Right = right } -> right
    | Top ty -> BitVector.signedMax ty
    | _ -> failwith "No"

  let getUMin = function
    | Top ty -> BitVector.zero ty
    | Empty _ -> failwith "No"
    | Interval { Type = ty ; Left = left ; Right = right } ->
      if BitVector.isNegative (right - left) then BitVector.zero ty else left

  let numElem ty left right =
    if BitVector.isNegative (left - right) then
      BitVector.toUInt32 right - BitVector.toUInt32 left + 1u
    else
      BitVector.toUInt32 left + (1u <<< (RegType.toBitWidth ty))
        - BitVector.toUInt32 right + 1u

  let isEmpty = function
    | Empty _ -> true
    | _ -> false

  let isConst = function
    | Top ty -> false
    | Empty ty -> false
    | Interval { Type = ty; Left = left; Right = right } -> left = right

  let complement = function
    | Top ty -> empty ty
    | Empty ty -> Top ty
    | Interval { Type = ty; Left = left; Right = right } ->
      { Type = ty;
        Left = right + BitVector.one ty;
        Right = left - BitVector.one ty } |> Interval

  let contains n = function
    | Top _ -> true
    | Empty _ -> false
    | Interval { Type = ty; Left = left; Right = right } ->
      if BitVector.isPositive <| right - left then
        BitVector.isPositive (right - n) && BitVector.isPositive (n - left)
      else BitVector.isPositive (right - n) || BitVector.isPositive (n - left)

  let union r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | Top _, r
    | r, Top _ -> r
    | (Interval r1 as i1), (Interval r2 as i2) ->
      if contains r1.Left i2 && contains r1.Right i2 && contains r2.Left i1 && contains r2.Right i1 then
        if i1 = i2 then i1 else top r1.Type // XXX: Temp Fix
      elif contains r1.Left i2 && contains r1.Right i2 then i2
      elif contains r2.Left i1 && contains r2.Right i1 then i1
      elif contains r1.Right i2 && contains r2.Left i1 then
        cons r1.Type r1.Left r2.Right
      elif contains r1.Left i2 && contains r2.Right i1 then
        cons r1.Type r2.Left r1.Right
      else
        let n1 = numElem r1.Type r1.Right r2.Left
        let n2 = numElem r1.Type r2.Right r1.Left
        if n1 < n2 || (n1 = n2 && BitVector.isPositive (r2.Left - r1.Left)) then
          cons r1.Type r1.Left r2.Right
        else cons r1.Type r2.Left r1.Right

  let intersect r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | Top _, r
    | r, Top _ -> r
    | (Interval r1 as i1), (Interval r2 as i2) ->
      if contains r1.Left i2 && contains r1.Right i2
          && contains r2.Left i1 && contains r2.Right i1 then
        let i1 = cons r1.Type r1.Left r2.Right
        let i2 = cons r1.Type r2.Left r1.Right
        union i1 i2
      elif contains r1.Left i2 && contains r1.Right i2 then i1
      elif contains r2.Left i1 && contains r2.Right i1 then i2
      elif contains r1.Left i2 && contains r2.Right i1
            && not <| contains r1.Right i2 && not <| contains r2.Left i1 then
        cons r1.Type r1.Left r2.Right
      elif contains r1.Right i2 && contains r2.Left i1
            && not <| contains r1.Left i2 && not <| contains r2.Right i1 then
        cons r1.Type r2.Left r1.Right
      else empty r1.Type

  let normalize = function
    | Top _ as r -> r
    | Empty _ as r -> r
    | Interval r ->
      cons r.Type (r.Left - r.Left) (r.Right - r.Left)

  let widen r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | Empty _, i -> i
    | _, (Empty _ as i) -> i
    | Top _, r -> r
    | r, Top _ -> r
    | (Interval r1 as i1), (Interval r2 as i2) ->
      if contains r1.Left i2 && contains r1.Right i2
          && (not <| contains r2.Left i1 || not <| contains r2.Right i1) then
        i2
      elif contains r1.Left i2 && (not <| contains r1.Right i2)
          && (not <| contains r2.Left i1) && contains r2.Right i1 then
        i2
      else intersect i1 i2

  let uNeg = function
    | Top _ as i -> i
    | Empty _ as i -> i
    | Interval { Type = ty; Left = left; Right = right } ->
      cons ty (BitVector.neg right) (BitVector.neg left)

  let uNot = function
    | Top _ as i -> i
    | Empty _ as i -> i
    | Interval ({ Type = ty; Left = left; Right = right } as r) as i ->
      if isConst i then cons ty (~~~ left) (~~~ right) else top ty

  let bAdd r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | (Top _ as i), _
    | _, (Top _ as i) -> i
    | Interval r1, Interval r2 ->
      cons r1.Type (r1.Left + r2.Left) (r1.Right + r2.Right)

  let bSub r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | (Top _ as i), _
    | _, (Top _ as i) -> i
    | (Interval r1 as i1), (Interval r2 as i2) ->
      bAdd i1 <| uNeg i2

  let bMul r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | (Top _ as i), _
    | _, (Top _ as i) -> i
    | (Interval r1 as i1), (Interval r2 as i2) ->
      if isConst i2 then
        cons r1.Type (r1.Left * r2.Left) (r1.Right * r2.Right)
      else failwith "NONO"

  let bDiv r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | (Top _ as i), _
    | _, (Top _ as i) -> i
    | (Interval r1 as i1), (Interval r2 as i2) ->
      if isConst i2 then
        cons r1.Type (r1.Left / r2.Left) (r1.Right / r2.Right)
      else failwith "NONO"

  let bMod r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | (Top _ as i), _
    | _, (Top _ as i) -> i
    | (Interval r1 as i1), (Interval r2 as i2) ->
      if isConst i2 then
        let size =
          BitVector.ofUInt32 (numElem r1.Type r1.Left r1.Right) r1.Type
        if size - r2.Right |> BitVector.isNegative then
          let left = BitVector.modulo r1.Left r2.Left
          let right = BitVector.modulo r1.Right r2.Left
          if BitVector.isNegative (right - left) then
            let left = BitVector.zero r1.Type
            let right = r2.Left - BitVector.one r1.Type
            cons r1.Type left right
          else cons r1.Type left right
        else
          let left = BitVector.zero r1.Type
          let right = r2.Left - BitVector.one r1.Type
          cons r1.Type left right
      else failwith "NONO"

  let bShl r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | (Top _ as i), _
    | _, (Top _ as i) -> i
    | (Interval r1 as i1), (Interval r2 as i2) ->
      if isConst i2 then
        let left = BitVector.shl r1.Left r2.Left
        let right = BitVector.shl r1.Right r2.Right
        cons r1.Type left right
      else failwith "NONO"

  let bShr r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | (Top _ as i), _
    | _, (Top _ as i) -> i
    | (Interval r1 as i1), (Interval r2 as i2) ->
      if isConst i2 then
        let left = BitVector.shr r1.Left r2.Left
        let right = BitVector.shr r1.Right r2.Right
        cons r1.Type left right
      else failwith "NONO"

  let bSar r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | (Top _ as i), _
    | _, (Top _ as i) -> i
    | (Interval r1 as i1), (Interval r2 as i2) ->
      if isConst i2 then
        let left = BitVector.sar r1.Left r2.Left
        let right = BitVector.sar r1.Right r2.Right
        cons r1.Type left right
      else failwith "NONO"

  let bAnd r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | (Top _ as i), _
    | _, (Top _ as i) -> i
    | (Interval r1 as i1), (Interval r2 as i2) ->
      if isConst i1 && isConst i2 then
        cons r1.Type (r1.Left &&& r2.Left) (r1.Right &&& r2.Right)
      else top r1.Type

  let bOr r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | (Top _ as i), _
    | _, (Top _ as i) -> i
    | (Interval r1 as i1), (Interval r2 as i2) ->
      assert (r1.Type = r2.Type)
      if isConst i1 && isConst i2 then
        cons r1.Type (r1.Left ||| r2.Left) (r1.Right ||| r2.Right)
      else top r1.Type

  let bXor r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> i
    | (Top _ as i), _
    | _, (Top _ as i) -> i
    | (Interval r1 as i1), (Interval r2 as i2) ->
      assert (r1.Type = r2.Type)
      if isConst i1 && isConst i2 then
        cons r1.Type (r1.Left ^^^ r2.Left) (r1.Right ^^^ r2.Right)
      else top r1.Type

  let bConcat r1 r2 =
    assert (getType r1 = getType r2)
    let r1t = RegType.toBitWidth <| getType r1
    let r2t = RegType.toBitWidth <| getType r2
    let t = RegType.fromBitWidth (r1t + r2t)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> empty t
    | Top _, _
    | _, Top _
    | _ -> top t

  let extract r size start =
    match r with
    | Top _ -> top <| RegType.fromBitWidth size
    | Empty _ -> empty <| RegType.fromBitWidth size
    | Interval i ->
      let left = BitVector.ofUInt64 ((1UL <<< start) - 1UL) i.Type
      let right = BitVector.ofUInt64 (((1UL <<< size) - 1UL) <<< start) i.Type
      let r = cons i.Type left right
      let ty = RegType.fromBitWidth size
      if size = 1 then top ty
      else
        if contains i.Left r && contains i.Right r then
          let left = BitVector.toUInt64 i.Left
          let left = BitVector.ofUInt64 left ty
          let right = BitVector.toUInt64 i.Right
          let right = BitVector.ofUInt64 right ty
          cons ty left right
        else top <| ty
      (*
      let mask = ((1L <<< size) - 1L) <<< start
      let min = (r.Min &&& mask) >>> start |> toRegular r.Type
      let max = (r.Max &&& mask) >>> start |> toRegular r.Type
      // XXX: Super overapproximate
      //cons r.Type min max
      top <| RegType.fromBitWidth size
      *)

  let rEq r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> f
    | (Top _ as i), _
    | _, (Top _ as i) -> maybe
    | (Interval r1 as i1), (Interval r2 as i2) ->
      if isConst i1 && isConst i2 then
        if r1.Left = r2.Left then t else f
      elif isConst i1 then
        if contains r1.Left i2 then maybe else f
      elif isConst i2 then
        if contains r2.Left i1 then maybe else f
      else
        let r = intersect i1 i2
        if isEmpty r then f elif r = i1 && r = i2 then t else maybe

  let rNeq r1 r2 =
    assert (getType r1 = getType r2)
    match r1, r2 with
    | (Empty _ as i), _
    | _, (Empty _ as i) -> t
    | (Top _ as i), _
    | _, (Top _ as i) -> maybe
    | (Interval r1 as i1), (Interval r2 as i2) ->
      if isConst i1 && isConst i2 then
        if r1.Left <> r2.Left then t else f
      elif isConst i1 then
        if contains r1.Left i2 then maybe else t
      elif isConst i2 then
        if contains r2.Left i1 then maybe else t
      else
        let r = intersect i1 i2
        if isEmpty r then t elif r = i1 && r = i2 then f else maybe

  let rLt r1 r2 =
    assert (getType r1 = getType r2)
    match bSub r1 r2 with
    | Empty _ -> f
    | Top _ -> maybe
    | Interval r1 ->
      if BitVector.isNegative r1.Left && BitVector.isNegative r1.Right then t
      elif not <| BitVector.isNegative r1.Left
            && not <| BitVector.isNegative r1.Right then f
      else maybe

  let cSign ty = function
    | Empty _ -> empty ty
    | Top _ -> top ty
    | Interval r ->
      cons ty (BitVector.sext r.Left ty) (BitVector.sext r.Right ty)

  let cZero ty = function
    | Empty _ -> empty ty
    | Top _ -> top ty
    | Interval r ->
      cons ty (BitVector.zext r.Left ty) (BitVector.zext r.Right ty)

type WExpr =
  | Normal of Expr
  | PhiNum of int []

type Context = {
  Def : Map<Destination, WExpr>
  LastUpdated : Map<string, int>
  MemDef : Dictionary<Addr, Expr>
  VarContext : Map<Destination, Interval>
  MemContext : Dictionary<Addr, Interval>
}

module Context =
  let initContext () =
    let esp =
      RegVar (32<rt>, Intel.Register.ESP |> Intel.Register.toRegID, "ESP", 0)
    let espValue = BitVector.ofInt32 0x1000000 32<rt>
    let espRange = Interval.cons 32<rt> espValue espValue
    let ebp =
      RegVar (32<rt>, Intel.Register.EBP |> Intel.Register.toRegID, "EBP", 0)
    let ebpValue = BitVector.ofInt32 0x1000010 32<rt>
    let ebpRange = Interval.cons 32<rt> ebpValue ebpValue
    let varContext = Map.add esp espRange Map.empty |> Map.add ebp ebpRange
    let lastUpdated = Map.add "ESP" 0 Map.empty |> Map.add "EBP" 0
    { Def = Map.empty ; LastUpdated = lastUpdated ; MemDef = Dictionary () ;
      VarContext = varContext ; MemContext = Dictionary () }

  let addNormalDef dest expr ctxt =
    { ctxt with Def = Map.add dest (Normal expr) ctxt.Def }

  let addPhiDef dest ns ctxt =
    { ctxt with Def = Map.add dest (PhiNum ns) ctxt.Def }

  let updateVar lastUpdated = function
    | RegVar (_, _, s, n) -> Map.add s n lastUpdated
    | PCVar (_, n) -> Map.add "PC" n lastUpdated
    | _ -> lastUpdated

  // Never defined..?
  let isLastVar dest ctxt =
    match dest with
    | RegVar (_, _, s, n) ->
      match Map.tryFind s ctxt.LastUpdated with
      | Some n' -> n = n'
      | None -> false
    | PCVar (_, n) -> Map.find "PC" ctxt.LastUpdated = n
    | _ -> true

  let getLastVar dest ctxt =
    match dest with
    | RegVar (ty, i, s, _) ->
      match Map.tryFind s ctxt.LastUpdated with
      | Some n -> RegVar (ty, i, s, n)
      | None -> RegVar (ty, i, s, 0)
    | PCVar (ty, _) -> PCVar (ty, Map.find "PC" ctxt.LastUpdated)
    | _ -> failwith "No"

  let addVarRange dest range ctxt =
    { ctxt with
        VarContext = Map.add dest range ctxt.VarContext
        LastUpdated = updateVar ctxt.LastUpdated dest }

  let findVarRange ty dest ctxt =
    match Map.tryFind dest ctxt.VarContext with
    | Some range -> range, ctxt
    | None ->
      let range = Interval.top ty
      let ctxt = { ctxt with VarContext = Map.add dest range ctxt.VarContext }
      range, ctxt

  let tryFindMemDef addr ctxt =
    let memDef = ctxt.MemDef
    if memDef.ContainsKey addr then Some memDef.[addr] else None

  let addMemRange addr expr range ctxt =
    let mem = ctxt.MemContext
    if mem.ContainsKey addr then
      let memRange = mem.[addr]
      let range =
        if Interval.getType memRange > Interval.getType range then
          Interval.cZero (Interval.getType memRange) range
        else range
      mem.[addr] <- range
    else mem.[addr] <- range
    ctxt.MemDef.[addr] <- expr
    //printfn "Result: %x <- %A" addr range
    ctxt

  let widenMemRange addr range ctxt =
    let mem = ctxt.MemContext
    if mem.ContainsKey addr then
      let memRange = mem.[addr]
      let range =
        if Interval.getType memRange > Interval.getType range then
          Interval.cZero (Interval.getType memRange) range
        else range
      mem.[addr] <- Interval.widen memRange range
    else mem.[addr] <- range
    //printfn "Result: %x <- %A" addr range
    ctxt

  let findMemRange ty addr ctxt =
    let mem = ctxt.MemContext
    /// XXX: Should make this more good..
    if mem.ContainsKey addr then
      match mem.[addr] with
      | Top t
      | Empty t
      | Interval { Type = t } as i ->
        if t = ty then i
        elif ty < t then Interval.extract i (RegType.toBitWidth ty) 0
        else Interval.cZero ty i
    else Interval.top ty

let interpRangeDest ctxt = function
  | MemVar _ -> failwith "NOOO"
  | RegVar (ty, _, _, _) as dest ->
    Context.findVarRange ty dest ctxt
  | TempVar (ty, _) as dest ->
    Context.findVarRange ty dest ctxt
  | PCVar (ty, _) as dest ->
    Context.findVarRange ty dest ctxt

let interpRangeReturn ctxt = function
  | MemVar _ -> Interval.top 32<rt>, ctxt
  | RegVar (ty, _, _, _) -> Interval.top ty, ctxt
  | TempVar (ty, _) -> Interval.top ty, ctxt
  | _ -> failwith "TODO"

let isESP = function
  | RegVar (_, _, "ESP", _) -> true
  | _ -> false

let getDestType = function
  | RegVar (ty, _, _, _)
  | PCVar (ty, _)
  | TempVar (ty, _) -> ty
  | _ -> failwith "No"

let genDef n = function
  | RegVar (ty, r, s, _) -> RegVar (ty, r, s, n)
  | PCVar (ty, _) -> PCVar (ty, n)
  | TempVar (ty, _) -> TempVar (ty, n)
  | MemVar _ -> MemVar n

let rec stConc ctxt = function
  | Num _ as expr -> expr
  | Var dest as expr ->
    let range, _ = interpRangeDest ctxt dest
    if Interval.isConst range then Num (Interval.getLeft range) else expr
  | Load _ as expr -> expr
  | Store _ as expr -> expr
  | FuncName _ -> failwith "No"
  | UnOp (op, expr) ->
    let expr = stConc ctxt expr
    UnOp (op, expr)
  | BinOp (op, ty, expr1, expr2) ->
    let expr1 = stConc ctxt expr1
    let expr2 = stConc ctxt expr2
    BinOp (op, ty, expr1, expr2)
  | RelOp (op, expr1, expr2) ->
    let expr1 = stConc ctxt expr1
    let expr2 = stConc ctxt expr2
    RelOp (op, expr1, expr2)
  | Ite (expr1, expr2, expr3) ->
    let expr1 = stConc ctxt expr1
    let expr2 = stConc ctxt expr2
    let expr3 = stConc ctxt expr3
    Ite (expr1, expr2, expr3)
  | Cast (op, ty, expr) ->
    let expr = stConc ctxt expr
    Cast (op, ty, expr)
  | Extract (expr, ty, pos) ->
    let expr = stConc ctxt expr
    Extract (expr, ty, pos)
  | Undefined _ as expr -> expr
  | Return _ as expr -> expr

let rec getHash = function
  | Num bv -> BitVector.toUInt64 bv
  | Var dest -> getHashDest dest
  | Load _ -> failwith "No"
  | Store _ -> failwith "No"
  | FuncName _ -> failwith "No"
  | UnOp (op, expr) ->
    failwith "No"
    let expr = getHash expr
    getHashUnOp op expr
  | BinOp (op, _, expr1, expr2) ->
    let expr1 = getHash expr1
    let expr2 = getHash expr2
    getHashBinOp op expr1 expr2
  | RelOp (op, expr1, expr2) ->
    failwith "No"
    let expr1 = getHash expr1
    let expr2 = getHash expr2
    getHashRelOp op expr1 expr2
  | Ite _ -> failwith "No"
  | Cast _ -> failwith "No"
  | Extract _ -> failwith "No"
  | Undefined _ -> failwith "No"
  | Return _ -> failwith "No"

and getHashDest = function
  | RegVar (_, n, _, _) -> 0x100000000UL * (uint64 n)
  | _ -> 0UL

and getHashUnOp op expr =
  match op with
  | _ -> failwith "No"

and getHashBinOp op expr1 expr2 =
  match op with
  | BinOpType.ADD -> expr1 + expr2
  | BinOpType.SUB -> expr1 - expr2
  | BinOpType.MUL -> expr1 * expr2
  | _ -> failwith "No"

and getHashRelOp op expr1 expr2 =
  match op with
  | _ -> failwith "No"

let rec interpRangeExpr (builder: CFGBuilder) ctxt loc dest = function
  | Num bv ->
    Interval.cons (BitVector.getType bv) bv bv, ctxt
  | Var dest -> interpRangeDest ctxt dest
  | Load (_, ty, addr) as expr ->
    interpRangeLoad builder ctxt loc dest ty addr expr
  | Store (src, addr, expr) ->
    interpRangeStore builder ctxt loc dest src addr expr
  | FuncName _ -> failwith "No"
  | UnOp (op, expr) -> interpRangeUnOp builder ctxt loc dest op expr
  | BinOp (op, ty, expr1, expr2) ->
    interpRangeBinOp builder ctxt loc dest op ty expr1 expr2
  | RelOp (op, expr1, expr2) ->
    interpRangeRelOp builder ctxt loc dest op expr1 expr2
  | Ite (expr1, expr2, expr3) ->
    interpRangeIte builder ctxt loc dest expr1 expr2 expr3
  | Cast (op, ty, expr) ->
    interpRangeCast builder ctxt loc dest op ty expr
  | Extract (expr, ty, pos) ->
    let range, ctxt = interpRangeExpr builder ctxt loc dest expr
    let range = Interval.extract range (RegType.toBitWidth ty) pos
    range, ctxt
  | Undefined (ty, _) -> Interval.top ty, ctxt
  | Return name ->
    if isESP dest then
      let ty = getDestType dest
      let range, ctxt =
        Context.findVarRange ty (Context.getLastVar dest ctxt) ctxt
      let bv = BitVector.ofUInt64 4UL ty
      (Interval.bAdd range (Interval.cons ty bv bv)), ctxt
    elif name.StartsWith "__x86.get_pc_thunk" then
      let instr = builder.GetInstr loc
      let next = BitVector.ofUInt64 (instr.Address + uint64 instr.Length) 32<rt>
      let range = Interval.cons 32<rt> next next
      range, ctxt
    else interpRangeReturn ctxt dest

and interpRangeLoad builder ctxt loc dest ty addr expr =
  let range, ctxt = interpRangeExpr builder ctxt loc dest addr
  if Interval.isConst range then
    Context.findMemRange ty (Interval.getUMin range |> BitVector.toUInt64) ctxt, ctxt
  else
    let conc = stConc ctxt addr
    let addr = stConc ctxt addr |> getHash
    Context.findMemRange ty addr ctxt, ctxt

and interpRangeUnOp builder ctxt loc dest op expr =
  let range, ctxt = interpRangeExpr builder ctxt loc dest expr
  match op with
  | UnOpType.NEG ->
    Interval.uNeg range, ctxt
  | UnOpType.NOT ->
    Interval.uNot range, ctxt
  | op -> failwith "No"

and interpRangeBinOp builder ctxt loc dest op ty expr1 expr2 =
  let range1, ctxt = interpRangeExpr builder ctxt loc dest expr1
  let range2, ctxt = interpRangeExpr builder ctxt loc dest expr2
  match op with
  | BinOpType.ADD ->
    Interval.bAdd range1 range2, ctxt
  | BinOpType.SUB ->
    Interval.bSub range1 range2, ctxt
  | BinOpType.MUL ->
    Interval.bMul range1 range2, ctxt
  | BinOpType.DIV ->
    Interval.bDiv range1 range2, ctxt
  | BinOpType.MOD ->
    Interval.bMod range1 range2, ctxt
  | BinOpType.SHL ->
    Interval.bShl range1 range2, ctxt
  | BinOpType.SHR ->
    Interval.bShr range1 range2, ctxt
  | BinOpType.SAR ->
    Interval.bSar range1 range2, ctxt
  | BinOpType.AND ->
    Interval.bAnd range1 range2, ctxt
  | BinOpType.OR ->
    Interval.bOr range1 range2, ctxt
  | BinOpType.XOR ->
    Interval.bXor range1 range2, ctxt
  | BinOpType.CONCAT ->
    Interval.bConcat range1 range2, ctxt
  | _ -> printfn "%x %A" loc op; failwith "Not Implemented"

and interpRangeRelOp builder ctxt loc dest op expr1 expr2 =
  let range1, ctxt = interpRangeExpr builder ctxt loc dest expr1
  let range2, ctxt = interpRangeExpr builder ctxt loc dest expr2
  match op with
  | RelOpType.EQ ->
    Interval.rEq range1 range2, ctxt
  | RelOpType.NEQ ->
    Interval.rNeq range1 range2, ctxt
  | RelOpType.LT ->
    Interval.rLt range1 range2, ctxt
  | _ -> printfn "%A" op; failwith "Not Implemented"

and interpRangeIte builder ctxt loc dest expr1 expr2 expr3 =
  let range1, ctxt = interpRangeExpr builder ctxt loc dest expr1
  let range2, ctxt = interpRangeExpr builder ctxt loc dest expr2
  let range3, ctxt = interpRangeExpr builder ctxt loc dest expr3
  if range1 = Interval.t then range2, ctxt
  elif range2 = Interval.f then range3, ctxt
  else Interval.union range2 range3, ctxt

and interpRangeStore builder ctxt loc dest src addr expr =
  let addrRange, ctxt = interpRangeExpr builder ctxt loc dest addr
  let exprRange, ctxt = interpRangeExpr builder ctxt loc dest expr
  match src, dest with
  | MemVar src, MemVar dst ->
    if Interval.isConst addrRange then
      let ctxt =
        Context.addMemRange (Interval.getUMin addrRange |> BitVector.toUInt64) expr exprRange ctxt
      exprRange, ctxt
    else
      let conc = stConc ctxt addr
      let addr = stConc ctxt addr |> getHash
      let ctxt = Context.addMemRange addr expr exprRange ctxt
      exprRange, ctxt
  | _ -> failwith "No"

and interpRangeCast builder ctxt loc dest op ty expr =
  let range, ctxt = interpRangeExpr builder ctxt loc dest expr
  match op with
  | CastKind.SignExt ->
    Interval.cSign ty range, ctxt
  | CastKind.ZeroExt ->
    Interval.cZero ty range, ctxt
  | _ -> failwith "No"

let isMemVar = function
  | MemVar _ -> true
  | _ -> false

let isReturn (ctxt: Context) def =
  match Map.tryFind def ctxt.Def with
  | Some (Normal (Return _)) -> true
  | _ -> false

let interpPhi ctxt (v: SSAVertex) dest ns =
  let ctxt = Context.addPhiDef dest ns ctxt
  if isMemVar dest then ctxt
  else
    let defs = List.map (fun n -> genDef n dest) <| Array.toList ns
    let defs = List.filter (fun dest -> Context.isLastVar dest ctxt) defs
    let def =
      if List.length defs = 1 then List.head defs
      else Context.getLastVar dest ctxt
    let range, ctxt = interpRangeDest ctxt def
    //printfn "Result: %A <- %A" dest range
    Context.addVarRange dest range ctxt

let rec releaseWExpr ctxt dest = function
  | Normal expr -> releaseExpr ctxt expr
  | PhiNum ns ->
    let defs = List.map (fun n -> genDef n dest) <| Array.toList ns
    let defs = List.filter (fun def -> Map.containsKey def ctxt.Def) defs
    let def = List.head defs
    releaseWExpr ctxt dest <| (Map.find def ctxt.Def)

and releaseExpr ctxt = function
  | Num _ as expr -> expr
  | Var (TempVar _ as dest) -> releaseWExpr ctxt dest <| Map.find dest ctxt.Def
  | Var _ as expr -> expr
  | Load (dest, ty, addr) -> Load (dest, ty, releaseExpr ctxt addr)
  | Store (dest, addr, expr) ->
    Store (dest, releaseExpr ctxt addr, releaseExpr ctxt expr)
  | FuncName _ as expr -> expr
  | UnOp (op, expr) -> UnOp (op, releaseExpr ctxt expr)
  | BinOp (op, ty, expr1, expr2) ->
    BinOp (op, ty, releaseExpr ctxt expr1, releaseExpr ctxt expr2)
  | RelOp (op, expr1, expr2) ->
    RelOp (op, releaseExpr ctxt expr1, releaseExpr ctxt expr2)
  | Ite (expr1, expr2, expr3) ->
    Ite (releaseExpr ctxt expr1, releaseExpr ctxt expr2, releaseExpr ctxt expr3)
  | Cast (op, ty, expr) -> Cast (op, ty, releaseExpr ctxt expr)
  | Extract (expr, ty, pos) -> Extract (releaseExpr ctxt expr, ty, pos)
  | Undefined _ as expr -> expr
  | Return _ as expr -> expr

let rec getExprType = function
  | Num bv -> BitVector.getType bv
  | Var (dest) -> getDestType dest
  | Load (_, ty, _) -> ty
  | Store _ -> failwith "No"
  | FuncName _ -> failwith "No"
  | UnOp (_, expr) -> getExprType expr
  | BinOp (_, ty, _, _) -> ty
  | RelOp (_, expr, _) -> getExprType expr
  | Ite (_, expr, _) -> getExprType expr
  | Cast (_, ty, _) -> ty
  | Extract (_, ty, _) -> ty
  | Undefined (ty, _) -> ty
  | Return _ -> failwith "No"

let inferOperandZF ctxt isPos dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | RelOp (RelOpType.EQ, Var dest, Num bv) ->
    let ty = BitVector.getType bv
    let range = Interval.cons ty bv bv
    let range = if isPos then range else Interval.complement range
    Some (Var dest, range)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.ADD, ty, Var _, Load _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.ADD, ty, Var _, Var _), Num _) ->
    None
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, arg1, Num bv), Num _) ->
    let range = Interval.cons ty bv bv
    let range = if isPos then range else Interval.complement range
    Some (arg1, range)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, _, Num _, arg1), Num _) ->
    failwith "XXX"
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, _, arg1, arg2), Num _) ->
    None
  | RelOp (RelOpType.EQ, BinOp (BinOpType.AND, ty, arg1, arg2), Num _) ->
    if arg1 = arg2 then
      let range = Interval.cons ty (BitVector.zero ty) (BitVector.zero ty)
      let range = if isPos then range else Interval.complement range
      Some (arg1, range)
    else None
  | RelOp (RelOpType.EQ, BinOp (BinOpType.OR, _, arg1, arg2), Num _) ->
    if arg1 = arg2 then failwith "XXX"
    else None
  | RelOp (RelOpType.EQ, BinOp (BinOpType.XOR, _, Num _, arg1), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.XOR, _, arg1, Num _), Num _) ->
    failwith "XXX"
  | RelOp (RelOpType.EQ, BinOp (BinOpType.XOR, _, arg1, arg2), Num _) ->
    if arg1 = arg2 then
      let ty = getExprType arg1
      let range = Interval.cons ty (BitVector.zero ty) (BitVector.zero ty)
      let range = if isPos then range else Interval.complement range
      Some (arg1, range)
    else None
  | _ -> printfn "%A" expr; failwith "Not Implemented Yet"

let inferOperandSF ctxt isPos dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | Extract (BinOp (BinOpType.SUB, ty, arg1, Num bv), 1<rt>, 31) ->
    let range = Interval.cons ty (BitVector.signedMin ty) bv
    let range = if isPos then range else Interval.complement range
    Some (arg1, range)
  | Extract (BinOp (BinOpType.AND, ty, Var dest1, Var dest2), 1<rt>, 31) ->
    if dest1 = dest2 then
      let range = Interval.cons ty (BitVector.zero ty) (BitVector.signedMax ty)
      let range = if isPos then Interval.complement range else range
      Some (Var dest1, range)
    else failwith "TODO"
  | _ -> printfn "%A" expr; failwith "Not Implemented Yet"

let inferOperandCF ctxt isPos dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | RelOp (RelOpType.LT, arg1, Num bv) ->
    let ty = BitVector.getType bv
    let range =
      Interval.cons ty (BitVector.signedMin ty) (bv - BitVector.one ty)
    let range = if isPos then range else Interval.complement range
    Some (arg1, range)
  | RelOp (RelOpType.LT, Num _, arg1) ->
    failwith "XXX"
  | RelOp (RelOpType.LT, arg1, arg2) -> None
  | Extract (BinOp _, _, _) -> None
  | _ -> printfn "%A" expr; failwith "Not Implemented Yet"

let type1 ctxt = function
  | RegVar (_, _, "ZF", _) as dest ->
    inferOperandZF ctxt true dest
  | RegVar (_, _, "SF", _) as dest ->
    inferOperandSF ctxt true dest
  | RegVar (_, _, "CF", _) as dest ->
    inferOperandCF ctxt true dest
  | RegVar (_, _, "OF", _) as dest ->
    None // XXX
  | RegVar (_, _, "PF", _) as dest ->
    None // XXX
  | expr -> printfn "%A" expr; failwith "No"

let type2 ctxt = function
  | RegVar (_, _, "ZF", _) as dest ->
    inferOperandZF ctxt false dest
  | RegVar (_, _, "SF", _) as dest ->
    inferOperandSF ctxt false dest
  | RegVar (_, _, "CF", _) as dest ->
    inferOperandCF ctxt false dest
  | RegVar (_, _, "OF", _) as dest ->
    None // XXX
  | expr -> printfn "%A" expr; failwith "No"

let type3Aux ctxt dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, arg1, Num bv), Num _) ->
    let range = Interval.cons ty (BitVector.zero ty) bv
    Some (arg1, range)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Load _, Var _), Num _) ->
    None
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Load _), Num _) ->
    None
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Var _), Num _) ->
    None
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Extract _, Load _), Num _) ->
    None
  | _ -> printfn "%A" expr; failwith "Not Implemented Yet"

let type3 ctxt = function
  | RegVar (_, _, "CF", _), (RegVar (_, _, "ZF", _) as dest)
  | (RegVar (_, _, "ZF", _) as dest), RegVar (_, _, "CF", _) ->
    type3Aux ctxt dest
  | _ -> failwith "No"

let type4Aux ctxt dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | RelOp (RelOpType.EQ, BinOp (BinOpType.ADD, ty, arg1, Num bv), Num _) ->
    None
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, arg1, Num bv), Num _) ->
    let range = Interval.cons ty (BitVector.one ty + bv) (BitVector.unsignedMax ty)
    Some (arg1, range)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Var _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Load _, Var _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Load _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Extract _, Extract _), Num _) ->
    None
  | _ -> printfn "%A" expr; failwith "Not Implemented Yet"

let type4 ctxt = function
  | RegVar (_, _, "CF", _), (RegVar (_, _, "ZF", _) as dest)
  | (RegVar (_, _, "ZF", _) as dest), RegVar (_, _, "CF", _) ->
    type4Aux ctxt dest
  | _ -> failwith "No"

let type5Aux ctxt dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, arg1, Num bv), Num _) ->
    let range = Interval.cons ty (BitVector.signedMin ty) bv
    Some (arg1, range)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Var _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Load _, Var _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Load _), Num _) ->
    None
  | RelOp (RelOpType.EQ, BinOp (BinOpType.AND, ty, Var dest1, Var dest2), Num _) ->
    if dest1 = dest2 then
      let range = Interval.cons ty (BitVector.signedMin ty) (BitVector.zero ty)
      Some (Var dest1, range)
    else None
  | Extract (BinOp (BinOpType.SUB, _, Var _, Load _), _, _) -> None
  | _ -> printfn "%A" expr; failwith "Not Implemented Yet"

let type5 ctxt = function
  | RegVar (_, _, "ZF", _) as dest, RegVar _, RegVar _ ->
    type5Aux ctxt dest
  | _ -> failwith "No"

let type6Aux ctxt dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, arg1, Num bv), Num _) ->
    let range = Interval.cons ty (BitVector.one ty + bv) (BitVector.signedMax ty)
    Some (arg1, range)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Var _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Load _, Var _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Load _), Num _) ->
    None
  | RelOp (RelOpType.EQ, BinOp (BinOpType.AND, ty, Var dest1, Var dest2), Num _) ->
    if dest1 = dest2 then
      let range = Interval.cons ty (BitVector.one ty) (BitVector.signedMax ty)
      Some (Var dest1, range)
    else None
  | _ -> printfn "%A" expr; failwith "Not Implemented Yet"

let type6 ctxt = function
  | RegVar (_, _, "ZF", _) as dest, RegVar _, RegVar _ ->
    type6Aux ctxt dest
  | _ -> failwith "No"

let type7Aux ctxt dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | Extract (BinOp (BinOpType.SUB, _, Var _, Load _), _, _)
  | Extract (BinOp (BinOpType.SUB, _, Load _, Var _), _, _) -> None
  | _ -> printfn "%A" expr; failwith "Not Implemented Yet"

let type7 ctxt = function
  | RegVar (_, _, "SF", _) as dest, RegVar _ ->
    type7Aux ctxt dest
  | _ -> failwith "No"

let type8Aux ctxt dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | Extract (BinOp (BinOpType.SUB, _, Load _, Var _), _, _)
  | Extract (BinOp (BinOpType.SUB, _, Var _, Load _), _, _) -> None
  | Extract (BinOp (BinOpType.SUB, _, Var dest1, Var dest2), _, _) ->
    if dest1 = dest2 then failwith "Not Implemented Yet" else None
  | _ -> printfn "%A" expr; failwith "Not Implemented Yet"

let type8 ctxt = function
  | RegVar (_, _, "SF", _) as dest, RegVar _ ->
    type8Aux ctxt dest
  | _ -> failwith "No"

let inferCondKind ctxt = function
  // pattern1 , ZF, SF, CF
  | Var (dest) -> type1 ctxt dest
  // pattern2 , not ZF, not SF, not CF
  | RelOp (RelOpType.EQ, Var (dest), Num _) -> type2 ctxt dest
  // pattern3 , CF or ZF
  | BinOp (BinOpType.OR, 1<rt>, Var (dest1), Var (dest2)) ->
    type3 ctxt (dest1, dest2)
  // pattern 4 , not (CF or ZF)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.OR, 1<rt>, Var (dest1), Var (dest2)), Num _) ->
    type4 ctxt (dest1, dest2)
  // pattern 5 , ZF or (SF != OF)
  | BinOp (BinOpType.OR, 1<rt>, Var (dest1), RelOp (RelOpType.NEQ, Var (dest2), Var (dest3))) ->
    type5 ctxt (dest1, dest2, dest3)
  // pattern 6 , not (ZF or (SF != OF))
  | BinOp (BinOpType.AND, 1<rt>, RelOp (RelOpType.EQ, Var (dest1), Num _), RelOp (RelOpType.EQ, Var (dest2), Var (dest3))) ->
    type6 ctxt (dest1, dest2, dest3)
  // pattern 7 , SF = OF
  | RelOp (RelOpType.EQ, Var (dest1), Var (dest2)) ->
    type7 ctxt (dest1, dest2)
  // pattern 8 , SF <> OF
  | RelOp (RelOpType.NEQ, Var (dest1), Var (dest2)) ->
    type8 ctxt (dest1, dest2)
  | cond -> printfn "%A" cond; failwith "No"

let interpCond (builder: CFGBuilder) ctxt addr cond =
  let instr = builder.GetInstr addr
  if not <| instr.IsBranch () then failwith "NONONONO"
  inferCondKind ctxt cond

let interpStmt builder v (ctxt, addr, cond) = function
  | LMark (addr, ("AddrMark", 0)) -> ctxt, addr, None
  | LMark _ -> ctxt, addr, None
  | Def ((MemVar _ as dest), (Store _ as expr)) as stmt ->
    //printfn "Stmt: %A" stmt
    let ctxt = Context.addNormalDef dest expr ctxt
    let range, ctxt = interpRangeExpr builder ctxt addr dest expr
    ctxt, addr, None
  | Def (MemVar _, _) -> ctxt, addr, None
  | Def (dest, expr) as stmt ->
    let ctxt = Context.addNormalDef dest expr ctxt
    //printfn "Stmt: %A" stmt
    let range, ctxt = interpRangeExpr builder ctxt addr dest expr
    //printfn "Result: %A <- %A" dest range
    Context.addVarRange dest range ctxt, addr, None
  | Phi (dest, ns) as stmt ->
    //printfn "Stmt: %A" stmt
    let ctxt = Context.addPhiDef dest ns ctxt
    interpPhi ctxt v dest ns, addr, None
  | Jmp (IntraCJmp (cond, _, _)) ->
    ctxt, addr, None // XXX: FIX
  | Jmp (InterCJmp (cond, _, _, _)) as stmt ->
    //printfn "Stmt: %A" stmt
    let cond = interpCond builder ctxt addr cond
    //printfn "Cond: %A" cond
    ctxt, addr, cond // XXX: Fix
  | Jmp _ -> ctxt, addr, None
  | SideEffect _ -> ctxt, addr, None

let interpStmts builder ctxt addr v stmts =
  List.fold (interpStmt builder v) (ctxt, addr, None) stmts

let interpCallPhi (builder: CFGBuilder) (ctxt, addr) = function
  | Def (dest, (Return name as expr)) as stmt ->
    //printfn "Stmt: %A" stmt
    let ctxt = Context.addNormalDef dest expr ctxt
    if isMemVar dest then ctxt, addr
    elif isESP dest then
      let ty = getDestType dest
      let range, ctxt =
        Context.findVarRange ty (Context.getLastVar dest ctxt) ctxt
      let bv = BitVector.ofUInt64 4UL ty
      let range = Interval.bAdd range (Interval.cons ty bv bv)
      //printfn "Result: %A <- %A" dest range
      Context.addVarRange dest range ctxt, addr
    elif name.StartsWith "__x86.get_pc_thunk" then
      let instr = builder.GetInstr addr
      let next = BitVector.ofUInt64 (instr.Address + uint64 instr.Length) 32<rt>
      let range = Interval.cons 32<rt> next next
      //printfn "Result: %A <- %A" dest range
      Context.addVarRange dest range ctxt, addr
    else
      let range, ctxt = interpRangeReturn ctxt dest
      //printfn "Result: %A <- %A" dest range
      Context.addVarRange dest range ctxt, addr
  | Phi (dest, ns) as stmt ->
    //printfn "Stmt: %A" stmt
    let ctxt = Context.addPhiDef dest ns ctxt
    if isMemVar dest then ctxt, addr
    else
      let defs = List.map (fun n -> genDef n dest) <| Array.toList ns
      let defs = List.filter (fun dest -> Context.isLastVar dest ctxt) defs
      //let def = List.head defs // XXX
      let def =
        if List.length defs = 1 then List.head defs
        else Context.getLastVar dest ctxt
      let range, ctxt = interpRangeDest ctxt def
      //printfn "Result: %A <- %A" dest range
      Context.addVarRange dest range ctxt, addr
  | stmt -> printfn "%A" stmt; failwith "No"

let interpCall builder (ctxt, addr) stmts =
  List.fold (interpCallPhi builder) (ctxt, addr) stmts

let rec hasVar dest = function
  | Num _ -> false
  | Var dest_ -> dest = dest_
  | Load _ -> false
  | Store _ -> false
  | FuncName _ -> false
  | UnOp (_, expr) -> hasVar dest expr
  | BinOp (_, _, expr1, expr2) -> hasVar dest expr1 || hasVar dest expr2
  | RelOp (_, expr1, expr2) -> hasVar dest expr1 || hasVar dest expr2
  | Ite (expr1, expr2, expr3) ->
    hasVar dest expr1 || hasVar dest expr2 || hasVar dest expr3
  | Cast (_, _, expr) -> hasVar dest expr
  | Extract (expr, _, _) -> hasVar dest expr
  | Undefined _ -> false
  | Return _ -> false

let updateAlias builder dest ctxt =
  let varContext =
    ctxt.VarContext
    |> Map.map (fun def interval ->
        match Map.tryFind def ctxt.Def with
        | Some (Normal expr) ->
          if hasVar dest expr then
            let range, _ =
              interpRangeExpr builder ctxt 0UL (PCVar (32<rt>, 0)) expr
            range
          else interval
        | Some _ -> interval
        | None -> interval)
  { ctxt with VarContext = varContext }

let applyCond builder cond ctxt =
  match cond with
  | None -> ctxt
  | Some (Var dest, range) ->
    Context.addVarRange dest range ctxt
    |> updateAlias builder dest
  | Some (Extract (Var dest, size, pos), range) ->
    (*
    let size = RegType.toBitWidth size
    let mask = BitVector.ofUInt64 (((1UL <<< (32 - pos - size)) - 1UL) <<< (pos + size)) 32<rt>
    let r, _ = interpRangeDest ctxt dest
    let left = (Interval.getLeft r &&& mask) ||| Interval.getLeft range
    let right = (Interval.getRight r &&& mask) ||| Interval.getRight range
    let range = Interval.cons (Interval.getType r) left right
    let range = Interval.intersect r range
    Context.addVarRange dest range ctxt // FIXME
    *)
    if pos = 0 then
      let ty = Interval.getType <| fst (interpRangeDest ctxt dest)
      let range = Interval.cZero ty range
      Context.addVarRange dest range ctxt
      |> updateAlias builder dest
    else failwith "Reallly?"
  | Some (Load (_, _, expr), range) ->
    let addr, _ = interpRangeExpr builder ctxt 0UL (PCVar (32<rt>, 0)) expr
    if not <| Interval.isConst addr then
      let conc = stConc ctxt expr |> getHash
      let ctxt = Context.widenMemRange conc range ctxt
      ctxt
    else Context.widenMemRange (Interval.getLeft addr |> BitVector.toUInt64) range ctxt
  | Some (expr, _) -> printfn "%A" expr; failwith "No"

let checkTarget (cfg: SSACFG) visited (v: SSAVertex) =
  v.Preds |> List.filter (fun v' ->
    match cfg.FindEdge v' v with
    | JmpEdge | CJmpTrueEdge | CJmpFalseEdge | FallThroughEdge -> true
    | _ -> false)
  |> List.forall (fun v' -> Set.contains v' visited)

let rec intervalAnalysis builder (cfg: SSACFG) ctxt addr condMap = function
  | [] -> ctxt
  | (v: SSAVertex) :: vs ->
    let cond = Map.find v condMap
    let ctxt = applyCond builder cond ctxt
    let ctxt, addr, cond =
      interpStmts builder ctxt addr v <| v.VData.GetStmts ()
    let ctxt, addr =
      List.fold (fun (ctxt, addr) v' ->
        match cfg.FindEdge v v' with
        | CallEdge ->
          let ctxt, addr =
            interpCall builder (ctxt, addr) <| v'.VData.GetStmts ()
          ctxt, addr
        | _ -> ctxt, addr) (ctxt, addr) v.Succs
    //printfn "Addr: %x" addr
    let tmpDest = PCVar (32<rt>, 0)
    let condMap =
      if List.length vs = 0 then condMap
      else
        let v' = List.head vs
        match cfg.FindEdge v v', cond with
        | CJmpTrueEdge, Some (dest, cond) ->
          let range, ctxt = interpRangeExpr builder ctxt addr tmpDest dest
          //Map.add v' (Some (dest, Interval.widen range cond)) condMap
          Map.add v' (Some (dest, cond)) condMap
        | CJmpFalseEdge, Some (dest, cond) ->
          let ccond = Interval.complement cond
          let range, ctxt = interpRangeExpr builder ctxt addr tmpDest dest
          //Map.add v' (Some (dest, Interval.widen range ccond)) condMap
          Map.add v' (Some (dest, ccond)) condMap
        | _ -> condMap
    intervalAnalysis builder cfg ctxt addr condMap vs

let rec unfoldWExpr ctxt dest = function
  | Normal expr -> unfoldExpr ctxt expr
  | PhiNum ns ->
    Array.map (fun n -> genDef n dest) ns
    |> Array.pick (fun def -> Map.tryFind def ctxt.Def)
    |> unfoldWExpr ctxt dest

and unfoldExpr ctxt = function
  | Num _ as expr -> expr
  | Var dest -> unfoldWExpr ctxt dest <| Map.find dest ctxt.Def
  | Load _ as expr -> expr
  | UnOp (op, expr) -> UnOp (op, unfoldExpr ctxt expr)
  | BinOp (op, ty, expr1, expr2) ->
    BinOp (op, ty, unfoldExpr ctxt expr1, unfoldExpr ctxt expr2)
  | RelOp (op, expr1, expr2) ->
    RelOp (op, unfoldExpr ctxt expr1, unfoldExpr ctxt expr2)
  | Ite (expr1, expr2, expr3) ->
    Ite (unfoldExpr ctxt expr1, unfoldExpr ctxt expr2, unfoldExpr ctxt expr3)
  | Cast (op, ty, expr) -> Cast (op, ty, unfoldExpr ctxt expr)
  | Extract (expr, ty, pos) -> Extract (unfoldExpr ctxt expr, ty, pos)
  | Return _ as expr -> expr
  | expr -> printfn "%A" expr; failwith "No"

let getAddr = function
  | BinOp (_, _, Load (_, _, expr), _) -> expr
  | BinOp (_, _, _, Load (_, _, expr)) -> expr
  | Load (_, _, expr) -> expr
  | expr -> printfn "%A" expr; failwith "No"

let rec getWAddrs acc ctxt dest = function
  | Normal expr -> getAddrs acc ctxt expr
  | PhiNum ns ->
    Array.map (fun n -> genDef n dest) ns
    |> Array.filter (fun d -> d <> dest)
    |> Array.pick (fun def -> Map.tryFind def ctxt.Def)
    |> getWAddrs acc ctxt dest

and getAddrs acc ctxt = function
  | Num _ -> acc
  | Var dest ->
    if Map.containsKey dest ctxt.Def then
      getWAddrs acc ctxt dest <| Map.find dest ctxt.Def
    else acc
  | Load (_, _, expr) -> expr :: acc
  | UnOp (op, expr) -> getAddrs acc ctxt expr
  | BinOp (op, ty, expr1, expr2) ->
    let acc = getAddrs acc ctxt expr1
    getAddrs acc ctxt expr2
  | RelOp (op, expr1, expr2) ->
    let acc = getAddrs acc ctxt expr1
    getAddrs acc ctxt expr2
  | Ite (expr1, expr2, expr3) ->
    let acc = getAddrs acc ctxt expr1
    let acc = getAddrs acc ctxt expr2
    getAddrs acc ctxt expr3
  | Cast (op, ty, expr) -> getAddrs acc ctxt expr
  | Extract (expr, ty, pos) -> getAddrs acc ctxt expr
  | Return _ -> acc
  | expr -> printfn "%A" expr; failwith "No"

let rec unfoldWAddr ctxt dest = function
  | Normal (BinOp (BinOpType.MUL, ty, expr1, Num bv) as expr) ->
    let bv_ = BitVector.ofUInt64 4UL ty
    if bv = bv_ then expr else Var dest
  | Normal (BinOp (BinOpType.SHL, ty, expr1, Num bv) as expr) ->
    let bv_ = BitVector.ofUInt64 2UL ty
    if bv = bv_ then expr else Var dest
  | Normal expr -> Var dest
  | PhiNum ns ->
    Array.map (fun n -> genDef n dest) ns
    |> Array.pick (fun def -> Map.tryFind def ctxt.Def)
    |> unfoldWAddr ctxt dest

and unfoldAddr ctxt = function
  | Num _ as expr -> expr
  | Var dest ->
    if Map.containsKey dest ctxt.Def then
      unfoldWAddr ctxt dest <| Map.find dest ctxt.Def
    else Var dest
  | Load _ as expr -> expr
  | UnOp (op, expr) -> UnOp (op, unfoldAddr ctxt expr)
  | BinOp (op, ty, expr1, expr2) ->
    BinOp (op, ty, unfoldAddr ctxt expr1, unfoldAddr ctxt expr2)
  | RelOp (op, expr1, expr2) ->
    RelOp (op, unfoldAddr ctxt expr1, unfoldAddr ctxt expr2)
  | Ite (expr1, expr2, expr3) ->
    Ite (unfoldAddr ctxt expr1, unfoldAddr ctxt expr2, unfoldAddr ctxt expr3)
  | Cast (op, ty, expr) -> Cast (op, ty, unfoldAddr ctxt expr)
  | Extract (expr, ty, pos) -> Extract (unfoldAddr ctxt expr, ty, pos)
  | Return _ as expr -> expr
  | expr -> printfn "%A" expr; failwith "No"

let rec simplify = function
  | Num _ as expr -> expr
  | Var _ as expr -> expr
  | Load (dest, ty, expr) -> Load (dest, ty, simplify expr)
  | Store (dest, addr, expr) -> Store (dest, simplify addr, simplify expr)
  | FuncName _ as expr -> expr
  | UnOp (op, expr) -> UnOp (op, simplify expr)
  | BinOp (BinOpType.MUL, ty, expr1, Num bv) ->
    if bv = BitVector.one ty then simplify expr1 else BinOp (BinOpType.MUL, ty, simplify expr1, Num bv)
  | BinOp (op, ty, expr1, expr2) -> BinOp (op, ty, simplify expr1, simplify expr2)
  | RelOp (op, expr1, expr2) -> RelOp (op, simplify expr1, simplify expr2)
  | Ite (expr1, expr2, expr3) -> Ite (simplify expr1, simplify expr2, simplify expr3)
  | Cast (op, ty, expr) -> Cast (op, ty, simplify expr)
  | Extract (expr, ty, pos) -> Extract (simplify expr, ty, pos)
  | Undefined _ as expr -> expr
  | Return _ as expr -> expr

let rec extractTerms acc = function
  | Num _ as expr -> expr :: acc
  | Var _ as expr -> expr :: acc
  | BinOp (BinOpType.ADD, _, expr1, expr2) ->
    let acc = extractTerms acc expr1
    let acc = extractTerms acc expr2
    acc
  | BinOp (BinOpType.MUL, _, expr1, Num _) ->
    extractTerms acc expr1
  | BinOp (BinOpType.SHL, _, expr1, Num _) ->
    extractTerms acc expr1
  | expr -> printfn "%A" expr; failwith "No"

let rec isGOTWExpr builder gotAddr ctxt dest = function
  | Normal expr -> isGOTExpr builder gotAddr ctxt expr
  | PhiNum ns ->
    Array.map (fun n -> genDef n dest) ns
    |> Array.exists (fun def ->
      match Map.tryFind def ctxt.Def with
      | None -> false
      | Some def -> isGOTWExpr builder gotAddr ctxt dest def)

and isGOTExpr builder gotAddr ctxt = function
  | Num _ -> false
  | Var dest ->
    match Map.tryFind dest ctxt.Def with
    | None -> false
    | Some def -> isGOTWExpr builder gotAddr ctxt dest def
  | Load (dest, ty, addr) as expr ->
    let range, _ = interpRangeLoad builder ctxt 0UL dest ty addr expr
    if Interval.isConst range then
      gotAddr = (Interval.getLeft range |> BitVector.toUInt64)
    else false
  | Store (dest, addr, expr) -> false
  | FuncName _ -> false
  | UnOp (op, expr) -> isGOTExpr builder gotAddr ctxt expr
  | BinOp (op, ty, expr1, expr2) ->
    isGOTExpr builder gotAddr ctxt expr1 || isGOTExpr builder gotAddr ctxt expr2
  | RelOp (op, expr1, expr2) ->
    isGOTExpr builder gotAddr ctxt expr1 || isGOTExpr builder gotAddr ctxt expr2
  | Ite (expr1, expr2, expr3) ->
    isGOTExpr builder gotAddr ctxt expr1 || isGOTExpr builder gotAddr ctxt expr2 || isGOTExpr builder gotAddr ctxt expr3
  | Cast (op, ty, expr) -> isGOTExpr builder gotAddr ctxt expr
  | Extract (expr, ty, pos) -> isGOTExpr builder gotAddr ctxt expr
  | Undefined _ -> false
  | Return name -> name.StartsWith "__x86.get_pc_thunk"

let updateOffsetTerm offset bv =
  match offset with
  | None -> Some bv
  | Some bv' -> Some <| bv + bv'

let classifyTerm builder gotAddr ctxt (offset, idx) = function
  | Num bv -> updateOffsetTerm offset bv, idx
  | Var dest as expr ->
    if not <| isGOTExpr builder gotAddr ctxt expr then offset, Some dest
    else
      let range, _ = Context.findVarRange (getDestType dest) dest ctxt
      let got = Interval.getLeft range
      updateOffsetTerm offset got, idx
  | _ -> offset, idx

let analIndirectJump (builder: CFGBuilder) gotAddr entry addr ctxt = function
  | Jmp (InterJmp (_, expr)) ->
    let addrs = getAddrs [] ctxt expr
    let addrs =
      List.map (fun addr ->
        fst <| interpRangeExpr builder ctxt 0UL (PCVar (32<rt>, 0)) addr) addrs
      |> List.filter (fun addr -> not <| Interval.isConst addr)
    if List.length addrs = 1 then
      let range = List.head addrs
      let baseAddr = Interval.getLeft range |> BitVector.toUInt64
      let normalized = Interval.normalize range
      let ty = Interval.getType range
      let bv = BitVector.ofUInt64 4UL ty
      let range = Interval.bDiv normalized (Interval.cons ty bv bv)
      let size = Interval.getRight range
      //printfn "Addr: %x" addr
      //printfn "%A" size
      if not <| BitVector.isZero (size - BitVector.signedMax 32<rt>) then
        let size = (size |> BitVector.toInt32) + 1
        builder.AddUnresolvedJumpTable addr baseAddr size
  | _ -> ()

let getGOT (hdl: BinHandler) =
  let fileInfo = hdl.FileInfo
  let sections = fileInfo.GetSections ()
  let gotSection =
    if Seq.exists (fun (sec: Section) -> sec.Name = ".got.plt") sections then
      Seq.find (fun (sec: Section) -> sec.Name = ".got.plt") sections
    else Seq.find (fun (sec: Section) -> sec.Name = ".got") sections
  gotSection.Address

let jumpTableAnalysis hdl builder (fcg: CallGraph) =
  let gotAddr = getGOT hdl
  if fcg.Size () <> 0 then
    fcg.IterVertex (fun (f: Vertex<Function>) ->
      let ssaCFG = f.VData.SSACFG
      let root = ssaCFG.GetRoot ()
      List.iter (fun (v: SSAVertex) ->
        let irVData = v.VData.IRVertexData
        let b, isIndirectJump = irVData.GetIsIndirectJump ()
        if b && isIndirectJump then
          let _, pp = irVData.GetPpoint ()
          //printfn "Now starting from %x" <| fst pp
          /// Basic blocks need jump table analysis
          /// 1. Find a path from root to indirect jump
          let path = Algorithms.dijkstra root v
          /// 2. Prepare variables
          let ctxt = Context.initContext ()
          let condMap =
            List.fold (fun acc v -> Map.add v None acc) Map.empty path
          /// 3. Do interval analysis along the path
          let ctxt = intervalAnalysis builder ssaCFG ctxt 0UL condMap path
          /// 4. Identify jump tables
          let _, ppoint = irVData.GetLastPpoint ()
          let addr = fst ppoint
          v.VData.GetStmts () |> List.rev |> List.head
          |> analIndirectJump builder gotAddr f.VData.Entry addr ctxt) ssaCFG.Exits)
