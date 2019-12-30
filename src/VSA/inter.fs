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

module B2R2.VSA.Analysis

open B2R2
open B2R2.BinIR
open B2R2.BinIR.SSA
open B2R2.BinGraph
open B2R2.FrontEnd
open B2R2.ABI
open B2R2.VSA.LoopAnalysis

exception InvalidExprException

let recoverVariables (env: AbsEnv) =
  let doPrint (KeyValue (k, v)) =
    match k with
    | ALoc.Mem (mem, offset, reg) ->
      if mem = MemRgn.Global then ()
      else
        let newALoc = ALoc.Mem (mem, offset+8L, reg)
        if offset = 0L || offset = -8L then ()
        else printfn "%A" newALoc
      (* // TODO : remove comments if we don't need to debug
      match mem with
      | MemRgn.Local (func, addr) ->
        let newOffset = offset + 8L
        if newOffset = 0L then printf ""
        else
          let newALoc = ALoc.Mem (MemRgn.Local (func, addr), newOffset, reg)
          ////printfn "%A: %s" newALoc (v.ToString())
      | _ ->
        ////printfn "%A: %s" k (v.ToString ())
      *)
    //| ALoc.Register _ -> printfn "%A: %s" k (v.ToString ());acc2
    | _ -> ()//"%A: %s" k (v.ToString ());acc2
  env |> Seq.iter doPrint

(* TODO: convert LowUIR.AST.TypeCheck module *)
let getTypeDest (dest: SSA.Destination) =
  match dest with
  | RegVar (t, _, _, _)
  | PCVar (t, _)
  | TempVar (t, _) -> t
  | MemVar _ -> 64<rt>

(* TODO: convert LowUIR.AST.TypeCheck module *)
let rec getType (expr: SSA.Expr) =
  match expr with
  | Num n -> BitVector.getType n
  | Var dest -> getTypeDest dest
  | Load (_, t, _) -> t
  | Store (_, e1, e2) -> getType e1
  | UnOp (_, e) -> getType e
  | BinOp (_, t, _, _) -> t
  | RelOp (_) -> 1<rt>
  | Ite (e1, e2, e3) -> getType e1
  | Cast (_, t, _) -> t
  | Extract (_, t, _) -> t
  | Undefined (t, _) -> t
  | FuncName (_) -> raise InvalidExprException
  // TODO: Consider return type
  | Return -> 64<rt>

let translateDestALoc (dest: SSA.Destination) =
  match dest with
  | PCVar (typ, idx) -> ALoc.Register ("PC", idx, typ)
  | RegVar (typ, id, name, idx) -> ALoc.Register (name, idx, typ)
  | TempVar (typ, idx) -> ALoc.Register ("Temp", idx, typ)
  // TODO: handle MemVar properly.
  | MemVar (idx) -> ALoc.Temp ("MemVar", idx, 64<rt>)

let translateALoc (expr: SSA.Expr) =
  match expr with
  | Num bv ->
    ALoc.Mem (MemRgn.Global, bv |> BitVector.toInt64, (BitVector.getType bv))
  | Var dest -> translateDestALoc dest
  | _ -> failwithf "translateALoc: Not implemented: %A" expr

let setDefaultVS aloc env =
  // TODO: handle register, global a-loc differently
  // TODO: get valueset from the binary if aloc is Global
  let bits = ALoc.getType aloc
  let si = StridedInterval.all bits
  let defaultVS = ValueSet.ofSIMemRgn si MemRgn.Global
  defaultVS, (env |> Map.add aloc defaultVS)

let storeMemType1 pos aloc oldVS vs env =
  let bit = RegType.fromBitWidth (int pos)
  if oldVS.Bits <= bit + vs.Bits then // new+old
    let vs1 = ValueSet.extract oldVS bit 0
    let vs1 = ValueSet.cast vs1 oldVS.Bits
    let vs2 = ValueSet.cast vs oldVS.Bits
    let bv = BitVector.ofInt64 pos oldVS.Bits
    let vs2 = ValueSet.shl vs2 (ValueSet.ofBV bv)
    let vs = ValueSet.bor vs1 vs2
    vs, env |> Map.add aloc vs
  else // old+new+old
    let gap = vs.Bits + bit
    let num = oldVS.Bits - gap
    let vs1 = ValueSet.extract oldVS num (int gap)
    let vs1 = ValueSet.cast vs1 oldVS.Bits
    let bv = BitVector.ofInt64 (int64 gap) oldVS.Bits
    let vs1 = ValueSet.shl vs1 (ValueSet.ofBV bv)
    let vs2 = ValueSet.cast vs oldVS.Bits
    let bv = BitVector.ofInt64 pos oldVS.Bits
    let vs2 = ValueSet.shl vs2 (ValueSet.ofBV bv)
    let vs3 = ValueSet.extract oldVS bit 0
    let vs3 = ValueSet.cast vs3 oldVS.Bits
    let vs = ValueSet.bor vs3 (ValueSet.bor vs1 vs2)
    vs, env |> Map.add aloc vs

let storeMemType2 pos aloc oldVS vs env =
  if vs.Bits > oldVS.Bits then
    let newVS = ValueSet.extract vs oldVS.Bits 0
    newVS, env |> Map.add aloc newVS
  elif vs.Bits < oldVS.Bits then
    let newVS = ValueSet.cast vs oldVS.Bits
    newVS, env |> Map.add aloc newVS
  else vs, env |> Map.add aloc vs

let storeMemType3 pos aloc oldVS vs env =
  let bit = RegType.fromBitWidth (int pos)
  if vs.Bits < bit + oldVS.Bits then // old+new
    let gap = vs.Bits - bit
    let bit = oldVS.Bits - gap
    let vs1 = ValueSet.extract oldVS bit (int gap)
    let vs1 = ValueSet.cast vs1 oldVS.Bits
    let bv = BitVector.ofInt64 (int64 gap) oldVS.Bits
    let vs1 = ValueSet.shl vs1 (ValueSet.ofBV bv)
    let vs2 = ValueSet.cast vs oldVS.Bits
    let vs = ValueSet.bor vs1 vs2
    vs, env |> Map.add aloc vs
  else // new
    let vs = ValueSet.cast vs oldVS.Bits
    vs, env |> Map.add aloc vs

let getMemType1 pos oldALoc oldVS vs accEnv =
  let bit = RegType.fromBitWidth (int pos)
  if oldVS.Bits < bit + vs.Bits then // old + new(binrg oldVS)
    let bv = BitVector.ofInt64 (int64 pos) oldVS.Bits
    let vs1 = ValueSet.shr oldVS (ValueSet.ofBV bv)
    let vs1 = ValueSet.cast vs1 vs.Bits
    let newBit = oldVS.Bits - bit
    let bv = BitVector.ofInt64 (int64 newBit) vs.Bits
    let vs2 = ValueSet.shl vs (ValueSet.ofBV bv)
    let vs2 = ValueSet.bor vs1 vs2
    vs2, accEnv
  else // new(bring oldVS)
    let bv = BitVector.ofInt64 (int64 pos) oldVS.Bits
    let vs1 = ValueSet.shr oldVS (ValueSet.ofBV bv)
    let vs1 = ValueSet.cast vs1 vs.Bits
    vs1, accEnv

let getMemType2 pos aloc oldVS vs env =
  let newVS = ValueSet.cast oldVS vs.Bits
  newVS, env

let getMemType3 pos oldALoc oldVS vs accEnv =
  let bit = RegType.fromBitWidth (int pos)
  if vs.Bits <= bit + oldVS.Bits then
    let bv = BitVector.ofInt64 (int64 pos) oldVS.Bits
    let vs1 = ValueSet.shl oldVS (ValueSet.ofBV bv)
    let vs1 = ValueSet.cast vs1 vs.Bits
    let vs2 = ValueSet.shl vs (ValueSet.ofBV (BitVector.ofInt64 pos vs.Bits))
    let bv = BitVector.ofInt64 ((int64 vs.Bits) - pos) vs.Bits
    let vs2 = ValueSet.shr vs2 (ValueSet.ofBV bv)
    let vs2 = ValueSet.cast vs2 vs.Bits
    let vs2 = ValueSet.bor vs1 vs2
    vs2, accEnv
  else
    vs, accEnv

let loadMemType1 gap pad oldALoc oldVS vs accEnv =
  let max = BitVector.zero vs.Bits - BitVector.one vs.Bits
  let newVS, newEnv = getMemType1 gap oldALoc oldVS vs accEnv
  let newPad, _ = getMemType1 gap oldALoc (ValueSet.ofBV max) pad accEnv
  //printfn "pad1%A %A" oldALoc newPad
  newPad, newVS, newEnv

let loadMemType2 gap pad oldALoc oldVS vs accEnv =
  let max = BitVector.zero vs.Bits - BitVector.one vs.Bits
  let newVS, newEnv = getMemType2 gap oldALoc oldVS vs accEnv
  let newPad, _ = getMemType2 gap oldALoc (ValueSet.ofBV max) pad accEnv
  //printfn "pad2%A %A" oldALoc newPad
  newPad, newVS, newEnv

let loadMemType3 gap pad oldALoc oldVS vs accEnv =
  let max = BitVector.zero vs.Bits - BitVector.one vs.Bits
  let newVS, newEnv = getMemType3 gap oldALoc oldVS vs accEnv
  let newPad, _ = getMemType3 gap oldALoc (ValueSet.ofBV max) pad accEnv
  //printfn "pad3%A %A" oldALoc newPad
  newPad, newVS, newEnv

let checkOffset aloc oldALoc =
  match oldALoc, aloc with
  | Mem (mem1, offs1, typ1), Mem (mem2, offs2, typ2) ->
    let bit1, bit2 = int64 typ1, int64 typ2
    if offs1 > offs2 then 3, (offs1 - offs2) * 8L
    elif offs1 = offs2 then 2, 0L
    else 1, (offs2 - offs1) * 8L
  | _, _ -> failwith "x"

let handleUnknownValue pad vs aloc env =
  let max = BitVector.zero vs.Bits - BitVector.one vs.Bits
  let si1, si2 = ValueSet.toSI vs, ValueSet.toSI pad
  let st = BitVector.one vs.Bits
  let lower, upper =
    match si1.SI, si2.SI with
    | Value sival1, Value sival2 ->
      let ub = BitVector.bor (BitVector.bxor sival2.Upper max) sival1.Upper
      sival1.Lower, ub
    | _ -> failwith "handleUnknownValue error"
  let si = StridedInterval.init st lower upper vs.Bits
  let vs = ValueSet.ofSIMemRgn si (ValueSet.getMemRgn vs)
  vs, env |> Map.add aloc vs

let lookupMemVar aloc bits memEnv env =
  let zero = ValueSet.zero bits
  let isFull data =
    let max = BitVector.zero bits - BitVector.one bits
    if data = (ValueSet.ofBV max) then true else false
  let main (pad, vs, accEnv) oldALoc oldVS =
    if isFull pad then pad, vs, accEnv
    else
      match checkOffset aloc oldALoc with
      | 1, num -> loadMemType1 num pad oldALoc oldVS vs accEnv
      | 2, num -> loadMemType2 num pad oldALoc oldVS vs accEnv
      | 3, num -> loadMemType3 num pad oldALoc oldVS vs accEnv
      | _, _ -> pad, vs, accEnv
  let pad, vs, env = memEnv |> Map.fold main (zero, zero, env)
  if isFull pad then vs, env |> Map.add aloc vs
  else handleUnknownValue pad vs aloc env

let lookupALoc aloc (env: AbsEnv) =
  match env.TryGetValue aloc with
  | true, vs -> vs, env;
  | false, _ -> setDefaultVS aloc env

let lookupMemALoc aloc (env: AbsEnv) =
  match env.TryGetValue aloc with
  | true, vs -> vs, env;
  | false, _ ->
    match aloc with
    | Mem (mem, offs, typ) ->
      let bit = (int64 typ) / 8L
      let getEnv key value =
        match key with
        | Mem (memRgn, off, ty) ->
          let bit2 = (int64 ty) / 8L
          if memRgn = mem then
            if off > offs && offs + bit > off then true
            elif off = offs then true
            elif off < offs && off + bit2 > offs then true
            else false
          else false
        | _ -> false
      let memEnv = env |> Map.filter getEnv |> Map.remove aloc
      if Map.isEmpty memEnv then setDefaultVS aloc env
      else
        match Map.tryFindKey (fun k v -> ValueSet.isAll v) memEnv with
        | Some key -> setDefaultVS aloc env
        | Option.None -> lookupMemVar aloc typ memEnv env
    | _ -> setDefaultVS aloc env

let translateNumsALoc dest aloc (nums: int[]) env ctxt =
  let numsToALoc acc index =
    let aloc =
      match aloc with
      | ALoc.Register (name, idx, typ) -> ALoc.Register (name, index, typ)
      | ALoc.Temp (name, idx, typ) -> ALoc.Temp (name, index, typ)
      | _ -> failwithf "translateNumsALoc : Not implemented : %A" aloc
    match Map.tryFind aloc env with
    | Some x -> List.append [aloc] acc
    | Option.None -> acc
  let getIdx acc v =
    let idx = List.tryFindIndex (fun elem -> v = elem) ctxt.ALocs
    match idx with
    | Some value -> if acc < value then acc else value
    | Option.None -> acc
  let setVS acc elem =
    match Map.tryFind elem env with
    | Some x -> x
    | Option.None -> acc
  let alocs = nums |> Array.fold numsToALoc []
  let length = (List.length ctxt.ALocs) - 1
  let idx = alocs |> List.fold getIdx length
  if idx = length then ValueSet.all (getTypeDest dest), env
  else lookupALoc (ctxt.ALocs.[idx]) env

// TODO: implement other operations. Please check ValueSet.fs
let inline translateBinOp (op: BinOpType) =
  match op with
  | BinOpType.ADD -> ValueSet.add
  | BinOpType.SUB -> ValueSet.sub
  | BinOpType.MUL -> ValueSet.mul
  | BinOpType.DIV -> ValueSet.div
  | BinOpType.SDIV -> ValueSet.sdiv
  | BinOpType.MOD -> ValueSet.modulo
  | BinOpType.SMOD -> ValueSet.smodulo
  | BinOpType.SHL -> ValueSet.shl
  | BinOpType.SHR -> ValueSet.shr
  | BinOpType.SAR -> ValueSet.sar
  | BinOpType.AND -> ValueSet.band
  | BinOpType.OR -> ValueSet.bor
  | BinOpType.XOR -> ValueSet.bxor
  | BinOpType.CONCAT -> ValueSet.concat
  | BinOpType.APP -> ValueSet.app
  | BinOpType.CONS -> ValueSet.cons
  | (_ as e) -> failwithf "translateBinOp: Not implemented: %A" e

let inline translateUnOp (op: UnOpType) =
  match op with
  | UnOpType.NEG -> ValueSet.neg
  | UnOpType.NOT -> ValueSet.bnot
  | (_ as e) -> failwithf "translateUnOp: Not implemented: %A" e

let inline translateCastOp (op: CastKind) =
  match op with
  | CastKind.SignExt -> ValueSet.sext
  | CastKind.ZeroExt -> ValueSet.zext
  | (_ as e) -> failwithf "translateCastOp: Not implemented: %A" e


// TODO: check if we can remove e1 and e2 in evalRelOp by checking vs1 and vs2.
// Maybe Global can be considered as a constant?
let isConst (e: SSA.Expr) =
  match e with
  | Num _ -> true
  | Var _ -> false
  | _ -> failwithf "isConst: this never happens: %A" e

// this also handles case 4 and case 5 in Figure 3.1
let relOpGEHelper e1 e2 vs1 vs2 fn (env: AbsEnv) =
  // if e1 is constant, we do not need to proceed
  if isConst e1 then env
  else
    let newvs2 =
      // if e2 is constant, we need to set its all memory region to Top.
      if isConst e2 then ValueSet.setOtherRgnAll vs2 vs1
      else vs2
    let aloc1 = translateALoc e1
    //printfn "======"
    //printfn "vs1: %s" (vs1.ToString ())
    //printfn "vs2: %s" ((fn newvs2).ToString ())
    let newvs1 = ValueSet.intersection vs1 (fn newvs2)
    env |> Map.add aloc1 newvs1

// vs1 = vs2
let relOpEQ e1 e2 vs1 vs2 env =
  env |> relOpGEHelper e1 e2 vs1 vs2 ValueSet.init
      |> relOpGEHelper e2 e1 vs2 vs1 ValueSet.init

// vs1 >= vs2
let relOpGE e1 e2 vs1 vs2 env =
  env |> relOpGEHelper e1 e2 vs1 vs2 ValueSet.removeUpperBounds
      |> relOpGEHelper e2 e1 vs2 vs1 ValueSet.removeLowerBounds

// vs1 > vs2
let relOpGT e1 e2 vs1 vs2 env =
  let newvs1 = ValueSet.cutUpperBounds vs1
  let newvs2 = ValueSet.cutLowerBounds vs2
  env |> relOpGEHelper e1 e2 vs1 newvs2 ValueSet.removeUpperBounds
      |> relOpGEHelper e2 e1 vs2 newvs1 ValueSet.removeLowerBounds

// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
// TODO: consider 3.4.1 Idioms.
// TODO: check if we need to consider signed operation differently.
// TODO: need to evaluate each RelOp and return proper T/F/Maybe value
let evalRelOp (op: RelOpType)
              (e1: SSA.Expr) (e2: SSA.Expr)
              (vs1: ValueSet) (vs2: ValueSet)
              (env: AbsEnv) =
  match op with
  | RelOpType.EQ -> ValueSet.eq vs1 vs2, env
  | RelOpType.NEQ -> ValueSet.neq vs1 vs2, env
  | RelOpType.GT -> ValueSet.gt vs1 vs2, env
  | RelOpType.GE -> ValueSet.ge vs1 vs2, env
  | RelOpType.SGT -> ValueSet.sgt vs1 vs2, env
  | RelOpType.SGE -> ValueSet.sge vs1 vs2, env
  | RelOpType.LT -> ValueSet.lt vs1 vs2, env
  | RelOpType.LE -> ValueSet.le vs1 vs2, env
  | RelOpType.SLT -> ValueSet.slt vs1 vs2, env
  | RelOpType.SLE -> ValueSet.sle vs1 vs2, env
  | (_ as e) -> failwithf "translateRelOp: Not implemented: %A" e

let initializeALocs (vs: ValueSet) size (env: AbsEnv) : AbsEnv =
  let addMapHelper (rgn: MemRgn) (accEnv: AbsEnv) addrBV =
    let aloc = ALoc.Mem (rgn, addrBV |> BitVector.toInt64, size)
    // TODO: get valueset from the binary if aloc is Global
    if accEnv.ContainsKey aloc then accEnv
    else
      let tempVS, env1 = lookupMemALoc aloc accEnv
      env1 |> Map.add aloc tempVS
  let handleTop vs =
    let bv = BitVector.ofInt64 -9999L vs.Bits
    addMapHelper (ValueSet.getMemRgn vs) env bv
  let foldHelper accEnv rgn addrs =
    addrs |> List.fold (addMapHelper rgn) accEnv
  if ValueSet.isConst vs then
    let addrList = ValueSet.concrete vs
    addrList |> Map.fold foldHelper env
  else //TODO : Handle a case that uses index with counter in a loop
    let si = ValueSet.toSI vs
    match si.SI with
    | Value sival ->
      let st, lb, ub = sival.Stride, sival.Lower, sival.Upper
      let isAll = ub - lb
      let bv = BitVector.ofInt64 60L si.Bits
      if BitVector.isTrue <| BitVector.gt isAll bv then handleTop vs
      else (ValueSet.concrete vs) |> Map.fold foldHelper env
    | _ -> handleTop vs


// 3.1. Fetch fully/partially accessed a-locs.
// TODO: we merge and split intersections of aloc at variable recovery.
let fetchALocs (vs: ValueSet) (size: RegType) (env: AbsEnv) =
  // case 1: fully accessed -> ALoc.StartAddr in VS and ALoc.RegType = size
  // case 2: partially accessed -> ALoc.StartAddr in VS, ALoc.RegType <> size
  // case 3: partially accessed -> ALoc intersects with VS.
  //printfn "VS: %s" (vs.ToString ())
  let classifyALoc (F: ALoc list, P: ALoc list) (aloc: ALoc) =
    match aloc with
    | Mem (memRgn, offs, typ) ->
      let offsBV = BitVector.ofInt64 offs vs.Bits
      //printfn "COMP ==="
      //printfn "VS_IN: %s" (vs.ToString ())
      //printfn "Aloc: %A" aloc
      if ValueSet.containsMemRgnBV vs memRgn offsBV then
        if typ = size then // case 1
          aloc :: F, P
        else // case 2
          F, aloc :: P
      else
        let alocSIVS = ALoc.toVSInterval aloc vs.Bits
        let interVS = ValueSet.intersection vs alocSIVS
        //printfn "AlocVS: %s" (alocSIVS.ToString ())
        //printfn "InterVS: %s" (interVS.ToString ())
        if ValueSet.isNone <| interVS then F, P
        // case 3
        // We check any address in [Aloc.StartAddr, ALoc.EndAddr] exists in
        // ValueSet.
        // TODO: We may also consider the size of addresses in ValueSet.
        else F, aloc :: P
    | _ -> F, P
  let alocs = env |> Map.toList |> List.map fst
  alocs |> List.fold classifyALoc ([], [])

let checkMemVar accEnv vs aloc oldALoc oldVS =
  match checkOffset aloc oldALoc with
  | 1, num ->
    let _, env = storeMemType1 num oldALoc oldVS vs accEnv
    env
  | 2, num ->
    let _, env = storeMemType2 num oldALoc oldVS vs accEnv
    env
  | 3, num ->
    let _, env = storeMemType3 num oldALoc oldVS vs accEnv
    env
  | _, _ -> accEnv

let handleMemVar (vs: ValueSet) aloc env =
  match aloc with
  | Mem (mem, offs, typ) ->
    let bit = (int64 typ) / 8L
    let getEnv key value =
      match key with
      | Mem (memRgn, off, ty) ->
        let bit2 = (int64 ty) / 8L
        if memRgn = mem then
          if off > offs && offs + bit > off then true
          elif off = offs then true
          elif off < offs && off + bit2 > offs then true
          else false
        else false
      | _ -> false
    let memEnv = env |> Map.filter getEnv |> Map.remove aloc
    AbsEnvAPI.merge env (memEnv |> Map.fold (fun acc key value ->
      checkMemVar acc vs aloc key value) memEnv)
  | _ -> env

let evalStore aloc vs1 vs2 oldEnv env dest ctxt =
  let size = ValueSet.getType vs2
  // First, initialize alocs for a given vs, and then proceed
  let env2 = initializeALocs vs1 size env
  //printfn "--------"
  let fullALocs, partialALocs = fetchALocs vs1 size env2
  //printfn "FULL: %A" fullALocs
  //printfn "Partial: %A" partialALocs
  let updateStrong (accEnv: AbsEnv) aloc =
    let env = accEnv |> Map.add aloc vs2
    handleMemVar vs2 aloc env
  let updateWeak (accEnv: AbsEnv) aloc =
    let env = accEnv |> Map.add aloc vs2
    handleMemVar vs2 aloc env
  let updateAll (accEnv: AbsEnv) aloc =
    accEnv |> Map.add aloc (ValueSet.all size)
  let isStrong (aloc: ALoc) =
    match aloc with
    | Mem (memRgn, offs, typ) ->
      match memRgn with
      | MemRgn.Global -> true
      | MemRgn.Local (name, addr) ->
        // TODO: check if a-loc is in recursive procedure
        true
      | MemRgn.Heap _ -> false
    | _ -> false
  // Update fully accessed a-locs
  let fullEnv =
    if (fullALocs |> List.length) = 1 &&
       List.isEmpty <| partialALocs &&
       isStrong fullALocs.[0] then
      fullALocs |> List.fold updateStrong env2
    else
      fullALocs |> List.fold updateWeak env2
  // Update partially accessed a-locs
  // let retEnv =
  //   partialALocs |> List.fold updateAll fullEnv
  //printfn "--------"
  // TODO: check if we need to return calculated vs here.
  vs2, fullEnv

let evalLoad vs1 size env1 =
  // First, initialize alocs for a given vs, and then proceed
  if ValueSet.isAll vs1 then ValueSet.setType vs1 size, env1
  else
    let env2 = initializeALocs vs1 size env1 // Lock
    let fullALocs, partialALocs = fetchALocs vs1 size env2
    //printfn "FULL: %A" fullALocs
    //printfn "Partial: %A" partialALocs
    let doUnion (accVS: ValueSet, accEnv: AbsEnv) aloc =
      let vs, env = lookupALoc aloc accEnv
      ValueSet.union accVS vs, env
    let doWeakUnion (accVS: ValueSet, accEnv: AbsEnv) aloc =
      let vs, env = lookupMemALoc aloc accEnv
      ValueSet.union accVS vs, env
    let retVS, retEnv =
      if List.isEmpty fullALocs then
        (ValueSet.all size), env2
      elif List.isEmpty partialALocs then
        fullALocs |> List.fold doUnion ((ValueSet.none size), env2)
      elif List.length fullALocs < 30 then
        fullALocs |> List.fold doWeakUnion ((ValueSet.none size), env2)
      else (ValueSet.all size), env2
    //printfn "retVS: %A" retVS
    retVS, retEnv

/// this returns (ValueSet * AbsEnv)
let rec evalSSAExpr aloc (expr: SSA.Expr) (env: AbsEnv) ctxt =
  // TODO: clean up for handling Memvar, Store, and Load
  match expr with
  // TODO: check if all constants can be set as ValueSetKind.All
  | Num bv -> ValueSet.ofBV bv, env
  | Var dest ->
    let aloc = translateDestALoc dest
    lookupALoc aloc env
  | BinOp (op, typ, e1, e2) ->
    let vs1, env1 = evalSSAExpr aloc e1 env ctxt
    let vs2, env2 = evalSSAExpr aloc e2 env1 ctxt
    (translateBinOp op) vs1 vs2, env2
  | UnOp (op, e) ->
    let vs1, env1 = evalSSAExpr aloc e env ctxt
    (translateUnOp op) vs1, env1
  | RelOp (op, e1, e2) ->
    let vs1, env1 = evalSSAExpr aloc e1 env ctxt
    let vs2, env2 = evalSSAExpr aloc e2 env1 ctxt
    evalRelOp op e1 e2 vs1 vs2 env2
  | Cast (op, typ, e) ->
    let vs1, env1 = evalSSAExpr aloc e env ctxt
    (translateCastOp op) vs1 typ, env1
  | Extract (e, typ, pos) ->
    let vs1, env1 = evalSSAExpr aloc e env ctxt
    ValueSet.extract vs1 typ pos, env1
  | Store (dest, e1, e2) -> // e1 = addr
    let vs1, env1 = evalSSAExpr aloc e1 env ctxt
    let vs2, env2 = evalSSAExpr aloc e2 env1 ctxt
    evalStore aloc vs1 vs2 env env2 dest ctxt
  | Load (dest, typ, e) ->
    let vs1, env1 = evalSSAExpr aloc e env ctxt
    evalLoad vs1 typ env1
  | Undefined (typ, s ) -> ValueSet.all typ, env
  (* TODO: check if we need to handle below cases
  | FuncName s ->
  *)
  | Ite (e1, e2, e3) ->
    let vs1, _ = evalSSAExpr aloc e1 env ctxt
    if vs1 = ValueSet.True then evalSSAExpr aloc e2 env ctxt
    else evalSSAExpr aloc e3 env ctxt
  | Return ->
    let retALoc =
      match aloc with
      | Register (name, idx, typ) -> ALoc.Register (name, idx - 1, typ)
      | Temp (name, idx, typ) -> ALoc.Temp (name, idx - 1, typ)
      | _ -> failwithf "evalSSAExpr Return : not implemented: %A" aloc
    let newEnv = env |> Map.filter (fun key value ->
      if key = retALoc then true else false)
    let retEnv = AbsEnvAPI.merge env newEnv
    let vs = retEnv.[retALoc]
    vs, retEnv
  | (_ as e) -> failwithf "evalSSAExpr aloc: Not implemented: %A" e

let genDef n = function
  | RegVar (ty, r, s, _) -> RegVar(ty,r,s,n)
  | PCVar (ty, _) -> PCVar(ty,n)
  | TempVar (ty, _) -> TempVar (ty, n)
  | MemVar _ -> MemVar n

let rec releaseWExpr ctxt dest = function
  | Normal expr -> releaseExpr ctxt expr
  | PhiNum ns ->
    let defs = List.map (fun n-> genDef n dest) <| Array.toList ns
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
    Ite (releaseExpr ctxt expr1,
         releaseExpr ctxt expr2, releaseExpr ctxt expr3)
  | Cast (op, ty, expr) -> Cast (op, ty, releaseExpr ctxt expr)
  | Extract (expr, ty, pos) -> Extract (releaseExpr ctxt expr, ty, pos)
  | Undefined _ as expr -> expr
  | Return _ as expr -> expr

let rec releaseOp2 ctxt = function
  | Var var ->
    let vs, env = lookupALoc (translateDestALoc var) ctxt.Env
    ValueSet.toSI vs
  | Load (dest, ty, e) ->
    let aloc = translateDestALoc dest
    let vs1, env1 = evalSSAExpr aloc e ctxt.Env ctxt
    let vs1, env1 = evalLoad vs1 ty env1
    ValueSet.toSI vs1
  | Num bv -> StridedInterval.ofBV bv
  | _ as e -> failwithf "%A" e
  //| _ as e -> Temp ("Temp", 0, 64<rt>)

let rec releaseOp1 ctxt = function
  | Var dest -> translateDestALoc dest
  | Load (dest, ty, e) ->
    let aloc = translateDestALoc dest
    let vs1, env1 = evalSSAExpr aloc e ctxt.Env ctxt
    let env2 = initializeALocs vs1 ty env1
    let fALocs, pALocs = fetchALocs vs1 ty env2
    if List.isEmpty fALocs then List.head pALocs
    else List.head fALocs
  | Num bv -> Temp ("Temp", 0, 64<rt>)
  | Extract (expr, ty, pos) ->
    releaseOp1 ctxt expr
  | _ as e -> failwithf "%A" e
  //| _ as e -> Temp ("Temp", 0, 64<rt>)

let getDest = function
  | Var dest -> dest
  | _ as e -> failwithf "%A" e

let inferCondFlag = function
  | (RegVar (_, _, "ZF", _) as dest), RegVar (_, _, _, _)
  | RegVar (_, _, _, _), (RegVar (_, _, "ZF", _) as dest) -> dest
  | _ as e -> failwithf "infercondFlag %A" e

let calEqCond dest1 dest2 ctxt = function
  | true -> // EQ
    let result = ValueSet.eq dest1 dest2
    if result = ValueSet.True then Context.setJmpFlag CJmpTrueEdge ctxt
    elif result = ValueSet.Maybe then Context.setJmpFlag JmpEdge ctxt
    else Context.setJmpFlag CJmpFalseEdge ctxt
  | false ->  // NEQ
    let result = ValueSet.neq dest1 dest2
    if result = ValueSet.True then Context.setJmpFlag CJmpTrueEdge ctxt
    elif result = ValueSet.Maybe then Context.setJmpFlag JmpEdge ctxt
    else Context.setJmpFlag CJmpFalseEdge ctxt

let calOrCond dest1 dest2 ctxt =
  let one = ValueSet.one 1<rt>
  let result = ValueSet.bor dest1 dest2
  if ValueSet.isAll result then Context.setJmpFlag JmpEdge ctxt
  elif result = one then Context.setJmpFlag CJmpTrueEdge ctxt
  else Context.setJmpFlag CJmpFalseEdge ctxt

let calAndCond dest1 dest2 ctxt =
  let one = ValueSet.one 1<rt>
  let result = ValueSet.band dest1 dest2
  if ValueSet.isAll result then Context.setJmpFlag JmpEdge ctxt
  elif result = one then Context.setJmpFlag CJmpTrueEdge ctxt
  else Context.setJmpFlag CJmpFalseEdge ctxt

let inferBound si =
  if StridedInterval.isConstSi si then
    let si = StridedInterval.complement si
    match si.SI with
    | Value sival ->
      StridedInterval.ofBV sival.Lower |> StridedInterval.removeLowerBounds,
      StridedInterval.ofBV sival.Upper |> StridedInterval.removeUpperBounds
    | _ -> failwith "here"
  else StridedInterval.complement si, StridedInterval.complement si


let joinCond ctxt edge =
  if edge <> CJmpFalseEdge && edge <> CJmpTrueEdge then ctxt, edge
  else
    let getCondSi acc si =
      let si1, si2 = if edge = CJmpTrueEdge then si, si else inferBound si
      List.append [si1;si2] acc
    let main env aloc siList =
      let siList = siList |> List.fold getCondSi [] |> List.distinct
      let vs, _ = lookupALoc aloc env
      if List.length siList <> 1 && ValueSet.isAll vs then
        let temp = siList |> List.fold (fun acc elem ->
          StridedInterval.intersection acc elem) (StridedInterval.all vs.Bits)
        if StridedInterval.isNone temp then env
        else AbsEnvAPI.envOpSi Join env aloc [temp]
      else AbsEnvAPI.envOpSi Join env aloc siList
    let env = ctxt.Cond |> Map.fold main ctxt.Env
    let ctxt = Context.addEnv env ctxt |> Context.delCond
    ctxt, edge

let storeCond arg1 si ctxt =
  let aloc = releaseOp1 ctxt arg1
  ctxt |> Context.addCond aloc si

let inferOperandZF ctxt isPos dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | RelOp (RelOpType.EQ, Var dest, Num bv) ->
    let arg1 = Var (dest)
    let si = StridedInterval.ofBV bv
    let si1, si2 = if isPos then si, si else inferBound si
    storeCond arg1 si1 ctxt |> storeCond arg1 si2
  | RelOp (RelOpType.EQ, BinOp (BinOpType.ADD, ty, Var _, Load _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.ADD, ty, Var _, Var _), Num _) -> ctxt
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, arg1, Num bv), Num _) ->
    let si = StridedInterval.ofBV bv
    let si1, si2 = if isPos then si, si else inferBound si
    storeCond arg1 si1 ctxt |> storeCond arg1 si2
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, _, Num _, arg1), Num _) ->
    failwith "XXX"
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, _, arg1, arg2), Num _) -> ctxt
  | RelOp (RelOpType.EQ, BinOp (BinOpType.AND, ty, arg1, arg2), Num _) ->
    if arg1 = arg2 then
      let si = StridedInterval.zero ty
      let si1, si2 = if isPos then si, si else inferBound si
      storeCond arg1 si1 ctxt |> storeCond arg1 si2
    else ctxt
  | RelOp (RelOpType.EQ, BinOp (BinOpType.OR, _, arg1, arg2), Num _) ->
    if arg1 = arg2 then failwith "XXX"
    else ctxt
  | RelOp (RelOpType.EQ, BinOp (BinOpType.XOR, _, Num _, arg1), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.XOR, _, arg1, Num _), Num _) ->
    failwith "XXX"
  | RelOp (RelOpType.EQ, BinOp (BinOpType.XOR, ty, arg1, arg2), Num _) ->
    if arg1 = arg2 then
      let si = StridedInterval.zero ty
      let si1, si2 = if isPos then si, si else inferBound si
      storeCond arg1 si1 ctxt |> storeCond arg1 si2
    else ctxt
  | _ -> ctxt////printfn "%A" expr; failwith "Not Implemented Yet"

let inferOperandSF ctxt isPos dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | Extract (BinOp (BinOpType.SUB, ty, arg1, Num bv), 1<rt>, 31) ->
    let si = StridedInterval.ofBV bv |> StridedInterval.removeLowerBounds
    let si = if isPos then si else StridedInterval.complement si
    storeCond arg1 si ctxt
  | Extract (BinOp (BinOpType.AND, ty, arg, Var dest2), 1<rt>, 31) ->
    let dest1 = getDest arg
    if dest1 = dest2 then
      let si = StridedInterval.zero ty |> StridedInterval.removeUpperBounds
      let si = if isPos then si else StridedInterval.complement si
      storeCond arg si ctxt
    else failwith "TODO"
  | _ -> ctxt////printfn "%A" expr; failwith "Not Implemented Yet"

let inferOperandCF ctxt isPos dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | RelOp (RelOpType.LT, arg1, Num bv) ->
    let bit = BitVector.getType bv
    let si = (StridedInterval.ofBV bv) - (StridedInterval.one bit)
             |> StridedInterval.removeLowerBounds
    let si = if isPos then si else StridedInterval.complement si
    storeCond arg1 si ctxt
  | RelOp (RelOpType.LT, Num _, arg1) -> failwith "XXX"
  | RelOp (RelOpType.LT, arg1, arg2) -> ctxt
  | Extract (BinOp _, _, _) -> ctxt
  | _ -> ctxt////printfn "%A" expr; failwith "Not Implemented Yet"

let type1 ctxt = function
  | RegVar (_, _, "ZF", _) as dest -> inferOperandZF ctxt true dest
  | RegVar (_, _, "SF", _) as dest -> inferOperandSF ctxt true dest
  | RegVar (_, _, "CF", _) as dest -> inferOperandCF ctxt true dest
  | RegVar (_, _, "OF", _) as dest -> ctxt
  | RegVar (_, _, "PF", _) as dest -> ctxt
  | expr -> ctxt //printfn "%A" expr; failwith "No"

let type2 ctxt = function
  | RegVar (_, _, "ZF", _) as dest -> inferOperandZF ctxt false dest
  | RegVar (_, _, "SF", _) as dest -> inferOperandSF ctxt false dest
  | RegVar (_, _, "CF", _) as dest -> inferOperandCF ctxt false dest
  | RegVar (_, _, "OF", _) as dest -> ctxt
  | expr -> ctxt //printfn "%A" expr; failwith "No"

let type3Aux ctxt dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, t, arg1, Num bv), Num _) ->
    let si = StridedInterval.ofInt64 1L 0L (BitVector.toInt64 bv) t
    storeCond arg1 si ctxt
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Load _, Var _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Load _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Extract _, Load _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Var _), Num _) -> ctxt
  | _ -> ctxt////printfn "%A" expr; failwith "Not Implemented Yet"

let type3 ctxt = function
  | RegVar (_, _, "CF", _), (RegVar (_, _, "ZF", _) as dest)
  | (RegVar (_, _, "ZF", _) as dest), RegVar (_, _, "CF", _) ->
    type3Aux ctxt dest
  | _ -> failwith "No"

let type4Aux ctxt dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | RelOp (RelOpType.EQ, BinOp (BinOpType.ADD, ty, arg1, Num bv), Num _) -> ctxt
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, arg1, Num bv), Num _) ->
    let si = StridedInterval.one ty + StridedInterval.ofBV bv
             |> StridedInterval.removeUpperBounds
    storeCond arg1 si ctxt
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Load _, Var _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Load _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Extract _, Extract _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Var _), Num _) -> ctxt
  | _ -> ctxt////printfn "%A" expr; failwith "Not Implemented Yet"

let type4 ctxt = function
  | RegVar (_, _, "CF", _), (RegVar (_, _, "ZF", _) as dest)
  | (RegVar (_, _, "ZF", _) as dest), RegVar (_, _, "CF", _) ->
    type4Aux ctxt dest
  | _ -> failwith "No"

let type5Aux ctxt dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, arg1, Num bv), Num _) ->
    let si = StridedInterval.ofBV bv |> StridedInterval.removeLowerBounds
    storeCond arg1 si ctxt
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Load _, Var _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Load _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Var _), Num _) -> ctxt
  | RelOp (RelOpType.EQ, BinOp (BinOpType.AND, ty, arg, Var v2), Num _) ->
    let v1 = getDest arg
    if v1 = v2 then
      let si = StridedInterval.zero ty |> StridedInterval.removeLowerBounds
      storeCond arg si ctxt
    else ctxt
  | Extract (BinOp (BinOpType.SUB, _, Var _, Load _), _, _) -> ctxt
  | _ -> ctxt////printfn "%A" expr; failwith "Not Implemented Yet"

let type5 ctxt = function
  | RegVar (_, _, "ZF", _) as dest, RegVar _, RegVar _ ->
    type5Aux ctxt dest
  | _ -> failwith "No"

let type6Aux ctxt dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, arg1, Num bv), Num _) ->
    let si = StridedInterval.one ty + StridedInterval.ofBV bv
             |> StridedInterval.removeUpperBounds
    storeCond arg1 si ctxt
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Load _, Var _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Load _), Num _)
  | RelOp (RelOpType.EQ, BinOp (BinOpType.SUB, ty, Var _, Var _), Num _) -> ctxt
  | RelOp (RelOpType.EQ, BinOp (BinOpType.AND, ty, arg, Var v2), Num _) ->
    let v1 = getDest arg
    if v1 = v2 then
      let si = StridedInterval.one ty |> StridedInterval.removeUpperBounds
      storeCond arg si ctxt
    else ctxt
  | _ -> ctxt////printfn "%A" expr; failwith "Not Implemented Yet"

let type6 ctxt = function
  | RegVar (_, _, "ZF", _) as dest, RegVar _, RegVar _ ->
    type6Aux ctxt dest
  | _ -> failwith "No"

let type7Aux ctxt dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | Extract (BinOp (BinOpType.SUB, _, Var _, Load _), _, _)
  | Extract (BinOp (BinOpType.SUB, _, Load _, Var _), _, _) -> ctxt
  | _ -> ctxt////printfn "%A" expr; failwith "Not Implemented Yet"

let type7 ctxt = function
  | RegVar (_, _, "SF", _) as dest, RegVar _ ->
    type7Aux ctxt dest
  | _ -> failwith "No"

let type8Aux ctxt dest =
  let expr = Map.find dest ctxt.Def |> releaseWExpr ctxt dest
  match expr with
  | Extract (BinOp (BinOpType.SUB, _, Load _, Var _), _, _)
  | Extract (BinOp (BinOpType.SUB, _, Var _, Load _), _, _) -> ctxt
  | Extract (BinOp (BinOpType.SUB, _, Var dest1, Var dest2), _, _) ->
    if dest1 = dest2 then failwith "Not Implemented Yet" else ctxt
  | _ -> ctxt////printfn "%A" expr; failwith "Not Implemented Yet"

let type8 ctxt = function
  | RegVar (_, _, "SF", _) as dest, RegVar _ ->
    type8Aux ctxt dest
  | _ -> failwith "No"

let inferCondKind expr ctxt =
  let one = ValueSet.one 1<rt>
  let zero = ValueSet.zero 1<rt>
  let all = ValueSet.all 1<rt>
  let opNeq vs1 vs2 =
    if ValueSet.isAll vs1 || ValueSet.isAll vs2 then all
    else ValueSet.neq vs1 vs2
  let opEq vs1 vs2 =
    if ValueSet.isAll vs1 || ValueSet.isAll vs2 then all
    else ValueSet.eq vs1 vs2
  match expr with
  | Var (dest) ->
    let vs, _ = lookupALoc (translateDestALoc dest) ctxt.Env
    let ctxt = calAndCond vs vs ctxt
    type1 ctxt dest
  | RelOp (RelOpType.EQ, Var (dest), Num num) ->
    let vs, _ = lookupALoc (translateDestALoc dest) ctxt.Env
    let vs1 = ValueSet.ofBV num
    let ctxt = calEqCond vs vs1 ctxt true
    type2 ctxt dest
  | BinOp (BinOpType.OR, 1<rt>, Var (dest1), Var (dest2)) ->
    let vs, _ = lookupALoc (translateDestALoc dest1) ctxt.Env
    let vs1, _ = lookupALoc (translateDestALoc dest2) ctxt.Env
    let ctxt = calOrCond vs vs1 ctxt
    type3 ctxt (dest1, dest2)
  | RelOp (RelOpType.EQ,
           BinOp (BinOpType.OR, 1<rt>, Var (dest1), Var (dest2)),
           Num num) ->
    let vs, _ = lookupALoc (translateDestALoc dest1) ctxt.Env
    let vs1, _ = lookupALoc (translateDestALoc dest2) ctxt.Env
    let vs = ValueSet.bor vs vs1
    let vs1 = ValueSet.ofBV num
    let ctxt = calEqCond vs vs1 ctxt true
    type4 ctxt (dest1, dest2)
  | BinOp (BinOpType.OR, 1<rt>, Var (dest1),
           RelOp (RelOpType.NEQ, Var (dest2), Var (dest3))) ->
    let vs, _ = lookupALoc (translateDestALoc dest1) ctxt.Env
    let vs1, _ = lookupALoc (translateDestALoc dest2) ctxt.Env
    let vs2, _ = lookupALoc (translateDestALoc dest3) ctxt.Env
    let vs1 = opNeq vs1 vs2
    let ctxt = calOrCond vs vs1 ctxt
    type5 ctxt (dest1, dest2, dest3)
  | BinOp (BinOpType.AND, 1<rt>, RelOp (RelOpType.EQ, Var (dest1), Num num),
           RelOp (RelOpType.EQ, Var (dest2), Var (dest3))) ->
    let vs1, _ = lookupALoc (translateDestALoc dest1) ctxt.Env
    let vs2 = ValueSet.ofBV num
    let vs3, _ = lookupALoc (translateDestALoc dest2) ctxt.Env
    let vs4, _ = lookupALoc (translateDestALoc dest3) ctxt.Env
    let vs = opEq vs1 vs2
    let vs1 = opEq vs3 vs4
    let ctxt = calAndCond vs vs1 ctxt
    type6 ctxt (dest1, dest2, dest3)
  | RelOp (RelOpType.EQ, Var (dest1), Var (dest2)) ->
    let vs, _ = lookupALoc (translateDestALoc dest1) ctxt.Env
    let vs1, _ = lookupALoc (translateDestALoc dest2) ctxt.Env
    let ctxt = calEqCond vs vs1 ctxt true
    type7 ctxt (dest1, dest2)
  | RelOp (RelOpType.NEQ, Var (dest1), Var (dest2)) ->
    let vs, _ = lookupALoc (translateDestALoc dest1) ctxt.Env
    let vs1, _ = lookupALoc (translateDestALoc dest2) ctxt.Env
    let ctxt = calEqCond vs vs1 ctxt false
    type8 ctxt (dest1, dest2)
  | _ as e -> failwithf "%A is not implemented" e

let restoreSP (env: AbsEnv) =
  let isSPALoc (aloc: ALoc) =
    match aloc with
    | Register (name, idx, typ) when name = "RSP" -> true
    | _ -> false
  let lastSPALoc =
    let alocs = env |> Map.toSeq |> Seq.map fst
    alocs |> Seq.filter isSPALoc |> Seq.maxBy ALoc.getIdx
  let vs, env1 = lookupALoc lastSPALoc env
  let eight = BitVector.ofUInt64 8UL (ALoc.getType lastSPALoc)
  let vs8 = ValueSet.ofBV eight
  env1 |> Map.add lastSPALoc (vs + vs8)

let removeSP env =
  env |> Map.filter (fun key value ->
    match key with
    | Register (name, idx, typ) when (name = "RBP" || name = "RSP") -> false
    | _ -> true)

let removeRetAddr (func: Function) ctxt =
  //printfn "subcall exit"
  let env = ctxt.Env
  let rec getLastMem alocs retALoc addr =
    if Seq.isEmpty alocs then retALoc
    else
      let aloc = Seq.head alocs
      let remainALocs = Seq.tail alocs
      let offset = ALoc.getOffs aloc
      if offset < addr then getLastMem remainALocs aloc offset
      else getLastMem remainALocs retALoc addr
  let isMemALoc (aloc: ALoc) =
    match aloc with
    | Mem (mem, addr, typ) ->
      match mem with
      | Local (name, addr)
      | Heap (name, addr) ->
        if name = func.Name then true
        else false
      | _ -> false
    | _ -> false
  let aloc = ALoc.Temp ("MemVar", 0, 64<rt>)
  let alocs = env |> Map.toSeq |> Seq.map fst
  let memALocs = alocs |> Seq.filter isMemALoc
  let lastMemALoc = getLastMem memALocs aloc 0L
  Context.addEnv (env |> Map.remove lastMemALoc) ctxt

let fallThroughFunc ctxt (func: Function) =
  let ssacfg = func.SSACFG
  let root = ssacfg.GetRoot ()
  let rootId = root.GetID ()
  match Map.tryFind rootId ctxt.BBL with
  | Some x -> true
  | Option.None -> false

let mergeAtEndCall oldEnv newEnv f f_ ctxt =
  // 1. Remove ESP, EBP of newEnv
  // 2. Add ESP, EBP of oldEnv to newEnv
  // 3. Merge lastEnv to oldEnv only last idx register
  AbsEnvAPI.setRegIdx ctxt.FunCtxt.FEnv newEnv
  |> removeSP |> AbsEnvAPI.merge oldEnv

let getFunction env funcs addr =
  let funcAddr =
    match addr with
    | Num bv -> BitVector.toUInt64 bv
    | Var dest ->
      let aloc = translateDestALoc dest
      let zero = BitVector.zero (getTypeDest dest)
      let vs, env1 = lookupALoc aloc env
      let vs_ = ValueSet.getConst vs
      let value_ =
        Map.pick (fun key value ->
        if BitVector.isTrue <| BitVector.sge value zero then Some(value)
        else Option.None) vs_
      BitVector.toUInt64 value_
    | Return -> 0UL
    | (_ as e) -> failwithf "getFunction not implemented %A" e
  funcs |> Seq.tryPick (fun (KeyValue (k,v)) ->
    if k = funcAddr then Some(v) else Option.None)

let getAddr stmt =
  match stmt with
  | Jmp (jmpTyp) ->
    match jmpTyp with
    | InterJmp (pc, address) -> address
    // TODO : Consider other value instead of return
    | _ -> Return
  | _ -> Return

let getTempBits aloc expr env ctxt =
  match expr with
  | Store (dest, e1, e2) ->
    let vs1, env1 = evalSSAExpr aloc e1 env ctxt
    ValueSet.getType vs1
  | Return -> 64<rt>
  | (_ as e) -> failwithf "getTempBits not implemented %A" e

let AbstractTransformer (stmt: SSA.Stmt) ctxt (env: AbsEnv) =
  // TODO: Check if we have to translate RSP to RBP or RBP to RSP
  printfn "=========================" |> ignore
  //printfn "Cur BBL: %A" ctxt.CurBBLId
  //printfn "Par BBL: %A" ctxt.ParBBLId
  printfn "stmt: %A" stmt |> ignore
  let ctxt =
    match stmt with
    | Def (dest, expr) ->
      let ctxt = Context.addNormalDef dest expr ctxt
      let aloc = translateDestALoc dest
      let vs, env1 = evalSSAExpr aloc expr env ctxt
      //printfn " %A %A" aloc (vs.ToString())
      let vs, env1 =
        // Set Temp ALoc bit
        match aloc with
        | ALoc.Temp (name, idx, typ) ->
          let vs = getTempBits aloc expr env ctxt |> ValueSet.cast vs
          vs, env1 |> Map.add aloc vs
        | _ -> vs, env1 |> Map.add aloc vs
      recoverVariables env1 |> ignore
      //match dest with
      //| PCVar (typ, idx) -> printfn "PCVar %A" (vs.ToString())
      //| _ -> ()
      let fctxt = FunContext.setCallEnv aloc vs ctxt.FunCtxt
      Context.addEnv env1 (Context.setFunCtxt fctxt ctxt)
      |> Context.addALocs env1
    | Jmp (jmpTyp) ->
      match jmpTyp with
      | IntraJmp (label) -> ctxt
      | InterJmp (pc, addr) -> ctxt
      | InterCJmp (expr, pcVar, expr1, expr2) ->
        let ctxt = inferCondKind expr ctxt
        //recoverVariables ctxt.Env |> ignore
        ctxt
      | IntraCJmp (e1, e2, e3) ->
        let succs = ctxt.BBL.[ctxt.CurBBLId].Succs
        if List.length succs = 1 then ctxt
        else ctxt
          (* TODO : Add case
          let aloc = ALoc.Register ("Temp", -1, 64<rt>)
          let vs, env1 = evalSSAExpr aloc e1 env ctxt
          let LMark = if vs = ValueSet.True then e2 else e3
          getLMarkBBL LMark succs
          *)
          //f0/ailwithf "not implemented %A" stmt
    | Phi (dest, nums) ->
      let ctxt = Context.addPhiDef dest nums ctxt
      let aloc = translateDestALoc dest
      let vs, _ = translateNumsALoc dest aloc nums env ctxt
      let env1 = env |> Map.add aloc vs
      //recoverVariables env1
      let fctxt = FunContext.setCallEnv aloc vs ctxt.FunCtxt
      Context.addEnv env1 (Context.setFunCtxt fctxt ctxt)
      |> Context.addALocs env1
    // skip LMark or SideEffect
    | LMark (e) -> ctxt
    | SideEffect (e) -> ctxt // TODO : Handle sideeffect
  ctxt

let initializeSP (f: Function) (env: AbsEnv)  =
  //TODO: Generalize stack pointer a-loc setup
  let sp = Intel.Register.ofRegID X86_64.abi.StackPtrRegister
  let bp = Intel.Register.ofRegID X86_64.abi.StackBasePtrRegister
  let bits = WordSize.toRegType X86_64.abi.WordSize
  let aloc = ALoc.Register (sp.ToString (), 0, bits)
  let aloc1 = ALoc.Register (bp.ToString (), 0, bits)
  let memRgn = MemRgn.Local (f.Name, f.Entry)
  let defaultVS = ValueSet.zeroMemRgn bits memRgn
  env |> Map.add aloc defaultVS |> Map.add aloc1 defaultVS

let initializeAbsEnv (f: Function) =
  (* TODO: check if we can get/set global a-locs here. Currently, this will be
   * handled lazily *)
  AbsEnv [] |> initializeSP f

let handleVertex ctxt =
  let handleStmt accCtxt (stmt: SSA.Stmt) =
    AbstractTransformer stmt accCtxt accCtxt.Env
  let succ = ctxt.BBL.[ctxt.CurBBLId]
  let stmts = succ.VData.GetStmts ()
  stmts |> List.fold handleStmt ctxt

let readyToEscapeLoop ctxt =
  let id = ctxt.CurBBLId
  let lctxt = ctxt.LoopCtxt.[ctxt.LoopTempId]
  let c2 = AbsEnvAPI.envOpEnv Union ctxt.Env lctxt.C1
           |> AbsEnvAPI.envOpEnv Narrow lctxt.C2
  Context.setLoopFlag -1 ctxt |> Context.setLoopCurId 0
  |> Context.addEnv c2

let startLoop ctxt id edge =
  if ctxt.LoopFlag = 0 then
    let ctxt = Context.setLoopCurId id ctxt |> Context.setLoopTempId id
    Context.setLoopFlag (1 + ctxt.LoopFlag) ctxt, edge
  else if ctxt.LoopFlag = 1 then
    Context.setC1 ctxt |> Context.setC2 ctxt.Env
    |> Context.setLoopFlag (1 + ctxt.LoopFlag), edge
  else
    let lctxt = ctxt.LoopCtxt.[ctxt.CurBBLId]
    let c2 = AbsEnvAPI.envOpEnv Union ctxt.Env lctxt.C1
             |> AbsEnvAPI.envOpEnv Widen lctxt.C2
    if AbsEnvAPI.eqEnv c2 lctxt.C2 || ctxt.LoopFlag > 4 then
      readyToEscapeLoop ctxt, edge
    else
      let ctxt = Context.addEnv c2 ctxt
      Context.setC2 c2 ctxt |> Context.setLoopFlag (1+ ctxt.LoopFlag), edge

let breakLoop ctxt edge =
  let ctxt = Context.setLoopFlag 0 ctxt
  if List.isEmpty ctxt.LoopStack then ctxt, edge
  else
    let flag, id, ctxt = Context.popLoopStack ctxt
    Context.setLoopFlag flag ctxt |> Context.setLoopCurId id
    |> Context.setLoopTempId id, edge

let finishLoop ctxt edge =
  let id = ctxt.LoopTempId
  let ctxt = Context.setLoopCond (ctxt.LoopCond - 1) ctxt
  if ctxt.LoopCond < 0 then
    let ctxt, edge = breakLoop ctxt edge
    ctxt, edge
  elif ctxt.LoopCond <> 0 then
    let edge =
      match ctxt.LoopCtxt.[id].BackEdge.[ctxt.LoopCond] = edge with
      | true -> FallThroughEdge
      | false -> edge
    ctxt, edge
  else
    let ctxt, edge = breakLoop ctxt edge
    let edge =
      match ctxt.LoopCtxt.[id].BackEdge.[ctxt.LoopCond] = edge with
      | true -> FallThroughEdge
      | false -> edge
    ctxt, edge

let isBreak (succ : Vertex<_>) ctxt =
  let succList = succ.Succs
  if List.length succList <> 1 || ctxt.ParBBLId = ctxt.LoopCurId then false
  else
    let succ = List.head succList
    let sid, pid = succ.GetID (), ctxt.LoopTempId
    match Map.tryFind pid ctxt.LoopCtxt, Map.tryFind sid ctxt.LoopCtxt with
    | Some lctxt, Option.None ->
      let cid = ctxt.CurBBLId
      match List.contains cid lctxt.Body with
      | true -> false
       | false -> true
    | _, _ -> false

let checkGoto id ctxt =
  let loopList = ctxt.LoopStack
  let isGoto (flag, bbl) = bbl = id
  match List.tryFindIndex isGoto loopList with
  | Some index ->
    let _, loopList = loopList |> List.splitAt index
    let ctxt = Context.addLoopStack loopList ctxt
    true, ctxt
  | Option.None -> false, ctxt

let loopHandler succ ctxt edge =
  let id = ctxt.CurBBLId
  if ctxt.LoopFlag = -1 then finishLoop ctxt edge
  elif isBreak succ ctxt then breakLoop ctxt edge
  else
    match ctxt.LoopFlag, ctxt.LoopCurId = id, Map.tryFind id ctxt.LoopCtxt with
    | _, true, Some x
    | 0, _, Some x ->
      let backEdge = ctxt.LoopCtxt.[id].BackEdge
      let ctxt = Context.setLoopCond (List.length backEdge) ctxt
      startLoop ctxt id edge
    | _, false, Some x -> // nested
      let backEdge = ctxt.LoopCtxt.[id].BackEdge
      let isGoto, ctxt = checkGoto id ctxt
      if isGoto then // TODO : Consider other cases
        let flag, id, ctxt = Context.popLoopStack ctxt
        let ctxt = Context.setLoopFlag flag ctxt |> Context.setLoopCurId id
                   |> Context.setLoopTempId id
                   |> Context.setLoopCond (List.length backEdge)
        startLoop ctxt id edge
      else
        let backEdge = ctxt.LoopCtxt.[id].BackEdge
        let ctxt = Context.pushLoopStack ctxt.LoopFlag ctxt.LoopCurId ctxt
                   |> Context.setLoopFlag 0
                   |> Context.setLoopCond (List.length backEdge)
        startLoop ctxt id edge
    | _, _, _ -> ctxt, edge

let getRetDest (par: Vertex<_>) curBBL ctxt =
  let succs = par.Succs
  let fallSucc = succs |> List.filter (fun x -> x <> curBBL)
  let funCtxt = FunContext.addRetBBL fallSucc ctxt.FunCtxt
  Context.setFunCtxt funCtxt ctxt

let pathSens edge ctxt =
  if ctxt.LoopFlag = -1 then Context.setJmpFlag JmpEdge ctxt, edge
  else
    if ctxt.JmpFlag = CJmpTrueEdge || ctxt.JmpFlag = CJmpFalseEdge then
      if ctxt.JmpFlag <> edge then ctxt, FallThroughEdge
      else Context.setJmpFlag JmpEdge ctxt, edge
    else Context.setJmpFlag JmpEdge ctxt, edge

let rec intraProceduralVSA ctxt (f: Function) funcs cs  =
  //printfn "func : %A" (f.Name)
  let interProceduralVSA ctxt caller funcs stmt cs =
    let addr = getAddr stmt
    //printfn "func addr : %A" addr
    let callee = getFunction ctxt.Env funcs addr
    match callee with
    | Some(callee) ->
      // If we called the function, we will skip the function
      // if fallThroughFunc ctxt callee then ctxt
      // else
      // Give last idx register + all Mem instead of oldEnv
      let env = AbsEnvAPI.changeIdx 0 ctxt.FunCtxt.FEnv
      let ctxt1 = Context.addEnv env ctxt
      let ctxt1 = intraProceduralVSA ctxt1 callee funcs cs
      let newEnv = ctxt1.Env |> AbsEnvAPI.getLastIdxReg
      Context.addEnv (mergeAtEndCall ctxt.Env newEnv caller callee ctxt) ctxt
      |> Context.addRetEnv ctxt1.RetEnv
    | Option.None -> ctxt
  let env = AbsEnvAPI.removeALocName "RSP" ctxt.Env
  let ctxt = Context.addEnv (AbsEnvAPI.merge (initializeAbsEnv f) env) ctxt
  let absEnvMap = AbsEnvMap ();
  let ssacfg = f.SSACFG
  let ctxt = Context.addCFG ssacfg ctxt
  let root = ssacfg.GetRoot ()
  let rootId = root.GetID ()
  // for nested function call (maybe ctxt is not changed)
  //let lastStmt = n.VData.GetStmts () |> List.rev |> List.head
  //let ctxt = interProceduralVSA ctxt f funcs lastStmt cs
  let rec iterLoop (v: Vertex<SSAVertexData>) pred oldCtxt =
    let mainLoop edge paramCtxt =
      if edge <> CallEdge then handleVertex paramCtxt
      else paramCtxt
    let handleSucc acc (n: Vertex<SSAVertexData>) =
      let newCtxt = iterLoop n v acc
      Context.addEnv acc.Env newCtxt
      |> Context.setFunCtxt acc.FunCtxt
    let lId = oldCtxt.LoopCurId
    if v = root then // root node
      let oldCtxt = Context.addBBL rootId root oldCtxt
                 |> Context.setCurBBLId rootId |> handleVertex
      if List.isEmpty v.Succs then Context.addRetEnv oldCtxt.Env oldCtxt
      else v.Succs |> List.fold handleSucc oldCtxt
    else
      let edge = ssacfg.FindEdge pred v
      if oldCtxt.LoopFlag <= 0 && edge <> CallEdge &&
         edge <> RetEdge && v.IsVisited then
        let edge = ssacfg.FindEdge pred v
        if edge = FallThroughEdge then
          let oldCtxt = removeRetAddr f oldCtxt
          Context.addRetEnv oldCtxt.Env oldCtxt
        else Context.addRetEnv oldCtxt.Env oldCtxt
      else
        let id = v.GetID ()
        let oldCtxt = Context.setCurBBLId id oldCtxt
        let oldCtxt, edge = Context.addEdge oldCtxt.ParBBLId edge oldCtxt
                            |> Context.addBBL id v |> pathSens edge
        let oldCtxt, edge = loopHandler v oldCtxt edge
        let oldCtxt, edge = joinCond oldCtxt edge
        if edge = FallThroughEdge then
          let oldCtxt = removeRetAddr f oldCtxt
          Context.addRetEnv oldCtxt.Env oldCtxt
        elif edge = RetEdge then
          v.Visit()
          let head, funCtxt = FunContext.getRetBBL oldCtxt.FunCtxt
          let oldCtxt = Context.setFunCtxt funCtxt oldCtxt
          if v = head then
            let oldCtxt = mainLoop edge oldCtxt
            if List.isEmpty v.Succs then
              Context.addRetEnv oldCtxt.Env oldCtxt
            else v.Succs |> List.fold handleSucc oldCtxt
          else Context.addRetEnv oldCtxt.Env oldCtxt
        else
          v.Visit()
          let oldCtxt =
            if edge = CallEdge then
              let lastStmt = pred.VData.GetStmts () |> List.rev |> List.head
              let oldCtxt = getRetDest pred v oldCtxt
              interProceduralVSA oldCtxt f funcs lastStmt cs
              |> removeRetAddr f |> mainLoop edge
            else mainLoop edge oldCtxt
          if List.isEmpty v.Succs then Context.addRetEnv oldCtxt.Env oldCtxt
          else v.Succs |> List.fold handleSucc oldCtxt
  absEnvMap.[ rootId ] <- ctxt.Env
  iterLoop root root ctxt


let analyzeVSA (func: Vertex<Function>) funcs_ =
  let clearCFG (v: Vertex<SSAVertexData>) = v.UnVisit
  let fList, cycleList = LoopAnalysis.main func
  let f = func.VData
  let ssacfg = f.SSACFG
  // loop Analysis
  let root = ssacfg.GetRoot ()
  // Value Set Analysis
  let ctxt = Context.init (initializeAbsEnv f) (root.GetID ())
            |> Context.addLoopCtxt cycleList
  let ret = intraProceduralVSA ctxt f funcs_ []
  recoverVariables ret.RetEnv
  ret.CFGList |> List.iter (fun (v: SSACFG) ->
    v.IterVertex clearCFG)
  ()
