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
open B2R2.BinGraph // for VertexID
open B2R2.BinIR // for VertexID
open B2R2.BinIR.SSA // for Destination

open System.Collections.Generic

type Offset = int64

type Idx = int

/// 2.2 Abstract Location (A-Locs)
/// ALoc represents its type, offset, and size.
[<StructuralEquality; StructuralComparison>]
type ALoc =
  (* Global a-loc is based on the absolute global address. Otherwise, address
   * represents the offset from the start address. *)
  | Mem of MemRgn * Offset * RegType
  // TODO: check if we need to change Name to RegisterID.
  // TODO: check if we need Idx. DK thinks we don't.
  | Register of Name * Idx * RegType
  // TODO: check if we can merge Flag with Register
  | Flag of Name * Idx * RegType
  // To represent MemVar
  | Temp of Name * Idx * RegType

  static member getType (aloc: ALoc) =
    match aloc with
    | Mem (_, _, typ) -> typ
    | Register (_, _, typ) -> typ
    | Flag (_, _, typ) -> typ
    | Temp (_, _, typ) -> typ

  static member getIdx (aloc: ALoc) =
    match aloc with
    | Register (_, idx, _) -> idx
    | Flag (_, idx, _) -> idx
    | Temp (_, idx, _) -> idx
    | _ -> failwithf "ALoc.getIdx: No index exists for %A" aloc

  static member getOffs (aloc: ALoc) =
    match aloc with
    | Mem (_, offs, _) -> offs
    | _ -> failwithf "ALoc.getIdx: No offset exists for %A" aloc

  static member getName (aloc: ALoc) =
    match aloc with
    | Register (name, idx, _)
    | Temp (name, idx, _)
    | Flag (name, idx, _) -> name
    | _ -> failwithf "ALoc.getIdx: No offset exists for %A" aloc

  static member toVS (aloc: ALoc) bits =
    match aloc with
    | Mem (memRgn, offs, typ) ->
      let offsBV = BitVector.ofInt64 offs bits
      ValueSet.ofBVMemRgn offsBV memRgn
    | _ -> failwithf "ALoc.toVS: this should not happen: %A" aloc

  static member toVSInterval (aloc: ALoc) bits =
    match aloc with
    | Mem (memRgn, offs, typ) ->
      let startAddr = offs
      let endAddr = offs + (RegType.toByteWidth typ |> int64) - 1L
      let alocSI = StridedInterval.ofInt64 1L startAddr endAddr bits
      ValueSet.ofSIMemRgn alocSI memRgn
    | _ -> failwithf "ALoc.toVSInterval: this should not happen: %A" aloc

type AbsVal =
  | Flag of Bool3
  | VS of ValueSet

/// The authors implement AbsEnv with AVL tree, and F#'s Map does so.
type AbsEnv = Map<ALoc, ValueSet>

type envOp =
  | Join
  | Union
  | Widen
  | Narrow

type AbsEnvAPI =

  static member getVS aloc env =
    match Map.tryFind aloc env with
    | Some x -> x
    | Option.None ->
      let bits = ALoc.getType aloc
      let si = StridedInterval.all bits
      ValueSet.ofSIMemRgn si MemRgn.Global


  static member merge env1 env2 = // env item is removed if env2 has same key
    Map (Seq.concat [ (Map.toSeq env1) ; (Map.toSeq env2) ] )

  static member getMemEnv env =
    let main key value =
      match key with
      | Mem ( _, _, _) -> true
      | _ -> false
    Map.filter main env

  static member eqEnv env1 env2 =
    let env1, env2 = AbsEnvAPI.getMemEnv env1, AbsEnvAPI.getMemEnv env2
    if env1 = env2 then true else false

  static member envOpEnv op env1 env2 =
    let absEnv = AbsEnvAPI.merge env1 env2
    let memEnv = AbsEnvAPI.getMemEnv env1
    let getVS env aloc bit =
      match Map.tryFind aloc env with
      | Some x -> x
      | Option.None -> ValueSet.none bit
    let main env k v =
      let bit = v.Bits
      match op with
      | Union ->
        Map.add k (ValueSet.union (getVS env1 k bit) (getVS env2 k bit)) env
      | Widen ->
        Map.add k (ValueSet.widen (getVS env1 k bit) (getVS env2 k bit)) env
      | Narrow ->
        Map.add k (ValueSet.narrow (getVS env1 k bit) (getVS env2 k bit)) env
      | _ -> failwith "X"
    memEnv |> Map.fold main absEnv

  static member envOpSi op env aloc siList =
    let vs = AbsEnvAPI.getVS aloc env
    let join vs vs1 env_ =
      match op with
      | Join ->
        let tempVS = ValueSet.intersection vs vs1
        if ValueSet.isNone tempVS then env_
        else env_ |> Map.add aloc tempVS
      | _ -> failwith "x"
    let main env_ si =
      let vs1 = ValueSet.getMemRgn vs |> ValueSet.ofSIMemRgn si
      if vs.Bits >= vs1.Bits then join vs (ValueSet.sext vs1 vs.Bits) env_
      else failwith "a" // main (ValueSet.sext vs vs1.Bits) vs1
    siList |> List.fold main env

  static member getALocName name_ env =
    env |> Map.filter (fun key value ->
      match key with
      | ALoc.Flag (name, idx, typ)
      | ALoc.Temp (name, idx, typ)
      | ALoc.Register (name, idx, typ) ->
        if name = name_ then true else false
      | _ -> false) // It never works

  static member removeALocName name_ env =
    env |> Map.filter (fun key value ->
      match key with
      | ALoc.Flag (name, idx, typ)
      | ALoc.Temp (name, idx, typ)
      | ALoc.Register (name, idx, typ) ->
        if name = name_ then false else true
      | _ -> true) // It never works

  static member changeIdx idx_ env =
    let absEnv = AbsEnv []
    env |> Map.fold (fun state key value ->
      match key with
      | ALoc.Mem (_, _, _) -> state |> Map.add key value
      | ALoc.Flag (name, idx, typ) ->
        let newKey = ALoc.Flag (name, idx_, typ)
        state |> Map.add newKey value
      | ALoc.Register (name, idx, typ) ->
        let newKey = ALoc.Register (name, idx_, typ)
        state |> Map.add newKey value
      | ALoc.Temp (name, idx, typ) ->
        let newKey = ALoc.Temp (name, idx_, typ)
        state |> Map.add newKey value) absEnv

  static member getLastIdxReg env =
    let absEnv = AbsEnv []
    env |> Map.fold (fun state key value ->
      match key with
      | ALoc.Mem (_, _, _) -> state |> Map.add key value // Add all Mem value
      | ALoc.Flag (name, idx, typ)
      | ALoc.Register (name, idx, typ)
      | ALoc.Temp (name, idx, typ) ->
        let lastIdxEnv = AbsEnvAPI.getALocName name state
        if lastIdxEnv |> Map.isEmpty = true then state |> Map.add key value
        else
          // Select high idx value
          let aloc = lastIdxEnv |> Map.toSeq |> Seq.map fst |> Seq.head
          let curIdx = ALoc.getIdx <| aloc
          if curIdx > idx then state
          else Map.remove aloc state |> Map.add key value) absEnv

  static member setRegIdx oldEnv newEnv =
    let absEnv = AbsEnv []
    let oldLastEnv = AbsEnvAPI.getLastIdxReg oldEnv
    let newLastEnv = AbsEnvAPI.getLastIdxReg newEnv
    let getKey name_ typ alocType =
      let env = AbsEnvAPI.getALocName name_ oldLastEnv
      if Map.isEmpty env then
        match alocType with
        | "Flag" -> ALoc.Flag (name_, 0, typ)
        | "Register" -> ALoc.Register (name_, 0, typ)
        | "Temp" -> ALoc.Temp (name_, 0, typ)
        | _ -> failwithf "AbsEnvAPI setLastIdxReg error"
      else
        env |> Map.toSeq |> Seq.map fst |> Seq.head
    newLastEnv |> Map.fold (fun state key value ->
      match key with
      | ALoc.Mem (_, _, _) -> state |> Map.add key value
      | ALoc.Flag (name, idx, typ) ->
        let newKey = getKey name typ "Flag"
        state |> Map.add newKey value
      | ALoc.Register (name, idx, typ) ->
        let newKey = getKey name typ "Register"
        state |> Map.add newKey value
      | ALoc.Temp (name, idx, typ) ->
        let newKey = getKey name typ "Temp"
        state |> Map.add newKey value) absEnv



/// AbsEnvMap stores AbsEnv of each Stmt by their VertexID in SSACFG
// TODO: consider changing this locally immutable dictionary
type AbsEnvMap = Dictionary<VertexID, AbsEnv>

type WExpr =
  | Normal of Expr
  | PhiNum of int []

type CondAbs = Map<ALoc, StridedInterval>

type LoopContext = {
  C1 : AbsEnv
  C2 : AbsEnv
  Head : VertexID
  Tail : VertexID list
  BackEdge : CFGEdgeKind list
  Body : VertexID list
}
with
  static member init head tail edge bbls =
    { C1 = AbsEnv []; C2 = AbsEnv [];
      Head = head; Tail = tail; BackEdge = edge; Body = bbls }

  static member setC1 env ctxt =
    { ctxt with C1 = env }

  static member setC2 env ctxt =
    { ctxt with C2 = env }

type FunContext = {
  RetBBL : Vertex<SSABBlock> list // to find function call destination
  FEnv : AbsEnv
}
with
  static member init env =
    { FEnv = env; RetBBL = List.empty }


  static member setRetBBL bblList ctxt =
    { ctxt with RetBBL = bblList }

  static member addRetBBL bbl ctxt =
    { ctxt with RetBBL = List.append bbl ctxt.RetBBL }

  static member getRetBBL ctxt =
    let head = List.head ctxt.RetBBL
    let tail = List.tail ctxt.RetBBL
    let ctxt = FunContext.setRetBBL tail ctxt
    head, ctxt

  static member setCallEnv aloc vs ctxt =
    let name = ALoc.getName aloc
    let env = AbsEnvAPI.removeALocName name ctxt.FEnv
    let env = env |> Map.add aloc vs
    { ctxt with FEnv = env }

type Context = {
  Env : AbsEnv // curEnv
  RetEnv : AbsEnv // result env
  CurBBLId : VertexID // current BBL
  ParBBLId : VertexID // parent BBL
  BBL : Map<VertexID, Vertex<SSABBlock>> // BBL ID * BBL
  Edge : Map<VertexID,CFGEdgeKind> // VertexID * Edge (True, False)
  ALocs : ALoc list

  // For widening in Loop
  Def : Map<Variable, WExpr> // Reg * Expr
  Cond : Map<ALoc, StridedInterval list>

  // For Loop
  LoopFlag : int
  LoopCurId : VertexID
  LoopTempId : VertexID
  LoopCond : int
  LoopStack : VertexID list // for nested loop

  // preLoopAnalysis
  LoopCtxt : Map<VertexID,LoopContext>

  // path-sensitive
  JmpFlag : CFGEdgeKind

  // for function call
  FunCtxt : FunContext

  // for evaluation interprocedural
  CFGList : SSACFG list

  test : Vertex<SSABBlock>
  test2 : Vertex<SSABBlock>

  paths : int
}
with
  static member init env (v:Vertex<SSABBlock>) =
    { Env = env; RetEnv = env; CurBBLId = (v.GetID()); ParBBLId = (v.GetID());
      BBL = Map.empty; Edge = Map.empty; Cond = Map.empty; CFGList = List.empty;
      Def = Map.empty; LoopStack = List.empty; ALocs = List.empty;
      LoopFlag = 0; LoopCurId = 0; JmpFlag = InterJmpEdge; LoopCtxt = Map.empty;
      FunCtxt = FunContext.init env; LoopTempId = 0; LoopCond = 0;
      test = v; test2 = v; paths = 0}

  static member delCond ctxt =
    { ctxt with Cond = Map.empty }

  static member addCond aloc si ctxt =
    match Map.tryFind aloc ctxt.Cond with
    | Some x ->
      let si_ = List.append [si] x
      { ctxt with Cond = Map.add aloc si_ ctxt.Cond }
    | Option.None -> { ctxt with Cond = Map.add aloc [si] ctxt.Cond }

  static member setCurBBLId id v ctxt =
    let parentId = ctxt.CurBBLId
    let a = ctxt.test
    { ctxt with ParBBLId = parentId; CurBBLId = id; test = v; test2 = a }

  static member addEnv env ctxt =
    { ctxt with Env = env }

  static member addRetEnv env ctxt =
    let newEnv = AbsEnvAPI.merge ctxt.RetEnv env
    { ctxt with RetEnv = newEnv; paths = ctxt.paths + 1 }

  static member addBBL id bbl ctxt =
    { ctxt with BBL = Map.add id bbl ctxt.BBL }

  static member addEdge id flag ctxt =
    { ctxt with Edge = Map.add id flag ctxt.Edge }

  static member addNormalDef dest expr ctxt =
    { ctxt with Def = Map.add dest (Normal expr) ctxt.Def }

  static member addPhiDef dest nums ctxt =
    { ctxt with Def = Map.add dest (PhiNum nums) ctxt.Def }

  static member setLoopFlag count ctxt =
    { ctxt with LoopFlag = count }

  static member setLoopCurId id ctxt =
    { ctxt with LoopCurId = id; }

  static member setLoopTempId id ctxt =
    { ctxt with LoopTempId = id; }

  static member pushLoopStack (id: VertexID) ctxt =
    { ctxt with LoopStack = List.append [id] ctxt.LoopStack }

  static member addLoopStack loopStack ctxt =
    { ctxt with LoopStack = loopStack }

  static member popLoopStack ctxt =
    ctxt

  static member addLoopCtxt cycleList ctxt =
    let main acc elem = Map.add elem.Head elem acc
    let lctxt = cycleList |> List.fold main Map.empty
    { ctxt with LoopCtxt = lctxt }

  static member setC2 env ctxt =
    let lctxt = LoopContext.setC2 env ctxt.LoopCtxt.[ctxt.CurBBLId]
    { ctxt with LoopCtxt = Map.add ctxt.CurBBLId lctxt ctxt.LoopCtxt }

  static member setC1 ctxt =
    let lctxt = LoopContext.setC1 ctxt.Env ctxt.LoopCtxt.[ctxt.CurBBLId]
    { ctxt with LoopCtxt = Map.add ctxt.CurBBLId lctxt ctxt.LoopCtxt }

  static member setJmpFlag edge ctxt =
    { ctxt with JmpFlag = edge }

  static member setFunCtxt fctxt ctxt =
    { ctxt with FunCtxt = fctxt }

  static member addALocs env ctxt =
    let getALocs acc k v = List.append [k] acc
    let aLocs = env |> Map.fold getALocs List.empty
    { ctxt with ALocs = List.append aLocs ctxt.ALocs |> List.distinct }

  static member setLoopCond value ctxt =
    { ctxt with LoopCond = value }

  static member addCFG cfg ctxt =
    if cfg = [] then { ctxt with CFGList = [] }
    else { ctxt with CFGList = List.append cfg ctxt.CFGList }

  static member popCFG ctxt =
    let cfg = List.head ctxt.CFGList
    let cfgList = List.tail ctxt.CFGList
    cfg, { ctxt with CFGList = cfgList }

  static member mergeBBL bblList ctxt =
    let a = Map (Seq.concat [ (Map.toSeq bblList) ; (Map.toSeq ctxt.BBL) ] )
    { ctxt with BBL = a }

  static member addPaths ctxt =
    { ctxt with paths = ctxt.paths + 1 }

