open B2R2
open B2R2.FrontEnd
open B2R2.BinFile
open B2R2.BinGraph
open B2R2.VSA

open FSharp.Core

[<EntryPoint>]
let main argv =
  let fname = argv.[0]
  let isa = ISA.Init Arch.IntelX86 Endian.Little
  let hdl = BinHandler.Init (isa, fname)
  let ess = BinEssence.Init hdl
  let funcs = BinaryApparatus.getFunctionAddrs ess.BinaryApparatus |> Seq.toList
  Analysis.analyzeVSA ess hdl funcs

  //TODO : choice lens SimpleDiGraph
  //let ctxt = List.fold aaa ctxt


//  let callGraph = SimpleDiGraph ()
//  let _ = CFGUtils.buildCallGraph handle funcs_ callGraph
  //let _ = NoReturn.noReturnAnalysis handle callGraph
//  let root = callGraph.GetRoot()
//  let funcs = callGraph.GetVertices ()
//  let func = funcs |> Set.filter (fun elem -> "main" = elem.VData.Name)
//             |> Set.toList |> List.head
//  Analysis.analyzeVSA func funcs_
  0
