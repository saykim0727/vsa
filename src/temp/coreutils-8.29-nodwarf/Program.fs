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
  let handle = BinHandler.Init (isa, fname)
  let builder = CFGBuilder ()
  let funcs = CFGUtils.construct handle builder None
  let funcs_ = CFGUtils.analCalls funcs
  let callGraph = SimpleDiGraph ()
  let _ = CFGUtils.buildCallGraph handle funcs_ callGraph
  //let _ = NoReturn.noReturnAnalysis handle callGraph
  let root = callGraph.GetRoot()
  let funcs = callGraph.GetVertices ()
  let func = funcs |> Set.filter (fun elem -> "main" = elem.VData.Name)
             |> Set.toList |> List.head
  Analysis.analyzeVSA func funcs_
  0
  //Analysis.analyzeVSA func funcs_
