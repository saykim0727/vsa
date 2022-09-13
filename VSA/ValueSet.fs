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

open System.Collections.Generic

open B2R2

[<AutoOpen>]
module internal ValueSetHelper =
  exception ValueSetTypeException
  exception ValueSetNotImplemented

  let opErr vs1 vs2 =
    failwithf "No operation for Value Set (%s %s)" (vs1.ToString ())
                                                   (vs2.ToString ())

/// 4.3 ValueSet Kind
/// We do not need single as it can be handled by Arb. This also embeds MemRgn
/// such as Global, AR_main, and so on described in 3.2 (AbsEnv).
/// TODO: merge Global to Arb
type ValueSetType =
  // 'Global' represents constants
  | Global of StridedInterval
  // 'string' represnts the name of memory region (e.g., function name)
  | Arb of Map<MemRgn, StridedInterval>
  | All   // This represents Top
  | None  // This represents Bottom

/// 3.2 This may represent Abstract Environment (AbsEnv)
type ValueSet = {
    Bits   : RegType
    VS : ValueSetType
  }
with
  override __.ToString () =
    match __.VS with
    | Global si -> sprintf "Global: %s" (si.ToString ())
    | Arb siMap ->
      let foldHelper accStr rgn si =
        let rgnStr = rgn.ToString ()
        let siStr = si.ToString ()
        sprintf "%s%s: %s, " accStr rgnStr siStr
      siMap |> Map.fold foldHelper ""
    | All -> "All"
    | None -> "None"
    |> sprintf "VS:I%s [ %s ]" (__.Bits.ToString ())

  /// Below represents abstract interpretation for the infix operators.
  static member (+) ((vs1: ValueSet), (vs2: ValueSet)) =
    ValueSet.add vs1 vs2

  static member (-) ((vs1: ValueSet), (vs2: ValueSet)) =
    ValueSet.sub vs1 vs2

  static member (~-) (vs1: ValueSet) =
    ValueSet.neg vs1

  static member (&&&) ((vs1: ValueSet), (vs2: ValueSet)) =
    ValueSet.band vs1 vs2

  static member (|||) ((vs1: ValueSet),(vs2: ValueSet)) =
    ValueSet.bor vs1 vs2

  static member (^^^) ((vs1: ValueSet), (vs2: ValueSet)) =
    ValueSet.bxor vs1 vs2

  [<CompiledName("Find")>]
  static member find vs (memRgn: MemRgn) =
    match vs.VS with
    | None -> StridedInterval.none vs.Bits
    | Global si ->
      if memRgn = MemRgn.Global then si
      else StridedInterval.none vs.Bits
    | Arb siMap ->
      match siMap.TryGetValue memRgn with
      | true, si -> si
      | false, _ -> StridedInterval.none vs.Bits
    | All -> StridedInterval.all vs.Bits

  [<CompiledName("isConst")>]
  static member isConst vs =
    let isConstSI si =
      match si.SI with
      | Value sival ->
        if StridedInterval.isConst sival then true
        else false
      | _ -> false
    match vs.VS with
    | Global si -> isConstSI si
    | Arb siMap ->
      let mapList = siMap |> Map.filter (fun key value -> isConstSI value)
      if Map.isEmpty mapList then false
      else true
    | _ -> false

  // For widening bits
  [<CompiledName("SetType")>]
  static member setType vs bits =
    match vs.VS with
    | None -> { vs with Bits = bits }
    | Global si ->
      { Bits = bits; VS = ValueSet.initVS (StridedInterval.setType si bits) }
    | Arb siMap ->
      let newSiMap =
        siMap |> Map.map (fun rgn si -> StridedInterval.setType si bits)
      { Bits = bits; VS = ValueSet.initVSMap newSiMap }
    | All -> { vs with Bits = bits; }

  [<CompiledName("GetType")>]
  static member getType (vs: ValueSet) = vs.Bits

  [<CompiledName("IsAll")>]
  static member isAll vs =
    match vs.VS with
    | All -> true
    | Global si -> StridedInterval.isAll si
    | Arb siMap ->
      // TODO : Consider many case? because path-sensitive has only one value
      siMap |> Map.fold (fun acc mem si -> StridedInterval.isAll si) false
    | _ -> false

  [<CompiledName("IsNone")>]
  static member isNone (vs: ValueSet) =
    match vs.VS with
    | None -> true
    | Global si -> StridedInterval.isNone si
    | Arb siMap ->
      // TODO : Consider many case? because path-sensitive has only one value
      siMap |> Map.fold (fun acc mem si -> StridedInterval.isNone si) false
    | All -> false

  [<CompiledName("IsGlobal")>]
  static member isGlobal (siMap: Map<MemRgn, StridedInterval>) =
    if siMap.Count = 1 && siMap.ContainsKey MemRgn.Global then true
    else false

  [<CompiledName("HasGlobal")>]
  static member hasGlobal (siMap: Map<MemRgn, StridedInterval>) =
    if siMap.ContainsKey MemRgn.Global then true
    else false

  // Just return ValueSet for relOpEQ operation
  [<CompiledName("init")>]
  static member init vs = vs

  // TODO: this function should be modified if we merge Global to Arb
  [<CompiledName("initVS")>]
  static member initVS (si: StridedInterval) = Global (si)

  [<CompiledName("initVSMap")>]
  static member initVSMap siMap =
    let newSiMap =
      Map.filter (fun rgn si -> not (StridedInterval.isNone si)) siMap
    if Map.isEmpty newSiMap then None
    elif ValueSet.isGlobal newSiMap then Global (newSiMap.[MemRgn.Global])
    else
      let checkAll accBool rgn si =
        accBool && StridedInterval.isAll si
      if newSiMap |> Map.fold checkAll true then All
      else Arb (newSiMap)

  [<CompiledName("All")>]
  static member all bits = { Bits = bits; VS = All }

  [<CompiledName("None")>]
  static member none bits = { Bits = bits; VS = None }

  static member getConst vs =
    match vs.VS with
    | None -> Map.empty
    | Global si -> Map.add MemRgn.Global (StridedInterval.getConst si) Map.empty
    | Arb siMap -> Map.map (fun rgn si -> StridedInterval.getConst si) siMap
    | All -> raise ValueSetTypeException

  static member one bits =
    { Bits = bits; VS = Global (StridedInterval.one bits) }

  static member zero bits =
    { Bits = bits; VS = Global (StridedInterval.zero bits) }

  static member zeroMemRgn bits (memRgn: MemRgn) =
    match memRgn with
    | MemRgn.Global -> ValueSet.zero bits
    | _ ->
      let siMap = Map.add memRgn (StridedInterval.zero bits) Map.empty
      { Bits = bits; VS = ValueSet.initVSMap siMap }

  static member True = ValueSet.one 1<rt>

  static member False = ValueSet.zero 1<rt>

  static member Maybe =
    { Bits = 1<rt>; VS = Global (StridedInterval.all 1<rt>) }

  [<CompiledName("Concrete")>]
  static member concrete (vs: ValueSet) =
    match vs.VS with
    | None -> Map.empty
    | Global si -> Map.add MemRgn.Global (StridedInterval.concrete si) Map.empty
    | Arb siMap -> Map.map (fun rgn si -> StridedInterval.concrete si) siMap
    | All -> raise ValueSetTypeException

  static member ofBV bv =
    let bits = BitVector.getType bv
    let si = StridedInterval.ofBV bv
    { Bits = bits; VS = ValueSet.initVS si }

  static member ofBVMemRgn bv (memRgn: MemRgn) =
    match memRgn with
    | MemRgn.Global -> ValueSet.ofBV bv
    | _ ->
      let siMap = Map.empty |> Map.add memRgn (StridedInterval.ofBV bv)
      { Bits = BitVector.getType bv; VS = ValueSet.initVSMap siMap }

  static member ofSIMemRgn (si: StridedInterval) (memRgn: MemRgn) =
    let bits = StridedInterval.getType si
    match memRgn with
    | MemRgn.Global -> { Bits = bits; VS = ValueSet.initVS si }
    | _ ->
      let siMap = Map.empty |> Map.add memRgn si
      { Bits = bits; VS = ValueSet.initVSMap siMap }

  static member getMemRgn vs =
    match vs.VS with
    | Global si -> MemRgn.Global
    | Arb siMap -> Map.fold (fun a k v -> k) MemRgn.Global siMap
    | _ -> MemRgn.Global

  // TODO : Consider Arb simap's memrgn? This code just union all memrgn si
  static member toSI vs =
    match vs.VS with
    | Global si -> si
    | Arb siMap ->
      let none = StridedInterval.none vs.Bits
      siMap |> Map.fold (fun acc rgn si -> StridedInterval.union acc si) none
    | All -> StridedInterval.all vs.Bits
    | None -> StridedInterval.none vs.Bits

  static member vop op vs1 vs2 =
    match vs1.VS, vs2.VS with
    | None, _
    | _, None -> raise ValueSetTypeException
    | Global si1, Global si2 -> { vs1 with VS = ValueSet.initVS (op si1 si2) }
    // TODO: check if we need to handle Global differently.
//    | Global si1, Arb siMap
//    | Arb siMap, Global si1 -> raise ValueSetNotImplemented
    | _ , _ -> { vs1 with VS = All }

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 4.3.1 Addition
  /// We merged Single and Arb (Arb) as their behavior is the same. Constant
  /// should be transformed to Global ValueSet and added using this method.
  [<CompiledName("Add")>]
  static member add vs1 vs2 =
    match vs1.VS, vs2.VS with
    | None, _
    | _, None -> { vs1 with VS = None }
    | Global si1, Global si2 -> { vs1 with VS = ValueSet.initVS (si1 + si2) }
    | Global si1, Arb siMap
    | Arb siMap, Global si1 ->
      let newSiMap = siMap |> Map.map (fun rgn si -> (si + si1))
      { vs1 with VS = ValueSet.initVSMap newSiMap }
    | _ , _ -> { vs1 with VS = All }

  /// Unary minus of ValueSet
  [<CompiledName("Neg")>]
  static member neg vs =
    match vs.VS with
    | None -> raise ValueSetTypeException
    | Global si -> { vs with VS = ValueSet.initVS (-si) }
    | _ -> { vs with VS = All }

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 4.3.2 Subtraction
  [<CompiledName("Sub")>]
  static member sub vs1 vs2 = ValueSet.add vs1 (ValueSet.neg vs2)

  [<CompiledName("Mul")>]
  static member mul vs1 vs2 = ValueSet.vop (*) vs1 vs2

  [<CompiledName("Div")>]
  static member div vs1 vs2 = ValueSet.vop (|/|) vs1 vs2

  [<CompiledName("Sdiv")>]
  static member sdiv vs1 vs2 = ValueSet.vop (/) vs1 vs2

  [<CompiledName("Modulo")>]
  static member modulo vs1 vs2 = ValueSet.vop (|%|) vs1 vs2

  [<CompiledName("Smodulo")>]
  static member smodulo vs1 vs2 = ValueSet.vop (%) vs1 vs2

  [<CompiledName("Shr")>]
  static member shr vs1 vs2 = ValueSet.vop StridedInterval.shr vs1 vs2

  [<CompiledName("Shl")>]
  static member shl vs1 vs2 = ValueSet.vop StridedInterval.shl vs1 vs2

  [<CompiledName("Sar")>]
  static member sar vs1 vs2 = ValueSet.vop StridedInterval.sar vs1 vs2

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 4.3.3 Bitwise And, Or, Xor
  static member bop op vs1 vs2 id annihilator =
    match vs1.VS, vs2.VS with
    | None, _
    | _, None -> raise ValueSetTypeException
    | Global si1, Global si2 ->
      { vs1 with VS = ValueSet.initVS (op si1 si2) }
    | Global si1, _ ->
      if vs1.VS = id then vs2
      elif vs1.VS = annihilator then { vs2 with VS = annihilator }
      else { vs2 with VS = All }
    | _, Global si1 ->
      if vs2.VS = id then vs1
      elif vs2.VS = annihilator then { vs1 with VS = annihilator }
      else { vs1 with VS = All }
    | _ -> { vs1 with VS = All }

  [<CompiledName("BitwiseAnd")>]
  static member band vs1 vs2 =
    let bits = vs1.Bits
    let id = Global -(StridedInterval.one bits)
    let annihilator = Global (StridedInterval.zero bits)
    ValueSet.bop (&&&) vs1 vs2 id annihilator

  [<CompiledName("BitwiseOr")>]
  static member bor vs1 vs2 =
    let bits = vs1.Bits
    let id = Global (StridedInterval.zero bits)
    let annihilator = Global -(StridedInterval.one bits)
    ValueSet.bop (|||) vs1 vs2 id annihilator

  [<CompiledName("BitwiseXor")>]
  static member bxor vs1 vs2 =
    let bits = vs1.Bits
    let id = Global (StridedInterval.zero bits)
    let annihilator = All // This should not be used
    ValueSet.bop (^^^) vs1 vs2 id annihilator

  [<CompiledName("BitwiseNot")>]
  static member bnot vs =
    match vs.VS with
    | None -> raise ValueSetTypeException
    | Global si -> { vs with VS = ValueSet.initVS (~~~si) }
    | _ -> { vs with VS = All }

  static member containsSi (map: Map<MemRgn, StridedInterval>)
                           (rgn: MemRgn) (si1: StridedInterval) =
    match map.TryGetValue rgn with
    | true, si2 -> StridedInterval.contains si2 si1
    | false, _ -> false

  /// https://people.eng.unimelb.edu.au/pstuckey/papers/toplas15.pdf
  /// 3.2. Ordering wrapped intervals
  [<CompiledName("Contains")>]
  static member contains vs1 vs2 =
    // consider moving equal check in each match condition to improve the
    // performance.
    if vs1 = vs2 then true
    else
      match vs1.VS, vs2.VS with
      | _, None -> true
      | All, _ -> true
      | _, All -> false
      | None, _ -> false
      | Global si1, Arb siMap -> false
      | Global si1, Global si2 -> StridedInterval.contains si1 si2
      | Arb siMap, Global si1 -> ValueSet.containsSi siMap MemRgn.Global si1
      | Arb siMap1, Arb siMap2 ->
        let foldHelper accBool rgn si =
          accBool && ValueSet.containsSi siMap1 rgn si
        siMap2 |> Map.fold foldHelper true

  [<CompiledName("ContainsMemRgnBV")>]
  static member containsMemRgnBV vs rgn bv =
    let si1 = StridedInterval.ofBV bv
    match vs.VS with
    | None -> false
    | All -> true
    | Global si2 -> StridedInterval.contains si2 si1
    | Arb siMap -> ValueSet.containsSi siMap rgn si1

  /// Meet operation for ValueSet. Please check StridedInterval.intersection for
  /// details.
  [<CompiledName("Intersection")>]
  static member intersection vs1 vs2 =
    let intersectionSi (accMap: Map<MemRgn, StridedInterval>)
                       (rgn: MemRgn) (si1: StridedInterval) =
      let newSi =
        match accMap.TryGetValue rgn with
        | true, si2 -> StridedInterval.intersection si2 si1
        | false, _ -> StridedInterval.none si1.Bits
      accMap |> Map.add rgn newSi
    match vs1.VS, vs2.VS with
    | None, _ -> vs1
    | _, None -> vs2
    | All, _ -> vs2
    | _ , All -> vs1
    | Global si1, Global si2 ->
      { vs1 with VS = ValueSet.initVS (StridedInterval.intersection si1 si2) }
    | Global _, Arb siMap
    | Arb siMap, Global _ ->
      let si1 = ValueSet.find vs1 MemRgn.Global
      let si2 = ValueSet.find vs2 MemRgn.Global
      { vs1 with VS = ValueSet.initVS (StridedInterval.intersection si1 si2) }
    // Because we do not change the value, we can compute component-wise value.
    | Arb siMap1, Arb siMap2 ->
      let newSiMap = siMap2 |> Map.fold intersectionSi Map.empty
      { vs1 with VS = ValueSet.initVSMap newSiMap }

  /// Join operation for ValueSet. Please check StridedInterval.union for
  /// details.
  [<CompiledName("Union")>]
  static member union vs1 vs2 =
    let unionSi (accMap: Map<MemRgn, StridedInterval>)
                (rgn: MemRgn) (si1: StridedInterval) =
      let newSi =
        match accMap.TryGetValue rgn with
        | true, si2 -> StridedInterval.union si2 si1
        | false, _ -> si1
      accMap |> Map.add rgn newSi
    match vs1.VS, vs2.VS with
    | All, _ -> vs1
    | _ , All -> vs2
    | None, _ -> vs2
    | _, None -> vs1
    | Global si1, Global si2 ->
      { vs1 with VS = ValueSet.initVS (StridedInterval.union si1 si2) }
    | Global si1, Arb siMap
    | Arb siMap, Global si1 ->
      let newSiMap = unionSi siMap MemRgn.Global si1
      { vs1 with VS = ValueSet.initVSMap newSiMap }
    // Because we do not change the value, we can compute component-wise value.
    | Arb siMap1, Arb siMap2 ->
      let newSiMap = siMap2 |> Map.fold unionSi siMap1
      { vs1 with VS = ValueSet.initVSMap newSiMap }

  /// Widen operation for ValueSet. Please check StridedInterval.widen for
  /// details.
  [<CompiledName("Widen")>]
  static member widen vs1 vs2 =
    let widenSi (accMap: Map<MemRgn, StridedInterval>)
                (rgn: MemRgn) (si1: StridedInterval) =
      let newSi =
        match accMap.TryGetValue rgn with
        | true, si2 -> StridedInterval.widen si2 si1
        | false, _ -> si1
      accMap |> Map.add rgn newSi
    match vs1.VS, vs2.VS with
    | All, _ -> vs1
    | _, All -> vs2
    | None, _ -> vs2
    | _, None -> vs1
    | Global si1, Global si2 ->
      { vs1 with VS = ValueSet.initVS (StridedInterval.widen si1 si2 ) }
    | Global si1, Arb siMap ->
      let newSiMap =
        let si2 = ValueSet.find vs2 MemRgn.Global
        siMap |> Map.add MemRgn.Global (StridedInterval.widen si1 si2 )
      { vs1 with VS = ValueSet.initVSMap newSiMap }
    | Arb siMap, Global si1 ->
      let newSiMap =
        let si2 = ValueSet.find vs1 MemRgn.Global
        siMap |> Map.add MemRgn.Global (StridedInterval.widen si2 si1 )
      { vs1 with VS = ValueSet.initVSMap newSiMap }
    | Arb siMap1, Arb siMap2 ->
      let newSiMap = siMap2 |> Map.fold widenSi siMap1
      { vs1 with VS = ValueSet.initVSMap newSiMap }

  [<CompiledName("Narrow")>]
  static member narrow vs1 vs2 =
    let narrowSi (accMap: Map<MemRgn, StridedInterval>)
                (rgn: MemRgn) (si1: StridedInterval) =
      let newSi =
        match accMap.TryGetValue rgn with
        | true, si2 -> StridedInterval.narrow si2 si1
        | false, _ -> si1
      accMap |> Map.add rgn newSi
    match vs1.VS, vs2.VS with
    | All, _ -> vs2
    | _, All -> vs1
    | None, _ -> vs2
    | _, None -> vs1
    | Global si1, Global si2 ->
      { vs1 with VS = ValueSet.initVS (StridedInterval.narrow si1 si2 ) }
    | Global si1, Arb siMap ->
      let newSiMap =
        let si2 = ValueSet.find vs2 MemRgn.Global
        siMap |> Map.add MemRgn.Global (StridedInterval.narrow si1 si2 )
      { vs1 with VS = ValueSet.initVSMap newSiMap }
    | Arb siMap, Global si1 ->
      let newSiMap =
        let si2 = ValueSet.find vs1 MemRgn.Global
        siMap |> Map.add MemRgn.Global (StridedInterval.narrow si2 si1 )
      { vs1 with VS = ValueSet.initVSMap newSiMap }
    | Arb siMap1, Arb siMap2 ->
      let newSiMap = siMap2 |> Map.fold narrowSi siMap1
      { vs1 with VS = ValueSet.initVSMap newSiMap }

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 3.1 Value-Set
  /// TODO: check if we can use widen operation for this
  [<CompiledName("RemoveLowerBounds")>]
  static member removeLowerBounds vs =
    match vs.VS with
    | None -> raise ValueSetTypeException
    | Global si ->
      { vs with VS = ValueSet.initVS (StridedInterval.removeLowerBounds si) }
    | Arb siMap ->
      let removeHelper rgn si = StridedInterval.removeLowerBounds si
      let newSiMap = siMap |> Map.map removeHelper
      { vs with VS = ValueSet.initVSMap newSiMap }
    | All -> vs

  /// https://research.cs.wisc.edu/wpis/papers/balakrishnan_thesis.pdf
  /// 3.1 Value-Set
  /// TODO: check if we can use widen operation for this

  [<CompiledName("RemoveUpperBounds")>]
  static member removeUpperBounds vs =
    match vs.VS with
    | None -> raise ValueSetTypeException
    | Global si ->
      { vs with VS = ValueSet.initVS (StridedInterval.removeUpperBounds si) }
    | Arb siMap ->
      let removeHelper rgn si = StridedInterval.removeUpperBounds si
      let newSiMap = siMap |> Map.map removeHelper
      { vs with VS = ValueSet.initVSMap newSiMap }
    | All -> vs

  /// Below is helper for CutLowerBounds and CutUpperBounds
  [<CompiledName("CutBounds")>]
  static member cutBounds op vs =
    let one = StridedInterval.one vs.Bits
    match vs.VS with
    | None -> raise ValueSetTypeException
    | Global si ->
      { vs with VS = ValueSet.initVS (op si one) }
    | Arb siMap ->
      let newSiMap = siMap |> Map.map (fun rgn si -> (op si one))
      { vs with VS = ValueSet.initVSMap newSiMap }
    // We do not know how to handle All here ...
    | All -> raise ValueSetNotImplemented

  /// Narrow lowerbound by one (+1). Currently, we only consider integer range.
  /// This is used for lt gt comparison.
  [<CompiledName("CutLowerBounds")>]
  static member cutLowerBounds vs =
    ValueSet.cutBounds (+) vs

  /// Narrow upperbound by one (-1). Currently, we only consider integer range.
  /// This is used for lt gt comparison.
  [<CompiledName("CutUpperBounds")>]
  static member cutUpperBounds vs =
    ValueSet.cutBounds (-) vs

  /// This function is only for constants in RelOpType operation.
  /// TODO: check if we can use widen operation for this
  [<CompiledName("SetOtherRgnAll")>]
  static member setOtherRgnAll vs1 vs2 =
    let mapHelper (rgn: MemRgn) si =
      match rgn with
      | MemRgn.Global -> si
      | _ -> StridedInterval.all vs1.Bits
    match vs1.VS, vs2.VS with
    | Global si, Arb siMap ->
      let newSiMap = siMap |> Map.map mapHelper
      { vs1 with VS = ValueSet.initVSMap newSiMap }
    // if vs1 is not Global, there must be a problem.
    | _ -> failwithf "makeTop: this never happens: %A <- %A" vs1 vs2

  // TODO : Add unittest in ValueSetTests
  // This only handles extension.
  [<CompiledName("Cast")>]
  static member cast (vs: ValueSet) bits =
    if vs.Bits = bits then vs
    else
      match vs.VS with
      | None -> { vs with Bits = bits }
      | All -> { vs with Bits = bits }
      | Global si ->
        if ValueSet.isAll vs then
          { Bits = bits;
            VS = ValueSet.initVS (StridedInterval.all bits) }
        else
          { Bits = bits;
            VS = ValueSet.initVS (StridedInterval.cast si bits) }
      | Arb siMap ->
        let newSiMap =
          siMap |> Map.map (fun rgn si -> StridedInterval.cast si bits)
        { Bits = bits; VS = ValueSet.initVSMap newSiMap }

  [<CompiledName("Sext")>]
  static member sext vs bits =
    if vs.Bits = bits then vs
    else
      match vs.VS with
      | None -> { vs with Bits = bits }
      | All -> { vs with Bits = bits }
      | Global si ->
        if ValueSet.isAll vs then
          { Bits = bits;
            VS = ValueSet.initVS (StridedInterval.all bits) }
        else
          { Bits = bits;
            VS = ValueSet.initVS (StridedInterval.sext si bits) }
      | Arb siMap ->
        let newSiMap =
          siMap |> Map.map (fun rgn si -> StridedInterval.sext si bits)
        { Bits = bits; VS = ValueSet.initVSMap newSiMap }

  [<CompiledName("Zext")>]
  static member zext vs bits = ValueSet.cast vs bits

  [<CompiledName("Extract")>]
  static member extract vs bits pos =
    let bit1, bit2 = vs.Bits |> int64, bits |> int64
    match vs.VS with
    | None -> failwithf "None"
    | All -> { vs with Bits = bits }
    | Global si ->
      if ValueSet.isAll vs then
        { Bits = bits;
          VS = ValueSet.initVS (StridedInterval.all bits) }
      else
        { Bits = bits;
        VS = ValueSet.initVS (StridedInterval.extract si bits pos) }
    | Arb siMap ->
      // TODO: check if we need to handle Global differently.
      let newSiMap =
        siMap |> Map.map (fun rgn si -> StridedInterval.all vs.Bits)
      { Bits = bits; VS = ValueSet.initVSMap newSiMap }

  [<CompiledName("Concat")>]
  static member concat vs1 vs2 =
    match vs1.VS, vs2.VS with
    | None, _
    | _, None -> raise ValueSetTypeException
    | Global si1, Global si2 ->
      { vs1 with VS = ValueSet.initVS (StridedInterval.concat si1 si2) }
    | _ , _ -> { Bits = (vs1.Bits + vs2.Bits); VS = All }

  [<CompiledName("App")>]
  static member app vs1 vs2 =
    // TODO: implement ValueSet.app
    failwithf "%A %A" vs1 vs2

  [<CompiledName("Cons")>]
  static member cons vs1 vs2 =
    // TODO: implement ValueSet.cons
    failwithf "%A %A" vs1 vs2

  static member comp op vs1 vs2 =
    let foldHelper (targetMap: Map<MemRgn, StridedInterval>)
                   (accSi: StridedInterval)
                   (rgn: MemRgn) (si2: StridedInterval) =
      match targetMap.TryGetValue rgn with
      | true, si1 -> StridedInterval.union accSi (op si1 si2)
      | _ -> raise ValueSetTypeException
    let noneSi = StridedInterval.none vs1.Bits
    match vs1.VS, vs2.VS with
    | None, _
    | _, None -> raise ValueSetTypeException
    | All, _  -> ValueSet.Maybe
    | _, All -> ValueSet.Maybe
    | Global si1, Global si2 ->
      { Bits = 1<rt>; VS = ValueSet.initVS (op si1 si2) }
    | Arb siMap, Global si2 ->
      let newSi = siMap |> Map.fold (fun accSi rgn si1 ->
        StridedInterval.union accSi (op si1 si2)) noneSi
      { Bits = 1<rt>; VS = ValueSet.initVS newSi }
    | Global si1, Arb siMap ->
      let newSi = siMap |> Map.fold (fun accSi rgn si2 ->
        StridedInterval.union accSi (op si1 si2)) noneSi
      { Bits = 1<rt>; VS = ValueSet.initVS newSi }
    | Arb siMap1, Arb siMap2 ->
      let newSi =
        siMap2 |> Map.fold (foldHelper siMap1) noneSi
      { Bits = 1<rt>; VS = ValueSet.initVS newSi }

  [<CompiledName("EQ")>]
  static member eq vs1 vs2 =
    let all = ValueSet.all vs1.Bits
    if vs1 = vs2 then ValueSet.True
    elif vs1 = all || vs2 = all || ValueSet.contains vs1 vs2 ||
         ValueSet.contains vs2 vs1 then ValueSet.Maybe
    else ValueSet.False

  [<CompiledName("NEQ")>]
  static member neq vs1 vs2 =
    let all = ValueSet.all vs1.Bits
    if vs1 = vs2 then ValueSet.False
    elif vs1 = all || vs2 = all || ValueSet.contains vs1 vs2 ||
         ValueSet.contains vs2 vs1 then ValueSet.Maybe
    else ValueSet.True

  [<CompiledName("LT")>]
  static member lt vs1 vs2 = ValueSet.comp StridedInterval.lt vs1 vs2

  [<CompiledName("LE")>]
  static member le vs1 vs2 = ValueSet.comp StridedInterval.le vs1 vs2

  [<CompiledName("GT")>]
  static member gt vs1 vs2 = ValueSet.lt vs2 vs1

  [<CompiledName("GE")>]
  static member ge vs1 vs2 = ValueSet.le vs2 vs1

  [<CompiledName("SLT")>]
  static member slt vs1 vs2 = ValueSet.comp StridedInterval.slt vs1 vs2

  [<CompiledName("SLE")>]
  static member sle vs1 vs2 = ValueSet.comp StridedInterval.sle vs1 vs2

  [<CompiledName("SGT")>]
  static member sgt vs1 vs2 = ValueSet.slt vs2 vs1

  [<CompiledName("SGE")>]
  static member sge vs1 vs2 = ValueSet.sle vs2 vs1
