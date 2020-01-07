namespace B2R2.ABI

open B2R2
open B2R2.BinIR
open B2R2.BinIR.LowUIR
open B2R2.FrontEnd.Intel

type IABI =
  abstract member WordSize             : WordSize
  abstract member ULongMax             : uint64
  abstract member Endian               : Endian
  abstract member IsFP                 : RegisterID -> bool
  abstract member SyscallRetRegister   : RegisterID
  abstract member StackPtrRegister     : RegisterID
  abstract member StackBasePtrRegister : RegisterID
  abstract member GetSyscallArgument   : int -> RegisterID
  abstract member GetFunctionArgument  : int -> Expr

module X86_64 =
  type private ABI () =
    interface IABI with
      member __.WordSize = WordSize.Bit64
      member __.ULongMax = 0xFFFFFFFFFFFFFFFFUL
      member __.Endian = Endian.Little

      member __.IsFP x =
        Register.Kind.YMM = Register.getKind (Register.ofRegID x)

      member __.SyscallRetRegister = Register.toRegID Register.RAX

      member __.GetSyscallArgument idx =
        match idx with
        | 1 -> Register.toRegID Register.RDI
        | 2 -> Register.toRegID Register.RSI
        | 3 -> Register.toRegID Register.RDX
        | _ as e -> failwithf "Invalid index: %d" e

      member __.StackPtrRegister = Register.toRegID Register.RSP

      member __.StackBasePtrRegister = Register.toRegID Register.RBP

      member __.GetFunctionArgument n = failwith "todo"

  let abi = new ABI () :> IABI

