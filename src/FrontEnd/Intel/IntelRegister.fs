(*
  B2R2 - the Next-Generation Reversing Platform

  Author: Sang Kil Cha <sangkilc@kaist.ac.kr>
          Seung Il Jung <sijung@kaist.ac.kr>
          Minkyu Jung <hestati@kaist.ac.kr>

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

namespace B2R2.FrontEnd.Intel

open B2R2
open System.Runtime.CompilerServices

[<assembly: InternalsVisibleTo("B2R2.FrontEnd.Tests")>]
do ()

/// This exception occurs when an UnknownReg is explicitly used. This exception
/// should not happen in general.
exception UnknownRegException

/// <summary>
/// Registers for x86 (and x86-64).<para/>
///
/// Internally, a Register is represented with an integer (we use only 12 bits).
/// The most significant 4 bits (from 8th to 11th bits) represent the register
/// kind, and the reset of 8 bits are used to represent a register ID. There are
/// currently 13 kinds of registers including GP, FPU, MMX, etc. <para/>
/// <code>
/// 11 10 09 08 07 06 05 04 03 02 01 00 (bit position)
/// +----------+----------------------+
/// | Kind     |  Register ID.        |
/// +----------+----------------------+
/// </code>
/// </summary>
type Register =
  /// Accumulator for operands and results data (64bit).
  | RAX = 0x0
  /// Pointer to data in the DS segment (64bit).
  | RBX = 0x1
  /// TCounter for string and loop operations (64bit).
  | RCX = 0x2
  /// I/O pointer (64bit).
  | RDX = 0x3
  /// Stack pointer (in the SS segment) (64bit).
  | RSP = 0x4
  /// Pointer to data on the stack (in the SS segment) (64bit).
  | RBP = 0x5
  /// Pointer to data in the segment pointed to by the DS register (64bit).
  | RSI = 0x6
  /// Pointer to data in the segment pointed to by the ES register (64bit).
  | RDI = 0x7
  /// Accumulator for operands and results data (32bit).
  | EAX = 0x8
  /// Pointer to data in the DS segment (32bit).
  | EBX = 0x9
  /// TCounter for string and loop operations (32bit).
  | ECX = 0xA
  /// I/O pointer (32bit).
  | EDX = 0xB
  /// Stack pointer (in the SS segment) (32bit).
  | ESP = 0xC
  /// Pointer to data on the stack (in the SS segment) (32bit).
  | EBP = 0xD
  /// Pointer to data in the segment pointed to by the DS register (32bit).
  | ESI = 0xE
  /// Pointer to data in the segment pointed to by the ES register (32bit).
  | EDI = 0xF
  /// General-Purpose Registers (lower 16bits EAX).
  | AX = 0x10
  /// General-Purpose Registers (lower 16bits EBX).
  | BX = 0x11
  /// General-Purpose Registers (lower 16bits ECX).
  | CX = 0x12
  /// General-Purpose Registers (lower 16bits EDX).
  | DX = 0x13
  /// General-Purpose Registers (lower 16bits ESP).
  | SP = 0x14
  /// General-Purpose Registers (lower 16bits EBP).
  | BP = 0x15
  /// General-Purpose Registers (lower 16bits ESI).
  | SI = 0x16
  /// General-Purpose Registers (lower 16bits EDI).
  | DI = 0x17
  /// General-Purpose Registers (lower 8bits AX).
  | AL = 0x18
  /// General-Purpose Registers (lower 8bits BX).
  | BL = 0x19
  /// General-Purpose Registers (lower 8bits CX).
  | CL = 0x1A
  /// General-Purpose Registers (lower 8bits DX).
  | DL = 0x1B
  /// General-Purpose Registers (Higher 8bits AX).
  | AH = 0x1C
  /// General-Purpose Registers (Higher 8bits BX).
  | BH = 0x1D
  /// General-Purpose Registers (Higher 8bits CX).
  | CH = 0x1E
  /// General-Purpose Registers (Higher 8bits DX).
  | DH = 0x1F
  /// General-Purpose Registers for 64bit Mode.
  | R8 = 0x20
  /// General-Purpose Registers for 64bit Mode.
  | R9 = 0x21
  /// General-Purpose Registers for 64bit Mode.
  | R10 = 0x22
  /// General-Purpose Registers for 64bit Mode.
  | R11 = 0x23
  /// General-Purpose Registers for 64bit Mode.
  | R12 = 0x24
  /// General-Purpose Registers for 64bit Mode.
  | R13 = 0x25
  /// General-Purpose Registers for 64bit Mode.
  | R14 = 0x26
  /// General-Purpose Registers for 64bit Mode.
  | R15 = 0x27
  /// General-Purpose Registers for 64bit Mode (Doubleword Register).
  | R8D = 0x28
  /// General-Purpose Registers for 64bit Mode (Doubleword Register).
  | R9D = 0x29
  /// General-Purpose Registers for 64bit Mode (Doubleword Register).
  | R10D = 0x2A
  /// General-Purpose Registers for 64bit Mode (Doubleword Register).
  | R11D = 0x2B
  /// General-Purpose Registers for 64bit Mode (Doubleword Register).
  | R12D = 0x2C
  /// General-Purpose Registers for 64bit Mode (Doubleword Register).
  | R13D = 0x2D
  /// General-Purpose Registers for 64bit Mode (Doubleword Register).
  | R14D = 0x2E
  /// General-Purpose Registers for 64bit Mode (Doubleword Register).
  | R15D = 0x2F
  /// General-Purpose Registers for 64bit Mode (Word Register).
  | R8W = 0x30
  /// General-Purpose Registers for 64bit Mode (Word Register).
  | R9W = 0x31
  /// General-Purpose Registers for 64bit Mode (Word Register).
  | R10W = 0x32
  /// General-Purpose Registers for 64bit Mode (Word Register).
  | R11W = 0x33
  /// General-Purpose Registers for 64bit Mode (Word Register).
  | R12W = 0x34
  /// General-Purpose Registers for 64bit Mode (Word Register).
  | R13W = 0x35
  /// General-Purpose Registers for 64bit Mode (Word Register).
  | R14W = 0x36
  /// General-Purpose Registers for 64bit Mode (Word Register).
  | R15W = 0x37
  /// General-Purpose Registers for 64bit Mode (Byte Register).
  | R8L = 0x38
  /// General-Purpose Registers for 64bit Mode (Byte Register).
  | R9L = 0x39
  /// General-Purpose Registers for 64bit Mode (Byte Register).
  | R10L = 0x3A
  /// General-Purpose Registers for 64bit Mode (Byte Register).
  | R11L = 0x3B
  /// General-Purpose Registers for 64bit Mode (Byte Register).
  | R12L = 0x3C
  /// General-Purpose Registers for 64bit Mode (Byte Register).
  | R13L = 0x3D
  /// General-Purpose Registers for 64bit Mode (Byte Register).
  | R14L = 0x3E
  /// General-Purpose Registers for 64bit Mode (Byte Register).
  | R15L = 0x3F
  /// General-Purpose Registers for 64bit Mode (Byte Register).
  | SPL = 0x40
  /// General-Purpose Registers for 64bit Mode (Byte Register).
  | BPL = 0x41
  /// General-Purpose Registers for 64bit Mode (Byte Register).
  | SIL = 0x42
  /// General-Purpose Registers for 64bit Mode (Byte Register).
  | DIL = 0x43
  /// Instruction Pointer (32Bit).
  | EIP = 0x44
  /// Instruction Pointer (64Bit).
  | RIP = 0x45
  /// x87 FPU registers.
  | ST0 = 0x100
  /// x87 FPU registers.
  | ST1 = 0x101
  /// x87 FPU registers.
  | ST2 = 0x102
  /// x87 FPU registers.
  | ST3 = 0x103
  /// x87 FPU registers.
  | ST4 = 0x104
  /// x87 FPU registers.
  | ST5 = 0x105
  /// x87 FPU registers.
  | ST6 = 0x106
  /// x87 FPU registers.
  | ST7 = 0x107
  /// MMX registers.
  | MM0 = 0x200
  /// MMX registers.
  | MM1 = 0x201
  /// MMX registers.
  | MM2 = 0x202
  /// MMX registers.
  | MM3 = 0x203
  /// MMX registers.
  | MM4 = 0x204
  /// MMX registers.
  | MM5 = 0x205
  /// MMX registers.
  | MM6 = 0x206
  /// MMX registers.
  | MM7 = 0x207
  /// XMM registers.
  | XMM0 = 0x30F
  /// XMM registers.
  | XMM1 = 0x30E
  /// XMM registers.
  | XMM2 = 0x30D
  /// XMM registers.
  | XMM3 = 0x30C
  /// XMM registers.
  | XMM4 = 0x30B
  /// XMM registers.
  | XMM5 = 0x30A
  /// XMM registers.
  | XMM6 = 0x309
  /// XMM registers.
  | XMM7 = 0x308
  /// XMM registers.
  | XMM8 = 0x307
  /// XMM registers.
  | XMM9 = 0x306
  /// XMM registers.
  | XMM10 = 0x305
  /// XMM registers.
  | XMM11 = 0x304
  /// XMM registers.
  | XMM12 = 0x303
  /// XMM registers.
  | XMM13 = 0x302
  /// XMM registers.
  | XMM14 = 0x301
  /// XMM registers.
  | XMM15 = 0x300
  /// 256-bit vector registers.
  | YMM0 = 0x40F
  /// 256-bit vector registers.
  | YMM1 = 0x40E
  /// 256-bit vector registers.
  | YMM2 = 0x40D
  /// 256-bit vector registers.
  | YMM3 = 0x40C
  /// 256-bit vector registers.
  | YMM4 = 0x40B
  /// 256-bit vector registers.
  | YMM5 = 0x40A
  /// 256-bit vector registers.
  | YMM6 = 0x409
  /// 256-bit vector registers.
  | YMM7 = 0x408
  /// 256-bit vector registers.
  | YMM8 = 0x407
  /// 256-bit vector registers.
  | YMM9 = 0x406
  /// 256-bit vector registers.
  | YMM10 = 0x405
  /// 256-bit vector registers.
  | YMM11 = 0x404
  /// 256-bit vector registers.
  | YMM12 = 0x403
  /// 256-bit vector registers.
  | YMM13 = 0x402
  /// 256-bit vector registers.
  | YMM14 = 0x401
  /// 256-bit vector registers.
  | YMM15 = 0x400
  /// 512-bit vector registers.
  | ZMM0 = 0x50F
  /// 512-bit vector registers.
  | ZMM1 = 0x50E
  /// 512-bit vector registers.
  | ZMM2 = 0x50D
  /// 512-bit vector registers.
  | ZMM3 = 0x50C
  /// 512-bit vector registers.
  | ZMM4 = 0x50B
  /// 512-bit vector registers.
  | ZMM5 = 0x50A
  /// 512-bit vector registers.
  | ZMM6 = 0x509
  /// 512-bit vector registers.
  | ZMM7 = 0x508
  /// 512-bit vector registers.
  | ZMM8 = 0x507
  /// 512-bit vector registers.
  | ZMM9 = 0x506
  /// 512-bit vector registers.
  | ZMM10 = 0x505
  /// 512-bit vector registers.
  | ZMM11 = 0x504
  /// 512-bit vector registers.
  | ZMM12 = 0x503
  /// 512-bit vector registers.
  | ZMM13 = 0x502
  /// 512-bit vector registers.
  | ZMM14 = 0x501
  /// 512-bit vector registers.
  | ZMM15 = 0x500
  /// 512-bit vector registers.
  | ES = 0x600
  /// 512-bit vector registers.
  | CS = 0x601
  /// Segment registers.
  | SS = 0x602
  /// Segment registers.
  | DS = 0x603
  /// Segment registers.
  | FS = 0x604
  /// Segment registers.
  | GS = 0x605
  /// ES.base.
  | ESBase = 0x700
  /// CS.base.
  | CSBase = 0x701
  /// SS.base.
  | SSBase = 0x702
  /// DS.base.
  | DSBase = 0x703
  /// FS.base.
  | FSBase = 0x704
  /// ES.base.
  | GSBase = 0x705
  /// Control registers.
  | CR0 = 0x800
  /// Control registers.
  | CR2 = 0x802
  /// Control registers.
  | CR3 = 0x803
  /// Control registers.
  | CR4 = 0x804
  /// Control registers.
  | CR8 = 0x808
  /// Debug registers.
  | DR0 = 0x900
  /// Debug registers.
  | DR1 = 0x901
  /// Debug registers.
  | DR2 = 0x902
  /// Debug registers.
  | DR3 = 0x903
  /// Debug registers.
  | DR6 = 0x906
  /// Debug registers.
  | DR7 = 0x907
  /// BND registers.
  | BND0 = 0xA00
  /// BND registers.
  | BND1 = 0xA01
  /// BND registers.
  | BND2 = 0xA02
  /// BND registers.
  | BND3 = 0xA03
  /// Overflow Flag in EFLAGS Register
  | OF = 0xB00
  /// Direction Flag in EFLAGS Register
  | DF = 0xB01
  /// Interrupt Enable Flag in EFLAGS Register
  | IF = 0xB02
  /// Trap Flag in EFLAGS Register
  | TF = 0xB03
  /// Sign Flag in EFLAGS Register
  | SF = 0xB04
  /// Zero Flag in EFLAGS Register
  | ZF = 0xB05
  /// Auxiliary Carry Flag in EFLAGS Register
  | AF = 0xB06
  /// Parity Flag in EFLAGS Register
  | PF = 0xB07
  /// Carry Flag in EFLAGS Register
  | CF = 0xB08
  /// C87 FPU Control Word.
  | FCW = 0xC00
  /// x87 FPU Status Word.
  | FSW = 0xC01
  /// x87 FPU Tag Word.
  | FTW = 0xC02
  /// x87 FPU Opcode.
  | FOP = 0xC03
  /// x87 FPU Instruction Pointer Offset.
  | FIP = 0xC04
  /// x87 FPU Instruction Pointer Selector.
  | FCS = 0xC05
  /// x87 FPU Data Pointer Offset.
  | FDP = 0xC06
  /// x87 FPU Data Pointer Selector.
  | FDS = 0xC07
  /// MXCSR Control and Status Register.
  | MXCSR = 0xC08
  /// MXCSR_MASK.
  | MXCSRMASK = 0xC09
  /// Protection-key features register.
  | PKRU = 0xC0A
  /// BND Register (lower 64bits BND0).
  | BND0A = 0xD80
  /// BND Register (Higher 64bits BND0).
  | BND0B = 0xD81
  /// BND Register (lower 64bits BND1).
  | BND1A = 0xD82
  /// BND Register (Higher 64bits BND1).
  | BND1B = 0xD83
  /// BND Register (lower 64bits BND2).
  | BND2A = 0xD84
  /// BND Register (Higher 64bits BND2).
  | BND2B = 0xD85
  /// BND Register (lower 64bits BND3).
  | BND3A = 0xD86
  /// BND Register (Higher 64bits BND3).
  | BND3B = 0xD87
  /// ZMM0A is the 1st 64-bit chunk of ZMM0.
  | ZMM0A = 0xD00
  /// ZMM0B is the 2nd 64-bit chunk of ZMM0.
  | ZMM0B = 0xD01
  /// ZMM0C is the 3rd 64-bit chunk of ZMM0.
  | ZMM0C = 0xD02
  /// ZMM0D is the 4th 64-bit chunk of ZMM0.
  | ZMM0D = 0xD03
  /// ZMM0E is the 5th 64-bit chunk of ZMM0.
  | ZMM0E = 0xD04
  /// ZMM0F is the 6th 64-bit chunk of ZMM0.
  | ZMM0F = 0xD05
  /// ZMM0G is the 7th 64-bit chunk of ZMM0.
  | ZMM0G = 0xD06
  /// ZMM0H is the 8th 64-bit chunk of ZMM0.
  | ZMM0H = 0xD07
  /// ZMM1A is the 1st 64-bit chunk of ZMM1.
  | ZMM1A = 0xD08
  /// ZMM1B is the 2nd 64-bit chunk of ZMM1.
  | ZMM1B = 0xD09
  /// ZMM1C is the 3rd 64-bit chunk of ZMM1.
  | ZMM1C = 0xD0A
  /// ZMM1D is the 4th 64-bit chunk of ZMM1.
  | ZMM1D = 0xD0B
  /// ZMM1E is the 5th 64-bit chunk of ZMM1.
  | ZMM1E = 0xD0C
  /// ZMM1F is the 6th 64-bit chunk of ZMM1.
  | ZMM1F = 0xD0D
  /// ZMM1G is the 7th 64-bit chunk of ZMM1.
  | ZMM1G = 0xD0E
  /// ZMM1H is the 8th 64-bit chunk of ZMM1.
  | ZMM1H = 0xD0F
  /// ZMM2A is the 1st 64-bit chunk of ZMM2.
  | ZMM2A = 0xD10
  /// ZMM2B is the 2nd 64-bit chunk of ZMM2.
  | ZMM2B = 0xD11
  /// ZMM2C is the 3rd 64-bit chunk of ZMM2.
  | ZMM2C = 0xD12
  /// ZMM2D is the 4th 64-bit chunk of ZMM2.
  | ZMM2D = 0xD13
  /// ZMM2E is the 5th 64-bit chunk of ZMM2.
  | ZMM2E = 0xD14
  /// ZMM2F is the 6th 64-bit chunk of ZMM2.
  | ZMM2F = 0xD15
  /// ZMM2G is the 7th 64-bit chunk of ZMM2.
  | ZMM2G = 0xD16
  /// ZMM2H is the 8th 64-bit chunk of ZMM2.
  | ZMM2H = 0xD17
  /// ZMM3A is the 1st 64-bit chunk of ZMM3.
  | ZMM3A = 0xD18
  /// ZMM3B is the 2nd 64-bit chunk of ZMM3.
  | ZMM3B = 0xD19
  /// ZMM3C is the 3rd 64-bit chunk of ZMM3.
  | ZMM3C = 0xD1A
  /// ZMM3D is the 4th 64-bit chunk of ZMM3.
  | ZMM3D = 0xD1B
  /// ZMM3E is the 5th 64-bit chunk of ZMM3.
  | ZMM3E = 0xD1C
  /// ZMM3F is the 6th 64-bit chunk of ZMM3.
  | ZMM3F = 0xD1D
  /// ZMM3G is the 7th 64-bit chunk of ZMM3.
  | ZMM3G = 0xD1E
  /// ZMM3H is the 8th 64-bit chunk of ZMM3.
  | ZMM3H = 0xD1F
  /// ZMM4A is the 1st 64-bit chunk of ZMM4.
  | ZMM4A = 0xD20
  /// ZMM4B is the 2nd 64-bit chunk of ZMM4.
  | ZMM4B = 0xD21
  /// ZMM4C is the 3rd 64-bit chunk of ZMM4.
  | ZMM4C = 0xD22
  /// ZMM4D is the 4th 64-bit chunk of ZMM4.
  | ZMM4D = 0xD23
  /// ZMM4E is the 5th 64-bit chunk of ZMM4.
  | ZMM4E = 0xD24
  /// ZMM4F is the 6th 64-bit chunk of ZMM4.
  | ZMM4F = 0xD25
  /// ZMM4G is the 7th 64-bit chunk of ZMM4.
  | ZMM4G = 0xD26
  /// ZMM4H is the 8th 64-bit chunk of ZMM4.
  | ZMM4H = 0xD27
  /// ZMM5A is the 1st 64-bit chunk of ZMM5.
  | ZMM5A = 0xD28
  /// ZMM5B is the 2nd 64-bit chunk of ZMM5.
  | ZMM5B = 0xD29
  /// ZMM5C is the 3rd 64-bit chunk of ZMM5.
  | ZMM5C = 0xD2A
  /// ZMM5D is the 4th 64-bit chunk of ZMM5.
  | ZMM5D = 0xD2B
  /// ZMM5E is the 5th 64-bit chunk of ZMM5.
  | ZMM5E = 0xD2C
  /// ZMM5F is the 6th 64-bit chunk of ZMM5.
  | ZMM5F = 0xD2D
  /// ZMM5G is the 7th 64-bit chunk of ZMM5.
  | ZMM5G = 0xD2E
  /// ZMM5H is the 8th 64-bit chunk of ZMM5.
  | ZMM5H = 0xD2F
  /// ZMM6A is the 1st 64-bit chunk of ZMM6.
  | ZMM6A = 0xD30
  /// ZMM6B is the 2nd 64-bit chunk of ZMM6.
  | ZMM6B = 0xD31
  /// ZMM6C is the 3rd 64-bit chunk of ZMM6.
  | ZMM6C = 0xD32
  /// ZMM6D is the 4th 64-bit chunk of ZMM6.
  | ZMM6D = 0xD33
  /// ZMM6E is the 5th 64-bit chunk of ZMM6.
  | ZMM6E = 0xD34
  /// ZMM6F is the 6th 64-bit chunk of ZMM6.
  | ZMM6F = 0xD35
  /// ZMM6G is the 7th 64-bit chunk of ZMM6.
  | ZMM6G = 0xD36
  /// ZMM6H is the 8th 64-bit chunk of ZMM6.
  | ZMM6H = 0xD37
  /// ZMM7A is the 1st 64-bit chunk of ZMM7.
  | ZMM7A = 0xD38
  /// ZMM7B is the 2nd 64-bit chunk of ZMM7.
  | ZMM7B = 0xD39
  /// ZMM7C is the 3rd 64-bit chunk of ZMM7.
  | ZMM7C = 0xD3A
  /// ZMM7D is the 4th 64-bit chunk of ZMM7.
  | ZMM7D = 0xD3B
  /// ZMM7E is the 5th 64-bit chunk of ZMM7.
  | ZMM7E = 0xD3C
  /// ZMM7F is the 6th 64-bit chunk of ZMM7.
  | ZMM7F = 0xD3D
  /// ZMM7G is the 7th 64-bit chunk of ZMM7.
  | ZMM7G = 0xD3E
  /// ZMM7H is the 8th 64-bit chunk of ZMM7.
  | ZMM7H = 0xD3F
  /// ZMM8A is the 1st 64-bit chunk of ZMM8.
  | ZMM8A = 0xD40
  /// ZMM8B is the 2nd 64-bit chunk of ZMM8.
  | ZMM8B = 0xD41
  /// ZMM8C is the 3rd 64-bit chunk of ZMM8.
  | ZMM8C = 0xD42
  /// ZMM8D is the 4th 64-bit chunk of ZMM8.
  | ZMM8D = 0xD43
  /// ZMM8E is the 5th 64-bit chunk of ZMM8.
  | ZMM8E = 0xD44
  /// ZMM8F is the 6th 64-bit chunk of ZMM8.
  | ZMM8F = 0xD45
  /// ZMM8G is the 7th 64-bit chunk of ZMM8.
  | ZMM8G = 0xD46
  /// ZMM8H is the 8th 64-bit chunk of ZMM8.
  | ZMM8H = 0xD47
  /// ZMM9A is the 1st 64-bit chunk of ZMM9.
  | ZMM9A = 0xD48
  /// ZMM9B is the 2nd 64-bit chunk of ZMM9.
  | ZMM9B = 0xD49
  /// ZMM9C is the 3rd 64-bit chunk of ZMM9.
  | ZMM9C = 0xD4A
  /// ZMM9D is the 4th 64-bit chunk of ZMM9.
  | ZMM9D = 0xD4B
  /// ZMM9E is the 5th 64-bit chunk of ZMM9.
  | ZMM9E = 0xD4C
  /// ZMM9F is the 6th 64-bit chunk of ZMM9.
  | ZMM9F = 0xD4D
  /// ZMM9G is the 7th 64-bit chunk of ZMM9.
  | ZMM9G = 0xD4E
  /// ZMM9H is the 8th 64-bit chunk of ZMM9.
  | ZMM9H = 0xD4F
  /// ZMM10A is the 1st 64-bit chunk of ZMM10.
  | ZMM10A = 0xD50
  /// ZMM10B is the 2nd 64-bit chunk of ZMM10.
  | ZMM10B = 0xD51
  /// ZMM10C is the 3rd 64-bit chunk of ZMM10.
  | ZMM10C = 0xD52
  /// ZMM10D is the 4th 64-bit chunk of ZMM10.
  | ZMM10D = 0xD53
  /// ZMM10E is the 5th 64-bit chunk of ZMM10.
  | ZMM10E = 0xD54
  /// ZMM10F is the 6th 64-bit chunk of ZMM10.
  | ZMM10F = 0xD55
  /// ZMM10G is the 7th 64-bit chunk of ZMM10.
  | ZMM10G = 0xD56
  /// ZMM10H is the 8th 64-bit chunk of ZMM10.
  | ZMM10H = 0xD57
  /// ZMM11A is the 1st 64-bit chunk of ZMM11.
  | ZMM11A = 0xD58
  /// ZMM11B is the 2nd 64-bit chunk of ZMM11.
  | ZMM11B = 0xD59
  /// ZMM11C is the 3rd 64-bit chunk of ZMM11.
  | ZMM11C = 0xD5A
  /// ZMM11D is the 4th 64-bit chunk of ZMM11.
  | ZMM11D = 0xD5B
  /// ZMM11E is the 5th 64-bit chunk of ZMM11.
  | ZMM11E = 0xD5C
  /// ZMM11F is the 6th 64-bit chunk of ZMM11.
  | ZMM11F = 0xD5D
  /// ZMM11G is the 7th 64-bit chunk of ZMM11.
  | ZMM11G = 0xD5E
  /// ZMM11H is the 8th 64-bit chunk of ZMM11.
  | ZMM11H = 0xD5F
  /// ZMM12A is the 1st 64-bit chunk of ZMM12.
  | ZMM12A = 0xD60
  /// ZMM12B is the 2nd 64-bit chunk of ZMM12.
  | ZMM12B = 0xD61
  /// ZMM12C is the 3rd 64-bit chunk of ZMM12.
  | ZMM12C = 0xD62
  /// ZMM12D is the 4th 64-bit chunk of ZMM12.
  | ZMM12D = 0xD63
  /// ZMM12E is the 5th 64-bit chunk of ZMM12.
  | ZMM12E = 0xD64
  /// ZMM12F is the 6th 64-bit chunk of ZMM12.
  | ZMM12F = 0xD65
  /// ZMM12G is the 7th 64-bit chunk of ZMM12.
  | ZMM12G = 0xD66
  /// ZMM12H is the 8th 64-bit chunk of ZMM12.
  | ZMM12H = 0xD67
  /// ZMM13A is the 1st 64-bit chunk of ZMM13.
  | ZMM13A = 0xD68
  /// ZMM13B is the 2nd 64-bit chunk of ZMM13.
  | ZMM13B = 0xD69
  /// ZMM13C is the 3rd 64-bit chunk of ZMM13.
  | ZMM13C = 0xD6A
  /// ZMM13D is the 4th 64-bit chunk of ZMM13.
  | ZMM13D = 0xD6B
  /// ZMM13E is the 5th 64-bit chunk of ZMM13.
  | ZMM13E = 0xD6C
  /// ZMM13F is the 6th 64-bit chunk of ZMM13.
  | ZMM13F = 0xD6D
  /// ZMM13G is the 7th 64-bit chunk of ZMM13.
  | ZMM13G = 0xD6E
  /// ZMM13H is the 8th 64-bit chunk of ZMM13.
  | ZMM13H = 0xD6F
  /// ZMM14A is the 1st 64-bit chunk of ZMM14.
  | ZMM14A = 0xD70
  /// ZMM14B is the 2nd 64-bit chunk of ZMM14.
  | ZMM14B = 0xD71
  /// ZMM14C is the 3rd 64-bit chunk of ZMM14.
  | ZMM14C = 0xD72
  /// ZMM14D is the 4th 64-bit chunk of ZMM14.
  | ZMM14D = 0xD73
  /// ZMM14E is the 5th 64-bit chunk of ZMM14.
  | ZMM14E = 0xD74
  /// ZMM14F is the 6th 64-bit chunk of ZMM14.
  | ZMM14F = 0xD75
  /// ZMM14G is the 7th 64-bit chunk of ZMM14.
  | ZMM14G = 0xD76
  /// ZMM14H is the 8th 64-bit chunk of ZMM14.
  | ZMM14H = 0xD77
  /// ZMM15A is the 1st 64-bit chunk of ZMM15.
  | ZMM15A = 0xD78
  /// ZMM15B is the 2nd 64-bit chunk of ZMM15.
  | ZMM15B = 0xD79
  /// ZMM15C is the 3rd 64-bit chunk of ZMM15.
  | ZMM15C = 0xD7A
  /// ZMM15D is the 4th 64-bit chunk of ZMM15.
  | ZMM15D = 0xD7B
  /// ZMM15E is the 5th 64-bit chunk of ZMM15.
  | ZMM15E = 0xD7C
  /// ZMM15F is the 6th 64-bit chunk of ZMM15.
  | ZMM15F = 0xD7D
  /// ZMM15G is the 7th 64-bit chunk of ZMM15.
  | ZMM15G = 0xD7E
  /// ZMM15H is the 8th 64-bit chunk of ZMM15.
  | ZMM15H = 0xD7F
  /// Opmask registers. For EVEX.
  | K0 = 0xE00
  /// Opmask registers. For EVEX.
  | K1 = 0xE01
  /// Opmask registers. For EVEX.
  | K2 = 0xE02
  /// Opmask registers. For EVEX.
  | K3 = 0xE03
  /// Opmask registers. For EVEX.
  | K4 = 0xE04
  /// Opmask registers. For EVEX.
  | K5 = 0xE05
  /// Opmask registers. For EVEX.
  | K6 = 0xE06
  /// Opmask registers. For EVEX.
  | K7 = 0xE07
  /// Unknown Register.
  | UnknownReg = 0xF00

/// Shortcut for Register type.
type internal R = Register

/// This module exposes several useful functions to handle Intel registers.
[<RequireQualifiedAccess>]
module Register = begin
  /// Intel register kind, which is based on their usage.
  type Kind =
    /// General purpose registers.
    | GP = 0x0
    /// Floating-point registers.
    | FPU = 0x1
    /// MMX registers.
    | MMX = 0x2
    /// XMM registers.
    | XMM = 0x3
    /// YMM registers.
    | YMM = 0x4
    /// ZMM registers.
    | ZMM = 0x5
    /// Segment registers.
    | Segment = 0x6
    /// Registers represeting a segment base.
    | SegBase = 0x7
    /// Control registers.
    | Control = 0x8
    /// Debug registers.
    | Debug = 0x9
    /// Bound registers.
    | Bound = 0xA
    /// Flags registers.
    | Flags = 0xB
    /// Unclassified registers.
    | Unclassified = 0xC
    /// PseudoRegisters are the ones that we create to ease handling AVX
    /// registers and operations. Each AVX register is divided into a series of
    /// 64-bit pseudoregisters, and we name each pseudoregister using a suffix
    /// character from 'A' to 'H'. For example, XMM0A refers to the first 64-bit
    /// chunk of XMM0.
    | PseudoRegister = 0xD

  let getKind (reg: Register): Kind =
    (int reg >>> 8) &&& 0b1111 |> LanguagePrimitives.EnumOfValue

  let make id (kind: Kind): Register =
    (int kind <<< 8) ||| id |> LanguagePrimitives.EnumOfValue

  let inline ofRegID (n: RegisterID): Register =
    int n |> LanguagePrimitives.EnumOfValue

  let inline toRegID (reg: Register) =
    LanguagePrimitives.EnumToValue (reg) |> RegisterID.create

  let toRegType = function
    | R.MM0 | R.MM1 | R.MM2 | R.MM3
    | R.MM4 | R.MM5 | R.MM6 | R.MM7
    | R.RIP | R.R8 | R.R9 | R.R10 | R.R11 | R.R12 | R.R13 | R.R14 | R.R15
    | R.RAX | R.RBX | R.RCX | R.RDX | R.RSP | R.RBP | R.RSI | R.RDI -> 64<rt>
    | R.R8D | R.R9D | R.R10D | R.R11D
    | R.R12D | R.R13D | R.R14D | R.R15D
    | R.EAX | R.EBX | R.ECX | R.EDX
    | R.ESP | R.EBP | R.ESI | R.EDI | R.EIP | R.PKRU -> 32<rt>
    | R.ES | R.CS | R.SS | R.DS | R.FS | R.GS
    | R.R8W | R.R9W | R.R10W | R.R11W
    | R.R12W | R.R13W | R.R14W | R.R15W
    | R.AX | R.BX | R.CX | R.DX | R.SP | R.BP | R.SI | R.DI -> 16<rt>
    | R.R8L | R.R9L | R.R10L | R.R11L
    | R.R12L | R.R13L | R.R14L | R.R15L
    | R.SPL | R.BPL | R.SIL | R.DIL
    | R.AL | R.BL | R.CL | R.DL | R.AH | R.BH | R.CH | R.DH -> 8<rt>
    | R.XMM0 | R.XMM1 | R.XMM2 | R.XMM3
    | R.XMM4 | R.XMM5 | R.XMM6 | R.XMM7
    | R.XMM8 | R.XMM9 | R.XMM10 | R.XMM11
    | R.XMM12 | R.XMM13 | R.XMM14 | R.XMM15 -> 128<rt>
    | R.YMM0 | R.YMM1 | R.YMM2 | R.YMM3
    | R.YMM4 | R.YMM5 | R.YMM6 | R.YMM7
    | R.YMM8 | R.YMM9 | R.YMM10 | R.YMM11
    | R.YMM12 | R.YMM13 | R.YMM14 | R.YMM15 -> 256<rt>
    | _ -> raise UnknownRegException

  let extendRegister32 = function
    | R.EAX | R.AX | R.AL | R.AH -> R.EAX
    | R.EBX | R.BX | R.BL | R.BH -> R.EBX
    | R.ECX | R.CX | R.CL | R.CH -> R.ECX
    | R.EDX | R.DX | R.DL | R.DH -> R.EDX
    | R.ESP | R.SP | R.SPL -> R.ESP
    | R.EBP | R.BP | R.BPL -> R.EBP
    | R.ESI | R.SI | R.SIL -> R.ESI
    | R.EDI | R.DI | R.DIL -> R.EDI
    | R.XMM0 | R.YMM0 | R.ZMM0 -> R.YMM0
    | R.XMM1 | R.YMM1 | R.ZMM1 -> R.YMM1
    | R.XMM2 | R.YMM2 | R.ZMM2 -> R.YMM2
    | R.XMM3 | R.YMM3 | R.ZMM3 -> R.YMM3
    | R.XMM4 | R.YMM4 | R.ZMM4 -> R.YMM4
    | R.XMM5 | R.YMM5 | R.ZMM5 -> R.YMM5
    | R.XMM6 | R.YMM6 | R.ZMM6 -> R.YMM6
    | R.XMM7 | R.YMM7 | R.ZMM7 -> R.YMM7
    | R.DF | R.CF | R.PF | R.AF | R.ZF | R.SF | R.OF
    | R.BND0 | R.BND1 | R.BND2 | R.BND3 as e -> e
    | R.ESBase | R.ES -> R.ESBase
    | R.CSBase | R.CS -> R.CSBase
    | R.SSBase | R.SS -> R.SSBase
    | R.DSBase | R.DS -> R.DSBase
    | R.FSBase | R.FS -> R.FSBase
    | R.GSBase | R.GS -> R.GSBase
    | R.EIP -> R.EIP
    | e -> e

  let extendRegister64 = function
    | R.RAX | R.EAX | R.AX | R.AL | R.AH -> R.RAX
    | R.RBX | R.EBX | R.BX | R.BL | R.BH -> R.RBX
    | R.RCX | R.ECX | R.CX | R.CL | R.CH -> R.RCX
    | R.RDX | R.EDX | R.DX | R.DL | R.DH -> R.RDX
    | R.RSP | R.ESP | R.SP | R.SPL -> R.RSP
    | R.RBP | R.EBP | R.BP | R.BPL -> R.RBP
    | R.RSI | R.ESI | R.SI | R.SIL -> R.RSI
    | R.RDI | R.EDI | R.DI | R.DIL-> R.RDI
    | R.R8  | R.R8D | R.R8L | R.R8W -> R.R8
    | R.R9  | R.R9D | R.R9L | R.R9W -> R.R9
    | R.R10 | R.R10D | R.R10L | R.R10W -> R.R10
    | R.R11 | R.R11D | R.R11L | R.R11W -> R.R11
    | R.R12 | R.R12D | R.R12L | R.R12W -> R.R12
    | R.R13 | R.R13D | R.R13L | R.R13W -> R.R13
    | R.R14 | R.R14D | R.R14L | R.R14W -> R.R14
    | R.R15 | R.R15D | R.R15L | R.R15W -> R.R15
    | R.XMM0 | R.YMM0 | R.ZMM0 -> R.YMM0
    | R.XMM1 | R.YMM1 | R.ZMM1 -> R.YMM1
    | R.XMM2 | R.YMM2 | R.ZMM2 -> R.YMM2
    | R.XMM3 | R.YMM3 | R.ZMM3 -> R.YMM3
    | R.XMM4 | R.YMM4 | R.ZMM4 -> R.YMM4
    | R.XMM5 | R.YMM5 | R.ZMM5 -> R.YMM5
    | R.XMM6 | R.YMM6 | R.ZMM6 -> R.YMM6
    | R.XMM7 | R.YMM7 | R.ZMM7 -> R.YMM7
    | R.XMM8 | R.YMM8 | R.ZMM8 -> R.YMM8
    | R.XMM9 | R.YMM9 | R.ZMM9 -> R.YMM9
    | R.XMM10 | R.YMM10 | R.ZMM10 -> R.YMM10
    | R.XMM11 | R.YMM11 | R.ZMM11 -> R.YMM11
    | R.XMM12 | R.YMM12 | R.ZMM12 -> R.YMM12
    | R.XMM13 | R.YMM13 | R.ZMM13 -> R.YMM13
    | R.XMM14 | R.YMM14 | R.ZMM14 -> R.YMM14
    | R.XMM15 | R.YMM15 | R.ZMM15 -> R.YMM15
    | R.DF | R.CF | R.PF | R.AF | R.ZF | R.SF | R.OF
    | R.BND0 | R.BND1 | R.BND2 | R.BND3 as e -> e
    | R.ESBase | R.ES -> R.ESBase
    | R.CSBase | R.CS -> R.CSBase
    | R.SSBase | R.SS -> R.SSBase
    | R.DSBase | R.DS -> R.DSBase
    | R.FSBase | R.FS -> R.FSBase
    | R.GSBase | R.GS -> R.GSBase
    | R.RIP | R.EIP -> R.RIP
    | e -> e

  let regToPseudoReg = function
    | R.XMM0  -> [ R.ZMM0B; R.ZMM0A ]
    | R.XMM1  -> [ R.ZMM1B; R.ZMM1A ]
    | R.XMM2  -> [ R.ZMM2B; R.ZMM2A ]
    | R.XMM3  -> [ R.ZMM3B; R.ZMM3A ]
    | R.XMM4  -> [ R.ZMM4B; R.ZMM4A ]
    | R.XMM5  -> [ R.ZMM5B; R.ZMM5A ]
    | R.XMM6  -> [ R.ZMM6B; R.ZMM6A ]
    | R.XMM7  -> [ R.ZMM7B; R.ZMM7A ]
    | R.XMM8  -> [ R.ZMM8B; R.ZMM8A ]
    | R.XMM9  -> [ R.ZMM9B; R.ZMM9A ]
    | R.XMM10 -> [ R.ZMM10B; R.ZMM10A ]
    | R.XMM11 -> [ R.ZMM11B; R.ZMM11A ]
    | R.XMM12 -> [ R.ZMM12B; R.ZMM12A ]
    | R.XMM13 -> [ R.ZMM13B; R.ZMM13A ]
    | R.XMM14 -> [ R.ZMM14B; R.ZMM14A ]
    | R.XMM15 -> [ R.ZMM15B; R.ZMM15A ]
    | R.YMM0  -> [ R.ZMM0D; R.ZMM0C; R.ZMM0B; R.ZMM0A ]
    | R.YMM1  -> [ R.ZMM1D; R.ZMM1C; R.ZMM1B; R.ZMM1A ]
    | R.YMM2  -> [ R.ZMM2D; R.ZMM2C; R.ZMM2B; R.ZMM2A ]
    | R.YMM3  -> [ R.ZMM3D; R.ZMM3C; R.ZMM3B; R.ZMM3A ]
    | R.YMM4  -> [ R.ZMM4D; R.ZMM4C; R.ZMM4B; R.ZMM4A ]
    | R.YMM5  -> [ R.ZMM5D; R.ZMM5C; R.ZMM5B; R.ZMM5A ]
    | R.YMM6  -> [ R.ZMM6D; R.ZMM6C; R.ZMM6B; R.ZMM6A ]
    | R.YMM7  -> [ R.ZMM7D; R.ZMM7C; R.ZMM7B; R.ZMM7A ]
    | R.YMM8  -> [ R.ZMM8D; R.ZMM8C; R.ZMM8B; R.ZMM8A ]
    | R.YMM9  -> [ R.ZMM9D; R.ZMM9C; R.ZMM9B; R.ZMM9A ]
    | R.YMM10 -> [ R.ZMM10D; R.ZMM10C; R.ZMM10B; R.ZMM10A ]
    | R.YMM11 -> [ R.ZMM11D; R.ZMM11C; R.ZMM11B; R.ZMM11A ]
    | R.YMM12 -> [ R.ZMM12D; R.ZMM12C; R.ZMM12B; R.ZMM12A ]
    | R.YMM13 -> [ R.ZMM13D; R.ZMM13C; R.ZMM13B; R.ZMM13A ]
    | R.YMM14 -> [ R.ZMM14D; R.ZMM14C; R.ZMM14B; R.ZMM14A ]
    | R.YMM15 -> [ R.ZMM15D; R.ZMM15C; R.ZMM15B; R.ZMM15A ]
    | e -> failwithf "Unhandled register: %A" e
end

/// This module defines sets of registers that are frequently grouped by Intel.
module internal RegGroup = begin
  let GrpEAX = [| R.AL; R.AX; R.EAX; R.RAX; R.XMM0; R.YMM0; R.ZMM0 |] (* Grp0 *)
  let GrpECX = [| R.CL; R.CX; R.ECX; R.RCX; R.XMM1; R.YMM1; R.ZMM1 |] (* Grp1 *)
  let GrpEDX = [| R.DL; R.DX; R.EDX; R.RDX; R.XMM2; R.YMM2; R.ZMM2 |] (* Grp2 *)
  let GrpEBX = [| R.BL; R.BX; R.EBX; R.RBX; R.XMM3; R.YMM3; R.ZMM3 |] (* Grp3 *)
  let GrpAH  = [| R.AH; R.SP; R.ESP; R.RSP; R.XMM4; R.YMM4; R.ZMM4 |] (* Grp4 *)
  let GrpCH  = [| R.CH; R.BP; R.EBP; R.RBP; R.XMM5; R.YMM5; R.ZMM5 |] (* Grp5 *)
  let GrpDH  = [| R.DH; R.SI; R.ESI; R.RSI; R.XMM6; R.YMM6; R.ZMM6 |] (* Grp6 *)
  let GrpBH  = [| R.BH; R.DI; R.EDI; R.RDI; R.XMM7; R.YMM7; R.ZMM7 |] (* Grp7 *)

  let GrpESP = [| R.SPL; R.SP; R.ESP; R.RSP; R.XMM4; R.YMM4; R.ZMM4 |]
  let GrpEBP = [| R.BPL; R.BP; R.EBP; R.RBP; R.XMM5; R.YMM5; R.ZMM5 |]
  let GrpESI = [| R.SIL; R.SI; R.ESI; R.RSI; R.XMM6; R.YMM6; R.ZMM6 |]
  let GrpEDI = [| R.DIL; R.DI; R.EDI; R.RDI; R.XMM7; R.YMM7; R.ZMM7 |]

  let GrpR8  = [| R.R8L; R.R8W; R.R8D; R.R8; R.XMM8; R.YMM8; R.ZMM8 |]
  let GrpR9  = [| R.R9L; R.R9W; R.R9D; R.R9; R.XMM9; R.YMM9; R.ZMM9 |]
  let GrpR10 = [| R.R10L; R.R10W; R.R10D; R.R10; R.XMM10; R.YMM10; R.ZMM10 |]
  let GrpR11 = [| R.R11L; R.R11W; R.R11D; R.R11; R.XMM11; R.YMM11; R.ZMM11 |]
  let GrpR12 = [| R.R12L; R.R12W; R.R12D; R.R12; R.XMM12; R.YMM12; R.ZMM12 |]
  let GrpR13 = [| R.R13L; R.R13W; R.R13D; R.R13; R.XMM13; R.YMM13; R.ZMM13 |]
  let GrpR14 = [| R.R14L; R.R14W; R.R14D; R.R14; R.XMM14; R.YMM14; R.ZMM14 |]
  let GrpR15 = [| R.R15L; R.R15W; R.R15D; R.R15; R.XMM15; R.YMM15; R.ZMM15 |]
end
