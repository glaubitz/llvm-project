//===-- M68kInstrData.td - M68k Data Movement Instructions -*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file describes the Motorola 680x0 data movement instructions which are
/// either not yet or will never be part of a larger instruction family.
/// Here is the current status of the file:
///
///  Machine:
///
///     EXG   [ ]     FMOVE [ ]     FSMOVE [ ]     FDMOVE [ ]     FMOVEM [ ]
///     MOVEM [ ]     MOVEP [ ]     MOVEQ  [ ]     LINK   [~]     UNLK   [~]
///
///  Map:
///
///   [ ] - was not touched at all
///   [!] - requires extarnal stuff implemented
///   [~] - functional implementation
///   [X] - complete implementation
///
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
// MOVE
//===----------------------------------------------------------------------===//

/// ----------------------------------------------------
///  F  E | D  C | B  A  9 | 8  7  6 | 5  4  3 | 2  1  0
/// ----------------------------------------------------
///  0  0 | SIZE |   DESTINATION EA  |     SOURCE EA
/// ----------------------------------------------------
///               MODE  |   REG      |   MODE  |   REG
/// ----------------------------------------------------

class MxMoveSize<bits<2> value> {
  bits<2> Value = value;
}
def MxMoveSize8  : MxMoveSize<0b01>;
def MxMoveSize16 : MxMoveSize<0b11>;
def MxMoveSize32 : MxMoveSize<0b10>;

class MxMoveEncoding<MxMoveSize size, MxEncMemOp dst_enc, MxEncMemOp src_enc> {
  dag Value = (ascend
    (descend 0b00, size.Value,
             !cond(
               !eq(!getdagop(dst_enc.EA), descend): !setdagop(dst_enc.EA, ascend),
               !eq(!getdagop(dst_enc.EA), ascend): !setdagop(dst_enc.EA, descend)),
             src_enc.EA),
    // Source extension
    src_enc.Supplement,
    // Destination extension
    dst_enc.Supplement
  );
}

// Special encoding for Xn
class MxMoveEncAddrMode_r<string reg_opnd> : MxEncMemOp {
  let EA = (descend (descend 0b00, (slice "$"#reg_opnd, 3, 3)),
                    (operand "$"#reg_opnd, 3));
}

// TODO: Generalize and adopt this utility in other .td files as well.
multiclass MxMoveOperandEncodings<string opnd_name> {
  // Dn
  def MxMove#NAME#OpEnc_d : MxEncAddrMode_d<opnd_name>;
  // An
  def MxMove#NAME#OpEnc_a : MxEncAddrMode_a<opnd_name>;
  // Xn
  def MxMove#NAME#OpEnc_r : MxMoveEncAddrMode_r<opnd_name>;
  // (An)+
  def MxMove#NAME#OpEnc_o : MxEncAddrMode_o<opnd_name>;
  // -(An)
  def MxMove#NAME#OpEnc_e : MxEncAddrMode_e<opnd_name>;
  // (i,PC,Xn)
  def MxMove#NAME#OpEnc_k : MxEncAddrMode_k<opnd_name>;
  // (i,PC)
  def MxMove#NAME#OpEnc_q : MxEncAddrMode_q<opnd_name>;
  // (i32,PC)
  def MxMove#NAME#OpEnc_q32 : MxMove#NAME#OpEnc_q;
  // (i,An,Xn)
  def MxMove#NAME#OpEnc_f : MxEncAddrMode_f<opnd_name>;
  // (i,An)
  def MxMove#NAME#OpEnc_p : MxEncAddrMode_p<opnd_name>;
  // (i32,An)
  def MxMove#NAME#OpEnc_p32 : MxMove#NAME#OpEnc_p;
  // (abs).W/L
  def MxMove#NAME#OpEnc_b : MxEncAddrMode_abs<opnd_name, /*W/L=*/true>;
  // (An)
  def MxMove#NAME#OpEnc_j : MxEncAddrMode_j<opnd_name>;
}

defm Src : MxMoveOperandEncodings<"src">;
defm Dst : MxMoveOperandEncodings<"dst">;

class MxMove<string size, dag outs, dag ins, list<dag> pattern, MxMoveEncoding enc>
    : MxInst<outs, ins, "move."#size#"\t$src, $dst", pattern> {
  let Inst = enc.Value;
  // Almost all MOVE instructions clobber flags on M68k.
  // The only exception is MOVEA (Move to Address Register).
  let Defs = [CCR];
}

// R <- R
class MxMove_RR<MxType TYPE, string DST_REG, string SRC_REG,
                MxMoveEncoding ENC,
                MxOpBundle DST = !cast<MxOpBundle>("MxOp"#TYPE.Size#"AddrMode_"#DST_REG),
                MxOpBundle SRC = !cast<MxOpBundle>("MxOp"#TYPE.Size#"AddrMode_"#SRC_REG)>
    : MxMove<TYPE.Prefix,
             (outs DST.Op:$dst), (ins SRC.Op:$src),
             [(null_frag)], ENC>;

foreach DST_REG = ["r", "a"] in {
  let Defs = !if(!eq(DST_REG, "a"), [], [CCR]) in {
  foreach SRC_REG = ["r", "a"] in
  foreach TYPE = [MxType16, MxType32] in
  def MOV # TYPE.Size # DST_REG # SRC_REG # TYPE.Postfix
      : MxMove_RR<TYPE, DST_REG, SRC_REG,
                  MxMoveEncoding<!cast<MxMoveSize>("MxMoveSize"#TYPE.Size),
                                 !cast<MxEncMemOp>("MxMoveDstOpEnc_"#DST_REG),
                                 !cast<MxEncMemOp>("MxMoveSrcOpEnc_"#SRC_REG)>>;
  }
} // foreach DST_REG

foreach TYPE = [MxType8, MxType16, MxType32] in
def MOV # TYPE.Size # dd # TYPE.Postfix
    : MxMove_RR<TYPE, "d", "d",
                MxMoveEncoding<!cast<MxMoveSize>("MxMoveSize"#TYPE.Size),
                               !cast<MxEncMemOp>("MxMoveDstOpEnc_d"),
                               !cast<MxEncMemOp>("MxMoveSrcOpEnc_d")>>;

// M <- R/I
let mayStore = 1 in {
class MxMove_MR<MxType TYPE, MxOpBundle DST, string SRC_REG, MxMoveEncoding ENC,
                MxOpBundle SRC = !cast<MxOpBundle>("MxOp"#TYPE.Size#"AddrMode_"#SRC_REG)>
    : MxMove<TYPE.Prefix, (outs), (ins DST.Op:$dst, SRC.Op:$src),
             [(store TYPE.VT:$src, DST.Pat:$dst)], ENC>;

class MxMove_MI<MxType TYPE, MxOpBundle DST, MxMoveEncoding ENC,
                MxImmOpBundle SRC = !cast<MxImmOpBundle>("MxOp"#TYPE.Size#"AddrMode_i")>
    : MxMove<TYPE.Prefix, (outs), (ins DST.Op:$dst, SRC.Op:$src),
             [(store SRC.ImmPat:$src, DST.Pat:$dst)], ENC>;
} // let mayStore = 1

defvar MxMoveDstAMs = ["o", "e", "f", "p", "b", "j"];
defvar MxMoveSrcAMs = ["o", "e", "f", "p", "b", "j", "q", "k"];

foreach REG = ["r", "a", "d"] in
foreach AM = MxMoveDstAMs in {
  let Defs = !if(!eq(REG, "a"), [], [CCR]) in
  foreach TYPE = !if(!eq(REG, "d"), [MxType8, MxType16, MxType32], [MxType16, MxType32]) in
  def MOV # TYPE.Size # AM # REG # TYPE.Postfix
      : MxMove_MR<TYPE, !cast<MxOpBundle>("MxOp"#TYPE.Size#"AddrMode_"#AM), REG,
                  MxMoveEncoding<!cast<MxMoveSize>("MxMoveSize"#TYPE.Size),
                                 !cast<MxEncMemOp>("MxMoveDstOpEnc_"#AM),
                                 !cast<MxEncMemOp>("MxMoveSrcOpEnc_"#REG)>>;
} // foreach AM

foreach AM = MxMoveDstAMs in {
  foreach TYPE = [MxType8, MxType16, MxType32] in
  def MOV # TYPE.Size # AM # i # TYPE.Postfix
      : MxMove_MI<TYPE, !cast<MxOpBundle>("MxOp"#TYPE.Size#"AddrMode_"#AM),
                  MxMoveEncoding<!cast<MxMoveSize>("MxMoveSize"#TYPE.Size),
                                 !cast<MxEncMemOp>("MxMoveDstOpEnc_"#AM),
                                 MxEncAddrMode_i<"src", TYPE.Size>>>;
  let Predicates = [AtLeastM68020] in
  def MOV32 # AM # p32 : MxMove_MI<MxType32, !cast<MxOpBundle>("MxOp32AddrMode_"#AM),
                                  MxMoveEncoding<MxMoveSize32,
                                                 !cast<MxEncMemOp>("MxMoveDstOpEnc_"#AM),
                                                 MxEncAddrMode_p32<"src">>,
                                  MxOp32AddrMode_i>;
} // foreach AM

// R <- I
class MxMove_RI<MxType TYPE, string DST_REG, MxMoveEncoding ENC,
                MxImmOpBundle SRC = !cast<MxImmOpBundle>("MxOp"#TYPE.Size#"AddrMode_i"),
                MxOpBundle DST = !cast<MxOpBundle>("MxOp"#TYPE.Size#"AddrMode_"#DST_REG)>
    : MxMove<TYPE.Prefix, (outs DST.Op:$dst), (ins SRC.Op:$src),
              [(null_frag)], ENC>;

foreach REG = ["r", "a", "d"] in {
  let Defs = !if(!eq(REG, "a"), [], [CCR]) in {
  foreach TYPE = !if(!eq(REG, "d"), [MxType8, MxType16, MxType32], [MxType16, MxType32]) in
  def MOV # TYPE.Size # REG # i # TYPE.Postfix
      : MxMove_RI<TYPE, REG,
                  MxMoveEncoding<!cast<MxMoveSize>("MxMoveSize"#TYPE.Size),
                                 !cast<MxEncMemOp>("MxMoveDstOpEnc_"#REG),
                                 MxEncAddrMode_i<"src", TYPE.Size>>>;
  }
} // foreach REG

// R <- M
let mayLoad = 1 in
class MxMove_RM<MxType TYPE, string DST_REG, MxOpBundle SRC, MxEncMemOp SRC_ENC,
                MxMoveSize SIZE_ENC = !cast<MxMoveSize>("MxMoveSize"#TYPE.Size),
                MxOpBundle DST = !cast<MxOpBundle>("MxOp"#TYPE.Size#"AddrMode_"#DST_REG),
                MxEncMemOp DST_ENC = !cast<MxEncMemOp>("MxMoveDstOpEnc_"#DST_REG)>
    : MxMove<TYPE.Prefix, (outs DST.Op:$dst), (ins SRC.Op:$src),
             [(set TYPE.VT:$dst, (TYPE.Load SRC.Pat:$src))],
             MxMoveEncoding<SIZE_ENC, DST_ENC, SRC_ENC>>;

foreach REG = ["r", "a", "d"] in {
  let Defs = !if(!eq(REG, "a"), [], [CCR]) in {
  foreach TYPE = !if(!eq(REG, "d"), [MxType8, MxType16, MxType32], [MxType16, MxType32]) in {
    let Predicates = [AtLeastM68020] in {
    def MOV # TYPE.Size # REG # q32 : MxMove_RM<TYPE, REG, MxOp32AddrMode_q32,
                                                MxEncAddrMode_q32<"src">>;
    def MOV # TYPE.Size # REG # p32 : MxMove_RM<TYPE, REG, MxOp32AddrMode_p32,
                                                MxEncAddrMode_p32<"src">>;

    def MOV # TYPE.Size # p32 # REG : MxMove_MR<TYPE, MxOp32AddrMode_p32, REG,
                                                MxMoveEncoding<!cast<MxMoveSize>("MxMoveSize"#TYPE.Size),
                                                               MxEncAddrMode_p32<"dst">,
                                                               !cast<MxEncMemOp>("MxMoveSrcOpEnc_"#REG)>>;
    }
  }
  }
}

foreach REG = ["r", "a", "d"] in
foreach AM = MxMoveSrcAMs in {
  let Defs = !if(!eq(REG, "a"), [], [CCR]) in
  foreach TYPE = !if(!eq(REG, "d"), [MxType8, MxType16, MxType32], [MxType16, MxType32]) in
  def MOV # TYPE.Size # REG # AM # TYPE.Postfix
      : MxMove_RM<TYPE, REG, !cast<MxOpBundle>("MxOp"#TYPE.Size#"AddrMode_"#AM),
                  !cast<MxEncMemOp>("MxMoveSrcOpEnc_"#AM)>;
}

def MOV32rq32_TC : MxMove_RM<MxType32, "r", MxOp32AddrMode_q32,
                             MxEncAddrMode_q32<"src">>;
def MOV32aq32_TC : MxMove_RM<MxType32, "a", MxOp32AddrMode_q32,
                             MxEncAddrMode_q32<"src">>;

foreach AM = MxMoveSrcAMs in {
  foreach TYPE = [MxType8, MxType16, MxType32] in
  foreach REG = ["d", "a"] in
  let Defs = !if(!eq(REG, "a"), [], [CCR]) in
  def MOV # TYPE.Size # REG # AM # _TC
      : MxMove_RM<TYPE, REG, !cast<MxOpBundle>("MxOp"#TYPE.Size#"AddrMode_"#AM),
                  !cast<MxEncMemOp>("MxMoveSrcOpEnc_"#AM)>;
}

// M <- M
class MxMove_MM<MxType TYPE, MxOpBundle DST, MxOpBundle SRC,
                MxEncMemOp DST_ENC, MxEncMemOp SRC_ENC>
    : MxMove<TYPE.Prefix, (outs), (ins DST.Op:$dst, SRC.Op:$src),
             [(store (TYPE.Load SRC.Pat:$src), DST.Pat:$dst)],
             MxMoveEncoding<!cast<MxMoveSize>("MxMoveSize"#TYPE.Size),
                            DST_ENC, SRC_ENC>>;

// Use a store-load patfrag that can reject unsafe load chains (e.g. callseq).
let mayLoad = 1, mayStore = 1 in
class MxMove_MM_Safe<MxType TYPE, PatFrag StoreLoad,
                     MxOpBundle DST, MxOpBundle SRC,
                     MxEncMemOp DST_ENC, MxEncMemOp SRC_ENC>
    : MxMove<TYPE.Prefix, (outs), (ins DST.Op:$dst, SRC.Op:$src),
             [(StoreLoad DST.Pat:$dst, SRC.Pat:$src)],
             MxMoveEncoding<!cast<MxMoveSize>("MxMoveSize"#TYPE.Size),
                            DST_ENC, SRC_ENC>>;

foreach DST_AM = MxMoveDstAMs in
foreach SRC_AM = MxMoveSrcAMs in {
  def MOV8 # DST_AM # SRC_AM # !cast<MxType>("MxType8").Postfix
      : MxMove_MM_Safe<MxType8, Mxstoreloadi8_safe,
                       !cast<MxOpBundle>("MxOp8AddrMode_"#DST_AM),
                       !cast<MxOpBundle>("MxOp8AddrMode_"#SRC_AM),
                       !cast<MxEncMemOp>("MxMoveDstOpEnc_"#DST_AM),
                       !cast<MxEncMemOp>("MxMoveSrcOpEnc_"#SRC_AM)>;

  def MOV16 # DST_AM # SRC_AM # !cast<MxType>("MxType16").Postfix
      : MxMove_MM_Safe<MxType16, Mxstoreloadi16_safe,
                       !cast<MxOpBundle>("MxOp16AddrMode_"#DST_AM),
                       !cast<MxOpBundle>("MxOp16AddrMode_"#SRC_AM),
                       !cast<MxEncMemOp>("MxMoveDstOpEnc_"#DST_AM),
                       !cast<MxEncMemOp>("MxMoveSrcOpEnc_"#SRC_AM)>;

  def MOV32 # DST_AM # SRC_AM # !cast<MxType>("MxType32").Postfix
      : MxMove_MM_Safe<MxType32, Mxstoreloadi32_safe,
                       !cast<MxOpBundle>("MxOp32AddrMode_"#DST_AM),
                       !cast<MxOpBundle>("MxOp32AddrMode_"#SRC_AM),
                       !cast<MxEncMemOp>("MxMoveDstOpEnc_"#DST_AM),
                       !cast<MxEncMemOp>("MxMoveSrcOpEnc_"#SRC_AM)>;
}


//===----------------------------------------------------------------------===//
// Pseudo Move
//===----------------------------------------------------------------------===//

// They are expanded post-RA into either move or moveq instructions,
// depending on the immediate value.
// We can use any register as the destination, but we prefer
// data registers if moveq matches.
// i8 imm -> reg can always be converted to moveq,
// but it is limited to data register only.
let isReMaterializable = 1, isAsCheapAsAMove = 1 in
def MOVI32 : MxPseudo<(outs MxRD32:$dst), (ins Mxi32imm:$src),
                       [(set i32:$dst, imm:$src)]>;

// i16/i8 imm -> reg
def MOVI16 : MxPseudo<(outs MxRD16:$dst), (ins Mxi16imm:$src),
                       [(set i16:$dst, imm:$src)]>;
def MOVI8  : MxPseudo<(outs MxRD8:$dst),  (ins Mxi8imm:$src),
                       [(set i8:$dst, imm:$src)]>;

// FIXME check if they clobber CCR
// They are expanded during MC emission.
// tglobaladdr -> reg
def MOV32rGA : MxPseudo<(outs MxRD32:$dst), (ins Mxi32imm:$src),
                        [(set i32:$dst, tglobaladdr:$src)]>;

// texternalsym -> reg
def MOV32rES : MxPseudo<(outs MxRD32:$dst), (ins Mxi32imm:$src),
                        [(set i32:$dst, texternalsym:$src)]>;

// tblockaddress -> reg
def MOV32rBA : MxPseudo<(outs MxRD32:$dst), (ins Mxi32imm:$src),
                        [(set i32:$dst, tblockaddress:$src)]>;

// tjt -> reg
def MOV32rJT : MxPseudo<(outs MxRD32:$dst), (ins Mxi32imm:$src),
                        [(set i32:$dst, tjumptable:$src)]>;

// tcp -> reg
def MOV32rCP : MxPseudo<(outs MxRD32:$dst), (ins Mxi32imm:$src),
                        [(set i32:$dst, tconstpool:$src)]>;


//===----------------------------------------------------------------------===//
// Move to/from CCR/SR
//===----------------------------------------------------------------------===//

/// Move to CCR
/// --------------------------------------------------
///  F  E  D  C  B  A  9  8  7  6 | 5  4  3 | 2  1  0
/// --------------------------------------------------
///                               | EFFECTIVE ADDRESS
///  0  1  0  0  0  1  0  0  1  1 |   MODE  |   REG
/// --------------------------------------------------

let Defs = [CCR] in {
class MxMoveToCCR<MxOperand MEMOp, MxEncMemOp SRC_ENC>
    : MxInst<(outs CCRC:$dst), (ins MEMOp:$src), "move.w\t$src, $dst", []> {
  let Inst = (ascend
    (descend 0b0100010011, SRC_ENC.EA),
    SRC_ENC.Supplement
  );
}

class MxMoveToCCRPseudo<MxOperand MEMOp>
    : MxPseudo<(outs CCRC:$dst), (ins MEMOp:$src)>;
} // let Defs = [CCR]

let mayLoad = 1 in
foreach AM = MxMoveSrcAMs in {
  def MOV16c # AM : MxMoveToCCR<!cast<MxOpBundle>("MxOp16AddrMode_"#AM).Op,
                                !cast<MxEncMemOp>("MxMoveSrcOpEnc_"#AM)>;
  def MOV8c # AM  : MxMoveToCCRPseudo<!cast<MxOpBundle>("MxOp8AddrMode_"#AM).Op>;
} // foreach AM

// Only data register is allowed.
def MOV16cd : MxMoveToCCR<MxOp16AddrMode_d.Op, MxMoveSrcOpEnc_d>;

/// Move from CCR
/// --------------------------------------------------
///  F  E  D  C  B  A  9  8  7  6 | 5  4  3 | 2  1  0
/// --------------------------------------------------
///                               | EFFECTIVE ADDRESS
///  0  1  0  0  0  0  1  0  1  1 |   MODE  |   REG
/// --------------------------------------------------

let Uses = [CCR] in {
class MxMoveFromCCR_R
    : MxInst<(outs MxDRD16:$dst), (ins CCRC:$src), "move.w\t$src, $dst", []>,
      Requires<[ AtLeastM68010 ]> {
  let Inst = (descend 0b0100001011, MxEncAddrMode_d<"dst">.EA);
}

class MxMoveFromCCR_M<MxOperand MEMOp, MxEncMemOp DST_ENC>
    : MxInst<(outs), (ins MEMOp:$dst, CCRC:$src), "move.w\t$src, $dst", []>,
      Requires<[ AtLeastM68010 ]> {
  let Inst = (ascend
    (descend 0b0100001011, DST_ENC.EA),
    DST_ENC.Supplement
  );
}

class MxMoveFromCCRPseudo<MxOperand MEMOp>
    : MxPseudo<(outs), (ins MEMOp:$dst, CCRC:$src)>;
class MxMoveFromCCR_RPseudo<MxOperand MEMOp>
    : MxPseudo<(outs MEMOp:$dst), (ins CCRC:$src)>;
} // let Uses = [CCR]

let mayStore = 1 in
foreach AM = MxMoveDstAMs in {
  def MOV16 # AM # c
    : MxMoveFromCCR_M<!cast<MxOpBundle>("MxOp16AddrMode_"#AM).Op,
                      !cast<MxEncMemOp>("MxMoveDstOpEnc_"#AM)>;
  def MOV8 # AM # c
    : MxMoveFromCCRPseudo<!cast<MxOpBundle>("MxOp8AddrMode_"#AM).Op>;
} // foreach AM

// Only data register is allowed.
def MOV16dc : MxMoveFromCCR_R;

/// Move to SR
/// --------------------------------------------------
///  F  E  D  C  B  A  9  8  7  6 | 5  4  3 | 2  1  0
/// --------------------------------------------------
///                               | EFFECTIVE ADDRESS
///  0  1  0  0  0  1  1  0  1  1 |   MODE  |   REG
/// --------------------------------------------------

let Defs = [SR] in {
class MxMoveToSR<MxOperand MEMOp, MxEncMemOp SRC_ENC>
    : MxInst<(outs SRC:$dst), (ins MEMOp:$src), "move.w\t$src, $dst", []> {
  let Inst = (ascend
    (descend 0b0100011011, SRC_ENC.EA),
    SRC_ENC.Supplement
  );
}
} // let Defs = [SR]

let mayLoad = 1 in
foreach AM = MxMoveSrcAMs in {
  def MOV16s # AM : MxMoveToSR<!cast<MxOpBundle>("MxOp16AddrMode_"#AM).Op,
                                !cast<MxEncMemOp>("MxMoveSrcOpEnc_"#AM)>;
} // foreach AM

def MOV16sd : MxMoveToSR<MxOp16AddrMode_d.Op, MxMoveSrcOpEnc_d>;

/// Move from SR
/// --------------------------------------------------
///  F  E  D  C  B  A  9  8  7  6 | 5  4  3 | 2  1  0
/// --------------------------------------------------
///                               | EFFECTIVE ADDRESS
///  0  1  0  0  0  0  0  0  1  1 |   MODE  |   REG
/// --------------------------------------------------

let Uses = [SR] in {
class MxMoveFromSR_R
    : MxInst<(outs MxDRD16:$dst), (ins SRC:$src), "move.w\t$src, $dst", []> {
  let Inst = (descend 0b0100000011, MxEncAddrMode_d<"dst">.EA);
}

class MxMoveFromSR_M<MxOperand MEMOp, MxEncMemOp DST_ENC>
    : MxInst<(outs), (ins MEMOp:$dst, SRC:$src), "move.w\t$src, $dst", []> {
  let Inst = (ascend
    (descend 0b0100000011, DST_ENC.EA),
    DST_ENC.Supplement
  );
}
} // let Uses = [SR]

let mayStore = 1 in
foreach AM = MxMoveDstAMs in {
  def MOV16 # AM # s
    : MxMoveFromSR_M<!cast<MxOpBundle>("MxOp16AddrMode_"#AM).Op,
                      !cast<MxEncMemOp>("MxMoveDstOpEnc_"#AM)>;
} // foreach AM

def MOV16ds : MxMoveFromSR_R;

//===----------------------------------------------------------------------===//
// LEA
//===----------------------------------------------------------------------===//

/// --------------------------------------------------
///  F  E  D  C | B  A  9 | 8  7  6 | 5  4  3 | 2  1  0
/// --------------------------------------------------
///  0  1  0  0 |   REG   | 1  1  1 |   MODE  |   REG
/// --------------------------------------------------

class MxLEA<MxOpBundle SRC, MxEncMemOp SRC_ENC>
    : MxInst<(outs MxARD32:$dst), (ins SRC.Op:$src),
             "lea\t$src, $dst", [(set i32:$dst, SRC.Pat:$src)]> {
  let Inst = (ascend
    (descend 0b0100, (operand "$dst", 3), 0b111, SRC_ENC.EA),
    SRC_ENC.Supplement
  );
}

foreach AM = ["p", "f", "b", "q", "k"] in
def LEA32 # AM : MxLEA<!cast<MxOpBundle>("MxOp32AddrMode_"#AM),
                        !cast<MxEncMemOp>("MxMoveSrcOpEnc_"#AM)>;

let Predicates = [AtLeastM68020] in {
def LEA32q32 : MxLEA<MxOp32AddrMode_q32, MxEncAddrMode_q32<"src">>;
def LEA32p32 : MxLEA<MxOp32AddrMode_p32, MxEncAddrMode_p32<"src">>;
}

//===----------------------------------------------------------------------===//
// PEA
//===----------------------------------------------------------------------===//

/// --------------------------------------------------
///  F  E  D  C  B  A  9  8  7  6 | 5  4  3 | 2  1  0
/// --------------------------------------------------
///  0  1  0  0  1  0  0  0  0  1 |   MODE  |   REG
/// --------------------------------------------------

let mayStore = 1 in
class MxPEA<MxOpBundle SRC, MxEncMemOp SRC_ENC>
    : MxInst<(outs), (ins SRC.Op:$src), "pea\t$src", []> {
  let Inst = (ascend
    (descend 0b0100100001, SRC_ENC.EA),
    SRC_ENC.Supplement
  );
}

foreach AM = ["j", "p", "f", "b", "q", "k"] in
def PEA32 # AM : MxPEA<!cast<MxOpBundle>("MxOp32AddrMode_"#AM),
                        !cast<MxEncMemOp>("MxMoveSrcOpEnc_"#AM)>;

let Predicates = [AtLeastM68020] in {
def PEA32q32 : MxPEA<MxOp32AddrMode_q32, MxEncAddrMode_q32<"src">>;
def PEA32p32 : MxPEA<MxOp32AddrMode_p32, MxEncAddrMode_p32<"src">>;
}
