//===-- M68kInstrAtomics.td - Atomics Instructions ---------*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

foreach size = [8, 16, 32] in {
  def : Pat<(!cast<SDPatternOperator>("atomic_load_"#size) MxCP_ARI:$ptr),
            (!cast<MxInst>("MOV"#size#"dj") !cast<MxMemOp>("MxARI"#size):$ptr)>;

  def : Pat<(!cast<SDPatternOperator>("atomic_load_"#size) MxCP_ARII:$ptr),
            (!cast<MxInst>("MOV"#size#"df") !cast<MxMemOp>("MxARII"#size):$ptr)>;

  def : Pat<(!cast<SDPatternOperator>("atomic_load_"#size) MxCP_ARID:$ptr),
            (!cast<MxInst>("MOV"#size#"dp") !cast<MxMemOp>("MxARID"#size):$ptr)>;

  def : Pat<(!cast<SDPatternOperator>("atomic_load_"#size) MxCP_PCD:$ptr),
            (!cast<MxInst>("MOV"#size#"dq") !cast<MxMemOp>("MxPCD"#size):$ptr)>;

  def : Pat<(!cast<SDPatternOperator>("atomic_load_"#size) MxCP_PCI:$ptr),
            (!cast<MxInst>("MOV"#size#"dk") !cast<MxMemOp>("MxPCI"#size):$ptr)>;

  def : Pat<(!cast<SDPatternOperator>("atomic_store_"#size) !cast<MxRegOp>("MxDRD"#size):$val, MxCP_ARI:$ptr),
            (!cast<MxInst>("MOV"#size#"jd") !cast<MxMemOp>("MxARI"#size):$ptr,
                                            !cast<MxRegOp>("MxDRD"#size):$val)>;

  def : Pat<(!cast<SDPatternOperator>("atomic_store_"#size) !cast<MxRegOp>("MxDRD"#size):$val, MxCP_ARID:$ptr),
            (!cast<MxInst>("MOV"#size#"pd") !cast<MxMemOp>("MxARID"#size):$ptr,
                                            !cast<MxRegOp>("MxDRD"#size):$val)>;

  def : Pat<(!cast<SDPatternOperator>("atomic_load_"#size) iPTR:$ptr),
            (!cast<MxInst>("MOV"#size#"dj") !cast<MxMemOp>("MxARI"#size):$ptr)>;

  def : Pat<(!cast<SDPatternOperator>("atomic_store_"#size) !cast<MxRegOp>("MxDRD"#size):$val, iPTR:$ptr),
            (!cast<MxInst>("MOV"#size#"jd") !cast<MxMemOp>("MxARI"#size):$ptr,
                                            !cast<MxRegOp>("MxDRD"#size):$val)>;
}

let Predicates = [AtLeastM68020] in {
let Defs = [CCR], mayLoad = 1, mayStore = 1 in {
class MxCASARIOp<bits<2> size_encoding, MxType type>
    : MxInst<(outs type.ROp:$out),
             (ins type.ROp:$dc, type.ROp:$du, !cast<MxMemOp>("MxARI"#type.Size):$mem),
             "cas."#type.Prefix#" $dc, $du, $mem",
             [(set type.VT:$out, CCR, (MxCas MxCP_ARI:$mem, type.VT:$dc, type.VT:$du))]> {
  let Inst = (ascend
                (descend 0b00001, size_encoding, 0b011, MxEncAddrMode_j<"mem">.EA),
                (descend 0b0000000, (operand "$du", 3), 0b000, (operand "$dc", 3))
              );
  let Constraints = "$out = $dc";
}

def CASARI8  : MxCASARIOp<0x1, MxType8d>;
def CASARI16 : MxCASARIOp<0x2, MxType16d>;
def CASARI32 : MxCASARIOp<0x3, MxType32d>;

class MxCASARIDOp<bits<2> size_encoding, MxType type>
    : MxInst<(outs type.ROp:$out),
             (ins type.ROp:$dc, type.ROp:$du, !cast<MxMemOp>("MxARID"#type.Size):$mem),
             "cas."#type.Prefix#" $dc, $du, $mem",
             [(set type.VT:$out, CCR, (MxCas MxCP_ARID:$mem, type.VT:$dc, type.VT:$du))]> {
  let Inst = (ascend
                (descend 0b00001, size_encoding, 0b011, MxEncAddrMode_p<"mem">.EA),
                (descend 0b0000000, (operand "$du", 3), 0b000, (operand "$dc", 3)),
                MxEncAddrMode_p<"mem">.Supplement
              );
  let Constraints = "$out = $dc";
}

def CASARID8  : MxCASARIDOp<0x1, MxType8d>;
def CASARID16 : MxCASARIDOp<0x2, MxType16d>;
def CASARID32 : MxCASARIDOp<0x3, MxType32d>;

class MxCASARIIOp<bits<2> size_encoding, MxType type>
    : MxInst<(outs type.ROp:$out),
             (ins type.ROp:$dc, type.ROp:$du, !cast<MxMemOp>("MxARII"#type.Size):$mem),
             "cas."#type.Prefix#" $dc, $du, $mem",
             [(set type.VT:$out, CCR, (MxCas MxCP_ARII:$mem, type.VT:$dc, type.VT:$du))]> {
  let Inst = (ascend
                (descend 0b00001, size_encoding, 0b011, MxEncAddrMode_f<"mem">.EA),
                (descend 0b0000000, (operand "$du", 3), 0b000, (operand "$dc", 3)),
                MxEncAddrMode_f<"mem">.Supplement
              );
  let Constraints = "$out = $dc";
}

def CASARII8  : MxCASARIIOp<0x1, MxType8d>;
def CASARII16 : MxCASARIIOp<0x2, MxType16d>;
def CASARII32 : MxCASARIIOp<0x3, MxType32d>;

class MxCASALOp<bits<2> size_encoding, MxType type>
    : MxInst<(outs type.ROp:$out),
             (ins type.ROp:$dc, type.ROp:$du, !cast<MxMemOp>("MxAL"#type.Size):$mem),
             "cas."#type.Prefix#" $dc, $du, $mem",
             [(set type.VT:$out, CCR, (MxCas MxCP_AL:$mem, type.VT:$dc, type.VT:$du))]> {
  let Inst = (ascend
                (descend 0b00001, size_encoding, 0b011, MxEncAddrMode_abs<"mem", true>.EA),
                (descend 0b0000000, (operand "$du", 3), 0b000, (operand "$dc", 3)),
                MxEncAddrMode_abs<"mem", true>.Supplement
              );
  let Constraints = "$out = $dc";
}

def CASAL8  : MxCASALOp<0x1, MxType8d>;
def CASAL16 : MxCASALOp<0x2, MxType16d>;
def CASAL32 : MxCASALOp<0x3, MxType32d>;
} // let Defs = [CCR], mayLoad = 1, mayStore = 1

// Fallback for raw pointers in registers
foreach size = [8, 16, 32] in {
  def : Pat<(set !cast<MxRegOp>("MxDRD"#size):$dc, CCR,
                 (MxCas iPTR:$ptr,
                        !cast<MxRegOp>("MxDRD"#size):$dc,
                        !cast<MxRegOp>("MxDRD"#size):$du)),
            (!cast<MxInst>("CASARI"#size) !cast<MxRegOp>("MxDRD"#size):$dc,
                                          !cast<MxRegOp>("MxDRD"#size):$du,
                                          !cast<MxMemOp>("MxARI"#size):$ptr)>;
}
} // let Predicates = [AtLeastM68020]

