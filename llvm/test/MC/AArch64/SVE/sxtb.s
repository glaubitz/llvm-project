// RUN: llvm-mc -triple=aarch64 -show-encoding -mattr=+sve < %s \
// RUN:        | FileCheck %s --check-prefixes=CHECK-ENCODING,CHECK-INST
// RUN: not llvm-mc -triple=aarch64 -show-encoding < %s 2>&1 \
// RUN:        | FileCheck %s --check-prefix=CHECK-ERROR
// RUN: llvm-mc -triple=aarch64 -filetype=obj -mattr=+sve < %s \
// RUN:        | llvm-objdump -d -mattr=+sve - | FileCheck %s --check-prefix=CHECK-INST
// RUN: llvm-mc -triple=aarch64 -filetype=obj -mattr=+sve < %s \
// RUN:        | llvm-objdump -d - | FileCheck %s --check-prefix=CHECK-UNKNOWN

sxtb    z0.h, p0/m, z0.h
// CHECK-INST: sxtb    z0.h, p0/m, z0.h
// CHECK-ENCODING: [0x00,0xa0,0x50,0x04]
// CHECK-ERROR: instruction requires: sve
// CHECK-UNKNOWN: 00 a0 50 04 <unknown>

sxtb    z0.s, p0/m, z0.s
// CHECK-INST: sxtb    z0.s, p0/m, z0.s
// CHECK-ENCODING: [0x00,0xa0,0x90,0x04]
// CHECK-ERROR: instruction requires: sve
// CHECK-UNKNOWN: 00 a0 90 04 <unknown>

sxtb    z0.d, p0/m, z0.d
// CHECK-INST: sxtb    z0.d, p0/m, z0.d
// CHECK-ENCODING: [0x00,0xa0,0xd0,0x04]
// CHECK-ERROR: instruction requires: sve
// CHECK-UNKNOWN: 00 a0 d0 04 <unknown>

sxtb    z31.h, p7/m, z31.h
// CHECK-INST: sxtb    z31.h, p7/m, z31.h
// CHECK-ENCODING: [0xff,0xbf,0x50,0x04]
// CHECK-ERROR: instruction requires: sve
// CHECK-UNKNOWN: ff bf 50 04 <unknown>

sxtb    z31.s, p7/m, z31.s
// CHECK-INST: sxtb    z31.s, p7/m, z31.s
// CHECK-ENCODING: [0xff,0xbf,0x90,0x04]
// CHECK-ERROR: instruction requires: sve
// CHECK-UNKNOWN: ff bf 90 04 <unknown>

sxtb    z31.d, p7/m, z31.d
// CHECK-INST: sxtb    z31.d, p7/m, z31.d
// CHECK-ENCODING: [0xff,0xbf,0xd0,0x04]
// CHECK-ERROR: instruction requires: sve
// CHECK-UNKNOWN: ff bf d0 04 <unknown>