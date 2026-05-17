; RUN: llc < %s -mtriple=m68k -mcpu=m68020 -code-model=medium -relocation-model=pic | FileCheck %s

@data = internal global i32 42

define i32 @get_data() {
entry:
; CHECK-LABEL: get_data:
; CHECK: lea (data,%pc), %a0
  %0 = load i32, ptr @data
  ret i32 %0
}

define void @set_data(i32 %val) {
entry:
; CHECK-LABEL: set_data:
; CHECK: lea (data,%pc), %a0
  store i32 %val, ptr @data
  ret void
}
