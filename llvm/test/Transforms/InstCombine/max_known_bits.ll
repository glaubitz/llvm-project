; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -S -instcombine < %s | FileCheck %s
; TODO: The entire thing should be folded to and i16 %0, 255.

define i16 @foo(i16 )  {
; CHECK-LABEL: @foo(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[TMP1:%.*]] = and i16 [[TMP0:%.*]], 255
; CHECK-NEXT:    [[TMP2:%.*]] = zext i16 [[TMP1]] to i32
; CHECK-NEXT:    [[TMP3:%.*]] = icmp ult i32 [[TMP2]], 255
; CHECK-NEXT:    [[TMP4:%.*]] = select i1 [[TMP3]], i32 [[TMP2]], i32 255
; CHECK-NEXT:    [[TMP5:%.*]] = trunc i32 [[TMP4]] to i16
; CHECK-NEXT:    [[TMP6:%.*]] = and i16 [[TMP5]], 255
; CHECK-NEXT:    ret i16 [[TMP6]]
;
entry:
  %1 = and i16 %0, 255
  %2 = zext i16 %1 to i32
  %3 = icmp ult i32 %2, 255
  %4 = select i1 %3, i32 %2, i32 255
  %5 = trunc i32 %4 to i16
  %6 = and i16 %5, 255
  ret i16 %6
}