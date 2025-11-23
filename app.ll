




define i32 @testSum$m68435900(i32 %x,i32 %y) {
entry:
%tmp_reg_18 = add i32 %x, %y
ret i32 %tmp_reg_18

}
define {i8, i64} @testShape$m68435900() {
entry:
%tmp_reg_15 = insertvalue {i8, i64} undef, i8 1, 0
%tmp_reg_16 = zext i32 5 to i64
%tmp_reg_17 = insertvalue {i8, i64} %tmp_reg_15, i64 %tmp_reg_16, 1
ret {i8, i64} %tmp_reg_17

}
define i32 @sum$m68435900() {
entry:
%tmp_reg_14 = add i32 5, 3
ret i32 %tmp_reg_14

}
define i32 @statefulCompute$m68435900(i32 %arg0,i32 %arg1) {
block23:
%tmp_reg_13 = add i32 %arg0, %arg1
ret i32 %tmp_reg_13

}
define i1 @isZero$m68435900(i32 %arg0) {
block17:
switch i32 %arg0, label %block20 [i32 0, label %block19]

block19:
ret i1 1

block20:
ret i1 0

}
define i1 @equals$Shape$m68435900({i8, i64} %arg0,{i8, i64} %arg1) {
block2:
%tmp_reg_1 = extractvalue {i8, i64} %arg0, 0
switch i8 %tmp_reg_1, label %block6 [i8 1, label %block4 i8 0, label %block5]

block4:
%tmp_reg_2 = extractvalue {i8, i64} %arg1, 0
switch i8 %tmp_reg_2, label %block8 [i8 1, label %block7]

block7:
%tmp_reg_3 = extractvalue {i8, i64} %arg0, 1
%tmp_reg_4 = trunc i64 %tmp_reg_3 to i32
%tmp_reg_5 = extractvalue {i8, i64} %arg1, 1
%tmp_reg_6 = trunc i64 %tmp_reg_5 to i32
%tmp_reg_7 = call i1 @equals$Int$m68435900(i32 %tmp_reg_4, i32 %tmp_reg_6)
ret i1 %tmp_reg_7

block8:
ret i1 0

block5:
%tmp_reg_8 = extractvalue {i8, i64} %arg1, 0
switch i8 %tmp_reg_8, label %block10 [i8 0, label %block9]

block9:
%tmp_reg_9 = extractvalue {i8, i64} %arg0, 1
%tmp_reg_10 = trunc i64 %tmp_reg_9 to i32
%tmp_reg_11 = extractvalue {i8, i64} %arg1, 1
%tmp_reg_12 = trunc i64 %tmp_reg_11 to i32
ret i1 1

block10:
ret i1 0

block6:
ret i1 0

}
define i1 @equals$Int$m68435900(i32 %x,i32 %y) {
entry:
ret i1 1

}
define i1 @areNumEqual$m68435900(i32 %num1,i32 %num2) {
entry:
%tmp_reg_0 = call i1 @equals$Int$m68435900(i32 %num1, i32 %num2)
ret i1 %tmp_reg_0

}
