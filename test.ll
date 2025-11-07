

define {i8, i64} @validateAndAdd(i32 %arg0,i32 %arg1) {
block31:
%tmp_reg_24 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_25 = zext i32 %arg0 to i64
%tmp_reg_26 = insertvalue {i8, i64} %tmp_reg_24, i64 %tmp_reg_25, 1
br label %block34

block34:
%tmp_reg_27 = extractvalue {i8, i64} %tmp_reg_26, 1
%tmp_reg_28 = trunc i64 %tmp_reg_27 to i32
%tmp_reg_29 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_30 = zext i32 %arg1 to i64
%tmp_reg_31 = insertvalue {i8, i64} %tmp_reg_29, i64 %tmp_reg_30, 1
br label %block36

block36:
%tmp_reg_32 = extractvalue {i8, i64} %tmp_reg_31, 1
%tmp_reg_33 = trunc i64 %tmp_reg_32 to i32
%tmp_reg_34 = add i32 %tmp_reg_28, %tmp_reg_33
%tmp_reg_35 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_36 = zext i32 %tmp_reg_34 to i64
%tmp_reg_37 = insertvalue {i8, i64} %tmp_reg_35, i64 %tmp_reg_36, 1
ret {i8, i64} %tmp_reg_37

}
define i32 @testStateMem2Reg(i1 %arg0) {
block25:
ret i32 1

}
define i32 @statefulCompute(i32 %arg0,i32 %arg1) {
block23:
%tmp_reg_23 = add i32 %arg0, %arg1
ret i32 %tmp_reg_23

}
define i32 @stateBranch(i32 %arg0) {
block17:
ret i32 10

}
define i32 @multiRef(i32 %arg0) {
block15:
%tmp_reg_21 = add i32 %arg0, 1
%tmp_reg_22 = add i32 %arg0, %tmp_reg_21
ret i32 %tmp_reg_22

}
define void @main() {
block8:
%tmp_reg_15 = call i32 @testStateMem2Reg(i1 1)
%tmp_reg_16 = call i32 @testStateMem2Reg(i1 0)
%tmp_reg_17 = call i32 @statefulCompute(i32 10, i32 20)
%tmp_reg_18 = call i32 @stateBranch(i32 5)
%tmp_reg_19 = call {i8, i64} @validateAndAdd(i32 3, i32 7)
%tmp_reg_20 = call i32 @multiRef(i32 100)
br i1 1, label %block12, label %block12

block12:
ret void

}
define {i8, i64} @eitherChain(i32 %arg0) {
block2:
%tmp_reg_0 = insertvalue {i8, i64} undef, i8 1, 0
%tmp_reg_1 = zext i32 %arg0 to i64
%tmp_reg_2 = insertvalue {i8, i64} %tmp_reg_0, i64 %tmp_reg_1, 1
br label %block5

block5:
%tmp_reg_3 = extractvalue {i8, i64} %tmp_reg_2, 1
%tmp_reg_4 = trunc i64 %tmp_reg_3 to i32
%tmp_reg_5 = add i32 %tmp_reg_4, 1
%tmp_reg_6 = insertvalue {i8, i64} undef, i8 1, 0
%tmp_reg_7 = zext i32 %tmp_reg_5 to i64
%tmp_reg_8 = insertvalue {i8, i64} %tmp_reg_6, i64 %tmp_reg_7, 1
br label %block7

block7:
%tmp_reg_9 = extractvalue {i8, i64} %tmp_reg_8, 1
%tmp_reg_10 = trunc i64 %tmp_reg_9 to i32
%tmp_reg_11 = add i32 %tmp_reg_10, 10
%tmp_reg_12 = insertvalue {i8, i64} undef, i8 1, 0
%tmp_reg_13 = zext i32 %tmp_reg_11 to i64
%tmp_reg_14 = insertvalue {i8, i64} %tmp_reg_12, i64 %tmp_reg_13, 1
ret {i8, i64} %tmp_reg_14

}
