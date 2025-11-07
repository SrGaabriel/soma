

define i1 @totallyGenericEqGen$Optional({i8, i64} %left,{i8, i64} %right) {
entry:
%tmp_reg_24 = call i1 @equals({i8, i64} %left, {i8, i64} %right)
ret i1 %tmp_reg_24

}
define i1 @totallyGenericEqGen(i32 %left,i32 %right) {
entry:
%tmp_reg_23 = call i1 @equals(i32 %left, i32 %right)
ret i1 %tmp_reg_23

}
define i1 @testTotallyGenericEqGenOptional({i8, i64} %left,{i8, i64} %right) {
entry:
%tmp_reg_22 = call i1 @totallyGenericEqGen$Optional({i8, i64} %left, {i8, i64} %right)
ret i1 %tmp_reg_22

}
define i1 @testTotallyGenericEqGen(i32 %left,i32 %right) {
entry:
%tmp_reg_21 = call i1 @totallyGenericEqGen(i32 %left, i32 %right)
ret i1 %tmp_reg_21

}
define i32 @testSum(i32 %x,i32 %y) {
entry:
%tmp_reg_20 = add i32 %x, %y
ret i32 %tmp_reg_20

}
define i1 @testOptionalEqGen() {
entry:
%tmp_reg_15 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_16 = zext i32 5 to i64
%tmp_reg_17 = insertvalue {i8, i64} %tmp_reg_15, i64 %tmp_reg_16, 1
%tmp_reg_18 = call {i8, i64} @pureOptionalInt(i32 5)
%tmp_reg_19 = call i1 @equals({i8, i64} %tmp_reg_17, {i8, i64} %tmp_reg_18)
ret i1 %tmp_reg_19

}
define i1 @testOptionalEq({i8, i64} %x,{i8, i64} %y) {
entry:
%tmp_reg_14 = call i1 @equals({i8, i64} %x, {i8, i64} %y)
ret i1 %tmp_reg_14

}
define {i8, i64} @pureOptionalInt(i32 %value) {
entry:
%tmp_reg_11 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_12 = zext i32 %value to i64
%tmp_reg_13 = insertvalue {i8, i64} %tmp_reg_11, i64 %tmp_reg_12, 1
ret {i8, i64} %tmp_reg_13

}
define {i8, i64} @pureMaybeInt(i32 %value) {
entry:
%tmp_reg_8 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_9 = zext i32 %value to i64
%tmp_reg_10 = insertvalue {i8, i64} %tmp_reg_8, i64 %tmp_reg_9, 1
ret {i8, i64} %tmp_reg_10

}
define {i8, i64} @primeNumbers() {
entry:
%tmp_reg_3 = alloca [4 x i32]
%tmp_reg_4 = getelementptr inbounds i32, ptr %tmp_reg_3, i32 0
store i32 2, ptr %tmp_reg_4
%tmp_reg_5 = getelementptr inbounds i32, ptr %tmp_reg_3, i32 1
store i32 3, ptr %tmp_reg_5
%tmp_reg_6 = getelementptr inbounds i32, ptr %tmp_reg_3, i32 2
store i32 5, ptr %tmp_reg_6
%tmp_reg_7 = getelementptr inbounds i32, ptr %tmp_reg_3, i32 3
store i32 7, ptr %tmp_reg_7
ret ptr %tmp_reg_3

}
define void @main() {
entry:
%tmp_reg_1 = call {i8, i64} @map(ptr @lambda$0, ptr @primeNumbers)
%tmp_reg_2 = call void @println({i8, i64} %tmp_reg_1)
ret void

}
define i32 @lambda$0(i32 %x) {
entry:
ret i32 1

}
define i1 @isZero(i32 %arg0) {
block0:
switch i32 %arg0, label %block3 [i32 0, label %block2]

block2:
ret i1 1

block3:
ret i1 0

}
define i1 @areNumEqual(i32 %num1,i32 %num2) {
entry:
%tmp_reg_0 = icmp eq i32 %num1, %num2
ret i1 %tmp_reg_0

}
