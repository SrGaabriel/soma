%Display$Dict = type { ptr (ptr)* }
%Eq$Dict = type { i1 ({i8, i64}, {i8, i64})* }

declare i32 @puts(ptr)
@str_3=private unnamed_addr constant [16 x i8] c"<unknown shape>\00"
@str_2=private unnamed_addr constant [10 x i8] c"Optional!\00"
@str_1=private unnamed_addr constant [16 x i8] c"<unimplemented>\00"
@str_0=private unnamed_addr constant [7 x i8] c"<list>\00"


@dict$Display$Array = internal constant %Display$Dict { ptr (ptr)* @display$Array }
@dict$Display$Int = internal constant %Display$Dict { ptr (i32)* @display$Int }
@dict$Display$Optional = internal constant %Display$Dict { ptr ({i8, i64})* @display$Optional }
@dict$Display$Shape = internal constant %Display$Dict { ptr ({i8, i64})* @display$Shape }
@dict$Display$String = internal constant %Display$Dict { ptr (ptr)* @display$String }
@dict$Eq$Optional = internal constant %Eq$Dict { i1 ({i8, i64}, {i8, i64})* @equals$Optional }


define i1 @totallyGenericEqGen(ptr %dict$Eq$Ta,i32 %left,i32 %right) {
entry:
%tmp_reg_39 = getelementptr %Eq$Dict, ptr %dict$Eq$Ta, i32 0, i32 0
%tmp_reg_40 = load i1 (i32, i32)*, ptr %tmp_reg_39
%tmp_reg_41 = call i1 %tmp_reg_40(i32 %left, i32 %right)
ret i1 %tmp_reg_41

}
define i1 @testTotallyGenericEqGenOptional({i8, i64} %left,{i8, i64} %right) {
entry:
%tmp_reg_38 = call i1 @totallyGenericEqGen(ptr @dict$Eq$Optional, {i8, i64} %left, {i8, i64} %right)
ret i1 %tmp_reg_38

}
define i1 @testTotallyGenericEqGen(ptr %dict$Eq$Ta,i32 %left,i32 %right) {
entry:
%tmp_reg_37 = call i1 @totallyGenericEqGen(i32 %left, i32 %right)
ret i1 %tmp_reg_37

}
define i32 @testSum(i32 %x,i32 %y) {
entry:
%tmp_reg_36 = add i32 %x, %y
ret i32 %tmp_reg_36

}
define i1 @testOptionalEqGen() {
entry:
%tmp_reg_31 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_32 = zext i32 5 to i64
%tmp_reg_33 = insertvalue {i8, i64} %tmp_reg_31, i64 %tmp_reg_32, 1
%tmp_reg_34 = call {i8, i64} @pureOptionalInt(i32 5)
%tmp_reg_35 = call i1 @equals$Optional({i8, i64} %tmp_reg_33, {i8, i64} %tmp_reg_34)
ret i1 %tmp_reg_35

}
define i1 @testOptionalEq({i8, i64} %x,{i8, i64} %y) {
entry:
%tmp_reg_30 = call i1 @equals$Optional({i8, i64} %x, {i8, i64} %y)
ret i1 %tmp_reg_30

}
define {i8, i64} @pureOptionalInt(i32 %value) {
entry:
%tmp_reg_27 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_28 = zext i32 %value to i64
%tmp_reg_29 = insertvalue {i8, i64} %tmp_reg_27, i64 %tmp_reg_28, 1
ret {i8, i64} %tmp_reg_29

}
define {i8, i64} @pureMaybeInt(i32 %value) {
entry:
%tmp_reg_24 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_25 = zext i32 %value to i64
%tmp_reg_26 = insertvalue {i8, i64} %tmp_reg_24, i64 %tmp_reg_25, 1
ret {i8, i64} %tmp_reg_26

}
define ptr @primeNumbers() {
entry:
%tmp_reg_19 = alloca [4 x i32]
%tmp_reg_20 = getelementptr inbounds i32, ptr %tmp_reg_19, i32 0
store i32 2, ptr %tmp_reg_20
%tmp_reg_21 = getelementptr inbounds i32, ptr %tmp_reg_19, i32 1
store i32 3, ptr %tmp_reg_21
%tmp_reg_22 = getelementptr inbounds i32, ptr %tmp_reg_19, i32 2
store i32 5, ptr %tmp_reg_22
%tmp_reg_23 = getelementptr inbounds i32, ptr %tmp_reg_19, i32 3
store i32 7, ptr %tmp_reg_23
ret ptr %tmp_reg_19

}
define void @main() {
entry:
%tmp_reg_8 = alloca [4 x i32]
%tmp_reg_9 = alloca i32
store i32 0, ptr %tmp_reg_9
br label %map_cond_10
map_cond_10:
%tmp_reg_10 = load i32, ptr %tmp_reg_9
%tmp_reg_11 = icmp slt i32 %tmp_reg_10, 4
br i1 %tmp_reg_11, label %map_body_11, label %map_end_12
map_body_11:
%tmp_reg_12 = load i32, ptr %tmp_reg_9
%tmp_reg_13 = getelementptr inbounds i32, ptr @primeNumbers, i32 %tmp_reg_12
%tmp_reg_14 = load i32, ptr %tmp_reg_13
%tmp_reg_15 = call i32 @lambda$0(i32 %tmp_reg_14)
%tmp_reg_16 = getelementptr inbounds i32, ptr %tmp_reg_8, i32 %tmp_reg_12
store i32 %tmp_reg_15, ptr %tmp_reg_16
%tmp_reg_17 = add i32 %tmp_reg_12, 1
store i32 %tmp_reg_17, ptr %tmp_reg_9
br label %map_cond_10
map_end_12:
%tmp_reg_18 = call ptr @display$Array(ptr %tmp_reg_8)
call i32 @puts(ptr %tmp_reg_18)
ret void

}
define i32 @lambda$0(i32 %x) {
entry:
ret i32 1

}
define i1 @isZero(i32 %arg0) {
block5:
switch i32 %arg0, label %block8 [i32 0, label %block7]

block7:
ret i1 1

block8:
ret i1 0

}
define i1 @equals$Optional({i8, i64} %x,{i8, i64} %y) {
entry:
ret i1 1

}
define ptr @display$String(ptr %str) {
entry:
ret ptr %str

}
define ptr @display$Shape({i8, i64} %arg0) {
block0:
%tmp_reg_1 = extractvalue {i8, i64} %arg0, 0
switch i8 %tmp_reg_1, label %block4 [i8 1, label %block2 i8 0, label %block3]

block2:
%tmp_reg_2 = extractvalue {i8, i64} %arg0, 1
%tmp_reg_3 = trunc i64 %tmp_reg_2 to i32
%tmp_reg_4 = call ptr @display$Int(i32 %tmp_reg_3)
ret ptr %tmp_reg_4

block3:
%tmp_reg_5 = extractvalue {i8, i64} %arg0, 1
%tmp_reg_6 = trunc i64 %tmp_reg_5 to i32
%tmp_reg_7 = call ptr @display$Int(i32 %tmp_reg_6)
ret ptr %tmp_reg_7

block4:
ret ptr @str_3

}
define ptr @display$Optional({i8, i64} %optional) {
entry:
ret ptr @str_2

}
define ptr @display$Int(i32 %num) {
entry:
ret ptr @str_1

}
define ptr @display$Array(ptr %lst) {
entry:
ret ptr @str_0

}
define i1 @areNumEqual(i32 %num1,i32 %num2) {
entry:
%tmp_reg_0 = icmp eq i32 %num1, %num2
ret i1 %tmp_reg_0

}
