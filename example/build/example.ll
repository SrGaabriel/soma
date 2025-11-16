%Display$m55344248$Dict = type { ptr }
%Eq$m55344248$Dict = type { ptr }
%Monad$m55344248$Dict = type { ptr }

declare i32 @puts(ptr)
@str_3=private unnamed_addr constant [16 x i8] c"<unknown shape>\00"
@str_2=private unnamed_addr constant [10 x i8] c"Optional!\00"
@str_1=private unnamed_addr constant [16 x i8] c"<unimplemented>\00"
@str_0=private unnamed_addr constant [7 x i8] c"<list>\00"


@dict$Display$Array$m55344248 = internal constant %Display$m55344248$Dict { i8* @display$Array$m55344248 }
@dict$Display$Int$m55344248 = internal constant %Display$m55344248$Dict { i8* @display$Int$m55344248 }
@dict$Display$Optional$m55344248 = internal constant %Display$m55344248$Dict { i8* @display$Optional$m55344248 }
@dict$Display$Shape$m55344248 = internal constant %Display$m55344248$Dict { i8* @display$Shape$m55344248 }
@dict$Display$String$m55344248 = internal constant %Display$m55344248$Dict { i8* @display$String$m55344248 }
@dict$Eq$Optional$m55344248 = internal constant %Eq$m55344248$Dict { i8* @equals$Optional$m55344248 }
@dict$Monad$IO$m55344248 = internal constant %Monad$m55344248$Dict { i8* @pure$IO$m55344248 }


define i1 @totallyGenericEqGen$m55344248(ptr %dict$Eq$Ta,i32 %left,i32 %right) {
entry:
%tmp_reg_42 = getelementptr %Eq$m55344248$Dict, ptr %dict$Eq$Ta, i32 0, i32 0
%tmp_reg_43 = load i1 (i32, i32)*, ptr %tmp_reg_42
%tmp_reg_44 = call i1 %tmp_reg_43(i32 %left, i32 %right)
ret i1 %tmp_reg_44

}
define i1 @testTotallyGenericEqGenOptional$m55344248({i8, i64} %left,{i8, i64} %right) {
entry:
%tmp_reg_41 = call i1 @totallyGenericEqGen$m55344248(ptr @dict$Eq$Optional$m55344248, {i8, i64} %left, {i8, i64} %right)
ret i1 %tmp_reg_41

}
define i1 @testTotallyGenericEqGen$m55344248(ptr %dict$Eq$Ta,i32 %left,i32 %right) {
entry:
%tmp_reg_40 = call i1 @totallyGenericEqGen$m55344248(i32 %left, i32 %right)
ret i1 %tmp_reg_40

}
define i32 @testSum$m55344248(i32 %x,i32 %y) {
entry:
%tmp_reg_39 = add i32 %x, %y
ret i32 %tmp_reg_39

}
define i1 @testOptionalEqGen$m55344248() {
entry:
%tmp_reg_34 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_35 = zext i32 5 to i64
%tmp_reg_36 = insertvalue {i8, i64} %tmp_reg_34, i64 %tmp_reg_35, 1
%tmp_reg_37 = call {i8, i64} @pureOptionalInt$m55344248(i32 5)
%tmp_reg_38 = call i1 @equals$Optional$m55344248({i8, i64} %tmp_reg_36, {i8, i64} %tmp_reg_37)
ret i1 %tmp_reg_38

}
define i1 @testOptionalEq$m55344248({i8, i64} %x,{i8, i64} %y) {
entry:
%tmp_reg_33 = call i1 @equals$Optional$m55344248({i8, i64} %x, {i8, i64} %y)
ret i1 %tmp_reg_33

}
define i32 @summing$m55344248(i32 %x,i32 %y) {
entry:
%tmp_reg_32 = add i32 %x, %y
ret i32 %tmp_reg_32

}
define {i8, i64} @pureOptionalInt$m55344248(i32 %value) {
entry:
%tmp_reg_29 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_30 = zext i32 %value to i64
%tmp_reg_31 = insertvalue {i8, i64} %tmp_reg_29, i64 %tmp_reg_30, 1
ret {i8, i64} %tmp_reg_31

}
define {i8, i64} @pureMaybeInt$m55344248(i32 %value) {
entry:
%tmp_reg_26 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_27 = zext i32 %value to i64
%tmp_reg_28 = insertvalue {i8, i64} %tmp_reg_26, i64 %tmp_reg_27, 1
ret {i8, i64} %tmp_reg_28

}
define i32 @pure$IO$m55344248(i32 %value) {
entry:
ret i32 %value

}
define ptr @primeNumbers$m55344248() {
entry:
%tmp_reg_21 = alloca [4 x i32]
%tmp_reg_22 = getelementptr inbounds i32, ptr %tmp_reg_21, i32 0
store i32 2, ptr %tmp_reg_22
%tmp_reg_23 = getelementptr inbounds i32, ptr %tmp_reg_21, i32 1
store i32 3, ptr %tmp_reg_23
%tmp_reg_24 = getelementptr inbounds i32, ptr %tmp_reg_21, i32 2
store i32 5, ptr %tmp_reg_24
%tmp_reg_25 = getelementptr inbounds i32, ptr %tmp_reg_21, i32 3
store i32 7, ptr %tmp_reg_25
ret ptr %tmp_reg_21

}
define i32 @main() {
entry:
%tmp_reg_8 = call i32 @id$Int$m55344248$m55344248(i32 5)
%tmp_reg_9 = call ptr @primeNumbers$m55344248()
%tmp_reg_10 = alloca [4 x i32]
%tmp_reg_11 = alloca i32
store i32 0, ptr %tmp_reg_11
br label %map_cond_12
map_cond_12:
%tmp_reg_12 = load i32, ptr %tmp_reg_11
%tmp_reg_13 = icmp slt i32 %tmp_reg_12, 4
br i1 %tmp_reg_13, label %map_body_13, label %map_end_14
map_body_13:
%tmp_reg_14 = load i32, ptr %tmp_reg_11
%tmp_reg_15 = getelementptr inbounds i32, ptr %tmp_reg_9, i32 %tmp_reg_14
%tmp_reg_16 = load i32, ptr %tmp_reg_15
%tmp_reg_17 = call i32 @lambda$0$m55344248(i32 %tmp_reg_16)
%tmp_reg_18 = getelementptr inbounds i32, ptr %tmp_reg_10, i32 %tmp_reg_14
store i32 %tmp_reg_17, ptr %tmp_reg_18
%tmp_reg_19 = add i32 %tmp_reg_14, 1
store i32 %tmp_reg_19, ptr %tmp_reg_11
br label %map_cond_12
map_end_14:
br label %block9

block9:
%tmp_reg_20 = call ptr @display$Array$m55344248(ptr %tmp_reg_10)
call i32 @puts(ptr %tmp_reg_20)
ret i32 0

}
define i32 @lambda$0$m55344248(i32 %x) {
entry:
ret i32 1

}
define i1 @isZero$m55344248(i32 %arg0) {
block5:
switch i32 %arg0, label %block8 [i32 0, label %block7]

block7:
ret i1 1

block8:
ret i1 0

}
define i32 @id$Int$m55344248$m55344248(i32 %value) {
entry:
ret i32 %value

}
define i32 @id$m55344248(i32 %value) {
entry:
ret i32 %value

}
define i1 @equals$Optional$m55344248({i8, i64} %x,{i8, i64} %y) {
entry:
ret i1 1

}
define ptr @display$String$m55344248(ptr %str) {
entry:
ret ptr %str

}
define ptr @display$Shape$m55344248({i8, i64} %arg0) {
block0:
%tmp_reg_1 = extractvalue {i8, i64} %arg0, 0
switch i8 %tmp_reg_1, label %block4 [i8 1, label %block2 i8 0, label %block3]

block2:
%tmp_reg_2 = extractvalue {i8, i64} %arg0, 1
%tmp_reg_3 = trunc i64 %tmp_reg_2 to i32
%tmp_reg_4 = call ptr @display$Int$m55344248(i32 %tmp_reg_3)
ret ptr %tmp_reg_4

block3:
%tmp_reg_5 = extractvalue {i8, i64} %arg0, 1
%tmp_reg_6 = trunc i64 %tmp_reg_5 to i32
%tmp_reg_7 = call ptr @display$Int$m55344248(i32 %tmp_reg_6)
ret ptr %tmp_reg_7

block4:
ret ptr @str_3

}
define ptr @display$Optional$m55344248({i8, i64} %optional) {
entry:
ret ptr @str_2

}
define ptr @display$Int$m55344248(i32 %num) {
entry:
ret ptr @str_1

}
define ptr @display$Array$m55344248(ptr %lst) {
entry:
ret ptr @str_0

}
define i1 @areNumEqual$m55344248(i32 %num1,i32 %num2) {
entry:
%tmp_reg_0 = icmp eq i32 %num1, %num2
ret i1 %tmp_reg_0

}
