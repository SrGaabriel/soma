

%Optional = type {i8, [4 x i8]}
%Maybe_Int = type {i8, [4 x i8]}


define i1 @areNumEqual(i32 %reg_14,i32 %reg_15) {
%reg_16 = icmp eq i32 %reg_15, %reg_14
ret i1 %reg_16
}
define i32 @testSum(i32 %reg_11,i32 %reg_12) {
%reg_13 = add i32 %reg_12, %reg_11
ret i32 %reg_13
}
define %Optional @pureOptionalInt(i32 %reg_7) {
%reg_8 = alloca %Optional
%reg_9 = getelementptr %Optional, ptr %reg_8, i32 0, i32 0
store i8 0, ptr %reg_9
%reg_10 = load %Optional, ptr %reg_8
ret %Optional %reg_10
}
define %Maybe_Int @pureMaybeInt(i32 %reg_0) {
%reg_1 = alloca %Maybe_Int
%reg_2 = getelementptr %Maybe_Int, ptr %reg_1, i32 0, i32 0
store i8 0, ptr %reg_2
%reg_3 = getelementptr %Maybe_Int, ptr %reg_1, i32 0, i32 1
%reg_4 = getelementptr [4 x i8], ptr %reg_3, i32 0, i32 0
%reg_5 = bitcast i8* %reg_4 to i32*
store i32 %reg_0, ptr %reg_5
%reg_6 = load %Maybe_Int, ptr %reg_1
ret %Maybe_Int %reg_6
}
