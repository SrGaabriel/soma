

%MaybeInt = type {i8, [4 x i8]}


define i1 @areNumEqual(i32 %reg_10,i32 %reg_11) {
%reg_12 = icmp eq i32 %reg_11, %reg_10
ret i1 %reg_12
}
define i32 @testSum(i32 %reg_7,i32 %reg_8) {
%reg_9 = add i32 %reg_8, %reg_7
ret i32 %reg_9
}
define %MaybeInt @giveMaybeInt(i32 %reg_0) {
%reg_1 = alloca %MaybeInt
%reg_2 = getelementptr %MaybeInt, ptr %reg_1, i32 0, i32 0
store i8 0, ptr %reg_2
%reg_3 = getelementptr %MaybeInt, ptr %reg_1, i32 0, i32 1
%reg_4 = getelementptr [4 x i8], ptr %reg_3, i32 0, i32 0
%reg_5 = bitcast i8* %reg_4 to i32*
store i32 %reg_0, ptr %reg_5
%reg_6 = load %MaybeInt, ptr %reg_1
ret %MaybeInt %reg_6
}
