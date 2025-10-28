

%Optional_dt = type {i8, [4 x i8]}


define i32 @summing(i32 %reg_0,i32 %reg_1) {
%reg_2 = add i32 %reg_0, %reg_1
ret i32 %reg_2
}
