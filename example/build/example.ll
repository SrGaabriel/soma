

define i1 @areNumEqual(i32 %reg_3,i32 %reg_4) {
%reg_5 = icmp eq i32 %reg_4, %reg_3
ret i1 %reg_5
}
define i32 @testSum(i32 %reg_0,i32 %reg_1) {
%reg_2 = add i32 %reg_1, %reg_0
ret i32 %reg_2
}
