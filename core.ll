
declare i32 @printf(ptr,...)
@str_1=private unnamed_addr constant [4 x i8] c"%d\0A\00"
@str_0=private unnamed_addr constant [4 x i8] c"num\00"




define void @"main"() {
entry:
%tmp_reg_1 = call i32 @"<>$Int$m22343894"(i32 10, i32 20)
call i32 @printf(ptr @str_1, i32 %tmp_reg_1)
ret void

}
define ptr @"display$Int$m22343894"(i32 %x) {
entry:
ret ptr @str_0

}
define i32 @"<>$Int$m22343894"(i32 %x,i32 %y) {
entry:
%tmp_reg_0 = add i32 %x, %y
ret i32 %tmp_reg_0

}
