
declare i32 @puts(ptr)
@str_0=private unnamed_addr constant [2 x i8] c"H\00"




define void @"main"() {
entry:
%tmp_reg_0 = add i32 10, 20
call i32 @puts(ptr @str_0)
ret void

}
define ptr @"display$String$m55344248"(ptr %str) {
entry:
ret ptr %str

}
