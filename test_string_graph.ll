
declare i64 @inet_reduce(ptr,i64)
@g_inet = external global ptr
declare i64 @inet_num_ext(i64)
declare void @inet_register_func(ptr,ptr,i16,ptr)
@str_1=private unnamed_addr constant [22 x i8] c"getGreeting$m72886682\00"
@str_0=private unnamed_addr constant [14 x i8] c"Hello, World!\00"




define i32 @"soma_main"() {
block1:
%tmp_reg_2 = load ptr, ptr @g_inet
%tmp_reg_3 = select i1 true, ptr @"getGreeting$m72886682", ptr @"getGreeting$m72886682"
call void @inet_register_func(ptr %tmp_reg_2, ptr @str_1, i16 0, ptr %tmp_reg_3)
%tmp_reg_4 = sext i32 42 to i64
%tmp_reg_5 = call i64 @inet_num_ext(i64 %tmp_reg_4)
%tmp_reg_6 = load ptr, ptr @g_inet
%tmp_reg_7 = call i64 @inet_reduce(ptr %tmp_reg_6, i64 %tmp_reg_5)
%tmp_reg_8 = trunc i64 %tmp_reg_7 to i32
ret i32 %tmp_reg_8

}
define i64 @"getGreeting$m72886682"(ptr %net,ptr %tm,i64 %arg) {
block0:
%tmp_reg_0 = ptrtoint ptr @str_0 to i64
%tmp_reg_1 = call i64 @inet_num_ext(i64 %tmp_reg_0)
ret i64 %tmp_reg_1

}
