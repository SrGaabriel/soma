
declare i64 @inet_reduce(ptr,i64)
@g_inet = external global ptr
declare i64 @inet_ref(ptr,ptr,i16,i64)
@g_inet_tm = external global ptr
declare i64 @inet_num_ext(i64)
declare void @inet_register_func(ptr,ptr,i16,ptr)
@str_0=private unnamed_addr constant [14 x i8] c"fib$m30910637\00"
declare i64 @inet_opr(ptr,ptr,i16,i64,i64)
declare i64 @inet_get_num_ext(i64)




define i32 @"soma_main"() {
block5:
%tmp_reg_17 = load ptr, ptr @g_inet
%tmp_reg_18 = select i1 true, ptr @"fib$m30910637", ptr @"fib$m30910637"
call void @inet_register_func(ptr %tmp_reg_17, ptr @str_0, i16 1, ptr %tmp_reg_18)
%tmp_reg_19 = sext i32 40 to i64
%tmp_reg_20 = call i64 @inet_num_ext(i64 %tmp_reg_19)
%tmp_reg_21 = load ptr, ptr @g_inet
%tmp_reg_22 = load ptr, ptr @g_inet_tm
%tmp_reg_23 = call i64 @inet_ref(ptr %tmp_reg_21, ptr %tmp_reg_22, i16 0, i64 %tmp_reg_20)
%tmp_reg_24 = load ptr, ptr @g_inet
%tmp_reg_25 = call i64 @inet_reduce(ptr %tmp_reg_24, i64 %tmp_reg_23)
%tmp_reg_26 = trunc i64 %tmp_reg_25 to i32
ret i32 %tmp_reg_26

}
define i64 @"fib$m30910637"(ptr %net,ptr %tm,i64 %arg) {
block0:
%tmp_reg_0 = call i64 @inet_get_num_ext(i64 %arg)
%tmp_reg_1 = trunc i64 %tmp_reg_0 to i32
switch i32 %tmp_reg_1, label %block4 [i32 0, label %block2 i32 1, label %block3]

block2:
%tmp_reg_2 = sext i32 0 to i64
%tmp_reg_3 = call i64 @inet_num_ext(i64 %tmp_reg_2)
ret i64 %tmp_reg_3

block3:
%tmp_reg_4 = sext i32 1 to i64
%tmp_reg_5 = call i64 @inet_num_ext(i64 %tmp_reg_4)
ret i64 %tmp_reg_5

block4:
%tmp_reg_6 = add i32 1, 0
%tmp_reg_7 = sub i32 %tmp_reg_1, %tmp_reg_6
%tmp_reg_8 = sext i32 %tmp_reg_7 to i64
%tmp_reg_9 = call i64 @inet_num_ext(i64 %tmp_reg_8)
%tmp_reg_10 = call i64 @inet_ref(ptr %net, ptr %tm, i16 0, i64 %tmp_reg_9)
%tmp_reg_11 = add i32 2, 0
%tmp_reg_12 = sub i32 %tmp_reg_1, %tmp_reg_11
%tmp_reg_13 = sext i32 %tmp_reg_12 to i64
%tmp_reg_14 = call i64 @inet_num_ext(i64 %tmp_reg_13)
%tmp_reg_15 = call i64 @inet_ref(ptr %net, ptr %tm, i16 0, i64 %tmp_reg_14)
%tmp_reg_16 = call i64 @inet_opr(ptr %net, ptr %tm, i16 0, i64 %tmp_reg_10, i64 %tmp_reg_15)
ret i64 %tmp_reg_16

}
