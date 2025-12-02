
declare i64 @inet_opr(ptr,ptr,i16,i64,i64)
declare i64 @inet_app(ptr,ptr,i64,i64)
declare i64 @inet_num_ext(i64)
declare i64 @inet_closure(ptr,ptr,i16,i16,ptr,i16)
declare i64 @inet_get_num_ext(i64)
declare i64 @inet_reduce(ptr,i64)
@g_inet = external global ptr
declare i64 @inet_ref(ptr,ptr,i16,i64)
@g_inet_tm = external global ptr
declare void @inet_register_func(ptr,ptr,i16,ptr)
@str_1=private unnamed_addr constant [19 x i8] c"lambda$0$m22524851\00"
@str_0=private unnamed_addr constant [24 x i8] c"testSimpleDup$m22524851\00"
declare i64 @inet_closure_get_env(ptr,i64,i16)




define i64 @"testSimpleDup$m22524851"(ptr %net,ptr %tm,i64 %arg) {
block0:
%tmp_reg_19 = call i64 @inet_get_num_ext(i64 %arg)
%tmp_reg_20 = trunc i64 %tmp_reg_19 to i32
%tmp_reg_21 = sext i32 %tmp_reg_20 to i64
%tmp_reg_22 = call i64 @inet_num_ext(i64 %tmp_reg_21)
%tmp_reg_23 = alloca i64, i32 1
%tmp_reg_24 = getelementptr i64, ptr %tmp_reg_23, i64 0
store i64 %tmp_reg_22, ptr %tmp_reg_24
%tmp_reg_25 = call i64 @inet_closure(ptr %net, ptr %tm, i16 1, i16 1, ptr %tmp_reg_23, i16 1)
%tmp_reg_26 = sext i32 1 to i64
%tmp_reg_27 = call i64 @inet_num_ext(i64 %tmp_reg_26)
%tmp_reg_28 = call i64 @inet_app(ptr %net, ptr %tm, i64 %tmp_reg_25, i64 %tmp_reg_27)
%tmp_reg_29 = sext i32 2 to i64
%tmp_reg_30 = call i64 @inet_num_ext(i64 %tmp_reg_29)
%tmp_reg_31 = call i64 @inet_app(ptr %net, ptr %tm, i64 %tmp_reg_25, i64 %tmp_reg_30)
%tmp_reg_32 = call i64 @inet_opr(ptr %net, ptr %tm, i16 0, i64 %tmp_reg_28, i64 %tmp_reg_31)
ret i64 %tmp_reg_32

}
define i32 @"soma_main"() {
block2:
%tmp_reg_7 = load ptr, ptr @g_inet
%tmp_reg_8 = select i1 true, ptr @"testSimpleDup$m22524851", ptr @"testSimpleDup$m22524851"
call void @inet_register_func(ptr %tmp_reg_7, ptr @str_0, i16 1, ptr %tmp_reg_8)
%tmp_reg_9 = load ptr, ptr @g_inet
%tmp_reg_10 = select i1 true, ptr @"lambda$0$m22524851", ptr @"lambda$0$m22524851"
call void @inet_register_func(ptr %tmp_reg_9, ptr @str_1, i16 2, ptr %tmp_reg_10)
%tmp_reg_11 = sext i32 100 to i64
%tmp_reg_12 = call i64 @inet_num_ext(i64 %tmp_reg_11)
%tmp_reg_13 = load ptr, ptr @g_inet
%tmp_reg_14 = load ptr, ptr @g_inet_tm
%tmp_reg_15 = call i64 @inet_ref(ptr %tmp_reg_13, ptr %tmp_reg_14, i16 0, i64 %tmp_reg_12)
%tmp_reg_16 = load ptr, ptr @g_inet
%tmp_reg_17 = call i64 @inet_reduce(ptr %tmp_reg_16, i64 %tmp_reg_15)
%tmp_reg_18 = trunc i64 %tmp_reg_17 to i32
ret i32 %tmp_reg_18

}
define i64 @"lambda$0$m22524851"(ptr %net,ptr %tm,i64 %arg) {
block1:
%tmp_reg_0 = call i64 @inet_closure_get_env(ptr %net, i64 %arg, i16 1)
%tmp_reg_1 = call i64 @inet_get_num_ext(i64 %tmp_reg_0)
%tmp_reg_2 = trunc i64 %tmp_reg_1 to i32
%tmp_reg_3 = call i64 @inet_closure_get_env(ptr %net, i64 %arg, i16 0)
%tmp_reg_4 = sext i32 %tmp_reg_2 to i64
%tmp_reg_5 = call i64 @inet_num_ext(i64 %tmp_reg_4)
%tmp_reg_6 = call i64 @inet_opr(ptr %net, ptr %tm, i16 0, i64 %tmp_reg_3, i64 %tmp_reg_5)
ret i64 %tmp_reg_6

}
