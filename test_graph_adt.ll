
declare i64 @inet_opr(ptr,ptr,i16,i64,i64)
declare i64 @inet_get(ptr,i32)
declare i64 @inet_reduce(ptr,i64)
@g_inet = external global ptr
declare i64 @inet_ref(ptr,ptr,i16,i64)
@g_inet_tm = external global ptr
declare i64 @inet_con(ptr,ptr,i64,i64)
declare i64 @inet_num_ext(i64)
declare void @inet_register_func(ptr,ptr,i16,ptr)
@str_0=private unnamed_addr constant [18 x i8] c"sumPair$m22764646\00"




define i64 @"sumPair$m22764646"(ptr %net,ptr %tm,i64 %arg) {
block2:
%tmp_reg_23 = lshr i64 %arg, 32
%tmp_reg_24 = add i64 %tmp_reg_23, 1
%tmp_reg_25 = trunc i64 %tmp_reg_24 to i32
%tmp_reg_26 = call i64 @inet_get(ptr %net, i32 %tmp_reg_25)
%tmp_reg_27 = lshr i64 %tmp_reg_26, 32
%tmp_reg_28 = add i64 %tmp_reg_27, 0
%tmp_reg_29 = trunc i64 %tmp_reg_28 to i32
%tmp_reg_30 = call i64 @inet_get(ptr %net, i32 %tmp_reg_29)
%tmp_reg_31 = lshr i64 %tmp_reg_26, 32
%tmp_reg_32 = add i64 %tmp_reg_31, 1
%tmp_reg_33 = trunc i64 %tmp_reg_32 to i32
%tmp_reg_34 = call i64 @inet_get(ptr %net, i32 %tmp_reg_33)
%tmp_reg_35 = lshr i64 %tmp_reg_34, 32
%tmp_reg_36 = add i64 %tmp_reg_35, 0
%tmp_reg_37 = trunc i64 %tmp_reg_36 to i32
%tmp_reg_38 = call i64 @inet_get(ptr %net, i32 %tmp_reg_37)
%tmp_reg_39 = call i64 @inet_opr(ptr %net, ptr %tm, i16 0, i64 %tmp_reg_30, i64 %tmp_reg_38)
ret i64 %tmp_reg_39

}
define i32 @"soma_main"() {
block3:
%tmp_reg_0 = load ptr, ptr @g_inet
%tmp_reg_1 = select i1 true, ptr @"sumPair$m22764646", ptr @"sumPair$m22764646"
call void @inet_register_func(ptr %tmp_reg_0, ptr @str_0, i16 1, ptr %tmp_reg_1)
%tmp_reg_2 = sext i32 0 to i64
%tmp_reg_3 = call i64 @inet_num_ext(i64 %tmp_reg_2)
%tmp_reg_4 = sext i32 10 to i64
%tmp_reg_5 = call i64 @inet_num_ext(i64 %tmp_reg_4)
%tmp_reg_6 = sext i32 32 to i64
%tmp_reg_7 = call i64 @inet_num_ext(i64 %tmp_reg_6)
%tmp_reg_8 = load ptr, ptr @g_inet
%tmp_reg_9 = load ptr, ptr @g_inet_tm
%tmp_reg_10 = call i64 @inet_con(ptr %tmp_reg_8, ptr %tmp_reg_9, i64 %tmp_reg_7, i64 20)
%tmp_reg_11 = load ptr, ptr @g_inet
%tmp_reg_12 = load ptr, ptr @g_inet_tm
%tmp_reg_13 = call i64 @inet_con(ptr %tmp_reg_11, ptr %tmp_reg_12, i64 %tmp_reg_5, i64 %tmp_reg_10)
%tmp_reg_14 = load ptr, ptr @g_inet
%tmp_reg_15 = load ptr, ptr @g_inet_tm
%tmp_reg_16 = call i64 @inet_con(ptr %tmp_reg_14, ptr %tmp_reg_15, i64 %tmp_reg_3, i64 %tmp_reg_13)
%tmp_reg_17 = load ptr, ptr @g_inet
%tmp_reg_18 = load ptr, ptr @g_inet_tm
%tmp_reg_19 = call i64 @inet_ref(ptr %tmp_reg_17, ptr %tmp_reg_18, i16 0, i64 %tmp_reg_16)
%tmp_reg_20 = load ptr, ptr @g_inet
%tmp_reg_21 = call i64 @inet_reduce(ptr %tmp_reg_20, i64 %tmp_reg_19)
%tmp_reg_22 = trunc i64 %tmp_reg_21 to i32
ret i32 %tmp_reg_22

}
