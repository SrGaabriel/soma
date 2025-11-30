declare void @soma_pool_init()
declare void @soma_pool_cleanup()
declare ptr @soma_dup(i32,ptr)
declare i64 @soma_proj0(i64)
declare i64 @soma_proj1(i64)
declare i64 @soma_par_proj0(i64,i32)
declare i64 @soma_par_proj1(i64,i32)
declare ptr @soma_fork_direct(ptr,i64)
declare ptr @soma_fork_closure(ptr,ptr,i64)
declare ptr @soma_fork_multi(ptr,ptr,i32)
declare i64 @soma_join(ptr)
declare i32 @soma_par_enabled_export()
declare ptr @soma_alloc_closure(ptr,i8,i16)
declare void @soma_closure_set_env(ptr,i16,i64)
declare i64 @soma_closure_get_env(ptr,i16)
declare ptr @soma_clone_closure(ptr)
declare void @soma_era_free(ptr)
declare i32 @soma_fresh_label()
declare ptr @soma_pool_alloc_sup()
declare ptr @soma_pool_alloc_closure(i16)
declare void @soma_pool_free_sup(ptr)
declare void @soma_pool_free_closure(ptr,i16)
declare ptr @malloc(i64)
declare void @free(ptr)
declare ptr @memcpy(ptr,ptr,i64)

declare i32 @puts(ptr)
@str_1=private unnamed_addr constant [2 x i8] c"5\00"
@str_0=private unnamed_addr constant [2 x i8] c"1\00"




define void @"soma_main"() {
block0:
%tmp_reg_0 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_1 = ptrtoint ptr @str_1 to i64
%tmp_reg_2 = insertvalue {i8, i64} %tmp_reg_0, i64 %tmp_reg_1, 1
%tmp_reg_3 = select i1 true, ptr @"lambda$0$m51113078", ptr @"lambda$0$m51113078"
%tmp_reg_4 = call ptr @"soma_alloc_closure"(ptr %tmp_reg_3, i8 1, i16 0)
%tmp_reg_5 = bitcast ptr %tmp_reg_4 to ptr
%tmp_reg_6 = call {i8, i64} @"fmap$m51113078"(ptr %tmp_reg_5, {i8, i64} %tmp_reg_2)
%tmp_reg_7 = call ptr @"display$m51113078"({i8, i64} %tmp_reg_6)
call i32 @puts(ptr %tmp_reg_7)
ret void

}
define ptr @"lambda$0$m51113078"(ptr %closure_self,ptr %x) {
block1:
ret ptr @str_0

}
