; ModuleID = 'merged'
target triple = "x86_64-pc-windows-msvc"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"

@.str.0 = private constant [23 x i8] c"soma: unreachable code\00", align 1

declare noalias ptr @malloc(i64 %size) nounwind memory(inaccessiblemem: readwrite) willreturn

declare void @free(ptr nocapture %ptr) nounwind memory(argmem: readwrite, inaccessiblemem: readwrite) willreturn

declare void @soma_era_free(ptr nocapture %ptr) nounwind

declare void @soma_era_closure(ptr nocapture %ptr) nounwind

declare void @soma_era_string(ptr byval({ ptr, i64 }) %str) nounwind

declare void @soma_from_cstring(ptr sret({ ptr, i64 }) %ret, ptr nocapture readonly %cstr) nounwind

declare ptr @soma_to_cstring(ptr byval({ ptr, i64 }) %str) nounwind

declare void @soma_strcat(ptr sret({ ptr, i64 }) %ret, ptr byval({ ptr, i64 }) %a, ptr byval({ ptr, i64 }) %b) nounwind

declare void @soma_int_to_string(ptr sret({ ptr, i64 }) %ret, i32 %val) nounwind

declare noalias ptr @soma_pool_alloc_raw(i64 %byte_size) nounwind

declare void @soma_pool_free_raw(ptr nocapture %ptr, i64 %byte_size) nounwind

declare void @soma_panic(ptr nocapture readonly %msg) nounwind noreturn cold

declare void @llvm.memcpy.p0.p0.i64(ptr nocapture writeonly %dst, ptr nocapture readonly %src, i64 %len, i1 %isvolatile) nounwind

declare void @llvm.memset.p0.i64(ptr nocapture writeonly %dst, i8 %val, i64 %len, i1 %isvolatile) nounwind

declare ptr @soma_apply(ptr %closure, ptr %arg) nounwind

declare i64 @soma_dup_typed(i32 %label, i64 %value, ptr %type_desc) nounwind

declare ptr @soma_clone_closure(ptr %closure, i32 %label) nounwind

declare ptr @soma_clone_heap_value_for_dup(ptr %value, i32 %label) nounwind

declare i64 @soma_proj0(i64 %sup_val) nounwind

declare i64 @soma_proj1(i64 %sup_val) nounwind

declare noalias ptr @soma_clone_flat_array_view(ptr nocapture readonly %src) nounwind

declare noalias ptr @soma_alloc_view() nounwind

declare void @soma_free_view(ptr nocapture %ptr) nounwind

declare void @soma_list_cons(ptr sret({ ptr, i32, i32 }) %ret, ptr nocapture readonly %elem, ptr byval({ ptr, i32, i32 }) %tail, i16 %elem_size) nounwind

declare ptr @soma_list_head(ptr byval({ ptr, i32, i32 }) %list, i16 %elem_size) nounwind

declare void @soma_list_tail(ptr sret({ ptr, i32, i32 }) %ret, ptr byval({ ptr, i32, i32 }) %list, i16 %elem_size) nounwind

declare void @soma_list_dup(ptr sret({ ptr, i32, i32 }) %ret, ptr byval({ ptr, i32, i32 }) %list, i16 %elem_size) nounwind

declare void @soma_list_era(ptr byval({ ptr, i32, i32 }) %list) nounwind

declare void @soma_list_from_array(ptr sret({ ptr, i32, i32 }) %ret, ptr nocapture readonly %data, i32 %len, i16 %elem_size) nounwind

declare i64 @soma_dup_typed_list(i32 %label, ptr %boxed) nounwind

declare ptr @soma_list_box_for_sup(ptr byval({ ptr, i32, i32 }) %list, i16 %elem_size) nounwind

declare void @soma_list_unbox(ptr sret({ ptr, i32, i32 }) %ret, ptr %boxed) nounwind