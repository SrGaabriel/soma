; ModuleID = 'main'
@.str.0 = private constant [14 x i8] c"Hello, World!\00", align 1

declare ptr @malloc(i64 %size)

declare void @free(ptr %ptr)

declare void @soma_era_free(ptr %ptr)

declare void @soma_panic(i32 %msg, i32 %line) noreturn

declare void @llvm.memcpy.p0.p0.i64(ptr %dst, ptr %src, i64 %len, i1 %isvolatile)

declare void @llvm.memset.p0.i64(ptr %dst, i8 %val, i64 %len, i1 %isvolatile)

declare ptr @soma_to_cstring(i64 %str)

declare ptr @soma_from_cstring(ptr %cstr)

declare i64 @soma_cstring_len(ptr %cstr)

declare ptr @soma_strcat(ptr %a, ptr %b)

declare ptr @soma_int_to_string(i32 %val)

define i8 @soma_main() nounwind {
bb0:
  %0 = call ptr @malloc(i64 16)
  %1 = add i64 13, 0
  store i64 %1, ptr %0
  %2 = ptrtoint ptr %0 to i64
  %3 = add i64 8, 0
  %4 = add i64 %2, %3
  %5 = inttoptr i64 %4 to ptr
  %6 = bitcast ptr @.str.0 to ptr
  store ptr %6, ptr %5
  %7 = add i8 0, 0
  ret i8 0
}