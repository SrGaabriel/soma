; ModuleID = 'base'
declare ptr @malloc(i64 %size)

declare void @free(ptr %ptr)

declare void @soma_era_free(ptr %ptr)

declare void @soma_panic(i32 %msg, i32 %line) noreturn

declare void @llvm.memcpy.p0.p0.i64(ptr %dst, ptr %src, i64 %len, i1 %isvolatile)

declare void @llvm.memset.p0.i64(ptr %dst, i8 %val, i64 %len, i1 %isvolatile)

define i32 @"$base/src/core$$test"() nounwind {
bb0:
  %0 = add i32 5, 0
  ret i32 %0
}

define i32 @"$base/src/core$$main"() nounwind {
bb0:
  %0 = bitcast ptr @"$base/src/core$$main" to ptr
  ret ptr %0
}