
@str_0=private unnamed_addr constant [6 x i8] c"<int>\00"
declare ptr @soma_alloc_closure(ptr,i8,i16)




define ptr @"lambda$3$m22343894"(ptr %closure_self,i32 %n) nounwind nosync nofree memory(none) willreturn norecurse {
block14:
ret ptr @str_0

}
define ptr @"lambda$2$m22343894"(ptr %closure_self,ptr %str) nounwind nosync nofree memory(none) willreturn norecurse {
block15:
ret ptr %str

}
define ptr @"display$String$m22343894"(ptr %arg0) nounwind nosync nofree willreturn norecurse {
block26:
%tmp_reg_3 = bitcast ptr @"lambda$2$m22343894" to ptr
%tmp_reg_4 = call ptr @soma_alloc_closure(ptr %tmp_reg_3, i8 1, i16 0)
%tmp_reg_5 = bitcast ptr %tmp_reg_4 to ptr
ret ptr %tmp_reg_5

}
define ptr @"display$Int$m22343894"(i32 %arg0) nounwind nosync nofree willreturn norecurse {
block27:
%tmp_reg_0 = bitcast ptr @"lambda$3$m22343894" to ptr
%tmp_reg_1 = call ptr @soma_alloc_closure(ptr %tmp_reg_0, i8 1, i16 0)
%tmp_reg_2 = bitcast ptr %tmp_reg_1 to ptr
ret ptr %tmp_reg_2

}
