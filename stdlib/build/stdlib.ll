
%SomaClosure = type {i8, i8, i16, i32, ptr}
declare i64 @soma_closure_get_env(ptr,i16)
declare void @soma_closure_set_env(ptr,i16,i64)
declare ptr @soma_alloc_closure(ptr,i8,i16)
@str_0=private unnamed_addr constant [6 x i8] c"<int>\00"




define ptr @"lambda$6$m33972100"(ptr %closure_self,ptr %x) nounwind nosync nofree willreturn norecurse {
block18:
%tmp_reg_29 = call i64 @soma_closure_get_env(ptr %closure_self, i16 0)
%tmp_reg_30 = inttoptr i64 %tmp_reg_29 to ptr
%tmp_reg_31 = bitcast ptr %tmp_reg_30 to ptr
%tmp_reg_32 = getelementptr inbounds %SomaClosure, ptr %tmp_reg_31, i32 0, i32 4
%tmp_reg_33 = load ptr, ptr %tmp_reg_32
%tmp_reg_34 = bitcast ptr %tmp_reg_33 to ptr
%tmp_reg_35 = tail call ptr %tmp_reg_34(ptr %tmp_reg_30, ptr %x)
ret ptr %tmp_reg_35

}
define ptr @"lambda$5$m33972100"(ptr %closure_self,ptr %a) nounwind nosync nofree willreturn norecurse {
block19:
%tmp_reg_27 = call i64 @soma_closure_get_env(ptr %closure_self, i16 0)
%tmp_reg_28 = inttoptr i64 %tmp_reg_27 to ptr
ret ptr %tmp_reg_28

}
define ptr @"lambda$4$m33972100"(ptr %closure_self,ptr %f) nounwind nosync nofree willreturn norecurse {
block20:
%tmp_reg_19 = call i64 @soma_closure_get_env(ptr %closure_self, i16 1)
%tmp_reg_20 = inttoptr i64 %tmp_reg_19 to ptr
%tmp_reg_21 = bitcast ptr @"lambda$3$m33972100" to ptr
%tmp_reg_22 = call ptr @soma_alloc_closure(ptr %tmp_reg_21, i8 1, i16 1)
%tmp_reg_23 = bitcast ptr %tmp_reg_22 to ptr
%tmp_reg_24 = bitcast ptr %tmp_reg_23 to ptr
%tmp_reg_25 = ptrtoint ptr %f to i64
call void @soma_closure_set_env(ptr %tmp_reg_24, i16 0, i64 %tmp_reg_25)
%tmp_reg_26 = tail call ptr @">>=$IO$m33972100"(ptr %tmp_reg_20, ptr %tmp_reg_23)
ret ptr %tmp_reg_26

}
define ptr @"lambda$3$m33972100"(ptr %closure_self,ptr %a) nounwind nosync nofree willreturn norecurse {
block21:
%tmp_reg_12 = call i64 @soma_closure_get_env(ptr %closure_self, i16 0)
%tmp_reg_13 = inttoptr i64 %tmp_reg_12 to ptr
%tmp_reg_14 = bitcast ptr %tmp_reg_13 to ptr
%tmp_reg_15 = getelementptr inbounds %SomaClosure, ptr %tmp_reg_14, i32 0, i32 4
%tmp_reg_16 = load ptr, ptr %tmp_reg_15
%tmp_reg_17 = bitcast ptr %tmp_reg_16 to ptr
%tmp_reg_18 = tail call ptr %tmp_reg_17(ptr %tmp_reg_13, ptr %a)
ret ptr %tmp_reg_18

}
define ptr @"lambda$2$m33972100"(ptr %closure_self,ptr %a) nounwind nosync nofree willreturn norecurse {
block22:
%tmp_reg_4 = call i64 @soma_closure_get_env(ptr %closure_self, i16 1)
%tmp_reg_5 = inttoptr i64 %tmp_reg_4 to ptr
%tmp_reg_6 = bitcast ptr @"lambda$1$m33972100" to ptr
%tmp_reg_7 = call ptr @soma_alloc_closure(ptr %tmp_reg_6, i8 1, i16 1)
%tmp_reg_8 = bitcast ptr %tmp_reg_7 to ptr
%tmp_reg_9 = bitcast ptr %tmp_reg_8 to ptr
%tmp_reg_10 = ptrtoint ptr %a to i64
call void @soma_closure_set_env(ptr %tmp_reg_9, i16 0, i64 %tmp_reg_10)
%tmp_reg_11 = tail call ptr @">>=$IO$m33972100"(ptr %tmp_reg_5, ptr %tmp_reg_8)
ret ptr %tmp_reg_11

}
define ptr @"lambda$1$m33972100"(ptr %closure_self,ptr %b) nounwind nosync nofree willreturn norecurse {
block23:
%tmp_reg_2 = call i64 @soma_closure_get_env(ptr %closure_self, i16 0)
%tmp_reg_3 = inttoptr i64 %tmp_reg_2 to ptr
ret ptr %tmp_reg_3

}
define ptr @"lambda$0$m33972100"(ptr %closure_self,ptr %a) nounwind nosync nofree willreturn norecurse {
block24:
%tmp_reg_0 = call i64 @soma_closure_get_env(ptr %closure_self, i16 0)
%tmp_reg_1 = inttoptr i64 %tmp_reg_0 to ptr
ret ptr %tmp_reg_1

}
define ptr @"display$String$m33972100"(ptr %str) nounwind nosync nofree memory(none) willreturn norecurse {
block11:
ret ptr %str

}
define ptr @"display$Int$m33972100"(i32 %n) nounwind nosync nofree memory(none) willreturn norecurse {
block6:
ret ptr @str_0

}
