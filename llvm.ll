
declare void @soma_closure_set_env(ptr,i16,i64)
declare ptr @soma_alloc_closure(ptr,i8,i16)
declare i32 @printf(ptr,...)
@str_2=private unnamed_addr constant [9 x i8] c"<value>\0A\00"
declare i32 @puts(ptr)
declare ptr @malloc(i64)
@str_1=private unnamed_addr constant [6 x i8] c"<int>\00"
declare i64 @soma_closure_get_env(ptr,i16)
@str_0=private unnamed_addr constant [5 x i8] c"None\00"
%SomaClosure = type {i8, i8, i16, i32, ptr}




define void @"soma_main"() nounwind nosync nofree willreturn norecurse {
block0:
%tmp_reg_46 = call ptr @malloc(i64 40)
%tmp_reg_47 = bitcast ptr %tmp_reg_46 to ptr
%tmp_reg_48 = getelementptr inbounds i32, ptr %tmp_reg_47, i64 0
store i32 5, ptr %tmp_reg_48
%tmp_reg_49 = getelementptr inbounds i32, ptr %tmp_reg_47, i64 1
store i32 4, ptr %tmp_reg_49
%tmp_reg_50 = getelementptr inbounds i32, ptr %tmp_reg_47, i64 2
store i32 3, ptr %tmp_reg_50
%tmp_reg_51 = getelementptr inbounds i32, ptr %tmp_reg_47, i64 3
store i32 2, ptr %tmp_reg_51
%tmp_reg_52 = getelementptr inbounds i32, ptr %tmp_reg_47, i64 4
store i32 1, ptr %tmp_reg_52
%tmp_reg_53 = call ptr @"display$m64725555"(ptr %tmp_reg_47)
call i32 @puts(ptr %tmp_reg_53)
%tmp_reg_54 = bitcast ptr @"lambda$1$ClosurePtr_Option_String$m64725555" to ptr
%tmp_reg_55 = call ptr @soma_alloc_closure(ptr %tmp_reg_54, i8 1, i16 1)
%tmp_reg_56 = bitcast ptr %tmp_reg_55 to ptr
%tmp_reg_57 = bitcast ptr %tmp_reg_56 to ptr
%tmp_reg_58 = ptrtoint ptr @"display$String$m64725555" to i64
call void @soma_closure_set_env(ptr %tmp_reg_57, i16 0, i64 %tmp_reg_58)
call i32 @printf(ptr @str_2)
%tmp_reg_59 = bitcast ptr @"lambda$17$ClosurePtr_IO_Unit_IO_Unit$m64725555" to ptr
%tmp_reg_60 = call ptr @soma_alloc_closure(ptr %tmp_reg_59, i8 2, i16 1)
%tmp_reg_61 = bitcast ptr %tmp_reg_60 to ptr
%tmp_reg_62 = bitcast ptr %tmp_reg_61 to ptr
%tmp_reg_63 = ptrtoint ptr @">>=$m64725555" to i64
call void @soma_closure_set_env(ptr %tmp_reg_62, i16 0, i64 %tmp_reg_63)
ret ptr %tmp_reg_61

}
define ptr @"lambda$3$m64725555"(ptr %closure_self,i32 %n) nounwind nosync nofree memory(none) willreturn norecurse {
block14:
ret ptr @str_1

}
define ptr @"lambda$2$m64725555"(ptr %closure_self,ptr %str) nounwind nosync nofree memory(none) willreturn norecurse {
block15:
ret ptr %str

}
define void @"lambda$17$ClosurePtr_IO_Unit_IO_Unit$m64725555"(ptr %closure_self,void %ioA,void %ioB) nounwind nosync nofree willreturn norecurse {
block0:
%tmp_reg_43 = bitcast ptr @"lambda$15$ClosurePtr_IO_Unit_fn_Unit_to_IO_Unit$m64725555" to ptr
%tmp_reg_44 = call ptr @soma_alloc_closure(ptr %tmp_reg_43, i8 2, i16 0)
%tmp_reg_45 = bitcast ptr %tmp_reg_44 to ptr
ret ptr %tmp_reg_45

}
define ptr @"lambda$16$ClosurePtr_Unit$m64725555"(ptr %closure_self,void %a) nounwind nosync nofree willreturn norecurse {
block1:
%tmp_reg_41 = call i64 @soma_closure_get_env(ptr %closure_self, i16 0)
%tmp_reg_42 = inttoptr i64 %tmp_reg_41 to ptr
ret ptr %tmp_reg_42

}
define void @"lambda$15$ClosurePtr_IO_Unit_fn_Unit_to_IO_Unit$m64725555"(ptr %closure_self,void %ioA,ptr %f) nounwind nosync nofree willreturn norecurse {
block2:
call void @"pureIOSeq$m64725555"(void %ioA, ptr %f)
ret void

}
define ptr @"lambda$1$ClosurePtr_Option_String$m64725555"(ptr %closure_self,{i8, i64} %arg0) nounwind nosync nofree willreturn norecurse {
block16:
%tmp_reg_37 = extractvalue {i8, i64} %arg0, 0
switch i8 %tmp_reg_37, label %block18 [i8 0, label %block18 i8 1, label %block19]

block18:
%tmp_reg_38 = bitcast ptr @"lambda$2$m64725555" to ptr
%tmp_reg_39 = call ptr @soma_alloc_closure(ptr %tmp_reg_38, i8 1, i16 0)
%tmp_reg_40 = bitcast ptr %tmp_reg_39 to ptr
ret ptr %tmp_reg_40

block19:
ret ptr @str_0

}
define {i8, i64} @"lambda$0$ClosurePtr_fn_String_to_String_Option_String$m64725555"(ptr %closure_self,ptr %arg0,{i8, i64} %arg1) nounwind nosync nofree willreturn norecurse {
block20:
%tmp_reg_22 = extractvalue {i8, i64} %arg1, 0
switch i8 %tmp_reg_22, label %block22 [i8 0, label %block22 i8 1, label %block23]

block22:
%tmp_reg_23 = extractvalue {i8, i64} %arg1, 1
%tmp_reg_24 = inttoptr i64 %tmp_reg_23 to ptr
%tmp_reg_25 = getelementptr inbounds i64, ptr %tmp_reg_24, i64 1
%tmp_reg_26 = load i64, ptr %tmp_reg_25
%tmp_reg_27 = inttoptr i64 %tmp_reg_26 to ptr
%tmp_reg_28 = bitcast ptr %arg0 to ptr
%tmp_reg_29 = getelementptr inbounds %SomaClosure, ptr %tmp_reg_28, i32 0, i32 4
%tmp_reg_30 = load ptr, ptr %tmp_reg_29
%tmp_reg_31 = bitcast ptr %tmp_reg_30 to ptr
%tmp_reg_32 = call ptr %tmp_reg_31(ptr %arg0, ptr %tmp_reg_27)
%tmp_reg_33 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_34 = ptrtoint ptr %tmp_reg_32 to i64
%tmp_reg_35 = insertvalue {i8, i64} %tmp_reg_33, i64 %tmp_reg_34, 1
ret {i8, i64} %tmp_reg_35

block23:
%tmp_reg_36 = insertvalue {i8, i64} undef, i8 1, 0
ret {i8, i64} %tmp_reg_36

}
define {i8, i64} @"fmap$Option$fn_String_to_String_Option_String$m64725555"(ptr %arg0,{i8, i64} %arg1) nounwind nosync nofree willreturn norecurse {
block24:
%tmp_reg_19 = bitcast ptr @"lambda$0$ClosurePtr_fn_String_to_String_Option_String$m64725555" to ptr
%tmp_reg_20 = call ptr @soma_alloc_closure(ptr %tmp_reg_19, i8 2, i16 0)
%tmp_reg_21 = bitcast ptr %tmp_reg_20 to ptr
ret ptr %tmp_reg_21

}
define ptr @"display$String$m64725555"(ptr %arg0) nounwind nosync nofree willreturn norecurse {
block26:
%tmp_reg_16 = bitcast ptr @"lambda$2$m64725555" to ptr
%tmp_reg_17 = call ptr @soma_alloc_closure(ptr %tmp_reg_16, i8 1, i16 0)
%tmp_reg_18 = bitcast ptr %tmp_reg_17 to ptr
ret ptr %tmp_reg_18

}
define ptr @"display$Option$Option_String$m64725555"({i8, i64} %arg0) nounwind nosync nofree willreturn norecurse {
block25:
%tmp_reg_11 = bitcast ptr @"lambda$1$ClosurePtr_Option_String$m64725555" to ptr
%tmp_reg_12 = call ptr @soma_alloc_closure(ptr %tmp_reg_11, i8 1, i16 1)
%tmp_reg_13 = bitcast ptr %tmp_reg_12 to ptr
%tmp_reg_14 = bitcast ptr %tmp_reg_13 to ptr
%tmp_reg_15 = ptrtoint ptr @"display$String$m64725555" to i64
call void @soma_closure_set_env(ptr %tmp_reg_14, i16 0, i64 %tmp_reg_15)
ret ptr %tmp_reg_13

}
define ptr @"display$Int$m64725555"(i32 %arg0) nounwind nosync nofree willreturn norecurse {
block27:
%tmp_reg_8 = bitcast ptr @"lambda$3$m64725555" to ptr
%tmp_reg_9 = call ptr @soma_alloc_closure(ptr %tmp_reg_8, i8 1, i16 0)
%tmp_reg_10 = bitcast ptr %tmp_reg_9 to ptr
ret ptr %tmp_reg_10

}
define void @">>=$IO$IO_Unit_fn_Unit_to_IO_Unit$m64725555"(void %arg0,ptr %arg1) nounwind nosync nofree willreturn norecurse {
block34:
%tmp_reg_5 = bitcast ptr @"lambda$15$ClosurePtr_IO_Unit_fn_Unit_to_IO_Unit$m64725555" to ptr
%tmp_reg_6 = call ptr @soma_alloc_closure(ptr %tmp_reg_5, i8 2, i16 0)
%tmp_reg_7 = bitcast ptr %tmp_reg_6 to ptr
ret ptr %tmp_reg_7

}
define void @">>$IO$IO_Unit_IO_Unit$m64725555"(void %arg0,void %arg1) nounwind nosync nofree willreturn norecurse {
block35:
%tmp_reg_0 = bitcast ptr @"lambda$17$ClosurePtr_IO_Unit_IO_Unit$m64725555" to ptr
%tmp_reg_1 = call ptr @soma_alloc_closure(ptr %tmp_reg_0, i8 2, i16 1)
%tmp_reg_2 = bitcast ptr %tmp_reg_1 to ptr
%tmp_reg_3 = bitcast ptr %tmp_reg_2 to ptr
%tmp_reg_4 = ptrtoint ptr @">>=$m64725555" to i64
call void @soma_closure_set_env(ptr %tmp_reg_3, i16 0, i64 %tmp_reg_4)
ret ptr %tmp_reg_2

}
