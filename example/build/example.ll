
declare i32 @puts(ptr)
@str_6=private unnamed_addr constant [7 x i8] c"<list>\00"
@str_5=private unnamed_addr constant [7 x i8] c"<list>\00"
declare ptr @soma_alloc_closure(ptr,i8,i16)
%SomaClosure = type {i8, i8, i16, i32, ptr}
@str_4=private unnamed_addr constant [5 x i8] c"None\00"
@str_3=private unnamed_addr constant [6 x i8] c"<int>\00"
@str_2=private unnamed_addr constant [6 x i8] c"<int>\00"
@str_1=private unnamed_addr constant [6 x i8] c"<int>\00"
@str_0=private unnamed_addr constant [7 x i8] c"<list>\00"




define void @"soma_main"() nounwind nosync nofree willreturn norecurse {
block0:
%tmp_reg_14 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_15 = zext i32 5 to i64
%tmp_reg_16 = insertvalue {i8, i64} %tmp_reg_14, i64 %tmp_reg_15, 1
%tmp_reg_17 = bitcast ptr @"example/llvm.lambda$0$m55344248" to ptr
%tmp_reg_18 = call ptr @soma_alloc_closure(ptr %tmp_reg_17, i8 1, i16 0)
%tmp_reg_19 = bitcast ptr %tmp_reg_18 to ptr
%tmp_reg_20 = call {i8, i64} @"fmap$Option$m55344248$fn_Int_to_Int_Option_Int$m55344248"(ptr %tmp_reg_19, {i8, i64} %tmp_reg_16)
%tmp_reg_21 = select i1 1, ptr @str_5, ptr @str_6
call i32 @puts(ptr %tmp_reg_21)
%tmp_reg_22 = call ptr @"display$Option$m55344248$Option_Int$m55344248"({i8, i64} %tmp_reg_20)
call i32 @puts(ptr %tmp_reg_22)
ret void

}
define {i8, i64} @"fmap$Option$m55344248$fn_Int_to_Int_Option_Int$m55344248"(ptr %arg0,{i8, i64} %arg1) nounwind nosync nofree willreturn norecurse {
block6:
%tmp_reg_2 = extractvalue {i8, i64} %arg1, 0
switch i8 %tmp_reg_2, label %block8 [i8 0, label %block8 i8 1, label %block9]

block8:
%tmp_reg_3 = extractvalue {i8, i64} %arg1, 1
%tmp_reg_4 = trunc i64 %tmp_reg_3 to i32
%tmp_reg_5 = bitcast ptr %arg0 to ptr
%tmp_reg_6 = getelementptr inbounds %SomaClosure, ptr %tmp_reg_5, i32 0, i32 4
%tmp_reg_7 = load ptr, ptr %tmp_reg_6
%tmp_reg_8 = bitcast ptr %tmp_reg_7 to ptr
%tmp_reg_9 = call i32 %tmp_reg_8(ptr %arg0, i32 %tmp_reg_4)
%tmp_reg_10 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_11 = zext i32 %tmp_reg_9 to i64
%tmp_reg_12 = insertvalue {i8, i64} %tmp_reg_10, i64 %tmp_reg_11, 1
ret {i8, i64} %tmp_reg_12

block9:
%tmp_reg_13 = insertvalue {i8, i64} undef, i8 1, 0
ret {i8, i64} %tmp_reg_13

}
define i32 @"example/llvm.lambda$0$m55344248"(ptr %closure_self,i32 %x) nounwind nosync nofree memory(none) willreturn norecurse {
block1:
ret i32 30

}
define ptr @"display$String$m55344248"(ptr %arg0) nounwind nosync nofree memory(none) willreturn norecurse {
block14:
ret ptr %arg0

}
define ptr @"display$Option$m55344248$Option_Int$m55344248"({i8, i64} %arg0) nounwind nosync nofree memory(none) willreturn norecurse {
block10:
%tmp_reg_0 = extractvalue {i8, i64} %arg0, 0
switch i8 %tmp_reg_0, label %block12 [i8 0, label %block12 i8 1, label %block13]

block12:
%tmp_reg_1 = select i1 1, ptr @str_2, ptr @str_3
ret ptr %tmp_reg_1

block13:
ret ptr @str_4

}
define ptr @"display$Int$m55344248"(i32 %arg0) nounwind nosync nofree memory(none) willreturn norecurse {
block15:
ret ptr @str_1

}
define ptr @"display$Array$Poly$m55344248$Array_Int$m55344248"(ptr %arg0) nounwind nosync nofree memory(none) willreturn norecurse {
block16:
ret ptr @str_0

}
