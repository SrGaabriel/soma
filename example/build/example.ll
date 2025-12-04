
declare i32 @puts(ptr)
@str_4=private unnamed_addr constant [3 x i8] c"42\00"
declare ptr @soma_alloc_closure(ptr,i8,i16)
@str_3=private unnamed_addr constant [2 x i8] c"5\00"
@str_2=private unnamed_addr constant [2 x i8] c"1\00"
@str_1=private unnamed_addr constant [5 x i8] c"None\00"
@str_0=private unnamed_addr constant [6 x i8] c"<int>\00"




define void @"test$m55344248"() nounwind nosync nofree willreturn norecurse {
block11:
%tmp_reg_15 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_16 = ptrtoint ptr @str_4 to i64
%tmp_reg_17 = insertvalue {i8, i64} %tmp_reg_15, i64 %tmp_reg_16, 1
%tmp_reg_18 = call ptr @"display$Option$Option_String$m55344248"({i8, i64} %tmp_reg_17)
call i32 @puts(ptr %tmp_reg_18)
ret void

}
define void @"soma_main"() nounwind nosync nofree willreturn norecurse {
block0:
%tmp_reg_7 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_8 = ptrtoint ptr @str_3 to i64
%tmp_reg_9 = insertvalue {i8, i64} %tmp_reg_7, i64 %tmp_reg_8, 1
%tmp_reg_10 = bitcast ptr @"lambda$0$m55344248" to ptr
%tmp_reg_11 = call ptr @soma_alloc_closure(ptr %tmp_reg_10, i8 1, i16 0)
%tmp_reg_12 = bitcast ptr %tmp_reg_11 to ptr
%tmp_reg_13 = call {i8, i64} @"fmap$Option$m55344248"(ptr %tmp_reg_12, {i8, i64} %tmp_reg_9)
%tmp_reg_14 = call ptr @"display$Option$m55344248"({i8, i64} %tmp_reg_13)
call i32 @puts(ptr %tmp_reg_14)
ret void

}
define ptr @"lambda$0$m55344248"(ptr %closure_self,ptr %x) nounwind nosync nofree memory(none) willreturn norecurse {
block1:
ret ptr @str_2

}
define ptr @"display$String$m55344248"(ptr %str) nounwind nosync nofree memory(none) willreturn norecurse {
block6:
ret ptr %str

}
define ptr @"display$Option$Option_String$m55344248"({i8, i64} %arg0) nounwind nosync nofree willreturn norecurse {
block2:
%tmp_reg_0 = extractvalue {i8, i64} %arg0, 0
switch i8 %tmp_reg_0, label %block4 [i8 0, label %block4 i8 1, label %block5]

block4:
%tmp_reg_1 = extractvalue {i8, i64} %arg0, 1
%tmp_reg_2 = inttoptr i64 %tmp_reg_1 to ptr
%tmp_reg_3 = getelementptr inbounds i64, ptr %tmp_reg_2, i64 1
%tmp_reg_4 = load i64, ptr %tmp_reg_3
%tmp_reg_5 = inttoptr i64 %tmp_reg_4 to ptr
%tmp_reg_6 = select i1 1, ptr %tmp_reg_5, ptr %tmp_reg_5
ret ptr %tmp_reg_6

block5:
ret ptr @str_1

}
define ptr @"display$Int$m55344248"(i32 %n) nounwind nosync nofree memory(none) willreturn norecurse {
block1:
ret ptr @str_0

}
