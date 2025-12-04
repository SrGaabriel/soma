
declare i32 @puts(ptr)
@str_2=private unnamed_addr constant [3 x i8] c"42\00"
@str_1=private unnamed_addr constant [5 x i8] c"None\00"
@str_0=private unnamed_addr constant [6 x i8] c"<int>\00"




define void @"test$m33972100"() nounwind nosync nofree willreturn norecurse {
block11:
%tmp_reg_7 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_8 = ptrtoint ptr @str_2 to i64
%tmp_reg_9 = insertvalue {i8, i64} %tmp_reg_7, i64 %tmp_reg_8, 1
%tmp_reg_10 = call ptr @"display$Option$Option_String$m33972100"({i8, i64} %tmp_reg_9)
call i32 @puts(ptr %tmp_reg_10)
ret void

}
define ptr @"display$String$m33972100"(ptr %str) nounwind nosync nofree memory(none) willreturn norecurse {
block6:
ret ptr %str

}
define ptr @"display$Option$Option_String$m33972100"({i8, i64} %arg0) nounwind nosync nofree willreturn norecurse {
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
define ptr @"display$Int$m33972100"(i32 %n) nounwind nosync nofree memory(none) willreturn norecurse {
block1:
ret ptr @str_0

}
